`default_nettype none

`include "warp_defines.v"

module warp_fetch #(
    parameter RESET_ADDR = 64'h8000000000000000
) (
    input  wire        i_clk,
    input  wire        i_rst_n,
    // read only parallel interface to instruction memory,
    // in practice connected to the instruction cache which
    // is backed by an AHB/AXI connection to the memory
    // this can transfer 64 bits per clock, which is enough to
    // feed the 2-wide fetch unit with 2 uncompressed instructions
    //
    // to request data from the memory, the address is placed in
    // raddr and ren is asserted. the memory will reply as soon
    // as it can by placing data in rdata and asserting valid.
    // the interface blocks until memory is returned (in case of
    // a cache miss). if a request was made but valid is not true,
    // the raddr must be kept stable
    output wire        o_imem_ren,
    // currently implementing risc-v sv39, meaning instructions are
    // addressed in a 39 bit virtual address space. the fetch unit
    // doesn't care what the underlying physical address space is
    // FIXME: using 64 bit PC for now to simplify verification in
    // machine (M) mode. once user/supervisor mode and virtual memory
    // are implemented this should be a 39 bit address (look into the
    // implications for auipc)
    output wire [63:0] o_imem_raddr,
    input  wire        i_imem_valid,
    input  wire [63:0] i_imem_rdata,
    // when asserted, branch_target contains the result of a branch
    // instruction target calculated by an execution unit
    input  wire        i_branch_valid,
    input  wire [63:0] i_branch_target,
`ifdef RISCV_FORMAL
    `RVFI_METADATA_OUTPUTS(_ch0),
    `RVFI_PC_OUTPUTS(_ch0),
    `RVFI_METADATA_OUTPUTS(_ch1),
    `RVFI_PC_OUTPUTS(_ch1),
`endif
    // indicates that the decode unit is ready to accept the
    // instructions output. while the decode unit itself does
    // not generate a stall, it may propogate one from downstream.
    // if not asserted, the fetch should keep the output data stable
    // unless the outputs are generated nops in order to avoid
    // dropping instructions
    input  wire        i_stall,
    // fetch outputs two instructions per clock cycle (can be nops)
    // if the instructions are 16 bit, only the lower 16 bits
    // of o_inst[01] are valid, specified by o_compressed.
    output wire [31:0] o_inst0,
    output wire [31:0] o_inst1,
    output wire [63:0] o_inst0_pc_rdata,
    output wire [63:0] o_inst0_pc_wdata,
    output wire [63:0] o_inst1_pc_rdata,
    output wire [63:0] o_inst1_pc_wdata,
    output wire [ 1:0] o_compressed
);
    reg [63:0] pc, next_pc;
    always @(posedge i_clk, negedge i_rst_n) begin
        if (!i_rst_n)
            pc <= RESET_ADDR;
        else
            pc <= next_pc;
    end

    // detect compressed instructions and segment appropriately
    wire [1:0] compressed;
    warp_pick pick (.i_buffer(i_imem_rdata), .o_compressed(compressed));

    wire [31:0] inst0 = i_imem_rdata[31:0];
    wire [31:0] inst1 = compressed[0] ? i_imem_rdata[47:16] : i_imem_rdata[63:32];

    wire [1:0] branch;
    warp_predecode predecode [1:0] (
        .i_inst({inst1, inst0}), .i_compressed(compressed),
        .o_branch(branch)
    );

    // for now, we assume the branch predictor (not yet implemented)
    // as well as the icache are single cycle and therefore we cannot
    // fetch past a branch to a potentially non-adjacent basic block
    // in this cycle. if the first instruction is a branch we emit a
    // nop for the second.
    // TODO: if the branch predictor allows async read (will increase area)
    // and predicted not taken, we can fetch past the branch
    wire count = !branch[0];

    // advance the pc depending on predecode results, segmenting by
    // compressed/uncompressed and avoid fetching past a branch
    // this is only used if the data is valid and downstream doesn't stall
    reg [63:0] advance_pc;
    always @(*) begin
        advance_pc = 64'hx;

        casez ({branch[0], compressed})
            3'b000: advance_pc = pc + 64'h8;
            3'b001,
            3'b010: advance_pc = pc + 64'h6;
            3'b011: advance_pc = pc + 64'h4;
            3'b10?: advance_pc = pc + 64'h4;
            3'b11?: advance_pc = pc + 64'h2;
        endcase
    end

    wire output_valid;
    wire transmit = output_valid && !i_stall;

    // if a branch instruction is encountered, the fetch stage stalls
    // until it receives a branch target from the execution units
    reg branch_stall;
    always @(posedge i_clk, negedge i_rst_n) begin
        if (!i_rst_n)
            branch_stall <= 1'b0;
        else if ((branch[0] || branch[1]) && transmit)
            branch_stall <= 1'b1;
        else if (i_branch_valid)
            branch_stall <= 1'b0;
    end

    // because the fetch stalls by requesting the same instruction
    // from cache, an untransmitted valid instruction will continue
    // to be valid on the next cycle without latching
    assign output_valid = i_imem_valid && !branch_stall;

    always @(*) begin
        // if decode does not stall, advance the program counter
        // according to the length of instructions fetched this cycle
        if (transmit)
            next_pc = advance_pc;
        // if we get a reply from the execution unit about branch
        // target, jump to that
        else if (i_branch_valid)
            next_pc = i_branch_target;
        // otherwise we have stalled for one reason or another
        // (waiting on cache, decode not ready)
        else
            next_pc = pc;
    end

    // edge detector that triggers a one cycle pulse after reset,
    // triggering the first fetch
    reg [1:0] init_edge;
    always @(posedge i_clk, negedge i_rst_n) begin
        if (!i_rst_n)
            init_edge <= 2'b00;
        else
            init_edge <= {init_edge[0], 1'b1};
    end

    wire init = !init_edge[1] && init_edge[0];

    // read from memory in three cases:
    // * once on init (first clock, triggered by edge detector)
    // * valid data at output (not waiting on outstanding mem transaction)
    //   and not stalling on branch
    // * branch target resolved and time to resume reading
    // read from imem once on init (first clock), and then every time
    // there is valid data output so we can read next
    wire imem_ren = init || (output_valid && (branch == 2'b00)) || i_branch_valid;

    wire [1:0] inst_valid = {output_valid && count, output_valid};

    wire [63:0] inst0_pc_rdata = pc;
    wire [63:0] inst0_pc_wdata = compressed[0] ? (pc + 64'h2) : (pc + 64'h4);
    wire [63:0] inst1_pc_rdata = inst0_pc_wdata;
    wire [63:0] inst1_pc_wdata = advance_pc;

    // request the next pc address from the cache, which
    // automatically handles stalling by re-fetching the
    // same instruction. this shouldn't cause any problems
    // since the instruction cache is a private single cycle
    // cache and this theoretically will never cause a cache miss
    // following an initial cache hit. however in the future it
    // may be beneficial to latch the buffer and avoid re-fetching
    // mostly to save energy usage
    assign o_imem_ren = imem_ren;
    assign o_imem_raddr = next_pc;

    assign o_inst0 = inst_valid[0] ? inst0 : `CANONICAL_NOP;
    assign o_inst1 = inst_valid[1] ? inst1 : `CANONICAL_NOP;
    assign o_inst0_pc_rdata = inst0_pc_rdata;
    assign o_inst0_pc_wdata = inst0_pc_wdata;
    assign o_inst1_pc_rdata = inst1_pc_rdata;
    assign o_inst1_pc_wdata = inst1_pc_wdata;
    assign o_compressed = compressed & inst_valid;

`ifdef RISCV_FORMAL
    reg [63:0] f_order;
    always @(posedge i_clk, negedge i_rst_n) begin
        if (!i_rst_n)
            f_order <= 64'h0;
        else if (transmit)
            f_order <= count ? 64'h2 : 64'h1;
    end

    assign of_valid_ch0 = inst_valid[0];
    assign of_order_ch0 = f_order;
    assign of_insn_ch0  = compressed[0] ? {16'h0, o_inst0[15:0]} : o_inst0;
    assign of_trap_ch0  = 1'b0; // only set by decode stage and later
    assign of_halt_ch0  = 1'b0;
    assign of_intr_ch0  = 1'b0;
    assign of_mode_ch0  = 2'h3; // machine mode (M)
    assign of_ixl_ch0   = 2'h2; // 64 bits
    assign of_pc_rdata_ch0 = inst0_pc_rdata;
    assign of_pc_wdata_ch0 = inst0_pc_wdata;

    assign of_valid_ch1 = inst_valid[1];
    assign of_order_ch1 = f_order + 64'h1;
    assign of_insn_ch1  = compressed[1] ? {16'h0, o_inst1[15:0]} : o_inst1;
    assign of_trap_ch1  = 1'b0; // only set by decode stage and later
    assign of_halt_ch1  = 1'b0;
    assign of_intr_ch1  = 1'b0;
    assign of_mode_ch1  = 2'h3; // machine mode (M)
    assign of_ixl_ch1   = 2'h2; // 64 bits
    assign of_pc_rdata_ch1 = inst1_pc_rdata;
    assign of_pc_wdata_ch1 = inst1_pc_wdata;
`endif

`ifdef WARP_FORMAL
    reg f_past_valid;
    initial f_past_valid <= 1'b0;
    always @(posedge i_clk) f_past_valid <= 1'b1;

    initial assume (!i_rst_n);
    initial assume (!i_clk);

    always @(*) begin
        if (!i_rst_n) begin
            assume (!i_imem_valid);
            assume (!i_branch_valid);

            assert (!o_imem_ren);
        end
    end

    reg f_mem_outstanding;
    always @(posedge i_clk, negedge i_rst_n) begin
        if (!i_rst_n)
            f_mem_outstanding <= 1'b0;
        else if (o_imem_ren)
            f_mem_outstanding <= 1'b1;
        else if (i_imem_valid)
            f_mem_outstanding <= 1'b0;
    end

    reg f_branch_outstanding;
    always @(posedge i_clk, negedge i_rst_n) begin
        if (!i_rst_n)
            f_branch_outstanding <= 1'b0;
        else if ((branch[0] || branch[1]) && transmit)
            f_branch_outstanding <= 1'b1;
        else if (i_branch_valid)
            f_branch_outstanding <= 1'b0;
    end

    always @(posedge i_clk) begin
        // imem will never respond without a request
        if (i_imem_valid)
            assume (f_mem_outstanding);

        // branch will never respond unless fetch is stalled
        if (i_branch_valid)
            assume (f_branch_outstanding);

        if (i_rst_n) begin
            // unit must not issue a memory request while another one
            // is outstanding
            if (f_mem_outstanding && !i_imem_valid)
                assert (!o_imem_ren);

            // make sure the unit can actually complete a bus transaction
            cover (f_mem_outstanding && i_imem_valid);

            // since it takes a clock to read data from the memory following reset,
            // we should not expect valid output right after reset
            if (f_past_valid && !$past(i_rst_n))
                assert (inst_valid == 2'b00);

            // since the current implementation never buffers instructions,
            // inst_valid implies icache response
            if (inst_valid != 2'b00)
                assert (i_imem_valid);

            // if stalling on branch and haven't received a target, do not
            // output any valid instructions
            if (f_branch_outstanding && !i_branch_valid)
                assert (inst_valid == 2'b00);

            // without branch prediction, we cannot fetch right after a branch
            // because there is at least one cycle delay for the target reply
            if (f_past_valid && $past((branch & inst_valid) != 2'b00))
                assert (!$past(o_imem_ren) && (inst_valid == 2'b00));

            // if instruction 0 is a branch, instruction 1 should not be valid
            if (branch[0])
                assert (!inst_valid[1]);

            // if instruction is not valid, output a nop
            if (!inst_valid[0])
                assert (o_inst0 == `CANONICAL_NOP);
            if (!inst_valid[1])
                assert (o_inst1 == `CANONICAL_NOP);

            // do not stall the pc without a reason
            if (f_past_valid && $stable(pc))
                assert ($past(inst_valid == 2'b00) || $past(i_stall) || $past(branch_stall && !i_branch_valid));

            // receiving a branch target implies was waiting for one
            if (i_branch_valid)
                assert (branch_stall);

            // if a branch target is provided, take it
            if (f_past_valid && $past(i_branch_valid))
                assert ($past(branch_stall || (branch != 2'b00)) && (pc == $past(i_branch_target)));

            // and cover that we can take a branch target
            if (f_past_valid)
                cover ($past(i_branch_valid) && (pc == $past(i_branch_target)));

            // pc should jump by a standard amount unless jumping to
            // a branch target, which is checked by previous property
            if (f_past_valid && !$past(i_branch_valid))
                assert (
                    pc == $past(pc + 64'h0) ||
                    pc == $past(pc + 64'h2) ||
                    pc == $past(pc + 64'h4) ||
                    pc == $past(pc + 64'h6) ||
                    pc == $past(pc + 64'h8)
                );

            // and cover that all such standard increments are possible
            if (f_past_valid) begin
                cover (pc == $past(pc + 64'h0));
                cover (pc == $past(pc + 64'h2));
                cover (pc == $past(pc + 64'h4));
                cover (pc == $past(pc + 64'h6));
                cover (pc == $past(pc + 64'h8));
            end

            // NOTE: we should add a liveness property here such that
            // assuming fairness (instruction cache eventually replies with
            // some data, and the branch unit doesn't get stuck) we will
            // always eventually output valid instructions

            // cover different state transitions
            // waiting for memory -> serving one instruction
            cover (f_past_valid && $past(inst_valid == 2'b00) && (inst_valid == 2'b01));
            // waiting for memory -> serving two instructions
            cover (f_past_valid && $past(inst_valid == 2'b00) && (inst_valid == 2'b11));
            // waiting for memory -> still waiting
            cover (f_past_valid && $past(inst_valid == 2'b00) && (inst_valid == 2'b00));
            // serving instruction -> still serving the same one
            if (o_past_valid && $past(inst_valid != 2'b00))
                cover ($stable(pc) && $stable(o_compressed) && $stable(o_inst0) && $stable(o_inst1));
            // back to back dual issue of different insts (100% throughput)
            if (o_past_valid)
                cover ($past(!i_stall) && $past(inst_valid == 2'b11) && !i_stall && (inst_valid == 2'b11) && !$stable(pc) && !$stable(inst0) && !$stable(inst1));
        end
    end
`endif
endmodule

`default_nettype wire
