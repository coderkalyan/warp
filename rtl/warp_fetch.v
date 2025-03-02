`default_nettype none

module warp_fetch_old #(
    parameter RESET_ADDR = 39'h4000000000
) (
    input  wire        i_clk,
    input  wire        i_rst_n,
    output wire        o_mem_ren,
    output wire [63:0] o_mem_raddr,
    input  wire [63:0] i_mem_rdata,
    input  wire        i_mem_valid,
    input  wire [63:0] i_branch_target,
    input  wire        i_branch_valid,
    input  wire        i_output_ready,
    output wire        o_output_valid,
    output wire [31:0] o_inst0,
    output wire [31:0] o_inst1,
    output wire [1:0]  o_compressed,
    output wire        o_count
);
    reg [63:0] pc, next_pc;
    always @(posedge i_clk, negedge i_rst_n) begin
        if (!i_rst_n)
            pc <= RESET_ADDR;
        else
            pc <= next_pc;
    end

    wire [63:0] buffer = i_mem_rdata;

    reg buffer_valid;
    always @(posedge i_clk, negedge i_rst_n) begin
        if (!i_rst_n)
            buffer_valid <= 1'h0;
        else if (i_output_ready)
            buffer_valid <= 1'b0;
        else if (i_mem_valid)
            buffer_valid <= 1'b1;
    end

    // detect compressed instructions and segment appropriately
    wire [1:0] compressed;
    warp_pick pick (.i_buffer(buffer), .o_compressed(compressed));

    wire [31:0] inst0 = buffer[31:0];
    wire [31:0] inst1 = compressed[0] ? buffer[47:16] : buffer[63:32];

    wire [1:0] branch;
    warp_predecode predecode [1:0] (
        .i_inst({inst0, inst1}), .i_compressed(compressed),
        .o_branch(branch)
    );

    // if the first instruction is not a branch, the second is valid
    // this unit does not attempt to speculate past a branch in a single
    // cycle, as this requires double the read bandwidth from the cache
    wire count = !branch[0];

    // latches output data to hold if not immediately accepted
    // by receiver (output_valid held for multiple cycles)
    reg [31:0] hold_inst0, hold_inst1;
    reg [1:0]  hold_compressed;
    reg        hold_count;
    always @(posedge i_clk, negedge i_rst_n) begin
        if (!i_rst_n) begin
            hold_inst0 <= 32'h0;
            hold_inst1 <= 32'h0;
            hold_compressed <= 2'b0;
            hold_count <= 1'b0;
        end else if (i_mem_valid) begin
            hold_inst0 <= inst0;
            hold_inst1 <= inst1;
            hold_compressed <= compressed;
            hold_count <= count;
        end
    end

    `ifdef WARP_FORMAL
    reg [63:0] f_hold_buffer;
    always @(posedge i_clk, negedge i_rst_n) begin
        if (!i_rst_n)
            f_hold_buffer <= 64'h0;
        else if (i_mem_valid)
            f_hold_buffer <= buffer;
    end
    `endif

    // output instruction(s) and pipeline next request to cache
    // if valid (output ready and didn't hit a branch)
    localparam FETCH = 3'h0;
    // stalled on instruction cache, no PC change and no new request
    // to cache, output not valid
    localparam CACHE = 3'h1;
    // stalled on backend (prev output not ready), no PC change,
    // output valid, no request to cache unless output ready this cycle
    localparam VALID = 3'h2;
    // stalled on branch resolution, no PC change, output not valid,
    // no request to cache
    localparam RESOL = 3'h3;
    // reset state, initiates a read request to cache
    localparam INIT  = 3'h4;

    reg [2:0] state, next_state;
    always @(posedge i_clk, negedge i_rst_n) begin
        if (!i_rst_n)
            state <= INIT;
        else
            state <= next_state;
    end

    // instruction "sent" if output handshake succeeds
    // that is, fetch is valid and receiver ready
    wire sent = o_output_valid && i_output_ready;
    wire branched = branch != 2'b00;

    always @(*) begin
        next_state = state;

        case (state)
            INIT: next_state = FETCH;
            // FETCH -> VALID if output not ready
            // FETCH -> RESOL if predecode detected a branch
            // FETCH -> FETCH if output ready and no branch
            FETCH: next_state = sent ? (branched ? RESOL : FETCH) : (o_output_valid ? VALID : CACHE);
            // CACHE -> FETCH if cache returned value
            // CACHE -> CACHE if not
            CACHE: next_state = i_mem_valid ? (sent ? (branched ? RESOL : FETCH) : VALID) : CACHE;
            // VALID -> FETCH if output ready
            // VALID -> VALID if output not ready
            VALID: next_state = sent ? (branched ? RESOL : FETCH) : VALID;
            // RESOL -> FETCH if input branch target valid
            // RESOL -> RESOL if not
            RESOL: next_state = i_branch_valid ? FETCH : RESOL;
        endcase
    end

    wire mem_ren = i_rst_n && (next_state == FETCH);

    // advance the pc depending on predecode results
    // this is only used in some state transitions
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

    // in the RESOL state, pc stalls until i_branch_valid and
    // then latches the received branch target
    // in all other states, pc stalls if !sent, else advances
    always @(*) begin
        next_pc = pc;

        if ((state == RESOL) && i_branch_valid)
            next_pc = i_branch_target;
        else if ((state != RESOL) && sent)
            next_pc = advance_pc;
    end

    wire hold = state == VALID;
    // the cache read enable is asserted for exactly one cycle
    // after an instruction was sent - else we are stalled for
    // some reason. the cache interface latches this request and
    // it doesn't need to be continuously asserted on cache miss.
    // when fully pipelined (and on cache hit) this can achieve
    // 100% throughput, reading an address each clock cycle.
    assign o_mem_ren = mem_ren;
    assign o_mem_raddr = pc;
    // assign o_output_valid = hold ? valid : i_mem_valid; // valid || i_mem_valid;
    assign o_output_valid = i_mem_valid || hold;
    assign o_inst0 = hold ? hold_inst0 : inst0;
    assign o_inst1 = hold ? hold_inst1 : inst1;
    assign o_compressed = hold ? hold_compressed : compressed;
    assign o_count = hold ? hold_count : count;

    `ifdef WARP_FORMAL
        reg f_past_valid;
        initial f_past_valid <= 1'b0;
        always @(posedge i_clk) f_past_valid <= 1'b1;

        (* gclk *) reg formal_timestep;
        reg [7:0] f_cycle;
        initial f_cycle <= 8'd0;
        always @(posedge formal_timestep)
            f_cycle <= f_cycle + 8'd1;

        initial begin
            assume (!i_rst_n);
            assume (!i_clk);
            assume (!i_mem_valid);
            assume (!i_branch_valid);

            assert (!o_output_valid);
            assert (!o_mem_ren);
        end

        // the interface is entirely synchronous
        always @(posedge formal_timestep) begin
            if (!i_rst_n) begin
                assume (!i_mem_valid);
                assume (!i_branch_valid);

                assert (!o_mem_ren);
                assert (!o_output_valid);
            end

            if (!$rose(i_clk)) begin
                assume ($stable(i_mem_rdata));
                assume ($stable(i_mem_valid));
                assume ($stable(i_branch_target));
                assume ($stable(i_branch_valid));
                assume ($stable(i_output_ready));
            end

            if (f_past_valid && !$changed(i_rst_n) && !$rose(i_clk)) begin
                assert ($stable(o_mem_raddr));
                assert ($stable(o_mem_ren));
                assert ($stable(o_output_valid));
                assert ($stable(o_inst0));
                assert ($stable(o_inst1));
                assert ($stable(o_compressed));
                assert ($stable(o_count));
            end
        end

reg f_mem_outstanding;
        initial f_mem_outstanding <= 1'b0;
        always @(posedge i_clk, negedge i_rst_n) begin
            if (!i_rst_n)
                f_mem_outstanding <= 1'b0;
            else if (o_mem_ren)
                f_mem_outstanding <= 1'b1;
            else if (i_mem_valid)
                f_mem_outstanding <= 1'b0;
        end

        reg f_branch_outstanding;
        initial f_branch_outstanding <= 1'b0;
        always @(posedge i_clk, negedge i_rst_n) begin
            if (!i_rst_n)
                f_branch_outstanding <= 1'b0;
            else if (next_state == RESOL)
                f_branch_outstanding <= 1'b1;
            else if (i_branch_valid)
                f_branch_outstanding <= 1'b0;
        end

        always @(posedge i_clk) begin
            // cache will never "respond" without a request
            if (f_past_valid && i_mem_valid)
                assume (f_mem_outstanding);
            // unit must not issue a memory request while
            // another one is outstanding
            if (o_mem_ren)
                assert (!f_mem_outstanding || i_mem_valid);

            a_mem: cover (f_mem_outstanding);
        end

        // reg [63:0] f_mem_rdata;
        wire [63:0] f_buffer = hold ? f_hold_buffer : buffer;
        (* anyconst *) reg [63:0] f_buffer1, f_buffer2;
        (* any *) reg f_latch_d1;
        initial assume (f_buffer1 != f_buffer2);

        reg f_in1, f_in2, f_out1, f_out2;
        always @(posedge i_clk, negedge i_rst_n) begin
            if (!i_rst_n) begin
                f_in1 <= 1'b0;
                f_in2 <= 1'b0;
                f_out1 <= 1'b0;
                f_out2 <= 1'b0;
            end else begin
                if (i_mem_valid && (i_mem_rdata == f_buffer1) && f_latch_d1)
                    f_in1 <= 1'b1;
                if (i_mem_valid && (i_mem_rdata == f_buffer2))
                    f_in2 <= 1'b1;
                if (!f_in1)
                    assume (!f_in2);

                if (o_output_valid && (f_buffer == f_buffer1))
                    f_out1 <= 1'b1;
                if (o_output_valid && (f_buffer == f_buffer2))
                    f_out2 <= 1'b1;
            end
        end

        reg f_advance0, f_advance2, f_advance4, f_advance6, f_advance8;

        always @(posedge i_clk) begin
            if (f_past_valid && !$past(i_rst_n)) begin
                assert (!o_output_valid);
            end

            if (i_rst_n) begin
                // downstream backpressure should not drop insts:
                // if output is valid but not ready (transmitted),
                // the output data should remain stable
                if (f_past_valid && (state != INIT) && $past(o_output_valid) && !$past(i_output_ready)) begin
                    a_backpressure1: assert ($stable(o_output_valid));
                    a_backpressure2: assert ($stable(o_inst0));
                    a_backpressure3: assert ($stable(o_inst1));
                    a_backpressure4: assert ($stable(o_compressed));
                    a_backpressure5: assert ($stable(o_count));
                end

                // liveness:
                // instruction received from the cache
                // must eventually appear at output interface,
                // assuming instruction cache and branch resolution
                // are "fair" and don't stall indefinitely
                if ((f_cycle == `WARP_FORMAL_DEPTH) && f_in1)
                    a_liveness: assert (f_out1);

                // order: if `d1` was received on the cache interface
                // before `d2`, it should also appear on the output
                // interface first
                if (f_in1 && f_in2 && !f_out1)
                    a_order: assert (!f_out2);

                // if (i_mem_valid)
                //     f_mem_rdata <= i_mem_rdata;
                // assert property (s_eventually (o_output_valid && (buffer == f_mem_rdata)));

                // branch target resolution
                if (f_past_valid && $stable(i_rst_n) && $past(state == RESOL) && $past(i_branch_valid)) begin
                    a_branch: assert (
                        (state == INIT) ||
                        ((state == FETCH) && (pc == $past(i_branch_target)))
                    );
                end

                // state machine check: if receiving data from memory,
                // we expect to be in idle, fetch or cache stages
                if (i_mem_valid)
                    a_rx: assert ((state == INIT) || (state == FETCH) || (state == CACHE));

                c_valid:    cover (f_past_valid && $past(i_rst_n) && $rose(o_output_valid));
                c_notvalid: cover (f_past_valid && $past(i_rst_n) && $fell(o_output_valid));
                // ensures we can achieve 100% throughput (back to back)
                c_throughput: cover (f_past_valid && $past(sent, 2) && sent);

                // state transitions
                c_state1: cover (f_past_valid && $past(state == VALID) && (state == FETCH));
                c_state2: cover (f_past_valid && $past(state == CACHE) && (state == FETCH));
                c_state3: cover (f_past_valid && $past(state == RESOL) && (state == FETCH));

                // stall protection - both runaway and indefinite stall
                if (f_past_valid && !$past(sent) && !$past(i_branch_valid))
                    a_pc: assert ((pc == RESET_ADDR) || $stable(pc));
                if (f_past_valid && $past(state == FETCH))
                    c_pc1: cover (!$stable(pc));

                f_advance0 = f_past_valid && (pc == ($past(pc) + 64'h0));
                f_advance2 = f_past_valid && (pc == ($past(pc) + 64'h2));
                f_advance4 = f_past_valid && (pc == ($past(pc) + 64'h4));
                f_advance6 = f_past_valid && (pc == ($past(pc) + 64'h6));
                f_advance8 = f_past_valid && (pc == ($past(pc) + 64'h8));

                assert (
                    (pc == RESET_ADDR) ||
                    f_advance0 ||
                    f_advance2 ||
                    f_advance4 ||
                    f_advance6 ||
                    f_advance8 ||
                    ($past(i_branch_valid) && (pc == $past(i_branch_target)))
                );

                c_pc2:  cover (f_advance0);
                c_pc3:  cover (f_advance2);
                c_pc4:  cover (f_advance4);
                c_pc5:  cover (f_advance6);
                c_pc6:  cover (f_advance8);
                c_jump: cover (f_past_valid && $past(i_branch_valid) && (pc == $past(i_branch_target)));
            end
        end
    `endif
endmodule

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
    output wire [38:0] o_imem_raddr,
    input  wire        i_imem_valid,
    input  wire [63:0] i_imem_rdata,
    // input  wire [63:0] i_branch_target,
    // input  wire        i_branch_valid,
    // fetch outputs up to two instructions per clock cycle,
    // specified by o_cout. if the instructions are 16 bit,
    // only the lower 16 bits of o_inst[01] are valid.
    // this is specified by o_compressed.
    //
    // indicates that the fetch unit is presenting valid output
    // instructions, if not asserted the decode should not try
    // to consume new instructions. if not asserted, and output
    // is valid, the fetch should keep the output data stable
    // (effectively stalling the frontend)
    output wire        o_output_valid,
    // indicates that the decode unit is ready to accept the
    // instructions output here.
    input  wire        i_output_ready,
    output wire [31:0] o_inst0,
    output wire [31:0] o_inst1,
    output wire [1:0]  o_compressed,
    output wire        o_count
);
    reg [39:0] pc, next_pc;
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
        .i_inst({inst0, inst1}), .i_compressed(compressed),
        .o_branch(branch)
    );

    // if the first instruction is not a branch, the second is valid
    // this unit does not attempt to speculate past a branch in a single
    // cycle, as this requires double the read bandwidth from the cache
    // TODO: in certain cases, we may be able to speculate not taken and
    // fetch here, but this requires more bookkeeping
    // it might increase frontend significantly for unlikely branches
    wire count = !branch[0];

    // advance the pc depending on predecode results
    // this is only used if the fetch data is valid and decode
    // unit is ready
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

    // because the fetch stalls by requesting the same instruction
    // from cache, an untransmitted valid instruction will continue
    // to be valid on the next cycle without latching
    wire output_valid = i_imem_valid;
    wire transmit = output_valid && i_output_ready;

    // FIXME: implement branching
    always @(*) begin
        // if output is valid and decode is ready to accept,
        // advance the program counter according to the length
        // of instructions fetched on this cycle
        if (transmit)
            next_pc = advance_pc;
        // otherwise we have stalled for one reason or another
        // (waiting on cache, decode not ready)
        else
            next_pc = pc;
    end

    reg imem_init;
    always @(posedge i_clk, negedge i_rst_n) begin
        if (!i_rst_n)
            imem_init <= 1'b1;
        else
            imem_init <= 1'b0;
    end

    // read from imem once on init (first clock), and then every time
    // there is valid data output so we can read next
    wire imem_ren = i_rst_n && (imem_init || output_valid);

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

    assign o_output_valid = output_valid;
    assign o_inst0 = inst0;
    assign o_inst1 = inst1;
    assign o_compressed = compressed;
    assign o_count = count;

`ifdef WARP_FORMAL
    reg f_past_valid;
    initial f_past_valid <= 1'b0;
    always @(posedge i_clk) f_past_valid <= 1'b1;

    (* gclk *) reg formal_timestep;

    initial assume (!i_rst_n);
    initial assume (!i_clk);

    always @(*) begin
        if (!i_rst_n) begin
            assume (!i_imem_valid);

            assert (!o_output_valid);
            assert (!o_imem_ren);
        end
    end

    // the interface must be entirely synchronous
    always @(posedge formal_timestep) begin
        // asynchronous assert, synchronous deassert clock
        if (f_past_valid && $rose(i_rst_n))
            assume ($rose(i_clk));

        if (!$rose(i_clk)) begin
            assume ($stable(i_imem_valid));
            assume ($stable(i_imem_rdata));
            assume ($stable(i_output_ready));
        end

        if (f_past_valid && i_rst_n && !$rose(i_clk)) begin
            assert ($stable(o_imem_ren));
            assert ($stable(o_imem_raddr));
            assert ($stable(o_output_valid));
            assert ($stable(o_inst0));
            assert ($stable(o_inst1));
            assert ($stable(o_compressed));
            assert ($stable(o_count));
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

    // FIXME:ideally, the formal needs to know the behavior of the imem
    // interface is a memory in order to generally show that multiple
    // reads to the same address are identical, which is needed because the
    // fetch unit stalls by repeatedly requesting the same address
    // however, due to the size of the problem space, currently only
    // consecutive reads to the same address (when stalled) are ad-hoc assumed
    reg [39:0] f_raddr;
    always @(posedge i_clk) begin
        // track the most recent read from imem
        if (o_imem_ren)
            f_raddr <= o_imem_raddr;

        // a cache hit followed by an access to the same address will always
        // be a cache hit - we assume this to make the fetch unit simpler. if
        // necessary this can be revised
        // this is basically temporal locality, and makes no assumptions about
        // delayed requests to the same address
        if (f_past_valid && $past(i_imem_valid) && $stable(f_raddr)) begin
            assume (i_imem_valid);
            assume ($stable(i_imem_rdata));
        end
    end

    always @(posedge i_clk) begin
        // imem will never respond without a request
        if (i_imem_valid)
            assume (f_mem_outstanding);

        // unit must not issue a memory request while another one
        // is outstanding
        if (f_mem_outstanding && !i_imem_valid)
            assert (!o_imem_ren);

        // make sure the unit can actually complete a bus transaction
        cover (f_mem_outstanding && i_imem_valid);

        // since it takes a clock to read data from the memory following reset,
        // we should not expect valid output right after reset
        if (f_past_valid && !$past(i_rst_n))
            assert (!o_output_valid);

        if (i_rst_n) begin
            // downstream backpressure should not drop instructions:
            // if output is valid but decoder not ready (transmitted),
            // the output data should remain stable
            if (f_past_valid && $past(o_output_valid) && !$past(i_output_ready)) begin
                assert ($stable(o_output_valid));
                assert ($stable(o_count));
                // the implementation will hold both of these stable in
                // practice, but technically it only needs to uphold this
                // contract for the valid instructions
                // TODO: to behave like an optimal 2 entry fifo, we should
                // be able to load one more instruction following a single
                // instruction output that was not consumed downstream
                assert ($stable(o_compressed[0]));
                assert ($stable(o_inst0));
                if (o_count) begin
                    assert ($stable(o_compressed[1]));
                    assert ($stable(o_inst1));
                end
            end

            // TODO: liveness

            // cover different state transitions
            // waiting for memory -> serving instruction
            cover (f_past_valid && !$past(o_output_valid) && o_output_valid);
            // waiting for memory -> still waiting
            cover (f_past_valid && !$past(o_output_valid) && !o_output_valid);
            // serving instruction -> still serving the same one
            cover (f_past_valid && $past(o_output_valid) && o_past_valid && $stable(pc) && $stable(o_count) && $stable(o_inst0) && $stable(o_inst1));
            // back to back dual issue of different insts (100% throughput)
            cover (f_past_valid && $past(transmit) && $past(o_count) && transmit && o_count && !$stable(i_mem_rdata));
        end
    end
`endif
endmodule

`default_nettype wire
