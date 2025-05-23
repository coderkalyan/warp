`default_nettype none

// `include "warp_defines.v"

`define XSHIFT_OP_SHL 2'b00
`define XSHIFT_OP_SHR 2'b01
`define XSHIFT_OP_ROL 2'b10
`define XSHIFT_OP_ROR 2'b11

// scalar integer arithmetic unit - add/sub, set less than, min/max, branch
// latency: 1 cycle
// initiation interval: 1 cycle
module warp_xarith (
    input  wire        i_clk,
    input  wire        i_rst_n,
    // when asserted, the unit with start an arithmetic operation with the
    // given operands and selected operation
    input  wire        i_valid,
    input  wire [63:0] i_op1,
    input  wire [63:0] i_op2,
    // destination register is passed through the execution unit to track
    // the write back location, but is not used or modified by this unit
    input  wire [ 4:0] i_rd,
    // pc of current instruction is used to calculate branch target address
    // when conditional branches and unconditional direct jumps are taken
    input  wire [63:0] i_pc_rdata,
    // pc of next instruction is used to calculate branch target address
    // when conditional branches are not taken as well as link address
    // for linking jumps (jal, jalr)
    input  wire [63:0] i_pc_wdata,
    // for pc-relative branch and jump instructions, this contains the offset
    // to compute the branch target address
    input  wire [63:0] i_branch_offset,
    // `XARITH_OP_ADD: o_result = i_op1 +/- i_op2
    // `XARITH_OP_SLT: o_result = (i_op1 < i_op2) ? 1'b1 : 1'b0
    // `XARITH_OP_CMP: o_result = min/max(i_op1, i_op2)
    // `XARITH_OP_BRANCH: o_result = undefined, branch calculation enabled
    input  wire [ 2:0] i_opsel,
    // subtract mode: when asserted, negate i_op2 before adding
    // only used for OP_ADD
    input  wire        i_sub,
    // unsigned: treat i_op1 and i_op2 as unsigned numbers for comparison
    // only used for OP_SLT, OP_CMP, and branch comparison
    input  wire        i_unsigned,
    // comparison mode: when asserted, min, otherwise max
    // only used for OP_CMP
    input  wire        i_cmp_mode,
    // if asserted, branch resolution compares (in)equality
    // if not, compares less than (unsigned)
    input  wire        i_branch_equal,
    // if asserted, branch resolution negates the comparison
    // eq  -> ne
    // lt  -> ge
    // ltu -> geu
    input  wire        i_branch_invert,
    // when asserted, operate on lower 32 bits only of i_op1 and i_op2 and
    // sign extend the result to 64 bits
    // only used for OP_ADD
    input  wire        i_word,
`ifdef RISCV_FORMAL
    `RVFI_METADATA_INPUTS(),
    `RVFI_PC_INPUTS(),
    `RVFI_REG_INPUTS(),
    `RVFI_METADATA_OUTPUTS(),
    `RVFI_PC_OUTPUTS(),
    `RVFI_REG_OUTPUTS(),
`endif
    // when asserted, o_result contains the result of the arithmetic
    // operation issued on the previous cycle and o_branch is asserted
    // if a branch operation was issued and the branch was taken
    output wire        o_valid,
    // contains the result of the arithmetic operation issued previous cycle
    // this includes arithmetic and comparison operations as well as linking
    // jumps (jal, jalr)
    output wire [63:0] o_result,
    // if the issued operation is a branch or jump and the branch should be
    // taken, this signal is asserted
    // since the branch target is calculated internally, this is primarily
    // used to verify and update the branch predictor
    output wire        o_branch,
    // if the issued operation is a branch or jump, this instruction contains
    // the branch target address (next logical program counter value)
    output wire [63:0] o_branch_target,
    // the destination register is passed through from i_rd and output in sync
    // with o_valid and o_result. it is not modified internally but is used to
    // determine which register to write to in write back
    output wire [ 4:0] o_rd
);
    // add/sub
    wire [64:0] add_op1 = {i_op1[63] & ~i_unsigned, i_op1};
    wire [64:0] add_op2 = {i_op2[63] & ~i_unsigned, i_op2} ^ {65{i_sub}};
    wire [64:0] sum = add_op1 + add_op2 + i_sub;
    wire [63:0] add_result;
    assign add_result[63:32] = i_word ? {32{sum[31]}} : sum[63:32];
    assign add_result[31:0]  = sum[31:0];

    // comparison
    wire slt = sum[64];
    wire [63:0] slt_result = {63'h0, slt};

    // min/max
    wire cmp = slt ^ i_cmp_mode;
    wire [63:0] cmp_result = cmp ? i_op2 : i_op1;

    // branch
    wire eq = i_op1 == i_op2;
    wire branch_en = (i_opsel == `XARITH_OP_BRANCH) || (i_opsel == `XARITH_OP_JAL) || (i_opsel == `XARITH_OP_JALR);
    (* keep *) wire branch = branch_en && ((i_branch_equal ? eq : slt) ^ i_branch_invert);

    reg [63:0] result;
    always @(*) begin
        result = 64'hx;

        case (i_opsel)
            `XARITH_OP_ADD: result  = add_result;
            `XARITH_OP_SLT: result  = slt_result;
            `XARITH_OP_CMP: result  = cmp_result;
            `XARITH_OP_JAL: result  = i_pc_wdata;
            `XARITH_OP_JALR: result = i_pc_wdata;
            default: result = 64'hx;
        endcase
    end

    wire [63:0] branch_address = i_pc_rdata + i_branch_offset;

    reg [63:0] branch_target;
    always @(*) begin
        branch_target = 64'hx;
        case (i_opsel)
            `XARITH_OP_BRANCH: branch_target = branch ? branch_address : i_pc_wdata;
            `XARITH_OP_JAL:    branch_target = add_result;
            `XARITH_OP_JALR:   branch_target = {add_result[63:1], 1'b0};
        endcase
    end

`ifdef RISCV_FORMAL
    // the formal interface calculates essentially the same branch target
    // address but based on the formal pc data, which should be equivalent
    // FIXME: this is doing too much work, we should use the normal
    // branch_target calculation and also phase out the formal pc data
    wire [63:0] f_branch_address = if_pc_rdata + i_branch_offset;
    reg [63:0] f_pc_wdata;
    always @(*) begin
        f_pc_wdata = if_pc_wdata;
        if ((i_opsel == `XARITH_OP_BRANCH) && branch)
            f_pc_wdata = f_branch_address;
        else if (i_opsel == `XARITH_OP_JAL)
            f_pc_wdata = add_result;
        else if (i_opsel == `XARITH_OP_JALR)
            f_pc_wdata = {add_result[63:1], 1'b0};
    end

    // FIXME: we should probably remove this from the formal interface
    // and put it in the main datapath so we can actually trap on
    // illegal branches (and other illegal instructions)
    // FIXME: once this illegal address trap causes either a real trap or
    // a halt in fetch, we can change this expression to only use
    // branch_taken_address but for now we check the whole target (but only
    // for branches)
    // wire f_xarith_trap = f_xarith_trap_tmp || (xarith_branch && branch_taken_address[0]);
    wire f_trap = if_trap || (branch_en && f_pc_wdata[0]);
`endif

    // integer arithmetic is a single cycle synchronous unit
    // so register the calculated values one cycle
    reg        r_valid;
    reg [63:0] r_result;
    reg        r_branch;
    reg [63:0] r_branch_target;
    reg [4:0]  r_rd;
    always @(posedge i_clk, negedge i_rst_n) begin
        if (!i_rst_n) begin
            r_valid <= 1'b0;
            r_result <= 64'h0;
            r_branch <= 1'b0;
            r_branch_target <= 64'h0;
            r_rd <= 5'd0;
        end else begin
            r_valid <= i_valid;
            r_result <= result;
            r_branch <= branch;
            r_branch_target <= branch_target;
            r_rd <= i_rd;
        end
    end

    assign o_valid         = r_valid;
    assign o_result        = r_result;
    assign o_rd            = r_rd;
    assign o_branch        = r_branch;
    assign o_branch_target = r_branch_target;

`ifdef RISCV_FORMAL
    reg        rf_valid;
    reg [63:0] rf_order;
    reg [31:0] rf_insn;
    reg        rf_trap;
    reg        rf_halt;
    reg        rf_intr;
    reg [ 1:0] rf_mode;
    reg [ 1:0] rf_ixl;
    reg [63:0] rf_pc_rdata;
    reg [63:0] rf_pc_wdata;
    reg [ 4:0] rf_rs1_addr;
    reg [ 4:0] rf_rs2_addr;
    reg [63:0] rf_rs1_rdata;
    reg [63:0] rf_rs2_rdata;
    reg [ 4:0] rf_rd_addr;
    reg [63:0] rf_rd_wdata;
    always @(posedge i_clk, negedge i_rst_n) begin
        if (!i_rst_n) begin
            rf_valid       <= 1'b0;
            rf_order       <= 64'h0;
            rf_insn        <= 32'h0;
            rf_trap        <= 1'b0;
            rf_halt        <= 1'b0;
            rf_intr        <= 1'b0;
            rf_mode        <= 2'b0;
            rf_ixl         <= 2'b0;
            rf_pc_rdata    <= 64'h0;
            rf_pc_wdata    <= 64'h0;
            rf_rs1_addr    <= 5'h0;
            rf_rs2_addr    <= 5'h0;
            rf_rs1_rdata   <= 64'h0;
            rf_rs2_rdata   <= 64'h0;
            rf_rd_addr     <= 5'h0;
            rf_rd_wdata    <= 64'h0;
        end else begin
            rf_valid       <= if_valid;
            rf_order       <= if_order;
            rf_insn        <= if_insn;
            rf_trap        <= f_trap;
            rf_halt        <= if_halt;
            rf_intr        <= if_intr;
            rf_mode        <= if_mode;
            rf_ixl         <= if_ixl;
            rf_pc_rdata    <= if_pc_rdata;
            rf_pc_wdata    <= f_pc_wdata;
            rf_rs1_addr    <= if_rs1_addr;
            rf_rs2_addr    <= if_rs2_addr;
            rf_rs1_rdata   <= if_rs1_rdata;
            rf_rs2_rdata   <= if_rs2_rdata;
            rf_rd_addr     <= if_rd_addr;
            rf_rd_wdata    <= (if_rd_addr == 32'd0) ? 64'd0 : result;
        end
    end

    assign of_valid       = rf_valid;
    assign of_order       = rf_order;
    assign of_insn        = rf_insn;
    assign of_trap        = rf_trap;
    assign of_halt        = rf_halt;
    assign of_intr        = rf_intr;
    assign of_mode        = rf_mode;
    assign of_ixl         = rf_ixl;
    assign of_pc_rdata    = rf_pc_rdata;
    assign of_pc_wdata    = rf_pc_wdata;
    assign of_rs1_addr    = rf_rs1_addr;
    assign of_rs2_addr    = rf_rs2_addr;
    assign of_rs1_rdata   = rf_rs1_rdata;
    assign of_rs2_rdata   = rf_rs2_rdata;
    assign of_rd_addr     = rf_rd_addr;
    assign of_rd_wdata    = rf_rd_wdata;
`endif
endmodule

module warp_xlogic (
    input  wire        i_clk,
    input  wire        i_rst_n,
    // when asserted, the unit with start a logical operation with the
    // given operands and selected operation
    input  wire        i_valid,
    input  wire [63:0] i_op1,
    input  wire [63:0] i_op2,
    // destination register is passed through the execution unit to track
    // the write back location, but is not used or modified by this unit
    input  wire [ 4:0] i_rd,
    // `XLOGIC_OP_AND: o_result = i_op1 & i_op2
    // `XLOGIC_OP_OR : o_result = i_op1 | i_op2
    // `XLOGIC_OP_XOR: o_result = i_op1 ^ i_op2
    // `XLOGIC_OP_SHF: o_result = i_op1 <</>>/>>> i_op2
    // `XLOGIC_OP_SLA: o_result = (i_op1 << sll[1:0]) + i_op2
    // `XLOGIC_OP_CLZ: o_result = leadingzeros(i_op1)
    // `XLOGIC_OP_CTZ: o_result = trailingzeros(i_op1)
    // `XLOGIC_OP_POP: o_result = popcount(i_op1)
    input  wire [ 2:0] i_opsel,
    // when asserted, invert (logical not) i_op2
    // implements andnot, ornot, and xnor
    // only used for OP_AND, OR_OR, OP_XOR
    input  wire        i_invert,
    // number of bits to shift i_op1 left by before adding i_op2
    // used for address generation (2/4/8 * base + offset)
    // only used for OP_SLA
    input  wire [ 1:0] i_sll,
    // when asserted, operate on lower 32 bits only of i_op1 and i_op2 and
    // sign extend the result to 64 bits
    // only used for OP_SHF
    input  wire        i_word,
`ifdef RISCV_FORMAL
    `RVFI_METADATA_INPUTS(),
    `RVFI_PC_INPUTS(),
    `RVFI_REG_INPUTS(),
    `RVFI_METADATA_OUTPUTS(),
    `RVFI_PC_OUTPUTS(),
    `RVFI_REG_OUTPUTS(),
`endif
    // when asserted, o_result contains the result of the logical
    // operation issued on the previous cycle
    output wire        o_valid,
    output wire [63:0] o_result,
    // the destination register is passed through from i_rd and output in sync
    // with o_valid and o_result. it is not modified internally but is used to
    // determine which register to write to in write back
    output wire [ 4:0] o_rd
);
    // and/or with conditional invert of op2
    wire [63:0] op2 = i_op2 ^ {64{i_invert}};
    wire [63:0] and_result = i_op1 & op2;
    wire [63:0] or_result  = i_op1 | op2;
    wire [63:0] xor_result = i_op1 ^ op2; // i_op1 ^ ~i_op2 == i_op1 ~^ i_op2

    // shift left 1/2/3 (2 bits operand) + add (address generation)
    wire [63:0] sl1 = i_sll[1] ? {i_op1[61:0], 2'b00} : i_op1;
    wire [63:0] sl0 = i_sll[0] ? {sl1[62:0], 1'b0} : sl1;
    wire [63:0] sla_result = sl0 + i_op2;

    reg [63:0] result;
    always @(*) begin
        result = 64'hx;

        case (i_opsel)
            `XLOGIC_OP_AND: result = and_result;
            `XLOGIC_OP_OR:  result = or_result;
            `XLOGIC_OP_XOR: result = xor_result;
            // `XLOGIC_OP_SHF: result = shift_result;
            `XLOGIC_OP_SLA: result = sla_result;
            default: result = 64'hx;
        endcase
    end

    reg        r_valid;
    reg [63:0] r_result;
    reg [4:0]  r_rd;
    always @(posedge i_clk, negedge i_rst_n) begin
        if (!i_rst_n) begin
            r_valid <= 1'b0;
            r_result <= 64'h0;
            r_rd <= 5'd0;
        end else begin
            r_valid <= i_valid;
            r_result <= result;
            r_rd <= i_rd;
        end
    end

    assign o_valid  = r_valid;
    assign o_result = r_result;
    assign o_rd     = r_rd;

`ifdef RISCV_FORMAL
    reg        rf_valid;
    reg [63:0] rf_order;
    reg [31:0] rf_insn;
    reg        rf_trap;
    reg        rf_halt;
    reg        rf_intr;
    reg [ 1:0] rf_mode;
    reg [ 1:0] rf_ixl;
    reg [63:0] rf_pc_rdata;
    reg [63:0] rf_pc_wdata;
    reg [ 4:0] rf_rs1_addr;
    reg [ 4:0] rf_rs2_addr;
    reg [63:0] rf_rs1_rdata;
    reg [63:0] rf_rs2_rdata;
    reg [ 4:0] rf_rd_addr;
    reg [63:0] rf_rd_wdata;
    always @(posedge i_clk, negedge i_rst_n) begin
        if (!i_rst_n) begin
            rf_valid       <= 1'b0;
            rf_order       <= 64'h0;
            rf_insn        <= 32'h0;
            rf_trap        <= 1'b0;
            rf_halt        <= 1'b0;
            rf_intr        <= 1'b0;
            rf_mode        <= 2'b0;
            rf_ixl         <= 2'b0;
            rf_pc_rdata    <= 64'h0;
            rf_pc_wdata    <= 64'h0;
            rf_rs1_addr    <= 5'h0;
            rf_rs2_addr    <= 5'h0;
            rf_rs1_rdata   <= 64'h0;
            rf_rs2_rdata   <= 64'h0;
            rf_rd_addr     <= 5'h0;
            rf_rd_wdata    <= 64'h0;
        end else begin
            rf_valid       <= if_valid;
            rf_order       <= if_order;
            rf_insn        <= if_insn;
            rf_trap        <= if_trap;
            rf_halt        <= if_halt;
            rf_intr        <= if_intr;
            rf_mode        <= if_mode;
            rf_ixl         <= if_ixl;
            rf_pc_rdata    <= if_pc_rdata;
            rf_pc_wdata    <= if_pc_wdata;
            rf_rs1_addr    <= if_rs1_addr;
            rf_rs2_addr    <= if_rs2_addr;
            rf_rs1_rdata   <= if_rs1_rdata;
            rf_rs2_rdata   <= if_rs2_rdata;
            rf_rd_addr     <= if_rd_addr;
            rf_rd_wdata    <= (if_rd_addr == 32'd0) ? 64'd0 : result;
        end
    end

    assign of_valid       = rf_valid;
    assign of_order       = rf_order;
    assign of_insn        = rf_insn;
    assign of_trap        = rf_trap;
    assign of_halt        = rf_halt;
    assign of_intr        = rf_intr;
    assign of_mode        = rf_mode;
    assign of_ixl         = rf_ixl;
    assign of_pc_rdata    = rf_pc_rdata;
    assign of_pc_wdata    = rf_pc_wdata;
    assign of_rs1_addr    = rf_rs1_addr;
    assign of_rs2_addr    = rf_rs2_addr;
    assign of_rs1_rdata   = rf_rs1_rdata;
    assign of_rs2_rdata   = rf_rs2_rdata;
    assign of_rd_addr     = rf_rd_addr;
    assign of_rd_wdata    = rf_rd_wdata;
`endif
endmodule

// latency: 2 cycles
// throughput: 1 cpi
// since throughput and latency are fixed, this unit does not
// employ a "done" signal and expects the parent issue logic to
// expect a value with the given delay
module warp_xshift (
    input  wire        i_clk,
    input  wire        i_rst_n,
    input  wire [63:0] i_operand,
    input  wire [5:0]  i_amount,
    // `XSHIFT_OP_SHL: o_result = i_operand << i_amount
    // `XSHIFT_OP_SHR: o_result = i_operand >>/>>> i_amount
    // `XSHIFT_OP_ROL: o_result = i_operand rol i_amount
    // `XSHIFT_OP_ROR: o_result = i_operand ror i_amount
    input  wire [1:0]  i_opsel,
    // if asserted, shift right arithmetic instead of logical (>>/>>>)
    // only used for OP_SHR
    input  wire        i_arithmetic,
    // when asserted, operate on lower 32 bits only of operands and
    // sign extend the result to 64 bits
    input  wire        i_word,
    output wire [63:0] o_result
);
endmodule

// multiplies two 64 bit operands and outputs the lower 64 bits of
// the result
// latency: 1 - 2 cycles
// throughput: 1 cpi
module warp_xmultl (
    input  wire        i_clk,
    input  wire        i_rst_n,
    // multiplication is performed when valid is asserted
    input  wire        i_valid,
    input  wire [63:0] i_op1,
    input  wire [63:0] i_op2,
    // when asserted, operate on lower 32 bits of operands and
    // sign extend the result to 64 bits
    // 32 bit operations take 1 cycle, while 64 bit operations
    // take 2 cycles
    input  wire        i_word,
    // when asserted, o_result contains the result of the most
    // recently completed multiply
    output wire        o_valid,
    output wire [63:0] o_result
);
endmodule

// multiplies two 64 bit operands and outputs the upper 64 bits of
// the result
// latency: 2 cycles
// throughput: 1 cpi
module warp_xmulth (
    input  wire        i_clk,
    input  wire        i_rst_n,
    // multiplication is performed when valid is asserted
    input  wire        i_valid,
    input  wire [63:0] i_op1,
    input  wire [63:0] i_op2,
    // when asserted, the corresponding operand is treated
    // as unsigned instead of signed
    // this is used to implement mulhu and mulhsu
    input  wire [1:0]  i_unsigned,
    // when asserted, o_result contains the result of the most
    // recently completed multiply
    output wire        o_valid,
    output wire [63:0] o_result
);
endmodule

// divides two 64 bit operands and outputs the quotient
// and remainder of the result
// latency: varied
// throughput: 1 / latency
module warp_xdiv (
    input  wire        i_clk,
    input  wire        i_rst_n,
    // division is performed when valid and ready are asserted
    // this handshake is necessary because the divider does not
    // have a throughput of 1 cpi, and the state machine must
    // complete a varied latency operation before accepting another
    input  wire        i_input_valid,
    output wire        o_input_ready,
    input  wire [63:0] i_op1,
    input  wire [63:0] i_op2,
    // when asserted, operands are treated as unsigned
    input  wire        i_unsigned,
    // when asserted, operate on lower 32 bits of operands and
    // sign extend the result to 64 bits
    input  wire        i_word,
    // when asserted, o_quotient and o_remainder contain the result
    // of the completed division operation
    // a full ready/valid handshake is not necessary here because it
    // is assumed the writeback stage can always accept output data
    // and will buffer it externally as necessary
    output wire        o_valid,
    output wire [63:0] o_quotient,
    output wire [63:0] o_remainder
);
endmodule

// TODO: while the interface to this register file is
// (mostly) correct, it currently will synthesize very
// poorly to FPGAs and needs to be internally reworked
module warp_xrf (
    input  wire        i_clk,
    input  wire        i_rst_n,
    // 4 port synchronous read
    input  wire [4:0]  i_rs1_addr,
    input  wire [4:0]  i_rs2_addr,
    input  wire [4:0]  i_rs3_addr,
    input  wire [4:0]  i_rs4_addr,
    output wire [63:0] o_rs1_rdata,
    output wire [63:0] o_rs2_rdata,
    output wire [63:0] o_rs3_rdata,
    output wire [63:0] o_rs4_rdata,
    // 2 port synchronous write with enable
    input  wire        i_rd1_wen,
    input  wire        i_rd2_wen,
    input  wire [4:0]  i_rd1_addr,
    input  wire [4:0]  i_rd2_addr,
    input  wire [63:0] i_rd1_wdata,
    input  wire [63:0] i_rd2_wdata
);
    reg [63:0] file [31:0];
    reg [63:0] rs1_rdata, rs2_rdata, rs3_rdata, rs4_rdata;
    integer i;
    always @(posedge i_clk, negedge i_rst_n) begin
        if (!i_rst_n) begin
            for (i = 0; i < 31; i = i + 1)
                file[i] <= 64'h0;
        end else begin
            // implement bypassing for all read ports, assumes
            // rd1 != rd2
            if (i_rd1_wen && (i_rs1_addr == i_rd1_addr) && (i_rd1_addr != 5'd0))
                rs1_rdata <= i_rd1_wdata;
            else if (i_rd2_wen && (i_rs1_addr == i_rd2_addr) && (i_rd2_addr != 5'd0))
                rs1_rdata <= i_rd2_wdata;
            else
                rs1_rdata <= file[i_rs1_addr];

            if (i_rd1_wen && (i_rs2_addr == i_rd1_addr) && (i_rd1_addr != 5'd0))
                rs2_rdata <= i_rd1_wdata;
            else if (i_rd2_wen && (i_rs2_addr == i_rd2_addr) && (i_rd2_addr != 5'd0))
                rs2_rdata <= i_rd2_wdata;
            else
                rs2_rdata <= file[i_rs2_addr];

            if (i_rd1_wen && (i_rs3_addr == i_rd1_addr) && (i_rd1_addr != 5'd0))
                rs3_rdata <= i_rd1_wdata;
            else if (i_rd2_wen && (i_rs3_addr == i_rd2_addr) && (i_rd2_addr != 5'd0))
                rs3_rdata <= i_rd2_wdata;
            else
                rs3_rdata <= file[i_rs3_addr];

            if (i_rd1_wen && (i_rs4_addr == i_rd1_addr) && (i_rd1_addr != 5'd0))
                rs4_rdata <= i_rd1_wdata;
            else if (i_rd2_wen && (i_rs4_addr == i_rd2_addr) && (i_rd2_addr != 5'd0))
                rs4_rdata <= i_rd2_wdata;
            else
                rs4_rdata <= file[i_rs4_addr];

            if (i_rd1_wen && (i_rd1_addr != 5'd0))
                file[i_rd1_addr] <= i_rd1_wdata;
            if (i_rd2_wen && (i_rd2_addr != 5'd0))
                file[i_rd2_addr] <= i_rd2_wdata;
        end
    end

    assign o_rs1_rdata = rs1_rdata;
    assign o_rs2_rdata = rs2_rdata;
    assign o_rs3_rdata = rs3_rdata;
    assign o_rs4_rdata = rs4_rdata;
endmodule
