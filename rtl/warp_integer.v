`default_nettype none

`define XARITH_OP_ADD 2'b00
`define XARITH_OP_SLT 2'b01
`define XARITH_OP_CMP 2'b10

`define XLOGIC_OP_AND 3'b000
`define XLOGIC_OP_OR  3'b001
`define XLOGIC_OP_XOR 3'b010
`define XLOGIC_OP_SHF 3'b011
`define XLOGIC_OP_SLA 3'b100
`define XLOGIC_OP_CLZ 3'b101
`define XLOGIC_OP_CTZ 3'b110
`define XLOGIC_OP_POP 3'b111

// scalar integer arithmetic unit - add/sub, set less than, min/max, branch
module warp_xarith (
    input  wire [63:0] i_op1,
    input  wire [63:0] i_op2,
    // `XARITH_OP_ADD: o_result = i_op1 +/- i_op2
    // `XARITH_OP_SLT: o_result = (i_op1 < i_op2) ? 1'b1 : 1'b0
    // `XARITH_OP_CMP: o_result = min/max(i_op1, i_op2)
    input  wire [1:0]  i_opsel,
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
    output wire [63:0] o_result,
    output wire        o_branch
);
    // add/sub
    wire [64:0] add_op1 = {i_op1[63], i_op1};
    wire [64:0] add_op2 = {i_op2[63], i_op2} & {65{i_sub}};
    wire [64:0] sum = add_op1 + add_op2 + i_sub;
    wire [63:0] add_result;
    assign add_result[63:32] = i_word ? {32{sum[31]}} : sum[63:32];
    assign add_result[31:0]  = sum[31:0];

    // comparison
    wire lt  = sum[63];
    wire ltu = sum[64];
    wire slt = i_unsigned ? ltu : lt;
    wire [63:0] slt_result = {63'h0, slt};

    // min/max
    wire cmp = slt ^ i_cmp_mode;
    wire [63:0] cmp_result = cmp ? i_op2 : i_op1;

    // branch
    wire eq = i_op1 == i_op2;
    wire branch = (i_branch_equal ? eq : slt) ^ i_branch_invert;

    reg [63:0] result;
    always @(*) begin
        result = 64'hx;

        case (i_opsel)
            `XARITH_OP_ADD: result = add_result;
            `XARITH_OP_SLT: result = slt_result;
            `XARITH_OP_CMP: result = cmp_result;
            default: result = 64'hx;
        endcase
    end

    assign o_branch = branch;
    assign o_result = result;
endmodule

module warp_xlogic (
    input  wire [63:0] i_op1,
    input  wire [63:0] i_op2,
    // `XLOGIC_OP_AND: o_result = i_op1 & i_op2
    // `XLOGIC_OP_OR : o_result = i_op1 | i_op2
    // `XLOGIC_OP_XOR: o_result = i_op1 ^ i_op2
    // `XLOGIC_OP_SHF: o_result = i_op1 <</>>/>>> i_op2
    // `XLOGIC_OP_SLA: o_result = (i_op1 << sll[1:0]) + i_op2
    // `XLOGIC_OP_CLZ: o_result = leadingzeros(i_op1)
    // `XLOGIC_OP_CTZ: o_result = trailingzeros(i_op1)
    // `XLOGIC_OP_POP: o_result = popcount(i_op1)
    input  wire [2:0]  i_opsel,
    // when asserted, invert (logical not) i_op2
    // implements andnot, ornot, and xnor
    // only used for OP_AND, OR_OR, OP_XOR
    input  wire        i_invert,
    // number of bits to shift i_op1 left by before adding i_op2
    // used for address generation (2/4/8 * base + offset)
    // only used for OP_SLA
    input  wire [1:0]  i_sll,
    // when asserted, operate on lower 32 bits only of i_op1 and i_op2 and
    // sign extend the result to 64 bits
    // only used for OP_SHF
    input  wire        i_word,
    output wire [63:0] o_result
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
            `XLOGIC_OP_SHF: result = shift_result;
            `XLOGIC_OP_SLA: result = sla_result;
            default: result = 64'hx;
        endcase
    end

    assign o_result = result;
endmodule

// TODO: while the interface to this register file is
// (mostly) correct, it currently will synthesize very
// poorly to FPGAs and needs to be internally reworked
module warp_xrf (
    input  wire        i_clk,
    input  wire [4:0]  i_rs1_addr,
    input  wire [4:0]  i_rs2_addr,
    input  wire [4:0]  i_rs3_addr,
    input  wire [4:0]  i_rs4_addr,
    input  wire [4:0]  i_rd1_addr,
    input  wire [4:0]  i_rd2_addr,
    input  wire [63:0] i_rd1_wdata,
    input  wire [63:0] i_rd2_wdata,
    input  wire        i_rd1_wen,
    input  wire        i_rd2_wen,
    output wire [63:0] o_rs1_rdata,
    output wire [63:0] o_rs2_rdata,
    output wire [63:0] o_rs3_rdata,
    output wire [63:0] o_rs4_rdata
);
    reg [63:0] file [30:0];
    reg [63:0] rs1_rdata, rs2_rdata; //, rs3_rdata, rs4_rdata;
    always @(posedge i_clk) begin
        begin
            rs1_rdata <= file[~i_rs1_addr];
            rs2_rdata <= file[~i_rs2_addr];
            rs3_rdata <= file[~i_rs3_addr];
            rs4_rdata <= file[~i_rs4_addr];

            if (i_rd1_wen)
                file[~i_rd1_addr] <= i_rd1_wdata;
            if (i_rd2_wen)
                file[~i_rd2_addr] <= i_rd2_wdata;
        end
    end

    assign o_rs1_rdata = rs1_rdata;
    assign o_rs2_rdata = rs2_rdata;
    assign o_rs3_rdata = rs3_rdata;
    assign o_rs4_rdata = rs4_rdata;
endmodule
