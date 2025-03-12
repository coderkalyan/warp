`default_nettype none

`include "warp_defines.v"

// scalar integer arithmetic unit - add/sub, set less than, min/max, branch
module warp_xarith (
    input  wire [63:0] i_op1,
    input  wire [63:0] i_op2,
    // `XARITH_OP_ADD: o_result = i_op1 +/- i_op2
    // `XARITH_OP_SLT: o_result = (i_op1 < i_op2) ? 1'b1 : 1'b0
    // `XARITH_OP_CMP: o_result = min/max(i_op1, i_op2)
    input  wire [ 1:0] i_opsel,
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
    wire lt = sum[63];
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
    output wire [63:0] o_result
);
    // and/or with conditional invert of op2
    wire [63:0] op2 = i_op2 ^ {64{i_invert}};
    wire [63:0] and_result = i_op1 & op2;
    wire [63:0] or_result = i_op1 | op2;
    wire [63:0] xor_result = i_op1 ^ op2;  // i_op1 ^ ~i_op2 == i_op1 ~^ i_op2

    // shift left 1/2/3 (2 bits operand) + add (address generation)
    wire [63:0] sl1 = i_sll[1] ? {i_op1[61:0], 2'b00} : i_op1;
    wire [63:0] sl0 = i_sll[0] ? {sl1[62:0], 1'b0} : sl1;
    wire [63:0] sla_result = sl0 + i_op2;

    reg  [63:0] result;
    always @(*) begin
        result = 64'hx;

        case (i_opsel)
            `XLOGIC_OP_AND: result = and_result;
            `XLOGIC_OP_OR: result = or_result;
            `XLOGIC_OP_XOR: result = xor_result;
            `XLOGIC_OP_SHF: result = shift_result;
            `XLOGIC_OP_SLA: result = sla_result;
            default: result = 64'hx;
        endcase
    end

    assign o_result = result;
endmodule

// latency: 2 cycles
// throughput: 1 cpi
// since throughput and latency are fixed, this unit does not
// employ a "done" signal and expects the parent issue logic to
// expect a value with the given delay
module warp_xshift (
    input wire        i_clk,
    input wire        i_rst_n,
    input wire [63:0] i_operand,
    input wire [ 5:0] i_amount,

    // `XSHIFT_OP_SHL: o_result = i_operand << i_amount
    // `XSHIFT_OP_SHR: o_result = i_operand >>/>>> i_amount
    // `XSHIFT_OP_ROL: o_result = i_operand rol i_amount
    // `XSHIFT_OP_ROR: o_result = i_operand ror i_amount
    input wire [1:0] i_opsel,

    // if asserted, shift right arithmetic instead of logical (>>/>>>)
    // only used for OP_SHR
    input wire i_arithmetic,

    // when asserted, operate on lower 32 bits only of operands and
    // sign extend the result to 64 bits
    input  wire        i_word,
    output wire [63:0] o_result
);
    // Internal wires for each shift stage
    //stage out wires for each operation (shift right/left)
    // wire [63:0] stage0_out, stage1_out, stage2_out, stage3_out, stage4_out;
    wire [63:0] stage0_rol, stage1_rol, stage2_rol, stage3_rol, stage4_rol;
    wire [63:0] stage0_ror, stage1_ror, stage2_ror, stage3_ror, stage4_ror;
    wire [63:0] stage0_shl, stage1_shl, stage2_shl, stage3_shl, stage4_shl;
    wire [63:0] stage0_shr, stage1_shr, stage2_shr, stage3_shr, stage4_shr;
    // ...existing code... 
    wire [31:0] stage0_32_rotate, stage1_32_rotate, stage2_32_rotate, stage3_32_rotate, stage4_32_rotate;
    wire [63:0] operand_in;
    wire [63:0] o_result_tmp;  //result for 64 bit (shift & rotate) and 32 bit shift
    wire [63:0] out_rotated_32;  //result for 32 bit rotate

    //if i_word true between rotate or shift outputs for 32 bits, else select 64 bit 
    assign o_result = (i_word) ? (
        ((i_opsel == `XSHIFT_OP_ROL) | (i_opsel == `XSHIFT_OP_ROR)) ? rotated_32:
        {{32{o_result_tmp[31]}}, o_result_tmp[31:0]}
    ) : o_result_tmp;

    // sign extend for i_word before operation 
    // (use to help keep results signed extended for 32 bit shift left)
    assign operand_in = i_word ? {{32{i_operand[31]}}, i_operand[31:0]} : i_operand;

    // Barrel shifter stages
    // Stage 0: shift or rotate by 1
    assign stage0_shl = (i_amount[0]) ? ({operand_in[62:0], 1'b0}) : operand_in;
    assign stage0_shr = (i_amount[0]) ? ({(i_arithmetic & operand_in[63]), operand_in[63:1]}) : operand_in;
    assign stage0_rol = (i_amount[0]) ? ({operand_in[62:0], operand_in[63]}) : operand_in;
    assign stage0_ror = (i_amount[0]) ? ({operand_in[0], operand_in[63:1]}) : operand_in;

    // Stage 1: shift or rotate by 2
    assign stage1_shl = (i_amount[1]) ? ({stage0_shl[61:0], 2'b0}) : stage0_shl;
    assign stage1_shr = (i_amount[1]) ? ({{2{i_arithmetic & stage0_shr[63]}}, stage0_shr[63:2]}) : stage0_shr;
    assign stage1_rol = (i_amount[1]) ? ({stage0_rol[61:0], stage0_rol[63:62]}) : stage0_rol;
    assign stage1_ror = (i_amount[1]) ? ({stage0_ror[1:0], stage0_ror[63:2]}) : stage0_ror;

    // Stage 2: shift or rotate by 4
    assign stage2_shl = (i_amount[2]) ? ({stage1_shl[59:0], 4'b0}) : stage1_shl;
    assign stage2_shr = (i_amount[2]) ? ({{4{i_arithmetic & stage1_shr[63]}}, stage1_shr[63:4]}) : stage1_shr;
    assign stage2_rol = (i_amount[2]) ? ({stage1_rol[59:0], stage1_rol[63:60]}) : stage1_rol;
    assign stage2_ror = (i_amount[2]) ? ({stage1_ror[3:0], stage1_ror[63:4]}) : stage1_ror;

    // Stage 3: shift or rotate by 8
    assign stage3_shl = (i_amount[3]) ? ({stage2_shl[55:0], 8'b0}) : stage2_shl;
    assign stage3_shr = (i_amount[3]) ? ({{8{i_arithmetic & stage2_shr[63]}}, stage2_shr[63:8]}) : stage2_shr;
    assign stage3_rol = (i_amount[3]) ? ({stage2_rol[55:0], stage2_rol[63:56]}) : stage2_rol;
    assign stage3_ror = (i_amount[3]) ? ({stage2_ror[7:0], stage2_ror[63:8]}) : stage2_ror;

    // Stage 4: shift or rotate by 16
    assign stage4_shl = (i_amount[4]) ? ({stage3_shl[47:0], 16'b0}) : stage3_shl;
    assign stage4_shr = (i_amount[4]) ? ({{16{i_arithmetic & stage3_shr[63]}}, stage3_shr[63:16]}) : stage3_shr;
    assign stage4_rol = (i_amount[4]) ? ({stage3_rol[47:0], stage3_rol[63:48]}) : stage3_rol;
    assign stage4_ror = (i_amount[4]) ? ({stage3_ror[15:0], stage3_ror[63:16]}) : stage3_ror;

    // Stage 5: shift or rotate by 32
    assign stage5_shl = (i_amount[5] & ~i_word) ? ({stage4_shl[31:0], 32'b0}) : stage4_shl;
    assign stage5_shr = (i_amount[5] & ~i_word) ? ({{32{i_arithmetic & stage4_shr[63]}}, stage4_shr[63:32]}) : stage4_shr;
    assign stage5_rol = (i_amount[5]) ? ({stage4_rol[31:0], stage4_rol[63:32]}) : stage4_rol;
    assign stage5_ror = (i_amount[5]) ? ({stage4_ror[31:0], stage4_ror[63:32]}) : stage4_ror;

    // Select operation for final output
    assign o_result_tmp = 
        (i_opsel == `XSHIFT_OP_SHL) ? stage5_shl :
        (i_opsel == `XSHIFT_OP_SHR) ? stage5_shr :
        (i_opsel == `XSHIFT_OP_ROL) ? stage5_rol :
        stage5_ror;

    // Stage 0: rotate by 1 (32 bit)
    assign stage0_32_rotate = (i_amount[0]) ? (
        (i_opsel == `XSHIFT_OP_ROL) ? {operand_in[30:0], operand_in[31]} : // Rotate Left by 1
        {operand_in[0], operand_in[31:1]}  // Rotate Right by 1
        ) : operand_in;

    // Stage 1: rotate by 2 (32 bit)
    assign stage1_32_rotate = (i_amount[1]) ? (
        (i_opsel == `XSHIFT_OP_ROL) ? {stage0_32_rotate[29:0], stage0_32_rotate[31:30]} : // Rotate Left by 2
        {stage0_32_rotate[1:0], stage0_32_rotate[31:2]}  // Rotate Right by 2
        ) : stage0_32_rotate;

    // Stage 2: rotate by 4 (32 bit)
    assign stage2_32_rotate = (i_amount[2]) ? (
        (i_opsel == `XSHIFT_OP_ROL) ? {stage1_32_rotate[27:0], stage1_32_rotate[31:28]} : // Rotate Left by 4
        {stage1_32_rotate[3:0], stage1_32_rotate[31:4]}  // Rotate Right by 4
        ) : stage1_32_rotate;

    // Stage 3: rotate by 8 (32 bit)
    assign stage3_32_rotate = (i_amount[3]) ? (
        (i_opsel == `XSHIFT_OP_ROL) ? {stage2_32_rotate[23:0], stage2_32_rotate[31:24]} : // Rotate Left by 8
        {stage2_32_rotate[7:0], stage2_32_rotate[31:8]}  // Rotate Right by 8
        ) : stage2_32_rotate;

    // Stage 4: rotate by 16 (32 bit)
    assign stage4_32_rotate = (i_amount[4]) ? (
        (i_opsel == `XSHIFT_OP_ROL) ? {stage3_32_rotate[15:0], stage3_32_rotate[31:16]} : // Rotate Left by 16
        {stage3_32_rotate[15:0], stage3_32_rotate[31:16]}  // Rotate Right by 16
        ) : stage3_32_rotate;

    // Final output for 32 bit rotate
    assign rotated_32 = {{32{stage4_32_rotate[31]}}, stage4_32_rotate};
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
    input  wire [ 1:0] i_unsigned,
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
    input  wire [ 4:0] i_rs1_addr,
    input  wire [ 4:0] i_rs2_addr,
    input  wire [ 4:0] i_rs3_addr,
    input  wire [ 4:0] i_rs4_addr,
    input  wire [ 4:0] i_rd1_addr,
    input  wire [ 4:0] i_rd2_addr,
    input  wire [63:0] i_rd1_wdata,
    input  wire [63:0] i_rd2_wdata,
    input  wire        i_rd1_wen,
    input  wire        i_rd2_wen,
    output wire [63:0] o_rs1_rdata,
    output wire [63:0] o_rs2_rdata,
    output wire [63:0] o_rs3_rdata,
    output wire [63:0] o_rs4_rdata
);
    reg [63:0] file[30:0];
    reg [63:0] rs1_rdata, rs2_rdata, rs3_rdata, rs4_rdata;
    always @(posedge i_clk) begin
        begin
            // implement bypassing for all read ports, assumes
            // rd1 != rd2
            if (i_rd1_wen && (i_rs1_addr == i_rd1_addr)) rs1_rdata <= i_rd1_wdata;
            else if (i_rd2_wen && (i_rs1_addr == i_rd2_addr)) rs1_rdata <= i_rd2_wdata;
            else rs1_rdata <= file[~i_rs1_addr];

            if (i_rd1_wen && (i_rs2_addr == i_rd1_addr)) rs2_rdata <= i_rd1_wdata;
            else if (i_rd2_wen && (i_rs2_addr == i_rd2_addr)) rs2_rdata <= i_rd2_wdata;
            else rs2_rdata <= file[~i_rs2_addr];

            if (i_rd1_wen && (i_rs3_addr == i_rd1_addr)) rs3_rdata <= i_rd1_wdata;
            else if (i_rd2_wen && (i_rs3_addr == i_rd2_addr)) rs3_rdata <= i_rd2_wdata;
            else rs3_rdata <= file[~i_rs3_addr];

            if (i_rd1_wen && (i_rs4_addr == i_rd1_addr)) rs4_rdata <= i_rd1_wdata;
            else if (i_rd2_wen && (i_rs4_addr == i_rd2_addr)) rs4_rdata <= i_rd2_wdata;
            else rs4_rdata <= file[~i_rs4_addr];

            if (i_rd1_wen) file[~i_rd1_addr] <= i_rd1_wdata;
            if (i_rd2_wen) file[~i_rd2_addr] <= i_rd2_wdata;
        end
    end

    assign o_rs1_rdata = rs1_rdata;
    assign o_rs2_rdata = rs2_rdata;
    assign o_rs3_rdata = rs3_rdata;
    assign o_rs4_rdata = rs4_rdata;
endmodule
