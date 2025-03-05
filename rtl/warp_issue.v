`default_nettype none

`include "warp_defines.v"

module warp_issue (
    input  wire        i_clk,
    input  wire        i_rst_n,
    output wire        o_input_ready,
    input  wire        i_input_valid,
    input  wire [`BUNDLE_SIZE - 1:0] i_bundle0,
    input  wire [`BUNDLE_SIZE - 1:0] i_bundle1,
    // interface to integer arithmetic pipeline 0
    output wire [63:0] o_xarith0_op1,
    output wire [63:0] o_xarith0_op2,
    output wire [63:0] o_xarith0_opsel,
    output wire [63:0] o_xarith0_sub,
    output wire [63:0] o_xarith0_unsigned,
    output wire [63:0] o_xarith0_cmp_mode,
    output wire [63:0] o_xarith0_branch_equal,
    output wire [63:0] o_xarith0_branch_invert,
    output wire [63:0] o_xarith0_word,
    // interface to integer arithmetic pipeline 1
    output wire [63:0] o_xarith1_op1,
    output wire [63:0] o_xarith1_op2,
    output wire [63:0] o_xarith1_opsel,
    output wire [63:0] o_xarith1_sub,
    output wire [63:0] o_xarith1_unsigned,
    output wire [63:0] o_xarith1_cmp_mode,
    output wire [63:0] o_xarith1_branch_equal,
    output wire [63:0] o_xarith1_branch_invert,
    output wire [63:0] o_xarith1_word,
    // interface to integer logic pipeline 0
    output wire [63:0] o_xlogic0_op1,
    output wire [63:0] o_xlogic0_op2,
    output wire [63:0] o_xlogic0_opsel,
    output wire [63:0] o_xlogic0_invert,
    output wire [63:0] o_xlogic0_sll,
    output wire [63:0] o_xlogic0_word,
    // interface to integer logic pipeline 1
    output wire [63:0] o_xlogic1_op1,
    output wire [63:0] o_xlogic1_op2,
    output wire [63:0] o_xlogic1_opsel,
    output wire [63:0] o_xlogic1_invert,
    output wire [63:0] o_xlogic1_sll,
    output wire [63:0] o_xlogic1_word,
    // interface to integer shift/rotate pipeline
    output wire [63:0] o_xshift_operand,
    output wire [63:0] o_xshift_amount,
    output wire [63:0] o_xshift_opsel,
    output wire [63:0] o_xshift_arithmetic,
    output wire [63:0] o_xshift_word
);
endmodule

`default_nettype wire
