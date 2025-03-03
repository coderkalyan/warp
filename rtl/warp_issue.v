`default_nettype none

`include "warp_defines.v"

module warp_issue (
    input  wire        i_clk,
    input  wire        i_rst_n,
    output wire        o_input_ready,
    input  wire        i_input_valid,
    input  wire [`BUNDLE_SIZE - 1:0] i_bundle0,
    input  wire [`BUNDLE_SIZE - 1:0] i_bundle1,
);

`default_nettype wire
