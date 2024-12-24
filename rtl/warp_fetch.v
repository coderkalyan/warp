`default_nettype none

module warp_fetch #(
    parameter RESET_ADDR = 64'h0000000000000000
) (
    input  wire i_clk,
    input  wire i_rst_n,
);

`default_nettype wire
