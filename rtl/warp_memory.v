`default_nettype none

`define WIDTH_BYTE   2'b00
`define WIDTH_HALF   2'b01
`define WIDTH_WORD   2'b10
`define WIDTH_DOUBLE 2'b11

`define LSU_OP_READ  1'b0
`define LSU_OP_WRITE 1'b1

module warp_lsu (
    input  wire        i_clk,
    input  wire        i_rst_n,
    input  wire        i_valid,
    input  wire        i_opsel,
    input  wire [63:0] i_base,
    input  wire [31:0] i_offset,
    input  wire [1:0]  i_width,
    input  wire        i_unsigned,
    input  wire [63:0] i_wdata,
    output wire        o_ready,
    output wire        o_fault,
    output wire [63:0] o_rdata
);
    // effective address (base + signed offset)
    wire [63:0] next_addr = i_base + {{32{i_offset[31]}}, i_offset};

    // alignment based on width
    wire [2:0] align_mask = {i_width == `WIDTH_DOUBLE, i_width == `WIDTH_DOUBLE || i_width == `WIDTH_WORD, i_width != `WIDTH_BYTE};
    wire aligned = (mem_addr[2:0] & align_mask) == 3'b000;

    reg [2:0] state, next_state;
    always @(posedge i_clk, negedge i_rst_n) begin
        if (!i_rst_n)
            state <= `STATE_IDLE;
        else
            state <= next_state;
    end

    always @(*) begin
        next_state = state;
    end
endmodule
