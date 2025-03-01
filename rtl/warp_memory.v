`default_nettype none

`define WIDTH_BYTE   2'b00
`define WIDTH_HALF   2'b01
`define WIDTH_WORD   2'b10
`define WIDTH_DOUBLE 2'b11

`define LSU_OP_READ  1'b0
`define LSU_OP_WRITE 1'b1

module warp_icache (
    input  wire        i_clk,
    input  wire        i_rst_n,
    // interface to fetch unit
    output wire        o_req_ready,
    input  wire        i_req_valid,
    input  wire [33:0] i_req_raddr,
    output wire        o_res_valid,
    input  wire        i_res_ready,
    output wire [63:0] i_res_rdata,
    // AHB5 interface (manager) to memory
    input  wire        o_ahb_hclk,
    input  wire        o_ahb_hreset_n,
    output wire [33:0] o_ahb_haddr,
    output wire [2:0]  o_ahb_hburst,
    output wire        o_ahb_hmastlock,
    output wire [3:0]  o_ahb_hprot,
    output wire [2:0]  o_ahb_hsize,
    output wire        o_ahb_hnonsec,
    output wire        o_ahb_hexcl,
    output wire [1:0]  o_ahb_htrans,
    output wire [63:0] o_ahb_hwdata,
    output wire [7:0]  o_ahb_hwstrb,
    output wire        o_ahb_hwrite,
    input  wire [63:0] i_ahb_hrdata,
    input  wire        i_ahb_hreadyout,
    input  wire        i_ahb_hresp,
    input  wire        i_ahb_hexokay
);
    localparam O = 6;            // 6 bit offset => 64 byte cache line
    localparam S = 8;            // 2 bit set index => 4 way set associative
    localparam T = 34 - O - S;   // 20 bit tag
    localparam D = 8 * (2 ** O); // 8 * 64 data bits per line
    localparam V = 1;            // 1 valid bit per line
    localparam DEPTH = 2 ** S;   // 256 sets * 4 ways per set * 64 bytes per way = 64K cache

    reg [T + D - 1:0] way0 [DEPTH - 1:0];
    reg [T + D - 1:0] way1 [DEPTH - 1:0];
    reg [T + D - 1:0] way2 [DEPTH - 1:0];
    reg [T + D - 1:0] way3 [DEPTH - 1:0];
    reg [3:0] valid [DEPTH - 1:0];

    // always @(posedge i_clk, negedge i_rst_n) begin
    //     if (i_rst_n) begin
    //     end else begin
    //     end
    // end
endmodule

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
