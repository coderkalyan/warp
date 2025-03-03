`default_nettype none

module warp_hart #(
    parameter RESET_ADDR = 39'h4000000000
) (
    input  wire i_clk,
    input  wire i_rst_n
);
    // instruction fetch
    wire        imem_ren, imem_valid;
    wire [38:0] imem_raddr;
    wire [63:0] imem_rdata;
    wire        if_valid, id_ready;
    wire [31:0] fetch_inst0, fetch_inst1;
    wire [1:0]  fetch_compressed;
    warp_fetch fetch (
        .i_clk(i_clk), .i_rst_n(i_rst_n),
        .o_imem_ren(imem_ren), .o_imem_raddr(imem_raddr),
        .i_imem_valid(imem_valid), .i_imem_rdata(imem_rdata),
        .o_output_valid(if_valid), .i_output_ready(id_valid),
        .o_inst0(fetch_inst0), .o_inst1(fetch_inst1),
        .o_compressed(fetch_compressed)
    );

    // IF/ID pipeline barrier
    reg [31:0] if_inst0, if_inst1;
    reg [1:0]  if_compressed;
    always @(posedge i_clk, negedge i_rst_n) begin
        if (!i_rst_n) begin
            if_inst0      <= 32'h0;
            if_inst1      <= 32'h0;
            if_compressed <= 2'b00;
        end else begin
            if_inst0      <= fetch_inst0;
            if_inst1      <= fetch_inst1;
            if_compressed <= fetch_compressed;
        end
    end

    // instruction decode
    wire [31:0] decode_inst0, decode_inst1;
    wire        id_valid, is_ready;
    wire [`BUNDLE_SIZE - 1:0] decode_bundle0, decode_bundle1;
    warp_decode decode (
        .i_clk(i_clk), .i_rst_n(i_rst_n),
        .o_input_ready(id_ready), .i_input_valid(if_valid),
        .i_inst0(if_inst0), .i_inst1(if_inst1),
        .i_compressed(if_compressed),
        .i_output_ready(is_ready), .o_output_valid(id_valid),
        .o_bundle0(decode_bundle0), .o_bundle1(decode_bundle1)
    );

    // ID/IS pipeline barrier
    reg [`BUNDLE_SIZE - 1:0] id_bundle0, id_bundle1;
    always @(posedge i_clk, negedge i_rst_n) begin
        if (!i_rst_n) begin
            id_bundle0 <= 0;
            id_bundle1 <= 0;
        end else begin
            id_bundle0 <= decode_bundle0;
            id_bundle1 <= decode_bundle1;
        end
    end
endmodule

`default_nettype wire
