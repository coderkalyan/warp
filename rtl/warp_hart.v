`default_nettype none

module warp_hart #(
    parameter RESET_ADDR = 64'h0000000000000000
) (
    input  wire i_clk,
    input  wire i_rst_n
);
    // instruction fetch
    wire [63:0] branch_target;
    wire        branch_target_valid;
    wire        id_ready, if_valid;
    wire [31:0] fetch_inst0, fetch_inst1;
    wire [1:0]  fetch_compressed;
    wire        fetch_count;
    warp_fetch fetch (
        .i_clk(i_clk), .i_rst_n(i_rst_n),
        .i_branch_target(branch_target), .i_branch_valid(branch_target_valid),
        .i_output_ready(id_ready), .o_output_valid(if_valid),
        .o_inst0(fetch_inst0), .o_inst1(fetch_inst1),
        .o_compressed(fetch_compressed), .o_count(fetch_count)
    );

    // IF/ID pipeline barrier
    reg [31:0] if_inst0, if_inst1;
    reg [1:0]  if_compressed;
    reg        if_count;
    always @(posedge i_clk, negedge i_rst_n) begin
        if (!i_rst_n) begin
            if_inst0      <= 32'h0;
            if_inst1      <= 32'h0;
            if_compressed <= 2'b00;
            if_count      <= 1'b0;
        end else begin
            if_inst0      <= fetch_inst0;
            if_inst1      <= fetch_inst1;
            if_compressed <= fetch_compressed;
            if_count      <= fetch_count;
        end
    end

    // instruction decode
endmodule

`default_nettype wire
