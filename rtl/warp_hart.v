`default_nettype none

module warp_hart #(
    parameter RESET_ADDR = 64'h8000000000000000
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
    wire        decode_legal    [0:3];
    wire [14:0] decode_raddr    [0:3];
    wire [31:0] decode_imm      [0:3];
    wire [3:0]  decode_pipeline [0:3];
    wire [6:0]  decode_xarith   [0:3];
    wire [5:0]  decode_xlogic   [0:3];
    warp_udecode udecode [0:1] (
        .i_inst({if_uinst0, if_uinst1}),
        .o_legal(decode_valid[0:1]), .o_raddr(decode_raddr[0:1]),
        .o_imm(decode_imm[0:1]), .o_pipeline(decode_pipeline[0:1]),
        .o_xarith(decode_xarith[0:1]), .o_xlogic(decode_xlogic[0:1])
    );

    wire [64:0] decode_bundle [0:3];
    genvar i;
    generate
        for (i = 0; i < 4; i = i + 1)
            assign decode_bundle[i] = {decode_valid[i], decode_raddr[i], decode_imm[i], decode_pipeline[i], decode_xarith[i], decode_xlogic[i]};
    endgenerate

    wire [64:0] bundle0 = decode_bundle[bsel0];
    wire [64:0] bundle1 = decode_bundle[bsel1];
    wire [1:0] decode_valid;
    assign decode_valid[0] = if_valid;
    assign decode_valid[1] = if_valid; // TODO: not legal for branch?
endmodule

`default_nettype wire
