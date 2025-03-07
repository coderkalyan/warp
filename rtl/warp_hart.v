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

    wire        is_valid;
    wire [4:0]  rs1_addr, rs2_addr, rs3_addr, rs4_addr;
    wire [1:0]  xarith_opsel;
    wire        xarith_banksel, xarith_op2_sel;
    wire        xarith_sub, xarith_unsigned, xarith_cmp_mode, xarith_branch_equal;
    wire        xarith_branch_invert, xarith_word;
    wire [2:0]  xlogic_opsel;
    wire        xlogic_banksel, xlogic_op2_sel;
    wire        xlogic_invert, xlogic_word;
    wire [1:0]  xlogic_sll;
    wire [31:0] inst0_retire, inst1_retire;
    warp_issue issue (
        .i_clk(i_clk), .i_rst_n(i_rst_n),
        .o_input_ready(is_ready), .i_input_valid(is_valid),
        .i_bundle0(id_bundle0), .i_bundle1(id_bundle1),
        .o_rs1_addr(rs1_addr), .o_rs2_addr(rs2_addr),
        .o_rs3_addr(rs3_addr), .o_rs4_addr(rs4_addr),
        .o_xarith_banksel(xarith_banksel),
        .o_xarith_op2_sel(xarith_op2_sel),
        .o_xarith_opsel(xarith_opsel),
        .o_xarith_sub(xarith_sub),
        .o_xarith_unsigned(xarith_unsigned),
        .o_xarith_cmp_mode(xarith_cmp_mode),
        .o_xarith_branch_equal(xarith_branch_equal),
        .o_xarith_branch_invert(xarith_branch_invert),
        .o_xarith_word(xarith_word),
        .o_xlogic_banksel(xlogic_banksel),
        .o_xlogic_op2_sel(xlogic_op2_sel),
        .o_xlogic_opsel(xlogic_opsel),
        .o_xlogic_invert(xlogic_invert),
        .o_xlogic_sll(xlogic_sll),
        .o_xlogic_word(xlogic_word),
        .i_inst0_retire(inst0_retire),
        .i_inst1_retire(inst1_retire)
    );
endmodule

`default_nettype wire
