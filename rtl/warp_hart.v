`default_nettype none

`timescale 1ns/100ps

module warp_hart #(
    parameter RESET_ADDR = 39'h4000000000
) (
    input  wire        i_clk,
    input  wire        i_rst_n,
    output wire        o_imem_ren,
    output wire [38:0] o_imem_raddr,
    input  wire        i_imem_valid,
    input  wire [63:0] i_imem_rdata
);
    // instruction fetch
    wire        imem_ren, imem_valid;
    wire [38:0] imem_raddr;
    wire [63:0] imem_rdata;
    wire        fetch_valid, decode_ready;
    wire [31:0] fetch_inst0, fetch_inst1;
    wire [1:0]  fetch_compressed;
    warp_fetch fetch (
        .i_clk(i_clk), .i_rst_n(i_rst_n),
        .o_imem_ren(imem_ren), .o_imem_raddr(imem_raddr),
        .i_imem_valid(imem_valid), .i_imem_rdata(imem_rdata),
        .o_output_valid(fetch_valid), .i_output_ready(decode_ready),
        .o_inst0(fetch_inst0), .o_inst1(fetch_inst1),
        .o_compressed(fetch_compressed)
    );

    // FIXME: temporary memory interface/harness to test hart without
    // a compliant cache and AHB interface
    assign o_imem_ren = imem_ren;
    assign o_imem_raddr = imem_raddr;
    assign imem_valid = i_imem_valid;
    assign imem_rdata = i_imem_rdata;

    // instruction decode
    wire [31:0] decode_inst0, decode_inst1;
    wire        decode_valid, issue_ready;
    wire [`BUNDLE_SIZE - 1:0] decode_bundle0, decode_bundle1;
    warp_decode decode (
        .i_clk(i_clk), .i_rst_n(i_rst_n),
        .o_input_ready(decode_ready), .i_input_valid(fetch_valid),
        .i_inst0(fetch_inst0), .i_inst1(fetch_inst1),
        .i_compressed(fetch_compressed),
        .i_output_ready(issue_ready), .o_output_valid(decode_valid),
        .o_bundle0(decode_bundle0), .o_bundle1(decode_bundle1)
    );

    // reg [`BUNDLE_SIZE - 1:0] id_bundle0, id_bundle1;
    // always @(posedge i_clk, negedge i_rst_n) begin
    //     if (!i_rst_n) begin
    //         id_bundle0 <= 32'h0;
    //         id_bundle1 <= 32'h0;
    //     end else begin
    //         id_bundle0 <= decode_bundle0;
    //         id_bundle1 <= decode_bundle1;
    //     end
    // end

    wire [ 4:0] rs1_addr, rs2_addr, rs3_addr, rs4_addr;
    wire        xarith_valid, xarith_ready;
    wire [ 1:0] xarith_opsel;
    wire        xarith_banksel, xarith_op2_sel;
    wire [63:0] xarith_imm;
    wire        xarith_sub, xarith_unsigned, xarith_cmp_mode, xarith_branch_equal;
    wire        xarith_branch_invert, xarith_word;
    wire [4:0]  xarith_issue_rd;
    wire        xlogic_valid, xlogic_ready;
    wire [ 2:0] xlogic_opsel;
    wire        xlogic_banksel, xlogic_op2_sel;
    wire [63:0] xlogic_imm;
    wire        xlogic_invert, xlogic_word;
    wire [ 1:0] xlogic_sll;
    wire [4:0]  xlogic_issue_rd;
    wire [31:0] inst0_retire, inst1_retire;
    warp_issue issue (
        .i_clk(i_clk), .i_rst_n(i_rst_n),
        .o_input_ready(issue_ready), .i_input_valid(decode_valid),
        .i_bundle0(decode_bundle0), .i_bundle1(decode_bundle1),
        .o_rs1_addr(rs1_addr), .o_rs2_addr(rs2_addr),
        .o_rs3_addr(rs3_addr), .o_rs4_addr(rs4_addr),
        .o_xarith_banksel(xarith_banksel),
        .o_xarith_op2_sel(xarith_op2_sel),
        .o_xarith_imm(xarith_imm),
        .o_xarith_opsel(xarith_opsel),
        .o_xarith_sub(xarith_sub),
        .o_xarith_unsigned(xarith_unsigned),
        .o_xarith_cmp_mode(xarith_cmp_mode),
        .o_xarith_branch_equal(xarith_branch_equal),
        .o_xarith_branch_invert(xarith_branch_invert),
        .o_xarith_word(xarith_word),
        .o_xarith_rd(xarith_issue_rd),
        .o_xarith_valid(xarith_valid),
        .i_xarith_ready(xarith_ready),
        .o_xlogic_banksel(xlogic_banksel),
        .o_xlogic_op2_sel(xlogic_op2_sel),
        .o_xlogic_imm(xlogic_imm),
        .o_xlogic_opsel(xlogic_opsel),
        .o_xlogic_invert(xlogic_invert),
        .o_xlogic_sll(xlogic_sll),
        .o_xlogic_word(xlogic_word),
        .o_xlogic_rd(xlogic_issue_rd),
        .o_xlogic_valid(xlogic_valid),
        .i_xlogic_ready(xlogic_ready),
        .i_inst0_retire(inst0_retire),
        .i_inst1_retire(inst1_retire)
    );

    // register file is wired to issue, execution, and write back units
    // for read (4 ports), address is specified by issue when an instruction
    // is dispatched, and the resulting data after the clock edge is supplied
    // directly to the execution units
    // for write (2 ports), address and data is specified by write back
    wire [4:0]  rd1_addr, rd2_addr;
    wire        rd1_wen, rd2_wen;
    wire [63:0] rd1_wdata, rd2_wdata;
    wire [63:0] rs1_rdata, rs2_rdata, rs3_rdata, rs4_rdata;
    warp_xrf xrf (
        .i_clk(i_clk),
        .i_rst_n(i_rst_n),
        .i_rs1_addr(rs1_addr),
        .i_rs2_addr(rs2_addr),
        .i_rs3_addr(rs3_addr),
        .i_rs4_addr(rs4_addr),
        .o_rs1_rdata(rs1_rdata),
        .o_rs2_rdata(rs2_rdata),
        .o_rs3_rdata(rs3_rdata),
        .o_rs4_rdata(rs4_rdata),
        .i_rd1_wen(rd1_wen),
        .i_rd2_wen(rd2_wen),
        .i_rd1_addr(rd1_addr),
        .i_rd2_addr(rd2_addr),
        .i_rd1_wdata(rd1_wdata),
        .i_rd2_wdata(rd2_wdata)
    );

    // FIXME: this isn't true due to backpressure from the register file
    assign xarith_ready = 1'b1;
    wire [63:0] xarith_op1 = xarith_banksel ? rs1_rdata : rs3_rdata;
    wire [63:0] xarith_op2 = xarith_op2_sel ? xarith_imm : (xarith_banksel ? rs1_rdata : rs3_rdata);
    wire [63:0] xarith_result;
    wire        xarith_branch, xarith_wen;
    wire [4:0]  xarith_write_rd;
    warp_xarith xarith (
        .i_clk(i_clk),
        .i_rst_n(i_rst_n),
        .i_valid(xarith_valid),
        .i_op1(xarith_op1),
        .i_op2(xarith_op2),
        .i_rd(xarith_issue_rd),
        .i_opsel(xarith_opsel),
        .i_sub(xarith_sub),
        .i_unsigned(xarith_unsigned),
        .i_cmp_mode(xarith_cmp_mode),
        .i_branch_equal(xarith_branch_equal),
        .i_branch_invert(xarith_branch_invert),
        .i_word(xarith_word),
        .o_valid(xarith_wen),
        .o_result(xarith_result),
        .o_branch(xarith_branch),
        .o_rd(xarith_write_rd)
    );

    // FIXME: this isn't true due to backpressure from the register file
    assign xlogic_ready = 1'b1;
    wire [63:0] xlogic_op1 = xlogic_banksel ? rs1_rdata : rs3_rdata;
    wire [63:0] xlogic_op2 = xlogic_op2_sel ? xlogic_imm : (xlogic_banksel ? rs1_rdata : rs3_rdata);
    wire [63:0] xlogic_result;
    wire        xlogic_wen;
    wire [4:0]  xlogic_write_rd;
    warp_xlogic xlogic (
        .i_clk(i_clk),
        .i_rst_n(i_rst_n),
        .i_valid(xlogic_valid),
        .i_op1(xlogic_op1),
        .i_op2(xlogic_op2),
        .i_rd(xlogic_issue_rd),
        .i_opsel(xlogic_opsel),
        .i_invert(xlogic_invert),
        .i_sll(xlogic_sll),
        .i_word(xlogic_word),
        .o_valid(xlogic_wen),
        .o_result(xlogic_result),
        .o_rd(xlogic_write_rd)
    );

    // FIXME: priority logic needed to write more than two execution units
    assign rd1_wen   = xarith_wen;
    assign rd1_addr  = xarith_write_rd;
    assign rd1_wdata = xarith_result;
    assign rd2_wen   = xlogic_wen;
    assign rd2_addr  = xlogic_write_rd;
    assign rd2_wdata = xlogic_result;

    // TODO: wen can be merged with write_rd to 0
    assign inst0_retire = (32'h1 << xarith_write_rd) & {32{xarith_wen}};
    assign inst1_retire = (32'h1 << xlogic_write_rd) & {32{xlogic_wen}};
endmodule

`default_nettype wire
