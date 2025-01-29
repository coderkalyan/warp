`default_nettype none

module warp_hart #(
    param RESET_ADDR = 64'h0000000000000000
) (
    input  wire i_clk,
    input  wire i_rst_n
);
    // instruction fetch
    reg [63:0] pc, next_pc;
    always @(posedge i_clk, negedge i_rst_n) begin
        if (!i_rst_n)
            pc <= RESET_ADDR;
        else
            pc <= next_pc;
    end

    wire if_stall;
    // TODO: actually calculate this properly
    always @(*) begin
        next_pc = pc + 64'h4;
    end

    // TODO: implement instruction cache
    wire [63:0] buffer;
    wire buffer_valid = 1'b1;

    // predecode logic (pick instructions)
    wire [31:0] uinst0, uinst1;
    wire [15:0] cinst0, cinst1;
    wire [1:0] bsel0, bsel1;
    warp_predecode predeccode (
        .i_buffer(buffer),
        .o_uinst0(uinst0), .o_uinst1(uinst1),
        .o_cinst0(cinst0), .o_cinst1(cinst1),
        .o_sel0(bsel0), .o_sel1(bsel1)
    );

    // IF/ID pipeline barrier
    reg [31:0] if_uinst0, if_uinst1;
    reg [15:0] if_cinst0, if_cinst1;
    reg [1:0] if_bsel0, if_bsel1;
    reg if_valid;
    always @(posedge i_clk, negedge i_rst_n) begin
        if (!i_rst_n) begin
            if_valid <= 1'b0;
            if_uinst0 <= 32'h0;
            if_uinst1 <= 32'h0;
            if_cinst0 <= 16'h0;
            if_cinst1 <= 16'h0;
            if_bsel0 <= 2'h0;
            if_bsel1 <= 2'h0;
        end else begin
            if_valid <= buffer_valid;
            if_uinst0 <= uinst0;
            if_uinst1 <= uinst1;
            if_cinst0 <= cinst0;
            if_cinst1 <= cinst1;
            if_bsel0 <= bsel0;
            if_bsel1 <= bsel1;
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
