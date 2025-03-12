// module warp_xshift (
//     input  wire        i_clk,
//     input  wire        i_rst_n,
//     input  wire [63:0] i_operand,
//     input  wire [ 5:0] i_amount,

//     // `XSHIFT_OP_SHL: o_result = i_operand << i_amount
//     // `XSHIFT_OP_SHR: o_result = i_operand >>/>>> i_amount
//     // `XSHIFT_OP_ROL: o_result = i_operand rol i_amount
//     // `XSHIFT_OP_ROR: o_result = i_operand ror i_amount
//     input  wire [ 1:0] i_opsel,

//     // if asserted, shift right arithmetic instead of logical (>>/>>>)
//     // only used for OP_SHR
//     input  wire        i_arithmetic,

//     // when asserted, operate on lower 32 bits only of operands and
//     // sign extend the result to 64 bits
//     input  wire        i_word,

//     output wire [63:0] o_result
// );


`include "warp_defines.v"

module tb_shifter ();
    reg clk;
    reg rst_n;

    localparam CLK_PERIOD = 10;
    always #(CLK_PERIOD / 2) clk = ~clk;

    reg i_clk;
    reg i_rst_n;
    reg [63:0] i_operand;
    reg [5:0] i_amount;
    reg [1:0] i_opsel;
    reg i_arithmetic;
    reg i_word;
    wire [63:0] o_result;

    warp_xshift u_shifter (
        .i_clk(clk),
        .i_rst_n(rst_n),
        .i_operand(i_operand),
        .i_amount(i_amount),
        .i_opsel(i_opsel),
        .i_arithmetic(i_arithmetic),
        .i_word(i_word),
        .o_result(o_result)
    );

    initial begin
        $dumpfile("tb_shifter.vcd");
        $dumpvars(0, tb_shifter);
    end

    wire i_word_true = i_word == 1'b1;
    wire i_word_false = i_word == 1'b0;

    initial begin
        // formal verification

        //for 64 bits:
        //test rotate left
        assert (o_result == (i_operand << i_amount) && (i_opsel == XSHIFT_OP_SHL) && i_word_false);

        //test rotate right zero extended
        assert (o_result == (i_operand >> i_amount) &&
        (i_opsel == XSHIFT_OP_SHR) &&
        (i_arithmetic == 1'b0) &&
        i_word_false);

        //test rotate right signed extended
        assert (o_result == (i_operand >>> i_amount) &&
        (i_opsel == XSHIFT_OP_SHR) &&
        (i_arithmetic == 1'b1) &&
        i_word_false);

        //test rotate right
        assert (o_result == (i_operand >> i_amount | i_operand << (64-i_amount)) &&
        (i_opsel == XSHIFT_OP_ROR) &&
        i_word_false);

        //test rotate left
        assert (o_result == (i_operand << i_amount | i_operand >> (64-i_amount)) &&
        (i_opsel == XSHIFT_OP_ROL) &&
        i_word_false);
    end

    initial begin
        // formatl verification
        // for 32 bits

    end
    

endmodule
