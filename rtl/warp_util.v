`default_nettype none

// `include "warp_defines.v"

// skid buffer implementation
// adapted from https://fpgacpu.ca/fpga/Pipeline_Skid_Buffer.html
module warp_skid #(
    parameter WIDTH = 1
) (
    input  wire               i_clk,
    input  wire               i_rst_n,
    input  wire               i_input_valid,
    output wire               o_input_ready,
    input  wire [WIDTH - 1:0] i_input_data,
    output wire               o_output_valid,
    input  wire               i_output_ready,
    output wire [WIDTH - 1:0] o_output_data
);
    wire insert = i_input_valid  && o_input_ready;
    wire remove = o_output_valid && i_output_ready;
    wire load  = (state == STATE_EMPTY) &&  insert && !remove;
    wire flow  = (state == STATE_BUSY)  &&  insert &&  remove;
    wire fill  = (state == STATE_BUSY)  &&  insert && !remove;
    wire flush = (state == STATE_FULL)  && !insert &&  remove;

    localparam STATE_EMPTY = 2'b00;
    localparam STATE_BUSY  = 2'b01;
    localparam STATE_FULL  = 2'b10;
    reg [1:0] state, next_state;
    always @(*) begin
        next_state = state;

        if (insert && !remove && (state != STATE_FULL))
            next_state = state + 2'h1;
        else if (!insert && remove && (state != STATE_EMPTY))
            next_state = state - 2'h1;
    end

    always @(posedge i_clk, negedge i_rst_n) begin
        if (!i_rst_n)
            state <= STATE_EMPTY;
        else
            state <= next_state;
    end

    // pipelined ready/valid interface
    reg ready, valid;
    always @(posedge i_clk, negedge i_rst_n) begin
        if (!i_rst_n) begin
            ready <= 1'b1;
            valid <= 1'b0;
        end else begin
            ready <= next_state != STATE_FULL;
            valid <= next_state != STATE_EMPTY;
        end
    end

    // data path
    reg [WIDTH - 1:0] buffer;
    always @(posedge i_clk, negedge i_rst_n) begin
        if (!i_rst_n)
            buffer <= {WIDTH{1'b0}};
        else if (fill)
            buffer <= i_input_data;
    end

    reg [WIDTH - 1:0] output_data;
    always @(posedge i_clk, negedge i_rst_n) begin
        if (!i_rst_n)
            output_data <= {WIDTH{1'b0}};
        else if (load || flow || flush)
            output_data <= flush ? buffer : i_input_data;
    end

    assign o_input_ready = ready;
    assign o_output_valid = valid;
    assign o_output_data = output_data;

`ifdef WARP_FORMAL
    reg f_past_valid;
    initial f_past_valid <= 1'b0;
    always @(posedge i_clk) f_past_valid <= 1'b1;

    wire f_load   = (state == STATE_EMPTY) &&  insert && !remove;
    wire f_flow   = (state == STATE_BUSY)  &&  insert &&  remove;
    wire f_fill   = (state == STATE_BUSY)  &&  insert && !remove;
    wire f_unload = (state == STATE_BUSY)  && !insert &&  remove;
    wire f_flush  = (state == STATE_FULL)  && !insert &&  remove;

    initial assume (!i_rst_n);
    initial assume (!i_clk);

    // ready/valid interface always starts up ready but not valid
    always @(*) begin
        if (!i_rst_n) begin
            assert (o_input_ready);
            assert (!o_output_valid);
        end
    end

    always @(posedge i_clk) begin
        if (i_rst_n) begin
            // ensure no runaway to invalid state
            assert((state == STATE_EMPTY) || (state == STATE_BUSY) || (state == STATE_FULL));

            // FIXME: implement formal asserts here
            cover(o_input_ready);
            cover(!o_input_ready);
            cover(o_output_valid);
            cover(!o_output_valid);

            // state transitions
            cover(load);
            cover(flow);
            cover(fill);
            cover(unload);
            cover(flush);
        end
    end
`endif
endmodule

module warp_decoder #(
    parameter width = 1,
    parameter depth = 2 ** width
) (
    input  wire [width - 1:0] i_input,
    output wire [depth - 1:0] o_output
);
    // TODO: determine if synthesis(yosys) generates good
    // output for this or if its better to unroll a loop
    reg [depth - 1:0] out;
    always @(*) begin
        out = {depth{1'b0}};
        out[i_input] = 1'b1;
    end

    assign o_output = out;
endmodule

// module warp_ahbm_formal #(
//     parameter addr_width = 64,
//     parameter data_width = 64,
//     parameter strb_width = $clog2(data_width)
// ) (
//     input  wire                    i_ahb_hclk,
//     input  wire                    i_ahb_hreset_n,
//     input  wire [addr_width - 1:0] i_ahb_haddr,
//     input  wire [2:0]              i_ahb_hburst,
//     input  wire                    i_ahb_hmastlock,
//     input  wire [3:0]              i_ahb_hprot,
//     input  wire [2:0]              i_ahb_hsize,
//     input  wire                    i_ahb_hnonsec,
//     input  wire                    i_ahb_hexcl,
//     input  wire [1:0]              i_ahb_htrans,
//     input  wire [63:0]             i_ahb_hwdata,
//     input  wire [strb_width:0]     i_ahb_hwstrb,
//     input  wire                    i_ahb_hwrite,
//     output wire [63:0]             o_ahb_hrdata,
//     output wire                    o_ahb_hready,
//     output wire                    o_ahb_hresp,
//     output wire                    o_ahb_hexokay
// );
//     // this formal interface connects to a manager, rather than being embedded
//     // into one. therefore the input/output roles are swapped here - inputs
//     // are asserted, and outputs are assumed
//     (* gclk *) reg formal_timestep;
//
//     reg f_past_valid;
//     initial f_past_valid <= 1'b0;
//     always @(posedge i_ahb_hclk) f_past_valid <= 1'b1;
//
//     initial assume (!i_ahb_hreset_n);
//
//     always @(posedge formal_timestep) begin
//         // async assert, synchronous deassert of reset
//         if (f_past_valid && !$past(i_ahb_hreset_n) && !$rose(i_ahb_hclk))
//             assume (!i_ahb_hreset_n);
//
//         // all bus lines must be synchronous wrt clk, except under reset
//         if (f_past_valid && !$rose(i_clk) && !$fell(i_ahb_hreset_n)) begin
//             assert ($stable(i_ahb_haddr));
//             assert ($stable(i_ahb_hburst));
//             assert ($stable(i_ahb_hmastlock));
//             assert ($stable(i_ahb_hprot));
//             assert ($stable(i_ahb_hsize));
//             assert ($stable(i_ahb_hnonsec));
//             assert ($stable(i_ahb_hexcl));
//             assert ($stable(i_ahb_htrans));
//             assert ($stable(i_ahb_hwdata));
//             assert ($stable(i_ahb_hwstrb));
//         end
//
//         if (!$rose(i_clk)) begin
//             assume ($stable(o_ahb_hrdata));
//             assume ($stable(o_ahb_hready));
//             assume ($stable(o_ahb_hresp));
//             assume ($stable(o_ahb_hexokay));
//         end
//     end
//
//     always @(*) begin
//         // specification requires idle and hready under reset
//         if (!i_ahb_hreset_n) begin
//             assert (i_ahb_htrans == `AHB_HTRANS_IDLE);
//             assume (o_ahb_hready);
//         end
//     end
//
//     always @(posedge i_ahb_hclk) begin
//         // if subordinate extends (does not assert ready), manager must hold
//         // all signals stable
//         // if (f_past_valid && $past(i_ahb_htrans != `AHB_HTRANS_IDLE) && !$past(o_ahb_hready))
//         //     assert 
//     end
// endmodule

// this is a dual entry skid buffer placed between stages of the dual
// issue pipeline. this gives a place to buffer instructions when a stage is
// only able to consume one instruction out of two, and otherwise smooth out
// inconsistent data rates.
// module warp_dualskid #(
//     parameter width = 32,
// ) (
//     input  wire               i_clk,
//     input  wire               i_rst_n,
//     input  wire [1:0]         i_wcount,
//     output wire [1:0]         o_wcapacity,
//     input  wire [width - 1:0] i_wdata0,
//     input  wire [width - 1:0] i_wdata1,
//     input  wire               i_
// );
// endmodule

`default_nettype wire
