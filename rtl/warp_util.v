`default_nettype none

// skid buffer implementation
// see https://fpgacpu.ca/fpga/Pipeline_Skid_Buffer.html
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
    localparam STATE_EMPTY = 2'b00;
    localparam STATE_BUSY  = 2'b01;
    localparam STATE_FULL  = 2'b10;
    reg [1:0] state, next_state;

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

    wire insert = ready && i_input_valid;
    wire remove = valid && o_output_valid;

    // state transitions
    // TODO: taken from example article, but probably
    // can be simplified to saturating addition
    wire load   = (state == STATE_EMPTY) && insert  && !remove;
    wire flow   = (state == STATE_BUSY)  && insert  && remove;
    wire fill   = (state == STATE_BUSY)  && insert  && !remove;
    wire unload = (state == STATE_BUSY)  && !insert && remove;
    wire flush  = (state == STATE_FULL)  && !insert && remove;

    always @(*) begin
        next_state = state;

        case (1'b1)
            load:   next_state = STATE_BUSY;
            flow:   next_state = STATE_BUSY;
            fill:   next_state = STATE_FULL;
            flush:  next_state = STATE_BUSY;
            unload: next_state = STATE_EMPTY;
        endcase
    end

    // data path
    reg  [WIDTH - 1:0] buffer, out;
    wire [WIDTH - 1:0] out_sel = flush ? buffer : i_input_data;

    always @(posedge i_clk, negedge i_rst_n) begin
        if (!i_rst_n) begin
            buffer <= {WIDTH{1'b0}};
            out <= {WIDTH{1'b0}};
        end else begin
            if (fill)
                buffer <= i_input_data;
            if (load || flow || flush)
                out <= out_sel;
        end
    end

    assign o_input_ready = ready;
    assign o_output_valid = valid;
    assign o_output_data = out;

`ifdef WARP_FORMAL
    reg f_past_valid;
    initial f_past_valid <= 1'b0;
    always @(posedge i_clk) f_past_valid <= 1'b1;

    always @(posedge i_clk) begin
        if (!i_rst_n) begin
            assert(o_input_ready);
            assert(!o_output_valid);
        end else begin
            assert((state == STATE_EMPTY) || (state == STATE_BUSY) || (state == STATE_FULL));
        end

        cover(o_input_ready);
        cover(!o_input_ready);
        cover(o_output_valid);
        cover(!o_output_valid);

        cover(load);
        cover(flow);
        cover(fill);
        cover(unload);
        cover(flush);
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
    reg [depth - 1:0] output;
    always @(*) begin
        output = {depth{1'b0}};
        output[i_input] = 1'b1;
    end

    assign o_output = output;
endmodule

module warp_ahbm_formal #(
    parameter addr_width = 64,
    parameter data_width = 64,
    parameter strb_width = $clog2(data_width),
) (
    input  wire                    i_ahb_hclk,
    input  wire                    i_ahb_hreset_n,
    input  wire [addr_width - 1:0] i_ahb_haddr,
    input  wire [2:0]              i_ahb_hburst,
    input  wire                    i_ahb_hmastlock,
    input  wire [3:0]              i_ahb_hprot,
    input  wire [2:0]              i_ahb_hsize,
    input  wire                    i_ahb_hnonsec,
    input  wire                    i_ahb_hexcl,
    input  wire [1:0]              i_ahb_htrans,
    input  wire [63:0]             i_ahb_hwdata,
    input  wire [strb_width:0]     i_ahb_hwstrb,
    input  wire                    i_ahb_hwrite,
    output wire [63:0]             o_ahb_hrdata,
    output wire                    o_ahb_hreadyout,
    output wire                    o_ahb_hresp,
    output wire                    o_ahb_hexokay
);
    
endmodule

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
endmodule

`default_nettype wire
