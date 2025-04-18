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
    input  wire        i_req_valid,
    // TODO: this should be reduced to the size of the virtual address space
    // once virtual memory and supervisor mode have been implemented
    input  wire [63:0] i_req_raddr,
    output wire        o_res_valid,
    output wire [63:0] o_res_rdata,
    // AHB5 interface (manager) to memory
    output wire        o_ahb_hclk,
    output wire        o_ahb_hreset_n,
    output wire [63:0] o_ahb_haddr,
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
    input  wire        i_ahb_hready,
    input  wire        i_ahb_hresp,
    input  wire        i_ahb_hexokay
);
    // NOTE: the 6 bit offset is hardcoded and only kept here for clarity and
    // calculation. other parameters *should* be adjustable.
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

    localparam IDLE = 1'b0;
    localparam BUSY = 1'b1;
    reg state, next_state;
    always @(posedge i_clk, negedge i_rst_n) begin
        if (!i_rst_n)
            state <= IDLE;
        else
            state <= next_state;
    end

    localparam HTRANS_IDLE   = 2'b00;
    localparam HTRANS_BUSY   = 2'b01;
    localparam HTRANS_NONSEQ = 2'b10;
    localparam HTRANS_SEQ    = 2'b11;

    localparam HBURST_SINGLE = 3'b000;
    localparam HBURST_INCR   = 3'b001;
    localparam HBURST_WRAP4  = 3'b010;
    localparam HBURST_INCR4  = 3'b011;
    localparam HBURST_WRAP8  = 3'b100;
    localparam HBURST_INCR8  = 3'b101;
    localparam HBURST_WRAP16 = 3'b110;
    localparam HBURST_INCR16 = 3'b111;

    localparam HRESP_OKAY    = 1'b0;
    localparam HRESP_ERROR   = 1'b0;

    reg [ 2:0] beats, next_beats;
    reg        res_valid, next_res_valid;
    reg [63:0] ahb_haddr, next_ahb_haddr;
    reg [ 2:0] ahb_hburst;
    reg [ 2:0] ahb_hsize;
    reg [ 1:0] ahb_htrans, next_ahb_htrans;
    always @(*) begin
        // defaults
        next_state = state;
        next_beats = 3'h0;
        next_ahb_haddr  = 64'h0;
        ahb_hburst = HBURST_WRAP8;
        // HSIZE_DWORD = 8 bytes
        ahb_hsize  = 3'b011;
        next_ahb_htrans = HTRANS_IDLE;
        next_res_valid = 1'b0;

        case (state)
            // initiate a read transfer of 1 full 64 byte cache line
            // this will take (64 bytes) / (64 bit data line) = 8 transfers
            // or at least 9 clocks of latency
            // NOTE: we should be able to achieve higher throughput by
            // initiating new nonconsecutive accesses immediately
            IDLE: begin
                if (i_req_valid) begin
                    // to initiate the transfer we present the address of the
                    // first word in the cache line and latch this on the
                    // next clock so we can use it to increment
                    next_beats = 3'h0;
                    next_ahb_haddr = {i_req_raddr[63:6], 6'h0};
                    next_ahb_htrans = HTRANS_NONSEQ;
                    next_state = BUSY;
                end
            end
            // wait for a reply on the bus and request another line if needed
            BUSY: begin
                // until bus replies, hold the address line steady
                next_beats = beats;
                next_ahb_haddr = ahb_haddr;
                next_ahb_htrans = ahb_htrans;

                if (i_ahb_hready) begin
                    next_beats = beats + 3'h1;
                    next_ahb_haddr = ahb_haddr + 64'h8;

                    // if this is the last address, we are done
                    if (beats == 3'h7) begin
                        next_ahb_htrans = HTRANS_IDLE;
                        next_res_valid = 1'b1;
                        next_state = IDLE;
                    end else begin
                        next_ahb_htrans = HTRANS_SEQ;
                    end
                end
            end
        endcase
    end

    always @(posedge i_clk, negedge i_rst_n) begin
        if (!i_rst_n) begin
            beats <= 3'h0;
            res_valid <= 1'b0;
            ahb_haddr <= 64'h0;
            ahb_htrans <= 2'h0;
        end else begin
            beats <= next_beats;
            res_valid <= next_res_valid;
            ahb_haddr <= next_ahb_haddr;
            ahb_htrans <= next_ahb_htrans;
        end
    end

    // FIXME: actually reply
    assign o_res_valid = res_valid;
    // NOTE: these first two may need to be treated specially
    assign o_ahb_hclk = i_clk;
    assign o_ahb_hreset_n = i_rst_n;
    assign o_ahb_haddr = ahb_haddr;
    assign o_ahb_hburst = ahb_hburst;
    assign o_ahb_hmastlock = 1'b0;
    assign o_ahb_hprot = 4'b0011;
    assign o_ahb_hsize = ahb_hsize;
    assign o_ahb_hnonsec = 1'b1;
    assign o_ahb_hexcl = 1'b0;
    assign o_ahb_htrans = ahb_htrans;
    // read only manager
    assign o_ahb_hwdata = 64'h0;
    assign o_ahb_hwstrb = 8'h0;
    assign o_ahb_hwrite = 1'b0;

`ifdef WARP_FORMAL
    wire f_clk = o_ahb_hclk;
    wire f_rst_n = o_ahb_hreset_n;

    reg f_past_valid;
    initial f_past_valid <= 1'b0;
    always @(posedge f_clk) f_past_valid <= 1'b1;

    // TODO: verify that the interface is entirely synchronous
    
    reg [63:0] f_haddr;
    reg        f_hwrite;

    always @(posedge f_clk) begin
        if (f_rst_n) begin
            // subordinates must always provide zero wait state OKAY
            // responses to IDLE transfers
            if (f_past_valid && $past(o_ahb_htrans == HTRANS_IDLE)) begin
                assume (i_ahb_hready);
                assume (i_ahb_hresp == HRESP_OKAY);
            end

            // if a subordinate is not ready, the manager should
            // hold all request signals steady
            // if (f_past_valid && $past(o_ahb_htrans != HTRANS_IDLE) && $past(!i_ahb_hready)) begin
            //     assert ($stable(o_ahb_haddr));
            //     assert ($stable(o_ahb_hburst));
            //     assert ($stable(o_ahb_hmastlock));
            //     assert ($stable(o_ahb_hprot));
            //     assert ($stable(o_ahb_hsize));
            //     assert ($stable(o_ahb_hnonsec));
            //     assert ($stable(o_ahb_hexcl));
            //     assert ($stable(o_ahb_htrans));
            //     assert ($stable(o_ahb_hwdata));
            //     assert ($stable(o_ahb_hwstrb));
            //     assert ($stable(o_ahb_hwrite));
            // end
        end
    end
`endif
endmodule

// module warp_lsu (
//     input  wire        i_clk,
//     input  wire        i_rst_n,
//     input  wire        i_valid,
//     input  wire        i_opsel,
//     input  wire [63:0] i_base,
//     input  wire [31:0] i_offset,
//     input  wire [1:0]  i_width,
//     input  wire        i_unsigned,
//     input  wire [63:0] i_wdata,
//     output wire        o_ready,
//     output wire        o_fault,
//     output wire [63:0] o_rdata
// );
//     // effective address (base + signed offset)
//     wire [63:0] next_addr = i_base + {{32{i_offset[31]}}, i_offset};
//
//     // alignment based on width
//     wire [2:0] align_mask = {i_width == `WIDTH_DOUBLE, i_width == `WIDTH_DOUBLE || i_width == `WIDTH_WORD, i_width != `WIDTH_BYTE};
//     wire aligned = (mem_addr[2:0] & align_mask) == 3'b000;
//
//     reg [2:0] state, next_state;
//     always @(posedge i_clk, negedge i_rst_n) begin
//         if (!i_rst_n)
//             state <= `STATE_IDLE;
//         else
//             state <= next_state;
//     end
//
//     always @(*) begin
//         next_state = state;
//     end
// endmodule
