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
    localparam S = 8;            // 8 bit set index => 256 sets
    localparam W = 4;            // 4 way set associative
    localparam T = 64 - O - S;   // 50 bit tag
    localparam D = 8 * (2 ** O); // 8 * 64 data bits per line
    localparam V = 1;            // 1 valid bit per line
    localparam DEPTH = 2 ** S;   // 256 sets * 4 ways per set * 64 bytes per way = 64K cache

    reg [T + D - 1:0] way0 [DEPTH - 1:0];
    reg [T + D - 1:0] way1 [DEPTH - 1:0];
    reg [T + D - 1:0] way2 [DEPTH - 1:0];
    reg [T + D - 1:0] way3 [DEPTH - 1:0];
    reg [3:0] valid [DEPTH - 1:0];

    // synchronous single cycle read from the cache should
    // improve synthesis over flip flops
    reg [T - 1:0] tag0, tag1, tag2, tag3;
    reg [D - 1:0] data0, data1, data2, data3;
    always @(posedge i_clk) begin
        tag0 <= way0[index][D + T - 1:D];
        tag1 <= way1[index][D + T - 1:D];
        tag2 <= way2[index][D + T - 1:D];
        tag3 <= way3[index][D + T - 1:D];
        data0 <= way0[index][D - 1:0];
        data1 <= way1[index][D - 1:0];
        data2 <= way2[index][D - 1:0];
        data3 <= way3[index][D - 1:0];
    end

    // valid needs to be treated a little more carefully because
    // a false hit would be very bad
    reg valid0, valid1, valid2, valid3;
    always @(posedge i_clk) begin
        if (!i_rst_n) begin
            valid0 <= 1'b0;
            valid1 <= 1'b0;
            valid2 <= 1'b0;
            valid3 <= 1'b0;
        end else begin
            valid0 <= valid[index][0];
            valid1 <= valid[index][1];
            valid2 <= valid[index][2];
            valid3 <= valid[index][3];
        end
    end

    // set index and tag of incoming request
    wire [S - 1:0] index = i_req_raddr[O + S - 1:O];
    wire [T - 1:0] tag   = i_req_raddr[63:O + S];

    // check if any of the ways are a hit
    wire hit0 = valid0 && (tag0 == tag);
    wire hit1 = valid1 && (tag1 == tag);
    wire hit2 = valid2 && (tag2 == tag);
    wire hit3 = valid3 && (tag3 == tag);
    wire hit = hit0 || hit1 || hit2 || hit3;

    reg [63:0] hit_rdata;
    always @(*) begin
        hit_rdata = 64'h0;

        if (hit0)
            hit_rdata = data0;
        else if (hit1)
            hit_rdata = data1;
        else if (hit2)
            hit_rdata = data2;
        else if (hit3)
            hit_rdata = data3;
    end
    
    reg r_req_valid;
    always @(posedge i_clk, negedge i_rst_n) begin
        if (!i_rst_n)
            r_req_valid <= 1'b0;
        else
            r_req_valid <= i_req_valid;
    end

    wire miss = r_req_valid && !hit;

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
    reg        write_data, write_meta, fill_done;
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
        write_data = 1'b0;
        write_meta = 1'b0;
        fill_done = 1'b0;

        case (state)
            // initiate a read transfer of 1 full 64 byte cache line
            // this will take (64 bytes) / (64 bit data line) = 8 transfers
            // or at least 9 clocks of latency
            // NOTE: we should be able to achieve higher throughput by
            // initiating new nonconsecutive accesses immediately however
            // this might require two accesses in flight from the hart
            IDLE: begin
                if (miss) begin
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
                    write_data = 1'b1;

                    // if this is the last address, we are done
                    if (beats == 3'h7) begin
                        next_ahb_htrans = HTRANS_IDLE;
                        write_meta = 1'b1;
                        fill_done = 1'b1;
                        next_state = IDLE;
                    end else begin
                        next_ahb_htrans = HTRANS_SEQ;
                    end
                end
            end
        endcase
    end

    // global round robin replacement policy
    reg [1:0] victim;
    always @(posedge i_clk, negedge i_rst_n) begin
        if (!i_rst_n)
            victim <= 2'b00;
        else if (fill_done)
            victim <= victim + 2'b01;
    end

    // target first tries to find an invalid line to fill
    // and failing to do so, uses the replacement victim
    reg [1:0] target;
    always @(*) begin
        if (valid0)
            target = 2'b00;
        else if (valid1)
            target = 2'b01;
        else if (valid2)
            target = 2'b10;
        else if (valid3)
            target = 2'b11;
        else
            target = victim;
    end

    // writes to the cache are controlled by the fill fsm
    // once again, valid store needs to be treated carefully wrt reset
    integer j;
    always @(posedge i_clk, negedge i_rst_n) begin
        // on reset, clear all the valid bits
        // ways will contain junk data
        if (!i_rst_n)
            for (j = 0; j < DEPTH; j = j + 1)
                valid[j] <= 4'h0;
        // otherwise, when we are done filling a cache line,
        // mark it as valid
        else if (write_meta)
            valid[index] <= valid[index] | (1 << target);
    end

    // each word returned from memory is buffered and then atomically written
    // however, in order to not delay an extra cycle, the last value bypasses
    // this buffer and writes directly to the cache line
    // NOTE: investigate if this is worth the effort or synthesis works out
    // with split out data and tag lines
    (* keep *) reg [63:0] line [0:2 ** (O - 3) - 2];
    always @(posedge i_clk) begin
        if (write_data)
            line[beats] <= i_ahb_hrdata;
    end

    wire [2 ** (O + 3) - 1:0] line_concat;
    genvar i;
    generate
        for (i = 0; i < O - 1; i = i + 1)
            assign line_concat[i * 64 +: 64] = line[i];
    endgenerate

    // the tag is updated when the cache line is filled
    always @(posedge i_clk) begin
        if (write_meta) begin
            if (target == 2'b00)
                way0[index] <= {tag, i_ahb_hrdata, line_concat};
            else if (target == 2'b01)
                way1[index] <= {tag, i_ahb_hrdata, line_concat};
            else if (target == 2'b10)
                way2[index] <= {tag, i_ahb_hrdata, line_concat};
            else if (target == 2'b11)
                way3[index] <= {tag, i_ahb_hrdata, line_concat};
        end
    end

    always @(posedge i_clk, negedge i_rst_n) begin
        if (!i_rst_n) begin
            beats <= 3'h0;
            ahb_haddr <= 64'h0;
            ahb_htrans <= 2'h0;
        end else begin
            beats <= next_beats;
            ahb_haddr <= next_ahb_haddr;
            ahb_htrans <= next_ahb_htrans;
        end
    end

    wire        res_valid = hit || fill_done;
    wire [63:0] res_rdata = hit ? hit_rdata : line[ahb_haddr[O - 1:3]];

    // FIXME: actually reply
    assign o_res_valid = res_valid;
    assign o_res_rdata = res_rdata;
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

    initial assume (!i_rst_n);
    initial assume (!i_clk);

    always @(*) begin
        if (!i_rst_n) begin
            assume (!i_req_valid);
            assert (!o_res_valid);
        end
    end

    reg f_req_outstanding;
    always @(posedge i_clk, negedge i_rst_n) begin
        if (!i_rst_n)
            f_req_outstanding <= 1'b0;
        else if (i_req_valid)
            f_req_outstanding <= 1'b1;
        else if (o_res_valid)
            f_req_outstanding <= 1'b0;
    end

    reg [63:0] f_req_addr;
    always @(posedge i_clk) begin
        if (i_req_valid)
            f_req_addr <= i_req_raddr;
    end

    // formal verification of the memory interface is done with three signals
    // an arbitrary constant address on wrt. which to observe transactions
    // an arbitrary constant data at that address in main memory
    // NOTE: we assume for now that instruction memory is read only
    (* anyconst *) wire [63:0] f_addr;
    (* anyconst *) wire [63:0] f_data;
    // always @(*) begin
    //     // assume memory is cleared on reset
    //     if (!i_rst_n)
    //         f_data <= 64'h0;
    // end

    always @(posedge i_clk) begin
        // on an incoming memory read transfer, assume that requests for
        // address f_addr equal f_data
        if (f_past_valid && $past(o_ahb_htrans != IDLE) && $past(o_ahb_haddr == f_addr) && i_ahb_hready)
            assume (i_ahb_hrdata == f_data);

        // memory should never respond without a request
        if (o_res_valid)
            assert (f_req_outstanding);

        // if cache responds to a request from the hart for address f_addr,
        // it should reply with f_data
        if (o_res_valid && (f_req_addr == f_addr))
            assert (o_res_rdata == f_data);

        // we should be able to hit on any of the four ways
        cover (hit0);
        cover (hit1);
        cover (hit2);
        cover (hit3);
        // and we should cover a full hit and miss
        cover (hit);
        cover (!hit);

        // TODO: verify the fill fsm
    end

    // TODO: verify that the interface is entirely synchronous
    // TODO: a lot more verification needed here for the ahb interface
    always @(posedge f_clk) begin
        if (f_rst_n) begin
            // subordinates must always provide zero wait state OKAY
            // responses to IDLE transfers
            if (f_past_valid && $past(o_ahb_htrans == HTRANS_IDLE) && $past(i_ahb_hready)) begin
                assume (i_ahb_hready);
                assume (i_ahb_hresp == HRESP_OKAY);
            end

            // if a subordinate is not ready, the manager should
            // hold all relevant request signals steady
            if (f_past_valid && $past(o_ahb_htrans != HTRANS_IDLE) && $past(!i_ahb_hready)) begin
                // always valid
                assert ($stable(o_ahb_htrans));
                assert ($stable(o_ahb_haddr));
                assert ($stable(o_ahb_hmastlock));
                // always valid for htrans != IDLE
                assert ($stable(o_ahb_hburst));
                assert ($stable(o_ahb_hprot));
                assert ($stable(o_ahb_hsize));
                assert ($stable(o_ahb_hnonsec));
                assert ($stable(o_ahb_hexcl));
                assert ($stable(o_ahb_hwrite));
                // only valid for write transfers
                if (o_ahb_hwrite) begin
                    assert ($stable(o_ahb_hwdata));
                    assert ($stable(o_ahb_hwstrb));
                end
            end
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
