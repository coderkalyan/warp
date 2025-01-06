`default_nettype none

module warp_fetch #(
    parameter RESET_ADDR = 64'h8000000000000000
) (
    input  wire        i_clk,
    input  wire        i_rst_n,
    output wire        o_mem_ren,
    output wire [63:0] o_mem_raddr,
    input  wire [63:0] i_mem_rdata,
    input  wire        i_mem_valid,
    input  wire [63:0] i_branch_target,
    input  wire        i_branch_valid,
    input  wire        i_output_ready,
    output wire        o_output_valid,
    output wire [31:0] o_inst0,
    output wire [31:0] o_inst1,
    output wire [1:0]  o_compressed,
    output wire        o_count
);
    reg [63:0] pc, next_pc;
    always @(posedge i_clk, negedge i_rst_n) begin
        if (!i_rst_n)
            pc <= RESET_ADDR;
        else
            pc <= next_pc;
    end

    reg [63:0] buffer;
    always @(posedge i_clk, negedge i_rst_n) begin
        if (!i_rst_n)
            buffer <= 64'h0;
        else if (i_mem_valid)
            buffer <= i_mem_rdata;
    end

    reg buffer_valid;
    always @(posedge i_clk, negedge i_rst_n) begin
        if (!i_rst_n)
            buffer_valid <= 1'h0;
        else begin
            if (i_mem_valid)
                buffer_valid <= 1'b1;
            else if (sent)
                buffer_valid <= 1'b0;
        end
    end

    // detect compressed instructions and segment appropriately
    wire [1:0] compressed;
    warp_pick pick (.i_buffer(buffer), .o_compressed(compressed));

    wire [31:0] inst0 = buffer[31:0];
    wire [31:0] inst1 = compressed[0] ? buffer[47:16] : buffer[63:32];

    wire [1:0] branch;
    warp_predecode predecode [1:0] (
        .i_inst({inst0, inst1}), .i_compressed(compressed),
        .o_branch(branch)
    );

    // output instruction(s) and pipeline next request to cache
    // if valid (output ready and didn't hit a branch)
    localparam FETCH = 3'h0;
    // stalled on instruction cache, no PC change and no new request
    // to cache, output not valid
    localparam CACHE = 3'h1;
    // stalled on backend (prev output not ready), no PC change,
    // output valid, no request to cache unless output ready this cycle
    localparam VALID = 3'h2;
    // stalled on branch resolution, no PC change, output not valid,
    // no request to cache
    localparam RESOL = 3'h3;
    // reset state, initiates a read request to cache
    localparam INIT  = 3'h4;

    reg [2:0] state, next_state;
    always @(posedge i_clk, negedge i_rst_n) begin
        if (!i_rst_n)
            state <= INIT;
        else
            state <= next_state;
    end

    // instruction "sent and received" if output handshake succeeds
    // that is, fetch is valid and receiver ready
    wire sent = o_output_valid && i_output_ready;
    wire branched = branch != 2'b00;

    always @(*) begin
        case (state)
            INIT: next_state = FETCH;
            // FETCH -> VALID if output not ready
            // FETCH -> RESOL if predecode detected a branch
            // FETCH -> FETCH if output ready and no branch
            FETCH: next_state = sent ? (branched ? RESOL : FETCH) : (o_output_valid ? VALID : CACHE);
            // CACHE -> FETCH if cache returned value
            // CACHE -> CACHE if not
            CACHE: next_state = i_mem_valid ? (sent ? (branched ? RESOL : FETCH) : VALID) : CACHE;
            // VALID -> FETCH if output ready
            // VALID -> VALID if output not ready
            VALID: next_state = sent ? (branched ? RESOL : FETCH) : VALID;
            // RESOL -> FETCH if input branch target valid
            // RESOL -> RESOL if not
            RESOL: next_state = i_branch_valid ? FETCH : RESOL;
        endcase
    end

    wire valid = buffer_valid;

    // advance the pc depending on predecode results
    // this is only used in some state transitions
    reg [63:0] advance_pc;
    always @(*) begin
        advance_pc = 64'hx;

        casez ({branch, compressed})
            4'b0000: advance_pc = pc + 64'h8;
            4'b0001,
            4'b0010: advance_pc = pc + 64'h6;
            4'b0011: advance_pc = pc + 64'h4;
            4'b1?0?: advance_pc = pc + 64'h4;
            4'b1?1?: advance_pc = pc + 64'h2;
        endcase
    end

    // in the RESOL state, pc stalls until i_branch_valid and
    // then latches the received branch target
    // in all other states, pc stalls if !sent, else advances
    always @(*) begin
        next_pc = pc;

        if ((state == RESOL) && i_branch_valid)
            next_pc = i_branch_target;
        else if ((state != RESOL) && sent)
            next_pc = advance_pc;
    end

    // the cache read enable is asserted for exactly one cycle
    // after an instruction was sent - else we are stalled for
    // some reason. the cache interface latches this request and
    // it doesn't need to be continuously asserted on cache miss.
    // when fully pipelined (and on cache hit) this can achieve
    // 100% throughput, reading an address each clock cycle.
    assign o_mem_ren = i_rst_n && (next_state == FETCH);
    assign o_mem_raddr = pc;
    assign o_output_valid = valid;
    assign o_inst0 = inst0;
    assign o_inst1 = inst1;
    assign o_compressed = compressed;
    // if the first instruction is not a branch, the second is valid
    // this unit does not attempt to speculate past a branch in a single
    // cycle, as this requires double the read bandwidth from the cache
    assign o_count = !branch[0];

    `ifdef WARP_FORMAL
        reg f_past_valid;
        initial f_past_valid <= 1'b0;
        always @(posedge i_clk) f_past_valid <= 1'b1;

        (* gclk *) reg formal_timestep;

        initial begin
            assume (!i_rst_n);
            assume (!i_clk);
            assume (!i_mem_valid);
            assume (!i_branch_valid);

            assert (!o_output_valid);
            assert (!o_mem_ren);
        end

        // the interface is entirely synchronous
        always @(posedge formal_timestep) begin
            if (!i_rst_n) begin
                assume (!i_mem_valid);
                assume (!i_branch_valid);

                assert (!o_mem_ren);
                assert (!o_output_valid);
            end

            if (f_past_valid && !$rose(i_clk)) begin
                assume ($stable(i_mem_rdata));
                assume ($stable(i_mem_valid));
                assume ($stable(i_branch_target));
                assume ($stable(i_branch_valid));
                assume ($stable(i_output_ready));
            end

            if (f_past_valid && !$rose(i_clk) && !$changed(i_rst_n)) begin
                assert ($stable(o_mem_raddr));
                assert ($stable(o_mem_ren));
                assert ($stable(o_output_valid));
                assert ($stable(o_inst0));
                assert ($stable(o_inst1));
                assert ($stable(o_compressed));
                assert ($stable(o_count));
            end
        end

        reg f_mem_outstanding;
        initial f_mem_outstanding <= 1'b0;
        always @(posedge i_clk, negedge i_rst_n) begin
            if (!i_rst_n) begin
                f_mem_outstanding <= 1'b0;
            end else begin
                if (o_mem_ren)
                    f_mem_outstanding <= 1'b1;
                else if (i_mem_valid)
                    f_mem_outstanding <= 1'b0;

                // cache will never "respond" without a request
                if (!f_mem_outstanding)
                    assume (!i_mem_valid);

                cover (f_mem_outstanding);
            end
        end

        always @(posedge i_clk) begin
            if (f_past_valid && !$past(i_rst_n)) begin
                assert (!o_output_valid);
                assert (o_mem_ren == i_rst_n);
            end

            if (i_rst_n) begin
                // stable - if output is valid but not ready (transmitted),
                // the output data should remain stable
                if (f_past_valid && (state != INIT) && $past(o_output_valid) && !$past(i_output_ready)) begin
                    assert ($stable(o_output_valid));
                    assert ($stable(o_inst0));
                    assert ($stable(o_inst1));
                    assert ($stable(o_compressed));
                    assert ($stable(o_count));
                end

                // liveness - instruction fetched must eventually appear
                // at output interface, assuming instruction cache and
                // branch resolution are "fair" and don't stall indefinitely
                // track outstanding memory requests

                // TODO: assert no request while outstanding
                // memory interface will never respond without request

                // memory request should be stable during transaction
                // if (f_past_valid && $past(f_mem_outstanding))
                //     assert ($stable(o_mem_raddr));

                // if 'busy' state received memory, should propogate
                // without wasting any cycles
                // if (f_past_valid && $past(i_rst_n) && $past(state == BUSY) && $past(i_mem_valid))
                //     assert (o_output_valid);

                // branch target resolution
                // if (f_past_valid && $past(state == STALL) && $past(i_branch_valid)) begin
                //     assert (state == BUSY);
                //     assert (pc == i_branch_target);
                // end

                // if (f_past_valid && $past(o_output_valid) && !$past(i_output_ready)) begin
                //     assert ($stable(o_inst0));
                //     assert ($stable(o_inst1));
                //     assert ($stable(o_compressed));
                //     assert ($stable(o_count));
                // end
                //
                // cover (f_past_valid && $rose(valid));
                // cover (f_past_valid && $fell(valid));
                // cover (f_past_valid && $past(valid) && valid);
                //
                // state transitions
                // cover (f_past_valid && $past(state == VALID) && (state == BUSY));
                // cover (state == STALL);
                // cover (f_past_valid && $past(state == BUSY) && $past(|branch));
                // cover (f_past_valid && $past(state == STALL) && (state == BUSY));
                //
                // // stall protection - both runaway and indefinite stall
                // if (f_past_valid && $past(state != BUSY))
                //     assert ($stable(pc));
                // if (f_past_valid && $past(state == BUSY))
                //     cover (!$stable(pc));
            end
        end
    `endif
endmodule

`default_nettype wire
