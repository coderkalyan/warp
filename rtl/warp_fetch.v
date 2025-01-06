`default_nettype none

module warp_fetch #(
    parameter RESET_ADDR = 64'h8000000000000000
) (
    input  wire        i_clk,
    input  wire        i_rst_n,
    output wire [63:0] o_mem_raddr,
    output wire        o_mem_ren,
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

    wire [63:0] buffer = i_mem_rdata;
    wire buffer_valid = i_mem_valid;

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

    localparam BUSY  = 2'h0; // output instruction and fetch next
    localparam VALID = 2'h1; // ready to output, stalled on decode
    localparam STALL = 2'h2; // hit branch, stalled on resolution
    reg [1:0] state, next_state;
    always @(posedge i_clk, negedge i_rst_n) begin
        if (!i_rst_n)
            state <= BUSY;
        else
            state <= next_state;
    end

    wire transmit;
    always @(*) begin
        case (state)
            BUSY:  next_state = transmit ? (|branch ? STALL : BUSY) : VALID;
            VALID: next_state = transmit ? BUSY : VALID;
            STALL: next_state = i_branch_valid ? BUSY : STALL;
            default: next_state = BUSY;
        endcase
    end

    wire next_valid = (state != STALL) && buffer_valid;
    reg valid;
    always @(posedge i_clk, negedge i_rst_n) begin
        if (!i_rst_n)
            valid <= 1'b0;
        else
            valid <= next_valid;
    end

    assign transmit = valid && i_output_ready;

    reg [63:0] advance_pc;
    always @(*) begin
        advance_pc = 64'hx;

        casez ({branch, compressed})
            4'b0000: advance_pc = pc + 64'h8;
            4'b0001, 4'b0010: advance_pc = pc + 64'h6;
            4'b0011: advance_pc = pc + 64'h4;
            4'b1?0?: advance_pc = pc + 64'h4;
            4'b1?1?: advance_pc = pc + 64'h2;
        endcase
    end

    always @(*) begin
        next_pc = 64'hx;

        case (state)
            BUSY: next_pc = buffer_valid ? advance_pc : pc;
            VALID: next_pc = pc;
            STALL: next_pc = i_branch_valid ? i_branch_target : pc;
        endcase
    end

    assign o_mem_raddr = transmit && (next_pc == BUSY);
    assign o_mem_ren = i_rst_n;
    assign o_output_valid = valid;
    assign o_inst0 = inst0;
    assign o_inst1 = inst1;
    assign o_compressed = compressed;
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
        end

        always @(posedge formal_timestep) begin
            if (f_past_valid && !$rose(i_clk) && !$changed(i_rst_n)) begin
                assume ($stable(i_mem_rdata));
                assume ($stable(i_mem_valid));
                assume ($stable(i_branch_target));
                assume ($stable(i_branch_valid));
                assume ($stable(i_output_ready));
                
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

        always @(posedge i_clk) begin
            if (f_past_valid && !$past(i_rst_n)) begin
                assert (!o_output_valid);
            end

            if (i_rst_n) begin
                // track outstanding memory requests
                if (o_mem_ren)
                    f_mem_outstanding <= 1'b1;
                else if (i_mem_valid)
                    f_mem_outstanding <= 1'b0;

                // TODO: assert no request while outstanding
                // memory interface will never respond without request
                if (!f_mem_outstanding)
                    assume (!i_mem_valid);

                // memory request should be stable during transaction
                if (f_past_valid && $past(f_mem_outstanding))
                    assert ($stable(o_mem_raddr));

                // if 'busy' state received memory, should propogate
                // without wasting any cycles
                if (f_past_valid && $past(i_rst_n) && $past(state == BUSY) && $past(i_mem_valid))
                    assert (o_output_valid);

                // branch target resolution
                if (f_past_valid && $past(state == STALL) && $past(i_branch_valid)) begin
                    assert (state == BUSY);
                    assert (pc == i_branch_target);
                end

                // if (f_past_valid && $past(o_output_valid) && !$past(i_output_ready)) begin
                //     assert ($stable(o_inst0));
                //     assert ($stable(o_inst1));
                //     assert ($stable(o_compressed));
                //     assert ($stable(o_count));
                // end
                //
                cover (f_past_valid && $rose(valid));
                // cover (f_past_valid && $fell(valid));
                // cover (f_past_valid && $past(valid) && valid);
                //
                // state transitions
                cover (f_past_valid && $past(state == VALID) && (state == BUSY));
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
