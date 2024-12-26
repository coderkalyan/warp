`default_nettype none

// TODO: parametrize cache size
// module warp_icache (
//     input  wire [63:]
// );
// endmodule

module warp_fetch #(
    parameter RESET_ADDR = 64'h0000000000000000
) (
    input  wire        i_clk,
    input  wire        i_rst_n,
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

    // TODO: fetch this from the instruction cache
    wire [63:0] buffer;
    wire buffer_valid = 1'b1;

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
    localparam READY = 2'h1; // ready to output, stalled on decode
    localparam STALL = 2'h2; // hit branch, stalled on resolution
    reg [1:0] state, next_state;
    always @(posedge i_clk, negedge i_rst_n) begin
        if (!i_rst_n)
            state <= BUSY;
        else
            state <= next_state;
    end

    wire next_valid, transmit;
    always @(*) begin
        case (state)
            BUSY: next_state = !transmit ? READY : (|branch ? STALL : state);
            READY: next_state = transmit ? BUSY : state;
            STALL: next_state = i_branch_valid ? BUSY : state;
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
            READY: next_pc = pc;
            STALL: next_pc = pc;
        endcase
    end

    assign o_output_valid = valid;
    assign o_inst0 = inst0;
    assign o_inst1 = inst1;
    assign o_compressed = compressed;
    assign o_count = !branch[0];

    `ifdef WARP_FORMAL
        reg f_past_valid;
        initial f_past_valid <= 1'b0;
        always @(posedge i_clk) f_past_valid <= 1'b1;

        initial begin
            assume (!i_rst_n);
            assume (!i_clk);
            assume (!i_branch_valid);
        end

        always @(posedge i_clk) begin
            if (i_rst_n) begin
                // output ready/valid interface
                if (f_past_valid && (state == BUSY))
                    assert ($past(!i_rst_n) || ($past(valid) && $past(i_output_ready)) || ($past(state == STALL) && $past(i_branch_valid)));

                cover (f_past_valid && $rose(valid));
                cover (f_past_valid && $fell(valid));
                cover (f_past_valid && $past(valid) && valid);

                // state transitions
                cover (f_past_valid && $past(state == READY) && (state == BUSY));
                cover (f_past_valid && $past(state == STALL) && (state == BUSY));

                // stall protection - both runaway and indefinite stall
                if (f_past_valid && $past(state != BUSY))
                    assert ($stable(pc));
                if (f_past_valid && $past(state == BUSY))
                    cover (!$stable(pc));
            end
        end
    `endif
endmodule

`default_nettype wire
