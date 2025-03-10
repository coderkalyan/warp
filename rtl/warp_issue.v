`default_nettype none

// `include "warp_defines.v"

module warp_issue (
    input  wire        i_clk,
    input  wire        i_rst_n,
    // receive zero or two instruction bundles per clock from the decode unit
    output wire        o_input_ready,
    input  wire        i_input_valid,
    input  wire [`BUNDLE_SIZE - 1:0] i_bundle0,
    input  wire [`BUNDLE_SIZE - 1:0] i_bundle1,
    // reading data from registers happens on the clock edge that an
    // instruction leaves issue and enters one of the functional units
    // it cannot be done earlier as instructions stall in issue until
    // dependencies are ready, and to avoid another pipeline stage for now,
    // the read results are wired directly to the execution units
    output wire [4:0]  o_rs1_addr,
    output wire [4:0]  o_rs2_addr,
    output wire [4:0]  o_rs3_addr,
    output wire [4:0]  o_rs4_addr,
    // interface to integer arithmetic pipeline
    // op1 is always rs1, op2 is either rs2 or immediate
    // FIXME: implement this decode signal
    output wire        o_xarith_banksel, // (rs1, rs2) or (rs3, rs4)
    output wire        o_xarith_op2_sel,
    output wire [ 1:0] o_xarith_opsel,
    output wire        o_xarith_sub,
    output wire        o_xarith_unsigned,
    output wire        o_xarith_cmp_mode,
    output wire        o_xarith_branch_equal,
    output wire        o_xarith_branch_invert,
    output wire        o_xarith_word,
    output wire        o_xarith_valid,
    input  wire        i_xarith_ready,
    // interface to integer logic pipeline
    // op1 is always rs1, op2 is either rs2 or immediate
    // FIXME: implement this decode signal
    output wire        o_xlogic_banksel, // (rs1, rs2) or (rs3, rs4)
    output wire        o_xlogic_op2_sel,
    output wire [ 2:0] o_xlogic_opsel,
    output wire        o_xlogic_invert,
    output wire [ 1:0] o_xlogic_sll,
    output wire        o_xlogic_word,
    output wire        o_xlogic_valid,
    input  wire        i_xlogic_ready,
    // interface to integer shift/rotate pipeline
    // xshift_operand is always rs1
    // xshift_amount is either rs2 or immediate
    output wire        o_xshift_banksel, // (rs1, rs2) or (rs3, rs4)
    output wire [ 1:0] o_xshift_opsel,
    output wire        o_xshift_arithmetic,
    output wire        o_xshift_word,
    output wire        o_xshift_valid,
    input  wire        i_xshift_ready,
    // interface to integer lower 32 multiply
    // op1 is always rs1, op2 is always rs2
    output wire        o_xmultl_banksel, // (rs1, rs2) or (rs3, rs4)
    output wire        o_xmultl_word,
    output wire        o_xmultl_valid,
    input  wire        i_xmultl_ready,
    // interface to integer upper 32 multiply
    // op1 is always rs1, op2 is always rs2
    output wire        o_xmulth_banksel, // (rs1, rs2) or (rs3, rs4)
    output wire        o_xmulth_unsigned,
    output wire        o_xmulth_valid,
    input  wire        i_xmulth_ready,
    // interface to integer divide/remainder
    // op1 is always rs1, op2 is always rs2
    output wire        o_xdiv_unsigned,
    output wire        o_xdiv_word,
    output wire        o_xdiv_valid,
    input  wire        i_xdiv_ready,
    // execution units clear the reservation for each of their source and
    // destination registers upon retiring the instruction
    input  wire [31:0] i_inst0_retire,
    input  wire [31:0] i_inst1_retire
);
    // currently, both RAW and WAW hazards are handled with a reservation
    // register that keeps track of "in flight" destination registers
    // these are set by issue when dispatching an instruction and cleared
    // when the instruction reaches write back
    // an instruction cannot be issued until the corresponding reservation is
    // free, which makes sure dependencies are ready and won't be overwritten
    // WAR dependencies are not possible in this pipeline since register reads
    // are performed strictly before register writes, and the core issues
    // instructions in order (even if they don't always retire in order)
    // TODO: while this is correct for WAW, it is potentially underutilizing
    // the execution units as the only thing that actually needs to be checked
    // is that the dispatched instruction will not retire before anything
    // already in the pipeline that has reserved the same destination
    reg  [31:0] reservation;
    wire [31:0] next_reservation;
    always @(posedge i_clk, negedge i_rst_n) begin
        if (!i_rst_n)
            reservation <= 32'h0;
        else
            reservation <= next_reservation;
    end

    // unpack parts of the instruction bundles to extract register address and
    // pipeline destination
    wire        bundle0_legal    = i_bundle0[ 0: 0];
    wire [14:0] bundle0_raddr    = i_bundle0[15: 1];
    wire [31:0] bundle0_imm      = i_bundle0[47:16];
    wire [ 3:0] bundle0_pipeline = i_bundle0[51:48];
    wire [ 7:0] bundle0_xarith   = i_bundle0[59:52];
    wire [ 6:0] bundle0_xlogic   = i_bundle0[66:60];

    wire        bundle1_legal    = i_bundle1[ 0: 0];
    wire [14:0] bundle1_raddr    = i_bundle1[15: 1];
    wire [31:0] bundle1_imm      = i_bundle1[47:16];
    wire [ 3:0] bundle1_pipeline = i_bundle1[51:48];
    wire [ 7:0] bundle1_xarith   = i_bundle1[59:52];
    wire [ 6:0] bundle1_xlogic   = i_bundle1[66:60];

    // register addresses are used check for hazards
    wire [4:0] bundle0_rs1 = bundle0_raddr[ 4: 0];
    wire [4:0] bundle0_rs2 = bundle0_raddr[ 9: 5];
    wire [4:0] bundle0_rd  = bundle0_raddr[14:10];

    wire [4:0] bundle1_rs1 = bundle1_raddr[ 4: 0];
    wire [4:0] bundle1_rs2 = bundle1_raddr[ 9: 5];
    wire [4:0] bundle1_rd  = bundle1_raddr[14:10];

    // the first instruction (both in bundle order and in time) only needs to
    // wait until the reservation is free for all its source and destination
    // operands, and can then be piped into the right execution unit
    //
    // note that since at most two instructions are dispatched from the issue
    // stage on each cycle, it is possible to unconditionally "present" the
    // control signals for this instruction to the functional units and the
    // register file, but only mark "valid" based on
    // 1) which functional unit actually used for instruction, else don't care
    // 2) which functional unit is available in the case of duplicated
    //    backends (integer arithmetic and logic) (not implemented yet)
    // with the only caveat being that both instructions have bundles that
    // need to be muxed to each functional unit, which is relatively cheap
    //
    // if the functional unit is valid but not ready, issue stalls to maintain
    // in order dispatch
    wire bundle0_pipe_xarith = bundle0_pipeline == `PIPE_XARITH;
    wire bundle0_pipe_xlogic = bundle0_pipeline == `PIPE_XLOGIC;
    wire bundle0_pipe_xmultl = bundle0_pipeline == `PIPE_XMULTL;
    wire bundle0_pipe_xmulth = bundle0_pipeline == `PIPE_XMULTH;
    wire bundle0_pipe_xdiv   = bundle0_pipeline == `PIPE_XDIV;

    wire bundle1_pipe_xarith = bundle1_pipeline == `PIPE_XARITH;
    wire bundle1_pipe_xlogic = bundle1_pipeline == `PIPE_XLOGIC;
    wire bundle1_pipe_xmultl = bundle1_pipeline == `PIPE_XMULTL;
    wire bundle1_pipe_xmulth = bundle1_pipeline == `PIPE_XMULTH;
    wire bundle1_pipe_xdiv   = bundle1_pipeline == `PIPE_XDIV;

    wire xarith_opsel         = bundle0_pipe_xarith ? bundle0_xarith[1:0] : bundle1_xarith[1:0];
    wire xarith_sub           = bundle0_pipe_xarith ? bundle0_xarith[2] : bundle1_xarith[2];
    wire xarith_unsigned      = bundle0_pipe_xarith ? bundle0_xarith[3] : bundle1_xarith[3];
    wire xarith_cmp_mode      = bundle0_pipe_xarith ? bundle0_xarith[4] : bundle1_xarith[4];
    wire xarith_branch_equal  = bundle0_pipe_xarith ? bundle0_xarith[5] : bundle1_xarith[5];
    wire xarith_branch_invert = bundle0_pipe_xarith ? bundle0_xarith[6] : bundle1_xarith[6];
    wire xarith_word          = bundle0_pipe_xarith ? bundle0_xarith[7] : bundle1_xarith[7];

    wire xlogic_opsel  = bundle0_pipe_xlogic ? bundle0_xlogic[2:0] : bundle1_xlogic[2:0];
    wire xlogic_invert = bundle0_pipe_xlogic ? bundle0_xlogic[3]   : bundle1_xlogic[3];
    wire xlogic_sll    = bundle0_pipe_xlogic ? bundle0_xlogic[5:4] : bundle1_xlogic[5:4];
    wire xlogic_word   = bundle0_pipe_xlogic ? bundle0_xlogic[6]   : bundle1_xlogic[6];

    // dispatch enable for instruction 0 just involves checking rs1, rs2, and
    // rd against the reservation register to avoid RAW and WAW hazards
    // similar for instruction 1 but additional conflict logic below
    // TODO: this can be implemented more efficiently, but for now just
    // generate a bitmask and compare it against the reservation
    wire [31:0] bundle0_mask = (32'b1 << bundle0_rs1) | (32'b1 << bundle0_rs2) | (32'b1 << bundle0_rd);
    wire [31:0] bundle1_mask = (32'b1 << bundle1_rs1) | (32'b1 << bundle1_rs2) | (32'b1 << bundle1_rd);

    // instructions are ready once all their dependencies are ready and no
    // WAW hazards exist wrt. instructions already in the backend pipeline.
    // the second instruction must additionally wait for instruction 0 to
    // be ready to maintain in order dispatch, and check for a WAW hazard with
    // the first instruction
    // instruction 1 cannot dispatch if it writes to the same register as
    // instruction 0, since this could cause a WAW hazard if instruction 1
    // finishes first (can implement more complex logic here later on to
    // improve many cases)
    // FIXME: do we want a check against 0 here? check what RF does
    wire bundle1_waw = bundle0_rd == bundle1_rd;
    wire bundle0_ready = i_input_valid && ((reservation & bundle0_mask) == 32'h0);
    wire bundle1_ready = i_input_valid && ((reservation & bundle1_mask) == 32'h0) && bundle0_ready && !bundle1_waw;

    wire bundle0_dispatch_xarith = bundle0_pipe_xarith && bundle0_ready;
    wire bundle0_dispatch_xlogic = bundle0_pipe_xlogic && bundle0_ready;
    wire bundle0_dispatch_xmultl = bundle0_pipe_xmultl && bundle0_ready;
    wire bundle0_dispatch_xmulth = bundle0_pipe_xmulth && bundle0_ready;
    wire bundle0_dispatch_xdiv   = bundle0_pipe_xdiv   && bundle0_ready;

    wire bundle1_dispatch_xarith = !bundle0_pipe_xarith && bundle1_pipe_xarith && bundle1_ready;
    wire bundle1_dispatch_xlogic = !bundle0_pipe_xarith && bundle1_pipe_xlogic && bundle1_ready;
    wire bundle1_dispatch_xmultl = !bundle0_pipe_xmultl && bundle1_pipe_xmultl && bundle1_ready;
    wire bundle1_dispatch_xmulth = !bundle0_pipe_xmulth && bundle1_pipe_xmulth && bundle1_ready;
    wire bundle1_dispatch_xdiv   = !bundle0_pipe_xdiv   && bundle1_pipe_xdiv   && bundle1_ready;

    wire xarith_valid = bundle0_dispatch_xarith || bundle1_dispatch_xarith;
    wire xlogic_valid = bundle0_dispatch_xlogic || bundle1_dispatch_xlogic;

    // FIXME: what happens when we only dispatch one instruction? need to hold
    // state
    reg bundle0_transmit, bundle1_transmit, bundle0_done;
    always @(*) begin
        bundle0_transmit = 1'b0;
        bundle1_transmit = 1'b0;

        if (!bundle0_done) begin
            case (1'b1)
                bundle0_pipe_xarith: bundle0_transmit = bundle0_dispatch_xarith && i_xarith_ready;
                bundle0_pipe_xlogic: bundle0_transmit = bundle0_dispatch_xlogic && i_xlogic_ready;
                bundle0_pipe_xmultl: bundle0_transmit = bundle0_dispatch_xmultl && i_xmultl_ready;
                bundle0_pipe_xmulth: bundle0_transmit = bundle0_dispatch_xmulth && i_xmulth_ready;
                bundle0_pipe_xdiv  : bundle0_transmit = bundle0_dispatch_xdiv   && i_xdiv_ready;
            endcase
        end

        case (1'b1)
            bundle1_pipe_xarith: bundle1_transmit = bundle1_dispatch_xarith && i_xarith_ready;
            bundle1_pipe_xlogic: bundle1_transmit = bundle1_dispatch_xlogic && i_xlogic_ready;
            bundle1_pipe_xmultl: bundle1_transmit = bundle1_dispatch_xmultl && i_xmultl_ready;
            bundle1_pipe_xmulth: bundle1_transmit = bundle1_dispatch_xmulth && i_xmulth_ready;
            bundle1_pipe_xdiv  : bundle1_transmit = bundle1_dispatch_xdiv   && i_xdiv_ready;
        endcase
    end

    // when the first instruction is dispatched but the second isn't, the
    // issue unit stalls. however, to avoid re-dispatching the first
    // instruction, this bit keeps track of if the first instruction is done
    // and we are only waiting on the second
    always @(posedge i_clk, negedge i_rst_n) begin
        if (!i_rst_n)
            bundle0_done <= 1'b0;
        else if (bundle1_transmit)
            bundle0_done <= 1'b0;
        else if (bundle0_transmit)
            bundle0_done <= 1'b1;
    end

    reg input_ready;
    always @(posedge i_clk, negedge i_rst_n) begin
        if (!i_rst_n)
            input_ready <= 1'b1;
        else if (bundle1_transmit)
            input_ready <= 1'b1;
        else if (i_input_valid)
            input_ready <= 1'b0;
    end

    wire [31:0] bundle0_reserve = bundle0_mask & {32{bundle0_transmit}};
    wire [31:0] bundle1_reserve = bundle1_mask & {32{bundle1_transmit}};
    wire [31:0] retire  = i_inst0_retire & i_inst1_retire;
    wire [31:0] reserve = (bundle0_reserve | bundle1_reserve) & 32'hfffffffe;
    assign next_reservation = (reservation & ~retire) | reserve;

    assign o_input_ready = input_ready;

    assign o_xarith_banksel       = bundle1_pipe_xarith;
    assign o_xarith_opsel         = xarith_opsel;
    assign o_xarith_sub           = xarith_sub;
    assign o_xarith_unsigned      = xarith_unsigned;
    assign o_xarith_cmp_mode      = xarith_cmp_mode;
    assign o_xarith_branch_equal  = xarith_branch_equal;
    assign o_xarith_branch_invert = xarith_branch_invert;
    assign o_xarith_word          = xarith_word;
    assign o_xarith_valid         = xarith_valid;

    assign o_xlogic_banksel = bundle1_pipe_xlogic;
    assign o_xlogic_opsel   = xlogic_opsel;
    assign o_xlogic_invert  = xlogic_invert;
    assign o_xlogic_sll     = xlogic_sll;
    assign o_xlogic_word    = xlogic_word;
    assign o_xlogic_valid   = xlogic_valid;
endmodule

`default_nettype wire
