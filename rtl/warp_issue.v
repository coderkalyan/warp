`default_nettype none

`include "warp_defines.v"

module warp_issue (
    input  wire        i_clk,
    input  wire        i_rst_n,
    // receive zero or two instruction bundles per clock from the decode unit
    output wire        o_input_ready,
    input  wire        i_input_valid,
    input  wire [`BUNDLE_SIZE - 1:0] i_bundle0,
    input  wire [`BUNDLE_SIZE - 1:0] i_bundle1,
    // interface to integer arithmetic pipeline 0
    // xarith_op1 is always rs1
    // xarith_op2 is either rs2 or immediate
    // FIXME: implement this decode signal
    output wire [ 1:0] o_xarith0_opsel,
    output wire        o_xarith0_sub,
    output wire        o_xarith0_unsigned,
    output wire        o_xarith0_cmp_mode,
    output wire        o_xarith0_branch_equal,
    output wire        o_xarith0_branch_invert,
    output wire        o_xarith0_word,
    output wire        o_xarith0_valid,
    input  wire        i_xarith0_ready,
    // interface to integer arithmetic pipeline 1
    // xarith_op1 is always rs1
    // xarith_op2 is either rs2 or immediate
    // FIXME: implement this decode signal
    output wire [ 1:0] o_xarith1_opsel,
    output wire        o_xarith1_sub,
    output wire        o_xarith1_unsigned,
    output wire        o_xarith1_cmp_mode,
    output wire        o_xarith1_branch_equal,
    output wire        o_xarith1_branch_invert,
    output wire        o_xarith1_word,
    output wire        o_xarith1_valid,
    input  wire        i_xarith1_ready,
    // interface to integer logic pipeline 0
    // xlogic_op1 is always rs1
    // xlogic_op2 is either rs2 or immediate
    // FIXME: implement this decode signal
    output wire [ 2:0] o_xlogic0_opsel,
    output wire        o_xlogic0_invert,
    output wire [ 1:0] o_xlogic0_sll,
    output wire        o_xlogic0_word,
    output wire        o_xlogic0_valid,
    input  wire        i_xlogic0_ready,
    // interface to integer logic pipeline 1
    // xlogic_op1 is always rs1
    // xlogic_op2 is either rs2 or immediate
    // FIXME: implement this decode signal
    output wire [ 2:0] o_xlogic1_opsel,
    output wire        o_xlogic1_invert,
    output wire [ 1:0] o_xlogic1_sll,
    output wire        o_xlogic1_word,
    output wire        o_xlogic1_valid,
    input  wire        i_xlogic1_ready,
    // interface to integer shift/rotate pipeline
    // xshift_operand is always rs1
    // xshift_amount is either rs2 or immediate
    output wire [ 1:0] o_xshift_opsel,
    output wire        o_xshift_arithmetic,
    output wire        o_xshift_word,
    output wire        o_xshift_valid,
    input  wire        i_xshift_ready,
    // interface to integer lower 32 multiply
    // op1 is always rs1, op2 is always rs2
    output wire        o_xmultl_word,
    output wire        o_xmultl_valid,
    input  wire        i_xmultl_ready,
    // interface to integer upper 32 multiply
    // op1 is always rs1, op2 is always rs2
    output wire        o_xmulth_unsigned,
    output wire        o_xmulth_valid,
    input  wire        i_xmulth_ready,
    // interface to integer divide/remainder
    // op1 is always rs1, op2 is always rs2
    output wire        o_div_unsigned,
    output wire        o_div_word,
    output wire        o_xdiv_valid,
    input  wire        i_xdiv_ready
    // reading data from registers happens on the clock edge that an
    // instruction leaves issue and enters one of the functional units
    // it cannot be done earlier as instructions stall in issue until
    // dependencies are ready, and to avoid another pipeline stage for now,
    // the read results are wired directly to the execution units
    output wire [4:0]  o_rs1_addr,
    output wire [4:0]  o_rs2_addr,
    output wire [4:0]  o_rs3_addr,
    output wire [4:0]  o_rs4_addr
);
    // currently, both RAW and WAW hazards are handled with a reservation
    // register that keeps track of "in flight" destination registers
    // these are marked by issue when dispatching an instruction and cleared
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
    reg [31:0] reservation;

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

    wire [4:0] bundle0_rs1 = bundle0_raddr[ 4: 0];
    wire [4:0] bundle0_rs2 = bundle0_raddr[ 9: 5];
    wire [4:0] bundle0_rd  = bundle0_raddr[14:10];

    wire [4:0] bundle1_rs1 = bundle1_raddr[ 4: 0];
    wire [4:0] bundle1_rs2 = bundle1_raddr[ 9: 5];
    wire [4:0] bundle1_rd  = bundle1_raddr[14:10];

    // the first instruction (both in bundle order and in time) only needs to
    // wait until the reservation is free for all its source and destination
    // operands, and can then be piped into the right execution unit
    // note that since at most two instructions are dispatched from the issue
    // stage on each cycle, it is possible to unconditionally "present" the
    // control signals for this instruction to the functional units and the
    // register file, but only mark "valid" based on
    // 1) which functional unit actually used for instruction, else don't care
    // 2) which functional unit is available in the case of duplicated
    //    backends (integer arithmetic and logic)
    // with the only caveat being that both instructions have bundles that
    // need to be muxed to each functional unit, which is relatively cheap
    // if the functional unit is valid but not ready, issue stalls to maintain
    // in order dispatch
    // TODO: this means that the instruction will not obey read valid
    // interface semantics, but thats *fine* as long as we test correctly
    wire bundle0_pipe_xarith = bundle0_pipeline == `PIPE_XARITH;
    wire bundle0_pipe_xlogic = bundle0_pipeline == `PIPE_XLOGIC;
    wire bundle0_pipe_xmultl = bundle0_pipeline == `PIPE_XMULTL;
    wire bundle0_pipe_xmulth = bundle0_pipeline == `PIPE_XMULTH;
    wire bundle0_pipe_xdiv   = bundle0_pipeline == `PIPE_XDIV;
    wire bundle0_pipe_xarith0 = bundle0_pipe_xarith;
    wire bundle0_pipe_xarith1 = bundle0_pipe_xarith && !i_xarith0_ready;
    wire bundle0_pipe_xlogic0 = bundle0_pipe_xlogic;
    wire bundle0_pipe_xlogic1 = bundle0_pipe_xlogic && !i_xlogic0_ready;

    wire xarith0_opsel         = bundle0_pipe_xarith0 ? bundle0_xarith[1:0] : bundle1_xarith[1:0];
    wire xarith0_sub           = bundle0_pipe_xarith0 ? bundle0_xarith[2] : bundle1_xarith[2];
    wire xarith0_unsigned      = bundle0_pipe_xarith0 ? bundle0_xarith[3] : bundle1_xarith[3];
    wire xarith0_cmp_mode      = bundle0_pipe_xarith0 ? bundle0_xarith[4] : bundle1_xarith[4];
    wire xarith0_branch_equal  = bundle0_pipe_xarith0 ? bundle0_xarith[5] : bundle1_xarith[5];
    wire xarith0_branch_invert = bundle0_pipe_xarith0 ? bundle0_xarith[6] : bundle1_xarith[6];

    wire xarith1_opsel         = bundle0_pipe_xarith1 ? bundle0_xarith[1:0] : bundle1_xarith[1:0];
    wire xarith1_sub           = bundle0_pipe_xarith1 ? bundle0_xarith[2] : bundle1_xarith[2];
    wire xarith1_unsigned      = bundle0_pipe_xarith1 ? bundle0_xarith[3] : bundle1_xarith[3];
    wire xarith1_cmp_mode      = bundle0_pipe_xarith1 ? bundle0_xarith[4] : bundle1_xarith[4];
    wire xarith1_branch_equal  = bundle0_pipe_xarith1 ? bundle0_xarith[5] : bundle1_xarith[5];
    wire xarith1_branch_invert = bundle0_pipe_xarith1 ? bundle0_xarith[6] : bundle1_xarith[6];

    wire xlogic0_opsel  = bundle0_pipe_xlogic0 ? bundle0_xlogic[2:0] : bundle1_xlogic[2:0];
    wire xlogic0_invert = bundle0_pipe_xlogic0 ? bundle0_xlogic[3]   : bundle1_xlogic[3];
    wire xlogic0_sll    = bundle0_pipe_xlogic0 ? bundle0_xlogic[5:4] : bundle1_xlogic[5:4];
    wire xlogic0_word   = bundle0_pipe_xlogic0 ? bundle0_xlogic[6]   : bundle1_xlogic[6];

    wire xlogic1_opsel  = bundle0_pipe_xlogic1 ? bundle0_xlogic[2:0] : bundle1_xlogic[2:0];
    wire xlogic1_invert = bundle0_pipe_xlogic1 ? bundle0_xlogic[3]   : bundle1_xlogic[3];
    wire xlogic1_sll    = bundle0_pipe_xlogic1 ? bundle0_xlogic[5:4] : bundle1_xlogic[5:4];
    wire xlogic1_word   = bundle0_pipe_xlogic1 ? bundle0_xlogic[6]   : bundle1_xlogic[6];

    // dispatch enable for instruction 0 just involves checking rs1, rs2, and
    // rd against the reservation register to avoid RAW and WAW hazards
    // similar for instruction 1 but additional conflict logic below
    reg inst0_stall_rs1, inst0_stall_rs2, inst0_stall_rd; 
    reg inst1_stall_rs1, inst1_stall_rs2, inst1_stall_rd; 
    integer i;
    always @(*) begin
        inst0_stall_rs1 = 1'b0;
        inst0_stall_rs2 = 1'b0;
        inst0_stall_rd  = 1'b0;
        inst1_stall_rs1 = 1'b0;
        inst1_stall_rs2 = 1'b0;
        inst1_stall_rd  = 1'b0;

        for (i = 0; i < 32; i = i + 1) begin
            if ((i == bundle0_rs1) && reservation[i])
                inst0_stall_rs1 = 1'b1;
            if ((i == bundle0_rs2) && reservation[i])
                inst0_stall_rs2 = 1'b1;
            if ((i == bundle0_rd) && reservation[i])
                inst0_stall_rd = 1'b1;

            if ((i == bundle1_rs1) && reservation[i])
                inst1_stall_rs1 = 1'b1;
            if ((i == bundle1_rs2) && reservation[i])
                inst1_stall_rs2 = 1'b1;
            if ((i == bundle1_rd) && reservation[i])
                inst1_stall_rd = 1'b1;
        end
    end

    // instructions are ready once all their dependencies are ready
    // this doesn't mean that they will dispatch, only that there are
    // no data hazards wrt. instructions already in the backend pipeline
    wire bundle0_ready = !inst0_stall_rs1 && !inst0_stall_rs2 && !inst0_stall_rd;
    wire bundle1_ready = !inst1_stall_rs1 && !inst1_stall_rs2 && !inst1_stall_rd;

    // instruction 1 cannot dispatch if it writes to the same register as
    // instruction 0, since this could cause a WAW hazard if instruction 1
    // finishes first (can implement more complex logic here later on to
    // improve many cases)
    // FIXME: do we want a check against 0 here? check what RF does
    wire bundle1_waw = bundle0_rd == bundle1_rd;

    wire bundle1_pipe_xarith = bundle1_pipeline == `PIPE_XARITH;
    wire bundle1_pipe_xlogic = bundle1_pipeline == `PIPE_XLOGIC;
    wire bundle1_pipe_xmultl = bundle1_pipeline == `PIPE_XMULTL;
    wire bundle1_pipe_xmulth = bundle1_pipeline == `PIPE_XMULTH;
    wire bundle1_pipe_xdiv   = bundle1_pipeline == `PIPE_XDIV;
    wire bundle1_pipe_xarith0 = !bundle1_pipe_xarith;
    wire bundle1_pipe_xarith1 = bundle1_pipe_xarith && !i_xarith0_ready;
    wire bundle1_pipe_xlogic0 = bundle1_pipe_xlogic;
    wire bundle1_pipe_xlogic1 = bundle1_pipe_xlogic && !i_xlogic0_ready;

    wire bundle0_dispatch = bundle0_ready;
    wire bundle1_dispatch = bundle0_dispatch && bundle1_ready && !bundle1_waw;

    assign o_xarith0_opsel         = xarith0_opsel;
    assign o_xarith0_sub           = xarith0_sub;
    assign o_xarith0_unsigned      = xarith0_unsigned;
    assign o_xarith0_cmp_mode      = xarith0_cmp_mode;
    assign o_xarith0_branch_equal  = xarith0_branch_equal;
    assign o_xarith0_branch_invert = xarith0_branch_invert;
    assign o_xarith0_valid         = (bundle0_pipe_xarith0 && bundle0_dispatch) || (bundle1_pipe_xarith0 && ;

    assign o_xarith1_opsel         = xarith1_opsel;
    assign o_xarith1_sub           = xarith1_sub;
    assign o_xarith1_unsigned      = xarith1_unsigned;
    assign o_xarith1_cmp_mode      = xarith1_cmp_mode;
    assign o_xarith1_branch_equal  = xarith1_branch_equal;
    assign o_xarith1_branch_invert = xarith1_branch_invert;
    assign o_xarith1_valid         = bundle0_pipe_xarith1 && bundle0_ready;

    assign o_xlogic0_opsel  = xlogic0_opsel;
    assign o_xlogic0_invert = xlogic0_invert;
    assign o_xlogic0_sll    = xlogic0_sll;
    assign o_xlogic0_word   = xlogic0_word;
    assign o_xlogic0_valid  = bundle0_pipe_xlogic0 && bundle0_ready;

    assign o_xlogic1_opsel  = xlogic1_opsel;
    assign o_xlogic1_invert = xlogic1_invert;
    assign o_xlogic1_sll    = xlogic1_sll;
    assign o_xlogic1_word   = xlogic1_word;
    assign o_xlogic1_valid  = bundle0_pipe_xlogic1 && bundle0_ready;
endmodule

`default_nettype wire
