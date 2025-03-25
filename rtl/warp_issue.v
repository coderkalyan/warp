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
`ifdef RISCV_FORMAL
    `RVFI_METADATA_INPUTS(ch0),
    `RVFI_PC_INPUTS(ch0),
    `RVFI_REG_INPUTS(ch0),
    `RVFI_METADATA_INPUTS(ch1),
    `RVFI_PC_INPUTS(ch1),
    `RVFI_REG_INPUTS(ch1),
`endif
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
    output wire        o_xarith_banksel, // (rs1, rs2) or (rs3, rs4)
    output wire        o_xarith_op2_sel,
    output wire [63:0] o_xarith_imm,
    output wire [ 1:0] o_xarith_opsel,
    output wire        o_xarith_sub,
    output wire        o_xarith_unsigned,
    output wire        o_xarith_cmp_mode,
    output wire        o_xarith_branch_equal,
    output wire        o_xarith_branch_invert,
    output wire        o_xarith_word,
    output wire [ 4:0] o_xarith_rd,
    output wire        o_xarith_valid,
    input  wire        i_xarith_ready,
`ifdef RISCV_FORMAL
    `RVFI_METADATA_OUTPUTS(xarith),
    `RVFI_PC_OUTPUTS(xarith),
    `RVFI_REG_OUTPUTS(xarith),
`endif
    // interface to integer logic pipeline
    // op1 is always rs1, op2 is either rs2 or immediate
    output wire        o_xlogic_banksel, // (rs1, rs2) or (rs3, rs4)
    output wire        o_xlogic_op2_sel,
    output wire [63:0] o_xlogic_imm,
    output wire [ 2:0] o_xlogic_opsel,
    output wire        o_xlogic_invert,
    output wire [ 1:0] o_xlogic_sll,
    output wire        o_xlogic_word,
    output wire [ 4:0] o_xlogic_rd,
    output wire        o_xlogic_valid,
    input  wire        i_xlogic_ready,
`ifdef RISCV_FORMAL
    `RVFI_METADATA_OUTPUTS(xlogic),
    `RVFI_PC_OUTPUTS(xlogic),
    `RVFI_REG_OUTPUTS(xlogic),
`endif
    // interface to integer shift/rotate pipeline
    // xshift_operand is always rs1
    // xshift_amount is either rs2 or immediate
    output wire        o_xshift_banksel, // (rs1, rs2) or (rs3, rs4)
    output wire        o_xshift_op2_sel,
    output wire [ 5:0] o_xshift_imm,
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
    wire [31:0] bundle0_imm32    = i_bundle0[47:16];
    wire [ 3:0] bundle0_pipeline = i_bundle0[51:48];
    wire [ 0:0] bundle0_shared   = i_bundle0[52:52];
    wire [ 7:0] bundle0_xarith   = i_bundle0[60:53];
    wire [ 6:0] bundle0_xlogic   = i_bundle0[67:61];

    wire        bundle1_legal    = i_bundle1[ 0: 0];
    wire [14:0] bundle1_raddr    = i_bundle1[15: 1];
    wire [31:0] bundle1_imm32    = i_bundle1[47:16];
    wire [ 3:0] bundle1_pipeline = i_bundle1[51:48];
    wire [ 0:0] bundle1_shared   = i_bundle1[52:52];
    wire [ 7:0] bundle1_xarith   = i_bundle1[60:53];
    wire [ 6:0] bundle1_xlogic   = i_bundle1[67:61];

    // immediates are at most 32 bits in the instruction (actually less),
    // so sign extend them here to 64 bits
    // this is done here instead of in the decoder to save interconnect
    // resources between decode and issue but may be revisited
    wire [63:0] bundle0_imm = {{32{bundle0_imm32[31]}}, bundle0_imm32};
    wire [63:0] bundle1_imm = {{32{bundle1_imm32[31]}}, bundle1_imm32};

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
    wire bundle0_pipe_xarith = bundle0_pipeline == `PIPELINE_XARITH;
    wire bundle0_pipe_xlogic = bundle0_pipeline == `PIPELINE_XLOGIC;
    wire bundle0_pipe_xmultl = bundle0_pipeline == `PIPELINE_XMULTL;
    wire bundle0_pipe_xmulth = bundle0_pipeline == `PIPELINE_XMULTH;
    wire bundle0_pipe_xdiv   = bundle0_pipeline == `PIPELINE_XDIV;

    wire bundle1_pipe_xarith = bundle1_pipeline == `PIPELINE_XARITH;
    wire bundle1_pipe_xlogic = bundle1_pipeline == `PIPELINE_XLOGIC;
    wire bundle1_pipe_xmultl = bundle1_pipeline == `PIPELINE_XMULTL;
    wire bundle1_pipe_xmulth = bundle1_pipeline == `PIPELINE_XMULTH;
    wire bundle1_pipe_xdiv   = bundle1_pipeline == `PIPELINE_XDIV;

    // switch xarith control signals based on port usage
    wire [63:0] xarith_imm    = bundle0_pipe_xarith ? bundle0_imm         : bundle1_imm;
    wire [ 1:0] xarith_opsel  = bundle0_pipe_xarith ? bundle0_xarith[1:0] : bundle1_xarith[1:0];
    wire xarith_sub           = bundle0_pipe_xarith ? bundle0_xarith[2]   : bundle1_xarith[2];
    wire xarith_unsigned      = bundle0_pipe_xarith ? bundle0_xarith[3]   : bundle1_xarith[3];
    wire xarith_cmp_mode      = bundle0_pipe_xarith ? bundle0_xarith[4]   : bundle1_xarith[4];
    wire xarith_branch_equal  = bundle0_pipe_xarith ? bundle0_xarith[5]   : bundle1_xarith[5];
    wire xarith_branch_invert = bundle0_pipe_xarith ? bundle0_xarith[6]   : bundle1_xarith[6];
    wire xarith_word          = bundle0_pipe_xarith ? bundle0_xarith[7]   : bundle1_xarith[7];
    wire xarith_op2_sel       = bundle0_pipe_xarith ? bundle0_shared[0]   : bundle1_shared[0];
    wire [ 4:0] xarith_rd     = bundle0_pipe_xarith ? bundle0_rd          : bundle1_rd;
`ifdef RISCV_FORMAL
    wire [63:0] f_valid_xarith;
    wire [63:0] f_order_xarith     = bundle0_pipe_xarith ? if_order_ch0     : if_order_ch1;
    wire [31:0] f_insn_xarith      = bundle0_pipe_xarith ? if_insn_ch0      : if_insn_ch1;
    wire        f_trap_xarith      = bundle0_pipe_xarith ? if_trap_ch0      : if_trap_ch1;
    wire        f_halt_xarith      = bundle0_pipe_xarith ? if_halt_ch0      : if_halt_ch1;
    wire        f_intr_xarith      = bundle0_pipe_xarith ? if_intr_ch0      : if_intr_ch1;
    wire [ 1:0] f_mode_xarith      = bundle0_pipe_xarith ? if_mode_ch0      : if_mode_ch1;
    wire [ 1:0] f_ixl_xarith       = bundle0_pipe_xarith ? if_ixl_ch0       : if_ixl_ch1;
    wire [63:0] f_pc_rdata_xarith  = bundle0_pipe_xarith ? if_pc_rdata_ch0  : if_pc_rdata_ch1;
    wire [63:0] f_pc_wdata_xarith  = bundle0_pipe_xarith ? if_pc_wdata_ch0  : if_pc_wdata_ch1;
    wire [ 4:0] f_rs1_addr_xarith  = bundle0_pipe_xarith ? if_rs1_addr_ch0  : if_rs1_addr_ch1;
    wire [ 4:0] f_rs2_addr_xarith  = bundle0_pipe_xarith ? if_rs2_addr_ch0  : if_rs2_addr_ch1;
    wire [63:0] f_rs1_rdata_xarith = bundle0_pipe_xarith ? if_rs1_rdata_ch0 : if_rs1_rdata_ch1;
    wire [63:0] f_rs2_rdata_xarith = bundle0_pipe_xarith ? if_rs2_rdata_ch0 : if_rs2_rdata_ch1;
    wire [ 4:0] f_rd_addr_xarith   = bundle0_pipe_xarith ? if_rd_addr_ch0   : if_rd_addr_ch1;
    wire [63:0] f_rd_wdata_xarith  = bundle0_pipe_xarith ? if_rd_wdata_ch0  : if_rd_wdata_ch1;
`endif

    // switch xlogic control signals based on port usage
    wire [63:0] xlogic_imm   = bundle0_pipe_xlogic ? bundle0_imm         : bundle1_imm;
    wire [ 2:0] xlogic_opsel = bundle0_pipe_xlogic ? bundle0_xlogic[2:0] : bundle1_xlogic[2:0];
    wire xlogic_invert       = bundle0_pipe_xlogic ? bundle0_xlogic[3]   : bundle1_xlogic[3];
    wire xlogic_sll          = bundle0_pipe_xlogic ? bundle0_xlogic[5:4] : bundle1_xlogic[5:4];
    wire xlogic_word         = bundle0_pipe_xlogic ? bundle0_xlogic[6]   : bundle1_xlogic[6];
    wire xlogic_op2_sel      = bundle0_pipe_xlogic ? bundle0_shared[0]   : bundle1_shared[0];
    wire [ 4:0] xlogic_rd    = bundle0_pipe_xlogic ? bundle0_rd          : bundle1_rd;
`ifdef RISCV_FORMAL
    wire        f_valid_xlogic;
    wire [63:0] f_order_xlogic     = bundle0_pipe_xlogic ? if_order_ch0     : if_order_ch1;
    wire [31:0] f_insn_xlogic      = bundle0_pipe_xlogic ? if_insn_ch0      : if_insn_ch1;
    wire        f_trap_xlogic      = bundle0_pipe_xlogic ? if_trap_ch0      : if_trap_ch1;
    wire        f_halt_xlogic      = bundle0_pipe_xlogic ? if_halt_ch0      : if_halt_ch1;
    wire        f_intr_xlogic      = bundle0_pipe_xlogic ? if_intr_ch0      : if_intr_ch1;
    wire [ 1:0] f_mode_xlogic      = bundle0_pipe_xlogic ? if_mode_ch0      : if_mode_ch1;
    wire [ 1:0] f_ixl_xlogic       = bundle0_pipe_xlogic ? if_ixl_ch0       : if_ixl_ch1;
    wire [63:0] f_pc_rdata_xlogic  = bundle0_pipe_xlogic ? if_pc_rdata_ch0  : if_pc_rdata_ch1;
    wire [63:0] f_pc_wdata_xlogic  = bundle0_pipe_xlogic ? if_pc_wdata_ch0  : if_pc_wdata_ch1;
    wire [ 4:0] f_rs1_addr_xlogic  = bundle0_pipe_xlogic ? if_rs1_addr_ch0  : if_rs1_addr_ch1;
    wire [ 4:0] f_rs2_addr_xlogic  = bundle0_pipe_xlogic ? if_rs2_addr_ch0  : if_rs2_addr_ch1;
    wire [63:0] f_rs1_rdata_xlogic = bundle0_pipe_xlogic ? if_rs1_rdata_ch0 : if_rs1_rdata_ch1;
    wire [63:0] f_rs2_rdata_xlogic = bundle0_pipe_xlogic ? if_rs2_rdata_ch0 : if_rs2_rdata_ch1;
    wire [ 4:0] f_rd_addr_xlogic   = bundle0_pipe_xlogic ? if_rd_addr_ch0   : if_rd_addr_ch1;
    wire [63:0] f_rd_wdata_xlogic  = bundle0_pipe_xlogic ? if_rd_wdata_ch0  : if_rd_wdata_ch1;
`endif

    // pull out the op2 select signal from the bundle for use in reservation
    // masking
    wire bundle0_op2_sel = bundle0_shared[0];
    wire bundle1_op2_sel = bundle1_shared[0];

    // dispatch enable for instruction 0 just involves checking rs1, rs2, and
    // rd against the reservation register to avoid RAW and WAW hazards
    // similar for instruction 1 but additional conflict logic below
    // TODO: this can be implemented more efficiently, but for now just
    // generate a bitmask and compare it against the reservation
    wire [31:0] bundle0_rs1_mask = (32'b1 << bundle0_rs1);
    wire [31:0] bundle0_rs2_mask = (32'b1 << bundle0_rs2) & {32{!bundle0_op2_sel}};
    wire [31:0] bundle0_rd_mask  = (32'b1 << bundle0_rd);
    wire [31:0] bundle1_rs1_mask = (32'b1 << bundle1_rs1);
    wire [31:0] bundle1_rs2_mask = (32'b1 << bundle1_rs2) & {32{!bundle1_op2_sel}};
    wire [31:0] bundle1_rd_mask  = (32'b1 << bundle1_rd);
    wire [31:0] bundle0_mask = bundle0_rs1_mask | bundle0_rs2_mask | bundle0_rd_mask;
    wire [31:0] bundle1_mask = bundle1_rs1_mask | bundle1_rs2_mask | bundle1_rd_mask;

    // instructions are ready once all their dependencies are ready and no
    // WAW hazards exist wrt. instructions already in the backend pipeline.
    // the second instruction must additionally wait for instruction 0 to
    // be ready to maintain in order dispatch, and check for a WAW hazard with
    // the first instruction
    // instruction 1 cannot dispatch if it writes to the same register as
    // instruction 0, since this could cause a WAW hazard if instruction 1
    // finishes first (can implement more complex logic here later on to
    // improve many cases)
    //
    // once bundle0 is dispatched, bundle1_waw is no longer asserted,
    // but the instruction will not be dispatched incorrectly because the
    // destination register will be marked in the reservation register
    // FIXME: do we want a check against 0 here? check what RF does
    wire bundle1_waw = (bundle0_rd == bundle1_rd) && !bundle0_done;
    wire bundle0_ready = i_input_valid && ((reservation & bundle0_mask) == 32'h0);
    wire bundle1_ready = i_input_valid && ((reservation & bundle1_mask) == 32'h0) && (bundle0_ready || bundle0_done) && !bundle1_waw;

    wire bundle0_dispatch_xarith = bundle0_pipe_xarith && bundle0_ready;
    wire bundle0_dispatch_xlogic = bundle0_pipe_xlogic && bundle0_ready;
    wire bundle0_dispatch_xmultl = bundle0_pipe_xmultl && bundle0_ready;
    wire bundle0_dispatch_xmulth = bundle0_pipe_xmulth && bundle0_ready;
    wire bundle0_dispatch_xdiv   = bundle0_pipe_xdiv   && bundle0_ready;

    wire bundle1_dispatch_xarith = (!bundle0_pipe_xarith || bundle0_done) && bundle1_pipe_xarith && bundle1_ready;
    wire bundle1_dispatch_xlogic = (!bundle0_pipe_xlogic || bundle0_done) && bundle1_pipe_xlogic && bundle1_ready;
    wire bundle1_dispatch_xmultl = (!bundle0_pipe_xmultl || bundle0_done) && bundle1_pipe_xmultl && bundle1_ready;
    wire bundle1_dispatch_xmulth = (!bundle0_pipe_xmulth || bundle0_done) && bundle1_pipe_xmulth && bundle1_ready;
    wire bundle1_dispatch_xdiv   = (!bundle0_pipe_xdiv   || bundle0_done) && bundle1_pipe_xdiv   && bundle1_ready;

    wire xarith_valid = bundle0_dispatch_xarith || bundle1_dispatch_xarith;
    wire xlogic_valid = bundle0_dispatch_xlogic || bundle1_dispatch_xlogic;
    assign f_valid_xarith = xarith_valid;
    assign f_valid_xlogic = xlogic_valid;

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

    wire input_ready = bundle1_transmit;

    wire [31:0] bundle0_reserve = bundle0_rd_mask & {32{bundle0_transmit}};
    wire [31:0] bundle1_reserve = bundle1_rd_mask & {32{bundle1_transmit}};
    wire [31:0] retire  = i_inst0_retire | i_inst1_retire;
    wire [31:0] reserve = (bundle0_reserve | bundle1_reserve) & 32'hfffffffe;
    assign next_reservation = (reservation & ~retire) | reserve;

    reg [4:0] r_rs1_addr, r_rs2_addr, r_rs3_addr, r_rs4_addr;
    always @(posedge i_clk, negedge i_rst_n) begin
        if (!i_rst_n) begin
            r_rs1_addr <= 5'd0;
            r_rs2_addr <= 5'd0;
            r_rs3_addr <= 5'd0;
            r_rs4_addr <= 5'd0;
        end else begin
            r_rs1_addr <= bundle0_rs1;
            r_rs2_addr <= bundle0_rs2;
            r_rs3_addr <= bundle1_rs1;
            r_rs4_addr <= bundle1_rs2;
        end
    end

    reg        r_xarith_banksel, r_xarith_op2_sel;
    reg [63:0] r_xarith_imm;
    reg [ 1:0] r_xarith_opsel;
    reg        r_xarith_sub, r_xarith_unsigned, r_xarith_cmp_mode;
    reg        r_xarith_branch_equal, r_xarith_branch_invert;
    reg        r_xarith_word, r_xarith_valid;
    reg [ 4:0] r_xarith_rd;
    always @(posedge i_clk, negedge i_rst_n) begin
        if (!i_rst_n) begin
            r_xarith_banksel       <= 1'b0;
            r_xarith_op2_sel       <= 1'b0;
            r_xarith_imm           <= 64'h0;
            r_xarith_opsel         <= 2'b00;
            r_xarith_sub           <= 1'b0;
            r_xarith_unsigned      <= 1'b0;
            r_xarith_cmp_mode      <= 1'b0;
            r_xarith_branch_equal  <= 1'b0;
            r_xarith_branch_invert <= 1'b0;
            r_xarith_word          <= 1'b0;
            r_xarith_valid         <= 1'b0;
            r_xarith_rd            <= 5'h0;
        end else begin
            r_xarith_banksel       <= bundle1_pipe_xarith;
            r_xarith_op2_sel       <= xarith_op2_sel;
            r_xarith_imm           <= xarith_imm;
            r_xarith_opsel         <= xarith_opsel;
            r_xarith_sub           <= xarith_sub;
            r_xarith_unsigned      <= xarith_unsigned;
            r_xarith_cmp_mode      <= xarith_cmp_mode;
            r_xarith_branch_equal  <= xarith_branch_equal;
            r_xarith_branch_invert <= xarith_branch_invert;
            r_xarith_word          <= xarith_word;
            r_xarith_valid         <= xarith_valid;
            r_xarith_rd            <= xarith_rd;
        end
    end

    reg        r_xlogic_banksel, r_xlogic_op2_sel;
    reg [63:0] r_xlogic_imm;
    reg [ 2:0] r_xlogic_opsel;
    reg        r_xlogic_invert, r_xlogic_word, r_xlogic_valid;
    reg [ 1:0] r_xlogic_sll;
    reg [ 4:0] r_xlogic_rd;
    always @(posedge i_clk, negedge i_rst_n) begin
        if (!i_rst_n) begin
            r_xlogic_banksel <= 1'b0;
            r_xlogic_op2_sel <= 1'b0;
            r_xlogic_imm     <= 64'h0;
            r_xlogic_opsel   <= 3'b000;
            r_xlogic_invert  <= 1'b0;
            r_xlogic_sll     <= 1'b0;
            r_xlogic_word    <= 1'b0;
            r_xlogic_valid   <= 1'b0;
            r_xlogic_rd      <= 5'h0;
        end else begin
            r_xlogic_banksel <= bundle1_pipe_xlogic;
            r_xlogic_op2_sel <= xlogic_op2_sel;
            r_xlogic_imm     <= xlogic_imm;
            r_xlogic_opsel   <= xlogic_opsel;
            r_xlogic_invert  <= xlogic_invert;
            r_xlogic_sll     <= xlogic_sll;
            r_xlogic_word    <= xlogic_word;
            r_xlogic_valid   <= xlogic_valid;
            r_xlogic_rd      <= xlogic_rd;
        end
    end

`ifdef RISCV_FORMAL
    reg        rf_xarith_valid, rf_xlogic_valid;
    reg [31:0] rf_xarith_inst, rf_xlogic_inst;
    reg [63:0] rf_xarith_order, rf_xlogic_order;
    always @(posedge i_clk, negedge i_rst_n) begin
        if (!i_rst_n) begin
            rf_xarith_valid <= 1'b0;
            rf_xarith_inst  <= 32'h0;
            rf_xarith_order <= 64'h0;
            rf_xlogic_valid <= 1'b0;
            rf_xlogic_inst  <= 32'h0;
            rf_xlogic_order <= 64'h0;
        end else begin
            // rf_xarith_valid <= f_xarith_valid;
            // rf_xarith_inst  <= f_xarith_inst;
            // rf_xarith_order <= f_xarith_order;
            // rf_xlogic_valid <= f_xlogic_valid;
            // rf_xlogic_inst  <= f_xlogic_inst;
            // rf_xlogic_order <= f_xlogic_order;
        end
    end
`endif

    assign o_input_ready = input_ready;
    assign o_rs1_addr    = r_rs1_addr;
    assign o_rs2_addr    = r_rs2_addr;
    assign o_rs3_addr    = r_rs3_addr;
    assign o_rs4_addr    = r_rs4_addr;

    assign o_xarith_banksel       = r_xarith_banksel;
    assign o_xarith_op2_sel       = r_xarith_op2_sel;
    assign o_xarith_imm           = r_xarith_imm;
    assign o_xarith_opsel         = r_xarith_opsel;
    assign o_xarith_sub           = r_xarith_sub;
    assign o_xarith_unsigned      = r_xarith_unsigned;
    assign o_xarith_cmp_mode      = r_xarith_cmp_mode;
    assign o_xarith_branch_equal  = r_xarith_branch_equal;
    assign o_xarith_branch_invert = r_xarith_branch_invert;
    assign o_xarith_word          = r_xarith_word;
    assign o_xarith_rd            = r_xarith_rd;
    assign o_xarith_valid         = r_xarith_valid;

    assign o_xlogic_banksel = r_xlogic_banksel;
    assign o_xlogic_op2_sel = r_xlogic_op2_sel;
    assign o_xlogic_imm     = r_xlogic_imm;
    assign o_xlogic_opsel   = r_xlogic_opsel;
    assign o_xlogic_invert  = r_xlogic_invert;
    assign o_xlogic_sll     = r_xlogic_sll;
    assign o_xlogic_word    = r_xlogic_word;
    assign o_xlogic_rd      = r_xlogic_rd;
    assign o_xlogic_valid   = r_xlogic_valid;

// `ifdef RISCV_FORMAL
//     assign of_xarith_valid = rf_xarith_valid;
//     assign of_xarith_inst  = rf_xarith_inst;
//     assign of_xarith_order = rf_xarith_order;
//     assign of_xlogic_valid = rf_xlogic_valid;
//     assign of_xlogic_inst  = rf_xlogic_inst;
//     assign of_xlogic_order = rf_xlogic_order;
// `endif
endmodule

`default_nettype wire
