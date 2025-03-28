`default_nettype none

`include "warp_defines.v"

module warp_decode (
    input  wire        i_clk,
    input  wire        i_rst_n,
    // if fetch cannot deliver any instructions, i_input_valid is not
    // asserted. if fetch only has one valid instruction, it pads the
    // stream with a nop (which is discarded by the issue stage down
    // the pipeline)
    // in the future, this can be replaced with an output instruction
    // count and a dual issue FIFO (with skid buffer functionality)
    output wire        o_input_ready,
    input  wire        i_input_valid,
    input  wire [31:0] i_inst0,
    input  wire [31:0] i_inst1,
    input  wire [1:0]  i_compressed,
`ifdef RISCV_FORMAL
    `RVFI_METADATA_INPUTS(ch0),
    `RVFI_PC_INPUTS(ch0),
    `RVFI_METADATA_INPUTS(ch1),
    `RVFI_PC_INPUTS(ch1),

    `RVFI_METADATA_OUTPUTS(ch0),
    `RVFI_PC_OUTPUTS(ch0),
    `RVFI_REG_OUTPUTS(ch0),
    `RVFI_METADATA_OUTPUTS(ch1),
    `RVFI_PC_OUTPUTS(ch1),
    `RVFI_REG_OUTPUTS(ch1),
`endif
    // after consuming two instructions from fetch and decoding them, this
    // unit always presents both as valid on the next cycle. however, if
    // issue is not ready (i_output_ready), this unit has to hold the two
    // instructions (like an integrated skid buffer)
    input  wire        i_output_ready,
    output wire        o_output_valid,
    output wire [`BUNDLE_SIZE - 1:0] o_bundle0,
    output wire [`BUNDLE_SIZE - 1:0] o_bundle1
);
    wire [31:0] decode_inst     [1:0];
    wire        decode_legal    [1:0];
    wire [14:0] decode_raddr    [1:0];
    wire [31:0] decode_imm      [1:0]; // TODO: consider reducing imm size by doing signext later
    wire [3:0]  decode_pipeline [1:0];
    wire [0:0]  decode_shared   [1:0];
    wire [7:0]  decode_xarith   [1:0];
    wire [6:0]  decode_xlogic   [1:0];
    wire [`BUNDLE_SIZE - 1:0] decode_bundle [1:0];

    // can't assign both of these inline due to verilog syntax limitations
    assign decode_inst[0] = i_inst0;
    assign decode_inst[1] = i_inst1;

    genvar i;
    generate
        for (i = 0; i < 2; i = i + 1) begin
            warp_udecode udecode (
                .i_inst(decode_inst[i]),
                .o_legal(decode_legal[i]),
                .o_raddr(decode_raddr[i]),
                .o_imm(decode_imm[i]),
                .o_pipeline(decode_pipeline[i]),
                .o_shared(decode_shared[i]),
                .o_xarith(decode_xarith[i]),
                .o_xlogic(decode_xlogic[i])
            );

            assign decode_bundle[i][ 0: 0] = decode_legal[i];
            assign decode_bundle[i][15: 1] = decode_raddr[i];
            assign decode_bundle[i][47:16] = decode_imm[i];
            assign decode_bundle[i][51:48] = decode_pipeline[i];
            assign decode_bundle[i][52:52] = decode_shared[i];
            assign decode_bundle[i][60:53] = decode_xarith[i];
            assign decode_bundle[i][67:61] = decode_xlogic[i];
        end
    endgenerate

`ifdef RISCV_FORMAL
    localparam FBUNDLE_SIZE = 1 + 64 + 32 + 7 + 15;
    wire [FBUNDLE_SIZE - 1:0] f_ibundle [1:0];
    assign f_ibundle[0] = {decode_raddr[0], if_ixl_ch0, if_mode_ch0, if_intr_ch0, if_halt_ch0, if_trap_ch0, if_insn_ch0, if_order_ch0, if_valid_ch0};
    assign f_ibundle[1] = {decode_raddr[0], if_ixl_ch1, if_mode_ch1, if_intr_ch1, if_halt_ch1, if_trap_ch1, if_insn_ch1, if_order_ch1, if_valid_ch1};
`else
    localparam FBUNDLE_SIZE = 0;
`endif

    // decode always accepts two instructions (if available) but since issue
    // could stall, a skid buffer is required to hold the two instructions
    // until the !o_output_ready signal propogates up the pipeline to the fetch
    localparam SKID_WIDTH = (FBUNDLE_SIZE * 2) + (`BUNDLE_SIZE * 2);
    wire [SKID_WIDTH - 1:0] skid_input_data;
`ifdef RISCV_FORMAL
    assign skid_input_data = {f_ibundle[1], f_ibundle[0], decode_bundle[1], decode_bundle[0]};
`else
    assign skid_input_data = {decode_bundle[1], decode_bundle[0]};
`endif

    wire input_ready, output_valid;
    wire [SKID_WIDTH - 1:0] skid_output_data;
    warp_skid #(
        .WIDTH(SKID_WIDTH)
    ) skid (
        .i_clk(i_clk), .i_rst_n(i_rst_n),
        .i_input_valid(i_input_valid), .o_input_ready(input_ready),
        .i_input_data(skid_input_data),
        .o_output_valid(output_valid), .i_output_ready(i_output_ready),
        .o_output_data(skid_output_data)
    );

    wire [`BUNDLE_SIZE - 1:0] bundle [1:0];
    assign bundle[0] = skid_output_data[0 +: `BUNDLE_SIZE ];
    assign bundle[1] = skid_output_data[`BUNDLE_SIZE +: `BUNDLE_SIZE];

`ifdef RISC_FORMAL
    wire [FBUNDLE_SIZE - 1:0] f_obundle [1:0];
    assign f_obundle[0] = skid_output_data[`BUNDLE_SIZE * 2 +: FBUNDLE_SIZE];
    assign f_obundle[1] = skid_output_data[`BUNDLE_SIZE * 2 + FBUNDLE_SIZE +: FBUNDLE_SIZE];

    assign of_valid_ch0     = f_obundle[0][0] & output_valid;
    assign of_order_ch0     = f_obundle[0][1  +: 64];
    assign of_insn_ch0      = f_obundle[0][65 +: 32];
    assign of_trap_ch0      = f_obundle[0][97];
    assign of_halt_ch0      = f_obundle[0][98];
    assign of_intr_ch0      = f_obundle[0][99];
    assign of_mode_ch0      = f_obundle[0][100 +: 2];
    assign of_ixl_ch0       = f_obundle[0][102 +: 2];
    assign of_rs1_addr_ch0  = f_obundle[0][104 +: 5];
    assign of_rs2_addr_ch0  = f_obundle[0][109 +: 5];
    assign of_rd_addr_ch0   = f_obundle[0][114 +: 5];
    assign of_rs1_rdata_ch0 = 64'h0; // filled in at later stage
    assign of_rs2_rdata_ch0 = 64'h0; // filled in at later stage
    assign of_rd_wdata_ch0  = 64'h0; // filled in at later stage

    assign of_valid_ch1     = f_obundle[1][0] & output_valid;
    assign of_order_ch1     = f_obundle[1][1 +: 64];
    assign of_insn_ch1      = f_obundle[1][65 +: 32];
    assign of_trap_ch1      = f_obundle[1][97];
    assign of_halt_ch1      = f_obundle[1][98];
    assign of_intr_ch1      = f_obundle[1][99];
    assign of_mode_ch1      = f_obundle[1][100 +: 2];
    assign of_ixl_ch1       = f_obundle[1][102 +: 2];
    assign of_rs_ch1_addr1  = f_obundle[1][104 +: 5];
    assign of_rs2_addr_ch1  = f_obundle[1][109 +: 5];
    assign of_rd_addr_ch1   = f_obundle[1][114 +: 5];
    assign of_rs_ch1_rdata1 = 64'h0; // filled in at later stage
    assign of_rs2_rdata_ch1 = 64'h0; // filled in at later stage
    assign of_rd_wdata_ch1  = 64'h0; // filled in at later stage
`endif

    assign o_input_ready = input_ready;
    assign o_output_valid = output_valid;
    assign o_bundle0 = bundle[0];
    assign o_bundle1 = bundle[1];

    `ifdef WARP_FORMAL
        reg f_past_valid;
        initial f_past_valid <= 1'b0;
        always @(posedge i_clk) f_past_valid <= 1'b1;

        (* gclk *) reg formal_timestep;

        initial assume (!i_clk);
        initial assume (!i_rst_n);

        // ensure this is a synchronous interface
        always @(posedge formal_timestep) begin
            // asynchronous assert, synchronous deassert clock
            if (f_past_valid && $rose(i_rst_n))
                assume ($rose(i_clk));

            if (f_past_valid && !$rose(i_clk)) begin
                assume ($stable(i_input_valid));
                assume ($stable(i_inst0));
                assume ($stable(i_inst1));
                assume ($stable(i_compressed));
                assume ($stable(i_output_ready));
            end

            if (f_past_valid && i_rst_n && !$rose(i_clk)) begin
                assert ($stable(o_input_ready));
                assert ($stable(o_output_valid));
                assert ($stable(o_bundle0));
                assert ($stable(o_bundle1));
            end
        end

        always @(*) begin
            if (!i_rst_n) begin
                assume (!i_input_valid);
                assume (!i_output_ready);

                assert (o_input_ready);
                assert (!o_output_valid);
            end
        end

        wire f_transmit = i_output_ready && o_output_valid;

        always @(posedge i_clk) begin
            if (i_rst_n) begin
                // assume input interface doesn't drop instructions
                if (f_past_valid && $past(i_input_valid) && !$past(o_input_ready)) begin
                    assume ($stable(i_input_valid));
                    assume ($stable(i_compressed));
                    assume ($stable(i_inst0));
                    assume ($stable(i_inst1));
                end

                // downstream backpressure should not drop insts
                if (f_past_valid && $past(o_output_valid) && !$past(i_output_ready)) begin
                    assert ($stable(o_output_valid));
                    assert ($stable(o_bundle0));
                    assert ($stable(o_bundle1));
                end

                // ensure 100% throughput
                cover (f_past_valid && $past(f_transmit) && f_transmit && $changed(o_bundle0) && $changed(o_bundle1));
            end
        end
    `endif
endmodule

module warp_pick (
    input  wire [63:0] i_buffer,
    output wire [1:0]  o_compressed
);
    wire [1:0] opcode [0:2];
    assign opcode[0] = i_buffer[1:0];
    assign opcode[1] = i_buffer[17:16];
    assign opcode[2] = i_buffer[33:32];

    wire [1:0] compressed;
    assign compressed[0] = opcode[0] != 2'b11;
    assign compressed[1] = (compressed[0] ? opcode[1] : opcode[2]) != 2'b11;

    assign o_compressed = compressed;
endmodule

module warp_predecode (
    input  wire [31:0] i_inst,
    input  wire        i_compressed,
    output wire        o_branch
);
    wire op_branch = i_inst[6:0] == 7'b1100011;
    wire op_jal    = i_inst[6:0] == 7'b1101111;
    wire op_jalr   = i_inst[6:0] == 7'b1100111;
    wire op_cj     = i_inst[1:0] == 2'b01 && i_inst[15:13] == 3'b101;
    wire op_cjal   = i_inst[1:0] == 2'b01 && i_inst[15:13] == 3'b001;
    wire op_cjr    = i_inst[1:0] == 2'b10 && i_inst[15:12] == 4'b1000 && i_inst[6:2] == 5'd0 && i_inst[11:7] != 5'd0;
    wire op_cjalr  = i_inst[1:0] == 2'b10 && i_inst[15:12] == 4'b1001 && i_inst[6:2] == 5'd0 && i_inst[11:7] != 5'd0;
    wire op_cbeqz  = i_inst[1:0] == 2'b01 && i_inst[15:13] == 3'b110;
    wire op_cbnez  = i_inst[1:0] == 2'b01 && i_inst[15:13] == 3'b111;

    wire op_ubranch = op_branch || op_jal || op_jalr;
    wire op_cbranch = op_cj || op_cjal || op_cjr || op_cjalr || op_cbeqz || op_cbnez;
    wire branch = i_compressed ? op_cbranch : op_ubranch;

    assign o_branch = branch;
endmodule

module warp_udecode (
    input  wire [31:0] i_inst,
    output wire        o_legal,
    // [4:0]   = rs1_addr
    // [9:5]   = rs2_addr
    // [14:10] = rd_addr
    output wire [14:0] o_raddr,
    output wire [31:0] o_imm,
    output wire [3:0]  o_pipeline,
    // [0]   = op2_sel
    output wire [0:0]  o_shared,
    // [1:0] = opsel
    // [2]   = sub
    // [3]   = unsigned
    // [4]   = cmp_mode
    // [5]   = branch_equal
    // [6]   = branch_invert
    // [7]   = word
    output wire [7:0]  o_xarith,
    // [2:0] = opsel
    // [3]   = invert
    // [5:4] = sll
    // [6]   = word
    output wire [6:0]  o_xlogic
);
    wire [4:0] opcode = i_inst[6:2];
    wire [4:0] rs1    = i_inst[19:15];
    wire [4:0] rs2    = i_inst[24:20];
    wire [4:0] rd     = i_inst[11:7];
    wire [2:0] funct3 = i_inst[14:12];
    wire [6:0] funct7 = i_inst[31:25];

    // major opcode selection
    wire op_load      = opcode == 5'b00000;
    wire op_load_fp   = opcode == 5'b00001;
    wire op_misc_mem  = opcode == 5'b00011;
    wire op_op_imm    = opcode == 5'b00100;
    wire op_auipc     = opcode == 5'b00101;
    wire op_op_imm_32 = opcode == 5'b00110;
    wire op_store     = opcode == 5'b01000;
    wire op_store_fp  = opcode == 5'b01001;
    wire op_amo       = opcode == 5'b01011;
    wire op_op        = opcode == 5'b01100;
    wire op_lui       = opcode == 5'b01101;
    wire op_op_32     = opcode == 5'b01110;
    wire op_madd      = opcode == 5'b10000;
    wire op_msub      = opcode == 5'b10001;
    wire op_nmsub     = opcode == 5'b10010;
    wire op_nmadd     = opcode == 5'b10011;
    wire op_fp        = opcode == 5'b10100;
    wire op_branch    = opcode == 5'b11000;
    wire op_jalr      = opcode == 5'b11001;
    wire op_jal       = opcode == 5'b11011;
    wire op_system    = opcode == 5'b11100;

    // immediate decoding
    wire format_r = op_op || op_op_32 || op_amo;
    wire format_i = op_op_imm || op_op_imm_32 || op_jalr || op_load;
    wire format_s = op_store;
    wire format_b = op_branch;
    wire format_u = op_lui || op_auipc;
    wire format_j = op_jal;

    wire format_sb = format_s || format_b;
    wire format_ij = format_i || format_j;
    wire format_uj = format_u || format_j;

    wire [31:0] imm;
    assign imm[0] = (format_s & i_inst[7]) | (format_i && i_inst[20]);
    assign imm[4:1] = ({4{format_sb}} & i_inst[11:8]) | ({4{format_ij}} & i_inst[24:21]);
    assign imm[10:5] = {6{!format_u}} & i_inst[30:25];
    assign imm[11] = format_b ? i_inst[7] : (format_j ? i_inst[20] : (format_u ? 1'b0 : i_inst[31]));
    assign imm[19:12] = format_uj ? i_inst[19:12] : {8{i_inst[31]}};
    assign imm[30:20] = format_u ? i_inst[30:20] : {11{i_inst[31]}};
    assign imm[31] = i_inst[31];

    // instruction legal
    reg legal;
    // backend pipeline selection
    reg [3:0] pipeline;
    // shared control signals
    reg       op2_sel;
    // xarith control signals
    reg [1:0] xarith_opsel;
    reg xarith_sub, xarith_unsigned, xarith_cmp_mode;
    reg xarith_branch_equal, xarith_branch_invert;
    reg xarith_word;
    // xlogic control signals
    reg [2:0] xlogic_opsel;
    reg xlogic_invert, xlogic_word;
    reg [1:0] xlogic_sll;
    always @(*) begin
        legal = 1'b0;
        // FIXME: some of these can be x once we debug everything
        pipeline = 4'b0000;
        op2_sel = 1'b0;
        xarith_opsel = 2'b00;
        xarith_sub = 1'b0;
        xarith_unsigned = 1'b0;
        xarith_cmp_mode = 1'b0;
        xarith_branch_equal = 1'b0;
        xarith_branch_invert = 1'b0;
        xarith_word = 1'b0;
        xlogic_opsel = 3'b000;
        xlogic_invert = 1'b0;
        xlogic_sll = 2'b00;
        xlogic_word = 1'b0;

        case (1'b1)
            // addi, slti, sltiu, xori, ori, andi, slli, srli, srai
            op_op_imm: begin
                case (funct3)
                    // addi
                    3'b000: begin
                        legal = 1'b1;
                        pipeline = `PIPELINE_XARITH;
                        xarith_opsel = `XARITH_OP_ADD;
                        xarith_word = 1'b0;
                    end
                    // slli
                    3'b001: begin
                        legal = i_inst[31:26] == 6'b000000;
                        pipeline = `PIPELINE_XLOGIC;
                        xlogic_opsel = `XLOGIC_OP_SHF;
                        xlogic_word = 1'b0;
                    end
                    // slti, sltiu
                    3'b010, 3'b011: begin
                        legal = 1'b1;
                        pipeline = `PIPELINE_XARITH;
                        xarith_opsel = `XARITH_OP_SLT;
                        xlogic_word = 1'b0;
                    end
                    // xori
                    3'b100: begin
                        legal = 1'b1;
                        pipeline = `PIPELINE_XLOGIC;
                        xlogic_opsel = `XLOGIC_OP_XOR;
                        xlogic_word = 1'b0;
                    end
                    // srli, srai
                    3'b101: begin
                        legal = i_inst[31:26] == 6'b000000 || i_inst[31:26] == 6'b010000;
                        pipeline = `PIPELINE_XLOGIC;
                        xlogic_opsel = `XLOGIC_OP_SHF;
                        xlogic_word = 1'b0;
                    end
                    // ori
                    3'b110: begin
                        legal = 1'b1;
                        pipeline = `PIPELINE_XLOGIC;
                        xlogic_opsel = `XLOGIC_OP_OR;
                        xlogic_word = 1'b0;
                    end
                    // andi
                    3'b111: begin
                        legal = 1'b1;
                        pipeline = `PIPELINE_XLOGIC;
                        xlogic_opsel = `XLOGIC_OP_AND;
                        xlogic_word = 1'b0;
                    end
                endcase

                op2_sel = 1'b1;
                xarith_sub = 1'b0;
                xarith_unsigned = funct3[0];
                xlogic_invert = 1'b0;
            end
            // auipc
            op_auipc: begin
                legal = 1'b1;
                pipeline = `PIPELINE_XARITH;
                op2_sel = 1'b1;
                xarith_opsel = `XARITH_OP_ADD;
                xarith_sub = 1'b0;
                xarith_word = 1'b0;
            end
            // addiw, slliw, srliw, sraiw
            op_op_imm_32: begin
                case (funct3)
                    // addiw
                    3'b000: begin
                        legal = 1'b1;
                        pipeline = `PIPELINE_XARITH;
                        xarith_opsel = `XARITH_OP_ADD;
                    end
                    // slliw
                    3'b001: begin
                        legal = i_inst[31:25] == 7'b0000000;
                        pipeline = `PIPELINE_XLOGIC;
                        xlogic_opsel = `XLOGIC_OP_SHF;
                    end
                    // srliw, sraiw
                    3'b101: begin
                        legal = i_inst[31:25] == 7'b0000000 || i_inst[31:25] == 7'b0100000;
                        pipeline = `PIPELINE_XLOGIC;
                        xlogic_opsel = `XLOGIC_OP_SHF;
                    end
                endcase

                op2_sel = 1'b1;
                xarith_sub = 1'b0;
                xarith_word = 1'b1;
                xlogic_invert = 1'b0;
                xlogic_word = 1'b1;
            end
            // add, sub, sll, slt, sltu, xor, srl, sra, or, and
            op_op: begin
                case (funct3)
                    // add, sub
                    3'b000: begin
                        legal = funct7 == 7'b0000000 || funct7 == 7'b0100000;
                        pipeline = `PIPELINE_XARITH;
                        xarith_opsel = `XARITH_OP_ADD;
                    end
                    // sll
                    3'b001: begin
                        legal = funct7 == 7'b0000000;
                        pipeline = `PIPELINE_XLOGIC;
                        xlogic_opsel = `XLOGIC_OP_SHF;
                    end
                    // slt, sltu
                    3'b010, 3'b011: begin
                        legal = 1'b1;
                        pipeline = `PIPELINE_XARITH;
                        xarith_opsel = `XARITH_OP_SLT;
                    end
                    // xor
                    3'b100: begin
                        legal = 1'b1;
                        pipeline = `PIPELINE_XLOGIC;
                        xlogic_opsel = `XLOGIC_OP_XOR;
                    end
                    // srl, sra
                    3'b101: begin
                        legal = funct7 == 7'b0000000 || funct7 == 7'b0100000;
                        pipeline = `PIPELINE_XLOGIC;
                        xlogic_opsel = `XLOGIC_OP_SHF;
                    end
                    // or
                    3'b110: begin
                        legal = 1'b1;
                        pipeline = `PIPELINE_XLOGIC;
                        xlogic_opsel = `XLOGIC_OP_OR;
                    end
                    // and
                    3'b111: begin
                        legal = 1'b1;
                        pipeline = `PIPELINE_XLOGIC;
                        xlogic_opsel = `XLOGIC_OP_AND;
                    end
                endcase

                op2_sel = 1'b0;
                xarith_sub = funct7[5];
                xarith_word = 1'b0;
                xarith_unsigned = funct3[0];
                xlogic_invert = 1'b0;
                xlogic_word = 1'b0;
            end
            // lui
            op_lui: begin
                legal = 1'b1;
                pipeline = `PIPELINE_XARITH;
                op2_sel = 1'b1;
                xarith_opsel = `XARITH_OP_ADD;
                xarith_sub = 1'b0;
                xarith_word = 1'b0;
            end
            op_op_32: begin
                case (funct3)
                    // addw, subw
                    3'b000: begin
                        legal = funct7 == 7'b0000000 || funct7 == 7'b0100000;
                        pipeline = `PIPELINE_XARITH;
                        xarith_opsel = `XARITH_OP_ADD;
                    end
                    // sllw
                    3'b001: begin
                        legal = funct7 == 7'b0000000;
                        pipeline = `PIPELINE_XLOGIC;
                        xlogic_opsel = `XLOGIC_OP_SHF;
                    end
                    // srlw, sraw
                    3'b101: begin
                        legal = funct7 == 7'b0000000 || funct7 == 7'b0100000;
                        pipeline = `PIPELINE_XLOGIC;
                        xlogic_opsel = `XLOGIC_OP_SHF;
                    end
                endcase

                op2_sel = 1'b0;
                xarith_sub = funct7[5];
                xarith_word = 1'b1;
                xlogic_invert = 1'b0;
                xlogic_word = 1'b1;
            end
        endcase
    end

    assign o_legal    = legal;
    assign o_raddr    = {rd, rs2, rs1};
    assign o_imm      = imm;
    assign o_pipeline = pipeline;

    assign o_shared[0] = op2_sel;

    assign o_xarith[1:0] = xarith_opsel;
    assign o_xarith[2]   = xarith_sub;
    assign o_xarith[3]   = xarith_unsigned;
    assign o_xarith[4]   = xarith_cmp_mode;
    assign o_xarith[5]   = xarith_branch_equal;
    assign o_xarith[6]   = xarith_branch_invert;
    assign o_xarith[7]   = xarith_word;

    assign o_xlogic[2:0] = xlogic_opsel;
    assign o_xlogic[3]   = xlogic_invert;
    assign o_xlogic[5:4] = xlogic_sll;
    assign o_xlogic[6]   = xlogic_word;
endmodule

/*
module warp_cdecode (
    input  wire [15:0] i_inst,
    output wire        o_valid,
    output wire [4:0]  o_rs1_addr,
    output wire [4:0]  o_rs2_addr,
    output wire [4:0]  o_rd_addr,
    output wire [31:0] o_imm,
    output wire [3:0]  o_pipeline,
    output wire [1:0]  o_xarith_opsel,
    output wire        o_xarith_sub,
    output wire        o_xarith_unsigned,
    output wire        o_xarith_cmp_mode,
    output wire        o_xarith_branch_equal,
    output wire        o_xarith_branch_invert,
    output wire [2:0]  o_xlogic_opsel,
    output wire        o_xlogic_invert,
    output wire [1:0]  o_xlogic_sll
);
    wire [1:0] opcode  = i_inst[1:0];
    // wire [4:0] rs2     = i_inst[6:2];
    wire [4:0] rs1_rd  = i_inst[11:7];
    wire [2:0] rdp     = i_inst[4:2];
    wire [2:0] rs2p    = i_inst[4:2];
    wire [2:0] rs1p    = i_inst[9:7];
    // wire [2:0] rs1p    = i_inst[9:7];
    wire [2:0] funct3  = i_inst[15:13];
    wire [3:0] funct4  = i_inst[15:12];
    wire [5:0] funct6  = i_inst[15:10];

    wire op_addi4spn = (opcode == 2'b00) && (funct3 == 3'b000);
    wire op_fld      = (opcode == 2'b00) && (funct3 == 3'b001);
    wire op_lw       = (opcode == 2'b00) && (funct3 == 3'b010);
    wire op_ld       = (opcode == 2'b00) && (funct3 == 3'b011);
    wire op_fsd      = (opcode == 2'b00) && (funct3 == 3'b101);
    wire op_sw       = (opcode == 2'b00) && (funct3 == 3'b110);
    wire op_sd       = (opcode == 2'b00) && (funct3 == 3'b111);
    wire op_addi     = (opcode == 2'b01) && (funct3 == 3'b000);
    wire op_addiw    = (opcode == 2'b01) && (funct3 == 3'b001);
    wire op_li       = (opcode == 2'b01) && (funct3 == 3'b010);

    // lui/addi16sp
    wire op_lui      = (opcode == 2'b01) && (funct3 == 3'b011);
    wire op_misc_alu = (opcode == 2'b01) && (funct3 == 3'b100);
    wire op_j        = (opcode == 2'b01) && (funct3 == 3'b101);
    wire op_beqz     = (opcode == 2'b01) && (funct3 == 3'b110);
    wire op_bnez     = (opcode == 2'b01) && (funct3 == 3'b111);
    wire op_slli     = (opcode == 2'b10) && (funct3 == 3'b000);
    wire op_fldsp   = (opcode == 2'b10) && (funct3 == 3'b001);
    wire op_lwsp     = (opcode == 2'b10) && (funct3 == 3'b010);
    wire op_ldsp     = (opcode == 2'b10) && (funct3 == 3'b011);

    // j[al]r/mv/add
    wire op_jalr     = (opcode == 2'b10) && (funct3 == 3'b100);
    wire op_fsdsp    = (opcode == 2'b10) && (funct3 == 3'b101);
    wire op_swsp     = (opcode == 2'b10) && (funct3 == 3'b110);
    wire op_sdsp     = (opcode == 2'b10) && (funct3 == 3'b111);

    wire op_nop      = (opcode == 2'b01) && (funct3 == 3'b000);
    // immediate decoding

    wire [15:0] imm;

    // instruction valid
    reg valid;
    // backend pipeline selection
    reg [3:0] pipeline;
    // register selection
    reg [4:0] rd, rs1, rs2;
    // xarith control signals
    reg [1:0] xarith_opsel;
    reg xarith_sub, xarith_unsigned, xarith_cmp_mode;
    reg xarith_branch_equal, xarith_branch_invert;
    // xlogic control signals
    reg [2:0] xlogic_opsel;
    reg xlogic_invert;
    reg [1:0] xlogic_sll;
    reg
        format_cr,
        format_ci,
        format_css,
        format_ciw,
        format_cl,
        format_cs,
        format_ca,
        format_cb,
        format_cj;
    // wire format_cr  = ;
    // wire format_ci  = ;
    // wire format_css = ;
    // wire format_ciw = op_addi4spn;
    // wire format_cl  = ;
    // wire format_cs  = ;
    // wire format_ca  = ;
    // wire format_cb  = ;
    // wire format_cj  = ;

    //immidates formats
    wire format_8_43__ = op_beqz | op_bnez;
    wire formatu_53_86 = op_fsdsp | op_sdsp;
    wire formatu_52_76 = op_swsp;
    wire format_x11_4_98_ = op_cj;
    wire format_5__40 = op_li | op_addiw | op_addi | op_nop; //TODO: op_and
    wire formatu_5__40 = op_slli; //TODO: op_srai op_srli
    wire formatu_5__42_76 = op_lwsp;
    wire formatu_5__43_86 = op_ldsp | op_fldsp;
    wire formatu_54_96_2_3 = addi4spn;
    
    // TODO: LIU and addi16sap format (depends on rd = 2 or not)

    //speical below, use a 2nd case for the lower bits for immeidate
    wire formatu_53__ = op_fld | op_lw | op_ld | op_fsd | op_sw | op_sd;
    wire formatu_2_6 = op_lw | op_sw;
    wire formatu_76 = op_fld | op_ld | op_fsd | op_sd;

    always @(*) begin
        valid = 1'b0;
        pipeline = 4'bxxxx;
        rd = 5'bxxxxx;
        rs1 = 5'bxxxxx;
        rs2 = 5'bxxxxx;
        xarith_opsel = 2'bxx;
        xarith_sub = 1'bx;
        xarith_unsigned = 1'bx;
        xarith_cmp_mode = 1'bx;
        xarith_branch_equal = 1'bx;
        xarith_branch_invert = 1'bx;
        xlogic_opsel = 3'bxxx;
        xlogic_invert = 1'bx;
        xlogic_sll = 2'bxx;

        case (1'b1)
            // FIXME: fix immediates 
            // TODO: ci: lwsp, ldsp, fldsp
            // TODO: css: swsp, sdsp, fsdsp
            // TODO: cl: lw, ld, fld
            // TODO: cs: sw, sd, fsd
            // TODO: cj: j
            // TODO: cr: jr, jalr
            // TODO: cb: beqz, bnez
            // TODO: ci: li, lui
            // TODO: ci: addi, addiw, addi16sp
            // TODO: ciw: addi4spn
            // addi4spn
            // op_addi4spn: begin
            //     // TODO: invalid if immediate is zero
            //     valid = 1'b1;
            //     pipeline = `PIPELINE_XARITH;
            //     xarith_opsel = `XARITH_OP_ADD;
            // end
            // slli
            op_addi4spn: begin
                //TODO: valid = (nzuimm != 8'd0);
                pipeline = `PIPELINE_XARITH;
                xarith_opsel = `XARITH_OP_ADD;
                xarith_sub = 1'b0;
                rd = rsp;
                rs1 = 5'd2;

            end
            op_li: begin
                valid = rs1_rd != 5'd0;
                pipeline = `PIPELINE_XARITH;
                xarith_opsel = `XARITH_OP_ADD;
                xarith_sub = 1'b0;
                rd = rs1_rd;
                rs1 = 5'd0;
            end
            op_lui: begin
                valid = (rs1_rd != 5'd0) & (rs1 != 5'd2);
                pipeline = `PIPELINE_XARITH;
                xarith_opsel = `XARITH_OP_ADD;
                xarith_sub = 1'b0;
                rd = rs1_rd;
                rs1 = 5'd0;
            end
            op_slli: begin
                valid = rs1_rd != 5'd0;
                pipeline = `PIPELINE_XLOGIC;
                xlogic_opsel = `XLOGIC_OP_SHF;
                rd = rd_rs1;
                rs1 = rd_rs1;
                // TODO: add control signal for direction
            end
            // mv, add
            op_jalr: begin
                valid = (rs1_rd != 5'd0) && (rs2 != 5'd0);
                pipeline = `PIPELINE_XARITH;
                xarith_opsel = `XARITH_OP_ADD;
                xarith_sub = 1'b0;
                rd = rd_rs1;
                rs1 = funct4[0] ? rd_rs1 : 5'd0;
                rs2 = rs2;
            end
            // srli, srai, andi, and, or, xor, sub, addw, subw
            op_misc_alu: begin
                rd = {2'b01, rdp};
                rs1 = {2'b01, rdp};
                rs2 = {2'b01, rs2p};

                case (i_inst[11:10])
                    // srli, srai
                    2'b00, 2'b01: begin
                        valid = 1'b1;
                        pipeline = `PIPELINE_XLOGIC;
                        xlogic_opsel = `XLOGIC_OP_SHF;
                        // TODO: add control signal for direction, arithmetic
                    end
                    2'b10: begin
                        valid = 1'b1;
                        pipeline = `PIPELINE_XLOGIC;
                        xlogic_opsel = `XLOGIC_OP_AND;
                    end
                    // and, or, xor, sub, addw, subw
                    2'b11: begin
                        case ({i_inst[12], i_inst[6:5]})
                            // sub
                            3'b000: begin
                                valid = 1'b1;
                                pipeline = `PIPELINE_XARITH;
                                xarith_opsel = `XARITH_OP_ADD;
                                xarith_sub = 1'b1;
                            end
                            // xor
                            3'b001: begin
                                valid = 1'b1;
                                pipeline = `PIPELINE_XLOGIC;
                                xlogic_opsel = `XLOGIC_OP_XOR;
                            end
                            // or
                            3'b010: begin
                                valid = 1'b1;
                                pipeline = `PIPELINE_XLOGIC;
                                xlogic_opsel = `XLOGIC_OP_OR;
                            end
                            // and
                            3'b011: begin
                                valid = 1'b1;
                                pipeline = `PIPELINE_XLOGIC;
                                xlogic_opsel = `XLOGIC_OP_AND;
                            end
                            // subw, addw
                            3'b100, 3'b101, 3'b110, 3'b111: begin
                                valid = i_inst[6] == 1'b0;
                                pipeline = `PIPELINE_XARITH;
                                xarith_opsel = `XARITH_OP_ADD;
                                xarith_sub = 1'b1;
                                // TODO: mark lower 32
                            end
                        endcase
                    end
                endcase
            end
            // TODO: ci: nop
            // TODO: cr: ebreak
        endcase
        //TODO: sign extend (and make sure error check for invalid imm)
        case(1'b1)
        format_8_43__:begin
            imm[8] = opcode[12];
            imm[4:3] = opcode[11:10];
            imm[7:6] = opcode[6:5];
            imm[2:1] =opcode[4:3];
            imm[5] = opcode[2];
        end
        formatu_53_86:begin
            imm[5:3] = opcode[12:10];
            imm[8:6] = opcode[9:7];
        end
        formatu_52_76:begin
            imm[5:2] = opcode[12:9];
            imm[7:6] = opcode[8:7];
        end
        format_x11_4_98_:begin
            imm[11] = opcode[12];
            imm[4] = opcode[11];
            imm[9:8] = opcode[10:9];
            imm[10] = opcode[8];
            imm[6] = opcode[7];
            imm[7] = opcode[6];
            imm[3:1] = opcode[5:3];
            imm[5] = opcode[2];
        end
        format_5__40:
        begin
            imm[5] = opcode[12];
            imm[4:0] = opcode[6:2];
        end
        formatu_5__40:
        begin
            imm[5] = opcode[12];
            imm[4:0] = opcode[6:2];
        end
        formatu_5__42_76:
        begin
            imm[5] = opcode[12];
            imm[4:2] = opcode[6:4];
            imm[7:6] = opcode[3:2];
        end
        formatu_5__43_86:
        begin
            imm[5] = opcode[12];
            imm[4:3] = opcode[6:5];
            imm[8:6] = opcode[4:2];
        end
        formatu_54_96_2_3:
        begin
            imm[5:4] = opcode[12:11];
            imm[9:6] = opcode[10:7];
            imm[2] = opcode[6];
            imm[3] = opcode[5];
        end
        formatu_53__:
        begin
            imm[5:3]= opcode[12:10];
        end
        formatu_2_6:
        begin
            imm[2]= opcode[6];
            imm[6]= opcode[5];
        end
        formatu_76:
        begin
            imm[7]= opcode[6];
            imm[6]= opcode[5];
        end
        endcase

    end
endmodule
*/

`default_nettype wire
