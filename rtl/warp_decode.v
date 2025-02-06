`default_nettype none

`define PIPE_XARITH 4'b0000
`define PIPE_XLOGIC 4'b0001
`define PIPE_XMUL   4'b0010
`define PIPE_XDIV   4'b0011

module warp_decode (
    input  wire        i_clk,
    input  wire        i_rst_n,
    output wire        o_input_ready,
    input  wire        i_input_valid,
    input  wire [31:0] i_inst0,
    input  wire [31:0] i_inst1,
    input  wire [1:0]  i_compressed,
    input  wire        i_count,
    input  wire        i_output_ready,
    output wire        o_output_valid,
    output wire [64:0] o_bundle0,
    output wire [64:0] o_bundle1,
    output wire        o_count
);
    // decode stage doesn't generate any valid or ready
    // signals, only propogates them
    reg ready, valid;
    always @(posedge i_clk, negedge i_rst_n) begin
        if (!i_rst_n) begin
            ready <= 1'b1;
            valid <= 1'b0;
        end else begin
            ready <= i_output_ready;
            valid <= i_input_valid;
        end
    end

    wire        decode_legal    [0:3];
    wire [14:0] decode_raddr    [0:3];
    wire [31:0] decode_imm      [0:3];
    wire [3:0]  decode_pipeline [0:3];
    wire [6:0]  decode_xarith   [0:3];
    wire [5:0]  decode_xlogic   [0:3];
    warp_udecode udecode [0:1] (
        .i_inst({i_inst0, i_inst1}),
        .o_legal({decode_legal[0], decode_legal[1]}),
        .o_raddr({decode_raddr[0], decode_raddr[1]}),
        .o_imm({decode_imm[0], decode_imm[1]}),
        .o_pipeline({decode_pipeline[0], decode_pipeline[1]}),
        .o_xarith({decode_xarith[0], decode_xarith[1]}),
        .o_xlogic({decode_xlogic[0], decode_xlogic[1]})
    );

    wire [64:0] decode_bundle [0:3];
    genvar i;
    generate
        for (i = 0; i < 4; i = i + 1)
            assign decode_bundle[i] = {decode_legal[i], decode_raddr[i], decode_imm[i], decode_pipeline[i], decode_xarith[i], decode_xlogic[i]};
    endgenerate

    reg [64:0] bundle0, bundle1;
    reg        count;

    always @(posedge i_clk, negedge i_rst_n) begin
        if (!i_rst_n) begin
            bundle0 <= 64'h0;
            bundle1 <= 64'h0;
            count <= 1'b0;
        end else begin
            bundle0 <= i_compressed[0] ? decode_bundle[2] : decode_bundle[0];
            bundle1 <= i_compressed[1] ? decode_bundle[3] : decode_bundle[1];
            count <= i_count;
        end
    end

    assign o_input_ready = ready;
    assign o_output_valid = valid;
    assign o_bundle0 = bundle0;
    assign o_bundle1 = bundle1;
    assign o_count = count;

    `ifdef WARP_FORMAL
        reg f_past_valid;
        initial f_past_valid <= 1'b0;
        always @(posedge i_clk) f_past_valid <= 1'b1;

        (* gclk *) reg formal_timestep;


        reg f_valid, f_count;
        initial f_valid <= 1'b0;

        initial begin
            assume (!i_clk);
            assume (!i_rst_n);
            assume (!i_input_valid);

            assert (o_input_ready);
            assert (!o_output_valid);
        end

        always @(posedge formal_timestep) begin
            if (!i_rst_n) begin
                assume (!i_clk);
                assume (!i_rst_n);
                assume (!i_input_valid);

                assert (o_input_ready);
                assert (!o_output_valid);
            end

            if (!$rose(i_clk)) begin
                assume ($stable(i_input_valid));
                assume ($stable(i_inst0));
                assume ($stable(i_inst1));
                assume ($stable(i_compressed));
                assume ($stable(i_count));
                assume ($stable(i_output_ready));
            end

            if (f_past_valid && !$changed(i_rst_n) && !$rose(i_clk)) begin
                assert ($stable(o_input_ready));
                assert ($stable(o_output_valid));
                assert ($stable(o_bundle0));
                assert ($stable(o_bundle1));
                assert ($stable(o_count));
            end
        end

        always @(posedge i_clk) begin
            if (!i_rst_n) begin
                assert (o_input_ready);
                assert (!o_output_valid);
            end else begin
                // assume input interface doesn't drop instructions
                if (f_past_valid && $past(i_input_valid) && !$past(o_input_ready)) begin
                    assume ($stable(i_input_valid));
                    assume ($stable(i_inst0));
                    assume ($stable(i_inst1));
                    assume ($stable(i_compressed));
                    assume ($stable(i_count));
                end

                // downstream backpressure should not drop insts
                if (f_past_valid && $past(o_output_valid) && !$past(i_output_ready)) begin
                    a_backpressure1: assert ($stable(o_output_valid));
                    a_backpressure2: assert ($stable(o_bundle0));
                    a_backpressure3: assert ($stable(o_bundle1));
                    a_backpressure4: assert ($stable(o_count));
                end

                if (o_input_ready && i_input_valid) begin
                    f_valid <= 1'b1;
                    f_count <= i_count;
                end
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
    // [1:0] = opsel
    // [2]   = sub
    // [3]   = unsigned
    // [4]   = cmp_mode
// [5]   = branch_equal
    // [6]   = branch_invert
    output wire [6:0]  o_xarith,
    // [2:0] = opsel
    // [3]   = invert
    // [5:4] = sll
    output wire [5:0]  o_xlogic
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
        pipeline = 4'bxxxx;
        xarith_opsel = 2'bxx;
        xarith_sub = 1'bx;
        xarith_unsigned = 1'bx;
        xarith_cmp_mode = 1'bx;
        xarith_branch_equal = 1'bx;
        xarith_branch_invert = 1'bx;
        xarith_word = 1'bx;
        xlogic_opsel = 3'bxxx;
        xlogic_invert = 1'bx;
        xlogic_word = 1'bx;
        xlogic_sll = 2'bxx;

        case (1'b1)
            // addi, slti, sltiu, xori, ori, andi, slli, srli, srai
            op_op_imm: begin
                case (funct3)
                    // addi
                    3'b000: begin
                        legal = 1'b1;
                        pipeline = `PIPE_XARITH;
                        xarith_opsel = `XARITH_OP_ADD;
                        xarith_word = 1'b0;
                    end
                    // slli
                    3'b001: begin
                        legal = i_inst[31:26] == 6'b000000;
                        pipeline = `PIPE_XLOGIC;
                        xlogic_opsel = `XLOGIC_OP_SHF;
                        xlogic_word = 1'b0;
                    end
                    // slti, sltiu
                    3'b010, 3'b011: begin
                        legal = 1'b1;
                        pipeline = `PIPE_XARITH;
                        xarith_opsel = `XARITH_OP_SLT;
                        xlogic_word = 1'b0;
                    end
                    // xori
                    3'b100: begin
                        legal = 1'b1;
                        pipeline = `PIPE_XLOGIC;
                        xlogic_opsel = `XLOGIC_OP_XOR;
                        xlogic_word = 1'b0;
                    end
                    // srli, srai
                    3'b101: begin
                        legal = i_inst[31:26] == 6'b000000 || i_inst[31:26] == 6'b010000;
                        pipeline = `PIPE_XLOGIC;
                        xlogic_opsel = `XLOGIC_OP_SHF;
                        xlogic_word = 1'b0;
                    end
                    // ori
                    3'b110: begin
                        legal = 1'b1;
                        pipeline = `PIPE_XLOGIC;
                        xlogic_opsel = `XLOGIC_OP_OR;
                        xlogic_word = 1'b0;
                    end
                    // andi
                    3'b111: begin
                        legal = 1'b1;
                        pipeline = `PIPE_XLOGIC;
                        xlogic_opsel = `XLOGIC_OP_AND;
                        xlogic_word = 1'b0;
                    end
                endcase

                xarith_sub = 1'b0;
                xarith_unsigned = funct3[0];
                xlogic_invert = 1'b0;
            end
            // auipc
            op_auipc: begin
                legal = 1'b1;
                pipeline = `PIPE_XARITH;
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
                        pipeline = `PIPE_XARITH;
                        xarith_opsel = `XARITH_OP_ADD;
                        xarith_word = 1'b1;
                    end
                    // slliw
                    3'b001: begin
                        legal = i_inst[31:25] == 7'b0000000;
                        pipeline = `PIPE_XLOGIC;
                        xlogic_opsel = `XLOGIC_OP_SHF;
                        xlogic_word = 1'b1;
                    end
                    // srliw, sraiw
                    3'b101: begin
                        legal = i_inst[31:25] == 7'b0000000 || i_inst[31:25] == 7'b0100000;
                        pipeline = `PIPE_XLOGIC;
                        xlogic_opsel = `XLOGIC_OP_SHF;
                        xlogic_word = 1'b1;
                    end
                endcase

                xarith_sub = 1'b0;
                xlogic_invert = 1'b0;
            end
            // add, sub, sll, slt, sltu, xor, srl, sra, or, and
            op_op: begin
                case (funct3)
                    // add, sub
                    3'b000: begin
                        legal = funct7 == 7'b0000000 || funct7 == 7'b0100000;
                        pipeline = `PIPE_XARITH;
                        xarith_opsel = `XARITH_OP_ADD;
                        xarith_word = 1'b0;
                    end
                    // sll
                    3'b001: begin
                        legal = funct7 == 7'b0000000;
                        pipeline = `PIPE_XLOGIC;
                        xlogic_opsel = `XLOGIC_OP_SHF;
                        xlogic_word = 1'b0;
                    end
                    // slt, sltu
                    3'b010, 3'b011: begin
                        legal = 1'b1;
                        pipeline = `PIPE_XARITH;
                        xarith_opsel = `XARITH_OP_SLT;
                        xarith_word = 1'b0;
                    end
                    // xor
                    3'b100: begin
                        legal = 1'b1;
                        pipeline = `PIPE_XLOGIC;
                        xlogic_opsel = `XLOGIC_OP_XOR;
                        xlogic_word = 1'b0;
                    end
                    // srl, sra
                    3'b101: begin
                        legal = funct7 == 7'b0000000 || funct7 == 7'b0100000;
                        pipeline = `PIPE_XLOGIC;
                        xlogic_opsel = `XLOGIC_OP_SHF;
                        xlogic_word = 1'b0;
                    end
                    // or
                    3'b110: begin
                        legal = 1'b1;
                        pipeline = `PIPE_XLOGIC;
                        xlogic_opsel = `XLOGIC_OP_OR;
                        xlogic_word = 1'b0;
                    end
                    // and
                    3'b111: begin
                        legal = 1'b1;
                        pipeline = `PIPE_XLOGIC;
                        xlogic_opsel = `XLOGIC_OP_AND;
                        xlogic_word = 1'b0;
                    end
                endcase

                xarith_sub = funct7[5];
                xarith_unsigned = funct3[0];
                xlogic_invert = 1'b0;
            end
            // lui
            op_lui: begin
                legal = 1'b1;
                pipeline = `PIPE_XARITH;
                xarith_opsel = `XARITH_OP_ADD;
                xarith_sub = 1'b0;
                xarith_word = 1'b0;
            end
            op_op_32: begin
                case (funct3)
                    // addw, subw
                    3'b000: begin
                        legal = funct7 == 7'b0000000 || funct7 == 7'b0100000;
                        pipeline = `PIPE_XARITH;
                        xarith_opsel = `XARITH_OP_ADD;
                        xarith_word = 1'b1;
                    end
                    // sllw
                    3'b001: begin
                        legal = funct7 == 7'b0000000;
                        pipeline = `PIPE_XLOGIC;
                        xlogic_opsel = `XLOGIC_OP_SHF;
                        xlogic_word = 1'b1;
                    end
                    // srlw, sraw
                    3'b101: begin
                        legal = funct7 == 7'b0000000 || funct7 == 7'b0100000;
                        pipeline = `PIPE_XLOGIC;
                        xlogic_opsel = `XLOGIC_OP_SHF;
                        xlogic_word = 1'b1;
                    end
                endcase

                xarith_sub = funct7[5];
                xlogic_invert = 1'b0;
            end
        endcase
    end

    assign o_legal = legal;
    assign o_raddr = {rd, rs2, rs1};
    assign o_imm = imm;
    assign o_pipeline = pipeline;
    assign o_xarith[1:0] = xarith_opsel;
    assign o_xarith[2]   = xarith_sub;
    assign o_xarith[3]   = xarith_unsigned;
    assign o_xarith[4]   = xarith_cmp_mode;
    assign o_xarith[5]   = xarith_branch_equal;
    assign o_xarith[6]   = xarith_branch_invert;
    assign o_xlogic[2:0] = xlogic_opsel;
    assign o_xlogic[3]   = xlogic_invert;
    assign o_xlogic[5:4] = xlogic_sll;
endmodule

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
    wire [4:0] rs2     = i_inst[6:2];
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
    wire op_fldsqp   = (opcode == 2'b10) && (funct3 == 3'b001);
    wire op_lwsp     = (opcode == 2'b10) && (funct3 == 3'b010);
    wire op_ldsp     = (opcode == 2'b10) && (funct3 == 3'b011);
    // j[al]r/mv/add
    wire op_jalr     = (opcode == 2'b10) && (funct3 == 3'b100);
    wire op_fsdsp    = (opcode == 2'b10) && (funct3 == 3'b101);
    wire op_swsp     = (opcode == 2'b10) && (funct3 == 3'b110);
    wire op_sdsp     = (opcode == 2'b10) && (funct3 == 3'b111);

    // immediate decoding
    wire format_cr  = ;
    wire format_ci  = ;
    wire format_css = ;
    wire format_ciw = op_addi4spn;
    wire format_cl  = ;
    wire format_cs  = ;
    wire format_ca  = ;
    wire format_cb  = ;
    wire format_cj  = ;

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
            //     pipeline = `PIPE_XARITH;
            //     xarith_opsel = `XARITH_OP_ADD;
            // end
            // slli
            op_slli: begin
                valid = rs1_rd != 5'd0;
                pipeline = `PIPE_XLOGIC;
                xlogic_opsel = `XLOGIC_OP_SHF;
                rd = rd_rs1;
                rs1 = rd_rs1;
                // TODO: add control signal for direction
            end
            // mv, add
            op_jalr: begin
                valid = (rs1_rd != 5'd0) && (rs2 != 5'd0);
                pipeline = `PIPE_XARITH;
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
                        pipeline = `PIPE_XLOGIC;
                        xlogic_opsel = `XLOGIC_OP_SHF;
                        // TODO: add control signal for direction, arithmetic
                    end
                    2'b10: begin
                        valid = 1'b1;
                        pipeline = `PIPE_XLOGIC;
                        xlogic_opsel = `XLOGIC_OP_AND;
                    end
                    // and, or, xor, sub, addw, subw
                    2'b11: begin
                        case ({i_inst[12], i_inst[6:5]})
                            // sub
                            3'b000: begin
                                valid = 1'b1;
                                pipeline = `PIPE_XARITH;
                                xarith_opsel = `XARITH_OP_ADD;
                                xarith_sub = 1'b1;
                            end
                            // xor
                            3'b001: begin
                                valid = 1'b1;
                                pipeline = `PIPE_XLOGIC;
                                xlogic_opsel = `XLOGIC_OP_XOR;
                            end
                            // or
                            3'b010: begin
                                valid = 1'b1;
                                pipeline = `PIPE_XLOGIC;
                                xlogic_opsel = `XLOGIC_OP_OR;
                            end
                            // and
                            3'b011: begin
                                valid = 1'b1;
                                pipeline = `PIPE_XLOGIC;
                                xlogic_opsel = `XLOGIC_OP_AND;
                            end
                            // subw, addw
                            3'b100, 3'b101, 3'b110, 3'b111: begin
                                valid = i_inst[6] == 1'b0;
                                pipeline = `PIPE_XARITH;
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
    end
endmodule

`default_nettype wire
