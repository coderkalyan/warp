`default_nettype none

`define PIPE_XARITH 4'b0000
`define PIPE_XLOGIC 4'b0001
`define PIPE_XMUL   4'b0010
`define PIPE_XDIV   4'b0011

module warp_predecode (
    input  wire [63:0] i_buffer,
    // 0 = u[31:0]
    // 1 = u[47:16]
    // 2 = u[63:32]
    // 3 = c[15:0]
    // 4 = c[31:16]
    // 5 = c[47:32]
    // 6 = c[63:48]
    output wire [6:0]  o_pick,
);
    wire [1:0] opcode [3:0];
    assign opcode[0] = i_buffer[1:0];
    assign opcode[1] = i_buffer[17:16];
    assign opcode[2] = i_buffer[33:32];
    assign opcode[3] = i_buffer[49:48];

    wire [3:0] compressed = {opcode[3] != 2'b11, opcode[opcode[2] != 2'b11], opcode[1] != 2'b11, opcode[0] != 2'b11};
endmodule

module warp_udecode (
    input  wire [31:0] i_inst,
    output wire        o_valid,
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

    // instruction valid
    reg valid;
    // backend pipeline selection
    reg [3:0] pipeline;
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
            // addi, slti, sltiu, xori, ori, andi, slli, srli, srai
            op_op_imm: begin
                case (funct3)
                    // addi
                    3'b000: begin
                        valid = 1'b1;
                        pipeline = `PIPE_XARITH;
                        xarith_opsel = `XARITH_OP_ADD;
                    end
                    // slli
                    3'b001: begin
                        valid = i_inst[31:26] == 6'b000000;
                        pipeline = `PIPE_XLOGIC;
                        xlogic_opsel = `XLOGIC_OP_SHF;
                    end
                    // slti, sltiu
                    3'b010, 3'b011: begin
                        valid = 1'b1;
                        pipeline = `PIPE_XARITH;
                        xarith_opsel = `XARITH_OP_SLT;
                    end
                    // xori
                    3'b100: begin
                        valid = 1'b1;
                        pipeline = `PIPE_XLOGIC;
                        xlogic_opsel = `XLOGIC_OP_XOR;
                    end
                    // srli, srai
                    3'b101: begin
                        valid = i_inst[31:26] == 6'b000000 || i_inst[31:26] == 6'b010000;
                        pipeline = `PIPE_XLOGIC;
                        xlogic_opsel = `XLOGIC_OP_SHF;
                    end
                    // ori
                    3'b110: begin
                        valid = 1'b1;
                        pipeline = `PIPE_XLOGIC;
                        xlogic_opsel = `XLOGIC_OP_OR;
                    end
                    // andi
                    3'b111: begin
                        valid = 1'b1;
                        pipeline = `PIPE_XLOGIC;
                        xlogic_opsel = `XLOGIC_OP_AND;
                    end
                endcase

                xarith_sub = 1'b0;
                xarith_unsigned = funct3[0];
                xlogic_invert = 1'b0;
            end
            // auipc
            op_auipc: begin
                valid = 1'b1;
                pipeline = `PIPE_XARITH;
                xarith_opsel = `XARITH_OP_ADD;
                xarith_sub = 1'b0;
            end
            // addiw, slliw, srliw, sraiw
            op_op_imm_32: begin
                case (funct3)
                    // addiw
                    3'b000: begin
                        valid = 1'b1;
                        pipeline = `PIPE_XARITH;
                        xarith_opsel = `XARITH_OP_ADD;
                    end
                    // slliw
                    3'b001: begin
                        valid = i_inst[31:25] == 7'b0000000;
                        pipeline = `PIPE_XLOGIC;
                        xlogic_opsel = `XLOGIC_OP_SHF;
                    end
                    // srliw, sraiw
                    3'b101: begin
                        valid = i_inst[31:25] == 7'b0000000 || i_inst[31:25] == 7'b0100000;
                        pipeline = `PIPE_XLOGIC;
                        xlogic_opsel = `XLOGIC_OP_SHF;
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
                        valid = funct7 == 7'b0000000 || funct7 == 7'b0100000;
                        pipeline = `PIPE_XARITH;
                        xarith_opsel = `XARITH_OP_ADD;
                    end
                    // sll
                    3'b001: begin
                        valid = funct7 == 7'b0000000;
                        pipeline = `PIPE_XLOGIC;
                        xlogic_opsel = `XLOGIC_OP_SHF;
                    end
                    // slt, sltu
                    3'b010, 3'b011: begin
                        valid = 1'b1;
                        pipeline = `PIPE_XARITH;
                        xarith_opsel = `XARITH_OP_SLT;
                    end
                    // xor
                    3'b100: begin
                        valid = 1'b1;
                        pipeline = `PIPE_XLOGIC;
                        xlogic_opsel = `XLOGIC_OP_XOR;
                    end
                    // srl, sra
                    3'b101: begin
                        valid = funct7 == 7'b0000000 || funct7 == 7'b0100000;
                        pipeline = `PIPE_XLOGIC;
                        xlogic_opsel = `XLOGIC_OP_SHF;
                    end
                    // or
                    3'b110: begin
                        valid = 1'b1;
                        pipeline = `PIPE_XLOGIC;
                        xlogic_opsel = `XLOGIC_OP_OR;
                    end
                    // and
                    3'b111: begin
                        valid = 1'b1;
                        pipeline = `PIPE_XLOGIC;
                        xlogic_opsel = `XLOGIC_OP_AND;
                    end
                endcase

                xarith_sub = funct7[5];
                xarith_unsigned = funct3[0];
                xlogic_invert = 1'b0;
            end
            // lui
            op_lui: begin
                valid = 1'b1;
                pipeline = `PIPE_XARITH;
                xarith_opsel = `XARITH_OP_ADD;
                xarith_sub = 1'b0;
            end
            op_op_32: begin
                case (funct3)
                    // addw, subw
                    3'b000: begin
                        valid = funct7 == 7'b0000000 || funct7 == 7'b0100000;
                        pipeline = `PIPE_XARITH;
                        xarith_opsel = `XARITH_OP_ADD;
                    end
                    // sllw
                    3'b001: begin
                        valid = funct7 == 7'b0000000;
                        pipeline = `PIPE_XLOGIC;
                        xlogic_opsel = `XLOGIC_OP_SHF;
                    end
                    // srlw, sraw
                    3'b101: begin
                        valid = funct7 == 7'b0000000 || funct7 == 7'b0100000;
                        pipeline = `PIPE_XLOGIC;
                        xlogic_opsel = `XLOGIC_OP_SHF;
                    end
                endcase

                xarith_sub = funct7[5];
                xlogic_invert = 1'b0;
            end
        endcase
    end

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
    wire [2:0] rs1p    = i_inst[9:7];
    wire [2:0] funct3  = i_inst[15:13];
    wire [3:0] funct4  = i_inst[15:12];
    wire [5:0] funct6  = i_inst[15:10];

    // instruction valid
    reg valid;
    // backend pipeline selection
    reg [3:0] pipeline;
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
        xarith_opsel = 2'bxx;
        xarith_sub = 1'bx;
        xarith_unsigned = 1'bx;
        xarith_cmp_mode = 1'bx;
        xarith_branch_equal = 1'bx;
        xarith_branch_invert = 1'bx;
        xlogic_opsel = 3'bxxx;
        xlogic_invert = 1'bx;
        xlogic_sll = 2'bxx;
    end
endmodule
