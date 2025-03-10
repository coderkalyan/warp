`ifndef WARP_DEFINES
`define WARP_DEFINES

`define XARITH_OP_ADD 2'b00
`define XARITH_OP_SLT 2'b01
`define XARITH_OP_CMP 2'b10

`define XLOGIC_OP_AND 3'b000
`define XLOGIC_OP_OR  3'b001
`define XLOGIC_OP_XOR 3'b010
`define XLOGIC_OP_SHF 3'b011
`define XLOGIC_OP_SLA 3'b100
`define XLOGIC_OP_CLZ 3'b101
`define XLOGIC_OP_CTZ 3'b110
`define XLOGIC_OP_POP 3'b111

`define PIPE_XARITH 4'd0
`define PIPE_XLOGIC 4'd1
`define PIPE_XSHIFT 4'd2
`define PIPE_XMULTL 4'd3
`define PIPE_XMULTH 4'd4
`define PIPE_XDIV   4'd5

`define AHB_HTRANS_IDLE   2'b00
`define AHB_HTRANS_BUSY   2'b01
`define AHB_HTRANS_NONSEQ 2'b10
`define AHB_HTRANS_SEQ    2'b11

`define CANONICAL_NOP 32'h00000013
`define BUNDLE_SIZE 67

`endif
