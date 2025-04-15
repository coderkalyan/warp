# Warp

Welcome to the repository of warp, an open source processor core IP targeting the RISC-V instruction set architecture. Specifically, it is a dual issue in order architecture supporting the RV64GCBV architecture, plus privileged mode and various other minor extensions.

## Progress

Warp is early in development. It currently executes most of the base RV32I and RV64I instruction set, with the exception of shift, load/store, unconditional jumps, and environment calls. An exhaustive instruction support list is below:

### RV32I
* add, sub, or, and, xor, slt, sltu
* addi, ori, andi, xori, slti, sltiu
* lui, auipc
* beq, bne, blt, bltu, bge, bgeu

### RV64I
* addw, subw
* addiw
