module rvfi_wrapper (
    input wire clock,
    input wire reset,
    `RVFI_OUTPUTS
);
    
    (* keep *) wire [31:0] imem_addr;
    (* keep *) wire [31:0] imem_rdata;
    (* keep *) wire [31:0] dmem_addr;
    (* keep *) wire [31:0] dmem_wdata;
    (* keep *) wire [31:0] dmem_rdata;

    warp_hart dut (
        .i_clk(clock),
        .i_rst_n(!reset),

        // .o_imem_addr(imem_addr),
        // .i_imem_rdata(imem_rdata),
        // .o_dmem_addr(dmem_addr),
        // .o_dmem_wdata(dmem_wdata),
        // .i_dmem_rdata(dmem_rdata),

        `RVFI_CONN
    );
endmodule
