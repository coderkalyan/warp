`default_nettype none

module warp_hart_tb ();
    logic clk, rst_n;
    logic imem_ren, imem_valid;
    logic [38:0] imem_raddr;
    logic [63:0] imem_rdata;

    warp_hart #(.RESET_ADDR(39'h4000000000)) hart (
        .i_clk(clk),
        .i_rst_n(rst_n),
        .o_imem_ren(imem_ren),
        .o_imem_raddr(imem_raddr),
        .i_imem_valid(imem_valid),
        .i_imem_rdata(imem_rdata)
    );

    initial begin
        $dumpfile("warp_hart_tb.vcd");
        $dumpvars(0, warp_hart_tb);

        clk = 0;
        rst_n = 0;
        imem_valid = 0;
        imem_rdata = 0;

        #4;
        rst_n = 1;
        @(posedge clk); // init

        @(posedge clk); // fetch

        imem_valid = 1;
        imem_rdata = {32'h001000b3, 32'h00100133};
        @(posedge clk); // decode

        imem_valid = 0;
        imem_rdata = 0;
        @(posedge clk); // issue

        @(posedge clk); // execute

        $finish;
    end

    always #5 clk <= ~clk;
endmodule

`default_nettype wire
