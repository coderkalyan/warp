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
        // 32'h08200113 for addi (stalls because of backend throughput)
        imem_rdata = {32'h08206113, 32'h07800093};
        @(posedge clk); // decode

        // imem_rdata = {32'h08206113, 32'h07800093};
        // imem_rdata = {32'h03206213, 32'h1c200193};
        @(negedge clk);
        imem_valid = 0;
        imem_rdata = 0;
        @(posedge clk); // issue

        imem_valid = 0;
        imem_rdata = 0;
        @(posedge clk); // execute

        @(posedge clk); // write back

        @(posedge clk); // done
        $display("cycle 7:");
        $display("x1: %d", $signed(hart.xrf.file[1]));
        $display("x2: %d", $signed(hart.xrf.file[2]));
        $display("x3: %d", $signed(hart.xrf.file[3]));
        $display("x4: %d", $signed(hart.xrf.file[4]));

        @(posedge clk); // done
        $display("cycle 8:");
        $display("x3: %d", $signed(hart.xrf.file[3]));
        $display("x4: %d", $signed(hart.xrf.file[4]));

        @(posedge clk);
        @(posedge clk);

        $finish;
    end

    always #5 clk <= ~clk;
endmodule

`default_nettype wire
