`default_nettype none

module warp_icache_tb ();
    logic        clk, rst_n;
    logic        req_valid;
    logic [63:0] req_raddr;
    logic        res_valid;
    logic [63:0] res_rdata;
    logic        ahb_hclk, ahb_hreset_n;
    logic [63:0] ahb_haddr;
    logic [ 2:0] ahb_hburst;
    logic        ahb_hmastlock;
    logic [ 3:0] ahb_hprot;
    logic [ 2:0] ahb_hsize;
    logic        ahb_hnonsec, ahb_hexcl;
    logic [ 1:0] ahb_htrans;
    logic [63:0] ahb_hwdata;
    logic [ 7:0] ahb_hwstrb;
    logic        ahb_hwrite;
    logic [63:0] ahb_hrdata;
    logic        ahb_hreadyout, ahb_hresp, ahb_hexokay;

    warp_icache icache (
        .i_clk(clk),
        .i_rst_n(rst_n),
        .i_req_valid(req_valid),
        .i_req_raddr(req_raddr),
        .o_res_valid(res_valid),
        .o_res_rdata(res_rdata),
        .o_ahb_hclk(ahb_hclk),
        .o_ahb_hreset_n(ahb_hreset_n),
        .o_ahb_haddr(ahb_haddr),
        .o_ahb_hburst(ahb_hburst),
        .o_ahb_hmastlock(ahb_hmastlock),
        .o_ahb_hprot(ahb_hprot),
        .o_ahb_hsize(ahb_hsize),
        .o_ahb_hnonsec(ahb_hnonsec),
        .o_ahb_hexcl(ahb_hexcl),
        .o_ahb_htrans(ahb_htrans),
        .o_ahb_hwdata(ahb_hwdata),
        .o_ahb_hwstrb(ahb_hwstrb),
        .o_ahb_hwrite(ahb_hwrite),
        .i_ahb_hrdata(ahb_hrdata),
        .i_ahb_hready(ahb_hreadyout),
        .i_ahb_hresp(ahb_hresp),
        .i_ahb_hexokay(ahb_hexokay)
    );

    logic [63:0] memory [0:15];

    localparam HTRANS_IDLE   = 2'b00;
    localparam HTRANS_BUSY   = 2'b01;
    localparam HTRANS_NONSEQ = 2'b10;
    localparam HTRANS_SEQ    = 2'b11;

    localparam HBURST_SINGLE = 3'b000;
    localparam HBURST_INCR   = 3'b001;
    localparam HBURST_WRAP4  = 3'b010;
    localparam HBURST_INCR4  = 3'b011;
    localparam HBURST_WRAP8  = 3'b100;
    localparam HBURST_INCR8  = 3'b101;
    localparam HBURST_WRAP16 = 3'b110;
    localparam HBURST_INCR16 = 3'b111;

    assign ahb_hreadyout = rst_n && (ahb_htrans != HTRANS_IDLE);
    always @(posedge clk, negedge rst_n) begin
        if (ahb_htrans != HTRANS_IDLE)
            ahb_hrdata <= memory[ahb_haddr >> 3];
    end

    integer i;
    initial begin
        $dumpfile("warp_icache_tb.vcd");
        $dumpvars(0, warp_icache_tb);

        rst_n = 0;
        clk = 0;
        req_valid = 0;
        req_raddr = 0;
        ahb_hrdata = 0;
        $readmemh("imem.hex", memory);

        #10;
        rst_n = 1;

        @(posedge clk); #0;

        // first transaction at address 0x00
        req_raddr = 64'h00;
        req_valid = 1;

        @(posedge clk); #0;
        req_valid = 0;

        // for (i = 0; i < 10; i = i + 1)
        //     @(posedge clk);

        @(posedge res_valid);
        // while (ahb_htrans != HTRANS_IDLE)
        //     @(posedge clk);

        // immediately start another transaction at address 0x40
        req_raddr = 64'h40;
        req_valid = 1;

        @(posedge clk);
        req_valid = 0;

        // @(posedge res_valid);
        // while (ahb_htrans != HTRANS_IDLE)
        //     @(posedge clk);

        @(posedge clk);
        @(posedge clk);

        $finish;
    end

    always #5 clk = ~clk;
endmodule

`default_nettype wire
