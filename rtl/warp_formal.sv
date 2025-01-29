module warp_formal ();
    reg f_past_valid;
    initial f_past_valid <= 1'b0;
    always @(posedge i_clk) f_past_valid <= 1'b1;

    (* gclk *) reg formal_timestep;

    module f_fetch_interface ();
        initial begin
            assume (!i_rst_n);
            assume (!i_clk);
            assume (!i_mem_valid);
            assume (!i_branch_valid);

            assert (!o_output_valid);
            assert (!o_mem_ren);
        end

        // the interface is entirely synchronous
        always @(posedge formal_timestep) begin
            if (f_past_valid && !$rose(i_clk) && !$changed(i_rst_n)) begin
                assume ($stable(i_mem_rdata));
                assume ($stable(i_mem_valid));
                assume ($stable(i_branch_target));
                assume ($stable(i_branch_valid));
                assume ($stable(i_output_ready));

                assert ($stable(o_mem_raddr));
                assert ($stable(o_mem_ren));
                assert ($stable(o_output_valid));
                assert ($stable(o_inst0));
                assert ($stable(o_inst1));
                assert ($stable(o_compressed));
                assert ($stable(o_count));
            end
        end
    endmodule
endmodule
