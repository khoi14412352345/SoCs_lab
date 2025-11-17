`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 11/14/2025 05:30:24 PM
// Design Name: 
// Module Name: tb_sevenseg
// Project Name: 
// Target Devices: 
// Tool Versions: 
// Description: 
// 
// Dependencies: 
// 
// Revision:
// Revision 0.01 - File Created
// Additional Comments:
// 
//////////////////////////////////////////////////////////////////////////////////


module tb_sevenseg;

    reg         clk;
    reg  [3:0]  in;
    reg  [1:0]  sw;
    wire [6:0]  seg;
    wire        dp;
    wire [3:0]  an;
    wire [3:0]  out;

    // Small "clock frequency" for simulation:
    // 1 "second" tick every 10 cycles (CLK_FREQ = 10)
    localparam integer SIM_CLK_FREQ = 10;

    // Instantiate DUT
    sevenseg #(
        .CLK_FREQ(SIM_CLK_FREQ)
    ) dut (
        .clk(clk),
        .in(in),
        .sw(sw),
        .seg(seg),
        .dp(dp),
        .an(an),
        .out(out)
    );

    // Clock: 10 ns period (100 MHz in sim time, but logic assumes 10 Hz)
    initial begin
        clk = 1'b0;
        forever #5 clk = ~clk;
    end

    initial begin
        // Initial values
        in = 4'b0000;
        sw = 2'b00;   // Effect 1 (scroll) by default

        // Apply reset via BTN0
        #20;
        in[0] = 1'b1;
        #20;
        in[0] = 1'b0;

        // Let it run in Effect 1 for some "seconds"
        #500;

        // Switch to Effect 2 (bounce)
        sw[0] = 1'b1;

        // Run in Effect 2 for more "seconds"
        #500;

        $finish;
    end

    // Monitor debug out signals
    initial begin
        $display("Time\t reset sw[0] pos(out[1:0]) effect(out[2])");
        $monitor("%0t\t %b     %b    %b           %b",
                 $time, in[0], sw[0], out[1:0], out[2]);
    end

endmodule
