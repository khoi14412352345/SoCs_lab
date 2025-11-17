`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 11/14/2025 03:17:43 PM
// Design Name: 
// Module Name: tb_traffic_lights
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


`timescale 1ns / 1ps

module tb_traffic_lights;

    reg         clk;
    reg  [1:0]  sw;
    reg  [3:0]  in;

    wire        led4_r, led4_g, led4_b;
    wire        led5_r, led5_g, led5_b;
    wire [3:0]  out;
    wire [6:0]  seg;
    wire        dp;
    wire [3:0]  an;

    // Instantiate DUT with small parameters for fast simulation
    traffic_lights #(
        .CLK_FREQ   (10),  // 10 "Hz"
        .GREEN_TIME (4),   // 4 seconds
        .YELLOW_TIME(2)    // 2 seconds
    ) dut (
        .clk    (clk),
        .sw     (sw),
        .in     (in),
        .led4_r (led4_r),
        .led4_g (led4_g),
        .led4_b (led4_b),
        .led5_r (led5_r),
        .led5_g (led5_g),
        .led5_b (led5_b),
        .out    (out),
        .seg    (seg),
        .dp     (dp),
        .an     (an)
    );

    // Clock: 10 ns period → 100 MHz sim clock (but CLK_FREQ=10 ticks)
    initial begin
        clk = 1'b0;
        forever #5 clk = ~clk;
    end

    initial begin
        // Initial values
        sw = 2'b00;   // base timing
        in = 4'b0000; // no reset yet

        // Apply reset
        #20;
        in[0] = 1'b1;
        #40;
        in[0] = 1'b0;

        // Run long enough to see a few full cycles
        #5000;

        $finish;
    end

    // Optional monitor for debugging in console
    initial begin
        $display("Time\t state out\tled4 (RGB)\tled5 (RGB)\tan seg");
        $monitor("%0t\t %0d   %b\t %b%b%b\t %b%b%b\t %b %b",
                 $time,
                 dut.state,
                 out,
                 led4_r, led4_g, led4_b,
                 led5_r, led5_g, led5_b,
                 an, seg);
    end

endmodule
