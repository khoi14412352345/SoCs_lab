`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 11/14/2025 05:31:24 PM
// Design Name: 
// Module Name: tb_stringbit
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


module tb_stringbit;

    reg         clk;
    reg  [3:0]  in;
    wire [3:0]  out;
    wire        uart_tx;

    // Use very small "clock freq" and baud rate for quick sim
    localparam integer SIM_CLK_FREQ = 10;  // "10 Hz" for 1s tick every 10 cycles
    localparam integer SIM_BAUD     = 1;   // 1 baud -> 10 cycles per bit (BAUD_DIV = 10)

    // Instantiate DUT
    stringbit #(
        .CLK_FREQ   (SIM_CLK_FREQ),
        .BAUD       (SIM_BAUD),
        .DEFAULT_STR(4'b0011)
    ) dut (
        .clk    (clk),
        .in     (in),
        .out    (out),
        .uart_tx(uart_tx)
    );

    // Clock: 10ns period (100 MHz in simulation time, but our logic thinks it's 10 Hz)
    initial begin
        clk = 1'b0;
        forever #5 clk = ~clk;
    end

    // Stimulus
    initial begin
        in = 4'b0000;

        // Apply Mode Reset (BTN0) to set default string
        #20;
        in[0] = 1'b1;
        #10;
        in[0] = 1'b0;

        // Let it sit in RESET mode for a few "seconds"
        #200;

        // Mode = Circular Shift Left Ring (BTN1)
        in[1] = 1'b1;
        #10;
        in[1] = 1'b0;

        // Run shifting left for a while
        #300;

        // Pause (BTN3)
        in[3] = 1'b1;
        #10;
        in[3] = 1'b0;

        // Stay paused for a bit
        #200;

        // Mode = Circular Shift Right Ring (BTN2)
        in[2] = 1'b1;
        #10;
        in[2] = 1'b0;

        // Run shifting right
        #300;

        $finish;
    end

    // Simple console monitor
    initial begin
        $display("Time\t buttons(in)\t LEDs(out)");
        $monitor("%0t\t %b\t\t %b", $time, in, out);
    end

endmodule
