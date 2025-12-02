`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 11/17/2025 10:10:22 AM
// Design Name: 
// Module Name: tb_divider_unsigned
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


module tb_divider_unsigned;

    reg  [31:0] dividend, divisor;
    wire [31:0] quotient, remainder;

    divider_unsigned dut (
        .dividend(dividend),
        .divisor (divisor),
        .quotient(quotient),
        .remainder(remainder)
    );

    initial begin
        // ví dụ 1: 13 / 5
        dividend = 32'd13;
        divisor  = 32'd5;
        #10;   // combinational nên chỉ cần chút thời gian

        $display("13 / 5: q = %0d, r = %0d", quotient, remainder);

        // ví dụ 2: 100 / 7
        dividend = 32'd100;
        divisor  = 32'd7;
        #10;
        $display("100 / 7: q = %0d, r = %0d", quotient, remainder);

        $finish;
    end

endmodule