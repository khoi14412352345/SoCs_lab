`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 11/17/2025 09:50:46 AM
// Design Name: 
// Module Name: divu_1iter
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


module divu_1iter (
    input  [31:0] i_dividend_in,
    input  [31:0] i_divisor,
    input  [31:0] i_quotient_in,
    input  [31:0] i_remainder_in,

    output [31:0] o_dividend_out,
    output [31:0] o_quotient_out,
    output [31:0] o_remainder_out
);

    // remainder' = (remainder << 1) | MSB(dividend)
    wire [31:0] rem_shift;
    assign rem_shift = {i_remainder_in[30:0], i_dividend_in[31]};

    // dividend' = dividend << 1
    assign o_dividend_out = {i_dividend_in[30:0], 1'b0};

    // so sánh remainder' với divisor
    wire rem_lt_div;
    assign rem_lt_div = (rem_shift < i_divisor);

    // quotient' = shift left, thêm bit 0 hoặc 1 tùy theo so sánh
    assign o_quotient_out =
        rem_lt_div ?
            (i_quotient_in << 1) :
            ((i_quotient_in << 1) | 32'h1);

    // remainder' = rem_shift hoặc rem_shift - divisor
    assign o_remainder_out =
        rem_lt_div ?
            rem_shift :
            (rem_shift - i_divisor);

endmodule
