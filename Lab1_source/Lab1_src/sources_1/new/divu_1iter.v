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
    input  [31:0] dividend_in,
    input  [31:0] divisor,
    input  [31:0] quotient_in,
    input  [31:0] remainder_in,

    output [31:0] dividend_out,
    output [31:0] quotient_out,
    output [31:0] remainder_out
);
    // remainder' = (remainder << 1) | MSB(dividend)
    wire [31:0] rem_shift;
    assign rem_shift = {remainder_in[30:0], dividend_in[31]};

    // dividend' = dividend << 1
    assign dividend_out = {dividend_in[30:0], 1'b0};

    // so sánh remainder' với divisor
    wire rem_lt_div;
    assign rem_lt_div = (rem_shift < divisor);

    // nếu rem_shift < divisor:
    //    quotient'  = quotient << 1
    //    remainder' = rem_shift
    // ngược lại:
    //    quotient'  = (quotient << 1) | 1
    //    remainder' = rem_shift - divisor
    assign quotient_out  = rem_lt_div ?
                           (quotient_in << 1) :
                           ((quotient_in << 1) | 32'h0000_0001);

    assign remainder_out = rem_lt_div ?
                           rem_shift :
                           (rem_shift - divisor);

endmodule