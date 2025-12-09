`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 11/17/2025 09:51:19 AM
// Design Name: 
// Module Name: divider_unsigned
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


module divider_unsigned (
    input  [31:0] i_dividend,     // was: dividend
    input  [31:0] i_divisor,      // was: divisor
    output [31:0] o_quotient,     // was: quotient
    output [31:0] o_remainder     // was: remainder
);

    // Internal stage arrays (0..32)
    wire [31:0] dividend_stage  [0:32];
    wire [31:0] quotient_stage  [0:32];
    wire [31:0] remainder_stage [0:32];

    // Initial values before iteration 0
    assign dividend_stage[0]  = i_dividend;
    assign quotient_stage[0]  = 32'b0;
    assign remainder_stage[0] = 32'b0;

    genvar i;
    generate
        for (i = 0; i < 32; i = i + 1) begin : iter
            divu_1iter u_iter (
    .i_dividend_in (dividend_stage[i]),
    .i_divisor     (i_divisor),
    .i_quotient_in (quotient_stage[i]),
    .i_remainder_in(remainder_stage[i]),

    .o_dividend_out(dividend_stage[i+1]),
    .o_quotient_out(quotient_stage[i+1]),
    .o_remainder_out(remainder_stage[i+1])
);

        end
    endgenerate

    // Final results after 32 rounds
    assign o_quotient  = quotient_stage[32];
    assign o_remainder = remainder_stage[32];

endmodule

