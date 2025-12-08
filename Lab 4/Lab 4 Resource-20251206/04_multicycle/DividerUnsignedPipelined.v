`timescale 1ns / 1ns

// quotient = dividend / divisor

module DividerUnsignedPipelined (
    input             clk, rst, stall,
    input      [31:0] i_dividend,
    input      [31:0] i_divisor,
    output reg [31:0] o_remainder,
    output reg [31:0] o_quotient
);

  // TODO: your code here

endmodule


module divu_1iter (
    input      [31:0] i_dividend,
    input      [31:0] i_divisor,
    input      [31:0] i_remainder,
    input      [31:0] i_quotient,
    output reg [31:0] o_dividend,
    output reg [31:0] o_remainder,
    output reg [31:0] o_quotient
);

  // TODO: copy your code from homework #1 here

endmodule
