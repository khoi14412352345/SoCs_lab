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
    input  [31:0] dividend,
    input  [31:0] divisor,
    output [31:0] quotient,
    output [31:0] remainder
);
    // Mảng tín hiệu cho 33 điểm (0..32)
    wire [31:0] dividend_stage  [0:32];
    wire [31:0] quotient_stage  [0:32];
    wire [31:0] remainder_stage [0:32];

    // giá trị ban đầu (trước iteration #0)
    assign dividend_stage[0]  = dividend;
    assign quotient_stage[0]  = 32'b0;
    assign remainder_stage[0] = 32'b0;

    genvar i;
    generate
        for (i = 0; i < 32; i = i + 1) begin : iter
            divu_1iter u_iter (
                .dividend_in  (dividend_stage[i]),
                .divisor      (divisor),
                .quotient_in  (quotient_stage[i]),
                .remainder_in (remainder_stage[i]),

                .dividend_out (dividend_stage[i+1]),
                .quotient_out (quotient_stage[i+1]),
                .remainder_out(remainder_stage[i+1])
            );
        end
    endgenerate

    // kết quả cuối cùng sau 32 vòng
    assign quotient  = quotient_stage[32];
    assign remainder = remainder_stage[32];

endmodule