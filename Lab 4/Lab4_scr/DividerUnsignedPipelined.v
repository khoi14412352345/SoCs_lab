`timescale 1ns / 1ps

// ---------------------------------------------------------------------------
// DividerUnsignedPipelined
// ---------------------------------------------------------------------------
// - 32-bit unsigned divider
// - 8 pipeline stages
// - Each stage performs 4 "1-iteration" divide steps (divu_1iter)
// - Total of 32 iterations = 32 bits of quotient
// - Interface:
//     * clk   : pipeline clock
//     * rst   : synchronous reset for pipeline registers
//     * stall : when 1, hold the pipeline (no new data moves to next stage)
// ---------------------------------------------------------------------------
module DividerUnsignedPipelined (
    input             clk,
    input             rst,
    input             stall,
    input      [31:0] i_dividend,
    input      [31:0] i_divisor,
    output     [31:0] o_remainder,
    output     [31:0] o_quotient
);

    // Pipeline register arrays (9 stages: 0..8)
    // stage_*[0] : initial input stage
    // stage_*[1] : after stage 0
    // ...
    // stage_*[8] : after stage 7 (final output)
    reg [31:0] stage_dividend [0:8];
    reg [31:0] stage_remainder[0:8];
    reg [31:0] stage_quotient [0:8];
    reg [31:0] stage_divisor  [0:8];

    // -----------------------------------------------------------------------
    // Stage 0: purely combinational input logic
    // - Capture i_dividend and i_divisor
    // - Initialize remainder and quotient to zero
    // -----------------------------------------------------------------------
    always @(*) begin
        stage_dividend[0]  = i_dividend;
        stage_divisor[0]   = i_divisor;
        stage_remainder[0] = 32'b0;
        stage_quotient[0]  = 32'b0;
    end

    genvar i, j;

    generate
        // -------------------------------------------------------------------
        // 8 pipeline stages
        // Each stage performs 4 internal division iterations
        // -------------------------------------------------------------------
        for (i = 0; i < 8; i = i + 1) begin : STAGE

            // Intermediate wires inside one stage (4 iterations)
            // t_*[0] : stage input (from stage_*[i])
            // t_*[4] : stage output (goes to stage_*[i+1])
            wire [31:0] t_dividend [0:4];
            wire [31:0] t_remainder[0:4];
            wire [31:0] t_quotient [0:4];

            // Chain input comes from previous pipeline stage registers
            assign t_dividend[0]  = stage_dividend[i];
            assign t_remainder[0] = stage_remainder[i];
            assign t_quotient[0]  = stage_quotient[i];

            // ----------------------------------------------------------------
            // 4 serial "1-iteration" dividers within this stage
            // ----------------------------------------------------------------
            for (j = 0; j < 4; j = j + 1) begin : ITER
                divu_1iter u_iter (
                    // Inputs
                    .i_dividend  (t_dividend[j]),
                    .i_divisor   (stage_divisor[i]),
                    .i_remainder (t_remainder[j]),
                    .i_quotient  (t_quotient[j]),

                    // Outputs
                    .o_dividend  (t_dividend[j+1]),
                    .o_remainder (t_remainder[j+1]),
                    .o_quotient_bit (),             // single bit not used here
                    .o_quotient  (t_quotient[j+1])
                );
            end

            // ----------------------------------------------------------------
            // Sequential logic: register outputs into the next pipeline stage
            // ----------------------------------------------------------------
            always @(posedge clk) begin
                if (rst) begin
                    stage_dividend[i+1]  <= 32'b0;
                    stage_remainder[i+1] <= 32'b0;
                    stage_quotient[i+1]  <= 32'b0;
                    stage_divisor[i+1]   <= 32'b0;
                end else if (!stall) begin
                    // Pass the results of the 4-iteration chain to the next stage
                    stage_dividend[i+1]  <= t_dividend[4];
                    stage_remainder[i+1] <= t_remainder[4];
                    stage_quotient[i+1]  <= t_quotient[4];
                    stage_divisor[i+1]   <= stage_divisor[i];
                end
            end
        end
    endgenerate

    // Final outputs from the last pipeline stage
    assign o_quotient  = stage_quotient[8];
    assign o_remainder = stage_remainder[8];

endmodule

// ---------------------------------------------------------------------------
// divu_1iter
// ---------------------------------------------------------------------------
// One iteration of restoring division for unsigned 32-bit inputs:
// - Shifts in one new dividend bit into the remainder
// - Compares with divisor
// - Conditionally subtracts divisor
// - Produces next remainder, next dividend, and next quotient
// ---------------------------------------------------------------------------
module divu_1iter (
    input      [31:0] i_dividend,
    input      [31:0] i_divisor,
    input      [31:0] i_remainder,
    input      [31:0] i_quotient,
    output     [31:0] o_dividend,
    output     [31:0] o_remainder,
    output            o_quotient_bit,
    output     [31:0] o_quotient
);

    // Shifted remainder (bring in the MSB of dividend)
    wire [31:0] remainder_sh;
    // Difference remainder_sh - divisor
    wire [31:0] diff;
    // Flag: remainder_sh >= divisor?
    wire        gte;

    assign remainder_sh = {i_remainder[30:0], i_dividend[31]};
    assign gte          = (remainder_sh >= i_divisor);
    assign diff         = remainder_sh - i_divisor;

    // If remainder_sh >= divisor, subtract; otherwise keep remainder_sh
    assign o_remainder    = gte ? diff : remainder_sh;

    // This iteration's quotient bit
    assign o_quotient_bit = gte;

    // Next dividend: shift left by 1 (we consume the MSB each step)
    assign o_dividend     = i_dividend << 1;

    // Next quotient: shift previous quotient left and OR in the new bit
    assign o_quotient     = (i_quotient << 1) | {31'b0, gte};

endmodule
