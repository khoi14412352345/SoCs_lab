`timescale 1ns / 1ps

// -----------------------------------------------------------------------------
// 1-bit generate/propagate cell
// -----------------------------------------------------------------------------
// Given a single bit of a and b:
//   g = generate  = 1 if this bit-pair will generate a carry (a & b)
//   p = propagate = 1 if this bit-pair will propagate an incoming carry (a | b)
/**
 * @param a first 1-bit input
 * @param b second 1-bit input
 * @param g whether a and b generate a carry
 * @param p whether a and b would propagate an incoming carry
 */
module gp1 (
    input  wire a,
    input  wire b,
    output wire g,
    output wire p
);
    // Generate when both bits are 1
    assign g = a & b;

    // Propagate when at least one bit is 1
    assign p = a | b;
endmodule

// -----------------------------------------------------------------------------
// 4-bit group generate/propagate
// -----------------------------------------------------------------------------
// Computes the group generate (gout) and group propagate (pout) for 4 bits,
// plus the internal carries (cout[2:0]) using the gin/pin "bit-level" G/P.
/**
 * Computes aggregate generate/propagate signals over a 4-bit window.
 * @param gin incoming generate signals
 * @param pin incoming propagate signals
 * @param cin the incoming carry
 * @param gout whether these 4 bits internally would generate a carry-out (independent of cin)
 * @param pout whether these 4 bits internally would propagate an incoming carry from cin
 * @param cout the carry outs for the low-order 3 bits
 */
module gp4 (
    input  wire [3:0] gin,
    input  wire [3:0] pin,
    input  wire       cin,
    output wire       gout,
    output wire       pout,
    output wire [2:0] cout
);

    // TODO: your code here
    // Local g/p signals computed from gin/pin using gp1
    wire [3:0] g;
    wire [3:0] p;

    // Compute bit-level generate/propagate for each position
    gp1 gp_bit0 (
        .a (gin[0]),
        .b (pin[0]),
        .g (g[0]),
        .p (p[0])
    );

    gp1 gp_bit1 (
        .a (gin[1]),
        .b (pin[1]),
        .g (g[1]),
        .p (p[1])
    );

    gp1 gp_bit2 (
        .a (gin[2]),
        .b (pin[2]),
        .g (g[2]),
        .p (p[2])
    );

    gp1 gp_bit3 (
        .a (gin[3]),
        .b (pin[3]),
        .g (g[3]),
        .p (p[3])
    );

    // Carry-out of bit 0 (goes into bit 1)
    assign cout[0] = g[0] | (p[0] & cin);

    // Carry-out of bit 1 (goes into bit 2)
    assign cout[1] = g[1]
                   | (p[1] & g[0])
                   | (p[1] & p[0] & cin);

    // Carry-out of bit 2 (goes into bit 3)
    assign cout[2] = g[2]
                   | (p[2] & g[1])
                   | (p[2] & p[1] & g[0])
                   | (p[2] & p[1] & p[0] & cin);

    // Group generate for all 4 bits:
    //  whether this block will generate a carry regardless of cin
    assign gout = g[3]
                | (p[3] & g[2])
                | (p[3] & p[2] & g[1])
                | (p[3] & p[2] & p[1] & g[0]);

    // Group propagate: all bits must propagate
    assign pout = &p;
endmodule

// -----------------------------------------------------------------------------
// 8-bit group generate/propagate
// -----------------------------------------------------------------------------
// Same idea as gp4 but for 8 bits, built hierarchically from two gp4 blocks.
/** Same as gp4 but for an 8-bit window instead */
module gp8 (
    input  wire [7:0] gin,
    input  wire [7:0] pin,
    input  wire       cin,
    output wire       gout,
    output wire       pout,
    output wire [6:0] cout
);

    // TODO: your code here

    // Group generate/propagate for lower and upper 4-bit blocks
    wire       g_low;
    wire       p_low;
    wire       g_high;
    wire       p_high;

    // Internal carries inside each 4-bit block
    wire [2:0] c_low;
    wire [2:0] c_high;

    // Carry between lower 4-bit block and upper 4-bit block
    wire       c4;

    // Lower 4 bits (bits 0..3)
    gp4 lower (
        .gin  (gin[3:0]),
        .pin  (pin[3:0]),
        .cin  (cin),
        .gout (g_low),
        .pout (p_low),
        .cout (c_low)
    );

    // Carry into upper 4 bits = group generate low OR (group propagate low & cin)
    assign cout[2:0] = c_low;
    assign c4        = g_low | (p_low & cin);
    assign cout[3]   = c4;

    // Upper 4 bits (bits 4..7)
    gp4 upper (
        .gin  (gin[7:4]),
        .pin  (pin[7:4]),
        .cin  (c4),
        .gout (g_high),
        .pout (p_high),
        .cout (c_high)
    );

    // Internal carries of the high 4-bit block (bits 5,6,7)
    assign cout[6:4] = c_high;

    // Group generate/propagate for the full 8-bit block
    assign gout = g_high | (p_high & g_low);
    assign pout = p_high & p_low;

endmodule

// -----------------------------------------------------------------------------
// 32-bit Carry Lookahead Adder (CLA)
// -----------------------------------------------------------------------------
// Uses:
//   - gp1 for bit-level generate/propagate
//   - gp4/gp8 hierarchy for efficient carry computation across 32 bits
// ---------------------------------------------------------------------------
module cla (
    input  wire [31:0] a,
    input  wire [31:0] b,
    input  wire        cin,
    output wire [31:0] sum
);

    // TODO: your code here

    // Bit-level generate/propagate for all 32 bits
    wire [31:0] g;
    wire [31:0] p;

    // Group generate/propagate per 8-bit block
    wire [3:0]  g8;
    wire [3:0]  p8;

    // c[i] is the carry into bit (i+1), i.e. c[0] is carry into bit 1
    wire [30:0] c;

    // carry8[k] is the carry into 8-bit block k+1
    //   carry8[0] -> block1, carry8[1] -> block2, carry8[2] -> block3
    wire [2:0]  carry8;

    // ------------------------------------------------------------------------
    // Compute bit-level G/P using gp1 for each bit
    // ------------------------------------------------------------------------
    genvar i;
    generate
        for (i = 0; i < 32; i = i + 1) begin : GP1
            gp1 gp1_inst (
                .a (a[i]),
                .b (b[i]),
                .g (g[i]),
                .p (p[i])
            );
        end
    endgenerate

    // ------------------------------------------------------------------------
    // Group into four 8-bit blocks and compute internal carries
    // ------------------------------------------------------------------------
    // Block 0: bits [7:0]
    gp8 block0 (
        .gin  (g[7:0]),
        .pin  (p[7:0]),
        .cin  (cin),
        .gout (g8[0]),
        .pout (p8[0]),
        .cout (c[6:0])
    );

    // Block 1: bits [15:8]
    gp8 block1 (
        .gin  (g[15:8]),
        .pin  (p[15:8]),
        .cin  (carry8[0]),
        .gout (g8[1]),
        .pout (p8[1]),
        .cout (c[14:8])
    );

    // Block 2: bits [23:16]
    gp8 block2 (
        .gin  (g[23:16]),
        .pin  (p[23:16]),
        .cin  (carry8[1]),
        .gout (g8[2]),
        .pout (p8[2]),
        .cout (c[22:16])
    );

    // Block 3: bits [31:24]
    gp8 block3 (
        .gin  (g[31:24]),
        .pin  (p[31:24]),
        .cin  (carry8[2]),
        .gout (g8[3]),
        .pout (p8[3]),
        .cout (c[30:24])
    );

    // ------------------------------------------------------------------------
    // Carry between 8-bit blocks
    // ------------------------------------------------------------------------
    assign carry8[0] = g8[0] | (p8[0] & cin);
    assign carry8[1] = g8[1] | (p8[1] & carry8[0]);
    assign carry8[2] = g8[2] | (p8[2] & carry8[1]);

    // Insert block-level carries at bit positions 8, 16, 24
    assign c[7]  = carry8[0];
    assign c[15] = carry8[1];
    assign c[23] = carry8[2];

    // ------------------------------------------------------------------------
    // Final sum computation: sum = a ^ b ^ carry
    // ------------------------------------------------------------------------
    // Bit 0 uses cin directly
    assign sum[0] = a[0] ^ b[0] ^ cin;

    // Bits 31..1 use the corresponding carry from c[30..0]
    assign sum[31:1] = a[31:1] ^ b[31:1] ^ c[30:0];

endmodule
