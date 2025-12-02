`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 11/14/2025 05:29:39 PM
// Design Name: 
// Module Name: sevenseg
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


module sevenseg #(
    parameter integer CLK_FREQ = 125_000_000  // Arty Z7 system clock
)(
    input  wire        clk,
    input  wire [3:0]  in,   // buttons (in[0] = reset)
    input  wire [1:0]  sw,   // switches (sw[0] selects effect)
    output reg  [6:0]  seg,  // 7-seg segments a..g (active-high)
    output reg         dp,   // decimal point (active-high, off by default)
    output reg  [3:0]  an,   // digit enable (active-low)
    output reg  [3:0]  out   // debug LEDs
);

    // ===========================
    // Reset
    // ===========================
    wire reset = in[0];

    // ===========================
    // 1 Hz tick generator
    // ===========================
    // One "second" tick every CLK_FREQ cycles.
    localparam integer SEC_COUNT_MAX = CLK_FREQ - 1;

    reg [31:0] sec_counter;
    reg        one_sec_tick;

    always @(posedge clk) begin
        if (reset) begin
            sec_counter  <= 32'd0;
            one_sec_tick <= 1'b0;
        end else begin
            if (sec_counter == SEC_COUNT_MAX) begin
                sec_counter  <= 32'd0;
                one_sec_tick <= 1'b1;
            end else begin
                sec_counter  <= sec_counter + 1'b1;
                one_sec_tick <= 1'b0;
            end
        end
    end

    // ===========================
    // Position and effect FSM
    // ===========================
    // 4 digits: [3] [2] [1] [0] (3 = left-most)
    // "CE" occupies 2 adjacent digits.
    // Positions:
    //   pos = 0: "CE" at digits 3,2  (left)
    //   pos = 1: "CE" at digits 2,1
    //   pos = 2: "CE" at digits 1,0  (right)

    reg [1:0] pos;       // 0,1,2
    reg       dir;       // 0 = moving right, 1 = moving left (for bounce mode)

    // sw[0] = effect select
    //   0 -> Effect 1: scroll left -> right repeatedly
    //   1 -> Effect 2: bounce left <-> right
    wire effect_bounce = sw[0];

    always @(posedge clk) begin
        if (reset) begin
            pos <= 2'd0;     // start at left
            dir <= 1'b0;     // initial direction: right
        end else if (one_sec_tick) begin
            if (!effect_bounce) begin
                // Effect 1: scroll left -> right -> left -> right...
                if (pos == 2'd2)
                    pos <= 2'd0;
                else
                    pos <= pos + 2'd1;
                dir <= 1'b0; // dir not used in this mode
            end else begin
                // Effect 2: bounce between edges
                if (dir == 1'b0) begin
                    // moving right
                    if (pos == 2'd2) begin
                        dir <= 1'b1;        // change direction at right edge
                        pos <= 2'd1;
                    end else begin
                        pos <= pos + 2'd1;
                    end
                end else begin
                    // moving left
                    if (pos == 2'd0) begin
                        dir <= 1'b0;        // change direction at left edge
                        pos <= 2'd1;
                    end else begin
                        pos <= pos - 2'd1;
                    end
                end
            end
        end
    end

    // ===========================
    // On-board LEDs as indicators
    // ===========================
    always @* begin
        out[1:0] = pos;             // show position (0..2)
        out[2]   = effect_bounce;   // 0: scroll, 1: bounce
        out[3]   = 1'b0;            // unused
    end

    // ===========================
    // Character assignment to 4 digits
    // ===========================
    // char code:
    //   2'b00 -> blank
    //   2'b01 -> 'C'
    //   2'b10 -> 'E'

    reg [1:0] digit_char [3:0];  // [3] left-most, [0] right-most

    integer i;

    always @* begin
        // default all blank
        for (i = 0; i < 4; i = i + 1)
            digit_char[i] = 2'b00;

        // Place "CE" depending on pos
        case (pos)
            2'd0: begin
                digit_char[3] = 2'b01; // C
                digit_char[2] = 2'b10; // E
            end
            2'd1: begin
                digit_char[2] = 2'b01; // C
                digit_char[1] = 2'b10; // E
            end
            2'd2: begin
                digit_char[1] = 2'b01; // C
                digit_char[0] = 2'b10; // E
            end
            default: begin
                // all blank
            end
        endcase
    end

    // ===========================
    // 7-seg multiplexing
    // ===========================
    reg [15:0] refresh_counter;
    wire [1:0] refresh_sel = refresh_counter[15:14];
    reg [3:0] current_digit_code;  // 0=blank, 1=C, 2=E

    always @(posedge clk) begin
        if (reset) begin
            refresh_counter <= 16'd0;
        end else begin
            refresh_counter <= refresh_counter + 16'd1;
        end
    end

    always @* begin
        dp = 1'b0; // decimal point off (active-high, so 0 = off if wired differently adapt)

        case (refresh_sel)
            2'b00: begin
                an                 = 4'b1110;       // digit 0 (right-most)
                current_digit_code = {2'b00, digit_char[0]}; // use lower bits
            end
            2'b01: begin
                an                 = 4'b1101;       // digit 1
                current_digit_code = {2'b00, digit_char[1]};
            end
            2'b10: begin
                an                 = 4'b1011;       // digit 2
                current_digit_code = {2'b00, digit_char[2]};
            end
            2'b11: begin
                an                 = 4'b0111;       // digit 3 (left-most)
                current_digit_code = {2'b00, digit_char[3]};
            end
            default: begin
                an                 = 4'b1111;
                current_digit_code = 4'd0;
            end
        endcase
    end

    // ===========================
    // Decode character to 7-seg pattern
    // seg[6:0] = {a,b,c,d,e,f,g}, active-high
    // 'C' -> segments a, f, e, d
    // 'E' -> segments a, f, e, d, g
    // ===========================
    always @* begin
        case (current_digit_code[1:0])
            2'b00: seg = 7'b0000000; // blank
            2'b01: seg = 7'b1001110; // C
            2'b10: seg = 7'b1001111; // E
            default: seg = 7'b0000000;
        endcase
    end

endmodule
