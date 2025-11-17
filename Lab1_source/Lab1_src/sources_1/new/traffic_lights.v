`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 11/14/2025 03:00:35 PM 
// Design Name: 
// Module Name: traffic_lights
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

module traffic_lights #(
    // Clock frequency of Arty Z7-20: 125 MHz
    parameter integer CLK_FREQ    = 125_000_000,
    // Base green time (seconds)
    parameter integer GREEN_TIME  = 10,
    // Yellow time (seconds)
    parameter integer YELLOW_TIME = 3
)(
    input  wire        clk,
    input  wire [1:0]  sw,   // timing configuration
    input  wire [3:0]  in,   // buttons (in[0] = reset)

    // RGB LEDs for pole 1 (main road)
    output reg         led4_r,
    output reg         led4_g,
    output reg         led4_b,

    // RGB LEDs for pole 2 (side road)
    output reg         led5_r,
    output reg         led5_g,
    output reg         led5_b,

    // On-board LEDs as debug
    output reg  [3:0]  out,

    // 7-seg segments (a..g)
    output reg  [6:0]  seg,
    // decimal point
    output reg         dp,
    // digit enable (active-low assumed)
    output reg  [3:0]  an
);

    // ===========================
    // Reset
    // ===========================
    wire reset = in[0];

    // ===========================
    // 1 Hz "seconds" tick generator
    // ===========================
    localparam integer SEC_COUNT_MAX = CLK_FREQ - 1;
    reg [26:0] sec_counter = 27'd0; // 27 bits enough for 125M
    reg        one_sec_tick = 1'b0;

    always @(posedge clk) begin
        if (reset) begin
            sec_counter  <= 27'd0;
            one_sec_tick <= 1'b0;
        end else begin
            if (sec_counter == SEC_COUNT_MAX[26:0]) begin
                sec_counter  <= 27'd0;
                one_sec_tick <= 1'b1;
            end else begin
                sec_counter  <= sec_counter + 1'b1;
                one_sec_tick <= 1'b0;
            end
        end
    end

    // ===========================
    // Traffic light state machine
    // ===========================

    // States:
    // 0: Main Green  / Side Red
    // 1: Main Yellow / Side Red
    // 2: Main Red    / Side Green
    // 3: Main Red    / Side Yellow
    localparam [1:0]
        S_MAIN_GREEN  = 2'd0,
        S_MAIN_YELLOW = 2'd1,
        S_SIDE_GREEN  = 2'd2,
        S_SIDE_YELLOW = 2'd3;

    reg [1:0] state = S_MAIN_GREEN;

    // Configure green time with switches: GREEN_TIME + sw (0..3)
    wire [6:0] green_time_cfg  = GREEN_TIME[6:0] + {5'd0, sw};
    wire [6:0] yellow_time_cfg = YELLOW_TIME[6:0];

    // Remaining time in the current phase (seconds), max 99
    reg [6:0] time_left = 7'd0;

    // Initialize / update state and timer
    always @(posedge clk) begin
        if (reset) begin
            state     <= S_MAIN_GREEN;
            time_left <= green_time_cfg;
        end else if (one_sec_tick) begin
            if (time_left != 0) begin
                time_left <= time_left - 1'b1;
            end else begin
                // Time for next phase
                case (state)
                    S_MAIN_GREEN: begin
                        state     <= S_MAIN_YELLOW;
                        time_left <= yellow_time_cfg;
                    end
                    S_MAIN_YELLOW: begin
                        state     <= S_SIDE_GREEN;
                        time_left <= green_time_cfg;
                    end
                    S_SIDE_GREEN: begin
                        state     <= S_SIDE_YELLOW;
                        time_left <= yellow_time_cfg;
                    end
                    S_SIDE_YELLOW: begin
                        state     <= S_MAIN_GREEN;
                        time_left <= green_time_cfg;
                    end
                    default: begin
                        state     <= S_MAIN_GREEN;
                        time_left <= green_time_cfg;
                    end
                endcase
            end
        end
    end

    // ===========================
    // Drive RGB LEDs
    // ===========================
    // Red   = *_r
    // Green = *_g
    // Yellow= *_b

    always @* begin
        // default all off
        led4_r = 1'b0;
        led4_g = 1'b0;
        led4_b = 1'b0;

        led5_r = 1'b0;
        led5_g = 1'b0;
        led5_b = 1'b0;

        case (state)
            // Main Green / Side Red
            S_MAIN_GREEN: begin
                led4_g = 1'b1; // main green
                led5_r = 1'b1; // side red
            end

            // Main Yellow / Side Red
            S_MAIN_YELLOW: begin
                led4_b = 1'b1; // main yellow (blue LED)
                led5_r = 1'b1; // side red
            end

            // Main Red / Side Green
            S_SIDE_GREEN: begin
                led4_r = 1'b1; // main red
                led5_g = 1'b1; // side green
            end

            // Main Red / Side Yellow
            S_SIDE_YELLOW: begin
                led4_r = 1'b1; // main red
                led5_b = 1'b1; // side yellow (blue LED)
            end

            default: begin
                led4_r = 1'b1;
                led5_r = 1'b1;
            end
        endcase
    end

    // ===========================
    // Debug LEDs
    // ===========================
    // out[1:0] = state; out[3:2] = 0
    always @* begin
        out        = 4'b0000;
        out[1:0]   = state;
    end

    // ===========================
    // 7-Segment display logic
    // ===========================
    // 4-digit multiplexed display
    // - If main road is active (states 0/1) → show time_left on digits 3:2
    // - If side road is active (states 2/3) → show time_left on digits 1:0
    // Segments active-high, an[] active-low

    // Refresh counter for multiplexing
    reg [15:0] refresh_counter = 16'd0;
    wire [1:0] refresh_sel = refresh_counter[15:14]; // choose digit

    always @(posedge clk) begin
        if (reset) begin
            refresh_counter <= 16'd0;
        end else begin
            refresh_counter <= refresh_counter + 1'b1;
        end
    end

    // Split time_left into tens and ones (0-99)
    reg [3:0] tens;
    reg [3:0] ones;

    always @* begin
        // simple division/modulo by 10
        tens = (time_left / 10) % 10;
        ones = time_left % 10;
    end

    // Assign BCD digits to physical positions
    reg [3:0] digit0, digit1, digit2, digit3;
    reg [3:0] current_digit;

    always @* begin
        // default all zeros
        digit0 = 4'd0;
        digit1 = 4'd0;
        digit2 = 4'd0;
        digit3 = 4'd0;

        if (state == S_MAIN_GREEN || state == S_MAIN_YELLOW) begin
            // display on left side: digits 3:2
            digit3 = tens;
            digit2 = ones;
        end else begin
            // side road active → display on right side: digits 1:0
            digit1 = tens;
            digit0 = ones;
        end
    end

    // Digit enable + decimal point + current_digit selection
    always @* begin
        dp = 1'b1; // decimal point off

        case (refresh_sel)
            2'b00: begin
                an           = 4'b1110; // digit 0 active (right-most)
                current_digit = digit0;
            end
            2'b01: begin
                an           = 4'b1101; // digit 1
                current_digit = digit1;
            end
            2'b10: begin
                an           = 4'b1011; // digit 2
                current_digit = digit2;
            end
            2'b11: begin
                an           = 4'b0111; // digit 3 (left-most)
                current_digit = digit3;
            end
            default: begin
                an           = 4'b1111;
                current_digit = 4'd0;
            end
        endcase
    end

    // BCD to 7-seg decoder (segments a..g, active-high)
    function [6:0] seg_decode;
        input [3:0] value;
        begin
            case (value)
                4'd0: seg_decode = 7'b1111110; // 0
                4'd1: seg_decode = 7'b0110000; // 1
                4'd2: seg_decode = 7'b1101101; // 2
                4'd3: seg_decode = 7'b1111001; // 3
                4'd4: seg_decode = 7'b0110011; // 4
                4'd5: seg_decode = 7'b1011011; // 5
                4'd6: seg_decode = 7'b1011111; // 6
                4'd7: seg_decode = 7'b1110000; // 7
                4'd8: seg_decode = 7'b1111111; // 8
                4'd9: seg_decode = 7'b1111011; // 9
                default: seg_decode = 7'b0000001; // dash or blank
            endcase
        end
    endfunction

    always @* begin
        seg = seg_decode(current_digit);
    end

endmodule

