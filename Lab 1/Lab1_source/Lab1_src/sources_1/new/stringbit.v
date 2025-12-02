`timescale 1ns / 1ps

// ======================================================
// Exercise 3: Change Mode String Bit LED Circuit
// - 4-bit default string (DEFAULT_STR)
// - BTN0: Reset to default string (Mode Reset)
// - BTN1: Circular Shift Left (every 1s)
// - BTN2: Circular Shift Right (every 1s)
// - BTN3: Pause (hold current string)
// - UART sends current LED pattern as "xxxx\n" every 1s
// ======================================================

module stringbit #(
    parameter integer CLK_FREQ    = 125_000_000,    // Arty Z7 system clock
    parameter integer BAUD        = 115200,         // UART baud rate
    parameter [3:0]   DEFAULT_STR = 4'b0011        // Default LED pattern
)(
    input  wire        clk,
    input  wire [3:0]  in,       // buttons: in[0]=reset mode, in[1]=L, in[2]=R, in[3]=pause
    output reg  [3:0]  out,      // LEDs
    output wire        uart_tx   // UART TX line to PC
);

    // ===========================
    // Mode encoding
    // ===========================
    localparam [1:0]
        MODE_RESET = 2'd0,
        MODE_LEFT  = 2'd1,
        MODE_RIGHT = 2'd2,
        MODE_PAUSE = 2'd3;

    reg [1:0] mode = MODE_RESET;
    reg [3:0] led_reg = DEFAULT_STR;

    // ===========================
    // 1 Hz tick generator (1 second)
    // ===========================
    localparam integer SEC_COUNT_MAX = CLK_FREQ - 1;
    reg [$clog2(SEC_COUNT_MAX+1)-1:0] sec_counter = 0;
    reg                               one_sec_tick = 1'b0;

    always @(posedge clk) begin
        if (in[0]) begin
            sec_counter  <= 0;
            one_sec_tick <= 1'b0;
        end else begin
            if (sec_counter == SEC_COUNT_MAX) begin
                sec_counter  <= 0;
                one_sec_tick <= 1'b1;
            end else begin
                sec_counter  <= sec_counter + 1'b1;
                one_sec_tick <= 1'b0;
            end
        end
    end

    // ===========================
    // Mode and LED register update
    // ===========================
    always @(posedge clk) begin
        if (in[0]) begin
            // Mode Reset: show default string
            mode    <= MODE_RESET;
            led_reg <= DEFAULT_STR;
        end else begin
            // Change mode based on buttons (priority: left > right > pause)
            if (in[1])
                mode <= MODE_LEFT;
            else if (in[2])
                mode <= MODE_RIGHT;
            else if (in[3])
                mode <= MODE_PAUSE;

            // On each second tick, perform action depending on mode
            if (one_sec_tick) begin
                case (mode)
                    MODE_RESET: begin
                        led_reg <= DEFAULT_STR;
                    end
                    MODE_LEFT: begin
                        // circular shift left: [3 2 1 0] -> [2 1 0 3]
                        led_reg <= {led_reg[2:0], led_reg[3]};
                    end
                    MODE_RIGHT: begin
                        // circular shift right: [3 2 1 0] -> [0 3 2 1]
                        led_reg <= {led_reg[0], led_reg[3:1]};
                    end
                    MODE_PAUSE: begin
                        led_reg <= led_reg; // hold
                    end
                    default: begin
                        led_reg <= DEFAULT_STR;
                    end
                endcase
            end
        end
    end

    // Drive LEDs
    always @* begin
        out = led_reg;
    end

    // ===========================
    // UART: send current LED string to PC every 1s
    // - Format: 4 ASCII chars '0'/'1' for bits [3:0], then '\n'
    // ===========================

    // UART transmitter instance
    wire       tx_busy;
    reg  [7:0] tx_data;
    reg        tx_start;

    uart_tx #(
        .CLK_FREQ(CLK_FREQ),
        .BAUD    (BAUD)
    ) uart_inst (
        .clk   (clk),
        .reset (in[0]),      // use BTN0 as UART reset too
        .data  (tx_data),
        .start (tx_start),
        .tx    (uart_tx),
        .busy  (tx_busy)
    );

    // Convert a single bit to ASCII '0' or '1'
    function [7:0] bit_to_ascii;
        input b;
        begin
            bit_to_ascii = b ? "1" : "0";
        end
    endfunction

    // Simple FSM to send 5 bytes: bit3, bit2, bit1, bit0, '\n'
    localparam [2:0]
        TX_IDLE  = 3'd0,
        TX_B3    = 3'd1,
        TX_B2    = 3'd2,
        TX_B1    = 3'd3,
        TX_B0    = 3'd4,
        TX_LF    = 3'd5;

    reg [2:0] tx_state = TX_IDLE;

    always @(posedge clk) begin
        if (in[0]) begin
            tx_state <= TX_IDLE;
            tx_start <= 1'b0;
            tx_data  <= 8'd0;
        end else begin
            tx_start <= 1'b0;  // default: no new byte

            case (tx_state)
                TX_IDLE: begin
                    // Start a new transmission every 1s when UART is free
                    if (one_sec_tick && !tx_busy) begin
                        tx_data  <= bit_to_ascii(led_reg[3]);
                        tx_start <= 1'b1;
                        tx_state <= TX_B3;
                    end
                end

                TX_B3: begin
                    if (!tx_busy) begin
                        tx_data  <= bit_to_ascii(led_reg[2]);
                        tx_start <= 1'b1;
                        tx_state <= TX_B2;
                    end
                end

                TX_B2: begin
                    if (!tx_busy) begin
                        tx_data  <= bit_to_ascii(led_reg[1]);
                        tx_start <= 1'b1;
                        tx_state <= TX_B1;
                    end
                end

                TX_B1: begin
                    if (!tx_busy) begin
                        tx_data  <= bit_to_ascii(led_reg[0]);
                        tx_start <= 1'b1;
                        tx_state <= TX_B0;
                    end
                end

                TX_B0: begin
                    if (!tx_busy) begin
                        tx_data  <= 8'h0A; // '\n'
                        tx_start <= 1'b1;
                        tx_state <= TX_LF;
                    end
                end

                TX_LF: begin
                    if (!tx_busy) begin
                        tx_state <= TX_IDLE;
                    end
                end

                default: begin
                    tx_state <= TX_IDLE;
                end
            endcase
        end
    end

endmodule



// ======================================================
// Simple UART Transmitter (8N1)
// ======================================================
module uart_tx #(
    parameter integer CLK_FREQ = 125_000_000,
    parameter integer BAUD     = 115200
)(
    input  wire       clk,
    input  wire       reset,
    input  wire [7:0] data,
    input  wire       start,
    output reg        tx,
    output reg        busy
);
    localparam integer BAUD_DIV = CLK_FREQ / BAUD;

    reg [$clog2(BAUD_DIV)-1:0] baud_cnt = 0;
    reg [3:0]                  bit_idx  = 0;
    reg [9:0]                  shifter  = 10'b1111111111; // start + 8 data + stop

    always @(posedge clk) begin
        if (reset) begin
            tx      <= 1'b1;          // idle high
            busy    <= 1'b0;
            baud_cnt <= 0;
            bit_idx <= 0;
            shifter <= 10'b1111111111;
        end else begin
            if (!busy) begin
                tx <= 1'b1; // idle
                if (start) begin
                    // Frame: start(0) + data(LSB first) + stop(1)
                    shifter <= {1'b1, data, 1'b0};
                    busy    <= 1'b1;
                    baud_cnt <= 0;
                    bit_idx <= 0;
                end
            end else begin
                // Sending bits at baud rate
                if (baud_cnt == BAUD_DIV - 1) begin
                    baud_cnt <= 0;
                    tx       <= shifter[0];               // output LSB
                    shifter  <= {1'b1, shifter[9:1]};     // shift right, keep MSB at 1 (idle)
                    if (bit_idx == 4'd9) begin
                        busy <= 1'b0;                     // finished 10 bits
                    end else begin
                        bit_idx <= bit_idx + 1'b1;
                    end
                end else begin
                    baud_cnt <= baud_cnt + 1'b1;
                end
            end
        end
    end

endmodule
