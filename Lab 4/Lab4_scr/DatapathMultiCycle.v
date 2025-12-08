/* INSERT NAME AND PENNKEY HERE */

`timescale 1ns / 1ns

// ---------------------------------------------------------------------------
// Global defines
// ---------------------------------------------------------------------------

// registers are 32 bits in RV32
`define REG_SIZE   31

// RV opcodes are 7 bits
`define OPCODE_SIZE 6

// Don't forget your CLA and Divider
`include "cla.v"
`include "DividerUnsignedPipelined.v"

// ---------------------------------------------------------------------------
// Register File
// ---------------------------------------------------------------------------
// - 32 registers (x0..x31), each 32-bit
// - x0 is hard-wired to 0 (writes to x0 are ignored)
// - Asynchronous read, synchronous write
// ---------------------------------------------------------------------------
module RegFile (
  input      [        4:0] rd,        // destination register index
  input      [`REG_SIZE:0] rd_data,   // data to write
  input      [        4:0] rs1,       // source register 1 index
  output reg [`REG_SIZE:0] rs1_data,  // data read from rs1
  input      [        4:0] rs2,       // source register 2 index
  output reg [`REG_SIZE:0] rs2_data,  // data read from rs2
  input                    clk,
  input                    we,        // write enable
  input                    rst
);

  // TODO: copy your homework #3 code here
  localparam NumRegs = 32;
  reg [`REG_SIZE:0] regs[0:NumRegs-1];

  // TODO: your code here

  integer i;

  // Synchronous write, synchronous reset
  always @(posedge clk or posedge rst) begin
    if (rst) begin
      // Clear all registers on reset
      for (i = 0; i < NumRegs; i = i + 1) begin
        regs[i] <= 32'd0;
      end
    end
    // Write-back: ignore writes to x0 (rd != 0)
    else if (we && rd != 5'd0) begin
      regs[rd] <= rd_data;
    end
  end

  // Asynchronous read: x0 is always zero
  always @(*) begin
    rs1_data = (rs1 == 5'd0) ? 32'd0 : regs[rs1];
    rs2_data = (rs2 == 5'd0) ? 32'd0 : regs[rs2];
  end

endmodule

// ---------------------------------------------------------------------------
// DatapathMultiCycle
// ---------------------------------------------------------------------------
// - Multi-cycle RISC-V RV32I/M datapath
// - Uses single CLA for ALU operations
// - Uses an 8-stage pipelined divider for DIV/REM instructions
// - Handles instruction decode, PC update, load/store, branches, jumps
// ---------------------------------------------------------------------------
module DatapathMultiCycle (
    input                    clk,
    input                    rst,
    output reg               halt,
    output     [`REG_SIZE:0] pc_to_imem,
    input      [`REG_SIZE:0] inst_from_imem,

    // addr_to_dmem is a read-write port
    output reg [`REG_SIZE:0] addr_to_dmem,
    input      [`REG_SIZE:0] load_data_from_dmem,
    output reg [`REG_SIZE:0] store_data_to_dmem,
    output reg [        3:0] store_we_to_dmem
);

  // TODO: your code here (largely based on homework #3)

  // -------------------------------------------------------------------------
  // Instruction fields
  // -------------------------------------------------------------------------
  wire [           6:0] inst_funct7;
  wire [           4:0] inst_rs2;
  wire [           4:0] inst_rs1;
  wire [           2:0] inst_funct3;
  wire [           4:0] inst_rd;
  wire [`OPCODE_SIZE:0] inst_opcode;

  // Split R-type instruction - see section 2.2 of RISC-V spec
  assign {inst_funct7, inst_rs2, inst_rs1, inst_funct3, inst_rd, inst_opcode} = inst_from_imem;

  // -------------------------------------------------------------------------
  // Immediate fields for I, S, B, J types
  // -------------------------------------------------------------------------

  // I-type: short immediates and loads
  wire [11:0] imm_i;
  assign imm_i = inst_from_imem[31:20];
  wire [ 4:0] imm_shamt = inst_from_imem[24:20];

  // S-type: stores
  wire [11:0] imm_s;
  assign imm_s = {inst_funct7, inst_rd};

  // B-type: conditional branches
  wire [12:0] imm_b;
  assign {imm_b[12], imm_b[10:1], imm_b[11], imm_b[0]} = {inst_funct7, inst_rd, 1'b0};

  // J-type: JAL (unconditional jumps)
  wire [20:0] imm_j;
  assign {imm_j[20], imm_j[10:1], imm_j[11], imm_j[19:12], imm_j[0]} = {inst_from_imem[31:12], 1'b0};

  // Sign-extended immediates
  wire [`REG_SIZE:0] imm_i_sext = {{20{imm_i[11]}}, imm_i[11:0]};
  wire [`REG_SIZE:0] imm_s_sext = {{20{imm_s[11]}}, imm_s[11:0]};
  wire [`REG_SIZE:0] imm_b_sext = {{19{imm_b[12]}}, imm_b[12:0]};
  wire [`REG_SIZE:0] imm_j_sext = {{11{imm_j[20]}}, imm_j[20:0]};

  // -------------------------------------------------------------------------
  // Opcodes - see section 19 of RISC-V spec
  // -------------------------------------------------------------------------
  localparam [`OPCODE_SIZE:0] OpLoad    = 7'b00_000_11;
  localparam [`OPCODE_SIZE:0] OpStore   = 7'b01_000_11;
  localparam [`OPCODE_SIZE:0] OpBranch  = 7'b11_000_11;
  localparam [`OPCODE_SIZE:0] OpJalr    = 7'b11_001_11;
  localparam [`OPCODE_SIZE:0] OpMiscMem = 7'b00_011_11;
  localparam [`OPCODE_SIZE:0] OpJal     = 7'b11_011_11;

  localparam [`OPCODE_SIZE:0] OpRegImm  = 7'b00_100_11;
  localparam [`OPCODE_SIZE:0] OpRegReg  = 7'b01_100_11;
  localparam [`OPCODE_SIZE:0] OpEnviron = 7'b11_100_11;

  localparam [`OPCODE_SIZE:0] OpAuipc   = 7'b00_101_11;
  localparam [`OPCODE_SIZE:0] OpLui     = 7'b01_101_11;

  // -------------------------------------------------------------------------
  // Instruction decode (one-hot-ish wires)
  // -------------------------------------------------------------------------
  wire inst_lui    = (inst_opcode == OpLui    );
  wire inst_auipc  = (inst_opcode == OpAuipc  );
  wire inst_jal    = (inst_opcode == OpJal    );
  wire inst_jalr   = (inst_opcode == OpJalr   );

  wire inst_beq    = (inst_opcode == OpBranch ) & (inst_from_imem[14:12] == 3'b000);
  wire inst_bne    = (inst_opcode == OpBranch ) & (inst_from_imem[14:12] == 3'b001);
  wire inst_blt    = (inst_opcode == OpBranch ) & (inst_from_imem[14:12] == 3'b100);
  wire inst_bge    = (inst_opcode == OpBranch ) & (inst_from_imem[14:12] == 3'b101);
  wire inst_bltu   = (inst_opcode == OpBranch ) & (inst_from_imem[14:12] == 3'b110);
  wire inst_bgeu   = (inst_opcode == OpBranch ) & (inst_from_imem[14:12] == 3'b111);

  wire inst_lb     = (inst_opcode == OpLoad   ) & (inst_from_imem[14:12] == 3'b000);
  wire inst_lh     = (inst_opcode == OpLoad   ) & (inst_from_imem[14:12] == 3'b001);
  wire inst_lw     = (inst_opcode == OpLoad   ) & (inst_from_imem[14:12] == 3'b010);
  wire inst_lbu    = (inst_opcode == OpLoad   ) & (inst_from_imem[14:12] == 3'b100);
  wire inst_lhu    = (inst_opcode == OpLoad   ) & (inst_from_imem[14:12] == 3'b101);

  wire inst_sb     = (inst_opcode == OpStore  ) & (inst_from_imem[14:12] == 3'b000);
  wire inst_sh     = (inst_opcode == OpStore  ) & (inst_from_imem[14:12] == 3'b001);
  wire inst_sw     = (inst_opcode == OpStore  ) & (inst_from_imem[14:12] == 3'b010);

  wire inst_addi   = (inst_opcode == OpRegImm ) & (inst_from_imem[14:12] == 3'b000);
  wire inst_slti   = (inst_opcode == OpRegImm ) & (inst_from_imem[14:12] == 3'b010);
  wire inst_sltiu  = (inst_opcode == OpRegImm ) & (inst_from_imem[14:12] == 3'b011);
  wire inst_xori   = (inst_opcode == OpRegImm ) & (inst_from_imem[14:12] == 3'b100);
  wire inst_ori    = (inst_opcode == OpRegImm ) & (inst_from_imem[14:12] == 3'b110);
  wire inst_andi   = (inst_opcode == OpRegImm ) & (inst_from_imem[14:12] == 3'b111);

  wire inst_slli   = (inst_opcode == OpRegImm ) & (inst_from_imem[14:12] == 3'b001) & (inst_from_imem[31:25] == 7'd0      );
  wire inst_srli   = (inst_opcode == OpRegImm ) & (inst_from_imem[14:12] == 3'b101) & (inst_from_imem[31:25] == 7'd0      );
  wire inst_srai   = (inst_opcode == OpRegImm ) & (inst_from_imem[14:12] == 3'b101) & (inst_from_imem[31:25] == 7'b0100000);

  wire inst_add    = (inst_opcode == OpRegReg ) & (inst_from_imem[14:12] == 3'b000) & (inst_from_imem[31:25] == 7'd0      );
  wire inst_sub    = (inst_opcode == OpRegReg ) & (inst_from_imem[14:12] == 3'b000) & (inst_from_imem[31:25] == 7'b0100000);
  wire inst_sll    = (inst_opcode == OpRegReg ) & (inst_from_imem[14:12] == 3'b001) & (inst_from_imem[31:25] == 7'd0      );
  wire inst_slt    = (inst_opcode == OpRegReg ) & (inst_from_imem[14:12] == 3'b010) & (inst_from_imem[31:25] == 7'd0      );
  wire inst_sltu   = (inst_opcode == OpRegReg ) & (inst_from_imem[14:12] == 3'b011) & (inst_from_imem[31:25] == 7'd0      );
  wire inst_xor    = (inst_opcode == OpRegReg ) & (inst_from_imem[14:12] == 3'b100) & (inst_from_imem[31:25] == 7'd0      );
  wire inst_srl    = (inst_opcode == OpRegReg ) & (inst_from_imem[14:12] == 3'b101) & (inst_from_imem[31:25] == 7'd0      );
  wire inst_sra    = (inst_opcode == OpRegReg ) & (inst_from_imem[14:12] == 3'b101) & (inst_from_imem[31:25] == 7'b0100000);
  wire inst_or     = (inst_opcode == OpRegReg ) & (inst_from_imem[14:12] == 3'b110) & (inst_from_imem[31:25] == 7'd0      );
  wire inst_and    = (inst_opcode == OpRegReg ) & (inst_from_imem[14:12] == 3'b111) & (inst_from_imem[31:25] == 7'd0      );

  // M-extension instructions (MUL/DIV/REM)
  wire inst_mul    = (inst_opcode == OpRegReg ) & (inst_from_imem[31:25] == 7'd1  ) & (inst_from_imem[14:12] == 3'b000    );
  wire inst_mulh   = (inst_opcode == OpRegReg ) & (inst_from_imem[31:25] == 7'd1  ) & (inst_from_imem[14:12] == 3'b001    );
  wire inst_mulhsu = (inst_opcode == OpRegReg ) & (inst_from_imem[31:25] == 7'd1  ) & (inst_from_imem[14:12] == 3'b010    );
  wire inst_mulhu  = (inst_opcode == OpRegReg ) & (inst_from_imem[31:25] == 7'd1  ) & (inst_from_imem[14:12] == 3'b011    );
  wire inst_div    = (inst_opcode == OpRegReg ) & (inst_from_imem[31:25] == 7'd1  ) & (inst_from_imem[14:12] == 3'b100    );
  wire inst_divu   = (inst_opcode == OpRegReg ) & (inst_from_imem[31:25] == 7'd1  ) & (inst_from_imem[14:12] == 3'b101    );
  wire inst_rem    = (inst_opcode == OpRegReg ) & (inst_from_imem[31:25] == 7'd1  ) & (inst_from_imem[14:12] == 3'b110    );
  wire inst_remu   = (inst_opcode == OpRegReg ) & (inst_from_imem[31:25] == 7'd1  ) & (inst_from_imem[14:12] == 3'b111    );

  wire inst_ecall  = (inst_opcode == OpEnviron) & (inst_from_imem[31:7] == 25'd0  );
  wire inst_fence  = (inst_opcode == OpMiscMem);

  // -------------------------------------------------------------------------
  // Program counter
  // -------------------------------------------------------------------------
  reg [`REG_SIZE:0] pcNext, pcCurrent;

  always @(posedge clk) begin
    if (rst) begin
      pcCurrent <= 32'd0;
    end else begin
      pcCurrent <= pcNext;
    end
  end

  assign pc_to_imem = pcCurrent;

  // -------------------------------------------------------------------------
  // Cycle and instruction counters
  // -------------------------------------------------------------------------
  reg [`REG_SIZE:0] cycles_current, num_inst_current;

  always @(posedge clk) begin
    if (rst) begin
      cycles_current   <= 32'd0;
      num_inst_current <= 32'd0;
    end else begin
      cycles_current   <= cycles_current + 1;
      // increment instruction count every cycle (simple model)
      if (!rst) begin
        num_inst_current <= num_inst_current + 1;
      end
    end
  end

  // -------------------------------------------------------------------------
  // Register file and main ALU
  // -------------------------------------------------------------------------

  // NOTE: don't rename your RegFile instance as the tests expect it to be `rf`
  // TODO: you will need to edit the port connections, however.
  wire [19:0] lui_imm = inst_from_imem[31:12];
  reg         reg_write;
  reg [31:0]  reg_write_data;

  wire [`REG_SIZE:0] rs1_data;
  wire [`REG_SIZE:0] rs2_data;

  RegFile rf (
    .clk      (clk),
    .rst      (rst),
    .we       (reg_write),
    .rd       (inst_rd),
    .rd_data  (reg_write_data),
    .rs1      (inst_rs1),
    .rs2      (inst_rs2),
    .rs1_data (rs1_data),
    .rs2_data (rs2_data)
  );

  // ========================================================================
  // CLA-based ALU
  // ========================================================================
  // CLA can be used for all + / - operations and address calculations
  // ========================================================================
  wire [31:0] alu_a = rs1_data;
  reg  [31:0] alu_b;
  reg         alu_cin;
  wire [31:0] alu_result;

  cla cla_main (
    .a   (alu_a),
    .b   (alu_b),
    .cin (alu_cin),
    .sum (alu_result)
  );

  // ========================================================================
  // Divider (M extension)
  // ========================================================================

  // Determine whether this is a signed division/remainder instruction
  wire is_div_signed = inst_div || inst_rem;

  // Take absolute values if signed div/rem and operands are negative
  wire [31:0] div_dividend_abs;
  wire [31:0] div_divisor_abs;

  // If signed div/rem and operand is negative (bit 31 = 1), take two's complement (~x + 1)
  assign div_dividend_abs = (is_div_signed && rs1_data[31]) ? (~rs1_data + 1) : rs1_data;
  assign div_divisor_abs  = (is_div_signed && rs2_data[31]) ? (~rs2_data + 1) : rs2_data;

  // Raw (unsigned) outputs from divider
  wire [31:0] div_quotient_raw;
  wire [31:0] div_remainder_raw;

  wire [31:0] div_quotient;   // not used directly (kept for clarity)
  wire [31:0] div_remainder;  // not used directly (kept for clarity)

  // Pipelined unsigned divider
  DividerUnsignedPipelined div_inst (
    .clk        (clk),
    .rst        (rst),
    .stall      (1'b0),               // allow divider to run freely
    .i_dividend (div_dividend_abs),
    .i_divisor  (div_divisor_abs),
    .o_quotient (div_quotient_raw),
    .o_remainder(div_remainder_raw)
  );

  // Handle sign correction for the divider outputs
  reg [31:0] div_quotient_final;
  reg [31:0] div_remainder_final;

  always @(*) begin
    div_quotient_final  = div_quotient_raw;
    div_remainder_final = div_remainder_raw;

    if (is_div_signed) begin
      if (rs2_data == 0) begin
        // Division by zero for signed div: quotient = -1, remainder = dividend
        div_quotient_final  = 32'hFFFFFFFF;
        div_remainder_final = rs1_data;
      end else begin
        // Normal signed division:
        // If signs differ and quotient is non-zero, negate quotient
        if ((rs1_data[31] ^ rs2_data[31]) && div_quotient_raw != 0) begin
          div_quotient_final = ~div_quotient_raw + 1;
        end
        // If dividend was negative and remainder is non-zero, negate remainder
        if (rs1_data[31] && div_remainder_raw != 0) begin
          div_remainder_final = ~div_remainder_raw + 1;
        end
      end
    end
  end

  // -------------------------------------------------------------------------
  // Multi-cycle division control
  // -------------------------------------------------------------------------
  reg        div_busy;     // 1 = divider pipeline is in use
  reg  [2:0] div_counter;  // counts divider latency (0..7)

  wire       is_div_op    = inst_div || inst_divu || inst_rem || inst_remu;
  wire       div_start    = is_div_op && !div_busy;
  wire       div_done     = div_busy && (div_counter == 3'd7);
  wire       should_stall = is_div_op && !div_done;

  // Count 8 cycles of divider latency
  always @(posedge clk or posedge rst) begin
    if (rst) begin
      div_busy    <= 1'b0;
      div_counter <= 3'd0;
    end else begin
      if (div_start) begin
        div_busy    <= 1'b1;
        div_counter <= 3'd0;
      end else if (div_busy) begin
        if (div_done) begin
          div_busy    <= 1'b0;
          div_counter <= 3'd0;
        end else begin
          div_counter <= div_counter + 3'd1;
        end
      end
    end
  end

  // ========================================================================
  // Main control logic
  // ========================================================================
  reg illegal_inst;

  always @(*) begin
    // Default values for control signals
    illegal_inst        = 1'b0;
    pcNext              = pcCurrent + 4;
    reg_write           = 1'b0;
    reg_write_data      = 32'd0;
    halt                = 1'b0;
    illegal_inst        = 1'b0;
    addr_to_dmem        = 32'd0;
    store_data_to_dmem  = 32'd0;
    store_we_to_dmem    = 4'b0000;

    alu_b               = rs2_data;
    alu_cin             = 1'b0;

    // Select ALU operand B based on instruction type
    if (inst_opcode == OpStore) begin
      alu_b = imm_s_sext;
    end
    if (inst_addi || (inst_opcode == OpLoad) || inst_jalr || inst_auipc) begin
      alu_b = imm_i_sext;
    end
    if (inst_sub) begin
      // Subtraction via two's complement
      alu_b   = ~rs2_data + 32'd1;
      alu_cin = 1'b0;
    end

    // ======================================================================
    // Opcode decode and control
    // ======================================================================
    case (inst_opcode)
      // --------------------------------------------------------------------
      // LUI: Load Upper Immediate
      // rd = imm << 12
      // --------------------------------------------------------------------
      OpLui: begin
        reg_write      = 1'b1;
        reg_write_data = {lui_imm, 12'd0};
      end

      // --------------------------------------------------------------------
      // AUIPC: Add Upper Immediate to PC
      // rd = PC + imm << 12
      // --------------------------------------------------------------------
      OpAuipc: begin
        reg_write      = 1'b1;
        reg_write_data = pcCurrent + {inst_from_imem[31:12], 12'd0};
      end

      // --------------------------------------------------------------------
      // JAL: Jump and Link
      // rd = PC + 4; PC = PC + imm_j
      // --------------------------------------------------------------------
      OpJal: begin
        reg_write      = 1'b1;
        reg_write_data = pcCurrent + 32'd4;
        pcNext         = pcCurrent + imm_j_sext;
      end

      // --------------------------------------------------------------------
      // JALR: Jump and Link Register
      // rd = PC + 4; PC = (rs1 + imm_i) & ~1
      // --------------------------------------------------------------------
      OpJalr: begin
        reg_write      = 1'b1;
        reg_write_data = pcCurrent + 32'd4;
        // Clear LSB
        pcNext         = alu_result & ~32'd1;
      end

      // --------------------------------------------------------------------
      // Branches
      // --------------------------------------------------------------------
      OpBranch: begin
        if (inst_beq && (rs1_data == rs2_data)) begin
          pcNext = pcCurrent + imm_b_sext;
        end
        else if (inst_bne && (rs1_data != rs2_data)) begin
          pcNext = pcCurrent + imm_b_sext;
        end
        else if (inst_blt && ($signed(rs1_data) < $signed(rs2_data))) begin
          pcNext = pcCurrent + imm_b_sext;
        end
        else if (inst_bge && ($signed(rs1_data) >= $signed(rs2_data))) begin
          pcNext = pcCurrent + imm_b_sext;
        end
        else if (inst_bltu && (rs1_data < rs2_data)) begin
          pcNext = pcCurrent + imm_b_sext;
        end
        else if (inst_bgeu && (rs1_data >= rs2_data)) begin
          pcNext = pcCurrent + imm_b_sext;
        end
      end

      // --------------------------------------------------------------------
      // Loads
      // --------------------------------------------------------------------
      OpLoad: begin
        addr_to_dmem = alu_result;
        reg_write    = 1'b1;

        // Fix load alignment here: use low bits of address to choose byte/halfword
        case (inst_funct3)
          3'b000: begin // LB
            case (alu_result[1:0])
              2'b00: reg_write_data = {{24{load_data_from_dmem[7]}},  load_data_from_dmem[7:0]};
              2'b01: reg_write_data = {{24{load_data_from_dmem[15]}}, load_data_from_dmem[15:8]};
              2'b10: reg_write_data = {{24{load_data_from_dmem[23]}}, load_data_from_dmem[23:16]};
              2'b11: reg_write_data = {{24{load_data_from_dmem[31]}}, load_data_from_dmem[31:24]};
            endcase
          end

          3'b001: begin // LH
            case (alu_result[1])
              1'b0: reg_write_data = {{16{load_data_from_dmem[15]}}, load_data_from_dmem[15:0]};
              1'b1: reg_write_data = {{16{load_data_from_dmem[31]}}, load_data_from_dmem[31:16]};
            endcase
          end

          3'b010: begin // LW
            reg_write_data = load_data_from_dmem;
          end

          3'b100: begin // LBU
            case (alu_result[1:0])
              2'b00: reg_write_data = {24'd0, load_data_from_dmem[7:0]};
              2'b01: reg_write_data = {24'd0, load_data_from_dmem[15:8]};
              2'b10: reg_write_data = {24'd0, load_data_from_dmem[23:16]};
              2'b11: reg_write_data = {24'd0, load_data_from_dmem[31:24]};
            endcase
          end

          3'b101: begin // LHU
            case (alu_result[1])
              1'b0: reg_write_data = {16'd0, load_data_from_dmem[15:0]};
              1'b1: reg_write_data = {16'd0, load_data_from_dmem[31:16]};
            endcase
          end

          default: begin
            reg_write = 1'b0;
          end
        endcase
      end

      // --------------------------------------------------------------------
      // Stores
      // --------------------------------------------------------------------
      OpStore: begin
        addr_to_dmem       = alu_result;
        store_data_to_dmem = rs2_data << (alu_result[1:0] * 8);

        if (inst_sw) begin
          store_we_to_dmem = 4'b1111;
        end
        else if (inst_sb) begin
          store_we_to_dmem = 4'b0001 << alu_result[1:0];
        end
        else if (inst_sh) begin
          store_we_to_dmem = (alu_result[1] == 1'b0) ? 4'b0011 : 4'b1100;
        end
        else begin
          store_we_to_dmem = 4'b0000;
          illegal_inst     = 1'b1;
        end
      end

      // --------------------------------------------------------------------
      // Register-immediate operations
      // --------------------------------------------------------------------
      OpRegImm: begin
        reg_write = 1'b1;

        if (inst_addi) begin
          // ADDI: use CLA result = rs1 + imm_i_sext
          reg_write_data = alu_result;
        end
        else if (inst_slti) begin
          reg_write_data = ($signed(rs1_data) < $signed(imm_i_sext)) ? 32'd1 : 32'd0;
        end
        else if (inst_sltiu) begin
          reg_write_data = (rs1_data < imm_i_sext) ? 32'd1 : 32'd0;
        end
        else if (inst_xori) begin
          reg_write_data = rs1_data ^ imm_i_sext;
        end
        else if (inst_ori) begin
          reg_write_data = rs1_data | imm_i_sext;
        end
        else if (inst_andi) begin
          reg_write_data = rs1_data & imm_i_sext;
        end
        else if (inst_slli) begin
          // Shift amount uses lower 5 bits
          reg_write_data = rs1_data << imm_i[4:0];
        end
        else if (inst_srli) begin
          reg_write_data = rs1_data >> imm_i[4:0];
        end
        else if (inst_srai) begin
          reg_write_data = $signed(rs1_data) >>> imm_i[4:0]; // arithmetic right shift
        end
        else begin
          reg_write    = 1'b0;
          illegal_inst = 1'b1;
        end
      end

      // --------------------------------------------------------------------
      // Register-register operations
      // --------------------------------------------------------------------
      OpRegReg: begin
        reg_write = 1'b1;

        if (inst_add || inst_sub) begin
          // Use CLA result = rs1 (+/-) rs2
          reg_write_data = alu_result;
        end
        else if (inst_slt) begin
          reg_write_data = ($signed(rs1_data) < $signed(rs2_data)) ? 32'd1 : 32'd0;
        end
        else if (inst_sltu) begin
          reg_write_data = (rs1_data < rs2_data) ? 32'd1 : 32'd0;
        end
        else if (inst_xor) begin
          reg_write_data = rs1_data ^ rs2_data;
        end
        else if (inst_or) begin
          reg_write_data = rs1_data | rs2_data;
        end
        else if (inst_and) begin
          reg_write_data = rs1_data & rs2_data;
        end
        else if (inst_sll) begin
          reg_write_data = rs1_data << rs2_data[4:0]; // shift amount uses lower 5 bits
        end
        else if (inst_srl) begin
          reg_write_data = rs1_data >> rs2_data[4:0];
        end
        else if (inst_sra) begin
          reg_write_data = $signed(rs1_data) >>> rs2_data[4:0]; // arithmetic right shift
        end
        else if (inst_mul) begin
          reg_write_data = rs1_data * rs2_data;
        end
        else if (inst_div || inst_divu) begin
          reg_write_data = div_quotient_final;
        end
        else if (inst_rem || inst_remu) begin
          reg_write_data = div_remainder_final;
        end
        else if (inst_mulh) begin
          reg_write_data = $signed({{32{rs1_data[31]}}, rs1_data}) *
                           $signed({{32{rs2_data[31]}}, rs2_data}) >> 32;
        end
        else if (inst_mulhsu) begin
          reg_write_data = $signed({{32{rs1_data[31]}}, rs1_data}) *
                           {32'd0, rs2_data} >> 32;
        end
        else if (inst_mulhu) begin
          reg_write_data = ({32'b0, rs1_data} * {32'b0, rs2_data}) >> 32;
        end
        else begin
          reg_write    = 1'b0;
          illegal_inst = 1'b1;
        end
      end

      // --------------------------------------------------------------------
      // Environment (ECALL)
      // --------------------------------------------------------------------
      OpEnviron: begin
        if (inst_ecall) begin
          halt = 1'b1;
        end
      end

      // --------------------------------------------------------------------
      // MiscMem (FENCE)
      // --------------------------------------------------------------------
      OpMiscMem: begin
        if (inst_fence) begin
          // No operation for FENCE in this simple model
        end
      end

      // --------------------------------------------------------------------
      // Default: illegal instruction
      // --------------------------------------------------------------------
      default: begin
        illegal_inst = 1'b1;
      end
    endcase

    // Stall on division until divider is done
    if (should_stall) begin
      pcNext           = pcCurrent;
      reg_write        = 1'b0;
      store_we_to_dmem = 4'b0000;
    end
  end

endmodule

// ---------------------------------------------------------------------------
// MemorySingleCycle
// ---------------------------------------------------------------------------
// - Shared memory for instruction + data (word-addressed)
// - Instructions read at posedge clock_mem
// - Data read/write at negedge clock_mem (read-first behavior)
// ---------------------------------------------------------------------------
module MemorySingleCycle #(
    parameter NUM_WORDS = 512
) (
  input                    rst,                  // reset for both imem and dmem
  input                    clock_mem,            // clock for both imem and dmem
  input      [`REG_SIZE:0] pc_to_imem,           // must always be aligned to 4B boundary
  output reg [`REG_SIZE:0] inst_from_imem,       // value at memory location pc_to_imem

  input      [`REG_SIZE:0] addr_to_dmem,         // must always be aligned to 4B boundary
  output reg [`REG_SIZE:0] load_data_from_dmem,  // value at memory location addr_to_dmem
  input      [`REG_SIZE:0] store_data_to_dmem,   // value to be written to addr_to_dmem
                                                  // (controlled by store_we_to_dmem)
  // Each bit determines whether to write the corresponding byte of
  // store_data_to_dmem to memory location addr_to_dmem.
  // Example:
  //   4'b1111 writes 4 bytes
  //   4'b0001 writes only the least-significant byte
  input      [        3:0] store_we_to_dmem
);

  // Memory organized as an array of 4B words
  reg [`REG_SIZE:0] mem_array[0:NUM_WORDS-1];

  // Preload instructions to mem_array
  initial begin
    $readmemh("D:/SOC_Lab/lab3/sw_project1_2/prog_mem.hex", mem_array);
  end

  localparam AddrMsb = $clog2(NUM_WORDS) + 1;
  localparam AddrLsb = 2;

  // Instruction fetch
  always @(posedge clock_mem) begin
    inst_from_imem <= mem_array[pc_to_imem[AddrMsb:AddrLsb]];
  end

  // Data memory read/write (read-first behavior)
  always @(negedge clock_mem) begin
    // Byte enables
    if (store_we_to_dmem[0]) begin
      mem_array[addr_to_dmem[AddrMsb:AddrLsb]][7:0]   <= store_data_to_dmem[7:0];
    end
    if (store_we_to_dmem[1]) begin
      mem_array[addr_to_dmem[AddrMsb:AddrLsb]][15:8]  <= store_data_to_dmem[15:8];
    end
    if (store_we_to_dmem[2]) begin
      mem_array[addr_to_dmem[AddrMsb:AddrLsb]][23:16] <= store_data_to_dmem[23:16];
    end
    if (store_we_to_dmem[3]) begin
      mem_array[addr_to_dmem[AddrMsb:AddrLsb]][31:24] <= store_data_to_dmem[31:24];
    end

    // Read-first: read returns value before the write
    load_data_from_dmem <= mem_array[addr_to_dmem[AddrMsb:AddrLsb]];
  end

endmodule

/*
This shows the relationship between clock_proc and clock_mem. The clock_mem is
phase-shifted 90° from clock_proc. You could think of one proc cycle being
broken down into 3 parts. During part 1 (which starts @posedge clock_proc)
the current PC is sent to the imem. In part 2 (starting @posedge clock_mem) we
read from imem. In part 3 (starting @negedge clock_mem) we read/write memory and
prepare register/PC updates, which occur at @posedge clock_proc.

        ____
 proc: |    |______
           ____
 mem:  ___|    |___
*/

// ---------------------------------------------------------------------------
// Processor
// ---------------------------------------------------------------------------
// - Ties together DatapathMultiCycle with MemorySingleCycle
// - Uses two clocks:
//     * clock_proc : processor core clock (PC/reg updates)
//     * clock_mem  : memory clock (instruction + data)
// ---------------------------------------------------------------------------
module Processor (
    input  clock_proc,
    input  clock_mem,
    input  rst,
    output halt
);

  wire [`REG_SIZE:0] pc_to_imem;
  wire [`REG_SIZE:0] inst_from_imem;
  wire [`REG_SIZE:0] mem_data_addr;
  wire [`REG_SIZE:0] mem_data_loaded_value;
  wire [`REG_SIZE:0] mem_data_to_write;
  wire [        3:0] mem_data_we;

  // This wire is set by cocotb to the name of the currently-running test,
  // to make it easier to see what is going on in the waveforms.
  wire [(8*32)-1:0] test_case;

  MemorySingleCycle #(
      .NUM_WORDS(8192)
  ) memory (
    .rst                 (rst),
    .clock_mem           (clock_mem),
    // imem is read-only
    .pc_to_imem          (pc_to_imem),
    .inst_from_imem      (inst_from_imem),
    // dmem is read-write
    .addr_to_dmem        (mem_data_addr),
    .load_data_from_dmem (mem_data_loaded_value),
    .store_data_to_dmem  (mem_data_to_write),
    .store_we_to_dmem    (mem_data_we)
  );

  DatapathMultiCycle datapath (
    .clk                 (clock_proc),
    .rst                 (rst),
    .pc_to_imem          (pc_to_imem),
    .inst_from_imem      (inst_from_imem),
    .addr_to_dmem        (mem_data_addr),
    .store_data_to_dmem  (mem_data_to_write),
    .store_we_to_dmem    (mem_data_we),
    .load_data_from_dmem (mem_data_loaded_value),
    .halt                (halt)
  );

endmodule
