`timescale 1ns / 1ns

// registers are 32 bits in RV32
`define REG_SIZE 31

// RV opcodes are 7 bits
`define OPCODE_SIZE 6

// Don't forget your previous ALUs
//`include "divider_unsigned.v"
//`include "cla.v"
wire        rf_we;
wire [4:0]  rf_rd;
wire [31:0] rf_rd_data;
module RegFile (
    input      [        4:0] rd,
    input      [`REG_SIZE:0] rd_data,
    input      [        4:0] rs1,
    output reg [`REG_SIZE:0] rs1_data,
    input      [        4:0] rs2,
    output reg [`REG_SIZE:0] rs2_data,
    input                    clk,
    input                    we,
    input                    rst
);
  localparam NumRegs = 32;
  wire [`REG_SIZE:0] regs[0:NumRegs-1];
  // TODO: your code here
  //patch: state-holding real register file
  reg [`REG_SIZE:0] shadow_regs[0:NumRegs-1];
  integer i;
  //reset: zero all registers except x0 (which must always remain 0 anyway)
  always @(posedge clk) begin
    if (rst) begin
      for (i=0; i<NumRegs; i=i+1)
        shadow_regs[i] <= 32'd0;
    end else begin
      if (we && rd != 0)  //this guarantee x0 is always zero
        shadow_regs[rd] <= rd_data;
    end
  end

  //aync read (the cpu can read registers instantly)
  always @(*) begin
    rs1_data = (rs1 == 0) ? 32'd0 : shadow_regs[rs1];
    rs2_data = (rs2 == 0) ? 32'd0 : shadow_regs[rs2];
  end
  // drive skeleton wires
  generate
    genvar k;
    for (k=0; k<NumRegs; k=k+1) begin : MAP
      assign regs[k] = shadow_regs[k];
    end
  endgenerate

endmodule

module DatapathSingleCycle (
    input                    clk,
    input                    rst,
    output reg                  halt,
    output     [`REG_SIZE:0] pc_to_imem,
    input      [`REG_SIZE:0] inst_from_imem,
    // addr_to_dmem is a read-write port
    output reg [`REG_SIZE:0] addr_to_dmem,
    input      [`REG_SIZE:0] load_data_from_dmem,
    output reg [`REG_SIZE:0] store_data_to_dmem,
    output reg [        3:0] store_we_to_dmem
);
  //translate the raw 32-bit instruction into its signals so that the datapath can understand
  // components of the instruction
  wire [           6:0] inst_funct7;
  wire [           4:0] inst_rs2;
  wire [           4:0] inst_rs1;
  wire [           2:0] inst_funct3;
  wire [           4:0] inst_rd;
  wire [`OPCODE_SIZE:0] inst_opcode;

  // split R-type instruction - see section 2.2 of RiscV spec
  assign {inst_funct7, inst_rs2, inst_rs1, inst_funct3, inst_rd, inst_opcode} = inst_from_imem;

  // setup for I, S, B & J type instructions
  // I - short immediates and loads
  wire [11:0] imm_i;
  assign imm_i = inst_from_imem[31:20];
  wire [ 4:0] imm_shamt = inst_from_imem[24:20];

  // S - stores
  wire [11:0] imm_s;
  assign imm_s = {inst_funct7, inst_rd};

  // B - conditionals
  wire [12:0] imm_b;
  assign {imm_b[12], imm_b[10:1], imm_b[11], imm_b[0]} = {inst_funct7, inst_rd, 1'b0};

  // J - unconditional jumps
  wire [20:0] imm_j;
  assign {imm_j[20], imm_j[10:1], imm_j[11], imm_j[19:12], imm_j[0]} = {inst_from_imem[31:12], 1'b0};

  wire [`REG_SIZE:0] imm_i_sext = {{20{imm_i[11]}}, imm_i[11:0]};
  wire [`REG_SIZE:0] imm_s_sext = {{20{imm_s[11]}}, imm_s[11:0]};
  wire [`REG_SIZE:0] imm_b_sext = {{19{imm_b[12]}}, imm_b[12:0]};
  wire [`REG_SIZE:0] imm_j_sext = {{11{imm_j[20]}}, imm_j[20:0]};
    // U-type immediate (LUI / AUIPC)
  wire [31:0] imm_u = {inst_from_imem[31:12], 12'd0};

  // opcodes - see section 19 of RiscV spec
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

  // program counter
  reg [`REG_SIZE:0] pcNext, pcCurrent;
  always @(posedge clk) begin
    if (rst) begin
      pcCurrent <= 32'd0;
    end else begin
      pcCurrent <= pcNext;
    end
  end
  assign pc_to_imem = pcCurrent;

  // cycle/inst._from_imem counters
  reg [`REG_SIZE:0] cycles_current, num_inst_current;
  always @(posedge clk) begin
    if (rst) begin
      cycles_current <= 0;
      num_inst_current <= 0;
    end else begin
      cycles_current <= cycles_current + 1;
      if (!rst) begin
        num_inst_current <= num_inst_current + 1;
      end
    end
  end

  // NOTE: don't rename your RegFile instance as the tests expect it to be `rf`
  // TODO: you will need to edit the port connections, however.
  wire [`REG_SIZE:0] rs1_data;
  wire [`REG_SIZE:0] rs2_data;
  RegFile rf (
    .clk      (clk),
    .rst      (rst),
    .we       (rf_we),
    .rd       (rf_rd),
    .rd_data  (rf_rd_data),
    .rs1      (inst_rs1),
    .rs2      (inst_rs2),
    .rs1_data (rs1_data),
    .rs2_data (rs2_data)
);
  // ========================================================
  // ALU sources
  // ========================================================
  wire inst_alu_imm =
    inst_addi  || inst_slti  || inst_sltiu ||
    inst_xori  || inst_ori   || inst_andi  ||
    inst_slli  || inst_srli  || inst_srai;
  wire [31:0] alu_in1 = rs1_data;
  wire [31:0] alu_in2 =
        (inst_lui)   ? 0 :
        (inst_auipc) ? 0 :
        (inst_jal)   ? pcCurrent :
        (inst_jalr)  ? pcCurrent :
        (inst_alu_imm) ? imm_i_sext :
        rs2_data;

  // ========================================================
  // CLA ADDER (for add/sub)
  // ========================================================
  wire [31:0] cla_sum_add, cla_sum_sub;

  // ADD
  cla cla_add (
    .a(alu_in1),
    .b(alu_in2),
    .cin(1'b0),
    .sum(cla_sum_add)
  );

  // SUB = a + (~b + 1)
  wire [31:0] sub_b = ~alu_in2;
  cla cla_sub (
    .a(alu_in1),
    .b(sub_b),
    .cin(1'b1),
    .sum(cla_sum_sub)
  );

  // ========================================================
  // DIVIDER (unsigned core)
  // ========================================================
  wire [31:0] divu_q, divu_r;

  divider_unsigned divu_core (
    .i_dividend(alu_in1),
    .i_divisor (alu_in2),
    .o_quotient(divu_q),
    .o_remainder(divu_r)
  );

  // ========================================================
  // Signed division rules
  // ========================================================
  // Common zero divisor
  wire div_by_zero = (alu_in2 == 0);

  // Signs
  wire signA = alu_in1[31];
  wire signB = alu_in2[31];

  // Absolute values for unsigned divider
  wire [31:0] A_abs = signA ? (~alu_in1 + 1) : alu_in1;
  wire [31:0] B_abs = signB ? (~alu_in2 + 1) : alu_in2;

  // Use unsigned divider core
  wire [31:0] q_abs;
  wire [31:0] r_abs;

  divider_unsigned div_core_fixed (
    .i_dividend(A_abs),
    .i_divisor (B_abs),
    .o_quotient(q_abs),
    .o_remainder(r_abs)
);

  // Apply signs
  wire [31:0] q_signed = (signA ^ signB) ? (~q_abs + 1) : q_abs;
  wire [31:0] r_signed = signA ? (~r_abs + 1) : r_abs;

  // Overflow: INT_MIN / -1
  wire is_overflow =
    (alu_in1 == 32'h8000_0000) && (alu_in2 == 32'hFFFF_FFFF);

  // Final DIV result
  wire [31:0] div_signed =
    div_by_zero ? 32'hFFFF_FFFF :
    is_overflow ? 32'h8000_0000 :
    q_signed;

  // Final REM result
  wire [31:0] rem_signed =
    div_by_zero ? alu_in1 :
    is_overflow ? 32'h00000000 :
    r_signed;
  // Unsigned DIV and REM 
  wire [31:0] div_unsigned = divu_q;
  wire [31:0] rem_unsigned = divu_r;

  // ========================================================
  // ALU Output
  // ========================================================
  reg  [31:0] alu_out;
  // Signed & unsigned aliases 
  wire signed [31:0] A_s = alu_in1;
  wire signed [31:0] B_s = alu_in2;
  wire        [31:0] A_u = alu_in1;
  wire        [31:0] B_u = alu_in2;

  wire signed [63:0] mul_ss = A_s * B_s;
  wire signed [63:0] mul_su = A_s * $signed({1'b0, B_u});   
  wire        [63:0] mul_uu = A_u * B_u;
  always @(*) begin
    alu_out = 32'd0;

    // LUI, AUIPC
    if (inst_lui)   alu_out = imm_u;
    if (inst_auipc) alu_out = pcCurrent + imm_u;

    // JAL, JALR return address
    if (inst_jal)   alu_out = pcCurrent + 32'd4;
    if (inst_jalr)  alu_out = pcCurrent + 32'd4;

    // Arithmetic
    if (inst_add || inst_addi) alu_out = cla_sum_add;
    if (inst_sub)              alu_out = cla_sum_sub;

    // Shifts
    if (inst_sll || inst_slli) alu_out = alu_in1 << alu_in2[4:0];
    if (inst_srl || inst_srli) alu_out = alu_in1 >> alu_in2[4:0];
    if (inst_sra || inst_srai) alu_out = $signed(alu_in1) >>> alu_in2[4:0];

    // Logic
    if (inst_xor || inst_xori) alu_out = alu_in1 ^ alu_in2;
    if (inst_or  || inst_ori ) alu_out = alu_in1 | alu_in2;
    if (inst_and || inst_andi) alu_out = alu_in1 & alu_in2;

    // Compare
    if (inst_slt  || inst_slti ) alu_out = ($signed(alu_in1) <  $signed(alu_in2)) ? 32'd1 : 32'd0;
    if (inst_sltu || inst_sltiu) alu_out = (alu_in1 < alu_in2) ? 32'd1 : 32'd0;

    // Multiply
    if (inst_mul)    alu_out = mul_ss[31:0];
    if (inst_mulh)   alu_out = mul_ss[63:32];
    if (inst_mulhsu) alu_out = mul_su[63:32];
    if (inst_mulhu)  alu_out = mul_uu[63:32];

    // Division
    if (inst_div)  alu_out = div_signed;
    if (inst_divu) alu_out = div_unsigned;

    // Remainder
    if (inst_rem)  alu_out = rem_signed;
    if (inst_remu) alu_out = rem_unsigned;

    // Loads store effective address
    if (inst_lb || inst_lh || inst_lw || inst_lbu || inst_lhu)
      alu_out = alu_in1 + imm_i_sext;
    if (inst_sb || inst_sh || inst_sw)
      alu_out = alu_in1 + imm_s_sext;
  end

  // ========================================================
  // Branch Decision
  // ========================================================

  wire take_branch =
      (inst_beq  && (rs1_data == rs2_data)) ||
      (inst_bne  && (rs1_data != rs2_data)) ||
      (inst_blt  && ($signed(rs1_data) <  $signed(rs2_data))) ||
      (inst_bge  && ($signed(rs1_data) >= $signed(rs2_data))) ||
      (inst_bltu && (rs1_data < rs2_data)) ||
      (inst_bgeu && (rs1_data >= rs2_data));

  // ========================================================
  // Next PC Logic
  // ========================================================
  always @(*) begin
    pcNext = pcCurrent + 32'd4;

    if (inst_jal)
      pcNext = pcCurrent + imm_j_sext;

    if (inst_jalr)
      pcNext = (rs1_data + imm_i_sext) & ~32'd1;

    if (inst_beq || inst_bne || inst_blt || inst_bge || inst_bltu || inst_bgeu)
      if (take_branch)
        pcNext = pcCurrent + imm_b_sext;
  end

  // ========================================================
  // Store signals
  // ========================================================

  // combinational mask generator + aligned store data
  reg [3:0]  store_we_comb;
  reg [31:0] store_data_aligned;

always @(*) begin
    // defaults
    store_we_comb      = 4'b0000;
    store_data_aligned = rs2_data;

    // SB: store low 8 bits of rs2 to one byte lane
    if (inst_sb) begin
        store_we_comb      = 4'b0001 << alu_out[1:0];
        store_data_aligned = {4{rs2_data[7:0]}};   // replicate LSByte
    end

    // SH: store low 16 bits of rs2 to one halfword lane
    if (inst_sh) begin
        case (alu_out[1:0])
            2'b00: store_we_comb = 4'b0011;   // lower half
            2'b10: store_we_comb = 4'b1100;   // upper half
            default: store_we_comb = 4'b0000; // misaligned → no write
        endcase
        store_data_aligned = {2{rs2_data[15:0]}}; // replicate LSHalf
    end
    // SW: full word
    if (inst_sw) begin
        store_we_comb      = 4'b1111;
        store_data_aligned = rs2_data;
    end
end

assign addr_to_dmem       = alu_out;
assign store_data_to_dmem = store_data_aligned;
assign store_we_to_dmem   = store_we_comb;

  // ========================================================
  // Load data extension
  // ========================================================
  reg [31:0] load_val;

  always @(*) begin
    load_val = 32'd0;

if (inst_lb) begin
  case (alu_out[1:0])
    2'b00: load_val = {{24{load_data_from_dmem[7]}},  load_data_from_dmem[7:0]};
    2'b01: load_val = {{24{load_data_from_dmem[15]}}, load_data_from_dmem[15:8]};
    2'b10: load_val = {{24{load_data_from_dmem[23]}}, load_data_from_dmem[23:16]};
    2'b11: load_val = {{24{load_data_from_dmem[31]}}, load_data_from_dmem[31:24]};
  endcase
end

if (inst_lbu) begin
  case (alu_out[1:0])
    2'b00: load_val = {24'd0, load_data_from_dmem[7:0]};
    2'b01: load_val = {24'd0, load_data_from_dmem[15:8]};
    2'b10: load_val = {24'd0, load_data_from_dmem[23:16]};
    2'b11: load_val = {24'd0, load_data_from_dmem[31:24]};
  endcase
end

if (inst_lh) begin
  case (alu_out[1:0])
    2'b00: load_val = {{16{load_data_from_dmem[15]}}, load_data_from_dmem[15:0]};
    2'b10: load_val = {{16{load_data_from_dmem[31]}}, load_data_from_dmem[31:16]};
    default: load_val = 32'd0;  // misaligned
  endcase
end

if (inst_lhu) begin
  case (alu_out[1:0])
    2'b00: load_val = {16'd0, load_data_from_dmem[15:0]};
    2'b10: load_val = {16'd0, load_data_from_dmem[31:16]};
    default: load_val = 32'd0;   // misaligned
  endcase
end

if (inst_lw) begin
      load_val = load_data_from_dmem;
end
end

  // ========================================================
  // Writeback mux
  // ========================================================
  reg wb_en;
  reg [31:0] wb_data;

  always @(*) begin
    wb_en   = 1'b0;
    wb_data = 32'd0;

    if (inst_lui)    begin wb_en = 1'b1; wb_data = imm_u; end
    if (inst_auipc)  begin wb_en = 1'b1; wb_data = pcCurrent + imm_u; end
    if (inst_jal ||
        inst_jalr)   begin wb_en = 1'b1; wb_data = pcCurrent + 32'd4; end

    if (inst_addi || inst_slti || inst_sltiu ||
        inst_xori || inst_ori  || inst_andi ||
        inst_slli || inst_srli || inst_srai ||
        inst_add  || inst_sub  ||
        inst_sll  || inst_slt  || inst_sltu ||
        inst_xor  || inst_srl  || inst_sra ||
        inst_or   || inst_and  ||
        inst_mul  || inst_mulh || inst_mulhsu || inst_mulhu ||
        inst_div  || inst_divu || inst_rem    || inst_remu)
    begin
        wb_en   = 1'b1;
        wb_data = alu_out;
    end

    if (inst_lb || inst_lbu || inst_lh || inst_lhu || inst_lw) begin
        wb_en   = 1'b1;
        wb_data = load_val;
    end
  end

  // Connect RegFile write ports
  assign rf_we      = wb_en & (inst_rd != 0);
  assign rf_rd      = inst_rd;
  assign rf_rd_data = wb_data;

  // ========================================================
  // ECALL HALT (sticky until reset)
  // ========================================================

  // Sticky storage bit
  always @(*) begin
    if (rst)
        halt = 1'b0;
    else
        halt = inst_ecall;
end

endmodule

/* A memory module that supports 1-cycle reads and writes, with one read-only port
 * and one read+write port.
 */
module MemorySingleCycle #(
    parameter NUM_WORDS = 512
) (
  input                    rst,                 // rst for both imem and dmem
  input                    clock_mem,           // clock for both imem and dmem
  input      [`REG_SIZE:0] pc_to_imem,          // must always be aligned to a 4B boundary
  output reg [`REG_SIZE:0] inst_from_imem,      // the value at memory location pc_to_imem
  input      [`REG_SIZE:0] addr_to_dmem,        // must always be aligned to a 4B boundary
  output reg [`REG_SIZE:0] load_data_from_dmem, // the value at memory location addr_to_dmem
  input      [`REG_SIZE:0] store_data_to_dmem,  // the value to be written to addr_to_dmem, controlled by store_we_to_dmem
  // Each bit determines whether to write the corresponding byte of store_data_to_dmem to memory location addr_to_dmem.
  // E.g., 4'b1111 will write 4 bytes. 4'b0001 will write only the least-significant byte.
  input      [        3:0] store_we_to_dmem
);

  // memory is arranged as an array of 4B words
  reg [`REG_SIZE:0] mem_array[0:NUM_WORDS-1];

  // preload instructions to mem_array
  initial begin
    $readmemh("mem_initial_contents.hex", mem_array);
  end

  localparam AddrMsb = $clog2(NUM_WORDS) + 1;
  localparam AddrLsb = 2;

  always @(posedge clock_mem) begin
    inst_from_imem <= mem_array[{pc_to_imem[AddrMsb:AddrLsb]}];
  end

  always @(negedge clock_mem) begin
   if (store_we_to_dmem[0]) begin
     mem_array[addr_to_dmem[AddrMsb:AddrLsb]][7:0] <= store_data_to_dmem[7:0];
   end
   if (store_we_to_dmem[1]) begin
     mem_array[addr_to_dmem[AddrMsb:AddrLsb]][15:8] <= store_data_to_dmem[15:8];
   end
   if (store_we_to_dmem[2]) begin
     mem_array[addr_to_dmem[AddrMsb:AddrLsb]][23:16] <= store_data_to_dmem[23:16];
   end
   if (store_we_to_dmem[3]) begin
     mem_array[addr_to_dmem[AddrMsb:AddrLsb]][31:24] <= store_data_to_dmem[31:24];
   end
   // dmem is "read-first": read returns value before the write
   load_data_from_dmem <= mem_array[{addr_to_dmem[AddrMsb:AddrLsb]}];
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
module Processor (
    input  clock_proc,
    input  clock_mem,
    input  rst,
    output halt
);

  wire [`REG_SIZE:0] pc_to_imem, inst_from_imem, mem_data_addr, mem_data_loaded_value, mem_data_to_write;
  wire [        3:0] mem_data_we;

  // This wire is set by cocotb to the name of the currently-running test, to make it easier
  // to see what is going on in the waveforms.
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

  DatapathSingleCycle datapath (
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
