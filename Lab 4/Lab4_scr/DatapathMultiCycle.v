/* INSERT NAME AND PENNKEY HERE */

`timescale 1ns / 1ns

// registers are 32 bits in RV32
`define REG_SIZE 31

// RV opcodes are 7 bits
`define OPCODE_SIZE 6

// Don't forget your CLA and Divider
`include "cla.v"
`include "DividerUnsignedPipelined.v"

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
  wire [19:0] lui_imm = inst_from_imem[31:12];
  reg reg_write;
  reg [31:0] reg_write_data;
  reg signed [63:0] mul_temp;
  reg        [63:0] mul_temp_u;
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
  //====================================================
  // ALU: Carry-Lookahead Adder (CLA) for + / - / address calc
  //====================================================

  wire [31:0] alu_a = rs1_data;
  reg  [31:0] alu_b;
  reg  alu_cin;
  wire [31:0] alu_result;
  cla cla_main(
    .a   (alu_a),
    .b   (alu_b),
    .cin (alu_cin),
    .sum (alu_result)
  );
  
  //====================================================
  // DIV / REM: Signed/Unsigned Division Front-End
  //====================================================

  // True if this is a signed operation (DIV or REM)
  wire is_div_signed = inst_div || inst_rem;
  
  // Absolute value inputs to the *unsigned* divider core
  wire [31:0] div_dividend_abs;
  wire [31:0] div_divisor_abs;
  
  // If signed op and rs1 is negative, take two's complement to make it positive
  assign div_dividend_abs = (is_div_signed && rs1_data[31]) ? (~rs1_data + 1) : rs1_data;

  // Same for rs2: convert negative divisor to positive for unsigned divider
  assign div_divisor_abs  = (is_div_signed && rs2_data[31]) ? (~rs2_data + 1) : rs2_data;
  
  wire [31:0] div_quotient_raw;
  wire [31:0] div_remainder_raw;
  
  wire [31:0] div_quotient; 
  wire [31:0] div_remainder;

  //====================================================
  // 8-stage pipelined *unsigned* divider
  //====================================================
  DividerUnsignedPipelined div_inst(
    .clk        (clk),
    .rst        (rst),
    .stall      (1'b0),              // always allowed to run; stalling handled outside
    .i_dividend (div_dividend_abs),  // absolute value of dividend
    .i_divisor  (div_divisor_abs),   // absolute value of divisor
    .o_quotient (div_quotient_raw),  // unsigned quotient
    .o_remainder(div_remainder_raw)  // unsigned remainder
  );

  // Final outputs *after* sign / special-case handling
  reg [31:0] div_quotient_final;
  reg [31:0] div_remainder_final;
  
  //====================================================
  // Post-processing: signed result fix-up and div-by-zero cases
  //====================================================
  always @(*) begin
      // Default: use raw unsigned results
      div_quotient_final  = div_quotient_raw;
      div_remainder_final = div_remainder_raw;

      if (is_div_signed) begin
          // Signed DIV/REM behavior
          if (rs2_data == 0) begin
              // RISC-V spec: DIV/REM by zero
              // - quotient = -1 (all 1s)
              // - remainder = dividend
              div_quotient_final  = 32'hFFFFFFFF; 
              div_remainder_final = rs1_data;
          end else begin
              // If signs differ, quotient should be negative
              if ((rs1_data[31] ^ rs2_data[31]) && div_quotient_raw != 0) begin
                  div_quotient_final = ~div_quotient_raw + 1;
              end
              // Remainder has same sign as dividend
              if (rs1_data[31] && div_remainder_raw != 0) begin
                  div_remainder_final = ~div_remainder_raw + 1;
              end
          end
      end
  end
  
  //====================================================
  // Divider Latency Tracking / Stall Control
  //====================================================

  reg        div_busy; 
  reg  [2:0] div_counter;
  wire       is_div_op   = inst_div || inst_divu || inst_rem || inst_remu;
  wire       div_start   = is_div_op && !div_busy;
  wire       div_done    = div_busy && (div_counter == 3'd7);
  // Stall the pipeline/datapath while a div op is not finished
  wire       should_stall = is_div_op && !div_done;

  //====================================================
  // Sequential logic: track divider state and cycle count
  //====================================================
  always @(posedge clk) begin
    if (rst) begin
        div_busy    <= 1'b0;
        div_counter <= 3'd0;
    end else begin
      if (div_start) begin
        // New divide: enter busy and reset cycle counter
        div_busy    <= 1'b1;
        div_counter <= 3'd0;
      end else if (div_busy) begin
        if (div_done) begin
          // Finished: clear busy and reset counter
          div_busy    <= 1'b0;
          div_counter <= 3'd0;
        end else begin
          // Still running: increment cycle counter
          div_counter <= div_counter + 3'd1;
        end
      end
    end
  end

//PC UPDATE LOGIC 
always @(*) begin
    pcNext = pcCurrent + 32'd4;   // default sequential PC
    // JAL
    if (inst_jal) begin
        pcNext = pcCurrent + imm_j_sext;
    end
    // JALR
    else if (inst_jalr) begin
        pcNext = (rs1_data + imm_i_sext) & ~32'd1;
    end
    // BRANCHES
    else if (inst_opcode == OpBranch) begin
        if ((inst_beq  && (rs1_data == rs2_data)) ||
            (inst_bne  && (rs1_data != rs2_data)) ||
            (inst_blt  && ($signed(rs1_data) <  $signed(rs2_data))) ||
            (inst_bge  && ($signed(rs1_data) >= $signed(rs2_data))) ||
            (inst_bltu && (rs1_data <  rs2_data)) ||
            (inst_bgeu && (rs1_data >= rs2_data))) begin

            pcNext = pcCurrent + imm_b_sext;
        end
    end
    // STALL OVERRIDES EVERYTHING
    if (should_stall)
        pcNext = pcCurrent;
end

  reg illegal_inst;
  always @(*) begin
    illegal_inst = 1'b0;

    reg_write = 1'b0;
    reg_write_data =  32'd0;
    halt = 1'b0;

    addr_to_dmem = 32'd0;
    store_data_to_dmem = 32'd0;
    store_we_to_dmem = 4'b0000;
  
    alu_b = rs2_data;
    alu_cin = 1'b0;
    
    if (inst_opcode == OpStore) begin
        alu_b = imm_s_sext;
    end
    if (inst_addi || (inst_opcode == OpLoad) || inst_jalr || inst_auipc) begin
        alu_b = imm_i_sext;
    end 
    if (inst_sub) begin
        alu_b = ~rs2_data + 32'd1;
        alu_cin = 1'b0;
    end    
    case (inst_opcode)
      OpLui: begin
        // TODO: start here by implementing lui
        reg_write = 1;
        reg_write_data = {lui_imm, 12'd0};
      end
      
      OpAuipc: begin
        reg_write = 1'b1;
        reg_write_data = pcCurrent + {inst_from_imem[31:12], 12'd0};
      end
      
      OpJal: begin
        reg_write = 1'b1;
        reg_write_data = pcCurrent + 32'd4;
      end
      
      OpJalr: begin
        reg_write = 1'b1;
        reg_write_data = pcCurrent + 32'd4;
      end
      
      OpBranch: begin
      end
      
      OpLoad: begin 
        addr_to_dmem = alu_result;
        reg_write = 1'b1;
        // Decode load type based on funct3 and handle misaligned addresses
        case (inst_funct3)
            3'b000: begin // LB: load signed byte
                // alu_result[1:0] = byte offset inside the 32-bit word from dmem
                case (alu_result[1:0])
                    2'b00: 
                        // select lowest byte [7:0], sign-extend bit 7
                        reg_write_data = {{24{load_data_from_dmem[7]}},  load_data_from_dmem[7:0]};
                    2'b01: 
                        // select next byte [15:8], sign-extend bit 15
                        reg_write_data = {{24{load_data_from_dmem[15]}}, load_data_from_dmem[15:8]};
                    2'b10: 
                        // select next byte [23:16], sign-extend bit 23
                        reg_write_data = {{24{load_data_from_dmem[23]}}, load_data_from_dmem[23:16]};
                    2'b11: 
                        // select highest byte [31:24], sign-extend bit 31
                        reg_write_data = {{24{load_data_from_dmem[31]}}, load_data_from_dmem[31:24]};
                endcase
            end
            3'b001: begin // LH: load signed halfword
                // alu_result[1] = halfword offset: 0 = lower 16 bits, 1 = upper 16 bits
                case (alu_result[1])
                    1'b0: 
                        // select lower halfword [15:0], sign-extend bit 15
                        reg_write_data = {{16{load_data_from_dmem[15]}}, load_data_from_dmem[15:0]};
                    1'b1: 
                        // select upper halfword [31:16], sign-extend bit 31
                        reg_write_data = {{16{load_data_from_dmem[31]}}, load_data_from_dmem[31:16]};
                endcase
            end
            3'b010: 
                // LW: load full 32-bit word directly, no alignment gymnastics
                reg_write_data = load_data_from_dmem;
            3'b100: begin // LBU: load unsigned byte
                // Same byte selection as LB, but zero-extended instead of sign-extended
                case (alu_result[1:0])
                    2'b00: reg_write_data = {24'd0, load_data_from_dmem[7:0]};    // lowest byte
                    2'b01: reg_write_data = {24'd0, load_data_from_dmem[15:8]};   // next byte
                    2'b10: reg_write_data = {24'd0, load_data_from_dmem[23:16]};  // next byte
                    2'b11: reg_write_data = {24'd0, load_data_from_dmem[31:24]};  // highest byte
                endcase
            end

            3'b101: begin // LHU: load unsigned halfword
                // Same halfword selection as LH, but zero-extended
                case (alu_result[1])
                    1'b0: reg_write_data = {16'd0, load_data_from_dmem[15:0]};    // lower halfword
                    1'b1: reg_write_data = {16'd0, load_data_from_dmem[31:16]};   // upper halfword
                endcase
            end

            default: 
                // For unsupported funct3 values, disable write and mark illegal if you want
                reg_write = 1'b0;
        endcase
      end
      
      OpStore: begin
        addr_to_dmem = alu_result;
        store_data_to_dmem = rs2_data << (alu_result[1:0] * 8);
        if (inst_sw) begin
            store_we_to_dmem = 4'b1111;
        end
        else if (inst_sb) begin
            store_we_to_dmem = 4'b0001 << alu_result[1:0];
        end
        else if (inst_sh) begin
            store_we_to_dmem = (alu_result[1] == 0) ? 4'b0011 : 4'b1100;
        end
        else begin
            store_we_to_dmem = 4'b0000;
            illegal_inst =1'b1;
        end
      end
      
      OpRegImm: begin
        reg_write = 1'b1;
        if (inst_addi) begin
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
            reg_write_data = rs1_data << imm_i[4:0]; 
        end
        else if (inst_srli) begin
            reg_write_data = rs1_data >> imm_i[4:0];
        end
        else if (inst_srai) begin
            reg_write_data = $signed(rs1_data) >>> imm_i[4:0]; 
        end
        else begin
            reg_write = 1'b0;
            illegal_inst = 1'b1;
        end
      end
      
      OpRegReg: begin
        reg_write = 1'b1;   // R-type instructions write by default
        if (inst_add || inst_sub) begin
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
            reg_write_data = rs1_data << rs2_data[4:0]; 
        end
        else if (inst_srl) begin
            reg_write_data = rs1_data >> rs2_data[4:0];
        end
        else if (inst_sra) begin
            reg_write_data = $signed(rs1_data) >>> rs2_data[4:0]; 
        end
        else if (inst_div || inst_divu) begin
            if (div_done) begin
                reg_write_data = div_quotient_final;
            end else begin
                reg_write = 1'b0;   // don’t write until result is ready
            end
        end
        else if (inst_rem || inst_remu) begin
            if (div_done) begin
                reg_write_data = div_remainder_final;
            end else begin
                reg_write = 1'b0;
            end
        end
        // MULH (signed × signed → upper 32 bits)
        else if (inst_mul) begin
        // low 32 bits of rs1 * rs2 (signed/unsigned same in low bits)
            mul_temp = $signed({{32{rs1_data[31]}}, rs1_data}) * $signed({{32{rs2_data[31]}}, rs2_data});
            reg_write_data = mul_temp[31:0];
        end
        else if (inst_mulh) begin
        // signed × signed, high 32 bits
            mul_temp = $signed({{32{rs1_data[31]}}, rs1_data}) * $signed({{32{rs2_data[31]}}, rs2_data});
            reg_write_data = mul_temp[63:32];
        end
        else if (inst_mulhsu) begin
        // signed × unsigned, high 32 bits
            mul_temp = $signed({{32{rs1_data[31]}}, rs1_data}) * $signed({32'b0, rs2_data});
            reg_write_data = mul_temp[63:32];
        end
        else if (inst_mulhu) begin
        // unsigned × unsigned, high 32 bits
            mul_temp_u = {32'b0, rs1_data} * {32'b0, rs2_data};
            reg_write_data = mul_temp_u[63:32];
        end
        else begin
            reg_write = 1'b0;
            illegal_inst = 1'b1;
        end
      end
      
      OpEnviron: begin
        if (inst_ecall) halt = 1'b1;
      end
      
      OpMiscMem: begin
        if (inst_fence);
      end
      default: begin
        illegal_inst = 1'b1;
      end
    endcase
    if (should_stall) begin
        // PC stall is already handled in the separate PC logic block
        reg_write       = 1'b0;
        store_we_to_dmem = 4'b0000;
    end
  end
endmodule

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

