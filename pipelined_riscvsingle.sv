//pipelined_riscvsingle.sv

// RISC-V single-cycle processor


// run 210
// Expect simulator to print "Simulation succeeded"
// when the value 25 (0x19) is written to address 100 (0x64)

// Single-cycle implementation of RISC-V (RV32I)
// User-level Instruction Set Architecture V2.2 (May 7, 2017)
// Implements a subset of the base integer instructions:
//    lw, sw
//    add, sub, and, or, slt, 
//    addi, andi, ori, slti
//    beq
//    jal
// Exceptions, traps, and interrupts not implemented
// little-endian memory

// 31 32-bit registers x1-x31, x0 hardwired to 0

module testbench();

  logic        clk;
  logic        reset;

  logic [31:0] WriteData, DataAdr;
  logic        MemWrite;

  // instantiate device to be tested
  lab9 dut(clk, reset, WriteData, DataAdr, MemWrite);
  
  // initialize test
  initial
    begin
      reset <= 1; # 22; reset <= 0;
    end

  // generate clock to sequence tests
  always
    begin
      clk <= 1; # 5; clk <= 0; # 5;
    end

  // check results
  always @(negedge clk)
    begin
      if(MemWrite) begin
        if(DataAdr === 100 & WriteData === 25) begin
          $display("Simulation succeeded");
			
       //doesnt stop anymore after sim succeeds
        end else if (DataAdr !== 96) begin
          $display("Simulation failed");
          $stop;
        end
      end
    end
endmodule
///////////////////////////////////////////////////////////
///// End Testbench                                   /////
///////////////////////////////////////////////////////////


module lab9(input  logic        clk, reset, 
           output logic [31:0] WriteDataM, DataAdrM, 
           output logic        MemWriteM);

  logic [31:0] PCF, InstrF, ReadDataM;
  
  // instantiate processor and memories
  riscvsingle rvsingle(clk, reset, PCF, InstrF, MemWriteM, DataAdrM, 
                       WriteDataM, ReadDataM);
  imem imem(PCF, InstrF);
  dmem dmem(clk, MemWriteM, DataAdrM, WriteDataM, ReadDataM);
endmodule

module riscvsingle(
    input  logic        clk, reset,
    output logic [31:0] PCF,
    input  logic [31:0] InstrF,
    output logic        MemWriteM,
    output logic [31:0] ALUResultM, WriteDataM,
    input  logic [31:0] ReadDataM
);

    // Control signals
    logic       RegWriteD, MemWriteD, JumpD, BranchD, ALUSrcD;
    logic RegWriteM, RegWriteW;
    logic [1:0] ResultSrcD;
    logic [2:0] ImmSrcD;
    logic [3:0] ALUControlD;

    // Hazard and forwarding control signals
    logic StallF, StallD, FlushD, FlushE;
    logic [1:0] ForwardAE, ForwardBE;

    // Datapath signals
    logic [31:0] InstrD;
    logic [4:0] Rs1D, Rs2D, Rs1E, Rs2E, RdE, RdM, RdW;
    logic [1:0] ResultSrcE;
    logic PCSrcE;

    // Instantiate controller
    controller c(
        InstrD[6:0], InstrD[14:12], InstrD[30], BranchD,
        ResultSrcD, MemWriteD, 
        ALUSrcD, RegWriteD, JumpD,
        ImmSrcD, ALUControlD
    );

    // Instantiate datapath
    datapath dp(
        clk, reset,
        RegWriteD, ResultSrcD, MemWriteD, JumpD, BranchD, MemWriteM,
        ALUControlD, ALUSrcD, ImmSrcD,
        PCF, InstrF, InstrD,
        ALUResultM, WriteDataM, ReadDataM,
        StallF, StallD, FlushD, FlushE,
        ForwardAE, ForwardBE, RegWriteM, RegWriteW,
        Rs1D, Rs2D, Rs1E, Rs2E, RdE, RdM, RdW, PCSrcE, ResultSrcE
    );

   hazardunit hu(
    Rs1D, Rs2D, Rs1E, Rs2E, RdE, PCSrcE, ResultSrcE, 
    RdM, RdW, RegWriteM, RegWriteW, 
    StallF, StallD, FlushD, FlushE, ForwardAE, ForwardBE
);


endmodule


module hazardunit (
    // Inputs
    input  logic [4:0] Rs1D,      // Source register 1 in Decode stage
    input  logic [4:0] Rs2D,      // Source register 2 in Decode stage
    
    input  logic [4:0] Rs1E,
    input  logic [4:0] Rs2E,
    input  logic [4:0] RdE,
    input logic PCSrcE,
    input logic [1:0] ResultSrcE,
    
    input  logic [4:0] RdM,       // Destination register in Memory stage
    input  logic [4:0] RdW,       // Destination register in Write-back stage
    input  logic       RegWriteM, // Register write signal in Memory stage
    input  logic       RegWriteW, // Register write signal in Write-back stage
    // Outputs
    output logic       StallF,    // Stall signal for Fetch stage
    output logic       StallD,    // Stall signal for Decode stage
    output logic       FlushD,    // Flush signal for Decode stage
    output logic       FlushE,    // Flush signal for Execute stage
    output logic [1:0] ForwardAE, // Forwarding control for ALU SrcA
    output logic [1:0] ForwardBE  // Forwarding control for ALU SrcB
);

logic lwStall;
assign lwStall = ((Rs2D == RdE) || (Rs1D == RdE)) && (ResultSrcE[0]);
always_comb begin
    if ((Rs1E == RdM) && RegWriteM && (Rs1E != 0)) begin
        ForwardAE = 2'b10;  // Forward from Memory stage
    end else if ((Rs1E == RdW) && RegWriteW && (Rs1E != 0)) begin
        ForwardAE = 2'b01;  // Forward from Write-back stage
    end else begin
        ForwardAE = 2'b00;  // No forwarding
    end
end

always_comb begin
    if ((Rs2E == RdM) && RegWriteM && (Rs2E != 0)) begin
        ForwardBE = 2'b10;  // Forward from Memory stage
    end else if ((Rs2E == RdW) && RegWriteW && (Rs2E != 0)) begin
        ForwardBE = 2'b01;  // Forward from Write-back stage
    end else begin
        ForwardBE = 2'b00;  // No forwarding
    end
end



// Generate lwStall
//lwStall = (ResultSrcE[0] && ((Rs1D == RdE) || (Rs2D == RdE)));

// Stall signals
assign StallF = lwStall;
assign StallD = lwStall;

// Flush signals
assign FlushD = PCSrcE;             // Flush Decode stage on branch or jump
assign FlushE = lwStall || PCSrcE;  // Flush Execute stage on load-use stall or branch/jump



endmodule


module controller(input  logic [6:0] op,
                  input  logic [2:0] funct3,
                  input  logic       funct7b5,
						output logic Branch,
                  output logic [1:0] ResultSrc,
                  output logic       MemWrite, ALUSrc,
                  output logic       RegWrite, Jump,
                  output logic [2:0] ImmSrc,
                  output logic [3:0] ALUControl);

  logic [1:0] ALUOp;


  maindec md(op, ResultSrc, MemWrite, Branch,
             ALUSrc, RegWrite, Jump, ImmSrc, ALUOp);
  aludec  ad(op[5], funct3, funct7b5, ALUOp, ALUControl);

 

endmodule

module maindec(input  logic [6:0] op,
               output logic [1:0] ResultSrc,
               output logic       MemWrite,
               output logic       Branch, ALUSrc,
               output logic       RegWrite, Jump,
               output logic [2:0] ImmSrc, // Update to 3 bits
               output logic [1:0] ALUOp);

  logic [11:0] controls; // Increase width to 12 bits

  assign {RegWrite, ImmSrc, ALUSrc, MemWrite,
          ResultSrc, Branch, ALUOp, Jump} = controls;

  always_comb
    case(op)
    // RegWrite_ImmSrc_ALUSrc_MemWrite_ResultSrc_Branch_ALUOp_Jump
      7'b0000011: controls = 12'b1_000_1_0_01_0_00_0; // lw
      7'b0100011: controls = 12'b0_001_1_1_00_0_00_0; // sw
      7'b0110011: controls = 12'b1_000_0_0_00_0_10_0; // R-type
      7'b1100011: controls = 12'b0_010_0_0_00_1_01_0; // beq
      7'b0010011: controls = 12'b1_000_1_0_00_0_10_0; // I-type ALU
      7'b1101111: controls = 12'b1_011_0_0_10_0_00_1; // jal
      7'b0110111: controls = 12'b1_100_1_0_00_0_11_0; // lui
      default:    controls = 12'b0_000_0_0_00_0_00_0;  // non-implemented
    endcase
endmodule


module aludec(input  logic       opb5,
              input  logic [2:0] funct3,
              input  logic       funct7b5, 
              input  logic [1:0] ALUOp,
              output logic [3:0] ALUControl);

  logic  RtypeSub;
  assign RtypeSub = funct7b5 & opb5;  // TRUE for R-type subtract instruction

  always_comb
   case (ALUOp)
    2'b00:                ALUControl = 4'b0000; // addition
      2'b01:                ALUControl = 4'b0001; // subtraction
		2'b11: ALUControl = 4'b1001; //lui
      default: case(funct3) // R-type or I-type ALU
                 3'b000:  if (RtypeSub) 
                            ALUControl = 4'b0001; // sub
                          else          
                            ALUControl = 4'b0000; // add, addi
                 3'b001:    ALUControl = 4'b0110; // sll
                 3'b010:    ALUControl = 4'b0101; // slt, slti
                 3'b100:    ALUControl = 4'b0100; // xor
                 3'b101:  if (funct7b5)
                             ALUControl = 4'b1000; // sra
                           else
                             ALUControl = 4'b0111; // srl
                 3'b110:    ALUControl = 4'b0011; // or, ori
                 3'b111:    ALUControl = 4'b0010; // and, andi
                 default:   ALUControl = 4'b0000; // ???
               endcase
    endcase
endmodule

module datapath(
    input  logic        clk, reset,
    input  logic        RegWriteD,
    input  logic [1:0]  ResultSrcD,
    input  logic        MemWriteD, JumpD, BranchD,
    output logic MemWriteM,
    input  logic [3:0]  ALUControlD,
    input  logic        ALUSrcD,
    input  logic [2:0]  ImmSrcD,
    output logic [31:0] PCF,
    input  logic [31:0] InstrF,
    output logic [31:0] InstrD,
    output logic [31:0] ALUResultM, WriteDataM,
    input  logic [31:0] ReadDataM,
    input  logic        StallF, StallD, FlushD, FlushE,
    input  logic [1:0]  ForwardAE, ForwardBE,
    output logic RegWriteM, RegWriteW,
    output logic [4:0]  Rs1D, Rs2D, Rs1E, Rs2E, RdE, RdM, RdW,
    output logic        PCSrcE,
    output logic [1:0]  ResultSrcE
);

  logic JumpE, ZeroE;
  logic [31:0] PCPlus4F, PCPlus4D, PCPlus4E, PCPlus4M, PCPlus4W;
   logic [3:0] ALUControlE;
  logic [1:0]  ResultSrcM, ResultSrcW;
  logic [31:0] PCD, PCE, PCFp;
  logic [31:0] PCTargetE;
  logic [31:0] ImmExtD, ImmExtE;
  logic [31:0] Rd1D, Rd2D, Rd1E,Rd2E;
  logic [4:0] RdD;
  logic [31:0] SrcA, SrcB, SrcAE, SrcBE;
  logic [31:0] ResultW, ALUResultE, WriteDataE,ALUResultW, ReadDataW;	



  
  // next PC logic
  

  mux2 #(32)  pcmux(PCPlus4F, PCTargetE, PCSrcE, PCFp);
  flopr #(32) pcreg(clk, reset, StallF, PCFp, PCF); 
  adder       pcadd4(PCF, 32'd4, PCPlus4F);
  reg3 #(32)  regD(clk, StallD, FlushD, reset, InstrF,PCF,PCPlus4F,InstrD,PCD,PCPlus4D);
  
  
 	
  // register file logic
  regfile     rf(clk, RegWriteW, InstrD[19:15], InstrD[24:20], 
                 RdW, ResultW, Rd1D, Rd2D);
  extend      ext(InstrD[31:7], ImmSrcD, ImmExtD);
  
  assign Rs1D = InstrD[19:15];
  assign Rs2D = InstrD[24:20];
  assign RdD = InstrD[11:7];	
  
  reg16 #(32) regDToE(clk, FlushE,  reset, 
                    RegWriteD, ResultSrcD, MemWriteD, JumpD, BranchD, ALUControlD, ALUSrcD, Rd1D, Rd2D, PCD, Rs1D, Rs2D, RdD, ImmExtD, PCPlus4D, 
                    RegWriteE, ResultSrcE, MemWriteE, JumpE, BranchE, ALUControlE, ALUSrcE,Rd1E, Rd2E, PCE, Rs1E, Rs2E, RdE, ImmExtE, PCPlus4E);
   
  srcmux3 #(32) srcAmux(Rd1E, ResultW, ALUResultM, ForwardAE, SrcAE);
  srcmux3 #(32) WDmux(Rd2E, ResultW, ALUResultM, ForwardBE, WriteDataE);
  mux2 #(32) srcBmux(WriteDataE, ImmExtE, ALUSrcE, SrcBE);



 
  // ALU logic

    alu         alu(SrcAE, SrcBE, ALUControlE, ALUResultE, ZeroE, LessE);
    adder pcaddbranch(PCE, ImmExtE, PCTargetE);
    assign PCSrcE = (BranchE & ZeroE) | JumpE;
    
    reg7 #(32) regEToM(
    clk, reset, 
    RegWriteE, ResultSrcE, MemWriteE, ALUResultE, WriteDataE, RdE, PCPlus4E,
    RegWriteM, ResultSrcM, MemWriteM, ALUResultM, WriteDataM, RdM, PCPlus4M);
    
    
    reg6 #(32) regMToW(
    clk, reset, 
    RegWriteM, ResultSrcM, ALUResultM, ReadDataM, RdM, PCPlus4M,
    RegWriteW, ResultSrcW, ALUResultW, ReadDataW, RdW, PCPlus4W
);

   mux3 #(32) resultmux(ALUResultW, ReadDataW,PCPlus4W, ResultSrcW, ResultW);
    
   
   
endmodule


module srcmux2 #(parameter WIDTH = 8)
             (input  logic [WIDTH-1:0] d0, d1, 
              input  logic             s, 
              output logic [WIDTH-1:0] y);

  assign y = s ? d1 : d0; 
endmodule

module srcmux3 #(parameter WIDTH = 8)
             (input  logic  [WIDTH-1:0] rd,
              input logic [WIDTH-1:0] aluresultm, resultw,
              input  logic [1:0]       forward, 
              output logic [WIDTH-1:0] src);

  assign src = forward[1] ? resultw : (forward[0] ? aluresultm : rd); 
endmodule

module regfile(
    input  logic        clk, 
    input  logic        we3, 
    input  logic [4:0]  a1, a2, a3, 
    input  logic [31:0] wd3, 
    output logic [31:0] rd1, rd2
);

  logic [31:0] rf[31:0];  // Register file array

  // Write operation occurs on the falling edge of the clock
  always_ff @(negedge clk) begin
    if (we3) 
      rf[a3] <= wd3;
  end

  // Read operation is combinational
  assign rd1 = (a1 != 0) ? rf[a1] : 0; 
  assign rd2 = (a2 != 0) ? rf[a2] : 0;

endmodule


module adder(input  [31:0] a, b,
             output [31:0] y);

  assign y = a + b;
endmodule

module extend(input  logic [31:7] instr,
              input  logic [2:0]  immsrc, 
              output logic [31:0] immext);
 
  always_comb
    case(immsrc) 
      3'b000: immext = {{20{instr[31]}}, instr[31:20]}; // I-type
      3'b001: immext = {{20{instr[31]}}, instr[31:25], instr[11:7]}; // S-type
      3'b010: immext = {{20{instr[31]}}, instr[7], instr[30:25], instr[11:8], 1'b0}; // B-type
      3'b011: immext = {{12{instr[31]}}, instr[19:12], instr[20], instr[30:21], 1'b0}; // J-type
      3'b100: immext = {instr[31:12], 12'b0}; // U-type
      default: immext = 32'b0; // undefined
    endcase             
endmodule


module flopr #(parameter WIDTH = 8)
              (input  logic             clk,
               input  logic             reset,
               input  logic             en,
               input  logic [WIDTH-1:0] d,
               output logic [WIDTH-1:0] q);  
               
always_ff @(posedge clk, posedge reset) begin
    if (reset)
      q <= 0;           // Reset q to 0
    else if (!en)
      q <= d;           // Update q only when not stalled  end
    end
endmodule



module reg3 #(parameter WIDTH = 32) (
    input  logic             clk,  // Clock signal
    input  logic             en,   // Enable signal
    input  logic             clr,  // Clear signal
    input logic reset,
    input  logic [WIDTH-1:0] d1,   // First data input
    input  logic [WIDTH-1:0] d2,   // Second data input
    input  logic [WIDTH-1:0] d3,   // Third data input
    output logic [WIDTH-1:0] q1,   // First output
    output logic [WIDTH-1:0] q2,   // Second output
    output logic [WIDTH-1:0] q3    // Third output
);  
always_ff @(posedge clk, posedge clr, posedge reset) begin
        if (clr || reset) begin
            q1 <= 0;
            q2 <= 0;
            q3 <= 0;
        end
        else if (!en) begin
            q1 <= d1;
            q2 <= d2;
            q3 <= d3;
        end
    end
endmodule

module reg16 #(parameter WIDTH = 32) (
    input  logic             clk,          
    input  logic             clr,          
    input  logic             reset,        
    input  logic             RegWriteD,    
    input  logic [1:0]       ResultSrcD,   
    input  logic             MemWriteD,    
    input  logic             JumpD,        
    input  logic             BranchD,      
    input  logic [3:0]       ALUControlD,  
    input  logic             ALUSrcD,     

    input  logic [WIDTH-1:0] RD1,          
    input  logic [WIDTH-1:0] RD2,          
    input  logic [WIDTH-1:0] PCD,          
    input  logic [4:0]       Rs1D,         
    input  logic [4:0]       Rs2D,         
    input  logic [4:0]       RdD,          
    input  logic [WIDTH-1:0] ImmExtD,      
    input  logic [WIDTH-1:0] PCPlus4D,     
    output logic             RegWriteE,    
    output logic [1:0]       ResultSrcE,   
    output logic             MemWriteE,    
    output logic             JumpE,        
    output logic             BranchE,     
    output logic [3:0]       ALUControlE,  
    output logic             ALUSrcE,      

    output logic [WIDTH-1:0] RD1E,         
    output logic [WIDTH-1:0] RD2E,       
    output logic [WIDTH-1:0] PCE,         
    output logic [4:0]       Rs1E,         
    output logic [4:0]       Rs2E,         
    output logic [4:0]       RdE,         
    output logic [WIDTH-1:0] ImmExtE,      
    output logic [WIDTH-1:0] PCPlus4E     
);

    always_ff @(posedge clk or posedge reset) begin
        if (reset) begin
            // Reset all outputs
            RegWriteE   <= 0; ResultSrcE  <= 0; MemWriteE   <= 0; JumpE      <= 0; 
            BranchE     <= 0; ALUControlE <= 0; ALUSrcE     <= 0;
            RD1E        <= 0; RD2E        <= 0; PCE         <= 0; Rs1E       <= 0; 
            Rs2E        <= 0; RdE         <= 0; ImmExtE     <= 0; PCPlus4E   <= 0;
        end else if (clr) begin
            // Flush outputs
            RegWriteE   <= 0; ResultSrcE  <= 0; MemWriteE   <= 0; JumpE      <= 0; 
            BranchE     <= 0; ALUControlE <= 0; ALUSrcE     <= 0;
            RD1E        <= 0; RD2E        <= 0; PCE         <= 0; Rs1E       <= 0; 
            Rs2E        <= 0; RdE         <= 0; ImmExtE     <= 0; PCPlus4E   <= 0;
        end else begin
            RegWriteE   <= RegWriteD; ResultSrcE  <= ResultSrcD; MemWriteE   <= MemWriteD;
            JumpE       <= JumpD;     BranchE     <= BranchD;   ALUControlE <= ALUControlD;
            ALUSrcE     <= ALUSrcD;  RD1E        <= RD1;
            RD2E        <= RD2;       PCE         <= PCD;       Rs1E        <= Rs1D;
            Rs2E        <= Rs2D;      RdE         <= RdD;       ImmExtE     <= ImmExtD;
            PCPlus4E    <= PCPlus4D;
        end
    end

endmodule



module reg7 #(parameter WIDTH = 32) (
    input  logic             clk,          // Clock signal
    input  logic             reset,        // Reset signal
    input  logic             RegWriteE,    // Input for RegWrite in Execute stage
    input  logic [1:0]       ResultSrcE,   // Input for ResultSrc in Execute stage
    input  logic             MemWriteE,    // Input for MemWrite in Execute stage
    input  logic [WIDTH-1:0] ALUResultE,   // Input for ALU Result in Execute stage
    input  logic [WIDTH-1:0] WriteDataE,   // Input for Write Data in Execute stage
    input  logic [4:0]       RdE,          // Input for Destination Register in Execute stage
    input  logic [WIDTH-1:0] PCPlus4E,     // Input for PC+4 in Execute stage
    output logic             RegWriteM,    // Output for RegWrite in Memory stage
    output logic [1:0]       ResultSrcM,   // Output for ResultSrc in Memory stage
    output logic             MemWriteM,    // Output for MemWrite in Memory stage
    output logic [WIDTH-1:0] ALUResultM,   // Output for ALU Result in Memory stage
    output logic [WIDTH-1:0] WriteDataM,   // Output for Write Data in Memory stage
    output logic [4:0]       RdM,          // Output for Destination Register in Memory stage
    output logic [WIDTH-1:0] PCPlus4M      // Output for PC+4 in Memory stage
);

    always_ff @(posedge clk, posedge reset) begin
        if (reset) begin
            RegWriteM   <= 0;
            ResultSrcM  <= 0;
            MemWriteM   <= 0;
            ALUResultM  <= 0;
            WriteDataM  <= 0;
            RdM         <= 0;
            PCPlus4M    <= 0;
        end else begin
            RegWriteM   <= RegWriteE;
            ResultSrcM  <= ResultSrcE;
            MemWriteM   <= MemWriteE;
            ALUResultM  <= ALUResultE;
            WriteDataM  <= WriteDataE;
            RdM         <= RdE;
            PCPlus4M    <= PCPlus4E;
        end
    end

endmodule


module reg6 #(parameter WIDTH = 32) (
    input  logic             clk,         // Clock signal
    input  logic             reset,       // Reset signal
    input  logic  RegWriteM,   // Input for RegWriteM
    input  logic  [1:0] ResultSrcM,  // Input for ResultSrcM
    input  logic [WIDTH-1:0] ALUResultM,  // Input for ALUResultM
    input  logic [WIDTH-1:0] ReadDataM,   // Input for ReadDataM
    input  logic [4:0] RdM,         // Input for RdM
    input  logic [WIDTH-1:0] PCPlus4M,    // Input for PCPlus4M
    output logic  RegWriteW,   // Output for RegWriteW
    output logic [1:0] ResultSrcW,  // Output for ResultSrcW
    output logic [WIDTH-1:0] ALUResultW,  // Output for ALUResultW
    output logic [WIDTH-1:0] ReadDataW,   // Output for ReadDataW
    output logic [4:0] RdW,         // Output for RdW
    output logic [WIDTH-1:0] PCPlus4W     // Output for PCPlus4W
);

    always_ff @(posedge clk, posedge reset) begin
        if (reset) begin
            RegWriteW   <= 0;
            ResultSrcW  <= 0;
            ALUResultW  <= 0;
            ReadDataW   <= 0;
            RdW         <= 0;
            PCPlus4W    <= 0;
        end else begin
            RegWriteW   <= RegWriteM;
            ResultSrcW  <= ResultSrcM;
            ALUResultW  <= ALUResultM;
            ReadDataW   <= ReadDataM;
            RdW         <= RdM;
            PCPlus4W    <= PCPlus4M;
        end
    end

endmodule


module mux2 #(parameter WIDTH = 8)
             (input  logic [WIDTH-1:0] d0, d1, 
              input  logic             s, 
              output logic [WIDTH-1:0] y);

  assign y = s ? d1 : d0; 
endmodule

module mux3 #(parameter WIDTH = 8)
             (input  logic [WIDTH-1:0] d0, d1, d2,
              input  logic [1:0]       s, 
              output logic [WIDTH-1:0] y);

  assign y = s[1] ? d2 : (s[0] ? d1 : d0); 
endmodule

module imem(input  logic [31:0] a,
            output logic [31:0] rd);

  logic [31:0] RAM[63:0];

  initial
      $readmemh("riscvtest.txt",RAM);

  assign rd = RAM[a[31:2]]; // word aligned
endmodule

module dmem(input  logic        clk, we,
            input  logic [31:0] a, wd,
            output logic [31:0] rd);

  logic [31:0] RAM[63:0];

  assign rd = RAM[a[31:2]]; // word aligned

  always_ff @(posedge clk)
    if (we) RAM[a[31:2]] <= wd;
endmodule

module alu(input  logic [31:0] a, b,
           input  logic [3:0]  alucontrol,
           output logic [31:0] result,
           output logic        zero,
           output logic less);

  logic [31:0] condinvb, sum;
  logic        v;              // overflow
  logic        isAddSub;       // true when is add or subtract operation

  assign condinvb = alucontrol[0] ? ~b : b;
  assign sum = a + condinvb + alucontrol[0];
  assign isAddSub = ~alucontrol[2] & ~alucontrol[1] |
                    ~alucontrol[1] & alucontrol[0];

  always_comb
    case (alucontrol)
      4'b0000:  result = sum;                 // add
      4'b0001:  result = sum;                 // subtract
      4'b0010:  result = a & b;               // and
      4'b0011:  result = a | b;               // or
      4'b0100:  result = a ^ b;               // xor
      4'b0101:  result = ($signed(a) < $signed(b)) ? 1 : 0; // slt
      4'b0110:  result = a <<< b;         // sll
      4'b0111:  result = a >>> b;         // srl
      4'b1000:  result = a >> b;        // sra
		4'b1001:  result = b; 
      default:   result = 32'b0;    endcase

  assign zero = (result == 32'b0);
  assign less = ($signed(a) < $signed(b));  // Signed comparison for blt
  assign v = ~(alucontrol[0] ^ a[31] ^ b[31]) & (a[31] ^ sum[31]) & isAddSub;
endmodule
