# README: Single-Cycle (Pipelined) RISC-V Processor

## Overview
This project implements a simplified RISC-V **RV32I** processor in SystemVerilog. Although the original label suggests “single-cycle,” the design is actually **pipelined** with multiple stages (Fetch, Decode, Execute, Memory, and Write-back) and includes hazard detection and forwarding logic. It is based on examples from *Digital Design and Computer Architecture* by Harris & Harris, adapted for RISC-V.

## Project Purpose
1. **Learn the RISC-V ISA**: Focus on integer instructions (`lw`, `sw`, arithmetic, immediate instructions, branches, jumps, etc.).
2. **Pipeline Design**: Explore a standard 5-stage pipeline (IF, ID, EX, MEM, WB) with hazard and forwarding units.
3. **SystemVerilog Practice**: Demonstrates module hierarchy, procedural blocks, testbenches, memory instantiation, and debugging strategies.

## Key Features

1. **Instruction Support**:
   - **Load/Store**: `lw`, `sw`
   - **Arithmetic**: `add`, `sub`, `and`, `or`, `xor`, `sll`, `srl`, `sra`, `slt`
   - **Immediate**: `addi`, `andi`, `ori`, `slti`
   - **Branch**: `beq`
   - **Jump**: `jal`
   - **LUI**: `lui`
   
2. **Pipeline Stages & Registers**:
   - **IF (Instruction Fetch)**
   - **ID (Decode)**
   - **EX (Execute)**
   - **MEM (Memory)**
   - **WB (Write-back)**
   
   Pipeline registers (`regDToE`, `regEToM`, `regMToW`) separate the stages, holding the necessary signals for each stage.

3. **Hazard Unit**:
   - **Load-Use**: Introduces a stall if the data needed in the EX stage is not yet available from a preceding load.
   - **Forwarding**: Forwards results from MEM/WB stages back to EX to minimize stalls.
   - **Branch/Jump Flush**: Flushes instructions in the pipeline when a taken branch or jump is detected to avoid using incorrect instructions.

4. **Register File**:
   - 32 registers (`x0`–`x31`), with **x0** hardwired to 0.
   - Written on the **falling edge** of the clock.

5. **Memory**:
   - **Instruction Memory** (`imem`): Loads instructions from `riscvtest.txt`.
   - **Data Memory** (`dmem`): Allows `lw` and `sw` instructions to read/write data.

## Simulation & Testing

### Testbench Behavior
1. **Resets** the processor for the first 22 time units.
2. **Generates** a regular clock (period of 10 time units).
3. **Monitors** writes to data memory:
   - Expects to see `25 (0x19)` written to address `100 (0x64)`.  
     - If so, prints **"Simulation succeeded"**.  
   - If any unexpected memory write occurs (to an address other than 96 or 100), the testbench prints **"Simulation failed"** and stops.

### How to Run
1. **Compile** `riscvsingle.sv` in your preferred simulator (e.g., QuestaSim, VCS, or Icarus Verilog).
2. **Place** `riscvtest.txt` in the same directory (or correct path) so that `imem` can load it.
3. **Simulate** the `testbench` module.
4. **Check** the console output for success or failure messages.
