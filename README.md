# UART
# UART RTL Design and Testbench Verification

## Overview
This project implements a **UART 8-bit(Universal Asynchronous Receiver/Transmitter)** system using SystemVerilog.
The design includes both **transmitter (TX)** and **receiver (RX)** modules, along with a **self-checking testbench** for functional verification.

The project focuses on understanding UART protocol behavior and verifying correct data transmission and reception.

---

## UART Features
- Asynchronous serial communication
- Configurable baud rate
- Start bit, data bits, and stop bit handling
- Independent transmitter and receiver modules

---

## Design Modules
- uart_tx: Handles serial transmission of parallel data

- uart_rx: Receives serial data and converts it to parallel form

- uart_top 
  Integrates UART transmitter and receiver

---

## Testbench
The testbench is written using **SystemVerilog** and includes:

- Clock and reset generation
- Random stimulus generation for UART TX
- Serial data driving for UART RX testing
- TX-to-RX loopback verification
- Back-to-back transmission and reception testing
- Output monitoring and result checking
- Functional coverage collection for UART TX/RX 

---

## Simulation
- Simulator: ModelSim / Quartus
- Language: SystemVerilog

### How to Run
1. Compile RTL and testbench files
2. Run Makefile
3. Observe waveform and console output to verify correctness

---

## Project Scope
- RTL implementation of UART TX and RX
- Functional verification using a traditional testbench
- No UVM methodology is used in this project

---

## Author
Vu Hoang Nam  
Design Verification

