vsim -gui work.tb_uart 
add wave  \
sim:/tb_uart/dut_rx/clk_count \
sim:/tb_uart/dut_rx/Bit_Index \
sim:/tb_uart/dut_rx/Rx_state
sim:/tb_uart/dut_tx/clk_count \
sim:/tb_uart/dut_tx/Bit_Index \
sim:/tb_uart/dut_tx/Tx_state
vsim -coverage -gui work.tb_uart
run -all
coverage report -summary
coverage report -codeAll -details
coverage report -cvg -verbose
