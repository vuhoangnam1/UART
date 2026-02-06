module Check_Tx_to_Rx(
input logic clk,
input logic o_Tx_Done,
input logic [7:0] Tx_byte,
input logic [7:0] expected_data
input logic Rx_dv,
input logic [7:0] Rx_byte
);
property Tx_t;
@(posedge clk)
o_Tx_Done |-> (Tx_byte == expected_data);
endproperty
test3: assert property (Tx_t)
else $error("FAIL: Sent=%0h | Expected=%0h", Tx_byte, expected_data);

property Rx_t;
@(posedge clk)
Rx_dv |-> (Rx_byte == expected_data);
endproperty
test_4: assert property (Rx_t)
else $error("FAIL | Expected=%0h | Got=%0h", expected_data, Rx_byte);
endmodule