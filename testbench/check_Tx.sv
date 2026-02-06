module checker_Tx (
input logic clk,
input logic o_Tx_Done,
input logic [7:0] Tx_Byte,
input logic [7:0] expected_data
);
//kiểm tra 8-bit thu được
property Tx_test;
Tx_dv = 1'b0;
o_Tx_Done |-> (Tx_Byte == expected_data);
endproperty
test_2: assert property (Tx_test)
else $error("FAIL | sent=%0h | Expected=%0h",Tx_Byte, expected_data);
endmodule
