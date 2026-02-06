module checker_Rx (
input logic clk,
input logic Rx_dv,
input logic [7:0] Rx_byte,
input logic [7:0] expected_data
);
//kiểm tra 8-bit thu được
property Rx_test;
@(posedge clk)
Rx_dv |-> (Rx_byte == expected_data);
endproperty
test_1: assert property (Rx_test)
else $error("FAIL | Expected=%0h | Got=%0h", expected_data, Rx_byte);
endmodule
