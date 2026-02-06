module monitor_Tx(
input logic clk,
input logic Tx_dv,
input logic Tx_Serial,
input logic o_Tx_Done,
input logic [7:0] Tx_Byte
);
always_ff @(posedge o_Tx_Done) begin
$display("//////////////////////////////////////////////");
$display("PASS | Tx_data %0h ",Tx_Byte);
end
endmodule
