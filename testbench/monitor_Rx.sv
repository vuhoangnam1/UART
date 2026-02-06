module monitor_Rx(
input logic Rx_dv,
input logic [7:0] Rx_byte
);
always_ff @(posedge Rx_dv) begin
$display("//////////////////////////////////////////////");
$display("PASS | Rx_data %0h ",Rx_byte);
end
endmodule
