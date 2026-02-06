module driver_Tx(
output logic clk,
output logic Tx_dv,
output logic [7:0] Tx_Byte
);
localparam CLK_PERIOD_NS=400; //Fclk=1Mhz
localparam BIT_PERIOD = 1600; // thời gian kéo dài của 1 bit UART
localparam CLK_PER_BIT = 4; //số xung clock cho 1 bit UART
always #(CLK_PERIOD_NS/2) clk=~clk;
initial begin
clk=0;
Tx_Byte = 0;
//tín hiệu bắt đầu start bit
Tx_dv = 1;
@(posedge clk);
Tx_dv = 1'b0;
end
endmodule
