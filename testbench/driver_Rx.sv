module driver_Rx(
output logic clk,
output logic Rx_serial,
output logic [7:0] Rx_byte
);
localparam CLK_PERIOD_NS=400; //Fclk=1Mhz
localparam BIT_PERIOD = 1600; // thời gian kéo dài của 1 bit UART
localparam CLK_PER_BIT = 4; //số xung clock cho 1 bit UART
always #(CLK_PERIOD_NS/2) clk=~clk;
initial begin
clk=0;
Rx_byte=0;
//tín hiệu bắt đầu start bit
Rx_serial=0;
end
endmodule
