module tb_uart;
parameter CLK_PERIOD_NS=400; //Fclk=1Mhz
parameter BIT_PERIOD = 1600; // thời gian kéo dài của 1 bit UART
parameter CLK_PER_BIT = 4; //số xung clock cho 1 bit UART
logic clk;
logic [7:0] expected_data;
//Rx
logic Rx_dv;
logic [7:0] Rx_byte;
logic Rx_serial;
//Tx
logic Tx_dv;
logic o_Tx_Active;
logic Tx_Serial;
logic o_Tx_Done;
logic [7:0] Tx_Byte;
//interface tb với dut_Rx
uart_rx #(.CLK_PER_BIT(CLK_PER_BIT)) dut_rx(
.clk(clk),
.Rx_dv(Rx_dv),
.Rx_byte(Rx_byte),
.Rx_serial(Rx_serial)
);

//interface tb với dut_Tx
uart_tx #(.CLK_PER_BIT(CLK_PER_BIT)) dut_tx(
.clk(clk),
.Tx_dv(Tx_dv),
.o_Tx_Active(o_Tx_Active),
.Tx_Serial(Tx_Serial),
.o_Tx_Done(o_Tx_Done),
.Tx_Byte(Tx_Byte)
);

drive_Rx drv1(.clk(clk),.Rx_serial(Rx_serial),.Rx_byte(Rx_byte));
drive_Tx drv2(.clk(clk),.Tx_dv(Tx_dv),.Tx_Byte(Tx_Byte));
monitor_Tx mon1(.clk(clk),.Tx_dv(Tx_dv),.Tx_Byte(Tx_Byte),.Tx_Serial(Tx_Serial),.o_Tx_Done(o_Tx_Done));
monitor_Rx mon2(.clk(clk),.Rx_dv(Rx_dv),.Rx_byte(Rx_byte));
checker_Tx chk1(.clk(clk),.Tx_Byte(Tx_Byte),.expected_data(expected_data),.o_Tx_Done(o_Tx_Done));
checker_Rx chk2(.clk(clk),.Rx_Byte(Rx_Byte),.expected_data(expected_data),.Rx_dv(Rx_dv));
initial begin
//kiểm tra các giá trị data ngẫu nhiên
repeat (10) begin
$display("//////////////////////////////////////////////////////////////////////////////////////////////////////////////////");
expected_data = $urandom_range(8'h00, 8'hFF));
repeat (2)@(posedge clk);
end
$stop;
end
endmodule
