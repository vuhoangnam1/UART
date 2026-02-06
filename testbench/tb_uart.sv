module tb_uart;
parameter CLK_PERIOD_NS=4; //Khoảng thời gian cho 1 chu kì clock (250MHz)
parameter BIT_PERIOD = 16; // thời gian kéo dài của 1 bit UART
parameter CLK_PER_BIT = 4; //số xung clock cần cho 1 bit UART
int i; //biến đếm vòng lặp
int j; //biến đếm vòng lặp
logic clk;
//các tín hiệu kết nối UART_RX
logic Rx_dv; //báo hiệu vừa nhận xong một byte
logic [7:0] Rx_byte; //dữ liệu mà UART_RX nhận được
logic Rx_serial; //đường tín hiệu UART input (đi từ testbench sang UART_RX)
//các tín hiệu kết nối UART_TX
logic Tx_dv; //báo hiệu yêu cầu UART_TX bắt đầu phát
logic o_Tx_Active; //cờ báo đang trong quá trình truyền
logic Tx_Serial; //đường tín hiệu UART output (đi từ UART_TX sang testbench)
logic o_Tx_Done; //cờ báo truyền hoàn tất
logic [7:0] Tx_Byte; //dữ liệu sẽ phát qua UART_TX
//mảng dữ liệu dùng test back-to-back
//mảng dữ liệu phát liên tục qua UART_TX 
logic [7:0] back_to_back_Tx_data[0:4] = '{8'h11, 8'h22, 8'h33, 8'h44, 8'h55};
//mảng dữ liệu thu liên tục vào UART_RX 
logic [7:0] back_to_back_Rx_data[0:4] = '{8'hA2, 8'h38, 8'hFF, 8'h3D, 8'h7A};

//kết nối testbench với DUT UART_RX
uart_rx #(.CLK_PER_BIT(CLK_PER_BIT)) dut_rx(
.clk(clk),
.Rx_dv(Rx_dv), //cờ data valid từ RX (output của DUT)
.Rx_byte(Rx_byte),  //byte dữ liệu nhận được (output của DUT)
.Rx_serial(Rx_serial) //dây serial đầu vào RX (input của DUT)
);

//kết nối testbench với DUT UART_TX
uart_tx #(.CLK_PER_BIT(CLK_PER_BIT)) dut_tx(
.clk(clk),
.Tx_dv(Tx_dv), //cờ yêu cầu phát (input vào DUT)
.o_Tx_Active(o_Tx_Active), //cờ báo đang truyền (output của DUT)
.Tx_Serial(Tx_Serial), //dây serial đầu ra TX (output của DUT)
.o_Tx_Done(o_Tx_Done), //cờ báo đã phát xong (output của DUT)
.Tx_Byte(Tx_Byte) //dữ liệu cần phát (input vào DUT)
);
//tạo chu kỳ xung clock
always #(CLK_PERIOD_NS/2) clk=~clk;

//Kiểm tra dữ liệu do UART_TX phát ra
task check_Tx(input logic [7:0] data);
begin
$display("kiem tra uart_Tx phat 8-bit %02h",data);
//gửi dữ liệu và start bit
Tx_Byte = data;
//Tx_dv = 1 trong 1 chu kỳ để bắt đầu phát
Tx_dv = 1'b1;
@(posedge clk);
//Tx_dv về 0 (chỉ cần xung 1 chu kỳ)
Tx_dv = 1'b0;
//chờ bắt đầu truyền (o_Tx_Active lên 1)
//đợi đến khi TX báo đang truyền
@(posedge o_Tx_Active);
$display("Bat dau phat %02h", data);

//đợi báo đã phát xong byte (kết thúc stop bit)
@(posedge o_Tx_Done);
$display("PASS | uart da phat %02h | o_Tx_Done = %0d",Tx_Byte, o_Tx_Done);

//thêm 2 chu kỳ clock làm khoảng đệm giữa các test
repeat(2) @(posedge clk);
end
endtask

//Kiểm tra dữ liệu UART_TX thu được
task check_Rx(input logic [7:0] data);
begin
i=0;
$display("kiem tra uart_Rx thu 8-bit %02h",data);
//Rx ở trạng thái chờ
Rx_serial =1;
repeat(2) @(posedge clk); // Đợi ổn định
//nhận start bit
Rx_serial =0;
//giữ start bit trong đúng thời gian 1 bit
#(BIT_PERIOD);
//vòng lặp phát 8 data bit (LSB trước)
for(i=0;i<8;i++) begin
Rx_serial = data[i]; //xuất từng bit của data vào Rx_serial
//giữ start bit trong đúng thời gian 1 bit
#(BIT_PERIOD);
end
//nhận stop bit
Rx_serial =1;
//chờ báo nhận hợp lệ, kết thúc nhận bit
@(posedge Rx_dv);
//so sánh byte RX nhận được với dữ liệu và in ra kết quả
if(Rx_byte == data)
$display("PASS | thu thanh cong %02h",Rx_byte);
else
$display("FAIL | thu khong thanh cong, nhan %02h, ky vong %02h",Rx_byte, data);
end
//thêm 2 chu kỳ clock làm khoảng đệm giữa các test
#(BIT_PERIOD);
endtask

//Kiểm tra trường hợp phát dữ liệu xong thu lại dữ liệu đó
task check_Tx_to_Rx(input logic [7:0] data);
time t_start_tx; //thời gian start bit của uart_tx
time t_stop_tx; //thời gian stop bit của uart_tx
time t_start_rx; //thời gian start bit của uart_rx
time t_stop_rx; //thời gian stop bit của uart_rx
begin
$display("kiem tra phat 8-bit roi lai thu 8-bit %02h",data);
//nạp dữ liệu cho TX
Tx_Byte = data;
//Tx_dv = 1 trong 1 chu kỳ để bắt đầu phát
Tx_dv = 1'b1;
//kết nối Tx output với Rx input
//mỗi khi Tx_Serial thay đổi thì gán trực tiếp sang Rx_serial
 fork
   forever @(Tx_Serial)
   Rx_serial = Tx_Serial;
   join_none
// Đợi 1 cạnh clock để đảm bảo Tx_dv đã được chốt
@(posedge clk);
//Tx_dv về 0
Tx_dv = 1'b0;
//thời điểm start bit Tx
//Khi Tx_Serial =0 sẽ báo đi vào trạng thái start-bit 
@(negedge Tx_Serial);
t_start_tx = $time;
$display("Thoi gian uart_tx start bit t=%0t",t_start_tx);
//bắt đầu thu dữ liệu đã phát
//thời điểm start bit Rx
t_start_rx = $time;
$display("Thoi gian uart_rx start bit t=%0t",t_start_rx);
//thời điểm báo stop bit
@(posedge o_Tx_Done);
t_stop_tx = $time;
$display("Thoi gian uart_tx stop bit t=%0t",t_stop_tx);
//thời điểm báo stop bit
@(posedge Rx_dv);
t_stop_rx = $time;
$display("Thoi gian uart_rx stop bit t=%0t",t_stop_rx);
repeat (2)@(posedge clk);
//Kiểm tra dữ liệu thu được từ dữ liệu phát
if(Rx_byte == data)
$display("PASS | Tx_data %02h | Rx_data %02h",Tx_Byte,Rx_byte);
else 
$display("FAIL | Tx_data %02h | Rx_data %02h",Tx_Byte,Rx_byte);
//Kiểm tra thời gian phát start bit - stop bit (tổng 10-bit)
if((t_stop_tx - t_start_tx) <= (10 * BIT_PERIOD))
$display("PASS | thoi gian phat timing chinh xac %0t ns", t_stop_tx - t_start_tx);
else
$display("FAIL | thoi gian phat timing khong chinh xac %0t ns", t_stop_tx - t_start_tx);
//Kiểm tra thời gian thu start bit - stop bit (tổng 10-bit)
if((t_stop_rx - t_start_rx) >= (10 * BIT_PERIOD))
$display("PASS | thoi gian thu timing chinh xac %0t ns", t_stop_rx - t_start_rx);
else
$display("FAIL | thoi gian thu timing khong chinh xac %0t ns", t_stop_rx - t_start_rx);
end
endtask

//Task kiểm tra truyền back-to-back nhiều byte (không chờ o_Tx_Done giữa các lần)
task check_back_to_back_Tx(input logic [7:0] data_array[], input int n);
begin
i=0;
$display("Kiem tra back-to-back UART TX");
  for(i =0; i<n;i++) begin
   Tx_Byte = data_array[i];
   Tx_dv = 1'b1;
   @(posedge clk);
   Tx_dv = 1'b0;
   //chờ TX bắt đầu truyền
   @(posedge o_Tx_Active);
   $display("uart_Tx dang phat byte %0d = %02h",i,Tx_Byte);
   //chờ hoàn thành truyền byte này
   @(posedge o_Tx_Done);
	$display("PASS | uart_Tx phat dung byte %0d = %02h",i,Tx_Byte);
   //thêm 2 chu kỳ clock làm khoảng đệm giữa các byte
   repeat(2) @(posedge clk);
  end
$display("Back-to-back TX test xong");
end
endtask

//Task kiểm tra thu back-to-back nhiều byte 
task check_back_to_back_Rx(input logic [7:0] data_array[], input int n);
begin
i=0;
j=0;
$display("Kiem tra back-to-back UART RX");
//Rx ở trạng thái chờ
Rx_serial =1'b1;
repeat(4) @(posedge clk);  //đợi ổn định
	for(i=0;i<n;i++) begin
	//nhận start bit
	Rx_serial =1'b0;
	#(BIT_PERIOD);
		for(j=0;j<8;j++) begin
		Rx_serial = data_array[i][j];
		#(BIT_PERIOD);
		end
	//nhận stop bit
	Rx_serial =1'b1;
	//chờ báo nhận hợp lệ, kết thúc nhận bit
	@(posedge Rx_dv);
	if(Rx_byte == data_array[i])
	 $display("PASS | Rx thu dung byte %0d = %02h", i, Rx_byte);
	else
	$display("FAIL | Rx sai byte %0d | thu duoc %02h | ky vong %02h", i, Rx_byte, data_array[i]);
	end
	$display("Back-to-back RX test xong");
	#(BIT_PERIOD*2);
end
endtask

//function coverage
covergroup cvg@(posedge clk);
//coverpoint cho Tx
cvgp_Tx_Byte: coverpoint Tx_Byte{
bins value ={[0:255]};
}
cvgp_Tx_dv: coverpoint Tx_dv{
bins begin_start ={0};
bins wait_Tx ={1};
}
cvgp_Tx_Done: coverpoint o_Tx_Done{
bins done = {1'b1};
bins not_done = {1'b0};
}
cvgp_Tx_Active: coverpoint o_Tx_Active{
bins transmit = {1'b1};
bins not_transmit = {1'b0};
}
//coverpoint cho Rx
cvgp_Rx_byte: coverpoint Rx_byte{
bins value ={[0:255]};
}
cvgp_Rx_dv: coverpoint Rx_dv{
bins begin_start ={0};
bins wait_Rx ={1};
}
// Cross coverage giữa dữ liệu phát và dữ liệu nhận
cross_Rx_Tx: cross cvgp_Tx_Byte, cvgp_Rx_byte;
//Cross coverage giữa Tx
cross_Tx: cross cvgp_Tx_Byte, cvgp_Tx_dv,cvgp_Tx_Done,cvgp_Tx_Active;
//Cross coverage giữa Rx
cross_Rx: cross cvgp_Rx_byte, cvgp_Rx_dv;
endgroup
// Khai báo một biến tên là cp thuộc kiểu covergroup cvg
cvg cp; 
always @(posedge clk) begin
  cp.sample(); // Thu thập coverage mỗi xung clock
end

initial begin
clk=0;
cp = new();
//Tx ở trạng thái chờ
Tx_dv = 0;
Tx_Byte = 0;
//kiểm tra các giá trị data ngẫu nhiên
//kiểm tra uart_Tx
$display("=== BAT DAU TEST UART ===");
repeat (5) begin
check_Tx($urandom_range(8'h00, 8'hFF));
repeat (2)@(posedge clk);
end
$display("uart_Tx test xong");
$display("//////////////////////////////////////////////////////////////////////////////////////////////////////////////////");
//kiểm tra uart_Rx
repeat (5) begin
check_Rx($urandom_range(8'h00, 8'hFF));
repeat (2)@(posedge clk);
end
$display("uart_Rx test xong");
$display("//////////////////////////////////////////////////////////////////////////////////////////////////////////////////");
//kiểm tra uart_Rx
repeat (5) begin
check_Tx_to_Rx($urandom_range(8'h00, 8'hFF));
$display("==================================================================================================================");
repeat (2)@(posedge clk);
end
$display("Tx_to_Rx test xong");
$display("//////////////////////////////////////////////////////////////////////////////////////////////////////////////////");
// Kiểm tra back-to-back uart_Tx (truyền liên tục 5 byte)
check_back_to_back_Tx(back_to_back_Tx_data, 5);
$display("==================================================================================================================");
// Kiểm tra back-to-back uart_Rx (truyền liên tục 5 byte)
check_back_to_back_Rx(back_to_back_Rx_data, 5);
$display("//////////////////////////////////////////////////////////////////////////////////////////////////////////////////");
$display("Coverage = %0.2f%%", cp.get_coverage());
$display("kiem tra hoan tat");
$stop;
end
endmodule
