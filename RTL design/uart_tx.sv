module uart_tx 
#(parameter CLK_PER_BIT=4) //số xung clock cho 1 bit UART
(
input logic clk,
input logic Tx_dv,//tín hiệu yêu cầu truyền 
input logic[7:0] Tx_Byte, //dữ liệu cần truyền (8 bit)
output logic o_Tx_Active,//cờ cho biết đang truyền dữ liệu
output logic Tx_Serial,//tín hiệu UART phát ra 
output logic o_Tx_Done //cờ báo đã truyền xong
);
//định nghĩa các trạng thái state FSM
localparam Tx_wait = 3'b000; //trạng thái chờ start bit
localparam Tx_start = 3'b001; //trạng thái phát start bit
localparam Tx_data_bit = 3'b010; //trạng thái phát các bit dữ liệu (8 bit)
localparam Tx_stop = 3'b011; //trạng thái phát stop bit
localparam Tx_clear = 3'b100; //hoàn tất, reset cờ và trở về trạng thái chờ 
// Các thanh ghi nội bộ
logic [7:0] clk_count = 0; //bộ đếm clock để canh thời điểm gửi mỗi bit
logic [2:0] Bit_Index = 0; //chỉ số bit đang truyền (0..7)
logic [7:0] Tx_data = 0; //lưu dữ liệu cần truyền
logic r_Tx_Done = 0; //báo hoàn tất truyền
logic r_Tx_Active = 0; //báo đang truyền
logic [2:0] Tx_state = 0; //trạng thái hiện tại của FSM  
//FSM truyền dữ liệu UART   
always @(posedge clk) begin
case (Tx_state)
//trạng thái chờ yêu cầu truyền
  Tx_wait: begin
   Tx_Serial <= 1'b1; //Tín hiệu ở mức cao khi chưa truyền dữ liệu
   r_Tx_Done <= 1'b0; //reset cờ báo hoàn tất
   clk_count <= 0; // Reset bộ đếm
   Bit_Index <= 0; // Reset chỉ số bit
	//khi có tín hiệu yêu cầu truyền
		if(Tx_dv == 1'b1) begin
      r_Tx_Active <= 1'b1; //cờ báo đang truyền bật lên 1
      Tx_data <= Tx_Byte; //lưu dữ liệu
      Tx_state <= Tx_start; //chuyển sang trạng thái gửi start bit
		end else begin
      Tx_state <= Tx_wait; //tiếp tục chờ
	   end
  end 
   //gửi start bit
  Tx_start: begin
   Tx_Serial <= 1'b0; //Start bit = 0
	//nếu chưa đủ thời gian gửi 1 bit
    if(clk_count < CLK_PER_BIT-1) begin
    clk_count <= clk_count + 1; //tiếp tục đếm
    Tx_state <= Tx_start;
    end else begin
    clk_count <= 0; //đủ thời gian truyền 1 bit, reset lại bộ đếm
    Tx_state <= Tx_data_bit; //chuyển sang trạng thái truyền dữ liệu
    end
  end 
 //Bắt đầu truyền bit      
  Tx_data_bit: begin
  Tx_Serial <= Tx_data[Bit_Index]; //Xuất bit dữ liệu hiện tại
	//nếu chưa đủ thời gian gửi 1 bit
	if(clk_count < CLK_PER_BIT-1) begin
   clk_count <= clk_count + 1; //tiếp tục đếm
   Tx_state <= Tx_data_bit;
   end else begin
   clk_count <= 0; //đủ thời gian truyền 1 bit, reset lại bộ đếm
		//kiểm tra xem đã truyền đủ 8 bit chưa
		if(Bit_Index < 7) begin
		Bit_Index <= Bit_Index + 1; //sang bit tiếp theo
		Tx_state <= Tx_data_bit; 
		end else begin
		// nếu đã truyền đủ 8 bit 
      Bit_Index <= 0; //reset lại chỉ số bit
      Tx_state <= Tx_stop; //chuyển sang trạng thái truyền stop bit
      end
    end
  end 
	//trạng thái truyền stop bit
   Tx_stop: begin
   Tx_Serial <= 1'b1; //Stop bit = 1
	 //nếu chưa đủ thời gian gửi 1 bit
    if (clk_count < CLK_PER_BIT-1) begin
    clk_count <= clk_count + 1; //tiếp tục đếm
    Tx_state <= Tx_stop;
    end else begin
    r_Tx_Done <= 1'b1; //báo truyền hoàn tất
    clk_count <= 0; //đủ thời gian truyền 1 bit, reset lại bộ đếm
    Tx_state <= Tx_clear; //sang trạng thái clear 
    r_Tx_Active <= 1'b0; //báo dừng truyền
    end
  end 
  //Hoàn thành truyền data    
  Tx_clear: begin
  r_Tx_Done <= 1'b1;//báo truyền hoàn tất
  Tx_state <= Tx_wait;//quay về trạng thái chờ truyền
  end
  
default: Tx_state <= Tx_wait; //trạng thái mặc định
endcase
end
assign o_Tx_Active = r_Tx_Active; //gán output cờ báo truyền
assign o_Tx_Done = r_Tx_Done; //gán output cờ báo hoàn tất  
endmodule





 