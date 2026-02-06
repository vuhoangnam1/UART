module uart_rx
#(parameter CLK_PER_BIT=4) //số xung clock cho 1 bit UART
(
input logic clk, 
input logic Rx_serial, //dữ liệu UART đầu vào 
output logic Rx_dv,  //data valid báo một byte mới đã được nhận 
output logic [7:0] Rx_byte  //byte dữ liệu nhận được (8 bit)
);
//định nghĩa các trạng thái state FSM
localparam Rx_wait = 3'b000; //trạng thái chờ start bit
localparam Rx_start = 3'b001; //trạng thái nhận start bit 
localparam Rx_data_bit = 3'b010; //trạng thái nhận các bit dữ liệu (8 bit)
localparam Rx_stop = 3'b011; //trạng thái nhận stop bit
localparam Rx_clear = 3'b100; //hoàn tất, reset cờ và trở về trạng thái chờ 
// Các thanh ghi nội bộ
logic Rx_data_i = 1'b1; //giữ mẫu đầu tiên từ Rx_serial
logic Rx_data = 1'b1; //dữ liệu đã ổn định, dùng cho FSM
logic [7:0] clk_count = 0; //bộ đếm clock để canh thời điểm lấy mẫu mỗi bit
logic [2:0] Bit_Index = 0; //chỉ số bit đang nhận
logic [7:0] Rx_Byte = 0; //lưu tạm byte dữ liệu đang nhận
logic       Rx_DV = 0; //Data Valid nội bộ
logic [2:0] Rx_state = 0; //trạng thái hiện tại của FSM

assign Rx_dv = Rx_DV; //gán output DV
assign Rx_byte = Rx_Byte; //gán output dữ liệu
// Đồng bộ tín hiệu serial vào với clock hệ thống 
always_ff @(posedge clk) begin
 Rx_data_i <= Rx_serial;
 Rx_data <= Rx_data_i;
end
//FSM nhận dữ liệu UART
always_ff @(posedge clk) begin
	case(Rx_state) //truy cập vào các trạng thái
	Rx_wait: begin //chờ start bit
	Rx_DV  <= 1'b0; //reset cờ báo dữ liệu hợp lệ
   clk_count <= 0;    //reset bộ đếm clock
   Bit_Index   <= 0;    //reset chỉ số bit đang nhận
    if (Rx_data == 1'b0) //phát hiện mức thấp đi vào trạng thái nhận start bit
    Rx_state <= Rx_start; 
	 else 
	 Rx_state <= Rx_wait; //UART chưa nhận được tín hiệu serial báo nhận start bit, tiếp tục chờ
	end

	Rx_start: begin //kiểm tra start bit
	//lấy mẫu giữa bit start để tránh sai lệch
	if(clk_count == ((CLK_PER_BIT-1)/2)) begin
			if(Rx_data==1'b0) begin //nhận được start bit là 0, hợp lệ
			clk_count <= 0;        //reset đếm
         Rx_state <= Rx_data_bit; //chuyển sang trạng thái nhận data bit
          end else
            Rx_state <= Rx_wait; // Nếu không phải 0 quay về về trạng thái chờ
        end else begin //nếu chưa đủ chu kì clock
          clk_count <= clk_count + 1; //chưa đủ chu kì nhận 1 bit, tiếp tục đếm
			 Rx_state <=Rx_start; //quay lại start
			end
		end
		
	Rx_data_bit: begin //nhận từng bit dữ liệu
	if (clk_count < CLK_PER_BIT-1) begin
          clk_count <= clk_count + 1; //chưa đủ chu kì nhận 1 bit, tiếp tục đếm
			 Rx_state   <= Rx_data_bit; //quay lại kiểm tra Rx_data_bit
        end else begin
          clk_count <= 0; //reset đếm sau nhận mỗi 1 bit
          Rx_Byte[Bit_Index] <= Rx_data; //lưu giá trị bit vào byte
          if (Bit_Index < 7) begin
            Bit_Index <= Bit_Index + 1; //nhận bit tiếp theo
				Rx_state   <= Rx_data_bit; //quay lại kiểm tra Rx_data_bit kế tiếp
          end else begin
            Bit_Index <= 0; //nhận xong 8 bit, reset lại số bit về 0
            Rx_state   <= Rx_stop; //trạng thái nhận stop bit
          end
        end
      end
	Rx_stop: begin //nhận stop bit 
		if (clk_count < CLK_PER_BIT-1) begin
          clk_count <= clk_count + 1; //chưa đủ chu kì nhận 1 bit, tiếp tục đếm
			 Rx_state   <= Rx_stop; //quay lại kiểm tra Rx_stop
        end else begin
          Rx_DV <= 1'b1; //báo dữ liệu hợp lệ
          clk_count <= 0; //Reset đếm
          Rx_state  <= Rx_clear; // Sang clear
        end
      end
	//Hoàn thành thu data	
	Rx_clear: begin 
	Rx_state <= Rx_wait; //về trạng thái chờ
	Rx_DV  <= 1'b0; //đặt lại Rx_DV
	end
default:Rx_state <= Rx_wait; //trạng thái mặc định
endcase
end
endmodule





 