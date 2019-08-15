`include "library.sv"

module Driver();

    parameter ROWS = 1024;
    parameter COLS = 600;

    logic clock, reset_L, en;
    logic hsync, vsync, data_en;
    logic [7:0] R, G, B;
    logic [3:0] Q, Q_n;
    logic [$clog2(ROWS)-1:0] row;
    logic [$clog2(COLS)-1:0] col;

    HV_Mode #(.ROWS(ROWS), .COLS(COLS)) hv();
    Colorizer #(.ROWS(ROWS), .COLS(COLS)) c();
    LVDS_Data_Formmater df();

endmodule : Driver

module Colorizer
#(parameter ROWS,
  parameter COLS
)
(
    input logic [$clog2(ROWS)-1:0] row,
    input logic [$clog2(COLS)-1:0] col,
    output logic [7:0] R, G, B
);

    logic q0, q1, q2, q3, q4;

    Range r0(.low(0), .check(col), .high(120), .inBtwn(q0));
    Range r1(.low(121), .check(col), .high(240), .inBtwn(q1));
    Range r2(.low(241), .check(col), .high(360), .inBtwn(q2));
    Range r3(.low(361), .check(col), .high(480), .inBtwn(q3));
    Range r4(.low(481), .check(col), .high(600), .inBtwn(q4));

    always_comb begin
        if (q0) begin
            R = 8'b0;
            G = 8'b0;
            B = 8'b11111111;
        end else if (q1) begin
            R = 8'b11111111;
            G = 8'b0;
            B = 8'b11111111;
        end else if (q2) begin
            R = 8'b11111111;
            G = 8'b11111111;
            B = 8'b0;
        end else if (q3) begin
            R = 8'b11111111;
            G = 8'b0;
            B = 8'b0;
        end else if (q4) begin
            R = 8'b11111111;
            G = 8'b11111111;
            B = 8'b11111111;
        end else begin
            R = 8'b00000000;
            G = 8'b00000000;
            B = 8'b00000000;

        end
    end

endmodule : Colorizer;

module 3Wire();



endmodule : 3Wire

module PowerSeq();



endmodule : PowerSeq
