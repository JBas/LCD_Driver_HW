/*
    Author: Joshua Bas
    Date: 8/9/2019
*/

`default_nettype none

module Register
#(parameter WIDTH 8)
(
    input logic clock, reset_L, en,
    input logic [WIDTH-1:0] D,
    output logic [WIDTH-1:0] Q
);

    always_ff @(posedge clock, negedge reset_L) begin
        if (~reset_L) begin
            Q <= 'b0;
        end
        else if (en) begin
            Q <= D;
        end
    end

endmodule : Register

module Counter
#(parameter WIDTH 8,
  parameter STEP 1
 )
(
    input logic clock, reset_L, en, incr,
    output logic [WIDTH-1:0] Q
);

    always_ff @(posedge clock, negedge reset_L) begin
        if (~reset_L) begin
            Q <= 'b0;
        end
        else if (en) begin
            if (incr) begin
                Q <= Q + STEP;
            end
            else begin
                Q <= Q - STEP;
            end
        end
    end

endmodule : Counter

module HV_Mode
#(parameter tHP 1344,   // units of clock
  parameter tWH 1,      // units of clock
  parameter tWHA 1024,  // units of clock
  parameter tVP 635,    // units of tHP
  parameter tWV 1,      // units of tHP
  parameter tWVA 600,   // units of tHP
  parameter tHBP 160,   // units of clock
  parameter tHFP 160,   // units of clock
  parameter tVBP 23,    // units of tHP
  parameter tVFP 12     // units of tHP
 )
(
    input logic clock, reset_L, en,
    output logic hsync, vsync, data_en
);

    logic [tHP-1:0] hp;
    logic [tVP-1:0] vp;
    logic [tWH-1:0] wh;
    logic [tWV-1:0] wv;
    logic [tWHA-1:0] wha;
    logic [tWVA-1:0] wva;

    Counter #(WIDTH=$clog2(tHP)) hperiod(.clock, .reset_L,
                                         .en, .incr('b1), .Q(hp));
    Counter #(WIDTH=$clog2(tVP)) vperiod(.clock, .reset_L,
                                         .en(hp == tHP), .incr('b1), .Q(vp));
    
    Counter #(WIDTH=$clog2(tWH)) hwidth(.clock, .reset_L,
                                         .en, .incr('b1), .Q(wh));
    Counter #(WIDTH=$clog2(tWV)) vwidth(.clock, .reset_L,
                                         .en(hp == tWV), .incr('b1), .Q(wv));
    
    Counter #(WIDTH=$clog2(tWHA)) hwidtha(.clock, .reset_L,
                                         .en, .incr('b1), .Q(wha));
    Counter #(WIDTH=$clog2(tWVA)) vwidtha(.clock, .reset_L,
                                         .en(hp == tWVA), .incr('b1), .Q(wva));

    assign data_en = hsync && vsync;

endmodule : HV_Mode
