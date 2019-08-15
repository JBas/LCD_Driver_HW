/*
    Author: Joshua Bas
    Date: 8/9/2019
*/

`default_nettype none

module Register
#(parameter WIDTH=8)
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
#(parameter WIDTH=8,
  parameter STEP=1
 )
(
    input logic clock, reset_L, en, incr, clear,
    output logic [WIDTH-1:0] Q
);

    always_ff @(posedge clock, negedge reset_L) begin
        if (~reset_L) begin
            Q <= 'b0;
        end
        else if (clear) begin
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

module Range
#(parameter WIDTH=8)
(
    input logic [$clog2(WIDTH)-1:0] low, check, high,
    output logic inBtwn
);

    assign inBtwn = ((low <= check) && (check <= high));

endmodule : Range

module LVDS_Data_Formatter
(
    input logic clock, reset_L, en,
    input logic [7:0] R, G, B,
    input logic hsync, vsync, data_en,
    output logic [3:0] Q, Q_n
);

    logic RA, RB, RC, RD;

    Shift_Register #(.WIDTH(7)) ra(.clock, .reset_L, .en, .lshift(1'b1),
                                   .D({G[0], R[5], R[4], R[3], R[2], R[1], R[0]}),
                                   .Qm(RA));
    Shift_Register #(.WIDTH(7)) rb(.clock, .reset_L, .en, .lshift(1'b1),
                                   .D({B[1], B[0], G[5], G[4], G[3], G[2], G[1]}),
                                   .Qm(RB));
    Shift_Register #(.WIDTH(7)) rc(.clock, .reset_L, .en, .lshift(1'b1),
                                   .D({data_en, vsync, hsync, B[5], B[4], B[3], B[2]}),
                                   .Qm(RC));
    Shift_Register #(.WIDTH(7)) rd(.clock, .reset_L, .en, .lshift(1'b1),
                                   .D({1'bx, B[7], B[6], G[7], G[6], R[7], R[6]}),
                                   .Qm(RD));
    assign Q = {RA, RB, RC, RD};
    assign Q_n = ~Q;

endmodule : LVDS_Data_Formatter

module HV_Mode
#(parameter tHP=1344,   // units of clock
  parameter tWH=1,      // units of clock
  parameter tWHA=1024,  // units of clock
  parameter tVP=635,    // units of tHP
  parameter tWV=1,      // units of tHP
  parameter tWVA=600,   // units of tHP
  parameter tHBP=160,   // units of clock
  parameter tHFP=160,   // units of clock
  parameter tVBP=23,    // units of tHP
  parameter tVFP=12     // units of tHP
  parameter ROWS=1024,
  parameter COLS=600
 )
(
    input logic clock, reset_L, en,
    output logic hsync, vsync, data_en,
    output logic [ROWS-1:0] row,
    output logic [COLS-1:0] col
);

    logic [$clog2(tHP)-1:0] hp;
    logic [$clog2(tVP)-1:0] vp;
    logic wh, hbp, wha, hfp;
    logic wv, vbp, wva, vfp;

    logic clear_hp;
    logic clear_vp;

    assign clear_hp = (hp == tHP);
    Counter #(.WIDTH($clog2(tHP))) hperiod(.clock, .reset_L, .clear(clear_hp),
                                         .en, .incr(1'b1), .Q(hp));
    
    assign wh = (hp >= tWH);
    assign hbp = (hp > tWH) && (hp <= (tWH+tHBP));
    assign wha = (hp > (tWH+tHBP)) && (hp <= (tWH+tHBP+tWHA));
    assign hfp = (hp > (tWH+tHBP+tWHA));

    assign clear_vp = (vp == tVP);
    Counter #(.WIDTH($clog2(tVP))) vperiod(.clock, .reset_L, .clear(clear_vp),
                                         .en(hp == tHP), .incr(1'b1), .Q(vp));

    assign wv = (vp >= tWV);
    assign vbp = (vp > tWV) && (vp <= (tWV+tVBP));
    assign wva = (vp > (tWV+tVBP)) && (vp <= (tWV+tVBP+tWVA));
    assign vfp = (vp > (tWV+tVBP+tWVA));

    assign hsync = wh | hbp | wha | hfp;
    assign vsync = wv | vbp | wva | vfp;

    assign data_en = hsync & vsync;

    Counter #(.WIDTH(ROWS-1)) r(.clock, .reset_L, .clear(1'b0),
                                .en(clear_hp), .incr(1'b1), .Q(row));
    Counter #(.WIDTH(COLS-1)) c(.clock, .reset_L, .clear(1'b0),
                                .en(clear_vp), .incr(1'b1), .Q(col));
    
    // properties
    property data_en_prop;
        @(posedge clock) disable iff (~reset_L) data_en |-> (hsync && vsync);
    endproperty
    property contr_data_en_prop;
        @(posedge clock) disable iff (~reset_L) (hsync && vsync) |-> data_en;
    endproperty
    property hperiod_prop;
        @(posedge clock) disable iff (~reset_L) ((hp == 0) && (en)) |-> ##[1229:1372] (hp == 0);
    endproperty
    property vperiod_prop;
        @(posedge clear_hp) disable iff (~reset_L) ((vp == 0) && (en)) |-> ##[623:718] (vp == 0);
    endproperty
    
    // assertions
    assert property (data_en_prop) else $display("data_en HIGH when both hsync and vsync NOT HIGHT!");
    assert property (contr_data_en_prop) else $display("data_en NOT HIGH when both hsync and vsync HIGHT!");
    assert property (hperiod_prop) else $display("hperiod not within MIN/MAX!");
    assert property (vperiod_prop) else $display("vperiod not within MIN/MAX!");


endmodule : HV_Mode

module HV_Mode_TB();
    logic clock, reset_L, en;
    logic hsync, vsync, data_en;

    HV_Mode DUT(.*);

    initial begin
        clock = 'b0;
        reset_L = 'b0;
        en = 'b0;
        forever #10 clock = ~clock;
    end

    initial begin
        @(posedge clock);
        reset_L <= 'b1;
        en <= 'b1;
        repeat (855000) begin
          @(posedge clock);
        end
        $finish();
    end

endmodule : HV_Mode_TB
