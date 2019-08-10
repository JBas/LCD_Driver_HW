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
 )
(
    input logic clock, reset_L, en,
    output logic hsync, vsync, data_en
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
    
    assign wh = (hp > tWH);
    assign hbp = (hp > tWH) && (hp <= (tWH+tHBP));
    assign wha = (hp > (tWH+tHBP)) && (hp <= (tWH+tHBP+tWHA));
    assign hfp = (hp > (tWH+tHBP+tWHA));

    assign clear_vp = (vp == tVP);
    Counter #(.WIDTH($clog2(tVP))) vperiod(.clock, .reset_L, .clear(clear_vp),
                                         .en(hp == tHP), .incr(1'b1), .Q(vp));

    assign wv = (vp > tWV);
    assign vbp = (vp > tWV) && (vp <= (tWV+tVBP));
    assign wva = (vp > (tWV+tVBP)) && (vp <= (tWV+tVBP+tWVA));
    assign vfp = (vp > (tWV+tVBP+tWVA));

    assign hsync = wh | hbp | wha | hfp;
    assign vsync = wv | vbp | wva | vfp;

    assign data_en = hsync & vsync;

endmodule : HV_Mode

module HV_Mode_TB();
    logic clock, reset_L, en;
    logic hsync, vsync, data_en;

    HV_Mode_TB DUT(.*);

    initial begin
        clock = 'b0;
        reset_L = 'b1;
        en = 'b0;
        forever #10 clock = ~clock;
    end

    initial begin
        $dumpfile("dump.vcd");
        $dumpvars;
        #100;
        $finish();
    end

    // properties
    property data_en_prop;
        @(posedge clock) disable iff (~reset_L) data_en |-> (hsync && vsync);
    endproperty
    
    property contr_data_en_prop;
        @(posedge clock) disable iff (~reset_L) (hsync && vsync) |-> data_en;
    endproperty

    // assertions
    assert property (data_en_prop) else $display("data_en HIGH when both hsync and vsync NOT HIGHT!");
    assert property (contr_data_en_prop) else $display("data_en NOT HIGH when both hsync and vsync HIGHT!");

endmodule : HV_Mode_TB
