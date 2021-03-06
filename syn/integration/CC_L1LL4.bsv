import Vector::*;
import BuildVector::*;
import FIFO::*;
import FIFOF::*;
import RWBramCore::*;
import SpecialFIFOs::*;
import HCCIfc::*;

interface CC;
    interface Vector#(L1Num, MemRqRs#(Struct1)) l1Ifc;
    interface DMA#(Bit#(14), Struct32, Vector#(4, Bit#(64))) llDma;
endinterface

typedef struct { Bit#(6) id; Bool type_; Bit#(64) addr; Vector#(4, Bit#(64)) value;  } Struct1 deriving(Eq, Bits);
typedef struct { Bool mesi_owned; Bit#(3) mesi_status; Bit#(3) mesi_dir_st; Bit#(4) mesi_dir_sharers;  } Struct10 deriving(Eq, Bits);
typedef struct { Bit#(64) mv_addr; Struct10 mv_info;  } Struct11 deriving(Eq, Bits);
typedef struct { Struct6 lr_ir_pp; Struct9 lr_ir; Vector#(4, Bit#(64)) lr_value;  } Struct12 deriving(Eq, Bits);
typedef struct { Bool victim_valid; Bit#(64) victim_addr; Struct10 victim_info; Vector#(4, Bit#(64)) victim_value; Bool victim_req;  } Struct13 deriving(Eq, Bits);
typedef struct { Bool m_is_ul; Bit#(4) m_qidx; Bool m_rsb; Bit#(4) m_dl_rss_from; Bit#(4) m_dl_rss_recv;  } Struct14 deriving(Eq, Bits);
typedef struct { Bit#(3) dir_st; Bit#(2) dir_excl; Bit#(4) dir_sharers;  } Struct15 deriving(Eq, Bits);
typedef struct { Bit#(64) addr; Bool info_write; Bool info_hit; Bit#(4) info_way; Bool edir_hit; Bit#(3) edir_way; Struct5 edir_slot; Struct10 info; Bool value_write; Vector#(4, Bit#(64)) value; Struct11 may_victim; Vector#(16, Bit#(8)) reps;  } Struct16 deriving(Eq, Bits);
typedef struct { Bit#(3) victim_idx; Struct10 victim_info; Vector#(4, Bit#(64)) victim_value;  } Struct17 deriving(Eq, Bits);
typedef struct { Bit#(2) enq_type; Bit#(2) enq_ch_idx; Struct1 enq_msg;  } Struct18 deriving(Eq, Bits);
typedef struct { Bit#(3) r_id; Bool r_ul_rsb; Bit#(2) r_ul_rsbTo;  } Struct19 deriving(Eq, Bits);
typedef struct { Struct1 in_msg; Bit#(4) in_msg_from;  } Struct2 deriving(Eq, Bits);
typedef struct { Bit#(3) r_id; Bit#(4) r_dl_rss_from; Bool r_dl_rsb; Bit#(4) r_dl_rsbTo;  } Struct20 deriving(Eq, Bits);
typedef struct { Bit#(4) cs_inds; Struct1 cs_msg;  } Struct21 deriving(Eq, Bits);
typedef struct { Bit#(4) cidx; Struct1 msg;  } Struct22 deriving(Eq, Bits);
typedef struct { Bit#(3) r_id; Bit#(4) r_dl_rss_from;  } Struct23 deriving(Eq, Bits);
typedef struct { Bit#(49) tag; Struct10 value;  } Struct24 deriving(Eq, Bits);
typedef struct { Bool tm_hit; Bit#(4) tm_way; Struct10 tm_value;  } Struct25 deriving(Eq, Bits);
typedef struct { Bit#(49) tag; Struct27 value;  } Struct26 deriving(Eq, Bits);
typedef struct { Bool mesi_edir_owned; Bit#(3) mesi_edir_st; Bit#(4) mesi_edir_sharers;  } Struct27 deriving(Eq, Bits);
typedef struct { Bool tm_hit; Bit#(3) tm_way; Struct27 tm_value;  } Struct28 deriving(Eq, Bits);
typedef struct { Bit#(10) addr; Struct24 datain;  } Struct29 deriving(Eq, Bits);
typedef struct { Bit#(3) r_id; Struct1 r_msg; Bit#(4) r_msg_from;  } Struct3 deriving(Eq, Bits);
typedef struct { Bit#(1) acc_type; Vector#(16, Bit#(8)) acc_reps; Bit#(10) acc_index; Bit#(4) acc_way;  } Struct30 deriving(Eq, Bits);
typedef struct { Bit#(10) addr; Struct26 datain;  } Struct31 deriving(Eq, Bits);
typedef struct { Bit#(14) addr; Vector#(4, Bit#(64)) datain;  } Struct32 deriving(Eq, Bits);
typedef struct { Bool valid; Struct13 data;  } Struct33 deriving(Eq, Bits);
typedef struct { Bit#(10) addr; Vector#(16, Bit#(8)) datain;  } Struct34 deriving(Eq, Bits);
typedef struct { Bit#(2) r_id; Struct1 r_msg; Bit#(4) r_msg_from;  } Struct35 deriving(Eq, Bits);
typedef struct { Bool s_has_slot; Bool s_conflict; Bit#(2) s_id;  } Struct36 deriving(Eq, Bits);
typedef struct { Bool valid; Bit#(1) data;  } Struct37 deriving(Eq, Bits);
typedef struct { Bool ir_is_rs_rel; Struct1 ir_msg; Bit#(4) ir_msg_from; Bit#(2) ir_mshr_id; Struct37 ir_by_victim;  } Struct38 deriving(Eq, Bits);
typedef struct { Bit#(8) info_index; Bool info_hit; Bit#(2) info_way; Bool edir_hit; void edir_way; Struct40 edir_slot; Struct10 info; Struct11 may_victim; Vector#(4, Bit#(8)) reps;  } Struct39 deriving(Eq, Bits);
typedef struct { Bool s_has_slot; Bool s_conflict; Bit#(3) s_id;  } Struct4 deriving(Eq, Bits);
typedef struct { Bool valid; void data;  } Struct40 deriving(Eq, Bits);
typedef struct { Struct38 lr_ir_pp; Struct39 lr_ir; Vector#(4, Bit#(64)) lr_value;  } Struct41 deriving(Eq, Bits);
typedef struct { Bit#(64) addr; Bool info_write; Bool info_hit; Bit#(2) info_way; Bool edir_hit; void edir_way; Struct40 edir_slot; Struct10 info; Bool value_write; Vector#(4, Bit#(64)) value; Struct11 may_victim; Vector#(4, Bit#(8)) reps;  } Struct42 deriving(Eq, Bits);
typedef struct { Bit#(2) r_id; Bool r_ul_rsb; Bit#(2) r_ul_rsbTo;  } Struct43 deriving(Eq, Bits);
typedef struct { Bit#(1) victim_idx; Struct10 victim_info; Vector#(4, Bit#(64)) victim_value;  } Struct44 deriving(Eq, Bits);
typedef struct { Bit#(51) tag; Struct10 value;  } Struct45 deriving(Eq, Bits);
typedef struct { Bool tm_hit; Bit#(2) tm_way; Struct10 tm_value;  } Struct46 deriving(Eq, Bits);
typedef struct { Bit#(8) addr; Struct45 datain;  } Struct47 deriving(Eq, Bits);
typedef struct { Bit#(1) acc_type; Vector#(4, Bit#(8)) acc_reps; Bit#(8) acc_index; Bit#(2) acc_way;  } Struct48 deriving(Eq, Bits);
typedef struct { Bit#(10) addr; Vector#(4, Bit#(64)) datain;  } Struct49 deriving(Eq, Bits);
typedef struct { Bool valid; Bit#(3) data;  } Struct5 deriving(Eq, Bits);
typedef struct { Bit#(8) addr; Vector#(4, Bit#(8)) datain;  } Struct50 deriving(Eq, Bits);
typedef struct { Bool valid; Bit#(2) data;  } Struct51 deriving(Eq, Bits);
typedef struct { Bool ir_is_rs_rel; Struct1 ir_msg; Bit#(4) ir_msg_from; Bit#(3) ir_mshr_id; Struct5 ir_by_victim;  } Struct6 deriving(Eq, Bits);
typedef struct { Bit#(2) r_midx; Struct1 r_msg;  } Struct7 deriving(Eq, Bits);
typedef struct { Bit#(3) r_id; Bit#(64) r_addr;  } Struct8 deriving(Eq, Bits);
typedef struct { Bit#(10) info_index; Bool info_hit; Bit#(4) info_way; Bool edir_hit; Bit#(3) edir_way; Struct5 edir_slot; Struct10 info; Struct11 may_victim; Vector#(16, Bit#(8)) reps;  } Struct9 deriving(Eq, Bits);

interface Module1;
    method Action enq_fifoCRqInput_00 (Struct2 x_0);
    method ActionValue#(Struct2) deq_fifoCRqInput_00 ();
endinterface

module mkModule1 (Module1);
    FIFOF#(Struct2) pff <- mkSizedFIFOF(4);

    method Action enq_fifoCRqInput_00 (Struct2 x_0);
        pff.enq(x_0);
    endmethod

    method ActionValue#(Struct2) deq_fifoCRqInput_00 ();
        pff.deq();
        return pff.first();
    endmethod

endmodule

interface Module2;
    method Action enq_fifoCRsInput_00 (Struct2 x_0);
    method ActionValue#(Struct2) deq_fifoCRsInput_00 ();
endinterface

module mkModule2 (Module2);
    FIFOF#(Struct2) pff <- mkSizedFIFOF(4);

    method Action enq_fifoCRsInput_00 (Struct2 x_0);
        pff.enq(x_0);
    endmethod

    method ActionValue#(Struct2) deq_fifoCRsInput_00 ();
        pff.deq();
        return pff.first();
    endmethod

endmodule

interface Module3;
    method Action enq_fifoPInput_00 (Struct2 x_0);
    method ActionValue#(Struct2) deq_fifoPInput_00 ();
endinterface

module mkModule3 (Module3);
    FIFOF#(Struct2) pff <- mkSizedFIFOF(4);

    method Action enq_fifoPInput_00 (Struct2 x_0);
        pff.enq(x_0);
    endmethod

    method ActionValue#(Struct2) deq_fifoPInput_00 ();
        pff.deq();
        return pff.first();
    endmethod

endmodule

interface Module4;
    method Action enq_fifoN2I_00 (Struct6 x_0);
    method ActionValue#(Struct6) deq_fifoN2I_00 ();
endinterface

module mkModule4 (Module4);
    FIFOF#(Struct6) pff <- mkPipelineFIFOF();

    method Action enq_fifoN2I_00 (Struct6 x_0);
        pff.enq(x_0);
    endmethod

    method ActionValue#(Struct6) deq_fifoN2I_00 ();
        pff.deq();
        return pff.first();
    endmethod

endmodule

interface Module5;
    method Action enq_fifoI2L_00 (Struct6 x_0);
    method ActionValue#(Struct6) deq_fifoI2L_00 ();
endinterface

module mkModule5 (Module5);
    FIFOF#(Struct6) pff <- mkPipelineFIFOF();

    method Action enq_fifoI2L_00 (Struct6 x_0);
        pff.enq(x_0);
    endmethod

    method ActionValue#(Struct6) deq_fifoI2L_00 ();
        pff.deq();
        return pff.first();
    endmethod

endmodule

interface Module6;
    method Action enq_fifoL2E_00 (Struct12 x_0);
    method ActionValue#(Struct12) deq_fifoL2E_00 ();
endinterface

module mkModule6 (Module6);
    FIFOF#(Struct12) pff <- mkPipelineFIFOF();

    method Action enq_fifoL2E_00 (Struct12 x_0);
        pff.enq(x_0);
    endmethod

    method ActionValue#(Struct12) deq_fifoL2E_00 ();
        pff.deq();
        return pff.first();
    endmethod

endmodule

interface Module7;
    method ActionValue#(Struct5) victims__00__findVictim (Bit#(64) x_0);
    method ActionValue#(Struct13) victims__00__getVictim (Bit#(3) x_0);
    method Action victims__00__setVictim (Struct17 x_0);
    method Action victims__00__registerVictim (Struct13 x_0);
    method ActionValue#(Struct13) victims__00__getFirstVictim ();
    method ActionValue#(Bool) victims__00__hasVictim ();
    method Action victims__00__setVictimRq (Bit#(64) x_0);
    method Action victims__00__releaseVictim (Bit#(64) x_0);
endinterface

module mkModule7
    (Module7);
    Reg#(Vector#(8, Struct13)) victimRegs__00 <- mkReg(unpack(0));

    // No rules in this module

    method ActionValue#(Struct5) victims__00__findVictim (Bit#(64) x_0);
        let x_1 = (victimRegs__00);
        Struct13 x_2 =
        ((x_1)[(Bit#(3))'(3'h0)]);
        let x_17 = ?;
        if (((x_2).victim_valid) && (((x_2).victim_addr) == (x_0))) begin
            x_17 = Struct5 {valid : (Bool)'(True), data : (Bit#(3))'(3'h0)};
        end else begin
            Struct13 x_3 =
            ((x_1)[(Bit#(3))'(3'h1)]);
            let x_16 = ?;
            if (((x_3).victim_valid) && (((x_3).victim_addr) == (x_0)))
                begin
                x_16 = Struct5 {valid : (Bool)'(True), data :
                (Bit#(3))'(3'h1)};
            end else begin
                Struct13 x_4 =
                ((x_1)[(Bit#(3))'(3'h2)]);
                let x_15 = ?;
                if (((x_4).victim_valid) && (((x_4).victim_addr) == (x_0)))
                    begin
                    x_15 = Struct5 {valid : (Bool)'(True), data :
                    (Bit#(3))'(3'h2)};
                end else begin
                    Struct13 x_5 =
                    ((x_1)[(Bit#(3))'(3'h3)]);
                    let x_14 = ?;
                    if (((x_5).victim_valid) && (((x_5).victim_addr) ==
                        (x_0))) begin
                        x_14 = Struct5 {valid : (Bool)'(True), data :
                        (Bit#(3))'(3'h3)};
                    end else begin
                        Struct13 x_6 =
                        ((x_1)[(Bit#(3))'(3'h4)]);
                        let x_13 = ?;
                        if (((x_6).victim_valid) && (((x_6).victim_addr) ==
                            (x_0))) begin
                            x_13 = Struct5 {valid : (Bool)'(True), data :
                            (Bit#(3))'(3'h4)};
                        end else begin
                            Struct13 x_7 =
                            ((x_1)[(Bit#(3))'(3'h5)]);
                            let x_12 = ?;
                            if (((x_7).victim_valid) && (((x_7).victim_addr)
                                == (x_0))) begin
                                x_12 = Struct5 {valid : (Bool)'(True), data :
                                (Bit#(3))'(3'h5)};
                            end else begin
                                Struct13 x_8 =
                                ((x_1)[(Bit#(3))'(3'h6)]);
                                let x_11 = ?;
                                if (((x_8).victim_valid) &&
                                    (((x_8).victim_addr) == (x_0))) begin
                                    x_11 = Struct5 {valid : (Bool)'(True),
                                    data : (Bit#(3))'(3'h6)};
                                end else begin
                                    Struct13 x_9 =
                                    ((x_1)[(Bit#(3))'(3'h7)]);
                                    let x_10 = ?;
                                    if (((x_9).victim_valid) &&
                                        (((x_9).victim_addr) == (x_0)))
                                        begin
                                        x_10 = Struct5 {valid :
                                        (Bool)'(True), data :
                                        (Bit#(3))'(3'h7)};
                                    end else begin
                                        x_10 = Struct5 {valid :
                                        (Bool)'(False), data : unpack(0)};
                                    end
                                    x_11 = x_10;
                                end
                                x_12 = x_11;
                            end
                            x_13 = x_12;
                        end
                        x_14 = x_13;
                    end
                    x_15 = x_14;
                end
                x_16 = x_15;
            end
            x_17 = x_16;
        end
        return x_17;
    endmethod

    method ActionValue#(Struct13) victims__00__getVictim (Bit#(3) x_0);
        let x_1 = (victimRegs__00);
        return (x_1)[x_0];
    endmethod

    method Action victims__00__setVictim (Struct17 x_0);
        let x_1 = (victimRegs__00);
        Struct13 x_2 = ((x_1)[(x_0).victim_idx]);
        Struct13 x_3 = (Struct13 {victim_valid : (Bool)'(True), victim_addr :
        (x_2).victim_addr, victim_info : (x_0).victim_info, victim_value :
        (x_0).victim_value, victim_req : (x_2).victim_req});
        victimRegs__00 <= update (x_1, (x_0).victim_idx, x_3);
    endmethod

    method Action victims__00__registerVictim (Struct13 x_0);
        let x_1 = (victimRegs__00);
        Struct5 x_2 = ((((x_1)[(Bit#(3))'(3'h7)]).victim_valid ?
        ((((x_1)[(Bit#(3))'(3'h6)]).victim_valid ?
        ((((x_1)[(Bit#(3))'(3'h5)]).victim_valid ?
        ((((x_1)[(Bit#(3))'(3'h4)]).victim_valid ?
        ((((x_1)[(Bit#(3))'(3'h3)]).victim_valid ?
        ((((x_1)[(Bit#(3))'(3'h2)]).victim_valid ?
        ((((x_1)[(Bit#(3))'(3'h1)]).victim_valid ?
        ((((x_1)[(Bit#(3))'(3'h0)]).victim_valid ? (Struct5 {valid :
        (Bool)'(False), data : unpack(0)}) : (Struct5 {valid : (Bool)'(True),
        data : (Bit#(3))'(3'h0)}))) : (Struct5 {valid : (Bool)'(True), data :
        (Bit#(3))'(3'h1)}))) : (Struct5 {valid : (Bool)'(True), data :
        (Bit#(3))'(3'h2)}))) : (Struct5 {valid : (Bool)'(True), data :
        (Bit#(3))'(3'h3)}))) : (Struct5 {valid : (Bool)'(True), data :
        (Bit#(3))'(3'h4)}))) : (Struct5 {valid : (Bool)'(True), data :
        (Bit#(3))'(3'h5)}))) : (Struct5 {valid : (Bool)'(True), data :
        (Bit#(3))'(3'h6)}))) : (Struct5 {valid : (Bool)'(True), data :
        (Bit#(3))'(3'h7)})));
        when ((x_2).valid, noAction);
        Bit#(3) x_3 = ((x_2).data);
        victimRegs__00 <= update (x_1, x_3, x_0);
    endmethod

    method ActionValue#(Struct13) victims__00__getFirstVictim ();
        let x_1 = (victimRegs__00);
        Struct33 x_2 = (((((x_1)[(Bit#(3))'(3'h7)]).victim_valid) && (!
        (((x_1)[(Bit#(3))'(3'h7)]).victim_req)) ? (Struct33 {valid :
        (Bool)'(True), data : (x_1)[(Bit#(3))'(3'h7)]}) :
        (((((x_1)[(Bit#(3))'(3'h6)]).victim_valid) && (!
        (((x_1)[(Bit#(3))'(3'h6)]).victim_req)) ? (Struct33 {valid :
        (Bool)'(True), data : (x_1)[(Bit#(3))'(3'h6)]}) :
        (((((x_1)[(Bit#(3))'(3'h5)]).victim_valid) && (!
        (((x_1)[(Bit#(3))'(3'h5)]).victim_req)) ? (Struct33 {valid :
        (Bool)'(True), data : (x_1)[(Bit#(3))'(3'h5)]}) :
        (((((x_1)[(Bit#(3))'(3'h4)]).victim_valid) && (!
        (((x_1)[(Bit#(3))'(3'h4)]).victim_req)) ? (Struct33 {valid :
        (Bool)'(True), data : (x_1)[(Bit#(3))'(3'h4)]}) :
        (((((x_1)[(Bit#(3))'(3'h3)]).victim_valid) && (!
        (((x_1)[(Bit#(3))'(3'h3)]).victim_req)) ? (Struct33 {valid :
        (Bool)'(True), data : (x_1)[(Bit#(3))'(3'h3)]}) :
        (((((x_1)[(Bit#(3))'(3'h2)]).victim_valid) && (!
        (((x_1)[(Bit#(3))'(3'h2)]).victim_req)) ? (Struct33 {valid :
        (Bool)'(True), data : (x_1)[(Bit#(3))'(3'h2)]}) :
        (((((x_1)[(Bit#(3))'(3'h1)]).victim_valid) && (!
        (((x_1)[(Bit#(3))'(3'h1)]).victim_req)) ? (Struct33 {valid :
        (Bool)'(True), data : (x_1)[(Bit#(3))'(3'h1)]}) :
        (((((x_1)[(Bit#(3))'(3'h0)]).victim_valid) && (!
        (((x_1)[(Bit#(3))'(3'h0)]).victim_req)) ? (Struct33 {valid :
        (Bool)'(True), data : (x_1)[(Bit#(3))'(3'h0)]}) : (Struct33 {valid :
        (Bool)'(False), data : unpack(0)})))))))))))))))));
        when ((x_2).valid, noAction);
        return (x_2).data;
    endmethod

    method ActionValue#(Bool) victims__00__hasVictim ();
        let x_1 = (victimRegs__00);
        Bool x_2 = (((((x_1)[(Bit#(3))'(3'h7)]).victim_valid) && (!
        (((x_1)[(Bit#(3))'(3'h7)]).victim_req)) ? ((Bool)'(True)) :
        (((((x_1)[(Bit#(3))'(3'h6)]).victim_valid) && (!
        (((x_1)[(Bit#(3))'(3'h6)]).victim_req)) ? ((Bool)'(True)) :
        (((((x_1)[(Bit#(3))'(3'h5)]).victim_valid) && (!
        (((x_1)[(Bit#(3))'(3'h5)]).victim_req)) ? ((Bool)'(True)) :
        (((((x_1)[(Bit#(3))'(3'h4)]).victim_valid) && (!
        (((x_1)[(Bit#(3))'(3'h4)]).victim_req)) ? ((Bool)'(True)) :
        (((((x_1)[(Bit#(3))'(3'h3)]).victim_valid) && (!
        (((x_1)[(Bit#(3))'(3'h3)]).victim_req)) ? ((Bool)'(True)) :
        (((((x_1)[(Bit#(3))'(3'h2)]).victim_valid) && (!
        (((x_1)[(Bit#(3))'(3'h2)]).victim_req)) ? ((Bool)'(True)) :
        (((((x_1)[(Bit#(3))'(3'h1)]).victim_valid) && (!
        (((x_1)[(Bit#(3))'(3'h1)]).victim_req)) ? ((Bool)'(True)) :
        (((((x_1)[(Bit#(3))'(3'h0)]).victim_valid) && (!
        (((x_1)[(Bit#(3))'(3'h0)]).victim_req)) ? ((Bool)'(True)) :
        ((Bool)'(False))))))))))))))))));
        return x_2;
    endmethod

    method Action victims__00__setVictimRq (Bit#(64) x_0);
        let x_1 = (victimRegs__00);
        Struct13 x_2 =
        ((x_1)[(Bit#(3))'(3'h7)]);
        if (((x_2).victim_valid) && (((x_2).victim_addr) == (x_0)))
            begin
            Struct13 x_3 = (Struct13 {victim_valid : (x_2).victim_valid,
            victim_addr : (x_2).victim_addr, victim_info : (x_2).victim_info,
            victim_value : (x_2).victim_value, victim_req :
            (Bool)'(True)});
            victimRegs__00 <= update (x_1, (Bit#(3))'(3'h7), x_3);
        end else begin
            Struct13 x_4 =
            ((x_1)[(Bit#(3))'(3'h6)]);
            if (((x_4).victim_valid) && (((x_4).victim_addr) == (x_0)))
                begin
                Struct13 x_5 = (Struct13 {victim_valid : (x_4).victim_valid,
                victim_addr : (x_4).victim_addr, victim_info :
                (x_4).victim_info, victim_value : (x_4).victim_value,
                victim_req : (Bool)'(True)});
                victimRegs__00 <= update (x_1, (Bit#(3))'(3'h6), x_5);
            end else begin
                Struct13 x_6 =
                ((x_1)[(Bit#(3))'(3'h5)]);
                if (((x_6).victim_valid) && (((x_6).victim_addr) == (x_0)))
                    begin
                    Struct13 x_7 = (Struct13 {victim_valid :
                    (x_6).victim_valid, victim_addr : (x_6).victim_addr,
                    victim_info : (x_6).victim_info, victim_value :
                    (x_6).victim_value, victim_req :
                    (Bool)'(True)});
                    victimRegs__00 <= update (x_1, (Bit#(3))'(3'h5), x_7);
                end else begin
                    Struct13 x_8 =
                    ((x_1)[(Bit#(3))'(3'h4)]);
                    if (((x_8).victim_valid) && (((x_8).victim_addr) ==
                        (x_0))) begin
                        Struct13 x_9 = (Struct13 {victim_valid :
                        (x_8).victim_valid, victim_addr : (x_8).victim_addr,
                        victim_info : (x_8).victim_info, victim_value :
                        (x_8).victim_value, victim_req :
                        (Bool)'(True)});
                        victimRegs__00 <= update (x_1, (Bit#(3))'(3'h4),
                        x_9);
                    end else begin
                        Struct13 x_10 =
                        ((x_1)[(Bit#(3))'(3'h3)]);
                        if (((x_10).victim_valid) && (((x_10).victim_addr) ==
                            (x_0))) begin
                            Struct13 x_11 = (Struct13 {victim_valid :
                            (x_10).victim_valid, victim_addr :
                            (x_10).victim_addr, victim_info :
                            (x_10).victim_info, victim_value :
                            (x_10).victim_value, victim_req :
                            (Bool)'(True)});
                            victimRegs__00 <= update (x_1, (Bit#(3))'(3'h3),
                            x_11);
                        end else begin
                            Struct13 x_12 =
                            ((x_1)[(Bit#(3))'(3'h2)]);
                            if (((x_12).victim_valid) &&
                                (((x_12).victim_addr) == (x_0)))
                                begin
                                Struct13 x_13 = (Struct13 {victim_valid :
                                (x_12).victim_valid, victim_addr :
                                (x_12).victim_addr, victim_info :
                                (x_12).victim_info, victim_value :
                                (x_12).victim_value, victim_req :
                                (Bool)'(True)});
                                victimRegs__00 <= update (x_1,
                                (Bit#(3))'(3'h2), x_13);
                            end else begin
                                Struct13 x_14 =
                                ((x_1)[(Bit#(3))'(3'h1)]);
                                if (((x_14).victim_valid) &&
                                    (((x_14).victim_addr) == (x_0)))
                                    begin
                                    Struct13 x_15 = (Struct13 {victim_valid :
                                    (x_14).victim_valid, victim_addr :
                                    (x_14).victim_addr, victim_info :
                                    (x_14).victim_info, victim_value :
                                    (x_14).victim_value, victim_req :
                                    (Bool)'(True)});
                                    victimRegs__00 <= update (x_1,
                                    (Bit#(3))'(3'h1), x_15);
                                end else begin
                                    Struct13 x_16 =
                                    ((x_1)[(Bit#(3))'(3'h0)]);
                                    if (((x_16).victim_valid) &&
                                        (((x_16).victim_addr) == (x_0)))
                                        begin
                                        Struct13 x_17 = (Struct13
                                        {victim_valid : (x_16).victim_valid,
                                        victim_addr : (x_16).victim_addr,
                                        victim_info : (x_16).victim_info,
                                        victim_value : (x_16).victim_value,
                                        victim_req :
                                        (Bool)'(True)});
                                        victimRegs__00 <= update (x_1,
                                        (Bit#(3))'(3'h0), x_17);
                                    end else begin

                                    end
                                end
                            end
                        end
                    end
                end
            end
        end
    endmethod

    method Action victims__00__releaseVictim (Bit#(64) x_0);
        let x_1 = (victimRegs__00);
        Struct13 x_2 =
        ((x_1)[(Bit#(3))'(3'h0)]);
        if (((x_2).victim_valid) && (((x_2).victim_addr) == (x_0)))
            begin
            victimRegs__00 <= update (x_1, (Bit#(3))'(3'h0), unpack(0));
        end else begin
            Struct13 x_3 =
            ((x_1)[(Bit#(3))'(3'h1)]);
            if (((x_3).victim_valid) && (((x_3).victim_addr) == (x_0)))
                begin
                victimRegs__00 <= update (x_1, (Bit#(3))'(3'h1), unpack(0));
            end else begin
                Struct13 x_4 =
                ((x_1)[(Bit#(3))'(3'h2)]);
                if (((x_4).victim_valid) && (((x_4).victim_addr) == (x_0)))
                    begin
                    victimRegs__00 <= update (x_1, (Bit#(3))'(3'h2),
                    unpack(0));
                end else begin
                    Struct13 x_5 =
                    ((x_1)[(Bit#(3))'(3'h3)]);
                    if (((x_5).victim_valid) && (((x_5).victim_addr) ==
                        (x_0))) begin
                        victimRegs__00 <= update (x_1, (Bit#(3))'(3'h3),
                        unpack(0));
                    end else begin
                        Struct13 x_6 =
                        ((x_1)[(Bit#(3))'(3'h4)]);
                        if (((x_6).victim_valid) && (((x_6).victim_addr) ==
                            (x_0))) begin
                            victimRegs__00 <= update (x_1, (Bit#(3))'(3'h4),
                            unpack(0));
                        end else begin
                            Struct13 x_7 =
                            ((x_1)[(Bit#(3))'(3'h5)]);
                            if (((x_7).victim_valid) && (((x_7).victim_addr)
                                == (x_0))) begin
                                victimRegs__00 <= update (x_1,
                                (Bit#(3))'(3'h5), unpack(0));
                            end else begin
                                Struct13 x_8 =
                                ((x_1)[(Bit#(3))'(3'h6)]);
                                if (((x_8).victim_valid) &&
                                    (((x_8).victim_addr) == (x_0)))
                                    begin
                                    victimRegs__00 <= update (x_1,
                                    (Bit#(3))'(3'h6), unpack(0));
                                end else begin
                                    Struct13 x_9 =
                                    ((x_1)[(Bit#(3))'(3'h7)]);
                                    if (((x_9).victim_valid) &&
                                        (((x_9).victim_addr) == (x_0)))
                                        begin
                                        victimRegs__00 <= update (x_1,
                                        (Bit#(3))'(3'h7), unpack(0));
                                    end else begin

                                    end
                                end
                            end
                        end
                    end
                end
            end
        end
    endmethod
endmodule

interface Module8;
    method Action rdReq_infoRam__00__15 (Bit#(10) x_0);
    method Action wrReq_infoRam__00__15 (Struct29 x_0);
    method ActionValue#(Struct24) rdResp_infoRam__00__15 ();
endinterface

module mkModule8 (Module8);
    RWBramCore#(Bit#(10), Struct24) bram <- mkRWBramCore();
    Reg#(Bool) initDone <- mkReg(False);
    Reg#(Bit#(10)) initIdx <- mkReg(0);

    rule init (!initDone);
        let initData = Struct24 {tag: 49'h1f, value: Struct10 {mesi_owned: False, mesi_status: 3'h1, mesi_dir_st: 3'h1, mesi_dir_sharers: 4'h0}};
        bram.wrReq(initIdx, initData);
        initIdx <= initIdx + 1;
        initDone <= (initIdx == maxBound);
    endrule

    method Action rdReq_infoRam__00__15 (Bit#(10) x_0) if(initDone);
        bram.rdReq(x_0);
    endmethod

    method Action wrReq_infoRam__00__15 (Struct29 x_0) if(initDone);
        bram.wrReq(x_0.addr, x_0.datain);
    endmethod

    method ActionValue#(Struct24) rdResp_infoRam__00__15 () if(initDone);
        bram.deqRdResp ();
        let data = bram.rdResp ();
        return data;
    endmethod


endmodule

interface Module9;
    method Action rdReq_infoRam__00__14 (Bit#(10) x_0);
    method Action wrReq_infoRam__00__14 (Struct29 x_0);
    method ActionValue#(Struct24) rdResp_infoRam__00__14 ();
endinterface

module mkModule9 (Module9);
    RWBramCore#(Bit#(10), Struct24) bram <- mkRWBramCore();
    Reg#(Bool) initDone <- mkReg(False);
    Reg#(Bit#(10)) initIdx <- mkReg(0);

    rule init (!initDone);
        let initData = Struct24 {tag: 49'h1e, value: Struct10 {mesi_owned: False, mesi_status: 3'h1, mesi_dir_st: 3'h1, mesi_dir_sharers: 4'h0}};
        bram.wrReq(initIdx, initData);
        initIdx <= initIdx + 1;
        initDone <= (initIdx == maxBound);
    endrule

    method Action rdReq_infoRam__00__14 (Bit#(10) x_0) if(initDone);
        bram.rdReq(x_0);
    endmethod

    method Action wrReq_infoRam__00__14 (Struct29 x_0) if(initDone);
        bram.wrReq(x_0.addr, x_0.datain);
    endmethod

    method ActionValue#(Struct24) rdResp_infoRam__00__14 () if(initDone);
        bram.deqRdResp ();
        let data = bram.rdResp ();
        return data;
    endmethod


endmodule

interface Module10;
    method Action rdReq_infoRam__00__13 (Bit#(10) x_0);
    method Action wrReq_infoRam__00__13 (Struct29 x_0);
    method ActionValue#(Struct24) rdResp_infoRam__00__13 ();
endinterface

module mkModule10 (Module10);
    RWBramCore#(Bit#(10), Struct24) bram <- mkRWBramCore();
    Reg#(Bool) initDone <- mkReg(False);
    Reg#(Bit#(10)) initIdx <- mkReg(0);

    rule init (!initDone);
        let initData = Struct24 {tag: 49'h1d, value: Struct10 {mesi_owned: False, mesi_status: 3'h1, mesi_dir_st: 3'h1, mesi_dir_sharers: 4'h0}};
        bram.wrReq(initIdx, initData);
        initIdx <= initIdx + 1;
        initDone <= (initIdx == maxBound);
    endrule

    method Action rdReq_infoRam__00__13 (Bit#(10) x_0) if(initDone);
        bram.rdReq(x_0);
    endmethod

    method Action wrReq_infoRam__00__13 (Struct29 x_0) if(initDone);
        bram.wrReq(x_0.addr, x_0.datain);
    endmethod

    method ActionValue#(Struct24) rdResp_infoRam__00__13 () if(initDone);
        bram.deqRdResp ();
        let data = bram.rdResp ();
        return data;
    endmethod


endmodule

interface Module11;
    method Action rdReq_infoRam__00__12 (Bit#(10) x_0);
    method Action wrReq_infoRam__00__12 (Struct29 x_0);
    method ActionValue#(Struct24) rdResp_infoRam__00__12 ();
endinterface

module mkModule11 (Module11);
    RWBramCore#(Bit#(10), Struct24) bram <- mkRWBramCore();
    Reg#(Bool) initDone <- mkReg(False);
    Reg#(Bit#(10)) initIdx <- mkReg(0);

    rule init (!initDone);
        let initData = Struct24 {tag: 49'h1c, value: Struct10 {mesi_owned: False, mesi_status: 3'h1, mesi_dir_st: 3'h1, mesi_dir_sharers: 4'h0}};
        bram.wrReq(initIdx, initData);
        initIdx <= initIdx + 1;
        initDone <= (initIdx == maxBound);
    endrule

    method Action rdReq_infoRam__00__12 (Bit#(10) x_0) if(initDone);
        bram.rdReq(x_0);
    endmethod

    method Action wrReq_infoRam__00__12 (Struct29 x_0) if(initDone);
        bram.wrReq(x_0.addr, x_0.datain);
    endmethod

    method ActionValue#(Struct24) rdResp_infoRam__00__12 () if(initDone);
        bram.deqRdResp ();
        let data = bram.rdResp ();
        return data;
    endmethod


endmodule

interface Module12;
    method Action rdReq_infoRam__00__11 (Bit#(10) x_0);
    method Action wrReq_infoRam__00__11 (Struct29 x_0);
    method ActionValue#(Struct24) rdResp_infoRam__00__11 ();
endinterface

module mkModule12 (Module12);
    RWBramCore#(Bit#(10), Struct24) bram <- mkRWBramCore();
    Reg#(Bool) initDone <- mkReg(False);
    Reg#(Bit#(10)) initIdx <- mkReg(0);

    rule init (!initDone);
        let initData = Struct24 {tag: 49'h1b, value: Struct10 {mesi_owned: False, mesi_status: 3'h1, mesi_dir_st: 3'h1, mesi_dir_sharers: 4'h0}};
        bram.wrReq(initIdx, initData);
        initIdx <= initIdx + 1;
        initDone <= (initIdx == maxBound);
    endrule

    method Action rdReq_infoRam__00__11 (Bit#(10) x_0) if(initDone);
        bram.rdReq(x_0);
    endmethod

    method Action wrReq_infoRam__00__11 (Struct29 x_0) if(initDone);
        bram.wrReq(x_0.addr, x_0.datain);
    endmethod

    method ActionValue#(Struct24) rdResp_infoRam__00__11 () if(initDone);
        bram.deqRdResp ();
        let data = bram.rdResp ();
        return data;
    endmethod


endmodule

interface Module13;
    method Action rdReq_infoRam__00__10 (Bit#(10) x_0);
    method Action wrReq_infoRam__00__10 (Struct29 x_0);
    method ActionValue#(Struct24) rdResp_infoRam__00__10 ();
endinterface

module mkModule13 (Module13);
    RWBramCore#(Bit#(10), Struct24) bram <- mkRWBramCore();
    Reg#(Bool) initDone <- mkReg(False);
    Reg#(Bit#(10)) initIdx <- mkReg(0);

    rule init (!initDone);
        let initData = Struct24 {tag: 49'h1a, value: Struct10 {mesi_owned: False, mesi_status: 3'h1, mesi_dir_st: 3'h1, mesi_dir_sharers: 4'h0}};
        bram.wrReq(initIdx, initData);
        initIdx <= initIdx + 1;
        initDone <= (initIdx == maxBound);
    endrule

    method Action rdReq_infoRam__00__10 (Bit#(10) x_0) if(initDone);
        bram.rdReq(x_0);
    endmethod

    method Action wrReq_infoRam__00__10 (Struct29 x_0) if(initDone);
        bram.wrReq(x_0.addr, x_0.datain);
    endmethod

    method ActionValue#(Struct24) rdResp_infoRam__00__10 () if(initDone);
        bram.deqRdResp ();
        let data = bram.rdResp ();
        return data;
    endmethod


endmodule

interface Module14;
    method Action rdReq_infoRam__00__9 (Bit#(10) x_0);
    method Action wrReq_infoRam__00__9 (Struct29 x_0);
    method ActionValue#(Struct24) rdResp_infoRam__00__9 ();
endinterface

module mkModule14 (Module14);
    RWBramCore#(Bit#(10), Struct24) bram <- mkRWBramCore();
    Reg#(Bool) initDone <- mkReg(False);
    Reg#(Bit#(10)) initIdx <- mkReg(0);

    rule init (!initDone);
        let initData = Struct24 {tag: 49'h19, value: Struct10 {mesi_owned: False, mesi_status: 3'h1, mesi_dir_st: 3'h1, mesi_dir_sharers: 4'h0}};
        bram.wrReq(initIdx, initData);
        initIdx <= initIdx + 1;
        initDone <= (initIdx == maxBound);
    endrule

    method Action rdReq_infoRam__00__9 (Bit#(10) x_0) if(initDone);
        bram.rdReq(x_0);
    endmethod

    method Action wrReq_infoRam__00__9 (Struct29 x_0) if(initDone);
        bram.wrReq(x_0.addr, x_0.datain);
    endmethod

    method ActionValue#(Struct24) rdResp_infoRam__00__9 () if(initDone);
        bram.deqRdResp ();
        let data = bram.rdResp ();
        return data;
    endmethod


endmodule

interface Module15;
    method Action rdReq_infoRam__00__8 (Bit#(10) x_0);
    method Action wrReq_infoRam__00__8 (Struct29 x_0);
    method ActionValue#(Struct24) rdResp_infoRam__00__8 ();
endinterface

module mkModule15 (Module15);
    RWBramCore#(Bit#(10), Struct24) bram <- mkRWBramCore();
    Reg#(Bool) initDone <- mkReg(False);
    Reg#(Bit#(10)) initIdx <- mkReg(0);

    rule init (!initDone);
        let initData = Struct24 {tag: 49'h18, value: Struct10 {mesi_owned: False, mesi_status: 3'h1, mesi_dir_st: 3'h1, mesi_dir_sharers: 4'h0}};
        bram.wrReq(initIdx, initData);
        initIdx <= initIdx + 1;
        initDone <= (initIdx == maxBound);
    endrule

    method Action rdReq_infoRam__00__8 (Bit#(10) x_0) if(initDone);
        bram.rdReq(x_0);
    endmethod

    method Action wrReq_infoRam__00__8 (Struct29 x_0) if(initDone);
        bram.wrReq(x_0.addr, x_0.datain);
    endmethod

    method ActionValue#(Struct24) rdResp_infoRam__00__8 () if(initDone);
        bram.deqRdResp ();
        let data = bram.rdResp ();
        return data;
    endmethod


endmodule

interface Module16;
    method Action rdReq_infoRam__00__7 (Bit#(10) x_0);
    method Action wrReq_infoRam__00__7 (Struct29 x_0);
    method ActionValue#(Struct24) rdResp_infoRam__00__7 ();
endinterface

module mkModule16 (Module16);
    RWBramCore#(Bit#(10), Struct24) bram <- mkRWBramCore();
    Reg#(Bool) initDone <- mkReg(False);
    Reg#(Bit#(10)) initIdx <- mkReg(0);

    rule init (!initDone);
        let initData = Struct24 {tag: 49'h17, value: Struct10 {mesi_owned: False, mesi_status: 3'h1, mesi_dir_st: 3'h1, mesi_dir_sharers: 4'h0}};
        bram.wrReq(initIdx, initData);
        initIdx <= initIdx + 1;
        initDone <= (initIdx == maxBound);
    endrule

    method Action rdReq_infoRam__00__7 (Bit#(10) x_0) if(initDone);
        bram.rdReq(x_0);
    endmethod

    method Action wrReq_infoRam__00__7 (Struct29 x_0) if(initDone);
        bram.wrReq(x_0.addr, x_0.datain);
    endmethod

    method ActionValue#(Struct24) rdResp_infoRam__00__7 () if(initDone);
        bram.deqRdResp ();
        let data = bram.rdResp ();
        return data;
    endmethod


endmodule

interface Module17;
    method Action rdReq_infoRam__00__6 (Bit#(10) x_0);
    method Action wrReq_infoRam__00__6 (Struct29 x_0);
    method ActionValue#(Struct24) rdResp_infoRam__00__6 ();
endinterface

module mkModule17 (Module17);
    RWBramCore#(Bit#(10), Struct24) bram <- mkRWBramCore();
    Reg#(Bool) initDone <- mkReg(False);
    Reg#(Bit#(10)) initIdx <- mkReg(0);

    rule init (!initDone);
        let initData = Struct24 {tag: 49'h16, value: Struct10 {mesi_owned: False, mesi_status: 3'h1, mesi_dir_st: 3'h1, mesi_dir_sharers: 4'h0}};
        bram.wrReq(initIdx, initData);
        initIdx <= initIdx + 1;
        initDone <= (initIdx == maxBound);
    endrule

    method Action rdReq_infoRam__00__6 (Bit#(10) x_0) if(initDone);
        bram.rdReq(x_0);
    endmethod

    method Action wrReq_infoRam__00__6 (Struct29 x_0) if(initDone);
        bram.wrReq(x_0.addr, x_0.datain);
    endmethod

    method ActionValue#(Struct24) rdResp_infoRam__00__6 () if(initDone);
        bram.deqRdResp ();
        let data = bram.rdResp ();
        return data;
    endmethod


endmodule

interface Module18;
    method Action rdReq_infoRam__00__5 (Bit#(10) x_0);
    method Action wrReq_infoRam__00__5 (Struct29 x_0);
    method ActionValue#(Struct24) rdResp_infoRam__00__5 ();
endinterface

module mkModule18 (Module18);
    RWBramCore#(Bit#(10), Struct24) bram <- mkRWBramCore();
    Reg#(Bool) initDone <- mkReg(False);
    Reg#(Bit#(10)) initIdx <- mkReg(0);

    rule init (!initDone);
        let initData = Struct24 {tag: 49'h15, value: Struct10 {mesi_owned: False, mesi_status: 3'h1, mesi_dir_st: 3'h1, mesi_dir_sharers: 4'h0}};
        bram.wrReq(initIdx, initData);
        initIdx <= initIdx + 1;
        initDone <= (initIdx == maxBound);
    endrule

    method Action rdReq_infoRam__00__5 (Bit#(10) x_0) if(initDone);
        bram.rdReq(x_0);
    endmethod

    method Action wrReq_infoRam__00__5 (Struct29 x_0) if(initDone);
        bram.wrReq(x_0.addr, x_0.datain);
    endmethod

    method ActionValue#(Struct24) rdResp_infoRam__00__5 () if(initDone);
        bram.deqRdResp ();
        let data = bram.rdResp ();
        return data;
    endmethod


endmodule

interface Module19;
    method Action rdReq_infoRam__00__4 (Bit#(10) x_0);
    method Action wrReq_infoRam__00__4 (Struct29 x_0);
    method ActionValue#(Struct24) rdResp_infoRam__00__4 ();
endinterface

module mkModule19 (Module19);
    RWBramCore#(Bit#(10), Struct24) bram <- mkRWBramCore();
    Reg#(Bool) initDone <- mkReg(False);
    Reg#(Bit#(10)) initIdx <- mkReg(0);

    rule init (!initDone);
        let initData = Struct24 {tag: 49'h14, value: Struct10 {mesi_owned: False, mesi_status: 3'h1, mesi_dir_st: 3'h1, mesi_dir_sharers: 4'h0}};
        bram.wrReq(initIdx, initData);
        initIdx <= initIdx + 1;
        initDone <= (initIdx == maxBound);
    endrule

    method Action rdReq_infoRam__00__4 (Bit#(10) x_0) if(initDone);
        bram.rdReq(x_0);
    endmethod

    method Action wrReq_infoRam__00__4 (Struct29 x_0) if(initDone);
        bram.wrReq(x_0.addr, x_0.datain);
    endmethod

    method ActionValue#(Struct24) rdResp_infoRam__00__4 () if(initDone);
        bram.deqRdResp ();
        let data = bram.rdResp ();
        return data;
    endmethod


endmodule

interface Module20;
    method Action rdReq_infoRam__00__3 (Bit#(10) x_0);
    method Action wrReq_infoRam__00__3 (Struct29 x_0);
    method ActionValue#(Struct24) rdResp_infoRam__00__3 ();
endinterface

module mkModule20 (Module20);
    RWBramCore#(Bit#(10), Struct24) bram <- mkRWBramCore();
    Reg#(Bool) initDone <- mkReg(False);
    Reg#(Bit#(10)) initIdx <- mkReg(0);

    rule init (!initDone);
        let initData = Struct24 {tag: 49'h13, value: Struct10 {mesi_owned: False, mesi_status: 3'h1, mesi_dir_st: 3'h1, mesi_dir_sharers: 4'h0}};
        bram.wrReq(initIdx, initData);
        initIdx <= initIdx + 1;
        initDone <= (initIdx == maxBound);
    endrule

    method Action rdReq_infoRam__00__3 (Bit#(10) x_0) if(initDone);
        bram.rdReq(x_0);
    endmethod

    method Action wrReq_infoRam__00__3 (Struct29 x_0) if(initDone);
        bram.wrReq(x_0.addr, x_0.datain);
    endmethod

    method ActionValue#(Struct24) rdResp_infoRam__00__3 () if(initDone);
        bram.deqRdResp ();
        let data = bram.rdResp ();
        return data;
    endmethod


endmodule

interface Module21;
    method Action rdReq_infoRam__00__2 (Bit#(10) x_0);
    method Action wrReq_infoRam__00__2 (Struct29 x_0);
    method ActionValue#(Struct24) rdResp_infoRam__00__2 ();
endinterface

module mkModule21 (Module21);
    RWBramCore#(Bit#(10), Struct24) bram <- mkRWBramCore();
    Reg#(Bool) initDone <- mkReg(False);
    Reg#(Bit#(10)) initIdx <- mkReg(0);

    rule init (!initDone);
        let initData = Struct24 {tag: 49'h12, value: Struct10 {mesi_owned: False, mesi_status: 3'h1, mesi_dir_st: 3'h1, mesi_dir_sharers: 4'h0}};
        bram.wrReq(initIdx, initData);
        initIdx <= initIdx + 1;
        initDone <= (initIdx == maxBound);
    endrule

    method Action rdReq_infoRam__00__2 (Bit#(10) x_0) if(initDone);
        bram.rdReq(x_0);
    endmethod

    method Action wrReq_infoRam__00__2 (Struct29 x_0) if(initDone);
        bram.wrReq(x_0.addr, x_0.datain);
    endmethod

    method ActionValue#(Struct24) rdResp_infoRam__00__2 () if(initDone);
        bram.deqRdResp ();
        let data = bram.rdResp ();
        return data;
    endmethod


endmodule

interface Module22;
    method Action rdReq_infoRam__00__1 (Bit#(10) x_0);
    method Action wrReq_infoRam__00__1 (Struct29 x_0);
    method ActionValue#(Struct24) rdResp_infoRam__00__1 ();
endinterface

module mkModule22 (Module22);
    RWBramCore#(Bit#(10), Struct24) bram <- mkRWBramCore();
    Reg#(Bool) initDone <- mkReg(False);
    Reg#(Bit#(10)) initIdx <- mkReg(0);

    rule init (!initDone);
        let initData = Struct24 {tag: 49'h11, value: Struct10 {mesi_owned: False, mesi_status: 3'h1, mesi_dir_st: 3'h1, mesi_dir_sharers: 4'h0}};
        bram.wrReq(initIdx, initData);
        initIdx <= initIdx + 1;
        initDone <= (initIdx == maxBound);
    endrule

    method Action rdReq_infoRam__00__1 (Bit#(10) x_0) if(initDone);
        bram.rdReq(x_0);
    endmethod

    method Action wrReq_infoRam__00__1 (Struct29 x_0) if(initDone);
        bram.wrReq(x_0.addr, x_0.datain);
    endmethod

    method ActionValue#(Struct24) rdResp_infoRam__00__1 () if(initDone);
        bram.deqRdResp ();
        let data = bram.rdResp ();
        return data;
    endmethod


endmodule

interface Module23;
    method Action rdReq_infoRam__00__0 (Bit#(10) x_0);
    method Action wrReq_infoRam__00__0 (Struct29 x_0);
    method ActionValue#(Struct24) rdResp_infoRam__00__0 ();
endinterface

module mkModule23 (Module23);
    RWBramCore#(Bit#(10), Struct24) bram <- mkRWBramCore();
    Reg#(Bool) initDone <- mkReg(False);
    Reg#(Bit#(10)) initIdx <- mkReg(0);

    rule init (!initDone);
        let initData = Struct24 {tag: 49'h10, value: Struct10 {mesi_owned: False, mesi_status: 3'h1, mesi_dir_st: 3'h1, mesi_dir_sharers: 4'h0}};
        bram.wrReq(initIdx, initData);
        initIdx <= initIdx + 1;
        initDone <= (initIdx == maxBound);
    endrule

    method Action rdReq_infoRam__00__0 (Bit#(10) x_0) if(initDone);
        bram.rdReq(x_0);
    endmethod

    method Action wrReq_infoRam__00__0 (Struct29 x_0) if(initDone);
        bram.wrReq(x_0.addr, x_0.datain);
    endmethod

    method ActionValue#(Struct24) rdResp_infoRam__00__0 () if(initDone);
        bram.deqRdResp ();
        let data = bram.rdResp ();
        return data;
    endmethod


endmodule

interface Module24;
    method Action rdReq_edirRam__00__7 (Bit#(10) x_0);
    method Action wrReq_edirRam__00__7 (Struct31 x_0);
    method ActionValue#(Struct26) rdResp_edirRam__00__7 ();
endinterface

module mkModule24 (Module24);
    RWBramCore#(Bit#(10), Struct26) bram <- mkRWBramCore();
    Reg#(Bool) initDone <- mkReg(False);
    Reg#(Bit#(10)) initIdx <- mkReg(0);

    rule init (!initDone);
        let initData = Struct26 {tag: 49'h27, value: Struct27 {mesi_edir_owned: False, mesi_edir_st: 3'h1, mesi_edir_sharers: 4'h0}};
        bram.wrReq(initIdx, initData);
        initIdx <= initIdx + 1;
        initDone <= (initIdx == maxBound);
    endrule

    method Action rdReq_edirRam__00__7 (Bit#(10) x_0) if(initDone);
        bram.rdReq(x_0);
    endmethod

    method Action wrReq_edirRam__00__7 (Struct31 x_0) if(initDone);
        bram.wrReq(x_0.addr, x_0.datain);
    endmethod

    method ActionValue#(Struct26) rdResp_edirRam__00__7 () if(initDone);
        bram.deqRdResp ();
        let data = bram.rdResp ();
        return data;
    endmethod


endmodule

interface Module25;
    method Action rdReq_edirRam__00__6 (Bit#(10) x_0);
    method Action wrReq_edirRam__00__6 (Struct31 x_0);
    method ActionValue#(Struct26) rdResp_edirRam__00__6 ();
endinterface

module mkModule25 (Module25);
    RWBramCore#(Bit#(10), Struct26) bram <- mkRWBramCore();
    Reg#(Bool) initDone <- mkReg(False);
    Reg#(Bit#(10)) initIdx <- mkReg(0);

    rule init (!initDone);
        let initData = Struct26 {tag: 49'h26, value: Struct27 {mesi_edir_owned: False, mesi_edir_st: 3'h1, mesi_edir_sharers: 4'h0}};
        bram.wrReq(initIdx, initData);
        initIdx <= initIdx + 1;
        initDone <= (initIdx == maxBound);
    endrule

    method Action rdReq_edirRam__00__6 (Bit#(10) x_0) if(initDone);
        bram.rdReq(x_0);
    endmethod

    method Action wrReq_edirRam__00__6 (Struct31 x_0) if(initDone);
        bram.wrReq(x_0.addr, x_0.datain);
    endmethod

    method ActionValue#(Struct26) rdResp_edirRam__00__6 () if(initDone);
        bram.deqRdResp ();
        let data = bram.rdResp ();
        return data;
    endmethod


endmodule

interface Module26;
    method Action rdReq_edirRam__00__5 (Bit#(10) x_0);
    method Action wrReq_edirRam__00__5 (Struct31 x_0);
    method ActionValue#(Struct26) rdResp_edirRam__00__5 ();
endinterface

module mkModule26 (Module26);
    RWBramCore#(Bit#(10), Struct26) bram <- mkRWBramCore();
    Reg#(Bool) initDone <- mkReg(False);
    Reg#(Bit#(10)) initIdx <- mkReg(0);

    rule init (!initDone);
        let initData = Struct26 {tag: 49'h25, value: Struct27 {mesi_edir_owned: False, mesi_edir_st: 3'h1, mesi_edir_sharers: 4'h0}};
        bram.wrReq(initIdx, initData);
        initIdx <= initIdx + 1;
        initDone <= (initIdx == maxBound);
    endrule

    method Action rdReq_edirRam__00__5 (Bit#(10) x_0) if(initDone);
        bram.rdReq(x_0);
    endmethod

    method Action wrReq_edirRam__00__5 (Struct31 x_0) if(initDone);
        bram.wrReq(x_0.addr, x_0.datain);
    endmethod

    method ActionValue#(Struct26) rdResp_edirRam__00__5 () if(initDone);
        bram.deqRdResp ();
        let data = bram.rdResp ();
        return data;
    endmethod


endmodule

interface Module27;
    method Action rdReq_edirRam__00__4 (Bit#(10) x_0);
    method Action wrReq_edirRam__00__4 (Struct31 x_0);
    method ActionValue#(Struct26) rdResp_edirRam__00__4 ();
endinterface

module mkModule27 (Module27);
    RWBramCore#(Bit#(10), Struct26) bram <- mkRWBramCore();
    Reg#(Bool) initDone <- mkReg(False);
    Reg#(Bit#(10)) initIdx <- mkReg(0);

    rule init (!initDone);
        let initData = Struct26 {tag: 49'h24, value: Struct27 {mesi_edir_owned: False, mesi_edir_st: 3'h1, mesi_edir_sharers: 4'h0}};
        bram.wrReq(initIdx, initData);
        initIdx <= initIdx + 1;
        initDone <= (initIdx == maxBound);
    endrule

    method Action rdReq_edirRam__00__4 (Bit#(10) x_0) if(initDone);
        bram.rdReq(x_0);
    endmethod

    method Action wrReq_edirRam__00__4 (Struct31 x_0) if(initDone);
        bram.wrReq(x_0.addr, x_0.datain);
    endmethod

    method ActionValue#(Struct26) rdResp_edirRam__00__4 () if(initDone);
        bram.deqRdResp ();
        let data = bram.rdResp ();
        return data;
    endmethod


endmodule

interface Module28;
    method Action rdReq_edirRam__00__3 (Bit#(10) x_0);
    method Action wrReq_edirRam__00__3 (Struct31 x_0);
    method ActionValue#(Struct26) rdResp_edirRam__00__3 ();
endinterface

module mkModule28 (Module28);
    RWBramCore#(Bit#(10), Struct26) bram <- mkRWBramCore();
    Reg#(Bool) initDone <- mkReg(False);
    Reg#(Bit#(10)) initIdx <- mkReg(0);

    rule init (!initDone);
        let initData = Struct26 {tag: 49'h23, value: Struct27 {mesi_edir_owned: False, mesi_edir_st: 3'h1, mesi_edir_sharers: 4'h0}};
        bram.wrReq(initIdx, initData);
        initIdx <= initIdx + 1;
        initDone <= (initIdx == maxBound);
    endrule

    method Action rdReq_edirRam__00__3 (Bit#(10) x_0) if(initDone);
        bram.rdReq(x_0);
    endmethod

    method Action wrReq_edirRam__00__3 (Struct31 x_0) if(initDone);
        bram.wrReq(x_0.addr, x_0.datain);
    endmethod

    method ActionValue#(Struct26) rdResp_edirRam__00__3 () if(initDone);
        bram.deqRdResp ();
        let data = bram.rdResp ();
        return data;
    endmethod


endmodule

interface Module29;
    method Action rdReq_edirRam__00__2 (Bit#(10) x_0);
    method Action wrReq_edirRam__00__2 (Struct31 x_0);
    method ActionValue#(Struct26) rdResp_edirRam__00__2 ();
endinterface

module mkModule29 (Module29);
    RWBramCore#(Bit#(10), Struct26) bram <- mkRWBramCore();
    Reg#(Bool) initDone <- mkReg(False);
    Reg#(Bit#(10)) initIdx <- mkReg(0);

    rule init (!initDone);
        let initData = Struct26 {tag: 49'h22, value: Struct27 {mesi_edir_owned: False, mesi_edir_st: 3'h1, mesi_edir_sharers: 4'h0}};
        bram.wrReq(initIdx, initData);
        initIdx <= initIdx + 1;
        initDone <= (initIdx == maxBound);
    endrule

    method Action rdReq_edirRam__00__2 (Bit#(10) x_0) if(initDone);
        bram.rdReq(x_0);
    endmethod

    method Action wrReq_edirRam__00__2 (Struct31 x_0) if(initDone);
        bram.wrReq(x_0.addr, x_0.datain);
    endmethod

    method ActionValue#(Struct26) rdResp_edirRam__00__2 () if(initDone);
        bram.deqRdResp ();
        let data = bram.rdResp ();
        return data;
    endmethod


endmodule

interface Module30;
    method Action rdReq_edirRam__00__1 (Bit#(10) x_0);
    method Action wrReq_edirRam__00__1 (Struct31 x_0);
    method ActionValue#(Struct26) rdResp_edirRam__00__1 ();
endinterface

module mkModule30 (Module30);
    RWBramCore#(Bit#(10), Struct26) bram <- mkRWBramCore();
    Reg#(Bool) initDone <- mkReg(False);
    Reg#(Bit#(10)) initIdx <- mkReg(0);

    rule init (!initDone);
        let initData = Struct26 {tag: 49'h21, value: Struct27 {mesi_edir_owned: False, mesi_edir_st: 3'h1, mesi_edir_sharers: 4'h0}};
        bram.wrReq(initIdx, initData);
        initIdx <= initIdx + 1;
        initDone <= (initIdx == maxBound);
    endrule

    method Action rdReq_edirRam__00__1 (Bit#(10) x_0) if(initDone);
        bram.rdReq(x_0);
    endmethod

    method Action wrReq_edirRam__00__1 (Struct31 x_0) if(initDone);
        bram.wrReq(x_0.addr, x_0.datain);
    endmethod

    method ActionValue#(Struct26) rdResp_edirRam__00__1 () if(initDone);
        bram.deqRdResp ();
        let data = bram.rdResp ();
        return data;
    endmethod


endmodule

interface Module31;
    method Action rdReq_edirRam__00__0 (Bit#(10) x_0);
    method Action wrReq_edirRam__00__0 (Struct31 x_0);
    method ActionValue#(Struct26) rdResp_edirRam__00__0 ();
endinterface

module mkModule31 (Module31);
    RWBramCore#(Bit#(10), Struct26) bram <- mkRWBramCore();
    Reg#(Bool) initDone <- mkReg(False);
    Reg#(Bit#(10)) initIdx <- mkReg(0);

    rule init (!initDone);
        let initData = Struct26 {tag: 49'h20, value: Struct27 {mesi_edir_owned: False, mesi_edir_st: 3'h1, mesi_edir_sharers: 4'h0}};
        bram.wrReq(initIdx, initData);
        initIdx <= initIdx + 1;
        initDone <= (initIdx == maxBound);
    endrule

    method Action rdReq_edirRam__00__0 (Bit#(10) x_0) if(initDone);
        bram.rdReq(x_0);
    endmethod

    method Action wrReq_edirRam__00__0 (Struct31 x_0) if(initDone);
        bram.wrReq(x_0.addr, x_0.datain);
    endmethod

    method ActionValue#(Struct26) rdResp_edirRam__00__0 () if(initDone);
        bram.deqRdResp ();
        let data = bram.rdResp ();
        return data;
    endmethod


endmodule

interface Module32;
    method Action rdReq_dataRam__00 (Bit#(14) x_0);
    method Action wrReq_dataRam__00 (Struct32 x_0);
    method ActionValue#(Vector#(4, Bit#(64))) rdResp_dataRam__00 ();
endinterface

module mkModule32 (Module32);
    RWBramCore#(Bit#(14), Vector#(4, Bit#(64))) bram <- mkRWBramCore();
    Reg#(Bool) initDone <- mkReg(False);
    Reg#(Bit#(14)) initIdx <- mkReg(0);

    rule init (!initDone);
        let initData = vec(64'h0, 64'h0, 64'h0, 64'h0);
        bram.wrReq(initIdx, initData);
        initIdx <= initIdx + 1;
        initDone <= (initIdx == maxBound);
    endrule

    method Action rdReq_dataRam__00 (Bit#(14) x_0) if(initDone);
        bram.rdReq(x_0);
    endmethod

    method Action wrReq_dataRam__00 (Struct32 x_0) if(initDone);
        bram.wrReq(x_0.addr, x_0.datain);
    endmethod

    method ActionValue#(Vector#(4, Bit#(64))) rdResp_dataRam__00 ()
    if(initDone);
        bram.deqRdResp ();
        let data = bram.rdResp ();
        return data;
    endmethod


endmodule

interface Module33;
    method Action rdReq_repRam__00 (Bit#(10) x_0);
    method Action wrReq_repRam__00 (Struct34 x_0);
    method ActionValue#(Vector#(16, Bit#(8))) rdResp_repRam__00 ();
endinterface

module mkModule33 (Module33);
    RWBramCore#(Bit#(10), Vector#(16, Bit#(8))) bram <- mkRWBramCore();
    Reg#(Bool) initDone <- mkReg(False);
    Reg#(Bit#(10)) initIdx <- mkReg(0);

    rule init (!initDone);
        let initData = vec(8'h1, 8'h1, 8'h1, 8'h1, 8'h1, 8'h1, 8'h1, 8'h1, 8'h1, 8'h1, 8'h1, 8'h1, 8'h1, 8'h1, 8'h1, 8'h1);
        bram.wrReq(initIdx, initData);
        initIdx <= initIdx + 1;
        initDone <= (initIdx == maxBound);
    endrule

    method Action rdReq_repRam__00 (Bit#(10) x_0) if(initDone);
        bram.rdReq(x_0);
    endmethod

    method Action wrReq_repRam__00 (Struct34 x_0) if(initDone);
        bram.wrReq(x_0.addr, x_0.datain);
    endmethod

    method ActionValue#(Vector#(16, Bit#(8))) rdResp_repRam__00 ()
    if(initDone);
        bram.deqRdResp ();
        let data = bram.rdResp ();
        return data;
    endmethod


endmodule

interface Module34;
    method ActionValue#(Struct14) getMSHR_00 (Bit#(3) x_0);
    method ActionValue#(Struct1) getMSHRRq_00 (Bit#(3) x_0);
    method ActionValue#(Struct1) getMSHRFirstRs_00 (Bit#(3) x_0);
    method ActionValue#(Struct4) getPRqSlot_00 (Struct3 x_0);
    method ActionValue#(Struct4) getCRqSlot_00 (Struct3 x_0);
    method ActionValue#(Struct3) getWait_00 ();
    method Action registerUL_00 (Struct19 x_0);
    method Action registerDL_00 (Struct20 x_0);
    method Action canImm_00 (Bit#(64) x_0);
    method Action setULImm_00 (Struct1 x_0);
    method Action transferUpDown_00 (Struct23 x_0);
    method Action addRs_00 (Struct7 x_0);
    method ActionValue#(Bit#(3)) getULReady_00 (Bit#(64) x_0);
    method ActionValue#(Struct8) getDLReady_00 ();
    method Action startRelease_00 (Bit#(3) x_0);
    method Action releaseMSHR_00 (Bit#(3) x_0);
endinterface

module mkModule34
    (Module34);
    Reg#(Vector#(8, Struct14)) mshrs_00 <- mkReg(unpack(0));
    Reg#(Vector#(8, Bit#(64))) maddrs_00 <- mkReg(unpack(0));
    Reg#(Vector#(8, Bit#(3))) msts_00 <- mkReg(unpack(0));
    Reg#(Vector#(8, Struct5)) mnexts_00 <- mkReg(unpack(0));
    Reg#(Vector#(8, Struct1)) rqs_00 <- mkReg(unpack(0));
    Reg#(Vector#(8, Struct1)) rss_00 <- mkReg(unpack(0));

    // No rules in this module

    method ActionValue#(Struct14) getMSHR_00 (Bit#(3) x_0);
        let x_1 = (mshrs_00);
        return (x_1)[x_0];
    endmethod

    method ActionValue#(Struct1) getMSHRRq_00 (Bit#(3) x_0);
        let x_1 = (rqs_00);
        return (x_1)[x_0];
    endmethod

    method ActionValue#(Struct1) getMSHRFirstRs_00 (Bit#(3) x_0);
        let x_1 = (rss_00);
        return (x_1)[x_0];
    endmethod

    method ActionValue#(Struct4) getPRqSlot_00 (Struct3 x_0);
        let x_1 = (mshrs_00);
        let x_2 = (maddrs_00);
        let x_3 = (msts_00);
        let x_4 = (mnexts_00);
        Struct5 x_5 = (Struct5 {valid : (Bool)'(False), data :
        unpack(0)});
        Bool x_6 = ((x_5).valid);
        Bit#(3) x_7 = ((x_5).data);
        Bit#(64) x_8 = (((x_0).r_msg).addr);
        Bool x_9 = ((((((x_3)[(Bit#(3))'(3'h0)]) == ((Bit#(3))'(3'h4))) ||
        (((x_3)[(Bit#(3))'(3'h0)]) == ((Bit#(3))'(3'h6)))) && (((!
        (((x_2)[(Bit#(3))'(3'h0)]) == (x_8))) &&
        ((((x_2)[(Bit#(3))'(3'h0)])[14:5]) == ((x_8)[14:5]))) ||
        (((x_2)[(Bit#(3))'(3'h0)]) == (x_8))) ? ((Bool)'(True)) :
        ((((((x_3)[(Bit#(3))'(3'h1)]) == ((Bit#(3))'(3'h4))) ||
        (((x_3)[(Bit#(3))'(3'h1)]) == ((Bit#(3))'(3'h6)))) && (((!
        (((x_2)[(Bit#(3))'(3'h1)]) == (x_8))) &&
        ((((x_2)[(Bit#(3))'(3'h1)])[14:5]) == ((x_8)[14:5]))) ||
        (((x_2)[(Bit#(3))'(3'h1)]) == (x_8))) ? ((Bool)'(True)) :
        ((((((x_3)[(Bit#(3))'(3'h2)]) == ((Bit#(3))'(3'h4))) ||
        (((x_3)[(Bit#(3))'(3'h2)]) == ((Bit#(3))'(3'h6)))) && (((!
        (((x_2)[(Bit#(3))'(3'h2)]) == (x_8))) &&
        ((((x_2)[(Bit#(3))'(3'h2)])[14:5]) == ((x_8)[14:5]))) ||
        (((x_2)[(Bit#(3))'(3'h2)]) == (x_8))) ? ((Bool)'(True)) :
        ((((((x_3)[(Bit#(3))'(3'h3)]) == ((Bit#(3))'(3'h4))) ||
        (((x_3)[(Bit#(3))'(3'h3)]) == ((Bit#(3))'(3'h6)))) && (((!
        (((x_2)[(Bit#(3))'(3'h3)]) == (x_8))) &&
        ((((x_2)[(Bit#(3))'(3'h3)])[14:5]) == ((x_8)[14:5]))) ||
        (((x_2)[(Bit#(3))'(3'h3)]) == (x_8))) ? ((Bool)'(True)) :
        ((((((x_3)[(Bit#(3))'(3'h4)]) == ((Bit#(3))'(3'h4))) ||
        (((x_3)[(Bit#(3))'(3'h4)]) == ((Bit#(3))'(3'h6)))) && (((!
        (((x_2)[(Bit#(3))'(3'h4)]) == (x_8))) &&
        ((((x_2)[(Bit#(3))'(3'h4)])[14:5]) == ((x_8)[14:5]))) ||
        (((x_2)[(Bit#(3))'(3'h4)]) == (x_8))) ? ((Bool)'(True)) :
        ((((((x_3)[(Bit#(3))'(3'h5)]) == ((Bit#(3))'(3'h4))) ||
        (((x_3)[(Bit#(3))'(3'h5)]) == ((Bit#(3))'(3'h6)))) && (((!
        (((x_2)[(Bit#(3))'(3'h5)]) == (x_8))) &&
        ((((x_2)[(Bit#(3))'(3'h5)])[14:5]) == ((x_8)[14:5]))) ||
        (((x_2)[(Bit#(3))'(3'h5)]) == (x_8))) ? ((Bool)'(True)) :
        ((((((x_3)[(Bit#(3))'(3'h6)]) == ((Bit#(3))'(3'h4))) ||
        (((x_3)[(Bit#(3))'(3'h6)]) == ((Bit#(3))'(3'h6)))) && (((!
        (((x_2)[(Bit#(3))'(3'h6)]) == (x_8))) &&
        ((((x_2)[(Bit#(3))'(3'h6)])[14:5]) == ((x_8)[14:5]))) ||
        (((x_2)[(Bit#(3))'(3'h6)]) == (x_8))) ? ((Bool)'(True)) :
        ((((((x_3)[(Bit#(3))'(3'h7)]) == ((Bit#(3))'(3'h4))) ||
        (((x_3)[(Bit#(3))'(3'h7)]) == ((Bit#(3))'(3'h6)))) && (((!
        (((x_2)[(Bit#(3))'(3'h7)]) == (x_8))) &&
        ((((x_2)[(Bit#(3))'(3'h7)])[14:5]) == ((x_8)[14:5]))) ||
        (((x_2)[(Bit#(3))'(3'h7)]) == (x_8))) ? ((Bool)'(True)) :
        ((Bool)'(False))))))))))))))))));
        Struct5 x_10 = ((((((x_3)[(Bit#(3))'(3'h0)]) == ((Bit#(3))'(3'h5)))
        && (! (((x_1)[(Bit#(3))'(3'h0)]).m_is_ul))) &&
        (((x_2)[(Bit#(3))'(3'h0)]) == (x_8)) ? (Struct5 {valid :
        (Bool)'(True), data : (Bit#(3))'(3'h0)}) :
        ((((((x_3)[(Bit#(3))'(3'h1)]) == ((Bit#(3))'(3'h5))) && (!
        (((x_1)[(Bit#(3))'(3'h1)]).m_is_ul))) && (((x_2)[(Bit#(3))'(3'h1)])
        == (x_8)) ? (Struct5 {valid : (Bool)'(True), data :
        (Bit#(3))'(3'h1)}) : ((((((x_3)[(Bit#(3))'(3'h2)]) ==
        ((Bit#(3))'(3'h5))) && (! (((x_1)[(Bit#(3))'(3'h2)]).m_is_ul))) &&
        (((x_2)[(Bit#(3))'(3'h2)]) == (x_8)) ? (Struct5 {valid :
        (Bool)'(True), data : (Bit#(3))'(3'h2)}) :
        ((((((x_3)[(Bit#(3))'(3'h3)]) == ((Bit#(3))'(3'h5))) && (!
        (((x_1)[(Bit#(3))'(3'h3)]).m_is_ul))) && (((x_2)[(Bit#(3))'(3'h3)])
        == (x_8)) ? (Struct5 {valid : (Bool)'(True), data :
        (Bit#(3))'(3'h3)}) : ((((((x_3)[(Bit#(3))'(3'h4)]) ==
        ((Bit#(3))'(3'h5))) && (! (((x_1)[(Bit#(3))'(3'h4)]).m_is_ul))) &&
        (((x_2)[(Bit#(3))'(3'h4)]) == (x_8)) ? (Struct5 {valid :
        (Bool)'(True), data : (Bit#(3))'(3'h4)}) :
        ((((((x_3)[(Bit#(3))'(3'h5)]) == ((Bit#(3))'(3'h5))) && (!
        (((x_1)[(Bit#(3))'(3'h5)]).m_is_ul))) && (((x_2)[(Bit#(3))'(3'h5)])
        == (x_8)) ? (Struct5 {valid : (Bool)'(True), data :
        (Bit#(3))'(3'h5)}) : ((((((x_3)[(Bit#(3))'(3'h6)]) ==
        ((Bit#(3))'(3'h5))) && (! (((x_1)[(Bit#(3))'(3'h6)]).m_is_ul))) &&
        (((x_2)[(Bit#(3))'(3'h6)]) == (x_8)) ? (Struct5 {valid :
        (Bool)'(True), data : (Bit#(3))'(3'h6)}) :
        ((((((x_3)[(Bit#(3))'(3'h7)]) == ((Bit#(3))'(3'h5))) && (!
        (((x_1)[(Bit#(3))'(3'h7)]).m_is_ul))) && (((x_2)[(Bit#(3))'(3'h7)])
        == (x_8)) ? (Struct5 {valid : (Bool)'(True), data :
        (Bit#(3))'(3'h7)}) : (Struct5 {valid : (Bool)'(False), data :
        unpack(0)})))))))))))))))));
        Bool x_11 = ((x_10).valid);
        Struct4 x_12 = (Struct4 {s_has_slot : (x_6) && (! (x_9)), s_conflict
        : x_11, s_id :
        x_7});
        if ((x_6) && (! (x_9))) begin
            mshrs_00 <= update (x_1, x_7, Struct14 {m_is_ul : unpack(0),
            m_qidx : (x_0).r_msg_from, m_rsb : unpack(0), m_dl_rss_from :
            unpack(0), m_dl_rss_recv : unpack(0)});
            maddrs_00 <= update (x_2, x_7, ((x_0).r_msg).addr);
            msts_00 <= update (x_3, x_7, (x_11 ? ((Bit#(3))'(3'h1)) :
            ((Bit#(3))'(3'h4))));
            let x_13 = (rqs_00);
            rqs_00 <= update (x_13, x_7,
            (x_0).r_msg);
            if (x_11) begin
                Bit#(3) x_14 = ((((! (((x_3)[(Bit#(3))'(3'h0)]) ==
                ((Bit#(3))'(3'h0)))) && (!
                (((x_4)[(Bit#(3))'(3'h0)]).valid))) &&
                (((x_2)[(Bit#(3))'(3'h0)]) == (x_8)) ? ((Bit#(3))'(3'h0)) :
                ((((! (((x_3)[(Bit#(3))'(3'h1)]) == ((Bit#(3))'(3'h0)))) &&
                (! (((x_4)[(Bit#(3))'(3'h1)]).valid))) &&
                (((x_2)[(Bit#(3))'(3'h1)]) == (x_8)) ? ((Bit#(3))'(3'h1)) :
                ((((! (((x_3)[(Bit#(3))'(3'h2)]) == ((Bit#(3))'(3'h0)))) &&
                (! (((x_4)[(Bit#(3))'(3'h2)]).valid))) &&
                (((x_2)[(Bit#(3))'(3'h2)]) == (x_8)) ? ((Bit#(3))'(3'h2)) :
                ((((! (((x_3)[(Bit#(3))'(3'h3)]) == ((Bit#(3))'(3'h0)))) &&
                (! (((x_4)[(Bit#(3))'(3'h3)]).valid))) &&
                (((x_2)[(Bit#(3))'(3'h3)]) == (x_8)) ? ((Bit#(3))'(3'h3)) :
                ((((! (((x_3)[(Bit#(3))'(3'h4)]) == ((Bit#(3))'(3'h0)))) &&
                (! (((x_4)[(Bit#(3))'(3'h4)]).valid))) &&
                (((x_2)[(Bit#(3))'(3'h4)]) == (x_8)) ? ((Bit#(3))'(3'h4)) :
                ((((! (((x_3)[(Bit#(3))'(3'h5)]) == ((Bit#(3))'(3'h0)))) &&
                (! (((x_4)[(Bit#(3))'(3'h5)]).valid))) &&
                (((x_2)[(Bit#(3))'(3'h5)]) == (x_8)) ? ((Bit#(3))'(3'h5)) :
                ((((! (((x_3)[(Bit#(3))'(3'h6)]) == ((Bit#(3))'(3'h0)))) &&
                (! (((x_4)[(Bit#(3))'(3'h6)]).valid))) &&
                (((x_2)[(Bit#(3))'(3'h6)]) == (x_8)) ? ((Bit#(3))'(3'h6)) :
                ((((! (((x_3)[(Bit#(3))'(3'h7)]) == ((Bit#(3))'(3'h0)))) &&
                (! (((x_4)[(Bit#(3))'(3'h7)]).valid))) &&
                (((x_2)[(Bit#(3))'(3'h7)]) == (x_8)) ? ((Bit#(3))'(3'h7)) :
                (unpack(0))))))))))))))))));
                Struct5 x_15 = ((x_4)[x_14]);
                mnexts_00 <= update (x_4, x_14, Struct5 {valid :
                (Bool)'(True), data : x_7});
            end else begin

            end
        end else begin

        end
        return x_12;
    endmethod

    method ActionValue#(Struct4) getCRqSlot_00 (Struct3 x_0);
        let x_1 = (mshrs_00);
        let x_2 = (maddrs_00);
        let x_3 = (msts_00);
        let x_4 = (mnexts_00);
        Struct5 x_5 = ((((x_3)[(Bit#(3))'(3'h0)]) == ((Bit#(3))'(3'h0)) ?
        (Struct5 {valid : (Bool)'(True), data : (Bit#(3))'(3'h0)}) :
        ((((x_3)[(Bit#(3))'(3'h1)]) == ((Bit#(3))'(3'h0)) ? (Struct5 {valid :
        (Bool)'(True), data : (Bit#(3))'(3'h1)}) :
        ((((x_3)[(Bit#(3))'(3'h2)]) == ((Bit#(3))'(3'h0)) ? (Struct5 {valid :
        (Bool)'(True), data : (Bit#(3))'(3'h2)}) :
        ((((x_3)[(Bit#(3))'(3'h3)]) == ((Bit#(3))'(3'h0)) ? (Struct5 {valid :
        (Bool)'(True), data : (Bit#(3))'(3'h3)}) :
        ((((x_3)[(Bit#(3))'(3'h4)]) == ((Bit#(3))'(3'h0)) ? (Struct5 {valid :
        (Bool)'(True), data : (Bit#(3))'(3'h4)}) :
        ((((x_3)[(Bit#(3))'(3'h5)]) == ((Bit#(3))'(3'h0)) ? (Struct5 {valid :
        (Bool)'(True), data : (Bit#(3))'(3'h5)}) :
        ((((x_3)[(Bit#(3))'(3'h6)]) == ((Bit#(3))'(3'h0)) ? (Struct5 {valid :
        (Bool)'(True), data : (Bit#(3))'(3'h6)}) :
        ((((x_3)[(Bit#(3))'(3'h7)]) == ((Bit#(3))'(3'h0)) ? (Struct5 {valid :
        (Bool)'(True), data : (Bit#(3))'(3'h7)}) : (Struct5 {valid :
        (Bool)'(False), data : unpack(0)})))))))))))))))));
        Bool x_6 = ((x_5).valid);
        Bit#(3) x_7 = ((x_5).data);
        Bit#(64) x_8 = (((x_0).r_msg).addr);
        Bool x_9 = ((((((x_3)[(Bit#(3))'(3'h0)]) == ((Bit#(3))'(3'h4))) ||
        (((x_3)[(Bit#(3))'(3'h0)]) == ((Bit#(3))'(3'h6)))) && ((!
        (((x_2)[(Bit#(3))'(3'h0)]) == (x_8))) &&
        ((((x_2)[(Bit#(3))'(3'h0)])[14:5]) == ((x_8)[14:5]))) ?
        ((Bool)'(True)) : ((((((x_3)[(Bit#(3))'(3'h1)]) ==
        ((Bit#(3))'(3'h4))) || (((x_3)[(Bit#(3))'(3'h1)]) ==
        ((Bit#(3))'(3'h6)))) && ((! (((x_2)[(Bit#(3))'(3'h1)]) == (x_8))) &&
        ((((x_2)[(Bit#(3))'(3'h1)])[14:5]) == ((x_8)[14:5]))) ?
        ((Bool)'(True)) : ((((((x_3)[(Bit#(3))'(3'h2)]) ==
        ((Bit#(3))'(3'h4))) || (((x_3)[(Bit#(3))'(3'h2)]) ==
        ((Bit#(3))'(3'h6)))) && ((! (((x_2)[(Bit#(3))'(3'h2)]) == (x_8))) &&
        ((((x_2)[(Bit#(3))'(3'h2)])[14:5]) == ((x_8)[14:5]))) ?
        ((Bool)'(True)) : ((((((x_3)[(Bit#(3))'(3'h3)]) ==
        ((Bit#(3))'(3'h4))) || (((x_3)[(Bit#(3))'(3'h3)]) ==
        ((Bit#(3))'(3'h6)))) && ((! (((x_2)[(Bit#(3))'(3'h3)]) == (x_8))) &&
        ((((x_2)[(Bit#(3))'(3'h3)])[14:5]) == ((x_8)[14:5]))) ?
        ((Bool)'(True)) : ((((((x_3)[(Bit#(3))'(3'h4)]) ==
        ((Bit#(3))'(3'h4))) || (((x_3)[(Bit#(3))'(3'h4)]) ==
        ((Bit#(3))'(3'h6)))) && ((! (((x_2)[(Bit#(3))'(3'h4)]) == (x_8))) &&
        ((((x_2)[(Bit#(3))'(3'h4)])[14:5]) == ((x_8)[14:5]))) ?
        ((Bool)'(True)) : ((((((x_3)[(Bit#(3))'(3'h5)]) ==
        ((Bit#(3))'(3'h4))) || (((x_3)[(Bit#(3))'(3'h5)]) ==
        ((Bit#(3))'(3'h6)))) && ((! (((x_2)[(Bit#(3))'(3'h5)]) == (x_8))) &&
        ((((x_2)[(Bit#(3))'(3'h5)])[14:5]) == ((x_8)[14:5]))) ?
        ((Bool)'(True)) : ((((((x_3)[(Bit#(3))'(3'h6)]) ==
        ((Bit#(3))'(3'h4))) || (((x_3)[(Bit#(3))'(3'h6)]) ==
        ((Bit#(3))'(3'h6)))) && ((! (((x_2)[(Bit#(3))'(3'h6)]) == (x_8))) &&
        ((((x_2)[(Bit#(3))'(3'h6)])[14:5]) == ((x_8)[14:5]))) ?
        ((Bool)'(True)) : ((((((x_3)[(Bit#(3))'(3'h7)]) ==
        ((Bit#(3))'(3'h4))) || (((x_3)[(Bit#(3))'(3'h7)]) ==
        ((Bit#(3))'(3'h6)))) && ((! (((x_2)[(Bit#(3))'(3'h7)]) == (x_8))) &&
        ((((x_2)[(Bit#(3))'(3'h7)])[14:5]) == ((x_8)[14:5]))) ?
        ((Bool)'(True)) : ((Bool)'(False))))))))))))))))));
        Struct5 x_10 = (((((! (((x_3)[(Bit#(3))'(3'h0)]) ==
        ((Bit#(3))'(3'h0)))) && (! (((x_4)[(Bit#(3))'(3'h0)]).valid))) &&
        (((x_1)[(Bit#(3))'(3'h0)]).m_is_ul)) && (((x_2)[(Bit#(3))'(3'h0)]) ==
        (x_8)) ? (Struct5 {valid : (Bool)'(True), data : (Bit#(3))'(3'h0)}) :
        (((((! (((x_3)[(Bit#(3))'(3'h1)]) == ((Bit#(3))'(3'h0)))) && (!
        (((x_4)[(Bit#(3))'(3'h1)]).valid))) &&
        (((x_1)[(Bit#(3))'(3'h1)]).m_is_ul)) && (((x_2)[(Bit#(3))'(3'h1)]) ==
        (x_8)) ? (Struct5 {valid : (Bool)'(True), data : (Bit#(3))'(3'h1)}) :
        (((((! (((x_3)[(Bit#(3))'(3'h2)]) == ((Bit#(3))'(3'h0)))) && (!
        (((x_4)[(Bit#(3))'(3'h2)]).valid))) &&
        (((x_1)[(Bit#(3))'(3'h2)]).m_is_ul)) && (((x_2)[(Bit#(3))'(3'h2)]) ==
        (x_8)) ? (Struct5 {valid : (Bool)'(True), data : (Bit#(3))'(3'h2)}) :
        (((((! (((x_3)[(Bit#(3))'(3'h3)]) == ((Bit#(3))'(3'h0)))) && (!
        (((x_4)[(Bit#(3))'(3'h3)]).valid))) &&
        (((x_1)[(Bit#(3))'(3'h3)]).m_is_ul)) && (((x_2)[(Bit#(3))'(3'h3)]) ==
        (x_8)) ? (Struct5 {valid : (Bool)'(True), data : (Bit#(3))'(3'h3)}) :
        (((((! (((x_3)[(Bit#(3))'(3'h4)]) == ((Bit#(3))'(3'h0)))) && (!
        (((x_4)[(Bit#(3))'(3'h4)]).valid))) &&
        (((x_1)[(Bit#(3))'(3'h4)]).m_is_ul)) && (((x_2)[(Bit#(3))'(3'h4)]) ==
        (x_8)) ? (Struct5 {valid : (Bool)'(True), data : (Bit#(3))'(3'h4)}) :
        (((((! (((x_3)[(Bit#(3))'(3'h5)]) == ((Bit#(3))'(3'h0)))) && (!
        (((x_4)[(Bit#(3))'(3'h5)]).valid))) &&
        (((x_1)[(Bit#(3))'(3'h5)]).m_is_ul)) && (((x_2)[(Bit#(3))'(3'h5)]) ==
        (x_8)) ? (Struct5 {valid : (Bool)'(True), data : (Bit#(3))'(3'h5)}) :
        (((((! (((x_3)[(Bit#(3))'(3'h6)]) == ((Bit#(3))'(3'h0)))) && (!
        (((x_4)[(Bit#(3))'(3'h6)]).valid))) &&
        (((x_1)[(Bit#(3))'(3'h6)]).m_is_ul)) && (((x_2)[(Bit#(3))'(3'h6)]) ==
        (x_8)) ? (Struct5 {valid : (Bool)'(True), data : (Bit#(3))'(3'h6)}) :
        (((((! (((x_3)[(Bit#(3))'(3'h7)]) == ((Bit#(3))'(3'h0)))) && (!
        (((x_4)[(Bit#(3))'(3'h7)]).valid))) &&
        (((x_1)[(Bit#(3))'(3'h7)]).m_is_ul)) && (((x_2)[(Bit#(3))'(3'h7)]) ==
        (x_8)) ? (Struct5 {valid : (Bool)'(True), data : (Bit#(3))'(3'h7)}) :
        (Struct5 {valid : (Bool)'(False), data :
        unpack(0)})))))))))))))))));
        Struct5 x_11 = (((((! (((x_3)[(Bit#(3))'(3'h0)]) ==
        ((Bit#(3))'(3'h0)))) && (! (((x_4)[(Bit#(3))'(3'h0)]).valid))) && (!
        (((x_1)[(Bit#(3))'(3'h0)]).m_is_ul))) && (((x_2)[(Bit#(3))'(3'h0)])
        == (x_8)) ? (Struct5 {valid : (Bool)'(True), data :
        (Bit#(3))'(3'h0)}) : (((((! (((x_3)[(Bit#(3))'(3'h1)]) ==
        ((Bit#(3))'(3'h0)))) && (! (((x_4)[(Bit#(3))'(3'h1)]).valid))) && (!
        (((x_1)[(Bit#(3))'(3'h1)]).m_is_ul))) && (((x_2)[(Bit#(3))'(3'h1)])
        == (x_8)) ? (Struct5 {valid : (Bool)'(True), data :
        (Bit#(3))'(3'h1)}) : (((((! (((x_3)[(Bit#(3))'(3'h2)]) ==
        ((Bit#(3))'(3'h0)))) && (! (((x_4)[(Bit#(3))'(3'h2)]).valid))) && (!
        (((x_1)[(Bit#(3))'(3'h2)]).m_is_ul))) && (((x_2)[(Bit#(3))'(3'h2)])
        == (x_8)) ? (Struct5 {valid : (Bool)'(True), data :
        (Bit#(3))'(3'h2)}) : (((((! (((x_3)[(Bit#(3))'(3'h3)]) ==
        ((Bit#(3))'(3'h0)))) && (! (((x_4)[(Bit#(3))'(3'h3)]).valid))) && (!
        (((x_1)[(Bit#(3))'(3'h3)]).m_is_ul))) && (((x_2)[(Bit#(3))'(3'h3)])
        == (x_8)) ? (Struct5 {valid : (Bool)'(True), data :
        (Bit#(3))'(3'h3)}) : (((((! (((x_3)[(Bit#(3))'(3'h4)]) ==
        ((Bit#(3))'(3'h0)))) && (! (((x_4)[(Bit#(3))'(3'h4)]).valid))) && (!
        (((x_1)[(Bit#(3))'(3'h4)]).m_is_ul))) && (((x_2)[(Bit#(3))'(3'h4)])
        == (x_8)) ? (Struct5 {valid : (Bool)'(True), data :
        (Bit#(3))'(3'h4)}) : (((((! (((x_3)[(Bit#(3))'(3'h5)]) ==
        ((Bit#(3))'(3'h0)))) && (! (((x_4)[(Bit#(3))'(3'h5)]).valid))) && (!
        (((x_1)[(Bit#(3))'(3'h5)]).m_is_ul))) && (((x_2)[(Bit#(3))'(3'h5)])
        == (x_8)) ? (Struct5 {valid : (Bool)'(True), data :
        (Bit#(3))'(3'h5)}) : (((((! (((x_3)[(Bit#(3))'(3'h6)]) ==
        ((Bit#(3))'(3'h0)))) && (! (((x_4)[(Bit#(3))'(3'h6)]).valid))) && (!
        (((x_1)[(Bit#(3))'(3'h6)]).m_is_ul))) && (((x_2)[(Bit#(3))'(3'h6)])
        == (x_8)) ? (Struct5 {valid : (Bool)'(True), data :
        (Bit#(3))'(3'h6)}) : (((((! (((x_3)[(Bit#(3))'(3'h7)]) ==
        ((Bit#(3))'(3'h0)))) && (! (((x_4)[(Bit#(3))'(3'h7)]).valid))) && (!
        (((x_1)[(Bit#(3))'(3'h7)]).m_is_ul))) && (((x_2)[(Bit#(3))'(3'h7)])
        == (x_8)) ? (Struct5 {valid : (Bool)'(True), data :
        (Bit#(3))'(3'h7)}) : (Struct5 {valid : (Bool)'(False), data :
        unpack(0)})))))))))))))))));
        Bool x_12 = ((x_10).valid);
        Bool x_13 = ((x_11).valid);
        Bool x_14 = ((x_12) || (x_13));
        Struct4 x_15 = (Struct4 {s_has_slot : (x_6) && (! (x_9)), s_conflict
        : x_14, s_id :
        x_7});
        if ((x_6) && (! (x_9))) begin
            mshrs_00 <= update (x_1, x_7, Struct14 {m_is_ul : unpack(0),
            m_qidx : (x_0).r_msg_from, m_rsb : unpack(0), m_dl_rss_from :
            unpack(0), m_dl_rss_recv : unpack(0)});
            maddrs_00 <= update (x_2, x_7, ((x_0).r_msg).addr);
            msts_00 <= update (x_3, x_7, (x_14 ? ((Bit#(3))'(3'h1)) :
            ((Bit#(3))'(3'h4))));
            let x_16 = (rqs_00);
            rqs_00 <= update (x_16, x_7,
            (x_0).r_msg);
            if (x_14) begin
                Bit#(3) x_17 = ((x_12 ? ((x_10).data) :
                ((x_11).data)));
                Struct5 x_18 = ((x_4)[x_17]);
                mnexts_00 <= update (x_4, x_17, Struct5 {valid :
                (Bool)'(True), data : x_7});
            end else begin

            end
        end else begin

        end
        return x_15;
    endmethod

    method ActionValue#(Struct3) getWait_00 ();
        let x_1 = (mshrs_00);
        let x_2 = (maddrs_00);
        let x_3 = (msts_00);
        let x_4 = (rqs_00);
        Struct5 x_5 = ((((x_3)[(Bit#(3))'(3'h0)]) == ((Bit#(3))'(3'h2)) ?
        (Struct5 {valid : (Bool)'(True), data : (Bit#(3))'(3'h0)}) :
        ((((x_3)[(Bit#(3))'(3'h1)]) == ((Bit#(3))'(3'h2)) ? (Struct5 {valid :
        (Bool)'(True), data : (Bit#(3))'(3'h1)}) :
        ((((x_3)[(Bit#(3))'(3'h2)]) == ((Bit#(3))'(3'h2)) ? (Struct5 {valid :
        (Bool)'(True), data : (Bit#(3))'(3'h2)}) :
        ((((x_3)[(Bit#(3))'(3'h3)]) == ((Bit#(3))'(3'h2)) ? (Struct5 {valid :
        (Bool)'(True), data : (Bit#(3))'(3'h3)}) :
        ((((x_3)[(Bit#(3))'(3'h4)]) == ((Bit#(3))'(3'h2)) ? (Struct5 {valid :
        (Bool)'(True), data : (Bit#(3))'(3'h4)}) :
        ((((x_3)[(Bit#(3))'(3'h5)]) == ((Bit#(3))'(3'h2)) ? (Struct5 {valid :
        (Bool)'(True), data : (Bit#(3))'(3'h5)}) :
        ((((x_3)[(Bit#(3))'(3'h6)]) == ((Bit#(3))'(3'h2)) ? (Struct5 {valid :
        (Bool)'(True), data : (Bit#(3))'(3'h6)}) :
        ((((x_3)[(Bit#(3))'(3'h7)]) == ((Bit#(3))'(3'h2)) ? (Struct5 {valid :
        (Bool)'(True), data : (Bit#(3))'(3'h7)}) : (Struct5 {valid :
        (Bool)'(False), data : unpack(0)})))))))))))))))));
        when ((x_5).valid, noAction);
        Bit#(3) x_6 = ((x_5).data);
        Struct14 x_7 = ((x_1)[x_6]);
        Bit#(64) x_8 = ((x_2)[x_6]);
        Struct1 x_9 = ((x_4)[x_6]);
        Bool x_10 = ((((! (((x_3)[(Bit#(3))'(3'h0)]) < ((Bit#(3))'(3'h4))))
        && (((x_2)[(Bit#(3))'(3'h0)]) == (x_8))) ||
        (((((x_3)[(Bit#(3))'(3'h0)]) == ((Bit#(3))'(3'h4))) ||
        (((x_3)[(Bit#(3))'(3'h0)]) == ((Bit#(3))'(3'h6)))) && ((!
        (((x_2)[(Bit#(3))'(3'h0)]) == (x_8))) &&
        ((((x_2)[(Bit#(3))'(3'h0)])[14:5]) == ((x_8)[14:5])))) ?
        ((Bool)'(True)) : ((((! (((x_3)[(Bit#(3))'(3'h1)]) <
        ((Bit#(3))'(3'h4)))) && (((x_2)[(Bit#(3))'(3'h1)]) == (x_8))) ||
        (((((x_3)[(Bit#(3))'(3'h1)]) == ((Bit#(3))'(3'h4))) ||
        (((x_3)[(Bit#(3))'(3'h1)]) == ((Bit#(3))'(3'h6)))) && ((!
        (((x_2)[(Bit#(3))'(3'h1)]) == (x_8))) &&
        ((((x_2)[(Bit#(3))'(3'h1)])[14:5]) == ((x_8)[14:5])))) ?
        ((Bool)'(True)) : ((((! (((x_3)[(Bit#(3))'(3'h2)]) <
        ((Bit#(3))'(3'h4)))) && (((x_2)[(Bit#(3))'(3'h2)]) == (x_8))) ||
        (((((x_3)[(Bit#(3))'(3'h2)]) == ((Bit#(3))'(3'h4))) ||
        (((x_3)[(Bit#(3))'(3'h2)]) == ((Bit#(3))'(3'h6)))) && ((!
        (((x_2)[(Bit#(3))'(3'h2)]) == (x_8))) &&
        ((((x_2)[(Bit#(3))'(3'h2)])[14:5]) == ((x_8)[14:5])))) ?
        ((Bool)'(True)) : ((((! (((x_3)[(Bit#(3))'(3'h3)]) <
        ((Bit#(3))'(3'h4)))) && (((x_2)[(Bit#(3))'(3'h3)]) == (x_8))) ||
        (((((x_3)[(Bit#(3))'(3'h3)]) == ((Bit#(3))'(3'h4))) ||
        (((x_3)[(Bit#(3))'(3'h3)]) == ((Bit#(3))'(3'h6)))) && ((!
        (((x_2)[(Bit#(3))'(3'h3)]) == (x_8))) &&
        ((((x_2)[(Bit#(3))'(3'h3)])[14:5]) == ((x_8)[14:5])))) ?
        ((Bool)'(True)) : ((((! (((x_3)[(Bit#(3))'(3'h4)]) <
        ((Bit#(3))'(3'h4)))) && (((x_2)[(Bit#(3))'(3'h4)]) == (x_8))) ||
        (((((x_3)[(Bit#(3))'(3'h4)]) == ((Bit#(3))'(3'h4))) ||
        (((x_3)[(Bit#(3))'(3'h4)]) == ((Bit#(3))'(3'h6)))) && ((!
        (((x_2)[(Bit#(3))'(3'h4)]) == (x_8))) &&
        ((((x_2)[(Bit#(3))'(3'h4)])[14:5]) == ((x_8)[14:5])))) ?
        ((Bool)'(True)) : ((((! (((x_3)[(Bit#(3))'(3'h5)]) <
        ((Bit#(3))'(3'h4)))) && (((x_2)[(Bit#(3))'(3'h5)]) == (x_8))) ||
        (((((x_3)[(Bit#(3))'(3'h5)]) == ((Bit#(3))'(3'h4))) ||
        (((x_3)[(Bit#(3))'(3'h5)]) == ((Bit#(3))'(3'h6)))) && ((!
        (((x_2)[(Bit#(3))'(3'h5)]) == (x_8))) &&
        ((((x_2)[(Bit#(3))'(3'h5)])[14:5]) == ((x_8)[14:5])))) ?
        ((Bool)'(True)) : ((((! (((x_3)[(Bit#(3))'(3'h6)]) <
        ((Bit#(3))'(3'h4)))) && (((x_2)[(Bit#(3))'(3'h6)]) == (x_8))) ||
        (((((x_3)[(Bit#(3))'(3'h6)]) == ((Bit#(3))'(3'h4))) ||
        (((x_3)[(Bit#(3))'(3'h6)]) == ((Bit#(3))'(3'h6)))) && ((!
        (((x_2)[(Bit#(3))'(3'h6)]) == (x_8))) &&
        ((((x_2)[(Bit#(3))'(3'h6)])[14:5]) == ((x_8)[14:5])))) ?
        ((Bool)'(True)) : ((((! (((x_3)[(Bit#(3))'(3'h7)]) <
        ((Bit#(3))'(3'h4)))) && (((x_2)[(Bit#(3))'(3'h7)]) == (x_8))) ||
        (((((x_3)[(Bit#(3))'(3'h7)]) == ((Bit#(3))'(3'h4))) ||
        (((x_3)[(Bit#(3))'(3'h7)]) == ((Bit#(3))'(3'h6)))) && ((!
        (((x_2)[(Bit#(3))'(3'h7)]) == (x_8))) &&
        ((((x_2)[(Bit#(3))'(3'h7)])[14:5]) == ((x_8)[14:5])))) ?
        ((Bool)'(True)) : ((Bool)'(False))))))))))))))))));
        when (! (x_10), noAction);
        msts_00 <= update (x_3, x_6, (Bit#(3))'(3'h4));
        Struct3 x_11 = (Struct3 {r_id : x_6, r_msg : x_9, r_msg_from :
        (x_7).m_qidx});
        return x_11;
    endmethod

    method Action registerUL_00 (Struct19 x_0);
        let x_1 = (mshrs_00);
        let x_2 = (msts_00);
        Bit#(3) x_3 = ((x_0).r_id);
        mshrs_00 <= update (x_1, x_3, Struct14 {m_is_ul : (Bool)'(True),
        m_qidx : {((Bit#(2))'(2'h2)),((x_0).r_ul_rsbTo)}, m_rsb :
        (x_0).r_ul_rsb, m_dl_rss_from : unpack(0), m_dl_rss_recv :
        unpack(0)});
        msts_00 <= update (x_2, x_3, (Bit#(3))'(3'h5));
    endmethod

    method Action registerDL_00 (Struct20 x_0);
        let x_1 = (mshrs_00);
        let x_2 = (msts_00);
        Bit#(3) x_3 = ((x_0).r_id);
        mshrs_00 <= update (x_1, x_3, Struct14 {m_is_ul : (Bool)'(False),
        m_qidx : (x_0).r_dl_rsbTo, m_rsb : (x_0).r_dl_rsb, m_dl_rss_from :
        (x_0).r_dl_rss_from, m_dl_rss_recv : unpack(0)});
        msts_00 <= update (x_2, x_3, (Bit#(3))'(3'h5));
    endmethod

    method Action canImm_00 (Bit#(64) x_0);
        let x_1 = (maddrs_00);
        let x_2 = (msts_00);
        let x_3 = (mnexts_00);
        Struct5 x_4 = ((((x_2)[(Bit#(3))'(3'h0)]) == ((Bit#(3))'(3'h0)) ?
        (Struct5 {valid : (Bool)'(True), data : (Bit#(3))'(3'h0)}) :
        ((((x_2)[(Bit#(3))'(3'h1)]) == ((Bit#(3))'(3'h0)) ? (Struct5 {valid :
        (Bool)'(True), data : (Bit#(3))'(3'h1)}) :
        ((((x_2)[(Bit#(3))'(3'h2)]) == ((Bit#(3))'(3'h0)) ? (Struct5 {valid :
        (Bool)'(True), data : (Bit#(3))'(3'h2)}) :
        ((((x_2)[(Bit#(3))'(3'h3)]) == ((Bit#(3))'(3'h0)) ? (Struct5 {valid :
        (Bool)'(True), data : (Bit#(3))'(3'h3)}) :
        ((((x_2)[(Bit#(3))'(3'h4)]) == ((Bit#(3))'(3'h0)) ? (Struct5 {valid :
        (Bool)'(True), data : (Bit#(3))'(3'h4)}) :
        ((((x_2)[(Bit#(3))'(3'h5)]) == ((Bit#(3))'(3'h0)) ? (Struct5 {valid :
        (Bool)'(True), data : (Bit#(3))'(3'h5)}) :
        ((((x_2)[(Bit#(3))'(3'h6)]) == ((Bit#(3))'(3'h0)) ? (Struct5 {valid :
        (Bool)'(True), data : (Bit#(3))'(3'h6)}) :
        ((((x_2)[(Bit#(3))'(3'h7)]) == ((Bit#(3))'(3'h0)) ? (Struct5 {valid :
        (Bool)'(True), data : (Bit#(3))'(3'h7)}) : (Struct5 {valid :
        (Bool)'(False), data : unpack(0)})))))))))))))))));
        when ((x_4).valid, noAction);
        Struct5 x_5 = ((((! (((x_2)[(Bit#(3))'(3'h0)]) ==
        ((Bit#(3))'(3'h0)))) && (! (((x_3)[(Bit#(3))'(3'h0)]).valid))) &&
        (((x_1)[(Bit#(3))'(3'h0)]) == (x_0)) ? (Struct5 {valid :
        (Bool)'(True), data : (Bit#(3))'(3'h0)}) : ((((!
        (((x_2)[(Bit#(3))'(3'h1)]) == ((Bit#(3))'(3'h0)))) && (!
        (((x_3)[(Bit#(3))'(3'h1)]).valid))) && (((x_1)[(Bit#(3))'(3'h1)]) ==
        (x_0)) ? (Struct5 {valid : (Bool)'(True), data : (Bit#(3))'(3'h1)}) :
        ((((! (((x_2)[(Bit#(3))'(3'h2)]) == ((Bit#(3))'(3'h0)))) && (!
        (((x_3)[(Bit#(3))'(3'h2)]).valid))) && (((x_1)[(Bit#(3))'(3'h2)]) ==
        (x_0)) ? (Struct5 {valid : (Bool)'(True), data : (Bit#(3))'(3'h2)}) :
        ((((! (((x_2)[(Bit#(3))'(3'h3)]) == ((Bit#(3))'(3'h0)))) && (!
        (((x_3)[(Bit#(3))'(3'h3)]).valid))) && (((x_1)[(Bit#(3))'(3'h3)]) ==
        (x_0)) ? (Struct5 {valid : (Bool)'(True), data : (Bit#(3))'(3'h3)}) :
        ((((! (((x_2)[(Bit#(3))'(3'h4)]) == ((Bit#(3))'(3'h0)))) && (!
        (((x_3)[(Bit#(3))'(3'h4)]).valid))) && (((x_1)[(Bit#(3))'(3'h4)]) ==
        (x_0)) ? (Struct5 {valid : (Bool)'(True), data : (Bit#(3))'(3'h4)}) :
        ((((! (((x_2)[(Bit#(3))'(3'h5)]) == ((Bit#(3))'(3'h0)))) && (!
        (((x_3)[(Bit#(3))'(3'h5)]).valid))) && (((x_1)[(Bit#(3))'(3'h5)]) ==
        (x_0)) ? (Struct5 {valid : (Bool)'(True), data : (Bit#(3))'(3'h5)}) :
        ((((! (((x_2)[(Bit#(3))'(3'h6)]) == ((Bit#(3))'(3'h0)))) && (!
        (((x_3)[(Bit#(3))'(3'h6)]).valid))) && (((x_1)[(Bit#(3))'(3'h6)]) ==
        (x_0)) ? (Struct5 {valid : (Bool)'(True), data : (Bit#(3))'(3'h6)}) :
        ((((! (((x_2)[(Bit#(3))'(3'h7)]) == ((Bit#(3))'(3'h0)))) && (!
        (((x_3)[(Bit#(3))'(3'h7)]).valid))) && (((x_1)[(Bit#(3))'(3'h7)]) ==
        (x_0)) ? (Struct5 {valid : (Bool)'(True), data : (Bit#(3))'(3'h7)}) :
        (Struct5 {valid : (Bool)'(False), data :
        unpack(0)})))))))))))))))));
        when (! ((x_5).valid), noAction);
    endmethod

    method Action setULImm_00 (Struct1 x_0);
        let x_1 = (mshrs_00);
        let x_2 = (maddrs_00);
        let x_3 = (msts_00);
        let x_4 = (rqs_00);
        Struct5 x_5 = ((((x_3)[(Bit#(3))'(3'h0)]) == ((Bit#(3))'(3'h0)) ?
        (Struct5 {valid : (Bool)'(True), data : (Bit#(3))'(3'h0)}) :
        ((((x_3)[(Bit#(3))'(3'h1)]) == ((Bit#(3))'(3'h0)) ? (Struct5 {valid :
        (Bool)'(True), data : (Bit#(3))'(3'h1)}) :
        ((((x_3)[(Bit#(3))'(3'h2)]) == ((Bit#(3))'(3'h0)) ? (Struct5 {valid :
        (Bool)'(True), data : (Bit#(3))'(3'h2)}) :
        ((((x_3)[(Bit#(3))'(3'h3)]) == ((Bit#(3))'(3'h0)) ? (Struct5 {valid :
        (Bool)'(True), data : (Bit#(3))'(3'h3)}) :
        ((((x_3)[(Bit#(3))'(3'h4)]) == ((Bit#(3))'(3'h0)) ? (Struct5 {valid :
        (Bool)'(True), data : (Bit#(3))'(3'h4)}) :
        ((((x_3)[(Bit#(3))'(3'h5)]) == ((Bit#(3))'(3'h0)) ? (Struct5 {valid :
        (Bool)'(True), data : (Bit#(3))'(3'h5)}) :
        ((((x_3)[(Bit#(3))'(3'h6)]) == ((Bit#(3))'(3'h0)) ? (Struct5 {valid :
        (Bool)'(True), data : (Bit#(3))'(3'h6)}) :
        ((((x_3)[(Bit#(3))'(3'h7)]) == ((Bit#(3))'(3'h0)) ? (Struct5 {valid :
        (Bool)'(True), data : (Bit#(3))'(3'h7)}) : (Struct5 {valid :
        (Bool)'(False), data : unpack(0)})))))))))))))))));
        when ((x_5).valid, noAction);
        Bit#(3) x_6 = ((x_5).data);
        Bit#(64) x_7 = ((x_0).addr);
        Struct5 x_8 = (((! (((x_3)[(Bit#(3))'(3'h0)]) == ((Bit#(3))'(3'h0))))
        && (((x_2)[(Bit#(3))'(3'h0)]) == (x_7)) ? (Struct5 {valid :
        (Bool)'(True), data : (Bit#(3))'(3'h0)}) : (((!
        (((x_3)[(Bit#(3))'(3'h1)]) == ((Bit#(3))'(3'h0)))) &&
        (((x_2)[(Bit#(3))'(3'h1)]) == (x_7)) ? (Struct5 {valid :
        (Bool)'(True), data : (Bit#(3))'(3'h1)}) : (((!
        (((x_3)[(Bit#(3))'(3'h2)]) == ((Bit#(3))'(3'h0)))) &&
        (((x_2)[(Bit#(3))'(3'h2)]) == (x_7)) ? (Struct5 {valid :
        (Bool)'(True), data : (Bit#(3))'(3'h2)}) : (((!
        (((x_3)[(Bit#(3))'(3'h3)]) == ((Bit#(3))'(3'h0)))) &&
        (((x_2)[(Bit#(3))'(3'h3)]) == (x_7)) ? (Struct5 {valid :
        (Bool)'(True), data : (Bit#(3))'(3'h3)}) : (((!
        (((x_3)[(Bit#(3))'(3'h4)]) == ((Bit#(3))'(3'h0)))) &&
        (((x_2)[(Bit#(3))'(3'h4)]) == (x_7)) ? (Struct5 {valid :
        (Bool)'(True), data : (Bit#(3))'(3'h4)}) : (((!
        (((x_3)[(Bit#(3))'(3'h5)]) == ((Bit#(3))'(3'h0)))) &&
        (((x_2)[(Bit#(3))'(3'h5)]) == (x_7)) ? (Struct5 {valid :
        (Bool)'(True), data : (Bit#(3))'(3'h5)}) : (((!
        (((x_3)[(Bit#(3))'(3'h6)]) == ((Bit#(3))'(3'h0)))) &&
        (((x_2)[(Bit#(3))'(3'h6)]) == (x_7)) ? (Struct5 {valid :
        (Bool)'(True), data : (Bit#(3))'(3'h6)}) : (((!
        (((x_3)[(Bit#(3))'(3'h7)]) == ((Bit#(3))'(3'h0)))) &&
        (((x_2)[(Bit#(3))'(3'h7)]) == (x_7)) ? (Struct5 {valid :
        (Bool)'(True), data : (Bit#(3))'(3'h7)}) : (Struct5 {valid :
        (Bool)'(False), data : unpack(0)})))))))))))))))));
        when (! ((x_8).valid), noAction);
        mshrs_00 <= update (x_1, x_6, Struct14 {m_is_ul : (Bool)'(True),
        m_qidx : unpack(0), m_rsb : (Bool)'(False), m_dl_rss_from :
        unpack(0), m_dl_rss_recv : unpack(0)});
        maddrs_00 <= update (x_2, x_6, (x_0).addr);
        msts_00 <= update (x_3, x_6, (Bit#(3))'(3'h5));
        rqs_00 <= update (x_4, x_6, x_0);
    endmethod

    method Action transferUpDown_00 (Struct23 x_0);
        let x_1 = (mshrs_00);
        let x_2 = (msts_00);
        Bit#(3) x_3 = ((x_0).r_id);
        Struct14 x_4 = ((x_1)[x_3]);
        mshrs_00 <= update (x_1, x_3, Struct14 {m_is_ul : (Bool)'(False),
        m_qidx : (x_4).m_qidx, m_rsb : (x_4).m_rsb, m_dl_rss_from :
        (x_0).r_dl_rss_from, m_dl_rss_recv : unpack(0)});
        msts_00 <= update (x_2, x_3, (Bit#(3))'(3'h5));
    endmethod

    method Action addRs_00 (Struct7 x_0);
        let x_1 = (mshrs_00);
        let x_2 = (maddrs_00);
        let x_3 = (msts_00);
        Bit#(64) x_4 = (((x_0).r_msg).addr);
        Struct5 x_5 = ((((((x_3)[(Bit#(3))'(3'h0)]) == ((Bit#(3))'(3'h5))) &&
        (! (((x_1)[(Bit#(3))'(3'h0)]).m_is_ul))) &&
        (((x_2)[(Bit#(3))'(3'h0)]) == (x_4)) ? (Struct5 {valid :
        (Bool)'(True), data : (Bit#(3))'(3'h0)}) :
        ((((((x_3)[(Bit#(3))'(3'h1)]) == ((Bit#(3))'(3'h5))) && (!
        (((x_1)[(Bit#(3))'(3'h1)]).m_is_ul))) && (((x_2)[(Bit#(3))'(3'h1)])
        == (x_4)) ? (Struct5 {valid : (Bool)'(True), data :
        (Bit#(3))'(3'h1)}) : ((((((x_3)[(Bit#(3))'(3'h2)]) ==
        ((Bit#(3))'(3'h5))) && (! (((x_1)[(Bit#(3))'(3'h2)]).m_is_ul))) &&
        (((x_2)[(Bit#(3))'(3'h2)]) == (x_4)) ? (Struct5 {valid :
        (Bool)'(True), data : (Bit#(3))'(3'h2)}) :
        ((((((x_3)[(Bit#(3))'(3'h3)]) == ((Bit#(3))'(3'h5))) && (!
        (((x_1)[(Bit#(3))'(3'h3)]).m_is_ul))) && (((x_2)[(Bit#(3))'(3'h3)])
        == (x_4)) ? (Struct5 {valid : (Bool)'(True), data :
        (Bit#(3))'(3'h3)}) : ((((((x_3)[(Bit#(3))'(3'h4)]) ==
        ((Bit#(3))'(3'h5))) && (! (((x_1)[(Bit#(3))'(3'h4)]).m_is_ul))) &&
        (((x_2)[(Bit#(3))'(3'h4)]) == (x_4)) ? (Struct5 {valid :
        (Bool)'(True), data : (Bit#(3))'(3'h4)}) :
        ((((((x_3)[(Bit#(3))'(3'h5)]) == ((Bit#(3))'(3'h5))) && (!
        (((x_1)[(Bit#(3))'(3'h5)]).m_is_ul))) && (((x_2)[(Bit#(3))'(3'h5)])
        == (x_4)) ? (Struct5 {valid : (Bool)'(True), data :
        (Bit#(3))'(3'h5)}) : ((((((x_3)[(Bit#(3))'(3'h6)]) ==
        ((Bit#(3))'(3'h5))) && (! (((x_1)[(Bit#(3))'(3'h6)]).m_is_ul))) &&
        (((x_2)[(Bit#(3))'(3'h6)]) == (x_4)) ? (Struct5 {valid :
        (Bool)'(True), data : (Bit#(3))'(3'h6)}) :
        ((((((x_3)[(Bit#(3))'(3'h7)]) == ((Bit#(3))'(3'h5))) && (!
        (((x_1)[(Bit#(3))'(3'h7)]).m_is_ul))) && (((x_2)[(Bit#(3))'(3'h7)])
        == (x_4)) ? (Struct5 {valid : (Bool)'(True), data :
        (Bit#(3))'(3'h7)}) : (Struct5 {valid : (Bool)'(False), data :
        unpack(0)})))))))))))))))));
        when ((x_5).valid, noAction);
        Bit#(3) x_6 = ((x_5).data);
        Struct14 x_7 = ((x_1)[x_6]);
        mshrs_00 <= update (x_1, x_6, Struct14 {m_is_ul : (x_7).m_is_ul,
        m_qidx : (x_7).m_qidx, m_rsb : (x_7).m_rsb, m_dl_rss_from :
        (x_7).m_dl_rss_from, m_dl_rss_recv : ((x_7).m_dl_rss_recv) |
        (((Bit#(4))'(4'h1)) << ((x_0).r_midx))});
        let x_8 = (rss_00);
        Struct1 x_9 = ((x_8)[x_6]);
        rss_00 <= update (x_8, x_6, (x_0).r_msg);
    endmethod

    method ActionValue#(Bit#(3)) getULReady_00 (Bit#(64) x_0);
        let x_1 = (mshrs_00);
        let x_2 = (maddrs_00);
        let x_3 = (msts_00);
        Bool x_4 = (((((((x_3)[(Bit#(3))'(3'h0)]) == ((Bit#(3))'(3'h4))) ||
        (((x_3)[(Bit#(3))'(3'h0)]) == ((Bit#(3))'(3'h6)))) && ((!
        (((x_2)[(Bit#(3))'(3'h0)]) == (x_0))) &&
        ((((x_2)[(Bit#(3))'(3'h0)])[14:5]) == ((x_0)[14:5])))) || (((!
        (((x_3)[(Bit#(3))'(3'h0)]) < ((Bit#(3))'(3'h4)))) && (!
        (((x_1)[(Bit#(3))'(3'h0)]).m_is_ul))) && (((x_2)[(Bit#(3))'(3'h0)])
        == (x_0))) ? ((Bool)'(True)) : (((((((x_3)[(Bit#(3))'(3'h1)]) ==
        ((Bit#(3))'(3'h4))) || (((x_3)[(Bit#(3))'(3'h1)]) ==
        ((Bit#(3))'(3'h6)))) && ((! (((x_2)[(Bit#(3))'(3'h1)]) == (x_0))) &&
        ((((x_2)[(Bit#(3))'(3'h1)])[14:5]) == ((x_0)[14:5])))) || (((!
        (((x_3)[(Bit#(3))'(3'h1)]) < ((Bit#(3))'(3'h4)))) && (!
        (((x_1)[(Bit#(3))'(3'h1)]).m_is_ul))) && (((x_2)[(Bit#(3))'(3'h1)])
        == (x_0))) ? ((Bool)'(True)) : (((((((x_3)[(Bit#(3))'(3'h2)]) ==
        ((Bit#(3))'(3'h4))) || (((x_3)[(Bit#(3))'(3'h2)]) ==
        ((Bit#(3))'(3'h6)))) && ((! (((x_2)[(Bit#(3))'(3'h2)]) == (x_0))) &&
        ((((x_2)[(Bit#(3))'(3'h2)])[14:5]) == ((x_0)[14:5])))) || (((!
        (((x_3)[(Bit#(3))'(3'h2)]) < ((Bit#(3))'(3'h4)))) && (!
        (((x_1)[(Bit#(3))'(3'h2)]).m_is_ul))) && (((x_2)[(Bit#(3))'(3'h2)])
        == (x_0))) ? ((Bool)'(True)) : (((((((x_3)[(Bit#(3))'(3'h3)]) ==
        ((Bit#(3))'(3'h4))) || (((x_3)[(Bit#(3))'(3'h3)]) ==
        ((Bit#(3))'(3'h6)))) && ((! (((x_2)[(Bit#(3))'(3'h3)]) == (x_0))) &&
        ((((x_2)[(Bit#(3))'(3'h3)])[14:5]) == ((x_0)[14:5])))) || (((!
        (((x_3)[(Bit#(3))'(3'h3)]) < ((Bit#(3))'(3'h4)))) && (!
        (((x_1)[(Bit#(3))'(3'h3)]).m_is_ul))) && (((x_2)[(Bit#(3))'(3'h3)])
        == (x_0))) ? ((Bool)'(True)) : (((((((x_3)[(Bit#(3))'(3'h4)]) ==
        ((Bit#(3))'(3'h4))) || (((x_3)[(Bit#(3))'(3'h4)]) ==
        ((Bit#(3))'(3'h6)))) && ((! (((x_2)[(Bit#(3))'(3'h4)]) == (x_0))) &&
        ((((x_2)[(Bit#(3))'(3'h4)])[14:5]) == ((x_0)[14:5])))) || (((!
        (((x_3)[(Bit#(3))'(3'h4)]) < ((Bit#(3))'(3'h4)))) && (!
        (((x_1)[(Bit#(3))'(3'h4)]).m_is_ul))) && (((x_2)[(Bit#(3))'(3'h4)])
        == (x_0))) ? ((Bool)'(True)) : (((((((x_3)[(Bit#(3))'(3'h5)]) ==
        ((Bit#(3))'(3'h4))) || (((x_3)[(Bit#(3))'(3'h5)]) ==
        ((Bit#(3))'(3'h6)))) && ((! (((x_2)[(Bit#(3))'(3'h5)]) == (x_0))) &&
        ((((x_2)[(Bit#(3))'(3'h5)])[14:5]) == ((x_0)[14:5])))) || (((!
        (((x_3)[(Bit#(3))'(3'h5)]) < ((Bit#(3))'(3'h4)))) && (!
        (((x_1)[(Bit#(3))'(3'h5)]).m_is_ul))) && (((x_2)[(Bit#(3))'(3'h5)])
        == (x_0))) ? ((Bool)'(True)) : (((((((x_3)[(Bit#(3))'(3'h6)]) ==
        ((Bit#(3))'(3'h4))) || (((x_3)[(Bit#(3))'(3'h6)]) ==
        ((Bit#(3))'(3'h6)))) && ((! (((x_2)[(Bit#(3))'(3'h6)]) == (x_0))) &&
        ((((x_2)[(Bit#(3))'(3'h6)])[14:5]) == ((x_0)[14:5])))) || (((!
        (((x_3)[(Bit#(3))'(3'h6)]) < ((Bit#(3))'(3'h4)))) && (!
        (((x_1)[(Bit#(3))'(3'h6)]).m_is_ul))) && (((x_2)[(Bit#(3))'(3'h6)])
        == (x_0))) ? ((Bool)'(True)) : (((((((x_3)[(Bit#(3))'(3'h7)]) ==
        ((Bit#(3))'(3'h4))) || (((x_3)[(Bit#(3))'(3'h7)]) ==
        ((Bit#(3))'(3'h6)))) && ((! (((x_2)[(Bit#(3))'(3'h7)]) == (x_0))) &&
        ((((x_2)[(Bit#(3))'(3'h7)])[14:5]) == ((x_0)[14:5])))) || (((!
        (((x_3)[(Bit#(3))'(3'h7)]) < ((Bit#(3))'(3'h4)))) && (!
        (((x_1)[(Bit#(3))'(3'h7)]).m_is_ul))) && (((x_2)[(Bit#(3))'(3'h7)])
        == (x_0))) ? ((Bool)'(True)) : ((Bool)'(False))))))))))))))))));
        when (! (x_4), noAction);
        Struct5 x_5 = ((((((x_3)[(Bit#(3))'(3'h0)]) == ((Bit#(3))'(3'h5))) &&
        (((x_1)[(Bit#(3))'(3'h0)]).m_is_ul)) && (((x_2)[(Bit#(3))'(3'h0)]) ==
        (x_0)) ? (Struct5 {valid : (Bool)'(True), data : (Bit#(3))'(3'h0)}) :
        ((((((x_3)[(Bit#(3))'(3'h1)]) == ((Bit#(3))'(3'h5))) &&
        (((x_1)[(Bit#(3))'(3'h1)]).m_is_ul)) && (((x_2)[(Bit#(3))'(3'h1)]) ==
        (x_0)) ? (Struct5 {valid : (Bool)'(True), data : (Bit#(3))'(3'h1)}) :
        ((((((x_3)[(Bit#(3))'(3'h2)]) == ((Bit#(3))'(3'h5))) &&
        (((x_1)[(Bit#(3))'(3'h2)]).m_is_ul)) && (((x_2)[(Bit#(3))'(3'h2)]) ==
        (x_0)) ? (Struct5 {valid : (Bool)'(True), data : (Bit#(3))'(3'h2)}) :
        ((((((x_3)[(Bit#(3))'(3'h3)]) == ((Bit#(3))'(3'h5))) &&
        (((x_1)[(Bit#(3))'(3'h3)]).m_is_ul)) && (((x_2)[(Bit#(3))'(3'h3)]) ==
        (x_0)) ? (Struct5 {valid : (Bool)'(True), data : (Bit#(3))'(3'h3)}) :
        ((((((x_3)[(Bit#(3))'(3'h4)]) == ((Bit#(3))'(3'h5))) &&
        (((x_1)[(Bit#(3))'(3'h4)]).m_is_ul)) && (((x_2)[(Bit#(3))'(3'h4)]) ==
        (x_0)) ? (Struct5 {valid : (Bool)'(True), data : (Bit#(3))'(3'h4)}) :
        ((((((x_3)[(Bit#(3))'(3'h5)]) == ((Bit#(3))'(3'h5))) &&
        (((x_1)[(Bit#(3))'(3'h5)]).m_is_ul)) && (((x_2)[(Bit#(3))'(3'h5)]) ==
        (x_0)) ? (Struct5 {valid : (Bool)'(True), data : (Bit#(3))'(3'h5)}) :
        ((((((x_3)[(Bit#(3))'(3'h6)]) == ((Bit#(3))'(3'h5))) &&
        (((x_1)[(Bit#(3))'(3'h6)]).m_is_ul)) && (((x_2)[(Bit#(3))'(3'h6)]) ==
        (x_0)) ? (Struct5 {valid : (Bool)'(True), data : (Bit#(3))'(3'h6)}) :
        ((((((x_3)[(Bit#(3))'(3'h7)]) == ((Bit#(3))'(3'h5))) &&
        (((x_1)[(Bit#(3))'(3'h7)]).m_is_ul)) && (((x_2)[(Bit#(3))'(3'h7)]) ==
        (x_0)) ? (Struct5 {valid : (Bool)'(True), data : (Bit#(3))'(3'h7)}) :
        (Struct5 {valid : (Bool)'(False), data :
        unpack(0)})))))))))))))))));
        when ((x_5).valid, noAction);
        Bit#(3) x_6 = ((x_5).data);
        return x_6;
    endmethod

    method ActionValue#(Struct8) getDLReady_00 ();
        let x_1 = (mshrs_00);
        let x_2 = (maddrs_00);
        let x_3 = (msts_00);
        Struct5 x_4 = ((((((x_3)[(Bit#(3))'(3'h0)]) == ((Bit#(3))'(3'h5))) &&
        (! (((x_1)[(Bit#(3))'(3'h0)]).m_is_ul))) &&
        ((((x_1)[(Bit#(3))'(3'h0)]).m_dl_rss_from) ==
        (((x_1)[(Bit#(3))'(3'h0)]).m_dl_rss_recv)) ? (Struct5 {valid :
        (Bool)'(True), data : (Bit#(3))'(3'h0)}) :
        ((((((x_3)[(Bit#(3))'(3'h1)]) == ((Bit#(3))'(3'h5))) && (!
        (((x_1)[(Bit#(3))'(3'h1)]).m_is_ul))) &&
        ((((x_1)[(Bit#(3))'(3'h1)]).m_dl_rss_from) ==
        (((x_1)[(Bit#(3))'(3'h1)]).m_dl_rss_recv)) ? (Struct5 {valid :
        (Bool)'(True), data : (Bit#(3))'(3'h1)}) :
        ((((((x_3)[(Bit#(3))'(3'h2)]) == ((Bit#(3))'(3'h5))) && (!
        (((x_1)[(Bit#(3))'(3'h2)]).m_is_ul))) &&
        ((((x_1)[(Bit#(3))'(3'h2)]).m_dl_rss_from) ==
        (((x_1)[(Bit#(3))'(3'h2)]).m_dl_rss_recv)) ? (Struct5 {valid :
        (Bool)'(True), data : (Bit#(3))'(3'h2)}) :
        ((((((x_3)[(Bit#(3))'(3'h3)]) == ((Bit#(3))'(3'h5))) && (!
        (((x_1)[(Bit#(3))'(3'h3)]).m_is_ul))) &&
        ((((x_1)[(Bit#(3))'(3'h3)]).m_dl_rss_from) ==
        (((x_1)[(Bit#(3))'(3'h3)]).m_dl_rss_recv)) ? (Struct5 {valid :
        (Bool)'(True), data : (Bit#(3))'(3'h3)}) :
        ((((((x_3)[(Bit#(3))'(3'h4)]) == ((Bit#(3))'(3'h5))) && (!
        (((x_1)[(Bit#(3))'(3'h4)]).m_is_ul))) &&
        ((((x_1)[(Bit#(3))'(3'h4)]).m_dl_rss_from) ==
        (((x_1)[(Bit#(3))'(3'h4)]).m_dl_rss_recv)) ? (Struct5 {valid :
        (Bool)'(True), data : (Bit#(3))'(3'h4)}) :
        ((((((x_3)[(Bit#(3))'(3'h5)]) == ((Bit#(3))'(3'h5))) && (!
        (((x_1)[(Bit#(3))'(3'h5)]).m_is_ul))) &&
        ((((x_1)[(Bit#(3))'(3'h5)]).m_dl_rss_from) ==
        (((x_1)[(Bit#(3))'(3'h5)]).m_dl_rss_recv)) ? (Struct5 {valid :
        (Bool)'(True), data : (Bit#(3))'(3'h5)}) :
        ((((((x_3)[(Bit#(3))'(3'h6)]) == ((Bit#(3))'(3'h5))) && (!
        (((x_1)[(Bit#(3))'(3'h6)]).m_is_ul))) &&
        ((((x_1)[(Bit#(3))'(3'h6)]).m_dl_rss_from) ==
        (((x_1)[(Bit#(3))'(3'h6)]).m_dl_rss_recv)) ? (Struct5 {valid :
        (Bool)'(True), data : (Bit#(3))'(3'h6)}) :
        ((((((x_3)[(Bit#(3))'(3'h7)]) == ((Bit#(3))'(3'h5))) && (!
        (((x_1)[(Bit#(3))'(3'h7)]).m_is_ul))) &&
        ((((x_1)[(Bit#(3))'(3'h7)]).m_dl_rss_from) ==
        (((x_1)[(Bit#(3))'(3'h7)]).m_dl_rss_recv)) ? (Struct5 {valid :
        (Bool)'(True), data : (Bit#(3))'(3'h7)}) : (Struct5 {valid :
        (Bool)'(False), data : unpack(0)})))))))))))))))));
        when ((x_4).valid, noAction);
        Bit#(3) x_5 = ((x_4).data);
        Bit#(64) x_6 = ((x_2)[x_5]);
        Bool x_7 = ((((((x_3)[(Bit#(3))'(3'h0)]) == ((Bit#(3))'(3'h4))) ||
        (((x_3)[(Bit#(3))'(3'h0)]) == ((Bit#(3))'(3'h6)))) && ((!
        (((x_2)[(Bit#(3))'(3'h0)]) == (x_6))) &&
        ((((x_2)[(Bit#(3))'(3'h0)])[14:5]) == ((x_6)[14:5]))) ?
        ((Bool)'(True)) : ((((((x_3)[(Bit#(3))'(3'h1)]) ==
        ((Bit#(3))'(3'h4))) || (((x_3)[(Bit#(3))'(3'h1)]) ==
        ((Bit#(3))'(3'h6)))) && ((! (((x_2)[(Bit#(3))'(3'h1)]) == (x_6))) &&
        ((((x_2)[(Bit#(3))'(3'h1)])[14:5]) == ((x_6)[14:5]))) ?
        ((Bool)'(True)) : ((((((x_3)[(Bit#(3))'(3'h2)]) ==
        ((Bit#(3))'(3'h4))) || (((x_3)[(Bit#(3))'(3'h2)]) ==
        ((Bit#(3))'(3'h6)))) && ((! (((x_2)[(Bit#(3))'(3'h2)]) == (x_6))) &&
        ((((x_2)[(Bit#(3))'(3'h2)])[14:5]) == ((x_6)[14:5]))) ?
        ((Bool)'(True)) : ((((((x_3)[(Bit#(3))'(3'h3)]) ==
        ((Bit#(3))'(3'h4))) || (((x_3)[(Bit#(3))'(3'h3)]) ==
        ((Bit#(3))'(3'h6)))) && ((! (((x_2)[(Bit#(3))'(3'h3)]) == (x_6))) &&
        ((((x_2)[(Bit#(3))'(3'h3)])[14:5]) == ((x_6)[14:5]))) ?
        ((Bool)'(True)) : ((((((x_3)[(Bit#(3))'(3'h4)]) ==
        ((Bit#(3))'(3'h4))) || (((x_3)[(Bit#(3))'(3'h4)]) ==
        ((Bit#(3))'(3'h6)))) && ((! (((x_2)[(Bit#(3))'(3'h4)]) == (x_6))) &&
        ((((x_2)[(Bit#(3))'(3'h4)])[14:5]) == ((x_6)[14:5]))) ?
        ((Bool)'(True)) : ((((((x_3)[(Bit#(3))'(3'h5)]) ==
        ((Bit#(3))'(3'h4))) || (((x_3)[(Bit#(3))'(3'h5)]) ==
        ((Bit#(3))'(3'h6)))) && ((! (((x_2)[(Bit#(3))'(3'h5)]) == (x_6))) &&
        ((((x_2)[(Bit#(3))'(3'h5)])[14:5]) == ((x_6)[14:5]))) ?
        ((Bool)'(True)) : ((((((x_3)[(Bit#(3))'(3'h6)]) ==
        ((Bit#(3))'(3'h4))) || (((x_3)[(Bit#(3))'(3'h6)]) ==
        ((Bit#(3))'(3'h6)))) && ((! (((x_2)[(Bit#(3))'(3'h6)]) == (x_6))) &&
        ((((x_2)[(Bit#(3))'(3'h6)])[14:5]) == ((x_6)[14:5]))) ?
        ((Bool)'(True)) : ((((((x_3)[(Bit#(3))'(3'h7)]) ==
        ((Bit#(3))'(3'h4))) || (((x_3)[(Bit#(3))'(3'h7)]) ==
        ((Bit#(3))'(3'h6)))) && ((! (((x_2)[(Bit#(3))'(3'h7)]) == (x_6))) &&
        ((((x_2)[(Bit#(3))'(3'h7)])[14:5]) == ((x_6)[14:5]))) ?
        ((Bool)'(True)) : ((Bool)'(False))))))))))))))))));
        when (! (x_7), noAction);
        Struct8 x_8 = (Struct8 {r_id : x_5, r_addr : x_6});
        return x_8;
    endmethod

    method Action startRelease_00 (Bit#(3) x_0);
        let x_1 = (msts_00);
        msts_00 <= update (x_1, x_0, (Bit#(3))'(3'h6));
    endmethod

    method Action releaseMSHR_00 (Bit#(3) x_0);
        let x_1 = (mshrs_00);
        let x_2 = (msts_00);
        let x_3 = (mnexts_00);
        mshrs_00 <= update (x_1, x_0, unpack(0));
        mnexts_00 <= update (x_3, x_0, unpack(0));
        Vector#(8, Bit#(3)) x_4 = (update (x_2, x_0, unpack(0)));
        Struct5 x_5 =
        ((x_3)[x_0]);
        let x_8 = ?;
        if ((x_5).valid) begin
            Bit#(3) x_6 = ((x_5).data);
            Vector#(8, Bit#(3)) x_7 = (update (x_4, x_6,
            (Bit#(3))'(3'h2)));
            x_8 = x_7;
        end else begin
            x_8 = x_4;
        end
        msts_00 <= x_8;
    endmethod
endmodule

interface Module35;
    method Action enq_fifoCRqInput_000 (Struct2 x_0);
    method ActionValue#(Struct2) deq_fifoCRqInput_000 ();
endinterface

module mkModule35 (Module35);
    FIFOF#(Struct2) pff <- mkSizedFIFOF(4);

    method Action enq_fifoCRqInput_000 (Struct2 x_0);
        pff.enq(x_0);
    endmethod

    method ActionValue#(Struct2) deq_fifoCRqInput_000 ();
        pff.deq();
        return pff.first();
    endmethod

endmodule

interface Module36;
    method Action enq_fifoPInput_000 (Struct2 x_0);
    method ActionValue#(Struct2) deq_fifoPInput_000 ();
endinterface

module mkModule36 (Module36);
    FIFOF#(Struct2) pff <- mkSizedFIFOF(4);

    method Action enq_fifoPInput_000 (Struct2 x_0);
        pff.enq(x_0);
    endmethod

    method ActionValue#(Struct2) deq_fifoPInput_000 ();
        pff.deq();
        return pff.first();
    endmethod

endmodule

interface Module37;
    method Action enq_fifoN2I_000 (Struct38 x_0);
    method ActionValue#(Struct38) deq_fifoN2I_000 ();
endinterface

module mkModule37 (Module37);
    FIFOF#(Struct38) pff <- mkPipelineFIFOF();

    method Action enq_fifoN2I_000 (Struct38 x_0);
        pff.enq(x_0);
    endmethod

    method ActionValue#(Struct38) deq_fifoN2I_000 ();
        pff.deq();
        return pff.first();
    endmethod

endmodule

interface Module38;
    method Action enq_fifoI2L_000 (Struct38 x_0);
    method ActionValue#(Struct38) deq_fifoI2L_000 ();
endinterface

module mkModule38 (Module38);
    FIFOF#(Struct38) pff <- mkPipelineFIFOF();

    method Action enq_fifoI2L_000 (Struct38 x_0);
        pff.enq(x_0);
    endmethod

    method ActionValue#(Struct38) deq_fifoI2L_000 ();
        pff.deq();
        return pff.first();
    endmethod

endmodule

interface Module39;
    method Action enq_fifoL2E_000 (Struct41 x_0);
    method ActionValue#(Struct41) deq_fifoL2E_000 ();
endinterface

module mkModule39 (Module39);
    FIFOF#(Struct41) pff <- mkPipelineFIFOF();

    method Action enq_fifoL2E_000 (Struct41 x_0);
        pff.enq(x_0);
    endmethod

    method ActionValue#(Struct41) deq_fifoL2E_000 ();
        pff.deq();
        return pff.first();
    endmethod

endmodule

interface Module40;
    method Action enq_fifo0000 (Struct1 x_0);
    method ActionValue#(Struct1) deq_fifo0000 ();
endinterface

module mkModule40 (Module40);
    FIFOF#(Struct1) pff <- mkSizedFIFOF(2);

    method Action enq_fifo0000 (Struct1 x_0);
        pff.enq(x_0);
    endmethod

    method ActionValue#(Struct1) deq_fifo0000 ();
        pff.deq();
        return pff.first();
    endmethod

endmodule

interface Module41;
    method Action enq_fifo0001 (Struct1 x_0);
    method ActionValue#(Struct1) deq_fifo0001 ();
endinterface

module mkModule41 (Module41);
    FIFOF#(Struct1) pff <- mkSizedFIFOF(2);

    method Action enq_fifo0001 (Struct1 x_0);
        pff.enq(x_0);
    endmethod

    method ActionValue#(Struct1) deq_fifo0001 ();
        pff.deq();
        return pff.first();
    endmethod

endmodule

interface Module42;
    method Action enq_fifo0002 (Struct1 x_0);
    method ActionValue#(Struct1) deq_fifo0002 ();
endinterface

module mkModule42 (Module42);
    FIFOF#(Struct1) pff <- mkSizedFIFOF(2);

    method Action enq_fifo0002 (Struct1 x_0);
        pff.enq(x_0);
    endmethod

    method ActionValue#(Struct1) deq_fifo0002 ();
        pff.deq();
        return pff.first();
    endmethod

endmodule

interface Module43;
    method Action enq_fifo00000 (Struct1 x_0);
    method ActionValue#(Struct1) deq_fifo00000 ();
endinterface

module mkModule43 (Module43);
    FIFOF#(Struct1) pff <- mkSizedFIFOF(2);

    method Action enq_fifo00000 (Struct1 x_0);
        pff.enq(x_0);
    endmethod

    method ActionValue#(Struct1) deq_fifo00000 ();
        pff.deq();
        return pff.first();
    endmethod

endmodule

interface Module44;
    method Action enq_fifo00002 (Struct1 x_0);
    method ActionValue#(Struct1) deq_fifo00002 ();
endinterface

module mkModule44 (Module44);
    FIFOF#(Struct1) pff <- mkSizedFIFOF(2);

    method Action enq_fifo00002 (Struct1 x_0);
        pff.enq(x_0);
    endmethod

    method ActionValue#(Struct1) deq_fifo00002 ();
        pff.deq();
        return pff.first();
    endmethod

endmodule

interface Module45;
    method ActionValue#(Struct37) victims__000__findVictim (Bit#(64) x_0);
    method ActionValue#(Struct13) victims__000__getVictim (Bit#(1) x_0);
    method Action victims__000__setVictim (Struct44 x_0);
    method Action victims__000__registerVictim (Struct13 x_0);
    method ActionValue#(Struct13) victims__000__getFirstVictim ();
    method ActionValue#(Bool) victims__000__hasVictim ();
    method Action victims__000__setVictimRq (Bit#(64) x_0);
    method Action victims__000__releaseVictim (Bit#(64) x_0);
endinterface

module mkModule45
    (Module45);
    Reg#(Vector#(2, Struct13)) victimRegs__000 <- mkReg(unpack(0));

    // No rules in this module

    method ActionValue#(Struct37) victims__000__findVictim (Bit#(64) x_0);
        let x_1 = (victimRegs__000);
        Struct13 x_2 =
        ((x_1)[(Bit#(1))'(1'h0)]);
        let x_5 = ?;
        if (((x_2).victim_valid) && (((x_2).victim_addr) == (x_0))) begin
            x_5 = Struct37 {valid : (Bool)'(True), data : (Bit#(1))'(1'h0)};
        end else begin
            Struct13 x_3 =
            ((x_1)[(Bit#(1))'(1'h1)]);
            let x_4 = ?;
            if (((x_3).victim_valid) && (((x_3).victim_addr) == (x_0)))
                begin
                x_4 = Struct37 {valid : (Bool)'(True), data :
                (Bit#(1))'(1'h1)};
            end else begin
                x_4 = Struct37 {valid : (Bool)'(False), data : unpack(0)};
            end
            x_5 = x_4;
        end
        return x_5;
    endmethod

    method ActionValue#(Struct13) victims__000__getVictim (Bit#(1) x_0);
        let x_1 = (victimRegs__000);
        return (x_1)[x_0];
    endmethod

    method Action victims__000__setVictim (Struct44 x_0);
        let x_1 = (victimRegs__000);
        Struct13 x_2 = ((x_1)[(x_0).victim_idx]);
        Struct13 x_3 = (Struct13 {victim_valid : (Bool)'(True), victim_addr :
        (x_2).victim_addr, victim_info : (x_0).victim_info, victim_value :
        (x_0).victim_value, victim_req : (x_2).victim_req});
        victimRegs__000 <= update (x_1, (x_0).victim_idx, x_3);
    endmethod

    method Action victims__000__registerVictim (Struct13 x_0);
        let x_1 = (victimRegs__000);
        Struct37 x_2 = ((((x_1)[(Bit#(1))'(1'h1)]).victim_valid ?
        ((((x_1)[(Bit#(1))'(1'h0)]).victim_valid ? (Struct37 {valid :
        (Bool)'(False), data : unpack(0)}) : (Struct37 {valid :
        (Bool)'(True), data : (Bit#(1))'(1'h0)}))) : (Struct37 {valid :
        (Bool)'(True), data : (Bit#(1))'(1'h1)})));
        when ((x_2).valid, noAction);
        Bit#(1) x_3 = ((x_2).data);
        victimRegs__000 <= update (x_1, x_3, x_0);
    endmethod

    method ActionValue#(Struct13) victims__000__getFirstVictim ();
        let x_1 = (victimRegs__000);
        Struct33 x_2 = (((((x_1)[(Bit#(1))'(1'h1)]).victim_valid) && (!
        (((x_1)[(Bit#(1))'(1'h1)]).victim_req)) ? (Struct33 {valid :
        (Bool)'(True), data : (x_1)[(Bit#(1))'(1'h1)]}) :
        (((((x_1)[(Bit#(1))'(1'h0)]).victim_valid) && (!
        (((x_1)[(Bit#(1))'(1'h0)]).victim_req)) ? (Struct33 {valid :
        (Bool)'(True), data : (x_1)[(Bit#(1))'(1'h0)]}) : (Struct33 {valid :
        (Bool)'(False), data : unpack(0)})))));
        when ((x_2).valid, noAction);
        return (x_2).data;
    endmethod

    method ActionValue#(Bool) victims__000__hasVictim ();
        let x_1 = (victimRegs__000);
        Bool x_2 = (((((x_1)[(Bit#(1))'(1'h1)]).victim_valid) && (!
        (((x_1)[(Bit#(1))'(1'h1)]).victim_req)) ? ((Bool)'(True)) :
        (((((x_1)[(Bit#(1))'(1'h0)]).victim_valid) && (!
        (((x_1)[(Bit#(1))'(1'h0)]).victim_req)) ? ((Bool)'(True)) :
        ((Bool)'(False))))));
        return x_2;
    endmethod

    method Action victims__000__setVictimRq (Bit#(64) x_0);
        let x_1 = (victimRegs__000);
        Struct13 x_2 =
        ((x_1)[(Bit#(1))'(1'h1)]);
        if (((x_2).victim_valid) && (((x_2).victim_addr) == (x_0)))
            begin
            Struct13 x_3 = (Struct13 {victim_valid : (x_2).victim_valid,
            victim_addr : (x_2).victim_addr, victim_info : (x_2).victim_info,
            victim_value : (x_2).victim_value, victim_req :
            (Bool)'(True)});
            victimRegs__000 <= update (x_1, (Bit#(1))'(1'h1), x_3);
        end else begin
            Struct13 x_4 =
            ((x_1)[(Bit#(1))'(1'h0)]);
            if (((x_4).victim_valid) && (((x_4).victim_addr) == (x_0)))
                begin
                Struct13 x_5 = (Struct13 {victim_valid : (x_4).victim_valid,
                victim_addr : (x_4).victim_addr, victim_info :
                (x_4).victim_info, victim_value : (x_4).victim_value,
                victim_req : (Bool)'(True)});
                victimRegs__000 <= update (x_1, (Bit#(1))'(1'h0), x_5);
            end else begin

            end
        end
    endmethod

    method Action victims__000__releaseVictim (Bit#(64) x_0);
        let x_1 = (victimRegs__000);
        Struct13 x_2 =
        ((x_1)[(Bit#(1))'(1'h0)]);
        if (((x_2).victim_valid) && (((x_2).victim_addr) == (x_0)))
            begin
            victimRegs__000 <= update (x_1, (Bit#(1))'(1'h0), unpack(0));
        end else begin
            Struct13 x_3 =
            ((x_1)[(Bit#(1))'(1'h1)]);
            if (((x_3).victim_valid) && (((x_3).victim_addr) == (x_0)))
                begin
                victimRegs__000 <= update (x_1, (Bit#(1))'(1'h1), unpack(0));
            end else begin

            end
        end
    endmethod
endmodule

interface Module46;
    method Action rdReq_infoRam__000__3 (Bit#(8) x_0);
    method Action wrReq_infoRam__000__3 (Struct47 x_0);
    method ActionValue#(Struct45) rdResp_infoRam__000__3 ();
endinterface

module mkModule46 (Module46);
    RWBramCore#(Bit#(8), Struct45) bram <- mkRWBramCore();
    Reg#(Bool) initDone <- mkReg(False);
    Reg#(Bit#(8)) initIdx <- mkReg(0);

    rule init (!initDone);
        let initData = Struct45 {tag: 51'h7, value: Struct10 {mesi_owned: False, mesi_status: 3'h1, mesi_dir_st: 3'h1, mesi_dir_sharers: 4'h0}};
        bram.wrReq(initIdx, initData);
        initIdx <= initIdx + 1;
        initDone <= (initIdx == maxBound);
    endrule

    method Action rdReq_infoRam__000__3 (Bit#(8) x_0) if(initDone);
        bram.rdReq(x_0);
    endmethod

    method Action wrReq_infoRam__000__3 (Struct47 x_0) if(initDone);
        bram.wrReq(x_0.addr, x_0.datain);
    endmethod

    method ActionValue#(Struct45) rdResp_infoRam__000__3 () if(initDone);
        bram.deqRdResp ();
        let data = bram.rdResp ();
        return data;
    endmethod


endmodule

interface Module47;
    method Action rdReq_infoRam__000__2 (Bit#(8) x_0);
    method Action wrReq_infoRam__000__2 (Struct47 x_0);
    method ActionValue#(Struct45) rdResp_infoRam__000__2 ();
endinterface

module mkModule47 (Module47);
    RWBramCore#(Bit#(8), Struct45) bram <- mkRWBramCore();
    Reg#(Bool) initDone <- mkReg(False);
    Reg#(Bit#(8)) initIdx <- mkReg(0);

    rule init (!initDone);
        let initData = Struct45 {tag: 51'h6, value: Struct10 {mesi_owned: False, mesi_status: 3'h1, mesi_dir_st: 3'h1, mesi_dir_sharers: 4'h0}};
        bram.wrReq(initIdx, initData);
        initIdx <= initIdx + 1;
        initDone <= (initIdx == maxBound);
    endrule

    method Action rdReq_infoRam__000__2 (Bit#(8) x_0) if(initDone);
        bram.rdReq(x_0);
    endmethod

    method Action wrReq_infoRam__000__2 (Struct47 x_0) if(initDone);
        bram.wrReq(x_0.addr, x_0.datain);
    endmethod

    method ActionValue#(Struct45) rdResp_infoRam__000__2 () if(initDone);
        bram.deqRdResp ();
        let data = bram.rdResp ();
        return data;
    endmethod


endmodule

interface Module48;
    method Action rdReq_infoRam__000__1 (Bit#(8) x_0);
    method Action wrReq_infoRam__000__1 (Struct47 x_0);
    method ActionValue#(Struct45) rdResp_infoRam__000__1 ();
endinterface

module mkModule48 (Module48);
    RWBramCore#(Bit#(8), Struct45) bram <- mkRWBramCore();
    Reg#(Bool) initDone <- mkReg(False);
    Reg#(Bit#(8)) initIdx <- mkReg(0);

    rule init (!initDone);
        let initData = Struct45 {tag: 51'h5, value: Struct10 {mesi_owned: False, mesi_status: 3'h1, mesi_dir_st: 3'h1, mesi_dir_sharers: 4'h0}};
        bram.wrReq(initIdx, initData);
        initIdx <= initIdx + 1;
        initDone <= (initIdx == maxBound);
    endrule

    method Action rdReq_infoRam__000__1 (Bit#(8) x_0) if(initDone);
        bram.rdReq(x_0);
    endmethod

    method Action wrReq_infoRam__000__1 (Struct47 x_0) if(initDone);
        bram.wrReq(x_0.addr, x_0.datain);
    endmethod

    method ActionValue#(Struct45) rdResp_infoRam__000__1 () if(initDone);
        bram.deqRdResp ();
        let data = bram.rdResp ();
        return data;
    endmethod


endmodule

interface Module49;
    method Action rdReq_infoRam__000__0 (Bit#(8) x_0);
    method Action wrReq_infoRam__000__0 (Struct47 x_0);
    method ActionValue#(Struct45) rdResp_infoRam__000__0 ();
endinterface

module mkModule49 (Module49);
    RWBramCore#(Bit#(8), Struct45) bram <- mkRWBramCore();
    Reg#(Bool) initDone <- mkReg(False);
    Reg#(Bit#(8)) initIdx <- mkReg(0);

    rule init (!initDone);
        let initData = Struct45 {tag: 51'h4, value: Struct10 {mesi_owned: False, mesi_status: 3'h1, mesi_dir_st: 3'h1, mesi_dir_sharers: 4'h0}};
        bram.wrReq(initIdx, initData);
        initIdx <= initIdx + 1;
        initDone <= (initIdx == maxBound);
    endrule

    method Action rdReq_infoRam__000__0 (Bit#(8) x_0) if(initDone);
        bram.rdReq(x_0);
    endmethod

    method Action wrReq_infoRam__000__0 (Struct47 x_0) if(initDone);
        bram.wrReq(x_0.addr, x_0.datain);
    endmethod

    method ActionValue#(Struct45) rdResp_infoRam__000__0 () if(initDone);
        bram.deqRdResp ();
        let data = bram.rdResp ();
        return data;
    endmethod


endmodule

interface Module50;
    method Action rdReq_dataRam__000 (Bit#(10) x_0);
    method Action wrReq_dataRam__000 (Struct49 x_0);
    method ActionValue#(Vector#(4, Bit#(64))) rdResp_dataRam__000 ();
endinterface

module mkModule50 (Module50);
    RWBramCore#(Bit#(10), Vector#(4, Bit#(64))) bram <- mkRWBramCore();
    Reg#(Bool) initDone <- mkReg(False);
    Reg#(Bit#(10)) initIdx <- mkReg(0);

    rule init (!initDone);
        let initData = vec(64'h0, 64'h0, 64'h0, 64'h0);
        bram.wrReq(initIdx, initData);
        initIdx <= initIdx + 1;
        initDone <= (initIdx == maxBound);
    endrule

    method Action rdReq_dataRam__000 (Bit#(10) x_0) if(initDone);
        bram.rdReq(x_0);
    endmethod

    method Action wrReq_dataRam__000 (Struct49 x_0) if(initDone);
        bram.wrReq(x_0.addr, x_0.datain);
    endmethod

    method ActionValue#(Vector#(4, Bit#(64))) rdResp_dataRam__000 ()
    if(initDone);
        bram.deqRdResp ();
        let data = bram.rdResp ();
        return data;
    endmethod


endmodule

interface Module51;
    method Action rdReq_repRam__000 (Bit#(8) x_0);
    method Action wrReq_repRam__000 (Struct50 x_0);
    method ActionValue#(Vector#(4, Bit#(8))) rdResp_repRam__000 ();
endinterface

module mkModule51 (Module51);
    RWBramCore#(Bit#(8), Vector#(4, Bit#(8))) bram <- mkRWBramCore();
    Reg#(Bool) initDone <- mkReg(False);
    Reg#(Bit#(8)) initIdx <- mkReg(0);

    rule init (!initDone);
        let initData = vec(8'h1, 8'h1, 8'h1, 8'h1);
        bram.wrReq(initIdx, initData);
        initIdx <= initIdx + 1;
        initDone <= (initIdx == maxBound);
    endrule

    method Action rdReq_repRam__000 (Bit#(8) x_0) if(initDone);
        bram.rdReq(x_0);
    endmethod

    method Action wrReq_repRam__000 (Struct50 x_0) if(initDone);
        bram.wrReq(x_0.addr, x_0.datain);
    endmethod

    method ActionValue#(Vector#(4, Bit#(8))) rdResp_repRam__000 ()
    if(initDone);
        bram.deqRdResp ();
        let data = bram.rdResp ();
        return data;
    endmethod


endmodule

interface Module52;
    method ActionValue#(Struct14) getMSHR_000 (Bit#(2) x_0);
    method ActionValue#(Struct1) getMSHRRq_000 (Bit#(2) x_0);
    method ActionValue#(Struct36) getPRqSlot_000 (Struct35 x_0);
    method ActionValue#(Struct36) getCRqSlot_000 (Struct35 x_0);
    method ActionValue#(Struct35) getWait_000 ();
    method Action registerUL_000 (Struct43 x_0);
    method Action canImm_000 (Bit#(64) x_0);
    method Action setULImm_000 (Struct1 x_0);
    method ActionValue#(Bit#(2)) getULReady_000 (Bit#(64) x_0);
    method Action startRelease_000 (Bit#(2) x_0);
    method Action releaseMSHR_000 (Bit#(2) x_0);
endinterface

module mkModule52
    (Module52);
    Reg#(Vector#(4, Struct14)) mshrs_000 <- mkReg(unpack(0));
    Reg#(Vector#(4, Bit#(64))) maddrs_000 <- mkReg(unpack(0));
    Reg#(Vector#(4, Bit#(3))) msts_000 <- mkReg(unpack(0));
    Reg#(Vector#(4, Struct51)) mnexts_000 <- mkReg(unpack(0));
    Reg#(Vector#(4, Struct1)) rqs_000 <- mkReg(unpack(0));

    // No rules in this module

    method ActionValue#(Struct14) getMSHR_000 (Bit#(2) x_0);
        let x_1 = (mshrs_000);
        return (x_1)[x_0];
    endmethod

    method ActionValue#(Struct1) getMSHRRq_000 (Bit#(2) x_0);
        let x_1 = (rqs_000);
        return (x_1)[x_0];
    endmethod

    method ActionValue#(Struct36) getPRqSlot_000 (Struct35 x_0);
        let x_1 = (mshrs_000);
        let x_2 = (maddrs_000);
        let x_3 = (msts_000);
        let x_4 = (mnexts_000);
        Struct51 x_5 = ((((x_3)[(Bit#(2))'(2'h0)]) == ((Bit#(3))'(3'h0)) ?
        (Struct51 {valid : (Bool)'(True), data : (Bit#(2))'(2'h0)}) :
        ((((x_3)[(Bit#(2))'(2'h1)]) == ((Bit#(3))'(3'h0)) ? (Struct51 {valid
        : (Bool)'(True), data : (Bit#(2))'(2'h1)}) : (Struct51 {valid :
        (Bool)'(False), data : unpack(0)})))));
        Bool x_6 = ((x_5).valid);
        Bit#(2) x_7 = ((x_5).data);
        Bit#(64) x_8 = (((x_0).r_msg).addr);
        Bool x_9 = ((((((x_3)[(Bit#(2))'(2'h0)]) == ((Bit#(3))'(3'h4))) ||
        (((x_3)[(Bit#(2))'(2'h0)]) == ((Bit#(3))'(3'h6)))) && (((!
        (((x_2)[(Bit#(2))'(2'h0)]) == (x_8))) &&
        ((((x_2)[(Bit#(2))'(2'h0)])[12:5]) == ((x_8)[12:5]))) ||
        (((x_2)[(Bit#(2))'(2'h0)]) == (x_8))) ? ((Bool)'(True)) :
        ((((((x_3)[(Bit#(2))'(2'h1)]) == ((Bit#(3))'(3'h4))) ||
        (((x_3)[(Bit#(2))'(2'h1)]) == ((Bit#(3))'(3'h6)))) && (((!
        (((x_2)[(Bit#(2))'(2'h1)]) == (x_8))) &&
        ((((x_2)[(Bit#(2))'(2'h1)])[12:5]) == ((x_8)[12:5]))) ||
        (((x_2)[(Bit#(2))'(2'h1)]) == (x_8))) ? ((Bool)'(True)) :
        ((((((x_3)[(Bit#(2))'(2'h2)]) == ((Bit#(3))'(3'h4))) ||
        (((x_3)[(Bit#(2))'(2'h2)]) == ((Bit#(3))'(3'h6)))) && (((!
        (((x_2)[(Bit#(2))'(2'h2)]) == (x_8))) &&
        ((((x_2)[(Bit#(2))'(2'h2)])[12:5]) == ((x_8)[12:5]))) ||
        (((x_2)[(Bit#(2))'(2'h2)]) == (x_8))) ? ((Bool)'(True)) :
        ((((((x_3)[(Bit#(2))'(2'h3)]) == ((Bit#(3))'(3'h4))) ||
        (((x_3)[(Bit#(2))'(2'h3)]) == ((Bit#(3))'(3'h6)))) && (((!
        (((x_2)[(Bit#(2))'(2'h3)]) == (x_8))) &&
        ((((x_2)[(Bit#(2))'(2'h3)])[12:5]) == ((x_8)[12:5]))) ||
        (((x_2)[(Bit#(2))'(2'h3)]) == (x_8))) ? ((Bool)'(True)) :
        ((Bool)'(False))))))))));
        Struct51 x_10 = ((((((x_3)[(Bit#(2))'(2'h0)]) == ((Bit#(3))'(3'h5)))
        && (! (((x_1)[(Bit#(2))'(2'h0)]).m_is_ul))) &&
        (((x_2)[(Bit#(2))'(2'h0)]) == (x_8)) ? (Struct51 {valid :
        (Bool)'(True), data : (Bit#(2))'(2'h0)}) :
        ((((((x_3)[(Bit#(2))'(2'h1)]) == ((Bit#(3))'(3'h5))) && (!
        (((x_1)[(Bit#(2))'(2'h1)]).m_is_ul))) && (((x_2)[(Bit#(2))'(2'h1)])
        == (x_8)) ? (Struct51 {valid : (Bool)'(True), data :
        (Bit#(2))'(2'h1)}) : ((((((x_3)[(Bit#(2))'(2'h2)]) ==
        ((Bit#(3))'(3'h5))) && (! (((x_1)[(Bit#(2))'(2'h2)]).m_is_ul))) &&
        (((x_2)[(Bit#(2))'(2'h2)]) == (x_8)) ? (Struct51 {valid :
        (Bool)'(True), data : (Bit#(2))'(2'h2)}) :
        ((((((x_3)[(Bit#(2))'(2'h3)]) == ((Bit#(3))'(3'h5))) && (!
        (((x_1)[(Bit#(2))'(2'h3)]).m_is_ul))) && (((x_2)[(Bit#(2))'(2'h3)])
        == (x_8)) ? (Struct51 {valid : (Bool)'(True), data :
        (Bit#(2))'(2'h3)}) : (Struct51 {valid : (Bool)'(False), data :
        unpack(0)})))))))));
        Bool x_11 = ((x_10).valid);
        Struct36 x_12 = (Struct36 {s_has_slot : (x_6) && (! (x_9)),
        s_conflict : x_11, s_id :
        x_7});
        if ((x_6) && (! (x_9))) begin
            mshrs_000 <= update (x_1, x_7, Struct14 {m_is_ul : unpack(0),
            m_qidx : (x_0).r_msg_from, m_rsb : unpack(0), m_dl_rss_from :
            unpack(0), m_dl_rss_recv : unpack(0)});
            maddrs_000 <= update (x_2, x_7, ((x_0).r_msg).addr);
            msts_000 <= update (x_3, x_7, (x_11 ? ((Bit#(3))'(3'h1)) :
            ((Bit#(3))'(3'h4))));
            let x_13 = (rqs_000);
            rqs_000 <= update (x_13, x_7,
            (x_0).r_msg);
            if (x_11) begin
                Bit#(2) x_14 = ((((! (((x_3)[(Bit#(2))'(2'h0)]) ==
                ((Bit#(3))'(3'h0)))) && (!
                (((x_4)[(Bit#(2))'(2'h0)]).valid))) &&
                (((x_2)[(Bit#(2))'(2'h0)]) == (x_8)) ? ((Bit#(2))'(2'h0)) :
                ((((! (((x_3)[(Bit#(2))'(2'h1)]) == ((Bit#(3))'(3'h0)))) &&
                (! (((x_4)[(Bit#(2))'(2'h1)]).valid))) &&
                (((x_2)[(Bit#(2))'(2'h1)]) == (x_8)) ? ((Bit#(2))'(2'h1)) :
                ((((! (((x_3)[(Bit#(2))'(2'h2)]) == ((Bit#(3))'(3'h0)))) &&
                (! (((x_4)[(Bit#(2))'(2'h2)]).valid))) &&
                (((x_2)[(Bit#(2))'(2'h2)]) == (x_8)) ? ((Bit#(2))'(2'h2)) :
                ((((! (((x_3)[(Bit#(2))'(2'h3)]) == ((Bit#(3))'(3'h0)))) &&
                (! (((x_4)[(Bit#(2))'(2'h3)]).valid))) &&
                (((x_2)[(Bit#(2))'(2'h3)]) == (x_8)) ? ((Bit#(2))'(2'h3)) :
                (unpack(0))))))))));
                Struct51 x_15 = ((x_4)[x_14]);
                mnexts_000 <= update (x_4, x_14, Struct51 {valid :
                (Bool)'(True), data : x_7});
            end else begin

            end
        end else begin

        end
        return x_12;
    endmethod

    method ActionValue#(Struct36) getCRqSlot_000 (Struct35 x_0);
        let x_1 = (mshrs_000);
        let x_2 = (maddrs_000);
        let x_3 = (msts_000);
        let x_4 = (mnexts_000);
        Struct51 x_5 = ((((x_3)[(Bit#(2))'(2'h2)]) == ((Bit#(3))'(3'h0)) ?
        (Struct51 {valid : (Bool)'(True), data : (Bit#(2))'(2'h2)}) :
        ((((x_3)[(Bit#(2))'(2'h3)]) == ((Bit#(3))'(3'h0)) ? (Struct51 {valid
        : (Bool)'(True), data : (Bit#(2))'(2'h3)}) : (Struct51 {valid :
        (Bool)'(False), data : unpack(0)})))));
        Bool x_6 = ((x_5).valid);
        Bit#(2) x_7 = ((x_5).data);
        Bit#(64) x_8 = (((x_0).r_msg).addr);
        Bool x_9 = ((((((x_3)[(Bit#(2))'(2'h0)]) == ((Bit#(3))'(3'h4))) ||
        (((x_3)[(Bit#(2))'(2'h0)]) == ((Bit#(3))'(3'h6)))) && ((!
        (((x_2)[(Bit#(2))'(2'h0)]) == (x_8))) &&
        ((((x_2)[(Bit#(2))'(2'h0)])[12:5]) == ((x_8)[12:5]))) ?
        ((Bool)'(True)) : ((((((x_3)[(Bit#(2))'(2'h1)]) ==
        ((Bit#(3))'(3'h4))) || (((x_3)[(Bit#(2))'(2'h1)]) ==
        ((Bit#(3))'(3'h6)))) && ((! (((x_2)[(Bit#(2))'(2'h1)]) == (x_8))) &&
        ((((x_2)[(Bit#(2))'(2'h1)])[12:5]) == ((x_8)[12:5]))) ?
        ((Bool)'(True)) : ((((((x_3)[(Bit#(2))'(2'h2)]) ==
        ((Bit#(3))'(3'h4))) || (((x_3)[(Bit#(2))'(2'h2)]) ==
        ((Bit#(3))'(3'h6)))) && ((! (((x_2)[(Bit#(2))'(2'h2)]) == (x_8))) &&
        ((((x_2)[(Bit#(2))'(2'h2)])[12:5]) == ((x_8)[12:5]))) ?
        ((Bool)'(True)) : ((((((x_3)[(Bit#(2))'(2'h3)]) ==
        ((Bit#(3))'(3'h4))) || (((x_3)[(Bit#(2))'(2'h3)]) ==
        ((Bit#(3))'(3'h6)))) && ((! (((x_2)[(Bit#(2))'(2'h3)]) == (x_8))) &&
        ((((x_2)[(Bit#(2))'(2'h3)])[12:5]) == ((x_8)[12:5]))) ?
        ((Bool)'(True)) : ((Bool)'(False))))))))));
        Struct51 x_10 = (((((! (((x_3)[(Bit#(2))'(2'h2)]) ==
        ((Bit#(3))'(3'h0)))) && (! (((x_4)[(Bit#(2))'(2'h2)]).valid))) &&
        (((x_1)[(Bit#(2))'(2'h2)]).m_is_ul)) && (((x_2)[(Bit#(2))'(2'h2)]) ==
        (x_8)) ? (Struct51 {valid : (Bool)'(True), data : (Bit#(2))'(2'h2)})
        : (((((! (((x_3)[(Bit#(2))'(2'h3)]) == ((Bit#(3))'(3'h0)))) && (!
        (((x_4)[(Bit#(2))'(2'h3)]).valid))) &&
        (((x_1)[(Bit#(2))'(2'h3)]).m_is_ul)) && (((x_2)[(Bit#(2))'(2'h3)]) ==
        (x_8)) ? (Struct51 {valid : (Bool)'(True), data : (Bit#(2))'(2'h3)})
        : (Struct51 {valid : (Bool)'(False), data : unpack(0)})))));
        Struct51 x_11 = (((((! (((x_3)[(Bit#(2))'(2'h0)]) ==
        ((Bit#(3))'(3'h0)))) && (! (((x_4)[(Bit#(2))'(2'h0)]).valid))) && (!
        (((x_1)[(Bit#(2))'(2'h0)]).m_is_ul))) && (((x_2)[(Bit#(2))'(2'h0)])
        == (x_8)) ? (Struct51 {valid : (Bool)'(True), data :
        (Bit#(2))'(2'h0)}) : (((((! (((x_3)[(Bit#(2))'(2'h1)]) ==
        ((Bit#(3))'(3'h0)))) && (! (((x_4)[(Bit#(2))'(2'h1)]).valid))) && (!
        (((x_1)[(Bit#(2))'(2'h1)]).m_is_ul))) && (((x_2)[(Bit#(2))'(2'h1)])
        == (x_8)) ? (Struct51 {valid : (Bool)'(True), data :
        (Bit#(2))'(2'h1)}) : (((((! (((x_3)[(Bit#(2))'(2'h2)]) ==
        ((Bit#(3))'(3'h0)))) && (! (((x_4)[(Bit#(2))'(2'h2)]).valid))) && (!
        (((x_1)[(Bit#(2))'(2'h2)]).m_is_ul))) && (((x_2)[(Bit#(2))'(2'h2)])
        == (x_8)) ? (Struct51 {valid : (Bool)'(True), data :
        (Bit#(2))'(2'h2)}) : (((((! (((x_3)[(Bit#(2))'(2'h3)]) ==
        ((Bit#(3))'(3'h0)))) && (! (((x_4)[(Bit#(2))'(2'h3)]).valid))) && (!
        (((x_1)[(Bit#(2))'(2'h3)]).m_is_ul))) && (((x_2)[(Bit#(2))'(2'h3)])
        == (x_8)) ? (Struct51 {valid : (Bool)'(True), data :
        (Bit#(2))'(2'h3)}) : (Struct51 {valid : (Bool)'(False), data :
        unpack(0)})))))))));
        Bool x_12 = ((x_10).valid);
        Bool x_13 = ((x_11).valid);
        Bool x_14 = ((x_12) || (x_13));
        Struct36 x_15 = (Struct36 {s_has_slot : (x_6) && (! (x_9)),
        s_conflict : x_14, s_id :
        x_7});
        if ((x_6) && (! (x_9))) begin
            mshrs_000 <= update (x_1, x_7, Struct14 {m_is_ul : unpack(0),
            m_qidx : (x_0).r_msg_from, m_rsb : unpack(0), m_dl_rss_from :
            unpack(0), m_dl_rss_recv : unpack(0)});
            maddrs_000 <= update (x_2, x_7, ((x_0).r_msg).addr);
            msts_000 <= update (x_3, x_7, (x_14 ? ((Bit#(3))'(3'h1)) :
            ((Bit#(3))'(3'h4))));
            let x_16 = (rqs_000);
            rqs_000 <= update (x_16, x_7,
            (x_0).r_msg);
            if (x_14) begin
                Bit#(2) x_17 = ((x_12 ? ((x_10).data) :
                ((x_11).data)));
                Struct51 x_18 = ((x_4)[x_17]);
                mnexts_000 <= update (x_4, x_17, Struct51 {valid :
                (Bool)'(True), data : x_7});
            end else begin

            end
        end else begin

        end
        return x_15;
    endmethod

    method ActionValue#(Struct35) getWait_000 ();
        let x_1 = (mshrs_000);
        let x_2 = (maddrs_000);
        let x_3 = (msts_000);
        let x_4 = (rqs_000);
        Struct51 x_5 = ((((x_3)[(Bit#(2))'(2'h0)]) == ((Bit#(3))'(3'h2)) ?
        (Struct51 {valid : (Bool)'(True), data : (Bit#(2))'(2'h0)}) :
        ((((x_3)[(Bit#(2))'(2'h1)]) == ((Bit#(3))'(3'h2)) ? (Struct51 {valid
        : (Bool)'(True), data : (Bit#(2))'(2'h1)}) :
        ((((x_3)[(Bit#(2))'(2'h2)]) == ((Bit#(3))'(3'h2)) ? (Struct51 {valid
        : (Bool)'(True), data : (Bit#(2))'(2'h2)}) :
        ((((x_3)[(Bit#(2))'(2'h3)]) == ((Bit#(3))'(3'h2)) ? (Struct51 {valid
        : (Bool)'(True), data : (Bit#(2))'(2'h3)}) : (Struct51 {valid :
        (Bool)'(False), data : unpack(0)})))))))));
        when ((x_5).valid, noAction);
        Bit#(2) x_6 = ((x_5).data);
        Struct14 x_7 = ((x_1)[x_6]);
        Bit#(64) x_8 = ((x_2)[x_6]);
        Struct1 x_9 = ((x_4)[x_6]);
        Bool x_10 = ((((! (((x_3)[(Bit#(2))'(2'h0)]) < ((Bit#(3))'(3'h4))))
        && (((x_2)[(Bit#(2))'(2'h0)]) == (x_8))) ||
        (((((x_3)[(Bit#(2))'(2'h0)]) == ((Bit#(3))'(3'h4))) ||
        (((x_3)[(Bit#(2))'(2'h0)]) == ((Bit#(3))'(3'h6)))) && ((!
        (((x_2)[(Bit#(2))'(2'h0)]) == (x_8))) &&
        ((((x_2)[(Bit#(2))'(2'h0)])[12:5]) == ((x_8)[12:5])))) ?
        ((Bool)'(True)) : ((((! (((x_3)[(Bit#(2))'(2'h1)]) <
        ((Bit#(3))'(3'h4)))) && (((x_2)[(Bit#(2))'(2'h1)]) == (x_8))) ||
        (((((x_3)[(Bit#(2))'(2'h1)]) == ((Bit#(3))'(3'h4))) ||
        (((x_3)[(Bit#(2))'(2'h1)]) == ((Bit#(3))'(3'h6)))) && ((!
        (((x_2)[(Bit#(2))'(2'h1)]) == (x_8))) &&
        ((((x_2)[(Bit#(2))'(2'h1)])[12:5]) == ((x_8)[12:5])))) ?
        ((Bool)'(True)) : ((((! (((x_3)[(Bit#(2))'(2'h2)]) <
        ((Bit#(3))'(3'h4)))) && (((x_2)[(Bit#(2))'(2'h2)]) == (x_8))) ||
        (((((x_3)[(Bit#(2))'(2'h2)]) == ((Bit#(3))'(3'h4))) ||
        (((x_3)[(Bit#(2))'(2'h2)]) == ((Bit#(3))'(3'h6)))) && ((!
        (((x_2)[(Bit#(2))'(2'h2)]) == (x_8))) &&
        ((((x_2)[(Bit#(2))'(2'h2)])[12:5]) == ((x_8)[12:5])))) ?
        ((Bool)'(True)) : ((((! (((x_3)[(Bit#(2))'(2'h3)]) <
        ((Bit#(3))'(3'h4)))) && (((x_2)[(Bit#(2))'(2'h3)]) == (x_8))) ||
        (((((x_3)[(Bit#(2))'(2'h3)]) == ((Bit#(3))'(3'h4))) ||
        (((x_3)[(Bit#(2))'(2'h3)]) == ((Bit#(3))'(3'h6)))) && ((!
        (((x_2)[(Bit#(2))'(2'h3)]) == (x_8))) &&
        ((((x_2)[(Bit#(2))'(2'h3)])[12:5]) == ((x_8)[12:5])))) ?
        ((Bool)'(True)) : ((Bool)'(False))))))))));
        when (! (x_10), noAction);
        msts_000 <= update (x_3, x_6, (Bit#(3))'(3'h4));
        Struct35 x_11 = (Struct35 {r_id : x_6, r_msg : x_9, r_msg_from :
        (x_7).m_qidx});
        return x_11;
    endmethod

    method Action registerUL_000 (Struct43 x_0);
        let x_1 = (mshrs_000);
        let x_2 = (msts_000);
        Bit#(2) x_3 = ((x_0).r_id);
        mshrs_000 <= update (x_1, x_3, Struct14 {m_is_ul : (Bool)'(True),
        m_qidx : {((Bit#(2))'(2'h2)),((x_0).r_ul_rsbTo)}, m_rsb :
        (x_0).r_ul_rsb, m_dl_rss_from : unpack(0), m_dl_rss_recv :
        unpack(0)});
        msts_000 <= update (x_2, x_3, (Bit#(3))'(3'h5));
    endmethod

    method Action canImm_000 (Bit#(64) x_0);
        let x_1 = (maddrs_000);
        let x_2 = (msts_000);
        let x_3 = (mnexts_000);
        Struct51 x_4 = ((((x_2)[(Bit#(2))'(2'h2)]) == ((Bit#(3))'(3'h0)) ?
        (Struct51 {valid : (Bool)'(True), data : (Bit#(2))'(2'h2)}) :
        ((((x_2)[(Bit#(2))'(2'h3)]) == ((Bit#(3))'(3'h0)) ? (Struct51 {valid
        : (Bool)'(True), data : (Bit#(2))'(2'h3)}) : (Struct51 {valid :
        (Bool)'(False), data : unpack(0)})))));
        when ((x_4).valid, noAction);
        Struct51 x_5 = ((((! (((x_2)[(Bit#(2))'(2'h0)]) ==
        ((Bit#(3))'(3'h0)))) && (! (((x_3)[(Bit#(2))'(2'h0)]).valid))) &&
        (((x_1)[(Bit#(2))'(2'h0)]) == (x_0)) ? (Struct51 {valid :
        (Bool)'(True), data : (Bit#(2))'(2'h0)}) : ((((!
        (((x_2)[(Bit#(2))'(2'h1)]) == ((Bit#(3))'(3'h0)))) && (!
        (((x_3)[(Bit#(2))'(2'h1)]).valid))) && (((x_1)[(Bit#(2))'(2'h1)]) ==
        (x_0)) ? (Struct51 {valid : (Bool)'(True), data : (Bit#(2))'(2'h1)})
        : ((((! (((x_2)[(Bit#(2))'(2'h2)]) == ((Bit#(3))'(3'h0)))) && (!
        (((x_3)[(Bit#(2))'(2'h2)]).valid))) && (((x_1)[(Bit#(2))'(2'h2)]) ==
        (x_0)) ? (Struct51 {valid : (Bool)'(True), data : (Bit#(2))'(2'h2)})
        : ((((! (((x_2)[(Bit#(2))'(2'h3)]) == ((Bit#(3))'(3'h0)))) && (!
        (((x_3)[(Bit#(2))'(2'h3)]).valid))) && (((x_1)[(Bit#(2))'(2'h3)]) ==
        (x_0)) ? (Struct51 {valid : (Bool)'(True), data : (Bit#(2))'(2'h3)})
        : (Struct51 {valid : (Bool)'(False), data : unpack(0)})))))))));
        when (! ((x_5).valid), noAction);
    endmethod

    method Action setULImm_000 (Struct1 x_0);
        let x_1 = (mshrs_000);
        let x_2 = (maddrs_000);
        let x_3 = (msts_000);
        let x_4 = (rqs_000);
        Struct51 x_5 = ((((x_3)[(Bit#(2))'(2'h2)]) == ((Bit#(3))'(3'h0)) ?
        (Struct51 {valid : (Bool)'(True), data : (Bit#(2))'(2'h2)}) :
        ((((x_3)[(Bit#(2))'(2'h3)]) == ((Bit#(3))'(3'h0)) ? (Struct51 {valid
        : (Bool)'(True), data : (Bit#(2))'(2'h3)}) : (Struct51 {valid :
        (Bool)'(False), data : unpack(0)})))));
        when ((x_5).valid, noAction);
        Bit#(2) x_6 = ((x_5).data);
        Bit#(64) x_7 = ((x_0).addr);
        Struct51 x_8 = (((! (((x_3)[(Bit#(2))'(2'h0)]) ==
        ((Bit#(3))'(3'h0)))) && (((x_2)[(Bit#(2))'(2'h0)]) == (x_7)) ?
        (Struct51 {valid : (Bool)'(True), data : (Bit#(2))'(2'h0)}) : (((!
        (((x_3)[(Bit#(2))'(2'h1)]) == ((Bit#(3))'(3'h0)))) &&
        (((x_2)[(Bit#(2))'(2'h1)]) == (x_7)) ? (Struct51 {valid :
        (Bool)'(True), data : (Bit#(2))'(2'h1)}) : (((!
        (((x_3)[(Bit#(2))'(2'h2)]) == ((Bit#(3))'(3'h0)))) &&
        (((x_2)[(Bit#(2))'(2'h2)]) == (x_7)) ? (Struct51 {valid :
        (Bool)'(True), data : (Bit#(2))'(2'h2)}) : (((!
        (((x_3)[(Bit#(2))'(2'h3)]) == ((Bit#(3))'(3'h0)))) &&
        (((x_2)[(Bit#(2))'(2'h3)]) == (x_7)) ? (Struct51 {valid :
        (Bool)'(True), data : (Bit#(2))'(2'h3)}) : (Struct51 {valid :
        (Bool)'(False), data : unpack(0)})))))))));
        when (! ((x_8).valid), noAction);
        mshrs_000 <= update (x_1, x_6, Struct14 {m_is_ul : (Bool)'(True),
        m_qidx : unpack(0), m_rsb : (Bool)'(False), m_dl_rss_from :
        unpack(0), m_dl_rss_recv : unpack(0)});
        maddrs_000 <= update (x_2, x_6, (x_0).addr);
        msts_000 <= update (x_3, x_6, (Bit#(3))'(3'h5));
        rqs_000 <= update (x_4, x_6, x_0);
    endmethod

    method ActionValue#(Bit#(2)) getULReady_000 (Bit#(64) x_0);
        let x_1 = (mshrs_000);
        let x_2 = (maddrs_000);
        let x_3 = (msts_000);
        Bool x_4 = (((((((x_3)[(Bit#(2))'(2'h0)]) == ((Bit#(3))'(3'h4))) ||
        (((x_3)[(Bit#(2))'(2'h0)]) == ((Bit#(3))'(3'h6)))) && ((!
        (((x_2)[(Bit#(2))'(2'h0)]) == (x_0))) &&
        ((((x_2)[(Bit#(2))'(2'h0)])[12:5]) == ((x_0)[12:5])))) || (((!
        (((x_3)[(Bit#(2))'(2'h0)]) < ((Bit#(3))'(3'h4)))) && (!
        (((x_1)[(Bit#(2))'(2'h0)]).m_is_ul))) && (((x_2)[(Bit#(2))'(2'h0)])
        == (x_0))) ? ((Bool)'(True)) : (((((((x_3)[(Bit#(2))'(2'h1)]) ==
        ((Bit#(3))'(3'h4))) || (((x_3)[(Bit#(2))'(2'h1)]) ==
        ((Bit#(3))'(3'h6)))) && ((! (((x_2)[(Bit#(2))'(2'h1)]) == (x_0))) &&
        ((((x_2)[(Bit#(2))'(2'h1)])[12:5]) == ((x_0)[12:5])))) || (((!
        (((x_3)[(Bit#(2))'(2'h1)]) < ((Bit#(3))'(3'h4)))) && (!
        (((x_1)[(Bit#(2))'(2'h1)]).m_is_ul))) && (((x_2)[(Bit#(2))'(2'h1)])
        == (x_0))) ? ((Bool)'(True)) : (((((((x_3)[(Bit#(2))'(2'h2)]) ==
        ((Bit#(3))'(3'h4))) || (((x_3)[(Bit#(2))'(2'h2)]) ==
        ((Bit#(3))'(3'h6)))) && ((! (((x_2)[(Bit#(2))'(2'h2)]) == (x_0))) &&
        ((((x_2)[(Bit#(2))'(2'h2)])[12:5]) == ((x_0)[12:5])))) || (((!
        (((x_3)[(Bit#(2))'(2'h2)]) < ((Bit#(3))'(3'h4)))) && (!
        (((x_1)[(Bit#(2))'(2'h2)]).m_is_ul))) && (((x_2)[(Bit#(2))'(2'h2)])
        == (x_0))) ? ((Bool)'(True)) : (((((((x_3)[(Bit#(2))'(2'h3)]) ==
        ((Bit#(3))'(3'h4))) || (((x_3)[(Bit#(2))'(2'h3)]) ==
        ((Bit#(3))'(3'h6)))) && ((! (((x_2)[(Bit#(2))'(2'h3)]) == (x_0))) &&
        ((((x_2)[(Bit#(2))'(2'h3)])[12:5]) == ((x_0)[12:5])))) || (((!
        (((x_3)[(Bit#(2))'(2'h3)]) < ((Bit#(3))'(3'h4)))) && (!
        (((x_1)[(Bit#(2))'(2'h3)]).m_is_ul))) && (((x_2)[(Bit#(2))'(2'h3)])
        == (x_0))) ? ((Bool)'(True)) : ((Bool)'(False))))))))));
        when (! (x_4), noAction);
        Struct51 x_5 = ((((((x_3)[(Bit#(2))'(2'h2)]) == ((Bit#(3))'(3'h5)))
        && (((x_1)[(Bit#(2))'(2'h2)]).m_is_ul)) && (((x_2)[(Bit#(2))'(2'h2)])
        == (x_0)) ? (Struct51 {valid : (Bool)'(True), data :
        (Bit#(2))'(2'h2)}) : ((((((x_3)[(Bit#(2))'(2'h3)]) ==
        ((Bit#(3))'(3'h5))) && (((x_1)[(Bit#(2))'(2'h3)]).m_is_ul)) &&
        (((x_2)[(Bit#(2))'(2'h3)]) == (x_0)) ? (Struct51 {valid :
        (Bool)'(True), data : (Bit#(2))'(2'h3)}) : (Struct51 {valid :
        (Bool)'(False), data : unpack(0)})))));
        when ((x_5).valid, noAction);
        Bit#(2) x_6 = ((x_5).data);
        return x_6;
    endmethod

    method Action startRelease_000 (Bit#(2) x_0);
        let x_1 = (msts_000);
        msts_000 <= update (x_1, x_0, (Bit#(3))'(3'h6));
    endmethod

    method Action releaseMSHR_000 (Bit#(2) x_0);
        let x_1 = (mshrs_000);
        let x_2 = (msts_000);
        let x_3 = (mnexts_000);
        mshrs_000 <= update (x_1, x_0, unpack(0));
        mnexts_000 <= update (x_3, x_0, unpack(0));
        Vector#(4, Bit#(3)) x_4 = (update (x_2, x_0, unpack(0)));
        Struct51 x_5 =
        ((x_3)[x_0]);
        let x_8 = ?;
        if ((x_5).valid) begin
            Bit#(2) x_6 = ((x_5).data);
            Vector#(4, Bit#(3)) x_7 = (update (x_4, x_6,
            (Bit#(3))'(3'h2)));
            x_8 = x_7;
        end else begin
            x_8 = x_4;
        end
        msts_000 <= x_8;
    endmethod
endmodule

interface Module53;
    method Action enq_fifoCRqInput_001 (Struct2 x_0);
    method ActionValue#(Struct2) deq_fifoCRqInput_001 ();
endinterface

module mkModule53 (Module53);
    FIFOF#(Struct2) pff <- mkSizedFIFOF(4);

    method Action enq_fifoCRqInput_001 (Struct2 x_0);
        pff.enq(x_0);
    endmethod

    method ActionValue#(Struct2) deq_fifoCRqInput_001 ();
        pff.deq();
        return pff.first();
    endmethod

endmodule

interface Module54;
    method Action enq_fifoPInput_001 (Struct2 x_0);
    method ActionValue#(Struct2) deq_fifoPInput_001 ();
endinterface

module mkModule54 (Module54);
    FIFOF#(Struct2) pff <- mkSizedFIFOF(4);

    method Action enq_fifoPInput_001 (Struct2 x_0);
        pff.enq(x_0);
    endmethod

    method ActionValue#(Struct2) deq_fifoPInput_001 ();
        pff.deq();
        return pff.first();
    endmethod

endmodule

interface Module55;
    method Action enq_fifoN2I_001 (Struct38 x_0);
    method ActionValue#(Struct38) deq_fifoN2I_001 ();
endinterface

module mkModule55 (Module55);
    FIFOF#(Struct38) pff <- mkPipelineFIFOF();

    method Action enq_fifoN2I_001 (Struct38 x_0);
        pff.enq(x_0);
    endmethod

    method ActionValue#(Struct38) deq_fifoN2I_001 ();
        pff.deq();
        return pff.first();
    endmethod

endmodule

interface Module56;
    method Action enq_fifoI2L_001 (Struct38 x_0);
    method ActionValue#(Struct38) deq_fifoI2L_001 ();
endinterface

module mkModule56 (Module56);
    FIFOF#(Struct38) pff <- mkPipelineFIFOF();

    method Action enq_fifoI2L_001 (Struct38 x_0);
        pff.enq(x_0);
    endmethod

    method ActionValue#(Struct38) deq_fifoI2L_001 ();
        pff.deq();
        return pff.first();
    endmethod

endmodule

interface Module57;
    method Action enq_fifoL2E_001 (Struct41 x_0);
    method ActionValue#(Struct41) deq_fifoL2E_001 ();
endinterface

module mkModule57 (Module57);
    FIFOF#(Struct41) pff <- mkPipelineFIFOF();

    method Action enq_fifoL2E_001 (Struct41 x_0);
        pff.enq(x_0);
    endmethod

    method ActionValue#(Struct41) deq_fifoL2E_001 ();
        pff.deq();
        return pff.first();
    endmethod

endmodule

interface Module58;
    method Action enq_fifo0010 (Struct1 x_0);
    method ActionValue#(Struct1) deq_fifo0010 ();
endinterface

module mkModule58 (Module58);
    FIFOF#(Struct1) pff <- mkSizedFIFOF(2);

    method Action enq_fifo0010 (Struct1 x_0);
        pff.enq(x_0);
    endmethod

    method ActionValue#(Struct1) deq_fifo0010 ();
        pff.deq();
        return pff.first();
    endmethod

endmodule

interface Module59;
    method Action enq_fifo0011 (Struct1 x_0);
    method ActionValue#(Struct1) deq_fifo0011 ();
endinterface

module mkModule59 (Module59);
    FIFOF#(Struct1) pff <- mkSizedFIFOF(2);

    method Action enq_fifo0011 (Struct1 x_0);
        pff.enq(x_0);
    endmethod

    method ActionValue#(Struct1) deq_fifo0011 ();
        pff.deq();
        return pff.first();
    endmethod

endmodule

interface Module60;
    method Action enq_fifo0012 (Struct1 x_0);
    method ActionValue#(Struct1) deq_fifo0012 ();
endinterface

module mkModule60 (Module60);
    FIFOF#(Struct1) pff <- mkSizedFIFOF(2);

    method Action enq_fifo0012 (Struct1 x_0);
        pff.enq(x_0);
    endmethod

    method ActionValue#(Struct1) deq_fifo0012 ();
        pff.deq();
        return pff.first();
    endmethod

endmodule

interface Module61;
    method Action enq_fifo00100 (Struct1 x_0);
    method ActionValue#(Struct1) deq_fifo00100 ();
endinterface

module mkModule61 (Module61);
    FIFOF#(Struct1) pff <- mkSizedFIFOF(2);

    method Action enq_fifo00100 (Struct1 x_0);
        pff.enq(x_0);
    endmethod

    method ActionValue#(Struct1) deq_fifo00100 ();
        pff.deq();
        return pff.first();
    endmethod

endmodule

interface Module62;
    method Action enq_fifo00102 (Struct1 x_0);
    method ActionValue#(Struct1) deq_fifo00102 ();
endinterface

module mkModule62 (Module62);
    FIFOF#(Struct1) pff <- mkSizedFIFOF(2);

    method Action enq_fifo00102 (Struct1 x_0);
        pff.enq(x_0);
    endmethod

    method ActionValue#(Struct1) deq_fifo00102 ();
        pff.deq();
        return pff.first();
    endmethod

endmodule

interface Module63;
    method ActionValue#(Struct37) victims__001__findVictim (Bit#(64) x_0);
    method ActionValue#(Struct13) victims__001__getVictim (Bit#(1) x_0);
    method Action victims__001__setVictim (Struct44 x_0);
    method Action victims__001__registerVictim (Struct13 x_0);
    method ActionValue#(Struct13) victims__001__getFirstVictim ();
    method ActionValue#(Bool) victims__001__hasVictim ();
    method Action victims__001__setVictimRq (Bit#(64) x_0);
    method Action victims__001__releaseVictim (Bit#(64) x_0);
endinterface

module mkModule63
    (Module63);
    Reg#(Vector#(2, Struct13)) victimRegs__001 <- mkReg(unpack(0));

    // No rules in this module

    method ActionValue#(Struct37) victims__001__findVictim (Bit#(64) x_0);
        let x_1 = (victimRegs__001);
        Struct13 x_2 =
        ((x_1)[(Bit#(1))'(1'h0)]);
        let x_5 = ?;
        if (((x_2).victim_valid) && (((x_2).victim_addr) == (x_0))) begin
            x_5 = Struct37 {valid : (Bool)'(True), data : (Bit#(1))'(1'h0)};
        end else begin
            Struct13 x_3 =
            ((x_1)[(Bit#(1))'(1'h1)]);
            let x_4 = ?;
            if (((x_3).victim_valid) && (((x_3).victim_addr) == (x_0)))
                begin
                x_4 = Struct37 {valid : (Bool)'(True), data :
                (Bit#(1))'(1'h1)};
            end else begin
                x_4 = Struct37 {valid : (Bool)'(False), data : unpack(0)};
            end
            x_5 = x_4;
        end
        return x_5;
    endmethod

    method ActionValue#(Struct13) victims__001__getVictim (Bit#(1) x_0);
        let x_1 = (victimRegs__001);
        return (x_1)[x_0];
    endmethod

    method Action victims__001__setVictim (Struct44 x_0);
        let x_1 = (victimRegs__001);
        Struct13 x_2 = ((x_1)[(x_0).victim_idx]);
        Struct13 x_3 = (Struct13 {victim_valid : (Bool)'(True), victim_addr :
        (x_2).victim_addr, victim_info : (x_0).victim_info, victim_value :
        (x_0).victim_value, victim_req : (x_2).victim_req});
        victimRegs__001 <= update (x_1, (x_0).victim_idx, x_3);
    endmethod

    method Action victims__001__registerVictim (Struct13 x_0);
        let x_1 = (victimRegs__001);
        Struct37 x_2 = ((((x_1)[(Bit#(1))'(1'h1)]).victim_valid ?
        ((((x_1)[(Bit#(1))'(1'h0)]).victim_valid ? (Struct37 {valid :
        (Bool)'(False), data : unpack(0)}) : (Struct37 {valid :
        (Bool)'(True), data : (Bit#(1))'(1'h0)}))) : (Struct37 {valid :
        (Bool)'(True), data : (Bit#(1))'(1'h1)})));
        when ((x_2).valid, noAction);
        Bit#(1) x_3 = ((x_2).data);
        victimRegs__001 <= update (x_1, x_3, x_0);
    endmethod

    method ActionValue#(Struct13) victims__001__getFirstVictim ();
        let x_1 = (victimRegs__001);
        Struct33 x_2 = (((((x_1)[(Bit#(1))'(1'h1)]).victim_valid) && (!
        (((x_1)[(Bit#(1))'(1'h1)]).victim_req)) ? (Struct33 {valid :
        (Bool)'(True), data : (x_1)[(Bit#(1))'(1'h1)]}) :
        (((((x_1)[(Bit#(1))'(1'h0)]).victim_valid) && (!
        (((x_1)[(Bit#(1))'(1'h0)]).victim_req)) ? (Struct33 {valid :
        (Bool)'(True), data : (x_1)[(Bit#(1))'(1'h0)]}) : (Struct33 {valid :
        (Bool)'(False), data : unpack(0)})))));
        when ((x_2).valid, noAction);
        return (x_2).data;
    endmethod

    method ActionValue#(Bool) victims__001__hasVictim ();
        let x_1 = (victimRegs__001);
        Bool x_2 = (((((x_1)[(Bit#(1))'(1'h1)]).victim_valid) && (!
        (((x_1)[(Bit#(1))'(1'h1)]).victim_req)) ? ((Bool)'(True)) :
        (((((x_1)[(Bit#(1))'(1'h0)]).victim_valid) && (!
        (((x_1)[(Bit#(1))'(1'h0)]).victim_req)) ? ((Bool)'(True)) :
        ((Bool)'(False))))));
        return x_2;
    endmethod

    method Action victims__001__setVictimRq (Bit#(64) x_0);
        let x_1 = (victimRegs__001);
        Struct13 x_2 =
        ((x_1)[(Bit#(1))'(1'h1)]);
        if (((x_2).victim_valid) && (((x_2).victim_addr) == (x_0)))
            begin
            Struct13 x_3 = (Struct13 {victim_valid : (x_2).victim_valid,
            victim_addr : (x_2).victim_addr, victim_info : (x_2).victim_info,
            victim_value : (x_2).victim_value, victim_req :
            (Bool)'(True)});
            victimRegs__001 <= update (x_1, (Bit#(1))'(1'h1), x_3);
        end else begin
            Struct13 x_4 =
            ((x_1)[(Bit#(1))'(1'h0)]);
            if (((x_4).victim_valid) && (((x_4).victim_addr) == (x_0)))
                begin
                Struct13 x_5 = (Struct13 {victim_valid : (x_4).victim_valid,
                victim_addr : (x_4).victim_addr, victim_info :
                (x_4).victim_info, victim_value : (x_4).victim_value,
                victim_req : (Bool)'(True)});
                victimRegs__001 <= update (x_1, (Bit#(1))'(1'h0), x_5);
            end else begin

            end
        end
    endmethod

    method Action victims__001__releaseVictim (Bit#(64) x_0);
        let x_1 = (victimRegs__001);
        Struct13 x_2 =
        ((x_1)[(Bit#(1))'(1'h0)]);
        if (((x_2).victim_valid) && (((x_2).victim_addr) == (x_0)))
            begin
            victimRegs__001 <= update (x_1, (Bit#(1))'(1'h0), unpack(0));
        end else begin
            Struct13 x_3 =
            ((x_1)[(Bit#(1))'(1'h1)]);
            if (((x_3).victim_valid) && (((x_3).victim_addr) == (x_0)))
                begin
                victimRegs__001 <= update (x_1, (Bit#(1))'(1'h1), unpack(0));
            end else begin

            end
        end
    endmethod
endmodule

interface Module64;
    method Action rdReq_infoRam__001__3 (Bit#(8) x_0);
    method Action wrReq_infoRam__001__3 (Struct47 x_0);
    method ActionValue#(Struct45) rdResp_infoRam__001__3 ();
endinterface

module mkModule64 (Module64);
    RWBramCore#(Bit#(8), Struct45) bram <- mkRWBramCore();
    Reg#(Bool) initDone <- mkReg(False);
    Reg#(Bit#(8)) initIdx <- mkReg(0);

    rule init (!initDone);
        let initData = Struct45 {tag: 51'h7, value: Struct10 {mesi_owned: False, mesi_status: 3'h1, mesi_dir_st: 3'h1, mesi_dir_sharers: 4'h0}};
        bram.wrReq(initIdx, initData);
        initIdx <= initIdx + 1;
        initDone <= (initIdx == maxBound);
    endrule

    method Action rdReq_infoRam__001__3 (Bit#(8) x_0) if(initDone);
        bram.rdReq(x_0);
    endmethod

    method Action wrReq_infoRam__001__3 (Struct47 x_0) if(initDone);
        bram.wrReq(x_0.addr, x_0.datain);
    endmethod

    method ActionValue#(Struct45) rdResp_infoRam__001__3 () if(initDone);
        bram.deqRdResp ();
        let data = bram.rdResp ();
        return data;
    endmethod


endmodule

interface Module65;
    method Action rdReq_infoRam__001__2 (Bit#(8) x_0);
    method Action wrReq_infoRam__001__2 (Struct47 x_0);
    method ActionValue#(Struct45) rdResp_infoRam__001__2 ();
endinterface

module mkModule65 (Module65);
    RWBramCore#(Bit#(8), Struct45) bram <- mkRWBramCore();
    Reg#(Bool) initDone <- mkReg(False);
    Reg#(Bit#(8)) initIdx <- mkReg(0);

    rule init (!initDone);
        let initData = Struct45 {tag: 51'h6, value: Struct10 {mesi_owned: False, mesi_status: 3'h1, mesi_dir_st: 3'h1, mesi_dir_sharers: 4'h0}};
        bram.wrReq(initIdx, initData);
        initIdx <= initIdx + 1;
        initDone <= (initIdx == maxBound);
    endrule

    method Action rdReq_infoRam__001__2 (Bit#(8) x_0) if(initDone);
        bram.rdReq(x_0);
    endmethod

    method Action wrReq_infoRam__001__2 (Struct47 x_0) if(initDone);
        bram.wrReq(x_0.addr, x_0.datain);
    endmethod

    method ActionValue#(Struct45) rdResp_infoRam__001__2 () if(initDone);
        bram.deqRdResp ();
        let data = bram.rdResp ();
        return data;
    endmethod


endmodule

interface Module66;
    method Action rdReq_infoRam__001__1 (Bit#(8) x_0);
    method Action wrReq_infoRam__001__1 (Struct47 x_0);
    method ActionValue#(Struct45) rdResp_infoRam__001__1 ();
endinterface

module mkModule66 (Module66);
    RWBramCore#(Bit#(8), Struct45) bram <- mkRWBramCore();
    Reg#(Bool) initDone <- mkReg(False);
    Reg#(Bit#(8)) initIdx <- mkReg(0);

    rule init (!initDone);
        let initData = Struct45 {tag: 51'h5, value: Struct10 {mesi_owned: False, mesi_status: 3'h1, mesi_dir_st: 3'h1, mesi_dir_sharers: 4'h0}};
        bram.wrReq(initIdx, initData);
        initIdx <= initIdx + 1;
        initDone <= (initIdx == maxBound);
    endrule

    method Action rdReq_infoRam__001__1 (Bit#(8) x_0) if(initDone);
        bram.rdReq(x_0);
    endmethod

    method Action wrReq_infoRam__001__1 (Struct47 x_0) if(initDone);
        bram.wrReq(x_0.addr, x_0.datain);
    endmethod

    method ActionValue#(Struct45) rdResp_infoRam__001__1 () if(initDone);
        bram.deqRdResp ();
        let data = bram.rdResp ();
        return data;
    endmethod


endmodule

interface Module67;
    method Action rdReq_infoRam__001__0 (Bit#(8) x_0);
    method Action wrReq_infoRam__001__0 (Struct47 x_0);
    method ActionValue#(Struct45) rdResp_infoRam__001__0 ();
endinterface

module mkModule67 (Module67);
    RWBramCore#(Bit#(8), Struct45) bram <- mkRWBramCore();
    Reg#(Bool) initDone <- mkReg(False);
    Reg#(Bit#(8)) initIdx <- mkReg(0);

    rule init (!initDone);
        let initData = Struct45 {tag: 51'h4, value: Struct10 {mesi_owned: False, mesi_status: 3'h1, mesi_dir_st: 3'h1, mesi_dir_sharers: 4'h0}};
        bram.wrReq(initIdx, initData);
        initIdx <= initIdx + 1;
        initDone <= (initIdx == maxBound);
    endrule

    method Action rdReq_infoRam__001__0 (Bit#(8) x_0) if(initDone);
        bram.rdReq(x_0);
    endmethod

    method Action wrReq_infoRam__001__0 (Struct47 x_0) if(initDone);
        bram.wrReq(x_0.addr, x_0.datain);
    endmethod

    method ActionValue#(Struct45) rdResp_infoRam__001__0 () if(initDone);
        bram.deqRdResp ();
        let data = bram.rdResp ();
        return data;
    endmethod


endmodule

interface Module68;
    method Action rdReq_dataRam__001 (Bit#(10) x_0);
    method Action wrReq_dataRam__001 (Struct49 x_0);
    method ActionValue#(Vector#(4, Bit#(64))) rdResp_dataRam__001 ();
endinterface

module mkModule68 (Module68);
    RWBramCore#(Bit#(10), Vector#(4, Bit#(64))) bram <- mkRWBramCore();
    Reg#(Bool) initDone <- mkReg(False);
    Reg#(Bit#(10)) initIdx <- mkReg(0);

    rule init (!initDone);
        let initData = vec(64'h0, 64'h0, 64'h0, 64'h0);
        bram.wrReq(initIdx, initData);
        initIdx <= initIdx + 1;
        initDone <= (initIdx == maxBound);
    endrule

    method Action rdReq_dataRam__001 (Bit#(10) x_0) if(initDone);
        bram.rdReq(x_0);
    endmethod

    method Action wrReq_dataRam__001 (Struct49 x_0) if(initDone);
        bram.wrReq(x_0.addr, x_0.datain);
    endmethod

    method ActionValue#(Vector#(4, Bit#(64))) rdResp_dataRam__001 ()
    if(initDone);
        bram.deqRdResp ();
        let data = bram.rdResp ();
        return data;
    endmethod


endmodule

interface Module69;
    method Action rdReq_repRam__001 (Bit#(8) x_0);
    method Action wrReq_repRam__001 (Struct50 x_0);
    method ActionValue#(Vector#(4, Bit#(8))) rdResp_repRam__001 ();
endinterface

module mkModule69 (Module69);
    RWBramCore#(Bit#(8), Vector#(4, Bit#(8))) bram <- mkRWBramCore();
    Reg#(Bool) initDone <- mkReg(False);
    Reg#(Bit#(8)) initIdx <- mkReg(0);

    rule init (!initDone);
        let initData = vec(8'h1, 8'h1, 8'h1, 8'h1);
        bram.wrReq(initIdx, initData);
        initIdx <= initIdx + 1;
        initDone <= (initIdx == maxBound);
    endrule

    method Action rdReq_repRam__001 (Bit#(8) x_0) if(initDone);
        bram.rdReq(x_0);
    endmethod

    method Action wrReq_repRam__001 (Struct50 x_0) if(initDone);
        bram.wrReq(x_0.addr, x_0.datain);
    endmethod

    method ActionValue#(Vector#(4, Bit#(8))) rdResp_repRam__001 ()
    if(initDone);
        bram.deqRdResp ();
        let data = bram.rdResp ();
        return data;
    endmethod


endmodule

interface Module70;
    method ActionValue#(Struct14) getMSHR_001 (Bit#(2) x_0);
    method ActionValue#(Struct1) getMSHRRq_001 (Bit#(2) x_0);
    method ActionValue#(Struct36) getPRqSlot_001 (Struct35 x_0);
    method ActionValue#(Struct36) getCRqSlot_001 (Struct35 x_0);
    method ActionValue#(Struct35) getWait_001 ();
    method Action registerUL_001 (Struct43 x_0);
    method Action canImm_001 (Bit#(64) x_0);
    method Action setULImm_001 (Struct1 x_0);
    method ActionValue#(Bit#(2)) getULReady_001 (Bit#(64) x_0);
    method Action startRelease_001 (Bit#(2) x_0);
    method Action releaseMSHR_001 (Bit#(2) x_0);
endinterface

module mkModule70
    (Module70);
    Reg#(Vector#(4, Struct14)) mshrs_001 <- mkReg(unpack(0));
    Reg#(Vector#(4, Bit#(64))) maddrs_001 <- mkReg(unpack(0));
    Reg#(Vector#(4, Bit#(3))) msts_001 <- mkReg(unpack(0));
    Reg#(Vector#(4, Struct51)) mnexts_001 <- mkReg(unpack(0));
    Reg#(Vector#(4, Struct1)) rqs_001 <- mkReg(unpack(0));

    // No rules in this module

    method ActionValue#(Struct14) getMSHR_001 (Bit#(2) x_0);
        let x_1 = (mshrs_001);
        return (x_1)[x_0];
    endmethod

    method ActionValue#(Struct1) getMSHRRq_001 (Bit#(2) x_0);
        let x_1 = (rqs_001);
        return (x_1)[x_0];
    endmethod

    method ActionValue#(Struct36) getPRqSlot_001 (Struct35 x_0);
        let x_1 = (mshrs_001);
        let x_2 = (maddrs_001);
        let x_3 = (msts_001);
        let x_4 = (mnexts_001);
        Struct51 x_5 = ((((x_3)[(Bit#(2))'(2'h0)]) == ((Bit#(3))'(3'h0)) ?
        (Struct51 {valid : (Bool)'(True), data : (Bit#(2))'(2'h0)}) :
        ((((x_3)[(Bit#(2))'(2'h1)]) == ((Bit#(3))'(3'h0)) ? (Struct51 {valid
        : (Bool)'(True), data : (Bit#(2))'(2'h1)}) : (Struct51 {valid :
        (Bool)'(False), data : unpack(0)})))));
        Bool x_6 = ((x_5).valid);
        Bit#(2) x_7 = ((x_5).data);
        Bit#(64) x_8 = (((x_0).r_msg).addr);
        Bool x_9 = ((((((x_3)[(Bit#(2))'(2'h0)]) == ((Bit#(3))'(3'h4))) ||
        (((x_3)[(Bit#(2))'(2'h0)]) == ((Bit#(3))'(3'h6)))) && (((!
        (((x_2)[(Bit#(2))'(2'h0)]) == (x_8))) &&
        ((((x_2)[(Bit#(2))'(2'h0)])[12:5]) == ((x_8)[12:5]))) ||
        (((x_2)[(Bit#(2))'(2'h0)]) == (x_8))) ? ((Bool)'(True)) :
        ((((((x_3)[(Bit#(2))'(2'h1)]) == ((Bit#(3))'(3'h4))) ||
        (((x_3)[(Bit#(2))'(2'h1)]) == ((Bit#(3))'(3'h6)))) && (((!
        (((x_2)[(Bit#(2))'(2'h1)]) == (x_8))) &&
        ((((x_2)[(Bit#(2))'(2'h1)])[12:5]) == ((x_8)[12:5]))) ||
        (((x_2)[(Bit#(2))'(2'h1)]) == (x_8))) ? ((Bool)'(True)) :
        ((((((x_3)[(Bit#(2))'(2'h2)]) == ((Bit#(3))'(3'h4))) ||
        (((x_3)[(Bit#(2))'(2'h2)]) == ((Bit#(3))'(3'h6)))) && (((!
        (((x_2)[(Bit#(2))'(2'h2)]) == (x_8))) &&
        ((((x_2)[(Bit#(2))'(2'h2)])[12:5]) == ((x_8)[12:5]))) ||
        (((x_2)[(Bit#(2))'(2'h2)]) == (x_8))) ? ((Bool)'(True)) :
        ((((((x_3)[(Bit#(2))'(2'h3)]) == ((Bit#(3))'(3'h4))) ||
        (((x_3)[(Bit#(2))'(2'h3)]) == ((Bit#(3))'(3'h6)))) && (((!
        (((x_2)[(Bit#(2))'(2'h3)]) == (x_8))) &&
        ((((x_2)[(Bit#(2))'(2'h3)])[12:5]) == ((x_8)[12:5]))) ||
        (((x_2)[(Bit#(2))'(2'h3)]) == (x_8))) ? ((Bool)'(True)) :
        ((Bool)'(False))))))))));
        Struct51 x_10 = ((((((x_3)[(Bit#(2))'(2'h0)]) == ((Bit#(3))'(3'h5)))
        && (! (((x_1)[(Bit#(2))'(2'h0)]).m_is_ul))) &&
        (((x_2)[(Bit#(2))'(2'h0)]) == (x_8)) ? (Struct51 {valid :
        (Bool)'(True), data : (Bit#(2))'(2'h0)}) :
        ((((((x_3)[(Bit#(2))'(2'h1)]) == ((Bit#(3))'(3'h5))) && (!
        (((x_1)[(Bit#(2))'(2'h1)]).m_is_ul))) && (((x_2)[(Bit#(2))'(2'h1)])
        == (x_8)) ? (Struct51 {valid : (Bool)'(True), data :
        (Bit#(2))'(2'h1)}) : ((((((x_3)[(Bit#(2))'(2'h2)]) ==
        ((Bit#(3))'(3'h5))) && (! (((x_1)[(Bit#(2))'(2'h2)]).m_is_ul))) &&
        (((x_2)[(Bit#(2))'(2'h2)]) == (x_8)) ? (Struct51 {valid :
        (Bool)'(True), data : (Bit#(2))'(2'h2)}) :
        ((((((x_3)[(Bit#(2))'(2'h3)]) == ((Bit#(3))'(3'h5))) && (!
        (((x_1)[(Bit#(2))'(2'h3)]).m_is_ul))) && (((x_2)[(Bit#(2))'(2'h3)])
        == (x_8)) ? (Struct51 {valid : (Bool)'(True), data :
        (Bit#(2))'(2'h3)}) : (Struct51 {valid : (Bool)'(False), data :
        unpack(0)})))))))));
        Bool x_11 = ((x_10).valid);
        Struct36 x_12 = (Struct36 {s_has_slot : (x_6) && (! (x_9)),
        s_conflict : x_11, s_id :
        x_7});
        if ((x_6) && (! (x_9))) begin
            mshrs_001 <= update (x_1, x_7, Struct14 {m_is_ul : unpack(0),
            m_qidx : (x_0).r_msg_from, m_rsb : unpack(0), m_dl_rss_from :
            unpack(0), m_dl_rss_recv : unpack(0)});
            maddrs_001 <= update (x_2, x_7, ((x_0).r_msg).addr);
            msts_001 <= update (x_3, x_7, (x_11 ? ((Bit#(3))'(3'h1)) :
            ((Bit#(3))'(3'h4))));
            let x_13 = (rqs_001);
            rqs_001 <= update (x_13, x_7,
            (x_0).r_msg);
            if (x_11) begin
                Bit#(2) x_14 = ((((! (((x_3)[(Bit#(2))'(2'h0)]) ==
                ((Bit#(3))'(3'h0)))) && (!
                (((x_4)[(Bit#(2))'(2'h0)]).valid))) &&
                (((x_2)[(Bit#(2))'(2'h0)]) == (x_8)) ? ((Bit#(2))'(2'h0)) :
                ((((! (((x_3)[(Bit#(2))'(2'h1)]) == ((Bit#(3))'(3'h0)))) &&
                (! (((x_4)[(Bit#(2))'(2'h1)]).valid))) &&
                (((x_2)[(Bit#(2))'(2'h1)]) == (x_8)) ? ((Bit#(2))'(2'h1)) :
                ((((! (((x_3)[(Bit#(2))'(2'h2)]) == ((Bit#(3))'(3'h0)))) &&
                (! (((x_4)[(Bit#(2))'(2'h2)]).valid))) &&
                (((x_2)[(Bit#(2))'(2'h2)]) == (x_8)) ? ((Bit#(2))'(2'h2)) :
                ((((! (((x_3)[(Bit#(2))'(2'h3)]) == ((Bit#(3))'(3'h0)))) &&
                (! (((x_4)[(Bit#(2))'(2'h3)]).valid))) &&
                (((x_2)[(Bit#(2))'(2'h3)]) == (x_8)) ? ((Bit#(2))'(2'h3)) :
                (unpack(0))))))))));
                Struct51 x_15 = ((x_4)[x_14]);
                mnexts_001 <= update (x_4, x_14, Struct51 {valid :
                (Bool)'(True), data : x_7});
            end else begin

            end
        end else begin

        end
        return x_12;
    endmethod

    method ActionValue#(Struct36) getCRqSlot_001 (Struct35 x_0);
        let x_1 = (mshrs_001);
        let x_2 = (maddrs_001);
        let x_3 = (msts_001);
        let x_4 = (mnexts_001);
        Struct51 x_5 = ((((x_3)[(Bit#(2))'(2'h2)]) == ((Bit#(3))'(3'h0)) ?
        (Struct51 {valid : (Bool)'(True), data : (Bit#(2))'(2'h2)}) :
        ((((x_3)[(Bit#(2))'(2'h3)]) == ((Bit#(3))'(3'h0)) ? (Struct51 {valid
        : (Bool)'(True), data : (Bit#(2))'(2'h3)}) : (Struct51 {valid :
        (Bool)'(False), data : unpack(0)})))));
        Bool x_6 = ((x_5).valid);
        Bit#(2) x_7 = ((x_5).data);
        Bit#(64) x_8 = (((x_0).r_msg).addr);
        Bool x_9 = ((((((x_3)[(Bit#(2))'(2'h0)]) == ((Bit#(3))'(3'h4))) ||
        (((x_3)[(Bit#(2))'(2'h0)]) == ((Bit#(3))'(3'h6)))) && ((!
        (((x_2)[(Bit#(2))'(2'h0)]) == (x_8))) &&
        ((((x_2)[(Bit#(2))'(2'h0)])[12:5]) == ((x_8)[12:5]))) ?
        ((Bool)'(True)) : ((((((x_3)[(Bit#(2))'(2'h1)]) ==
        ((Bit#(3))'(3'h4))) || (((x_3)[(Bit#(2))'(2'h1)]) ==
        ((Bit#(3))'(3'h6)))) && ((! (((x_2)[(Bit#(2))'(2'h1)]) == (x_8))) &&
        ((((x_2)[(Bit#(2))'(2'h1)])[12:5]) == ((x_8)[12:5]))) ?
        ((Bool)'(True)) : ((((((x_3)[(Bit#(2))'(2'h2)]) ==
        ((Bit#(3))'(3'h4))) || (((x_3)[(Bit#(2))'(2'h2)]) ==
        ((Bit#(3))'(3'h6)))) && ((! (((x_2)[(Bit#(2))'(2'h2)]) == (x_8))) &&
        ((((x_2)[(Bit#(2))'(2'h2)])[12:5]) == ((x_8)[12:5]))) ?
        ((Bool)'(True)) : ((((((x_3)[(Bit#(2))'(2'h3)]) ==
        ((Bit#(3))'(3'h4))) || (((x_3)[(Bit#(2))'(2'h3)]) ==
        ((Bit#(3))'(3'h6)))) && ((! (((x_2)[(Bit#(2))'(2'h3)]) == (x_8))) &&
        ((((x_2)[(Bit#(2))'(2'h3)])[12:5]) == ((x_8)[12:5]))) ?
        ((Bool)'(True)) : ((Bool)'(False))))))))));
        Struct51 x_10 = (((((! (((x_3)[(Bit#(2))'(2'h2)]) ==
        ((Bit#(3))'(3'h0)))) && (! (((x_4)[(Bit#(2))'(2'h2)]).valid))) &&
        (((x_1)[(Bit#(2))'(2'h2)]).m_is_ul)) && (((x_2)[(Bit#(2))'(2'h2)]) ==
        (x_8)) ? (Struct51 {valid : (Bool)'(True), data : (Bit#(2))'(2'h2)})
        : (((((! (((x_3)[(Bit#(2))'(2'h3)]) == ((Bit#(3))'(3'h0)))) && (!
        (((x_4)[(Bit#(2))'(2'h3)]).valid))) &&
        (((x_1)[(Bit#(2))'(2'h3)]).m_is_ul)) && (((x_2)[(Bit#(2))'(2'h3)]) ==
        (x_8)) ? (Struct51 {valid : (Bool)'(True), data : (Bit#(2))'(2'h3)})
        : (Struct51 {valid : (Bool)'(False), data : unpack(0)})))));
        Struct51 x_11 = (((((! (((x_3)[(Bit#(2))'(2'h0)]) ==
        ((Bit#(3))'(3'h0)))) && (! (((x_4)[(Bit#(2))'(2'h0)]).valid))) && (!
        (((x_1)[(Bit#(2))'(2'h0)]).m_is_ul))) && (((x_2)[(Bit#(2))'(2'h0)])
        == (x_8)) ? (Struct51 {valid : (Bool)'(True), data :
        (Bit#(2))'(2'h0)}) : (((((! (((x_3)[(Bit#(2))'(2'h1)]) ==
        ((Bit#(3))'(3'h0)))) && (! (((x_4)[(Bit#(2))'(2'h1)]).valid))) && (!
        (((x_1)[(Bit#(2))'(2'h1)]).m_is_ul))) && (((x_2)[(Bit#(2))'(2'h1)])
        == (x_8)) ? (Struct51 {valid : (Bool)'(True), data :
        (Bit#(2))'(2'h1)}) : (((((! (((x_3)[(Bit#(2))'(2'h2)]) ==
        ((Bit#(3))'(3'h0)))) && (! (((x_4)[(Bit#(2))'(2'h2)]).valid))) && (!
        (((x_1)[(Bit#(2))'(2'h2)]).m_is_ul))) && (((x_2)[(Bit#(2))'(2'h2)])
        == (x_8)) ? (Struct51 {valid : (Bool)'(True), data :
        (Bit#(2))'(2'h2)}) : (((((! (((x_3)[(Bit#(2))'(2'h3)]) ==
        ((Bit#(3))'(3'h0)))) && (! (((x_4)[(Bit#(2))'(2'h3)]).valid))) && (!
        (((x_1)[(Bit#(2))'(2'h3)]).m_is_ul))) && (((x_2)[(Bit#(2))'(2'h3)])
        == (x_8)) ? (Struct51 {valid : (Bool)'(True), data :
        (Bit#(2))'(2'h3)}) : (Struct51 {valid : (Bool)'(False), data :
        unpack(0)})))))))));
        Bool x_12 = ((x_10).valid);
        Bool x_13 = ((x_11).valid);
        Bool x_14 = ((x_12) || (x_13));
        Struct36 x_15 = (Struct36 {s_has_slot : (x_6) && (! (x_9)),
        s_conflict : x_14, s_id :
        x_7});
        if ((x_6) && (! (x_9))) begin
            mshrs_001 <= update (x_1, x_7, Struct14 {m_is_ul : unpack(0),
            m_qidx : (x_0).r_msg_from, m_rsb : unpack(0), m_dl_rss_from :
            unpack(0), m_dl_rss_recv : unpack(0)});
            maddrs_001 <= update (x_2, x_7, ((x_0).r_msg).addr);
            msts_001 <= update (x_3, x_7, (x_14 ? ((Bit#(3))'(3'h1)) :
            ((Bit#(3))'(3'h4))));
            let x_16 = (rqs_001);
            rqs_001 <= update (x_16, x_7,
            (x_0).r_msg);
            if (x_14) begin
                Bit#(2) x_17 = ((x_12 ? ((x_10).data) :
                ((x_11).data)));
                Struct51 x_18 = ((x_4)[x_17]);
                mnexts_001 <= update (x_4, x_17, Struct51 {valid :
                (Bool)'(True), data : x_7});
            end else begin

            end
        end else begin

        end
        return x_15;
    endmethod

    method ActionValue#(Struct35) getWait_001 ();
        let x_1 = (mshrs_001);
        let x_2 = (maddrs_001);
        let x_3 = (msts_001);
        let x_4 = (rqs_001);
        Struct51 x_5 = ((((x_3)[(Bit#(2))'(2'h0)]) == ((Bit#(3))'(3'h2)) ?
        (Struct51 {valid : (Bool)'(True), data : (Bit#(2))'(2'h0)}) :
        ((((x_3)[(Bit#(2))'(2'h1)]) == ((Bit#(3))'(3'h2)) ? (Struct51 {valid
        : (Bool)'(True), data : (Bit#(2))'(2'h1)}) :
        ((((x_3)[(Bit#(2))'(2'h2)]) == ((Bit#(3))'(3'h2)) ? (Struct51 {valid
        : (Bool)'(True), data : (Bit#(2))'(2'h2)}) :
        ((((x_3)[(Bit#(2))'(2'h3)]) == ((Bit#(3))'(3'h2)) ? (Struct51 {valid
        : (Bool)'(True), data : (Bit#(2))'(2'h3)}) : (Struct51 {valid :
        (Bool)'(False), data : unpack(0)})))))))));
        when ((x_5).valid, noAction);
        Bit#(2) x_6 = ((x_5).data);
        Struct14 x_7 = ((x_1)[x_6]);
        Bit#(64) x_8 = ((x_2)[x_6]);
        Struct1 x_9 = ((x_4)[x_6]);
        Bool x_10 = ((((! (((x_3)[(Bit#(2))'(2'h0)]) < ((Bit#(3))'(3'h4))))
        && (((x_2)[(Bit#(2))'(2'h0)]) == (x_8))) ||
        (((((x_3)[(Bit#(2))'(2'h0)]) == ((Bit#(3))'(3'h4))) ||
        (((x_3)[(Bit#(2))'(2'h0)]) == ((Bit#(3))'(3'h6)))) && ((!
        (((x_2)[(Bit#(2))'(2'h0)]) == (x_8))) &&
        ((((x_2)[(Bit#(2))'(2'h0)])[12:5]) == ((x_8)[12:5])))) ?
        ((Bool)'(True)) : ((((! (((x_3)[(Bit#(2))'(2'h1)]) <
        ((Bit#(3))'(3'h4)))) && (((x_2)[(Bit#(2))'(2'h1)]) == (x_8))) ||
        (((((x_3)[(Bit#(2))'(2'h1)]) == ((Bit#(3))'(3'h4))) ||
        (((x_3)[(Bit#(2))'(2'h1)]) == ((Bit#(3))'(3'h6)))) && ((!
        (((x_2)[(Bit#(2))'(2'h1)]) == (x_8))) &&
        ((((x_2)[(Bit#(2))'(2'h1)])[12:5]) == ((x_8)[12:5])))) ?
        ((Bool)'(True)) : ((((! (((x_3)[(Bit#(2))'(2'h2)]) <
        ((Bit#(3))'(3'h4)))) && (((x_2)[(Bit#(2))'(2'h2)]) == (x_8))) ||
        (((((x_3)[(Bit#(2))'(2'h2)]) == ((Bit#(3))'(3'h4))) ||
        (((x_3)[(Bit#(2))'(2'h2)]) == ((Bit#(3))'(3'h6)))) && ((!
        (((x_2)[(Bit#(2))'(2'h2)]) == (x_8))) &&
        ((((x_2)[(Bit#(2))'(2'h2)])[12:5]) == ((x_8)[12:5])))) ?
        ((Bool)'(True)) : ((((! (((x_3)[(Bit#(2))'(2'h3)]) <
        ((Bit#(3))'(3'h4)))) && (((x_2)[(Bit#(2))'(2'h3)]) == (x_8))) ||
        (((((x_3)[(Bit#(2))'(2'h3)]) == ((Bit#(3))'(3'h4))) ||
        (((x_3)[(Bit#(2))'(2'h3)]) == ((Bit#(3))'(3'h6)))) && ((!
        (((x_2)[(Bit#(2))'(2'h3)]) == (x_8))) &&
        ((((x_2)[(Bit#(2))'(2'h3)])[12:5]) == ((x_8)[12:5])))) ?
        ((Bool)'(True)) : ((Bool)'(False))))))))));
        when (! (x_10), noAction);
        msts_001 <= update (x_3, x_6, (Bit#(3))'(3'h4));
        Struct35 x_11 = (Struct35 {r_id : x_6, r_msg : x_9, r_msg_from :
        (x_7).m_qidx});
        return x_11;
    endmethod

    method Action registerUL_001 (Struct43 x_0);
        let x_1 = (mshrs_001);
        let x_2 = (msts_001);
        Bit#(2) x_3 = ((x_0).r_id);
        mshrs_001 <= update (x_1, x_3, Struct14 {m_is_ul : (Bool)'(True),
        m_qidx : {((Bit#(2))'(2'h2)),((x_0).r_ul_rsbTo)}, m_rsb :
        (x_0).r_ul_rsb, m_dl_rss_from : unpack(0), m_dl_rss_recv :
        unpack(0)});
        msts_001 <= update (x_2, x_3, (Bit#(3))'(3'h5));
    endmethod

    method Action canImm_001 (Bit#(64) x_0);
        let x_1 = (maddrs_001);
        let x_2 = (msts_001);
        let x_3 = (mnexts_001);
        Struct51 x_4 = ((((x_2)[(Bit#(2))'(2'h2)]) == ((Bit#(3))'(3'h0)) ?
        (Struct51 {valid : (Bool)'(True), data : (Bit#(2))'(2'h2)}) :
        ((((x_2)[(Bit#(2))'(2'h3)]) == ((Bit#(3))'(3'h0)) ? (Struct51 {valid
        : (Bool)'(True), data : (Bit#(2))'(2'h3)}) : (Struct51 {valid :
        (Bool)'(False), data : unpack(0)})))));
        when ((x_4).valid, noAction);
        Struct51 x_5 = ((((! (((x_2)[(Bit#(2))'(2'h0)]) ==
        ((Bit#(3))'(3'h0)))) && (! (((x_3)[(Bit#(2))'(2'h0)]).valid))) &&
        (((x_1)[(Bit#(2))'(2'h0)]) == (x_0)) ? (Struct51 {valid :
        (Bool)'(True), data : (Bit#(2))'(2'h0)}) : ((((!
        (((x_2)[(Bit#(2))'(2'h1)]) == ((Bit#(3))'(3'h0)))) && (!
        (((x_3)[(Bit#(2))'(2'h1)]).valid))) && (((x_1)[(Bit#(2))'(2'h1)]) ==
        (x_0)) ? (Struct51 {valid : (Bool)'(True), data : (Bit#(2))'(2'h1)})
        : ((((! (((x_2)[(Bit#(2))'(2'h2)]) == ((Bit#(3))'(3'h0)))) && (!
        (((x_3)[(Bit#(2))'(2'h2)]).valid))) && (((x_1)[(Bit#(2))'(2'h2)]) ==
        (x_0)) ? (Struct51 {valid : (Bool)'(True), data : (Bit#(2))'(2'h2)})
        : ((((! (((x_2)[(Bit#(2))'(2'h3)]) == ((Bit#(3))'(3'h0)))) && (!
        (((x_3)[(Bit#(2))'(2'h3)]).valid))) && (((x_1)[(Bit#(2))'(2'h3)]) ==
        (x_0)) ? (Struct51 {valid : (Bool)'(True), data : (Bit#(2))'(2'h3)})
        : (Struct51 {valid : (Bool)'(False), data : unpack(0)})))))))));
        when (! ((x_5).valid), noAction);
    endmethod

    method Action setULImm_001 (Struct1 x_0);
        let x_1 = (mshrs_001);
        let x_2 = (maddrs_001);
        let x_3 = (msts_001);
        let x_4 = (rqs_001);
        Struct51 x_5 = ((((x_3)[(Bit#(2))'(2'h2)]) == ((Bit#(3))'(3'h0)) ?
        (Struct51 {valid : (Bool)'(True), data : (Bit#(2))'(2'h2)}) :
        ((((x_3)[(Bit#(2))'(2'h3)]) == ((Bit#(3))'(3'h0)) ? (Struct51 {valid
        : (Bool)'(True), data : (Bit#(2))'(2'h3)}) : (Struct51 {valid :
        (Bool)'(False), data : unpack(0)})))));
        when ((x_5).valid, noAction);
        Bit#(2) x_6 = ((x_5).data);
        Bit#(64) x_7 = ((x_0).addr);
        Struct51 x_8 = (((! (((x_3)[(Bit#(2))'(2'h0)]) ==
        ((Bit#(3))'(3'h0)))) && (((x_2)[(Bit#(2))'(2'h0)]) == (x_7)) ?
        (Struct51 {valid : (Bool)'(True), data : (Bit#(2))'(2'h0)}) : (((!
        (((x_3)[(Bit#(2))'(2'h1)]) == ((Bit#(3))'(3'h0)))) &&
        (((x_2)[(Bit#(2))'(2'h1)]) == (x_7)) ? (Struct51 {valid :
        (Bool)'(True), data : (Bit#(2))'(2'h1)}) : (((!
        (((x_3)[(Bit#(2))'(2'h2)]) == ((Bit#(3))'(3'h0)))) &&
        (((x_2)[(Bit#(2))'(2'h2)]) == (x_7)) ? (Struct51 {valid :
        (Bool)'(True), data : (Bit#(2))'(2'h2)}) : (((!
        (((x_3)[(Bit#(2))'(2'h3)]) == ((Bit#(3))'(3'h0)))) &&
        (((x_2)[(Bit#(2))'(2'h3)]) == (x_7)) ? (Struct51 {valid :
        (Bool)'(True), data : (Bit#(2))'(2'h3)}) : (Struct51 {valid :
        (Bool)'(False), data : unpack(0)})))))))));
        when (! ((x_8).valid), noAction);
        mshrs_001 <= update (x_1, x_6, Struct14 {m_is_ul : (Bool)'(True),
        m_qidx : unpack(0), m_rsb : (Bool)'(False), m_dl_rss_from :
        unpack(0), m_dl_rss_recv : unpack(0)});
        maddrs_001 <= update (x_2, x_6, (x_0).addr);
        msts_001 <= update (x_3, x_6, (Bit#(3))'(3'h5));
        rqs_001 <= update (x_4, x_6, x_0);
    endmethod

    method ActionValue#(Bit#(2)) getULReady_001 (Bit#(64) x_0);
        let x_1 = (mshrs_001);
        let x_2 = (maddrs_001);
        let x_3 = (msts_001);
        Bool x_4 = (((((((x_3)[(Bit#(2))'(2'h0)]) == ((Bit#(3))'(3'h4))) ||
        (((x_3)[(Bit#(2))'(2'h0)]) == ((Bit#(3))'(3'h6)))) && ((!
        (((x_2)[(Bit#(2))'(2'h0)]) == (x_0))) &&
        ((((x_2)[(Bit#(2))'(2'h0)])[12:5]) == ((x_0)[12:5])))) || (((!
        (((x_3)[(Bit#(2))'(2'h0)]) < ((Bit#(3))'(3'h4)))) && (!
        (((x_1)[(Bit#(2))'(2'h0)]).m_is_ul))) && (((x_2)[(Bit#(2))'(2'h0)])
        == (x_0))) ? ((Bool)'(True)) : (((((((x_3)[(Bit#(2))'(2'h1)]) ==
        ((Bit#(3))'(3'h4))) || (((x_3)[(Bit#(2))'(2'h1)]) ==
        ((Bit#(3))'(3'h6)))) && ((! (((x_2)[(Bit#(2))'(2'h1)]) == (x_0))) &&
        ((((x_2)[(Bit#(2))'(2'h1)])[12:5]) == ((x_0)[12:5])))) || (((!
        (((x_3)[(Bit#(2))'(2'h1)]) < ((Bit#(3))'(3'h4)))) && (!
        (((x_1)[(Bit#(2))'(2'h1)]).m_is_ul))) && (((x_2)[(Bit#(2))'(2'h1)])
        == (x_0))) ? ((Bool)'(True)) : (((((((x_3)[(Bit#(2))'(2'h2)]) ==
        ((Bit#(3))'(3'h4))) || (((x_3)[(Bit#(2))'(2'h2)]) ==
        ((Bit#(3))'(3'h6)))) && ((! (((x_2)[(Bit#(2))'(2'h2)]) == (x_0))) &&
        ((((x_2)[(Bit#(2))'(2'h2)])[12:5]) == ((x_0)[12:5])))) || (((!
        (((x_3)[(Bit#(2))'(2'h2)]) < ((Bit#(3))'(3'h4)))) && (!
        (((x_1)[(Bit#(2))'(2'h2)]).m_is_ul))) && (((x_2)[(Bit#(2))'(2'h2)])
        == (x_0))) ? ((Bool)'(True)) : (((((((x_3)[(Bit#(2))'(2'h3)]) ==
        ((Bit#(3))'(3'h4))) || (((x_3)[(Bit#(2))'(2'h3)]) ==
        ((Bit#(3))'(3'h6)))) && ((! (((x_2)[(Bit#(2))'(2'h3)]) == (x_0))) &&
        ((((x_2)[(Bit#(2))'(2'h3)])[12:5]) == ((x_0)[12:5])))) || (((!
        (((x_3)[(Bit#(2))'(2'h3)]) < ((Bit#(3))'(3'h4)))) && (!
        (((x_1)[(Bit#(2))'(2'h3)]).m_is_ul))) && (((x_2)[(Bit#(2))'(2'h3)])
        == (x_0))) ? ((Bool)'(True)) : ((Bool)'(False))))))))));
        when (! (x_4), noAction);
        Struct51 x_5 = ((((((x_3)[(Bit#(2))'(2'h2)]) == ((Bit#(3))'(3'h5)))
        && (((x_1)[(Bit#(2))'(2'h2)]).m_is_ul)) && (((x_2)[(Bit#(2))'(2'h2)])
        == (x_0)) ? (Struct51 {valid : (Bool)'(True), data :
        (Bit#(2))'(2'h2)}) : ((((((x_3)[(Bit#(2))'(2'h3)]) ==
        ((Bit#(3))'(3'h5))) && (((x_1)[(Bit#(2))'(2'h3)]).m_is_ul)) &&
        (((x_2)[(Bit#(2))'(2'h3)]) == (x_0)) ? (Struct51 {valid :
        (Bool)'(True), data : (Bit#(2))'(2'h3)}) : (Struct51 {valid :
        (Bool)'(False), data : unpack(0)})))));
        when ((x_5).valid, noAction);
        Bit#(2) x_6 = ((x_5).data);
        return x_6;
    endmethod

    method Action startRelease_001 (Bit#(2) x_0);
        let x_1 = (msts_001);
        msts_001 <= update (x_1, x_0, (Bit#(3))'(3'h6));
    endmethod

    method Action releaseMSHR_001 (Bit#(2) x_0);
        let x_1 = (mshrs_001);
        let x_2 = (msts_001);
        let x_3 = (mnexts_001);
        mshrs_001 <= update (x_1, x_0, unpack(0));
        mnexts_001 <= update (x_3, x_0, unpack(0));
        Vector#(4, Bit#(3)) x_4 = (update (x_2, x_0, unpack(0)));
        Struct51 x_5 =
        ((x_3)[x_0]);
        let x_8 = ?;
        if ((x_5).valid) begin
            Bit#(2) x_6 = ((x_5).data);
            Vector#(4, Bit#(3)) x_7 = (update (x_4, x_6,
            (Bit#(3))'(3'h2)));
            x_8 = x_7;
        end else begin
            x_8 = x_4;
        end
        msts_001 <= x_8;
    endmethod
endmodule

interface Module71;
    method Action enq_fifoCRqInput_002 (Struct2 x_0);
    method ActionValue#(Struct2) deq_fifoCRqInput_002 ();
endinterface

module mkModule71 (Module71);
    FIFOF#(Struct2) pff <- mkSizedFIFOF(4);

    method Action enq_fifoCRqInput_002 (Struct2 x_0);
        pff.enq(x_0);
    endmethod

    method ActionValue#(Struct2) deq_fifoCRqInput_002 ();
        pff.deq();
        return pff.first();
    endmethod

endmodule

interface Module72;
    method Action enq_fifoPInput_002 (Struct2 x_0);
    method ActionValue#(Struct2) deq_fifoPInput_002 ();
endinterface

module mkModule72 (Module72);
    FIFOF#(Struct2) pff <- mkSizedFIFOF(4);

    method Action enq_fifoPInput_002 (Struct2 x_0);
        pff.enq(x_0);
    endmethod

    method ActionValue#(Struct2) deq_fifoPInput_002 ();
        pff.deq();
        return pff.first();
    endmethod

endmodule

interface Module73;
    method Action enq_fifoN2I_002 (Struct38 x_0);
    method ActionValue#(Struct38) deq_fifoN2I_002 ();
endinterface

module mkModule73 (Module73);
    FIFOF#(Struct38) pff <- mkPipelineFIFOF();

    method Action enq_fifoN2I_002 (Struct38 x_0);
        pff.enq(x_0);
    endmethod

    method ActionValue#(Struct38) deq_fifoN2I_002 ();
        pff.deq();
        return pff.first();
    endmethod

endmodule

interface Module74;
    method Action enq_fifoI2L_002 (Struct38 x_0);
    method ActionValue#(Struct38) deq_fifoI2L_002 ();
endinterface

module mkModule74 (Module74);
    FIFOF#(Struct38) pff <- mkPipelineFIFOF();

    method Action enq_fifoI2L_002 (Struct38 x_0);
        pff.enq(x_0);
    endmethod

    method ActionValue#(Struct38) deq_fifoI2L_002 ();
        pff.deq();
        return pff.first();
    endmethod

endmodule

interface Module75;
    method Action enq_fifoL2E_002 (Struct41 x_0);
    method ActionValue#(Struct41) deq_fifoL2E_002 ();
endinterface

module mkModule75 (Module75);
    FIFOF#(Struct41) pff <- mkPipelineFIFOF();

    method Action enq_fifoL2E_002 (Struct41 x_0);
        pff.enq(x_0);
    endmethod

    method ActionValue#(Struct41) deq_fifoL2E_002 ();
        pff.deq();
        return pff.first();
    endmethod

endmodule

interface Module76;
    method Action enq_fifo0020 (Struct1 x_0);
    method ActionValue#(Struct1) deq_fifo0020 ();
endinterface

module mkModule76 (Module76);
    FIFOF#(Struct1) pff <- mkSizedFIFOF(2);

    method Action enq_fifo0020 (Struct1 x_0);
        pff.enq(x_0);
    endmethod

    method ActionValue#(Struct1) deq_fifo0020 ();
        pff.deq();
        return pff.first();
    endmethod

endmodule

interface Module77;
    method Action enq_fifo0021 (Struct1 x_0);
    method ActionValue#(Struct1) deq_fifo0021 ();
endinterface

module mkModule77 (Module77);
    FIFOF#(Struct1) pff <- mkSizedFIFOF(2);

    method Action enq_fifo0021 (Struct1 x_0);
        pff.enq(x_0);
    endmethod

    method ActionValue#(Struct1) deq_fifo0021 ();
        pff.deq();
        return pff.first();
    endmethod

endmodule

interface Module78;
    method Action enq_fifo0022 (Struct1 x_0);
    method ActionValue#(Struct1) deq_fifo0022 ();
endinterface

module mkModule78 (Module78);
    FIFOF#(Struct1) pff <- mkSizedFIFOF(2);

    method Action enq_fifo0022 (Struct1 x_0);
        pff.enq(x_0);
    endmethod

    method ActionValue#(Struct1) deq_fifo0022 ();
        pff.deq();
        return pff.first();
    endmethod

endmodule

interface Module79;
    method Action enq_fifo00200 (Struct1 x_0);
    method ActionValue#(Struct1) deq_fifo00200 ();
endinterface

module mkModule79 (Module79);
    FIFOF#(Struct1) pff <- mkSizedFIFOF(2);

    method Action enq_fifo00200 (Struct1 x_0);
        pff.enq(x_0);
    endmethod

    method ActionValue#(Struct1) deq_fifo00200 ();
        pff.deq();
        return pff.first();
    endmethod

endmodule

interface Module80;
    method Action enq_fifo00202 (Struct1 x_0);
    method ActionValue#(Struct1) deq_fifo00202 ();
endinterface

module mkModule80 (Module80);
    FIFOF#(Struct1) pff <- mkSizedFIFOF(2);

    method Action enq_fifo00202 (Struct1 x_0);
        pff.enq(x_0);
    endmethod

    method ActionValue#(Struct1) deq_fifo00202 ();
        pff.deq();
        return pff.first();
    endmethod

endmodule

interface Module81;
    method ActionValue#(Struct37) victims__002__findVictim (Bit#(64) x_0);
    method ActionValue#(Struct13) victims__002__getVictim (Bit#(1) x_0);
    method Action victims__002__setVictim (Struct44 x_0);
    method Action victims__002__registerVictim (Struct13 x_0);
    method ActionValue#(Struct13) victims__002__getFirstVictim ();
    method ActionValue#(Bool) victims__002__hasVictim ();
    method Action victims__002__setVictimRq (Bit#(64) x_0);
    method Action victims__002__releaseVictim (Bit#(64) x_0);
endinterface

module mkModule81
    (Module81);
    Reg#(Vector#(2, Struct13)) victimRegs__002 <- mkReg(unpack(0));

    // No rules in this module

    method ActionValue#(Struct37) victims__002__findVictim (Bit#(64) x_0);
        let x_1 = (victimRegs__002);
        Struct13 x_2 =
        ((x_1)[(Bit#(1))'(1'h0)]);
        let x_5 = ?;
        if (((x_2).victim_valid) && (((x_2).victim_addr) == (x_0))) begin
            x_5 = Struct37 {valid : (Bool)'(True), data : (Bit#(1))'(1'h0)};
        end else begin
            Struct13 x_3 =
            ((x_1)[(Bit#(1))'(1'h1)]);
            let x_4 = ?;
            if (((x_3).victim_valid) && (((x_3).victim_addr) == (x_0)))
                begin
                x_4 = Struct37 {valid : (Bool)'(True), data :
                (Bit#(1))'(1'h1)};
            end else begin
                x_4 = Struct37 {valid : (Bool)'(False), data : unpack(0)};
            end
            x_5 = x_4;
        end
        return x_5;
    endmethod

    method ActionValue#(Struct13) victims__002__getVictim (Bit#(1) x_0);
        let x_1 = (victimRegs__002);
        return (x_1)[x_0];
    endmethod

    method Action victims__002__setVictim (Struct44 x_0);
        let x_1 = (victimRegs__002);
        Struct13 x_2 = ((x_1)[(x_0).victim_idx]);
        Struct13 x_3 = (Struct13 {victim_valid : (Bool)'(True), victim_addr :
        (x_2).victim_addr, victim_info : (x_0).victim_info, victim_value :
        (x_0).victim_value, victim_req : (x_2).victim_req});
        victimRegs__002 <= update (x_1, (x_0).victim_idx, x_3);
    endmethod

    method Action victims__002__registerVictim (Struct13 x_0);
        let x_1 = (victimRegs__002);
        Struct37 x_2 = ((((x_1)[(Bit#(1))'(1'h1)]).victim_valid ?
        ((((x_1)[(Bit#(1))'(1'h0)]).victim_valid ? (Struct37 {valid :
        (Bool)'(False), data : unpack(0)}) : (Struct37 {valid :
        (Bool)'(True), data : (Bit#(1))'(1'h0)}))) : (Struct37 {valid :
        (Bool)'(True), data : (Bit#(1))'(1'h1)})));
        when ((x_2).valid, noAction);
        Bit#(1) x_3 = ((x_2).data);
        victimRegs__002 <= update (x_1, x_3, x_0);
    endmethod

    method ActionValue#(Struct13) victims__002__getFirstVictim ();
        let x_1 = (victimRegs__002);
        Struct33 x_2 = (((((x_1)[(Bit#(1))'(1'h1)]).victim_valid) && (!
        (((x_1)[(Bit#(1))'(1'h1)]).victim_req)) ? (Struct33 {valid :
        (Bool)'(True), data : (x_1)[(Bit#(1))'(1'h1)]}) :
        (((((x_1)[(Bit#(1))'(1'h0)]).victim_valid) && (!
        (((x_1)[(Bit#(1))'(1'h0)]).victim_req)) ? (Struct33 {valid :
        (Bool)'(True), data : (x_1)[(Bit#(1))'(1'h0)]}) : (Struct33 {valid :
        (Bool)'(False), data : unpack(0)})))));
        when ((x_2).valid, noAction);
        return (x_2).data;
    endmethod

    method ActionValue#(Bool) victims__002__hasVictim ();
        let x_1 = (victimRegs__002);
        Bool x_2 = (((((x_1)[(Bit#(1))'(1'h1)]).victim_valid) && (!
        (((x_1)[(Bit#(1))'(1'h1)]).victim_req)) ? ((Bool)'(True)) :
        (((((x_1)[(Bit#(1))'(1'h0)]).victim_valid) && (!
        (((x_1)[(Bit#(1))'(1'h0)]).victim_req)) ? ((Bool)'(True)) :
        ((Bool)'(False))))));
        return x_2;
    endmethod

    method Action victims__002__setVictimRq (Bit#(64) x_0);
        let x_1 = (victimRegs__002);
        Struct13 x_2 =
        ((x_1)[(Bit#(1))'(1'h1)]);
        if (((x_2).victim_valid) && (((x_2).victim_addr) == (x_0)))
            begin
            Struct13 x_3 = (Struct13 {victim_valid : (x_2).victim_valid,
            victim_addr : (x_2).victim_addr, victim_info : (x_2).victim_info,
            victim_value : (x_2).victim_value, victim_req :
            (Bool)'(True)});
            victimRegs__002 <= update (x_1, (Bit#(1))'(1'h1), x_3);
        end else begin
            Struct13 x_4 =
            ((x_1)[(Bit#(1))'(1'h0)]);
            if (((x_4).victim_valid) && (((x_4).victim_addr) == (x_0)))
                begin
                Struct13 x_5 = (Struct13 {victim_valid : (x_4).victim_valid,
                victim_addr : (x_4).victim_addr, victim_info :
                (x_4).victim_info, victim_value : (x_4).victim_value,
                victim_req : (Bool)'(True)});
                victimRegs__002 <= update (x_1, (Bit#(1))'(1'h0), x_5);
            end else begin

            end
        end
    endmethod

    method Action victims__002__releaseVictim (Bit#(64) x_0);
        let x_1 = (victimRegs__002);
        Struct13 x_2 =
        ((x_1)[(Bit#(1))'(1'h0)]);
        if (((x_2).victim_valid) && (((x_2).victim_addr) == (x_0)))
            begin
            victimRegs__002 <= update (x_1, (Bit#(1))'(1'h0), unpack(0));
        end else begin
            Struct13 x_3 =
            ((x_1)[(Bit#(1))'(1'h1)]);
            if (((x_3).victim_valid) && (((x_3).victim_addr) == (x_0)))
                begin
                victimRegs__002 <= update (x_1, (Bit#(1))'(1'h1), unpack(0));
            end else begin

            end
        end
    endmethod
endmodule

interface Module82;
    method Action rdReq_infoRam__002__3 (Bit#(8) x_0);
    method Action wrReq_infoRam__002__3 (Struct47 x_0);
    method ActionValue#(Struct45) rdResp_infoRam__002__3 ();
endinterface

module mkModule82 (Module82);
    RWBramCore#(Bit#(8), Struct45) bram <- mkRWBramCore();
    Reg#(Bool) initDone <- mkReg(False);
    Reg#(Bit#(8)) initIdx <- mkReg(0);

    rule init (!initDone);
        let initData = Struct45 {tag: 51'h7, value: Struct10 {mesi_owned: False, mesi_status: 3'h1, mesi_dir_st: 3'h1, mesi_dir_sharers: 4'h0}};
        bram.wrReq(initIdx, initData);
        initIdx <= initIdx + 1;
        initDone <= (initIdx == maxBound);
    endrule

    method Action rdReq_infoRam__002__3 (Bit#(8) x_0) if(initDone);
        bram.rdReq(x_0);
    endmethod

    method Action wrReq_infoRam__002__3 (Struct47 x_0) if(initDone);
        bram.wrReq(x_0.addr, x_0.datain);
    endmethod

    method ActionValue#(Struct45) rdResp_infoRam__002__3 () if(initDone);
        bram.deqRdResp ();
        let data = bram.rdResp ();
        return data;
    endmethod


endmodule

interface Module83;
    method Action rdReq_infoRam__002__2 (Bit#(8) x_0);
    method Action wrReq_infoRam__002__2 (Struct47 x_0);
    method ActionValue#(Struct45) rdResp_infoRam__002__2 ();
endinterface

module mkModule83 (Module83);
    RWBramCore#(Bit#(8), Struct45) bram <- mkRWBramCore();
    Reg#(Bool) initDone <- mkReg(False);
    Reg#(Bit#(8)) initIdx <- mkReg(0);

    rule init (!initDone);
        let initData = Struct45 {tag: 51'h6, value: Struct10 {mesi_owned: False, mesi_status: 3'h1, mesi_dir_st: 3'h1, mesi_dir_sharers: 4'h0}};
        bram.wrReq(initIdx, initData);
        initIdx <= initIdx + 1;
        initDone <= (initIdx == maxBound);
    endrule

    method Action rdReq_infoRam__002__2 (Bit#(8) x_0) if(initDone);
        bram.rdReq(x_0);
    endmethod

    method Action wrReq_infoRam__002__2 (Struct47 x_0) if(initDone);
        bram.wrReq(x_0.addr, x_0.datain);
    endmethod

    method ActionValue#(Struct45) rdResp_infoRam__002__2 () if(initDone);
        bram.deqRdResp ();
        let data = bram.rdResp ();
        return data;
    endmethod


endmodule

interface Module84;
    method Action rdReq_infoRam__002__1 (Bit#(8) x_0);
    method Action wrReq_infoRam__002__1 (Struct47 x_0);
    method ActionValue#(Struct45) rdResp_infoRam__002__1 ();
endinterface

module mkModule84 (Module84);
    RWBramCore#(Bit#(8), Struct45) bram <- mkRWBramCore();
    Reg#(Bool) initDone <- mkReg(False);
    Reg#(Bit#(8)) initIdx <- mkReg(0);

    rule init (!initDone);
        let initData = Struct45 {tag: 51'h5, value: Struct10 {mesi_owned: False, mesi_status: 3'h1, mesi_dir_st: 3'h1, mesi_dir_sharers: 4'h0}};
        bram.wrReq(initIdx, initData);
        initIdx <= initIdx + 1;
        initDone <= (initIdx == maxBound);
    endrule

    method Action rdReq_infoRam__002__1 (Bit#(8) x_0) if(initDone);
        bram.rdReq(x_0);
    endmethod

    method Action wrReq_infoRam__002__1 (Struct47 x_0) if(initDone);
        bram.wrReq(x_0.addr, x_0.datain);
    endmethod

    method ActionValue#(Struct45) rdResp_infoRam__002__1 () if(initDone);
        bram.deqRdResp ();
        let data = bram.rdResp ();
        return data;
    endmethod


endmodule

interface Module85;
    method Action rdReq_infoRam__002__0 (Bit#(8) x_0);
    method Action wrReq_infoRam__002__0 (Struct47 x_0);
    method ActionValue#(Struct45) rdResp_infoRam__002__0 ();
endinterface

module mkModule85 (Module85);
    RWBramCore#(Bit#(8), Struct45) bram <- mkRWBramCore();
    Reg#(Bool) initDone <- mkReg(False);
    Reg#(Bit#(8)) initIdx <- mkReg(0);

    rule init (!initDone);
        let initData = Struct45 {tag: 51'h4, value: Struct10 {mesi_owned: False, mesi_status: 3'h1, mesi_dir_st: 3'h1, mesi_dir_sharers: 4'h0}};
        bram.wrReq(initIdx, initData);
        initIdx <= initIdx + 1;
        initDone <= (initIdx == maxBound);
    endrule

    method Action rdReq_infoRam__002__0 (Bit#(8) x_0) if(initDone);
        bram.rdReq(x_0);
    endmethod

    method Action wrReq_infoRam__002__0 (Struct47 x_0) if(initDone);
        bram.wrReq(x_0.addr, x_0.datain);
    endmethod

    method ActionValue#(Struct45) rdResp_infoRam__002__0 () if(initDone);
        bram.deqRdResp ();
        let data = bram.rdResp ();
        return data;
    endmethod


endmodule

interface Module86;
    method Action rdReq_dataRam__002 (Bit#(10) x_0);
    method Action wrReq_dataRam__002 (Struct49 x_0);
    method ActionValue#(Vector#(4, Bit#(64))) rdResp_dataRam__002 ();
endinterface

module mkModule86 (Module86);
    RWBramCore#(Bit#(10), Vector#(4, Bit#(64))) bram <- mkRWBramCore();
    Reg#(Bool) initDone <- mkReg(False);
    Reg#(Bit#(10)) initIdx <- mkReg(0);

    rule init (!initDone);
        let initData = vec(64'h0, 64'h0, 64'h0, 64'h0);
        bram.wrReq(initIdx, initData);
        initIdx <= initIdx + 1;
        initDone <= (initIdx == maxBound);
    endrule

    method Action rdReq_dataRam__002 (Bit#(10) x_0) if(initDone);
        bram.rdReq(x_0);
    endmethod

    method Action wrReq_dataRam__002 (Struct49 x_0) if(initDone);
        bram.wrReq(x_0.addr, x_0.datain);
    endmethod

    method ActionValue#(Vector#(4, Bit#(64))) rdResp_dataRam__002 ()
    if(initDone);
        bram.deqRdResp ();
        let data = bram.rdResp ();
        return data;
    endmethod


endmodule

interface Module87;
    method Action rdReq_repRam__002 (Bit#(8) x_0);
    method Action wrReq_repRam__002 (Struct50 x_0);
    method ActionValue#(Vector#(4, Bit#(8))) rdResp_repRam__002 ();
endinterface

module mkModule87 (Module87);
    RWBramCore#(Bit#(8), Vector#(4, Bit#(8))) bram <- mkRWBramCore();
    Reg#(Bool) initDone <- mkReg(False);
    Reg#(Bit#(8)) initIdx <- mkReg(0);

    rule init (!initDone);
        let initData = vec(8'h1, 8'h1, 8'h1, 8'h1);
        bram.wrReq(initIdx, initData);
        initIdx <= initIdx + 1;
        initDone <= (initIdx == maxBound);
    endrule

    method Action rdReq_repRam__002 (Bit#(8) x_0) if(initDone);
        bram.rdReq(x_0);
    endmethod

    method Action wrReq_repRam__002 (Struct50 x_0) if(initDone);
        bram.wrReq(x_0.addr, x_0.datain);
    endmethod

    method ActionValue#(Vector#(4, Bit#(8))) rdResp_repRam__002 ()
    if(initDone);
        bram.deqRdResp ();
        let data = bram.rdResp ();
        return data;
    endmethod


endmodule

interface Module88;
    method ActionValue#(Struct14) getMSHR_002 (Bit#(2) x_0);
    method ActionValue#(Struct1) getMSHRRq_002 (Bit#(2) x_0);
    method ActionValue#(Struct36) getPRqSlot_002 (Struct35 x_0);
    method ActionValue#(Struct36) getCRqSlot_002 (Struct35 x_0);
    method ActionValue#(Struct35) getWait_002 ();
    method Action registerUL_002 (Struct43 x_0);
    method Action canImm_002 (Bit#(64) x_0);
    method Action setULImm_002 (Struct1 x_0);
    method ActionValue#(Bit#(2)) getULReady_002 (Bit#(64) x_0);
    method Action startRelease_002 (Bit#(2) x_0);
    method Action releaseMSHR_002 (Bit#(2) x_0);
endinterface

module mkModule88
    (Module88);
    Reg#(Vector#(4, Struct14)) mshrs_002 <- mkReg(unpack(0));
    Reg#(Vector#(4, Bit#(64))) maddrs_002 <- mkReg(unpack(0));
    Reg#(Vector#(4, Bit#(3))) msts_002 <- mkReg(unpack(0));
    Reg#(Vector#(4, Struct51)) mnexts_002 <- mkReg(unpack(0));
    Reg#(Vector#(4, Struct1)) rqs_002 <- mkReg(unpack(0));

    // No rules in this module

    method ActionValue#(Struct14) getMSHR_002 (Bit#(2) x_0);
        let x_1 = (mshrs_002);
        return (x_1)[x_0];
    endmethod

    method ActionValue#(Struct1) getMSHRRq_002 (Bit#(2) x_0);
        let x_1 = (rqs_002);
        return (x_1)[x_0];
    endmethod

    method ActionValue#(Struct36) getPRqSlot_002 (Struct35 x_0);
        let x_1 = (mshrs_002);
        let x_2 = (maddrs_002);
        let x_3 = (msts_002);
        let x_4 = (mnexts_002);
        Struct51 x_5 = ((((x_3)[(Bit#(2))'(2'h0)]) == ((Bit#(3))'(3'h0)) ?
        (Struct51 {valid : (Bool)'(True), data : (Bit#(2))'(2'h0)}) :
        ((((x_3)[(Bit#(2))'(2'h1)]) == ((Bit#(3))'(3'h0)) ? (Struct51 {valid
        : (Bool)'(True), data : (Bit#(2))'(2'h1)}) : (Struct51 {valid :
        (Bool)'(False), data : unpack(0)})))));
        Bool x_6 = ((x_5).valid);
        Bit#(2) x_7 = ((x_5).data);
        Bit#(64) x_8 = (((x_0).r_msg).addr);
        Bool x_9 = ((((((x_3)[(Bit#(2))'(2'h0)]) == ((Bit#(3))'(3'h4))) ||
        (((x_3)[(Bit#(2))'(2'h0)]) == ((Bit#(3))'(3'h6)))) && (((!
        (((x_2)[(Bit#(2))'(2'h0)]) == (x_8))) &&
        ((((x_2)[(Bit#(2))'(2'h0)])[12:5]) == ((x_8)[12:5]))) ||
        (((x_2)[(Bit#(2))'(2'h0)]) == (x_8))) ? ((Bool)'(True)) :
        ((((((x_3)[(Bit#(2))'(2'h1)]) == ((Bit#(3))'(3'h4))) ||
        (((x_3)[(Bit#(2))'(2'h1)]) == ((Bit#(3))'(3'h6)))) && (((!
        (((x_2)[(Bit#(2))'(2'h1)]) == (x_8))) &&
        ((((x_2)[(Bit#(2))'(2'h1)])[12:5]) == ((x_8)[12:5]))) ||
        (((x_2)[(Bit#(2))'(2'h1)]) == (x_8))) ? ((Bool)'(True)) :
        ((((((x_3)[(Bit#(2))'(2'h2)]) == ((Bit#(3))'(3'h4))) ||
        (((x_3)[(Bit#(2))'(2'h2)]) == ((Bit#(3))'(3'h6)))) && (((!
        (((x_2)[(Bit#(2))'(2'h2)]) == (x_8))) &&
        ((((x_2)[(Bit#(2))'(2'h2)])[12:5]) == ((x_8)[12:5]))) ||
        (((x_2)[(Bit#(2))'(2'h2)]) == (x_8))) ? ((Bool)'(True)) :
        ((((((x_3)[(Bit#(2))'(2'h3)]) == ((Bit#(3))'(3'h4))) ||
        (((x_3)[(Bit#(2))'(2'h3)]) == ((Bit#(3))'(3'h6)))) && (((!
        (((x_2)[(Bit#(2))'(2'h3)]) == (x_8))) &&
        ((((x_2)[(Bit#(2))'(2'h3)])[12:5]) == ((x_8)[12:5]))) ||
        (((x_2)[(Bit#(2))'(2'h3)]) == (x_8))) ? ((Bool)'(True)) :
        ((Bool)'(False))))))))));
        Struct51 x_10 = ((((((x_3)[(Bit#(2))'(2'h0)]) == ((Bit#(3))'(3'h5)))
        && (! (((x_1)[(Bit#(2))'(2'h0)]).m_is_ul))) &&
        (((x_2)[(Bit#(2))'(2'h0)]) == (x_8)) ? (Struct51 {valid :
        (Bool)'(True), data : (Bit#(2))'(2'h0)}) :
        ((((((x_3)[(Bit#(2))'(2'h1)]) == ((Bit#(3))'(3'h5))) && (!
        (((x_1)[(Bit#(2))'(2'h1)]).m_is_ul))) && (((x_2)[(Bit#(2))'(2'h1)])
        == (x_8)) ? (Struct51 {valid : (Bool)'(True), data :
        (Bit#(2))'(2'h1)}) : ((((((x_3)[(Bit#(2))'(2'h2)]) ==
        ((Bit#(3))'(3'h5))) && (! (((x_1)[(Bit#(2))'(2'h2)]).m_is_ul))) &&
        (((x_2)[(Bit#(2))'(2'h2)]) == (x_8)) ? (Struct51 {valid :
        (Bool)'(True), data : (Bit#(2))'(2'h2)}) :
        ((((((x_3)[(Bit#(2))'(2'h3)]) == ((Bit#(3))'(3'h5))) && (!
        (((x_1)[(Bit#(2))'(2'h3)]).m_is_ul))) && (((x_2)[(Bit#(2))'(2'h3)])
        == (x_8)) ? (Struct51 {valid : (Bool)'(True), data :
        (Bit#(2))'(2'h3)}) : (Struct51 {valid : (Bool)'(False), data :
        unpack(0)})))))))));
        Bool x_11 = ((x_10).valid);
        Struct36 x_12 = (Struct36 {s_has_slot : (x_6) && (! (x_9)),
        s_conflict : x_11, s_id :
        x_7});
        if ((x_6) && (! (x_9))) begin
            mshrs_002 <= update (x_1, x_7, Struct14 {m_is_ul : unpack(0),
            m_qidx : (x_0).r_msg_from, m_rsb : unpack(0), m_dl_rss_from :
            unpack(0), m_dl_rss_recv : unpack(0)});
            maddrs_002 <= update (x_2, x_7, ((x_0).r_msg).addr);
            msts_002 <= update (x_3, x_7, (x_11 ? ((Bit#(3))'(3'h1)) :
            ((Bit#(3))'(3'h4))));
            let x_13 = (rqs_002);
            rqs_002 <= update (x_13, x_7,
            (x_0).r_msg);
            if (x_11) begin
                Bit#(2) x_14 = ((((! (((x_3)[(Bit#(2))'(2'h0)]) ==
                ((Bit#(3))'(3'h0)))) && (!
                (((x_4)[(Bit#(2))'(2'h0)]).valid))) &&
                (((x_2)[(Bit#(2))'(2'h0)]) == (x_8)) ? ((Bit#(2))'(2'h0)) :
                ((((! (((x_3)[(Bit#(2))'(2'h1)]) == ((Bit#(3))'(3'h0)))) &&
                (! (((x_4)[(Bit#(2))'(2'h1)]).valid))) &&
                (((x_2)[(Bit#(2))'(2'h1)]) == (x_8)) ? ((Bit#(2))'(2'h1)) :
                ((((! (((x_3)[(Bit#(2))'(2'h2)]) == ((Bit#(3))'(3'h0)))) &&
                (! (((x_4)[(Bit#(2))'(2'h2)]).valid))) &&
                (((x_2)[(Bit#(2))'(2'h2)]) == (x_8)) ? ((Bit#(2))'(2'h2)) :
                ((((! (((x_3)[(Bit#(2))'(2'h3)]) == ((Bit#(3))'(3'h0)))) &&
                (! (((x_4)[(Bit#(2))'(2'h3)]).valid))) &&
                (((x_2)[(Bit#(2))'(2'h3)]) == (x_8)) ? ((Bit#(2))'(2'h3)) :
                (unpack(0))))))))));
                Struct51 x_15 = ((x_4)[x_14]);
                mnexts_002 <= update (x_4, x_14, Struct51 {valid :
                (Bool)'(True), data : x_7});
            end else begin

            end
        end else begin

        end
        return x_12;
    endmethod

    method ActionValue#(Struct36) getCRqSlot_002 (Struct35 x_0);
        let x_1 = (mshrs_002);
        let x_2 = (maddrs_002);
        let x_3 = (msts_002);
        let x_4 = (mnexts_002);
        Struct51 x_5 = ((((x_3)[(Bit#(2))'(2'h2)]) == ((Bit#(3))'(3'h0)) ?
        (Struct51 {valid : (Bool)'(True), data : (Bit#(2))'(2'h2)}) :
        ((((x_3)[(Bit#(2))'(2'h3)]) == ((Bit#(3))'(3'h0)) ? (Struct51 {valid
        : (Bool)'(True), data : (Bit#(2))'(2'h3)}) : (Struct51 {valid :
        (Bool)'(False), data : unpack(0)})))));
        Bool x_6 = ((x_5).valid);
        Bit#(2) x_7 = ((x_5).data);
        Bit#(64) x_8 = (((x_0).r_msg).addr);
        Bool x_9 = ((((((x_3)[(Bit#(2))'(2'h0)]) == ((Bit#(3))'(3'h4))) ||
        (((x_3)[(Bit#(2))'(2'h0)]) == ((Bit#(3))'(3'h6)))) && ((!
        (((x_2)[(Bit#(2))'(2'h0)]) == (x_8))) &&
        ((((x_2)[(Bit#(2))'(2'h0)])[12:5]) == ((x_8)[12:5]))) ?
        ((Bool)'(True)) : ((((((x_3)[(Bit#(2))'(2'h1)]) ==
        ((Bit#(3))'(3'h4))) || (((x_3)[(Bit#(2))'(2'h1)]) ==
        ((Bit#(3))'(3'h6)))) && ((! (((x_2)[(Bit#(2))'(2'h1)]) == (x_8))) &&
        ((((x_2)[(Bit#(2))'(2'h1)])[12:5]) == ((x_8)[12:5]))) ?
        ((Bool)'(True)) : ((((((x_3)[(Bit#(2))'(2'h2)]) ==
        ((Bit#(3))'(3'h4))) || (((x_3)[(Bit#(2))'(2'h2)]) ==
        ((Bit#(3))'(3'h6)))) && ((! (((x_2)[(Bit#(2))'(2'h2)]) == (x_8))) &&
        ((((x_2)[(Bit#(2))'(2'h2)])[12:5]) == ((x_8)[12:5]))) ?
        ((Bool)'(True)) : ((((((x_3)[(Bit#(2))'(2'h3)]) ==
        ((Bit#(3))'(3'h4))) || (((x_3)[(Bit#(2))'(2'h3)]) ==
        ((Bit#(3))'(3'h6)))) && ((! (((x_2)[(Bit#(2))'(2'h3)]) == (x_8))) &&
        ((((x_2)[(Bit#(2))'(2'h3)])[12:5]) == ((x_8)[12:5]))) ?
        ((Bool)'(True)) : ((Bool)'(False))))))))));
        Struct51 x_10 = (((((! (((x_3)[(Bit#(2))'(2'h2)]) ==
        ((Bit#(3))'(3'h0)))) && (! (((x_4)[(Bit#(2))'(2'h2)]).valid))) &&
        (((x_1)[(Bit#(2))'(2'h2)]).m_is_ul)) && (((x_2)[(Bit#(2))'(2'h2)]) ==
        (x_8)) ? (Struct51 {valid : (Bool)'(True), data : (Bit#(2))'(2'h2)})
        : (((((! (((x_3)[(Bit#(2))'(2'h3)]) == ((Bit#(3))'(3'h0)))) && (!
        (((x_4)[(Bit#(2))'(2'h3)]).valid))) &&
        (((x_1)[(Bit#(2))'(2'h3)]).m_is_ul)) && (((x_2)[(Bit#(2))'(2'h3)]) ==
        (x_8)) ? (Struct51 {valid : (Bool)'(True), data : (Bit#(2))'(2'h3)})
        : (Struct51 {valid : (Bool)'(False), data : unpack(0)})))));
        Struct51 x_11 = (((((! (((x_3)[(Bit#(2))'(2'h0)]) ==
        ((Bit#(3))'(3'h0)))) && (! (((x_4)[(Bit#(2))'(2'h0)]).valid))) && (!
        (((x_1)[(Bit#(2))'(2'h0)]).m_is_ul))) && (((x_2)[(Bit#(2))'(2'h0)])
        == (x_8)) ? (Struct51 {valid : (Bool)'(True), data :
        (Bit#(2))'(2'h0)}) : (((((! (((x_3)[(Bit#(2))'(2'h1)]) ==
        ((Bit#(3))'(3'h0)))) && (! (((x_4)[(Bit#(2))'(2'h1)]).valid))) && (!
        (((x_1)[(Bit#(2))'(2'h1)]).m_is_ul))) && (((x_2)[(Bit#(2))'(2'h1)])
        == (x_8)) ? (Struct51 {valid : (Bool)'(True), data :
        (Bit#(2))'(2'h1)}) : (((((! (((x_3)[(Bit#(2))'(2'h2)]) ==
        ((Bit#(3))'(3'h0)))) && (! (((x_4)[(Bit#(2))'(2'h2)]).valid))) && (!
        (((x_1)[(Bit#(2))'(2'h2)]).m_is_ul))) && (((x_2)[(Bit#(2))'(2'h2)])
        == (x_8)) ? (Struct51 {valid : (Bool)'(True), data :
        (Bit#(2))'(2'h2)}) : (((((! (((x_3)[(Bit#(2))'(2'h3)]) ==
        ((Bit#(3))'(3'h0)))) && (! (((x_4)[(Bit#(2))'(2'h3)]).valid))) && (!
        (((x_1)[(Bit#(2))'(2'h3)]).m_is_ul))) && (((x_2)[(Bit#(2))'(2'h3)])
        == (x_8)) ? (Struct51 {valid : (Bool)'(True), data :
        (Bit#(2))'(2'h3)}) : (Struct51 {valid : (Bool)'(False), data :
        unpack(0)})))))))));
        Bool x_12 = ((x_10).valid);
        Bool x_13 = ((x_11).valid);
        Bool x_14 = ((x_12) || (x_13));
        Struct36 x_15 = (Struct36 {s_has_slot : (x_6) && (! (x_9)),
        s_conflict : x_14, s_id :
        x_7});
        if ((x_6) && (! (x_9))) begin
            mshrs_002 <= update (x_1, x_7, Struct14 {m_is_ul : unpack(0),
            m_qidx : (x_0).r_msg_from, m_rsb : unpack(0), m_dl_rss_from :
            unpack(0), m_dl_rss_recv : unpack(0)});
            maddrs_002 <= update (x_2, x_7, ((x_0).r_msg).addr);
            msts_002 <= update (x_3, x_7, (x_14 ? ((Bit#(3))'(3'h1)) :
            ((Bit#(3))'(3'h4))));
            let x_16 = (rqs_002);
            rqs_002 <= update (x_16, x_7,
            (x_0).r_msg);
            if (x_14) begin
                Bit#(2) x_17 = ((x_12 ? ((x_10).data) :
                ((x_11).data)));
                Struct51 x_18 = ((x_4)[x_17]);
                mnexts_002 <= update (x_4, x_17, Struct51 {valid :
                (Bool)'(True), data : x_7});
            end else begin

            end
        end else begin

        end
        return x_15;
    endmethod

    method ActionValue#(Struct35) getWait_002 ();
        let x_1 = (mshrs_002);
        let x_2 = (maddrs_002);
        let x_3 = (msts_002);
        let x_4 = (rqs_002);
        Struct51 x_5 = ((((x_3)[(Bit#(2))'(2'h0)]) == ((Bit#(3))'(3'h2)) ?
        (Struct51 {valid : (Bool)'(True), data : (Bit#(2))'(2'h0)}) :
        ((((x_3)[(Bit#(2))'(2'h1)]) == ((Bit#(3))'(3'h2)) ? (Struct51 {valid
        : (Bool)'(True), data : (Bit#(2))'(2'h1)}) :
        ((((x_3)[(Bit#(2))'(2'h2)]) == ((Bit#(3))'(3'h2)) ? (Struct51 {valid
        : (Bool)'(True), data : (Bit#(2))'(2'h2)}) :
        ((((x_3)[(Bit#(2))'(2'h3)]) == ((Bit#(3))'(3'h2)) ? (Struct51 {valid
        : (Bool)'(True), data : (Bit#(2))'(2'h3)}) : (Struct51 {valid :
        (Bool)'(False), data : unpack(0)})))))))));
        when ((x_5).valid, noAction);
        Bit#(2) x_6 = ((x_5).data);
        Struct14 x_7 = ((x_1)[x_6]);
        Bit#(64) x_8 = ((x_2)[x_6]);
        Struct1 x_9 = ((x_4)[x_6]);
        Bool x_10 = ((((! (((x_3)[(Bit#(2))'(2'h0)]) < ((Bit#(3))'(3'h4))))
        && (((x_2)[(Bit#(2))'(2'h0)]) == (x_8))) ||
        (((((x_3)[(Bit#(2))'(2'h0)]) == ((Bit#(3))'(3'h4))) ||
        (((x_3)[(Bit#(2))'(2'h0)]) == ((Bit#(3))'(3'h6)))) && ((!
        (((x_2)[(Bit#(2))'(2'h0)]) == (x_8))) &&
        ((((x_2)[(Bit#(2))'(2'h0)])[12:5]) == ((x_8)[12:5])))) ?
        ((Bool)'(True)) : ((((! (((x_3)[(Bit#(2))'(2'h1)]) <
        ((Bit#(3))'(3'h4)))) && (((x_2)[(Bit#(2))'(2'h1)]) == (x_8))) ||
        (((((x_3)[(Bit#(2))'(2'h1)]) == ((Bit#(3))'(3'h4))) ||
        (((x_3)[(Bit#(2))'(2'h1)]) == ((Bit#(3))'(3'h6)))) && ((!
        (((x_2)[(Bit#(2))'(2'h1)]) == (x_8))) &&
        ((((x_2)[(Bit#(2))'(2'h1)])[12:5]) == ((x_8)[12:5])))) ?
        ((Bool)'(True)) : ((((! (((x_3)[(Bit#(2))'(2'h2)]) <
        ((Bit#(3))'(3'h4)))) && (((x_2)[(Bit#(2))'(2'h2)]) == (x_8))) ||
        (((((x_3)[(Bit#(2))'(2'h2)]) == ((Bit#(3))'(3'h4))) ||
        (((x_3)[(Bit#(2))'(2'h2)]) == ((Bit#(3))'(3'h6)))) && ((!
        (((x_2)[(Bit#(2))'(2'h2)]) == (x_8))) &&
        ((((x_2)[(Bit#(2))'(2'h2)])[12:5]) == ((x_8)[12:5])))) ?
        ((Bool)'(True)) : ((((! (((x_3)[(Bit#(2))'(2'h3)]) <
        ((Bit#(3))'(3'h4)))) && (((x_2)[(Bit#(2))'(2'h3)]) == (x_8))) ||
        (((((x_3)[(Bit#(2))'(2'h3)]) == ((Bit#(3))'(3'h4))) ||
        (((x_3)[(Bit#(2))'(2'h3)]) == ((Bit#(3))'(3'h6)))) && ((!
        (((x_2)[(Bit#(2))'(2'h3)]) == (x_8))) &&
        ((((x_2)[(Bit#(2))'(2'h3)])[12:5]) == ((x_8)[12:5])))) ?
        ((Bool)'(True)) : ((Bool)'(False))))))))));
        when (! (x_10), noAction);
        msts_002 <= update (x_3, x_6, (Bit#(3))'(3'h4));
        Struct35 x_11 = (Struct35 {r_id : x_6, r_msg : x_9, r_msg_from :
        (x_7).m_qidx});
        return x_11;
    endmethod

    method Action registerUL_002 (Struct43 x_0);
        let x_1 = (mshrs_002);
        let x_2 = (msts_002);
        Bit#(2) x_3 = ((x_0).r_id);
        mshrs_002 <= update (x_1, x_3, Struct14 {m_is_ul : (Bool)'(True),
        m_qidx : {((Bit#(2))'(2'h2)),((x_0).r_ul_rsbTo)}, m_rsb :
        (x_0).r_ul_rsb, m_dl_rss_from : unpack(0), m_dl_rss_recv :
        unpack(0)});
        msts_002 <= update (x_2, x_3, (Bit#(3))'(3'h5));
    endmethod

    method Action canImm_002 (Bit#(64) x_0);
        let x_1 = (maddrs_002);
        let x_2 = (msts_002);
        let x_3 = (mnexts_002);
        Struct51 x_4 = ((((x_2)[(Bit#(2))'(2'h2)]) == ((Bit#(3))'(3'h0)) ?
        (Struct51 {valid : (Bool)'(True), data : (Bit#(2))'(2'h2)}) :
        ((((x_2)[(Bit#(2))'(2'h3)]) == ((Bit#(3))'(3'h0)) ? (Struct51 {valid
        : (Bool)'(True), data : (Bit#(2))'(2'h3)}) : (Struct51 {valid :
        (Bool)'(False), data : unpack(0)})))));
        when ((x_4).valid, noAction);
        Struct51 x_5 = ((((! (((x_2)[(Bit#(2))'(2'h0)]) ==
        ((Bit#(3))'(3'h0)))) && (! (((x_3)[(Bit#(2))'(2'h0)]).valid))) &&
        (((x_1)[(Bit#(2))'(2'h0)]) == (x_0)) ? (Struct51 {valid :
        (Bool)'(True), data : (Bit#(2))'(2'h0)}) : ((((!
        (((x_2)[(Bit#(2))'(2'h1)]) == ((Bit#(3))'(3'h0)))) && (!
        (((x_3)[(Bit#(2))'(2'h1)]).valid))) && (((x_1)[(Bit#(2))'(2'h1)]) ==
        (x_0)) ? (Struct51 {valid : (Bool)'(True), data : (Bit#(2))'(2'h1)})
        : ((((! (((x_2)[(Bit#(2))'(2'h2)]) == ((Bit#(3))'(3'h0)))) && (!
        (((x_3)[(Bit#(2))'(2'h2)]).valid))) && (((x_1)[(Bit#(2))'(2'h2)]) ==
        (x_0)) ? (Struct51 {valid : (Bool)'(True), data : (Bit#(2))'(2'h2)})
        : ((((! (((x_2)[(Bit#(2))'(2'h3)]) == ((Bit#(3))'(3'h0)))) && (!
        (((x_3)[(Bit#(2))'(2'h3)]).valid))) && (((x_1)[(Bit#(2))'(2'h3)]) ==
        (x_0)) ? (Struct51 {valid : (Bool)'(True), data : (Bit#(2))'(2'h3)})
        : (Struct51 {valid : (Bool)'(False), data : unpack(0)})))))))));
        when (! ((x_5).valid), noAction);
    endmethod

    method Action setULImm_002 (Struct1 x_0);
        let x_1 = (mshrs_002);
        let x_2 = (maddrs_002);
        let x_3 = (msts_002);
        let x_4 = (rqs_002);
        Struct51 x_5 = ((((x_3)[(Bit#(2))'(2'h2)]) == ((Bit#(3))'(3'h0)) ?
        (Struct51 {valid : (Bool)'(True), data : (Bit#(2))'(2'h2)}) :
        ((((x_3)[(Bit#(2))'(2'h3)]) == ((Bit#(3))'(3'h0)) ? (Struct51 {valid
        : (Bool)'(True), data : (Bit#(2))'(2'h3)}) : (Struct51 {valid :
        (Bool)'(False), data : unpack(0)})))));
        when ((x_5).valid, noAction);
        Bit#(2) x_6 = ((x_5).data);
        Bit#(64) x_7 = ((x_0).addr);
        Struct51 x_8 = (((! (((x_3)[(Bit#(2))'(2'h0)]) ==
        ((Bit#(3))'(3'h0)))) && (((x_2)[(Bit#(2))'(2'h0)]) == (x_7)) ?
        (Struct51 {valid : (Bool)'(True), data : (Bit#(2))'(2'h0)}) : (((!
        (((x_3)[(Bit#(2))'(2'h1)]) == ((Bit#(3))'(3'h0)))) &&
        (((x_2)[(Bit#(2))'(2'h1)]) == (x_7)) ? (Struct51 {valid :
        (Bool)'(True), data : (Bit#(2))'(2'h1)}) : (((!
        (((x_3)[(Bit#(2))'(2'h2)]) == ((Bit#(3))'(3'h0)))) &&
        (((x_2)[(Bit#(2))'(2'h2)]) == (x_7)) ? (Struct51 {valid :
        (Bool)'(True), data : (Bit#(2))'(2'h2)}) : (((!
        (((x_3)[(Bit#(2))'(2'h3)]) == ((Bit#(3))'(3'h0)))) &&
        (((x_2)[(Bit#(2))'(2'h3)]) == (x_7)) ? (Struct51 {valid :
        (Bool)'(True), data : (Bit#(2))'(2'h3)}) : (Struct51 {valid :
        (Bool)'(False), data : unpack(0)})))))))));
        when (! ((x_8).valid), noAction);
        mshrs_002 <= update (x_1, x_6, Struct14 {m_is_ul : (Bool)'(True),
        m_qidx : unpack(0), m_rsb : (Bool)'(False), m_dl_rss_from :
        unpack(0), m_dl_rss_recv : unpack(0)});
        maddrs_002 <= update (x_2, x_6, (x_0).addr);
        msts_002 <= update (x_3, x_6, (Bit#(3))'(3'h5));
        rqs_002 <= update (x_4, x_6, x_0);
    endmethod

    method ActionValue#(Bit#(2)) getULReady_002 (Bit#(64) x_0);
        let x_1 = (mshrs_002);
        let x_2 = (maddrs_002);
        let x_3 = (msts_002);
        Bool x_4 = (((((((x_3)[(Bit#(2))'(2'h0)]) == ((Bit#(3))'(3'h4))) ||
        (((x_3)[(Bit#(2))'(2'h0)]) == ((Bit#(3))'(3'h6)))) && ((!
        (((x_2)[(Bit#(2))'(2'h0)]) == (x_0))) &&
        ((((x_2)[(Bit#(2))'(2'h0)])[12:5]) == ((x_0)[12:5])))) || (((!
        (((x_3)[(Bit#(2))'(2'h0)]) < ((Bit#(3))'(3'h4)))) && (!
        (((x_1)[(Bit#(2))'(2'h0)]).m_is_ul))) && (((x_2)[(Bit#(2))'(2'h0)])
        == (x_0))) ? ((Bool)'(True)) : (((((((x_3)[(Bit#(2))'(2'h1)]) ==
        ((Bit#(3))'(3'h4))) || (((x_3)[(Bit#(2))'(2'h1)]) ==
        ((Bit#(3))'(3'h6)))) && ((! (((x_2)[(Bit#(2))'(2'h1)]) == (x_0))) &&
        ((((x_2)[(Bit#(2))'(2'h1)])[12:5]) == ((x_0)[12:5])))) || (((!
        (((x_3)[(Bit#(2))'(2'h1)]) < ((Bit#(3))'(3'h4)))) && (!
        (((x_1)[(Bit#(2))'(2'h1)]).m_is_ul))) && (((x_2)[(Bit#(2))'(2'h1)])
        == (x_0))) ? ((Bool)'(True)) : (((((((x_3)[(Bit#(2))'(2'h2)]) ==
        ((Bit#(3))'(3'h4))) || (((x_3)[(Bit#(2))'(2'h2)]) ==
        ((Bit#(3))'(3'h6)))) && ((! (((x_2)[(Bit#(2))'(2'h2)]) == (x_0))) &&
        ((((x_2)[(Bit#(2))'(2'h2)])[12:5]) == ((x_0)[12:5])))) || (((!
        (((x_3)[(Bit#(2))'(2'h2)]) < ((Bit#(3))'(3'h4)))) && (!
        (((x_1)[(Bit#(2))'(2'h2)]).m_is_ul))) && (((x_2)[(Bit#(2))'(2'h2)])
        == (x_0))) ? ((Bool)'(True)) : (((((((x_3)[(Bit#(2))'(2'h3)]) ==
        ((Bit#(3))'(3'h4))) || (((x_3)[(Bit#(2))'(2'h3)]) ==
        ((Bit#(3))'(3'h6)))) && ((! (((x_2)[(Bit#(2))'(2'h3)]) == (x_0))) &&
        ((((x_2)[(Bit#(2))'(2'h3)])[12:5]) == ((x_0)[12:5])))) || (((!
        (((x_3)[(Bit#(2))'(2'h3)]) < ((Bit#(3))'(3'h4)))) && (!
        (((x_1)[(Bit#(2))'(2'h3)]).m_is_ul))) && (((x_2)[(Bit#(2))'(2'h3)])
        == (x_0))) ? ((Bool)'(True)) : ((Bool)'(False))))))))));
        when (! (x_4), noAction);
        Struct51 x_5 = ((((((x_3)[(Bit#(2))'(2'h2)]) == ((Bit#(3))'(3'h5)))
        && (((x_1)[(Bit#(2))'(2'h2)]).m_is_ul)) && (((x_2)[(Bit#(2))'(2'h2)])
        == (x_0)) ? (Struct51 {valid : (Bool)'(True), data :
        (Bit#(2))'(2'h2)}) : ((((((x_3)[(Bit#(2))'(2'h3)]) ==
        ((Bit#(3))'(3'h5))) && (((x_1)[(Bit#(2))'(2'h3)]).m_is_ul)) &&
        (((x_2)[(Bit#(2))'(2'h3)]) == (x_0)) ? (Struct51 {valid :
        (Bool)'(True), data : (Bit#(2))'(2'h3)}) : (Struct51 {valid :
        (Bool)'(False), data : unpack(0)})))));
        when ((x_5).valid, noAction);
        Bit#(2) x_6 = ((x_5).data);
        return x_6;
    endmethod

    method Action startRelease_002 (Bit#(2) x_0);
        let x_1 = (msts_002);
        msts_002 <= update (x_1, x_0, (Bit#(3))'(3'h6));
    endmethod

    method Action releaseMSHR_002 (Bit#(2) x_0);
        let x_1 = (mshrs_002);
        let x_2 = (msts_002);
        let x_3 = (mnexts_002);
        mshrs_002 <= update (x_1, x_0, unpack(0));
        mnexts_002 <= update (x_3, x_0, unpack(0));
        Vector#(4, Bit#(3)) x_4 = (update (x_2, x_0, unpack(0)));
        Struct51 x_5 =
        ((x_3)[x_0]);
        let x_8 = ?;
        if ((x_5).valid) begin
            Bit#(2) x_6 = ((x_5).data);
            Vector#(4, Bit#(3)) x_7 = (update (x_4, x_6,
            (Bit#(3))'(3'h2)));
            x_8 = x_7;
        end else begin
            x_8 = x_4;
        end
        msts_002 <= x_8;
    endmethod
endmodule

interface Module89;
    method Action enq_fifoCRqInput_003 (Struct2 x_0);
    method ActionValue#(Struct2) deq_fifoCRqInput_003 ();
endinterface

module mkModule89 (Module89);
    FIFOF#(Struct2) pff <- mkSizedFIFOF(4);

    method Action enq_fifoCRqInput_003 (Struct2 x_0);
        pff.enq(x_0);
    endmethod

    method ActionValue#(Struct2) deq_fifoCRqInput_003 ();
        pff.deq();
        return pff.first();
    endmethod

endmodule

interface Module90;
    method Action enq_fifoPInput_003 (Struct2 x_0);
    method ActionValue#(Struct2) deq_fifoPInput_003 ();
endinterface

module mkModule90 (Module90);
    FIFOF#(Struct2) pff <- mkSizedFIFOF(4);

    method Action enq_fifoPInput_003 (Struct2 x_0);
        pff.enq(x_0);
    endmethod

    method ActionValue#(Struct2) deq_fifoPInput_003 ();
        pff.deq();
        return pff.first();
    endmethod

endmodule

interface Module91;
    method Action enq_fifoN2I_003 (Struct38 x_0);
    method ActionValue#(Struct38) deq_fifoN2I_003 ();
endinterface

module mkModule91 (Module91);
    FIFOF#(Struct38) pff <- mkPipelineFIFOF();

    method Action enq_fifoN2I_003 (Struct38 x_0);
        pff.enq(x_0);
    endmethod

    method ActionValue#(Struct38) deq_fifoN2I_003 ();
        pff.deq();
        return pff.first();
    endmethod

endmodule

interface Module92;
    method Action enq_fifoI2L_003 (Struct38 x_0);
    method ActionValue#(Struct38) deq_fifoI2L_003 ();
endinterface

module mkModule92 (Module92);
    FIFOF#(Struct38) pff <- mkPipelineFIFOF();

    method Action enq_fifoI2L_003 (Struct38 x_0);
        pff.enq(x_0);
    endmethod

    method ActionValue#(Struct38) deq_fifoI2L_003 ();
        pff.deq();
        return pff.first();
    endmethod

endmodule

interface Module93;
    method Action enq_fifoL2E_003 (Struct41 x_0);
    method ActionValue#(Struct41) deq_fifoL2E_003 ();
endinterface

module mkModule93 (Module93);
    FIFOF#(Struct41) pff <- mkPipelineFIFOF();

    method Action enq_fifoL2E_003 (Struct41 x_0);
        pff.enq(x_0);
    endmethod

    method ActionValue#(Struct41) deq_fifoL2E_003 ();
        pff.deq();
        return pff.first();
    endmethod

endmodule

interface Module94;
    method Action enq_fifo0030 (Struct1 x_0);
    method ActionValue#(Struct1) deq_fifo0030 ();
endinterface

module mkModule94 (Module94);
    FIFOF#(Struct1) pff <- mkSizedFIFOF(2);

    method Action enq_fifo0030 (Struct1 x_0);
        pff.enq(x_0);
    endmethod

    method ActionValue#(Struct1) deq_fifo0030 ();
        pff.deq();
        return pff.first();
    endmethod

endmodule

interface Module95;
    method Action enq_fifo0031 (Struct1 x_0);
    method ActionValue#(Struct1) deq_fifo0031 ();
endinterface

module mkModule95 (Module95);
    FIFOF#(Struct1) pff <- mkSizedFIFOF(2);

    method Action enq_fifo0031 (Struct1 x_0);
        pff.enq(x_0);
    endmethod

    method ActionValue#(Struct1) deq_fifo0031 ();
        pff.deq();
        return pff.first();
    endmethod

endmodule

interface Module96;
    method Action enq_fifo0032 (Struct1 x_0);
    method ActionValue#(Struct1) deq_fifo0032 ();
endinterface

module mkModule96 (Module96);
    FIFOF#(Struct1) pff <- mkSizedFIFOF(2);

    method Action enq_fifo0032 (Struct1 x_0);
        pff.enq(x_0);
    endmethod

    method ActionValue#(Struct1) deq_fifo0032 ();
        pff.deq();
        return pff.first();
    endmethod

endmodule

interface Module97;
    method Action enq_fifo00300 (Struct1 x_0);
    method ActionValue#(Struct1) deq_fifo00300 ();
endinterface

module mkModule97 (Module97);
    FIFOF#(Struct1) pff <- mkSizedFIFOF(2);

    method Action enq_fifo00300 (Struct1 x_0);
        pff.enq(x_0);
    endmethod

    method ActionValue#(Struct1) deq_fifo00300 ();
        pff.deq();
        return pff.first();
    endmethod

endmodule

interface Module98;
    method Action enq_fifo00302 (Struct1 x_0);
    method ActionValue#(Struct1) deq_fifo00302 ();
endinterface

module mkModule98 (Module98);
    FIFOF#(Struct1) pff <- mkSizedFIFOF(2);

    method Action enq_fifo00302 (Struct1 x_0);
        pff.enq(x_0);
    endmethod

    method ActionValue#(Struct1) deq_fifo00302 ();
        pff.deq();
        return pff.first();
    endmethod

endmodule

interface Module99;
    method ActionValue#(Struct37) victims__003__findVictim (Bit#(64) x_0);
    method ActionValue#(Struct13) victims__003__getVictim (Bit#(1) x_0);
    method Action victims__003__setVictim (Struct44 x_0);
    method Action victims__003__registerVictim (Struct13 x_0);
    method ActionValue#(Struct13) victims__003__getFirstVictim ();
    method ActionValue#(Bool) victims__003__hasVictim ();
    method Action victims__003__setVictimRq (Bit#(64) x_0);
    method Action victims__003__releaseVictim (Bit#(64) x_0);
endinterface

module mkModule99
    (Module99);
    Reg#(Vector#(2, Struct13)) victimRegs__003 <- mkReg(unpack(0));

    // No rules in this module

    method ActionValue#(Struct37) victims__003__findVictim (Bit#(64) x_0);
        let x_1 = (victimRegs__003);
        Struct13 x_2 =
        ((x_1)[(Bit#(1))'(1'h0)]);
        let x_5 = ?;
        if (((x_2).victim_valid) && (((x_2).victim_addr) == (x_0))) begin
            x_5 = Struct37 {valid : (Bool)'(True), data : (Bit#(1))'(1'h0)};
        end else begin
            Struct13 x_3 =
            ((x_1)[(Bit#(1))'(1'h1)]);
            let x_4 = ?;
            if (((x_3).victim_valid) && (((x_3).victim_addr) == (x_0)))
                begin
                x_4 = Struct37 {valid : (Bool)'(True), data :
                (Bit#(1))'(1'h1)};
            end else begin
                x_4 = Struct37 {valid : (Bool)'(False), data : unpack(0)};
            end
            x_5 = x_4;
        end
        return x_5;
    endmethod

    method ActionValue#(Struct13) victims__003__getVictim (Bit#(1) x_0);
        let x_1 = (victimRegs__003);
        return (x_1)[x_0];
    endmethod

    method Action victims__003__setVictim (Struct44 x_0);
        let x_1 = (victimRegs__003);
        Struct13 x_2 = ((x_1)[(x_0).victim_idx]);
        Struct13 x_3 = (Struct13 {victim_valid : (Bool)'(True), victim_addr :
        (x_2).victim_addr, victim_info : (x_0).victim_info, victim_value :
        (x_0).victim_value, victim_req : (x_2).victim_req});
        victimRegs__003 <= update (x_1, (x_0).victim_idx, x_3);
    endmethod

    method Action victims__003__registerVictim (Struct13 x_0);
        let x_1 = (victimRegs__003);
        Struct37 x_2 = ((((x_1)[(Bit#(1))'(1'h1)]).victim_valid ?
        ((((x_1)[(Bit#(1))'(1'h0)]).victim_valid ? (Struct37 {valid :
        (Bool)'(False), data : unpack(0)}) : (Struct37 {valid :
        (Bool)'(True), data : (Bit#(1))'(1'h0)}))) : (Struct37 {valid :
        (Bool)'(True), data : (Bit#(1))'(1'h1)})));
        when ((x_2).valid, noAction);
        Bit#(1) x_3 = ((x_2).data);
        victimRegs__003 <= update (x_1, x_3, x_0);
    endmethod

    method ActionValue#(Struct13) victims__003__getFirstVictim ();
        let x_1 = (victimRegs__003);
        Struct33 x_2 = (((((x_1)[(Bit#(1))'(1'h1)]).victim_valid) && (!
        (((x_1)[(Bit#(1))'(1'h1)]).victim_req)) ? (Struct33 {valid :
        (Bool)'(True), data : (x_1)[(Bit#(1))'(1'h1)]}) :
        (((((x_1)[(Bit#(1))'(1'h0)]).victim_valid) && (!
        (((x_1)[(Bit#(1))'(1'h0)]).victim_req)) ? (Struct33 {valid :
        (Bool)'(True), data : (x_1)[(Bit#(1))'(1'h0)]}) : (Struct33 {valid :
        (Bool)'(False), data : unpack(0)})))));
        when ((x_2).valid, noAction);
        return (x_2).data;
    endmethod

    method ActionValue#(Bool) victims__003__hasVictim ();
        let x_1 = (victimRegs__003);
        Bool x_2 = (((((x_1)[(Bit#(1))'(1'h1)]).victim_valid) && (!
        (((x_1)[(Bit#(1))'(1'h1)]).victim_req)) ? ((Bool)'(True)) :
        (((((x_1)[(Bit#(1))'(1'h0)]).victim_valid) && (!
        (((x_1)[(Bit#(1))'(1'h0)]).victim_req)) ? ((Bool)'(True)) :
        ((Bool)'(False))))));
        return x_2;
    endmethod

    method Action victims__003__setVictimRq (Bit#(64) x_0);
        let x_1 = (victimRegs__003);
        Struct13 x_2 =
        ((x_1)[(Bit#(1))'(1'h1)]);
        if (((x_2).victim_valid) && (((x_2).victim_addr) == (x_0)))
            begin
            Struct13 x_3 = (Struct13 {victim_valid : (x_2).victim_valid,
            victim_addr : (x_2).victim_addr, victim_info : (x_2).victim_info,
            victim_value : (x_2).victim_value, victim_req :
            (Bool)'(True)});
            victimRegs__003 <= update (x_1, (Bit#(1))'(1'h1), x_3);
        end else begin
            Struct13 x_4 =
            ((x_1)[(Bit#(1))'(1'h0)]);
            if (((x_4).victim_valid) && (((x_4).victim_addr) == (x_0)))
                begin
                Struct13 x_5 = (Struct13 {victim_valid : (x_4).victim_valid,
                victim_addr : (x_4).victim_addr, victim_info :
                (x_4).victim_info, victim_value : (x_4).victim_value,
                victim_req : (Bool)'(True)});
                victimRegs__003 <= update (x_1, (Bit#(1))'(1'h0), x_5);
            end else begin

            end
        end
    endmethod

    method Action victims__003__releaseVictim (Bit#(64) x_0);
        let x_1 = (victimRegs__003);
        Struct13 x_2 =
        ((x_1)[(Bit#(1))'(1'h0)]);
        if (((x_2).victim_valid) && (((x_2).victim_addr) == (x_0)))
            begin
            victimRegs__003 <= update (x_1, (Bit#(1))'(1'h0), unpack(0));
        end else begin
            Struct13 x_3 =
            ((x_1)[(Bit#(1))'(1'h1)]);
            if (((x_3).victim_valid) && (((x_3).victim_addr) == (x_0)))
                begin
                victimRegs__003 <= update (x_1, (Bit#(1))'(1'h1), unpack(0));
            end else begin

            end
        end
    endmethod
endmodule

interface Module100;
    method Action rdReq_infoRam__003__3 (Bit#(8) x_0);
    method Action wrReq_infoRam__003__3 (Struct47 x_0);
    method ActionValue#(Struct45) rdResp_infoRam__003__3 ();
endinterface

module mkModule100 (Module100);
    RWBramCore#(Bit#(8), Struct45) bram <- mkRWBramCore();
    Reg#(Bool) initDone <- mkReg(False);
    Reg#(Bit#(8)) initIdx <- mkReg(0);

    rule init (!initDone);
        let initData = Struct45 {tag: 51'h7, value: Struct10 {mesi_owned: False, mesi_status: 3'h1, mesi_dir_st: 3'h1, mesi_dir_sharers: 4'h0}};
        bram.wrReq(initIdx, initData);
        initIdx <= initIdx + 1;
        initDone <= (initIdx == maxBound);
    endrule

    method Action rdReq_infoRam__003__3 (Bit#(8) x_0) if(initDone);
        bram.rdReq(x_0);
    endmethod

    method Action wrReq_infoRam__003__3 (Struct47 x_0) if(initDone);
        bram.wrReq(x_0.addr, x_0.datain);
    endmethod

    method ActionValue#(Struct45) rdResp_infoRam__003__3 () if(initDone);
        bram.deqRdResp ();
        let data = bram.rdResp ();
        return data;
    endmethod


endmodule

interface Module101;
    method Action rdReq_infoRam__003__2 (Bit#(8) x_0);
    method Action wrReq_infoRam__003__2 (Struct47 x_0);
    method ActionValue#(Struct45) rdResp_infoRam__003__2 ();
endinterface

module mkModule101 (Module101);
    RWBramCore#(Bit#(8), Struct45) bram <- mkRWBramCore();
    Reg#(Bool) initDone <- mkReg(False);
    Reg#(Bit#(8)) initIdx <- mkReg(0);

    rule init (!initDone);
        let initData = Struct45 {tag: 51'h6, value: Struct10 {mesi_owned: False, mesi_status: 3'h1, mesi_dir_st: 3'h1, mesi_dir_sharers: 4'h0}};
        bram.wrReq(initIdx, initData);
        initIdx <= initIdx + 1;
        initDone <= (initIdx == maxBound);
    endrule

    method Action rdReq_infoRam__003__2 (Bit#(8) x_0) if(initDone);
        bram.rdReq(x_0);
    endmethod

    method Action wrReq_infoRam__003__2 (Struct47 x_0) if(initDone);
        bram.wrReq(x_0.addr, x_0.datain);
    endmethod

    method ActionValue#(Struct45) rdResp_infoRam__003__2 () if(initDone);
        bram.deqRdResp ();
        let data = bram.rdResp ();
        return data;
    endmethod


endmodule

interface Module102;
    method Action rdReq_infoRam__003__1 (Bit#(8) x_0);
    method Action wrReq_infoRam__003__1 (Struct47 x_0);
    method ActionValue#(Struct45) rdResp_infoRam__003__1 ();
endinterface

module mkModule102 (Module102);
    RWBramCore#(Bit#(8), Struct45) bram <- mkRWBramCore();
    Reg#(Bool) initDone <- mkReg(False);
    Reg#(Bit#(8)) initIdx <- mkReg(0);

    rule init (!initDone);
        let initData = Struct45 {tag: 51'h5, value: Struct10 {mesi_owned: False, mesi_status: 3'h1, mesi_dir_st: 3'h1, mesi_dir_sharers: 4'h0}};
        bram.wrReq(initIdx, initData);
        initIdx <= initIdx + 1;
        initDone <= (initIdx == maxBound);
    endrule

    method Action rdReq_infoRam__003__1 (Bit#(8) x_0) if(initDone);
        bram.rdReq(x_0);
    endmethod

    method Action wrReq_infoRam__003__1 (Struct47 x_0) if(initDone);
        bram.wrReq(x_0.addr, x_0.datain);
    endmethod

    method ActionValue#(Struct45) rdResp_infoRam__003__1 () if(initDone);
        bram.deqRdResp ();
        let data = bram.rdResp ();
        return data;
    endmethod


endmodule

interface Module103;
    method Action rdReq_infoRam__003__0 (Bit#(8) x_0);
    method Action wrReq_infoRam__003__0 (Struct47 x_0);
    method ActionValue#(Struct45) rdResp_infoRam__003__0 ();
endinterface

module mkModule103 (Module103);
    RWBramCore#(Bit#(8), Struct45) bram <- mkRWBramCore();
    Reg#(Bool) initDone <- mkReg(False);
    Reg#(Bit#(8)) initIdx <- mkReg(0);

    rule init (!initDone);
        let initData = Struct45 {tag: 51'h4, value: Struct10 {mesi_owned: False, mesi_status: 3'h1, mesi_dir_st: 3'h1, mesi_dir_sharers: 4'h0}};
        bram.wrReq(initIdx, initData);
        initIdx <= initIdx + 1;
        initDone <= (initIdx == maxBound);
    endrule

    method Action rdReq_infoRam__003__0 (Bit#(8) x_0) if(initDone);
        bram.rdReq(x_0);
    endmethod

    method Action wrReq_infoRam__003__0 (Struct47 x_0) if(initDone);
        bram.wrReq(x_0.addr, x_0.datain);
    endmethod

    method ActionValue#(Struct45) rdResp_infoRam__003__0 () if(initDone);
        bram.deqRdResp ();
        let data = bram.rdResp ();
        return data;
    endmethod


endmodule

interface Module104;
    method Action rdReq_dataRam__003 (Bit#(10) x_0);
    method Action wrReq_dataRam__003 (Struct49 x_0);
    method ActionValue#(Vector#(4, Bit#(64))) rdResp_dataRam__003 ();
endinterface

module mkModule104 (Module104);
    RWBramCore#(Bit#(10), Vector#(4, Bit#(64))) bram <- mkRWBramCore();
    Reg#(Bool) initDone <- mkReg(False);
    Reg#(Bit#(10)) initIdx <- mkReg(0);

    rule init (!initDone);
        let initData = vec(64'h0, 64'h0, 64'h0, 64'h0);
        bram.wrReq(initIdx, initData);
        initIdx <= initIdx + 1;
        initDone <= (initIdx == maxBound);
    endrule

    method Action rdReq_dataRam__003 (Bit#(10) x_0) if(initDone);
        bram.rdReq(x_0);
    endmethod

    method Action wrReq_dataRam__003 (Struct49 x_0) if(initDone);
        bram.wrReq(x_0.addr, x_0.datain);
    endmethod

    method ActionValue#(Vector#(4, Bit#(64))) rdResp_dataRam__003 ()
    if(initDone);
        bram.deqRdResp ();
        let data = bram.rdResp ();
        return data;
    endmethod


endmodule

interface Module105;
    method Action rdReq_repRam__003 (Bit#(8) x_0);
    method Action wrReq_repRam__003 (Struct50 x_0);
    method ActionValue#(Vector#(4, Bit#(8))) rdResp_repRam__003 ();
endinterface

module mkModule105 (Module105);
    RWBramCore#(Bit#(8), Vector#(4, Bit#(8))) bram <- mkRWBramCore();
    Reg#(Bool) initDone <- mkReg(False);
    Reg#(Bit#(8)) initIdx <- mkReg(0);

    rule init (!initDone);
        let initData = vec(8'h1, 8'h1, 8'h1, 8'h1);
        bram.wrReq(initIdx, initData);
        initIdx <= initIdx + 1;
        initDone <= (initIdx == maxBound);
    endrule

    method Action rdReq_repRam__003 (Bit#(8) x_0) if(initDone);
        bram.rdReq(x_0);
    endmethod

    method Action wrReq_repRam__003 (Struct50 x_0) if(initDone);
        bram.wrReq(x_0.addr, x_0.datain);
    endmethod

    method ActionValue#(Vector#(4, Bit#(8))) rdResp_repRam__003 ()
    if(initDone);
        bram.deqRdResp ();
        let data = bram.rdResp ();
        return data;
    endmethod


endmodule

interface Module106;
    method ActionValue#(Struct14) getMSHR_003 (Bit#(2) x_0);
    method ActionValue#(Struct1) getMSHRRq_003 (Bit#(2) x_0);
    method ActionValue#(Struct36) getPRqSlot_003 (Struct35 x_0);
    method ActionValue#(Struct36) getCRqSlot_003 (Struct35 x_0);
    method ActionValue#(Struct35) getWait_003 ();
    method Action registerUL_003 (Struct43 x_0);
    method Action canImm_003 (Bit#(64) x_0);
    method Action setULImm_003 (Struct1 x_0);
    method ActionValue#(Bit#(2)) getULReady_003 (Bit#(64) x_0);
    method Action startRelease_003 (Bit#(2) x_0);
    method Action releaseMSHR_003 (Bit#(2) x_0);
endinterface

module mkModule106
    (Module106);
    Reg#(Vector#(4, Struct14)) mshrs_003 <- mkReg(unpack(0));
    Reg#(Vector#(4, Bit#(64))) maddrs_003 <- mkReg(unpack(0));
    Reg#(Vector#(4, Bit#(3))) msts_003 <- mkReg(unpack(0));
    Reg#(Vector#(4, Struct51)) mnexts_003 <- mkReg(unpack(0));
    Reg#(Vector#(4, Struct1)) rqs_003 <- mkReg(unpack(0));

    // No rules in this module

    method ActionValue#(Struct14) getMSHR_003 (Bit#(2) x_0);
        let x_1 = (mshrs_003);
        return (x_1)[x_0];
    endmethod

    method ActionValue#(Struct1) getMSHRRq_003 (Bit#(2) x_0);
        let x_1 = (rqs_003);
        return (x_1)[x_0];
    endmethod

    method ActionValue#(Struct36) getPRqSlot_003 (Struct35 x_0);
        let x_1 = (mshrs_003);
        let x_2 = (maddrs_003);
        let x_3 = (msts_003);
        let x_4 = (mnexts_003);
        Struct51 x_5 = ((((x_3)[(Bit#(2))'(2'h0)]) == ((Bit#(3))'(3'h0)) ?
        (Struct51 {valid : (Bool)'(True), data : (Bit#(2))'(2'h0)}) :
        ((((x_3)[(Bit#(2))'(2'h1)]) == ((Bit#(3))'(3'h0)) ? (Struct51 {valid
        : (Bool)'(True), data : (Bit#(2))'(2'h1)}) : (Struct51 {valid :
        (Bool)'(False), data : unpack(0)})))));
        Bool x_6 = ((x_5).valid);
        Bit#(2) x_7 = ((x_5).data);
        Bit#(64) x_8 = (((x_0).r_msg).addr);
        Bool x_9 = ((((((x_3)[(Bit#(2))'(2'h0)]) == ((Bit#(3))'(3'h4))) ||
        (((x_3)[(Bit#(2))'(2'h0)]) == ((Bit#(3))'(3'h6)))) && (((!
        (((x_2)[(Bit#(2))'(2'h0)]) == (x_8))) &&
        ((((x_2)[(Bit#(2))'(2'h0)])[12:5]) == ((x_8)[12:5]))) ||
        (((x_2)[(Bit#(2))'(2'h0)]) == (x_8))) ? ((Bool)'(True)) :
        ((((((x_3)[(Bit#(2))'(2'h1)]) == ((Bit#(3))'(3'h4))) ||
        (((x_3)[(Bit#(2))'(2'h1)]) == ((Bit#(3))'(3'h6)))) && (((!
        (((x_2)[(Bit#(2))'(2'h1)]) == (x_8))) &&
        ((((x_2)[(Bit#(2))'(2'h1)])[12:5]) == ((x_8)[12:5]))) ||
        (((x_2)[(Bit#(2))'(2'h1)]) == (x_8))) ? ((Bool)'(True)) :
        ((((((x_3)[(Bit#(2))'(2'h2)]) == ((Bit#(3))'(3'h4))) ||
        (((x_3)[(Bit#(2))'(2'h2)]) == ((Bit#(3))'(3'h6)))) && (((!
        (((x_2)[(Bit#(2))'(2'h2)]) == (x_8))) &&
        ((((x_2)[(Bit#(2))'(2'h2)])[12:5]) == ((x_8)[12:5]))) ||
        (((x_2)[(Bit#(2))'(2'h2)]) == (x_8))) ? ((Bool)'(True)) :
        ((((((x_3)[(Bit#(2))'(2'h3)]) == ((Bit#(3))'(3'h4))) ||
        (((x_3)[(Bit#(2))'(2'h3)]) == ((Bit#(3))'(3'h6)))) && (((!
        (((x_2)[(Bit#(2))'(2'h3)]) == (x_8))) &&
        ((((x_2)[(Bit#(2))'(2'h3)])[12:5]) == ((x_8)[12:5]))) ||
        (((x_2)[(Bit#(2))'(2'h3)]) == (x_8))) ? ((Bool)'(True)) :
        ((Bool)'(False))))))))));
        Struct51 x_10 = ((((((x_3)[(Bit#(2))'(2'h0)]) == ((Bit#(3))'(3'h5)))
        && (! (((x_1)[(Bit#(2))'(2'h0)]).m_is_ul))) &&
        (((x_2)[(Bit#(2))'(2'h0)]) == (x_8)) ? (Struct51 {valid :
        (Bool)'(True), data : (Bit#(2))'(2'h0)}) :
        ((((((x_3)[(Bit#(2))'(2'h1)]) == ((Bit#(3))'(3'h5))) && (!
        (((x_1)[(Bit#(2))'(2'h1)]).m_is_ul))) && (((x_2)[(Bit#(2))'(2'h1)])
        == (x_8)) ? (Struct51 {valid : (Bool)'(True), data :
        (Bit#(2))'(2'h1)}) : ((((((x_3)[(Bit#(2))'(2'h2)]) ==
        ((Bit#(3))'(3'h5))) && (! (((x_1)[(Bit#(2))'(2'h2)]).m_is_ul))) &&
        (((x_2)[(Bit#(2))'(2'h2)]) == (x_8)) ? (Struct51 {valid :
        (Bool)'(True), data : (Bit#(2))'(2'h2)}) :
        ((((((x_3)[(Bit#(2))'(2'h3)]) == ((Bit#(3))'(3'h5))) && (!
        (((x_1)[(Bit#(2))'(2'h3)]).m_is_ul))) && (((x_2)[(Bit#(2))'(2'h3)])
        == (x_8)) ? (Struct51 {valid : (Bool)'(True), data :
        (Bit#(2))'(2'h3)}) : (Struct51 {valid : (Bool)'(False), data :
        unpack(0)})))))))));
        Bool x_11 = ((x_10).valid);
        Struct36 x_12 = (Struct36 {s_has_slot : (x_6) && (! (x_9)),
        s_conflict : x_11, s_id :
        x_7});
        if ((x_6) && (! (x_9))) begin
            mshrs_003 <= update (x_1, x_7, Struct14 {m_is_ul : unpack(0),
            m_qidx : (x_0).r_msg_from, m_rsb : unpack(0), m_dl_rss_from :
            unpack(0), m_dl_rss_recv : unpack(0)});
            maddrs_003 <= update (x_2, x_7, ((x_0).r_msg).addr);
            msts_003 <= update (x_3, x_7, (x_11 ? ((Bit#(3))'(3'h1)) :
            ((Bit#(3))'(3'h4))));
            let x_13 = (rqs_003);
            rqs_003 <= update (x_13, x_7,
            (x_0).r_msg);
            if (x_11) begin
                Bit#(2) x_14 = ((((! (((x_3)[(Bit#(2))'(2'h0)]) ==
                ((Bit#(3))'(3'h0)))) && (!
                (((x_4)[(Bit#(2))'(2'h0)]).valid))) &&
                (((x_2)[(Bit#(2))'(2'h0)]) == (x_8)) ? ((Bit#(2))'(2'h0)) :
                ((((! (((x_3)[(Bit#(2))'(2'h1)]) == ((Bit#(3))'(3'h0)))) &&
                (! (((x_4)[(Bit#(2))'(2'h1)]).valid))) &&
                (((x_2)[(Bit#(2))'(2'h1)]) == (x_8)) ? ((Bit#(2))'(2'h1)) :
                ((((! (((x_3)[(Bit#(2))'(2'h2)]) == ((Bit#(3))'(3'h0)))) &&
                (! (((x_4)[(Bit#(2))'(2'h2)]).valid))) &&
                (((x_2)[(Bit#(2))'(2'h2)]) == (x_8)) ? ((Bit#(2))'(2'h2)) :
                ((((! (((x_3)[(Bit#(2))'(2'h3)]) == ((Bit#(3))'(3'h0)))) &&
                (! (((x_4)[(Bit#(2))'(2'h3)]).valid))) &&
                (((x_2)[(Bit#(2))'(2'h3)]) == (x_8)) ? ((Bit#(2))'(2'h3)) :
                (unpack(0))))))))));
                Struct51 x_15 = ((x_4)[x_14]);
                mnexts_003 <= update (x_4, x_14, Struct51 {valid :
                (Bool)'(True), data : x_7});
            end else begin

            end
        end else begin

        end
        return x_12;
    endmethod

    method ActionValue#(Struct36) getCRqSlot_003 (Struct35 x_0);
        let x_1 = (mshrs_003);
        let x_2 = (maddrs_003);
        let x_3 = (msts_003);
        let x_4 = (mnexts_003);
        Struct51 x_5 = ((((x_3)[(Bit#(2))'(2'h2)]) == ((Bit#(3))'(3'h0)) ?
        (Struct51 {valid : (Bool)'(True), data : (Bit#(2))'(2'h2)}) :
        ((((x_3)[(Bit#(2))'(2'h3)]) == ((Bit#(3))'(3'h0)) ? (Struct51 {valid
        : (Bool)'(True), data : (Bit#(2))'(2'h3)}) : (Struct51 {valid :
        (Bool)'(False), data : unpack(0)})))));
        Bool x_6 = ((x_5).valid);
        Bit#(2) x_7 = ((x_5).data);
        Bit#(64) x_8 = (((x_0).r_msg).addr);
        Bool x_9 = ((((((x_3)[(Bit#(2))'(2'h0)]) == ((Bit#(3))'(3'h4))) ||
        (((x_3)[(Bit#(2))'(2'h0)]) == ((Bit#(3))'(3'h6)))) && ((!
        (((x_2)[(Bit#(2))'(2'h0)]) == (x_8))) &&
        ((((x_2)[(Bit#(2))'(2'h0)])[12:5]) == ((x_8)[12:5]))) ?
        ((Bool)'(True)) : ((((((x_3)[(Bit#(2))'(2'h1)]) ==
        ((Bit#(3))'(3'h4))) || (((x_3)[(Bit#(2))'(2'h1)]) ==
        ((Bit#(3))'(3'h6)))) && ((! (((x_2)[(Bit#(2))'(2'h1)]) == (x_8))) &&
        ((((x_2)[(Bit#(2))'(2'h1)])[12:5]) == ((x_8)[12:5]))) ?
        ((Bool)'(True)) : ((((((x_3)[(Bit#(2))'(2'h2)]) ==
        ((Bit#(3))'(3'h4))) || (((x_3)[(Bit#(2))'(2'h2)]) ==
        ((Bit#(3))'(3'h6)))) && ((! (((x_2)[(Bit#(2))'(2'h2)]) == (x_8))) &&
        ((((x_2)[(Bit#(2))'(2'h2)])[12:5]) == ((x_8)[12:5]))) ?
        ((Bool)'(True)) : ((((((x_3)[(Bit#(2))'(2'h3)]) ==
        ((Bit#(3))'(3'h4))) || (((x_3)[(Bit#(2))'(2'h3)]) ==
        ((Bit#(3))'(3'h6)))) && ((! (((x_2)[(Bit#(2))'(2'h3)]) == (x_8))) &&
        ((((x_2)[(Bit#(2))'(2'h3)])[12:5]) == ((x_8)[12:5]))) ?
        ((Bool)'(True)) : ((Bool)'(False))))))))));
        Struct51 x_10 = (((((! (((x_3)[(Bit#(2))'(2'h2)]) ==
        ((Bit#(3))'(3'h0)))) && (! (((x_4)[(Bit#(2))'(2'h2)]).valid))) &&
        (((x_1)[(Bit#(2))'(2'h2)]).m_is_ul)) && (((x_2)[(Bit#(2))'(2'h2)]) ==
        (x_8)) ? (Struct51 {valid : (Bool)'(True), data : (Bit#(2))'(2'h2)})
        : (((((! (((x_3)[(Bit#(2))'(2'h3)]) == ((Bit#(3))'(3'h0)))) && (!
        (((x_4)[(Bit#(2))'(2'h3)]).valid))) &&
        (((x_1)[(Bit#(2))'(2'h3)]).m_is_ul)) && (((x_2)[(Bit#(2))'(2'h3)]) ==
        (x_8)) ? (Struct51 {valid : (Bool)'(True), data : (Bit#(2))'(2'h3)})
        : (Struct51 {valid : (Bool)'(False), data : unpack(0)})))));
        Struct51 x_11 = (((((! (((x_3)[(Bit#(2))'(2'h0)]) ==
        ((Bit#(3))'(3'h0)))) && (! (((x_4)[(Bit#(2))'(2'h0)]).valid))) && (!
        (((x_1)[(Bit#(2))'(2'h0)]).m_is_ul))) && (((x_2)[(Bit#(2))'(2'h0)])
        == (x_8)) ? (Struct51 {valid : (Bool)'(True), data :
        (Bit#(2))'(2'h0)}) : (((((! (((x_3)[(Bit#(2))'(2'h1)]) ==
        ((Bit#(3))'(3'h0)))) && (! (((x_4)[(Bit#(2))'(2'h1)]).valid))) && (!
        (((x_1)[(Bit#(2))'(2'h1)]).m_is_ul))) && (((x_2)[(Bit#(2))'(2'h1)])
        == (x_8)) ? (Struct51 {valid : (Bool)'(True), data :
        (Bit#(2))'(2'h1)}) : (((((! (((x_3)[(Bit#(2))'(2'h2)]) ==
        ((Bit#(3))'(3'h0)))) && (! (((x_4)[(Bit#(2))'(2'h2)]).valid))) && (!
        (((x_1)[(Bit#(2))'(2'h2)]).m_is_ul))) && (((x_2)[(Bit#(2))'(2'h2)])
        == (x_8)) ? (Struct51 {valid : (Bool)'(True), data :
        (Bit#(2))'(2'h2)}) : (((((! (((x_3)[(Bit#(2))'(2'h3)]) ==
        ((Bit#(3))'(3'h0)))) && (! (((x_4)[(Bit#(2))'(2'h3)]).valid))) && (!
        (((x_1)[(Bit#(2))'(2'h3)]).m_is_ul))) && (((x_2)[(Bit#(2))'(2'h3)])
        == (x_8)) ? (Struct51 {valid : (Bool)'(True), data :
        (Bit#(2))'(2'h3)}) : (Struct51 {valid : (Bool)'(False), data :
        unpack(0)})))))))));
        Bool x_12 = ((x_10).valid);
        Bool x_13 = ((x_11).valid);
        Bool x_14 = ((x_12) || (x_13));
        Struct36 x_15 = (Struct36 {s_has_slot : (x_6) && (! (x_9)),
        s_conflict : x_14, s_id :
        x_7});
        if ((x_6) && (! (x_9))) begin
            mshrs_003 <= update (x_1, x_7, Struct14 {m_is_ul : unpack(0),
            m_qidx : (x_0).r_msg_from, m_rsb : unpack(0), m_dl_rss_from :
            unpack(0), m_dl_rss_recv : unpack(0)});
            maddrs_003 <= update (x_2, x_7, ((x_0).r_msg).addr);
            msts_003 <= update (x_3, x_7, (x_14 ? ((Bit#(3))'(3'h1)) :
            ((Bit#(3))'(3'h4))));
            let x_16 = (rqs_003);
            rqs_003 <= update (x_16, x_7,
            (x_0).r_msg);
            if (x_14) begin
                Bit#(2) x_17 = ((x_12 ? ((x_10).data) :
                ((x_11).data)));
                Struct51 x_18 = ((x_4)[x_17]);
                mnexts_003 <= update (x_4, x_17, Struct51 {valid :
                (Bool)'(True), data : x_7});
            end else begin

            end
        end else begin

        end
        return x_15;
    endmethod

    method ActionValue#(Struct35) getWait_003 ();
        let x_1 = (mshrs_003);
        let x_2 = (maddrs_003);
        let x_3 = (msts_003);
        let x_4 = (rqs_003);
        Struct51 x_5 = ((((x_3)[(Bit#(2))'(2'h0)]) == ((Bit#(3))'(3'h2)) ?
        (Struct51 {valid : (Bool)'(True), data : (Bit#(2))'(2'h0)}) :
        ((((x_3)[(Bit#(2))'(2'h1)]) == ((Bit#(3))'(3'h2)) ? (Struct51 {valid
        : (Bool)'(True), data : (Bit#(2))'(2'h1)}) :
        ((((x_3)[(Bit#(2))'(2'h2)]) == ((Bit#(3))'(3'h2)) ? (Struct51 {valid
        : (Bool)'(True), data : (Bit#(2))'(2'h2)}) :
        ((((x_3)[(Bit#(2))'(2'h3)]) == ((Bit#(3))'(3'h2)) ? (Struct51 {valid
        : (Bool)'(True), data : (Bit#(2))'(2'h3)}) : (Struct51 {valid :
        (Bool)'(False), data : unpack(0)})))))))));
        when ((x_5).valid, noAction);
        Bit#(2) x_6 = ((x_5).data);
        Struct14 x_7 = ((x_1)[x_6]);
        Bit#(64) x_8 = ((x_2)[x_6]);
        Struct1 x_9 = ((x_4)[x_6]);
        Bool x_10 = ((((! (((x_3)[(Bit#(2))'(2'h0)]) < ((Bit#(3))'(3'h4))))
        && (((x_2)[(Bit#(2))'(2'h0)]) == (x_8))) ||
        (((((x_3)[(Bit#(2))'(2'h0)]) == ((Bit#(3))'(3'h4))) ||
        (((x_3)[(Bit#(2))'(2'h0)]) == ((Bit#(3))'(3'h6)))) && ((!
        (((x_2)[(Bit#(2))'(2'h0)]) == (x_8))) &&
        ((((x_2)[(Bit#(2))'(2'h0)])[12:5]) == ((x_8)[12:5])))) ?
        ((Bool)'(True)) : ((((! (((x_3)[(Bit#(2))'(2'h1)]) <
        ((Bit#(3))'(3'h4)))) && (((x_2)[(Bit#(2))'(2'h1)]) == (x_8))) ||
        (((((x_3)[(Bit#(2))'(2'h1)]) == ((Bit#(3))'(3'h4))) ||
        (((x_3)[(Bit#(2))'(2'h1)]) == ((Bit#(3))'(3'h6)))) && ((!
        (((x_2)[(Bit#(2))'(2'h1)]) == (x_8))) &&
        ((((x_2)[(Bit#(2))'(2'h1)])[12:5]) == ((x_8)[12:5])))) ?
        ((Bool)'(True)) : ((((! (((x_3)[(Bit#(2))'(2'h2)]) <
        ((Bit#(3))'(3'h4)))) && (((x_2)[(Bit#(2))'(2'h2)]) == (x_8))) ||
        (((((x_3)[(Bit#(2))'(2'h2)]) == ((Bit#(3))'(3'h4))) ||
        (((x_3)[(Bit#(2))'(2'h2)]) == ((Bit#(3))'(3'h6)))) && ((!
        (((x_2)[(Bit#(2))'(2'h2)]) == (x_8))) &&
        ((((x_2)[(Bit#(2))'(2'h2)])[12:5]) == ((x_8)[12:5])))) ?
        ((Bool)'(True)) : ((((! (((x_3)[(Bit#(2))'(2'h3)]) <
        ((Bit#(3))'(3'h4)))) && (((x_2)[(Bit#(2))'(2'h3)]) == (x_8))) ||
        (((((x_3)[(Bit#(2))'(2'h3)]) == ((Bit#(3))'(3'h4))) ||
        (((x_3)[(Bit#(2))'(2'h3)]) == ((Bit#(3))'(3'h6)))) && ((!
        (((x_2)[(Bit#(2))'(2'h3)]) == (x_8))) &&
        ((((x_2)[(Bit#(2))'(2'h3)])[12:5]) == ((x_8)[12:5])))) ?
        ((Bool)'(True)) : ((Bool)'(False))))))))));
        when (! (x_10), noAction);
        msts_003 <= update (x_3, x_6, (Bit#(3))'(3'h4));
        Struct35 x_11 = (Struct35 {r_id : x_6, r_msg : x_9, r_msg_from :
        (x_7).m_qidx});
        return x_11;
    endmethod

    method Action registerUL_003 (Struct43 x_0);
        let x_1 = (mshrs_003);
        let x_2 = (msts_003);
        Bit#(2) x_3 = ((x_0).r_id);
        mshrs_003 <= update (x_1, x_3, Struct14 {m_is_ul : (Bool)'(True),
        m_qidx : {((Bit#(2))'(2'h2)),((x_0).r_ul_rsbTo)}, m_rsb :
        (x_0).r_ul_rsb, m_dl_rss_from : unpack(0), m_dl_rss_recv :
        unpack(0)});
        msts_003 <= update (x_2, x_3, (Bit#(3))'(3'h5));
    endmethod

    method Action canImm_003 (Bit#(64) x_0);
        let x_1 = (maddrs_003);
        let x_2 = (msts_003);
        let x_3 = (mnexts_003);
        Struct51 x_4 = ((((x_2)[(Bit#(2))'(2'h2)]) == ((Bit#(3))'(3'h0)) ?
        (Struct51 {valid : (Bool)'(True), data : (Bit#(2))'(2'h2)}) :
        ((((x_2)[(Bit#(2))'(2'h3)]) == ((Bit#(3))'(3'h0)) ? (Struct51 {valid
        : (Bool)'(True), data : (Bit#(2))'(2'h3)}) : (Struct51 {valid :
        (Bool)'(False), data : unpack(0)})))));
        when ((x_4).valid, noAction);
        Struct51 x_5 = ((((! (((x_2)[(Bit#(2))'(2'h0)]) ==
        ((Bit#(3))'(3'h0)))) && (! (((x_3)[(Bit#(2))'(2'h0)]).valid))) &&
        (((x_1)[(Bit#(2))'(2'h0)]) == (x_0)) ? (Struct51 {valid :
        (Bool)'(True), data : (Bit#(2))'(2'h0)}) : ((((!
        (((x_2)[(Bit#(2))'(2'h1)]) == ((Bit#(3))'(3'h0)))) && (!
        (((x_3)[(Bit#(2))'(2'h1)]).valid))) && (((x_1)[(Bit#(2))'(2'h1)]) ==
        (x_0)) ? (Struct51 {valid : (Bool)'(True), data : (Bit#(2))'(2'h1)})
        : ((((! (((x_2)[(Bit#(2))'(2'h2)]) == ((Bit#(3))'(3'h0)))) && (!
        (((x_3)[(Bit#(2))'(2'h2)]).valid))) && (((x_1)[(Bit#(2))'(2'h2)]) ==
        (x_0)) ? (Struct51 {valid : (Bool)'(True), data : (Bit#(2))'(2'h2)})
        : ((((! (((x_2)[(Bit#(2))'(2'h3)]) == ((Bit#(3))'(3'h0)))) && (!
        (((x_3)[(Bit#(2))'(2'h3)]).valid))) && (((x_1)[(Bit#(2))'(2'h3)]) ==
        (x_0)) ? (Struct51 {valid : (Bool)'(True), data : (Bit#(2))'(2'h3)})
        : (Struct51 {valid : (Bool)'(False), data : unpack(0)})))))))));
        when (! ((x_5).valid), noAction);
    endmethod

    method Action setULImm_003 (Struct1 x_0);
        let x_1 = (mshrs_003);
        let x_2 = (maddrs_003);
        let x_3 = (msts_003);
        let x_4 = (rqs_003);
        Struct51 x_5 = ((((x_3)[(Bit#(2))'(2'h2)]) == ((Bit#(3))'(3'h0)) ?
        (Struct51 {valid : (Bool)'(True), data : (Bit#(2))'(2'h2)}) :
        ((((x_3)[(Bit#(2))'(2'h3)]) == ((Bit#(3))'(3'h0)) ? (Struct51 {valid
        : (Bool)'(True), data : (Bit#(2))'(2'h3)}) : (Struct51 {valid :
        (Bool)'(False), data : unpack(0)})))));
        when ((x_5).valid, noAction);
        Bit#(2) x_6 = ((x_5).data);
        Bit#(64) x_7 = ((x_0).addr);
        Struct51 x_8 = (((! (((x_3)[(Bit#(2))'(2'h0)]) ==
        ((Bit#(3))'(3'h0)))) && (((x_2)[(Bit#(2))'(2'h0)]) == (x_7)) ?
        (Struct51 {valid : (Bool)'(True), data : (Bit#(2))'(2'h0)}) : (((!
        (((x_3)[(Bit#(2))'(2'h1)]) == ((Bit#(3))'(3'h0)))) &&
        (((x_2)[(Bit#(2))'(2'h1)]) == (x_7)) ? (Struct51 {valid :
        (Bool)'(True), data : (Bit#(2))'(2'h1)}) : (((!
        (((x_3)[(Bit#(2))'(2'h2)]) == ((Bit#(3))'(3'h0)))) &&
        (((x_2)[(Bit#(2))'(2'h2)]) == (x_7)) ? (Struct51 {valid :
        (Bool)'(True), data : (Bit#(2))'(2'h2)}) : (((!
        (((x_3)[(Bit#(2))'(2'h3)]) == ((Bit#(3))'(3'h0)))) &&
        (((x_2)[(Bit#(2))'(2'h3)]) == (x_7)) ? (Struct51 {valid :
        (Bool)'(True), data : (Bit#(2))'(2'h3)}) : (Struct51 {valid :
        (Bool)'(False), data : unpack(0)})))))))));
        when (! ((x_8).valid), noAction);
        mshrs_003 <= update (x_1, x_6, Struct14 {m_is_ul : (Bool)'(True),
        m_qidx : unpack(0), m_rsb : (Bool)'(False), m_dl_rss_from :
        unpack(0), m_dl_rss_recv : unpack(0)});
        maddrs_003 <= update (x_2, x_6, (x_0).addr);
        msts_003 <= update (x_3, x_6, (Bit#(3))'(3'h5));
        rqs_003 <= update (x_4, x_6, x_0);
    endmethod

    method ActionValue#(Bit#(2)) getULReady_003 (Bit#(64) x_0);
        let x_1 = (mshrs_003);
        let x_2 = (maddrs_003);
        let x_3 = (msts_003);
        Bool x_4 = (((((((x_3)[(Bit#(2))'(2'h0)]) == ((Bit#(3))'(3'h4))) ||
        (((x_3)[(Bit#(2))'(2'h0)]) == ((Bit#(3))'(3'h6)))) && ((!
        (((x_2)[(Bit#(2))'(2'h0)]) == (x_0))) &&
        ((((x_2)[(Bit#(2))'(2'h0)])[12:5]) == ((x_0)[12:5])))) || (((!
        (((x_3)[(Bit#(2))'(2'h0)]) < ((Bit#(3))'(3'h4)))) && (!
        (((x_1)[(Bit#(2))'(2'h0)]).m_is_ul))) && (((x_2)[(Bit#(2))'(2'h0)])
        == (x_0))) ? ((Bool)'(True)) : (((((((x_3)[(Bit#(2))'(2'h1)]) ==
        ((Bit#(3))'(3'h4))) || (((x_3)[(Bit#(2))'(2'h1)]) ==
        ((Bit#(3))'(3'h6)))) && ((! (((x_2)[(Bit#(2))'(2'h1)]) == (x_0))) &&
        ((((x_2)[(Bit#(2))'(2'h1)])[12:5]) == ((x_0)[12:5])))) || (((!
        (((x_3)[(Bit#(2))'(2'h1)]) < ((Bit#(3))'(3'h4)))) && (!
        (((x_1)[(Bit#(2))'(2'h1)]).m_is_ul))) && (((x_2)[(Bit#(2))'(2'h1)])
        == (x_0))) ? ((Bool)'(True)) : (((((((x_3)[(Bit#(2))'(2'h2)]) ==
        ((Bit#(3))'(3'h4))) || (((x_3)[(Bit#(2))'(2'h2)]) ==
        ((Bit#(3))'(3'h6)))) && ((! (((x_2)[(Bit#(2))'(2'h2)]) == (x_0))) &&
        ((((x_2)[(Bit#(2))'(2'h2)])[12:5]) == ((x_0)[12:5])))) || (((!
        (((x_3)[(Bit#(2))'(2'h2)]) < ((Bit#(3))'(3'h4)))) && (!
        (((x_1)[(Bit#(2))'(2'h2)]).m_is_ul))) && (((x_2)[(Bit#(2))'(2'h2)])
        == (x_0))) ? ((Bool)'(True)) : (((((((x_3)[(Bit#(2))'(2'h3)]) ==
        ((Bit#(3))'(3'h4))) || (((x_3)[(Bit#(2))'(2'h3)]) ==
        ((Bit#(3))'(3'h6)))) && ((! (((x_2)[(Bit#(2))'(2'h3)]) == (x_0))) &&
        ((((x_2)[(Bit#(2))'(2'h3)])[12:5]) == ((x_0)[12:5])))) || (((!
        (((x_3)[(Bit#(2))'(2'h3)]) < ((Bit#(3))'(3'h4)))) && (!
        (((x_1)[(Bit#(2))'(2'h3)]).m_is_ul))) && (((x_2)[(Bit#(2))'(2'h3)])
        == (x_0))) ? ((Bool)'(True)) : ((Bool)'(False))))))))));
        when (! (x_4), noAction);
        Struct51 x_5 = ((((((x_3)[(Bit#(2))'(2'h2)]) == ((Bit#(3))'(3'h5)))
        && (((x_1)[(Bit#(2))'(2'h2)]).m_is_ul)) && (((x_2)[(Bit#(2))'(2'h2)])
        == (x_0)) ? (Struct51 {valid : (Bool)'(True), data :
        (Bit#(2))'(2'h2)}) : ((((((x_3)[(Bit#(2))'(2'h3)]) ==
        ((Bit#(3))'(3'h5))) && (((x_1)[(Bit#(2))'(2'h3)]).m_is_ul)) &&
        (((x_2)[(Bit#(2))'(2'h3)]) == (x_0)) ? (Struct51 {valid :
        (Bool)'(True), data : (Bit#(2))'(2'h3)}) : (Struct51 {valid :
        (Bool)'(False), data : unpack(0)})))));
        when ((x_5).valid, noAction);
        Bit#(2) x_6 = ((x_5).data);
        return x_6;
    endmethod

    method Action startRelease_003 (Bit#(2) x_0);
        let x_1 = (msts_003);
        msts_003 <= update (x_1, x_0, (Bit#(3))'(3'h6));
    endmethod

    method Action releaseMSHR_003 (Bit#(2) x_0);
        let x_1 = (mshrs_003);
        let x_2 = (msts_003);
        let x_3 = (mnexts_003);
        mshrs_003 <= update (x_1, x_0, unpack(0));
        mnexts_003 <= update (x_3, x_0, unpack(0));
        Vector#(4, Bit#(3)) x_4 = (update (x_2, x_0, unpack(0)));
        Struct51 x_5 =
        ((x_3)[x_0]);
        let x_8 = ?;
        if ((x_5).valid) begin
            Bit#(2) x_6 = ((x_5).data);
            Vector#(4, Bit#(3)) x_7 = (update (x_4, x_6,
            (Bit#(3))'(3'h2)));
            x_8 = x_7;
        end else begin
            x_8 = x_4;
        end
        msts_003 <= x_8;
    endmethod
endmodule

interface Module107;

endinterface

module mkModule107#(function ActionValue#(Struct1) deq_fifo0030(),
    function ActionValue#(Struct1) deq_fifo0020(),
    function ActionValue#(Struct1) deq_fifo0010(),
    function Action enq_fifoCRqInput_00(Struct2 _),
    function ActionValue#(Struct1) deq_fifo0000())
    (Module107);
    Reg#(Bit#(2)) rr_cRq4_00 <- mkReg(unpack(0));

    rule inc_rr_cRq4_00;
        let x_0 = (rr_cRq4_00);
        rr_cRq4_00 <= (x_0) + ((Bit#(2))'(2'h1));
    endrule

    rule accept0_cRq4_00;
        let x_0 = (rr_cRq4_00);
        when ((x_0) == ((Bit#(2))'(2'h0)), noAction);
        let x_1 <- deq_fifo0000();
        Struct2 x_2 = (Struct2 {in_msg : x_1, in_msg_from :
        {((Bit#(2))'(2'h0)),((Bit#(2))'(2'h0))}});
        let x_3 <- enq_fifoCRqInput_00(x_2);
    endrule

    rule accept1_cRq4_00;
        let x_0 = (rr_cRq4_00);
        when ((x_0) == ((Bit#(2))'(2'h1)), noAction);
        let x_1 <- deq_fifo0010();
        Struct2 x_2 = (Struct2 {in_msg : x_1, in_msg_from :
        {((Bit#(2))'(2'h0)),((Bit#(2))'(2'h1))}});
        let x_3 <- enq_fifoCRqInput_00(x_2);
    endrule

    rule accept2_cRq4_00;
        let x_0 = (rr_cRq4_00);
        when ((x_0) == ((Bit#(2))'(2'h2)), noAction);
        let x_1 <- deq_fifo0020();
        Struct2 x_2 = (Struct2 {in_msg : x_1, in_msg_from :
        {((Bit#(2))'(2'h0)),((Bit#(2))'(2'h2))}});
        let x_3 <- enq_fifoCRqInput_00(x_2);
    endrule

    rule accept3_cRq4_00;
        let x_0 = (rr_cRq4_00);
        when ((x_0) == ((Bit#(2))'(2'h3)), noAction);
        let x_1 <- deq_fifo0030();
        Struct2 x_2 = (Struct2 {in_msg : x_1, in_msg_from :
        {((Bit#(2))'(2'h0)),((Bit#(2))'(2'h3))}});
        let x_3 <- enq_fifoCRqInput_00(x_2);
    endrule

    // No methods in this module
endmodule

interface Module108;

endinterface

module mkModule108#(function ActionValue#(Struct1) deq_fifo0031(),
    function ActionValue#(Struct1) deq_fifo0021(),
    function ActionValue#(Struct1) deq_fifo0011(),
    function Action enq_fifoCRsInput_00(Struct2 _),
    function ActionValue#(Struct1) deq_fifo0001())
    (Module108);
    Reg#(Bit#(2)) rr_cRs4_00 <- mkReg(unpack(0));

    rule inc_rr_cRs4_00;
        let x_0 = (rr_cRs4_00);
        rr_cRs4_00 <= (x_0) + ((Bit#(2))'(2'h1));
    endrule

    rule accept0_cRs4_00;
        let x_0 = (rr_cRs4_00);
        when ((x_0) == ((Bit#(2))'(2'h0)), noAction);
        let x_1 <- deq_fifo0001();
        Struct2 x_2 = (Struct2 {in_msg : x_1, in_msg_from :
        {((Bit#(2))'(2'h1)),((Bit#(2))'(2'h0))}});
        let x_3 <- enq_fifoCRsInput_00(x_2);
    endrule

    rule accept1_cRs4_00;
        let x_0 = (rr_cRs4_00);
        when ((x_0) == ((Bit#(2))'(2'h1)), noAction);
        let x_1 <- deq_fifo0011();
        Struct2 x_2 = (Struct2 {in_msg : x_1, in_msg_from :
        {((Bit#(2))'(2'h1)),((Bit#(2))'(2'h1))}});
        let x_3 <- enq_fifoCRsInput_00(x_2);
    endrule

    rule accept2_cRs4_00;
        let x_0 = (rr_cRs4_00);
        when ((x_0) == ((Bit#(2))'(2'h2)), noAction);
        let x_1 <- deq_fifo0021();
        Struct2 x_2 = (Struct2 {in_msg : x_1, in_msg_from :
        {((Bit#(2))'(2'h1)),((Bit#(2))'(2'h2))}});
        let x_3 <- enq_fifoCRsInput_00(x_2);
    endrule

    rule accept3_cRs4_00;
        let x_0 = (rr_cRs4_00);
        when ((x_0) == ((Bit#(2))'(2'h3)), noAction);
        let x_1 <- deq_fifo0031();
        Struct2 x_2 = (Struct2 {in_msg : x_1, in_msg_from :
        {((Bit#(2))'(2'h1)),((Bit#(2))'(2'h3))}});
        let x_3 <- enq_fifoCRsInput_00(x_2);
    endrule

    // No methods in this module
endmodule

interface Module109;

endinterface

module mkModule109#(function Action enq_fifoPInput_00(Struct2 _),
    function ActionValue#(Struct1) deq_fifo002())
    (Module109);

    rule parent_convert_00;
        let x_0 <- deq_fifo002();
        Struct2 x_1 = (Struct2 {in_msg : x_0, in_msg_from :
        {((Bit#(2))'(2'h2)),((Bit#(2))'(2'h0))}});
        let x_2 <- enq_fifoPInput_00(x_1);
    endrule

    // No methods in this module
endmodule

interface Module110;
    method Action makeEnq_parentChildren00 (Struct18 x_0);
    method Action broadcast_parentChildren00 (Struct21 x_0);
endinterface

module mkModule110#(function Action enq_fifo0002(Struct1 _),
    function Action enq_fifo0012(Struct1 _),
    function Action enq_fifo0022(Struct1 _),
    function Action enq_fifo0032(Struct1 _),
    function Action enq_fifo001(Struct1 _),
    function Action enq_fifo000(Struct1 _))
    (Module110);

    // No rules in this module

    method Action makeEnq_parentChildren00 (Struct18 x_0);
        if (((x_0).enq_type) == ((Bit#(2))'(2'h0))) begin
            let x_1 <- enq_fifo000((x_0).enq_msg);
        end else
            begin
            if (((x_0).enq_type) == ((Bit#(2))'(2'h1))) begin
                let x_2 <- enq_fifo001((x_0).enq_msg);
            end else begin
                Bit#(2) x_3 = ((x_0).enq_ch_idx);
                Struct1 x_4 =
                ((x_0).enq_msg);
                if ((x_3) == ((Bit#(2))'(2'h3))) begin
                    let x_5 <- enq_fifo0032(x_4);
                end else
                    begin
                    if ((x_3) == ((Bit#(2))'(2'h2))) begin
                        let x_6 <- enq_fifo0022(x_4);
                    end else
                        begin
                        if ((x_3) == ((Bit#(2))'(2'h1))) begin
                            let x_7 <- enq_fifo0012(x_4);
                        end else
                            begin
                            if ((x_3) == ((Bit#(2))'(2'h0))) begin
                                let x_8 <- enq_fifo0002(x_4);
                            end else begin

                            end
                        end
                    end
                end
            end
        end
    endmethod

    method Action broadcast_parentChildren00 (Struct21 x_0);
        Bit#(4) x_1 = ((x_0).cs_inds);
        Struct1 x_2 =
        ((x_0).cs_msg);
        if (((x_1) | (((Bit#(4))'(4'h1)) << ((Bit#(2))'(2'h3)))) == (x_1))
            begin
            let x_3 <- enq_fifo0032(x_2);
        end else begin

        end
        if (((x_1) | (((Bit#(4))'(4'h1)) << ((Bit#(2))'(2'h2)))) == (x_1))
            begin
            let x_5 <- enq_fifo0022(x_2);
        end else begin

        end
        if (((x_1) | (((Bit#(4))'(4'h1)) << ((Bit#(2))'(2'h1)))) == (x_1))
            begin
            let x_7 <- enq_fifo0012(x_2);
        end else begin

        end
        if (((x_1) | (((Bit#(4))'(4'h1)) << ((Bit#(2))'(2'h0)))) == (x_1))
            begin
            let x_9 <- enq_fifo0002(x_2);
        end else begin

        end
    endmethod
endmodule

interface Module111;
    method Action repGetRq__00 (Bit#(10) x_0);
    method ActionValue#(Vector#(16, Bit#(8))) repGetRs__00 ();
    method Action repAccess__00 (Struct30 x_0);
endinterface

module mkModule111#(function Action wrReq_repRam__00(Struct34 _),
    function ActionValue#(Vector#(16, Bit#(8))) rdResp_repRam__00(),
    function Action rdReq_repRam__00(Bit#(10) _))
    (Module111);

    // No rules in this module

    method Action repGetRq__00 (Bit#(10) x_0);
        let x_1 <- rdReq_repRam__00(x_0);
    endmethod

    method ActionValue#(Vector#(16, Bit#(8))) repGetRs__00 ();
        let x_1 <- rdResp_repRam__00();
        return x_1;
    endmethod

    method Action repAccess__00 (Struct30 x_0);
        Vector#(16, Bit#(8)) x_1 = ((x_0).acc_reps);
        Bit#(8) x_2 = (((x_1)[(Bit#(4))'(4'hf)]) +
        (((((x_1)[(Bit#(4))'(4'hf)]) == ((Bit#(8))'(8'h0))) ||
        (((x_1)[(Bit#(4))'(4'hf)]) == ((Bit#(8))'(8'hff))) ?
        ((Bit#(8))'(8'h0)) : ((Bit#(8))'(8'h1)))));
        Vector#(16, Bit#(8)) x_3 = (update (x_1, (Bit#(4))'(4'hf),
        x_2));
        Bit#(8) x_4 = (((x_3)[(Bit#(4))'(4'he)]) +
        (((((x_3)[(Bit#(4))'(4'he)]) == ((Bit#(8))'(8'h0))) ||
        (((x_3)[(Bit#(4))'(4'he)]) == ((Bit#(8))'(8'hff))) ?
        ((Bit#(8))'(8'h0)) : ((Bit#(8))'(8'h1)))));
        Vector#(16, Bit#(8)) x_5 = (update (x_3, (Bit#(4))'(4'he),
        x_4));
        Bit#(8) x_6 = (((x_5)[(Bit#(4))'(4'hd)]) +
        (((((x_5)[(Bit#(4))'(4'hd)]) == ((Bit#(8))'(8'h0))) ||
        (((x_5)[(Bit#(4))'(4'hd)]) == ((Bit#(8))'(8'hff))) ?
        ((Bit#(8))'(8'h0)) : ((Bit#(8))'(8'h1)))));
        Vector#(16, Bit#(8)) x_7 = (update (x_5, (Bit#(4))'(4'hd),
        x_6));
        Bit#(8) x_8 = (((x_7)[(Bit#(4))'(4'hc)]) +
        (((((x_7)[(Bit#(4))'(4'hc)]) == ((Bit#(8))'(8'h0))) ||
        (((x_7)[(Bit#(4))'(4'hc)]) == ((Bit#(8))'(8'hff))) ?
        ((Bit#(8))'(8'h0)) : ((Bit#(8))'(8'h1)))));
        Vector#(16, Bit#(8)) x_9 = (update (x_7, (Bit#(4))'(4'hc),
        x_8));
        Bit#(8) x_10 = (((x_9)[(Bit#(4))'(4'hb)]) +
        (((((x_9)[(Bit#(4))'(4'hb)]) == ((Bit#(8))'(8'h0))) ||
        (((x_9)[(Bit#(4))'(4'hb)]) == ((Bit#(8))'(8'hff))) ?
        ((Bit#(8))'(8'h0)) : ((Bit#(8))'(8'h1)))));
        Vector#(16, Bit#(8)) x_11 = (update (x_9, (Bit#(4))'(4'hb),
        x_10));
        Bit#(8) x_12 = (((x_11)[(Bit#(4))'(4'ha)]) +
        (((((x_11)[(Bit#(4))'(4'ha)]) == ((Bit#(8))'(8'h0))) ||
        (((x_11)[(Bit#(4))'(4'ha)]) == ((Bit#(8))'(8'hff))) ?
        ((Bit#(8))'(8'h0)) : ((Bit#(8))'(8'h1)))));
        Vector#(16, Bit#(8)) x_13 = (update (x_11, (Bit#(4))'(4'ha),
        x_12));
        Bit#(8) x_14 = (((x_13)[(Bit#(4))'(4'h9)]) +
        (((((x_13)[(Bit#(4))'(4'h9)]) == ((Bit#(8))'(8'h0))) ||
        (((x_13)[(Bit#(4))'(4'h9)]) == ((Bit#(8))'(8'hff))) ?
        ((Bit#(8))'(8'h0)) : ((Bit#(8))'(8'h1)))));
        Vector#(16, Bit#(8)) x_15 = (update (x_13, (Bit#(4))'(4'h9),
        x_14));
        Bit#(8) x_16 = (((x_15)[(Bit#(4))'(4'h8)]) +
        (((((x_15)[(Bit#(4))'(4'h8)]) == ((Bit#(8))'(8'h0))) ||
        (((x_15)[(Bit#(4))'(4'h8)]) == ((Bit#(8))'(8'hff))) ?
        ((Bit#(8))'(8'h0)) : ((Bit#(8))'(8'h1)))));
        Vector#(16, Bit#(8)) x_17 = (update (x_15, (Bit#(4))'(4'h8),
        x_16));
        Bit#(8) x_18 = (((x_17)[(Bit#(4))'(4'h7)]) +
        (((((x_17)[(Bit#(4))'(4'h7)]) == ((Bit#(8))'(8'h0))) ||
        (((x_17)[(Bit#(4))'(4'h7)]) == ((Bit#(8))'(8'hff))) ?
        ((Bit#(8))'(8'h0)) : ((Bit#(8))'(8'h1)))));
        Vector#(16, Bit#(8)) x_19 = (update (x_17, (Bit#(4))'(4'h7),
        x_18));
        Bit#(8) x_20 = (((x_19)[(Bit#(4))'(4'h6)]) +
        (((((x_19)[(Bit#(4))'(4'h6)]) == ((Bit#(8))'(8'h0))) ||
        (((x_19)[(Bit#(4))'(4'h6)]) == ((Bit#(8))'(8'hff))) ?
        ((Bit#(8))'(8'h0)) : ((Bit#(8))'(8'h1)))));
        Vector#(16, Bit#(8)) x_21 = (update (x_19, (Bit#(4))'(4'h6),
        x_20));
        Bit#(8) x_22 = (((x_21)[(Bit#(4))'(4'h5)]) +
        (((((x_21)[(Bit#(4))'(4'h5)]) == ((Bit#(8))'(8'h0))) ||
        (((x_21)[(Bit#(4))'(4'h5)]) == ((Bit#(8))'(8'hff))) ?
        ((Bit#(8))'(8'h0)) : ((Bit#(8))'(8'h1)))));
        Vector#(16, Bit#(8)) x_23 = (update (x_21, (Bit#(4))'(4'h5),
        x_22));
        Bit#(8) x_24 = (((x_23)[(Bit#(4))'(4'h4)]) +
        (((((x_23)[(Bit#(4))'(4'h4)]) == ((Bit#(8))'(8'h0))) ||
        (((x_23)[(Bit#(4))'(4'h4)]) == ((Bit#(8))'(8'hff))) ?
        ((Bit#(8))'(8'h0)) : ((Bit#(8))'(8'h1)))));
        Vector#(16, Bit#(8)) x_25 = (update (x_23, (Bit#(4))'(4'h4),
        x_24));
        Bit#(8) x_26 = (((x_25)[(Bit#(4))'(4'h3)]) +
        (((((x_25)[(Bit#(4))'(4'h3)]) == ((Bit#(8))'(8'h0))) ||
        (((x_25)[(Bit#(4))'(4'h3)]) == ((Bit#(8))'(8'hff))) ?
        ((Bit#(8))'(8'h0)) : ((Bit#(8))'(8'h1)))));
        Vector#(16, Bit#(8)) x_27 = (update (x_25, (Bit#(4))'(4'h3),
        x_26));
        Bit#(8) x_28 = (((x_27)[(Bit#(4))'(4'h2)]) +
        (((((x_27)[(Bit#(4))'(4'h2)]) == ((Bit#(8))'(8'h0))) ||
        (((x_27)[(Bit#(4))'(4'h2)]) == ((Bit#(8))'(8'hff))) ?
        ((Bit#(8))'(8'h0)) : ((Bit#(8))'(8'h1)))));
        Vector#(16, Bit#(8)) x_29 = (update (x_27, (Bit#(4))'(4'h2),
        x_28));
        Bit#(8) x_30 = (((x_29)[(Bit#(4))'(4'h1)]) +
        (((((x_29)[(Bit#(4))'(4'h1)]) == ((Bit#(8))'(8'h0))) ||
        (((x_29)[(Bit#(4))'(4'h1)]) == ((Bit#(8))'(8'hff))) ?
        ((Bit#(8))'(8'h0)) : ((Bit#(8))'(8'h1)))));
        Vector#(16, Bit#(8)) x_31 = (update (x_29, (Bit#(4))'(4'h1),
        x_30));
        Bit#(8) x_32 = (((x_31)[(Bit#(4))'(4'h0)]) +
        (((((x_31)[(Bit#(4))'(4'h0)]) == ((Bit#(8))'(8'h0))) ||
        (((x_31)[(Bit#(4))'(4'h0)]) == ((Bit#(8))'(8'hff))) ?
        ((Bit#(8))'(8'h0)) : ((Bit#(8))'(8'h1)))));
        Vector#(16, Bit#(8)) x_33 = (update (x_31, (Bit#(4))'(4'h0),
        x_32));
        let x_36 = ?;
        if (((x_0).acc_type) == ((Bit#(1))'(1'h0))) begin
            Vector#(16, Bit#(8)) x_34 = (update (x_33, (x_0).acc_way,
            (Bit#(8))'(8'h1)));
            x_36 = x_34;
        end else begin
            Vector#(16, Bit#(8)) x_35 = (update (x_33, (x_0).acc_way,
            (Bit#(8))'(8'h0)));
            x_36 = x_35;
        end
        Struct34 x_37 = (Struct34 {addr : (x_0).acc_index, datain :
        x_36});
        let x_38 <- wrReq_repRam__00(x_37);
    endmethod
endmodule

interface Module112;

endinterface

module mkModule112#(function Action enq_fifoCRqInput_000(Struct2 _),
    function ActionValue#(Struct1) deq_fifo00000())
    (Module112);

    rule child_convert_000;
        let x_0 <- deq_fifo00000();
        Struct2 x_1 = (Struct2 {in_msg : x_0, in_msg_from :
        {((Bit#(2))'(2'h0)),((Bit#(2))'(2'h0))}});
        let x_2 <- enq_fifoCRqInput_000(x_1);
    endrule

    // No methods in this module
endmodule

interface Module113;

endinterface

module mkModule113#(function Action enq_fifoPInput_000(Struct2 _),
    function ActionValue#(Struct1) deq_fifo0002())
    (Module113);

    rule parent_convert_000;
        let x_0 <- deq_fifo0002();
        Struct2 x_1 = (Struct2 {in_msg : x_0, in_msg_from :
        {((Bit#(2))'(2'h2)),((Bit#(2))'(2'h0))}});
        let x_2 <- enq_fifoPInput_000(x_1);
    endrule

    // No methods in this module
endmodule

interface Module114;
    method Action makeEnq_parentChildren000 (Struct18 x_0);
endinterface

module mkModule114#(function Action enq_fifo00002(Struct1 _),
    function Action enq_fifo0001(Struct1 _),
    function Action enq_fifo0000(Struct1 _))
    (Module114);

    // No rules in this module

    method Action makeEnq_parentChildren000 (Struct18 x_0);
        if (((x_0).enq_type) == ((Bit#(2))'(2'h0))) begin
            let x_1 <- enq_fifo0000((x_0).enq_msg);
        end else
            begin
            if (((x_0).enq_type) == ((Bit#(2))'(2'h1))) begin
                let x_2 <- enq_fifo0001((x_0).enq_msg);
            end else begin
                Struct1 x_3 = ((x_0).enq_msg);
                let x_4 <- enq_fifo00002(x_3);
            end
        end
    endmethod
endmodule

interface Module115;
    method Action repGetRq__000 (Bit#(8) x_0);
    method ActionValue#(Vector#(4, Bit#(8))) repGetRs__000 ();
    method Action repAccess__000 (Struct48 x_0);
endinterface

module mkModule115#(function Action wrReq_repRam__000(Struct50 _),
    function ActionValue#(Vector#(4, Bit#(8))) rdResp_repRam__000(),
    function Action rdReq_repRam__000(Bit#(8) _))
    (Module115);

    // No rules in this module

    method Action repGetRq__000 (Bit#(8) x_0);
        let x_1 <- rdReq_repRam__000(x_0);
    endmethod

    method ActionValue#(Vector#(4, Bit#(8))) repGetRs__000 ();
        let x_1 <- rdResp_repRam__000();
        return x_1;
    endmethod

    method Action repAccess__000 (Struct48 x_0);
        Vector#(4, Bit#(8)) x_1 = ((x_0).acc_reps);
        Bit#(8) x_2 = (((x_1)[(Bit#(2))'(2'h3)]) +
        (((((x_1)[(Bit#(2))'(2'h3)]) == ((Bit#(8))'(8'h0))) ||
        (((x_1)[(Bit#(2))'(2'h3)]) == ((Bit#(8))'(8'hff))) ?
        ((Bit#(8))'(8'h0)) : ((Bit#(8))'(8'h1)))));
        Vector#(4, Bit#(8)) x_3 = (update (x_1, (Bit#(2))'(2'h3),
        x_2));
        Bit#(8) x_4 = (((x_3)[(Bit#(2))'(2'h2)]) +
        (((((x_3)[(Bit#(2))'(2'h2)]) == ((Bit#(8))'(8'h0))) ||
        (((x_3)[(Bit#(2))'(2'h2)]) == ((Bit#(8))'(8'hff))) ?
        ((Bit#(8))'(8'h0)) : ((Bit#(8))'(8'h1)))));
        Vector#(4, Bit#(8)) x_5 = (update (x_3, (Bit#(2))'(2'h2),
        x_4));
        Bit#(8) x_6 = (((x_5)[(Bit#(2))'(2'h1)]) +
        (((((x_5)[(Bit#(2))'(2'h1)]) == ((Bit#(8))'(8'h0))) ||
        (((x_5)[(Bit#(2))'(2'h1)]) == ((Bit#(8))'(8'hff))) ?
        ((Bit#(8))'(8'h0)) : ((Bit#(8))'(8'h1)))));
        Vector#(4, Bit#(8)) x_7 = (update (x_5, (Bit#(2))'(2'h1),
        x_6));
        Bit#(8) x_8 = (((x_7)[(Bit#(2))'(2'h0)]) +
        (((((x_7)[(Bit#(2))'(2'h0)]) == ((Bit#(8))'(8'h0))) ||
        (((x_7)[(Bit#(2))'(2'h0)]) == ((Bit#(8))'(8'hff))) ?
        ((Bit#(8))'(8'h0)) : ((Bit#(8))'(8'h1)))));
        Vector#(4, Bit#(8)) x_9 = (update (x_7, (Bit#(2))'(2'h0),
        x_8));
        let x_12 = ?;
        if (((x_0).acc_type) == ((Bit#(1))'(1'h0))) begin
            Vector#(4, Bit#(8)) x_10 = (update (x_9, (x_0).acc_way,
            (Bit#(8))'(8'h1)));
            x_12 = x_10;
        end else begin
            Vector#(4, Bit#(8)) x_11 = (update (x_9, (x_0).acc_way,
            (Bit#(8))'(8'h0)));
            x_12 = x_11;
        end
        Struct50 x_13 = (Struct50 {addr : (x_0).acc_index, datain :
        x_12});
        let x_14 <- wrReq_repRam__000(x_13);
    endmethod
endmodule

interface Module116;

endinterface

module mkModule116#(function Action enq_fifoCRqInput_001(Struct2 _),
    function ActionValue#(Struct1) deq_fifo00100())
    (Module116);

    rule child_convert_001;
        let x_0 <- deq_fifo00100();
        Struct2 x_1 = (Struct2 {in_msg : x_0, in_msg_from :
        {((Bit#(2))'(2'h0)),((Bit#(2))'(2'h0))}});
        let x_2 <- enq_fifoCRqInput_001(x_1);
    endrule

    // No methods in this module
endmodule

interface Module117;

endinterface

module mkModule117#(function Action enq_fifoPInput_001(Struct2 _),
    function ActionValue#(Struct1) deq_fifo0012())
    (Module117);

    rule parent_convert_001;
        let x_0 <- deq_fifo0012();
        Struct2 x_1 = (Struct2 {in_msg : x_0, in_msg_from :
        {((Bit#(2))'(2'h2)),((Bit#(2))'(2'h1))}});
        let x_2 <- enq_fifoPInput_001(x_1);
    endrule

    // No methods in this module
endmodule

interface Module118;
    method Action makeEnq_parentChildren001 (Struct18 x_0);
endinterface

module mkModule118#(function Action enq_fifo00102(Struct1 _),
    function Action enq_fifo0011(Struct1 _),
    function Action enq_fifo0010(Struct1 _))
    (Module118);

    // No rules in this module

    method Action makeEnq_parentChildren001 (Struct18 x_0);
        if (((x_0).enq_type) == ((Bit#(2))'(2'h0))) begin
            let x_1 <- enq_fifo0010((x_0).enq_msg);
        end else
            begin
            if (((x_0).enq_type) == ((Bit#(2))'(2'h1))) begin
                let x_2 <- enq_fifo0011((x_0).enq_msg);
            end else begin
                Struct1 x_3 = ((x_0).enq_msg);
                let x_4 <- enq_fifo00102(x_3);
            end
        end
    endmethod
endmodule

interface Module119;
    method Action repGetRq__001 (Bit#(8) x_0);
    method ActionValue#(Vector#(4, Bit#(8))) repGetRs__001 ();
    method Action repAccess__001 (Struct48 x_0);
endinterface

module mkModule119#(function Action wrReq_repRam__001(Struct50 _),
    function ActionValue#(Vector#(4, Bit#(8))) rdResp_repRam__001(),
    function Action rdReq_repRam__001(Bit#(8) _))
    (Module119);

    // No rules in this module

    method Action repGetRq__001 (Bit#(8) x_0);
        let x_1 <- rdReq_repRam__001(x_0);
    endmethod

    method ActionValue#(Vector#(4, Bit#(8))) repGetRs__001 ();
        let x_1 <- rdResp_repRam__001();
        return x_1;
    endmethod

    method Action repAccess__001 (Struct48 x_0);
        Vector#(4, Bit#(8)) x_1 = ((x_0).acc_reps);
        Bit#(8) x_2 = (((x_1)[(Bit#(2))'(2'h3)]) +
        (((((x_1)[(Bit#(2))'(2'h3)]) == ((Bit#(8))'(8'h0))) ||
        (((x_1)[(Bit#(2))'(2'h3)]) == ((Bit#(8))'(8'hff))) ?
        ((Bit#(8))'(8'h0)) : ((Bit#(8))'(8'h1)))));
        Vector#(4, Bit#(8)) x_3 = (update (x_1, (Bit#(2))'(2'h3),
        x_2));
        Bit#(8) x_4 = (((x_3)[(Bit#(2))'(2'h2)]) +
        (((((x_3)[(Bit#(2))'(2'h2)]) == ((Bit#(8))'(8'h0))) ||
        (((x_3)[(Bit#(2))'(2'h2)]) == ((Bit#(8))'(8'hff))) ?
        ((Bit#(8))'(8'h0)) : ((Bit#(8))'(8'h1)))));
        Vector#(4, Bit#(8)) x_5 = (update (x_3, (Bit#(2))'(2'h2),
        x_4));
        Bit#(8) x_6 = (((x_5)[(Bit#(2))'(2'h1)]) +
        (((((x_5)[(Bit#(2))'(2'h1)]) == ((Bit#(8))'(8'h0))) ||
        (((x_5)[(Bit#(2))'(2'h1)]) == ((Bit#(8))'(8'hff))) ?
        ((Bit#(8))'(8'h0)) : ((Bit#(8))'(8'h1)))));
        Vector#(4, Bit#(8)) x_7 = (update (x_5, (Bit#(2))'(2'h1),
        x_6));
        Bit#(8) x_8 = (((x_7)[(Bit#(2))'(2'h0)]) +
        (((((x_7)[(Bit#(2))'(2'h0)]) == ((Bit#(8))'(8'h0))) ||
        (((x_7)[(Bit#(2))'(2'h0)]) == ((Bit#(8))'(8'hff))) ?
        ((Bit#(8))'(8'h0)) : ((Bit#(8))'(8'h1)))));
        Vector#(4, Bit#(8)) x_9 = (update (x_7, (Bit#(2))'(2'h0),
        x_8));
        let x_12 = ?;
        if (((x_0).acc_type) == ((Bit#(1))'(1'h0))) begin
            Vector#(4, Bit#(8)) x_10 = (update (x_9, (x_0).acc_way,
            (Bit#(8))'(8'h1)));
            x_12 = x_10;
        end else begin
            Vector#(4, Bit#(8)) x_11 = (update (x_9, (x_0).acc_way,
            (Bit#(8))'(8'h0)));
            x_12 = x_11;
        end
        Struct50 x_13 = (Struct50 {addr : (x_0).acc_index, datain :
        x_12});
        let x_14 <- wrReq_repRam__001(x_13);
    endmethod
endmodule

interface Module120;

endinterface

module mkModule120#(function Action enq_fifoCRqInput_002(Struct2 _),
    function ActionValue#(Struct1) deq_fifo00200())
    (Module120);

    rule child_convert_002;
        let x_0 <- deq_fifo00200();
        Struct2 x_1 = (Struct2 {in_msg : x_0, in_msg_from :
        {((Bit#(2))'(2'h0)),((Bit#(2))'(2'h0))}});
        let x_2 <- enq_fifoCRqInput_002(x_1);
    endrule

    // No methods in this module
endmodule

interface Module121;

endinterface

module mkModule121#(function Action enq_fifoPInput_002(Struct2 _),
    function ActionValue#(Struct1) deq_fifo0022())
    (Module121);

    rule parent_convert_002;
        let x_0 <- deq_fifo0022();
        Struct2 x_1 = (Struct2 {in_msg : x_0, in_msg_from :
        {((Bit#(2))'(2'h2)),((Bit#(2))'(2'h2))}});
        let x_2 <- enq_fifoPInput_002(x_1);
    endrule

    // No methods in this module
endmodule

interface Module122;
    method Action makeEnq_parentChildren002 (Struct18 x_0);
endinterface

module mkModule122#(function Action enq_fifo00202(Struct1 _),
    function Action enq_fifo0021(Struct1 _),
    function Action enq_fifo0020(Struct1 _))
    (Module122);

    // No rules in this module

    method Action makeEnq_parentChildren002 (Struct18 x_0);
        if (((x_0).enq_type) == ((Bit#(2))'(2'h0))) begin
            let x_1 <- enq_fifo0020((x_0).enq_msg);
        end else
            begin
            if (((x_0).enq_type) == ((Bit#(2))'(2'h1))) begin
                let x_2 <- enq_fifo0021((x_0).enq_msg);
            end else begin
                Struct1 x_3 = ((x_0).enq_msg);
                let x_4 <- enq_fifo00202(x_3);
            end
        end
    endmethod
endmodule

interface Module123;
    method Action repGetRq__002 (Bit#(8) x_0);
    method ActionValue#(Vector#(4, Bit#(8))) repGetRs__002 ();
    method Action repAccess__002 (Struct48 x_0);
endinterface

module mkModule123#(function Action wrReq_repRam__002(Struct50 _),
    function ActionValue#(Vector#(4, Bit#(8))) rdResp_repRam__002(),
    function Action rdReq_repRam__002(Bit#(8) _))
    (Module123);

    // No rules in this module

    method Action repGetRq__002 (Bit#(8) x_0);
        let x_1 <- rdReq_repRam__002(x_0);
    endmethod

    method ActionValue#(Vector#(4, Bit#(8))) repGetRs__002 ();
        let x_1 <- rdResp_repRam__002();
        return x_1;
    endmethod

    method Action repAccess__002 (Struct48 x_0);
        Vector#(4, Bit#(8)) x_1 = ((x_0).acc_reps);
        Bit#(8) x_2 = (((x_1)[(Bit#(2))'(2'h3)]) +
        (((((x_1)[(Bit#(2))'(2'h3)]) == ((Bit#(8))'(8'h0))) ||
        (((x_1)[(Bit#(2))'(2'h3)]) == ((Bit#(8))'(8'hff))) ?
        ((Bit#(8))'(8'h0)) : ((Bit#(8))'(8'h1)))));
        Vector#(4, Bit#(8)) x_3 = (update (x_1, (Bit#(2))'(2'h3),
        x_2));
        Bit#(8) x_4 = (((x_3)[(Bit#(2))'(2'h2)]) +
        (((((x_3)[(Bit#(2))'(2'h2)]) == ((Bit#(8))'(8'h0))) ||
        (((x_3)[(Bit#(2))'(2'h2)]) == ((Bit#(8))'(8'hff))) ?
        ((Bit#(8))'(8'h0)) : ((Bit#(8))'(8'h1)))));
        Vector#(4, Bit#(8)) x_5 = (update (x_3, (Bit#(2))'(2'h2),
        x_4));
        Bit#(8) x_6 = (((x_5)[(Bit#(2))'(2'h1)]) +
        (((((x_5)[(Bit#(2))'(2'h1)]) == ((Bit#(8))'(8'h0))) ||
        (((x_5)[(Bit#(2))'(2'h1)]) == ((Bit#(8))'(8'hff))) ?
        ((Bit#(8))'(8'h0)) : ((Bit#(8))'(8'h1)))));
        Vector#(4, Bit#(8)) x_7 = (update (x_5, (Bit#(2))'(2'h1),
        x_6));
        Bit#(8) x_8 = (((x_7)[(Bit#(2))'(2'h0)]) +
        (((((x_7)[(Bit#(2))'(2'h0)]) == ((Bit#(8))'(8'h0))) ||
        (((x_7)[(Bit#(2))'(2'h0)]) == ((Bit#(8))'(8'hff))) ?
        ((Bit#(8))'(8'h0)) : ((Bit#(8))'(8'h1)))));
        Vector#(4, Bit#(8)) x_9 = (update (x_7, (Bit#(2))'(2'h0),
        x_8));
        let x_12 = ?;
        if (((x_0).acc_type) == ((Bit#(1))'(1'h0))) begin
            Vector#(4, Bit#(8)) x_10 = (update (x_9, (x_0).acc_way,
            (Bit#(8))'(8'h1)));
            x_12 = x_10;
        end else begin
            Vector#(4, Bit#(8)) x_11 = (update (x_9, (x_0).acc_way,
            (Bit#(8))'(8'h0)));
            x_12 = x_11;
        end
        Struct50 x_13 = (Struct50 {addr : (x_0).acc_index, datain :
        x_12});
        let x_14 <- wrReq_repRam__002(x_13);
    endmethod
endmodule

interface Module124;

endinterface

module mkModule124#(function Action enq_fifoCRqInput_003(Struct2 _),
    function ActionValue#(Struct1) deq_fifo00300())
    (Module124);

    rule child_convert_003;
        let x_0 <- deq_fifo00300();
        Struct2 x_1 = (Struct2 {in_msg : x_0, in_msg_from :
        {((Bit#(2))'(2'h0)),((Bit#(2))'(2'h0))}});
        let x_2 <- enq_fifoCRqInput_003(x_1);
    endrule

    // No methods in this module
endmodule

interface Module125;

endinterface

module mkModule125#(function Action enq_fifoPInput_003(Struct2 _),
    function ActionValue#(Struct1) deq_fifo0032())
    (Module125);

    rule parent_convert_003;
        let x_0 <- deq_fifo0032();
        Struct2 x_1 = (Struct2 {in_msg : x_0, in_msg_from :
        {((Bit#(2))'(2'h2)),((Bit#(2))'(2'h3))}});
        let x_2 <- enq_fifoPInput_003(x_1);
    endrule

    // No methods in this module
endmodule

interface Module126;
    method Action makeEnq_parentChildren003 (Struct18 x_0);
endinterface

module mkModule126#(function Action enq_fifo00302(Struct1 _),
    function Action enq_fifo0031(Struct1 _),
    function Action enq_fifo0030(Struct1 _))
    (Module126);

    // No rules in this module

    method Action makeEnq_parentChildren003 (Struct18 x_0);
        if (((x_0).enq_type) == ((Bit#(2))'(2'h0))) begin
            let x_1 <- enq_fifo0030((x_0).enq_msg);
        end else
            begin
            if (((x_0).enq_type) == ((Bit#(2))'(2'h1))) begin
                let x_2 <- enq_fifo0031((x_0).enq_msg);
            end else begin
                Struct1 x_3 = ((x_0).enq_msg);
                let x_4 <- enq_fifo00302(x_3);
            end
        end
    endmethod
endmodule

interface Module127;
    method Action repGetRq__003 (Bit#(8) x_0);
    method ActionValue#(Vector#(4, Bit#(8))) repGetRs__003 ();
    method Action repAccess__003 (Struct48 x_0);
endinterface

module mkModule127#(function Action wrReq_repRam__003(Struct50 _),
    function ActionValue#(Vector#(4, Bit#(8))) rdResp_repRam__003(),
    function Action rdReq_repRam__003(Bit#(8) _))
    (Module127);

    // No rules in this module

    method Action repGetRq__003 (Bit#(8) x_0);
        let x_1 <- rdReq_repRam__003(x_0);
    endmethod

    method ActionValue#(Vector#(4, Bit#(8))) repGetRs__003 ();
        let x_1 <- rdResp_repRam__003();
        return x_1;
    endmethod

    method Action repAccess__003 (Struct48 x_0);
        Vector#(4, Bit#(8)) x_1 = ((x_0).acc_reps);
        Bit#(8) x_2 = (((x_1)[(Bit#(2))'(2'h3)]) +
        (((((x_1)[(Bit#(2))'(2'h3)]) == ((Bit#(8))'(8'h0))) ||
        (((x_1)[(Bit#(2))'(2'h3)]) == ((Bit#(8))'(8'hff))) ?
        ((Bit#(8))'(8'h0)) : ((Bit#(8))'(8'h1)))));
        Vector#(4, Bit#(8)) x_3 = (update (x_1, (Bit#(2))'(2'h3),
        x_2));
        Bit#(8) x_4 = (((x_3)[(Bit#(2))'(2'h2)]) +
        (((((x_3)[(Bit#(2))'(2'h2)]) == ((Bit#(8))'(8'h0))) ||
        (((x_3)[(Bit#(2))'(2'h2)]) == ((Bit#(8))'(8'hff))) ?
        ((Bit#(8))'(8'h0)) : ((Bit#(8))'(8'h1)))));
        Vector#(4, Bit#(8)) x_5 = (update (x_3, (Bit#(2))'(2'h2),
        x_4));
        Bit#(8) x_6 = (((x_5)[(Bit#(2))'(2'h1)]) +
        (((((x_5)[(Bit#(2))'(2'h1)]) == ((Bit#(8))'(8'h0))) ||
        (((x_5)[(Bit#(2))'(2'h1)]) == ((Bit#(8))'(8'hff))) ?
        ((Bit#(8))'(8'h0)) : ((Bit#(8))'(8'h1)))));
        Vector#(4, Bit#(8)) x_7 = (update (x_5, (Bit#(2))'(2'h1),
        x_6));
        Bit#(8) x_8 = (((x_7)[(Bit#(2))'(2'h0)]) +
        (((((x_7)[(Bit#(2))'(2'h0)]) == ((Bit#(8))'(8'h0))) ||
        (((x_7)[(Bit#(2))'(2'h0)]) == ((Bit#(8))'(8'hff))) ?
        ((Bit#(8))'(8'h0)) : ((Bit#(8))'(8'h1)))));
        Vector#(4, Bit#(8)) x_9 = (update (x_7, (Bit#(2))'(2'h0),
        x_8));
        let x_12 = ?;
        if (((x_0).acc_type) == ((Bit#(1))'(1'h0))) begin
            Vector#(4, Bit#(8)) x_10 = (update (x_9, (x_0).acc_way,
            (Bit#(8))'(8'h1)));
            x_12 = x_10;
        end else begin
            Vector#(4, Bit#(8)) x_11 = (update (x_9, (x_0).acc_way,
            (Bit#(8))'(8'h0)));
            x_12 = x_11;
        end
        Struct50 x_13 = (Struct50 {addr : (x_0).acc_index, datain :
        x_12});
        let x_14 <- wrReq_repRam__003(x_13);
    endmethod
endmodule

interface Module128;
    method Action cache__00__infoRq (Bit#(64) x_0);
    method ActionValue#(Struct9) cache__00__infoRsValueRq (Bit#(64) x_0);
    method ActionValue#(Vector#(4, Bit#(64))) cache__00__valueRsLineRq
    (Struct16 x_0);
endinterface

module mkModule128#(function Action wrReq_dataRam__00(Struct32 _),
    function Action wrReq_edirRam__00__7(Struct31 _),
    function Action wrReq_edirRam__00__6(Struct31 _),
    function Action wrReq_edirRam__00__5(Struct31 _),
    function Action wrReq_edirRam__00__4(Struct31 _),
    function Action wrReq_edirRam__00__3(Struct31 _),
    function Action wrReq_edirRam__00__2(Struct31 _),
    function Action wrReq_edirRam__00__1(Struct31 _),
    function Action wrReq_edirRam__00__0(Struct31 _),
    function Action repAccess__00(Struct30 _),
    function Action victims__00__registerVictim(Struct13 _),
    function Action wrReq_infoRam__00__15(Struct29 _),
    function Action wrReq_infoRam__00__14(Struct29 _),
    function Action wrReq_infoRam__00__13(Struct29 _),
    function Action wrReq_infoRam__00__12(Struct29 _),
    function Action wrReq_infoRam__00__11(Struct29 _),
    function Action wrReq_infoRam__00__10(Struct29 _),
    function Action wrReq_infoRam__00__9(Struct29 _),
    function Action wrReq_infoRam__00__8(Struct29 _),
    function Action wrReq_infoRam__00__7(Struct29 _),
    function Action wrReq_infoRam__00__6(Struct29 _),
    function Action wrReq_infoRam__00__5(Struct29 _),
    function Action wrReq_infoRam__00__4(Struct29 _),
    function Action wrReq_infoRam__00__3(Struct29 _),
    function Action wrReq_infoRam__00__2(Struct29 _),
    function Action wrReq_infoRam__00__1(Struct29 _),
    function Action wrReq_infoRam__00__0(Struct29 _),
    function ActionValue#(Vector#(4, Bit#(64))) rdResp_dataRam__00(),
    function Action rdReq_dataRam__00(Bit#(14) _),
    function ActionValue#(Vector#(16, Bit#(8))) repGetRs__00(),
    function ActionValue#(Struct26) rdResp_edirRam__00__7(),
    function ActionValue#(Struct26) rdResp_edirRam__00__6(),
    function ActionValue#(Struct26) rdResp_edirRam__00__5(),
    function ActionValue#(Struct26) rdResp_edirRam__00__4(),
    function ActionValue#(Struct26) rdResp_edirRam__00__3(),
    function ActionValue#(Struct26) rdResp_edirRam__00__2(),
    function ActionValue#(Struct26) rdResp_edirRam__00__1(),
    function ActionValue#(Struct26) rdResp_edirRam__00__0(),
    function ActionValue#(Struct24) rdResp_infoRam__00__15(),
    function ActionValue#(Struct24) rdResp_infoRam__00__14(),
    function ActionValue#(Struct24) rdResp_infoRam__00__13(),
    function ActionValue#(Struct24) rdResp_infoRam__00__12(),
    function ActionValue#(Struct24) rdResp_infoRam__00__11(),
    function ActionValue#(Struct24) rdResp_infoRam__00__10(),
    function ActionValue#(Struct24) rdResp_infoRam__00__9(),
    function ActionValue#(Struct24) rdResp_infoRam__00__8(),
    function ActionValue#(Struct24) rdResp_infoRam__00__7(),
    function ActionValue#(Struct24) rdResp_infoRam__00__6(),
    function ActionValue#(Struct24) rdResp_infoRam__00__5(),
    function ActionValue#(Struct24) rdResp_infoRam__00__4(),
    function ActionValue#(Struct24) rdResp_infoRam__00__3(),
    function ActionValue#(Struct24) rdResp_infoRam__00__2(),
    function ActionValue#(Struct24) rdResp_infoRam__00__1(),
    function ActionValue#(Struct24) rdResp_infoRam__00__0(),
    function Action repGetRq__00(Bit#(10) _),
    function Action rdReq_edirRam__00__7(Bit#(10) _),
    function Action rdReq_edirRam__00__6(Bit#(10) _),
    function Action rdReq_edirRam__00__5(Bit#(10) _),
    function Action rdReq_edirRam__00__4(Bit#(10) _),
    function Action rdReq_edirRam__00__3(Bit#(10) _),
    function Action rdReq_edirRam__00__2(Bit#(10) _),
    function Action rdReq_edirRam__00__1(Bit#(10) _),
    function Action rdReq_edirRam__00__0(Bit#(10) _),
    function Action rdReq_infoRam__00__15(Bit#(10) _),
    function Action rdReq_infoRam__00__14(Bit#(10) _),
    function Action rdReq_infoRam__00__13(Bit#(10) _),
    function Action rdReq_infoRam__00__12(Bit#(10) _),
    function Action rdReq_infoRam__00__11(Bit#(10) _),
    function Action rdReq_infoRam__00__10(Bit#(10) _),
    function Action rdReq_infoRam__00__9(Bit#(10) _),
    function Action rdReq_infoRam__00__8(Bit#(10) _),
    function Action rdReq_infoRam__00__7(Bit#(10) _),
    function Action rdReq_infoRam__00__6(Bit#(10) _),
    function Action rdReq_infoRam__00__5(Bit#(10) _),
    function Action rdReq_infoRam__00__4(Bit#(10) _),
    function Action rdReq_infoRam__00__3(Bit#(10) _),
    function Action rdReq_infoRam__00__2(Bit#(10) _),
    function Action rdReq_infoRam__00__1(Bit#(10) _),
    function Action rdReq_infoRam__00__0(Bit#(10) _))
    (Module128);

    // No rules in this module

    method Action cache__00__infoRq (Bit#(64) x_0);
        Bit#(10) x_1 = ((x_0)[14:5]);
        let x_2 <- rdReq_infoRam__00__0(x_1);
        let x_3 <- rdReq_infoRam__00__1(x_1);
        let x_4 <- rdReq_infoRam__00__2(x_1);
        let x_5 <- rdReq_infoRam__00__3(x_1);
        let x_6 <- rdReq_infoRam__00__4(x_1);
        let x_7 <- rdReq_infoRam__00__5(x_1);
        let x_8 <- rdReq_infoRam__00__6(x_1);
        let x_9 <- rdReq_infoRam__00__7(x_1);
        let x_10 <- rdReq_infoRam__00__8(x_1);
        let x_11 <- rdReq_infoRam__00__9(x_1);
        let x_12 <- rdReq_infoRam__00__10(x_1);
        let x_13 <- rdReq_infoRam__00__11(x_1);
        let x_14 <- rdReq_infoRam__00__12(x_1);
        let x_15 <- rdReq_infoRam__00__13(x_1);
        let x_16 <- rdReq_infoRam__00__14(x_1);
        let x_17 <- rdReq_infoRam__00__15(x_1);
        let x_18 <- rdReq_edirRam__00__0(x_1);
        let x_19 <- rdReq_edirRam__00__1(x_1);
        let x_20 <- rdReq_edirRam__00__2(x_1);
        let x_21 <- rdReq_edirRam__00__3(x_1);
        let x_22 <- rdReq_edirRam__00__4(x_1);
        let x_23 <- rdReq_edirRam__00__5(x_1);
        let x_24 <- rdReq_edirRam__00__6(x_1);
        let x_25 <- rdReq_edirRam__00__7(x_1);
        let x_26 <- repGetRq__00(x_1);
    endmethod

    method ActionValue#(Struct9) cache__00__infoRsValueRq (Bit#(64) x_0);
        Bit#(49) x_1 = ((x_0)[63:15]);
        Bit#(10) x_2 = ((x_0)[14:5]);
        Vector#(16, Struct24) x_3 = (unpack(0));
        let x_4 <- rdResp_infoRam__00__0();
        Vector#(16, Struct24) x_5 = (update (x_3, (Bit#(4))'(4'h0), x_4));
        let x_6 <- rdResp_infoRam__00__1();
        Vector#(16, Struct24) x_7 = (update (x_5, (Bit#(4))'(4'h1), x_6));
        let x_8 <- rdResp_infoRam__00__2();
        Vector#(16, Struct24) x_9 = (update (x_7, (Bit#(4))'(4'h2), x_8));
        let x_10 <- rdResp_infoRam__00__3();
        Vector#(16, Struct24) x_11 = (update (x_9, (Bit#(4))'(4'h3),
        x_10));
        let x_12 <- rdResp_infoRam__00__4();
        Vector#(16, Struct24) x_13 = (update (x_11, (Bit#(4))'(4'h4),
        x_12));
        let x_14 <- rdResp_infoRam__00__5();
        Vector#(16, Struct24) x_15 = (update (x_13, (Bit#(4))'(4'h5),
        x_14));
        let x_16 <- rdResp_infoRam__00__6();
        Vector#(16, Struct24) x_17 = (update (x_15, (Bit#(4))'(4'h6),
        x_16));
        let x_18 <- rdResp_infoRam__00__7();
        Vector#(16, Struct24) x_19 = (update (x_17, (Bit#(4))'(4'h7),
        x_18));
        let x_20 <- rdResp_infoRam__00__8();
        Vector#(16, Struct24) x_21 = (update (x_19, (Bit#(4))'(4'h8),
        x_20));
        let x_22 <- rdResp_infoRam__00__9();
        Vector#(16, Struct24) x_23 = (update (x_21, (Bit#(4))'(4'h9),
        x_22));
        let x_24 <- rdResp_infoRam__00__10();
        Vector#(16, Struct24) x_25 = (update (x_23, (Bit#(4))'(4'ha),
        x_24));
        let x_26 <- rdResp_infoRam__00__11();
        Vector#(16, Struct24) x_27 = (update (x_25, (Bit#(4))'(4'hb),
        x_26));
        let x_28 <- rdResp_infoRam__00__12();
        Vector#(16, Struct24) x_29 = (update (x_27, (Bit#(4))'(4'hc),
        x_28));
        let x_30 <- rdResp_infoRam__00__13();
        Vector#(16, Struct24) x_31 = (update (x_29, (Bit#(4))'(4'hd),
        x_30));
        let x_32 <- rdResp_infoRam__00__14();
        Vector#(16, Struct24) x_33 = (update (x_31, (Bit#(4))'(4'he),
        x_32));
        let x_34 <- rdResp_infoRam__00__15();
        Vector#(16, Struct24) x_35 = (update (x_33, (Bit#(4))'(4'hf),
        x_34));
        Struct25 x_36 = (((((x_35)[(Bit#(4))'(4'h0)]).tag) == (x_1) ?
        (Struct25 {tm_hit : (Bool)'(True), tm_way : (Bit#(4))'(4'h0),
        tm_value : ((x_35)[(Bit#(4))'(4'h0)]).value}) :
        (((((x_35)[(Bit#(4))'(4'h1)]).tag) == (x_1) ? (Struct25 {tm_hit :
        (Bool)'(True), tm_way : (Bit#(4))'(4'h1), tm_value :
        ((x_35)[(Bit#(4))'(4'h1)]).value}) :
        (((((x_35)[(Bit#(4))'(4'h2)]).tag) == (x_1) ? (Struct25 {tm_hit :
        (Bool)'(True), tm_way : (Bit#(4))'(4'h2), tm_value :
        ((x_35)[(Bit#(4))'(4'h2)]).value}) :
        (((((x_35)[(Bit#(4))'(4'h3)]).tag) == (x_1) ? (Struct25 {tm_hit :
        (Bool)'(True), tm_way : (Bit#(4))'(4'h3), tm_value :
        ((x_35)[(Bit#(4))'(4'h3)]).value}) :
        (((((x_35)[(Bit#(4))'(4'h4)]).tag) == (x_1) ? (Struct25 {tm_hit :
        (Bool)'(True), tm_way : (Bit#(4))'(4'h4), tm_value :
        ((x_35)[(Bit#(4))'(4'h4)]).value}) :
        (((((x_35)[(Bit#(4))'(4'h5)]).tag) == (x_1) ? (Struct25 {tm_hit :
        (Bool)'(True), tm_way : (Bit#(4))'(4'h5), tm_value :
        ((x_35)[(Bit#(4))'(4'h5)]).value}) :
        (((((x_35)[(Bit#(4))'(4'h6)]).tag) == (x_1) ? (Struct25 {tm_hit :
        (Bool)'(True), tm_way : (Bit#(4))'(4'h6), tm_value :
        ((x_35)[(Bit#(4))'(4'h6)]).value}) :
        (((((x_35)[(Bit#(4))'(4'h7)]).tag) == (x_1) ? (Struct25 {tm_hit :
        (Bool)'(True), tm_way : (Bit#(4))'(4'h7), tm_value :
        ((x_35)[(Bit#(4))'(4'h7)]).value}) :
        (((((x_35)[(Bit#(4))'(4'h8)]).tag) == (x_1) ? (Struct25 {tm_hit :
        (Bool)'(True), tm_way : (Bit#(4))'(4'h8), tm_value :
        ((x_35)[(Bit#(4))'(4'h8)]).value}) :
        (((((x_35)[(Bit#(4))'(4'h9)]).tag) == (x_1) ? (Struct25 {tm_hit :
        (Bool)'(True), tm_way : (Bit#(4))'(4'h9), tm_value :
        ((x_35)[(Bit#(4))'(4'h9)]).value}) :
        (((((x_35)[(Bit#(4))'(4'ha)]).tag) == (x_1) ? (Struct25 {tm_hit :
        (Bool)'(True), tm_way : (Bit#(4))'(4'ha), tm_value :
        ((x_35)[(Bit#(4))'(4'ha)]).value}) :
        (((((x_35)[(Bit#(4))'(4'hb)]).tag) == (x_1) ? (Struct25 {tm_hit :
        (Bool)'(True), tm_way : (Bit#(4))'(4'hb), tm_value :
        ((x_35)[(Bit#(4))'(4'hb)]).value}) :
        (((((x_35)[(Bit#(4))'(4'hc)]).tag) == (x_1) ? (Struct25 {tm_hit :
        (Bool)'(True), tm_way : (Bit#(4))'(4'hc), tm_value :
        ((x_35)[(Bit#(4))'(4'hc)]).value}) :
        (((((x_35)[(Bit#(4))'(4'hd)]).tag) == (x_1) ? (Struct25 {tm_hit :
        (Bool)'(True), tm_way : (Bit#(4))'(4'hd), tm_value :
        ((x_35)[(Bit#(4))'(4'hd)]).value}) :
        (((((x_35)[(Bit#(4))'(4'he)]).tag) == (x_1) ? (Struct25 {tm_hit :
        (Bool)'(True), tm_way : (Bit#(4))'(4'he), tm_value :
        ((x_35)[(Bit#(4))'(4'he)]).value}) :
        (((((x_35)[(Bit#(4))'(4'hf)]).tag) == (x_1) ? (Struct25 {tm_hit :
        (Bool)'(True), tm_way : (Bit#(4))'(4'hf), tm_value :
        ((x_35)[(Bit#(4))'(4'hf)]).value}) :
        (unpack(0))))))))))))))))))))))))))))))))));
        Vector#(8, Struct26) x_37 = (unpack(0));
        let x_38 <- rdResp_edirRam__00__0();
        Vector#(8, Struct26) x_39 = (update (x_37, (Bit#(3))'(3'h0),
        x_38));
        let x_40 <- rdResp_edirRam__00__1();
        Vector#(8, Struct26) x_41 = (update (x_39, (Bit#(3))'(3'h1),
        x_40));
        let x_42 <- rdResp_edirRam__00__2();
        Vector#(8, Struct26) x_43 = (update (x_41, (Bit#(3))'(3'h2),
        x_42));
        let x_44 <- rdResp_edirRam__00__3();
        Vector#(8, Struct26) x_45 = (update (x_43, (Bit#(3))'(3'h3),
        x_44));
        let x_46 <- rdResp_edirRam__00__4();
        Vector#(8, Struct26) x_47 = (update (x_45, (Bit#(3))'(3'h4),
        x_46));
        let x_48 <- rdResp_edirRam__00__5();
        Vector#(8, Struct26) x_49 = (update (x_47, (Bit#(3))'(3'h5),
        x_48));
        let x_50 <- rdResp_edirRam__00__6();
        Vector#(8, Struct26) x_51 = (update (x_49, (Bit#(3))'(3'h6),
        x_50));
        let x_52 <- rdResp_edirRam__00__7();
        Vector#(8, Struct26) x_53 = (update (x_51, (Bit#(3))'(3'h7),
        x_52));
        Struct28 x_54 = (((((x_53)[(Bit#(3))'(3'h0)]).tag) == (x_1) ?
        (Struct28 {tm_hit : (Bool)'(True), tm_way : (Bit#(3))'(3'h0),
        tm_value : ((x_53)[(Bit#(3))'(3'h0)]).value}) :
        (((((x_53)[(Bit#(3))'(3'h1)]).tag) == (x_1) ? (Struct28 {tm_hit :
        (Bool)'(True), tm_way : (Bit#(3))'(3'h1), tm_value :
        ((x_53)[(Bit#(3))'(3'h1)]).value}) :
        (((((x_53)[(Bit#(3))'(3'h2)]).tag) == (x_1) ? (Struct28 {tm_hit :
        (Bool)'(True), tm_way : (Bit#(3))'(3'h2), tm_value :
        ((x_53)[(Bit#(3))'(3'h2)]).value}) :
        (((((x_53)[(Bit#(3))'(3'h3)]).tag) == (x_1) ? (Struct28 {tm_hit :
        (Bool)'(True), tm_way : (Bit#(3))'(3'h3), tm_value :
        ((x_53)[(Bit#(3))'(3'h3)]).value}) :
        (((((x_53)[(Bit#(3))'(3'h4)]).tag) == (x_1) ? (Struct28 {tm_hit :
        (Bool)'(True), tm_way : (Bit#(3))'(3'h4), tm_value :
        ((x_53)[(Bit#(3))'(3'h4)]).value}) :
        (((((x_53)[(Bit#(3))'(3'h5)]).tag) == (x_1) ? (Struct28 {tm_hit :
        (Bool)'(True), tm_way : (Bit#(3))'(3'h5), tm_value :
        ((x_53)[(Bit#(3))'(3'h5)]).value}) :
        (((((x_53)[(Bit#(3))'(3'h6)]).tag) == (x_1) ? (Struct28 {tm_hit :
        (Bool)'(True), tm_way : (Bit#(3))'(3'h6), tm_value :
        ((x_53)[(Bit#(3))'(3'h6)]).value}) :
        (((((x_53)[(Bit#(3))'(3'h7)]).tag) == (x_1) ? (Struct28 {tm_hit :
        (Bool)'(True), tm_way : (Bit#(3))'(3'h7), tm_value :
        ((x_53)[(Bit#(3))'(3'h7)]).value}) :
        (unpack(0))))))))))))))))));
        Struct27 x_55 = ((x_54).tm_value);
        Struct5 x_56 = ((! (((Bit#(3))'(3'h1)) <
        ((((x_53)[(Bit#(3))'(3'h0)]).value).mesi_edir_st)) ? (Struct5 {valid
        : (Bool)'(True), data : (Bit#(3))'(3'h0)}) : ((! (((Bit#(3))'(3'h1))
        < ((((x_53)[(Bit#(3))'(3'h1)]).value).mesi_edir_st)) ? (Struct5
        {valid : (Bool)'(True), data : (Bit#(3))'(3'h1)}) : ((!
        (((Bit#(3))'(3'h1)) <
        ((((x_53)[(Bit#(3))'(3'h2)]).value).mesi_edir_st)) ? (Struct5 {valid
        : (Bool)'(True), data : (Bit#(3))'(3'h2)}) : ((! (((Bit#(3))'(3'h1))
        < ((((x_53)[(Bit#(3))'(3'h3)]).value).mesi_edir_st)) ? (Struct5
        {valid : (Bool)'(True), data : (Bit#(3))'(3'h3)}) : ((!
        (((Bit#(3))'(3'h1)) <
        ((((x_53)[(Bit#(3))'(3'h4)]).value).mesi_edir_st)) ? (Struct5 {valid
        : (Bool)'(True), data : (Bit#(3))'(3'h4)}) : ((! (((Bit#(3))'(3'h1))
        < ((((x_53)[(Bit#(3))'(3'h5)]).value).mesi_edir_st)) ? (Struct5
        {valid : (Bool)'(True), data : (Bit#(3))'(3'h5)}) : ((!
        (((Bit#(3))'(3'h1)) <
        ((((x_53)[(Bit#(3))'(3'h6)]).value).mesi_edir_st)) ? (Struct5 {valid
        : (Bool)'(True), data : (Bit#(3))'(3'h6)}) : ((! (((Bit#(3))'(3'h1))
        < ((((x_53)[(Bit#(3))'(3'h7)]).value).mesi_edir_st)) ? (Struct5
        {valid : (Bool)'(True), data : (Bit#(3))'(3'h7)}) : (Struct5 {valid :
        (Bool)'(False), data : unpack(0)})))))))))))))))));
        let x_57 <- repGetRs__00();
        Bit#(4) x_58 = (unpack(0));
        Bit#(8) x_59 = (unpack(0));
        Bit#(4) x_60 = ((! (((x_57)[(Bit#(4))'(4'hf)]) < (x_59)) ?
        ((Bit#(4))'(4'hf)) : (x_58)));
        Bit#(8) x_61 = ((! (((x_57)[(Bit#(4))'(4'hf)]) < (x_59)) ?
        ((x_57)[(Bit#(4))'(4'hf)]) : (x_59)));
        Bit#(4) x_62 = ((! (((x_57)[(Bit#(4))'(4'he)]) < (x_61)) ?
        ((Bit#(4))'(4'he)) : (x_60)));
        Bit#(8) x_63 = ((! (((x_57)[(Bit#(4))'(4'he)]) < (x_61)) ?
        ((x_57)[(Bit#(4))'(4'he)]) : (x_61)));
        Bit#(4) x_64 = ((! (((x_57)[(Bit#(4))'(4'hd)]) < (x_63)) ?
        ((Bit#(4))'(4'hd)) : (x_62)));
        Bit#(8) x_65 = ((! (((x_57)[(Bit#(4))'(4'hd)]) < (x_63)) ?
        ((x_57)[(Bit#(4))'(4'hd)]) : (x_63)));
        Bit#(4) x_66 = ((! (((x_57)[(Bit#(4))'(4'hc)]) < (x_65)) ?
        ((Bit#(4))'(4'hc)) : (x_64)));
        Bit#(8) x_67 = ((! (((x_57)[(Bit#(4))'(4'hc)]) < (x_65)) ?
        ((x_57)[(Bit#(4))'(4'hc)]) : (x_65)));
        Bit#(4) x_68 = ((! (((x_57)[(Bit#(4))'(4'hb)]) < (x_67)) ?
        ((Bit#(4))'(4'hb)) : (x_66)));
        Bit#(8) x_69 = ((! (((x_57)[(Bit#(4))'(4'hb)]) < (x_67)) ?
        ((x_57)[(Bit#(4))'(4'hb)]) : (x_67)));
        Bit#(4) x_70 = ((! (((x_57)[(Bit#(4))'(4'ha)]) < (x_69)) ?
        ((Bit#(4))'(4'ha)) : (x_68)));
        Bit#(8) x_71 = ((! (((x_57)[(Bit#(4))'(4'ha)]) < (x_69)) ?
        ((x_57)[(Bit#(4))'(4'ha)]) : (x_69)));
        Bit#(4) x_72 = ((! (((x_57)[(Bit#(4))'(4'h9)]) < (x_71)) ?
        ((Bit#(4))'(4'h9)) : (x_70)));
        Bit#(8) x_73 = ((! (((x_57)[(Bit#(4))'(4'h9)]) < (x_71)) ?
        ((x_57)[(Bit#(4))'(4'h9)]) : (x_71)));
        Bit#(4) x_74 = ((! (((x_57)[(Bit#(4))'(4'h8)]) < (x_73)) ?
        ((Bit#(4))'(4'h8)) : (x_72)));
        Bit#(8) x_75 = ((! (((x_57)[(Bit#(4))'(4'h8)]) < (x_73)) ?
        ((x_57)[(Bit#(4))'(4'h8)]) : (x_73)));
        Bit#(4) x_76 = ((! (((x_57)[(Bit#(4))'(4'h7)]) < (x_75)) ?
        ((Bit#(4))'(4'h7)) : (x_74)));
        Bit#(8) x_77 = ((! (((x_57)[(Bit#(4))'(4'h7)]) < (x_75)) ?
        ((x_57)[(Bit#(4))'(4'h7)]) : (x_75)));
        Bit#(4) x_78 = ((! (((x_57)[(Bit#(4))'(4'h6)]) < (x_77)) ?
        ((Bit#(4))'(4'h6)) : (x_76)));
        Bit#(8) x_79 = ((! (((x_57)[(Bit#(4))'(4'h6)]) < (x_77)) ?
        ((x_57)[(Bit#(4))'(4'h6)]) : (x_77)));
        Bit#(4) x_80 = ((! (((x_57)[(Bit#(4))'(4'h5)]) < (x_79)) ?
        ((Bit#(4))'(4'h5)) : (x_78)));
        Bit#(8) x_81 = ((! (((x_57)[(Bit#(4))'(4'h5)]) < (x_79)) ?
        ((x_57)[(Bit#(4))'(4'h5)]) : (x_79)));
        Bit#(4) x_82 = ((! (((x_57)[(Bit#(4))'(4'h4)]) < (x_81)) ?
        ((Bit#(4))'(4'h4)) : (x_80)));
        Bit#(8) x_83 = ((! (((x_57)[(Bit#(4))'(4'h4)]) < (x_81)) ?
        ((x_57)[(Bit#(4))'(4'h4)]) : (x_81)));
        Bit#(4) x_84 = ((! (((x_57)[(Bit#(4))'(4'h3)]) < (x_83)) ?
        ((Bit#(4))'(4'h3)) : (x_82)));
        Bit#(8) x_85 = ((! (((x_57)[(Bit#(4))'(4'h3)]) < (x_83)) ?
        ((x_57)[(Bit#(4))'(4'h3)]) : (x_83)));
        Bit#(4) x_86 = ((! (((x_57)[(Bit#(4))'(4'h2)]) < (x_85)) ?
        ((Bit#(4))'(4'h2)) : (x_84)));
        Bit#(8) x_87 = ((! (((x_57)[(Bit#(4))'(4'h2)]) < (x_85)) ?
        ((x_57)[(Bit#(4))'(4'h2)]) : (x_85)));
        Bit#(4) x_88 = ((! (((x_57)[(Bit#(4))'(4'h1)]) < (x_87)) ?
        ((Bit#(4))'(4'h1)) : (x_86)));
        Bit#(8) x_89 = ((! (((x_57)[(Bit#(4))'(4'h1)]) < (x_87)) ?
        ((x_57)[(Bit#(4))'(4'h1)]) : (x_87)));
        Bit#(4) x_90 = ((! (((x_57)[(Bit#(4))'(4'h0)]) < (x_89)) ?
        ((Bit#(4))'(4'h0)) : (x_88)));
        Bit#(8) x_91 = ((! (((x_57)[(Bit#(4))'(4'h0)]) < (x_89)) ?
        ((x_57)[(Bit#(4))'(4'h0)]) : (x_89)));
        when (! ((x_91) == ((Bit#(8))'(8'h0))), noAction);
        Struct24 x_92 = ((x_35)[x_90]);
        Bit#(49) x_93 = ((x_92).tag);
        Struct10 x_94 = ((x_92).value);
        Bit#(4) x_95 = (((x_36).tm_hit ? ((x_36).tm_way) : (x_90)));
        Struct9 x_96 = (Struct9 {info_index : x_2, info_hit : (x_36).tm_hit,
        info_way : x_95, edir_hit : (x_54).tm_hit, edir_way : (x_54).tm_way,
        edir_slot : x_56, info : ((x_36).tm_hit ? ((x_36).tm_value) :
        (Struct10 {mesi_owned : (x_55).mesi_edir_owned, mesi_status :
        (Bit#(3))'(3'h1), mesi_dir_st : (x_55).mesi_edir_st, mesi_dir_sharers
        : (x_55).mesi_edir_sharers})), may_victim : Struct11 {mv_addr :
        {(x_93),({(x_2),((Bit#(5))'(5'h0))})}, mv_info : x_94}, reps :
        x_57});
        let x_97 <- rdReq_dataRam__00({(x_95),(x_2)});
        return x_96;
    endmethod

    method ActionValue#(Vector#(4, Bit#(64))) cache__00__valueRsLineRq
    (Struct16 x_0);
        let x_1 <- rdResp_dataRam__00();
        Bit#(64) x_2 = ((x_0).addr);
        Bit#(10) x_3 = ((x_2)[14:5]);
        Bit#(4) x_4 = ((x_0).info_way);
        Struct10 x_5 = ((x_0).info);
        Bool x_6 = ((! (((Bit#(3))'(3'h1)) < ((x_5).mesi_status))) && (!
        (((x_5).mesi_dir_st) == ((Bit#(3))'(3'h3)))));
        Struct5 x_7 = ((x_0).edir_slot);
        Bool x_8 = ((x_7).valid);
        Bit#(3) x_9 =
        ((x_7).data);
        if ((x_0).info_write)
            begin
            if ((((x_0).info_hit) || (! (x_6))) || (((! ((x_0).edir_hit)) &&
                (x_6)) && (! (x_8)))) begin
                Struct29 x_10 = (Struct29 {addr : x_3, datain : Struct24 {tag
                : (x_2)[63:15], value :
                x_5}});
                if ((x_4) == ((Bit#(4))'(4'h0))) begin
                    let x_11 <- wrReq_infoRam__00__0(x_10);
                end else begin

                end
                if ((x_4) == ((Bit#(4))'(4'h1))) begin
                    let x_13 <- wrReq_infoRam__00__1(x_10);
                end else begin

                end
                if ((x_4) == ((Bit#(4))'(4'h2))) begin
                    let x_15 <- wrReq_infoRam__00__2(x_10);
                end else begin

                end
                if ((x_4) == ((Bit#(4))'(4'h3))) begin
                    let x_17 <- wrReq_infoRam__00__3(x_10);
                end else begin

                end
                if ((x_4) == ((Bit#(4))'(4'h4))) begin
                    let x_19 <- wrReq_infoRam__00__4(x_10);
                end else begin

                end
                if ((x_4) == ((Bit#(4))'(4'h5))) begin
                    let x_21 <- wrReq_infoRam__00__5(x_10);
                end else begin

                end
                if ((x_4) == ((Bit#(4))'(4'h6))) begin
                    let x_23 <- wrReq_infoRam__00__6(x_10);
                end else begin

                end
                if ((x_4) == ((Bit#(4))'(4'h7))) begin
                    let x_25 <- wrReq_infoRam__00__7(x_10);
                end else begin

                end
                if ((x_4) == ((Bit#(4))'(4'h8))) begin
                    let x_27 <- wrReq_infoRam__00__8(x_10);
                end else begin

                end
                if ((x_4) == ((Bit#(4))'(4'h9))) begin
                    let x_29 <- wrReq_infoRam__00__9(x_10);
                end else begin

                end
                if ((x_4) == ((Bit#(4))'(4'ha))) begin
                    let x_31 <- wrReq_infoRam__00__10(x_10);
                end else begin

                end
                if ((x_4) == ((Bit#(4))'(4'hb))) begin
                    let x_33 <- wrReq_infoRam__00__11(x_10);
                end else begin

                end
                if ((x_4) == ((Bit#(4))'(4'hc))) begin
                    let x_35 <- wrReq_infoRam__00__12(x_10);
                end else begin

                end
                if ((x_4) == ((Bit#(4))'(4'hd))) begin
                    let x_37 <- wrReq_infoRam__00__13(x_10);
                end else begin

                end
                if ((x_4) == ((Bit#(4))'(4'he))) begin
                    let x_39 <- wrReq_infoRam__00__14(x_10);
                end else begin

                end
                if ((x_4) == ((Bit#(4))'(4'hf))) begin
                    let x_41 <- wrReq_infoRam__00__15(x_10);
                end else begin

                end
                if (! ((x_0).info_hit)) begin
                    Struct11 x_43 = ((x_0).may_victim);
                    Struct13 x_44 = (Struct13 {victim_valid : (Bool)'(True),
                    victim_addr : (x_43).mv_addr, victim_info :
                    (x_43).mv_info, victim_value : x_1, victim_req :
                    (Bool)'(False)});
                    let x_45 <- victims__00__registerVictim(x_44);
                end else begin

                end
                let x_47 <- repAccess__00(Struct30 {acc_type : (!
                (((Bit#(3))'(3'h1)) < ((x_5).mesi_dir_st)) ?
                ((Bit#(1))'(1'h0)) : ((Bit#(1))'(1'h1))), acc_reps :
                (x_0).reps, acc_index : x_3, acc_way : x_4});
            end else begin

            end
            if (((! ((x_0).info_hit)) && (x_6)) && (((x_0).edir_hit) ||
                (x_8))) begin
                Bit#(3) x_49 = (((x_0).edir_hit ? ((x_0).edir_way) :
                (x_9)));
                Struct31 x_50 = (Struct31 {addr : (x_2)[14:5], datain :
                Struct26 {tag : (x_2)[63:15], value : Struct27
                {mesi_edir_owned : (x_5).mesi_owned, mesi_edir_st :
                (x_5).mesi_dir_st, mesi_edir_sharers :
                (x_5).mesi_dir_sharers}}});
                if ((x_49) == ((Bit#(3))'(3'h0))) begin
                    let x_51 <- wrReq_edirRam__00__0(x_50);
                end else begin

                end
                if ((x_49) == ((Bit#(3))'(3'h1))) begin
                    let x_53 <- wrReq_edirRam__00__1(x_50);
                end else begin

                end
                if ((x_49) == ((Bit#(3))'(3'h2))) begin
                    let x_55 <- wrReq_edirRam__00__2(x_50);
                end else begin

                end
                if ((x_49) == ((Bit#(3))'(3'h3))) begin
                    let x_57 <- wrReq_edirRam__00__3(x_50);
                end else begin

                end
                if ((x_49) == ((Bit#(3))'(3'h4))) begin
                    let x_59 <- wrReq_edirRam__00__4(x_50);
                end else begin

                end
                if ((x_49) == ((Bit#(3))'(3'h5))) begin
                    let x_61 <- wrReq_edirRam__00__5(x_50);
                end else begin

                end
                if ((x_49) == ((Bit#(3))'(3'h6))) begin
                    let x_63 <- wrReq_edirRam__00__6(x_50);
                end else begin

                end
                if ((x_49) == ((Bit#(3))'(3'h7))) begin
                    let x_65 <- wrReq_edirRam__00__7(x_50);
                end else begin

                end
            end else
                begin
                if ((x_0).edir_hit) begin
                    Bit#(3) x_67 = ((x_0).edir_way);
                    Struct31 x_68 = (Struct31 {addr : (x_2)[14:5], datain :
                    Struct26 {tag : (x_2)[63:15], value : Struct27
                    {mesi_edir_owned : (x_5).mesi_owned, mesi_edir_st :
                    (x_5).mesi_dir_st, mesi_edir_sharers :
                    (x_5).mesi_dir_sharers}}});
                    if ((x_67) == ((Bit#(3))'(3'h0))) begin
                        let x_69 <- wrReq_edirRam__00__0(x_68);
                    end else begin

                    end
                    if ((x_67) == ((Bit#(3))'(3'h1))) begin
                        let x_71 <- wrReq_edirRam__00__1(x_68);
                    end else begin

                    end
                    if ((x_67) == ((Bit#(3))'(3'h2))) begin
                        let x_73 <- wrReq_edirRam__00__2(x_68);
                    end else begin

                    end
                    if ((x_67) == ((Bit#(3))'(3'h3))) begin
                        let x_75 <- wrReq_edirRam__00__3(x_68);
                    end else begin

                    end
                    if ((x_67) == ((Bit#(3))'(3'h4))) begin
                        let x_77 <- wrReq_edirRam__00__4(x_68);
                    end else begin

                    end
                    if ((x_67) == ((Bit#(3))'(3'h5))) begin
                        let x_79 <- wrReq_edirRam__00__5(x_68);
                    end else begin

                    end
                    if ((x_67) == ((Bit#(3))'(3'h6))) begin
                        let x_81 <- wrReq_edirRam__00__6(x_68);
                    end else begin

                    end
                    if ((x_67) == ((Bit#(3))'(3'h7))) begin
                        let x_83 <- wrReq_edirRam__00__7(x_68);
                    end else begin

                    end
                end else begin

                end
            end
        end else begin

        end
        if ((x_0).value_write) begin
            Struct32 x_88 = (Struct32 {addr : {(x_4),((x_2)[14:5])}, datain :
            (x_0).value});
            let x_89 <- wrReq_dataRam__00(x_88);
        end else begin

        end
        return x_1;
    endmethod
endmodule

interface Module129;
    method Action cache__000__infoRq (Bit#(64) x_0);
    method ActionValue#(Struct39) cache__000__infoRsValueRq (Bit#(64) x_0);
    method ActionValue#(Vector#(4, Bit#(64))) cache__000__valueRsLineRq
    (Struct42 x_0);
endinterface

module mkModule129#(function Action wrReq_dataRam__000(Struct49 _),
    function Action repAccess__000(Struct48 _),
    function Action victims__000__registerVictim(Struct13 _),
    function Action wrReq_infoRam__000__3(Struct47 _),
    function Action wrReq_infoRam__000__2(Struct47 _),
    function Action wrReq_infoRam__000__1(Struct47 _),
    function Action wrReq_infoRam__000__0(Struct47 _),
    function ActionValue#(Vector#(4, Bit#(64))) rdResp_dataRam__000(),
    function Action rdReq_dataRam__000(Bit#(10) _),
    function ActionValue#(Vector#(4, Bit#(8))) repGetRs__000(),
    function ActionValue#(Struct45) rdResp_infoRam__000__3(),
    function ActionValue#(Struct45) rdResp_infoRam__000__2(),
    function ActionValue#(Struct45) rdResp_infoRam__000__1(),
    function ActionValue#(Struct45) rdResp_infoRam__000__0(),
    function Action repGetRq__000(Bit#(8) _),
    function Action rdReq_infoRam__000__3(Bit#(8) _),
    function Action rdReq_infoRam__000__2(Bit#(8) _),
    function Action rdReq_infoRam__000__1(Bit#(8) _),
    function Action rdReq_infoRam__000__0(Bit#(8) _))
    (Module129);

    // No rules in this module

    method Action cache__000__infoRq (Bit#(64) x_0);
        Bit#(8) x_1 = ((x_0)[12:5]);
        let x_2 <- rdReq_infoRam__000__0(x_1);
        let x_3 <- rdReq_infoRam__000__1(x_1);
        let x_4 <- rdReq_infoRam__000__2(x_1);
        let x_5 <- rdReq_infoRam__000__3(x_1);
        let x_6 <- repGetRq__000(x_1);
    endmethod

    method ActionValue#(Struct39) cache__000__infoRsValueRq (Bit#(64) x_0);
        Bit#(51) x_1 = ((x_0)[63:13]);
        Bit#(8) x_2 = ((x_0)[12:5]);
        Vector#(4, Struct45) x_3 = (unpack(0));
        let x_4 <- rdResp_infoRam__000__0();
        Vector#(4, Struct45) x_5 = (update (x_3, (Bit#(2))'(2'h0), x_4));
        let x_6 <- rdResp_infoRam__000__1();
        Vector#(4, Struct45) x_7 = (update (x_5, (Bit#(2))'(2'h1), x_6));
        let x_8 <- rdResp_infoRam__000__2();
        Vector#(4, Struct45) x_9 = (update (x_7, (Bit#(2))'(2'h2), x_8));
        let x_10 <- rdResp_infoRam__000__3();
        Vector#(4, Struct45) x_11 = (update (x_9, (Bit#(2))'(2'h3),
        x_10));
        Struct46 x_12 = (((((x_11)[(Bit#(2))'(2'h0)]).tag) == (x_1) ?
        (Struct46 {tm_hit : (Bool)'(True), tm_way : (Bit#(2))'(2'h0),
        tm_value : ((x_11)[(Bit#(2))'(2'h0)]).value}) :
        (((((x_11)[(Bit#(2))'(2'h1)]).tag) == (x_1) ? (Struct46 {tm_hit :
        (Bool)'(True), tm_way : (Bit#(2))'(2'h1), tm_value :
        ((x_11)[(Bit#(2))'(2'h1)]).value}) :
        (((((x_11)[(Bit#(2))'(2'h2)]).tag) == (x_1) ? (Struct46 {tm_hit :
        (Bool)'(True), tm_way : (Bit#(2))'(2'h2), tm_value :
        ((x_11)[(Bit#(2))'(2'h2)]).value}) :
        (((((x_11)[(Bit#(2))'(2'h3)]).tag) == (x_1) ? (Struct46 {tm_hit :
        (Bool)'(True), tm_way : (Bit#(2))'(2'h3), tm_value :
        ((x_11)[(Bit#(2))'(2'h3)]).value}) : (unpack(0))))))))));
        let x_13 <- repGetRs__000();
        Bit#(2) x_14 = (unpack(0));
        Bit#(8) x_15 = (unpack(0));
        Bit#(2) x_16 = ((! (((x_13)[(Bit#(2))'(2'h3)]) < (x_15)) ?
        ((Bit#(2))'(2'h3)) : (x_14)));
        Bit#(8) x_17 = ((! (((x_13)[(Bit#(2))'(2'h3)]) < (x_15)) ?
        ((x_13)[(Bit#(2))'(2'h3)]) : (x_15)));
        Bit#(2) x_18 = ((! (((x_13)[(Bit#(2))'(2'h2)]) < (x_17)) ?
        ((Bit#(2))'(2'h2)) : (x_16)));
        Bit#(8) x_19 = ((! (((x_13)[(Bit#(2))'(2'h2)]) < (x_17)) ?
        ((x_13)[(Bit#(2))'(2'h2)]) : (x_17)));
        Bit#(2) x_20 = ((! (((x_13)[(Bit#(2))'(2'h1)]) < (x_19)) ?
        ((Bit#(2))'(2'h1)) : (x_18)));
        Bit#(8) x_21 = ((! (((x_13)[(Bit#(2))'(2'h1)]) < (x_19)) ?
        ((x_13)[(Bit#(2))'(2'h1)]) : (x_19)));
        Bit#(2) x_22 = ((! (((x_13)[(Bit#(2))'(2'h0)]) < (x_21)) ?
        ((Bit#(2))'(2'h0)) : (x_20)));
        Bit#(8) x_23 = ((! (((x_13)[(Bit#(2))'(2'h0)]) < (x_21)) ?
        ((x_13)[(Bit#(2))'(2'h0)]) : (x_21)));
        when (! ((x_23) == ((Bit#(8))'(8'h0))), noAction);
        Struct45 x_24 = ((x_11)[x_22]);
        Bit#(51) x_25 = ((x_24).tag);
        Struct10 x_26 = ((x_24).value);
        Bit#(2) x_27 = (((x_12).tm_hit ? ((x_12).tm_way) : (x_22)));
        Struct39 x_28 = (Struct39 {info_index : x_2, info_hit :
        (x_12).tm_hit, info_way : x_27, edir_hit : unpack(0), edir_way :
        unpack(0), edir_slot : unpack(0), info : (x_12).tm_value, may_victim
        : Struct11 {mv_addr : {(x_25),({(x_2),((Bit#(5))'(5'h0))})}, mv_info
        : x_26}, reps : x_13});
        let x_29 <- rdReq_dataRam__000({(x_27),(x_2)});
        return x_28;
    endmethod

    method ActionValue#(Vector#(4, Bit#(64))) cache__000__valueRsLineRq
    (Struct42 x_0);
        let x_1 <- rdResp_dataRam__000();
        Bit#(64) x_2 = ((x_0).addr);
        Bit#(8) x_3 = ((x_2)[12:5]);
        Bit#(2) x_4 = ((x_0).info_way);
        Struct10 x_5 =
        ((x_0).info);
        if ((x_0).info_write) begin
            Struct47 x_6 = (Struct47 {addr : x_3, datain : Struct45 {tag :
            (x_2)[63:13], value :
            x_5}});
            if ((x_4) == ((Bit#(2))'(2'h0))) begin
                let x_7 <- wrReq_infoRam__000__0(x_6);
            end else begin

            end
            if ((x_4) == ((Bit#(2))'(2'h1))) begin
                let x_9 <- wrReq_infoRam__000__1(x_6);
            end else begin

            end
            if ((x_4) == ((Bit#(2))'(2'h2))) begin
                let x_11 <- wrReq_infoRam__000__2(x_6);
            end else begin

            end
            if ((x_4) == ((Bit#(2))'(2'h3))) begin
                let x_13 <- wrReq_infoRam__000__3(x_6);
            end else begin

            end
            if (! ((x_0).info_hit)) begin
                Struct11 x_15 = ((x_0).may_victim);
                Struct13 x_16 = (Struct13 {victim_valid : (Bool)'(True),
                victim_addr : (x_15).mv_addr, victim_info : (x_15).mv_info,
                victim_value : x_1, victim_req : (Bool)'(False)});
                let x_17 <- victims__000__registerVictim(x_16);
            end else begin

            end
            let x_19 <- repAccess__000(Struct48 {acc_type : (!
            (((Bit#(3))'(3'h1)) < ((x_5).mesi_dir_st)) ? ((Bit#(1))'(1'h0)) :
            ((Bit#(1))'(1'h1))), acc_reps : (x_0).reps, acc_index : x_3,
            acc_way : x_4});
        end else begin

        end
        if ((x_0).value_write) begin
            Struct49 x_21 = (Struct49 {addr : {(x_4),((x_2)[12:5])}, datain :
            (x_0).value});
            let x_22 <- wrReq_dataRam__000(x_21);
        end else begin

        end
        return x_1;
    endmethod
endmodule

interface Module130;
    method Action cache__001__infoRq (Bit#(64) x_0);
    method ActionValue#(Struct39) cache__001__infoRsValueRq (Bit#(64) x_0);
    method ActionValue#(Vector#(4, Bit#(64))) cache__001__valueRsLineRq
    (Struct42 x_0);
endinterface

module mkModule130#(function Action wrReq_dataRam__001(Struct49 _),
    function Action repAccess__001(Struct48 _),
    function Action victims__001__registerVictim(Struct13 _),
    function Action wrReq_infoRam__001__3(Struct47 _),
    function Action wrReq_infoRam__001__2(Struct47 _),
    function Action wrReq_infoRam__001__1(Struct47 _),
    function Action wrReq_infoRam__001__0(Struct47 _),
    function ActionValue#(Vector#(4, Bit#(64))) rdResp_dataRam__001(),
    function Action rdReq_dataRam__001(Bit#(10) _),
    function ActionValue#(Vector#(4, Bit#(8))) repGetRs__001(),
    function ActionValue#(Struct45) rdResp_infoRam__001__3(),
    function ActionValue#(Struct45) rdResp_infoRam__001__2(),
    function ActionValue#(Struct45) rdResp_infoRam__001__1(),
    function ActionValue#(Struct45) rdResp_infoRam__001__0(),
    function Action repGetRq__001(Bit#(8) _),
    function Action rdReq_infoRam__001__3(Bit#(8) _),
    function Action rdReq_infoRam__001__2(Bit#(8) _),
    function Action rdReq_infoRam__001__1(Bit#(8) _),
    function Action rdReq_infoRam__001__0(Bit#(8) _))
    (Module130);

    // No rules in this module

    method Action cache__001__infoRq (Bit#(64) x_0);
        Bit#(8) x_1 = ((x_0)[12:5]);
        let x_2 <- rdReq_infoRam__001__0(x_1);
        let x_3 <- rdReq_infoRam__001__1(x_1);
        let x_4 <- rdReq_infoRam__001__2(x_1);
        let x_5 <- rdReq_infoRam__001__3(x_1);
        let x_6 <- repGetRq__001(x_1);
    endmethod

    method ActionValue#(Struct39) cache__001__infoRsValueRq (Bit#(64) x_0);
        Bit#(51) x_1 = ((x_0)[63:13]);
        Bit#(8) x_2 = ((x_0)[12:5]);
        Vector#(4, Struct45) x_3 = (unpack(0));
        let x_4 <- rdResp_infoRam__001__0();
        Vector#(4, Struct45) x_5 = (update (x_3, (Bit#(2))'(2'h0), x_4));
        let x_6 <- rdResp_infoRam__001__1();
        Vector#(4, Struct45) x_7 = (update (x_5, (Bit#(2))'(2'h1), x_6));
        let x_8 <- rdResp_infoRam__001__2();
        Vector#(4, Struct45) x_9 = (update (x_7, (Bit#(2))'(2'h2), x_8));
        let x_10 <- rdResp_infoRam__001__3();
        Vector#(4, Struct45) x_11 = (update (x_9, (Bit#(2))'(2'h3),
        x_10));
        Struct46 x_12 = (((((x_11)[(Bit#(2))'(2'h0)]).tag) == (x_1) ?
        (Struct46 {tm_hit : (Bool)'(True), tm_way : (Bit#(2))'(2'h0),
        tm_value : ((x_11)[(Bit#(2))'(2'h0)]).value}) :
        (((((x_11)[(Bit#(2))'(2'h1)]).tag) == (x_1) ? (Struct46 {tm_hit :
        (Bool)'(True), tm_way : (Bit#(2))'(2'h1), tm_value :
        ((x_11)[(Bit#(2))'(2'h1)]).value}) :
        (((((x_11)[(Bit#(2))'(2'h2)]).tag) == (x_1) ? (Struct46 {tm_hit :
        (Bool)'(True), tm_way : (Bit#(2))'(2'h2), tm_value :
        ((x_11)[(Bit#(2))'(2'h2)]).value}) :
        (((((x_11)[(Bit#(2))'(2'h3)]).tag) == (x_1) ? (Struct46 {tm_hit :
        (Bool)'(True), tm_way : (Bit#(2))'(2'h3), tm_value :
        ((x_11)[(Bit#(2))'(2'h3)]).value}) : (unpack(0))))))))));
        let x_13 <- repGetRs__001();
        Bit#(2) x_14 = (unpack(0));
        Bit#(8) x_15 = (unpack(0));
        Bit#(2) x_16 = ((! (((x_13)[(Bit#(2))'(2'h3)]) < (x_15)) ?
        ((Bit#(2))'(2'h3)) : (x_14)));
        Bit#(8) x_17 = ((! (((x_13)[(Bit#(2))'(2'h3)]) < (x_15)) ?
        ((x_13)[(Bit#(2))'(2'h3)]) : (x_15)));
        Bit#(2) x_18 = ((! (((x_13)[(Bit#(2))'(2'h2)]) < (x_17)) ?
        ((Bit#(2))'(2'h2)) : (x_16)));
        Bit#(8) x_19 = ((! (((x_13)[(Bit#(2))'(2'h2)]) < (x_17)) ?
        ((x_13)[(Bit#(2))'(2'h2)]) : (x_17)));
        Bit#(2) x_20 = ((! (((x_13)[(Bit#(2))'(2'h1)]) < (x_19)) ?
        ((Bit#(2))'(2'h1)) : (x_18)));
        Bit#(8) x_21 = ((! (((x_13)[(Bit#(2))'(2'h1)]) < (x_19)) ?
        ((x_13)[(Bit#(2))'(2'h1)]) : (x_19)));
        Bit#(2) x_22 = ((! (((x_13)[(Bit#(2))'(2'h0)]) < (x_21)) ?
        ((Bit#(2))'(2'h0)) : (x_20)));
        Bit#(8) x_23 = ((! (((x_13)[(Bit#(2))'(2'h0)]) < (x_21)) ?
        ((x_13)[(Bit#(2))'(2'h0)]) : (x_21)));
        when (! ((x_23) == ((Bit#(8))'(8'h0))), noAction);
        Struct45 x_24 = ((x_11)[x_22]);
        Bit#(51) x_25 = ((x_24).tag);
        Struct10 x_26 = ((x_24).value);
        Bit#(2) x_27 = (((x_12).tm_hit ? ((x_12).tm_way) : (x_22)));
        Struct39 x_28 = (Struct39 {info_index : x_2, info_hit :
        (x_12).tm_hit, info_way : x_27, edir_hit : unpack(0), edir_way :
        unpack(0), edir_slot : unpack(0), info : (x_12).tm_value, may_victim
        : Struct11 {mv_addr : {(x_25),({(x_2),((Bit#(5))'(5'h0))})}, mv_info
        : x_26}, reps : x_13});
        let x_29 <- rdReq_dataRam__001({(x_27),(x_2)});
        return x_28;
    endmethod

    method ActionValue#(Vector#(4, Bit#(64))) cache__001__valueRsLineRq
    (Struct42 x_0);
        let x_1 <- rdResp_dataRam__001();
        Bit#(64) x_2 = ((x_0).addr);
        Bit#(8) x_3 = ((x_2)[12:5]);
        Bit#(2) x_4 = ((x_0).info_way);
        Struct10 x_5 =
        ((x_0).info);
        if ((x_0).info_write) begin
            Struct47 x_6 = (Struct47 {addr : x_3, datain : Struct45 {tag :
            (x_2)[63:13], value :
            x_5}});
            if ((x_4) == ((Bit#(2))'(2'h0))) begin
                let x_7 <- wrReq_infoRam__001__0(x_6);
            end else begin

            end
            if ((x_4) == ((Bit#(2))'(2'h1))) begin
                let x_9 <- wrReq_infoRam__001__1(x_6);
            end else begin

            end
            if ((x_4) == ((Bit#(2))'(2'h2))) begin
                let x_11 <- wrReq_infoRam__001__2(x_6);
            end else begin

            end
            if ((x_4) == ((Bit#(2))'(2'h3))) begin
                let x_13 <- wrReq_infoRam__001__3(x_6);
            end else begin

            end
            if (! ((x_0).info_hit)) begin
                Struct11 x_15 = ((x_0).may_victim);
                Struct13 x_16 = (Struct13 {victim_valid : (Bool)'(True),
                victim_addr : (x_15).mv_addr, victim_info : (x_15).mv_info,
                victim_value : x_1, victim_req : (Bool)'(False)});
                let x_17 <- victims__001__registerVictim(x_16);
            end else begin

            end
            let x_19 <- repAccess__001(Struct48 {acc_type : (!
            (((Bit#(3))'(3'h1)) < ((x_5).mesi_dir_st)) ? ((Bit#(1))'(1'h0)) :
            ((Bit#(1))'(1'h1))), acc_reps : (x_0).reps, acc_index : x_3,
            acc_way : x_4});
        end else begin

        end
        if ((x_0).value_write) begin
            Struct49 x_21 = (Struct49 {addr : {(x_4),((x_2)[12:5])}, datain :
            (x_0).value});
            let x_22 <- wrReq_dataRam__001(x_21);
        end else begin

        end
        return x_1;
    endmethod
endmodule

interface Module131;
    method Action cache__002__infoRq (Bit#(64) x_0);
    method ActionValue#(Struct39) cache__002__infoRsValueRq (Bit#(64) x_0);
    method ActionValue#(Vector#(4, Bit#(64))) cache__002__valueRsLineRq
    (Struct42 x_0);
endinterface

module mkModule131#(function Action wrReq_dataRam__002(Struct49 _),
    function Action repAccess__002(Struct48 _),
    function Action victims__002__registerVictim(Struct13 _),
    function Action wrReq_infoRam__002__3(Struct47 _),
    function Action wrReq_infoRam__002__2(Struct47 _),
    function Action wrReq_infoRam__002__1(Struct47 _),
    function Action wrReq_infoRam__002__0(Struct47 _),
    function ActionValue#(Vector#(4, Bit#(64))) rdResp_dataRam__002(),
    function Action rdReq_dataRam__002(Bit#(10) _),
    function ActionValue#(Vector#(4, Bit#(8))) repGetRs__002(),
    function ActionValue#(Struct45) rdResp_infoRam__002__3(),
    function ActionValue#(Struct45) rdResp_infoRam__002__2(),
    function ActionValue#(Struct45) rdResp_infoRam__002__1(),
    function ActionValue#(Struct45) rdResp_infoRam__002__0(),
    function Action repGetRq__002(Bit#(8) _),
    function Action rdReq_infoRam__002__3(Bit#(8) _),
    function Action rdReq_infoRam__002__2(Bit#(8) _),
    function Action rdReq_infoRam__002__1(Bit#(8) _),
    function Action rdReq_infoRam__002__0(Bit#(8) _))
    (Module131);

    // No rules in this module

    method Action cache__002__infoRq (Bit#(64) x_0);
        Bit#(8) x_1 = ((x_0)[12:5]);
        let x_2 <- rdReq_infoRam__002__0(x_1);
        let x_3 <- rdReq_infoRam__002__1(x_1);
        let x_4 <- rdReq_infoRam__002__2(x_1);
        let x_5 <- rdReq_infoRam__002__3(x_1);
        let x_6 <- repGetRq__002(x_1);
    endmethod

    method ActionValue#(Struct39) cache__002__infoRsValueRq (Bit#(64) x_0);
        Bit#(51) x_1 = ((x_0)[63:13]);
        Bit#(8) x_2 = ((x_0)[12:5]);
        Vector#(4, Struct45) x_3 = (unpack(0));
        let x_4 <- rdResp_infoRam__002__0();
        Vector#(4, Struct45) x_5 = (update (x_3, (Bit#(2))'(2'h0), x_4));
        let x_6 <- rdResp_infoRam__002__1();
        Vector#(4, Struct45) x_7 = (update (x_5, (Bit#(2))'(2'h1), x_6));
        let x_8 <- rdResp_infoRam__002__2();
        Vector#(4, Struct45) x_9 = (update (x_7, (Bit#(2))'(2'h2), x_8));
        let x_10 <- rdResp_infoRam__002__3();
        Vector#(4, Struct45) x_11 = (update (x_9, (Bit#(2))'(2'h3),
        x_10));
        Struct46 x_12 = (((((x_11)[(Bit#(2))'(2'h0)]).tag) == (x_1) ?
        (Struct46 {tm_hit : (Bool)'(True), tm_way : (Bit#(2))'(2'h0),
        tm_value : ((x_11)[(Bit#(2))'(2'h0)]).value}) :
        (((((x_11)[(Bit#(2))'(2'h1)]).tag) == (x_1) ? (Struct46 {tm_hit :
        (Bool)'(True), tm_way : (Bit#(2))'(2'h1), tm_value :
        ((x_11)[(Bit#(2))'(2'h1)]).value}) :
        (((((x_11)[(Bit#(2))'(2'h2)]).tag) == (x_1) ? (Struct46 {tm_hit :
        (Bool)'(True), tm_way : (Bit#(2))'(2'h2), tm_value :
        ((x_11)[(Bit#(2))'(2'h2)]).value}) :
        (((((x_11)[(Bit#(2))'(2'h3)]).tag) == (x_1) ? (Struct46 {tm_hit :
        (Bool)'(True), tm_way : (Bit#(2))'(2'h3), tm_value :
        ((x_11)[(Bit#(2))'(2'h3)]).value}) : (unpack(0))))))))));
        let x_13 <- repGetRs__002();
        Bit#(2) x_14 = (unpack(0));
        Bit#(8) x_15 = (unpack(0));
        Bit#(2) x_16 = ((! (((x_13)[(Bit#(2))'(2'h3)]) < (x_15)) ?
        ((Bit#(2))'(2'h3)) : (x_14)));
        Bit#(8) x_17 = ((! (((x_13)[(Bit#(2))'(2'h3)]) < (x_15)) ?
        ((x_13)[(Bit#(2))'(2'h3)]) : (x_15)));
        Bit#(2) x_18 = ((! (((x_13)[(Bit#(2))'(2'h2)]) < (x_17)) ?
        ((Bit#(2))'(2'h2)) : (x_16)));
        Bit#(8) x_19 = ((! (((x_13)[(Bit#(2))'(2'h2)]) < (x_17)) ?
        ((x_13)[(Bit#(2))'(2'h2)]) : (x_17)));
        Bit#(2) x_20 = ((! (((x_13)[(Bit#(2))'(2'h1)]) < (x_19)) ?
        ((Bit#(2))'(2'h1)) : (x_18)));
        Bit#(8) x_21 = ((! (((x_13)[(Bit#(2))'(2'h1)]) < (x_19)) ?
        ((x_13)[(Bit#(2))'(2'h1)]) : (x_19)));
        Bit#(2) x_22 = ((! (((x_13)[(Bit#(2))'(2'h0)]) < (x_21)) ?
        ((Bit#(2))'(2'h0)) : (x_20)));
        Bit#(8) x_23 = ((! (((x_13)[(Bit#(2))'(2'h0)]) < (x_21)) ?
        ((x_13)[(Bit#(2))'(2'h0)]) : (x_21)));
        when (! ((x_23) == ((Bit#(8))'(8'h0))), noAction);
        Struct45 x_24 = ((x_11)[x_22]);
        Bit#(51) x_25 = ((x_24).tag);
        Struct10 x_26 = ((x_24).value);
        Bit#(2) x_27 = (((x_12).tm_hit ? ((x_12).tm_way) : (x_22)));
        Struct39 x_28 = (Struct39 {info_index : x_2, info_hit :
        (x_12).tm_hit, info_way : x_27, edir_hit : unpack(0), edir_way :
        unpack(0), edir_slot : unpack(0), info : (x_12).tm_value, may_victim
        : Struct11 {mv_addr : {(x_25),({(x_2),((Bit#(5))'(5'h0))})}, mv_info
        : x_26}, reps : x_13});
        let x_29 <- rdReq_dataRam__002({(x_27),(x_2)});
        return x_28;
    endmethod

    method ActionValue#(Vector#(4, Bit#(64))) cache__002__valueRsLineRq
    (Struct42 x_0);
        let x_1 <- rdResp_dataRam__002();
        Bit#(64) x_2 = ((x_0).addr);
        Bit#(8) x_3 = ((x_2)[12:5]);
        Bit#(2) x_4 = ((x_0).info_way);
        Struct10 x_5 =
        ((x_0).info);
        if ((x_0).info_write) begin
            Struct47 x_6 = (Struct47 {addr : x_3, datain : Struct45 {tag :
            (x_2)[63:13], value :
            x_5}});
            if ((x_4) == ((Bit#(2))'(2'h0))) begin
                let x_7 <- wrReq_infoRam__002__0(x_6);
            end else begin

            end
            if ((x_4) == ((Bit#(2))'(2'h1))) begin
                let x_9 <- wrReq_infoRam__002__1(x_6);
            end else begin

            end
            if ((x_4) == ((Bit#(2))'(2'h2))) begin
                let x_11 <- wrReq_infoRam__002__2(x_6);
            end else begin

            end
            if ((x_4) == ((Bit#(2))'(2'h3))) begin
                let x_13 <- wrReq_infoRam__002__3(x_6);
            end else begin

            end
            if (! ((x_0).info_hit)) begin
                Struct11 x_15 = ((x_0).may_victim);
                Struct13 x_16 = (Struct13 {victim_valid : (Bool)'(True),
                victim_addr : (x_15).mv_addr, victim_info : (x_15).mv_info,
                victim_value : x_1, victim_req : (Bool)'(False)});
                let x_17 <- victims__002__registerVictim(x_16);
            end else begin

            end
            let x_19 <- repAccess__002(Struct48 {acc_type : (!
            (((Bit#(3))'(3'h1)) < ((x_5).mesi_dir_st)) ? ((Bit#(1))'(1'h0)) :
            ((Bit#(1))'(1'h1))), acc_reps : (x_0).reps, acc_index : x_3,
            acc_way : x_4});
        end else begin

        end
        if ((x_0).value_write) begin
            Struct49 x_21 = (Struct49 {addr : {(x_4),((x_2)[12:5])}, datain :
            (x_0).value});
            let x_22 <- wrReq_dataRam__002(x_21);
        end else begin

        end
        return x_1;
    endmethod
endmodule

interface Module132;
    method Action cache__003__infoRq (Bit#(64) x_0);
    method ActionValue#(Struct39) cache__003__infoRsValueRq (Bit#(64) x_0);
    method ActionValue#(Vector#(4, Bit#(64))) cache__003__valueRsLineRq
    (Struct42 x_0);
endinterface

module mkModule132#(function Action wrReq_dataRam__003(Struct49 _),
    function Action repAccess__003(Struct48 _),
    function Action victims__003__registerVictim(Struct13 _),
    function Action wrReq_infoRam__003__3(Struct47 _),
    function Action wrReq_infoRam__003__2(Struct47 _),
    function Action wrReq_infoRam__003__1(Struct47 _),
    function Action wrReq_infoRam__003__0(Struct47 _),
    function ActionValue#(Vector#(4, Bit#(64))) rdResp_dataRam__003(),
    function Action rdReq_dataRam__003(Bit#(10) _),
    function ActionValue#(Vector#(4, Bit#(8))) repGetRs__003(),
    function ActionValue#(Struct45) rdResp_infoRam__003__3(),
    function ActionValue#(Struct45) rdResp_infoRam__003__2(),
    function ActionValue#(Struct45) rdResp_infoRam__003__1(),
    function ActionValue#(Struct45) rdResp_infoRam__003__0(),
    function Action repGetRq__003(Bit#(8) _),
    function Action rdReq_infoRam__003__3(Bit#(8) _),
    function Action rdReq_infoRam__003__2(Bit#(8) _),
    function Action rdReq_infoRam__003__1(Bit#(8) _),
    function Action rdReq_infoRam__003__0(Bit#(8) _))
    (Module132);

    // No rules in this module

    method Action cache__003__infoRq (Bit#(64) x_0);
        Bit#(8) x_1 = ((x_0)[12:5]);
        let x_2 <- rdReq_infoRam__003__0(x_1);
        let x_3 <- rdReq_infoRam__003__1(x_1);
        let x_4 <- rdReq_infoRam__003__2(x_1);
        let x_5 <- rdReq_infoRam__003__3(x_1);
        let x_6 <- repGetRq__003(x_1);
    endmethod

    method ActionValue#(Struct39) cache__003__infoRsValueRq (Bit#(64) x_0);
        Bit#(51) x_1 = ((x_0)[63:13]);
        Bit#(8) x_2 = ((x_0)[12:5]);
        Vector#(4, Struct45) x_3 = (unpack(0));
        let x_4 <- rdResp_infoRam__003__0();
        Vector#(4, Struct45) x_5 = (update (x_3, (Bit#(2))'(2'h0), x_4));
        let x_6 <- rdResp_infoRam__003__1();
        Vector#(4, Struct45) x_7 = (update (x_5, (Bit#(2))'(2'h1), x_6));
        let x_8 <- rdResp_infoRam__003__2();
        Vector#(4, Struct45) x_9 = (update (x_7, (Bit#(2))'(2'h2), x_8));
        let x_10 <- rdResp_infoRam__003__3();
        Vector#(4, Struct45) x_11 = (update (x_9, (Bit#(2))'(2'h3),
        x_10));
        Struct46 x_12 = (((((x_11)[(Bit#(2))'(2'h0)]).tag) == (x_1) ?
        (Struct46 {tm_hit : (Bool)'(True), tm_way : (Bit#(2))'(2'h0),
        tm_value : ((x_11)[(Bit#(2))'(2'h0)]).value}) :
        (((((x_11)[(Bit#(2))'(2'h1)]).tag) == (x_1) ? (Struct46 {tm_hit :
        (Bool)'(True), tm_way : (Bit#(2))'(2'h1), tm_value :
        ((x_11)[(Bit#(2))'(2'h1)]).value}) :
        (((((x_11)[(Bit#(2))'(2'h2)]).tag) == (x_1) ? (Struct46 {tm_hit :
        (Bool)'(True), tm_way : (Bit#(2))'(2'h2), tm_value :
        ((x_11)[(Bit#(2))'(2'h2)]).value}) :
        (((((x_11)[(Bit#(2))'(2'h3)]).tag) == (x_1) ? (Struct46 {tm_hit :
        (Bool)'(True), tm_way : (Bit#(2))'(2'h3), tm_value :
        ((x_11)[(Bit#(2))'(2'h3)]).value}) : (unpack(0))))))))));
        let x_13 <- repGetRs__003();
        Bit#(2) x_14 = (unpack(0));
        Bit#(8) x_15 = (unpack(0));
        Bit#(2) x_16 = ((! (((x_13)[(Bit#(2))'(2'h3)]) < (x_15)) ?
        ((Bit#(2))'(2'h3)) : (x_14)));
        Bit#(8) x_17 = ((! (((x_13)[(Bit#(2))'(2'h3)]) < (x_15)) ?
        ((x_13)[(Bit#(2))'(2'h3)]) : (x_15)));
        Bit#(2) x_18 = ((! (((x_13)[(Bit#(2))'(2'h2)]) < (x_17)) ?
        ((Bit#(2))'(2'h2)) : (x_16)));
        Bit#(8) x_19 = ((! (((x_13)[(Bit#(2))'(2'h2)]) < (x_17)) ?
        ((x_13)[(Bit#(2))'(2'h2)]) : (x_17)));
        Bit#(2) x_20 = ((! (((x_13)[(Bit#(2))'(2'h1)]) < (x_19)) ?
        ((Bit#(2))'(2'h1)) : (x_18)));
        Bit#(8) x_21 = ((! (((x_13)[(Bit#(2))'(2'h1)]) < (x_19)) ?
        ((x_13)[(Bit#(2))'(2'h1)]) : (x_19)));
        Bit#(2) x_22 = ((! (((x_13)[(Bit#(2))'(2'h0)]) < (x_21)) ?
        ((Bit#(2))'(2'h0)) : (x_20)));
        Bit#(8) x_23 = ((! (((x_13)[(Bit#(2))'(2'h0)]) < (x_21)) ?
        ((x_13)[(Bit#(2))'(2'h0)]) : (x_21)));
        when (! ((x_23) == ((Bit#(8))'(8'h0))), noAction);
        Struct45 x_24 = ((x_11)[x_22]);
        Bit#(51) x_25 = ((x_24).tag);
        Struct10 x_26 = ((x_24).value);
        Bit#(2) x_27 = (((x_12).tm_hit ? ((x_12).tm_way) : (x_22)));
        Struct39 x_28 = (Struct39 {info_index : x_2, info_hit :
        (x_12).tm_hit, info_way : x_27, edir_hit : unpack(0), edir_way :
        unpack(0), edir_slot : unpack(0), info : (x_12).tm_value, may_victim
        : Struct11 {mv_addr : {(x_25),({(x_2),((Bit#(5))'(5'h0))})}, mv_info
        : x_26}, reps : x_13});
        let x_29 <- rdReq_dataRam__003({(x_27),(x_2)});
        return x_28;
    endmethod

    method ActionValue#(Vector#(4, Bit#(64))) cache__003__valueRsLineRq
    (Struct42 x_0);
        let x_1 <- rdResp_dataRam__003();
        Bit#(64) x_2 = ((x_0).addr);
        Bit#(8) x_3 = ((x_2)[12:5]);
        Bit#(2) x_4 = ((x_0).info_way);
        Struct10 x_5 =
        ((x_0).info);
        if ((x_0).info_write) begin
            Struct47 x_6 = (Struct47 {addr : x_3, datain : Struct45 {tag :
            (x_2)[63:13], value :
            x_5}});
            if ((x_4) == ((Bit#(2))'(2'h0))) begin
                let x_7 <- wrReq_infoRam__003__0(x_6);
            end else begin

            end
            if ((x_4) == ((Bit#(2))'(2'h1))) begin
                let x_9 <- wrReq_infoRam__003__1(x_6);
            end else begin

            end
            if ((x_4) == ((Bit#(2))'(2'h2))) begin
                let x_11 <- wrReq_infoRam__003__2(x_6);
            end else begin

            end
            if ((x_4) == ((Bit#(2))'(2'h3))) begin
                let x_13 <- wrReq_infoRam__003__3(x_6);
            end else begin

            end
            if (! ((x_0).info_hit)) begin
                Struct11 x_15 = ((x_0).may_victim);
                Struct13 x_16 = (Struct13 {victim_valid : (Bool)'(True),
                victim_addr : (x_15).mv_addr, victim_info : (x_15).mv_info,
                victim_value : x_1, victim_req : (Bool)'(False)});
                let x_17 <- victims__003__registerVictim(x_16);
            end else begin

            end
            let x_19 <- repAccess__003(Struct48 {acc_type : (!
            (((Bit#(3))'(3'h1)) < ((x_5).mesi_dir_st)) ? ((Bit#(1))'(1'h0)) :
            ((Bit#(1))'(1'h1))), acc_reps : (x_0).reps, acc_index : x_3,
            acc_way : x_4});
        end else begin

        end
        if ((x_0).value_write) begin
            Struct49 x_21 = (Struct49 {addr : {(x_4),((x_2)[12:5])}, datain :
            (x_0).value});
            let x_22 <- wrReq_dataRam__003(x_21);
        end else begin

        end
        return x_1;
    endmethod
endmodule

interface Module133;

endinterface

module mkModule133#(function Action canImm_00(Bit#(64) _),
    function Action victims__00__setVictimRq(Bit#(64) _),
    function Action setULImm_00(Struct1 _),
    function ActionValue#(Struct13) victims__00__getFirstVictim(),
    function Action transferUpDown_00(Struct23 _),
    function ActionValue#(Struct1) getMSHRFirstRs_00(Bit#(3) _),
    function Action broadcast_parentChildren00(Struct21 _),
    function Action registerDL_00(Struct20 _),
    function Action registerUL_00(Struct19 _),
    function Action makeEnq_parentChildren00(Struct18 _),
    function ActionValue#(Vector#(4, Bit#(64))) cache__00__valueRsLineRq(Struct16 _),
    function Action victims__00__setVictim(Struct17 _),
    function ActionValue#(Struct1) getMSHRRq_00(Bit#(3) _),
    function ActionValue#(Struct14) getMSHR_00(Bit#(3) _),
    function ActionValue#(Struct12) deq_fifoL2E_00(),
    function ActionValue#(Struct13) victims__00__getVictim(Bit#(3) _),
    function Action enq_fifoL2E_00(Struct12 _),
    function ActionValue#(Struct9) cache__00__infoRsValueRq(Bit#(64) _),
    function ActionValue#(Struct6) deq_fifoI2L_00(),
    function Action enq_fifoI2L_00(Struct6 _),
    function Action cache__00__infoRq(Bit#(64) _),
    function ActionValue#(Struct6) deq_fifoN2I_00(),
    function ActionValue#(Struct8) getDLReady_00(),
    function Action addRs_00(Struct7 _),
    function ActionValue#(Struct2) deq_fifoCRsInput_00(),
    function ActionValue#(Struct4) getCRqSlot_00(Struct3 _),
    function ActionValue#(Bool) victims__00__hasVictim(),
    function ActionValue#(Struct2) deq_fifoCRqInput_00(),
    function Action releaseMSHR_00(Bit#(3) _),
    function Action victims__00__releaseVictim(Bit#(64) _),
    function ActionValue#(Struct3) getWait_00(),
    function Action startRelease_00(Bit#(3) _),
    function ActionValue#(Bit#(3)) getULReady_00(Bit#(64) _),
    function Action enq_fifoN2I_00(Struct6 _),
    function ActionValue#(Struct5) victims__00__findVictim(Bit#(64) _),
    function ActionValue#(Struct4) getPRqSlot_00(Struct3 _),
    function ActionValue#(Struct2) deq_fifoPInput_00())
    (Module133);

    rule rule_in_prq_00;
        let x_0 <- deq_fifoPInput_00();
        Bit#(4) x_1 = ((x_0).in_msg_from);
        when ((x_1) == ({((Bit#(2))'(2'h2)),((Bit#(2))'(2'h0))}),
        noAction);
        Struct1 x_2 = ((x_0).in_msg);
        when (! ((x_2).type_), noAction);
        let x_3 <- getPRqSlot_00(Struct3 {r_id : unpack(0), r_msg : x_2,
        r_msg_from : (x_0).in_msg_from});
        when ((x_3).s_has_slot,
        noAction);
        if (! ((x_3).s_conflict)) begin
            let x_4 <- victims__00__findVictim((x_2).addr);
            Struct6 x_5 = (Struct6 {ir_is_rs_rel : (Bool)'(False), ir_msg :
            (x_0).in_msg, ir_msg_from : x_1, ir_mshr_id : (x_3).s_id,
            ir_by_victim : x_4});
            let x_6 <- enq_fifoN2I_00(x_5);
        end else begin

        end
    endrule

    rule rule_in_prs_00;
        let x_0 <- deq_fifoPInput_00();
        Bit#(4) x_1 = ((x_0).in_msg_from);
        when ((x_1) == ({((Bit#(2))'(2'h2)),((Bit#(2))'(2'h0))}),
        noAction);
        Struct1 x_2 = ((x_0).in_msg);
        when (((x_2).type_) && (! (((x_2).id) == ((Bit#(6))'(6'h16)))),
        noAction);
        let x_3 <- getULReady_00((x_2).addr);
        let x_4 <- startRelease_00(x_3);
        let x_5 <- victims__00__findVictim((x_2).addr);
        Struct6 x_6 = (Struct6 {ir_is_rs_rel : (Bool)'(False), ir_msg :
        (x_0).in_msg, ir_msg_from : x_1, ir_mshr_id : x_3, ir_by_victim :
        x_5});
        let x_7 <- enq_fifoN2I_00(x_6);
    endrule

    rule rule_in_retry_00;
        let x_0 <- getWait_00();
        Struct1 x_1 = ((x_0).r_msg);
        let x_2 <- victims__00__findVictim((x_1).addr);
        Struct6 x_3 = (Struct6 {ir_is_rs_rel : (Bool)'(False), ir_msg : x_1,
        ir_msg_from : (x_0).r_msg_from, ir_mshr_id : (x_0).r_id, ir_by_victim
        : x_2});
        let x_4 <- enq_fifoN2I_00(x_3);
    endrule

    rule rule_in_invrs_00;
        let x_0 <- deq_fifoPInput_00();
        Bit#(4) x_1 = ((x_0).in_msg_from);
        when ((x_1) == ({((Bit#(2))'(2'h2)),((Bit#(2))'(2'h0))}),
        noAction);
        Struct1 x_2 = ((x_0).in_msg);
        when (((x_2).type_) && (((x_2).id) == ((Bit#(6))'(6'h16))),
        noAction);
        let x_3 <- getULReady_00((x_2).addr);
        let x_4 <- victims__00__releaseVictim((x_2).addr);
        let x_5 <- releaseMSHR_00(x_3);
    endrule

    rule rule_in_crq_00;
        let x_0 <- deq_fifoCRqInput_00();
        Bit#(4) x_1 = ((x_0).in_msg_from);
        when (((x_1)[3:2]) == ((Bit#(2))'(2'h0)), noAction);
        Struct1 x_2 = ((x_0).in_msg);
        when (! ((x_2).type_), noAction);
        let x_3 <- victims__00__hasVictim();
        when (! (x_3), noAction);
        let x_4 <- getCRqSlot_00(Struct3 {r_id : unpack(0), r_msg : x_2,
        r_msg_from : x_1});
        when ((x_4).s_has_slot,
        noAction);
        if (! ((x_4).s_conflict)) begin
            let x_5 <- victims__00__findVictim((x_2).addr);
            Struct6 x_6 = (Struct6 {ir_is_rs_rel : (Bool)'(False), ir_msg :
            (x_0).in_msg, ir_msg_from : x_1, ir_mshr_id : (x_4).s_id,
            ir_by_victim : x_5});
            let x_7 <- enq_fifoN2I_00(x_6);
        end else begin

        end
    endrule

    rule rule_in_crs_00;
        let x_0 <- deq_fifoCRsInput_00();
        Bit#(4) x_1 = ((x_0).in_msg_from);
        when (((x_1)[3:2]) == ((Bit#(2))'(2'h1)), noAction);
        Struct1 x_2 = ((x_0).in_msg);
        when ((x_2).type_, noAction);
        let x_3 <- addRs_00(Struct7 {r_midx : (x_1)[1:0], r_msg : x_2});
    endrule

    rule rule_in_rsrel_00;
        let x_0 <- getDLReady_00();
        let x_1 <- startRelease_00((x_0).r_id);
        Struct1 x_2 = (Struct1 {id : unpack(0), type_ : unpack(0), addr :
        (x_0).r_addr, value : unpack(0)});
        Struct6 x_3 = (Struct6 {ir_is_rs_rel : (Bool)'(True), ir_msg : x_2,
        ir_msg_from : unpack(0), ir_mshr_id : (x_0).r_id, ir_by_victim :
        Struct5 {valid : (Bool)'(False), data : unpack(0)}});
        let x_4 <- enq_fifoN2I_00(x_3);
    endrule

    rule rule_ir_cache_00;
        let x_0 <- deq_fifoN2I_00();
        when (! (((x_0).ir_by_victim).valid), noAction);
        Struct1 x_1 = ((x_0).ir_msg);
        let x_2 <- cache__00__infoRq((x_1).addr);
        let x_3 <- enq_fifoI2L_00(x_0);
    endrule

    rule rule_ir_victims_00;
        let x_0 <- deq_fifoN2I_00();
        when (((x_0).ir_by_victim).valid, noAction);
        let x_1 <- enq_fifoI2L_00(x_0);
    endrule

    rule rule_lr_cache_00;
        let x_0 <- deq_fifoI2L_00();
        when (! (((x_0).ir_by_victim).valid), noAction);
        let x_1 <- cache__00__infoRsValueRq(((x_0).ir_msg).addr);
        Struct12 x_2 = (Struct12 {lr_ir_pp : x_0, lr_ir : x_1, lr_value :
        unpack(0)});
        let x_3 <- enq_fifoL2E_00(x_2);
    endrule

    rule rule_lr_victims_00;
        let x_0 <- deq_fifoI2L_00();
        when (((x_0).ir_by_victim).valid, noAction);
        Bit#(3) x_1 = (((x_0).ir_by_victim).data);
        let x_2 <- victims__00__getVictim(x_1);
        Struct9 x_3 = (Struct9 {info_index : unpack(0), info_hit : unpack(0),
        info_way : unpack(0), edir_hit : unpack(0), edir_way : unpack(0),
        edir_slot : unpack(0), info : (x_2).victim_info, may_victim :
        unpack(0), reps : unpack(0)});
        Struct12 x_4 = (Struct12 {lr_ir_pp : x_0, lr_ir : x_3, lr_value :
        (x_2).victim_value});
        let x_5 <- enq_fifoL2E_00(x_4);
    endrule

    rule rule_exec_00_000000;
        let x_0 <- deq_fifoL2E_00();
        Struct6 x_1 = ((x_0).lr_ir_pp);
        Bit#(4) x_2 = ((x_1).ir_msg_from);
        Struct1 x_3 = ((x_1).ir_msg);
        Bit#(3) x_4 = ((x_1).ir_mshr_id);
        Bool x_5 = ((x_1).ir_is_rs_rel);
        when (! (x_5), noAction);
        Struct9 x_6 = ((x_0).lr_ir);
        Struct10 x_7 = ((x_6).info);
        Struct5 x_8 = ((x_1).ir_by_victim);
        Vector#(4, Bit#(64)) x_9 = ((x_0).lr_value);
        let x_10 <- getMSHR_00(x_4);
        let x_11 <- getMSHRRq_00(x_4);
        Struct1 x_12 = (unpack(0));
        Vector#(4, Bit#(64)) x_13 = (unpack(0));
        Bool x_14 = ((x_7).mesi_owned);
        Bit#(3) x_15 = ((x_7).mesi_status);
        Struct15 x_16 = (Struct15 {dir_st : (((x_7).mesi_dir_st) ==
        ((Bit#(3))'(3'h0)) ? ((Bit#(3))'(3'h1)) : ((x_7).mesi_dir_st)),
        dir_excl : ((((x_7).mesi_dir_sharers)[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        ((((((x_7).mesi_dir_sharers)[3:1])[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        (((((((x_7).mesi_dir_sharers)[3:1])[2:1])[0:0]) == ((Bit#(1))'(1'h1))
        ? ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        ((((((((x_7).mesi_dir_sharers)[3:1])[2:1])[1:1])[0:0]) ==
        ((Bit#(1))'(1'h1)) ? ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        (unpack(0))))))))))))), dir_sharers : (x_7).mesi_dir_sharers});
        when ((x_2) == ((Bit#(4))'(4'h0)), noAction);
        when (((x_3).id) == ((Bit#(6))'(6'h2)), noAction);
        when (! ((x_3).type_), noAction);
        when ((! (((Bit#(3))'(3'h2)) < ((x_16).dir_st))) && ((x_15) ==
        ((Bit#(3))'(3'h2))), noAction);
        Struct1 x_17 = (x_3);
        Struct16 x_18 = (Struct16 {addr : (x_3).addr, info_write :
        (Bool)'(False), info_hit : (x_6).info_hit, info_way : (x_6).info_way,
        edir_hit : (x_6).edir_hit, edir_way : (x_6).edir_way, edir_slot :
        (x_6).edir_slot, info : (x_6).info, value_write : (Bool)'(False),
        value : unpack(0), may_victim : (x_6).may_victim, reps :
        (x_6).reps});
        Struct16 x_19 = (Struct16 {addr : (x_18).addr, info_write :
        (Bool)'(True), info_hit : (x_18).info_hit, info_way :
        (x_18).info_way, edir_hit : (x_18).edir_hit, edir_way :
        (x_18).edir_way, edir_slot : (x_18).edir_slot, info : Struct10
        {mesi_owned : ((x_18).info).mesi_owned, mesi_status :
        ((x_18).info).mesi_status, mesi_dir_st : (Struct15 {dir_st :
        (Bit#(3))'(3'h2), dir_excl : (x_16).dir_excl, dir_sharers :
        (((x_16).dir_st) == ((Bit#(3))'(3'h2)) ? (((x_16).dir_sharers) |
        (((Bit#(4))'(4'h1)) << ((Bit#(2))'(2'h0)))) : (((Bit#(4))'(4'h1)) <<
        ((Bit#(2))'(2'h0))))}).dir_st, mesi_dir_sharers : (((Struct15 {dir_st
        : (Bit#(3))'(3'h2), dir_excl : (x_16).dir_excl, dir_sharers :
        (((x_16).dir_st) == ((Bit#(3))'(3'h2)) ? (((x_16).dir_sharers) |
        (((Bit#(4))'(4'h1)) << ((Bit#(2))'(2'h0)))) : (((Bit#(4))'(4'h1)) <<
        ((Bit#(2))'(2'h0))))}).dir_st) == ((Bit#(3))'(3'h2)) ? ((Struct15
        {dir_st : (Bit#(3))'(3'h2), dir_excl : (x_16).dir_excl, dir_sharers :
        (((x_16).dir_st) == ((Bit#(3))'(3'h2)) ? (((x_16).dir_sharers) |
        (((Bit#(4))'(4'h1)) << ((Bit#(2))'(2'h0)))) : (((Bit#(4))'(4'h1)) <<
        ((Bit#(2))'(2'h0))))}).dir_sharers) : (((Bit#(4))'(4'h1)) <<
        ((Struct15 {dir_st : (Bit#(3))'(3'h2), dir_excl : (x_16).dir_excl,
        dir_sharers : (((x_16).dir_st) == ((Bit#(3))'(3'h2)) ?
        (((x_16).dir_sharers) | (((Bit#(4))'(4'h1)) << ((Bit#(2))'(2'h0)))) :
        (((Bit#(4))'(4'h1)) << ((Bit#(2))'(2'h0))))}).dir_excl)))},
        value_write : (x_18).value_write, value : (x_18).value, may_victim :
        (x_18).may_victim, reps :
        (x_18).reps});
        let x_22 = ?;
        if ((x_8).valid) begin
            let x_20 <- victims__00__setVictim(Struct17 {victim_idx :
            (x_8).data, victim_info : (x_19).info, victim_value :
            ((x_19).value_write ? ((x_19).value) : (x_9))});
            x_22 = x_9;
        end else begin
            let x_21 <- cache__00__valueRsLineRq(x_19);
            x_22 = x_21;
        end
        Struct18 x_23 = (Struct18 {enq_type : ((((Bit#(4))'(4'h8))[3:2]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : (((((Bit#(4))'(4'h8))[3:2])
        == ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : ((Bit#(4))'(4'h8))[1:0], enq_msg : Struct1 {id :
        (Bit#(6))'(6'h3), type_ : (Bool)'(True), addr : (x_17).addr, value :
        x_22}});
        let x_24 <- makeEnq_parentChildren00(x_23);
        let x_25 <- releaseMSHR_00(x_4);
    endrule

    rule rule_exec_00_001000;
        let x_0 <- deq_fifoL2E_00();
        Struct6 x_1 = ((x_0).lr_ir_pp);
        Bit#(4) x_2 = ((x_1).ir_msg_from);
        Struct1 x_3 = ((x_1).ir_msg);
        Bit#(3) x_4 = ((x_1).ir_mshr_id);
        Bool x_5 = ((x_1).ir_is_rs_rel);
        when (! (x_5), noAction);
        Struct9 x_6 = ((x_0).lr_ir);
        Struct10 x_7 = ((x_6).info);
        Struct5 x_8 = ((x_1).ir_by_victim);
        Vector#(4, Bit#(64)) x_9 = ((x_0).lr_value);
        let x_10 <- getMSHR_00(x_4);
        let x_11 <- getMSHRRq_00(x_4);
        Struct1 x_12 = (unpack(0));
        Vector#(4, Bit#(64)) x_13 = (unpack(0));
        Bool x_14 = ((x_7).mesi_owned);
        Bit#(3) x_15 = ((x_7).mesi_status);
        Struct15 x_16 = (Struct15 {dir_st : (((x_7).mesi_dir_st) ==
        ((Bit#(3))'(3'h0)) ? ((Bit#(3))'(3'h1)) : ((x_7).mesi_dir_st)),
        dir_excl : ((((x_7).mesi_dir_sharers)[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        ((((((x_7).mesi_dir_sharers)[3:1])[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        (((((((x_7).mesi_dir_sharers)[3:1])[2:1])[0:0]) == ((Bit#(1))'(1'h1))
        ? ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        ((((((((x_7).mesi_dir_sharers)[3:1])[2:1])[1:1])[0:0]) ==
        ((Bit#(1))'(1'h1)) ? ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        (unpack(0))))))))))))), dir_sharers : (x_7).mesi_dir_sharers});
        when ((x_2) == ((Bit#(4))'(4'h0)), noAction);
        when (((x_3).id) == ((Bit#(6))'(6'h2)), noAction);
        when (! ((x_3).type_), noAction);
        when ((! ((x_15) < ((Bit#(3))'(3'h3)))) && (((x_16).dir_st) ==
        ((Bit#(3))'(3'h1))), noAction);
        Struct1 x_17 = (x_3);
        Struct16 x_18 = (Struct16 {addr : (x_3).addr, info_write :
        (Bool)'(False), info_hit : (x_6).info_hit, info_way : (x_6).info_way,
        edir_hit : (x_6).edir_hit, edir_way : (x_6).edir_way, edir_slot :
        (x_6).edir_slot, info : (x_6).info, value_write : (Bool)'(False),
        value : unpack(0), may_victim : (x_6).may_victim, reps :
        (x_6).reps});
        Struct16 x_19 = (Struct16 {addr : (x_18).addr, info_write :
        (Bool)'(True), info_hit : (x_18).info_hit, info_way :
        (x_18).info_way, edir_hit : (x_18).edir_hit, edir_way :
        (x_18).edir_way, edir_slot : (x_18).edir_slot, info : Struct10
        {mesi_owned : ((x_18).info).mesi_owned, mesi_status :
        ((x_18).info).mesi_status, mesi_dir_st : (Struct15 {dir_st :
        (Bit#(3))'(3'h3), dir_excl : (Bit#(2))'(2'h0), dir_sharers :
        unpack(0)}).dir_st, mesi_dir_sharers : (((Struct15 {dir_st :
        (Bit#(3))'(3'h3), dir_excl : (Bit#(2))'(2'h0), dir_sharers :
        unpack(0)}).dir_st) == ((Bit#(3))'(3'h2)) ? ((Struct15 {dir_st :
        (Bit#(3))'(3'h3), dir_excl : (Bit#(2))'(2'h0), dir_sharers :
        unpack(0)}).dir_sharers) : (((Bit#(4))'(4'h1)) << ((Struct15 {dir_st
        : (Bit#(3))'(3'h3), dir_excl : (Bit#(2))'(2'h0), dir_sharers :
        unpack(0)}).dir_excl)))}, value_write : (x_18).value_write, value :
        (x_18).value, may_victim : (x_18).may_victim, reps :
        (x_18).reps});
        Struct16 x_20 = (Struct16 {addr : (x_19).addr, info_write :
        (Bool)'(True), info_hit : (x_19).info_hit, info_way :
        (x_19).info_way, edir_hit : (x_19).edir_hit, edir_way :
        (x_19).edir_way, edir_slot : (x_19).edir_slot, info : Struct10
        {mesi_owned : ((x_19).info).mesi_owned, mesi_status :
        (Bit#(3))'(3'h1), mesi_dir_st : ((x_19).info).mesi_dir_st,
        mesi_dir_sharers : ((x_19).info).mesi_dir_sharers}, value_write :
        (x_19).value_write, value : (x_19).value, may_victim :
        (x_19).may_victim, reps :
        (x_19).reps});
        let x_23 = ?;
        if ((x_8).valid) begin
            let x_21 <- victims__00__setVictim(Struct17 {victim_idx :
            (x_8).data, victim_info : (x_20).info, victim_value :
            ((x_20).value_write ? ((x_20).value) : (x_9))});
            x_23 = x_9;
        end else begin
            let x_22 <- cache__00__valueRsLineRq(x_20);
            x_23 = x_22;
        end
        Struct18 x_24 = (Struct18 {enq_type : ((((Bit#(4))'(4'h8))[3:2]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : (((((Bit#(4))'(4'h8))[3:2])
        == ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : ((Bit#(4))'(4'h8))[1:0], enq_msg : Struct1 {id :
        (Bit#(6))'(6'h4), type_ : (Bool)'(True), addr : (x_17).addr, value :
        x_23}});
        let x_25 <- makeEnq_parentChildren00(x_24);
        let x_26 <- releaseMSHR_00(x_4);
    endrule

    rule rule_exec_00_01000;
        let x_0 <- deq_fifoL2E_00();
        Struct6 x_1 = ((x_0).lr_ir_pp);
        Bit#(4) x_2 = ((x_1).ir_msg_from);
        Struct1 x_3 = ((x_1).ir_msg);
        Bit#(3) x_4 = ((x_1).ir_mshr_id);
        Bool x_5 = ((x_1).ir_is_rs_rel);
        when (! (x_5), noAction);
        Struct9 x_6 = ((x_0).lr_ir);
        Struct10 x_7 = ((x_6).info);
        Struct5 x_8 = ((x_1).ir_by_victim);
        Vector#(4, Bit#(64)) x_9 = ((x_0).lr_value);
        let x_10 <- getMSHR_00(x_4);
        let x_11 <- getMSHRRq_00(x_4);
        Struct1 x_12 = (unpack(0));
        Vector#(4, Bit#(64)) x_13 = (unpack(0));
        Bool x_14 = ((x_7).mesi_owned);
        Bit#(3) x_15 = ((x_7).mesi_status);
        Struct15 x_16 = (Struct15 {dir_st : (((x_7).mesi_dir_st) ==
        ((Bit#(3))'(3'h0)) ? ((Bit#(3))'(3'h1)) : ((x_7).mesi_dir_st)),
        dir_excl : ((((x_7).mesi_dir_sharers)[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        ((((((x_7).mesi_dir_sharers)[3:1])[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        (((((((x_7).mesi_dir_sharers)[3:1])[2:1])[0:0]) == ((Bit#(1))'(1'h1))
        ? ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        ((((((((x_7).mesi_dir_sharers)[3:1])[2:1])[1:1])[0:0]) ==
        ((Bit#(1))'(1'h1)) ? ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        (unpack(0))))))))))))), dir_sharers : (x_7).mesi_dir_sharers});
        when ((x_2) == ((Bit#(4))'(4'h0)), noAction);
        when (((x_3).id) == ((Bit#(6))'(6'h2)), noAction);
        when (! ((x_3).type_), noAction);
        when (((x_14) == ((Bool)'(False))) && ((! (((Bit#(3))'(3'h1)) <
        (x_15))) && (! (((Bit#(3))'(3'h2)) < ((x_16).dir_st)))),
        noAction);
        Struct1 x_17 = (x_3);
        Struct16 x_18 = (Struct16 {addr : (x_3).addr, info_write :
        (Bool)'(False), info_hit : (x_6).info_hit, info_way : (x_6).info_way,
        edir_hit : (x_6).edir_hit, edir_way : (x_6).edir_way, edir_slot :
        (x_6).edir_slot, info : (x_6).info, value_write : (Bool)'(False),
        value : unpack(0), may_victim : (x_6).may_victim, reps :
        (x_6).reps});
        let x_20 = ?;
        if ((x_8).valid) begin
            x_20 = x_9;
        end else begin
            let x_19 <- cache__00__valueRsLineRq(unpack(0));
            x_20 = x_19;
        end
        let x_21 <- registerUL_00(Struct19 {r_id : x_4, r_ul_rsb :
        (Bool)'(True), r_ul_rsbTo : ((Bit#(4))'(4'h8))[1:0]});
        Struct18 x_22 = (Struct18 {enq_type : ((((Bit#(4))'(4'h0))[3:2]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : (((((Bit#(4))'(4'h0))[3:2])
        == ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : ((Bit#(4))'(4'h0))[1:0], enq_msg : Struct1 {id :
        (Bit#(6))'(6'h2), type_ : (Bool)'(False), addr : (x_17).addr, value :
        unpack(0)}});
        let x_23 <- makeEnq_parentChildren00(x_22);
    endrule

    rule rule_exec_00_03000;
        let x_0 <- deq_fifoL2E_00();
        Struct6 x_1 = ((x_0).lr_ir_pp);
        Bit#(4) x_2 = ((x_1).ir_msg_from);
        Struct1 x_3 = ((x_1).ir_msg);
        Bit#(3) x_4 = ((x_1).ir_mshr_id);
        Bool x_5 = ((x_1).ir_is_rs_rel);
        when (! (x_5), noAction);
        Struct9 x_6 = ((x_0).lr_ir);
        Struct10 x_7 = ((x_6).info);
        Struct5 x_8 = ((x_1).ir_by_victim);
        Vector#(4, Bit#(64)) x_9 = ((x_0).lr_value);
        let x_10 <- getMSHR_00(x_4);
        let x_11 <- getMSHRRq_00(x_4);
        Struct1 x_12 = (unpack(0));
        Vector#(4, Bit#(64)) x_13 = (unpack(0));
        Bool x_14 = ((x_7).mesi_owned);
        Bit#(3) x_15 = ((x_7).mesi_status);
        Struct15 x_16 = (Struct15 {dir_st : (((x_7).mesi_dir_st) ==
        ((Bit#(3))'(3'h0)) ? ((Bit#(3))'(3'h1)) : ((x_7).mesi_dir_st)),
        dir_excl : ((((x_7).mesi_dir_sharers)[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        ((((((x_7).mesi_dir_sharers)[3:1])[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        (((((((x_7).mesi_dir_sharers)[3:1])[2:1])[0:0]) == ((Bit#(1))'(1'h1))
        ? ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        ((((((((x_7).mesi_dir_sharers)[3:1])[2:1])[1:1])[0:0]) ==
        ((Bit#(1))'(1'h1)) ? ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        (unpack(0))))))))))))), dir_sharers : (x_7).mesi_dir_sharers});
        when ((x_2) == ((Bit#(4))'(4'h0)), noAction);
        when (((x_3).id) == ((Bit#(6))'(6'h2)), noAction);
        when (! ((x_3).type_), noAction);
        when (((Bool)'(True)) && (((Bool)'(True)) && ((! (((Bit#(3))'(3'h1))
        < (x_15))) && ((! (((x_16).dir_st) < ((Bit#(3))'(3'h3)))) && (!
        (((Bit#(3))'(3'h4)) < ((x_16).dir_st)))))), noAction);
        Struct1 x_17 = (x_3);
        Struct16 x_18 = (Struct16 {addr : (x_3).addr, info_write :
        (Bool)'(False), info_hit : (x_6).info_hit, info_way : (x_6).info_way,
        edir_hit : (x_6).edir_hit, edir_way : (x_6).edir_way, edir_slot :
        (x_6).edir_slot, info : (x_6).info, value_write : (Bool)'(False),
        value : unpack(0), may_victim : (x_6).may_victim, reps :
        (x_6).reps});
        let x_20 = ?;
        if ((x_8).valid) begin
            x_20 = x_9;
        end else begin
            let x_19 <- cache__00__valueRsLineRq(unpack(0));
            x_20 = x_19;
        end
        let x_21 <- registerDL_00(Struct20 {r_id : x_4, r_dl_rss_from :
        (unpack(0)) | (((Bit#(4))'(4'h1)) <<
        (({((Bit#(2))'(2'h1)),((x_16).dir_excl)})[1:0])), r_dl_rsb :
        (Bool)'(True), r_dl_rsbTo : (Bit#(4))'(4'h8)});
        Struct18 x_22 = (Struct18 {enq_type :
        ((({((Bit#(2))'(2'h2)),((x_16).dir_excl)})[3:2]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) :
        (((({((Bit#(2))'(2'h2)),((x_16).dir_excl)})[3:2]) ==
        ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : ({((Bit#(2))'(2'h2)),((x_16).dir_excl)})[1:0], enq_msg :
        Struct1 {id : (Bit#(6))'(6'h5), type_ : (Bool)'(False), addr :
        (x_17).addr, value : unpack(0)}});
        let x_23 <- makeEnq_parentChildren00(x_22);
    endrule

    rule rule_exec_00_10000;
        let x_0 <- deq_fifoL2E_00();
        Struct6 x_1 = ((x_0).lr_ir_pp);
        Bit#(4) x_2 = ((x_1).ir_msg_from);
        Struct1 x_3 = ((x_1).ir_msg);
        Bit#(3) x_4 = ((x_1).ir_mshr_id);
        Bool x_5 = ((x_1).ir_is_rs_rel);
        when (! (x_5), noAction);
        Struct9 x_6 = ((x_0).lr_ir);
        Struct10 x_7 = ((x_6).info);
        Struct5 x_8 = ((x_1).ir_by_victim);
        Vector#(4, Bit#(64)) x_9 = ((x_0).lr_value);
        let x_10 <- getMSHR_00(x_4);
        let x_11 <- getMSHRRq_00(x_4);
        Struct1 x_12 = (unpack(0));
        Vector#(4, Bit#(64)) x_13 = (unpack(0));
        Bool x_14 = ((x_7).mesi_owned);
        Bit#(3) x_15 = ((x_7).mesi_status);
        Struct15 x_16 = (Struct15 {dir_st : (((x_7).mesi_dir_st) ==
        ((Bit#(3))'(3'h0)) ? ((Bit#(3))'(3'h1)) : ((x_7).mesi_dir_st)),
        dir_excl : ((((x_7).mesi_dir_sharers)[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        ((((((x_7).mesi_dir_sharers)[3:1])[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        (((((((x_7).mesi_dir_sharers)[3:1])[2:1])[0:0]) == ((Bit#(1))'(1'h1))
        ? ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        ((((((((x_7).mesi_dir_sharers)[3:1])[2:1])[1:1])[0:0]) ==
        ((Bit#(1))'(1'h1)) ? ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        (unpack(0))))))))))))), dir_sharers : (x_7).mesi_dir_sharers});
        when ((x_2) == ((Bit#(4))'(4'h0)), noAction);
        when (((x_3).id) == ((Bit#(6))'(6'ha)), noAction);
        when (! ((x_3).type_), noAction);
        when ((! ((x_15) < ((Bit#(3))'(3'h3)))) || (((x_15) ==
        ((Bit#(3))'(3'h2))) && (((x_14) == ((Bool)'(True))) &&
        ((((x_16).dir_st) == ((Bit#(3))'(3'h2))) && (((x_16).dir_sharers) ==
        (((Bit#(4))'(4'h1)) << ((Bit#(2))'(2'h0))))))), noAction);
        Struct1 x_17 = (x_3);
        Struct16 x_18 = (Struct16 {addr : (x_3).addr, info_write :
        (Bool)'(False), info_hit : (x_6).info_hit, info_way : (x_6).info_way,
        edir_hit : (x_6).edir_hit, edir_way : (x_6).edir_way, edir_slot :
        (x_6).edir_slot, info : (x_6).info, value_write : (Bool)'(False),
        value : unpack(0), may_victim : (x_6).may_victim, reps :
        (x_6).reps});
        Struct16 x_19 = (Struct16 {addr : (x_18).addr, info_write :
        (Bool)'(True), info_hit : (x_18).info_hit, info_way :
        (x_18).info_way, edir_hit : (x_18).edir_hit, edir_way :
        (x_18).edir_way, edir_slot : (x_18).edir_slot, info : Struct10
        {mesi_owned : ((x_18).info).mesi_owned, mesi_status :
        ((x_18).info).mesi_status, mesi_dir_st : (Struct15 {dir_st :
        (Bit#(3))'(3'h4), dir_excl : (Bit#(2))'(2'h0), dir_sharers :
        unpack(0)}).dir_st, mesi_dir_sharers : (((Struct15 {dir_st :
        (Bit#(3))'(3'h4), dir_excl : (Bit#(2))'(2'h0), dir_sharers :
        unpack(0)}).dir_st) == ((Bit#(3))'(3'h2)) ? ((Struct15 {dir_st :
        (Bit#(3))'(3'h4), dir_excl : (Bit#(2))'(2'h0), dir_sharers :
        unpack(0)}).dir_sharers) : (((Bit#(4))'(4'h1)) << ((Struct15 {dir_st
        : (Bit#(3))'(3'h4), dir_excl : (Bit#(2))'(2'h0), dir_sharers :
        unpack(0)}).dir_excl)))}, value_write : (x_18).value_write, value :
        (x_18).value, may_victim : (x_18).may_victim, reps :
        (x_18).reps});
        Struct16 x_20 = (Struct16 {addr : (x_19).addr, info_write :
        (Bool)'(True), info_hit : (x_19).info_hit, info_way :
        (x_19).info_way, edir_hit : (x_19).edir_hit, edir_way :
        (x_19).edir_way, edir_slot : (x_19).edir_slot, info : Struct10
        {mesi_owned : ((x_19).info).mesi_owned, mesi_status :
        (Bit#(3))'(3'h1), mesi_dir_st : ((x_19).info).mesi_dir_st,
        mesi_dir_sharers : ((x_19).info).mesi_dir_sharers}, value_write :
        (x_19).value_write, value : (x_19).value, may_victim :
        (x_19).may_victim, reps : (x_19).reps});
        Struct16 x_21 = (Struct16 {addr : (x_20).addr, info_write :
        (Bool)'(True), info_hit : (x_20).info_hit, info_way :
        (x_20).info_way, edir_hit : (x_20).edir_hit, edir_way :
        (x_20).edir_way, edir_slot : (x_20).edir_slot, info : Struct10
        {mesi_owned : (Bool)'(False), mesi_status :
        ((x_20).info).mesi_status, mesi_dir_st : ((x_20).info).mesi_dir_st,
        mesi_dir_sharers : ((x_20).info).mesi_dir_sharers}, value_write :
        (x_20).value_write, value : (x_20).value, may_victim :
        (x_20).may_victim, reps :
        (x_20).reps});
        let x_24 = ?;
        if ((x_8).valid) begin
            let x_22 <- victims__00__setVictim(Struct17 {victim_idx :
            (x_8).data, victim_info : (x_21).info, victim_value :
            ((x_21).value_write ? ((x_21).value) : (x_9))});
            x_24 = x_9;
        end else begin
            let x_23 <- cache__00__valueRsLineRq(x_21);
            x_24 = x_23;
        end
        Struct18 x_25 = (Struct18 {enq_type : ((((Bit#(4))'(4'h8))[3:2]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : (((((Bit#(4))'(4'h8))[3:2])
        == ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : ((Bit#(4))'(4'h8))[1:0], enq_msg : Struct1 {id :
        (Bit#(6))'(6'hb), type_ : (Bool)'(True), addr : (x_17).addr, value :
        unpack(0)}});
        let x_26 <- makeEnq_parentChildren00(x_25);
        let x_27 <- releaseMSHR_00(x_4);
    endrule

    rule rule_exec_00_11000;
        let x_0 <- deq_fifoL2E_00();
        Struct6 x_1 = ((x_0).lr_ir_pp);
        Bit#(4) x_2 = ((x_1).ir_msg_from);
        Struct1 x_3 = ((x_1).ir_msg);
        Bit#(3) x_4 = ((x_1).ir_mshr_id);
        Bool x_5 = ((x_1).ir_is_rs_rel);
        when (! (x_5), noAction);
        Struct9 x_6 = ((x_0).lr_ir);
        Struct10 x_7 = ((x_6).info);
        Struct5 x_8 = ((x_1).ir_by_victim);
        Vector#(4, Bit#(64)) x_9 = ((x_0).lr_value);
        let x_10 <- getMSHR_00(x_4);
        let x_11 <- getMSHRRq_00(x_4);
        Struct1 x_12 = (unpack(0));
        Vector#(4, Bit#(64)) x_13 = (unpack(0));
        Bool x_14 = ((x_7).mesi_owned);
        Bit#(3) x_15 = ((x_7).mesi_status);
        Struct15 x_16 = (Struct15 {dir_st : (((x_7).mesi_dir_st) ==
        ((Bit#(3))'(3'h0)) ? ((Bit#(3))'(3'h1)) : ((x_7).mesi_dir_st)),
        dir_excl : ((((x_7).mesi_dir_sharers)[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        ((((((x_7).mesi_dir_sharers)[3:1])[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        (((((((x_7).mesi_dir_sharers)[3:1])[2:1])[0:0]) == ((Bit#(1))'(1'h1))
        ? ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        ((((((((x_7).mesi_dir_sharers)[3:1])[2:1])[1:1])[0:0]) ==
        ((Bit#(1))'(1'h1)) ? ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        (unpack(0))))))))))))), dir_sharers : (x_7).mesi_dir_sharers});
        when ((x_2) == ((Bit#(4))'(4'h0)), noAction);
        when (((x_3).id) == ((Bit#(6))'(6'ha)), noAction);
        when (! ((x_3).type_), noAction);
        when (((x_14) == ((Bool)'(False))) && ((! (((Bit#(3))'(3'h2)) <
        (x_15))) && (! (((Bit#(3))'(3'h2)) < ((x_16).dir_st)))),
        noAction);
        Struct1 x_17 = (x_3);
        Struct16 x_18 = (Struct16 {addr : (x_3).addr, info_write :
        (Bool)'(False), info_hit : (x_6).info_hit, info_way : (x_6).info_way,
        edir_hit : (x_6).edir_hit, edir_way : (x_6).edir_way, edir_slot :
        (x_6).edir_slot, info : (x_6).info, value_write : (Bool)'(False),
        value : unpack(0), may_victim : (x_6).may_victim, reps :
        (x_6).reps});
        let x_20 = ?;
        if ((x_8).valid) begin
            x_20 = x_9;
        end else begin
            let x_19 <- cache__00__valueRsLineRq(unpack(0));
            x_20 = x_19;
        end
        let x_21 <- registerUL_00(Struct19 {r_id : x_4, r_ul_rsb :
        (Bool)'(True), r_ul_rsbTo : ((Bit#(4))'(4'h8))[1:0]});
        Struct18 x_22 = (Struct18 {enq_type : ((((Bit#(4))'(4'h0))[3:2]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : (((((Bit#(4))'(4'h0))[3:2])
        == ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : ((Bit#(4))'(4'h0))[1:0], enq_msg : Struct1 {id :
        (Bit#(6))'(6'ha), type_ : (Bool)'(False), addr : (x_17).addr, value :
        unpack(0)}});
        let x_23 <- makeEnq_parentChildren00(x_22);
    endrule

    rule rule_exec_00_14000;
        let x_0 <- deq_fifoL2E_00();
        Struct6 x_1 = ((x_0).lr_ir_pp);
        Bit#(4) x_2 = ((x_1).ir_msg_from);
        Struct1 x_3 = ((x_1).ir_msg);
        Bit#(3) x_4 = ((x_1).ir_mshr_id);
        Bool x_5 = ((x_1).ir_is_rs_rel);
        when (! (x_5), noAction);
        Struct9 x_6 = ((x_0).lr_ir);
        Struct10 x_7 = ((x_6).info);
        Struct5 x_8 = ((x_1).ir_by_victim);
        Vector#(4, Bit#(64)) x_9 = ((x_0).lr_value);
        let x_10 <- getMSHR_00(x_4);
        let x_11 <- getMSHRRq_00(x_4);
        Struct1 x_12 = (unpack(0));
        Vector#(4, Bit#(64)) x_13 = (unpack(0));
        Bool x_14 = ((x_7).mesi_owned);
        Bit#(3) x_15 = ((x_7).mesi_status);
        Struct15 x_16 = (Struct15 {dir_st : (((x_7).mesi_dir_st) ==
        ((Bit#(3))'(3'h0)) ? ((Bit#(3))'(3'h1)) : ((x_7).mesi_dir_st)),
        dir_excl : ((((x_7).mesi_dir_sharers)[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        ((((((x_7).mesi_dir_sharers)[3:1])[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        (((((((x_7).mesi_dir_sharers)[3:1])[2:1])[0:0]) == ((Bit#(1))'(1'h1))
        ? ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        ((((((((x_7).mesi_dir_sharers)[3:1])[2:1])[1:1])[0:0]) ==
        ((Bit#(1))'(1'h1)) ? ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        (unpack(0))))))))))))), dir_sharers : (x_7).mesi_dir_sharers});
        when ((x_2) == ((Bit#(4))'(4'h0)), noAction);
        when (((x_3).id) == ((Bit#(6))'(6'ha)), noAction);
        when (! ((x_3).type_), noAction);
        when (((Bool)'(True)) && (((Bool)'(True)) && ((! (((Bit#(3))'(3'h1))
        < (x_15))) && ((! (((x_16).dir_st) < ((Bit#(3))'(3'h3)))) && (!
        (((Bit#(3))'(3'h4)) < ((x_16).dir_st)))))), noAction);
        Struct1 x_17 = (x_3);
        Struct16 x_18 = (Struct16 {addr : (x_3).addr, info_write :
        (Bool)'(False), info_hit : (x_6).info_hit, info_way : (x_6).info_way,
        edir_hit : (x_6).edir_hit, edir_way : (x_6).edir_way, edir_slot :
        (x_6).edir_slot, info : (x_6).info, value_write : (Bool)'(False),
        value : unpack(0), may_victim : (x_6).may_victim, reps :
        (x_6).reps});
        let x_20 = ?;
        if ((x_8).valid) begin
            x_20 = x_9;
        end else begin
            let x_19 <- cache__00__valueRsLineRq(unpack(0));
            x_20 = x_19;
        end
        let x_21 <- registerDL_00(Struct20 {r_id : x_4, r_dl_rss_from :
        (unpack(0)) | (((Bit#(4))'(4'h1)) <<
        (({((Bit#(2))'(2'h1)),((x_16).dir_excl)})[1:0])), r_dl_rsb :
        (Bool)'(True), r_dl_rsbTo : (Bit#(4))'(4'h8)});
        Struct18 x_22 = (Struct18 {enq_type :
        ((({((Bit#(2))'(2'h2)),((x_16).dir_excl)})[3:2]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) :
        (((({((Bit#(2))'(2'h2)),((x_16).dir_excl)})[3:2]) ==
        ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : ({((Bit#(2))'(2'h2)),((x_16).dir_excl)})[1:0], enq_msg :
        Struct1 {id : (Bit#(6))'(6'he), type_ : (Bool)'(False), addr :
        (x_17).addr, value : unpack(0)}});
        let x_23 <- makeEnq_parentChildren00(x_22);
    endrule

    rule rule_exec_00_15000;
        let x_0 <- deq_fifoL2E_00();
        Struct6 x_1 = ((x_0).lr_ir_pp);
        Bit#(4) x_2 = ((x_1).ir_msg_from);
        Struct1 x_3 = ((x_1).ir_msg);
        Bit#(3) x_4 = ((x_1).ir_mshr_id);
        Bool x_5 = ((x_1).ir_is_rs_rel);
        when (! (x_5), noAction);
        Struct9 x_6 = ((x_0).lr_ir);
        Struct10 x_7 = ((x_6).info);
        Struct5 x_8 = ((x_1).ir_by_victim);
        Vector#(4, Bit#(64)) x_9 = ((x_0).lr_value);
        let x_10 <- getMSHR_00(x_4);
        let x_11 <- getMSHRRq_00(x_4);
        Struct1 x_12 = (unpack(0));
        Vector#(4, Bit#(64)) x_13 = (unpack(0));
        Bool x_14 = ((x_7).mesi_owned);
        Bit#(3) x_15 = ((x_7).mesi_status);
        Struct15 x_16 = (Struct15 {dir_st : (((x_7).mesi_dir_st) ==
        ((Bit#(3))'(3'h0)) ? ((Bit#(3))'(3'h1)) : ((x_7).mesi_dir_st)),
        dir_excl : ((((x_7).mesi_dir_sharers)[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        ((((((x_7).mesi_dir_sharers)[3:1])[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        (((((((x_7).mesi_dir_sharers)[3:1])[2:1])[0:0]) == ((Bit#(1))'(1'h1))
        ? ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        ((((((((x_7).mesi_dir_sharers)[3:1])[2:1])[1:1])[0:0]) ==
        ((Bit#(1))'(1'h1)) ? ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        (unpack(0))))))))))))), dir_sharers : (x_7).mesi_dir_sharers});
        when ((x_2) == ((Bit#(4))'(4'h0)), noAction);
        when (((x_3).id) == ((Bit#(6))'(6'ha)), noAction);
        when (! ((x_3).type_), noAction);
        when (((Bool)'(True)) && (((Bool)'(True)) && ((!
        ((((x_16).dir_sharers) & (~(((Bit#(4))'(4'h1)) <<
        ((Bit#(2))'(2'h0))))) == ((Bit#(4))'(4'h0)))) && (((x_14) ==
        ((Bool)'(True))) && ((! (((Bit#(3))'(3'h2)) < (x_15))) &&
        (((x_16).dir_st) == ((Bit#(3))'(3'h2))))))), noAction);
        Struct1 x_17 = (x_3);
        Struct16 x_18 = (Struct16 {addr : (x_3).addr, info_write :
        (Bool)'(False), info_hit : (x_6).info_hit, info_way : (x_6).info_way,
        edir_hit : (x_6).edir_hit, edir_way : (x_6).edir_way, edir_slot :
        (x_6).edir_slot, info : (x_6).info, value_write : (Bool)'(False),
        value : unpack(0), may_victim : (x_6).may_victim, reps :
        (x_6).reps});
        let x_20 = ?;
        if ((x_8).valid) begin
            x_20 = x_9;
        end else begin
            let x_19 <- cache__00__valueRsLineRq(unpack(0));
            x_20 = x_19;
        end
        let x_21 <- registerDL_00(Struct20 {r_id : x_4, r_dl_rss_from :
        ((x_16).dir_sharers) & (~(((Bit#(4))'(4'h1)) << ((Bit#(2))'(2'h0)))),
        r_dl_rsb : (Bool)'(True), r_dl_rsbTo : (Bit#(4))'(4'h8)});
        let x_22 <- broadcast_parentChildren00(Struct21 {cs_inds :
        ((x_16).dir_sharers) & (~(((Bit#(4))'(4'h1)) << ((Bit#(2))'(2'h0)))),
        cs_msg : Struct1 {id : (Bit#(6))'(6'hc), type_ : (Bool)'(False), addr
        : (x_17).addr, value : unpack(0)}});
    endrule

    rule rule_exec_00_25000;
        let x_0 <- deq_fifoL2E_00();
        Struct6 x_1 = ((x_0).lr_ir_pp);
        Bit#(4) x_2 = ((x_1).ir_msg_from);
        Struct1 x_3 = ((x_1).ir_msg);
        Bit#(3) x_4 = ((x_1).ir_mshr_id);
        Bool x_5 = ((x_1).ir_is_rs_rel);
        when (! (x_5), noAction);
        Struct9 x_6 = ((x_0).lr_ir);
        Struct10 x_7 = ((x_6).info);
        Struct5 x_8 = ((x_1).ir_by_victim);
        Vector#(4, Bit#(64)) x_9 = ((x_0).lr_value);
        let x_10 <- getMSHR_00(x_4);
        let x_11 <- getMSHRRq_00(x_4);
        Struct1 x_12 = (unpack(0));
        Vector#(4, Bit#(64)) x_13 = (unpack(0));
        Bool x_14 = ((x_7).mesi_owned);
        Bit#(3) x_15 = ((x_7).mesi_status);
        Struct15 x_16 = (Struct15 {dir_st : (((x_7).mesi_dir_st) ==
        ((Bit#(3))'(3'h0)) ? ((Bit#(3))'(3'h1)) : ((x_7).mesi_dir_st)),
        dir_excl : ((((x_7).mesi_dir_sharers)[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        ((((((x_7).mesi_dir_sharers)[3:1])[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        (((((((x_7).mesi_dir_sharers)[3:1])[2:1])[0:0]) == ((Bit#(1))'(1'h1))
        ? ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        ((((((((x_7).mesi_dir_sharers)[3:1])[2:1])[1:1])[0:0]) ==
        ((Bit#(1))'(1'h1)) ? ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        (unpack(0))))))))))))), dir_sharers : (x_7).mesi_dir_sharers});
        when ((x_2) == ((Bit#(4))'(4'h0)), noAction);
        when (((x_3).id) == ((Bit#(6))'(6'h14)), noAction);
        when (! ((x_3).type_), noAction);
        when ((((((x_16).dir_st) == ((Bit#(3))'(3'h4))) && (((x_16).dir_excl)
        == ((Bit#(2))'(2'h0))) ? ((Bit#(3))'(3'h4)) : (((((x_16).dir_st) ==
        ((Bit#(3))'(3'h3))) && (((x_16).dir_excl) == ((Bit#(2))'(2'h0))) ?
        ((Bit#(3))'(3'h3)) : (((((x_16).dir_st) == ((Bit#(3))'(3'h2))) &&
        ((((x_16).dir_sharers) | (((Bit#(4))'(4'h1)) << ((Bit#(2))'(2'h0))))
        == ((x_16).dir_sharers)) ? ((Bit#(3))'(3'h2)) :
        ((Bit#(3))'(3'h1)))))))) == ((Bit#(3))'(3'h1)), noAction);
        Struct1 x_17 = (x_3);
        Struct16 x_18 = (Struct16 {addr : (x_3).addr, info_write :
        (Bool)'(False), info_hit : (x_6).info_hit, info_way : (x_6).info_way,
        edir_hit : (x_6).edir_hit, edir_way : (x_6).edir_way, edir_slot :
        (x_6).edir_slot, info : (x_6).info, value_write : (Bool)'(False),
        value : unpack(0), may_victim : (x_6).may_victim, reps :
        (x_6).reps});
        let x_20 = ?;
        if ((x_8).valid) begin
            x_20 = x_9;
        end else begin
            let x_19 <- cache__00__valueRsLineRq(unpack(0));
            x_20 = x_19;
        end
        Struct18 x_21 = (Struct18 {enq_type : ((((Bit#(4))'(4'h8))[3:2]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : (((((Bit#(4))'(4'h8))[3:2])
        == ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : ((Bit#(4))'(4'h8))[1:0], enq_msg : Struct1 {id :
        (Bit#(6))'(6'h16), type_ : (Bool)'(True), addr : (x_17).addr, value :
        unpack(0)}});
        let x_22 <- makeEnq_parentChildren00(x_21);
        let x_23 <- releaseMSHR_00(x_4);
    endrule

    rule rule_exec_00_2600000;
        let x_0 <- deq_fifoL2E_00();
        Struct6 x_1 = ((x_0).lr_ir_pp);
        Bit#(4) x_2 = ((x_1).ir_msg_from);
        Struct1 x_3 = ((x_1).ir_msg);
        Bit#(3) x_4 = ((x_1).ir_mshr_id);
        Bool x_5 = ((x_1).ir_is_rs_rel);
        when (! (x_5), noAction);
        Struct9 x_6 = ((x_0).lr_ir);
        Struct10 x_7 = ((x_6).info);
        Struct5 x_8 = ((x_1).ir_by_victim);
        Vector#(4, Bit#(64)) x_9 = ((x_0).lr_value);
        let x_10 <- getMSHR_00(x_4);
        let x_11 <- getMSHRRq_00(x_4);
        Struct1 x_12 = (unpack(0));
        Vector#(4, Bit#(64)) x_13 = (unpack(0));
        Bool x_14 = ((x_7).mesi_owned);
        Bit#(3) x_15 = ((x_7).mesi_status);
        Struct15 x_16 = (Struct15 {dir_st : (((x_7).mesi_dir_st) ==
        ((Bit#(3))'(3'h0)) ? ((Bit#(3))'(3'h1)) : ((x_7).mesi_dir_st)),
        dir_excl : ((((x_7).mesi_dir_sharers)[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        ((((((x_7).mesi_dir_sharers)[3:1])[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        (((((((x_7).mesi_dir_sharers)[3:1])[2:1])[0:0]) == ((Bit#(1))'(1'h1))
        ? ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        ((((((((x_7).mesi_dir_sharers)[3:1])[2:1])[1:1])[0:0]) ==
        ((Bit#(1))'(1'h1)) ? ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        (unpack(0))))))))))))), dir_sharers : (x_7).mesi_dir_sharers});
        when ((x_2) == ((Bit#(4))'(4'h0)), noAction);
        when (((x_3).id) == ((Bit#(6))'(6'h14)), noAction);
        when (! ((x_3).type_), noAction);
        when (((x_14) == ((Bool)'(False))) && (((((((x_16).dir_st) ==
        ((Bit#(3))'(3'h4))) && (((x_16).dir_excl) == ((Bit#(2))'(2'h0))) ?
        ((Bit#(3))'(3'h4)) : (((((x_16).dir_st) == ((Bit#(3))'(3'h3))) &&
        (((x_16).dir_excl) == ((Bit#(2))'(2'h0))) ? ((Bit#(3))'(3'h3)) :
        (((((x_16).dir_st) == ((Bit#(3))'(3'h2))) && ((((x_16).dir_sharers) |
        (((Bit#(4))'(4'h1)) << ((Bit#(2))'(2'h0)))) == ((x_16).dir_sharers))
        ? ((Bit#(3))'(3'h2)) : ((Bit#(3))'(3'h1)))))))) ==
        ((Bit#(3))'(3'h2))) && (((x_16).dir_sharers) == (((Bit#(4))'(4'h1))
        << ((Bit#(2))'(2'h0))))), noAction);
        Struct1 x_17 = (x_3);
        Struct16 x_18 = (Struct16 {addr : (x_3).addr, info_write :
        (Bool)'(False), info_hit : (x_6).info_hit, info_way : (x_6).info_way,
        edir_hit : (x_6).edir_hit, edir_way : (x_6).edir_way, edir_slot :
        (x_6).edir_slot, info : (x_6).info, value_write : (Bool)'(False),
        value : unpack(0), may_victim : (x_6).may_victim, reps :
        (x_6).reps});
        Struct16 x_19 = (Struct16 {addr : (x_18).addr, info_write :
        (Bool)'(True), info_hit : (x_18).info_hit, info_way :
        (x_18).info_way, edir_hit : (x_18).edir_hit, edir_way :
        (x_18).edir_way, edir_slot : (x_18).edir_slot, info : Struct10
        {mesi_owned : ((x_18).info).mesi_owned, mesi_status :
        ((x_18).info).mesi_status, mesi_dir_st : (Struct15 {dir_st :
        (Bit#(3))'(3'h1), dir_excl : unpack(0), dir_sharers :
        unpack(0)}).dir_st, mesi_dir_sharers : (((Struct15 {dir_st :
        (Bit#(3))'(3'h1), dir_excl : unpack(0), dir_sharers :
        unpack(0)}).dir_st) == ((Bit#(3))'(3'h2)) ? ((Struct15 {dir_st :
        (Bit#(3))'(3'h1), dir_excl : unpack(0), dir_sharers :
        unpack(0)}).dir_sharers) : (((Bit#(4))'(4'h1)) << ((Struct15 {dir_st
        : (Bit#(3))'(3'h1), dir_excl : unpack(0), dir_sharers :
        unpack(0)}).dir_excl)))}, value_write : (x_18).value_write, value :
        (x_18).value, may_victim : (x_18).may_victim, reps :
        (x_18).reps});
        let x_22 = ?;
        if ((x_8).valid) begin
            let x_20 <- victims__00__setVictim(Struct17 {victim_idx :
            (x_8).data, victim_info : (x_19).info, victim_value :
            ((x_19).value_write ? ((x_19).value) : (x_9))});
            x_22 = x_9;
        end else begin
            let x_21 <- cache__00__valueRsLineRq(x_19);
            x_22 = x_21;
        end
        Struct18 x_23 = (Struct18 {enq_type : ((((Bit#(4))'(4'h8))[3:2]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : (((((Bit#(4))'(4'h8))[3:2])
        == ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : ((Bit#(4))'(4'h8))[1:0], enq_msg : Struct1 {id :
        (Bit#(6))'(6'h16), type_ : (Bool)'(True), addr : (x_17).addr, value :
        unpack(0)}});
        let x_24 <- makeEnq_parentChildren00(x_23);
        let x_25 <- releaseMSHR_00(x_4);
    endrule

    rule rule_exec_00_2601000;
        let x_0 <- deq_fifoL2E_00();
        Struct6 x_1 = ((x_0).lr_ir_pp);
        Bit#(4) x_2 = ((x_1).ir_msg_from);
        Struct1 x_3 = ((x_1).ir_msg);
        Bit#(3) x_4 = ((x_1).ir_mshr_id);
        Bool x_5 = ((x_1).ir_is_rs_rel);
        when (! (x_5), noAction);
        Struct9 x_6 = ((x_0).lr_ir);
        Struct10 x_7 = ((x_6).info);
        Struct5 x_8 = ((x_1).ir_by_victim);
        Vector#(4, Bit#(64)) x_9 = ((x_0).lr_value);
        let x_10 <- getMSHR_00(x_4);
        let x_11 <- getMSHRRq_00(x_4);
        Struct1 x_12 = (unpack(0));
        Vector#(4, Bit#(64)) x_13 = (unpack(0));
        Bool x_14 = ((x_7).mesi_owned);
        Bit#(3) x_15 = ((x_7).mesi_status);
        Struct15 x_16 = (Struct15 {dir_st : (((x_7).mesi_dir_st) ==
        ((Bit#(3))'(3'h0)) ? ((Bit#(3))'(3'h1)) : ((x_7).mesi_dir_st)),
        dir_excl : ((((x_7).mesi_dir_sharers)[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        ((((((x_7).mesi_dir_sharers)[3:1])[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        (((((((x_7).mesi_dir_sharers)[3:1])[2:1])[0:0]) == ((Bit#(1))'(1'h1))
        ? ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        ((((((((x_7).mesi_dir_sharers)[3:1])[2:1])[1:1])[0:0]) ==
        ((Bit#(1))'(1'h1)) ? ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        (unpack(0))))))))))))), dir_sharers : (x_7).mesi_dir_sharers});
        when ((x_2) == ((Bit#(4))'(4'h0)), noAction);
        when (((x_3).id) == ((Bit#(6))'(6'h14)), noAction);
        when (! ((x_3).type_), noAction);
        when (((x_14) == ((Bool)'(True))) && (((x_15) == ((Bit#(3))'(3'h2)))
        && (((((((x_16).dir_st) == ((Bit#(3))'(3'h4))) && (((x_16).dir_excl)
        == ((Bit#(2))'(2'h0))) ? ((Bit#(3))'(3'h4)) : (((((x_16).dir_st) ==
        ((Bit#(3))'(3'h3))) && (((x_16).dir_excl) == ((Bit#(2))'(2'h0))) ?
        ((Bit#(3))'(3'h3)) : (((((x_16).dir_st) == ((Bit#(3))'(3'h2))) &&
        ((((x_16).dir_sharers) | (((Bit#(4))'(4'h1)) << ((Bit#(2))'(2'h0))))
        == ((x_16).dir_sharers)) ? ((Bit#(3))'(3'h2)) :
        ((Bit#(3))'(3'h1)))))))) == ((Bit#(3))'(3'h2))) &&
        (((x_16).dir_sharers) == (((Bit#(4))'(4'h1)) <<
        ((Bit#(2))'(2'h0)))))), noAction);
        Struct1 x_17 = (x_3);
        Struct16 x_18 = (Struct16 {addr : (x_3).addr, info_write :
        (Bool)'(False), info_hit : (x_6).info_hit, info_way : (x_6).info_way,
        edir_hit : (x_6).edir_hit, edir_way : (x_6).edir_way, edir_slot :
        (x_6).edir_slot, info : (x_6).info, value_write : (Bool)'(False),
        value : unpack(0), may_victim : (x_6).may_victim, reps :
        (x_6).reps});
        Struct16 x_19 = (Struct16 {addr : (x_18).addr, info_write :
        (Bool)'(True), info_hit : (x_18).info_hit, info_way :
        (x_18).info_way, edir_hit : (x_18).edir_hit, edir_way :
        (x_18).edir_way, edir_slot : (x_18).edir_slot, info : Struct10
        {mesi_owned : ((x_18).info).mesi_owned, mesi_status :
        ((x_18).info).mesi_status, mesi_dir_st : (Struct15 {dir_st :
        (Bit#(3))'(3'h1), dir_excl : unpack(0), dir_sharers :
        unpack(0)}).dir_st, mesi_dir_sharers : (((Struct15 {dir_st :
        (Bit#(3))'(3'h1), dir_excl : unpack(0), dir_sharers :
        unpack(0)}).dir_st) == ((Bit#(3))'(3'h2)) ? ((Struct15 {dir_st :
        (Bit#(3))'(3'h1), dir_excl : unpack(0), dir_sharers :
        unpack(0)}).dir_sharers) : (((Bit#(4))'(4'h1)) << ((Struct15 {dir_st
        : (Bit#(3))'(3'h1), dir_excl : unpack(0), dir_sharers :
        unpack(0)}).dir_excl)))}, value_write : (x_18).value_write, value :
        (x_18).value, may_victim : (x_18).may_victim, reps :
        (x_18).reps});
        Struct16 x_20 = (Struct16 {addr : (x_19).addr, info_write :
        (Bool)'(True), info_hit : (x_19).info_hit, info_way :
        (x_19).info_way, edir_hit : (x_19).edir_hit, edir_way :
        (x_19).edir_way, edir_slot : (x_19).edir_slot, info : Struct10
        {mesi_owned : ((x_19).info).mesi_owned, mesi_status :
        (Bit#(3))'(3'h4), mesi_dir_st : ((x_19).info).mesi_dir_st,
        mesi_dir_sharers : ((x_19).info).mesi_dir_sharers}, value_write :
        (x_19).value_write, value : (x_19).value, may_victim :
        (x_19).may_victim, reps :
        (x_19).reps});
        let x_23 = ?;
        if ((x_8).valid) begin
            let x_21 <- victims__00__setVictim(Struct17 {victim_idx :
            (x_8).data, victim_info : (x_20).info, victim_value :
            ((x_20).value_write ? ((x_20).value) : (x_9))});
            x_23 = x_9;
        end else begin
            let x_22 <- cache__00__valueRsLineRq(x_20);
            x_23 = x_22;
        end
        Struct18 x_24 = (Struct18 {enq_type : ((((Bit#(4))'(4'h8))[3:2]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : (((((Bit#(4))'(4'h8))[3:2])
        == ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : ((Bit#(4))'(4'h8))[1:0], enq_msg : Struct1 {id :
        (Bit#(6))'(6'h16), type_ : (Bool)'(True), addr : (x_17).addr, value :
        unpack(0)}});
        let x_25 <- makeEnq_parentChildren00(x_24);
        let x_26 <- releaseMSHR_00(x_4);
    endrule

    rule rule_exec_00_261000;
        let x_0 <- deq_fifoL2E_00();
        Struct6 x_1 = ((x_0).lr_ir_pp);
        Bit#(4) x_2 = ((x_1).ir_msg_from);
        Struct1 x_3 = ((x_1).ir_msg);
        Bit#(3) x_4 = ((x_1).ir_mshr_id);
        Bool x_5 = ((x_1).ir_is_rs_rel);
        when (! (x_5), noAction);
        Struct9 x_6 = ((x_0).lr_ir);
        Struct10 x_7 = ((x_6).info);
        Struct5 x_8 = ((x_1).ir_by_victim);
        Vector#(4, Bit#(64)) x_9 = ((x_0).lr_value);
        let x_10 <- getMSHR_00(x_4);
        let x_11 <- getMSHRRq_00(x_4);
        Struct1 x_12 = (unpack(0));
        Vector#(4, Bit#(64)) x_13 = (unpack(0));
        Bool x_14 = ((x_7).mesi_owned);
        Bit#(3) x_15 = ((x_7).mesi_status);
        Struct15 x_16 = (Struct15 {dir_st : (((x_7).mesi_dir_st) ==
        ((Bit#(3))'(3'h0)) ? ((Bit#(3))'(3'h1)) : ((x_7).mesi_dir_st)),
        dir_excl : ((((x_7).mesi_dir_sharers)[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        ((((((x_7).mesi_dir_sharers)[3:1])[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        (((((((x_7).mesi_dir_sharers)[3:1])[2:1])[0:0]) == ((Bit#(1))'(1'h1))
        ? ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        ((((((((x_7).mesi_dir_sharers)[3:1])[2:1])[1:1])[0:0]) ==
        ((Bit#(1))'(1'h1)) ? ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        (unpack(0))))))))))))), dir_sharers : (x_7).mesi_dir_sharers});
        when ((x_2) == ((Bit#(4))'(4'h0)), noAction);
        when (((x_3).id) == ((Bit#(6))'(6'h14)), noAction);
        when (! ((x_3).type_), noAction);
        when (((((((x_16).dir_st) == ((Bit#(3))'(3'h4))) &&
        (((x_16).dir_excl) == ((Bit#(2))'(2'h0))) ? ((Bit#(3))'(3'h4)) :
        (((((x_16).dir_st) == ((Bit#(3))'(3'h3))) && (((x_16).dir_excl) ==
        ((Bit#(2))'(2'h0))) ? ((Bit#(3))'(3'h3)) : (((((x_16).dir_st) ==
        ((Bit#(3))'(3'h2))) && ((((x_16).dir_sharers) | (((Bit#(4))'(4'h1))
        << ((Bit#(2))'(2'h0)))) == ((x_16).dir_sharers)) ? ((Bit#(3))'(3'h2))
        : ((Bit#(3))'(3'h1)))))))) == ((Bit#(3))'(3'h2))) &&
        (((Bit#(3))'(3'h1)) < ((((((x_16).dir_sharers)[0:0]) ==
        ((Bit#(1))'(1'h1)) ? ((Bit#(3))'(3'h1)) : ((Bit#(3))'(3'h0)))) +
        (((((((x_16).dir_sharers)[3:1])[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(3))'(3'h1)) : ((Bit#(3))'(3'h0)))) +
        ((((((((x_16).dir_sharers)[3:1])[2:1])[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(3))'(3'h1)) : ((Bit#(3))'(3'h0)))) +
        (((((((((x_16).dir_sharers)[3:1])[2:1])[1:1])[0:0]) ==
        ((Bit#(1))'(1'h1)) ? ((Bit#(3))'(3'h1)) : ((Bit#(3))'(3'h0)))) +
        (unpack(0))))))), noAction);
        Struct1 x_17 = (x_3);
        Struct16 x_18 = (Struct16 {addr : (x_3).addr, info_write :
        (Bool)'(False), info_hit : (x_6).info_hit, info_way : (x_6).info_way,
        edir_hit : (x_6).edir_hit, edir_way : (x_6).edir_way, edir_slot :
        (x_6).edir_slot, info : (x_6).info, value_write : (Bool)'(False),
        value : unpack(0), may_victim : (x_6).may_victim, reps :
        (x_6).reps});
        Struct16 x_19 = (Struct16 {addr : (x_18).addr, info_write :
        (Bool)'(True), info_hit : (x_18).info_hit, info_way :
        (x_18).info_way, edir_hit : (x_18).edir_hit, edir_way :
        (x_18).edir_way, edir_slot : (x_18).edir_slot, info : Struct10
        {mesi_owned : ((x_18).info).mesi_owned, mesi_status :
        ((x_18).info).mesi_status, mesi_dir_st : (Struct15 {dir_st :
        (Bit#(3))'(3'h2), dir_excl : (x_16).dir_excl, dir_sharers :
        ((x_16).dir_sharers) & (~(((Bit#(4))'(4'h1)) <<
        ((Bit#(2))'(2'h0))))}).dir_st, mesi_dir_sharers : (((Struct15 {dir_st
        : (Bit#(3))'(3'h2), dir_excl : (x_16).dir_excl, dir_sharers :
        ((x_16).dir_sharers) & (~(((Bit#(4))'(4'h1)) <<
        ((Bit#(2))'(2'h0))))}).dir_st) == ((Bit#(3))'(3'h2)) ? ((Struct15
        {dir_st : (Bit#(3))'(3'h2), dir_excl : (x_16).dir_excl, dir_sharers :
        ((x_16).dir_sharers) & (~(((Bit#(4))'(4'h1)) <<
        ((Bit#(2))'(2'h0))))}).dir_sharers) : (((Bit#(4))'(4'h1)) <<
        ((Struct15 {dir_st : (Bit#(3))'(3'h2), dir_excl : (x_16).dir_excl,
        dir_sharers : ((x_16).dir_sharers) & (~(((Bit#(4))'(4'h1)) <<
        ((Bit#(2))'(2'h0))))}).dir_excl)))}, value_write :
        (x_18).value_write, value : (x_18).value, may_victim :
        (x_18).may_victim, reps :
        (x_18).reps});
        let x_22 = ?;
        if ((x_8).valid) begin
            let x_20 <- victims__00__setVictim(Struct17 {victim_idx :
            (x_8).data, victim_info : (x_19).info, victim_value :
            ((x_19).value_write ? ((x_19).value) : (x_9))});
            x_22 = x_9;
        end else begin
            let x_21 <- cache__00__valueRsLineRq(x_19);
            x_22 = x_21;
        end
        Struct18 x_23 = (Struct18 {enq_type : ((((Bit#(4))'(4'h8))[3:2]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : (((((Bit#(4))'(4'h8))[3:2])
        == ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : ((Bit#(4))'(4'h8))[1:0], enq_msg : Struct1 {id :
        (Bit#(6))'(6'h16), type_ : (Bool)'(True), addr : (x_17).addr, value :
        unpack(0)}});
        let x_24 <- makeEnq_parentChildren00(x_23);
        let x_25 <- releaseMSHR_00(x_4);
    endrule

    rule rule_exec_00_27000;
        let x_0 <- deq_fifoL2E_00();
        Struct6 x_1 = ((x_0).lr_ir_pp);
        Bit#(4) x_2 = ((x_1).ir_msg_from);
        Struct1 x_3 = ((x_1).ir_msg);
        Bit#(3) x_4 = ((x_1).ir_mshr_id);
        Bool x_5 = ((x_1).ir_is_rs_rel);
        when (! (x_5), noAction);
        Struct9 x_6 = ((x_0).lr_ir);
        Struct10 x_7 = ((x_6).info);
        Struct5 x_8 = ((x_1).ir_by_victim);
        Vector#(4, Bit#(64)) x_9 = ((x_0).lr_value);
        let x_10 <- getMSHR_00(x_4);
        let x_11 <- getMSHRRq_00(x_4);
        Struct1 x_12 = (unpack(0));
        Vector#(4, Bit#(64)) x_13 = (unpack(0));
        Bool x_14 = ((x_7).mesi_owned);
        Bit#(3) x_15 = ((x_7).mesi_status);
        Struct15 x_16 = (Struct15 {dir_st : (((x_7).mesi_dir_st) ==
        ((Bit#(3))'(3'h0)) ? ((Bit#(3))'(3'h1)) : ((x_7).mesi_dir_st)),
        dir_excl : ((((x_7).mesi_dir_sharers)[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        ((((((x_7).mesi_dir_sharers)[3:1])[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        (((((((x_7).mesi_dir_sharers)[3:1])[2:1])[0:0]) == ((Bit#(1))'(1'h1))
        ? ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        ((((((((x_7).mesi_dir_sharers)[3:1])[2:1])[1:1])[0:0]) ==
        ((Bit#(1))'(1'h1)) ? ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        (unpack(0))))))))))))), dir_sharers : (x_7).mesi_dir_sharers});
        when ((x_2) == ((Bit#(4))'(4'h0)), noAction);
        when (((x_3).id) == ((Bit#(6))'(6'h14)), noAction);
        when (! ((x_3).type_), noAction);
        when ((((((x_16).dir_st) == ((Bit#(3))'(3'h4))) && (((x_16).dir_excl)
        == ((Bit#(2))'(2'h0))) ? ((Bit#(3))'(3'h4)) : (((((x_16).dir_st) ==
        ((Bit#(3))'(3'h3))) && (((x_16).dir_excl) == ((Bit#(2))'(2'h0))) ?
        ((Bit#(3))'(3'h3)) : (((((x_16).dir_st) == ((Bit#(3))'(3'h2))) &&
        ((((x_16).dir_sharers) | (((Bit#(4))'(4'h1)) << ((Bit#(2))'(2'h0))))
        == ((x_16).dir_sharers)) ? ((Bit#(3))'(3'h2)) :
        ((Bit#(3))'(3'h1)))))))) == ((Bit#(3))'(3'h3)), noAction);
        Struct1 x_17 = (x_3);
        Struct16 x_18 = (Struct16 {addr : (x_3).addr, info_write :
        (Bool)'(False), info_hit : (x_6).info_hit, info_way : (x_6).info_way,
        edir_hit : (x_6).edir_hit, edir_way : (x_6).edir_way, edir_slot :
        (x_6).edir_slot, info : (x_6).info, value_write : (Bool)'(False),
        value : unpack(0), may_victim : (x_6).may_victim, reps :
        (x_6).reps});
        Struct16 x_19 = (Struct16 {addr : (x_18).addr, info_write :
        (Bool)'(True), info_hit : (x_18).info_hit, info_way :
        (x_18).info_way, edir_hit : (x_18).edir_hit, edir_way :
        (x_18).edir_way, edir_slot : (x_18).edir_slot, info : Struct10
        {mesi_owned : ((x_18).info).mesi_owned, mesi_status :
        ((x_18).info).mesi_status, mesi_dir_st : (Struct15 {dir_st :
        (Bit#(3))'(3'h1), dir_excl : unpack(0), dir_sharers :
        unpack(0)}).dir_st, mesi_dir_sharers : (((Struct15 {dir_st :
        (Bit#(3))'(3'h1), dir_excl : unpack(0), dir_sharers :
        unpack(0)}).dir_st) == ((Bit#(3))'(3'h2)) ? ((Struct15 {dir_st :
        (Bit#(3))'(3'h1), dir_excl : unpack(0), dir_sharers :
        unpack(0)}).dir_sharers) : (((Bit#(4))'(4'h1)) << ((Struct15 {dir_st
        : (Bit#(3))'(3'h1), dir_excl : unpack(0), dir_sharers :
        unpack(0)}).dir_excl)))}, value_write : (x_18).value_write, value :
        (x_18).value, may_victim : (x_18).may_victim, reps :
        (x_18).reps});
        Struct16 x_20 = (Struct16 {addr : (x_19).addr, info_write :
        (Bool)'(True), info_hit : (x_19).info_hit, info_way :
        (x_19).info_way, edir_hit : (x_19).edir_hit, edir_way :
        (x_19).edir_way, edir_slot : (x_19).edir_slot, info : Struct10
        {mesi_owned : ((x_19).info).mesi_owned, mesi_status :
        (Bit#(3))'(3'h3), mesi_dir_st : ((x_19).info).mesi_dir_st,
        mesi_dir_sharers : ((x_19).info).mesi_dir_sharers}, value_write :
        (x_19).value_write, value : (x_19).value, may_victim :
        (x_19).may_victim, reps :
        (x_19).reps});
        let x_23 = ?;
        if ((x_8).valid) begin
            let x_21 <- victims__00__setVictim(Struct17 {victim_idx :
            (x_8).data, victim_info : (x_20).info, victim_value :
            ((x_20).value_write ? ((x_20).value) : (x_9))});
            x_23 = x_9;
        end else begin
            let x_22 <- cache__00__valueRsLineRq(x_20);
            x_23 = x_22;
        end
        Struct18 x_24 = (Struct18 {enq_type : ((((Bit#(4))'(4'h8))[3:2]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : (((((Bit#(4))'(4'h8))[3:2])
        == ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : ((Bit#(4))'(4'h8))[1:0], enq_msg : Struct1 {id :
        (Bit#(6))'(6'h16), type_ : (Bool)'(True), addr : (x_17).addr, value :
        unpack(0)}});
        let x_25 <- makeEnq_parentChildren00(x_24);
        let x_26 <- releaseMSHR_00(x_4);
    endrule

    rule rule_exec_00_28000;
        let x_0 <- deq_fifoL2E_00();
        Struct6 x_1 = ((x_0).lr_ir_pp);
        Bit#(4) x_2 = ((x_1).ir_msg_from);
        Struct1 x_3 = ((x_1).ir_msg);
        Bit#(3) x_4 = ((x_1).ir_mshr_id);
        Bool x_5 = ((x_1).ir_is_rs_rel);
        when (! (x_5), noAction);
        Struct9 x_6 = ((x_0).lr_ir);
        Struct10 x_7 = ((x_6).info);
        Struct5 x_8 = ((x_1).ir_by_victim);
        Vector#(4, Bit#(64)) x_9 = ((x_0).lr_value);
        let x_10 <- getMSHR_00(x_4);
        let x_11 <- getMSHRRq_00(x_4);
        Struct1 x_12 = (unpack(0));
        Vector#(4, Bit#(64)) x_13 = (unpack(0));
        Bool x_14 = ((x_7).mesi_owned);
        Bit#(3) x_15 = ((x_7).mesi_status);
        Struct15 x_16 = (Struct15 {dir_st : (((x_7).mesi_dir_st) ==
        ((Bit#(3))'(3'h0)) ? ((Bit#(3))'(3'h1)) : ((x_7).mesi_dir_st)),
        dir_excl : ((((x_7).mesi_dir_sharers)[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        ((((((x_7).mesi_dir_sharers)[3:1])[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        (((((((x_7).mesi_dir_sharers)[3:1])[2:1])[0:0]) == ((Bit#(1))'(1'h1))
        ? ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        ((((((((x_7).mesi_dir_sharers)[3:1])[2:1])[1:1])[0:0]) ==
        ((Bit#(1))'(1'h1)) ? ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        (unpack(0))))))))))))), dir_sharers : (x_7).mesi_dir_sharers});
        when ((x_2) == ((Bit#(4))'(4'h0)), noAction);
        when (((x_3).id) == ((Bit#(6))'(6'h15)), noAction);
        when (! ((x_3).type_), noAction);
        when ((((((x_16).dir_st) == ((Bit#(3))'(3'h4))) && (((x_16).dir_excl)
        == ((Bit#(2))'(2'h0))) ? ((Bit#(3))'(3'h4)) : (((((x_16).dir_st) ==
        ((Bit#(3))'(3'h3))) && (((x_16).dir_excl) == ((Bit#(2))'(2'h0))) ?
        ((Bit#(3))'(3'h3)) : (((((x_16).dir_st) == ((Bit#(3))'(3'h2))) &&
        ((((x_16).dir_sharers) | (((Bit#(4))'(4'h1)) << ((Bit#(2))'(2'h0))))
        == ((x_16).dir_sharers)) ? ((Bit#(3))'(3'h2)) :
        ((Bit#(3))'(3'h1)))))))) == ((Bit#(3))'(3'h1)), noAction);
        Struct1 x_17 = (x_3);
        Struct16 x_18 = (Struct16 {addr : (x_3).addr, info_write :
        (Bool)'(False), info_hit : (x_6).info_hit, info_way : (x_6).info_way,
        edir_hit : (x_6).edir_hit, edir_way : (x_6).edir_way, edir_slot :
        (x_6).edir_slot, info : (x_6).info, value_write : (Bool)'(False),
        value : unpack(0), may_victim : (x_6).may_victim, reps :
        (x_6).reps});
        let x_20 = ?;
        if ((x_8).valid) begin
            x_20 = x_9;
        end else begin
            let x_19 <- cache__00__valueRsLineRq(unpack(0));
            x_20 = x_19;
        end
        Struct18 x_21 = (Struct18 {enq_type : ((((Bit#(4))'(4'h8))[3:2]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : (((((Bit#(4))'(4'h8))[3:2])
        == ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : ((Bit#(4))'(4'h8))[1:0], enq_msg : Struct1 {id :
        (Bit#(6))'(6'h16), type_ : (Bool)'(True), addr : (x_17).addr, value :
        unpack(0)}});
        let x_22 <- makeEnq_parentChildren00(x_21);
        let x_23 <- releaseMSHR_00(x_4);
    endrule

    rule rule_exec_00_290000;
        let x_0 <- deq_fifoL2E_00();
        Struct6 x_1 = ((x_0).lr_ir_pp);
        Bit#(4) x_2 = ((x_1).ir_msg_from);
        Struct1 x_3 = ((x_1).ir_msg);
        Bit#(3) x_4 = ((x_1).ir_mshr_id);
        Bool x_5 = ((x_1).ir_is_rs_rel);
        when (! (x_5), noAction);
        Struct9 x_6 = ((x_0).lr_ir);
        Struct10 x_7 = ((x_6).info);
        Struct5 x_8 = ((x_1).ir_by_victim);
        Vector#(4, Bit#(64)) x_9 = ((x_0).lr_value);
        let x_10 <- getMSHR_00(x_4);
        let x_11 <- getMSHRRq_00(x_4);
        Struct1 x_12 = (unpack(0));
        Vector#(4, Bit#(64)) x_13 = (unpack(0));
        Bool x_14 = ((x_7).mesi_owned);
        Bit#(3) x_15 = ((x_7).mesi_status);
        Struct15 x_16 = (Struct15 {dir_st : (((x_7).mesi_dir_st) ==
        ((Bit#(3))'(3'h0)) ? ((Bit#(3))'(3'h1)) : ((x_7).mesi_dir_st)),
        dir_excl : ((((x_7).mesi_dir_sharers)[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        ((((((x_7).mesi_dir_sharers)[3:1])[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        (((((((x_7).mesi_dir_sharers)[3:1])[2:1])[0:0]) == ((Bit#(1))'(1'h1))
        ? ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        ((((((((x_7).mesi_dir_sharers)[3:1])[2:1])[1:1])[0:0]) ==
        ((Bit#(1))'(1'h1)) ? ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        (unpack(0))))))))))))), dir_sharers : (x_7).mesi_dir_sharers});
        when ((x_2) == ((Bit#(4))'(4'h0)), noAction);
        when (((x_3).id) == ((Bit#(6))'(6'h15)), noAction);
        when (! ((x_3).type_), noAction);
        when (((x_14) == ((Bool)'(False))) && (((((((x_16).dir_st) ==
        ((Bit#(3))'(3'h4))) && (((x_16).dir_excl) == ((Bit#(2))'(2'h0))) ?
        ((Bit#(3))'(3'h4)) : (((((x_16).dir_st) == ((Bit#(3))'(3'h3))) &&
        (((x_16).dir_excl) == ((Bit#(2))'(2'h0))) ? ((Bit#(3))'(3'h3)) :
        (((((x_16).dir_st) == ((Bit#(3))'(3'h2))) && ((((x_16).dir_sharers) |
        (((Bit#(4))'(4'h1)) << ((Bit#(2))'(2'h0)))) == ((x_16).dir_sharers))
        ? ((Bit#(3))'(3'h2)) : ((Bit#(3))'(3'h1)))))))) ==
        ((Bit#(3))'(3'h2))) && (((x_16).dir_sharers) == (((Bit#(4))'(4'h1))
        << ((Bit#(2))'(2'h0))))), noAction);
        Struct1 x_17 = (x_3);
        Struct16 x_18 = (Struct16 {addr : (x_3).addr, info_write :
        (Bool)'(False), info_hit : (x_6).info_hit, info_way : (x_6).info_way,
        edir_hit : (x_6).edir_hit, edir_way : (x_6).edir_way, edir_slot :
        (x_6).edir_slot, info : (x_6).info, value_write : (Bool)'(False),
        value : unpack(0), may_victim : (x_6).may_victim, reps :
        (x_6).reps});
        Struct16 x_19 = (Struct16 {addr : (x_18).addr, info_write :
        (Bool)'(True), info_hit : (x_18).info_hit, info_way :
        (x_18).info_way, edir_hit : (x_18).edir_hit, edir_way :
        (x_18).edir_way, edir_slot : (x_18).edir_slot, info : Struct10
        {mesi_owned : ((x_18).info).mesi_owned, mesi_status :
        ((x_18).info).mesi_status, mesi_dir_st : (Struct15 {dir_st :
        (Bit#(3))'(3'h1), dir_excl : unpack(0), dir_sharers :
        unpack(0)}).dir_st, mesi_dir_sharers : (((Struct15 {dir_st :
        (Bit#(3))'(3'h1), dir_excl : unpack(0), dir_sharers :
        unpack(0)}).dir_st) == ((Bit#(3))'(3'h2)) ? ((Struct15 {dir_st :
        (Bit#(3))'(3'h1), dir_excl : unpack(0), dir_sharers :
        unpack(0)}).dir_sharers) : (((Bit#(4))'(4'h1)) << ((Struct15 {dir_st
        : (Bit#(3))'(3'h1), dir_excl : unpack(0), dir_sharers :
        unpack(0)}).dir_excl)))}, value_write : (x_18).value_write, value :
        (x_18).value, may_victim : (x_18).may_victim, reps :
        (x_18).reps});
        let x_22 = ?;
        if ((x_8).valid) begin
            let x_20 <- victims__00__setVictim(Struct17 {victim_idx :
            (x_8).data, victim_info : (x_19).info, victim_value :
            ((x_19).value_write ? ((x_19).value) : (x_9))});
            x_22 = x_9;
        end else begin
            let x_21 <- cache__00__valueRsLineRq(x_19);
            x_22 = x_21;
        end
        Struct18 x_23 = (Struct18 {enq_type : ((((Bit#(4))'(4'h8))[3:2]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : (((((Bit#(4))'(4'h8))[3:2])
        == ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : ((Bit#(4))'(4'h8))[1:0], enq_msg : Struct1 {id :
        (Bit#(6))'(6'h16), type_ : (Bool)'(True), addr : (x_17).addr, value :
        unpack(0)}});
        let x_24 <- makeEnq_parentChildren00(x_23);
        let x_25 <- releaseMSHR_00(x_4);
    endrule

    rule rule_exec_00_291000;
        let x_0 <- deq_fifoL2E_00();
        Struct6 x_1 = ((x_0).lr_ir_pp);
        Bit#(4) x_2 = ((x_1).ir_msg_from);
        Struct1 x_3 = ((x_1).ir_msg);
        Bit#(3) x_4 = ((x_1).ir_mshr_id);
        Bool x_5 = ((x_1).ir_is_rs_rel);
        when (! (x_5), noAction);
        Struct9 x_6 = ((x_0).lr_ir);
        Struct10 x_7 = ((x_6).info);
        Struct5 x_8 = ((x_1).ir_by_victim);
        Vector#(4, Bit#(64)) x_9 = ((x_0).lr_value);
        let x_10 <- getMSHR_00(x_4);
        let x_11 <- getMSHRRq_00(x_4);
        Struct1 x_12 = (unpack(0));
        Vector#(4, Bit#(64)) x_13 = (unpack(0));
        Bool x_14 = ((x_7).mesi_owned);
        Bit#(3) x_15 = ((x_7).mesi_status);
        Struct15 x_16 = (Struct15 {dir_st : (((x_7).mesi_dir_st) ==
        ((Bit#(3))'(3'h0)) ? ((Bit#(3))'(3'h1)) : ((x_7).mesi_dir_st)),
        dir_excl : ((((x_7).mesi_dir_sharers)[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        ((((((x_7).mesi_dir_sharers)[3:1])[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        (((((((x_7).mesi_dir_sharers)[3:1])[2:1])[0:0]) == ((Bit#(1))'(1'h1))
        ? ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        ((((((((x_7).mesi_dir_sharers)[3:1])[2:1])[1:1])[0:0]) ==
        ((Bit#(1))'(1'h1)) ? ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        (unpack(0))))))))))))), dir_sharers : (x_7).mesi_dir_sharers});
        when ((x_2) == ((Bit#(4))'(4'h0)), noAction);
        when (((x_3).id) == ((Bit#(6))'(6'h15)), noAction);
        when (! ((x_3).type_), noAction);
        when (((((((x_16).dir_st) == ((Bit#(3))'(3'h4))) &&
        (((x_16).dir_excl) == ((Bit#(2))'(2'h0))) ? ((Bit#(3))'(3'h4)) :
        (((((x_16).dir_st) == ((Bit#(3))'(3'h3))) && (((x_16).dir_excl) ==
        ((Bit#(2))'(2'h0))) ? ((Bit#(3))'(3'h3)) : (((((x_16).dir_st) ==
        ((Bit#(3))'(3'h2))) && ((((x_16).dir_sharers) | (((Bit#(4))'(4'h1))
        << ((Bit#(2))'(2'h0)))) == ((x_16).dir_sharers)) ? ((Bit#(3))'(3'h2))
        : ((Bit#(3))'(3'h1)))))))) == ((Bit#(3))'(3'h2))) &&
        (((Bit#(3))'(3'h1)) < ((((((x_16).dir_sharers)[0:0]) ==
        ((Bit#(1))'(1'h1)) ? ((Bit#(3))'(3'h1)) : ((Bit#(3))'(3'h0)))) +
        (((((((x_16).dir_sharers)[3:1])[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(3))'(3'h1)) : ((Bit#(3))'(3'h0)))) +
        ((((((((x_16).dir_sharers)[3:1])[2:1])[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(3))'(3'h1)) : ((Bit#(3))'(3'h0)))) +
        (((((((((x_16).dir_sharers)[3:1])[2:1])[1:1])[0:0]) ==
        ((Bit#(1))'(1'h1)) ? ((Bit#(3))'(3'h1)) : ((Bit#(3))'(3'h0)))) +
        (unpack(0))))))), noAction);
        Struct1 x_17 = (x_3);
        Struct16 x_18 = (Struct16 {addr : (x_3).addr, info_write :
        (Bool)'(False), info_hit : (x_6).info_hit, info_way : (x_6).info_way,
        edir_hit : (x_6).edir_hit, edir_way : (x_6).edir_way, edir_slot :
        (x_6).edir_slot, info : (x_6).info, value_write : (Bool)'(False),
        value : unpack(0), may_victim : (x_6).may_victim, reps :
        (x_6).reps});
        Struct16 x_19 = (Struct16 {addr : (x_18).addr, info_write :
        (Bool)'(True), info_hit : (x_18).info_hit, info_way :
        (x_18).info_way, edir_hit : (x_18).edir_hit, edir_way :
        (x_18).edir_way, edir_slot : (x_18).edir_slot, info : Struct10
        {mesi_owned : ((x_18).info).mesi_owned, mesi_status :
        ((x_18).info).mesi_status, mesi_dir_st : (Struct15 {dir_st :
        (Bit#(3))'(3'h2), dir_excl : (x_16).dir_excl, dir_sharers :
        ((x_16).dir_sharers) & (~(((Bit#(4))'(4'h1)) <<
        ((Bit#(2))'(2'h0))))}).dir_st, mesi_dir_sharers : (((Struct15 {dir_st
        : (Bit#(3))'(3'h2), dir_excl : (x_16).dir_excl, dir_sharers :
        ((x_16).dir_sharers) & (~(((Bit#(4))'(4'h1)) <<
        ((Bit#(2))'(2'h0))))}).dir_st) == ((Bit#(3))'(3'h2)) ? ((Struct15
        {dir_st : (Bit#(3))'(3'h2), dir_excl : (x_16).dir_excl, dir_sharers :
        ((x_16).dir_sharers) & (~(((Bit#(4))'(4'h1)) <<
        ((Bit#(2))'(2'h0))))}).dir_sharers) : (((Bit#(4))'(4'h1)) <<
        ((Struct15 {dir_st : (Bit#(3))'(3'h2), dir_excl : (x_16).dir_excl,
        dir_sharers : ((x_16).dir_sharers) & (~(((Bit#(4))'(4'h1)) <<
        ((Bit#(2))'(2'h0))))}).dir_excl)))}, value_write :
        (x_18).value_write, value : (x_18).value, may_victim :
        (x_18).may_victim, reps :
        (x_18).reps});
        let x_22 = ?;
        if ((x_8).valid) begin
            let x_20 <- victims__00__setVictim(Struct17 {victim_idx :
            (x_8).data, victim_info : (x_19).info, victim_value :
            ((x_19).value_write ? ((x_19).value) : (x_9))});
            x_22 = x_9;
        end else begin
            let x_21 <- cache__00__valueRsLineRq(x_19);
            x_22 = x_21;
        end
        Struct18 x_23 = (Struct18 {enq_type : ((((Bit#(4))'(4'h8))[3:2]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : (((((Bit#(4))'(4'h8))[3:2])
        == ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : ((Bit#(4))'(4'h8))[1:0], enq_msg : Struct1 {id :
        (Bit#(6))'(6'h16), type_ : (Bool)'(True), addr : (x_17).addr, value :
        unpack(0)}});
        let x_24 <- makeEnq_parentChildren00(x_23);
        let x_25 <- releaseMSHR_00(x_4);
    endrule

    rule rule_exec_00_210000;
        let x_0 <- deq_fifoL2E_00();
        Struct6 x_1 = ((x_0).lr_ir_pp);
        Bit#(4) x_2 = ((x_1).ir_msg_from);
        Struct1 x_3 = ((x_1).ir_msg);
        Bit#(3) x_4 = ((x_1).ir_mshr_id);
        Bool x_5 = ((x_1).ir_is_rs_rel);
        when (! (x_5), noAction);
        Struct9 x_6 = ((x_0).lr_ir);
        Struct10 x_7 = ((x_6).info);
        Struct5 x_8 = ((x_1).ir_by_victim);
        Vector#(4, Bit#(64)) x_9 = ((x_0).lr_value);
        let x_10 <- getMSHR_00(x_4);
        let x_11 <- getMSHRRq_00(x_4);
        Struct1 x_12 = (unpack(0));
        Vector#(4, Bit#(64)) x_13 = (unpack(0));
        Bool x_14 = ((x_7).mesi_owned);
        Bit#(3) x_15 = ((x_7).mesi_status);
        Struct15 x_16 = (Struct15 {dir_st : (((x_7).mesi_dir_st) ==
        ((Bit#(3))'(3'h0)) ? ((Bit#(3))'(3'h1)) : ((x_7).mesi_dir_st)),
        dir_excl : ((((x_7).mesi_dir_sharers)[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        ((((((x_7).mesi_dir_sharers)[3:1])[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        (((((((x_7).mesi_dir_sharers)[3:1])[2:1])[0:0]) == ((Bit#(1))'(1'h1))
        ? ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        ((((((((x_7).mesi_dir_sharers)[3:1])[2:1])[1:1])[0:0]) ==
        ((Bit#(1))'(1'h1)) ? ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        (unpack(0))))))))))))), dir_sharers : (x_7).mesi_dir_sharers});
        when ((x_2) == ((Bit#(4))'(4'h0)), noAction);
        when (((x_3).id) == ((Bit#(6))'(6'h15)), noAction);
        when (! ((x_3).type_), noAction);
        when (((x_14) == ((Bool)'(True))) && (((x_15) == ((Bit#(3))'(3'h2)))
        && (((((((x_16).dir_st) == ((Bit#(3))'(3'h4))) && (((x_16).dir_excl)
        == ((Bit#(2))'(2'h0))) ? ((Bit#(3))'(3'h4)) : (((((x_16).dir_st) ==
        ((Bit#(3))'(3'h3))) && (((x_16).dir_excl) == ((Bit#(2))'(2'h0))) ?
        ((Bit#(3))'(3'h3)) : (((((x_16).dir_st) == ((Bit#(3))'(3'h2))) &&
        ((((x_16).dir_sharers) | (((Bit#(4))'(4'h1)) << ((Bit#(2))'(2'h0))))
        == ((x_16).dir_sharers)) ? ((Bit#(3))'(3'h2)) :
        ((Bit#(3))'(3'h1)))))))) == ((Bit#(3))'(3'h2))) &&
        (((x_16).dir_sharers) == (((Bit#(4))'(4'h1)) <<
        ((Bit#(2))'(2'h0)))))), noAction);
        Struct1 x_17 = (x_3);
        Struct16 x_18 = (Struct16 {addr : (x_3).addr, info_write :
        (Bool)'(False), info_hit : (x_6).info_hit, info_way : (x_6).info_way,
        edir_hit : (x_6).edir_hit, edir_way : (x_6).edir_way, edir_slot :
        (x_6).edir_slot, info : (x_6).info, value_write : (Bool)'(False),
        value : unpack(0), may_victim : (x_6).may_victim, reps :
        (x_6).reps});
        Struct16 x_19 = (Struct16 {addr : (x_18).addr, info_write :
        (Bool)'(True), info_hit : (x_18).info_hit, info_way :
        (x_18).info_way, edir_hit : (x_18).edir_hit, edir_way :
        (x_18).edir_way, edir_slot : (x_18).edir_slot, info : Struct10
        {mesi_owned : ((x_18).info).mesi_owned, mesi_status :
        ((x_18).info).mesi_status, mesi_dir_st : (Struct15 {dir_st :
        (Bit#(3))'(3'h1), dir_excl : unpack(0), dir_sharers :
        unpack(0)}).dir_st, mesi_dir_sharers : (((Struct15 {dir_st :
        (Bit#(3))'(3'h1), dir_excl : unpack(0), dir_sharers :
        unpack(0)}).dir_st) == ((Bit#(3))'(3'h2)) ? ((Struct15 {dir_st :
        (Bit#(3))'(3'h1), dir_excl : unpack(0), dir_sharers :
        unpack(0)}).dir_sharers) : (((Bit#(4))'(4'h1)) << ((Struct15 {dir_st
        : (Bit#(3))'(3'h1), dir_excl : unpack(0), dir_sharers :
        unpack(0)}).dir_excl)))}, value_write : (x_18).value_write, value :
        (x_18).value, may_victim : (x_18).may_victim, reps :
        (x_18).reps});
        Struct16 x_20 = (Struct16 {addr : (x_19).addr, info_write :
        (Bool)'(True), info_hit : (x_19).info_hit, info_way :
        (x_19).info_way, edir_hit : (x_19).edir_hit, edir_way :
        (x_19).edir_way, edir_slot : (x_19).edir_slot, info : Struct10
        {mesi_owned : ((x_19).info).mesi_owned, mesi_status :
        (Bit#(3))'(3'h4), mesi_dir_st : ((x_19).info).mesi_dir_st,
        mesi_dir_sharers : ((x_19).info).mesi_dir_sharers}, value_write :
        (x_19).value_write, value : (x_19).value, may_victim :
        (x_19).may_victim, reps :
        (x_19).reps});
        let x_23 = ?;
        if ((x_8).valid) begin
            let x_21 <- victims__00__setVictim(Struct17 {victim_idx :
            (x_8).data, victim_info : (x_20).info, victim_value :
            ((x_20).value_write ? ((x_20).value) : (x_9))});
            x_23 = x_9;
        end else begin
            let x_22 <- cache__00__valueRsLineRq(x_20);
            x_23 = x_22;
        end
        Struct18 x_24 = (Struct18 {enq_type : ((((Bit#(4))'(4'h8))[3:2]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : (((((Bit#(4))'(4'h8))[3:2])
        == ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : ((Bit#(4))'(4'h8))[1:0], enq_msg : Struct1 {id :
        (Bit#(6))'(6'h16), type_ : (Bool)'(True), addr : (x_17).addr, value :
        unpack(0)}});
        let x_25 <- makeEnq_parentChildren00(x_24);
        let x_26 <- releaseMSHR_00(x_4);
    endrule

    rule rule_exec_00_211000;
        let x_0 <- deq_fifoL2E_00();
        Struct6 x_1 = ((x_0).lr_ir_pp);
        Bit#(4) x_2 = ((x_1).ir_msg_from);
        Struct1 x_3 = ((x_1).ir_msg);
        Bit#(3) x_4 = ((x_1).ir_mshr_id);
        Bool x_5 = ((x_1).ir_is_rs_rel);
        when (! (x_5), noAction);
        Struct9 x_6 = ((x_0).lr_ir);
        Struct10 x_7 = ((x_6).info);
        Struct5 x_8 = ((x_1).ir_by_victim);
        Vector#(4, Bit#(64)) x_9 = ((x_0).lr_value);
        let x_10 <- getMSHR_00(x_4);
        let x_11 <- getMSHRRq_00(x_4);
        Struct1 x_12 = (unpack(0));
        Vector#(4, Bit#(64)) x_13 = (unpack(0));
        Bool x_14 = ((x_7).mesi_owned);
        Bit#(3) x_15 = ((x_7).mesi_status);
        Struct15 x_16 = (Struct15 {dir_st : (((x_7).mesi_dir_st) ==
        ((Bit#(3))'(3'h0)) ? ((Bit#(3))'(3'h1)) : ((x_7).mesi_dir_st)),
        dir_excl : ((((x_7).mesi_dir_sharers)[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        ((((((x_7).mesi_dir_sharers)[3:1])[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        (((((((x_7).mesi_dir_sharers)[3:1])[2:1])[0:0]) == ((Bit#(1))'(1'h1))
        ? ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        ((((((((x_7).mesi_dir_sharers)[3:1])[2:1])[1:1])[0:0]) ==
        ((Bit#(1))'(1'h1)) ? ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        (unpack(0))))))))))))), dir_sharers : (x_7).mesi_dir_sharers});
        when ((x_2) == ((Bit#(4))'(4'h0)), noAction);
        when (((x_3).id) == ((Bit#(6))'(6'h15)), noAction);
        when (! ((x_3).type_), noAction);
        when (! ((((((x_16).dir_st) == ((Bit#(3))'(3'h4))) &&
        (((x_16).dir_excl) == ((Bit#(2))'(2'h0))) ? ((Bit#(3))'(3'h4)) :
        (((((x_16).dir_st) == ((Bit#(3))'(3'h3))) && (((x_16).dir_excl) ==
        ((Bit#(2))'(2'h0))) ? ((Bit#(3))'(3'h3)) : (((((x_16).dir_st) ==
        ((Bit#(3))'(3'h2))) && ((((x_16).dir_sharers) | (((Bit#(4))'(4'h1))
        << ((Bit#(2))'(2'h0)))) == ((x_16).dir_sharers)) ? ((Bit#(3))'(3'h2))
        : ((Bit#(3))'(3'h1)))))))) < ((Bit#(3))'(3'h3))), noAction);
        Struct1 x_17 = (x_3);
        Struct16 x_18 = (Struct16 {addr : (x_3).addr, info_write :
        (Bool)'(False), info_hit : (x_6).info_hit, info_way : (x_6).info_way,
        edir_hit : (x_6).edir_hit, edir_way : (x_6).edir_way, edir_slot :
        (x_6).edir_slot, info : (x_6).info, value_write : (Bool)'(False),
        value : unpack(0), may_victim : (x_6).may_victim, reps :
        (x_6).reps});
        Struct16 x_19 = (Struct16 {addr : (x_18).addr, info_write :
        (x_18).info_write, info_hit : (x_18).info_hit, info_way :
        (x_18).info_way, edir_hit : (x_18).edir_hit, edir_way :
        (x_18).edir_way, edir_slot : (x_18).edir_slot, info : (x_18).info,
        value_write : (Bool)'(True), value : (x_17).value, may_victim :
        (x_18).may_victim, reps : (x_18).reps});
        Struct16 x_20 = (Struct16 {addr : (x_19).addr, info_write :
        (Bool)'(True), info_hit : (x_19).info_hit, info_way :
        (x_19).info_way, edir_hit : (x_19).edir_hit, edir_way :
        (x_19).edir_way, edir_slot : (x_19).edir_slot, info : Struct10
        {mesi_owned : ((x_19).info).mesi_owned, mesi_status :
        (Bit#(3))'(3'h4), mesi_dir_st : ((x_19).info).mesi_dir_st,
        mesi_dir_sharers : ((x_19).info).mesi_dir_sharers}, value_write :
        (x_19).value_write, value : (x_19).value, may_victim :
        (x_19).may_victim, reps : (x_19).reps});
        Struct16 x_21 = (Struct16 {addr : (x_20).addr, info_write :
        (Bool)'(True), info_hit : (x_20).info_hit, info_way :
        (x_20).info_way, edir_hit : (x_20).edir_hit, edir_way :
        (x_20).edir_way, edir_slot : (x_20).edir_slot, info : Struct10
        {mesi_owned : (Bool)'(True), mesi_status : ((x_20).info).mesi_status,
        mesi_dir_st : ((x_20).info).mesi_dir_st, mesi_dir_sharers :
        ((x_20).info).mesi_dir_sharers}, value_write : (x_20).value_write,
        value : (x_20).value, may_victim : (x_20).may_victim, reps :
        (x_20).reps});
        Struct16 x_22 = (Struct16 {addr : (x_21).addr, info_write :
        (Bool)'(True), info_hit : (x_21).info_hit, info_way :
        (x_21).info_way, edir_hit : (x_21).edir_hit, edir_way :
        (x_21).edir_way, edir_slot : (x_21).edir_slot, info : Struct10
        {mesi_owned : ((x_21).info).mesi_owned, mesi_status :
        ((x_21).info).mesi_status, mesi_dir_st : (Struct15 {dir_st :
        (Bit#(3))'(3'h1), dir_excl : unpack(0), dir_sharers :
        unpack(0)}).dir_st, mesi_dir_sharers : (((Struct15 {dir_st :
        (Bit#(3))'(3'h1), dir_excl : unpack(0), dir_sharers :
        unpack(0)}).dir_st) == ((Bit#(3))'(3'h2)) ? ((Struct15 {dir_st :
        (Bit#(3))'(3'h1), dir_excl : unpack(0), dir_sharers :
        unpack(0)}).dir_sharers) : (((Bit#(4))'(4'h1)) << ((Struct15 {dir_st
        : (Bit#(3))'(3'h1), dir_excl : unpack(0), dir_sharers :
        unpack(0)}).dir_excl)))}, value_write : (x_21).value_write, value :
        (x_21).value, may_victim : (x_21).may_victim, reps :
        (x_21).reps});
        let x_25 = ?;
        if ((x_8).valid) begin
            let x_23 <- victims__00__setVictim(Struct17 {victim_idx :
            (x_8).data, victim_info : (x_22).info, victim_value :
            ((x_22).value_write ? ((x_22).value) : (x_9))});
            x_25 = x_9;
        end else begin
            let x_24 <- cache__00__valueRsLineRq(x_22);
            x_25 = x_24;
        end
        Struct18 x_26 = (Struct18 {enq_type : ((((Bit#(4))'(4'h8))[3:2]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : (((((Bit#(4))'(4'h8))[3:2])
        == ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : ((Bit#(4))'(4'h8))[1:0], enq_msg : Struct1 {id :
        (Bit#(6))'(6'h16), type_ : (Bool)'(True), addr : (x_17).addr, value :
        unpack(0)}});
        let x_27 <- makeEnq_parentChildren00(x_26);
        let x_28 <- releaseMSHR_00(x_4);
    endrule

    rule rule_exec_00_000001;
        let x_0 <- deq_fifoL2E_00();
        Struct6 x_1 = ((x_0).lr_ir_pp);
        Bit#(4) x_2 = ((x_1).ir_msg_from);
        Struct1 x_3 = ((x_1).ir_msg);
        Bit#(3) x_4 = ((x_1).ir_mshr_id);
        Bool x_5 = ((x_1).ir_is_rs_rel);
        when (! (x_5), noAction);
        Struct9 x_6 = ((x_0).lr_ir);
        Struct10 x_7 = ((x_6).info);
        Struct5 x_8 = ((x_1).ir_by_victim);
        Vector#(4, Bit#(64)) x_9 = ((x_0).lr_value);
        let x_10 <- getMSHR_00(x_4);
        let x_11 <- getMSHRRq_00(x_4);
        Struct1 x_12 = (unpack(0));
        Vector#(4, Bit#(64)) x_13 = (unpack(0));
        Bool x_14 = ((x_7).mesi_owned);
        Bit#(3) x_15 = ((x_7).mesi_status);
        Struct15 x_16 = (Struct15 {dir_st : (((x_7).mesi_dir_st) ==
        ((Bit#(3))'(3'h0)) ? ((Bit#(3))'(3'h1)) : ((x_7).mesi_dir_st)),
        dir_excl : ((((x_7).mesi_dir_sharers)[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        ((((((x_7).mesi_dir_sharers)[3:1])[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        (((((((x_7).mesi_dir_sharers)[3:1])[2:1])[0:0]) == ((Bit#(1))'(1'h1))
        ? ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        ((((((((x_7).mesi_dir_sharers)[3:1])[2:1])[1:1])[0:0]) ==
        ((Bit#(1))'(1'h1)) ? ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        (unpack(0))))))))))))), dir_sharers : (x_7).mesi_dir_sharers});
        when ((x_2) == ((Bit#(4))'(4'h1)), noAction);
        when (((x_3).id) == ((Bit#(6))'(6'h2)), noAction);
        when (! ((x_3).type_), noAction);
        when ((! (((Bit#(3))'(3'h2)) < ((x_16).dir_st))) && ((x_15) ==
        ((Bit#(3))'(3'h2))), noAction);
        Struct1 x_17 = (x_3);
        Struct16 x_18 = (Struct16 {addr : (x_3).addr, info_write :
        (Bool)'(False), info_hit : (x_6).info_hit, info_way : (x_6).info_way,
        edir_hit : (x_6).edir_hit, edir_way : (x_6).edir_way, edir_slot :
        (x_6).edir_slot, info : (x_6).info, value_write : (Bool)'(False),
        value : unpack(0), may_victim : (x_6).may_victim, reps :
        (x_6).reps});
        Struct16 x_19 = (Struct16 {addr : (x_18).addr, info_write :
        (Bool)'(True), info_hit : (x_18).info_hit, info_way :
        (x_18).info_way, edir_hit : (x_18).edir_hit, edir_way :
        (x_18).edir_way, edir_slot : (x_18).edir_slot, info : Struct10
        {mesi_owned : ((x_18).info).mesi_owned, mesi_status :
        ((x_18).info).mesi_status, mesi_dir_st : (Struct15 {dir_st :
        (Bit#(3))'(3'h2), dir_excl : (x_16).dir_excl, dir_sharers :
        (((x_16).dir_st) == ((Bit#(3))'(3'h2)) ? (((x_16).dir_sharers) |
        (((Bit#(4))'(4'h1)) << ((Bit#(2))'(2'h1)))) : (((Bit#(4))'(4'h1)) <<
        ((Bit#(2))'(2'h1))))}).dir_st, mesi_dir_sharers : (((Struct15 {dir_st
        : (Bit#(3))'(3'h2), dir_excl : (x_16).dir_excl, dir_sharers :
        (((x_16).dir_st) == ((Bit#(3))'(3'h2)) ? (((x_16).dir_sharers) |
        (((Bit#(4))'(4'h1)) << ((Bit#(2))'(2'h1)))) : (((Bit#(4))'(4'h1)) <<
        ((Bit#(2))'(2'h1))))}).dir_st) == ((Bit#(3))'(3'h2)) ? ((Struct15
        {dir_st : (Bit#(3))'(3'h2), dir_excl : (x_16).dir_excl, dir_sharers :
        (((x_16).dir_st) == ((Bit#(3))'(3'h2)) ? (((x_16).dir_sharers) |
        (((Bit#(4))'(4'h1)) << ((Bit#(2))'(2'h1)))) : (((Bit#(4))'(4'h1)) <<
        ((Bit#(2))'(2'h1))))}).dir_sharers) : (((Bit#(4))'(4'h1)) <<
        ((Struct15 {dir_st : (Bit#(3))'(3'h2), dir_excl : (x_16).dir_excl,
        dir_sharers : (((x_16).dir_st) == ((Bit#(3))'(3'h2)) ?
        (((x_16).dir_sharers) | (((Bit#(4))'(4'h1)) << ((Bit#(2))'(2'h1)))) :
        (((Bit#(4))'(4'h1)) << ((Bit#(2))'(2'h1))))}).dir_excl)))},
        value_write : (x_18).value_write, value : (x_18).value, may_victim :
        (x_18).may_victim, reps :
        (x_18).reps});
        let x_22 = ?;
        if ((x_8).valid) begin
            let x_20 <- victims__00__setVictim(Struct17 {victim_idx :
            (x_8).data, victim_info : (x_19).info, victim_value :
            ((x_19).value_write ? ((x_19).value) : (x_9))});
            x_22 = x_9;
        end else begin
            let x_21 <- cache__00__valueRsLineRq(x_19);
            x_22 = x_21;
        end
        Struct18 x_23 = (Struct18 {enq_type : ((((Bit#(4))'(4'h9))[3:2]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : (((((Bit#(4))'(4'h9))[3:2])
        == ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : ((Bit#(4))'(4'h9))[1:0], enq_msg : Struct1 {id :
        (Bit#(6))'(6'h3), type_ : (Bool)'(True), addr : (x_17).addr, value :
        x_22}});
        let x_24 <- makeEnq_parentChildren00(x_23);
        let x_25 <- releaseMSHR_00(x_4);
    endrule

    rule rule_exec_00_001001;
        let x_0 <- deq_fifoL2E_00();
        Struct6 x_1 = ((x_0).lr_ir_pp);
        Bit#(4) x_2 = ((x_1).ir_msg_from);
        Struct1 x_3 = ((x_1).ir_msg);
        Bit#(3) x_4 = ((x_1).ir_mshr_id);
        Bool x_5 = ((x_1).ir_is_rs_rel);
        when (! (x_5), noAction);
        Struct9 x_6 = ((x_0).lr_ir);
        Struct10 x_7 = ((x_6).info);
        Struct5 x_8 = ((x_1).ir_by_victim);
        Vector#(4, Bit#(64)) x_9 = ((x_0).lr_value);
        let x_10 <- getMSHR_00(x_4);
        let x_11 <- getMSHRRq_00(x_4);
        Struct1 x_12 = (unpack(0));
        Vector#(4, Bit#(64)) x_13 = (unpack(0));
        Bool x_14 = ((x_7).mesi_owned);
        Bit#(3) x_15 = ((x_7).mesi_status);
        Struct15 x_16 = (Struct15 {dir_st : (((x_7).mesi_dir_st) ==
        ((Bit#(3))'(3'h0)) ? ((Bit#(3))'(3'h1)) : ((x_7).mesi_dir_st)),
        dir_excl : ((((x_7).mesi_dir_sharers)[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        ((((((x_7).mesi_dir_sharers)[3:1])[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        (((((((x_7).mesi_dir_sharers)[3:1])[2:1])[0:0]) == ((Bit#(1))'(1'h1))
        ? ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        ((((((((x_7).mesi_dir_sharers)[3:1])[2:1])[1:1])[0:0]) ==
        ((Bit#(1))'(1'h1)) ? ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        (unpack(0))))))))))))), dir_sharers : (x_7).mesi_dir_sharers});
        when ((x_2) == ((Bit#(4))'(4'h1)), noAction);
        when (((x_3).id) == ((Bit#(6))'(6'h2)), noAction);
        when (! ((x_3).type_), noAction);
        when ((! ((x_15) < ((Bit#(3))'(3'h3)))) && (((x_16).dir_st) ==
        ((Bit#(3))'(3'h1))), noAction);
        Struct1 x_17 = (x_3);
        Struct16 x_18 = (Struct16 {addr : (x_3).addr, info_write :
        (Bool)'(False), info_hit : (x_6).info_hit, info_way : (x_6).info_way,
        edir_hit : (x_6).edir_hit, edir_way : (x_6).edir_way, edir_slot :
        (x_6).edir_slot, info : (x_6).info, value_write : (Bool)'(False),
        value : unpack(0), may_victim : (x_6).may_victim, reps :
        (x_6).reps});
        Struct16 x_19 = (Struct16 {addr : (x_18).addr, info_write :
        (Bool)'(True), info_hit : (x_18).info_hit, info_way :
        (x_18).info_way, edir_hit : (x_18).edir_hit, edir_way :
        (x_18).edir_way, edir_slot : (x_18).edir_slot, info : Struct10
        {mesi_owned : ((x_18).info).mesi_owned, mesi_status :
        ((x_18).info).mesi_status, mesi_dir_st : (Struct15 {dir_st :
        (Bit#(3))'(3'h3), dir_excl : (Bit#(2))'(2'h1), dir_sharers :
        unpack(0)}).dir_st, mesi_dir_sharers : (((Struct15 {dir_st :
        (Bit#(3))'(3'h3), dir_excl : (Bit#(2))'(2'h1), dir_sharers :
        unpack(0)}).dir_st) == ((Bit#(3))'(3'h2)) ? ((Struct15 {dir_st :
        (Bit#(3))'(3'h3), dir_excl : (Bit#(2))'(2'h1), dir_sharers :
        unpack(0)}).dir_sharers) : (((Bit#(4))'(4'h1)) << ((Struct15 {dir_st
        : (Bit#(3))'(3'h3), dir_excl : (Bit#(2))'(2'h1), dir_sharers :
        unpack(0)}).dir_excl)))}, value_write : (x_18).value_write, value :
        (x_18).value, may_victim : (x_18).may_victim, reps :
        (x_18).reps});
        Struct16 x_20 = (Struct16 {addr : (x_19).addr, info_write :
        (Bool)'(True), info_hit : (x_19).info_hit, info_way :
        (x_19).info_way, edir_hit : (x_19).edir_hit, edir_way :
        (x_19).edir_way, edir_slot : (x_19).edir_slot, info : Struct10
        {mesi_owned : ((x_19).info).mesi_owned, mesi_status :
        (Bit#(3))'(3'h1), mesi_dir_st : ((x_19).info).mesi_dir_st,
        mesi_dir_sharers : ((x_19).info).mesi_dir_sharers}, value_write :
        (x_19).value_write, value : (x_19).value, may_victim :
        (x_19).may_victim, reps :
        (x_19).reps});
        let x_23 = ?;
        if ((x_8).valid) begin
            let x_21 <- victims__00__setVictim(Struct17 {victim_idx :
            (x_8).data, victim_info : (x_20).info, victim_value :
            ((x_20).value_write ? ((x_20).value) : (x_9))});
            x_23 = x_9;
        end else begin
            let x_22 <- cache__00__valueRsLineRq(x_20);
            x_23 = x_22;
        end
        Struct18 x_24 = (Struct18 {enq_type : ((((Bit#(4))'(4'h9))[3:2]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : (((((Bit#(4))'(4'h9))[3:2])
        == ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : ((Bit#(4))'(4'h9))[1:0], enq_msg : Struct1 {id :
        (Bit#(6))'(6'h4), type_ : (Bool)'(True), addr : (x_17).addr, value :
        x_23}});
        let x_25 <- makeEnq_parentChildren00(x_24);
        let x_26 <- releaseMSHR_00(x_4);
    endrule

    rule rule_exec_00_01001;
        let x_0 <- deq_fifoL2E_00();
        Struct6 x_1 = ((x_0).lr_ir_pp);
        Bit#(4) x_2 = ((x_1).ir_msg_from);
        Struct1 x_3 = ((x_1).ir_msg);
        Bit#(3) x_4 = ((x_1).ir_mshr_id);
        Bool x_5 = ((x_1).ir_is_rs_rel);
        when (! (x_5), noAction);
        Struct9 x_6 = ((x_0).lr_ir);
        Struct10 x_7 = ((x_6).info);
        Struct5 x_8 = ((x_1).ir_by_victim);
        Vector#(4, Bit#(64)) x_9 = ((x_0).lr_value);
        let x_10 <- getMSHR_00(x_4);
        let x_11 <- getMSHRRq_00(x_4);
        Struct1 x_12 = (unpack(0));
        Vector#(4, Bit#(64)) x_13 = (unpack(0));
        Bool x_14 = ((x_7).mesi_owned);
        Bit#(3) x_15 = ((x_7).mesi_status);
        Struct15 x_16 = (Struct15 {dir_st : (((x_7).mesi_dir_st) ==
        ((Bit#(3))'(3'h0)) ? ((Bit#(3))'(3'h1)) : ((x_7).mesi_dir_st)),
        dir_excl : ((((x_7).mesi_dir_sharers)[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        ((((((x_7).mesi_dir_sharers)[3:1])[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        (((((((x_7).mesi_dir_sharers)[3:1])[2:1])[0:0]) == ((Bit#(1))'(1'h1))
        ? ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        ((((((((x_7).mesi_dir_sharers)[3:1])[2:1])[1:1])[0:0]) ==
        ((Bit#(1))'(1'h1)) ? ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        (unpack(0))))))))))))), dir_sharers : (x_7).mesi_dir_sharers});
        when ((x_2) == ((Bit#(4))'(4'h1)), noAction);
        when (((x_3).id) == ((Bit#(6))'(6'h2)), noAction);
        when (! ((x_3).type_), noAction);
        when (((x_14) == ((Bool)'(False))) && ((! (((Bit#(3))'(3'h1)) <
        (x_15))) && (! (((Bit#(3))'(3'h2)) < ((x_16).dir_st)))),
        noAction);
        Struct1 x_17 = (x_3);
        Struct16 x_18 = (Struct16 {addr : (x_3).addr, info_write :
        (Bool)'(False), info_hit : (x_6).info_hit, info_way : (x_6).info_way,
        edir_hit : (x_6).edir_hit, edir_way : (x_6).edir_way, edir_slot :
        (x_6).edir_slot, info : (x_6).info, value_write : (Bool)'(False),
        value : unpack(0), may_victim : (x_6).may_victim, reps :
        (x_6).reps});
        let x_20 = ?;
        if ((x_8).valid) begin
            x_20 = x_9;
        end else begin
            let x_19 <- cache__00__valueRsLineRq(unpack(0));
            x_20 = x_19;
        end
        let x_21 <- registerUL_00(Struct19 {r_id : x_4, r_ul_rsb :
        (Bool)'(True), r_ul_rsbTo : ((Bit#(4))'(4'h9))[1:0]});
        Struct18 x_22 = (Struct18 {enq_type : ((((Bit#(4))'(4'h0))[3:2]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : (((((Bit#(4))'(4'h0))[3:2])
        == ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : ((Bit#(4))'(4'h0))[1:0], enq_msg : Struct1 {id :
        (Bit#(6))'(6'h2), type_ : (Bool)'(False), addr : (x_17).addr, value :
        unpack(0)}});
        let x_23 <- makeEnq_parentChildren00(x_22);
    endrule

    rule rule_exec_00_03001;
        let x_0 <- deq_fifoL2E_00();
        Struct6 x_1 = ((x_0).lr_ir_pp);
        Bit#(4) x_2 = ((x_1).ir_msg_from);
        Struct1 x_3 = ((x_1).ir_msg);
        Bit#(3) x_4 = ((x_1).ir_mshr_id);
        Bool x_5 = ((x_1).ir_is_rs_rel);
        when (! (x_5), noAction);
        Struct9 x_6 = ((x_0).lr_ir);
        Struct10 x_7 = ((x_6).info);
        Struct5 x_8 = ((x_1).ir_by_victim);
        Vector#(4, Bit#(64)) x_9 = ((x_0).lr_value);
        let x_10 <- getMSHR_00(x_4);
        let x_11 <- getMSHRRq_00(x_4);
        Struct1 x_12 = (unpack(0));
        Vector#(4, Bit#(64)) x_13 = (unpack(0));
        Bool x_14 = ((x_7).mesi_owned);
        Bit#(3) x_15 = ((x_7).mesi_status);
        Struct15 x_16 = (Struct15 {dir_st : (((x_7).mesi_dir_st) ==
        ((Bit#(3))'(3'h0)) ? ((Bit#(3))'(3'h1)) : ((x_7).mesi_dir_st)),
        dir_excl : ((((x_7).mesi_dir_sharers)[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        ((((((x_7).mesi_dir_sharers)[3:1])[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        (((((((x_7).mesi_dir_sharers)[3:1])[2:1])[0:0]) == ((Bit#(1))'(1'h1))
        ? ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        ((((((((x_7).mesi_dir_sharers)[3:1])[2:1])[1:1])[0:0]) ==
        ((Bit#(1))'(1'h1)) ? ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        (unpack(0))))))))))))), dir_sharers : (x_7).mesi_dir_sharers});
        when ((x_2) == ((Bit#(4))'(4'h1)), noAction);
        when (((x_3).id) == ((Bit#(6))'(6'h2)), noAction);
        when (! ((x_3).type_), noAction);
        when (((Bool)'(True)) && (((Bool)'(True)) && ((! (((Bit#(3))'(3'h1))
        < (x_15))) && ((! (((x_16).dir_st) < ((Bit#(3))'(3'h3)))) && (!
        (((Bit#(3))'(3'h4)) < ((x_16).dir_st)))))), noAction);
        Struct1 x_17 = (x_3);
        Struct16 x_18 = (Struct16 {addr : (x_3).addr, info_write :
        (Bool)'(False), info_hit : (x_6).info_hit, info_way : (x_6).info_way,
        edir_hit : (x_6).edir_hit, edir_way : (x_6).edir_way, edir_slot :
        (x_6).edir_slot, info : (x_6).info, value_write : (Bool)'(False),
        value : unpack(0), may_victim : (x_6).may_victim, reps :
        (x_6).reps});
        let x_20 = ?;
        if ((x_8).valid) begin
            x_20 = x_9;
        end else begin
            let x_19 <- cache__00__valueRsLineRq(unpack(0));
            x_20 = x_19;
        end
        let x_21 <- registerDL_00(Struct20 {r_id : x_4, r_dl_rss_from :
        (unpack(0)) | (((Bit#(4))'(4'h1)) <<
        (({((Bit#(2))'(2'h1)),((x_16).dir_excl)})[1:0])), r_dl_rsb :
        (Bool)'(True), r_dl_rsbTo : (Bit#(4))'(4'h9)});
        Struct18 x_22 = (Struct18 {enq_type :
        ((({((Bit#(2))'(2'h2)),((x_16).dir_excl)})[3:2]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) :
        (((({((Bit#(2))'(2'h2)),((x_16).dir_excl)})[3:2]) ==
        ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : ({((Bit#(2))'(2'h2)),((x_16).dir_excl)})[1:0], enq_msg :
        Struct1 {id : (Bit#(6))'(6'h5), type_ : (Bool)'(False), addr :
        (x_17).addr, value : unpack(0)}});
        let x_23 <- makeEnq_parentChildren00(x_22);
    endrule

    rule rule_exec_00_10001;
        let x_0 <- deq_fifoL2E_00();
        Struct6 x_1 = ((x_0).lr_ir_pp);
        Bit#(4) x_2 = ((x_1).ir_msg_from);
        Struct1 x_3 = ((x_1).ir_msg);
        Bit#(3) x_4 = ((x_1).ir_mshr_id);
        Bool x_5 = ((x_1).ir_is_rs_rel);
        when (! (x_5), noAction);
        Struct9 x_6 = ((x_0).lr_ir);
        Struct10 x_7 = ((x_6).info);
        Struct5 x_8 = ((x_1).ir_by_victim);
        Vector#(4, Bit#(64)) x_9 = ((x_0).lr_value);
        let x_10 <- getMSHR_00(x_4);
        let x_11 <- getMSHRRq_00(x_4);
        Struct1 x_12 = (unpack(0));
        Vector#(4, Bit#(64)) x_13 = (unpack(0));
        Bool x_14 = ((x_7).mesi_owned);
        Bit#(3) x_15 = ((x_7).mesi_status);
        Struct15 x_16 = (Struct15 {dir_st : (((x_7).mesi_dir_st) ==
        ((Bit#(3))'(3'h0)) ? ((Bit#(3))'(3'h1)) : ((x_7).mesi_dir_st)),
        dir_excl : ((((x_7).mesi_dir_sharers)[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        ((((((x_7).mesi_dir_sharers)[3:1])[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        (((((((x_7).mesi_dir_sharers)[3:1])[2:1])[0:0]) == ((Bit#(1))'(1'h1))
        ? ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        ((((((((x_7).mesi_dir_sharers)[3:1])[2:1])[1:1])[0:0]) ==
        ((Bit#(1))'(1'h1)) ? ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        (unpack(0))))))))))))), dir_sharers : (x_7).mesi_dir_sharers});
        when ((x_2) == ((Bit#(4))'(4'h1)), noAction);
        when (((x_3).id) == ((Bit#(6))'(6'ha)), noAction);
        when (! ((x_3).type_), noAction);
        when ((! ((x_15) < ((Bit#(3))'(3'h3)))) || (((x_15) ==
        ((Bit#(3))'(3'h2))) && (((x_14) == ((Bool)'(True))) &&
        ((((x_16).dir_st) == ((Bit#(3))'(3'h2))) && (((x_16).dir_sharers) ==
        (((Bit#(4))'(4'h1)) << ((Bit#(2))'(2'h1))))))), noAction);
        Struct1 x_17 = (x_3);
        Struct16 x_18 = (Struct16 {addr : (x_3).addr, info_write :
        (Bool)'(False), info_hit : (x_6).info_hit, info_way : (x_6).info_way,
        edir_hit : (x_6).edir_hit, edir_way : (x_6).edir_way, edir_slot :
        (x_6).edir_slot, info : (x_6).info, value_write : (Bool)'(False),
        value : unpack(0), may_victim : (x_6).may_victim, reps :
        (x_6).reps});
        Struct16 x_19 = (Struct16 {addr : (x_18).addr, info_write :
        (Bool)'(True), info_hit : (x_18).info_hit, info_way :
        (x_18).info_way, edir_hit : (x_18).edir_hit, edir_way :
        (x_18).edir_way, edir_slot : (x_18).edir_slot, info : Struct10
        {mesi_owned : ((x_18).info).mesi_owned, mesi_status :
        ((x_18).info).mesi_status, mesi_dir_st : (Struct15 {dir_st :
        (Bit#(3))'(3'h4), dir_excl : (Bit#(2))'(2'h1), dir_sharers :
        unpack(0)}).dir_st, mesi_dir_sharers : (((Struct15 {dir_st :
        (Bit#(3))'(3'h4), dir_excl : (Bit#(2))'(2'h1), dir_sharers :
        unpack(0)}).dir_st) == ((Bit#(3))'(3'h2)) ? ((Struct15 {dir_st :
        (Bit#(3))'(3'h4), dir_excl : (Bit#(2))'(2'h1), dir_sharers :
        unpack(0)}).dir_sharers) : (((Bit#(4))'(4'h1)) << ((Struct15 {dir_st
        : (Bit#(3))'(3'h4), dir_excl : (Bit#(2))'(2'h1), dir_sharers :
        unpack(0)}).dir_excl)))}, value_write : (x_18).value_write, value :
        (x_18).value, may_victim : (x_18).may_victim, reps :
        (x_18).reps});
        Struct16 x_20 = (Struct16 {addr : (x_19).addr, info_write :
        (Bool)'(True), info_hit : (x_19).info_hit, info_way :
        (x_19).info_way, edir_hit : (x_19).edir_hit, edir_way :
        (x_19).edir_way, edir_slot : (x_19).edir_slot, info : Struct10
        {mesi_owned : ((x_19).info).mesi_owned, mesi_status :
        (Bit#(3))'(3'h1), mesi_dir_st : ((x_19).info).mesi_dir_st,
        mesi_dir_sharers : ((x_19).info).mesi_dir_sharers}, value_write :
        (x_19).value_write, value : (x_19).value, may_victim :
        (x_19).may_victim, reps : (x_19).reps});
        Struct16 x_21 = (Struct16 {addr : (x_20).addr, info_write :
        (Bool)'(True), info_hit : (x_20).info_hit, info_way :
        (x_20).info_way, edir_hit : (x_20).edir_hit, edir_way :
        (x_20).edir_way, edir_slot : (x_20).edir_slot, info : Struct10
        {mesi_owned : (Bool)'(False), mesi_status :
        ((x_20).info).mesi_status, mesi_dir_st : ((x_20).info).mesi_dir_st,
        mesi_dir_sharers : ((x_20).info).mesi_dir_sharers}, value_write :
        (x_20).value_write, value : (x_20).value, may_victim :
        (x_20).may_victim, reps :
        (x_20).reps});
        let x_24 = ?;
        if ((x_8).valid) begin
            let x_22 <- victims__00__setVictim(Struct17 {victim_idx :
            (x_8).data, victim_info : (x_21).info, victim_value :
            ((x_21).value_write ? ((x_21).value) : (x_9))});
            x_24 = x_9;
        end else begin
            let x_23 <- cache__00__valueRsLineRq(x_21);
            x_24 = x_23;
        end
        Struct18 x_25 = (Struct18 {enq_type : ((((Bit#(4))'(4'h9))[3:2]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : (((((Bit#(4))'(4'h9))[3:2])
        == ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : ((Bit#(4))'(4'h9))[1:0], enq_msg : Struct1 {id :
        (Bit#(6))'(6'hb), type_ : (Bool)'(True), addr : (x_17).addr, value :
        unpack(0)}});
        let x_26 <- makeEnq_parentChildren00(x_25);
        let x_27 <- releaseMSHR_00(x_4);
    endrule

    rule rule_exec_00_11001;
        let x_0 <- deq_fifoL2E_00();
        Struct6 x_1 = ((x_0).lr_ir_pp);
        Bit#(4) x_2 = ((x_1).ir_msg_from);
        Struct1 x_3 = ((x_1).ir_msg);
        Bit#(3) x_4 = ((x_1).ir_mshr_id);
        Bool x_5 = ((x_1).ir_is_rs_rel);
        when (! (x_5), noAction);
        Struct9 x_6 = ((x_0).lr_ir);
        Struct10 x_7 = ((x_6).info);
        Struct5 x_8 = ((x_1).ir_by_victim);
        Vector#(4, Bit#(64)) x_9 = ((x_0).lr_value);
        let x_10 <- getMSHR_00(x_4);
        let x_11 <- getMSHRRq_00(x_4);
        Struct1 x_12 = (unpack(0));
        Vector#(4, Bit#(64)) x_13 = (unpack(0));
        Bool x_14 = ((x_7).mesi_owned);
        Bit#(3) x_15 = ((x_7).mesi_status);
        Struct15 x_16 = (Struct15 {dir_st : (((x_7).mesi_dir_st) ==
        ((Bit#(3))'(3'h0)) ? ((Bit#(3))'(3'h1)) : ((x_7).mesi_dir_st)),
        dir_excl : ((((x_7).mesi_dir_sharers)[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        ((((((x_7).mesi_dir_sharers)[3:1])[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        (((((((x_7).mesi_dir_sharers)[3:1])[2:1])[0:0]) == ((Bit#(1))'(1'h1))
        ? ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        ((((((((x_7).mesi_dir_sharers)[3:1])[2:1])[1:1])[0:0]) ==
        ((Bit#(1))'(1'h1)) ? ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        (unpack(0))))))))))))), dir_sharers : (x_7).mesi_dir_sharers});
        when ((x_2) == ((Bit#(4))'(4'h1)), noAction);
        when (((x_3).id) == ((Bit#(6))'(6'ha)), noAction);
        when (! ((x_3).type_), noAction);
        when (((x_14) == ((Bool)'(False))) && ((! (((Bit#(3))'(3'h2)) <
        (x_15))) && (! (((Bit#(3))'(3'h2)) < ((x_16).dir_st)))),
        noAction);
        Struct1 x_17 = (x_3);
        Struct16 x_18 = (Struct16 {addr : (x_3).addr, info_write :
        (Bool)'(False), info_hit : (x_6).info_hit, info_way : (x_6).info_way,
        edir_hit : (x_6).edir_hit, edir_way : (x_6).edir_way, edir_slot :
        (x_6).edir_slot, info : (x_6).info, value_write : (Bool)'(False),
        value : unpack(0), may_victim : (x_6).may_victim, reps :
        (x_6).reps});
        let x_20 = ?;
        if ((x_8).valid) begin
            x_20 = x_9;
        end else begin
            let x_19 <- cache__00__valueRsLineRq(unpack(0));
            x_20 = x_19;
        end
        let x_21 <- registerUL_00(Struct19 {r_id : x_4, r_ul_rsb :
        (Bool)'(True), r_ul_rsbTo : ((Bit#(4))'(4'h9))[1:0]});
        Struct18 x_22 = (Struct18 {enq_type : ((((Bit#(4))'(4'h0))[3:2]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : (((((Bit#(4))'(4'h0))[3:2])
        == ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : ((Bit#(4))'(4'h0))[1:0], enq_msg : Struct1 {id :
        (Bit#(6))'(6'ha), type_ : (Bool)'(False), addr : (x_17).addr, value :
        unpack(0)}});
        let x_23 <- makeEnq_parentChildren00(x_22);
    endrule

    rule rule_exec_00_14001;
        let x_0 <- deq_fifoL2E_00();
        Struct6 x_1 = ((x_0).lr_ir_pp);
        Bit#(4) x_2 = ((x_1).ir_msg_from);
        Struct1 x_3 = ((x_1).ir_msg);
        Bit#(3) x_4 = ((x_1).ir_mshr_id);
        Bool x_5 = ((x_1).ir_is_rs_rel);
        when (! (x_5), noAction);
        Struct9 x_6 = ((x_0).lr_ir);
        Struct10 x_7 = ((x_6).info);
        Struct5 x_8 = ((x_1).ir_by_victim);
        Vector#(4, Bit#(64)) x_9 = ((x_0).lr_value);
        let x_10 <- getMSHR_00(x_4);
        let x_11 <- getMSHRRq_00(x_4);
        Struct1 x_12 = (unpack(0));
        Vector#(4, Bit#(64)) x_13 = (unpack(0));
        Bool x_14 = ((x_7).mesi_owned);
        Bit#(3) x_15 = ((x_7).mesi_status);
        Struct15 x_16 = (Struct15 {dir_st : (((x_7).mesi_dir_st) ==
        ((Bit#(3))'(3'h0)) ? ((Bit#(3))'(3'h1)) : ((x_7).mesi_dir_st)),
        dir_excl : ((((x_7).mesi_dir_sharers)[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        ((((((x_7).mesi_dir_sharers)[3:1])[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        (((((((x_7).mesi_dir_sharers)[3:1])[2:1])[0:0]) == ((Bit#(1))'(1'h1))
        ? ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        ((((((((x_7).mesi_dir_sharers)[3:1])[2:1])[1:1])[0:0]) ==
        ((Bit#(1))'(1'h1)) ? ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        (unpack(0))))))))))))), dir_sharers : (x_7).mesi_dir_sharers});
        when ((x_2) == ((Bit#(4))'(4'h1)), noAction);
        when (((x_3).id) == ((Bit#(6))'(6'ha)), noAction);
        when (! ((x_3).type_), noAction);
        when (((Bool)'(True)) && (((Bool)'(True)) && ((! (((Bit#(3))'(3'h1))
        < (x_15))) && ((! (((x_16).dir_st) < ((Bit#(3))'(3'h3)))) && (!
        (((Bit#(3))'(3'h4)) < ((x_16).dir_st)))))), noAction);
        Struct1 x_17 = (x_3);
        Struct16 x_18 = (Struct16 {addr : (x_3).addr, info_write :
        (Bool)'(False), info_hit : (x_6).info_hit, info_way : (x_6).info_way,
        edir_hit : (x_6).edir_hit, edir_way : (x_6).edir_way, edir_slot :
        (x_6).edir_slot, info : (x_6).info, value_write : (Bool)'(False),
        value : unpack(0), may_victim : (x_6).may_victim, reps :
        (x_6).reps});
        let x_20 = ?;
        if ((x_8).valid) begin
            x_20 = x_9;
        end else begin
            let x_19 <- cache__00__valueRsLineRq(unpack(0));
            x_20 = x_19;
        end
        let x_21 <- registerDL_00(Struct20 {r_id : x_4, r_dl_rss_from :
        (unpack(0)) | (((Bit#(4))'(4'h1)) <<
        (({((Bit#(2))'(2'h1)),((x_16).dir_excl)})[1:0])), r_dl_rsb :
        (Bool)'(True), r_dl_rsbTo : (Bit#(4))'(4'h9)});
        Struct18 x_22 = (Struct18 {enq_type :
        ((({((Bit#(2))'(2'h2)),((x_16).dir_excl)})[3:2]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) :
        (((({((Bit#(2))'(2'h2)),((x_16).dir_excl)})[3:2]) ==
        ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : ({((Bit#(2))'(2'h2)),((x_16).dir_excl)})[1:0], enq_msg :
        Struct1 {id : (Bit#(6))'(6'he), type_ : (Bool)'(False), addr :
        (x_17).addr, value : unpack(0)}});
        let x_23 <- makeEnq_parentChildren00(x_22);
    endrule

    rule rule_exec_00_15001;
        let x_0 <- deq_fifoL2E_00();
        Struct6 x_1 = ((x_0).lr_ir_pp);
        Bit#(4) x_2 = ((x_1).ir_msg_from);
        Struct1 x_3 = ((x_1).ir_msg);
        Bit#(3) x_4 = ((x_1).ir_mshr_id);
        Bool x_5 = ((x_1).ir_is_rs_rel);
        when (! (x_5), noAction);
        Struct9 x_6 = ((x_0).lr_ir);
        Struct10 x_7 = ((x_6).info);
        Struct5 x_8 = ((x_1).ir_by_victim);
        Vector#(4, Bit#(64)) x_9 = ((x_0).lr_value);
        let x_10 <- getMSHR_00(x_4);
        let x_11 <- getMSHRRq_00(x_4);
        Struct1 x_12 = (unpack(0));
        Vector#(4, Bit#(64)) x_13 = (unpack(0));
        Bool x_14 = ((x_7).mesi_owned);
        Bit#(3) x_15 = ((x_7).mesi_status);
        Struct15 x_16 = (Struct15 {dir_st : (((x_7).mesi_dir_st) ==
        ((Bit#(3))'(3'h0)) ? ((Bit#(3))'(3'h1)) : ((x_7).mesi_dir_st)),
        dir_excl : ((((x_7).mesi_dir_sharers)[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        ((((((x_7).mesi_dir_sharers)[3:1])[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        (((((((x_7).mesi_dir_sharers)[3:1])[2:1])[0:0]) == ((Bit#(1))'(1'h1))
        ? ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        ((((((((x_7).mesi_dir_sharers)[3:1])[2:1])[1:1])[0:0]) ==
        ((Bit#(1))'(1'h1)) ? ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        (unpack(0))))))))))))), dir_sharers : (x_7).mesi_dir_sharers});
        when ((x_2) == ((Bit#(4))'(4'h1)), noAction);
        when (((x_3).id) == ((Bit#(6))'(6'ha)), noAction);
        when (! ((x_3).type_), noAction);
        when (((Bool)'(True)) && (((Bool)'(True)) && ((!
        ((((x_16).dir_sharers) & (~(((Bit#(4))'(4'h1)) <<
        ((Bit#(2))'(2'h1))))) == ((Bit#(4))'(4'h0)))) && (((x_14) ==
        ((Bool)'(True))) && ((! (((Bit#(3))'(3'h2)) < (x_15))) &&
        (((x_16).dir_st) == ((Bit#(3))'(3'h2))))))), noAction);
        Struct1 x_17 = (x_3);
        Struct16 x_18 = (Struct16 {addr : (x_3).addr, info_write :
        (Bool)'(False), info_hit : (x_6).info_hit, info_way : (x_6).info_way,
        edir_hit : (x_6).edir_hit, edir_way : (x_6).edir_way, edir_slot :
        (x_6).edir_slot, info : (x_6).info, value_write : (Bool)'(False),
        value : unpack(0), may_victim : (x_6).may_victim, reps :
        (x_6).reps});
        let x_20 = ?;
        if ((x_8).valid) begin
            x_20 = x_9;
        end else begin
            let x_19 <- cache__00__valueRsLineRq(unpack(0));
            x_20 = x_19;
        end
        let x_21 <- registerDL_00(Struct20 {r_id : x_4, r_dl_rss_from :
        ((x_16).dir_sharers) & (~(((Bit#(4))'(4'h1)) << ((Bit#(2))'(2'h1)))),
        r_dl_rsb : (Bool)'(True), r_dl_rsbTo : (Bit#(4))'(4'h9)});
        let x_22 <- broadcast_parentChildren00(Struct21 {cs_inds :
        ((x_16).dir_sharers) & (~(((Bit#(4))'(4'h1)) << ((Bit#(2))'(2'h1)))),
        cs_msg : Struct1 {id : (Bit#(6))'(6'hc), type_ : (Bool)'(False), addr
        : (x_17).addr, value : unpack(0)}});
    endrule

    rule rule_exec_00_25001;
        let x_0 <- deq_fifoL2E_00();
        Struct6 x_1 = ((x_0).lr_ir_pp);
        Bit#(4) x_2 = ((x_1).ir_msg_from);
        Struct1 x_3 = ((x_1).ir_msg);
        Bit#(3) x_4 = ((x_1).ir_mshr_id);
        Bool x_5 = ((x_1).ir_is_rs_rel);
        when (! (x_5), noAction);
        Struct9 x_6 = ((x_0).lr_ir);
        Struct10 x_7 = ((x_6).info);
        Struct5 x_8 = ((x_1).ir_by_victim);
        Vector#(4, Bit#(64)) x_9 = ((x_0).lr_value);
        let x_10 <- getMSHR_00(x_4);
        let x_11 <- getMSHRRq_00(x_4);
        Struct1 x_12 = (unpack(0));
        Vector#(4, Bit#(64)) x_13 = (unpack(0));
        Bool x_14 = ((x_7).mesi_owned);
        Bit#(3) x_15 = ((x_7).mesi_status);
        Struct15 x_16 = (Struct15 {dir_st : (((x_7).mesi_dir_st) ==
        ((Bit#(3))'(3'h0)) ? ((Bit#(3))'(3'h1)) : ((x_7).mesi_dir_st)),
        dir_excl : ((((x_7).mesi_dir_sharers)[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        ((((((x_7).mesi_dir_sharers)[3:1])[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        (((((((x_7).mesi_dir_sharers)[3:1])[2:1])[0:0]) == ((Bit#(1))'(1'h1))
        ? ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        ((((((((x_7).mesi_dir_sharers)[3:1])[2:1])[1:1])[0:0]) ==
        ((Bit#(1))'(1'h1)) ? ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        (unpack(0))))))))))))), dir_sharers : (x_7).mesi_dir_sharers});
        when ((x_2) == ((Bit#(4))'(4'h1)), noAction);
        when (((x_3).id) == ((Bit#(6))'(6'h14)), noAction);
        when (! ((x_3).type_), noAction);
        when ((((((x_16).dir_st) == ((Bit#(3))'(3'h4))) && (((x_16).dir_excl)
        == ((Bit#(2))'(2'h1))) ? ((Bit#(3))'(3'h4)) : (((((x_16).dir_st) ==
        ((Bit#(3))'(3'h3))) && (((x_16).dir_excl) == ((Bit#(2))'(2'h1))) ?
        ((Bit#(3))'(3'h3)) : (((((x_16).dir_st) == ((Bit#(3))'(3'h2))) &&
        ((((x_16).dir_sharers) | (((Bit#(4))'(4'h1)) << ((Bit#(2))'(2'h1))))
        == ((x_16).dir_sharers)) ? ((Bit#(3))'(3'h2)) :
        ((Bit#(3))'(3'h1)))))))) == ((Bit#(3))'(3'h1)), noAction);
        Struct1 x_17 = (x_3);
        Struct16 x_18 = (Struct16 {addr : (x_3).addr, info_write :
        (Bool)'(False), info_hit : (x_6).info_hit, info_way : (x_6).info_way,
        edir_hit : (x_6).edir_hit, edir_way : (x_6).edir_way, edir_slot :
        (x_6).edir_slot, info : (x_6).info, value_write : (Bool)'(False),
        value : unpack(0), may_victim : (x_6).may_victim, reps :
        (x_6).reps});
        let x_20 = ?;
        if ((x_8).valid) begin
            x_20 = x_9;
        end else begin
            let x_19 <- cache__00__valueRsLineRq(unpack(0));
            x_20 = x_19;
        end
        Struct18 x_21 = (Struct18 {enq_type : ((((Bit#(4))'(4'h9))[3:2]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : (((((Bit#(4))'(4'h9))[3:2])
        == ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : ((Bit#(4))'(4'h9))[1:0], enq_msg : Struct1 {id :
        (Bit#(6))'(6'h16), type_ : (Bool)'(True), addr : (x_17).addr, value :
        unpack(0)}});
        let x_22 <- makeEnq_parentChildren00(x_21);
        let x_23 <- releaseMSHR_00(x_4);
    endrule

    rule rule_exec_00_2600001;
        let x_0 <- deq_fifoL2E_00();
        Struct6 x_1 = ((x_0).lr_ir_pp);
        Bit#(4) x_2 = ((x_1).ir_msg_from);
        Struct1 x_3 = ((x_1).ir_msg);
        Bit#(3) x_4 = ((x_1).ir_mshr_id);
        Bool x_5 = ((x_1).ir_is_rs_rel);
        when (! (x_5), noAction);
        Struct9 x_6 = ((x_0).lr_ir);
        Struct10 x_7 = ((x_6).info);
        Struct5 x_8 = ((x_1).ir_by_victim);
        Vector#(4, Bit#(64)) x_9 = ((x_0).lr_value);
        let x_10 <- getMSHR_00(x_4);
        let x_11 <- getMSHRRq_00(x_4);
        Struct1 x_12 = (unpack(0));
        Vector#(4, Bit#(64)) x_13 = (unpack(0));
        Bool x_14 = ((x_7).mesi_owned);
        Bit#(3) x_15 = ((x_7).mesi_status);
        Struct15 x_16 = (Struct15 {dir_st : (((x_7).mesi_dir_st) ==
        ((Bit#(3))'(3'h0)) ? ((Bit#(3))'(3'h1)) : ((x_7).mesi_dir_st)),
        dir_excl : ((((x_7).mesi_dir_sharers)[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        ((((((x_7).mesi_dir_sharers)[3:1])[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        (((((((x_7).mesi_dir_sharers)[3:1])[2:1])[0:0]) == ((Bit#(1))'(1'h1))
        ? ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        ((((((((x_7).mesi_dir_sharers)[3:1])[2:1])[1:1])[0:0]) ==
        ((Bit#(1))'(1'h1)) ? ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        (unpack(0))))))))))))), dir_sharers : (x_7).mesi_dir_sharers});
        when ((x_2) == ((Bit#(4))'(4'h1)), noAction);
        when (((x_3).id) == ((Bit#(6))'(6'h14)), noAction);
        when (! ((x_3).type_), noAction);
        when (((x_14) == ((Bool)'(False))) && (((((((x_16).dir_st) ==
        ((Bit#(3))'(3'h4))) && (((x_16).dir_excl) == ((Bit#(2))'(2'h1))) ?
        ((Bit#(3))'(3'h4)) : (((((x_16).dir_st) == ((Bit#(3))'(3'h3))) &&
        (((x_16).dir_excl) == ((Bit#(2))'(2'h1))) ? ((Bit#(3))'(3'h3)) :
        (((((x_16).dir_st) == ((Bit#(3))'(3'h2))) && ((((x_16).dir_sharers) |
        (((Bit#(4))'(4'h1)) << ((Bit#(2))'(2'h1)))) == ((x_16).dir_sharers))
        ? ((Bit#(3))'(3'h2)) : ((Bit#(3))'(3'h1)))))))) ==
        ((Bit#(3))'(3'h2))) && (((x_16).dir_sharers) == (((Bit#(4))'(4'h1))
        << ((Bit#(2))'(2'h1))))), noAction);
        Struct1 x_17 = (x_3);
        Struct16 x_18 = (Struct16 {addr : (x_3).addr, info_write :
        (Bool)'(False), info_hit : (x_6).info_hit, info_way : (x_6).info_way,
        edir_hit : (x_6).edir_hit, edir_way : (x_6).edir_way, edir_slot :
        (x_6).edir_slot, info : (x_6).info, value_write : (Bool)'(False),
        value : unpack(0), may_victim : (x_6).may_victim, reps :
        (x_6).reps});
        Struct16 x_19 = (Struct16 {addr : (x_18).addr, info_write :
        (Bool)'(True), info_hit : (x_18).info_hit, info_way :
        (x_18).info_way, edir_hit : (x_18).edir_hit, edir_way :
        (x_18).edir_way, edir_slot : (x_18).edir_slot, info : Struct10
        {mesi_owned : ((x_18).info).mesi_owned, mesi_status :
        ((x_18).info).mesi_status, mesi_dir_st : (Struct15 {dir_st :
        (Bit#(3))'(3'h1), dir_excl : unpack(0), dir_sharers :
        unpack(0)}).dir_st, mesi_dir_sharers : (((Struct15 {dir_st :
        (Bit#(3))'(3'h1), dir_excl : unpack(0), dir_sharers :
        unpack(0)}).dir_st) == ((Bit#(3))'(3'h2)) ? ((Struct15 {dir_st :
        (Bit#(3))'(3'h1), dir_excl : unpack(0), dir_sharers :
        unpack(0)}).dir_sharers) : (((Bit#(4))'(4'h1)) << ((Struct15 {dir_st
        : (Bit#(3))'(3'h1), dir_excl : unpack(0), dir_sharers :
        unpack(0)}).dir_excl)))}, value_write : (x_18).value_write, value :
        (x_18).value, may_victim : (x_18).may_victim, reps :
        (x_18).reps});
        let x_22 = ?;
        if ((x_8).valid) begin
            let x_20 <- victims__00__setVictim(Struct17 {victim_idx :
            (x_8).data, victim_info : (x_19).info, victim_value :
            ((x_19).value_write ? ((x_19).value) : (x_9))});
            x_22 = x_9;
        end else begin
            let x_21 <- cache__00__valueRsLineRq(x_19);
            x_22 = x_21;
        end
        Struct18 x_23 = (Struct18 {enq_type : ((((Bit#(4))'(4'h9))[3:2]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : (((((Bit#(4))'(4'h9))[3:2])
        == ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : ((Bit#(4))'(4'h9))[1:0], enq_msg : Struct1 {id :
        (Bit#(6))'(6'h16), type_ : (Bool)'(True), addr : (x_17).addr, value :
        unpack(0)}});
        let x_24 <- makeEnq_parentChildren00(x_23);
        let x_25 <- releaseMSHR_00(x_4);
    endrule

    rule rule_exec_00_2601001;
        let x_0 <- deq_fifoL2E_00();
        Struct6 x_1 = ((x_0).lr_ir_pp);
        Bit#(4) x_2 = ((x_1).ir_msg_from);
        Struct1 x_3 = ((x_1).ir_msg);
        Bit#(3) x_4 = ((x_1).ir_mshr_id);
        Bool x_5 = ((x_1).ir_is_rs_rel);
        when (! (x_5), noAction);
        Struct9 x_6 = ((x_0).lr_ir);
        Struct10 x_7 = ((x_6).info);
        Struct5 x_8 = ((x_1).ir_by_victim);
        Vector#(4, Bit#(64)) x_9 = ((x_0).lr_value);
        let x_10 <- getMSHR_00(x_4);
        let x_11 <- getMSHRRq_00(x_4);
        Struct1 x_12 = (unpack(0));
        Vector#(4, Bit#(64)) x_13 = (unpack(0));
        Bool x_14 = ((x_7).mesi_owned);
        Bit#(3) x_15 = ((x_7).mesi_status);
        Struct15 x_16 = (Struct15 {dir_st : (((x_7).mesi_dir_st) ==
        ((Bit#(3))'(3'h0)) ? ((Bit#(3))'(3'h1)) : ((x_7).mesi_dir_st)),
        dir_excl : ((((x_7).mesi_dir_sharers)[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        ((((((x_7).mesi_dir_sharers)[3:1])[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        (((((((x_7).mesi_dir_sharers)[3:1])[2:1])[0:0]) == ((Bit#(1))'(1'h1))
        ? ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        ((((((((x_7).mesi_dir_sharers)[3:1])[2:1])[1:1])[0:0]) ==
        ((Bit#(1))'(1'h1)) ? ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        (unpack(0))))))))))))), dir_sharers : (x_7).mesi_dir_sharers});
        when ((x_2) == ((Bit#(4))'(4'h1)), noAction);
        when (((x_3).id) == ((Bit#(6))'(6'h14)), noAction);
        when (! ((x_3).type_), noAction);
        when (((x_14) == ((Bool)'(True))) && (((x_15) == ((Bit#(3))'(3'h2)))
        && (((((((x_16).dir_st) == ((Bit#(3))'(3'h4))) && (((x_16).dir_excl)
        == ((Bit#(2))'(2'h1))) ? ((Bit#(3))'(3'h4)) : (((((x_16).dir_st) ==
        ((Bit#(3))'(3'h3))) && (((x_16).dir_excl) == ((Bit#(2))'(2'h1))) ?
        ((Bit#(3))'(3'h3)) : (((((x_16).dir_st) == ((Bit#(3))'(3'h2))) &&
        ((((x_16).dir_sharers) | (((Bit#(4))'(4'h1)) << ((Bit#(2))'(2'h1))))
        == ((x_16).dir_sharers)) ? ((Bit#(3))'(3'h2)) :
        ((Bit#(3))'(3'h1)))))))) == ((Bit#(3))'(3'h2))) &&
        (((x_16).dir_sharers) == (((Bit#(4))'(4'h1)) <<
        ((Bit#(2))'(2'h1)))))), noAction);
        Struct1 x_17 = (x_3);
        Struct16 x_18 = (Struct16 {addr : (x_3).addr, info_write :
        (Bool)'(False), info_hit : (x_6).info_hit, info_way : (x_6).info_way,
        edir_hit : (x_6).edir_hit, edir_way : (x_6).edir_way, edir_slot :
        (x_6).edir_slot, info : (x_6).info, value_write : (Bool)'(False),
        value : unpack(0), may_victim : (x_6).may_victim, reps :
        (x_6).reps});
        Struct16 x_19 = (Struct16 {addr : (x_18).addr, info_write :
        (Bool)'(True), info_hit : (x_18).info_hit, info_way :
        (x_18).info_way, edir_hit : (x_18).edir_hit, edir_way :
        (x_18).edir_way, edir_slot : (x_18).edir_slot, info : Struct10
        {mesi_owned : ((x_18).info).mesi_owned, mesi_status :
        ((x_18).info).mesi_status, mesi_dir_st : (Struct15 {dir_st :
        (Bit#(3))'(3'h1), dir_excl : unpack(0), dir_sharers :
        unpack(0)}).dir_st, mesi_dir_sharers : (((Struct15 {dir_st :
        (Bit#(3))'(3'h1), dir_excl : unpack(0), dir_sharers :
        unpack(0)}).dir_st) == ((Bit#(3))'(3'h2)) ? ((Struct15 {dir_st :
        (Bit#(3))'(3'h1), dir_excl : unpack(0), dir_sharers :
        unpack(0)}).dir_sharers) : (((Bit#(4))'(4'h1)) << ((Struct15 {dir_st
        : (Bit#(3))'(3'h1), dir_excl : unpack(0), dir_sharers :
        unpack(0)}).dir_excl)))}, value_write : (x_18).value_write, value :
        (x_18).value, may_victim : (x_18).may_victim, reps :
        (x_18).reps});
        Struct16 x_20 = (Struct16 {addr : (x_19).addr, info_write :
        (Bool)'(True), info_hit : (x_19).info_hit, info_way :
        (x_19).info_way, edir_hit : (x_19).edir_hit, edir_way :
        (x_19).edir_way, edir_slot : (x_19).edir_slot, info : Struct10
        {mesi_owned : ((x_19).info).mesi_owned, mesi_status :
        (Bit#(3))'(3'h4), mesi_dir_st : ((x_19).info).mesi_dir_st,
        mesi_dir_sharers : ((x_19).info).mesi_dir_sharers}, value_write :
        (x_19).value_write, value : (x_19).value, may_victim :
        (x_19).may_victim, reps :
        (x_19).reps});
        let x_23 = ?;
        if ((x_8).valid) begin
            let x_21 <- victims__00__setVictim(Struct17 {victim_idx :
            (x_8).data, victim_info : (x_20).info, victim_value :
            ((x_20).value_write ? ((x_20).value) : (x_9))});
            x_23 = x_9;
        end else begin
            let x_22 <- cache__00__valueRsLineRq(x_20);
            x_23 = x_22;
        end
        Struct18 x_24 = (Struct18 {enq_type : ((((Bit#(4))'(4'h9))[3:2]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : (((((Bit#(4))'(4'h9))[3:2])
        == ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : ((Bit#(4))'(4'h9))[1:0], enq_msg : Struct1 {id :
        (Bit#(6))'(6'h16), type_ : (Bool)'(True), addr : (x_17).addr, value :
        unpack(0)}});
        let x_25 <- makeEnq_parentChildren00(x_24);
        let x_26 <- releaseMSHR_00(x_4);
    endrule

    rule rule_exec_00_261001;
        let x_0 <- deq_fifoL2E_00();
        Struct6 x_1 = ((x_0).lr_ir_pp);
        Bit#(4) x_2 = ((x_1).ir_msg_from);
        Struct1 x_3 = ((x_1).ir_msg);
        Bit#(3) x_4 = ((x_1).ir_mshr_id);
        Bool x_5 = ((x_1).ir_is_rs_rel);
        when (! (x_5), noAction);
        Struct9 x_6 = ((x_0).lr_ir);
        Struct10 x_7 = ((x_6).info);
        Struct5 x_8 = ((x_1).ir_by_victim);
        Vector#(4, Bit#(64)) x_9 = ((x_0).lr_value);
        let x_10 <- getMSHR_00(x_4);
        let x_11 <- getMSHRRq_00(x_4);
        Struct1 x_12 = (unpack(0));
        Vector#(4, Bit#(64)) x_13 = (unpack(0));
        Bool x_14 = ((x_7).mesi_owned);
        Bit#(3) x_15 = ((x_7).mesi_status);
        Struct15 x_16 = (Struct15 {dir_st : (((x_7).mesi_dir_st) ==
        ((Bit#(3))'(3'h0)) ? ((Bit#(3))'(3'h1)) : ((x_7).mesi_dir_st)),
        dir_excl : ((((x_7).mesi_dir_sharers)[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        ((((((x_7).mesi_dir_sharers)[3:1])[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        (((((((x_7).mesi_dir_sharers)[3:1])[2:1])[0:0]) == ((Bit#(1))'(1'h1))
        ? ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        ((((((((x_7).mesi_dir_sharers)[3:1])[2:1])[1:1])[0:0]) ==
        ((Bit#(1))'(1'h1)) ? ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        (unpack(0))))))))))))), dir_sharers : (x_7).mesi_dir_sharers});
        when ((x_2) == ((Bit#(4))'(4'h1)), noAction);
        when (((x_3).id) == ((Bit#(6))'(6'h14)), noAction);
        when (! ((x_3).type_), noAction);
        when (((((((x_16).dir_st) == ((Bit#(3))'(3'h4))) &&
        (((x_16).dir_excl) == ((Bit#(2))'(2'h1))) ? ((Bit#(3))'(3'h4)) :
        (((((x_16).dir_st) == ((Bit#(3))'(3'h3))) && (((x_16).dir_excl) ==
        ((Bit#(2))'(2'h1))) ? ((Bit#(3))'(3'h3)) : (((((x_16).dir_st) ==
        ((Bit#(3))'(3'h2))) && ((((x_16).dir_sharers) | (((Bit#(4))'(4'h1))
        << ((Bit#(2))'(2'h1)))) == ((x_16).dir_sharers)) ? ((Bit#(3))'(3'h2))
        : ((Bit#(3))'(3'h1)))))))) == ((Bit#(3))'(3'h2))) &&
        (((Bit#(3))'(3'h1)) < ((((((x_16).dir_sharers)[0:0]) ==
        ((Bit#(1))'(1'h1)) ? ((Bit#(3))'(3'h1)) : ((Bit#(3))'(3'h0)))) +
        (((((((x_16).dir_sharers)[3:1])[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(3))'(3'h1)) : ((Bit#(3))'(3'h0)))) +
        ((((((((x_16).dir_sharers)[3:1])[2:1])[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(3))'(3'h1)) : ((Bit#(3))'(3'h0)))) +
        (((((((((x_16).dir_sharers)[3:1])[2:1])[1:1])[0:0]) ==
        ((Bit#(1))'(1'h1)) ? ((Bit#(3))'(3'h1)) : ((Bit#(3))'(3'h0)))) +
        (unpack(0))))))), noAction);
        Struct1 x_17 = (x_3);
        Struct16 x_18 = (Struct16 {addr : (x_3).addr, info_write :
        (Bool)'(False), info_hit : (x_6).info_hit, info_way : (x_6).info_way,
        edir_hit : (x_6).edir_hit, edir_way : (x_6).edir_way, edir_slot :
        (x_6).edir_slot, info : (x_6).info, value_write : (Bool)'(False),
        value : unpack(0), may_victim : (x_6).may_victim, reps :
        (x_6).reps});
        Struct16 x_19 = (Struct16 {addr : (x_18).addr, info_write :
        (Bool)'(True), info_hit : (x_18).info_hit, info_way :
        (x_18).info_way, edir_hit : (x_18).edir_hit, edir_way :
        (x_18).edir_way, edir_slot : (x_18).edir_slot, info : Struct10
        {mesi_owned : ((x_18).info).mesi_owned, mesi_status :
        ((x_18).info).mesi_status, mesi_dir_st : (Struct15 {dir_st :
        (Bit#(3))'(3'h2), dir_excl : (x_16).dir_excl, dir_sharers :
        ((x_16).dir_sharers) & (~(((Bit#(4))'(4'h1)) <<
        ((Bit#(2))'(2'h1))))}).dir_st, mesi_dir_sharers : (((Struct15 {dir_st
        : (Bit#(3))'(3'h2), dir_excl : (x_16).dir_excl, dir_sharers :
        ((x_16).dir_sharers) & (~(((Bit#(4))'(4'h1)) <<
        ((Bit#(2))'(2'h1))))}).dir_st) == ((Bit#(3))'(3'h2)) ? ((Struct15
        {dir_st : (Bit#(3))'(3'h2), dir_excl : (x_16).dir_excl, dir_sharers :
        ((x_16).dir_sharers) & (~(((Bit#(4))'(4'h1)) <<
        ((Bit#(2))'(2'h1))))}).dir_sharers) : (((Bit#(4))'(4'h1)) <<
        ((Struct15 {dir_st : (Bit#(3))'(3'h2), dir_excl : (x_16).dir_excl,
        dir_sharers : ((x_16).dir_sharers) & (~(((Bit#(4))'(4'h1)) <<
        ((Bit#(2))'(2'h1))))}).dir_excl)))}, value_write :
        (x_18).value_write, value : (x_18).value, may_victim :
        (x_18).may_victim, reps :
        (x_18).reps});
        let x_22 = ?;
        if ((x_8).valid) begin
            let x_20 <- victims__00__setVictim(Struct17 {victim_idx :
            (x_8).data, victim_info : (x_19).info, victim_value :
            ((x_19).value_write ? ((x_19).value) : (x_9))});
            x_22 = x_9;
        end else begin
            let x_21 <- cache__00__valueRsLineRq(x_19);
            x_22 = x_21;
        end
        Struct18 x_23 = (Struct18 {enq_type : ((((Bit#(4))'(4'h9))[3:2]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : (((((Bit#(4))'(4'h9))[3:2])
        == ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : ((Bit#(4))'(4'h9))[1:0], enq_msg : Struct1 {id :
        (Bit#(6))'(6'h16), type_ : (Bool)'(True), addr : (x_17).addr, value :
        unpack(0)}});
        let x_24 <- makeEnq_parentChildren00(x_23);
        let x_25 <- releaseMSHR_00(x_4);
    endrule

    rule rule_exec_00_27001;
        let x_0 <- deq_fifoL2E_00();
        Struct6 x_1 = ((x_0).lr_ir_pp);
        Bit#(4) x_2 = ((x_1).ir_msg_from);
        Struct1 x_3 = ((x_1).ir_msg);
        Bit#(3) x_4 = ((x_1).ir_mshr_id);
        Bool x_5 = ((x_1).ir_is_rs_rel);
        when (! (x_5), noAction);
        Struct9 x_6 = ((x_0).lr_ir);
        Struct10 x_7 = ((x_6).info);
        Struct5 x_8 = ((x_1).ir_by_victim);
        Vector#(4, Bit#(64)) x_9 = ((x_0).lr_value);
        let x_10 <- getMSHR_00(x_4);
        let x_11 <- getMSHRRq_00(x_4);
        Struct1 x_12 = (unpack(0));
        Vector#(4, Bit#(64)) x_13 = (unpack(0));
        Bool x_14 = ((x_7).mesi_owned);
        Bit#(3) x_15 = ((x_7).mesi_status);
        Struct15 x_16 = (Struct15 {dir_st : (((x_7).mesi_dir_st) ==
        ((Bit#(3))'(3'h0)) ? ((Bit#(3))'(3'h1)) : ((x_7).mesi_dir_st)),
        dir_excl : ((((x_7).mesi_dir_sharers)[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        ((((((x_7).mesi_dir_sharers)[3:1])[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        (((((((x_7).mesi_dir_sharers)[3:1])[2:1])[0:0]) == ((Bit#(1))'(1'h1))
        ? ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        ((((((((x_7).mesi_dir_sharers)[3:1])[2:1])[1:1])[0:0]) ==
        ((Bit#(1))'(1'h1)) ? ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        (unpack(0))))))))))))), dir_sharers : (x_7).mesi_dir_sharers});
        when ((x_2) == ((Bit#(4))'(4'h1)), noAction);
        when (((x_3).id) == ((Bit#(6))'(6'h14)), noAction);
        when (! ((x_3).type_), noAction);
        when ((((((x_16).dir_st) == ((Bit#(3))'(3'h4))) && (((x_16).dir_excl)
        == ((Bit#(2))'(2'h1))) ? ((Bit#(3))'(3'h4)) : (((((x_16).dir_st) ==
        ((Bit#(3))'(3'h3))) && (((x_16).dir_excl) == ((Bit#(2))'(2'h1))) ?
        ((Bit#(3))'(3'h3)) : (((((x_16).dir_st) == ((Bit#(3))'(3'h2))) &&
        ((((x_16).dir_sharers) | (((Bit#(4))'(4'h1)) << ((Bit#(2))'(2'h1))))
        == ((x_16).dir_sharers)) ? ((Bit#(3))'(3'h2)) :
        ((Bit#(3))'(3'h1)))))))) == ((Bit#(3))'(3'h3)), noAction);
        Struct1 x_17 = (x_3);
        Struct16 x_18 = (Struct16 {addr : (x_3).addr, info_write :
        (Bool)'(False), info_hit : (x_6).info_hit, info_way : (x_6).info_way,
        edir_hit : (x_6).edir_hit, edir_way : (x_6).edir_way, edir_slot :
        (x_6).edir_slot, info : (x_6).info, value_write : (Bool)'(False),
        value : unpack(0), may_victim : (x_6).may_victim, reps :
        (x_6).reps});
        Struct16 x_19 = (Struct16 {addr : (x_18).addr, info_write :
        (Bool)'(True), info_hit : (x_18).info_hit, info_way :
        (x_18).info_way, edir_hit : (x_18).edir_hit, edir_way :
        (x_18).edir_way, edir_slot : (x_18).edir_slot, info : Struct10
        {mesi_owned : ((x_18).info).mesi_owned, mesi_status :
        ((x_18).info).mesi_status, mesi_dir_st : (Struct15 {dir_st :
        (Bit#(3))'(3'h1), dir_excl : unpack(0), dir_sharers :
        unpack(0)}).dir_st, mesi_dir_sharers : (((Struct15 {dir_st :
        (Bit#(3))'(3'h1), dir_excl : unpack(0), dir_sharers :
        unpack(0)}).dir_st) == ((Bit#(3))'(3'h2)) ? ((Struct15 {dir_st :
        (Bit#(3))'(3'h1), dir_excl : unpack(0), dir_sharers :
        unpack(0)}).dir_sharers) : (((Bit#(4))'(4'h1)) << ((Struct15 {dir_st
        : (Bit#(3))'(3'h1), dir_excl : unpack(0), dir_sharers :
        unpack(0)}).dir_excl)))}, value_write : (x_18).value_write, value :
        (x_18).value, may_victim : (x_18).may_victim, reps :
        (x_18).reps});
        Struct16 x_20 = (Struct16 {addr : (x_19).addr, info_write :
        (Bool)'(True), info_hit : (x_19).info_hit, info_way :
        (x_19).info_way, edir_hit : (x_19).edir_hit, edir_way :
        (x_19).edir_way, edir_slot : (x_19).edir_slot, info : Struct10
        {mesi_owned : ((x_19).info).mesi_owned, mesi_status :
        (Bit#(3))'(3'h3), mesi_dir_st : ((x_19).info).mesi_dir_st,
        mesi_dir_sharers : ((x_19).info).mesi_dir_sharers}, value_write :
        (x_19).value_write, value : (x_19).value, may_victim :
        (x_19).may_victim, reps :
        (x_19).reps});
        let x_23 = ?;
        if ((x_8).valid) begin
            let x_21 <- victims__00__setVictim(Struct17 {victim_idx :
            (x_8).data, victim_info : (x_20).info, victim_value :
            ((x_20).value_write ? ((x_20).value) : (x_9))});
            x_23 = x_9;
        end else begin
            let x_22 <- cache__00__valueRsLineRq(x_20);
            x_23 = x_22;
        end
        Struct18 x_24 = (Struct18 {enq_type : ((((Bit#(4))'(4'h9))[3:2]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : (((((Bit#(4))'(4'h9))[3:2])
        == ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : ((Bit#(4))'(4'h9))[1:0], enq_msg : Struct1 {id :
        (Bit#(6))'(6'h16), type_ : (Bool)'(True), addr : (x_17).addr, value :
        unpack(0)}});
        let x_25 <- makeEnq_parentChildren00(x_24);
        let x_26 <- releaseMSHR_00(x_4);
    endrule

    rule rule_exec_00_28001;
        let x_0 <- deq_fifoL2E_00();
        Struct6 x_1 = ((x_0).lr_ir_pp);
        Bit#(4) x_2 = ((x_1).ir_msg_from);
        Struct1 x_3 = ((x_1).ir_msg);
        Bit#(3) x_4 = ((x_1).ir_mshr_id);
        Bool x_5 = ((x_1).ir_is_rs_rel);
        when (! (x_5), noAction);
        Struct9 x_6 = ((x_0).lr_ir);
        Struct10 x_7 = ((x_6).info);
        Struct5 x_8 = ((x_1).ir_by_victim);
        Vector#(4, Bit#(64)) x_9 = ((x_0).lr_value);
        let x_10 <- getMSHR_00(x_4);
        let x_11 <- getMSHRRq_00(x_4);
        Struct1 x_12 = (unpack(0));
        Vector#(4, Bit#(64)) x_13 = (unpack(0));
        Bool x_14 = ((x_7).mesi_owned);
        Bit#(3) x_15 = ((x_7).mesi_status);
        Struct15 x_16 = (Struct15 {dir_st : (((x_7).mesi_dir_st) ==
        ((Bit#(3))'(3'h0)) ? ((Bit#(3))'(3'h1)) : ((x_7).mesi_dir_st)),
        dir_excl : ((((x_7).mesi_dir_sharers)[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        ((((((x_7).mesi_dir_sharers)[3:1])[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        (((((((x_7).mesi_dir_sharers)[3:1])[2:1])[0:0]) == ((Bit#(1))'(1'h1))
        ? ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        ((((((((x_7).mesi_dir_sharers)[3:1])[2:1])[1:1])[0:0]) ==
        ((Bit#(1))'(1'h1)) ? ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        (unpack(0))))))))))))), dir_sharers : (x_7).mesi_dir_sharers});
        when ((x_2) == ((Bit#(4))'(4'h1)), noAction);
        when (((x_3).id) == ((Bit#(6))'(6'h15)), noAction);
        when (! ((x_3).type_), noAction);
        when ((((((x_16).dir_st) == ((Bit#(3))'(3'h4))) && (((x_16).dir_excl)
        == ((Bit#(2))'(2'h1))) ? ((Bit#(3))'(3'h4)) : (((((x_16).dir_st) ==
        ((Bit#(3))'(3'h3))) && (((x_16).dir_excl) == ((Bit#(2))'(2'h1))) ?
        ((Bit#(3))'(3'h3)) : (((((x_16).dir_st) == ((Bit#(3))'(3'h2))) &&
        ((((x_16).dir_sharers) | (((Bit#(4))'(4'h1)) << ((Bit#(2))'(2'h1))))
        == ((x_16).dir_sharers)) ? ((Bit#(3))'(3'h2)) :
        ((Bit#(3))'(3'h1)))))))) == ((Bit#(3))'(3'h1)), noAction);
        Struct1 x_17 = (x_3);
        Struct16 x_18 = (Struct16 {addr : (x_3).addr, info_write :
        (Bool)'(False), info_hit : (x_6).info_hit, info_way : (x_6).info_way,
        edir_hit : (x_6).edir_hit, edir_way : (x_6).edir_way, edir_slot :
        (x_6).edir_slot, info : (x_6).info, value_write : (Bool)'(False),
        value : unpack(0), may_victim : (x_6).may_victim, reps :
        (x_6).reps});
        let x_20 = ?;
        if ((x_8).valid) begin
            x_20 = x_9;
        end else begin
            let x_19 <- cache__00__valueRsLineRq(unpack(0));
            x_20 = x_19;
        end
        Struct18 x_21 = (Struct18 {enq_type : ((((Bit#(4))'(4'h9))[3:2]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : (((((Bit#(4))'(4'h9))[3:2])
        == ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : ((Bit#(4))'(4'h9))[1:0], enq_msg : Struct1 {id :
        (Bit#(6))'(6'h16), type_ : (Bool)'(True), addr : (x_17).addr, value :
        unpack(0)}});
        let x_22 <- makeEnq_parentChildren00(x_21);
        let x_23 <- releaseMSHR_00(x_4);
    endrule

    rule rule_exec_00_290001;
        let x_0 <- deq_fifoL2E_00();
        Struct6 x_1 = ((x_0).lr_ir_pp);
        Bit#(4) x_2 = ((x_1).ir_msg_from);
        Struct1 x_3 = ((x_1).ir_msg);
        Bit#(3) x_4 = ((x_1).ir_mshr_id);
        Bool x_5 = ((x_1).ir_is_rs_rel);
        when (! (x_5), noAction);
        Struct9 x_6 = ((x_0).lr_ir);
        Struct10 x_7 = ((x_6).info);
        Struct5 x_8 = ((x_1).ir_by_victim);
        Vector#(4, Bit#(64)) x_9 = ((x_0).lr_value);
        let x_10 <- getMSHR_00(x_4);
        let x_11 <- getMSHRRq_00(x_4);
        Struct1 x_12 = (unpack(0));
        Vector#(4, Bit#(64)) x_13 = (unpack(0));
        Bool x_14 = ((x_7).mesi_owned);
        Bit#(3) x_15 = ((x_7).mesi_status);
        Struct15 x_16 = (Struct15 {dir_st : (((x_7).mesi_dir_st) ==
        ((Bit#(3))'(3'h0)) ? ((Bit#(3))'(3'h1)) : ((x_7).mesi_dir_st)),
        dir_excl : ((((x_7).mesi_dir_sharers)[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        ((((((x_7).mesi_dir_sharers)[3:1])[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        (((((((x_7).mesi_dir_sharers)[3:1])[2:1])[0:0]) == ((Bit#(1))'(1'h1))
        ? ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        ((((((((x_7).mesi_dir_sharers)[3:1])[2:1])[1:1])[0:0]) ==
        ((Bit#(1))'(1'h1)) ? ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        (unpack(0))))))))))))), dir_sharers : (x_7).mesi_dir_sharers});
        when ((x_2) == ((Bit#(4))'(4'h1)), noAction);
        when (((x_3).id) == ((Bit#(6))'(6'h15)), noAction);
        when (! ((x_3).type_), noAction);
        when (((x_14) == ((Bool)'(False))) && (((((((x_16).dir_st) ==
        ((Bit#(3))'(3'h4))) && (((x_16).dir_excl) == ((Bit#(2))'(2'h1))) ?
        ((Bit#(3))'(3'h4)) : (((((x_16).dir_st) == ((Bit#(3))'(3'h3))) &&
        (((x_16).dir_excl) == ((Bit#(2))'(2'h1))) ? ((Bit#(3))'(3'h3)) :
        (((((x_16).dir_st) == ((Bit#(3))'(3'h2))) && ((((x_16).dir_sharers) |
        (((Bit#(4))'(4'h1)) << ((Bit#(2))'(2'h1)))) == ((x_16).dir_sharers))
        ? ((Bit#(3))'(3'h2)) : ((Bit#(3))'(3'h1)))))))) ==
        ((Bit#(3))'(3'h2))) && (((x_16).dir_sharers) == (((Bit#(4))'(4'h1))
        << ((Bit#(2))'(2'h1))))), noAction);
        Struct1 x_17 = (x_3);
        Struct16 x_18 = (Struct16 {addr : (x_3).addr, info_write :
        (Bool)'(False), info_hit : (x_6).info_hit, info_way : (x_6).info_way,
        edir_hit : (x_6).edir_hit, edir_way : (x_6).edir_way, edir_slot :
        (x_6).edir_slot, info : (x_6).info, value_write : (Bool)'(False),
        value : unpack(0), may_victim : (x_6).may_victim, reps :
        (x_6).reps});
        Struct16 x_19 = (Struct16 {addr : (x_18).addr, info_write :
        (Bool)'(True), info_hit : (x_18).info_hit, info_way :
        (x_18).info_way, edir_hit : (x_18).edir_hit, edir_way :
        (x_18).edir_way, edir_slot : (x_18).edir_slot, info : Struct10
        {mesi_owned : ((x_18).info).mesi_owned, mesi_status :
        ((x_18).info).mesi_status, mesi_dir_st : (Struct15 {dir_st :
        (Bit#(3))'(3'h1), dir_excl : unpack(0), dir_sharers :
        unpack(0)}).dir_st, mesi_dir_sharers : (((Struct15 {dir_st :
        (Bit#(3))'(3'h1), dir_excl : unpack(0), dir_sharers :
        unpack(0)}).dir_st) == ((Bit#(3))'(3'h2)) ? ((Struct15 {dir_st :
        (Bit#(3))'(3'h1), dir_excl : unpack(0), dir_sharers :
        unpack(0)}).dir_sharers) : (((Bit#(4))'(4'h1)) << ((Struct15 {dir_st
        : (Bit#(3))'(3'h1), dir_excl : unpack(0), dir_sharers :
        unpack(0)}).dir_excl)))}, value_write : (x_18).value_write, value :
        (x_18).value, may_victim : (x_18).may_victim, reps :
        (x_18).reps});
        let x_22 = ?;
        if ((x_8).valid) begin
            let x_20 <- victims__00__setVictim(Struct17 {victim_idx :
            (x_8).data, victim_info : (x_19).info, victim_value :
            ((x_19).value_write ? ((x_19).value) : (x_9))});
            x_22 = x_9;
        end else begin
            let x_21 <- cache__00__valueRsLineRq(x_19);
            x_22 = x_21;
        end
        Struct18 x_23 = (Struct18 {enq_type : ((((Bit#(4))'(4'h9))[3:2]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : (((((Bit#(4))'(4'h9))[3:2])
        == ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : ((Bit#(4))'(4'h9))[1:0], enq_msg : Struct1 {id :
        (Bit#(6))'(6'h16), type_ : (Bool)'(True), addr : (x_17).addr, value :
        unpack(0)}});
        let x_24 <- makeEnq_parentChildren00(x_23);
        let x_25 <- releaseMSHR_00(x_4);
    endrule

    rule rule_exec_00_291001;
        let x_0 <- deq_fifoL2E_00();
        Struct6 x_1 = ((x_0).lr_ir_pp);
        Bit#(4) x_2 = ((x_1).ir_msg_from);
        Struct1 x_3 = ((x_1).ir_msg);
        Bit#(3) x_4 = ((x_1).ir_mshr_id);
        Bool x_5 = ((x_1).ir_is_rs_rel);
        when (! (x_5), noAction);
        Struct9 x_6 = ((x_0).lr_ir);
        Struct10 x_7 = ((x_6).info);
        Struct5 x_8 = ((x_1).ir_by_victim);
        Vector#(4, Bit#(64)) x_9 = ((x_0).lr_value);
        let x_10 <- getMSHR_00(x_4);
        let x_11 <- getMSHRRq_00(x_4);
        Struct1 x_12 = (unpack(0));
        Vector#(4, Bit#(64)) x_13 = (unpack(0));
        Bool x_14 = ((x_7).mesi_owned);
        Bit#(3) x_15 = ((x_7).mesi_status);
        Struct15 x_16 = (Struct15 {dir_st : (((x_7).mesi_dir_st) ==
        ((Bit#(3))'(3'h0)) ? ((Bit#(3))'(3'h1)) : ((x_7).mesi_dir_st)),
        dir_excl : ((((x_7).mesi_dir_sharers)[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        ((((((x_7).mesi_dir_sharers)[3:1])[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        (((((((x_7).mesi_dir_sharers)[3:1])[2:1])[0:0]) == ((Bit#(1))'(1'h1))
        ? ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        ((((((((x_7).mesi_dir_sharers)[3:1])[2:1])[1:1])[0:0]) ==
        ((Bit#(1))'(1'h1)) ? ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        (unpack(0))))))))))))), dir_sharers : (x_7).mesi_dir_sharers});
        when ((x_2) == ((Bit#(4))'(4'h1)), noAction);
        when (((x_3).id) == ((Bit#(6))'(6'h15)), noAction);
        when (! ((x_3).type_), noAction);
        when (((((((x_16).dir_st) == ((Bit#(3))'(3'h4))) &&
        (((x_16).dir_excl) == ((Bit#(2))'(2'h1))) ? ((Bit#(3))'(3'h4)) :
        (((((x_16).dir_st) == ((Bit#(3))'(3'h3))) && (((x_16).dir_excl) ==
        ((Bit#(2))'(2'h1))) ? ((Bit#(3))'(3'h3)) : (((((x_16).dir_st) ==
        ((Bit#(3))'(3'h2))) && ((((x_16).dir_sharers) | (((Bit#(4))'(4'h1))
        << ((Bit#(2))'(2'h1)))) == ((x_16).dir_sharers)) ? ((Bit#(3))'(3'h2))
        : ((Bit#(3))'(3'h1)))))))) == ((Bit#(3))'(3'h2))) &&
        (((Bit#(3))'(3'h1)) < ((((((x_16).dir_sharers)[0:0]) ==
        ((Bit#(1))'(1'h1)) ? ((Bit#(3))'(3'h1)) : ((Bit#(3))'(3'h0)))) +
        (((((((x_16).dir_sharers)[3:1])[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(3))'(3'h1)) : ((Bit#(3))'(3'h0)))) +
        ((((((((x_16).dir_sharers)[3:1])[2:1])[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(3))'(3'h1)) : ((Bit#(3))'(3'h0)))) +
        (((((((((x_16).dir_sharers)[3:1])[2:1])[1:1])[0:0]) ==
        ((Bit#(1))'(1'h1)) ? ((Bit#(3))'(3'h1)) : ((Bit#(3))'(3'h0)))) +
        (unpack(0))))))), noAction);
        Struct1 x_17 = (x_3);
        Struct16 x_18 = (Struct16 {addr : (x_3).addr, info_write :
        (Bool)'(False), info_hit : (x_6).info_hit, info_way : (x_6).info_way,
        edir_hit : (x_6).edir_hit, edir_way : (x_6).edir_way, edir_slot :
        (x_6).edir_slot, info : (x_6).info, value_write : (Bool)'(False),
        value : unpack(0), may_victim : (x_6).may_victim, reps :
        (x_6).reps});
        Struct16 x_19 = (Struct16 {addr : (x_18).addr, info_write :
        (Bool)'(True), info_hit : (x_18).info_hit, info_way :
        (x_18).info_way, edir_hit : (x_18).edir_hit, edir_way :
        (x_18).edir_way, edir_slot : (x_18).edir_slot, info : Struct10
        {mesi_owned : ((x_18).info).mesi_owned, mesi_status :
        ((x_18).info).mesi_status, mesi_dir_st : (Struct15 {dir_st :
        (Bit#(3))'(3'h2), dir_excl : (x_16).dir_excl, dir_sharers :
        ((x_16).dir_sharers) & (~(((Bit#(4))'(4'h1)) <<
        ((Bit#(2))'(2'h1))))}).dir_st, mesi_dir_sharers : (((Struct15 {dir_st
        : (Bit#(3))'(3'h2), dir_excl : (x_16).dir_excl, dir_sharers :
        ((x_16).dir_sharers) & (~(((Bit#(4))'(4'h1)) <<
        ((Bit#(2))'(2'h1))))}).dir_st) == ((Bit#(3))'(3'h2)) ? ((Struct15
        {dir_st : (Bit#(3))'(3'h2), dir_excl : (x_16).dir_excl, dir_sharers :
        ((x_16).dir_sharers) & (~(((Bit#(4))'(4'h1)) <<
        ((Bit#(2))'(2'h1))))}).dir_sharers) : (((Bit#(4))'(4'h1)) <<
        ((Struct15 {dir_st : (Bit#(3))'(3'h2), dir_excl : (x_16).dir_excl,
        dir_sharers : ((x_16).dir_sharers) & (~(((Bit#(4))'(4'h1)) <<
        ((Bit#(2))'(2'h1))))}).dir_excl)))}, value_write :
        (x_18).value_write, value : (x_18).value, may_victim :
        (x_18).may_victim, reps :
        (x_18).reps});
        let x_22 = ?;
        if ((x_8).valid) begin
            let x_20 <- victims__00__setVictim(Struct17 {victim_idx :
            (x_8).data, victim_info : (x_19).info, victim_value :
            ((x_19).value_write ? ((x_19).value) : (x_9))});
            x_22 = x_9;
        end else begin
            let x_21 <- cache__00__valueRsLineRq(x_19);
            x_22 = x_21;
        end
        Struct18 x_23 = (Struct18 {enq_type : ((((Bit#(4))'(4'h9))[3:2]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : (((((Bit#(4))'(4'h9))[3:2])
        == ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : ((Bit#(4))'(4'h9))[1:0], enq_msg : Struct1 {id :
        (Bit#(6))'(6'h16), type_ : (Bool)'(True), addr : (x_17).addr, value :
        unpack(0)}});
        let x_24 <- makeEnq_parentChildren00(x_23);
        let x_25 <- releaseMSHR_00(x_4);
    endrule

    rule rule_exec_00_210001;
        let x_0 <- deq_fifoL2E_00();
        Struct6 x_1 = ((x_0).lr_ir_pp);
        Bit#(4) x_2 = ((x_1).ir_msg_from);
        Struct1 x_3 = ((x_1).ir_msg);
        Bit#(3) x_4 = ((x_1).ir_mshr_id);
        Bool x_5 = ((x_1).ir_is_rs_rel);
        when (! (x_5), noAction);
        Struct9 x_6 = ((x_0).lr_ir);
        Struct10 x_7 = ((x_6).info);
        Struct5 x_8 = ((x_1).ir_by_victim);
        Vector#(4, Bit#(64)) x_9 = ((x_0).lr_value);
        let x_10 <- getMSHR_00(x_4);
        let x_11 <- getMSHRRq_00(x_4);
        Struct1 x_12 = (unpack(0));
        Vector#(4, Bit#(64)) x_13 = (unpack(0));
        Bool x_14 = ((x_7).mesi_owned);
        Bit#(3) x_15 = ((x_7).mesi_status);
        Struct15 x_16 = (Struct15 {dir_st : (((x_7).mesi_dir_st) ==
        ((Bit#(3))'(3'h0)) ? ((Bit#(3))'(3'h1)) : ((x_7).mesi_dir_st)),
        dir_excl : ((((x_7).mesi_dir_sharers)[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        ((((((x_7).mesi_dir_sharers)[3:1])[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        (((((((x_7).mesi_dir_sharers)[3:1])[2:1])[0:0]) == ((Bit#(1))'(1'h1))
        ? ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        ((((((((x_7).mesi_dir_sharers)[3:1])[2:1])[1:1])[0:0]) ==
        ((Bit#(1))'(1'h1)) ? ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        (unpack(0))))))))))))), dir_sharers : (x_7).mesi_dir_sharers});
        when ((x_2) == ((Bit#(4))'(4'h1)), noAction);
        when (((x_3).id) == ((Bit#(6))'(6'h15)), noAction);
        when (! ((x_3).type_), noAction);
        when (((x_14) == ((Bool)'(True))) && (((x_15) == ((Bit#(3))'(3'h2)))
        && (((((((x_16).dir_st) == ((Bit#(3))'(3'h4))) && (((x_16).dir_excl)
        == ((Bit#(2))'(2'h1))) ? ((Bit#(3))'(3'h4)) : (((((x_16).dir_st) ==
        ((Bit#(3))'(3'h3))) && (((x_16).dir_excl) == ((Bit#(2))'(2'h1))) ?
        ((Bit#(3))'(3'h3)) : (((((x_16).dir_st) == ((Bit#(3))'(3'h2))) &&
        ((((x_16).dir_sharers) | (((Bit#(4))'(4'h1)) << ((Bit#(2))'(2'h1))))
        == ((x_16).dir_sharers)) ? ((Bit#(3))'(3'h2)) :
        ((Bit#(3))'(3'h1)))))))) == ((Bit#(3))'(3'h2))) &&
        (((x_16).dir_sharers) == (((Bit#(4))'(4'h1)) <<
        ((Bit#(2))'(2'h1)))))), noAction);
        Struct1 x_17 = (x_3);
        Struct16 x_18 = (Struct16 {addr : (x_3).addr, info_write :
        (Bool)'(False), info_hit : (x_6).info_hit, info_way : (x_6).info_way,
        edir_hit : (x_6).edir_hit, edir_way : (x_6).edir_way, edir_slot :
        (x_6).edir_slot, info : (x_6).info, value_write : (Bool)'(False),
        value : unpack(0), may_victim : (x_6).may_victim, reps :
        (x_6).reps});
        Struct16 x_19 = (Struct16 {addr : (x_18).addr, info_write :
        (Bool)'(True), info_hit : (x_18).info_hit, info_way :
        (x_18).info_way, edir_hit : (x_18).edir_hit, edir_way :
        (x_18).edir_way, edir_slot : (x_18).edir_slot, info : Struct10
        {mesi_owned : ((x_18).info).mesi_owned, mesi_status :
        ((x_18).info).mesi_status, mesi_dir_st : (Struct15 {dir_st :
        (Bit#(3))'(3'h1), dir_excl : unpack(0), dir_sharers :
        unpack(0)}).dir_st, mesi_dir_sharers : (((Struct15 {dir_st :
        (Bit#(3))'(3'h1), dir_excl : unpack(0), dir_sharers :
        unpack(0)}).dir_st) == ((Bit#(3))'(3'h2)) ? ((Struct15 {dir_st :
        (Bit#(3))'(3'h1), dir_excl : unpack(0), dir_sharers :
        unpack(0)}).dir_sharers) : (((Bit#(4))'(4'h1)) << ((Struct15 {dir_st
        : (Bit#(3))'(3'h1), dir_excl : unpack(0), dir_sharers :
        unpack(0)}).dir_excl)))}, value_write : (x_18).value_write, value :
        (x_18).value, may_victim : (x_18).may_victim, reps :
        (x_18).reps});
        Struct16 x_20 = (Struct16 {addr : (x_19).addr, info_write :
        (Bool)'(True), info_hit : (x_19).info_hit, info_way :
        (x_19).info_way, edir_hit : (x_19).edir_hit, edir_way :
        (x_19).edir_way, edir_slot : (x_19).edir_slot, info : Struct10
        {mesi_owned : ((x_19).info).mesi_owned, mesi_status :
        (Bit#(3))'(3'h4), mesi_dir_st : ((x_19).info).mesi_dir_st,
        mesi_dir_sharers : ((x_19).info).mesi_dir_sharers}, value_write :
        (x_19).value_write, value : (x_19).value, may_victim :
        (x_19).may_victim, reps :
        (x_19).reps});
        let x_23 = ?;
        if ((x_8).valid) begin
            let x_21 <- victims__00__setVictim(Struct17 {victim_idx :
            (x_8).data, victim_info : (x_20).info, victim_value :
            ((x_20).value_write ? ((x_20).value) : (x_9))});
            x_23 = x_9;
        end else begin
            let x_22 <- cache__00__valueRsLineRq(x_20);
            x_23 = x_22;
        end
        Struct18 x_24 = (Struct18 {enq_type : ((((Bit#(4))'(4'h9))[3:2]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : (((((Bit#(4))'(4'h9))[3:2])
        == ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : ((Bit#(4))'(4'h9))[1:0], enq_msg : Struct1 {id :
        (Bit#(6))'(6'h16), type_ : (Bool)'(True), addr : (x_17).addr, value :
        unpack(0)}});
        let x_25 <- makeEnq_parentChildren00(x_24);
        let x_26 <- releaseMSHR_00(x_4);
    endrule

    rule rule_exec_00_211001;
        let x_0 <- deq_fifoL2E_00();
        Struct6 x_1 = ((x_0).lr_ir_pp);
        Bit#(4) x_2 = ((x_1).ir_msg_from);
        Struct1 x_3 = ((x_1).ir_msg);
        Bit#(3) x_4 = ((x_1).ir_mshr_id);
        Bool x_5 = ((x_1).ir_is_rs_rel);
        when (! (x_5), noAction);
        Struct9 x_6 = ((x_0).lr_ir);
        Struct10 x_7 = ((x_6).info);
        Struct5 x_8 = ((x_1).ir_by_victim);
        Vector#(4, Bit#(64)) x_9 = ((x_0).lr_value);
        let x_10 <- getMSHR_00(x_4);
        let x_11 <- getMSHRRq_00(x_4);
        Struct1 x_12 = (unpack(0));
        Vector#(4, Bit#(64)) x_13 = (unpack(0));
        Bool x_14 = ((x_7).mesi_owned);
        Bit#(3) x_15 = ((x_7).mesi_status);
        Struct15 x_16 = (Struct15 {dir_st : (((x_7).mesi_dir_st) ==
        ((Bit#(3))'(3'h0)) ? ((Bit#(3))'(3'h1)) : ((x_7).mesi_dir_st)),
        dir_excl : ((((x_7).mesi_dir_sharers)[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        ((((((x_7).mesi_dir_sharers)[3:1])[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        (((((((x_7).mesi_dir_sharers)[3:1])[2:1])[0:0]) == ((Bit#(1))'(1'h1))
        ? ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        ((((((((x_7).mesi_dir_sharers)[3:1])[2:1])[1:1])[0:0]) ==
        ((Bit#(1))'(1'h1)) ? ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        (unpack(0))))))))))))), dir_sharers : (x_7).mesi_dir_sharers});
        when ((x_2) == ((Bit#(4))'(4'h1)), noAction);
        when (((x_3).id) == ((Bit#(6))'(6'h15)), noAction);
        when (! ((x_3).type_), noAction);
        when (! ((((((x_16).dir_st) == ((Bit#(3))'(3'h4))) &&
        (((x_16).dir_excl) == ((Bit#(2))'(2'h1))) ? ((Bit#(3))'(3'h4)) :
        (((((x_16).dir_st) == ((Bit#(3))'(3'h3))) && (((x_16).dir_excl) ==
        ((Bit#(2))'(2'h1))) ? ((Bit#(3))'(3'h3)) : (((((x_16).dir_st) ==
        ((Bit#(3))'(3'h2))) && ((((x_16).dir_sharers) | (((Bit#(4))'(4'h1))
        << ((Bit#(2))'(2'h1)))) == ((x_16).dir_sharers)) ? ((Bit#(3))'(3'h2))
        : ((Bit#(3))'(3'h1)))))))) < ((Bit#(3))'(3'h3))), noAction);
        Struct1 x_17 = (x_3);
        Struct16 x_18 = (Struct16 {addr : (x_3).addr, info_write :
        (Bool)'(False), info_hit : (x_6).info_hit, info_way : (x_6).info_way,
        edir_hit : (x_6).edir_hit, edir_way : (x_6).edir_way, edir_slot :
        (x_6).edir_slot, info : (x_6).info, value_write : (Bool)'(False),
        value : unpack(0), may_victim : (x_6).may_victim, reps :
        (x_6).reps});
        Struct16 x_19 = (Struct16 {addr : (x_18).addr, info_write :
        (x_18).info_write, info_hit : (x_18).info_hit, info_way :
        (x_18).info_way, edir_hit : (x_18).edir_hit, edir_way :
        (x_18).edir_way, edir_slot : (x_18).edir_slot, info : (x_18).info,
        value_write : (Bool)'(True), value : (x_17).value, may_victim :
        (x_18).may_victim, reps : (x_18).reps});
        Struct16 x_20 = (Struct16 {addr : (x_19).addr, info_write :
        (Bool)'(True), info_hit : (x_19).info_hit, info_way :
        (x_19).info_way, edir_hit : (x_19).edir_hit, edir_way :
        (x_19).edir_way, edir_slot : (x_19).edir_slot, info : Struct10
        {mesi_owned : ((x_19).info).mesi_owned, mesi_status :
        (Bit#(3))'(3'h4), mesi_dir_st : ((x_19).info).mesi_dir_st,
        mesi_dir_sharers : ((x_19).info).mesi_dir_sharers}, value_write :
        (x_19).value_write, value : (x_19).value, may_victim :
        (x_19).may_victim, reps : (x_19).reps});
        Struct16 x_21 = (Struct16 {addr : (x_20).addr, info_write :
        (Bool)'(True), info_hit : (x_20).info_hit, info_way :
        (x_20).info_way, edir_hit : (x_20).edir_hit, edir_way :
        (x_20).edir_way, edir_slot : (x_20).edir_slot, info : Struct10
        {mesi_owned : (Bool)'(True), mesi_status : ((x_20).info).mesi_status,
        mesi_dir_st : ((x_20).info).mesi_dir_st, mesi_dir_sharers :
        ((x_20).info).mesi_dir_sharers}, value_write : (x_20).value_write,
        value : (x_20).value, may_victim : (x_20).may_victim, reps :
        (x_20).reps});
        Struct16 x_22 = (Struct16 {addr : (x_21).addr, info_write :
        (Bool)'(True), info_hit : (x_21).info_hit, info_way :
        (x_21).info_way, edir_hit : (x_21).edir_hit, edir_way :
        (x_21).edir_way, edir_slot : (x_21).edir_slot, info : Struct10
        {mesi_owned : ((x_21).info).mesi_owned, mesi_status :
        ((x_21).info).mesi_status, mesi_dir_st : (Struct15 {dir_st :
        (Bit#(3))'(3'h1), dir_excl : unpack(0), dir_sharers :
        unpack(0)}).dir_st, mesi_dir_sharers : (((Struct15 {dir_st :
        (Bit#(3))'(3'h1), dir_excl : unpack(0), dir_sharers :
        unpack(0)}).dir_st) == ((Bit#(3))'(3'h2)) ? ((Struct15 {dir_st :
        (Bit#(3))'(3'h1), dir_excl : unpack(0), dir_sharers :
        unpack(0)}).dir_sharers) : (((Bit#(4))'(4'h1)) << ((Struct15 {dir_st
        : (Bit#(3))'(3'h1), dir_excl : unpack(0), dir_sharers :
        unpack(0)}).dir_excl)))}, value_write : (x_21).value_write, value :
        (x_21).value, may_victim : (x_21).may_victim, reps :
        (x_21).reps});
        let x_25 = ?;
        if ((x_8).valid) begin
            let x_23 <- victims__00__setVictim(Struct17 {victim_idx :
            (x_8).data, victim_info : (x_22).info, victim_value :
            ((x_22).value_write ? ((x_22).value) : (x_9))});
            x_25 = x_9;
        end else begin
            let x_24 <- cache__00__valueRsLineRq(x_22);
            x_25 = x_24;
        end
        Struct18 x_26 = (Struct18 {enq_type : ((((Bit#(4))'(4'h9))[3:2]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : (((((Bit#(4))'(4'h9))[3:2])
        == ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : ((Bit#(4))'(4'h9))[1:0], enq_msg : Struct1 {id :
        (Bit#(6))'(6'h16), type_ : (Bool)'(True), addr : (x_17).addr, value :
        unpack(0)}});
        let x_27 <- makeEnq_parentChildren00(x_26);
        let x_28 <- releaseMSHR_00(x_4);
    endrule

    rule rule_exec_00_000002;
        let x_0 <- deq_fifoL2E_00();
        Struct6 x_1 = ((x_0).lr_ir_pp);
        Bit#(4) x_2 = ((x_1).ir_msg_from);
        Struct1 x_3 = ((x_1).ir_msg);
        Bit#(3) x_4 = ((x_1).ir_mshr_id);
        Bool x_5 = ((x_1).ir_is_rs_rel);
        when (! (x_5), noAction);
        Struct9 x_6 = ((x_0).lr_ir);
        Struct10 x_7 = ((x_6).info);
        Struct5 x_8 = ((x_1).ir_by_victim);
        Vector#(4, Bit#(64)) x_9 = ((x_0).lr_value);
        let x_10 <- getMSHR_00(x_4);
        let x_11 <- getMSHRRq_00(x_4);
        Struct1 x_12 = (unpack(0));
        Vector#(4, Bit#(64)) x_13 = (unpack(0));
        Bool x_14 = ((x_7).mesi_owned);
        Bit#(3) x_15 = ((x_7).mesi_status);
        Struct15 x_16 = (Struct15 {dir_st : (((x_7).mesi_dir_st) ==
        ((Bit#(3))'(3'h0)) ? ((Bit#(3))'(3'h1)) : ((x_7).mesi_dir_st)),
        dir_excl : ((((x_7).mesi_dir_sharers)[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        ((((((x_7).mesi_dir_sharers)[3:1])[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        (((((((x_7).mesi_dir_sharers)[3:1])[2:1])[0:0]) == ((Bit#(1))'(1'h1))
        ? ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        ((((((((x_7).mesi_dir_sharers)[3:1])[2:1])[1:1])[0:0]) ==
        ((Bit#(1))'(1'h1)) ? ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        (unpack(0))))))))))))), dir_sharers : (x_7).mesi_dir_sharers});
        when ((x_2) == ((Bit#(4))'(4'h2)), noAction);
        when (((x_3).id) == ((Bit#(6))'(6'h2)), noAction);
        when (! ((x_3).type_), noAction);
        when ((! (((Bit#(3))'(3'h2)) < ((x_16).dir_st))) && ((x_15) ==
        ((Bit#(3))'(3'h2))), noAction);
        Struct1 x_17 = (x_3);
        Struct16 x_18 = (Struct16 {addr : (x_3).addr, info_write :
        (Bool)'(False), info_hit : (x_6).info_hit, info_way : (x_6).info_way,
        edir_hit : (x_6).edir_hit, edir_way : (x_6).edir_way, edir_slot :
        (x_6).edir_slot, info : (x_6).info, value_write : (Bool)'(False),
        value : unpack(0), may_victim : (x_6).may_victim, reps :
        (x_6).reps});
        Struct16 x_19 = (Struct16 {addr : (x_18).addr, info_write :
        (Bool)'(True), info_hit : (x_18).info_hit, info_way :
        (x_18).info_way, edir_hit : (x_18).edir_hit, edir_way :
        (x_18).edir_way, edir_slot : (x_18).edir_slot, info : Struct10
        {mesi_owned : ((x_18).info).mesi_owned, mesi_status :
        ((x_18).info).mesi_status, mesi_dir_st : (Struct15 {dir_st :
        (Bit#(3))'(3'h2), dir_excl : (x_16).dir_excl, dir_sharers :
        (((x_16).dir_st) == ((Bit#(3))'(3'h2)) ? (((x_16).dir_sharers) |
        (((Bit#(4))'(4'h1)) << ((Bit#(2))'(2'h2)))) : (((Bit#(4))'(4'h1)) <<
        ((Bit#(2))'(2'h2))))}).dir_st, mesi_dir_sharers : (((Struct15 {dir_st
        : (Bit#(3))'(3'h2), dir_excl : (x_16).dir_excl, dir_sharers :
        (((x_16).dir_st) == ((Bit#(3))'(3'h2)) ? (((x_16).dir_sharers) |
        (((Bit#(4))'(4'h1)) << ((Bit#(2))'(2'h2)))) : (((Bit#(4))'(4'h1)) <<
        ((Bit#(2))'(2'h2))))}).dir_st) == ((Bit#(3))'(3'h2)) ? ((Struct15
        {dir_st : (Bit#(3))'(3'h2), dir_excl : (x_16).dir_excl, dir_sharers :
        (((x_16).dir_st) == ((Bit#(3))'(3'h2)) ? (((x_16).dir_sharers) |
        (((Bit#(4))'(4'h1)) << ((Bit#(2))'(2'h2)))) : (((Bit#(4))'(4'h1)) <<
        ((Bit#(2))'(2'h2))))}).dir_sharers) : (((Bit#(4))'(4'h1)) <<
        ((Struct15 {dir_st : (Bit#(3))'(3'h2), dir_excl : (x_16).dir_excl,
        dir_sharers : (((x_16).dir_st) == ((Bit#(3))'(3'h2)) ?
        (((x_16).dir_sharers) | (((Bit#(4))'(4'h1)) << ((Bit#(2))'(2'h2)))) :
        (((Bit#(4))'(4'h1)) << ((Bit#(2))'(2'h2))))}).dir_excl)))},
        value_write : (x_18).value_write, value : (x_18).value, may_victim :
        (x_18).may_victim, reps :
        (x_18).reps});
        let x_22 = ?;
        if ((x_8).valid) begin
            let x_20 <- victims__00__setVictim(Struct17 {victim_idx :
            (x_8).data, victim_info : (x_19).info, victim_value :
            ((x_19).value_write ? ((x_19).value) : (x_9))});
            x_22 = x_9;
        end else begin
            let x_21 <- cache__00__valueRsLineRq(x_19);
            x_22 = x_21;
        end
        Struct18 x_23 = (Struct18 {enq_type : ((((Bit#(4))'(4'ha))[3:2]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : (((((Bit#(4))'(4'ha))[3:2])
        == ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : ((Bit#(4))'(4'ha))[1:0], enq_msg : Struct1 {id :
        (Bit#(6))'(6'h3), type_ : (Bool)'(True), addr : (x_17).addr, value :
        x_22}});
        let x_24 <- makeEnq_parentChildren00(x_23);
        let x_25 <- releaseMSHR_00(x_4);
    endrule

    rule rule_exec_00_001002;
        let x_0 <- deq_fifoL2E_00();
        Struct6 x_1 = ((x_0).lr_ir_pp);
        Bit#(4) x_2 = ((x_1).ir_msg_from);
        Struct1 x_3 = ((x_1).ir_msg);
        Bit#(3) x_4 = ((x_1).ir_mshr_id);
        Bool x_5 = ((x_1).ir_is_rs_rel);
        when (! (x_5), noAction);
        Struct9 x_6 = ((x_0).lr_ir);
        Struct10 x_7 = ((x_6).info);
        Struct5 x_8 = ((x_1).ir_by_victim);
        Vector#(4, Bit#(64)) x_9 = ((x_0).lr_value);
        let x_10 <- getMSHR_00(x_4);
        let x_11 <- getMSHRRq_00(x_4);
        Struct1 x_12 = (unpack(0));
        Vector#(4, Bit#(64)) x_13 = (unpack(0));
        Bool x_14 = ((x_7).mesi_owned);
        Bit#(3) x_15 = ((x_7).mesi_status);
        Struct15 x_16 = (Struct15 {dir_st : (((x_7).mesi_dir_st) ==
        ((Bit#(3))'(3'h0)) ? ((Bit#(3))'(3'h1)) : ((x_7).mesi_dir_st)),
        dir_excl : ((((x_7).mesi_dir_sharers)[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        ((((((x_7).mesi_dir_sharers)[3:1])[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        (((((((x_7).mesi_dir_sharers)[3:1])[2:1])[0:0]) == ((Bit#(1))'(1'h1))
        ? ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        ((((((((x_7).mesi_dir_sharers)[3:1])[2:1])[1:1])[0:0]) ==
        ((Bit#(1))'(1'h1)) ? ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        (unpack(0))))))))))))), dir_sharers : (x_7).mesi_dir_sharers});
        when ((x_2) == ((Bit#(4))'(4'h2)), noAction);
        when (((x_3).id) == ((Bit#(6))'(6'h2)), noAction);
        when (! ((x_3).type_), noAction);
        when ((! ((x_15) < ((Bit#(3))'(3'h3)))) && (((x_16).dir_st) ==
        ((Bit#(3))'(3'h1))), noAction);
        Struct1 x_17 = (x_3);
        Struct16 x_18 = (Struct16 {addr : (x_3).addr, info_write :
        (Bool)'(False), info_hit : (x_6).info_hit, info_way : (x_6).info_way,
        edir_hit : (x_6).edir_hit, edir_way : (x_6).edir_way, edir_slot :
        (x_6).edir_slot, info : (x_6).info, value_write : (Bool)'(False),
        value : unpack(0), may_victim : (x_6).may_victim, reps :
        (x_6).reps});
        Struct16 x_19 = (Struct16 {addr : (x_18).addr, info_write :
        (Bool)'(True), info_hit : (x_18).info_hit, info_way :
        (x_18).info_way, edir_hit : (x_18).edir_hit, edir_way :
        (x_18).edir_way, edir_slot : (x_18).edir_slot, info : Struct10
        {mesi_owned : ((x_18).info).mesi_owned, mesi_status :
        ((x_18).info).mesi_status, mesi_dir_st : (Struct15 {dir_st :
        (Bit#(3))'(3'h3), dir_excl : (Bit#(2))'(2'h2), dir_sharers :
        unpack(0)}).dir_st, mesi_dir_sharers : (((Struct15 {dir_st :
        (Bit#(3))'(3'h3), dir_excl : (Bit#(2))'(2'h2), dir_sharers :
        unpack(0)}).dir_st) == ((Bit#(3))'(3'h2)) ? ((Struct15 {dir_st :
        (Bit#(3))'(3'h3), dir_excl : (Bit#(2))'(2'h2), dir_sharers :
        unpack(0)}).dir_sharers) : (((Bit#(4))'(4'h1)) << ((Struct15 {dir_st
        : (Bit#(3))'(3'h3), dir_excl : (Bit#(2))'(2'h2), dir_sharers :
        unpack(0)}).dir_excl)))}, value_write : (x_18).value_write, value :
        (x_18).value, may_victim : (x_18).may_victim, reps :
        (x_18).reps});
        Struct16 x_20 = (Struct16 {addr : (x_19).addr, info_write :
        (Bool)'(True), info_hit : (x_19).info_hit, info_way :
        (x_19).info_way, edir_hit : (x_19).edir_hit, edir_way :
        (x_19).edir_way, edir_slot : (x_19).edir_slot, info : Struct10
        {mesi_owned : ((x_19).info).mesi_owned, mesi_status :
        (Bit#(3))'(3'h1), mesi_dir_st : ((x_19).info).mesi_dir_st,
        mesi_dir_sharers : ((x_19).info).mesi_dir_sharers}, value_write :
        (x_19).value_write, value : (x_19).value, may_victim :
        (x_19).may_victim, reps :
        (x_19).reps});
        let x_23 = ?;
        if ((x_8).valid) begin
            let x_21 <- victims__00__setVictim(Struct17 {victim_idx :
            (x_8).data, victim_info : (x_20).info, victim_value :
            ((x_20).value_write ? ((x_20).value) : (x_9))});
            x_23 = x_9;
        end else begin
            let x_22 <- cache__00__valueRsLineRq(x_20);
            x_23 = x_22;
        end
        Struct18 x_24 = (Struct18 {enq_type : ((((Bit#(4))'(4'ha))[3:2]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : (((((Bit#(4))'(4'ha))[3:2])
        == ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : ((Bit#(4))'(4'ha))[1:0], enq_msg : Struct1 {id :
        (Bit#(6))'(6'h4), type_ : (Bool)'(True), addr : (x_17).addr, value :
        x_23}});
        let x_25 <- makeEnq_parentChildren00(x_24);
        let x_26 <- releaseMSHR_00(x_4);
    endrule

    rule rule_exec_00_01002;
        let x_0 <- deq_fifoL2E_00();
        Struct6 x_1 = ((x_0).lr_ir_pp);
        Bit#(4) x_2 = ((x_1).ir_msg_from);
        Struct1 x_3 = ((x_1).ir_msg);
        Bit#(3) x_4 = ((x_1).ir_mshr_id);
        Bool x_5 = ((x_1).ir_is_rs_rel);
        when (! (x_5), noAction);
        Struct9 x_6 = ((x_0).lr_ir);
        Struct10 x_7 = ((x_6).info);
        Struct5 x_8 = ((x_1).ir_by_victim);
        Vector#(4, Bit#(64)) x_9 = ((x_0).lr_value);
        let x_10 <- getMSHR_00(x_4);
        let x_11 <- getMSHRRq_00(x_4);
        Struct1 x_12 = (unpack(0));
        Vector#(4, Bit#(64)) x_13 = (unpack(0));
        Bool x_14 = ((x_7).mesi_owned);
        Bit#(3) x_15 = ((x_7).mesi_status);
        Struct15 x_16 = (Struct15 {dir_st : (((x_7).mesi_dir_st) ==
        ((Bit#(3))'(3'h0)) ? ((Bit#(3))'(3'h1)) : ((x_7).mesi_dir_st)),
        dir_excl : ((((x_7).mesi_dir_sharers)[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        ((((((x_7).mesi_dir_sharers)[3:1])[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        (((((((x_7).mesi_dir_sharers)[3:1])[2:1])[0:0]) == ((Bit#(1))'(1'h1))
        ? ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        ((((((((x_7).mesi_dir_sharers)[3:1])[2:1])[1:1])[0:0]) ==
        ((Bit#(1))'(1'h1)) ? ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        (unpack(0))))))))))))), dir_sharers : (x_7).mesi_dir_sharers});
        when ((x_2) == ((Bit#(4))'(4'h2)), noAction);
        when (((x_3).id) == ((Bit#(6))'(6'h2)), noAction);
        when (! ((x_3).type_), noAction);
        when (((x_14) == ((Bool)'(False))) && ((! (((Bit#(3))'(3'h1)) <
        (x_15))) && (! (((Bit#(3))'(3'h2)) < ((x_16).dir_st)))),
        noAction);
        Struct1 x_17 = (x_3);
        Struct16 x_18 = (Struct16 {addr : (x_3).addr, info_write :
        (Bool)'(False), info_hit : (x_6).info_hit, info_way : (x_6).info_way,
        edir_hit : (x_6).edir_hit, edir_way : (x_6).edir_way, edir_slot :
        (x_6).edir_slot, info : (x_6).info, value_write : (Bool)'(False),
        value : unpack(0), may_victim : (x_6).may_victim, reps :
        (x_6).reps});
        let x_20 = ?;
        if ((x_8).valid) begin
            x_20 = x_9;
        end else begin
            let x_19 <- cache__00__valueRsLineRq(unpack(0));
            x_20 = x_19;
        end
        let x_21 <- registerUL_00(Struct19 {r_id : x_4, r_ul_rsb :
        (Bool)'(True), r_ul_rsbTo : ((Bit#(4))'(4'ha))[1:0]});
        Struct18 x_22 = (Struct18 {enq_type : ((((Bit#(4))'(4'h0))[3:2]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : (((((Bit#(4))'(4'h0))[3:2])
        == ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : ((Bit#(4))'(4'h0))[1:0], enq_msg : Struct1 {id :
        (Bit#(6))'(6'h2), type_ : (Bool)'(False), addr : (x_17).addr, value :
        unpack(0)}});
        let x_23 <- makeEnq_parentChildren00(x_22);
    endrule

    rule rule_exec_00_03002;
        let x_0 <- deq_fifoL2E_00();
        Struct6 x_1 = ((x_0).lr_ir_pp);
        Bit#(4) x_2 = ((x_1).ir_msg_from);
        Struct1 x_3 = ((x_1).ir_msg);
        Bit#(3) x_4 = ((x_1).ir_mshr_id);
        Bool x_5 = ((x_1).ir_is_rs_rel);
        when (! (x_5), noAction);
        Struct9 x_6 = ((x_0).lr_ir);
        Struct10 x_7 = ((x_6).info);
        Struct5 x_8 = ((x_1).ir_by_victim);
        Vector#(4, Bit#(64)) x_9 = ((x_0).lr_value);
        let x_10 <- getMSHR_00(x_4);
        let x_11 <- getMSHRRq_00(x_4);
        Struct1 x_12 = (unpack(0));
        Vector#(4, Bit#(64)) x_13 = (unpack(0));
        Bool x_14 = ((x_7).mesi_owned);
        Bit#(3) x_15 = ((x_7).mesi_status);
        Struct15 x_16 = (Struct15 {dir_st : (((x_7).mesi_dir_st) ==
        ((Bit#(3))'(3'h0)) ? ((Bit#(3))'(3'h1)) : ((x_7).mesi_dir_st)),
        dir_excl : ((((x_7).mesi_dir_sharers)[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        ((((((x_7).mesi_dir_sharers)[3:1])[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        (((((((x_7).mesi_dir_sharers)[3:1])[2:1])[0:0]) == ((Bit#(1))'(1'h1))
        ? ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        ((((((((x_7).mesi_dir_sharers)[3:1])[2:1])[1:1])[0:0]) ==
        ((Bit#(1))'(1'h1)) ? ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        (unpack(0))))))))))))), dir_sharers : (x_7).mesi_dir_sharers});
        when ((x_2) == ((Bit#(4))'(4'h2)), noAction);
        when (((x_3).id) == ((Bit#(6))'(6'h2)), noAction);
        when (! ((x_3).type_), noAction);
        when (((Bool)'(True)) && (((Bool)'(True)) && ((! (((Bit#(3))'(3'h1))
        < (x_15))) && ((! (((x_16).dir_st) < ((Bit#(3))'(3'h3)))) && (!
        (((Bit#(3))'(3'h4)) < ((x_16).dir_st)))))), noAction);
        Struct1 x_17 = (x_3);
        Struct16 x_18 = (Struct16 {addr : (x_3).addr, info_write :
        (Bool)'(False), info_hit : (x_6).info_hit, info_way : (x_6).info_way,
        edir_hit : (x_6).edir_hit, edir_way : (x_6).edir_way, edir_slot :
        (x_6).edir_slot, info : (x_6).info, value_write : (Bool)'(False),
        value : unpack(0), may_victim : (x_6).may_victim, reps :
        (x_6).reps});
        let x_20 = ?;
        if ((x_8).valid) begin
            x_20 = x_9;
        end else begin
            let x_19 <- cache__00__valueRsLineRq(unpack(0));
            x_20 = x_19;
        end
        let x_21 <- registerDL_00(Struct20 {r_id : x_4, r_dl_rss_from :
        (unpack(0)) | (((Bit#(4))'(4'h1)) <<
        (({((Bit#(2))'(2'h1)),((x_16).dir_excl)})[1:0])), r_dl_rsb :
        (Bool)'(True), r_dl_rsbTo : (Bit#(4))'(4'ha)});
        Struct18 x_22 = (Struct18 {enq_type :
        ((({((Bit#(2))'(2'h2)),((x_16).dir_excl)})[3:2]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) :
        (((({((Bit#(2))'(2'h2)),((x_16).dir_excl)})[3:2]) ==
        ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : ({((Bit#(2))'(2'h2)),((x_16).dir_excl)})[1:0], enq_msg :
        Struct1 {id : (Bit#(6))'(6'h5), type_ : (Bool)'(False), addr :
        (x_17).addr, value : unpack(0)}});
        let x_23 <- makeEnq_parentChildren00(x_22);
    endrule

    rule rule_exec_00_10002;
        let x_0 <- deq_fifoL2E_00();
        Struct6 x_1 = ((x_0).lr_ir_pp);
        Bit#(4) x_2 = ((x_1).ir_msg_from);
        Struct1 x_3 = ((x_1).ir_msg);
        Bit#(3) x_4 = ((x_1).ir_mshr_id);
        Bool x_5 = ((x_1).ir_is_rs_rel);
        when (! (x_5), noAction);
        Struct9 x_6 = ((x_0).lr_ir);
        Struct10 x_7 = ((x_6).info);
        Struct5 x_8 = ((x_1).ir_by_victim);
        Vector#(4, Bit#(64)) x_9 = ((x_0).lr_value);
        let x_10 <- getMSHR_00(x_4);
        let x_11 <- getMSHRRq_00(x_4);
        Struct1 x_12 = (unpack(0));
        Vector#(4, Bit#(64)) x_13 = (unpack(0));
        Bool x_14 = ((x_7).mesi_owned);
        Bit#(3) x_15 = ((x_7).mesi_status);
        Struct15 x_16 = (Struct15 {dir_st : (((x_7).mesi_dir_st) ==
        ((Bit#(3))'(3'h0)) ? ((Bit#(3))'(3'h1)) : ((x_7).mesi_dir_st)),
        dir_excl : ((((x_7).mesi_dir_sharers)[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        ((((((x_7).mesi_dir_sharers)[3:1])[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        (((((((x_7).mesi_dir_sharers)[3:1])[2:1])[0:0]) == ((Bit#(1))'(1'h1))
        ? ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        ((((((((x_7).mesi_dir_sharers)[3:1])[2:1])[1:1])[0:0]) ==
        ((Bit#(1))'(1'h1)) ? ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        (unpack(0))))))))))))), dir_sharers : (x_7).mesi_dir_sharers});
        when ((x_2) == ((Bit#(4))'(4'h2)), noAction);
        when (((x_3).id) == ((Bit#(6))'(6'ha)), noAction);
        when (! ((x_3).type_), noAction);
        when ((! ((x_15) < ((Bit#(3))'(3'h3)))) || (((x_15) ==
        ((Bit#(3))'(3'h2))) && (((x_14) == ((Bool)'(True))) &&
        ((((x_16).dir_st) == ((Bit#(3))'(3'h2))) && (((x_16).dir_sharers) ==
        (((Bit#(4))'(4'h1)) << ((Bit#(2))'(2'h2))))))), noAction);
        Struct1 x_17 = (x_3);
        Struct16 x_18 = (Struct16 {addr : (x_3).addr, info_write :
        (Bool)'(False), info_hit : (x_6).info_hit, info_way : (x_6).info_way,
        edir_hit : (x_6).edir_hit, edir_way : (x_6).edir_way, edir_slot :
        (x_6).edir_slot, info : (x_6).info, value_write : (Bool)'(False),
        value : unpack(0), may_victim : (x_6).may_victim, reps :
        (x_6).reps});
        Struct16 x_19 = (Struct16 {addr : (x_18).addr, info_write :
        (Bool)'(True), info_hit : (x_18).info_hit, info_way :
        (x_18).info_way, edir_hit : (x_18).edir_hit, edir_way :
        (x_18).edir_way, edir_slot : (x_18).edir_slot, info : Struct10
        {mesi_owned : ((x_18).info).mesi_owned, mesi_status :
        ((x_18).info).mesi_status, mesi_dir_st : (Struct15 {dir_st :
        (Bit#(3))'(3'h4), dir_excl : (Bit#(2))'(2'h2), dir_sharers :
        unpack(0)}).dir_st, mesi_dir_sharers : (((Struct15 {dir_st :
        (Bit#(3))'(3'h4), dir_excl : (Bit#(2))'(2'h2), dir_sharers :
        unpack(0)}).dir_st) == ((Bit#(3))'(3'h2)) ? ((Struct15 {dir_st :
        (Bit#(3))'(3'h4), dir_excl : (Bit#(2))'(2'h2), dir_sharers :
        unpack(0)}).dir_sharers) : (((Bit#(4))'(4'h1)) << ((Struct15 {dir_st
        : (Bit#(3))'(3'h4), dir_excl : (Bit#(2))'(2'h2), dir_sharers :
        unpack(0)}).dir_excl)))}, value_write : (x_18).value_write, value :
        (x_18).value, may_victim : (x_18).may_victim, reps :
        (x_18).reps});
        Struct16 x_20 = (Struct16 {addr : (x_19).addr, info_write :
        (Bool)'(True), info_hit : (x_19).info_hit, info_way :
        (x_19).info_way, edir_hit : (x_19).edir_hit, edir_way :
        (x_19).edir_way, edir_slot : (x_19).edir_slot, info : Struct10
        {mesi_owned : ((x_19).info).mesi_owned, mesi_status :
        (Bit#(3))'(3'h1), mesi_dir_st : ((x_19).info).mesi_dir_st,
        mesi_dir_sharers : ((x_19).info).mesi_dir_sharers}, value_write :
        (x_19).value_write, value : (x_19).value, may_victim :
        (x_19).may_victim, reps : (x_19).reps});
        Struct16 x_21 = (Struct16 {addr : (x_20).addr, info_write :
        (Bool)'(True), info_hit : (x_20).info_hit, info_way :
        (x_20).info_way, edir_hit : (x_20).edir_hit, edir_way :
        (x_20).edir_way, edir_slot : (x_20).edir_slot, info : Struct10
        {mesi_owned : (Bool)'(False), mesi_status :
        ((x_20).info).mesi_status, mesi_dir_st : ((x_20).info).mesi_dir_st,
        mesi_dir_sharers : ((x_20).info).mesi_dir_sharers}, value_write :
        (x_20).value_write, value : (x_20).value, may_victim :
        (x_20).may_victim, reps :
        (x_20).reps});
        let x_24 = ?;
        if ((x_8).valid) begin
            let x_22 <- victims__00__setVictim(Struct17 {victim_idx :
            (x_8).data, victim_info : (x_21).info, victim_value :
            ((x_21).value_write ? ((x_21).value) : (x_9))});
            x_24 = x_9;
        end else begin
            let x_23 <- cache__00__valueRsLineRq(x_21);
            x_24 = x_23;
        end
        Struct18 x_25 = (Struct18 {enq_type : ((((Bit#(4))'(4'ha))[3:2]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : (((((Bit#(4))'(4'ha))[3:2])
        == ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : ((Bit#(4))'(4'ha))[1:0], enq_msg : Struct1 {id :
        (Bit#(6))'(6'hb), type_ : (Bool)'(True), addr : (x_17).addr, value :
        unpack(0)}});
        let x_26 <- makeEnq_parentChildren00(x_25);
        let x_27 <- releaseMSHR_00(x_4);
    endrule

    rule rule_exec_00_11002;
        let x_0 <- deq_fifoL2E_00();
        Struct6 x_1 = ((x_0).lr_ir_pp);
        Bit#(4) x_2 = ((x_1).ir_msg_from);
        Struct1 x_3 = ((x_1).ir_msg);
        Bit#(3) x_4 = ((x_1).ir_mshr_id);
        Bool x_5 = ((x_1).ir_is_rs_rel);
        when (! (x_5), noAction);
        Struct9 x_6 = ((x_0).lr_ir);
        Struct10 x_7 = ((x_6).info);
        Struct5 x_8 = ((x_1).ir_by_victim);
        Vector#(4, Bit#(64)) x_9 = ((x_0).lr_value);
        let x_10 <- getMSHR_00(x_4);
        let x_11 <- getMSHRRq_00(x_4);
        Struct1 x_12 = (unpack(0));
        Vector#(4, Bit#(64)) x_13 = (unpack(0));
        Bool x_14 = ((x_7).mesi_owned);
        Bit#(3) x_15 = ((x_7).mesi_status);
        Struct15 x_16 = (Struct15 {dir_st : (((x_7).mesi_dir_st) ==
        ((Bit#(3))'(3'h0)) ? ((Bit#(3))'(3'h1)) : ((x_7).mesi_dir_st)),
        dir_excl : ((((x_7).mesi_dir_sharers)[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        ((((((x_7).mesi_dir_sharers)[3:1])[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        (((((((x_7).mesi_dir_sharers)[3:1])[2:1])[0:0]) == ((Bit#(1))'(1'h1))
        ? ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        ((((((((x_7).mesi_dir_sharers)[3:1])[2:1])[1:1])[0:0]) ==
        ((Bit#(1))'(1'h1)) ? ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        (unpack(0))))))))))))), dir_sharers : (x_7).mesi_dir_sharers});
        when ((x_2) == ((Bit#(4))'(4'h2)), noAction);
        when (((x_3).id) == ((Bit#(6))'(6'ha)), noAction);
        when (! ((x_3).type_), noAction);
        when (((x_14) == ((Bool)'(False))) && ((! (((Bit#(3))'(3'h2)) <
        (x_15))) && (! (((Bit#(3))'(3'h2)) < ((x_16).dir_st)))),
        noAction);
        Struct1 x_17 = (x_3);
        Struct16 x_18 = (Struct16 {addr : (x_3).addr, info_write :
        (Bool)'(False), info_hit : (x_6).info_hit, info_way : (x_6).info_way,
        edir_hit : (x_6).edir_hit, edir_way : (x_6).edir_way, edir_slot :
        (x_6).edir_slot, info : (x_6).info, value_write : (Bool)'(False),
        value : unpack(0), may_victim : (x_6).may_victim, reps :
        (x_6).reps});
        let x_20 = ?;
        if ((x_8).valid) begin
            x_20 = x_9;
        end else begin
            let x_19 <- cache__00__valueRsLineRq(unpack(0));
            x_20 = x_19;
        end
        let x_21 <- registerUL_00(Struct19 {r_id : x_4, r_ul_rsb :
        (Bool)'(True), r_ul_rsbTo : ((Bit#(4))'(4'ha))[1:0]});
        Struct18 x_22 = (Struct18 {enq_type : ((((Bit#(4))'(4'h0))[3:2]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : (((((Bit#(4))'(4'h0))[3:2])
        == ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : ((Bit#(4))'(4'h0))[1:0], enq_msg : Struct1 {id :
        (Bit#(6))'(6'ha), type_ : (Bool)'(False), addr : (x_17).addr, value :
        unpack(0)}});
        let x_23 <- makeEnq_parentChildren00(x_22);
    endrule

    rule rule_exec_00_14002;
        let x_0 <- deq_fifoL2E_00();
        Struct6 x_1 = ((x_0).lr_ir_pp);
        Bit#(4) x_2 = ((x_1).ir_msg_from);
        Struct1 x_3 = ((x_1).ir_msg);
        Bit#(3) x_4 = ((x_1).ir_mshr_id);
        Bool x_5 = ((x_1).ir_is_rs_rel);
        when (! (x_5), noAction);
        Struct9 x_6 = ((x_0).lr_ir);
        Struct10 x_7 = ((x_6).info);
        Struct5 x_8 = ((x_1).ir_by_victim);
        Vector#(4, Bit#(64)) x_9 = ((x_0).lr_value);
        let x_10 <- getMSHR_00(x_4);
        let x_11 <- getMSHRRq_00(x_4);
        Struct1 x_12 = (unpack(0));
        Vector#(4, Bit#(64)) x_13 = (unpack(0));
        Bool x_14 = ((x_7).mesi_owned);
        Bit#(3) x_15 = ((x_7).mesi_status);
        Struct15 x_16 = (Struct15 {dir_st : (((x_7).mesi_dir_st) ==
        ((Bit#(3))'(3'h0)) ? ((Bit#(3))'(3'h1)) : ((x_7).mesi_dir_st)),
        dir_excl : ((((x_7).mesi_dir_sharers)[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        ((((((x_7).mesi_dir_sharers)[3:1])[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        (((((((x_7).mesi_dir_sharers)[3:1])[2:1])[0:0]) == ((Bit#(1))'(1'h1))
        ? ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        ((((((((x_7).mesi_dir_sharers)[3:1])[2:1])[1:1])[0:0]) ==
        ((Bit#(1))'(1'h1)) ? ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        (unpack(0))))))))))))), dir_sharers : (x_7).mesi_dir_sharers});
        when ((x_2) == ((Bit#(4))'(4'h2)), noAction);
        when (((x_3).id) == ((Bit#(6))'(6'ha)), noAction);
        when (! ((x_3).type_), noAction);
        when (((Bool)'(True)) && (((Bool)'(True)) && ((! (((Bit#(3))'(3'h1))
        < (x_15))) && ((! (((x_16).dir_st) < ((Bit#(3))'(3'h3)))) && (!
        (((Bit#(3))'(3'h4)) < ((x_16).dir_st)))))), noAction);
        Struct1 x_17 = (x_3);
        Struct16 x_18 = (Struct16 {addr : (x_3).addr, info_write :
        (Bool)'(False), info_hit : (x_6).info_hit, info_way : (x_6).info_way,
        edir_hit : (x_6).edir_hit, edir_way : (x_6).edir_way, edir_slot :
        (x_6).edir_slot, info : (x_6).info, value_write : (Bool)'(False),
        value : unpack(0), may_victim : (x_6).may_victim, reps :
        (x_6).reps});
        let x_20 = ?;
        if ((x_8).valid) begin
            x_20 = x_9;
        end else begin
            let x_19 <- cache__00__valueRsLineRq(unpack(0));
            x_20 = x_19;
        end
        let x_21 <- registerDL_00(Struct20 {r_id : x_4, r_dl_rss_from :
        (unpack(0)) | (((Bit#(4))'(4'h1)) <<
        (({((Bit#(2))'(2'h1)),((x_16).dir_excl)})[1:0])), r_dl_rsb :
        (Bool)'(True), r_dl_rsbTo : (Bit#(4))'(4'ha)});
        Struct18 x_22 = (Struct18 {enq_type :
        ((({((Bit#(2))'(2'h2)),((x_16).dir_excl)})[3:2]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) :
        (((({((Bit#(2))'(2'h2)),((x_16).dir_excl)})[3:2]) ==
        ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : ({((Bit#(2))'(2'h2)),((x_16).dir_excl)})[1:0], enq_msg :
        Struct1 {id : (Bit#(6))'(6'he), type_ : (Bool)'(False), addr :
        (x_17).addr, value : unpack(0)}});
        let x_23 <- makeEnq_parentChildren00(x_22);
    endrule

    rule rule_exec_00_15002;
        let x_0 <- deq_fifoL2E_00();
        Struct6 x_1 = ((x_0).lr_ir_pp);
        Bit#(4) x_2 = ((x_1).ir_msg_from);
        Struct1 x_3 = ((x_1).ir_msg);
        Bit#(3) x_4 = ((x_1).ir_mshr_id);
        Bool x_5 = ((x_1).ir_is_rs_rel);
        when (! (x_5), noAction);
        Struct9 x_6 = ((x_0).lr_ir);
        Struct10 x_7 = ((x_6).info);
        Struct5 x_8 = ((x_1).ir_by_victim);
        Vector#(4, Bit#(64)) x_9 = ((x_0).lr_value);
        let x_10 <- getMSHR_00(x_4);
        let x_11 <- getMSHRRq_00(x_4);
        Struct1 x_12 = (unpack(0));
        Vector#(4, Bit#(64)) x_13 = (unpack(0));
        Bool x_14 = ((x_7).mesi_owned);
        Bit#(3) x_15 = ((x_7).mesi_status);
        Struct15 x_16 = (Struct15 {dir_st : (((x_7).mesi_dir_st) ==
        ((Bit#(3))'(3'h0)) ? ((Bit#(3))'(3'h1)) : ((x_7).mesi_dir_st)),
        dir_excl : ((((x_7).mesi_dir_sharers)[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        ((((((x_7).mesi_dir_sharers)[3:1])[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        (((((((x_7).mesi_dir_sharers)[3:1])[2:1])[0:0]) == ((Bit#(1))'(1'h1))
        ? ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        ((((((((x_7).mesi_dir_sharers)[3:1])[2:1])[1:1])[0:0]) ==
        ((Bit#(1))'(1'h1)) ? ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        (unpack(0))))))))))))), dir_sharers : (x_7).mesi_dir_sharers});
        when ((x_2) == ((Bit#(4))'(4'h2)), noAction);
        when (((x_3).id) == ((Bit#(6))'(6'ha)), noAction);
        when (! ((x_3).type_), noAction);
        when (((Bool)'(True)) && (((Bool)'(True)) && ((!
        ((((x_16).dir_sharers) & (~(((Bit#(4))'(4'h1)) <<
        ((Bit#(2))'(2'h2))))) == ((Bit#(4))'(4'h0)))) && (((x_14) ==
        ((Bool)'(True))) && ((! (((Bit#(3))'(3'h2)) < (x_15))) &&
        (((x_16).dir_st) == ((Bit#(3))'(3'h2))))))), noAction);
        Struct1 x_17 = (x_3);
        Struct16 x_18 = (Struct16 {addr : (x_3).addr, info_write :
        (Bool)'(False), info_hit : (x_6).info_hit, info_way : (x_6).info_way,
        edir_hit : (x_6).edir_hit, edir_way : (x_6).edir_way, edir_slot :
        (x_6).edir_slot, info : (x_6).info, value_write : (Bool)'(False),
        value : unpack(0), may_victim : (x_6).may_victim, reps :
        (x_6).reps});
        let x_20 = ?;
        if ((x_8).valid) begin
            x_20 = x_9;
        end else begin
            let x_19 <- cache__00__valueRsLineRq(unpack(0));
            x_20 = x_19;
        end
        let x_21 <- registerDL_00(Struct20 {r_id : x_4, r_dl_rss_from :
        ((x_16).dir_sharers) & (~(((Bit#(4))'(4'h1)) << ((Bit#(2))'(2'h2)))),
        r_dl_rsb : (Bool)'(True), r_dl_rsbTo : (Bit#(4))'(4'ha)});
        let x_22 <- broadcast_parentChildren00(Struct21 {cs_inds :
        ((x_16).dir_sharers) & (~(((Bit#(4))'(4'h1)) << ((Bit#(2))'(2'h2)))),
        cs_msg : Struct1 {id : (Bit#(6))'(6'hc), type_ : (Bool)'(False), addr
        : (x_17).addr, value : unpack(0)}});
    endrule

    rule rule_exec_00_25002;
        let x_0 <- deq_fifoL2E_00();
        Struct6 x_1 = ((x_0).lr_ir_pp);
        Bit#(4) x_2 = ((x_1).ir_msg_from);
        Struct1 x_3 = ((x_1).ir_msg);
        Bit#(3) x_4 = ((x_1).ir_mshr_id);
        Bool x_5 = ((x_1).ir_is_rs_rel);
        when (! (x_5), noAction);
        Struct9 x_6 = ((x_0).lr_ir);
        Struct10 x_7 = ((x_6).info);
        Struct5 x_8 = ((x_1).ir_by_victim);
        Vector#(4, Bit#(64)) x_9 = ((x_0).lr_value);
        let x_10 <- getMSHR_00(x_4);
        let x_11 <- getMSHRRq_00(x_4);
        Struct1 x_12 = (unpack(0));
        Vector#(4, Bit#(64)) x_13 = (unpack(0));
        Bool x_14 = ((x_7).mesi_owned);
        Bit#(3) x_15 = ((x_7).mesi_status);
        Struct15 x_16 = (Struct15 {dir_st : (((x_7).mesi_dir_st) ==
        ((Bit#(3))'(3'h0)) ? ((Bit#(3))'(3'h1)) : ((x_7).mesi_dir_st)),
        dir_excl : ((((x_7).mesi_dir_sharers)[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        ((((((x_7).mesi_dir_sharers)[3:1])[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        (((((((x_7).mesi_dir_sharers)[3:1])[2:1])[0:0]) == ((Bit#(1))'(1'h1))
        ? ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        ((((((((x_7).mesi_dir_sharers)[3:1])[2:1])[1:1])[0:0]) ==
        ((Bit#(1))'(1'h1)) ? ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        (unpack(0))))))))))))), dir_sharers : (x_7).mesi_dir_sharers});
        when ((x_2) == ((Bit#(4))'(4'h2)), noAction);
        when (((x_3).id) == ((Bit#(6))'(6'h14)), noAction);
        when (! ((x_3).type_), noAction);
        when ((((((x_16).dir_st) == ((Bit#(3))'(3'h4))) && (((x_16).dir_excl)
        == ((Bit#(2))'(2'h2))) ? ((Bit#(3))'(3'h4)) : (((((x_16).dir_st) ==
        ((Bit#(3))'(3'h3))) && (((x_16).dir_excl) == ((Bit#(2))'(2'h2))) ?
        ((Bit#(3))'(3'h3)) : (((((x_16).dir_st) == ((Bit#(3))'(3'h2))) &&
        ((((x_16).dir_sharers) | (((Bit#(4))'(4'h1)) << ((Bit#(2))'(2'h2))))
        == ((x_16).dir_sharers)) ? ((Bit#(3))'(3'h2)) :
        ((Bit#(3))'(3'h1)))))))) == ((Bit#(3))'(3'h1)), noAction);
        Struct1 x_17 = (x_3);
        Struct16 x_18 = (Struct16 {addr : (x_3).addr, info_write :
        (Bool)'(False), info_hit : (x_6).info_hit, info_way : (x_6).info_way,
        edir_hit : (x_6).edir_hit, edir_way : (x_6).edir_way, edir_slot :
        (x_6).edir_slot, info : (x_6).info, value_write : (Bool)'(False),
        value : unpack(0), may_victim : (x_6).may_victim, reps :
        (x_6).reps});
        let x_20 = ?;
        if ((x_8).valid) begin
            x_20 = x_9;
        end else begin
            let x_19 <- cache__00__valueRsLineRq(unpack(0));
            x_20 = x_19;
        end
        Struct18 x_21 = (Struct18 {enq_type : ((((Bit#(4))'(4'ha))[3:2]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : (((((Bit#(4))'(4'ha))[3:2])
        == ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : ((Bit#(4))'(4'ha))[1:0], enq_msg : Struct1 {id :
        (Bit#(6))'(6'h16), type_ : (Bool)'(True), addr : (x_17).addr, value :
        unpack(0)}});
        let x_22 <- makeEnq_parentChildren00(x_21);
        let x_23 <- releaseMSHR_00(x_4);
    endrule

    rule rule_exec_00_2600002;
        let x_0 <- deq_fifoL2E_00();
        Struct6 x_1 = ((x_0).lr_ir_pp);
        Bit#(4) x_2 = ((x_1).ir_msg_from);
        Struct1 x_3 = ((x_1).ir_msg);
        Bit#(3) x_4 = ((x_1).ir_mshr_id);
        Bool x_5 = ((x_1).ir_is_rs_rel);
        when (! (x_5), noAction);
        Struct9 x_6 = ((x_0).lr_ir);
        Struct10 x_7 = ((x_6).info);
        Struct5 x_8 = ((x_1).ir_by_victim);
        Vector#(4, Bit#(64)) x_9 = ((x_0).lr_value);
        let x_10 <- getMSHR_00(x_4);
        let x_11 <- getMSHRRq_00(x_4);
        Struct1 x_12 = (unpack(0));
        Vector#(4, Bit#(64)) x_13 = (unpack(0));
        Bool x_14 = ((x_7).mesi_owned);
        Bit#(3) x_15 = ((x_7).mesi_status);
        Struct15 x_16 = (Struct15 {dir_st : (((x_7).mesi_dir_st) ==
        ((Bit#(3))'(3'h0)) ? ((Bit#(3))'(3'h1)) : ((x_7).mesi_dir_st)),
        dir_excl : ((((x_7).mesi_dir_sharers)[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        ((((((x_7).mesi_dir_sharers)[3:1])[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        (((((((x_7).mesi_dir_sharers)[3:1])[2:1])[0:0]) == ((Bit#(1))'(1'h1))
        ? ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        ((((((((x_7).mesi_dir_sharers)[3:1])[2:1])[1:1])[0:0]) ==
        ((Bit#(1))'(1'h1)) ? ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        (unpack(0))))))))))))), dir_sharers : (x_7).mesi_dir_sharers});
        when ((x_2) == ((Bit#(4))'(4'h2)), noAction);
        when (((x_3).id) == ((Bit#(6))'(6'h14)), noAction);
        when (! ((x_3).type_), noAction);
        when (((x_14) == ((Bool)'(False))) && (((((((x_16).dir_st) ==
        ((Bit#(3))'(3'h4))) && (((x_16).dir_excl) == ((Bit#(2))'(2'h2))) ?
        ((Bit#(3))'(3'h4)) : (((((x_16).dir_st) == ((Bit#(3))'(3'h3))) &&
        (((x_16).dir_excl) == ((Bit#(2))'(2'h2))) ? ((Bit#(3))'(3'h3)) :
        (((((x_16).dir_st) == ((Bit#(3))'(3'h2))) && ((((x_16).dir_sharers) |
        (((Bit#(4))'(4'h1)) << ((Bit#(2))'(2'h2)))) == ((x_16).dir_sharers))
        ? ((Bit#(3))'(3'h2)) : ((Bit#(3))'(3'h1)))))))) ==
        ((Bit#(3))'(3'h2))) && (((x_16).dir_sharers) == (((Bit#(4))'(4'h1))
        << ((Bit#(2))'(2'h2))))), noAction);
        Struct1 x_17 = (x_3);
        Struct16 x_18 = (Struct16 {addr : (x_3).addr, info_write :
        (Bool)'(False), info_hit : (x_6).info_hit, info_way : (x_6).info_way,
        edir_hit : (x_6).edir_hit, edir_way : (x_6).edir_way, edir_slot :
        (x_6).edir_slot, info : (x_6).info, value_write : (Bool)'(False),
        value : unpack(0), may_victim : (x_6).may_victim, reps :
        (x_6).reps});
        Struct16 x_19 = (Struct16 {addr : (x_18).addr, info_write :
        (Bool)'(True), info_hit : (x_18).info_hit, info_way :
        (x_18).info_way, edir_hit : (x_18).edir_hit, edir_way :
        (x_18).edir_way, edir_slot : (x_18).edir_slot, info : Struct10
        {mesi_owned : ((x_18).info).mesi_owned, mesi_status :
        ((x_18).info).mesi_status, mesi_dir_st : (Struct15 {dir_st :
        (Bit#(3))'(3'h1), dir_excl : unpack(0), dir_sharers :
        unpack(0)}).dir_st, mesi_dir_sharers : (((Struct15 {dir_st :
        (Bit#(3))'(3'h1), dir_excl : unpack(0), dir_sharers :
        unpack(0)}).dir_st) == ((Bit#(3))'(3'h2)) ? ((Struct15 {dir_st :
        (Bit#(3))'(3'h1), dir_excl : unpack(0), dir_sharers :
        unpack(0)}).dir_sharers) : (((Bit#(4))'(4'h1)) << ((Struct15 {dir_st
        : (Bit#(3))'(3'h1), dir_excl : unpack(0), dir_sharers :
        unpack(0)}).dir_excl)))}, value_write : (x_18).value_write, value :
        (x_18).value, may_victim : (x_18).may_victim, reps :
        (x_18).reps});
        let x_22 = ?;
        if ((x_8).valid) begin
            let x_20 <- victims__00__setVictim(Struct17 {victim_idx :
            (x_8).data, victim_info : (x_19).info, victim_value :
            ((x_19).value_write ? ((x_19).value) : (x_9))});
            x_22 = x_9;
        end else begin
            let x_21 <- cache__00__valueRsLineRq(x_19);
            x_22 = x_21;
        end
        Struct18 x_23 = (Struct18 {enq_type : ((((Bit#(4))'(4'ha))[3:2]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : (((((Bit#(4))'(4'ha))[3:2])
        == ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : ((Bit#(4))'(4'ha))[1:0], enq_msg : Struct1 {id :
        (Bit#(6))'(6'h16), type_ : (Bool)'(True), addr : (x_17).addr, value :
        unpack(0)}});
        let x_24 <- makeEnq_parentChildren00(x_23);
        let x_25 <- releaseMSHR_00(x_4);
    endrule

    rule rule_exec_00_2601002;
        let x_0 <- deq_fifoL2E_00();
        Struct6 x_1 = ((x_0).lr_ir_pp);
        Bit#(4) x_2 = ((x_1).ir_msg_from);
        Struct1 x_3 = ((x_1).ir_msg);
        Bit#(3) x_4 = ((x_1).ir_mshr_id);
        Bool x_5 = ((x_1).ir_is_rs_rel);
        when (! (x_5), noAction);
        Struct9 x_6 = ((x_0).lr_ir);
        Struct10 x_7 = ((x_6).info);
        Struct5 x_8 = ((x_1).ir_by_victim);
        Vector#(4, Bit#(64)) x_9 = ((x_0).lr_value);
        let x_10 <- getMSHR_00(x_4);
        let x_11 <- getMSHRRq_00(x_4);
        Struct1 x_12 = (unpack(0));
        Vector#(4, Bit#(64)) x_13 = (unpack(0));
        Bool x_14 = ((x_7).mesi_owned);
        Bit#(3) x_15 = ((x_7).mesi_status);
        Struct15 x_16 = (Struct15 {dir_st : (((x_7).mesi_dir_st) ==
        ((Bit#(3))'(3'h0)) ? ((Bit#(3))'(3'h1)) : ((x_7).mesi_dir_st)),
        dir_excl : ((((x_7).mesi_dir_sharers)[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        ((((((x_7).mesi_dir_sharers)[3:1])[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        (((((((x_7).mesi_dir_sharers)[3:1])[2:1])[0:0]) == ((Bit#(1))'(1'h1))
        ? ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        ((((((((x_7).mesi_dir_sharers)[3:1])[2:1])[1:1])[0:0]) ==
        ((Bit#(1))'(1'h1)) ? ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        (unpack(0))))))))))))), dir_sharers : (x_7).mesi_dir_sharers});
        when ((x_2) == ((Bit#(4))'(4'h2)), noAction);
        when (((x_3).id) == ((Bit#(6))'(6'h14)), noAction);
        when (! ((x_3).type_), noAction);
        when (((x_14) == ((Bool)'(True))) && (((x_15) == ((Bit#(3))'(3'h2)))
        && (((((((x_16).dir_st) == ((Bit#(3))'(3'h4))) && (((x_16).dir_excl)
        == ((Bit#(2))'(2'h2))) ? ((Bit#(3))'(3'h4)) : (((((x_16).dir_st) ==
        ((Bit#(3))'(3'h3))) && (((x_16).dir_excl) == ((Bit#(2))'(2'h2))) ?
        ((Bit#(3))'(3'h3)) : (((((x_16).dir_st) == ((Bit#(3))'(3'h2))) &&
        ((((x_16).dir_sharers) | (((Bit#(4))'(4'h1)) << ((Bit#(2))'(2'h2))))
        == ((x_16).dir_sharers)) ? ((Bit#(3))'(3'h2)) :
        ((Bit#(3))'(3'h1)))))))) == ((Bit#(3))'(3'h2))) &&
        (((x_16).dir_sharers) == (((Bit#(4))'(4'h1)) <<
        ((Bit#(2))'(2'h2)))))), noAction);
        Struct1 x_17 = (x_3);
        Struct16 x_18 = (Struct16 {addr : (x_3).addr, info_write :
        (Bool)'(False), info_hit : (x_6).info_hit, info_way : (x_6).info_way,
        edir_hit : (x_6).edir_hit, edir_way : (x_6).edir_way, edir_slot :
        (x_6).edir_slot, info : (x_6).info, value_write : (Bool)'(False),
        value : unpack(0), may_victim : (x_6).may_victim, reps :
        (x_6).reps});
        Struct16 x_19 = (Struct16 {addr : (x_18).addr, info_write :
        (Bool)'(True), info_hit : (x_18).info_hit, info_way :
        (x_18).info_way, edir_hit : (x_18).edir_hit, edir_way :
        (x_18).edir_way, edir_slot : (x_18).edir_slot, info : Struct10
        {mesi_owned : ((x_18).info).mesi_owned, mesi_status :
        ((x_18).info).mesi_status, mesi_dir_st : (Struct15 {dir_st :
        (Bit#(3))'(3'h1), dir_excl : unpack(0), dir_sharers :
        unpack(0)}).dir_st, mesi_dir_sharers : (((Struct15 {dir_st :
        (Bit#(3))'(3'h1), dir_excl : unpack(0), dir_sharers :
        unpack(0)}).dir_st) == ((Bit#(3))'(3'h2)) ? ((Struct15 {dir_st :
        (Bit#(3))'(3'h1), dir_excl : unpack(0), dir_sharers :
        unpack(0)}).dir_sharers) : (((Bit#(4))'(4'h1)) << ((Struct15 {dir_st
        : (Bit#(3))'(3'h1), dir_excl : unpack(0), dir_sharers :
        unpack(0)}).dir_excl)))}, value_write : (x_18).value_write, value :
        (x_18).value, may_victim : (x_18).may_victim, reps :
        (x_18).reps});
        Struct16 x_20 = (Struct16 {addr : (x_19).addr, info_write :
        (Bool)'(True), info_hit : (x_19).info_hit, info_way :
        (x_19).info_way, edir_hit : (x_19).edir_hit, edir_way :
        (x_19).edir_way, edir_slot : (x_19).edir_slot, info : Struct10
        {mesi_owned : ((x_19).info).mesi_owned, mesi_status :
        (Bit#(3))'(3'h4), mesi_dir_st : ((x_19).info).mesi_dir_st,
        mesi_dir_sharers : ((x_19).info).mesi_dir_sharers}, value_write :
        (x_19).value_write, value : (x_19).value, may_victim :
        (x_19).may_victim, reps :
        (x_19).reps});
        let x_23 = ?;
        if ((x_8).valid) begin
            let x_21 <- victims__00__setVictim(Struct17 {victim_idx :
            (x_8).data, victim_info : (x_20).info, victim_value :
            ((x_20).value_write ? ((x_20).value) : (x_9))});
            x_23 = x_9;
        end else begin
            let x_22 <- cache__00__valueRsLineRq(x_20);
            x_23 = x_22;
        end
        Struct18 x_24 = (Struct18 {enq_type : ((((Bit#(4))'(4'ha))[3:2]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : (((((Bit#(4))'(4'ha))[3:2])
        == ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : ((Bit#(4))'(4'ha))[1:0], enq_msg : Struct1 {id :
        (Bit#(6))'(6'h16), type_ : (Bool)'(True), addr : (x_17).addr, value :
        unpack(0)}});
        let x_25 <- makeEnq_parentChildren00(x_24);
        let x_26 <- releaseMSHR_00(x_4);
    endrule

    rule rule_exec_00_261002;
        let x_0 <- deq_fifoL2E_00();
        Struct6 x_1 = ((x_0).lr_ir_pp);
        Bit#(4) x_2 = ((x_1).ir_msg_from);
        Struct1 x_3 = ((x_1).ir_msg);
        Bit#(3) x_4 = ((x_1).ir_mshr_id);
        Bool x_5 = ((x_1).ir_is_rs_rel);
        when (! (x_5), noAction);
        Struct9 x_6 = ((x_0).lr_ir);
        Struct10 x_7 = ((x_6).info);
        Struct5 x_8 = ((x_1).ir_by_victim);
        Vector#(4, Bit#(64)) x_9 = ((x_0).lr_value);
        let x_10 <- getMSHR_00(x_4);
        let x_11 <- getMSHRRq_00(x_4);
        Struct1 x_12 = (unpack(0));
        Vector#(4, Bit#(64)) x_13 = (unpack(0));
        Bool x_14 = ((x_7).mesi_owned);
        Bit#(3) x_15 = ((x_7).mesi_status);
        Struct15 x_16 = (Struct15 {dir_st : (((x_7).mesi_dir_st) ==
        ((Bit#(3))'(3'h0)) ? ((Bit#(3))'(3'h1)) : ((x_7).mesi_dir_st)),
        dir_excl : ((((x_7).mesi_dir_sharers)[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        ((((((x_7).mesi_dir_sharers)[3:1])[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        (((((((x_7).mesi_dir_sharers)[3:1])[2:1])[0:0]) == ((Bit#(1))'(1'h1))
        ? ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        ((((((((x_7).mesi_dir_sharers)[3:1])[2:1])[1:1])[0:0]) ==
        ((Bit#(1))'(1'h1)) ? ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        (unpack(0))))))))))))), dir_sharers : (x_7).mesi_dir_sharers});
        when ((x_2) == ((Bit#(4))'(4'h2)), noAction);
        when (((x_3).id) == ((Bit#(6))'(6'h14)), noAction);
        when (! ((x_3).type_), noAction);
        when (((((((x_16).dir_st) == ((Bit#(3))'(3'h4))) &&
        (((x_16).dir_excl) == ((Bit#(2))'(2'h2))) ? ((Bit#(3))'(3'h4)) :
        (((((x_16).dir_st) == ((Bit#(3))'(3'h3))) && (((x_16).dir_excl) ==
        ((Bit#(2))'(2'h2))) ? ((Bit#(3))'(3'h3)) : (((((x_16).dir_st) ==
        ((Bit#(3))'(3'h2))) && ((((x_16).dir_sharers) | (((Bit#(4))'(4'h1))
        << ((Bit#(2))'(2'h2)))) == ((x_16).dir_sharers)) ? ((Bit#(3))'(3'h2))
        : ((Bit#(3))'(3'h1)))))))) == ((Bit#(3))'(3'h2))) &&
        (((Bit#(3))'(3'h1)) < ((((((x_16).dir_sharers)[0:0]) ==
        ((Bit#(1))'(1'h1)) ? ((Bit#(3))'(3'h1)) : ((Bit#(3))'(3'h0)))) +
        (((((((x_16).dir_sharers)[3:1])[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(3))'(3'h1)) : ((Bit#(3))'(3'h0)))) +
        ((((((((x_16).dir_sharers)[3:1])[2:1])[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(3))'(3'h1)) : ((Bit#(3))'(3'h0)))) +
        (((((((((x_16).dir_sharers)[3:1])[2:1])[1:1])[0:0]) ==
        ((Bit#(1))'(1'h1)) ? ((Bit#(3))'(3'h1)) : ((Bit#(3))'(3'h0)))) +
        (unpack(0))))))), noAction);
        Struct1 x_17 = (x_3);
        Struct16 x_18 = (Struct16 {addr : (x_3).addr, info_write :
        (Bool)'(False), info_hit : (x_6).info_hit, info_way : (x_6).info_way,
        edir_hit : (x_6).edir_hit, edir_way : (x_6).edir_way, edir_slot :
        (x_6).edir_slot, info : (x_6).info, value_write : (Bool)'(False),
        value : unpack(0), may_victim : (x_6).may_victim, reps :
        (x_6).reps});
        Struct16 x_19 = (Struct16 {addr : (x_18).addr, info_write :
        (Bool)'(True), info_hit : (x_18).info_hit, info_way :
        (x_18).info_way, edir_hit : (x_18).edir_hit, edir_way :
        (x_18).edir_way, edir_slot : (x_18).edir_slot, info : Struct10
        {mesi_owned : ((x_18).info).mesi_owned, mesi_status :
        ((x_18).info).mesi_status, mesi_dir_st : (Struct15 {dir_st :
        (Bit#(3))'(3'h2), dir_excl : (x_16).dir_excl, dir_sharers :
        ((x_16).dir_sharers) & (~(((Bit#(4))'(4'h1)) <<
        ((Bit#(2))'(2'h2))))}).dir_st, mesi_dir_sharers : (((Struct15 {dir_st
        : (Bit#(3))'(3'h2), dir_excl : (x_16).dir_excl, dir_sharers :
        ((x_16).dir_sharers) & (~(((Bit#(4))'(4'h1)) <<
        ((Bit#(2))'(2'h2))))}).dir_st) == ((Bit#(3))'(3'h2)) ? ((Struct15
        {dir_st : (Bit#(3))'(3'h2), dir_excl : (x_16).dir_excl, dir_sharers :
        ((x_16).dir_sharers) & (~(((Bit#(4))'(4'h1)) <<
        ((Bit#(2))'(2'h2))))}).dir_sharers) : (((Bit#(4))'(4'h1)) <<
        ((Struct15 {dir_st : (Bit#(3))'(3'h2), dir_excl : (x_16).dir_excl,
        dir_sharers : ((x_16).dir_sharers) & (~(((Bit#(4))'(4'h1)) <<
        ((Bit#(2))'(2'h2))))}).dir_excl)))}, value_write :
        (x_18).value_write, value : (x_18).value, may_victim :
        (x_18).may_victim, reps :
        (x_18).reps});
        let x_22 = ?;
        if ((x_8).valid) begin
            let x_20 <- victims__00__setVictim(Struct17 {victim_idx :
            (x_8).data, victim_info : (x_19).info, victim_value :
            ((x_19).value_write ? ((x_19).value) : (x_9))});
            x_22 = x_9;
        end else begin
            let x_21 <- cache__00__valueRsLineRq(x_19);
            x_22 = x_21;
        end
        Struct18 x_23 = (Struct18 {enq_type : ((((Bit#(4))'(4'ha))[3:2]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : (((((Bit#(4))'(4'ha))[3:2])
        == ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : ((Bit#(4))'(4'ha))[1:0], enq_msg : Struct1 {id :
        (Bit#(6))'(6'h16), type_ : (Bool)'(True), addr : (x_17).addr, value :
        unpack(0)}});
        let x_24 <- makeEnq_parentChildren00(x_23);
        let x_25 <- releaseMSHR_00(x_4);
    endrule

    rule rule_exec_00_27002;
        let x_0 <- deq_fifoL2E_00();
        Struct6 x_1 = ((x_0).lr_ir_pp);
        Bit#(4) x_2 = ((x_1).ir_msg_from);
        Struct1 x_3 = ((x_1).ir_msg);
        Bit#(3) x_4 = ((x_1).ir_mshr_id);
        Bool x_5 = ((x_1).ir_is_rs_rel);
        when (! (x_5), noAction);
        Struct9 x_6 = ((x_0).lr_ir);
        Struct10 x_7 = ((x_6).info);
        Struct5 x_8 = ((x_1).ir_by_victim);
        Vector#(4, Bit#(64)) x_9 = ((x_0).lr_value);
        let x_10 <- getMSHR_00(x_4);
        let x_11 <- getMSHRRq_00(x_4);
        Struct1 x_12 = (unpack(0));
        Vector#(4, Bit#(64)) x_13 = (unpack(0));
        Bool x_14 = ((x_7).mesi_owned);
        Bit#(3) x_15 = ((x_7).mesi_status);
        Struct15 x_16 = (Struct15 {dir_st : (((x_7).mesi_dir_st) ==
        ((Bit#(3))'(3'h0)) ? ((Bit#(3))'(3'h1)) : ((x_7).mesi_dir_st)),
        dir_excl : ((((x_7).mesi_dir_sharers)[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        ((((((x_7).mesi_dir_sharers)[3:1])[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        (((((((x_7).mesi_dir_sharers)[3:1])[2:1])[0:0]) == ((Bit#(1))'(1'h1))
        ? ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        ((((((((x_7).mesi_dir_sharers)[3:1])[2:1])[1:1])[0:0]) ==
        ((Bit#(1))'(1'h1)) ? ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        (unpack(0))))))))))))), dir_sharers : (x_7).mesi_dir_sharers});
        when ((x_2) == ((Bit#(4))'(4'h2)), noAction);
        when (((x_3).id) == ((Bit#(6))'(6'h14)), noAction);
        when (! ((x_3).type_), noAction);
        when ((((((x_16).dir_st) == ((Bit#(3))'(3'h4))) && (((x_16).dir_excl)
        == ((Bit#(2))'(2'h2))) ? ((Bit#(3))'(3'h4)) : (((((x_16).dir_st) ==
        ((Bit#(3))'(3'h3))) && (((x_16).dir_excl) == ((Bit#(2))'(2'h2))) ?
        ((Bit#(3))'(3'h3)) : (((((x_16).dir_st) == ((Bit#(3))'(3'h2))) &&
        ((((x_16).dir_sharers) | (((Bit#(4))'(4'h1)) << ((Bit#(2))'(2'h2))))
        == ((x_16).dir_sharers)) ? ((Bit#(3))'(3'h2)) :
        ((Bit#(3))'(3'h1)))))))) == ((Bit#(3))'(3'h3)), noAction);
        Struct1 x_17 = (x_3);
        Struct16 x_18 = (Struct16 {addr : (x_3).addr, info_write :
        (Bool)'(False), info_hit : (x_6).info_hit, info_way : (x_6).info_way,
        edir_hit : (x_6).edir_hit, edir_way : (x_6).edir_way, edir_slot :
        (x_6).edir_slot, info : (x_6).info, value_write : (Bool)'(False),
        value : unpack(0), may_victim : (x_6).may_victim, reps :
        (x_6).reps});
        Struct16 x_19 = (Struct16 {addr : (x_18).addr, info_write :
        (Bool)'(True), info_hit : (x_18).info_hit, info_way :
        (x_18).info_way, edir_hit : (x_18).edir_hit, edir_way :
        (x_18).edir_way, edir_slot : (x_18).edir_slot, info : Struct10
        {mesi_owned : ((x_18).info).mesi_owned, mesi_status :
        ((x_18).info).mesi_status, mesi_dir_st : (Struct15 {dir_st :
        (Bit#(3))'(3'h1), dir_excl : unpack(0), dir_sharers :
        unpack(0)}).dir_st, mesi_dir_sharers : (((Struct15 {dir_st :
        (Bit#(3))'(3'h1), dir_excl : unpack(0), dir_sharers :
        unpack(0)}).dir_st) == ((Bit#(3))'(3'h2)) ? ((Struct15 {dir_st :
        (Bit#(3))'(3'h1), dir_excl : unpack(0), dir_sharers :
        unpack(0)}).dir_sharers) : (((Bit#(4))'(4'h1)) << ((Struct15 {dir_st
        : (Bit#(3))'(3'h1), dir_excl : unpack(0), dir_sharers :
        unpack(0)}).dir_excl)))}, value_write : (x_18).value_write, value :
        (x_18).value, may_victim : (x_18).may_victim, reps :
        (x_18).reps});
        Struct16 x_20 = (Struct16 {addr : (x_19).addr, info_write :
        (Bool)'(True), info_hit : (x_19).info_hit, info_way :
        (x_19).info_way, edir_hit : (x_19).edir_hit, edir_way :
        (x_19).edir_way, edir_slot : (x_19).edir_slot, info : Struct10
        {mesi_owned : ((x_19).info).mesi_owned, mesi_status :
        (Bit#(3))'(3'h3), mesi_dir_st : ((x_19).info).mesi_dir_st,
        mesi_dir_sharers : ((x_19).info).mesi_dir_sharers}, value_write :
        (x_19).value_write, value : (x_19).value, may_victim :
        (x_19).may_victim, reps :
        (x_19).reps});
        let x_23 = ?;
        if ((x_8).valid) begin
            let x_21 <- victims__00__setVictim(Struct17 {victim_idx :
            (x_8).data, victim_info : (x_20).info, victim_value :
            ((x_20).value_write ? ((x_20).value) : (x_9))});
            x_23 = x_9;
        end else begin
            let x_22 <- cache__00__valueRsLineRq(x_20);
            x_23 = x_22;
        end
        Struct18 x_24 = (Struct18 {enq_type : ((((Bit#(4))'(4'ha))[3:2]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : (((((Bit#(4))'(4'ha))[3:2])
        == ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : ((Bit#(4))'(4'ha))[1:0], enq_msg : Struct1 {id :
        (Bit#(6))'(6'h16), type_ : (Bool)'(True), addr : (x_17).addr, value :
        unpack(0)}});
        let x_25 <- makeEnq_parentChildren00(x_24);
        let x_26 <- releaseMSHR_00(x_4);
    endrule

    rule rule_exec_00_28002;
        let x_0 <- deq_fifoL2E_00();
        Struct6 x_1 = ((x_0).lr_ir_pp);
        Bit#(4) x_2 = ((x_1).ir_msg_from);
        Struct1 x_3 = ((x_1).ir_msg);
        Bit#(3) x_4 = ((x_1).ir_mshr_id);
        Bool x_5 = ((x_1).ir_is_rs_rel);
        when (! (x_5), noAction);
        Struct9 x_6 = ((x_0).lr_ir);
        Struct10 x_7 = ((x_6).info);
        Struct5 x_8 = ((x_1).ir_by_victim);
        Vector#(4, Bit#(64)) x_9 = ((x_0).lr_value);
        let x_10 <- getMSHR_00(x_4);
        let x_11 <- getMSHRRq_00(x_4);
        Struct1 x_12 = (unpack(0));
        Vector#(4, Bit#(64)) x_13 = (unpack(0));
        Bool x_14 = ((x_7).mesi_owned);
        Bit#(3) x_15 = ((x_7).mesi_status);
        Struct15 x_16 = (Struct15 {dir_st : (((x_7).mesi_dir_st) ==
        ((Bit#(3))'(3'h0)) ? ((Bit#(3))'(3'h1)) : ((x_7).mesi_dir_st)),
        dir_excl : ((((x_7).mesi_dir_sharers)[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        ((((((x_7).mesi_dir_sharers)[3:1])[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        (((((((x_7).mesi_dir_sharers)[3:1])[2:1])[0:0]) == ((Bit#(1))'(1'h1))
        ? ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        ((((((((x_7).mesi_dir_sharers)[3:1])[2:1])[1:1])[0:0]) ==
        ((Bit#(1))'(1'h1)) ? ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        (unpack(0))))))))))))), dir_sharers : (x_7).mesi_dir_sharers});
        when ((x_2) == ((Bit#(4))'(4'h2)), noAction);
        when (((x_3).id) == ((Bit#(6))'(6'h15)), noAction);
        when (! ((x_3).type_), noAction);
        when ((((((x_16).dir_st) == ((Bit#(3))'(3'h4))) && (((x_16).dir_excl)
        == ((Bit#(2))'(2'h2))) ? ((Bit#(3))'(3'h4)) : (((((x_16).dir_st) ==
        ((Bit#(3))'(3'h3))) && (((x_16).dir_excl) == ((Bit#(2))'(2'h2))) ?
        ((Bit#(3))'(3'h3)) : (((((x_16).dir_st) == ((Bit#(3))'(3'h2))) &&
        ((((x_16).dir_sharers) | (((Bit#(4))'(4'h1)) << ((Bit#(2))'(2'h2))))
        == ((x_16).dir_sharers)) ? ((Bit#(3))'(3'h2)) :
        ((Bit#(3))'(3'h1)))))))) == ((Bit#(3))'(3'h1)), noAction);
        Struct1 x_17 = (x_3);
        Struct16 x_18 = (Struct16 {addr : (x_3).addr, info_write :
        (Bool)'(False), info_hit : (x_6).info_hit, info_way : (x_6).info_way,
        edir_hit : (x_6).edir_hit, edir_way : (x_6).edir_way, edir_slot :
        (x_6).edir_slot, info : (x_6).info, value_write : (Bool)'(False),
        value : unpack(0), may_victim : (x_6).may_victim, reps :
        (x_6).reps});
        let x_20 = ?;
        if ((x_8).valid) begin
            x_20 = x_9;
        end else begin
            let x_19 <- cache__00__valueRsLineRq(unpack(0));
            x_20 = x_19;
        end
        Struct18 x_21 = (Struct18 {enq_type : ((((Bit#(4))'(4'ha))[3:2]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : (((((Bit#(4))'(4'ha))[3:2])
        == ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : ((Bit#(4))'(4'ha))[1:0], enq_msg : Struct1 {id :
        (Bit#(6))'(6'h16), type_ : (Bool)'(True), addr : (x_17).addr, value :
        unpack(0)}});
        let x_22 <- makeEnq_parentChildren00(x_21);
        let x_23 <- releaseMSHR_00(x_4);
    endrule

    rule rule_exec_00_290002;
        let x_0 <- deq_fifoL2E_00();
        Struct6 x_1 = ((x_0).lr_ir_pp);
        Bit#(4) x_2 = ((x_1).ir_msg_from);
        Struct1 x_3 = ((x_1).ir_msg);
        Bit#(3) x_4 = ((x_1).ir_mshr_id);
        Bool x_5 = ((x_1).ir_is_rs_rel);
        when (! (x_5), noAction);
        Struct9 x_6 = ((x_0).lr_ir);
        Struct10 x_7 = ((x_6).info);
        Struct5 x_8 = ((x_1).ir_by_victim);
        Vector#(4, Bit#(64)) x_9 = ((x_0).lr_value);
        let x_10 <- getMSHR_00(x_4);
        let x_11 <- getMSHRRq_00(x_4);
        Struct1 x_12 = (unpack(0));
        Vector#(4, Bit#(64)) x_13 = (unpack(0));
        Bool x_14 = ((x_7).mesi_owned);
        Bit#(3) x_15 = ((x_7).mesi_status);
        Struct15 x_16 = (Struct15 {dir_st : (((x_7).mesi_dir_st) ==
        ((Bit#(3))'(3'h0)) ? ((Bit#(3))'(3'h1)) : ((x_7).mesi_dir_st)),
        dir_excl : ((((x_7).mesi_dir_sharers)[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        ((((((x_7).mesi_dir_sharers)[3:1])[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        (((((((x_7).mesi_dir_sharers)[3:1])[2:1])[0:0]) == ((Bit#(1))'(1'h1))
        ? ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        ((((((((x_7).mesi_dir_sharers)[3:1])[2:1])[1:1])[0:0]) ==
        ((Bit#(1))'(1'h1)) ? ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        (unpack(0))))))))))))), dir_sharers : (x_7).mesi_dir_sharers});
        when ((x_2) == ((Bit#(4))'(4'h2)), noAction);
        when (((x_3).id) == ((Bit#(6))'(6'h15)), noAction);
        when (! ((x_3).type_), noAction);
        when (((x_14) == ((Bool)'(False))) && (((((((x_16).dir_st) ==
        ((Bit#(3))'(3'h4))) && (((x_16).dir_excl) == ((Bit#(2))'(2'h2))) ?
        ((Bit#(3))'(3'h4)) : (((((x_16).dir_st) == ((Bit#(3))'(3'h3))) &&
        (((x_16).dir_excl) == ((Bit#(2))'(2'h2))) ? ((Bit#(3))'(3'h3)) :
        (((((x_16).dir_st) == ((Bit#(3))'(3'h2))) && ((((x_16).dir_sharers) |
        (((Bit#(4))'(4'h1)) << ((Bit#(2))'(2'h2)))) == ((x_16).dir_sharers))
        ? ((Bit#(3))'(3'h2)) : ((Bit#(3))'(3'h1)))))))) ==
        ((Bit#(3))'(3'h2))) && (((x_16).dir_sharers) == (((Bit#(4))'(4'h1))
        << ((Bit#(2))'(2'h2))))), noAction);
        Struct1 x_17 = (x_3);
        Struct16 x_18 = (Struct16 {addr : (x_3).addr, info_write :
        (Bool)'(False), info_hit : (x_6).info_hit, info_way : (x_6).info_way,
        edir_hit : (x_6).edir_hit, edir_way : (x_6).edir_way, edir_slot :
        (x_6).edir_slot, info : (x_6).info, value_write : (Bool)'(False),
        value : unpack(0), may_victim : (x_6).may_victim, reps :
        (x_6).reps});
        Struct16 x_19 = (Struct16 {addr : (x_18).addr, info_write :
        (Bool)'(True), info_hit : (x_18).info_hit, info_way :
        (x_18).info_way, edir_hit : (x_18).edir_hit, edir_way :
        (x_18).edir_way, edir_slot : (x_18).edir_slot, info : Struct10
        {mesi_owned : ((x_18).info).mesi_owned, mesi_status :
        ((x_18).info).mesi_status, mesi_dir_st : (Struct15 {dir_st :
        (Bit#(3))'(3'h1), dir_excl : unpack(0), dir_sharers :
        unpack(0)}).dir_st, mesi_dir_sharers : (((Struct15 {dir_st :
        (Bit#(3))'(3'h1), dir_excl : unpack(0), dir_sharers :
        unpack(0)}).dir_st) == ((Bit#(3))'(3'h2)) ? ((Struct15 {dir_st :
        (Bit#(3))'(3'h1), dir_excl : unpack(0), dir_sharers :
        unpack(0)}).dir_sharers) : (((Bit#(4))'(4'h1)) << ((Struct15 {dir_st
        : (Bit#(3))'(3'h1), dir_excl : unpack(0), dir_sharers :
        unpack(0)}).dir_excl)))}, value_write : (x_18).value_write, value :
        (x_18).value, may_victim : (x_18).may_victim, reps :
        (x_18).reps});
        let x_22 = ?;
        if ((x_8).valid) begin
            let x_20 <- victims__00__setVictim(Struct17 {victim_idx :
            (x_8).data, victim_info : (x_19).info, victim_value :
            ((x_19).value_write ? ((x_19).value) : (x_9))});
            x_22 = x_9;
        end else begin
            let x_21 <- cache__00__valueRsLineRq(x_19);
            x_22 = x_21;
        end
        Struct18 x_23 = (Struct18 {enq_type : ((((Bit#(4))'(4'ha))[3:2]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : (((((Bit#(4))'(4'ha))[3:2])
        == ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : ((Bit#(4))'(4'ha))[1:0], enq_msg : Struct1 {id :
        (Bit#(6))'(6'h16), type_ : (Bool)'(True), addr : (x_17).addr, value :
        unpack(0)}});
        let x_24 <- makeEnq_parentChildren00(x_23);
        let x_25 <- releaseMSHR_00(x_4);
    endrule

    rule rule_exec_00_291002;
        let x_0 <- deq_fifoL2E_00();
        Struct6 x_1 = ((x_0).lr_ir_pp);
        Bit#(4) x_2 = ((x_1).ir_msg_from);
        Struct1 x_3 = ((x_1).ir_msg);
        Bit#(3) x_4 = ((x_1).ir_mshr_id);
        Bool x_5 = ((x_1).ir_is_rs_rel);
        when (! (x_5), noAction);
        Struct9 x_6 = ((x_0).lr_ir);
        Struct10 x_7 = ((x_6).info);
        Struct5 x_8 = ((x_1).ir_by_victim);
        Vector#(4, Bit#(64)) x_9 = ((x_0).lr_value);
        let x_10 <- getMSHR_00(x_4);
        let x_11 <- getMSHRRq_00(x_4);
        Struct1 x_12 = (unpack(0));
        Vector#(4, Bit#(64)) x_13 = (unpack(0));
        Bool x_14 = ((x_7).mesi_owned);
        Bit#(3) x_15 = ((x_7).mesi_status);
        Struct15 x_16 = (Struct15 {dir_st : (((x_7).mesi_dir_st) ==
        ((Bit#(3))'(3'h0)) ? ((Bit#(3))'(3'h1)) : ((x_7).mesi_dir_st)),
        dir_excl : ((((x_7).mesi_dir_sharers)[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        ((((((x_7).mesi_dir_sharers)[3:1])[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        (((((((x_7).mesi_dir_sharers)[3:1])[2:1])[0:0]) == ((Bit#(1))'(1'h1))
        ? ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        ((((((((x_7).mesi_dir_sharers)[3:1])[2:1])[1:1])[0:0]) ==
        ((Bit#(1))'(1'h1)) ? ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        (unpack(0))))))))))))), dir_sharers : (x_7).mesi_dir_sharers});
        when ((x_2) == ((Bit#(4))'(4'h2)), noAction);
        when (((x_3).id) == ((Bit#(6))'(6'h15)), noAction);
        when (! ((x_3).type_), noAction);
        when (((((((x_16).dir_st) == ((Bit#(3))'(3'h4))) &&
        (((x_16).dir_excl) == ((Bit#(2))'(2'h2))) ? ((Bit#(3))'(3'h4)) :
        (((((x_16).dir_st) == ((Bit#(3))'(3'h3))) && (((x_16).dir_excl) ==
        ((Bit#(2))'(2'h2))) ? ((Bit#(3))'(3'h3)) : (((((x_16).dir_st) ==
        ((Bit#(3))'(3'h2))) && ((((x_16).dir_sharers) | (((Bit#(4))'(4'h1))
        << ((Bit#(2))'(2'h2)))) == ((x_16).dir_sharers)) ? ((Bit#(3))'(3'h2))
        : ((Bit#(3))'(3'h1)))))))) == ((Bit#(3))'(3'h2))) &&
        (((Bit#(3))'(3'h1)) < ((((((x_16).dir_sharers)[0:0]) ==
        ((Bit#(1))'(1'h1)) ? ((Bit#(3))'(3'h1)) : ((Bit#(3))'(3'h0)))) +
        (((((((x_16).dir_sharers)[3:1])[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(3))'(3'h1)) : ((Bit#(3))'(3'h0)))) +
        ((((((((x_16).dir_sharers)[3:1])[2:1])[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(3))'(3'h1)) : ((Bit#(3))'(3'h0)))) +
        (((((((((x_16).dir_sharers)[3:1])[2:1])[1:1])[0:0]) ==
        ((Bit#(1))'(1'h1)) ? ((Bit#(3))'(3'h1)) : ((Bit#(3))'(3'h0)))) +
        (unpack(0))))))), noAction);
        Struct1 x_17 = (x_3);
        Struct16 x_18 = (Struct16 {addr : (x_3).addr, info_write :
        (Bool)'(False), info_hit : (x_6).info_hit, info_way : (x_6).info_way,
        edir_hit : (x_6).edir_hit, edir_way : (x_6).edir_way, edir_slot :
        (x_6).edir_slot, info : (x_6).info, value_write : (Bool)'(False),
        value : unpack(0), may_victim : (x_6).may_victim, reps :
        (x_6).reps});
        Struct16 x_19 = (Struct16 {addr : (x_18).addr, info_write :
        (Bool)'(True), info_hit : (x_18).info_hit, info_way :
        (x_18).info_way, edir_hit : (x_18).edir_hit, edir_way :
        (x_18).edir_way, edir_slot : (x_18).edir_slot, info : Struct10
        {mesi_owned : ((x_18).info).mesi_owned, mesi_status :
        ((x_18).info).mesi_status, mesi_dir_st : (Struct15 {dir_st :
        (Bit#(3))'(3'h2), dir_excl : (x_16).dir_excl, dir_sharers :
        ((x_16).dir_sharers) & (~(((Bit#(4))'(4'h1)) <<
        ((Bit#(2))'(2'h2))))}).dir_st, mesi_dir_sharers : (((Struct15 {dir_st
        : (Bit#(3))'(3'h2), dir_excl : (x_16).dir_excl, dir_sharers :
        ((x_16).dir_sharers) & (~(((Bit#(4))'(4'h1)) <<
        ((Bit#(2))'(2'h2))))}).dir_st) == ((Bit#(3))'(3'h2)) ? ((Struct15
        {dir_st : (Bit#(3))'(3'h2), dir_excl : (x_16).dir_excl, dir_sharers :
        ((x_16).dir_sharers) & (~(((Bit#(4))'(4'h1)) <<
        ((Bit#(2))'(2'h2))))}).dir_sharers) : (((Bit#(4))'(4'h1)) <<
        ((Struct15 {dir_st : (Bit#(3))'(3'h2), dir_excl : (x_16).dir_excl,
        dir_sharers : ((x_16).dir_sharers) & (~(((Bit#(4))'(4'h1)) <<
        ((Bit#(2))'(2'h2))))}).dir_excl)))}, value_write :
        (x_18).value_write, value : (x_18).value, may_victim :
        (x_18).may_victim, reps :
        (x_18).reps});
        let x_22 = ?;
        if ((x_8).valid) begin
            let x_20 <- victims__00__setVictim(Struct17 {victim_idx :
            (x_8).data, victim_info : (x_19).info, victim_value :
            ((x_19).value_write ? ((x_19).value) : (x_9))});
            x_22 = x_9;
        end else begin
            let x_21 <- cache__00__valueRsLineRq(x_19);
            x_22 = x_21;
        end
        Struct18 x_23 = (Struct18 {enq_type : ((((Bit#(4))'(4'ha))[3:2]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : (((((Bit#(4))'(4'ha))[3:2])
        == ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : ((Bit#(4))'(4'ha))[1:0], enq_msg : Struct1 {id :
        (Bit#(6))'(6'h16), type_ : (Bool)'(True), addr : (x_17).addr, value :
        unpack(0)}});
        let x_24 <- makeEnq_parentChildren00(x_23);
        let x_25 <- releaseMSHR_00(x_4);
    endrule

    rule rule_exec_00_210002;
        let x_0 <- deq_fifoL2E_00();
        Struct6 x_1 = ((x_0).lr_ir_pp);
        Bit#(4) x_2 = ((x_1).ir_msg_from);
        Struct1 x_3 = ((x_1).ir_msg);
        Bit#(3) x_4 = ((x_1).ir_mshr_id);
        Bool x_5 = ((x_1).ir_is_rs_rel);
        when (! (x_5), noAction);
        Struct9 x_6 = ((x_0).lr_ir);
        Struct10 x_7 = ((x_6).info);
        Struct5 x_8 = ((x_1).ir_by_victim);
        Vector#(4, Bit#(64)) x_9 = ((x_0).lr_value);
        let x_10 <- getMSHR_00(x_4);
        let x_11 <- getMSHRRq_00(x_4);
        Struct1 x_12 = (unpack(0));
        Vector#(4, Bit#(64)) x_13 = (unpack(0));
        Bool x_14 = ((x_7).mesi_owned);
        Bit#(3) x_15 = ((x_7).mesi_status);
        Struct15 x_16 = (Struct15 {dir_st : (((x_7).mesi_dir_st) ==
        ((Bit#(3))'(3'h0)) ? ((Bit#(3))'(3'h1)) : ((x_7).mesi_dir_st)),
        dir_excl : ((((x_7).mesi_dir_sharers)[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        ((((((x_7).mesi_dir_sharers)[3:1])[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        (((((((x_7).mesi_dir_sharers)[3:1])[2:1])[0:0]) == ((Bit#(1))'(1'h1))
        ? ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        ((((((((x_7).mesi_dir_sharers)[3:1])[2:1])[1:1])[0:0]) ==
        ((Bit#(1))'(1'h1)) ? ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        (unpack(0))))))))))))), dir_sharers : (x_7).mesi_dir_sharers});
        when ((x_2) == ((Bit#(4))'(4'h2)), noAction);
        when (((x_3).id) == ((Bit#(6))'(6'h15)), noAction);
        when (! ((x_3).type_), noAction);
        when (((x_14) == ((Bool)'(True))) && (((x_15) == ((Bit#(3))'(3'h2)))
        && (((((((x_16).dir_st) == ((Bit#(3))'(3'h4))) && (((x_16).dir_excl)
        == ((Bit#(2))'(2'h2))) ? ((Bit#(3))'(3'h4)) : (((((x_16).dir_st) ==
        ((Bit#(3))'(3'h3))) && (((x_16).dir_excl) == ((Bit#(2))'(2'h2))) ?
        ((Bit#(3))'(3'h3)) : (((((x_16).dir_st) == ((Bit#(3))'(3'h2))) &&
        ((((x_16).dir_sharers) | (((Bit#(4))'(4'h1)) << ((Bit#(2))'(2'h2))))
        == ((x_16).dir_sharers)) ? ((Bit#(3))'(3'h2)) :
        ((Bit#(3))'(3'h1)))))))) == ((Bit#(3))'(3'h2))) &&
        (((x_16).dir_sharers) == (((Bit#(4))'(4'h1)) <<
        ((Bit#(2))'(2'h2)))))), noAction);
        Struct1 x_17 = (x_3);
        Struct16 x_18 = (Struct16 {addr : (x_3).addr, info_write :
        (Bool)'(False), info_hit : (x_6).info_hit, info_way : (x_6).info_way,
        edir_hit : (x_6).edir_hit, edir_way : (x_6).edir_way, edir_slot :
        (x_6).edir_slot, info : (x_6).info, value_write : (Bool)'(False),
        value : unpack(0), may_victim : (x_6).may_victim, reps :
        (x_6).reps});
        Struct16 x_19 = (Struct16 {addr : (x_18).addr, info_write :
        (Bool)'(True), info_hit : (x_18).info_hit, info_way :
        (x_18).info_way, edir_hit : (x_18).edir_hit, edir_way :
        (x_18).edir_way, edir_slot : (x_18).edir_slot, info : Struct10
        {mesi_owned : ((x_18).info).mesi_owned, mesi_status :
        ((x_18).info).mesi_status, mesi_dir_st : (Struct15 {dir_st :
        (Bit#(3))'(3'h1), dir_excl : unpack(0), dir_sharers :
        unpack(0)}).dir_st, mesi_dir_sharers : (((Struct15 {dir_st :
        (Bit#(3))'(3'h1), dir_excl : unpack(0), dir_sharers :
        unpack(0)}).dir_st) == ((Bit#(3))'(3'h2)) ? ((Struct15 {dir_st :
        (Bit#(3))'(3'h1), dir_excl : unpack(0), dir_sharers :
        unpack(0)}).dir_sharers) : (((Bit#(4))'(4'h1)) << ((Struct15 {dir_st
        : (Bit#(3))'(3'h1), dir_excl : unpack(0), dir_sharers :
        unpack(0)}).dir_excl)))}, value_write : (x_18).value_write, value :
        (x_18).value, may_victim : (x_18).may_victim, reps :
        (x_18).reps});
        Struct16 x_20 = (Struct16 {addr : (x_19).addr, info_write :
        (Bool)'(True), info_hit : (x_19).info_hit, info_way :
        (x_19).info_way, edir_hit : (x_19).edir_hit, edir_way :
        (x_19).edir_way, edir_slot : (x_19).edir_slot, info : Struct10
        {mesi_owned : ((x_19).info).mesi_owned, mesi_status :
        (Bit#(3))'(3'h4), mesi_dir_st : ((x_19).info).mesi_dir_st,
        mesi_dir_sharers : ((x_19).info).mesi_dir_sharers}, value_write :
        (x_19).value_write, value : (x_19).value, may_victim :
        (x_19).may_victim, reps :
        (x_19).reps});
        let x_23 = ?;
        if ((x_8).valid) begin
            let x_21 <- victims__00__setVictim(Struct17 {victim_idx :
            (x_8).data, victim_info : (x_20).info, victim_value :
            ((x_20).value_write ? ((x_20).value) : (x_9))});
            x_23 = x_9;
        end else begin
            let x_22 <- cache__00__valueRsLineRq(x_20);
            x_23 = x_22;
        end
        Struct18 x_24 = (Struct18 {enq_type : ((((Bit#(4))'(4'ha))[3:2]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : (((((Bit#(4))'(4'ha))[3:2])
        == ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : ((Bit#(4))'(4'ha))[1:0], enq_msg : Struct1 {id :
        (Bit#(6))'(6'h16), type_ : (Bool)'(True), addr : (x_17).addr, value :
        unpack(0)}});
        let x_25 <- makeEnq_parentChildren00(x_24);
        let x_26 <- releaseMSHR_00(x_4);
    endrule

    rule rule_exec_00_211002;
        let x_0 <- deq_fifoL2E_00();
        Struct6 x_1 = ((x_0).lr_ir_pp);
        Bit#(4) x_2 = ((x_1).ir_msg_from);
        Struct1 x_3 = ((x_1).ir_msg);
        Bit#(3) x_4 = ((x_1).ir_mshr_id);
        Bool x_5 = ((x_1).ir_is_rs_rel);
        when (! (x_5), noAction);
        Struct9 x_6 = ((x_0).lr_ir);
        Struct10 x_7 = ((x_6).info);
        Struct5 x_8 = ((x_1).ir_by_victim);
        Vector#(4, Bit#(64)) x_9 = ((x_0).lr_value);
        let x_10 <- getMSHR_00(x_4);
        let x_11 <- getMSHRRq_00(x_4);
        Struct1 x_12 = (unpack(0));
        Vector#(4, Bit#(64)) x_13 = (unpack(0));
        Bool x_14 = ((x_7).mesi_owned);
        Bit#(3) x_15 = ((x_7).mesi_status);
        Struct15 x_16 = (Struct15 {dir_st : (((x_7).mesi_dir_st) ==
        ((Bit#(3))'(3'h0)) ? ((Bit#(3))'(3'h1)) : ((x_7).mesi_dir_st)),
        dir_excl : ((((x_7).mesi_dir_sharers)[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        ((((((x_7).mesi_dir_sharers)[3:1])[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        (((((((x_7).mesi_dir_sharers)[3:1])[2:1])[0:0]) == ((Bit#(1))'(1'h1))
        ? ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        ((((((((x_7).mesi_dir_sharers)[3:1])[2:1])[1:1])[0:0]) ==
        ((Bit#(1))'(1'h1)) ? ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        (unpack(0))))))))))))), dir_sharers : (x_7).mesi_dir_sharers});
        when ((x_2) == ((Bit#(4))'(4'h2)), noAction);
        when (((x_3).id) == ((Bit#(6))'(6'h15)), noAction);
        when (! ((x_3).type_), noAction);
        when (! ((((((x_16).dir_st) == ((Bit#(3))'(3'h4))) &&
        (((x_16).dir_excl) == ((Bit#(2))'(2'h2))) ? ((Bit#(3))'(3'h4)) :
        (((((x_16).dir_st) == ((Bit#(3))'(3'h3))) && (((x_16).dir_excl) ==
        ((Bit#(2))'(2'h2))) ? ((Bit#(3))'(3'h3)) : (((((x_16).dir_st) ==
        ((Bit#(3))'(3'h2))) && ((((x_16).dir_sharers) | (((Bit#(4))'(4'h1))
        << ((Bit#(2))'(2'h2)))) == ((x_16).dir_sharers)) ? ((Bit#(3))'(3'h2))
        : ((Bit#(3))'(3'h1)))))))) < ((Bit#(3))'(3'h3))), noAction);
        Struct1 x_17 = (x_3);
        Struct16 x_18 = (Struct16 {addr : (x_3).addr, info_write :
        (Bool)'(False), info_hit : (x_6).info_hit, info_way : (x_6).info_way,
        edir_hit : (x_6).edir_hit, edir_way : (x_6).edir_way, edir_slot :
        (x_6).edir_slot, info : (x_6).info, value_write : (Bool)'(False),
        value : unpack(0), may_victim : (x_6).may_victim, reps :
        (x_6).reps});
        Struct16 x_19 = (Struct16 {addr : (x_18).addr, info_write :
        (x_18).info_write, info_hit : (x_18).info_hit, info_way :
        (x_18).info_way, edir_hit : (x_18).edir_hit, edir_way :
        (x_18).edir_way, edir_slot : (x_18).edir_slot, info : (x_18).info,
        value_write : (Bool)'(True), value : (x_17).value, may_victim :
        (x_18).may_victim, reps : (x_18).reps});
        Struct16 x_20 = (Struct16 {addr : (x_19).addr, info_write :
        (Bool)'(True), info_hit : (x_19).info_hit, info_way :
        (x_19).info_way, edir_hit : (x_19).edir_hit, edir_way :
        (x_19).edir_way, edir_slot : (x_19).edir_slot, info : Struct10
        {mesi_owned : ((x_19).info).mesi_owned, mesi_status :
        (Bit#(3))'(3'h4), mesi_dir_st : ((x_19).info).mesi_dir_st,
        mesi_dir_sharers : ((x_19).info).mesi_dir_sharers}, value_write :
        (x_19).value_write, value : (x_19).value, may_victim :
        (x_19).may_victim, reps : (x_19).reps});
        Struct16 x_21 = (Struct16 {addr : (x_20).addr, info_write :
        (Bool)'(True), info_hit : (x_20).info_hit, info_way :
        (x_20).info_way, edir_hit : (x_20).edir_hit, edir_way :
        (x_20).edir_way, edir_slot : (x_20).edir_slot, info : Struct10
        {mesi_owned : (Bool)'(True), mesi_status : ((x_20).info).mesi_status,
        mesi_dir_st : ((x_20).info).mesi_dir_st, mesi_dir_sharers :
        ((x_20).info).mesi_dir_sharers}, value_write : (x_20).value_write,
        value : (x_20).value, may_victim : (x_20).may_victim, reps :
        (x_20).reps});
        Struct16 x_22 = (Struct16 {addr : (x_21).addr, info_write :
        (Bool)'(True), info_hit : (x_21).info_hit, info_way :
        (x_21).info_way, edir_hit : (x_21).edir_hit, edir_way :
        (x_21).edir_way, edir_slot : (x_21).edir_slot, info : Struct10
        {mesi_owned : ((x_21).info).mesi_owned, mesi_status :
        ((x_21).info).mesi_status, mesi_dir_st : (Struct15 {dir_st :
        (Bit#(3))'(3'h1), dir_excl : unpack(0), dir_sharers :
        unpack(0)}).dir_st, mesi_dir_sharers : (((Struct15 {dir_st :
        (Bit#(3))'(3'h1), dir_excl : unpack(0), dir_sharers :
        unpack(0)}).dir_st) == ((Bit#(3))'(3'h2)) ? ((Struct15 {dir_st :
        (Bit#(3))'(3'h1), dir_excl : unpack(0), dir_sharers :
        unpack(0)}).dir_sharers) : (((Bit#(4))'(4'h1)) << ((Struct15 {dir_st
        : (Bit#(3))'(3'h1), dir_excl : unpack(0), dir_sharers :
        unpack(0)}).dir_excl)))}, value_write : (x_21).value_write, value :
        (x_21).value, may_victim : (x_21).may_victim, reps :
        (x_21).reps});
        let x_25 = ?;
        if ((x_8).valid) begin
            let x_23 <- victims__00__setVictim(Struct17 {victim_idx :
            (x_8).data, victim_info : (x_22).info, victim_value :
            ((x_22).value_write ? ((x_22).value) : (x_9))});
            x_25 = x_9;
        end else begin
            let x_24 <- cache__00__valueRsLineRq(x_22);
            x_25 = x_24;
        end
        Struct18 x_26 = (Struct18 {enq_type : ((((Bit#(4))'(4'ha))[3:2]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : (((((Bit#(4))'(4'ha))[3:2])
        == ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : ((Bit#(4))'(4'ha))[1:0], enq_msg : Struct1 {id :
        (Bit#(6))'(6'h16), type_ : (Bool)'(True), addr : (x_17).addr, value :
        unpack(0)}});
        let x_27 <- makeEnq_parentChildren00(x_26);
        let x_28 <- releaseMSHR_00(x_4);
    endrule

    rule rule_exec_00_000003;
        let x_0 <- deq_fifoL2E_00();
        Struct6 x_1 = ((x_0).lr_ir_pp);
        Bit#(4) x_2 = ((x_1).ir_msg_from);
        Struct1 x_3 = ((x_1).ir_msg);
        Bit#(3) x_4 = ((x_1).ir_mshr_id);
        Bool x_5 = ((x_1).ir_is_rs_rel);
        when (! (x_5), noAction);
        Struct9 x_6 = ((x_0).lr_ir);
        Struct10 x_7 = ((x_6).info);
        Struct5 x_8 = ((x_1).ir_by_victim);
        Vector#(4, Bit#(64)) x_9 = ((x_0).lr_value);
        let x_10 <- getMSHR_00(x_4);
        let x_11 <- getMSHRRq_00(x_4);
        Struct1 x_12 = (unpack(0));
        Vector#(4, Bit#(64)) x_13 = (unpack(0));
        Bool x_14 = ((x_7).mesi_owned);
        Bit#(3) x_15 = ((x_7).mesi_status);
        Struct15 x_16 = (Struct15 {dir_st : (((x_7).mesi_dir_st) ==
        ((Bit#(3))'(3'h0)) ? ((Bit#(3))'(3'h1)) : ((x_7).mesi_dir_st)),
        dir_excl : ((((x_7).mesi_dir_sharers)[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        ((((((x_7).mesi_dir_sharers)[3:1])[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        (((((((x_7).mesi_dir_sharers)[3:1])[2:1])[0:0]) == ((Bit#(1))'(1'h1))
        ? ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        ((((((((x_7).mesi_dir_sharers)[3:1])[2:1])[1:1])[0:0]) ==
        ((Bit#(1))'(1'h1)) ? ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        (unpack(0))))))))))))), dir_sharers : (x_7).mesi_dir_sharers});
        when ((x_2) == ((Bit#(4))'(4'h3)), noAction);
        when (((x_3).id) == ((Bit#(6))'(6'h2)), noAction);
        when (! ((x_3).type_), noAction);
        when ((! (((Bit#(3))'(3'h2)) < ((x_16).dir_st))) && ((x_15) ==
        ((Bit#(3))'(3'h2))), noAction);
        Struct1 x_17 = (x_3);
        Struct16 x_18 = (Struct16 {addr : (x_3).addr, info_write :
        (Bool)'(False), info_hit : (x_6).info_hit, info_way : (x_6).info_way,
        edir_hit : (x_6).edir_hit, edir_way : (x_6).edir_way, edir_slot :
        (x_6).edir_slot, info : (x_6).info, value_write : (Bool)'(False),
        value : unpack(0), may_victim : (x_6).may_victim, reps :
        (x_6).reps});
        Struct16 x_19 = (Struct16 {addr : (x_18).addr, info_write :
        (Bool)'(True), info_hit : (x_18).info_hit, info_way :
        (x_18).info_way, edir_hit : (x_18).edir_hit, edir_way :
        (x_18).edir_way, edir_slot : (x_18).edir_slot, info : Struct10
        {mesi_owned : ((x_18).info).mesi_owned, mesi_status :
        ((x_18).info).mesi_status, mesi_dir_st : (Struct15 {dir_st :
        (Bit#(3))'(3'h2), dir_excl : (x_16).dir_excl, dir_sharers :
        (((x_16).dir_st) == ((Bit#(3))'(3'h2)) ? (((x_16).dir_sharers) |
        (((Bit#(4))'(4'h1)) << ((Bit#(2))'(2'h3)))) : (((Bit#(4))'(4'h1)) <<
        ((Bit#(2))'(2'h3))))}).dir_st, mesi_dir_sharers : (((Struct15 {dir_st
        : (Bit#(3))'(3'h2), dir_excl : (x_16).dir_excl, dir_sharers :
        (((x_16).dir_st) == ((Bit#(3))'(3'h2)) ? (((x_16).dir_sharers) |
        (((Bit#(4))'(4'h1)) << ((Bit#(2))'(2'h3)))) : (((Bit#(4))'(4'h1)) <<
        ((Bit#(2))'(2'h3))))}).dir_st) == ((Bit#(3))'(3'h2)) ? ((Struct15
        {dir_st : (Bit#(3))'(3'h2), dir_excl : (x_16).dir_excl, dir_sharers :
        (((x_16).dir_st) == ((Bit#(3))'(3'h2)) ? (((x_16).dir_sharers) |
        (((Bit#(4))'(4'h1)) << ((Bit#(2))'(2'h3)))) : (((Bit#(4))'(4'h1)) <<
        ((Bit#(2))'(2'h3))))}).dir_sharers) : (((Bit#(4))'(4'h1)) <<
        ((Struct15 {dir_st : (Bit#(3))'(3'h2), dir_excl : (x_16).dir_excl,
        dir_sharers : (((x_16).dir_st) == ((Bit#(3))'(3'h2)) ?
        (((x_16).dir_sharers) | (((Bit#(4))'(4'h1)) << ((Bit#(2))'(2'h3)))) :
        (((Bit#(4))'(4'h1)) << ((Bit#(2))'(2'h3))))}).dir_excl)))},
        value_write : (x_18).value_write, value : (x_18).value, may_victim :
        (x_18).may_victim, reps :
        (x_18).reps});
        let x_22 = ?;
        if ((x_8).valid) begin
            let x_20 <- victims__00__setVictim(Struct17 {victim_idx :
            (x_8).data, victim_info : (x_19).info, victim_value :
            ((x_19).value_write ? ((x_19).value) : (x_9))});
            x_22 = x_9;
        end else begin
            let x_21 <- cache__00__valueRsLineRq(x_19);
            x_22 = x_21;
        end
        Struct18 x_23 = (Struct18 {enq_type : ((((Bit#(4))'(4'hb))[3:2]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : (((((Bit#(4))'(4'hb))[3:2])
        == ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : ((Bit#(4))'(4'hb))[1:0], enq_msg : Struct1 {id :
        (Bit#(6))'(6'h3), type_ : (Bool)'(True), addr : (x_17).addr, value :
        x_22}});
        let x_24 <- makeEnq_parentChildren00(x_23);
        let x_25 <- releaseMSHR_00(x_4);
    endrule

    rule rule_exec_00_001003;
        let x_0 <- deq_fifoL2E_00();
        Struct6 x_1 = ((x_0).lr_ir_pp);
        Bit#(4) x_2 = ((x_1).ir_msg_from);
        Struct1 x_3 = ((x_1).ir_msg);
        Bit#(3) x_4 = ((x_1).ir_mshr_id);
        Bool x_5 = ((x_1).ir_is_rs_rel);
        when (! (x_5), noAction);
        Struct9 x_6 = ((x_0).lr_ir);
        Struct10 x_7 = ((x_6).info);
        Struct5 x_8 = ((x_1).ir_by_victim);
        Vector#(4, Bit#(64)) x_9 = ((x_0).lr_value);
        let x_10 <- getMSHR_00(x_4);
        let x_11 <- getMSHRRq_00(x_4);
        Struct1 x_12 = (unpack(0));
        Vector#(4, Bit#(64)) x_13 = (unpack(0));
        Bool x_14 = ((x_7).mesi_owned);
        Bit#(3) x_15 = ((x_7).mesi_status);
        Struct15 x_16 = (Struct15 {dir_st : (((x_7).mesi_dir_st) ==
        ((Bit#(3))'(3'h0)) ? ((Bit#(3))'(3'h1)) : ((x_7).mesi_dir_st)),
        dir_excl : ((((x_7).mesi_dir_sharers)[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        ((((((x_7).mesi_dir_sharers)[3:1])[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        (((((((x_7).mesi_dir_sharers)[3:1])[2:1])[0:0]) == ((Bit#(1))'(1'h1))
        ? ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        ((((((((x_7).mesi_dir_sharers)[3:1])[2:1])[1:1])[0:0]) ==
        ((Bit#(1))'(1'h1)) ? ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        (unpack(0))))))))))))), dir_sharers : (x_7).mesi_dir_sharers});
        when ((x_2) == ((Bit#(4))'(4'h3)), noAction);
        when (((x_3).id) == ((Bit#(6))'(6'h2)), noAction);
        when (! ((x_3).type_), noAction);
        when ((! ((x_15) < ((Bit#(3))'(3'h3)))) && (((x_16).dir_st) ==
        ((Bit#(3))'(3'h1))), noAction);
        Struct1 x_17 = (x_3);
        Struct16 x_18 = (Struct16 {addr : (x_3).addr, info_write :
        (Bool)'(False), info_hit : (x_6).info_hit, info_way : (x_6).info_way,
        edir_hit : (x_6).edir_hit, edir_way : (x_6).edir_way, edir_slot :
        (x_6).edir_slot, info : (x_6).info, value_write : (Bool)'(False),
        value : unpack(0), may_victim : (x_6).may_victim, reps :
        (x_6).reps});
        Struct16 x_19 = (Struct16 {addr : (x_18).addr, info_write :
        (Bool)'(True), info_hit : (x_18).info_hit, info_way :
        (x_18).info_way, edir_hit : (x_18).edir_hit, edir_way :
        (x_18).edir_way, edir_slot : (x_18).edir_slot, info : Struct10
        {mesi_owned : ((x_18).info).mesi_owned, mesi_status :
        ((x_18).info).mesi_status, mesi_dir_st : (Struct15 {dir_st :
        (Bit#(3))'(3'h3), dir_excl : (Bit#(2))'(2'h3), dir_sharers :
        unpack(0)}).dir_st, mesi_dir_sharers : (((Struct15 {dir_st :
        (Bit#(3))'(3'h3), dir_excl : (Bit#(2))'(2'h3), dir_sharers :
        unpack(0)}).dir_st) == ((Bit#(3))'(3'h2)) ? ((Struct15 {dir_st :
        (Bit#(3))'(3'h3), dir_excl : (Bit#(2))'(2'h3), dir_sharers :
        unpack(0)}).dir_sharers) : (((Bit#(4))'(4'h1)) << ((Struct15 {dir_st
        : (Bit#(3))'(3'h3), dir_excl : (Bit#(2))'(2'h3), dir_sharers :
        unpack(0)}).dir_excl)))}, value_write : (x_18).value_write, value :
        (x_18).value, may_victim : (x_18).may_victim, reps :
        (x_18).reps});
        Struct16 x_20 = (Struct16 {addr : (x_19).addr, info_write :
        (Bool)'(True), info_hit : (x_19).info_hit, info_way :
        (x_19).info_way, edir_hit : (x_19).edir_hit, edir_way :
        (x_19).edir_way, edir_slot : (x_19).edir_slot, info : Struct10
        {mesi_owned : ((x_19).info).mesi_owned, mesi_status :
        (Bit#(3))'(3'h1), mesi_dir_st : ((x_19).info).mesi_dir_st,
        mesi_dir_sharers : ((x_19).info).mesi_dir_sharers}, value_write :
        (x_19).value_write, value : (x_19).value, may_victim :
        (x_19).may_victim, reps :
        (x_19).reps});
        let x_23 = ?;
        if ((x_8).valid) begin
            let x_21 <- victims__00__setVictim(Struct17 {victim_idx :
            (x_8).data, victim_info : (x_20).info, victim_value :
            ((x_20).value_write ? ((x_20).value) : (x_9))});
            x_23 = x_9;
        end else begin
            let x_22 <- cache__00__valueRsLineRq(x_20);
            x_23 = x_22;
        end
        Struct18 x_24 = (Struct18 {enq_type : ((((Bit#(4))'(4'hb))[3:2]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : (((((Bit#(4))'(4'hb))[3:2])
        == ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : ((Bit#(4))'(4'hb))[1:0], enq_msg : Struct1 {id :
        (Bit#(6))'(6'h4), type_ : (Bool)'(True), addr : (x_17).addr, value :
        x_23}});
        let x_25 <- makeEnq_parentChildren00(x_24);
        let x_26 <- releaseMSHR_00(x_4);
    endrule

    rule rule_exec_00_01003;
        let x_0 <- deq_fifoL2E_00();
        Struct6 x_1 = ((x_0).lr_ir_pp);
        Bit#(4) x_2 = ((x_1).ir_msg_from);
        Struct1 x_3 = ((x_1).ir_msg);
        Bit#(3) x_4 = ((x_1).ir_mshr_id);
        Bool x_5 = ((x_1).ir_is_rs_rel);
        when (! (x_5), noAction);
        Struct9 x_6 = ((x_0).lr_ir);
        Struct10 x_7 = ((x_6).info);
        Struct5 x_8 = ((x_1).ir_by_victim);
        Vector#(4, Bit#(64)) x_9 = ((x_0).lr_value);
        let x_10 <- getMSHR_00(x_4);
        let x_11 <- getMSHRRq_00(x_4);
        Struct1 x_12 = (unpack(0));
        Vector#(4, Bit#(64)) x_13 = (unpack(0));
        Bool x_14 = ((x_7).mesi_owned);
        Bit#(3) x_15 = ((x_7).mesi_status);
        Struct15 x_16 = (Struct15 {dir_st : (((x_7).mesi_dir_st) ==
        ((Bit#(3))'(3'h0)) ? ((Bit#(3))'(3'h1)) : ((x_7).mesi_dir_st)),
        dir_excl : ((((x_7).mesi_dir_sharers)[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        ((((((x_7).mesi_dir_sharers)[3:1])[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        (((((((x_7).mesi_dir_sharers)[3:1])[2:1])[0:0]) == ((Bit#(1))'(1'h1))
        ? ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        ((((((((x_7).mesi_dir_sharers)[3:1])[2:1])[1:1])[0:0]) ==
        ((Bit#(1))'(1'h1)) ? ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        (unpack(0))))))))))))), dir_sharers : (x_7).mesi_dir_sharers});
        when ((x_2) == ((Bit#(4))'(4'h3)), noAction);
        when (((x_3).id) == ((Bit#(6))'(6'h2)), noAction);
        when (! ((x_3).type_), noAction);
        when (((x_14) == ((Bool)'(False))) && ((! (((Bit#(3))'(3'h1)) <
        (x_15))) && (! (((Bit#(3))'(3'h2)) < ((x_16).dir_st)))),
        noAction);
        Struct1 x_17 = (x_3);
        Struct16 x_18 = (Struct16 {addr : (x_3).addr, info_write :
        (Bool)'(False), info_hit : (x_6).info_hit, info_way : (x_6).info_way,
        edir_hit : (x_6).edir_hit, edir_way : (x_6).edir_way, edir_slot :
        (x_6).edir_slot, info : (x_6).info, value_write : (Bool)'(False),
        value : unpack(0), may_victim : (x_6).may_victim, reps :
        (x_6).reps});
        let x_20 = ?;
        if ((x_8).valid) begin
            x_20 = x_9;
        end else begin
            let x_19 <- cache__00__valueRsLineRq(unpack(0));
            x_20 = x_19;
        end
        let x_21 <- registerUL_00(Struct19 {r_id : x_4, r_ul_rsb :
        (Bool)'(True), r_ul_rsbTo : ((Bit#(4))'(4'hb))[1:0]});
        Struct18 x_22 = (Struct18 {enq_type : ((((Bit#(4))'(4'h0))[3:2]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : (((((Bit#(4))'(4'h0))[3:2])
        == ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : ((Bit#(4))'(4'h0))[1:0], enq_msg : Struct1 {id :
        (Bit#(6))'(6'h2), type_ : (Bool)'(False), addr : (x_17).addr, value :
        unpack(0)}});
        let x_23 <- makeEnq_parentChildren00(x_22);
    endrule

    rule rule_exec_00_03003;
        let x_0 <- deq_fifoL2E_00();
        Struct6 x_1 = ((x_0).lr_ir_pp);
        Bit#(4) x_2 = ((x_1).ir_msg_from);
        Struct1 x_3 = ((x_1).ir_msg);
        Bit#(3) x_4 = ((x_1).ir_mshr_id);
        Bool x_5 = ((x_1).ir_is_rs_rel);
        when (! (x_5), noAction);
        Struct9 x_6 = ((x_0).lr_ir);
        Struct10 x_7 = ((x_6).info);
        Struct5 x_8 = ((x_1).ir_by_victim);
        Vector#(4, Bit#(64)) x_9 = ((x_0).lr_value);
        let x_10 <- getMSHR_00(x_4);
        let x_11 <- getMSHRRq_00(x_4);
        Struct1 x_12 = (unpack(0));
        Vector#(4, Bit#(64)) x_13 = (unpack(0));
        Bool x_14 = ((x_7).mesi_owned);
        Bit#(3) x_15 = ((x_7).mesi_status);
        Struct15 x_16 = (Struct15 {dir_st : (((x_7).mesi_dir_st) ==
        ((Bit#(3))'(3'h0)) ? ((Bit#(3))'(3'h1)) : ((x_7).mesi_dir_st)),
        dir_excl : ((((x_7).mesi_dir_sharers)[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        ((((((x_7).mesi_dir_sharers)[3:1])[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        (((((((x_7).mesi_dir_sharers)[3:1])[2:1])[0:0]) == ((Bit#(1))'(1'h1))
        ? ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        ((((((((x_7).mesi_dir_sharers)[3:1])[2:1])[1:1])[0:0]) ==
        ((Bit#(1))'(1'h1)) ? ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        (unpack(0))))))))))))), dir_sharers : (x_7).mesi_dir_sharers});
        when ((x_2) == ((Bit#(4))'(4'h3)), noAction);
        when (((x_3).id) == ((Bit#(6))'(6'h2)), noAction);
        when (! ((x_3).type_), noAction);
        when (((Bool)'(True)) && (((Bool)'(True)) && ((! (((Bit#(3))'(3'h1))
        < (x_15))) && ((! (((x_16).dir_st) < ((Bit#(3))'(3'h3)))) && (!
        (((Bit#(3))'(3'h4)) < ((x_16).dir_st)))))), noAction);
        Struct1 x_17 = (x_3);
        Struct16 x_18 = (Struct16 {addr : (x_3).addr, info_write :
        (Bool)'(False), info_hit : (x_6).info_hit, info_way : (x_6).info_way,
        edir_hit : (x_6).edir_hit, edir_way : (x_6).edir_way, edir_slot :
        (x_6).edir_slot, info : (x_6).info, value_write : (Bool)'(False),
        value : unpack(0), may_victim : (x_6).may_victim, reps :
        (x_6).reps});
        let x_20 = ?;
        if ((x_8).valid) begin
            x_20 = x_9;
        end else begin
            let x_19 <- cache__00__valueRsLineRq(unpack(0));
            x_20 = x_19;
        end
        let x_21 <- registerDL_00(Struct20 {r_id : x_4, r_dl_rss_from :
        (unpack(0)) | (((Bit#(4))'(4'h1)) <<
        (({((Bit#(2))'(2'h1)),((x_16).dir_excl)})[1:0])), r_dl_rsb :
        (Bool)'(True), r_dl_rsbTo : (Bit#(4))'(4'hb)});
        Struct18 x_22 = (Struct18 {enq_type :
        ((({((Bit#(2))'(2'h2)),((x_16).dir_excl)})[3:2]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) :
        (((({((Bit#(2))'(2'h2)),((x_16).dir_excl)})[3:2]) ==
        ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : ({((Bit#(2))'(2'h2)),((x_16).dir_excl)})[1:0], enq_msg :
        Struct1 {id : (Bit#(6))'(6'h5), type_ : (Bool)'(False), addr :
        (x_17).addr, value : unpack(0)}});
        let x_23 <- makeEnq_parentChildren00(x_22);
    endrule

    rule rule_exec_00_10003;
        let x_0 <- deq_fifoL2E_00();
        Struct6 x_1 = ((x_0).lr_ir_pp);
        Bit#(4) x_2 = ((x_1).ir_msg_from);
        Struct1 x_3 = ((x_1).ir_msg);
        Bit#(3) x_4 = ((x_1).ir_mshr_id);
        Bool x_5 = ((x_1).ir_is_rs_rel);
        when (! (x_5), noAction);
        Struct9 x_6 = ((x_0).lr_ir);
        Struct10 x_7 = ((x_6).info);
        Struct5 x_8 = ((x_1).ir_by_victim);
        Vector#(4, Bit#(64)) x_9 = ((x_0).lr_value);
        let x_10 <- getMSHR_00(x_4);
        let x_11 <- getMSHRRq_00(x_4);
        Struct1 x_12 = (unpack(0));
        Vector#(4, Bit#(64)) x_13 = (unpack(0));
        Bool x_14 = ((x_7).mesi_owned);
        Bit#(3) x_15 = ((x_7).mesi_status);
        Struct15 x_16 = (Struct15 {dir_st : (((x_7).mesi_dir_st) ==
        ((Bit#(3))'(3'h0)) ? ((Bit#(3))'(3'h1)) : ((x_7).mesi_dir_st)),
        dir_excl : ((((x_7).mesi_dir_sharers)[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        ((((((x_7).mesi_dir_sharers)[3:1])[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        (((((((x_7).mesi_dir_sharers)[3:1])[2:1])[0:0]) == ((Bit#(1))'(1'h1))
        ? ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        ((((((((x_7).mesi_dir_sharers)[3:1])[2:1])[1:1])[0:0]) ==
        ((Bit#(1))'(1'h1)) ? ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        (unpack(0))))))))))))), dir_sharers : (x_7).mesi_dir_sharers});
        when ((x_2) == ((Bit#(4))'(4'h3)), noAction);
        when (((x_3).id) == ((Bit#(6))'(6'ha)), noAction);
        when (! ((x_3).type_), noAction);
        when ((! ((x_15) < ((Bit#(3))'(3'h3)))) || (((x_15) ==
        ((Bit#(3))'(3'h2))) && (((x_14) == ((Bool)'(True))) &&
        ((((x_16).dir_st) == ((Bit#(3))'(3'h2))) && (((x_16).dir_sharers) ==
        (((Bit#(4))'(4'h1)) << ((Bit#(2))'(2'h3))))))), noAction);
        Struct1 x_17 = (x_3);
        Struct16 x_18 = (Struct16 {addr : (x_3).addr, info_write :
        (Bool)'(False), info_hit : (x_6).info_hit, info_way : (x_6).info_way,
        edir_hit : (x_6).edir_hit, edir_way : (x_6).edir_way, edir_slot :
        (x_6).edir_slot, info : (x_6).info, value_write : (Bool)'(False),
        value : unpack(0), may_victim : (x_6).may_victim, reps :
        (x_6).reps});
        Struct16 x_19 = (Struct16 {addr : (x_18).addr, info_write :
        (Bool)'(True), info_hit : (x_18).info_hit, info_way :
        (x_18).info_way, edir_hit : (x_18).edir_hit, edir_way :
        (x_18).edir_way, edir_slot : (x_18).edir_slot, info : Struct10
        {mesi_owned : ((x_18).info).mesi_owned, mesi_status :
        ((x_18).info).mesi_status, mesi_dir_st : (Struct15 {dir_st :
        (Bit#(3))'(3'h4), dir_excl : (Bit#(2))'(2'h3), dir_sharers :
        unpack(0)}).dir_st, mesi_dir_sharers : (((Struct15 {dir_st :
        (Bit#(3))'(3'h4), dir_excl : (Bit#(2))'(2'h3), dir_sharers :
        unpack(0)}).dir_st) == ((Bit#(3))'(3'h2)) ? ((Struct15 {dir_st :
        (Bit#(3))'(3'h4), dir_excl : (Bit#(2))'(2'h3), dir_sharers :
        unpack(0)}).dir_sharers) : (((Bit#(4))'(4'h1)) << ((Struct15 {dir_st
        : (Bit#(3))'(3'h4), dir_excl : (Bit#(2))'(2'h3), dir_sharers :
        unpack(0)}).dir_excl)))}, value_write : (x_18).value_write, value :
        (x_18).value, may_victim : (x_18).may_victim, reps :
        (x_18).reps});
        Struct16 x_20 = (Struct16 {addr : (x_19).addr, info_write :
        (Bool)'(True), info_hit : (x_19).info_hit, info_way :
        (x_19).info_way, edir_hit : (x_19).edir_hit, edir_way :
        (x_19).edir_way, edir_slot : (x_19).edir_slot, info : Struct10
        {mesi_owned : ((x_19).info).mesi_owned, mesi_status :
        (Bit#(3))'(3'h1), mesi_dir_st : ((x_19).info).mesi_dir_st,
        mesi_dir_sharers : ((x_19).info).mesi_dir_sharers}, value_write :
        (x_19).value_write, value : (x_19).value, may_victim :
        (x_19).may_victim, reps : (x_19).reps});
        Struct16 x_21 = (Struct16 {addr : (x_20).addr, info_write :
        (Bool)'(True), info_hit : (x_20).info_hit, info_way :
        (x_20).info_way, edir_hit : (x_20).edir_hit, edir_way :
        (x_20).edir_way, edir_slot : (x_20).edir_slot, info : Struct10
        {mesi_owned : (Bool)'(False), mesi_status :
        ((x_20).info).mesi_status, mesi_dir_st : ((x_20).info).mesi_dir_st,
        mesi_dir_sharers : ((x_20).info).mesi_dir_sharers}, value_write :
        (x_20).value_write, value : (x_20).value, may_victim :
        (x_20).may_victim, reps :
        (x_20).reps});
        let x_24 = ?;
        if ((x_8).valid) begin
            let x_22 <- victims__00__setVictim(Struct17 {victim_idx :
            (x_8).data, victim_info : (x_21).info, victim_value :
            ((x_21).value_write ? ((x_21).value) : (x_9))});
            x_24 = x_9;
        end else begin
            let x_23 <- cache__00__valueRsLineRq(x_21);
            x_24 = x_23;
        end
        Struct18 x_25 = (Struct18 {enq_type : ((((Bit#(4))'(4'hb))[3:2]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : (((((Bit#(4))'(4'hb))[3:2])
        == ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : ((Bit#(4))'(4'hb))[1:0], enq_msg : Struct1 {id :
        (Bit#(6))'(6'hb), type_ : (Bool)'(True), addr : (x_17).addr, value :
        unpack(0)}});
        let x_26 <- makeEnq_parentChildren00(x_25);
        let x_27 <- releaseMSHR_00(x_4);
    endrule

    rule rule_exec_00_11003;
        let x_0 <- deq_fifoL2E_00();
        Struct6 x_1 = ((x_0).lr_ir_pp);
        Bit#(4) x_2 = ((x_1).ir_msg_from);
        Struct1 x_3 = ((x_1).ir_msg);
        Bit#(3) x_4 = ((x_1).ir_mshr_id);
        Bool x_5 = ((x_1).ir_is_rs_rel);
        when (! (x_5), noAction);
        Struct9 x_6 = ((x_0).lr_ir);
        Struct10 x_7 = ((x_6).info);
        Struct5 x_8 = ((x_1).ir_by_victim);
        Vector#(4, Bit#(64)) x_9 = ((x_0).lr_value);
        let x_10 <- getMSHR_00(x_4);
        let x_11 <- getMSHRRq_00(x_4);
        Struct1 x_12 = (unpack(0));
        Vector#(4, Bit#(64)) x_13 = (unpack(0));
        Bool x_14 = ((x_7).mesi_owned);
        Bit#(3) x_15 = ((x_7).mesi_status);
        Struct15 x_16 = (Struct15 {dir_st : (((x_7).mesi_dir_st) ==
        ((Bit#(3))'(3'h0)) ? ((Bit#(3))'(3'h1)) : ((x_7).mesi_dir_st)),
        dir_excl : ((((x_7).mesi_dir_sharers)[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        ((((((x_7).mesi_dir_sharers)[3:1])[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        (((((((x_7).mesi_dir_sharers)[3:1])[2:1])[0:0]) == ((Bit#(1))'(1'h1))
        ? ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        ((((((((x_7).mesi_dir_sharers)[3:1])[2:1])[1:1])[0:0]) ==
        ((Bit#(1))'(1'h1)) ? ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        (unpack(0))))))))))))), dir_sharers : (x_7).mesi_dir_sharers});
        when ((x_2) == ((Bit#(4))'(4'h3)), noAction);
        when (((x_3).id) == ((Bit#(6))'(6'ha)), noAction);
        when (! ((x_3).type_), noAction);
        when (((x_14) == ((Bool)'(False))) && ((! (((Bit#(3))'(3'h2)) <
        (x_15))) && (! (((Bit#(3))'(3'h2)) < ((x_16).dir_st)))),
        noAction);
        Struct1 x_17 = (x_3);
        Struct16 x_18 = (Struct16 {addr : (x_3).addr, info_write :
        (Bool)'(False), info_hit : (x_6).info_hit, info_way : (x_6).info_way,
        edir_hit : (x_6).edir_hit, edir_way : (x_6).edir_way, edir_slot :
        (x_6).edir_slot, info : (x_6).info, value_write : (Bool)'(False),
        value : unpack(0), may_victim : (x_6).may_victim, reps :
        (x_6).reps});
        let x_20 = ?;
        if ((x_8).valid) begin
            x_20 = x_9;
        end else begin
            let x_19 <- cache__00__valueRsLineRq(unpack(0));
            x_20 = x_19;
        end
        let x_21 <- registerUL_00(Struct19 {r_id : x_4, r_ul_rsb :
        (Bool)'(True), r_ul_rsbTo : ((Bit#(4))'(4'hb))[1:0]});
        Struct18 x_22 = (Struct18 {enq_type : ((((Bit#(4))'(4'h0))[3:2]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : (((((Bit#(4))'(4'h0))[3:2])
        == ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : ((Bit#(4))'(4'h0))[1:0], enq_msg : Struct1 {id :
        (Bit#(6))'(6'ha), type_ : (Bool)'(False), addr : (x_17).addr, value :
        unpack(0)}});
        let x_23 <- makeEnq_parentChildren00(x_22);
    endrule

    rule rule_exec_00_14003;
        let x_0 <- deq_fifoL2E_00();
        Struct6 x_1 = ((x_0).lr_ir_pp);
        Bit#(4) x_2 = ((x_1).ir_msg_from);
        Struct1 x_3 = ((x_1).ir_msg);
        Bit#(3) x_4 = ((x_1).ir_mshr_id);
        Bool x_5 = ((x_1).ir_is_rs_rel);
        when (! (x_5), noAction);
        Struct9 x_6 = ((x_0).lr_ir);
        Struct10 x_7 = ((x_6).info);
        Struct5 x_8 = ((x_1).ir_by_victim);
        Vector#(4, Bit#(64)) x_9 = ((x_0).lr_value);
        let x_10 <- getMSHR_00(x_4);
        let x_11 <- getMSHRRq_00(x_4);
        Struct1 x_12 = (unpack(0));
        Vector#(4, Bit#(64)) x_13 = (unpack(0));
        Bool x_14 = ((x_7).mesi_owned);
        Bit#(3) x_15 = ((x_7).mesi_status);
        Struct15 x_16 = (Struct15 {dir_st : (((x_7).mesi_dir_st) ==
        ((Bit#(3))'(3'h0)) ? ((Bit#(3))'(3'h1)) : ((x_7).mesi_dir_st)),
        dir_excl : ((((x_7).mesi_dir_sharers)[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        ((((((x_7).mesi_dir_sharers)[3:1])[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        (((((((x_7).mesi_dir_sharers)[3:1])[2:1])[0:0]) == ((Bit#(1))'(1'h1))
        ? ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        ((((((((x_7).mesi_dir_sharers)[3:1])[2:1])[1:1])[0:0]) ==
        ((Bit#(1))'(1'h1)) ? ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        (unpack(0))))))))))))), dir_sharers : (x_7).mesi_dir_sharers});
        when ((x_2) == ((Bit#(4))'(4'h3)), noAction);
        when (((x_3).id) == ((Bit#(6))'(6'ha)), noAction);
        when (! ((x_3).type_), noAction);
        when (((Bool)'(True)) && (((Bool)'(True)) && ((! (((Bit#(3))'(3'h1))
        < (x_15))) && ((! (((x_16).dir_st) < ((Bit#(3))'(3'h3)))) && (!
        (((Bit#(3))'(3'h4)) < ((x_16).dir_st)))))), noAction);
        Struct1 x_17 = (x_3);
        Struct16 x_18 = (Struct16 {addr : (x_3).addr, info_write :
        (Bool)'(False), info_hit : (x_6).info_hit, info_way : (x_6).info_way,
        edir_hit : (x_6).edir_hit, edir_way : (x_6).edir_way, edir_slot :
        (x_6).edir_slot, info : (x_6).info, value_write : (Bool)'(False),
        value : unpack(0), may_victim : (x_6).may_victim, reps :
        (x_6).reps});
        let x_20 = ?;
        if ((x_8).valid) begin
            x_20 = x_9;
        end else begin
            let x_19 <- cache__00__valueRsLineRq(unpack(0));
            x_20 = x_19;
        end
        let x_21 <- registerDL_00(Struct20 {r_id : x_4, r_dl_rss_from :
        (unpack(0)) | (((Bit#(4))'(4'h1)) <<
        (({((Bit#(2))'(2'h1)),((x_16).dir_excl)})[1:0])), r_dl_rsb :
        (Bool)'(True), r_dl_rsbTo : (Bit#(4))'(4'hb)});
        Struct18 x_22 = (Struct18 {enq_type :
        ((({((Bit#(2))'(2'h2)),((x_16).dir_excl)})[3:2]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) :
        (((({((Bit#(2))'(2'h2)),((x_16).dir_excl)})[3:2]) ==
        ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : ({((Bit#(2))'(2'h2)),((x_16).dir_excl)})[1:0], enq_msg :
        Struct1 {id : (Bit#(6))'(6'he), type_ : (Bool)'(False), addr :
        (x_17).addr, value : unpack(0)}});
        let x_23 <- makeEnq_parentChildren00(x_22);
    endrule

    rule rule_exec_00_15003;
        let x_0 <- deq_fifoL2E_00();
        Struct6 x_1 = ((x_0).lr_ir_pp);
        Bit#(4) x_2 = ((x_1).ir_msg_from);
        Struct1 x_3 = ((x_1).ir_msg);
        Bit#(3) x_4 = ((x_1).ir_mshr_id);
        Bool x_5 = ((x_1).ir_is_rs_rel);
        when (! (x_5), noAction);
        Struct9 x_6 = ((x_0).lr_ir);
        Struct10 x_7 = ((x_6).info);
        Struct5 x_8 = ((x_1).ir_by_victim);
        Vector#(4, Bit#(64)) x_9 = ((x_0).lr_value);
        let x_10 <- getMSHR_00(x_4);
        let x_11 <- getMSHRRq_00(x_4);
        Struct1 x_12 = (unpack(0));
        Vector#(4, Bit#(64)) x_13 = (unpack(0));
        Bool x_14 = ((x_7).mesi_owned);
        Bit#(3) x_15 = ((x_7).mesi_status);
        Struct15 x_16 = (Struct15 {dir_st : (((x_7).mesi_dir_st) ==
        ((Bit#(3))'(3'h0)) ? ((Bit#(3))'(3'h1)) : ((x_7).mesi_dir_st)),
        dir_excl : ((((x_7).mesi_dir_sharers)[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        ((((((x_7).mesi_dir_sharers)[3:1])[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        (((((((x_7).mesi_dir_sharers)[3:1])[2:1])[0:0]) == ((Bit#(1))'(1'h1))
        ? ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        ((((((((x_7).mesi_dir_sharers)[3:1])[2:1])[1:1])[0:0]) ==
        ((Bit#(1))'(1'h1)) ? ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        (unpack(0))))))))))))), dir_sharers : (x_7).mesi_dir_sharers});
        when ((x_2) == ((Bit#(4))'(4'h3)), noAction);
        when (((x_3).id) == ((Bit#(6))'(6'ha)), noAction);
        when (! ((x_3).type_), noAction);
        when (((Bool)'(True)) && (((Bool)'(True)) && ((!
        ((((x_16).dir_sharers) & (~(((Bit#(4))'(4'h1)) <<
        ((Bit#(2))'(2'h3))))) == ((Bit#(4))'(4'h0)))) && (((x_14) ==
        ((Bool)'(True))) && ((! (((Bit#(3))'(3'h2)) < (x_15))) &&
        (((x_16).dir_st) == ((Bit#(3))'(3'h2))))))), noAction);
        Struct1 x_17 = (x_3);
        Struct16 x_18 = (Struct16 {addr : (x_3).addr, info_write :
        (Bool)'(False), info_hit : (x_6).info_hit, info_way : (x_6).info_way,
        edir_hit : (x_6).edir_hit, edir_way : (x_6).edir_way, edir_slot :
        (x_6).edir_slot, info : (x_6).info, value_write : (Bool)'(False),
        value : unpack(0), may_victim : (x_6).may_victim, reps :
        (x_6).reps});
        let x_20 = ?;
        if ((x_8).valid) begin
            x_20 = x_9;
        end else begin
            let x_19 <- cache__00__valueRsLineRq(unpack(0));
            x_20 = x_19;
        end
        let x_21 <- registerDL_00(Struct20 {r_id : x_4, r_dl_rss_from :
        ((x_16).dir_sharers) & (~(((Bit#(4))'(4'h1)) << ((Bit#(2))'(2'h3)))),
        r_dl_rsb : (Bool)'(True), r_dl_rsbTo : (Bit#(4))'(4'hb)});
        let x_22 <- broadcast_parentChildren00(Struct21 {cs_inds :
        ((x_16).dir_sharers) & (~(((Bit#(4))'(4'h1)) << ((Bit#(2))'(2'h3)))),
        cs_msg : Struct1 {id : (Bit#(6))'(6'hc), type_ : (Bool)'(False), addr
        : (x_17).addr, value : unpack(0)}});
    endrule

    rule rule_exec_00_25003;
        let x_0 <- deq_fifoL2E_00();
        Struct6 x_1 = ((x_0).lr_ir_pp);
        Bit#(4) x_2 = ((x_1).ir_msg_from);
        Struct1 x_3 = ((x_1).ir_msg);
        Bit#(3) x_4 = ((x_1).ir_mshr_id);
        Bool x_5 = ((x_1).ir_is_rs_rel);
        when (! (x_5), noAction);
        Struct9 x_6 = ((x_0).lr_ir);
        Struct10 x_7 = ((x_6).info);
        Struct5 x_8 = ((x_1).ir_by_victim);
        Vector#(4, Bit#(64)) x_9 = ((x_0).lr_value);
        let x_10 <- getMSHR_00(x_4);
        let x_11 <- getMSHRRq_00(x_4);
        Struct1 x_12 = (unpack(0));
        Vector#(4, Bit#(64)) x_13 = (unpack(0));
        Bool x_14 = ((x_7).mesi_owned);
        Bit#(3) x_15 = ((x_7).mesi_status);
        Struct15 x_16 = (Struct15 {dir_st : (((x_7).mesi_dir_st) ==
        ((Bit#(3))'(3'h0)) ? ((Bit#(3))'(3'h1)) : ((x_7).mesi_dir_st)),
        dir_excl : ((((x_7).mesi_dir_sharers)[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        ((((((x_7).mesi_dir_sharers)[3:1])[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        (((((((x_7).mesi_dir_sharers)[3:1])[2:1])[0:0]) == ((Bit#(1))'(1'h1))
        ? ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        ((((((((x_7).mesi_dir_sharers)[3:1])[2:1])[1:1])[0:0]) ==
        ((Bit#(1))'(1'h1)) ? ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        (unpack(0))))))))))))), dir_sharers : (x_7).mesi_dir_sharers});
        when ((x_2) == ((Bit#(4))'(4'h3)), noAction);
        when (((x_3).id) == ((Bit#(6))'(6'h14)), noAction);
        when (! ((x_3).type_), noAction);
        when ((((((x_16).dir_st) == ((Bit#(3))'(3'h4))) && (((x_16).dir_excl)
        == ((Bit#(2))'(2'h3))) ? ((Bit#(3))'(3'h4)) : (((((x_16).dir_st) ==
        ((Bit#(3))'(3'h3))) && (((x_16).dir_excl) == ((Bit#(2))'(2'h3))) ?
        ((Bit#(3))'(3'h3)) : (((((x_16).dir_st) == ((Bit#(3))'(3'h2))) &&
        ((((x_16).dir_sharers) | (((Bit#(4))'(4'h1)) << ((Bit#(2))'(2'h3))))
        == ((x_16).dir_sharers)) ? ((Bit#(3))'(3'h2)) :
        ((Bit#(3))'(3'h1)))))))) == ((Bit#(3))'(3'h1)), noAction);
        Struct1 x_17 = (x_3);
        Struct16 x_18 = (Struct16 {addr : (x_3).addr, info_write :
        (Bool)'(False), info_hit : (x_6).info_hit, info_way : (x_6).info_way,
        edir_hit : (x_6).edir_hit, edir_way : (x_6).edir_way, edir_slot :
        (x_6).edir_slot, info : (x_6).info, value_write : (Bool)'(False),
        value : unpack(0), may_victim : (x_6).may_victim, reps :
        (x_6).reps});
        let x_20 = ?;
        if ((x_8).valid) begin
            x_20 = x_9;
        end else begin
            let x_19 <- cache__00__valueRsLineRq(unpack(0));
            x_20 = x_19;
        end
        Struct18 x_21 = (Struct18 {enq_type : ((((Bit#(4))'(4'hb))[3:2]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : (((((Bit#(4))'(4'hb))[3:2])
        == ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : ((Bit#(4))'(4'hb))[1:0], enq_msg : Struct1 {id :
        (Bit#(6))'(6'h16), type_ : (Bool)'(True), addr : (x_17).addr, value :
        unpack(0)}});
        let x_22 <- makeEnq_parentChildren00(x_21);
        let x_23 <- releaseMSHR_00(x_4);
    endrule

    rule rule_exec_00_2600003;
        let x_0 <- deq_fifoL2E_00();
        Struct6 x_1 = ((x_0).lr_ir_pp);
        Bit#(4) x_2 = ((x_1).ir_msg_from);
        Struct1 x_3 = ((x_1).ir_msg);
        Bit#(3) x_4 = ((x_1).ir_mshr_id);
        Bool x_5 = ((x_1).ir_is_rs_rel);
        when (! (x_5), noAction);
        Struct9 x_6 = ((x_0).lr_ir);
        Struct10 x_7 = ((x_6).info);
        Struct5 x_8 = ((x_1).ir_by_victim);
        Vector#(4, Bit#(64)) x_9 = ((x_0).lr_value);
        let x_10 <- getMSHR_00(x_4);
        let x_11 <- getMSHRRq_00(x_4);
        Struct1 x_12 = (unpack(0));
        Vector#(4, Bit#(64)) x_13 = (unpack(0));
        Bool x_14 = ((x_7).mesi_owned);
        Bit#(3) x_15 = ((x_7).mesi_status);
        Struct15 x_16 = (Struct15 {dir_st : (((x_7).mesi_dir_st) ==
        ((Bit#(3))'(3'h0)) ? ((Bit#(3))'(3'h1)) : ((x_7).mesi_dir_st)),
        dir_excl : ((((x_7).mesi_dir_sharers)[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        ((((((x_7).mesi_dir_sharers)[3:1])[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        (((((((x_7).mesi_dir_sharers)[3:1])[2:1])[0:0]) == ((Bit#(1))'(1'h1))
        ? ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        ((((((((x_7).mesi_dir_sharers)[3:1])[2:1])[1:1])[0:0]) ==
        ((Bit#(1))'(1'h1)) ? ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        (unpack(0))))))))))))), dir_sharers : (x_7).mesi_dir_sharers});
        when ((x_2) == ((Bit#(4))'(4'h3)), noAction);
        when (((x_3).id) == ((Bit#(6))'(6'h14)), noAction);
        when (! ((x_3).type_), noAction);
        when (((x_14) == ((Bool)'(False))) && (((((((x_16).dir_st) ==
        ((Bit#(3))'(3'h4))) && (((x_16).dir_excl) == ((Bit#(2))'(2'h3))) ?
        ((Bit#(3))'(3'h4)) : (((((x_16).dir_st) == ((Bit#(3))'(3'h3))) &&
        (((x_16).dir_excl) == ((Bit#(2))'(2'h3))) ? ((Bit#(3))'(3'h3)) :
        (((((x_16).dir_st) == ((Bit#(3))'(3'h2))) && ((((x_16).dir_sharers) |
        (((Bit#(4))'(4'h1)) << ((Bit#(2))'(2'h3)))) == ((x_16).dir_sharers))
        ? ((Bit#(3))'(3'h2)) : ((Bit#(3))'(3'h1)))))))) ==
        ((Bit#(3))'(3'h2))) && (((x_16).dir_sharers) == (((Bit#(4))'(4'h1))
        << ((Bit#(2))'(2'h3))))), noAction);
        Struct1 x_17 = (x_3);
        Struct16 x_18 = (Struct16 {addr : (x_3).addr, info_write :
        (Bool)'(False), info_hit : (x_6).info_hit, info_way : (x_6).info_way,
        edir_hit : (x_6).edir_hit, edir_way : (x_6).edir_way, edir_slot :
        (x_6).edir_slot, info : (x_6).info, value_write : (Bool)'(False),
        value : unpack(0), may_victim : (x_6).may_victim, reps :
        (x_6).reps});
        Struct16 x_19 = (Struct16 {addr : (x_18).addr, info_write :
        (Bool)'(True), info_hit : (x_18).info_hit, info_way :
        (x_18).info_way, edir_hit : (x_18).edir_hit, edir_way :
        (x_18).edir_way, edir_slot : (x_18).edir_slot, info : Struct10
        {mesi_owned : ((x_18).info).mesi_owned, mesi_status :
        ((x_18).info).mesi_status, mesi_dir_st : (Struct15 {dir_st :
        (Bit#(3))'(3'h1), dir_excl : unpack(0), dir_sharers :
        unpack(0)}).dir_st, mesi_dir_sharers : (((Struct15 {dir_st :
        (Bit#(3))'(3'h1), dir_excl : unpack(0), dir_sharers :
        unpack(0)}).dir_st) == ((Bit#(3))'(3'h2)) ? ((Struct15 {dir_st :
        (Bit#(3))'(3'h1), dir_excl : unpack(0), dir_sharers :
        unpack(0)}).dir_sharers) : (((Bit#(4))'(4'h1)) << ((Struct15 {dir_st
        : (Bit#(3))'(3'h1), dir_excl : unpack(0), dir_sharers :
        unpack(0)}).dir_excl)))}, value_write : (x_18).value_write, value :
        (x_18).value, may_victim : (x_18).may_victim, reps :
        (x_18).reps});
        let x_22 = ?;
        if ((x_8).valid) begin
            let x_20 <- victims__00__setVictim(Struct17 {victim_idx :
            (x_8).data, victim_info : (x_19).info, victim_value :
            ((x_19).value_write ? ((x_19).value) : (x_9))});
            x_22 = x_9;
        end else begin
            let x_21 <- cache__00__valueRsLineRq(x_19);
            x_22 = x_21;
        end
        Struct18 x_23 = (Struct18 {enq_type : ((((Bit#(4))'(4'hb))[3:2]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : (((((Bit#(4))'(4'hb))[3:2])
        == ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : ((Bit#(4))'(4'hb))[1:0], enq_msg : Struct1 {id :
        (Bit#(6))'(6'h16), type_ : (Bool)'(True), addr : (x_17).addr, value :
        unpack(0)}});
        let x_24 <- makeEnq_parentChildren00(x_23);
        let x_25 <- releaseMSHR_00(x_4);
    endrule

    rule rule_exec_00_2601003;
        let x_0 <- deq_fifoL2E_00();
        Struct6 x_1 = ((x_0).lr_ir_pp);
        Bit#(4) x_2 = ((x_1).ir_msg_from);
        Struct1 x_3 = ((x_1).ir_msg);
        Bit#(3) x_4 = ((x_1).ir_mshr_id);
        Bool x_5 = ((x_1).ir_is_rs_rel);
        when (! (x_5), noAction);
        Struct9 x_6 = ((x_0).lr_ir);
        Struct10 x_7 = ((x_6).info);
        Struct5 x_8 = ((x_1).ir_by_victim);
        Vector#(4, Bit#(64)) x_9 = ((x_0).lr_value);
        let x_10 <- getMSHR_00(x_4);
        let x_11 <- getMSHRRq_00(x_4);
        Struct1 x_12 = (unpack(0));
        Vector#(4, Bit#(64)) x_13 = (unpack(0));
        Bool x_14 = ((x_7).mesi_owned);
        Bit#(3) x_15 = ((x_7).mesi_status);
        Struct15 x_16 = (Struct15 {dir_st : (((x_7).mesi_dir_st) ==
        ((Bit#(3))'(3'h0)) ? ((Bit#(3))'(3'h1)) : ((x_7).mesi_dir_st)),
        dir_excl : ((((x_7).mesi_dir_sharers)[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        ((((((x_7).mesi_dir_sharers)[3:1])[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        (((((((x_7).mesi_dir_sharers)[3:1])[2:1])[0:0]) == ((Bit#(1))'(1'h1))
        ? ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        ((((((((x_7).mesi_dir_sharers)[3:1])[2:1])[1:1])[0:0]) ==
        ((Bit#(1))'(1'h1)) ? ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        (unpack(0))))))))))))), dir_sharers : (x_7).mesi_dir_sharers});
        when ((x_2) == ((Bit#(4))'(4'h3)), noAction);
        when (((x_3).id) == ((Bit#(6))'(6'h14)), noAction);
        when (! ((x_3).type_), noAction);
        when (((x_14) == ((Bool)'(True))) && (((x_15) == ((Bit#(3))'(3'h2)))
        && (((((((x_16).dir_st) == ((Bit#(3))'(3'h4))) && (((x_16).dir_excl)
        == ((Bit#(2))'(2'h3))) ? ((Bit#(3))'(3'h4)) : (((((x_16).dir_st) ==
        ((Bit#(3))'(3'h3))) && (((x_16).dir_excl) == ((Bit#(2))'(2'h3))) ?
        ((Bit#(3))'(3'h3)) : (((((x_16).dir_st) == ((Bit#(3))'(3'h2))) &&
        ((((x_16).dir_sharers) | (((Bit#(4))'(4'h1)) << ((Bit#(2))'(2'h3))))
        == ((x_16).dir_sharers)) ? ((Bit#(3))'(3'h2)) :
        ((Bit#(3))'(3'h1)))))))) == ((Bit#(3))'(3'h2))) &&
        (((x_16).dir_sharers) == (((Bit#(4))'(4'h1)) <<
        ((Bit#(2))'(2'h3)))))), noAction);
        Struct1 x_17 = (x_3);
        Struct16 x_18 = (Struct16 {addr : (x_3).addr, info_write :
        (Bool)'(False), info_hit : (x_6).info_hit, info_way : (x_6).info_way,
        edir_hit : (x_6).edir_hit, edir_way : (x_6).edir_way, edir_slot :
        (x_6).edir_slot, info : (x_6).info, value_write : (Bool)'(False),
        value : unpack(0), may_victim : (x_6).may_victim, reps :
        (x_6).reps});
        Struct16 x_19 = (Struct16 {addr : (x_18).addr, info_write :
        (Bool)'(True), info_hit : (x_18).info_hit, info_way :
        (x_18).info_way, edir_hit : (x_18).edir_hit, edir_way :
        (x_18).edir_way, edir_slot : (x_18).edir_slot, info : Struct10
        {mesi_owned : ((x_18).info).mesi_owned, mesi_status :
        ((x_18).info).mesi_status, mesi_dir_st : (Struct15 {dir_st :
        (Bit#(3))'(3'h1), dir_excl : unpack(0), dir_sharers :
        unpack(0)}).dir_st, mesi_dir_sharers : (((Struct15 {dir_st :
        (Bit#(3))'(3'h1), dir_excl : unpack(0), dir_sharers :
        unpack(0)}).dir_st) == ((Bit#(3))'(3'h2)) ? ((Struct15 {dir_st :
        (Bit#(3))'(3'h1), dir_excl : unpack(0), dir_sharers :
        unpack(0)}).dir_sharers) : (((Bit#(4))'(4'h1)) << ((Struct15 {dir_st
        : (Bit#(3))'(3'h1), dir_excl : unpack(0), dir_sharers :
        unpack(0)}).dir_excl)))}, value_write : (x_18).value_write, value :
        (x_18).value, may_victim : (x_18).may_victim, reps :
        (x_18).reps});
        Struct16 x_20 = (Struct16 {addr : (x_19).addr, info_write :
        (Bool)'(True), info_hit : (x_19).info_hit, info_way :
        (x_19).info_way, edir_hit : (x_19).edir_hit, edir_way :
        (x_19).edir_way, edir_slot : (x_19).edir_slot, info : Struct10
        {mesi_owned : ((x_19).info).mesi_owned, mesi_status :
        (Bit#(3))'(3'h4), mesi_dir_st : ((x_19).info).mesi_dir_st,
        mesi_dir_sharers : ((x_19).info).mesi_dir_sharers}, value_write :
        (x_19).value_write, value : (x_19).value, may_victim :
        (x_19).may_victim, reps :
        (x_19).reps});
        let x_23 = ?;
        if ((x_8).valid) begin
            let x_21 <- victims__00__setVictim(Struct17 {victim_idx :
            (x_8).data, victim_info : (x_20).info, victim_value :
            ((x_20).value_write ? ((x_20).value) : (x_9))});
            x_23 = x_9;
        end else begin
            let x_22 <- cache__00__valueRsLineRq(x_20);
            x_23 = x_22;
        end
        Struct18 x_24 = (Struct18 {enq_type : ((((Bit#(4))'(4'hb))[3:2]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : (((((Bit#(4))'(4'hb))[3:2])
        == ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : ((Bit#(4))'(4'hb))[1:0], enq_msg : Struct1 {id :
        (Bit#(6))'(6'h16), type_ : (Bool)'(True), addr : (x_17).addr, value :
        unpack(0)}});
        let x_25 <- makeEnq_parentChildren00(x_24);
        let x_26 <- releaseMSHR_00(x_4);
    endrule

    rule rule_exec_00_261003;
        let x_0 <- deq_fifoL2E_00();
        Struct6 x_1 = ((x_0).lr_ir_pp);
        Bit#(4) x_2 = ((x_1).ir_msg_from);
        Struct1 x_3 = ((x_1).ir_msg);
        Bit#(3) x_4 = ((x_1).ir_mshr_id);
        Bool x_5 = ((x_1).ir_is_rs_rel);
        when (! (x_5), noAction);
        Struct9 x_6 = ((x_0).lr_ir);
        Struct10 x_7 = ((x_6).info);
        Struct5 x_8 = ((x_1).ir_by_victim);
        Vector#(4, Bit#(64)) x_9 = ((x_0).lr_value);
        let x_10 <- getMSHR_00(x_4);
        let x_11 <- getMSHRRq_00(x_4);
        Struct1 x_12 = (unpack(0));
        Vector#(4, Bit#(64)) x_13 = (unpack(0));
        Bool x_14 = ((x_7).mesi_owned);
        Bit#(3) x_15 = ((x_7).mesi_status);
        Struct15 x_16 = (Struct15 {dir_st : (((x_7).mesi_dir_st) ==
        ((Bit#(3))'(3'h0)) ? ((Bit#(3))'(3'h1)) : ((x_7).mesi_dir_st)),
        dir_excl : ((((x_7).mesi_dir_sharers)[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        ((((((x_7).mesi_dir_sharers)[3:1])[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        (((((((x_7).mesi_dir_sharers)[3:1])[2:1])[0:0]) == ((Bit#(1))'(1'h1))
        ? ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        ((((((((x_7).mesi_dir_sharers)[3:1])[2:1])[1:1])[0:0]) ==
        ((Bit#(1))'(1'h1)) ? ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        (unpack(0))))))))))))), dir_sharers : (x_7).mesi_dir_sharers});
        when ((x_2) == ((Bit#(4))'(4'h3)), noAction);
        when (((x_3).id) == ((Bit#(6))'(6'h14)), noAction);
        when (! ((x_3).type_), noAction);
        when (((((((x_16).dir_st) == ((Bit#(3))'(3'h4))) &&
        (((x_16).dir_excl) == ((Bit#(2))'(2'h3))) ? ((Bit#(3))'(3'h4)) :
        (((((x_16).dir_st) == ((Bit#(3))'(3'h3))) && (((x_16).dir_excl) ==
        ((Bit#(2))'(2'h3))) ? ((Bit#(3))'(3'h3)) : (((((x_16).dir_st) ==
        ((Bit#(3))'(3'h2))) && ((((x_16).dir_sharers) | (((Bit#(4))'(4'h1))
        << ((Bit#(2))'(2'h3)))) == ((x_16).dir_sharers)) ? ((Bit#(3))'(3'h2))
        : ((Bit#(3))'(3'h1)))))))) == ((Bit#(3))'(3'h2))) &&
        (((Bit#(3))'(3'h1)) < ((((((x_16).dir_sharers)[0:0]) ==
        ((Bit#(1))'(1'h1)) ? ((Bit#(3))'(3'h1)) : ((Bit#(3))'(3'h0)))) +
        (((((((x_16).dir_sharers)[3:1])[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(3))'(3'h1)) : ((Bit#(3))'(3'h0)))) +
        ((((((((x_16).dir_sharers)[3:1])[2:1])[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(3))'(3'h1)) : ((Bit#(3))'(3'h0)))) +
        (((((((((x_16).dir_sharers)[3:1])[2:1])[1:1])[0:0]) ==
        ((Bit#(1))'(1'h1)) ? ((Bit#(3))'(3'h1)) : ((Bit#(3))'(3'h0)))) +
        (unpack(0))))))), noAction);
        Struct1 x_17 = (x_3);
        Struct16 x_18 = (Struct16 {addr : (x_3).addr, info_write :
        (Bool)'(False), info_hit : (x_6).info_hit, info_way : (x_6).info_way,
        edir_hit : (x_6).edir_hit, edir_way : (x_6).edir_way, edir_slot :
        (x_6).edir_slot, info : (x_6).info, value_write : (Bool)'(False),
        value : unpack(0), may_victim : (x_6).may_victim, reps :
        (x_6).reps});
        Struct16 x_19 = (Struct16 {addr : (x_18).addr, info_write :
        (Bool)'(True), info_hit : (x_18).info_hit, info_way :
        (x_18).info_way, edir_hit : (x_18).edir_hit, edir_way :
        (x_18).edir_way, edir_slot : (x_18).edir_slot, info : Struct10
        {mesi_owned : ((x_18).info).mesi_owned, mesi_status :
        ((x_18).info).mesi_status, mesi_dir_st : (Struct15 {dir_st :
        (Bit#(3))'(3'h2), dir_excl : (x_16).dir_excl, dir_sharers :
        ((x_16).dir_sharers) & (~(((Bit#(4))'(4'h1)) <<
        ((Bit#(2))'(2'h3))))}).dir_st, mesi_dir_sharers : (((Struct15 {dir_st
        : (Bit#(3))'(3'h2), dir_excl : (x_16).dir_excl, dir_sharers :
        ((x_16).dir_sharers) & (~(((Bit#(4))'(4'h1)) <<
        ((Bit#(2))'(2'h3))))}).dir_st) == ((Bit#(3))'(3'h2)) ? ((Struct15
        {dir_st : (Bit#(3))'(3'h2), dir_excl : (x_16).dir_excl, dir_sharers :
        ((x_16).dir_sharers) & (~(((Bit#(4))'(4'h1)) <<
        ((Bit#(2))'(2'h3))))}).dir_sharers) : (((Bit#(4))'(4'h1)) <<
        ((Struct15 {dir_st : (Bit#(3))'(3'h2), dir_excl : (x_16).dir_excl,
        dir_sharers : ((x_16).dir_sharers) & (~(((Bit#(4))'(4'h1)) <<
        ((Bit#(2))'(2'h3))))}).dir_excl)))}, value_write :
        (x_18).value_write, value : (x_18).value, may_victim :
        (x_18).may_victim, reps :
        (x_18).reps});
        let x_22 = ?;
        if ((x_8).valid) begin
            let x_20 <- victims__00__setVictim(Struct17 {victim_idx :
            (x_8).data, victim_info : (x_19).info, victim_value :
            ((x_19).value_write ? ((x_19).value) : (x_9))});
            x_22 = x_9;
        end else begin
            let x_21 <- cache__00__valueRsLineRq(x_19);
            x_22 = x_21;
        end
        Struct18 x_23 = (Struct18 {enq_type : ((((Bit#(4))'(4'hb))[3:2]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : (((((Bit#(4))'(4'hb))[3:2])
        == ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : ((Bit#(4))'(4'hb))[1:0], enq_msg : Struct1 {id :
        (Bit#(6))'(6'h16), type_ : (Bool)'(True), addr : (x_17).addr, value :
        unpack(0)}});
        let x_24 <- makeEnq_parentChildren00(x_23);
        let x_25 <- releaseMSHR_00(x_4);
    endrule

    rule rule_exec_00_27003;
        let x_0 <- deq_fifoL2E_00();
        Struct6 x_1 = ((x_0).lr_ir_pp);
        Bit#(4) x_2 = ((x_1).ir_msg_from);
        Struct1 x_3 = ((x_1).ir_msg);
        Bit#(3) x_4 = ((x_1).ir_mshr_id);
        Bool x_5 = ((x_1).ir_is_rs_rel);
        when (! (x_5), noAction);
        Struct9 x_6 = ((x_0).lr_ir);
        Struct10 x_7 = ((x_6).info);
        Struct5 x_8 = ((x_1).ir_by_victim);
        Vector#(4, Bit#(64)) x_9 = ((x_0).lr_value);
        let x_10 <- getMSHR_00(x_4);
        let x_11 <- getMSHRRq_00(x_4);
        Struct1 x_12 = (unpack(0));
        Vector#(4, Bit#(64)) x_13 = (unpack(0));
        Bool x_14 = ((x_7).mesi_owned);
        Bit#(3) x_15 = ((x_7).mesi_status);
        Struct15 x_16 = (Struct15 {dir_st : (((x_7).mesi_dir_st) ==
        ((Bit#(3))'(3'h0)) ? ((Bit#(3))'(3'h1)) : ((x_7).mesi_dir_st)),
        dir_excl : ((((x_7).mesi_dir_sharers)[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        ((((((x_7).mesi_dir_sharers)[3:1])[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        (((((((x_7).mesi_dir_sharers)[3:1])[2:1])[0:0]) == ((Bit#(1))'(1'h1))
        ? ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        ((((((((x_7).mesi_dir_sharers)[3:1])[2:1])[1:1])[0:0]) ==
        ((Bit#(1))'(1'h1)) ? ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        (unpack(0))))))))))))), dir_sharers : (x_7).mesi_dir_sharers});
        when ((x_2) == ((Bit#(4))'(4'h3)), noAction);
        when (((x_3).id) == ((Bit#(6))'(6'h14)), noAction);
        when (! ((x_3).type_), noAction);
        when ((((((x_16).dir_st) == ((Bit#(3))'(3'h4))) && (((x_16).dir_excl)
        == ((Bit#(2))'(2'h3))) ? ((Bit#(3))'(3'h4)) : (((((x_16).dir_st) ==
        ((Bit#(3))'(3'h3))) && (((x_16).dir_excl) == ((Bit#(2))'(2'h3))) ?
        ((Bit#(3))'(3'h3)) : (((((x_16).dir_st) == ((Bit#(3))'(3'h2))) &&
        ((((x_16).dir_sharers) | (((Bit#(4))'(4'h1)) << ((Bit#(2))'(2'h3))))
        == ((x_16).dir_sharers)) ? ((Bit#(3))'(3'h2)) :
        ((Bit#(3))'(3'h1)))))))) == ((Bit#(3))'(3'h3)), noAction);
        Struct1 x_17 = (x_3);
        Struct16 x_18 = (Struct16 {addr : (x_3).addr, info_write :
        (Bool)'(False), info_hit : (x_6).info_hit, info_way : (x_6).info_way,
        edir_hit : (x_6).edir_hit, edir_way : (x_6).edir_way, edir_slot :
        (x_6).edir_slot, info : (x_6).info, value_write : (Bool)'(False),
        value : unpack(0), may_victim : (x_6).may_victim, reps :
        (x_6).reps});
        Struct16 x_19 = (Struct16 {addr : (x_18).addr, info_write :
        (Bool)'(True), info_hit : (x_18).info_hit, info_way :
        (x_18).info_way, edir_hit : (x_18).edir_hit, edir_way :
        (x_18).edir_way, edir_slot : (x_18).edir_slot, info : Struct10
        {mesi_owned : ((x_18).info).mesi_owned, mesi_status :
        ((x_18).info).mesi_status, mesi_dir_st : (Struct15 {dir_st :
        (Bit#(3))'(3'h1), dir_excl : unpack(0), dir_sharers :
        unpack(0)}).dir_st, mesi_dir_sharers : (((Struct15 {dir_st :
        (Bit#(3))'(3'h1), dir_excl : unpack(0), dir_sharers :
        unpack(0)}).dir_st) == ((Bit#(3))'(3'h2)) ? ((Struct15 {dir_st :
        (Bit#(3))'(3'h1), dir_excl : unpack(0), dir_sharers :
        unpack(0)}).dir_sharers) : (((Bit#(4))'(4'h1)) << ((Struct15 {dir_st
        : (Bit#(3))'(3'h1), dir_excl : unpack(0), dir_sharers :
        unpack(0)}).dir_excl)))}, value_write : (x_18).value_write, value :
        (x_18).value, may_victim : (x_18).may_victim, reps :
        (x_18).reps});
        Struct16 x_20 = (Struct16 {addr : (x_19).addr, info_write :
        (Bool)'(True), info_hit : (x_19).info_hit, info_way :
        (x_19).info_way, edir_hit : (x_19).edir_hit, edir_way :
        (x_19).edir_way, edir_slot : (x_19).edir_slot, info : Struct10
        {mesi_owned : ((x_19).info).mesi_owned, mesi_status :
        (Bit#(3))'(3'h3), mesi_dir_st : ((x_19).info).mesi_dir_st,
        mesi_dir_sharers : ((x_19).info).mesi_dir_sharers}, value_write :
        (x_19).value_write, value : (x_19).value, may_victim :
        (x_19).may_victim, reps :
        (x_19).reps});
        let x_23 = ?;
        if ((x_8).valid) begin
            let x_21 <- victims__00__setVictim(Struct17 {victim_idx :
            (x_8).data, victim_info : (x_20).info, victim_value :
            ((x_20).value_write ? ((x_20).value) : (x_9))});
            x_23 = x_9;
        end else begin
            let x_22 <- cache__00__valueRsLineRq(x_20);
            x_23 = x_22;
        end
        Struct18 x_24 = (Struct18 {enq_type : ((((Bit#(4))'(4'hb))[3:2]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : (((((Bit#(4))'(4'hb))[3:2])
        == ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : ((Bit#(4))'(4'hb))[1:0], enq_msg : Struct1 {id :
        (Bit#(6))'(6'h16), type_ : (Bool)'(True), addr : (x_17).addr, value :
        unpack(0)}});
        let x_25 <- makeEnq_parentChildren00(x_24);
        let x_26 <- releaseMSHR_00(x_4);
    endrule

    rule rule_exec_00_28003;
        let x_0 <- deq_fifoL2E_00();
        Struct6 x_1 = ((x_0).lr_ir_pp);
        Bit#(4) x_2 = ((x_1).ir_msg_from);
        Struct1 x_3 = ((x_1).ir_msg);
        Bit#(3) x_4 = ((x_1).ir_mshr_id);
        Bool x_5 = ((x_1).ir_is_rs_rel);
        when (! (x_5), noAction);
        Struct9 x_6 = ((x_0).lr_ir);
        Struct10 x_7 = ((x_6).info);
        Struct5 x_8 = ((x_1).ir_by_victim);
        Vector#(4, Bit#(64)) x_9 = ((x_0).lr_value);
        let x_10 <- getMSHR_00(x_4);
        let x_11 <- getMSHRRq_00(x_4);
        Struct1 x_12 = (unpack(0));
        Vector#(4, Bit#(64)) x_13 = (unpack(0));
        Bool x_14 = ((x_7).mesi_owned);
        Bit#(3) x_15 = ((x_7).mesi_status);
        Struct15 x_16 = (Struct15 {dir_st : (((x_7).mesi_dir_st) ==
        ((Bit#(3))'(3'h0)) ? ((Bit#(3))'(3'h1)) : ((x_7).mesi_dir_st)),
        dir_excl : ((((x_7).mesi_dir_sharers)[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        ((((((x_7).mesi_dir_sharers)[3:1])[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        (((((((x_7).mesi_dir_sharers)[3:1])[2:1])[0:0]) == ((Bit#(1))'(1'h1))
        ? ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        ((((((((x_7).mesi_dir_sharers)[3:1])[2:1])[1:1])[0:0]) ==
        ((Bit#(1))'(1'h1)) ? ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        (unpack(0))))))))))))), dir_sharers : (x_7).mesi_dir_sharers});
        when ((x_2) == ((Bit#(4))'(4'h3)), noAction);
        when (((x_3).id) == ((Bit#(6))'(6'h15)), noAction);
        when (! ((x_3).type_), noAction);
        when ((((((x_16).dir_st) == ((Bit#(3))'(3'h4))) && (((x_16).dir_excl)
        == ((Bit#(2))'(2'h3))) ? ((Bit#(3))'(3'h4)) : (((((x_16).dir_st) ==
        ((Bit#(3))'(3'h3))) && (((x_16).dir_excl) == ((Bit#(2))'(2'h3))) ?
        ((Bit#(3))'(3'h3)) : (((((x_16).dir_st) == ((Bit#(3))'(3'h2))) &&
        ((((x_16).dir_sharers) | (((Bit#(4))'(4'h1)) << ((Bit#(2))'(2'h3))))
        == ((x_16).dir_sharers)) ? ((Bit#(3))'(3'h2)) :
        ((Bit#(3))'(3'h1)))))))) == ((Bit#(3))'(3'h1)), noAction);
        Struct1 x_17 = (x_3);
        Struct16 x_18 = (Struct16 {addr : (x_3).addr, info_write :
        (Bool)'(False), info_hit : (x_6).info_hit, info_way : (x_6).info_way,
        edir_hit : (x_6).edir_hit, edir_way : (x_6).edir_way, edir_slot :
        (x_6).edir_slot, info : (x_6).info, value_write : (Bool)'(False),
        value : unpack(0), may_victim : (x_6).may_victim, reps :
        (x_6).reps});
        let x_20 = ?;
        if ((x_8).valid) begin
            x_20 = x_9;
        end else begin
            let x_19 <- cache__00__valueRsLineRq(unpack(0));
            x_20 = x_19;
        end
        Struct18 x_21 = (Struct18 {enq_type : ((((Bit#(4))'(4'hb))[3:2]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : (((((Bit#(4))'(4'hb))[3:2])
        == ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : ((Bit#(4))'(4'hb))[1:0], enq_msg : Struct1 {id :
        (Bit#(6))'(6'h16), type_ : (Bool)'(True), addr : (x_17).addr, value :
        unpack(0)}});
        let x_22 <- makeEnq_parentChildren00(x_21);
        let x_23 <- releaseMSHR_00(x_4);
    endrule

    rule rule_exec_00_290003;
        let x_0 <- deq_fifoL2E_00();
        Struct6 x_1 = ((x_0).lr_ir_pp);
        Bit#(4) x_2 = ((x_1).ir_msg_from);
        Struct1 x_3 = ((x_1).ir_msg);
        Bit#(3) x_4 = ((x_1).ir_mshr_id);
        Bool x_5 = ((x_1).ir_is_rs_rel);
        when (! (x_5), noAction);
        Struct9 x_6 = ((x_0).lr_ir);
        Struct10 x_7 = ((x_6).info);
        Struct5 x_8 = ((x_1).ir_by_victim);
        Vector#(4, Bit#(64)) x_9 = ((x_0).lr_value);
        let x_10 <- getMSHR_00(x_4);
        let x_11 <- getMSHRRq_00(x_4);
        Struct1 x_12 = (unpack(0));
        Vector#(4, Bit#(64)) x_13 = (unpack(0));
        Bool x_14 = ((x_7).mesi_owned);
        Bit#(3) x_15 = ((x_7).mesi_status);
        Struct15 x_16 = (Struct15 {dir_st : (((x_7).mesi_dir_st) ==
        ((Bit#(3))'(3'h0)) ? ((Bit#(3))'(3'h1)) : ((x_7).mesi_dir_st)),
        dir_excl : ((((x_7).mesi_dir_sharers)[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        ((((((x_7).mesi_dir_sharers)[3:1])[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        (((((((x_7).mesi_dir_sharers)[3:1])[2:1])[0:0]) == ((Bit#(1))'(1'h1))
        ? ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        ((((((((x_7).mesi_dir_sharers)[3:1])[2:1])[1:1])[0:0]) ==
        ((Bit#(1))'(1'h1)) ? ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        (unpack(0))))))))))))), dir_sharers : (x_7).mesi_dir_sharers});
        when ((x_2) == ((Bit#(4))'(4'h3)), noAction);
        when (((x_3).id) == ((Bit#(6))'(6'h15)), noAction);
        when (! ((x_3).type_), noAction);
        when (((x_14) == ((Bool)'(False))) && (((((((x_16).dir_st) ==
        ((Bit#(3))'(3'h4))) && (((x_16).dir_excl) == ((Bit#(2))'(2'h3))) ?
        ((Bit#(3))'(3'h4)) : (((((x_16).dir_st) == ((Bit#(3))'(3'h3))) &&
        (((x_16).dir_excl) == ((Bit#(2))'(2'h3))) ? ((Bit#(3))'(3'h3)) :
        (((((x_16).dir_st) == ((Bit#(3))'(3'h2))) && ((((x_16).dir_sharers) |
        (((Bit#(4))'(4'h1)) << ((Bit#(2))'(2'h3)))) == ((x_16).dir_sharers))
        ? ((Bit#(3))'(3'h2)) : ((Bit#(3))'(3'h1)))))))) ==
        ((Bit#(3))'(3'h2))) && (((x_16).dir_sharers) == (((Bit#(4))'(4'h1))
        << ((Bit#(2))'(2'h3))))), noAction);
        Struct1 x_17 = (x_3);
        Struct16 x_18 = (Struct16 {addr : (x_3).addr, info_write :
        (Bool)'(False), info_hit : (x_6).info_hit, info_way : (x_6).info_way,
        edir_hit : (x_6).edir_hit, edir_way : (x_6).edir_way, edir_slot :
        (x_6).edir_slot, info : (x_6).info, value_write : (Bool)'(False),
        value : unpack(0), may_victim : (x_6).may_victim, reps :
        (x_6).reps});
        Struct16 x_19 = (Struct16 {addr : (x_18).addr, info_write :
        (Bool)'(True), info_hit : (x_18).info_hit, info_way :
        (x_18).info_way, edir_hit : (x_18).edir_hit, edir_way :
        (x_18).edir_way, edir_slot : (x_18).edir_slot, info : Struct10
        {mesi_owned : ((x_18).info).mesi_owned, mesi_status :
        ((x_18).info).mesi_status, mesi_dir_st : (Struct15 {dir_st :
        (Bit#(3))'(3'h1), dir_excl : unpack(0), dir_sharers :
        unpack(0)}).dir_st, mesi_dir_sharers : (((Struct15 {dir_st :
        (Bit#(3))'(3'h1), dir_excl : unpack(0), dir_sharers :
        unpack(0)}).dir_st) == ((Bit#(3))'(3'h2)) ? ((Struct15 {dir_st :
        (Bit#(3))'(3'h1), dir_excl : unpack(0), dir_sharers :
        unpack(0)}).dir_sharers) : (((Bit#(4))'(4'h1)) << ((Struct15 {dir_st
        : (Bit#(3))'(3'h1), dir_excl : unpack(0), dir_sharers :
        unpack(0)}).dir_excl)))}, value_write : (x_18).value_write, value :
        (x_18).value, may_victim : (x_18).may_victim, reps :
        (x_18).reps});
        let x_22 = ?;
        if ((x_8).valid) begin
            let x_20 <- victims__00__setVictim(Struct17 {victim_idx :
            (x_8).data, victim_info : (x_19).info, victim_value :
            ((x_19).value_write ? ((x_19).value) : (x_9))});
            x_22 = x_9;
        end else begin
            let x_21 <- cache__00__valueRsLineRq(x_19);
            x_22 = x_21;
        end
        Struct18 x_23 = (Struct18 {enq_type : ((((Bit#(4))'(4'hb))[3:2]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : (((((Bit#(4))'(4'hb))[3:2])
        == ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : ((Bit#(4))'(4'hb))[1:0], enq_msg : Struct1 {id :
        (Bit#(6))'(6'h16), type_ : (Bool)'(True), addr : (x_17).addr, value :
        unpack(0)}});
        let x_24 <- makeEnq_parentChildren00(x_23);
        let x_25 <- releaseMSHR_00(x_4);
    endrule

    rule rule_exec_00_291003;
        let x_0 <- deq_fifoL2E_00();
        Struct6 x_1 = ((x_0).lr_ir_pp);
        Bit#(4) x_2 = ((x_1).ir_msg_from);
        Struct1 x_3 = ((x_1).ir_msg);
        Bit#(3) x_4 = ((x_1).ir_mshr_id);
        Bool x_5 = ((x_1).ir_is_rs_rel);
        when (! (x_5), noAction);
        Struct9 x_6 = ((x_0).lr_ir);
        Struct10 x_7 = ((x_6).info);
        Struct5 x_8 = ((x_1).ir_by_victim);
        Vector#(4, Bit#(64)) x_9 = ((x_0).lr_value);
        let x_10 <- getMSHR_00(x_4);
        let x_11 <- getMSHRRq_00(x_4);
        Struct1 x_12 = (unpack(0));
        Vector#(4, Bit#(64)) x_13 = (unpack(0));
        Bool x_14 = ((x_7).mesi_owned);
        Bit#(3) x_15 = ((x_7).mesi_status);
        Struct15 x_16 = (Struct15 {dir_st : (((x_7).mesi_dir_st) ==
        ((Bit#(3))'(3'h0)) ? ((Bit#(3))'(3'h1)) : ((x_7).mesi_dir_st)),
        dir_excl : ((((x_7).mesi_dir_sharers)[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        ((((((x_7).mesi_dir_sharers)[3:1])[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        (((((((x_7).mesi_dir_sharers)[3:1])[2:1])[0:0]) == ((Bit#(1))'(1'h1))
        ? ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        ((((((((x_7).mesi_dir_sharers)[3:1])[2:1])[1:1])[0:0]) ==
        ((Bit#(1))'(1'h1)) ? ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        (unpack(0))))))))))))), dir_sharers : (x_7).mesi_dir_sharers});
        when ((x_2) == ((Bit#(4))'(4'h3)), noAction);
        when (((x_3).id) == ((Bit#(6))'(6'h15)), noAction);
        when (! ((x_3).type_), noAction);
        when (((((((x_16).dir_st) == ((Bit#(3))'(3'h4))) &&
        (((x_16).dir_excl) == ((Bit#(2))'(2'h3))) ? ((Bit#(3))'(3'h4)) :
        (((((x_16).dir_st) == ((Bit#(3))'(3'h3))) && (((x_16).dir_excl) ==
        ((Bit#(2))'(2'h3))) ? ((Bit#(3))'(3'h3)) : (((((x_16).dir_st) ==
        ((Bit#(3))'(3'h2))) && ((((x_16).dir_sharers) | (((Bit#(4))'(4'h1))
        << ((Bit#(2))'(2'h3)))) == ((x_16).dir_sharers)) ? ((Bit#(3))'(3'h2))
        : ((Bit#(3))'(3'h1)))))))) == ((Bit#(3))'(3'h2))) &&
        (((Bit#(3))'(3'h1)) < ((((((x_16).dir_sharers)[0:0]) ==
        ((Bit#(1))'(1'h1)) ? ((Bit#(3))'(3'h1)) : ((Bit#(3))'(3'h0)))) +
        (((((((x_16).dir_sharers)[3:1])[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(3))'(3'h1)) : ((Bit#(3))'(3'h0)))) +
        ((((((((x_16).dir_sharers)[3:1])[2:1])[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(3))'(3'h1)) : ((Bit#(3))'(3'h0)))) +
        (((((((((x_16).dir_sharers)[3:1])[2:1])[1:1])[0:0]) ==
        ((Bit#(1))'(1'h1)) ? ((Bit#(3))'(3'h1)) : ((Bit#(3))'(3'h0)))) +
        (unpack(0))))))), noAction);
        Struct1 x_17 = (x_3);
        Struct16 x_18 = (Struct16 {addr : (x_3).addr, info_write :
        (Bool)'(False), info_hit : (x_6).info_hit, info_way : (x_6).info_way,
        edir_hit : (x_6).edir_hit, edir_way : (x_6).edir_way, edir_slot :
        (x_6).edir_slot, info : (x_6).info, value_write : (Bool)'(False),
        value : unpack(0), may_victim : (x_6).may_victim, reps :
        (x_6).reps});
        Struct16 x_19 = (Struct16 {addr : (x_18).addr, info_write :
        (Bool)'(True), info_hit : (x_18).info_hit, info_way :
        (x_18).info_way, edir_hit : (x_18).edir_hit, edir_way :
        (x_18).edir_way, edir_slot : (x_18).edir_slot, info : Struct10
        {mesi_owned : ((x_18).info).mesi_owned, mesi_status :
        ((x_18).info).mesi_status, mesi_dir_st : (Struct15 {dir_st :
        (Bit#(3))'(3'h2), dir_excl : (x_16).dir_excl, dir_sharers :
        ((x_16).dir_sharers) & (~(((Bit#(4))'(4'h1)) <<
        ((Bit#(2))'(2'h3))))}).dir_st, mesi_dir_sharers : (((Struct15 {dir_st
        : (Bit#(3))'(3'h2), dir_excl : (x_16).dir_excl, dir_sharers :
        ((x_16).dir_sharers) & (~(((Bit#(4))'(4'h1)) <<
        ((Bit#(2))'(2'h3))))}).dir_st) == ((Bit#(3))'(3'h2)) ? ((Struct15
        {dir_st : (Bit#(3))'(3'h2), dir_excl : (x_16).dir_excl, dir_sharers :
        ((x_16).dir_sharers) & (~(((Bit#(4))'(4'h1)) <<
        ((Bit#(2))'(2'h3))))}).dir_sharers) : (((Bit#(4))'(4'h1)) <<
        ((Struct15 {dir_st : (Bit#(3))'(3'h2), dir_excl : (x_16).dir_excl,
        dir_sharers : ((x_16).dir_sharers) & (~(((Bit#(4))'(4'h1)) <<
        ((Bit#(2))'(2'h3))))}).dir_excl)))}, value_write :
        (x_18).value_write, value : (x_18).value, may_victim :
        (x_18).may_victim, reps :
        (x_18).reps});
        let x_22 = ?;
        if ((x_8).valid) begin
            let x_20 <- victims__00__setVictim(Struct17 {victim_idx :
            (x_8).data, victim_info : (x_19).info, victim_value :
            ((x_19).value_write ? ((x_19).value) : (x_9))});
            x_22 = x_9;
        end else begin
            let x_21 <- cache__00__valueRsLineRq(x_19);
            x_22 = x_21;
        end
        Struct18 x_23 = (Struct18 {enq_type : ((((Bit#(4))'(4'hb))[3:2]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : (((((Bit#(4))'(4'hb))[3:2])
        == ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : ((Bit#(4))'(4'hb))[1:0], enq_msg : Struct1 {id :
        (Bit#(6))'(6'h16), type_ : (Bool)'(True), addr : (x_17).addr, value :
        unpack(0)}});
        let x_24 <- makeEnq_parentChildren00(x_23);
        let x_25 <- releaseMSHR_00(x_4);
    endrule

    rule rule_exec_00_210003;
        let x_0 <- deq_fifoL2E_00();
        Struct6 x_1 = ((x_0).lr_ir_pp);
        Bit#(4) x_2 = ((x_1).ir_msg_from);
        Struct1 x_3 = ((x_1).ir_msg);
        Bit#(3) x_4 = ((x_1).ir_mshr_id);
        Bool x_5 = ((x_1).ir_is_rs_rel);
        when (! (x_5), noAction);
        Struct9 x_6 = ((x_0).lr_ir);
        Struct10 x_7 = ((x_6).info);
        Struct5 x_8 = ((x_1).ir_by_victim);
        Vector#(4, Bit#(64)) x_9 = ((x_0).lr_value);
        let x_10 <- getMSHR_00(x_4);
        let x_11 <- getMSHRRq_00(x_4);
        Struct1 x_12 = (unpack(0));
        Vector#(4, Bit#(64)) x_13 = (unpack(0));
        Bool x_14 = ((x_7).mesi_owned);
        Bit#(3) x_15 = ((x_7).mesi_status);
        Struct15 x_16 = (Struct15 {dir_st : (((x_7).mesi_dir_st) ==
        ((Bit#(3))'(3'h0)) ? ((Bit#(3))'(3'h1)) : ((x_7).mesi_dir_st)),
        dir_excl : ((((x_7).mesi_dir_sharers)[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        ((((((x_7).mesi_dir_sharers)[3:1])[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        (((((((x_7).mesi_dir_sharers)[3:1])[2:1])[0:0]) == ((Bit#(1))'(1'h1))
        ? ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        ((((((((x_7).mesi_dir_sharers)[3:1])[2:1])[1:1])[0:0]) ==
        ((Bit#(1))'(1'h1)) ? ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        (unpack(0))))))))))))), dir_sharers : (x_7).mesi_dir_sharers});
        when ((x_2) == ((Bit#(4))'(4'h3)), noAction);
        when (((x_3).id) == ((Bit#(6))'(6'h15)), noAction);
        when (! ((x_3).type_), noAction);
        when (((x_14) == ((Bool)'(True))) && (((x_15) == ((Bit#(3))'(3'h2)))
        && (((((((x_16).dir_st) == ((Bit#(3))'(3'h4))) && (((x_16).dir_excl)
        == ((Bit#(2))'(2'h3))) ? ((Bit#(3))'(3'h4)) : (((((x_16).dir_st) ==
        ((Bit#(3))'(3'h3))) && (((x_16).dir_excl) == ((Bit#(2))'(2'h3))) ?
        ((Bit#(3))'(3'h3)) : (((((x_16).dir_st) == ((Bit#(3))'(3'h2))) &&
        ((((x_16).dir_sharers) | (((Bit#(4))'(4'h1)) << ((Bit#(2))'(2'h3))))
        == ((x_16).dir_sharers)) ? ((Bit#(3))'(3'h2)) :
        ((Bit#(3))'(3'h1)))))))) == ((Bit#(3))'(3'h2))) &&
        (((x_16).dir_sharers) == (((Bit#(4))'(4'h1)) <<
        ((Bit#(2))'(2'h3)))))), noAction);
        Struct1 x_17 = (x_3);
        Struct16 x_18 = (Struct16 {addr : (x_3).addr, info_write :
        (Bool)'(False), info_hit : (x_6).info_hit, info_way : (x_6).info_way,
        edir_hit : (x_6).edir_hit, edir_way : (x_6).edir_way, edir_slot :
        (x_6).edir_slot, info : (x_6).info, value_write : (Bool)'(False),
        value : unpack(0), may_victim : (x_6).may_victim, reps :
        (x_6).reps});
        Struct16 x_19 = (Struct16 {addr : (x_18).addr, info_write :
        (Bool)'(True), info_hit : (x_18).info_hit, info_way :
        (x_18).info_way, edir_hit : (x_18).edir_hit, edir_way :
        (x_18).edir_way, edir_slot : (x_18).edir_slot, info : Struct10
        {mesi_owned : ((x_18).info).mesi_owned, mesi_status :
        ((x_18).info).mesi_status, mesi_dir_st : (Struct15 {dir_st :
        (Bit#(3))'(3'h1), dir_excl : unpack(0), dir_sharers :
        unpack(0)}).dir_st, mesi_dir_sharers : (((Struct15 {dir_st :
        (Bit#(3))'(3'h1), dir_excl : unpack(0), dir_sharers :
        unpack(0)}).dir_st) == ((Bit#(3))'(3'h2)) ? ((Struct15 {dir_st :
        (Bit#(3))'(3'h1), dir_excl : unpack(0), dir_sharers :
        unpack(0)}).dir_sharers) : (((Bit#(4))'(4'h1)) << ((Struct15 {dir_st
        : (Bit#(3))'(3'h1), dir_excl : unpack(0), dir_sharers :
        unpack(0)}).dir_excl)))}, value_write : (x_18).value_write, value :
        (x_18).value, may_victim : (x_18).may_victim, reps :
        (x_18).reps});
        Struct16 x_20 = (Struct16 {addr : (x_19).addr, info_write :
        (Bool)'(True), info_hit : (x_19).info_hit, info_way :
        (x_19).info_way, edir_hit : (x_19).edir_hit, edir_way :
        (x_19).edir_way, edir_slot : (x_19).edir_slot, info : Struct10
        {mesi_owned : ((x_19).info).mesi_owned, mesi_status :
        (Bit#(3))'(3'h4), mesi_dir_st : ((x_19).info).mesi_dir_st,
        mesi_dir_sharers : ((x_19).info).mesi_dir_sharers}, value_write :
        (x_19).value_write, value : (x_19).value, may_victim :
        (x_19).may_victim, reps :
        (x_19).reps});
        let x_23 = ?;
        if ((x_8).valid) begin
            let x_21 <- victims__00__setVictim(Struct17 {victim_idx :
            (x_8).data, victim_info : (x_20).info, victim_value :
            ((x_20).value_write ? ((x_20).value) : (x_9))});
            x_23 = x_9;
        end else begin
            let x_22 <- cache__00__valueRsLineRq(x_20);
            x_23 = x_22;
        end
        Struct18 x_24 = (Struct18 {enq_type : ((((Bit#(4))'(4'hb))[3:2]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : (((((Bit#(4))'(4'hb))[3:2])
        == ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : ((Bit#(4))'(4'hb))[1:0], enq_msg : Struct1 {id :
        (Bit#(6))'(6'h16), type_ : (Bool)'(True), addr : (x_17).addr, value :
        unpack(0)}});
        let x_25 <- makeEnq_parentChildren00(x_24);
        let x_26 <- releaseMSHR_00(x_4);
    endrule

    rule rule_exec_00_211003;
        let x_0 <- deq_fifoL2E_00();
        Struct6 x_1 = ((x_0).lr_ir_pp);
        Bit#(4) x_2 = ((x_1).ir_msg_from);
        Struct1 x_3 = ((x_1).ir_msg);
        Bit#(3) x_4 = ((x_1).ir_mshr_id);
        Bool x_5 = ((x_1).ir_is_rs_rel);
        when (! (x_5), noAction);
        Struct9 x_6 = ((x_0).lr_ir);
        Struct10 x_7 = ((x_6).info);
        Struct5 x_8 = ((x_1).ir_by_victim);
        Vector#(4, Bit#(64)) x_9 = ((x_0).lr_value);
        let x_10 <- getMSHR_00(x_4);
        let x_11 <- getMSHRRq_00(x_4);
        Struct1 x_12 = (unpack(0));
        Vector#(4, Bit#(64)) x_13 = (unpack(0));
        Bool x_14 = ((x_7).mesi_owned);
        Bit#(3) x_15 = ((x_7).mesi_status);
        Struct15 x_16 = (Struct15 {dir_st : (((x_7).mesi_dir_st) ==
        ((Bit#(3))'(3'h0)) ? ((Bit#(3))'(3'h1)) : ((x_7).mesi_dir_st)),
        dir_excl : ((((x_7).mesi_dir_sharers)[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        ((((((x_7).mesi_dir_sharers)[3:1])[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        (((((((x_7).mesi_dir_sharers)[3:1])[2:1])[0:0]) == ((Bit#(1))'(1'h1))
        ? ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        ((((((((x_7).mesi_dir_sharers)[3:1])[2:1])[1:1])[0:0]) ==
        ((Bit#(1))'(1'h1)) ? ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        (unpack(0))))))))))))), dir_sharers : (x_7).mesi_dir_sharers});
        when ((x_2) == ((Bit#(4))'(4'h3)), noAction);
        when (((x_3).id) == ((Bit#(6))'(6'h15)), noAction);
        when (! ((x_3).type_), noAction);
        when (! ((((((x_16).dir_st) == ((Bit#(3))'(3'h4))) &&
        (((x_16).dir_excl) == ((Bit#(2))'(2'h3))) ? ((Bit#(3))'(3'h4)) :
        (((((x_16).dir_st) == ((Bit#(3))'(3'h3))) && (((x_16).dir_excl) ==
        ((Bit#(2))'(2'h3))) ? ((Bit#(3))'(3'h3)) : (((((x_16).dir_st) ==
        ((Bit#(3))'(3'h2))) && ((((x_16).dir_sharers) | (((Bit#(4))'(4'h1))
        << ((Bit#(2))'(2'h3)))) == ((x_16).dir_sharers)) ? ((Bit#(3))'(3'h2))
        : ((Bit#(3))'(3'h1)))))))) < ((Bit#(3))'(3'h3))), noAction);
        Struct1 x_17 = (x_3);
        Struct16 x_18 = (Struct16 {addr : (x_3).addr, info_write :
        (Bool)'(False), info_hit : (x_6).info_hit, info_way : (x_6).info_way,
        edir_hit : (x_6).edir_hit, edir_way : (x_6).edir_way, edir_slot :
        (x_6).edir_slot, info : (x_6).info, value_write : (Bool)'(False),
        value : unpack(0), may_victim : (x_6).may_victim, reps :
        (x_6).reps});
        Struct16 x_19 = (Struct16 {addr : (x_18).addr, info_write :
        (x_18).info_write, info_hit : (x_18).info_hit, info_way :
        (x_18).info_way, edir_hit : (x_18).edir_hit, edir_way :
        (x_18).edir_way, edir_slot : (x_18).edir_slot, info : (x_18).info,
        value_write : (Bool)'(True), value : (x_17).value, may_victim :
        (x_18).may_victim, reps : (x_18).reps});
        Struct16 x_20 = (Struct16 {addr : (x_19).addr, info_write :
        (Bool)'(True), info_hit : (x_19).info_hit, info_way :
        (x_19).info_way, edir_hit : (x_19).edir_hit, edir_way :
        (x_19).edir_way, edir_slot : (x_19).edir_slot, info : Struct10
        {mesi_owned : ((x_19).info).mesi_owned, mesi_status :
        (Bit#(3))'(3'h4), mesi_dir_st : ((x_19).info).mesi_dir_st,
        mesi_dir_sharers : ((x_19).info).mesi_dir_sharers}, value_write :
        (x_19).value_write, value : (x_19).value, may_victim :
        (x_19).may_victim, reps : (x_19).reps});
        Struct16 x_21 = (Struct16 {addr : (x_20).addr, info_write :
        (Bool)'(True), info_hit : (x_20).info_hit, info_way :
        (x_20).info_way, edir_hit : (x_20).edir_hit, edir_way :
        (x_20).edir_way, edir_slot : (x_20).edir_slot, info : Struct10
        {mesi_owned : (Bool)'(True), mesi_status : ((x_20).info).mesi_status,
        mesi_dir_st : ((x_20).info).mesi_dir_st, mesi_dir_sharers :
        ((x_20).info).mesi_dir_sharers}, value_write : (x_20).value_write,
        value : (x_20).value, may_victim : (x_20).may_victim, reps :
        (x_20).reps});
        Struct16 x_22 = (Struct16 {addr : (x_21).addr, info_write :
        (Bool)'(True), info_hit : (x_21).info_hit, info_way :
        (x_21).info_way, edir_hit : (x_21).edir_hit, edir_way :
        (x_21).edir_way, edir_slot : (x_21).edir_slot, info : Struct10
        {mesi_owned : ((x_21).info).mesi_owned, mesi_status :
        ((x_21).info).mesi_status, mesi_dir_st : (Struct15 {dir_st :
        (Bit#(3))'(3'h1), dir_excl : unpack(0), dir_sharers :
        unpack(0)}).dir_st, mesi_dir_sharers : (((Struct15 {dir_st :
        (Bit#(3))'(3'h1), dir_excl : unpack(0), dir_sharers :
        unpack(0)}).dir_st) == ((Bit#(3))'(3'h2)) ? ((Struct15 {dir_st :
        (Bit#(3))'(3'h1), dir_excl : unpack(0), dir_sharers :
        unpack(0)}).dir_sharers) : (((Bit#(4))'(4'h1)) << ((Struct15 {dir_st
        : (Bit#(3))'(3'h1), dir_excl : unpack(0), dir_sharers :
        unpack(0)}).dir_excl)))}, value_write : (x_21).value_write, value :
        (x_21).value, may_victim : (x_21).may_victim, reps :
        (x_21).reps});
        let x_25 = ?;
        if ((x_8).valid) begin
            let x_23 <- victims__00__setVictim(Struct17 {victim_idx :
            (x_8).data, victim_info : (x_22).info, victim_value :
            ((x_22).value_write ? ((x_22).value) : (x_9))});
            x_25 = x_9;
        end else begin
            let x_24 <- cache__00__valueRsLineRq(x_22);
            x_25 = x_24;
        end
        Struct18 x_26 = (Struct18 {enq_type : ((((Bit#(4))'(4'hb))[3:2]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : (((((Bit#(4))'(4'hb))[3:2])
        == ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : ((Bit#(4))'(4'hb))[1:0], enq_msg : Struct1 {id :
        (Bit#(6))'(6'h16), type_ : (Bool)'(True), addr : (x_17).addr, value :
        unpack(0)}});
        let x_27 <- makeEnq_parentChildren00(x_26);
        let x_28 <- releaseMSHR_00(x_4);
    endrule

    rule rule_exec_00_020;
        let x_0 <- deq_fifoL2E_00();
        Struct6 x_1 = ((x_0).lr_ir_pp);
        Bit#(4) x_2 = ((x_1).ir_msg_from);
        Struct1 x_3 = ((x_1).ir_msg);
        Bit#(3) x_4 = ((x_1).ir_mshr_id);
        Bool x_5 = ((x_1).ir_is_rs_rel);
        when (! (x_5), noAction);
        Struct9 x_6 = ((x_0).lr_ir);
        Struct10 x_7 = ((x_6).info);
        Struct5 x_8 = ((x_1).ir_by_victim);
        Vector#(4, Bit#(64)) x_9 = ((x_0).lr_value);
        let x_10 <- getMSHR_00(x_4);
        let x_11 <- getMSHRRq_00(x_4);
        Struct1 x_12 = (unpack(0));
        Vector#(4, Bit#(64)) x_13 = (unpack(0));
        Bool x_14 = ((x_7).mesi_owned);
        Bit#(3) x_15 = ((x_7).mesi_status);
        Struct15 x_16 = (Struct15 {dir_st : (((x_7).mesi_dir_st) ==
        ((Bit#(3))'(3'h0)) ? ((Bit#(3))'(3'h1)) : ((x_7).mesi_dir_st)),
        dir_excl : ((((x_7).mesi_dir_sharers)[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        ((((((x_7).mesi_dir_sharers)[3:1])[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        (((((((x_7).mesi_dir_sharers)[3:1])[2:1])[0:0]) == ((Bit#(1))'(1'h1))
        ? ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        ((((((((x_7).mesi_dir_sharers)[3:1])[2:1])[1:1])[0:0]) ==
        ((Bit#(1))'(1'h1)) ? ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        (unpack(0))))))))))))), dir_sharers : (x_7).mesi_dir_sharers});
        when ((x_2) == ({((Bit#(2))'(2'h2)),((Bit#(2))'(2'h0))}),
        noAction);
        when (((x_3).id) == ((Bit#(6))'(6'h3)), noAction);
        when ((x_10).m_rsb, noAction);
        when (((x_11).type_) == ((Bool)'(False)), noAction);
        when (((x_11).id) == ((Bit#(6))'(6'h2)), noAction);
        when ((x_10).m_rsb, noAction);
        when ((x_3).type_, noAction);
        when ((Bool)'(True), noAction);
        Struct1 x_17 = (x_3);
        Struct1 x_18 = (x_11);
        Bit#(4) x_19 = ({((Bit#(2))'(2'h2)),(((x_10).m_qidx)[1:0])});
        Struct16 x_20 = (Struct16 {addr : (x_3).addr, info_write :
        (Bool)'(False), info_hit : (x_6).info_hit, info_way : (x_6).info_way,
        edir_hit : (x_6).edir_hit, edir_way : (x_6).edir_way, edir_slot :
        (x_6).edir_slot, info : (x_6).info, value_write : (Bool)'(False),
        value : unpack(0), may_victim : (x_6).may_victim, reps :
        (x_6).reps});
        Struct16 x_21 = (Struct16 {addr : (x_20).addr, info_write :
        (Bool)'(True), info_hit : (x_20).info_hit, info_way :
        (x_20).info_way, edir_hit : (x_20).edir_hit, edir_way :
        (x_20).edir_way, edir_slot : (x_20).edir_slot, info : Struct10
        {mesi_owned : ((x_20).info).mesi_owned, mesi_status :
        ((x_20).info).mesi_status, mesi_dir_st : (Struct15 {dir_st :
        (Bit#(3))'(3'h2), dir_excl : (x_16).dir_excl, dir_sharers :
        (((x_16).dir_st) == ((Bit#(3))'(3'h2)) ? (((x_16).dir_sharers) |
        (((Bit#(4))'(4'h1)) << ((x_19)[1:0]))) : (((Bit#(4))'(4'h1)) <<
        ((x_19)[1:0])))}).dir_st, mesi_dir_sharers : (((Struct15 {dir_st :
        (Bit#(3))'(3'h2), dir_excl : (x_16).dir_excl, dir_sharers :
        (((x_16).dir_st) == ((Bit#(3))'(3'h2)) ? (((x_16).dir_sharers) |
        (((Bit#(4))'(4'h1)) << ((x_19)[1:0]))) : (((Bit#(4))'(4'h1)) <<
        ((x_19)[1:0])))}).dir_st) == ((Bit#(3))'(3'h2)) ? ((Struct15 {dir_st
        : (Bit#(3))'(3'h2), dir_excl : (x_16).dir_excl, dir_sharers :
        (((x_16).dir_st) == ((Bit#(3))'(3'h2)) ? (((x_16).dir_sharers) |
        (((Bit#(4))'(4'h1)) << ((x_19)[1:0]))) : (((Bit#(4))'(4'h1)) <<
        ((x_19)[1:0])))}).dir_sharers) : (((Bit#(4))'(4'h1)) << ((Struct15
        {dir_st : (Bit#(3))'(3'h2), dir_excl : (x_16).dir_excl, dir_sharers :
        (((x_16).dir_st) == ((Bit#(3))'(3'h2)) ? (((x_16).dir_sharers) |
        (((Bit#(4))'(4'h1)) << ((x_19)[1:0]))) : (((Bit#(4))'(4'h1)) <<
        ((x_19)[1:0])))}).dir_excl)))}, value_write : (x_20).value_write,
        value : (x_20).value, may_victim : (x_20).may_victim, reps :
        (x_20).reps});
        Struct16 x_22 = (Struct16 {addr : (x_21).addr, info_write :
        (Bool)'(True), info_hit : (x_21).info_hit, info_way :
        (x_21).info_way, edir_hit : (x_21).edir_hit, edir_way :
        (x_21).edir_way, edir_slot : (x_21).edir_slot, info : Struct10
        {mesi_owned : ((x_21).info).mesi_owned, mesi_status :
        (Bit#(3))'(3'h2), mesi_dir_st : ((x_21).info).mesi_dir_st,
        mesi_dir_sharers : ((x_21).info).mesi_dir_sharers}, value_write :
        (x_21).value_write, value : (x_21).value, may_victim :
        (x_21).may_victim, reps : (x_21).reps});
        Struct16 x_23 = (Struct16 {addr : (x_22).addr, info_write :
        (Bool)'(True), info_hit : (x_22).info_hit, info_way :
        (x_22).info_way, edir_hit : (x_22).edir_hit, edir_way :
        (x_22).edir_way, edir_slot : (x_22).edir_slot, info : Struct10
        {mesi_owned : (Bool)'(False), mesi_status :
        ((x_22).info).mesi_status, mesi_dir_st : ((x_22).info).mesi_dir_st,
        mesi_dir_sharers : ((x_22).info).mesi_dir_sharers}, value_write :
        (x_22).value_write, value : (x_22).value, may_victim :
        (x_22).may_victim, reps : (x_22).reps});
        Struct16 x_24 = (Struct16 {addr : (x_23).addr, info_write :
        (x_23).info_write, info_hit : (x_23).info_hit, info_way :
        (x_23).info_way, edir_hit : (x_23).edir_hit, edir_way :
        (x_23).edir_way, edir_slot : (x_23).edir_slot, info : (x_23).info,
        value_write : (Bool)'(True), value : (x_17).value, may_victim :
        (x_23).may_victim, reps :
        (x_23).reps});
        let x_27 = ?;
        if ((x_8).valid) begin
            let x_25 <- victims__00__setVictim(Struct17 {victim_idx :
            (x_8).data, victim_info : (x_24).info, victim_value :
            ((x_24).value_write ? ((x_24).value) : (x_9))});
            x_27 = x_9;
        end else begin
            let x_26 <- cache__00__valueRsLineRq(x_24);
            x_27 = x_26;
        end
        let x_28 <- releaseMSHR_00(x_4);
        Struct18 x_29 = (Struct18 {enq_type : (((x_19)[3:2]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : ((((x_19)[3:2]) ==
        ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : (x_19)[1:0], enq_msg : Struct1 {id : (Bit#(6))'(6'h3),
        type_ : (Bool)'(True), addr : (x_17).addr, value :
        (x_17).value}});
        let x_30 <- makeEnq_parentChildren00(x_29);
    endrule

    rule rule_exec_00_021;
        let x_0 <- deq_fifoL2E_00();
        Struct6 x_1 = ((x_0).lr_ir_pp);
        Bit#(4) x_2 = ((x_1).ir_msg_from);
        Struct1 x_3 = ((x_1).ir_msg);
        Bit#(3) x_4 = ((x_1).ir_mshr_id);
        Bool x_5 = ((x_1).ir_is_rs_rel);
        when (! (x_5), noAction);
        Struct9 x_6 = ((x_0).lr_ir);
        Struct10 x_7 = ((x_6).info);
        Struct5 x_8 = ((x_1).ir_by_victim);
        Vector#(4, Bit#(64)) x_9 = ((x_0).lr_value);
        let x_10 <- getMSHR_00(x_4);
        let x_11 <- getMSHRRq_00(x_4);
        Struct1 x_12 = (unpack(0));
        Vector#(4, Bit#(64)) x_13 = (unpack(0));
        Bool x_14 = ((x_7).mesi_owned);
        Bit#(3) x_15 = ((x_7).mesi_status);
        Struct15 x_16 = (Struct15 {dir_st : (((x_7).mesi_dir_st) ==
        ((Bit#(3))'(3'h0)) ? ((Bit#(3))'(3'h1)) : ((x_7).mesi_dir_st)),
        dir_excl : ((((x_7).mesi_dir_sharers)[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        ((((((x_7).mesi_dir_sharers)[3:1])[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        (((((((x_7).mesi_dir_sharers)[3:1])[2:1])[0:0]) == ((Bit#(1))'(1'h1))
        ? ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        ((((((((x_7).mesi_dir_sharers)[3:1])[2:1])[1:1])[0:0]) ==
        ((Bit#(1))'(1'h1)) ? ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        (unpack(0))))))))))))), dir_sharers : (x_7).mesi_dir_sharers});
        when ((x_2) == ({((Bit#(2))'(2'h2)),((Bit#(2))'(2'h0))}),
        noAction);
        when (((x_3).id) == ((Bit#(6))'(6'h4)), noAction);
        when ((x_10).m_rsb, noAction);
        when (((x_11).type_) == ((Bool)'(False)), noAction);
        when (((x_11).id) == ((Bit#(6))'(6'h2)), noAction);
        when ((x_10).m_rsb, noAction);
        when ((x_3).type_, noAction);
        when ((Bool)'(True), noAction);
        Struct1 x_17 = (x_3);
        Struct1 x_18 = (x_11);
        Bit#(4) x_19 = ({((Bit#(2))'(2'h2)),(((x_10).m_qidx)[1:0])});
        Struct16 x_20 = (Struct16 {addr : (x_3).addr, info_write :
        (Bool)'(False), info_hit : (x_6).info_hit, info_way : (x_6).info_way,
        edir_hit : (x_6).edir_hit, edir_way : (x_6).edir_way, edir_slot :
        (x_6).edir_slot, info : (x_6).info, value_write : (Bool)'(False),
        value : unpack(0), may_victim : (x_6).may_victim, reps :
        (x_6).reps});
        Struct16 x_21 = (Struct16 {addr : (x_20).addr, info_write :
        (Bool)'(True), info_hit : (x_20).info_hit, info_way :
        (x_20).info_way, edir_hit : (x_20).edir_hit, edir_way :
        (x_20).edir_way, edir_slot : (x_20).edir_slot, info : Struct10
        {mesi_owned : ((x_20).info).mesi_owned, mesi_status :
        ((x_20).info).mesi_status, mesi_dir_st : (Struct15 {dir_st :
        (Bit#(3))'(3'h3), dir_excl : (x_19)[1:0], dir_sharers :
        unpack(0)}).dir_st, mesi_dir_sharers : (((Struct15 {dir_st :
        (Bit#(3))'(3'h3), dir_excl : (x_19)[1:0], dir_sharers :
        unpack(0)}).dir_st) == ((Bit#(3))'(3'h2)) ? ((Struct15 {dir_st :
        (Bit#(3))'(3'h3), dir_excl : (x_19)[1:0], dir_sharers :
        unpack(0)}).dir_sharers) : (((Bit#(4))'(4'h1)) << ((Struct15 {dir_st
        : (Bit#(3))'(3'h3), dir_excl : (x_19)[1:0], dir_sharers :
        unpack(0)}).dir_excl)))}, value_write : (x_20).value_write, value :
        (x_20).value, may_victim : (x_20).may_victim, reps :
        (x_20).reps});
        Struct16 x_22 = (Struct16 {addr : (x_21).addr, info_write :
        (Bool)'(True), info_hit : (x_21).info_hit, info_way :
        (x_21).info_way, edir_hit : (x_21).edir_hit, edir_way :
        (x_21).edir_way, edir_slot : (x_21).edir_slot, info : Struct10
        {mesi_owned : ((x_21).info).mesi_owned, mesi_status :
        (Bit#(3))'(3'h1), mesi_dir_st : ((x_21).info).mesi_dir_st,
        mesi_dir_sharers : ((x_21).info).mesi_dir_sharers}, value_write :
        (x_21).value_write, value : (x_21).value, may_victim :
        (x_21).may_victim, reps : (x_21).reps});
        Struct16 x_23 = (Struct16 {addr : (x_22).addr, info_write :
        (Bool)'(True), info_hit : (x_22).info_hit, info_way :
        (x_22).info_way, edir_hit : (x_22).edir_hit, edir_way :
        (x_22).edir_way, edir_slot : (x_22).edir_slot, info : Struct10
        {mesi_owned : (Bool)'(False), mesi_status :
        ((x_22).info).mesi_status, mesi_dir_st : ((x_22).info).mesi_dir_st,
        mesi_dir_sharers : ((x_22).info).mesi_dir_sharers}, value_write :
        (x_22).value_write, value : (x_22).value, may_victim :
        (x_22).may_victim, reps : (x_22).reps});
        Struct16 x_24 = (Struct16 {addr : (x_23).addr, info_write :
        (x_23).info_write, info_hit : (x_23).info_hit, info_way :
        (x_23).info_way, edir_hit : (x_23).edir_hit, edir_way :
        (x_23).edir_way, edir_slot : (x_23).edir_slot, info : (x_23).info,
        value_write : (Bool)'(True), value : (x_17).value, may_victim :
        (x_23).may_victim, reps :
        (x_23).reps});
        let x_27 = ?;
        if ((x_8).valid) begin
            let x_25 <- victims__00__setVictim(Struct17 {victim_idx :
            (x_8).data, victim_info : (x_24).info, victim_value :
            ((x_24).value_write ? ((x_24).value) : (x_9))});
            x_27 = x_9;
        end else begin
            let x_26 <- cache__00__valueRsLineRq(x_24);
            x_27 = x_26;
        end
        let x_28 <- releaseMSHR_00(x_4);
        Struct18 x_29 = (Struct18 {enq_type : (((x_19)[3:2]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : ((((x_19)[3:2]) ==
        ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : (x_19)[1:0], enq_msg : Struct1 {id : (Bit#(6))'(6'h4),
        type_ : (Bool)'(True), addr : (x_17).addr, value :
        (x_17).value}});
        let x_30 <- makeEnq_parentChildren00(x_29);
    endrule

    rule rule_exec_00_041;
        let x_0 <- deq_fifoL2E_00();
        Struct6 x_1 = ((x_0).lr_ir_pp);
        Bit#(4) x_2 = ((x_1).ir_msg_from);
        Struct1 x_3 = ((x_1).ir_msg);
        Bit#(3) x_4 = ((x_1).ir_mshr_id);
        Bool x_5 = ((x_1).ir_is_rs_rel);
        when (x_5, noAction);
        Struct9 x_6 = ((x_0).lr_ir);
        Struct10 x_7 = ((x_6).info);
        Struct5 x_8 = ((x_1).ir_by_victim);
        Vector#(4, Bit#(64)) x_9 = ((x_0).lr_value);
        let x_10 <- getMSHR_00(x_4);
        let x_11 <- getMSHRRq_00(x_4);
        let x_12 <- getMSHRFirstRs_00(x_4);
        Vector#(4, Bit#(64)) x_13 = (unpack(0));
        Bool x_14 = ((x_7).mesi_owned);
        Bit#(3) x_15 = ((x_7).mesi_status);
        Struct15 x_16 = (Struct15 {dir_st : (((x_7).mesi_dir_st) ==
        ((Bit#(3))'(3'h0)) ? ((Bit#(3))'(3'h1)) : ((x_7).mesi_dir_st)),
        dir_excl : ((((x_7).mesi_dir_sharers)[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        ((((((x_7).mesi_dir_sharers)[3:1])[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        (((((((x_7).mesi_dir_sharers)[3:1])[2:1])[0:0]) == ((Bit#(1))'(1'h1))
        ? ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        ((((((((x_7).mesi_dir_sharers)[3:1])[2:1])[1:1])[0:0]) ==
        ((Bit#(1))'(1'h1)) ? ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        (unpack(0))))))))))))), dir_sharers : (x_7).mesi_dir_sharers});
        when ((x_10).m_rsb, noAction);
        when (((x_11).type_) == ((Bool)'(False)), noAction);
        when (((x_11).id) == ((Bit#(6))'(6'h2)), noAction);
        when ((Bool)'(True), noAction);
        Struct22 x_17 = (Struct22 {cidx :
        {((Bit#(2))'(2'h1)),(((((x_10).m_dl_rss_from)[0:0]) ==
        ((Bit#(1))'(1'h1)) ? ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        ((((((x_10).m_dl_rss_from)[3:1])[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        (((((((x_10).m_dl_rss_from)[3:1])[2:1])[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        ((((((((x_10).m_dl_rss_from)[3:1])[2:1])[1:1])[0:0]) ==
        ((Bit#(1))'(1'h1)) ? ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        (unpack(0))))))))))))))}, msg : x_12});
        Struct1 x_18 = (x_11);
        Bit#(4) x_19 = ((x_10).m_qidx);
        Struct16 x_20 = (Struct16 {addr : (x_3).addr, info_write :
        (Bool)'(False), info_hit : (x_6).info_hit, info_way : (x_6).info_way,
        edir_hit : (x_6).edir_hit, edir_way : (x_6).edir_way, edir_slot :
        (x_6).edir_slot, info : (x_6).info, value_write : (Bool)'(False),
        value : unpack(0), may_victim : (x_6).may_victim, reps :
        (x_6).reps});
        Struct16 x_21 = (Struct16 {addr : (x_20).addr, info_write :
        (Bool)'(True), info_hit : (x_20).info_hit, info_way :
        (x_20).info_way, edir_hit : (x_20).edir_hit, edir_way :
        (x_20).edir_way, edir_slot : (x_20).edir_slot, info : Struct10
        {mesi_owned : ((x_20).info).mesi_owned, mesi_status :
        ((x_20).info).mesi_status, mesi_dir_st : (Struct15 {dir_st :
        (Bit#(3))'(3'h2), dir_excl : unpack(0), dir_sharers : ((unpack(0)) |
        (((Bit#(4))'(4'h1)) << ((x_19)[1:0]))) | (((Bit#(4))'(4'h1)) <<
        (((x_17).cidx)[1:0]))}).dir_st, mesi_dir_sharers : (((Struct15
        {dir_st : (Bit#(3))'(3'h2), dir_excl : unpack(0), dir_sharers :
        ((unpack(0)) | (((Bit#(4))'(4'h1)) << ((x_19)[1:0]))) |
        (((Bit#(4))'(4'h1)) << (((x_17).cidx)[1:0]))}).dir_st) ==
        ((Bit#(3))'(3'h2)) ? ((Struct15 {dir_st : (Bit#(3))'(3'h2), dir_excl
        : unpack(0), dir_sharers : ((unpack(0)) | (((Bit#(4))'(4'h1)) <<
        ((x_19)[1:0]))) | (((Bit#(4))'(4'h1)) <<
        (((x_17).cidx)[1:0]))}).dir_sharers) : (((Bit#(4))'(4'h1)) <<
        ((Struct15 {dir_st : (Bit#(3))'(3'h2), dir_excl : unpack(0),
        dir_sharers : ((unpack(0)) | (((Bit#(4))'(4'h1)) << ((x_19)[1:0]))) |
        (((Bit#(4))'(4'h1)) << (((x_17).cidx)[1:0]))}).dir_excl)))},
        value_write : (x_20).value_write, value : (x_20).value, may_victim :
        (x_20).may_victim, reps : (x_20).reps});
        Struct16 x_22 = (Struct16 {addr : (x_21).addr, info_write :
        (Bool)'(True), info_hit : (x_21).info_hit, info_way :
        (x_21).info_way, edir_hit : (x_21).edir_hit, edir_way :
        (x_21).edir_way, edir_slot : (x_21).edir_slot, info : Struct10
        {mesi_owned : ((x_21).info).mesi_owned, mesi_status :
        (Bit#(3))'(3'h2), mesi_dir_st : ((x_21).info).mesi_dir_st,
        mesi_dir_sharers : ((x_21).info).mesi_dir_sharers}, value_write :
        (x_21).value_write, value : (x_21).value, may_victim :
        (x_21).may_victim, reps : (x_21).reps});
        Struct16 x_23 = (Struct16 {addr : (x_22).addr, info_write :
        (x_22).info_write, info_hit : (x_22).info_hit, info_way :
        (x_22).info_way, edir_hit : (x_22).edir_hit, edir_way :
        (x_22).edir_way, edir_slot : (x_22).edir_slot, info : (x_22).info,
        value_write : (Bool)'(True), value : ((x_17).msg).value, may_victim :
        (x_22).may_victim, reps : (x_22).reps});
        Struct16 x_24 = (Struct16 {addr : (x_23).addr, info_write :
        (Bool)'(True), info_hit : (x_23).info_hit, info_way :
        (x_23).info_way, edir_hit : (x_23).edir_hit, edir_way :
        (x_23).edir_way, edir_slot : (x_23).edir_slot, info : Struct10
        {mesi_owned : (Bool)'(True), mesi_status : ((x_23).info).mesi_status,
        mesi_dir_st : ((x_23).info).mesi_dir_st, mesi_dir_sharers :
        ((x_23).info).mesi_dir_sharers}, value_write : (x_23).value_write,
        value : (x_23).value, may_victim : (x_23).may_victim, reps :
        (x_23).reps});
        let x_27 = ?;
        if ((x_8).valid) begin
            let x_25 <- victims__00__setVictim(Struct17 {victim_idx :
            (x_8).data, victim_info : (x_24).info, victim_value :
            ((x_24).value_write ? ((x_24).value) : (x_9))});
            x_27 = x_9;
        end else begin
            let x_26 <- cache__00__valueRsLineRq(x_24);
            x_27 = x_26;
        end
        let x_28 <- releaseMSHR_00(x_4);
        Struct18 x_29 = (Struct18 {enq_type : (((x_19)[3:2]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : ((((x_19)[3:2]) ==
        ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : (x_19)[1:0], enq_msg : Struct1 {id : (Bit#(6))'(6'h3),
        type_ : (Bool)'(True), addr : (x_18).addr, value :
        ((x_17).msg).value}});
        let x_30 <- makeEnq_parentChildren00(x_29);
    endrule

    rule rule_exec_00_05;
        let x_0 <- deq_fifoL2E_00();
        Struct6 x_1 = ((x_0).lr_ir_pp);
        Bit#(4) x_2 = ((x_1).ir_msg_from);
        Struct1 x_3 = ((x_1).ir_msg);
        Bit#(3) x_4 = ((x_1).ir_mshr_id);
        Bool x_5 = ((x_1).ir_is_rs_rel);
        when (! (x_5), noAction);
        Struct9 x_6 = ((x_0).lr_ir);
        Struct10 x_7 = ((x_6).info);
        Struct5 x_8 = ((x_1).ir_by_victim);
        Vector#(4, Bit#(64)) x_9 = ((x_0).lr_value);
        let x_10 <- getMSHR_00(x_4);
        let x_11 <- getMSHRRq_00(x_4);
        Struct1 x_12 = (unpack(0));
        Vector#(4, Bit#(64)) x_13 = (unpack(0));
        Bool x_14 = ((x_7).mesi_owned);
        Bit#(3) x_15 = ((x_7).mesi_status);
        Struct15 x_16 = (Struct15 {dir_st : (((x_7).mesi_dir_st) ==
        ((Bit#(3))'(3'h0)) ? ((Bit#(3))'(3'h1)) : ((x_7).mesi_dir_st)),
        dir_excl : ((((x_7).mesi_dir_sharers)[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        ((((((x_7).mesi_dir_sharers)[3:1])[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        (((((((x_7).mesi_dir_sharers)[3:1])[2:1])[0:0]) == ((Bit#(1))'(1'h1))
        ? ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        ((((((((x_7).mesi_dir_sharers)[3:1])[2:1])[1:1])[0:0]) ==
        ((Bit#(1))'(1'h1)) ? ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        (unpack(0))))))))))))), dir_sharers : (x_7).mesi_dir_sharers});
        when ((x_2) == ((Bit#(4))'(4'h8)), noAction);
        when (((x_3).id) == ((Bit#(6))'(6'h5)), noAction);
        when (! ((x_3).type_), noAction);
        when ((! ((x_15) < ((Bit#(3))'(3'h2)))) && (! (((Bit#(3))'(3'h2)) <
        ((x_16).dir_st))), noAction);
        Struct1 x_17 = (x_3);
        Struct16 x_18 = (Struct16 {addr : (x_3).addr, info_write :
        (Bool)'(False), info_hit : (x_6).info_hit, info_way : (x_6).info_way,
        edir_hit : (x_6).edir_hit, edir_way : (x_6).edir_way, edir_slot :
        (x_6).edir_slot, info : (x_6).info, value_write : (Bool)'(False),
        value : unpack(0), may_victim : (x_6).may_victim, reps :
        (x_6).reps});
        Struct16 x_19 = (Struct16 {addr : (x_18).addr, info_write :
        (Bool)'(True), info_hit : (x_18).info_hit, info_way :
        (x_18).info_way, edir_hit : (x_18).edir_hit, edir_way :
        (x_18).edir_way, edir_slot : (x_18).edir_slot, info : Struct10
        {mesi_owned : ((x_18).info).mesi_owned, mesi_status :
        (Bit#(3))'(3'h2), mesi_dir_st : ((x_18).info).mesi_dir_st,
        mesi_dir_sharers : ((x_18).info).mesi_dir_sharers}, value_write :
        (x_18).value_write, value : (x_18).value, may_victim :
        (x_18).may_victim, reps : (x_18).reps});
        Struct16 x_20 = (Struct16 {addr : (x_19).addr, info_write :
        (Bool)'(True), info_hit : (x_19).info_hit, info_way :
        (x_19).info_way, edir_hit : (x_19).edir_hit, edir_way :
        (x_19).edir_way, edir_slot : (x_19).edir_slot, info : Struct10
        {mesi_owned : (Bool)'(False), mesi_status :
        ((x_19).info).mesi_status, mesi_dir_st : ((x_19).info).mesi_dir_st,
        mesi_dir_sharers : ((x_19).info).mesi_dir_sharers}, value_write :
        (x_19).value_write, value : (x_19).value, may_victim :
        (x_19).may_victim, reps :
        (x_19).reps});
        let x_23 = ?;
        if ((x_8).valid) begin
            let x_21 <- victims__00__setVictim(Struct17 {victim_idx :
            (x_8).data, victim_info : (x_20).info, victim_value :
            ((x_20).value_write ? ((x_20).value) : (x_9))});
            x_23 = x_9;
        end else begin
            let x_22 <- cache__00__valueRsLineRq(x_20);
            x_23 = x_22;
        end
        Struct18 x_24 = (Struct18 {enq_type : ((((Bit#(4))'(4'h4))[3:2]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : (((((Bit#(4))'(4'h4))[3:2])
        == ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : ((Bit#(4))'(4'h4))[1:0], enq_msg : Struct1 {id :
        (Bit#(6))'(6'h6), type_ : (Bool)'(True), addr : (x_17).addr, value :
        x_23}});
        let x_25 <- makeEnq_parentChildren00(x_24);
        let x_26 <- releaseMSHR_00(x_4);
    endrule

    rule rule_exec_00_06;
        let x_0 <- deq_fifoL2E_00();
        Struct6 x_1 = ((x_0).lr_ir_pp);
        Bit#(4) x_2 = ((x_1).ir_msg_from);
        Struct1 x_3 = ((x_1).ir_msg);
        Bit#(3) x_4 = ((x_1).ir_mshr_id);
        Bool x_5 = ((x_1).ir_is_rs_rel);
        when (! (x_5), noAction);
        Struct9 x_6 = ((x_0).lr_ir);
        Struct10 x_7 = ((x_6).info);
        Struct5 x_8 = ((x_1).ir_by_victim);
        Vector#(4, Bit#(64)) x_9 = ((x_0).lr_value);
        let x_10 <- getMSHR_00(x_4);
        let x_11 <- getMSHRRq_00(x_4);
        Struct1 x_12 = (unpack(0));
        Vector#(4, Bit#(64)) x_13 = (unpack(0));
        Bool x_14 = ((x_7).mesi_owned);
        Bit#(3) x_15 = ((x_7).mesi_status);
        Struct15 x_16 = (Struct15 {dir_st : (((x_7).mesi_dir_st) ==
        ((Bit#(3))'(3'h0)) ? ((Bit#(3))'(3'h1)) : ((x_7).mesi_dir_st)),
        dir_excl : ((((x_7).mesi_dir_sharers)[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        ((((((x_7).mesi_dir_sharers)[3:1])[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        (((((((x_7).mesi_dir_sharers)[3:1])[2:1])[0:0]) == ((Bit#(1))'(1'h1))
        ? ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        ((((((((x_7).mesi_dir_sharers)[3:1])[2:1])[1:1])[0:0]) ==
        ((Bit#(1))'(1'h1)) ? ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        (unpack(0))))))))))))), dir_sharers : (x_7).mesi_dir_sharers});
        when ((x_2) == ((Bit#(4))'(4'h8)), noAction);
        when (((x_3).id) == ((Bit#(6))'(6'h5)), noAction);
        when (! ((x_3).type_), noAction);
        when (((Bool)'(True)) && ((! (((Bit#(3))'(3'h1)) < (x_15))) && ((!
        (((x_16).dir_st) < ((Bit#(3))'(3'h3)))) && (! (((Bit#(3))'(3'h4)) <
        ((x_16).dir_st))))), noAction);
        Struct1 x_17 = (x_3);
        Struct16 x_18 = (Struct16 {addr : (x_3).addr, info_write :
        (Bool)'(False), info_hit : (x_6).info_hit, info_way : (x_6).info_way,
        edir_hit : (x_6).edir_hit, edir_way : (x_6).edir_way, edir_slot :
        (x_6).edir_slot, info : (x_6).info, value_write : (Bool)'(False),
        value : unpack(0), may_victim : (x_6).may_victim, reps :
        (x_6).reps});
        let x_20 = ?;
        if ((x_8).valid) begin
            x_20 = x_9;
        end else begin
            let x_19 <- cache__00__valueRsLineRq(unpack(0));
            x_20 = x_19;
        end
        let x_21 <- registerDL_00(Struct20 {r_id : x_4, r_dl_rss_from :
        (unpack(0)) | (((Bit#(4))'(4'h1)) <<
        (({((Bit#(2))'(2'h1)),((x_16).dir_excl)})[1:0])), r_dl_rsb :
        (Bool)'(True), r_dl_rsbTo : (Bit#(4))'(4'h4)});
        Struct18 x_22 = (Struct18 {enq_type :
        ((({((Bit#(2))'(2'h2)),((x_16).dir_excl)})[3:2]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) :
        (((({((Bit#(2))'(2'h2)),((x_16).dir_excl)})[3:2]) ==
        ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : ({((Bit#(2))'(2'h2)),((x_16).dir_excl)})[1:0], enq_msg :
        Struct1 {id : (Bit#(6))'(6'h5), type_ : (Bool)'(False), addr :
        (x_17).addr, value : unpack(0)}});
        let x_23 <- makeEnq_parentChildren00(x_22);
    endrule

    rule rule_exec_00_071;
        let x_0 <- deq_fifoL2E_00();
        Struct6 x_1 = ((x_0).lr_ir_pp);
        Bit#(4) x_2 = ((x_1).ir_msg_from);
        Struct1 x_3 = ((x_1).ir_msg);
        Bit#(3) x_4 = ((x_1).ir_mshr_id);
        Bool x_5 = ((x_1).ir_is_rs_rel);
        when (x_5, noAction);
        Struct9 x_6 = ((x_0).lr_ir);
        Struct10 x_7 = ((x_6).info);
        Struct5 x_8 = ((x_1).ir_by_victim);
        Vector#(4, Bit#(64)) x_9 = ((x_0).lr_value);
        let x_10 <- getMSHR_00(x_4);
        let x_11 <- getMSHRRq_00(x_4);
        let x_12 <- getMSHRFirstRs_00(x_4);
        Vector#(4, Bit#(64)) x_13 = (unpack(0));
        Bool x_14 = ((x_7).mesi_owned);
        Bit#(3) x_15 = ((x_7).mesi_status);
        Struct15 x_16 = (Struct15 {dir_st : (((x_7).mesi_dir_st) ==
        ((Bit#(3))'(3'h0)) ? ((Bit#(3))'(3'h1)) : ((x_7).mesi_dir_st)),
        dir_excl : ((((x_7).mesi_dir_sharers)[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        ((((((x_7).mesi_dir_sharers)[3:1])[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        (((((((x_7).mesi_dir_sharers)[3:1])[2:1])[0:0]) == ((Bit#(1))'(1'h1))
        ? ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        ((((((((x_7).mesi_dir_sharers)[3:1])[2:1])[1:1])[0:0]) ==
        ((Bit#(1))'(1'h1)) ? ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        (unpack(0))))))))))))), dir_sharers : (x_7).mesi_dir_sharers});
        when ((x_10).m_rsb, noAction);
        when (((x_11).type_) == ((Bool)'(False)), noAction);
        when (((x_11).id) == ((Bit#(6))'(6'h5)), noAction);
        when ((Bool)'(True), noAction);
        Struct22 x_17 = (Struct22 {cidx :
        {((Bit#(2))'(2'h1)),(((((x_10).m_dl_rss_from)[0:0]) ==
        ((Bit#(1))'(1'h1)) ? ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        ((((((x_10).m_dl_rss_from)[3:1])[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        (((((((x_10).m_dl_rss_from)[3:1])[2:1])[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        ((((((((x_10).m_dl_rss_from)[3:1])[2:1])[1:1])[0:0]) ==
        ((Bit#(1))'(1'h1)) ? ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        (unpack(0))))))))))))))}, msg : x_12});
        Struct1 x_18 = (x_11);
        Bit#(4) x_19 = ((x_10).m_qidx);
        Struct16 x_20 = (Struct16 {addr : (x_3).addr, info_write :
        (Bool)'(False), info_hit : (x_6).info_hit, info_way : (x_6).info_way,
        edir_hit : (x_6).edir_hit, edir_way : (x_6).edir_way, edir_slot :
        (x_6).edir_slot, info : (x_6).info, value_write : (Bool)'(False),
        value : unpack(0), may_victim : (x_6).may_victim, reps :
        (x_6).reps});
        Struct16 x_21 = (Struct16 {addr : (x_20).addr, info_write :
        (Bool)'(True), info_hit : (x_20).info_hit, info_way :
        (x_20).info_way, edir_hit : (x_20).edir_hit, edir_way :
        (x_20).edir_way, edir_slot : (x_20).edir_slot, info : Struct10
        {mesi_owned : ((x_20).info).mesi_owned, mesi_status :
        ((x_20).info).mesi_status, mesi_dir_st : (Struct15 {dir_st :
        (Bit#(3))'(3'h2), dir_excl : unpack(0), dir_sharers : (unpack(0)) |
        (((Bit#(4))'(4'h1)) << (((x_17).cidx)[1:0]))}).dir_st,
        mesi_dir_sharers : (((Struct15 {dir_st : (Bit#(3))'(3'h2), dir_excl :
        unpack(0), dir_sharers : (unpack(0)) | (((Bit#(4))'(4'h1)) <<
        (((x_17).cidx)[1:0]))}).dir_st) == ((Bit#(3))'(3'h2)) ? ((Struct15
        {dir_st : (Bit#(3))'(3'h2), dir_excl : unpack(0), dir_sharers :
        (unpack(0)) | (((Bit#(4))'(4'h1)) <<
        (((x_17).cidx)[1:0]))}).dir_sharers) : (((Bit#(4))'(4'h1)) <<
        ((Struct15 {dir_st : (Bit#(3))'(3'h2), dir_excl : unpack(0),
        dir_sharers : (unpack(0)) | (((Bit#(4))'(4'h1)) <<
        (((x_17).cidx)[1:0]))}).dir_excl)))}, value_write :
        (x_20).value_write, value : (x_20).value, may_victim :
        (x_20).may_victim, reps : (x_20).reps});
        Struct16 x_22 = (Struct16 {addr : (x_21).addr, info_write :
        (Bool)'(True), info_hit : (x_21).info_hit, info_way :
        (x_21).info_way, edir_hit : (x_21).edir_hit, edir_way :
        (x_21).edir_way, edir_slot : (x_21).edir_slot, info : Struct10
        {mesi_owned : ((x_21).info).mesi_owned, mesi_status :
        (Bit#(3))'(3'h2), mesi_dir_st : ((x_21).info).mesi_dir_st,
        mesi_dir_sharers : ((x_21).info).mesi_dir_sharers}, value_write :
        (x_21).value_write, value : (x_21).value, may_victim :
        (x_21).may_victim, reps : (x_21).reps});
        Struct16 x_23 = (Struct16 {addr : (x_22).addr, info_write :
        (Bool)'(True), info_hit : (x_22).info_hit, info_way :
        (x_22).info_way, edir_hit : (x_22).edir_hit, edir_way :
        (x_22).edir_way, edir_slot : (x_22).edir_slot, info : Struct10
        {mesi_owned : (Bool)'(False), mesi_status :
        ((x_22).info).mesi_status, mesi_dir_st : ((x_22).info).mesi_dir_st,
        mesi_dir_sharers : ((x_22).info).mesi_dir_sharers}, value_write :
        (x_22).value_write, value : (x_22).value, may_victim :
        (x_22).may_victim, reps : (x_22).reps});
        Struct16 x_24 = (Struct16 {addr : (x_23).addr, info_write :
        (x_23).info_write, info_hit : (x_23).info_hit, info_way :
        (x_23).info_way, edir_hit : (x_23).edir_hit, edir_way :
        (x_23).edir_way, edir_slot : (x_23).edir_slot, info : (x_23).info,
        value_write : (Bool)'(True), value : ((x_17).msg).value, may_victim :
        (x_23).may_victim, reps :
        (x_23).reps});
        let x_27 = ?;
        if ((x_8).valid) begin
            let x_25 <- victims__00__setVictim(Struct17 {victim_idx :
            (x_8).data, victim_info : (x_24).info, victim_value :
            ((x_24).value_write ? ((x_24).value) : (x_9))});
            x_27 = x_9;
        end else begin
            let x_26 <- cache__00__valueRsLineRq(x_24);
            x_27 = x_26;
        end
        let x_28 <- releaseMSHR_00(x_4);
        Struct18 x_29 = (Struct18 {enq_type : (((x_19)[3:2]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : ((((x_19)[3:2]) ==
        ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : (x_19)[1:0], enq_msg : Struct1 {id : (Bit#(6))'(6'h6),
        type_ : (Bool)'(True), addr : (x_18).addr, value :
        ((x_17).msg).value}});
        let x_30 <- makeEnq_parentChildren00(x_29);
    endrule

    rule rule_exec_00_12;
        let x_0 <- deq_fifoL2E_00();
        Struct6 x_1 = ((x_0).lr_ir_pp);
        Bit#(4) x_2 = ((x_1).ir_msg_from);
        Struct1 x_3 = ((x_1).ir_msg);
        Bit#(3) x_4 = ((x_1).ir_mshr_id);
        Bool x_5 = ((x_1).ir_is_rs_rel);
        when (! (x_5), noAction);
        Struct9 x_6 = ((x_0).lr_ir);
        Struct10 x_7 = ((x_6).info);
        Struct5 x_8 = ((x_1).ir_by_victim);
        Vector#(4, Bit#(64)) x_9 = ((x_0).lr_value);
        let x_10 <- getMSHR_00(x_4);
        let x_11 <- getMSHRRq_00(x_4);
        Struct1 x_12 = (unpack(0));
        Vector#(4, Bit#(64)) x_13 = (unpack(0));
        Bool x_14 = ((x_7).mesi_owned);
        Bit#(3) x_15 = ((x_7).mesi_status);
        Struct15 x_16 = (Struct15 {dir_st : (((x_7).mesi_dir_st) ==
        ((Bit#(3))'(3'h0)) ? ((Bit#(3))'(3'h1)) : ((x_7).mesi_dir_st)),
        dir_excl : ((((x_7).mesi_dir_sharers)[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        ((((((x_7).mesi_dir_sharers)[3:1])[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        (((((((x_7).mesi_dir_sharers)[3:1])[2:1])[0:0]) == ((Bit#(1))'(1'h1))
        ? ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        ((((((((x_7).mesi_dir_sharers)[3:1])[2:1])[1:1])[0:0]) ==
        ((Bit#(1))'(1'h1)) ? ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        (unpack(0))))))))))))), dir_sharers : (x_7).mesi_dir_sharers});
        when ((x_2) == ({((Bit#(2))'(2'h2)),((Bit#(2))'(2'h0))}),
        noAction);
        when (((x_3).id) == ((Bit#(6))'(6'hb)), noAction);
        when ((x_10).m_rsb, noAction);
        when (((x_11).type_) == ((Bool)'(False)), noAction);
        when (((x_11).id) == ((Bit#(6))'(6'ha)), noAction);
        when ((x_10).m_rsb, noAction);
        when ((x_3).type_, noAction);
        when ((((x_16).dir_st) == ((Bit#(3))'(3'h1))) || ((((x_16).dir_st) ==
        ((Bit#(3))'(3'h2))) && (((x_16).dir_sharers) == (((Bit#(4))'(4'h1))
        << (({((Bit#(2))'(2'h2)),(((x_10).m_qidx)[1:0])})[1:0])))),
        noAction);
        Struct1 x_17 = (x_3);
        Struct1 x_18 = (x_11);
        Bit#(4) x_19 = ({((Bit#(2))'(2'h2)),(((x_10).m_qidx)[1:0])});
        Struct16 x_20 = (Struct16 {addr : (x_3).addr, info_write :
        (Bool)'(False), info_hit : (x_6).info_hit, info_way : (x_6).info_way,
        edir_hit : (x_6).edir_hit, edir_way : (x_6).edir_way, edir_slot :
        (x_6).edir_slot, info : (x_6).info, value_write : (Bool)'(False),
        value : unpack(0), may_victim : (x_6).may_victim, reps :
        (x_6).reps});
        Struct16 x_21 = (Struct16 {addr : (x_20).addr, info_write :
        (Bool)'(True), info_hit : (x_20).info_hit, info_way :
        (x_20).info_way, edir_hit : (x_20).edir_hit, edir_way :
        (x_20).edir_way, edir_slot : (x_20).edir_slot, info : Struct10
        {mesi_owned : ((x_20).info).mesi_owned, mesi_status :
        ((x_20).info).mesi_status, mesi_dir_st : (Struct15 {dir_st :
        (Bit#(3))'(3'h4), dir_excl : (x_19)[1:0], dir_sharers :
        unpack(0)}).dir_st, mesi_dir_sharers : (((Struct15 {dir_st :
        (Bit#(3))'(3'h4), dir_excl : (x_19)[1:0], dir_sharers :
        unpack(0)}).dir_st) == ((Bit#(3))'(3'h2)) ? ((Struct15 {dir_st :
        (Bit#(3))'(3'h4), dir_excl : (x_19)[1:0], dir_sharers :
        unpack(0)}).dir_sharers) : (((Bit#(4))'(4'h1)) << ((Struct15 {dir_st
        : (Bit#(3))'(3'h4), dir_excl : (x_19)[1:0], dir_sharers :
        unpack(0)}).dir_excl)))}, value_write : (x_20).value_write, value :
        (x_20).value, may_victim : (x_20).may_victim, reps :
        (x_20).reps});
        Struct16 x_22 = (Struct16 {addr : (x_21).addr, info_write :
        (Bool)'(True), info_hit : (x_21).info_hit, info_way :
        (x_21).info_way, edir_hit : (x_21).edir_hit, edir_way :
        (x_21).edir_way, edir_slot : (x_21).edir_slot, info : Struct10
        {mesi_owned : ((x_21).info).mesi_owned, mesi_status :
        (Bit#(3))'(3'h1), mesi_dir_st : ((x_21).info).mesi_dir_st,
        mesi_dir_sharers : ((x_21).info).mesi_dir_sharers}, value_write :
        (x_21).value_write, value : (x_21).value, may_victim :
        (x_21).may_victim, reps : (x_21).reps});
        Struct16 x_23 = (Struct16 {addr : (x_22).addr, info_write :
        (Bool)'(True), info_hit : (x_22).info_hit, info_way :
        (x_22).info_way, edir_hit : (x_22).edir_hit, edir_way :
        (x_22).edir_way, edir_slot : (x_22).edir_slot, info : Struct10
        {mesi_owned : (Bool)'(False), mesi_status :
        ((x_22).info).mesi_status, mesi_dir_st : ((x_22).info).mesi_dir_st,
        mesi_dir_sharers : ((x_22).info).mesi_dir_sharers}, value_write :
        (x_22).value_write, value : (x_22).value, may_victim :
        (x_22).may_victim, reps :
        (x_22).reps});
        let x_26 = ?;
        if ((x_8).valid) begin
            let x_24 <- victims__00__setVictim(Struct17 {victim_idx :
            (x_8).data, victim_info : (x_23).info, victim_value :
            ((x_23).value_write ? ((x_23).value) : (x_9))});
            x_26 = x_9;
        end else begin
            let x_25 <- cache__00__valueRsLineRq(x_23);
            x_26 = x_25;
        end
        let x_27 <- releaseMSHR_00(x_4);
        Struct18 x_28 = (Struct18 {enq_type : (((x_19)[3:2]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : ((((x_19)[3:2]) ==
        ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : (x_19)[1:0], enq_msg : Struct1 {id : (Bit#(6))'(6'hb),
        type_ : (Bool)'(True), addr : (x_17).addr, value : unpack(0)}});
        let x_29 <- makeEnq_parentChildren00(x_28);
    endrule

    rule rule_exec_00_13;
        let x_0 <- deq_fifoL2E_00();
        Struct6 x_1 = ((x_0).lr_ir_pp);
        Bit#(4) x_2 = ((x_1).ir_msg_from);
        Struct1 x_3 = ((x_1).ir_msg);
        Bit#(3) x_4 = ((x_1).ir_mshr_id);
        Bool x_5 = ((x_1).ir_is_rs_rel);
        when (! (x_5), noAction);
        Struct9 x_6 = ((x_0).lr_ir);
        Struct10 x_7 = ((x_6).info);
        Struct5 x_8 = ((x_1).ir_by_victim);
        Vector#(4, Bit#(64)) x_9 = ((x_0).lr_value);
        let x_10 <- getMSHR_00(x_4);
        let x_11 <- getMSHRRq_00(x_4);
        Struct1 x_12 = (unpack(0));
        Vector#(4, Bit#(64)) x_13 = (unpack(0));
        Bool x_14 = ((x_7).mesi_owned);
        Bit#(3) x_15 = ((x_7).mesi_status);
        Struct15 x_16 = (Struct15 {dir_st : (((x_7).mesi_dir_st) ==
        ((Bit#(3))'(3'h0)) ? ((Bit#(3))'(3'h1)) : ((x_7).mesi_dir_st)),
        dir_excl : ((((x_7).mesi_dir_sharers)[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        ((((((x_7).mesi_dir_sharers)[3:1])[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        (((((((x_7).mesi_dir_sharers)[3:1])[2:1])[0:0]) == ((Bit#(1))'(1'h1))
        ? ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        ((((((((x_7).mesi_dir_sharers)[3:1])[2:1])[1:1])[0:0]) ==
        ((Bit#(1))'(1'h1)) ? ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        (unpack(0))))))))))))), dir_sharers : (x_7).mesi_dir_sharers});
        when ((x_2) == ({((Bit#(2))'(2'h2)),((Bit#(2))'(2'h0))}),
        noAction);
        when (((x_3).id) == ((Bit#(6))'(6'hb)), noAction);
        when ((x_10).m_rsb, noAction);
        when (((x_11).type_) == ((Bool)'(False)), noAction);
        when (((x_11).id) == ((Bit#(6))'(6'ha)), noAction);
        when ((x_10).m_rsb, noAction);
        when ((x_3).type_, noAction);
        when (((Bool)'(True)) && (((Bool)'(True)) && (((Bool)'(True)) && ((!
        ((((x_16).dir_sharers) & (~(((Bit#(4))'(4'h1)) <<
        (({((Bit#(2))'(2'h2)),(((x_10).m_qidx)[1:0])})[1:0])))) ==
        ((Bit#(4))'(4'h0)))) && (((x_16).dir_st) == ((Bit#(3))'(3'h2)))))),
        noAction);
        Struct1 x_17 = (x_11);
        Bit#(4) x_18 = ({((Bit#(2))'(2'h2)),(((x_10).m_qidx)[1:0])});
        Struct16 x_19 = (Struct16 {addr : (x_3).addr, info_write :
        (Bool)'(False), info_hit : (x_6).info_hit, info_way : (x_6).info_way,
        edir_hit : (x_6).edir_hit, edir_way : (x_6).edir_way, edir_slot :
        (x_6).edir_slot, info : (x_6).info, value_write : (Bool)'(False),
        value : unpack(0), may_victim : (x_6).may_victim, reps :
        (x_6).reps});
        Struct16 x_20 = (Struct16 {addr : (x_19).addr, info_write :
        (Bool)'(True), info_hit : (x_19).info_hit, info_way :
        (x_19).info_way, edir_hit : (x_19).edir_hit, edir_way :
        (x_19).edir_way, edir_slot : (x_19).edir_slot, info : Struct10
        {mesi_owned : (Bool)'(True), mesi_status : ((x_19).info).mesi_status,
        mesi_dir_st : ((x_19).info).mesi_dir_st, mesi_dir_sharers :
        ((x_19).info).mesi_dir_sharers}, value_write : (x_19).value_write,
        value : (x_19).value, may_victim : (x_19).may_victim, reps :
        (x_19).reps});
        let x_23 = ?;
        if ((x_8).valid) begin
            let x_21 <- victims__00__setVictim(Struct17 {victim_idx :
            (x_8).data, victim_info : (x_20).info, victim_value :
            ((x_20).value_write ? ((x_20).value) : (x_9))});
            x_23 = x_9;
        end else begin
            let x_22 <- cache__00__valueRsLineRq(x_20);
            x_23 = x_22;
        end
        let x_24 <- transferUpDown_00(Struct23 {r_id : x_4, r_dl_rss_from :
        ((x_16).dir_sharers) & (~(((Bit#(4))'(4'h1)) << ((x_18)[1:0])))});
        let x_25 <- broadcast_parentChildren00(Struct21 {cs_inds :
        ((x_16).dir_sharers) & (~(((Bit#(4))'(4'h1)) << ((x_18)[1:0]))),
        cs_msg : Struct1 {id : (Bit#(6))'(6'hc), type_ : (Bool)'(False), addr
        : (x_17).addr, value : unpack(0)}});
    endrule

    rule rule_exec_00_161;
        let x_0 <- deq_fifoL2E_00();
        Struct6 x_1 = ((x_0).lr_ir_pp);
        Bit#(4) x_2 = ((x_1).ir_msg_from);
        Struct1 x_3 = ((x_1).ir_msg);
        Bit#(3) x_4 = ((x_1).ir_mshr_id);
        Bool x_5 = ((x_1).ir_is_rs_rel);
        when (x_5, noAction);
        Struct9 x_6 = ((x_0).lr_ir);
        Struct10 x_7 = ((x_6).info);
        Struct5 x_8 = ((x_1).ir_by_victim);
        Vector#(4, Bit#(64)) x_9 = ((x_0).lr_value);
        let x_10 <- getMSHR_00(x_4);
        let x_11 <- getMSHRRq_00(x_4);
        let x_12 <- getMSHRFirstRs_00(x_4);
        Vector#(4, Bit#(64)) x_13 = (unpack(0));
        Bool x_14 = ((x_7).mesi_owned);
        Bit#(3) x_15 = ((x_7).mesi_status);
        Struct15 x_16 = (Struct15 {dir_st : (((x_7).mesi_dir_st) ==
        ((Bit#(3))'(3'h0)) ? ((Bit#(3))'(3'h1)) : ((x_7).mesi_dir_st)),
        dir_excl : ((((x_7).mesi_dir_sharers)[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        ((((((x_7).mesi_dir_sharers)[3:1])[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        (((((((x_7).mesi_dir_sharers)[3:1])[2:1])[0:0]) == ((Bit#(1))'(1'h1))
        ? ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        ((((((((x_7).mesi_dir_sharers)[3:1])[2:1])[1:1])[0:0]) ==
        ((Bit#(1))'(1'h1)) ? ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        (unpack(0))))))))))))), dir_sharers : (x_7).mesi_dir_sharers});
        when ((x_10).m_rsb, noAction);
        when (((x_11).type_) == ((Bool)'(False)), noAction);
        when (((x_11).id) == ((Bit#(6))'(6'ha)), noAction);
        when ((Bool)'(True), noAction);
        Struct1 x_17 = (x_11);
        Bit#(4) x_18 = ((x_10).m_qidx);
        Struct16 x_19 = (Struct16 {addr : (x_3).addr, info_write :
        (Bool)'(False), info_hit : (x_6).info_hit, info_way : (x_6).info_way,
        edir_hit : (x_6).edir_hit, edir_way : (x_6).edir_way, edir_slot :
        (x_6).edir_slot, info : (x_6).info, value_write : (Bool)'(False),
        value : unpack(0), may_victim : (x_6).may_victim, reps :
        (x_6).reps});
        Struct16 x_20 = (Struct16 {addr : (x_19).addr, info_write :
        (Bool)'(True), info_hit : (x_19).info_hit, info_way :
        (x_19).info_way, edir_hit : (x_19).edir_hit, edir_way :
        (x_19).edir_way, edir_slot : (x_19).edir_slot, info : Struct10
        {mesi_owned : ((x_19).info).mesi_owned, mesi_status :
        ((x_19).info).mesi_status, mesi_dir_st : (Struct15 {dir_st :
        (Bit#(3))'(3'h4), dir_excl : (x_18)[1:0], dir_sharers :
        unpack(0)}).dir_st, mesi_dir_sharers : (((Struct15 {dir_st :
        (Bit#(3))'(3'h4), dir_excl : (x_18)[1:0], dir_sharers :
        unpack(0)}).dir_st) == ((Bit#(3))'(3'h2)) ? ((Struct15 {dir_st :
        (Bit#(3))'(3'h4), dir_excl : (x_18)[1:0], dir_sharers :
        unpack(0)}).dir_sharers) : (((Bit#(4))'(4'h1)) << ((Struct15 {dir_st
        : (Bit#(3))'(3'h4), dir_excl : (x_18)[1:0], dir_sharers :
        unpack(0)}).dir_excl)))}, value_write : (x_19).value_write, value :
        (x_19).value, may_victim : (x_19).may_victim, reps :
        (x_19).reps});
        Struct16 x_21 = (Struct16 {addr : (x_20).addr, info_write :
        (Bool)'(True), info_hit : (x_20).info_hit, info_way :
        (x_20).info_way, edir_hit : (x_20).edir_hit, edir_way :
        (x_20).edir_way, edir_slot : (x_20).edir_slot, info : Struct10
        {mesi_owned : ((x_20).info).mesi_owned, mesi_status :
        (Bit#(3))'(3'h1), mesi_dir_st : ((x_20).info).mesi_dir_st,
        mesi_dir_sharers : ((x_20).info).mesi_dir_sharers}, value_write :
        (x_20).value_write, value : (x_20).value, may_victim :
        (x_20).may_victim, reps : (x_20).reps});
        Struct16 x_22 = (Struct16 {addr : (x_21).addr, info_write :
        (Bool)'(True), info_hit : (x_21).info_hit, info_way :
        (x_21).info_way, edir_hit : (x_21).edir_hit, edir_way :
        (x_21).edir_way, edir_slot : (x_21).edir_slot, info : Struct10
        {mesi_owned : (Bool)'(False), mesi_status :
        ((x_21).info).mesi_status, mesi_dir_st : ((x_21).info).mesi_dir_st,
        mesi_dir_sharers : ((x_21).info).mesi_dir_sharers}, value_write :
        (x_21).value_write, value : (x_21).value, may_victim :
        (x_21).may_victim, reps :
        (x_21).reps});
        let x_25 = ?;
        if ((x_8).valid) begin
            let x_23 <- victims__00__setVictim(Struct17 {victim_idx :
            (x_8).data, victim_info : (x_22).info, victim_value :
            ((x_22).value_write ? ((x_22).value) : (x_9))});
            x_25 = x_9;
        end else begin
            let x_24 <- cache__00__valueRsLineRq(x_22);
            x_25 = x_24;
        end
        let x_26 <- releaseMSHR_00(x_4);
        Struct18 x_27 = (Struct18 {enq_type : (((x_18)[3:2]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : ((((x_18)[3:2]) ==
        ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : (x_18)[1:0], enq_msg : Struct1 {id : (Bit#(6))'(6'hb),
        type_ : (Bool)'(True), addr : (x_17).addr, value : unpack(0)}});
        let x_28 <- makeEnq_parentChildren00(x_27);
    endrule

    rule rule_exec_00_170;
        let x_0 <- deq_fifoL2E_00();
        Struct6 x_1 = ((x_0).lr_ir_pp);
        Bit#(4) x_2 = ((x_1).ir_msg_from);
        Struct1 x_3 = ((x_1).ir_msg);
        Bit#(3) x_4 = ((x_1).ir_mshr_id);
        Bool x_5 = ((x_1).ir_is_rs_rel);
        when (! (x_5), noAction);
        Struct9 x_6 = ((x_0).lr_ir);
        Struct10 x_7 = ((x_6).info);
        Struct5 x_8 = ((x_1).ir_by_victim);
        Vector#(4, Bit#(64)) x_9 = ((x_0).lr_value);
        let x_10 <- getMSHR_00(x_4);
        let x_11 <- getMSHRRq_00(x_4);
        Struct1 x_12 = (unpack(0));
        Vector#(4, Bit#(64)) x_13 = (unpack(0));
        Bool x_14 = ((x_7).mesi_owned);
        Bit#(3) x_15 = ((x_7).mesi_status);
        Struct15 x_16 = (Struct15 {dir_st : (((x_7).mesi_dir_st) ==
        ((Bit#(3))'(3'h0)) ? ((Bit#(3))'(3'h1)) : ((x_7).mesi_dir_st)),
        dir_excl : ((((x_7).mesi_dir_sharers)[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        ((((((x_7).mesi_dir_sharers)[3:1])[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        (((((((x_7).mesi_dir_sharers)[3:1])[2:1])[0:0]) == ((Bit#(1))'(1'h1))
        ? ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        ((((((((x_7).mesi_dir_sharers)[3:1])[2:1])[1:1])[0:0]) ==
        ((Bit#(1))'(1'h1)) ? ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        (unpack(0))))))))))))), dir_sharers : (x_7).mesi_dir_sharers});
        when ((x_2) == ((Bit#(4))'(4'h8)), noAction);
        when (((x_3).id) == ((Bit#(6))'(6'hc)), noAction);
        when (! ((x_3).type_), noAction);
        when (((x_16).dir_st) == ((Bit#(3))'(3'h1)), noAction);
        Struct1 x_17 = (x_3);
        Struct16 x_18 = (Struct16 {addr : (x_3).addr, info_write :
        (Bool)'(False), info_hit : (x_6).info_hit, info_way : (x_6).info_way,
        edir_hit : (x_6).edir_hit, edir_way : (x_6).edir_way, edir_slot :
        (x_6).edir_slot, info : (x_6).info, value_write : (Bool)'(False),
        value : unpack(0), may_victim : (x_6).may_victim, reps :
        (x_6).reps});
        Struct16 x_19 = (Struct16 {addr : (x_18).addr, info_write :
        (Bool)'(True), info_hit : (x_18).info_hit, info_way :
        (x_18).info_way, edir_hit : (x_18).edir_hit, edir_way :
        (x_18).edir_way, edir_slot : (x_18).edir_slot, info : Struct10
        {mesi_owned : ((x_18).info).mesi_owned, mesi_status :
        (Bit#(3))'(3'h1), mesi_dir_st : ((x_18).info).mesi_dir_st,
        mesi_dir_sharers : ((x_18).info).mesi_dir_sharers}, value_write :
        (x_18).value_write, value : (x_18).value, may_victim :
        (x_18).may_victim, reps : (x_18).reps});
        Struct16 x_20 = (Struct16 {addr : (x_19).addr, info_write :
        (Bool)'(True), info_hit : (x_19).info_hit, info_way :
        (x_19).info_way, edir_hit : (x_19).edir_hit, edir_way :
        (x_19).edir_way, edir_slot : (x_19).edir_slot, info : Struct10
        {mesi_owned : (Bool)'(False), mesi_status :
        ((x_19).info).mesi_status, mesi_dir_st : ((x_19).info).mesi_dir_st,
        mesi_dir_sharers : ((x_19).info).mesi_dir_sharers}, value_write :
        (x_19).value_write, value : (x_19).value, may_victim :
        (x_19).may_victim, reps :
        (x_19).reps});
        let x_23 = ?;
        if ((x_8).valid) begin
            let x_21 <- victims__00__setVictim(Struct17 {victim_idx :
            (x_8).data, victim_info : (x_20).info, victim_value :
            ((x_20).value_write ? ((x_20).value) : (x_9))});
            x_23 = x_9;
        end else begin
            let x_22 <- cache__00__valueRsLineRq(x_20);
            x_23 = x_22;
        end
        Struct18 x_24 = (Struct18 {enq_type : ((((Bit#(4))'(4'h4))[3:2]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : (((((Bit#(4))'(4'h4))[3:2])
        == ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : ((Bit#(4))'(4'h4))[1:0], enq_msg : Struct1 {id :
        (Bit#(6))'(6'hd), type_ : (Bool)'(True), addr : (x_17).addr, value :
        unpack(0)}});
        let x_25 <- makeEnq_parentChildren00(x_24);
        let x_26 <- releaseMSHR_00(x_4);
    endrule

    rule rule_exec_00_171;
        let x_0 <- deq_fifoL2E_00();
        Struct6 x_1 = ((x_0).lr_ir_pp);
        Bit#(4) x_2 = ((x_1).ir_msg_from);
        Struct1 x_3 = ((x_1).ir_msg);
        Bit#(3) x_4 = ((x_1).ir_mshr_id);
        Bool x_5 = ((x_1).ir_is_rs_rel);
        when (! (x_5), noAction);
        Struct9 x_6 = ((x_0).lr_ir);
        Struct10 x_7 = ((x_6).info);
        Struct5 x_8 = ((x_1).ir_by_victim);
        Vector#(4, Bit#(64)) x_9 = ((x_0).lr_value);
        let x_10 <- getMSHR_00(x_4);
        let x_11 <- getMSHRRq_00(x_4);
        Struct1 x_12 = (unpack(0));
        Vector#(4, Bit#(64)) x_13 = (unpack(0));
        Bool x_14 = ((x_7).mesi_owned);
        Bit#(3) x_15 = ((x_7).mesi_status);
        Struct15 x_16 = (Struct15 {dir_st : (((x_7).mesi_dir_st) ==
        ((Bit#(3))'(3'h0)) ? ((Bit#(3))'(3'h1)) : ((x_7).mesi_dir_st)),
        dir_excl : ((((x_7).mesi_dir_sharers)[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        ((((((x_7).mesi_dir_sharers)[3:1])[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        (((((((x_7).mesi_dir_sharers)[3:1])[2:1])[0:0]) == ((Bit#(1))'(1'h1))
        ? ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        ((((((((x_7).mesi_dir_sharers)[3:1])[2:1])[1:1])[0:0]) ==
        ((Bit#(1))'(1'h1)) ? ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        (unpack(0))))))))))))), dir_sharers : (x_7).mesi_dir_sharers});
        when ((x_2) == ((Bit#(4))'(4'h8)), noAction);
        when (((x_3).id) == ((Bit#(6))'(6'he)), noAction);
        when (! ((x_3).type_), noAction);
        when ((! ((x_15) < ((Bit#(3))'(3'h3)))) && (((x_16).dir_st) ==
        ((Bit#(3))'(3'h1))), noAction);
        Struct1 x_17 = (x_3);
        Struct16 x_18 = (Struct16 {addr : (x_3).addr, info_write :
        (Bool)'(False), info_hit : (x_6).info_hit, info_way : (x_6).info_way,
        edir_hit : (x_6).edir_hit, edir_way : (x_6).edir_way, edir_slot :
        (x_6).edir_slot, info : (x_6).info, value_write : (Bool)'(False),
        value : unpack(0), may_victim : (x_6).may_victim, reps :
        (x_6).reps});
        Struct16 x_19 = (Struct16 {addr : (x_18).addr, info_write :
        (Bool)'(True), info_hit : (x_18).info_hit, info_way :
        (x_18).info_way, edir_hit : (x_18).edir_hit, edir_way :
        (x_18).edir_way, edir_slot : (x_18).edir_slot, info : Struct10
        {mesi_owned : ((x_18).info).mesi_owned, mesi_status :
        (Bit#(3))'(3'h1), mesi_dir_st : ((x_18).info).mesi_dir_st,
        mesi_dir_sharers : ((x_18).info).mesi_dir_sharers}, value_write :
        (x_18).value_write, value : (x_18).value, may_victim :
        (x_18).may_victim, reps : (x_18).reps});
        Struct16 x_20 = (Struct16 {addr : (x_19).addr, info_write :
        (Bool)'(True), info_hit : (x_19).info_hit, info_way :
        (x_19).info_way, edir_hit : (x_19).edir_hit, edir_way :
        (x_19).edir_way, edir_slot : (x_19).edir_slot, info : Struct10
        {mesi_owned : (Bool)'(False), mesi_status :
        ((x_19).info).mesi_status, mesi_dir_st : ((x_19).info).mesi_dir_st,
        mesi_dir_sharers : ((x_19).info).mesi_dir_sharers}, value_write :
        (x_19).value_write, value : (x_19).value, may_victim :
        (x_19).may_victim, reps :
        (x_19).reps});
        let x_23 = ?;
        if ((x_8).valid) begin
            let x_21 <- victims__00__setVictim(Struct17 {victim_idx :
            (x_8).data, victim_info : (x_20).info, victim_value :
            ((x_20).value_write ? ((x_20).value) : (x_9))});
            x_23 = x_9;
        end else begin
            let x_22 <- cache__00__valueRsLineRq(x_20);
            x_23 = x_22;
        end
        Struct18 x_24 = (Struct18 {enq_type : ((((Bit#(4))'(4'h4))[3:2]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : (((((Bit#(4))'(4'h4))[3:2])
        == ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : ((Bit#(4))'(4'h4))[1:0], enq_msg : Struct1 {id :
        (Bit#(6))'(6'hf), type_ : (Bool)'(True), addr : (x_17).addr, value :
        unpack(0)}});
        let x_25 <- makeEnq_parentChildren00(x_24);
        let x_26 <- releaseMSHR_00(x_4);
    endrule

    rule rule_exec_00_190;
        let x_0 <- deq_fifoL2E_00();
        Struct6 x_1 = ((x_0).lr_ir_pp);
        Bit#(4) x_2 = ((x_1).ir_msg_from);
        Struct1 x_3 = ((x_1).ir_msg);
        Bit#(3) x_4 = ((x_1).ir_mshr_id);
        Bool x_5 = ((x_1).ir_is_rs_rel);
        when (! (x_5), noAction);
        Struct9 x_6 = ((x_0).lr_ir);
        Struct10 x_7 = ((x_6).info);
        Struct5 x_8 = ((x_1).ir_by_victim);
        Vector#(4, Bit#(64)) x_9 = ((x_0).lr_value);
        let x_10 <- getMSHR_00(x_4);
        let x_11 <- getMSHRRq_00(x_4);
        Struct1 x_12 = (unpack(0));
        Vector#(4, Bit#(64)) x_13 = (unpack(0));
        Bool x_14 = ((x_7).mesi_owned);
        Bit#(3) x_15 = ((x_7).mesi_status);
        Struct15 x_16 = (Struct15 {dir_st : (((x_7).mesi_dir_st) ==
        ((Bit#(3))'(3'h0)) ? ((Bit#(3))'(3'h1)) : ((x_7).mesi_dir_st)),
        dir_excl : ((((x_7).mesi_dir_sharers)[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        ((((((x_7).mesi_dir_sharers)[3:1])[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        (((((((x_7).mesi_dir_sharers)[3:1])[2:1])[0:0]) == ((Bit#(1))'(1'h1))
        ? ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        ((((((((x_7).mesi_dir_sharers)[3:1])[2:1])[1:1])[0:0]) ==
        ((Bit#(1))'(1'h1)) ? ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        (unpack(0))))))))))))), dir_sharers : (x_7).mesi_dir_sharers});
        when ((x_2) == ((Bit#(4))'(4'h8)), noAction);
        when (((x_3).id) == ((Bit#(6))'(6'hc)), noAction);
        when (! ((x_3).type_), noAction);
        when (((Bool)'(True)) && (((Bool)'(True)) && (((x_16).dir_st) ==
        ((Bit#(3))'(3'h2)))), noAction);
        Struct1 x_17 = (x_3);
        Struct16 x_18 = (Struct16 {addr : (x_3).addr, info_write :
        (Bool)'(False), info_hit : (x_6).info_hit, info_way : (x_6).info_way,
        edir_hit : (x_6).edir_hit, edir_way : (x_6).edir_way, edir_slot :
        (x_6).edir_slot, info : (x_6).info, value_write : (Bool)'(False),
        value : unpack(0), may_victim : (x_6).may_victim, reps :
        (x_6).reps});
        let x_20 = ?;
        if ((x_8).valid) begin
            x_20 = x_9;
        end else begin
            let x_19 <- cache__00__valueRsLineRq(unpack(0));
            x_20 = x_19;
        end
        let x_21 <- registerDL_00(Struct20 {r_id : x_4, r_dl_rss_from :
        (x_16).dir_sharers, r_dl_rsb : (Bool)'(True), r_dl_rsbTo :
        (Bit#(4))'(4'h4)});
        let x_22 <- broadcast_parentChildren00(Struct21 {cs_inds :
        (x_16).dir_sharers, cs_msg : Struct1 {id : (Bit#(6))'(6'hc), type_ :
        (Bool)'(False), addr : (x_17).addr, value : unpack(0)}});
    endrule

    rule rule_exec_00_191;
        let x_0 <- deq_fifoL2E_00();
        Struct6 x_1 = ((x_0).lr_ir_pp);
        Bit#(4) x_2 = ((x_1).ir_msg_from);
        Struct1 x_3 = ((x_1).ir_msg);
        Bit#(3) x_4 = ((x_1).ir_mshr_id);
        Bool x_5 = ((x_1).ir_is_rs_rel);
        when (! (x_5), noAction);
        Struct9 x_6 = ((x_0).lr_ir);
        Struct10 x_7 = ((x_6).info);
        Struct5 x_8 = ((x_1).ir_by_victim);
        Vector#(4, Bit#(64)) x_9 = ((x_0).lr_value);
        let x_10 <- getMSHR_00(x_4);
        let x_11 <- getMSHRRq_00(x_4);
        Struct1 x_12 = (unpack(0));
        Vector#(4, Bit#(64)) x_13 = (unpack(0));
        Bool x_14 = ((x_7).mesi_owned);
        Bit#(3) x_15 = ((x_7).mesi_status);
        Struct15 x_16 = (Struct15 {dir_st : (((x_7).mesi_dir_st) ==
        ((Bit#(3))'(3'h0)) ? ((Bit#(3))'(3'h1)) : ((x_7).mesi_dir_st)),
        dir_excl : ((((x_7).mesi_dir_sharers)[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        ((((((x_7).mesi_dir_sharers)[3:1])[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        (((((((x_7).mesi_dir_sharers)[3:1])[2:1])[0:0]) == ((Bit#(1))'(1'h1))
        ? ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        ((((((((x_7).mesi_dir_sharers)[3:1])[2:1])[1:1])[0:0]) ==
        ((Bit#(1))'(1'h1)) ? ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        (unpack(0))))))))))))), dir_sharers : (x_7).mesi_dir_sharers});
        when ((x_2) == ((Bit#(4))'(4'h8)), noAction);
        when (((x_3).id) == ((Bit#(6))'(6'he)), noAction);
        when (! ((x_3).type_), noAction);
        when (((Bool)'(True)) && ((! (((x_16).dir_st) < ((Bit#(3))'(3'h3))))
        && (! (((Bit#(3))'(3'h4)) < ((x_16).dir_st)))), noAction);
        Struct1 x_17 = (x_3);
        Struct16 x_18 = (Struct16 {addr : (x_3).addr, info_write :
        (Bool)'(False), info_hit : (x_6).info_hit, info_way : (x_6).info_way,
        edir_hit : (x_6).edir_hit, edir_way : (x_6).edir_way, edir_slot :
        (x_6).edir_slot, info : (x_6).info, value_write : (Bool)'(False),
        value : unpack(0), may_victim : (x_6).may_victim, reps :
        (x_6).reps});
        let x_20 = ?;
        if ((x_8).valid) begin
            x_20 = x_9;
        end else begin
            let x_19 <- cache__00__valueRsLineRq(unpack(0));
            x_20 = x_19;
        end
        let x_21 <- registerDL_00(Struct20 {r_id : x_4, r_dl_rss_from :
        (unpack(0)) | (((Bit#(4))'(4'h1)) <<
        (({((Bit#(2))'(2'h1)),((x_16).dir_excl)})[1:0])), r_dl_rsb :
        (Bool)'(True), r_dl_rsbTo : (Bit#(4))'(4'h4)});
        Struct18 x_22 = (Struct18 {enq_type :
        ((({((Bit#(2))'(2'h2)),((x_16).dir_excl)})[3:2]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) :
        (((({((Bit#(2))'(2'h2)),((x_16).dir_excl)})[3:2]) ==
        ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : ({((Bit#(2))'(2'h2)),((x_16).dir_excl)})[1:0], enq_msg :
        Struct1 {id : (Bit#(6))'(6'he), type_ : (Bool)'(False), addr :
        (x_17).addr, value : unpack(0)}});
        let x_23 <- makeEnq_parentChildren00(x_22);
    endrule

    rule rule_exec_00_192;
        let x_0 <- deq_fifoL2E_00();
        Struct6 x_1 = ((x_0).lr_ir_pp);
        Bit#(4) x_2 = ((x_1).ir_msg_from);
        Struct1 x_3 = ((x_1).ir_msg);
        Bit#(3) x_4 = ((x_1).ir_mshr_id);
        Bool x_5 = ((x_1).ir_is_rs_rel);
        when (! (x_5), noAction);
        Struct9 x_6 = ((x_0).lr_ir);
        Struct10 x_7 = ((x_6).info);
        Struct5 x_8 = ((x_1).ir_by_victim);
        Vector#(4, Bit#(64)) x_9 = ((x_0).lr_value);
        let x_10 <- getMSHR_00(x_4);
        let x_11 <- getMSHRRq_00(x_4);
        Struct1 x_12 = (unpack(0));
        Vector#(4, Bit#(64)) x_13 = (unpack(0));
        Bool x_14 = ((x_7).mesi_owned);
        Bit#(3) x_15 = ((x_7).mesi_status);
        Struct15 x_16 = (Struct15 {dir_st : (((x_7).mesi_dir_st) ==
        ((Bit#(3))'(3'h0)) ? ((Bit#(3))'(3'h1)) : ((x_7).mesi_dir_st)),
        dir_excl : ((((x_7).mesi_dir_sharers)[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        ((((((x_7).mesi_dir_sharers)[3:1])[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        (((((((x_7).mesi_dir_sharers)[3:1])[2:1])[0:0]) == ((Bit#(1))'(1'h1))
        ? ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        ((((((((x_7).mesi_dir_sharers)[3:1])[2:1])[1:1])[0:0]) ==
        ((Bit#(1))'(1'h1)) ? ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        (unpack(0))))))))))))), dir_sharers : (x_7).mesi_dir_sharers});
        when ((x_2) == ((Bit#(4))'(4'h8)), noAction);
        when (((x_3).id) == ((Bit#(6))'(6'he)), noAction);
        when (! ((x_3).type_), noAction);
        when (((Bool)'(True)) && (((Bool)'(True)) && (((x_16).dir_st) ==
        ((Bit#(3))'(3'h2)))), noAction);
        Struct1 x_17 = (x_3);
        Struct16 x_18 = (Struct16 {addr : (x_3).addr, info_write :
        (Bool)'(False), info_hit : (x_6).info_hit, info_way : (x_6).info_way,
        edir_hit : (x_6).edir_hit, edir_way : (x_6).edir_way, edir_slot :
        (x_6).edir_slot, info : (x_6).info, value_write : (Bool)'(False),
        value : unpack(0), may_victim : (x_6).may_victim, reps :
        (x_6).reps});
        let x_20 = ?;
        if ((x_8).valid) begin
            x_20 = x_9;
        end else begin
            let x_19 <- cache__00__valueRsLineRq(unpack(0));
            x_20 = x_19;
        end
        let x_21 <- registerDL_00(Struct20 {r_id : x_4, r_dl_rss_from :
        (x_16).dir_sharers, r_dl_rsb : (Bool)'(True), r_dl_rsbTo :
        (Bit#(4))'(4'h4)});
        let x_22 <- broadcast_parentChildren00(Struct21 {cs_inds :
        (x_16).dir_sharers, cs_msg : Struct1 {id : (Bit#(6))'(6'hc), type_ :
        (Bool)'(False), addr : (x_17).addr, value : unpack(0)}});
    endrule

    rule rule_exec_00_11010;
        let x_0 <- deq_fifoL2E_00();
        Struct6 x_1 = ((x_0).lr_ir_pp);
        Bit#(4) x_2 = ((x_1).ir_msg_from);
        Struct1 x_3 = ((x_1).ir_msg);
        Bit#(3) x_4 = ((x_1).ir_mshr_id);
        Bool x_5 = ((x_1).ir_is_rs_rel);
        when (x_5, noAction);
        Struct9 x_6 = ((x_0).lr_ir);
        Struct10 x_7 = ((x_6).info);
        Struct5 x_8 = ((x_1).ir_by_victim);
        Vector#(4, Bit#(64)) x_9 = ((x_0).lr_value);
        let x_10 <- getMSHR_00(x_4);
        let x_11 <- getMSHRRq_00(x_4);
        let x_12 <- getMSHRFirstRs_00(x_4);
        Vector#(4, Bit#(64)) x_13 = (unpack(0));
        Bool x_14 = ((x_7).mesi_owned);
        Bit#(3) x_15 = ((x_7).mesi_status);
        Struct15 x_16 = (Struct15 {dir_st : (((x_7).mesi_dir_st) ==
        ((Bit#(3))'(3'h0)) ? ((Bit#(3))'(3'h1)) : ((x_7).mesi_dir_st)),
        dir_excl : ((((x_7).mesi_dir_sharers)[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        ((((((x_7).mesi_dir_sharers)[3:1])[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        (((((((x_7).mesi_dir_sharers)[3:1])[2:1])[0:0]) == ((Bit#(1))'(1'h1))
        ? ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        ((((((((x_7).mesi_dir_sharers)[3:1])[2:1])[1:1])[0:0]) ==
        ((Bit#(1))'(1'h1)) ? ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        (unpack(0))))))))))))), dir_sharers : (x_7).mesi_dir_sharers});
        when ((x_10).m_rsb, noAction);
        when (((x_11).type_) == ((Bool)'(False)), noAction);
        when (((x_11).id) == ((Bit#(6))'(6'hc)), noAction);
        when ((Bool)'(True), noAction);
        Struct1 x_17 = (x_11);
        Bit#(4) x_18 = ((x_10).m_qidx);
        Struct16 x_19 = (Struct16 {addr : (x_3).addr, info_write :
        (Bool)'(False), info_hit : (x_6).info_hit, info_way : (x_6).info_way,
        edir_hit : (x_6).edir_hit, edir_way : (x_6).edir_way, edir_slot :
        (x_6).edir_slot, info : (x_6).info, value_write : (Bool)'(False),
        value : unpack(0), may_victim : (x_6).may_victim, reps :
        (x_6).reps});
        Struct16 x_20 = (Struct16 {addr : (x_19).addr, info_write :
        (Bool)'(True), info_hit : (x_19).info_hit, info_way :
        (x_19).info_way, edir_hit : (x_19).edir_hit, edir_way :
        (x_19).edir_way, edir_slot : (x_19).edir_slot, info : Struct10
        {mesi_owned : ((x_19).info).mesi_owned, mesi_status :
        ((x_19).info).mesi_status, mesi_dir_st : (Struct15 {dir_st :
        (Bit#(3))'(3'h1), dir_excl : unpack(0), dir_sharers :
        unpack(0)}).dir_st, mesi_dir_sharers : (((Struct15 {dir_st :
        (Bit#(3))'(3'h1), dir_excl : unpack(0), dir_sharers :
        unpack(0)}).dir_st) == ((Bit#(3))'(3'h2)) ? ((Struct15 {dir_st :
        (Bit#(3))'(3'h1), dir_excl : unpack(0), dir_sharers :
        unpack(0)}).dir_sharers) : (((Bit#(4))'(4'h1)) << ((Struct15 {dir_st
        : (Bit#(3))'(3'h1), dir_excl : unpack(0), dir_sharers :
        unpack(0)}).dir_excl)))}, value_write : (x_19).value_write, value :
        (x_19).value, may_victim : (x_19).may_victim, reps :
        (x_19).reps});
        Struct16 x_21 = (Struct16 {addr : (x_20).addr, info_write :
        (Bool)'(True), info_hit : (x_20).info_hit, info_way :
        (x_20).info_way, edir_hit : (x_20).edir_hit, edir_way :
        (x_20).edir_way, edir_slot : (x_20).edir_slot, info : Struct10
        {mesi_owned : ((x_20).info).mesi_owned, mesi_status :
        (Bit#(3))'(3'h1), mesi_dir_st : ((x_20).info).mesi_dir_st,
        mesi_dir_sharers : ((x_20).info).mesi_dir_sharers}, value_write :
        (x_20).value_write, value : (x_20).value, may_victim :
        (x_20).may_victim, reps : (x_20).reps});
        Struct16 x_22 = (Struct16 {addr : (x_21).addr, info_write :
        (Bool)'(True), info_hit : (x_21).info_hit, info_way :
        (x_21).info_way, edir_hit : (x_21).edir_hit, edir_way :
        (x_21).edir_way, edir_slot : (x_21).edir_slot, info : Struct10
        {mesi_owned : (Bool)'(False), mesi_status :
        ((x_21).info).mesi_status, mesi_dir_st : ((x_21).info).mesi_dir_st,
        mesi_dir_sharers : ((x_21).info).mesi_dir_sharers}, value_write :
        (x_21).value_write, value : (x_21).value, may_victim :
        (x_21).may_victim, reps :
        (x_21).reps});
        let x_25 = ?;
        if ((x_8).valid) begin
            let x_23 <- victims__00__setVictim(Struct17 {victim_idx :
            (x_8).data, victim_info : (x_22).info, victim_value :
            ((x_22).value_write ? ((x_22).value) : (x_9))});
            x_25 = x_9;
        end else begin
            let x_24 <- cache__00__valueRsLineRq(x_22);
            x_25 = x_24;
        end
        let x_26 <- releaseMSHR_00(x_4);
        Struct18 x_27 = (Struct18 {enq_type : (((x_18)[3:2]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : ((((x_18)[3:2]) ==
        ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : (x_18)[1:0], enq_msg : Struct1 {id : (Bit#(6))'(6'hd),
        type_ : (Bool)'(True), addr : (x_17).addr, value : unpack(0)}});
        let x_28 <- makeEnq_parentChildren00(x_27);
    endrule

    rule rule_exec_00_11011;
        let x_0 <- deq_fifoL2E_00();
        Struct6 x_1 = ((x_0).lr_ir_pp);
        Bit#(4) x_2 = ((x_1).ir_msg_from);
        Struct1 x_3 = ((x_1).ir_msg);
        Bit#(3) x_4 = ((x_1).ir_mshr_id);
        Bool x_5 = ((x_1).ir_is_rs_rel);
        when (x_5, noAction);
        Struct9 x_6 = ((x_0).lr_ir);
        Struct10 x_7 = ((x_6).info);
        Struct5 x_8 = ((x_1).ir_by_victim);
        Vector#(4, Bit#(64)) x_9 = ((x_0).lr_value);
        let x_10 <- getMSHR_00(x_4);
        let x_11 <- getMSHRRq_00(x_4);
        let x_12 <- getMSHRFirstRs_00(x_4);
        Vector#(4, Bit#(64)) x_13 = (unpack(0));
        Bool x_14 = ((x_7).mesi_owned);
        Bit#(3) x_15 = ((x_7).mesi_status);
        Struct15 x_16 = (Struct15 {dir_st : (((x_7).mesi_dir_st) ==
        ((Bit#(3))'(3'h0)) ? ((Bit#(3))'(3'h1)) : ((x_7).mesi_dir_st)),
        dir_excl : ((((x_7).mesi_dir_sharers)[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        ((((((x_7).mesi_dir_sharers)[3:1])[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        (((((((x_7).mesi_dir_sharers)[3:1])[2:1])[0:0]) == ((Bit#(1))'(1'h1))
        ? ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        ((((((((x_7).mesi_dir_sharers)[3:1])[2:1])[1:1])[0:0]) ==
        ((Bit#(1))'(1'h1)) ? ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        (unpack(0))))))))))))), dir_sharers : (x_7).mesi_dir_sharers});
        when ((x_10).m_rsb, noAction);
        when (((x_11).type_) == ((Bool)'(False)), noAction);
        when (((x_11).id) == ((Bit#(6))'(6'he)), noAction);
        when ((Bool)'(True), noAction);
        Struct1 x_17 = (x_11);
        Bit#(4) x_18 = ((x_10).m_qidx);
        Struct16 x_19 = (Struct16 {addr : (x_3).addr, info_write :
        (Bool)'(False), info_hit : (x_6).info_hit, info_way : (x_6).info_way,
        edir_hit : (x_6).edir_hit, edir_way : (x_6).edir_way, edir_slot :
        (x_6).edir_slot, info : (x_6).info, value_write : (Bool)'(False),
        value : unpack(0), may_victim : (x_6).may_victim, reps :
        (x_6).reps});
        Struct16 x_20 = (Struct16 {addr : (x_19).addr, info_write :
        (Bool)'(True), info_hit : (x_19).info_hit, info_way :
        (x_19).info_way, edir_hit : (x_19).edir_hit, edir_way :
        (x_19).edir_way, edir_slot : (x_19).edir_slot, info : Struct10
        {mesi_owned : ((x_19).info).mesi_owned, mesi_status :
        ((x_19).info).mesi_status, mesi_dir_st : (Struct15 {dir_st :
        (Bit#(3))'(3'h1), dir_excl : unpack(0), dir_sharers :
        unpack(0)}).dir_st, mesi_dir_sharers : (((Struct15 {dir_st :
        (Bit#(3))'(3'h1), dir_excl : unpack(0), dir_sharers :
        unpack(0)}).dir_st) == ((Bit#(3))'(3'h2)) ? ((Struct15 {dir_st :
        (Bit#(3))'(3'h1), dir_excl : unpack(0), dir_sharers :
        unpack(0)}).dir_sharers) : (((Bit#(4))'(4'h1)) << ((Struct15 {dir_st
        : (Bit#(3))'(3'h1), dir_excl : unpack(0), dir_sharers :
        unpack(0)}).dir_excl)))}, value_write : (x_19).value_write, value :
        (x_19).value, may_victim : (x_19).may_victim, reps :
        (x_19).reps});
        Struct16 x_21 = (Struct16 {addr : (x_20).addr, info_write :
        (Bool)'(True), info_hit : (x_20).info_hit, info_way :
        (x_20).info_way, edir_hit : (x_20).edir_hit, edir_way :
        (x_20).edir_way, edir_slot : (x_20).edir_slot, info : Struct10
        {mesi_owned : ((x_20).info).mesi_owned, mesi_status :
        (Bit#(3))'(3'h1), mesi_dir_st : ((x_20).info).mesi_dir_st,
        mesi_dir_sharers : ((x_20).info).mesi_dir_sharers}, value_write :
        (x_20).value_write, value : (x_20).value, may_victim :
        (x_20).may_victim, reps : (x_20).reps});
        Struct16 x_22 = (Struct16 {addr : (x_21).addr, info_write :
        (Bool)'(True), info_hit : (x_21).info_hit, info_way :
        (x_21).info_way, edir_hit : (x_21).edir_hit, edir_way :
        (x_21).edir_way, edir_slot : (x_21).edir_slot, info : Struct10
        {mesi_owned : (Bool)'(False), mesi_status :
        ((x_21).info).mesi_status, mesi_dir_st : ((x_21).info).mesi_dir_st,
        mesi_dir_sharers : ((x_21).info).mesi_dir_sharers}, value_write :
        (x_21).value_write, value : (x_21).value, may_victim :
        (x_21).may_victim, reps :
        (x_21).reps});
        let x_25 = ?;
        if ((x_8).valid) begin
            let x_23 <- victims__00__setVictim(Struct17 {victim_idx :
            (x_8).data, victim_info : (x_22).info, victim_value :
            ((x_22).value_write ? ((x_22).value) : (x_9))});
            x_25 = x_9;
        end else begin
            let x_24 <- cache__00__valueRsLineRq(x_22);
            x_25 = x_24;
        end
        let x_26 <- releaseMSHR_00(x_4);
        Struct18 x_27 = (Struct18 {enq_type : (((x_18)[3:2]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : ((((x_18)[3:2]) ==
        ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : (x_18)[1:0], enq_msg : Struct1 {id : (Bit#(6))'(6'hf),
        type_ : (Bool)'(True), addr : (x_17).addr, value : unpack(0)}});
        let x_28 <- makeEnq_parentChildren00(x_27);
    endrule

    rule rule_exec_00_20;
        let x_0 <- victims__00__getFirstVictim();
        Bit#(64) x_1 = ((x_0).victim_addr);
        Struct10 x_2 = ((x_0).victim_info);
        Vector#(4, Bit#(64)) x_3 = ((x_0).victim_value);
        Struct1 x_4 = (Struct1 {id : unpack(0), type_ : (Bool)'(False), addr
        : x_1, value : unpack(0)});
        Struct14 x_5 = (Struct14 {m_is_ul : (Bool)'(True), m_qidx :
        unpack(0), m_rsb : (Bool)'(False), m_dl_rss_from : unpack(0),
        m_dl_rss_recv : unpack(0)});
        Struct1 x_6 = (unpack(0));
        Struct1 x_7 = (unpack(0));
        Vector#(4, Bit#(64)) x_8 = (unpack(0));
        Bool x_9 = ((x_2).mesi_owned);
        Bit#(3) x_10 = ((x_2).mesi_status);
        Struct15 x_11 = (Struct15 {dir_st : (((x_2).mesi_dir_st) ==
        ((Bit#(3))'(3'h0)) ? ((Bit#(3))'(3'h1)) : ((x_2).mesi_dir_st)),
        dir_excl : ((((x_2).mesi_dir_sharers)[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        ((((((x_2).mesi_dir_sharers)[3:1])[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        (((((((x_2).mesi_dir_sharers)[3:1])[2:1])[0:0]) == ((Bit#(1))'(1'h1))
        ? ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        ((((((((x_2).mesi_dir_sharers)[3:1])[2:1])[1:1])[0:0]) ==
        ((Bit#(1))'(1'h1)) ? ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        (unpack(0))))))))))))), dir_sharers : (x_2).mesi_dir_sharers});
        when (! ((x_4).type_), noAction);
        when (((x_9) == ((Bool)'(False))) && (((((Bit#(3))'(3'h0)) < (x_10))
        && ((x_10) < ((Bit#(3))'(3'h4)))) && (((x_11).dir_st) ==
        ((Bit#(3))'(3'h1)))), noAction);
        Struct18 x_12 = (Struct18 {enq_type : ((((Bit#(4))'(4'h0))[3:2]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : (((((Bit#(4))'(4'h0))[3:2])
        == ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : ((Bit#(4))'(4'h0))[1:0], enq_msg : Struct1 {id :
        (Bit#(6))'(6'h14), type_ : (Bool)'(False), addr : (x_4).addr, value :
        unpack(0)}});
        let x_13 <- makeEnq_parentChildren00(x_12);
        let x_14 <- setULImm_00(x_4);
        let x_15 <- victims__00__setVictimRq(x_1);
    endrule

    rule rule_exec_00_21;
        let x_0 <- victims__00__getFirstVictim();
        Bit#(64) x_1 = ((x_0).victim_addr);
        Struct10 x_2 = ((x_0).victim_info);
        Vector#(4, Bit#(64)) x_3 = ((x_0).victim_value);
        Struct1 x_4 = (Struct1 {id : unpack(0), type_ : (Bool)'(False), addr
        : x_1, value : unpack(0)});
        Struct14 x_5 = (Struct14 {m_is_ul : (Bool)'(True), m_qidx :
        unpack(0), m_rsb : (Bool)'(False), m_dl_rss_from : unpack(0),
        m_dl_rss_recv : unpack(0)});
        Struct1 x_6 = (unpack(0));
        Struct1 x_7 = (unpack(0));
        Vector#(4, Bit#(64)) x_8 = (unpack(0));
        Bool x_9 = ((x_2).mesi_owned);
        Bit#(3) x_10 = ((x_2).mesi_status);
        Struct15 x_11 = (Struct15 {dir_st : (((x_2).mesi_dir_st) ==
        ((Bit#(3))'(3'h0)) ? ((Bit#(3))'(3'h1)) : ((x_2).mesi_dir_st)),
        dir_excl : ((((x_2).mesi_dir_sharers)[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        ((((((x_2).mesi_dir_sharers)[3:1])[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        (((((((x_2).mesi_dir_sharers)[3:1])[2:1])[0:0]) == ((Bit#(1))'(1'h1))
        ? ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        ((((((((x_2).mesi_dir_sharers)[3:1])[2:1])[1:1])[0:0]) ==
        ((Bit#(1))'(1'h1)) ? ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        (unpack(0))))))))))))), dir_sharers : (x_2).mesi_dir_sharers});
        when (! ((x_4).type_), noAction);
        when ((((x_11).dir_st) == ((Bit#(3))'(3'h1))) && ((((x_9) ==
        ((Bool)'(True))) && (((Bit#(3))'(3'h1)) < (x_10))) || (((x_9) ==
        ((Bool)'(False))) && ((((Bit#(3))'(3'h0)) < (x_10)) && ((x_10) <
        ((Bit#(3))'(3'h3)))))), noAction);
        Struct18 x_12 = (Struct18 {enq_type : ((((Bit#(4))'(4'h0))[3:2]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : (((((Bit#(4))'(4'h0))[3:2])
        == ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : ((Bit#(4))'(4'h0))[1:0], enq_msg : Struct1 {id :
        (Bit#(6))'(6'h15), type_ : (Bool)'(False), addr : (x_4).addr, value :
        x_3}});
        let x_13 <- makeEnq_parentChildren00(x_12);
        let x_14 <- setULImm_00(x_4);
        let x_15 <- victims__00__setVictimRq(x_1);
    endrule

    rule rule_exec_00_23;
        let x_0 <- victims__00__getFirstVictim();
        Bit#(64) x_1 = ((x_0).victim_addr);
        Struct10 x_2 = ((x_0).victim_info);
        Vector#(4, Bit#(64)) x_3 = ((x_0).victim_value);
        Struct1 x_4 = (Struct1 {id : unpack(0), type_ : (Bool)'(False), addr
        : x_1, value : unpack(0)});
        Struct14 x_5 = (Struct14 {m_is_ul : (Bool)'(True), m_qidx :
        unpack(0), m_rsb : (Bool)'(False), m_dl_rss_from : unpack(0),
        m_dl_rss_recv : unpack(0)});
        Struct1 x_6 = (unpack(0));
        Struct1 x_7 = (unpack(0));
        Vector#(4, Bit#(64)) x_8 = (unpack(0));
        Bool x_9 = ((x_2).mesi_owned);
        Bit#(3) x_10 = ((x_2).mesi_status);
        Struct15 x_11 = (Struct15 {dir_st : (((x_2).mesi_dir_st) ==
        ((Bit#(3))'(3'h0)) ? ((Bit#(3))'(3'h1)) : ((x_2).mesi_dir_st)),
        dir_excl : ((((x_2).mesi_dir_sharers)[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        ((((((x_2).mesi_dir_sharers)[3:1])[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        (((((((x_2).mesi_dir_sharers)[3:1])[2:1])[0:0]) == ((Bit#(1))'(1'h1))
        ? ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        ((((((((x_2).mesi_dir_sharers)[3:1])[2:1])[1:1])[0:0]) ==
        ((Bit#(1))'(1'h1)) ? ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        (unpack(0))))))))))))), dir_sharers : (x_2).mesi_dir_sharers});
        when ((((x_10) == ((Bit#(3))'(3'h1))) && (! (((x_11).dir_st) ==
        ((Bit#(3))'(3'h3))))) || (((x_10) == ((Bit#(3))'(3'h2))) && ((x_9) ==
        ((Bool)'(False)))), noAction);
        let x_12 <- canImm_00(x_1);
        let x_13 <- victims__00__releaseVictim(x_1);
    endrule

    // No methods in this module
endmodule

interface Module134;

endinterface

module mkModule134#(function Action victims__000__setVictimRq(Bit#(64) _),
    function Action setULImm_000(Struct1 _),
    function ActionValue#(Struct13) victims__000__getFirstVictim(),
    function Action victims__000__setVictim(Struct44 _),
    function Action registerUL_000(Struct43 _),
    function Action makeEnq_parentChildren000(Struct18 _),
    function ActionValue#(Vector#(4, Bit#(64))) cache__000__valueRsLineRq(Struct42 _),
    function ActionValue#(Struct1) getMSHRRq_000(Bit#(2) _),
    function ActionValue#(Struct14) getMSHR_000(Bit#(2) _),
    function ActionValue#(Struct41) deq_fifoL2E_000(),
    function ActionValue#(Struct13) victims__000__getVictim(Bit#(1) _),
    function Action enq_fifoL2E_000(Struct41 _),
    function ActionValue#(Struct39) cache__000__infoRsValueRq(Bit#(64) _),
    function ActionValue#(Struct38) deq_fifoI2L_000(),
    function Action enq_fifoI2L_000(Struct38 _),
    function Action cache__000__infoRq(Bit#(64) _),
    function ActionValue#(Struct38) deq_fifoN2I_000(),
    function ActionValue#(Struct36) getCRqSlot_000(Struct35 _),
    function ActionValue#(Bool) victims__000__hasVictim(),
    function ActionValue#(Struct2) deq_fifoCRqInput_000(),
    function Action releaseMSHR_000(Bit#(2) _),
    function Action victims__000__releaseVictim(Bit#(64) _),
    function ActionValue#(Struct35) getWait_000(),
    function Action startRelease_000(Bit#(2) _),
    function ActionValue#(Bit#(2)) getULReady_000(Bit#(64) _),
    function Action enq_fifoN2I_000(Struct38 _),
    function ActionValue#(Struct37) victims__000__findVictim(Bit#(64) _),
    function ActionValue#(Struct36) getPRqSlot_000(Struct35 _),
    function ActionValue#(Struct2) deq_fifoPInput_000())
    (Module134);

    rule rule_in_prq_000;
        let x_0 <- deq_fifoPInput_000();
        Bit#(4) x_1 = ((x_0).in_msg_from);
        when ((x_1) == ({((Bit#(2))'(2'h2)),((Bit#(2))'(2'h0))}),
        noAction);
        Struct1 x_2 = ((x_0).in_msg);
        when (! ((x_2).type_), noAction);
        let x_3 <- getPRqSlot_000(Struct35 {r_id : unpack(0), r_msg : x_2,
        r_msg_from : (x_0).in_msg_from});
        when ((x_3).s_has_slot,
        noAction);
        if (! ((x_3).s_conflict)) begin
            let x_4 <- victims__000__findVictim((x_2).addr);
            Struct38 x_5 = (Struct38 {ir_is_rs_rel : (Bool)'(False), ir_msg :
            (x_0).in_msg, ir_msg_from : x_1, ir_mshr_id : (x_3).s_id,
            ir_by_victim : x_4});
            let x_6 <- enq_fifoN2I_000(x_5);
        end else begin

        end
    endrule

    rule rule_in_prs_000;
        let x_0 <- deq_fifoPInput_000();
        Bit#(4) x_1 = ((x_0).in_msg_from);
        when ((x_1) == ({((Bit#(2))'(2'h2)),((Bit#(2))'(2'h0))}),
        noAction);
        Struct1 x_2 = ((x_0).in_msg);
        when (((x_2).type_) && (! (((x_2).id) == ((Bit#(6))'(6'h16)))),
        noAction);
        let x_3 <- getULReady_000((x_2).addr);
        let x_4 <- startRelease_000(x_3);
        let x_5 <- victims__000__findVictim((x_2).addr);
        Struct38 x_6 = (Struct38 {ir_is_rs_rel : (Bool)'(False), ir_msg :
        (x_0).in_msg, ir_msg_from : x_1, ir_mshr_id : x_3, ir_by_victim :
        x_5});
        let x_7 <- enq_fifoN2I_000(x_6);
    endrule

    rule rule_in_retry_000;
        let x_0 <- getWait_000();
        Struct1 x_1 = ((x_0).r_msg);
        let x_2 <- victims__000__findVictim((x_1).addr);
        Struct38 x_3 = (Struct38 {ir_is_rs_rel : (Bool)'(False), ir_msg :
        x_1, ir_msg_from : (x_0).r_msg_from, ir_mshr_id : (x_0).r_id,
        ir_by_victim : x_2});
        let x_4 <- enq_fifoN2I_000(x_3);
    endrule

    rule rule_in_invrs_000;
        let x_0 <- deq_fifoPInput_000();
        Bit#(4) x_1 = ((x_0).in_msg_from);
        when ((x_1) == ({((Bit#(2))'(2'h2)),((Bit#(2))'(2'h0))}),
        noAction);
        Struct1 x_2 = ((x_0).in_msg);
        when (((x_2).type_) && (((x_2).id) == ((Bit#(6))'(6'h16))),
        noAction);
        let x_3 <- getULReady_000((x_2).addr);
        let x_4 <- victims__000__releaseVictim((x_2).addr);
        let x_5 <- releaseMSHR_000(x_3);
    endrule

    rule rule_in_crq_000;
        let x_0 <- deq_fifoCRqInput_000();
        Bit#(4) x_1 = ((x_0).in_msg_from);
        when (((x_1)[3:2]) == ((Bit#(2))'(2'h0)), noAction);
        Struct1 x_2 = ((x_0).in_msg);
        when (! ((x_2).type_), noAction);
        let x_3 <- victims__000__hasVictim();
        when (! (x_3), noAction);
        let x_4 <- getCRqSlot_000(Struct35 {r_id : unpack(0), r_msg : x_2,
        r_msg_from : x_1});
        when ((x_4).s_has_slot,
        noAction);
        if (! ((x_4).s_conflict)) begin
            let x_5 <- victims__000__findVictim((x_2).addr);
            Struct38 x_6 = (Struct38 {ir_is_rs_rel : (Bool)'(False), ir_msg :
            (x_0).in_msg, ir_msg_from : x_1, ir_mshr_id : (x_4).s_id,
            ir_by_victim : x_5});
            let x_7 <- enq_fifoN2I_000(x_6);
        end else begin

        end
    endrule

    rule rule_ir_cache_000;
        let x_0 <- deq_fifoN2I_000();
        when (! (((x_0).ir_by_victim).valid), noAction);
        Struct1 x_1 = ((x_0).ir_msg);
        let x_2 <- cache__000__infoRq((x_1).addr);
        let x_3 <- enq_fifoI2L_000(x_0);
    endrule

    rule rule_ir_victims_000;
        let x_0 <- deq_fifoN2I_000();
        when (((x_0).ir_by_victim).valid, noAction);
        let x_1 <- enq_fifoI2L_000(x_0);
    endrule

    rule rule_lr_cache_000;
        let x_0 <- deq_fifoI2L_000();
        when (! (((x_0).ir_by_victim).valid), noAction);
        let x_1 <- cache__000__infoRsValueRq(((x_0).ir_msg).addr);
        Struct41 x_2 = (Struct41 {lr_ir_pp : x_0, lr_ir : x_1, lr_value :
        unpack(0)});
        let x_3 <- enq_fifoL2E_000(x_2);
    endrule

    rule rule_lr_victims_000;
        let x_0 <- deq_fifoI2L_000();
        when (((x_0).ir_by_victim).valid, noAction);
        Bit#(1) x_1 = (((x_0).ir_by_victim).data);
        let x_2 <- victims__000__getVictim(x_1);
        Struct39 x_3 = (Struct39 {info_index : unpack(0), info_hit :
        unpack(0), info_way : unpack(0), edir_hit : unpack(0), edir_way :
        unpack(0), edir_slot : unpack(0), info : (x_2).victim_info,
        may_victim : unpack(0), reps : unpack(0)});
        Struct41 x_4 = (Struct41 {lr_ir_pp : x_0, lr_ir : x_3, lr_value :
        (x_2).victim_value});
        let x_5 <- enq_fifoL2E_000(x_4);
    endrule

    rule rule_exec_000_00;
        let x_0 <- deq_fifoL2E_000();
        Struct38 x_1 = ((x_0).lr_ir_pp);
        Bit#(4) x_2 = ((x_1).ir_msg_from);
        Struct1 x_3 = ((x_1).ir_msg);
        Bit#(2) x_4 = ((x_1).ir_mshr_id);
        Bool x_5 = ((x_1).ir_is_rs_rel);
        when (! (x_5), noAction);
        Struct39 x_6 = ((x_0).lr_ir);
        Struct10 x_7 = ((x_6).info);
        Struct37 x_8 = ((x_1).ir_by_victim);
        Vector#(4, Bit#(64)) x_9 = ((x_0).lr_value);
        let x_10 <- getMSHR_000(x_4);
        let x_11 <- getMSHRRq_000(x_4);
        Struct1 x_12 = (unpack(0));
        Vector#(4, Bit#(64)) x_13 = (unpack(0));
        Bool x_14 = ((x_7).mesi_owned);
        Bit#(3) x_15 = ((x_7).mesi_status);
        Struct15 x_16 = (Struct15 {dir_st : (((x_7).mesi_dir_st) ==
        ((Bit#(3))'(3'h0)) ? ((Bit#(3))'(3'h1)) : ((x_7).mesi_dir_st)),
        dir_excl : ((((x_7).mesi_dir_sharers)[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        ((((((x_7).mesi_dir_sharers)[3:1])[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        (((((((x_7).mesi_dir_sharers)[3:1])[2:1])[0:0]) == ((Bit#(1))'(1'h1))
        ? ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        ((((((((x_7).mesi_dir_sharers)[3:1])[2:1])[1:1])[0:0]) ==
        ((Bit#(1))'(1'h1)) ? ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        (unpack(0))))))))))))), dir_sharers : (x_7).mesi_dir_sharers});
        when ((x_2) == ((Bit#(4))'(4'h0)), noAction);
        when (((x_3).id) == ((Bit#(6))'(6'h0)), noAction);
        when (! ((x_3).type_), noAction);
        when (! ((x_15) < ((Bit#(3))'(3'h2))), noAction);
        Struct1 x_17 = (x_3);
        Struct42 x_18 = (Struct42 {addr : (x_3).addr, info_write :
        (Bool)'(False), info_hit : (x_6).info_hit, info_way : (x_6).info_way,
        edir_hit : (x_6).edir_hit, edir_way : (x_6).edir_way, edir_slot :
        (x_6).edir_slot, info : (x_6).info, value_write : (Bool)'(False),
        value : unpack(0), may_victim : (x_6).may_victim, reps :
        (x_6).reps});
        let x_20 = ?;
        if ((x_8).valid) begin
            x_20 = x_9;
        end else begin
            let x_19 <- cache__000__valueRsLineRq(unpack(0));
            x_20 = x_19;
        end
        Struct18 x_21 = (Struct18 {enq_type : ((((Bit#(4))'(4'h8))[3:2]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : (((((Bit#(4))'(4'h8))[3:2])
        == ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : ((Bit#(4))'(4'h8))[1:0], enq_msg : Struct1 {id :
        (Bit#(6))'(6'h1), type_ : (Bool)'(True), addr : (x_17).addr, value :
        x_20}});
        let x_22 <- makeEnq_parentChildren000(x_21);
        let x_23 <- releaseMSHR_000(x_4);
    endrule

    rule rule_exec_000_01;
        let x_0 <- deq_fifoL2E_000();
        Struct38 x_1 = ((x_0).lr_ir_pp);
        Bit#(4) x_2 = ((x_1).ir_msg_from);
        Struct1 x_3 = ((x_1).ir_msg);
        Bit#(2) x_4 = ((x_1).ir_mshr_id);
        Bool x_5 = ((x_1).ir_is_rs_rel);
        when (! (x_5), noAction);
        Struct39 x_6 = ((x_0).lr_ir);
        Struct10 x_7 = ((x_6).info);
        Struct37 x_8 = ((x_1).ir_by_victim);
        Vector#(4, Bit#(64)) x_9 = ((x_0).lr_value);
        let x_10 <- getMSHR_000(x_4);
        let x_11 <- getMSHRRq_000(x_4);
        Struct1 x_12 = (unpack(0));
        Vector#(4, Bit#(64)) x_13 = (unpack(0));
        Bool x_14 = ((x_7).mesi_owned);
        Bit#(3) x_15 = ((x_7).mesi_status);
        Struct15 x_16 = (Struct15 {dir_st : (((x_7).mesi_dir_st) ==
        ((Bit#(3))'(3'h0)) ? ((Bit#(3))'(3'h1)) : ((x_7).mesi_dir_st)),
        dir_excl : ((((x_7).mesi_dir_sharers)[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        ((((((x_7).mesi_dir_sharers)[3:1])[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        (((((((x_7).mesi_dir_sharers)[3:1])[2:1])[0:0]) == ((Bit#(1))'(1'h1))
        ? ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        ((((((((x_7).mesi_dir_sharers)[3:1])[2:1])[1:1])[0:0]) ==
        ((Bit#(1))'(1'h1)) ? ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        (unpack(0))))))))))))), dir_sharers : (x_7).mesi_dir_sharers});
        when ((x_2) == ((Bit#(4))'(4'h0)), noAction);
        when (((x_3).id) == ((Bit#(6))'(6'h0)), noAction);
        when (! ((x_3).type_), noAction);
        when (! (((Bit#(3))'(3'h1)) < (x_15)), noAction);
        Struct1 x_17 = (x_3);
        Struct42 x_18 = (Struct42 {addr : (x_3).addr, info_write :
        (Bool)'(False), info_hit : (x_6).info_hit, info_way : (x_6).info_way,
        edir_hit : (x_6).edir_hit, edir_way : (x_6).edir_way, edir_slot :
        (x_6).edir_slot, info : (x_6).info, value_write : (Bool)'(False),
        value : unpack(0), may_victim : (x_6).may_victim, reps :
        (x_6).reps});
        let x_20 = ?;
        if ((x_8).valid) begin
            x_20 = x_9;
        end else begin
            let x_19 <- cache__000__valueRsLineRq(unpack(0));
            x_20 = x_19;
        end
        let x_21 <- registerUL_000(Struct43 {r_id : x_4, r_ul_rsb :
        (Bool)'(True), r_ul_rsbTo : ((Bit#(4))'(4'h8))[1:0]});
        Struct18 x_22 = (Struct18 {enq_type : ((((Bit#(4))'(4'h0))[3:2]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : (((((Bit#(4))'(4'h0))[3:2])
        == ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : ((Bit#(4))'(4'h0))[1:0], enq_msg : Struct1 {id :
        (Bit#(6))'(6'h2), type_ : (Bool)'(False), addr : (x_17).addr, value :
        unpack(0)}});
        let x_23 <- makeEnq_parentChildren000(x_22);
    endrule

    rule rule_exec_000_020;
        let x_0 <- deq_fifoL2E_000();
        Struct38 x_1 = ((x_0).lr_ir_pp);
        Bit#(4) x_2 = ((x_1).ir_msg_from);
        Struct1 x_3 = ((x_1).ir_msg);
        Bit#(2) x_4 = ((x_1).ir_mshr_id);
        Bool x_5 = ((x_1).ir_is_rs_rel);
        when (! (x_5), noAction);
        Struct39 x_6 = ((x_0).lr_ir);
        Struct10 x_7 = ((x_6).info);
        Struct37 x_8 = ((x_1).ir_by_victim);
        Vector#(4, Bit#(64)) x_9 = ((x_0).lr_value);
        let x_10 <- getMSHR_000(x_4);
        let x_11 <- getMSHRRq_000(x_4);
        Struct1 x_12 = (unpack(0));
        Vector#(4, Bit#(64)) x_13 = (unpack(0));
        Bool x_14 = ((x_7).mesi_owned);
        Bit#(3) x_15 = ((x_7).mesi_status);
        Struct15 x_16 = (Struct15 {dir_st : (((x_7).mesi_dir_st) ==
        ((Bit#(3))'(3'h0)) ? ((Bit#(3))'(3'h1)) : ((x_7).mesi_dir_st)),
        dir_excl : ((((x_7).mesi_dir_sharers)[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        ((((((x_7).mesi_dir_sharers)[3:1])[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        (((((((x_7).mesi_dir_sharers)[3:1])[2:1])[0:0]) == ((Bit#(1))'(1'h1))
        ? ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        ((((((((x_7).mesi_dir_sharers)[3:1])[2:1])[1:1])[0:0]) ==
        ((Bit#(1))'(1'h1)) ? ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        (unpack(0))))))))))))), dir_sharers : (x_7).mesi_dir_sharers});
        when ((x_2) == ({((Bit#(2))'(2'h2)),((Bit#(2))'(2'h0))}),
        noAction);
        when (((x_3).id) == ((Bit#(6))'(6'h3)), noAction);
        when ((x_10).m_rsb, noAction);
        when (((x_11).type_) == ((Bool)'(False)), noAction);
        when (((x_11).id) == ((Bit#(6))'(6'h0)), noAction);
        when ((x_10).m_rsb, noAction);
        when ((x_3).type_, noAction);
        when ((Bool)'(True), noAction);
        Struct1 x_17 = (x_3);
        Struct1 x_18 = (x_11);
        Bit#(4) x_19 = ({((Bit#(2))'(2'h2)),(((x_10).m_qidx)[1:0])});
        Struct42 x_20 = (Struct42 {addr : (x_3).addr, info_write :
        (Bool)'(False), info_hit : (x_6).info_hit, info_way : (x_6).info_way,
        edir_hit : (x_6).edir_hit, edir_way : (x_6).edir_way, edir_slot :
        (x_6).edir_slot, info : (x_6).info, value_write : (Bool)'(False),
        value : unpack(0), may_victim : (x_6).may_victim, reps :
        (x_6).reps});
        Struct42 x_21 = (Struct42 {addr : (x_20).addr, info_write :
        (Bool)'(True), info_hit : (x_20).info_hit, info_way :
        (x_20).info_way, edir_hit : (x_20).edir_hit, edir_way :
        (x_20).edir_way, edir_slot : (x_20).edir_slot, info : Struct10
        {mesi_owned : ((x_20).info).mesi_owned, mesi_status :
        (Bit#(3))'(3'h2), mesi_dir_st : ((x_20).info).mesi_dir_st,
        mesi_dir_sharers : ((x_20).info).mesi_dir_sharers}, value_write :
        (x_20).value_write, value : (x_20).value, may_victim :
        (x_20).may_victim, reps : (x_20).reps});
        Struct42 x_22 = (Struct42 {addr : (x_21).addr, info_write :
        (x_21).info_write, info_hit : (x_21).info_hit, info_way :
        (x_21).info_way, edir_hit : (x_21).edir_hit, edir_way :
        (x_21).edir_way, edir_slot : (x_21).edir_slot, info : (x_21).info,
        value_write : (Bool)'(True), value : (x_17).value, may_victim :
        (x_21).may_victim, reps :
        (x_21).reps});
        let x_25 = ?;
        if ((x_8).valid) begin
            let x_23 <- victims__000__setVictim(Struct44 {victim_idx :
            (x_8).data, victim_info : (x_22).info, victim_value :
            ((x_22).value_write ? ((x_22).value) : (x_9))});
            x_25 = x_9;
        end else begin
            let x_24 <- cache__000__valueRsLineRq(x_22);
            x_25 = x_24;
        end
        let x_26 <- releaseMSHR_000(x_4);
        Struct18 x_27 = (Struct18 {enq_type : (((x_19)[3:2]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : ((((x_19)[3:2]) ==
        ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : (x_19)[1:0], enq_msg : Struct1 {id : (Bit#(6))'(6'h1),
        type_ : (Bool)'(True), addr : (x_17).addr, value :
        (x_17).value}});
        let x_28 <- makeEnq_parentChildren000(x_27);
    endrule

    rule rule_exec_000_021;
        let x_0 <- deq_fifoL2E_000();
        Struct38 x_1 = ((x_0).lr_ir_pp);
        Bit#(4) x_2 = ((x_1).ir_msg_from);
        Struct1 x_3 = ((x_1).ir_msg);
        Bit#(2) x_4 = ((x_1).ir_mshr_id);
        Bool x_5 = ((x_1).ir_is_rs_rel);
        when (! (x_5), noAction);
        Struct39 x_6 = ((x_0).lr_ir);
        Struct10 x_7 = ((x_6).info);
        Struct37 x_8 = ((x_1).ir_by_victim);
        Vector#(4, Bit#(64)) x_9 = ((x_0).lr_value);
        let x_10 <- getMSHR_000(x_4);
        let x_11 <- getMSHRRq_000(x_4);
        Struct1 x_12 = (unpack(0));
        Vector#(4, Bit#(64)) x_13 = (unpack(0));
        Bool x_14 = ((x_7).mesi_owned);
        Bit#(3) x_15 = ((x_7).mesi_status);
        Struct15 x_16 = (Struct15 {dir_st : (((x_7).mesi_dir_st) ==
        ((Bit#(3))'(3'h0)) ? ((Bit#(3))'(3'h1)) : ((x_7).mesi_dir_st)),
        dir_excl : ((((x_7).mesi_dir_sharers)[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        ((((((x_7).mesi_dir_sharers)[3:1])[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        (((((((x_7).mesi_dir_sharers)[3:1])[2:1])[0:0]) == ((Bit#(1))'(1'h1))
        ? ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        ((((((((x_7).mesi_dir_sharers)[3:1])[2:1])[1:1])[0:0]) ==
        ((Bit#(1))'(1'h1)) ? ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        (unpack(0))))))))))))), dir_sharers : (x_7).mesi_dir_sharers});
        when ((x_2) == ({((Bit#(2))'(2'h2)),((Bit#(2))'(2'h0))}),
        noAction);
        when (((x_3).id) == ((Bit#(6))'(6'h4)), noAction);
        when ((x_10).m_rsb, noAction);
        when (((x_11).type_) == ((Bool)'(False)), noAction);
        when (((x_11).id) == ((Bit#(6))'(6'h0)), noAction);
        when ((x_10).m_rsb, noAction);
        when ((x_3).type_, noAction);
        when ((Bool)'(True), noAction);
        Struct1 x_17 = (x_3);
        Struct1 x_18 = (x_11);
        Bit#(4) x_19 = ({((Bit#(2))'(2'h2)),(((x_10).m_qidx)[1:0])});
        Struct42 x_20 = (Struct42 {addr : (x_3).addr, info_write :
        (Bool)'(False), info_hit : (x_6).info_hit, info_way : (x_6).info_way,
        edir_hit : (x_6).edir_hit, edir_way : (x_6).edir_way, edir_slot :
        (x_6).edir_slot, info : (x_6).info, value_write : (Bool)'(False),
        value : unpack(0), may_victim : (x_6).may_victim, reps :
        (x_6).reps});
        Struct42 x_21 = (Struct42 {addr : (x_20).addr, info_write :
        (Bool)'(True), info_hit : (x_20).info_hit, info_way :
        (x_20).info_way, edir_hit : (x_20).edir_hit, edir_way :
        (x_20).edir_way, edir_slot : (x_20).edir_slot, info : Struct10
        {mesi_owned : ((x_20).info).mesi_owned, mesi_status :
        (Bit#(3))'(3'h3), mesi_dir_st : ((x_20).info).mesi_dir_st,
        mesi_dir_sharers : ((x_20).info).mesi_dir_sharers}, value_write :
        (x_20).value_write, value : (x_20).value, may_victim :
        (x_20).may_victim, reps : (x_20).reps});
        Struct42 x_22 = (Struct42 {addr : (x_21).addr, info_write :
        (x_21).info_write, info_hit : (x_21).info_hit, info_way :
        (x_21).info_way, edir_hit : (x_21).edir_hit, edir_way :
        (x_21).edir_way, edir_slot : (x_21).edir_slot, info : (x_21).info,
        value_write : (Bool)'(True), value : (x_17).value, may_victim :
        (x_21).may_victim, reps :
        (x_21).reps});
        let x_25 = ?;
        if ((x_8).valid) begin
            let x_23 <- victims__000__setVictim(Struct44 {victim_idx :
            (x_8).data, victim_info : (x_22).info, victim_value :
            ((x_22).value_write ? ((x_22).value) : (x_9))});
            x_25 = x_9;
        end else begin
            let x_24 <- cache__000__valueRsLineRq(x_22);
            x_25 = x_24;
        end
        let x_26 <- releaseMSHR_000(x_4);
        Struct18 x_27 = (Struct18 {enq_type : (((x_19)[3:2]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : ((((x_19)[3:2]) ==
        ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : (x_19)[1:0], enq_msg : Struct1 {id : (Bit#(6))'(6'h1),
        type_ : (Bool)'(True), addr : (x_17).addr, value :
        (x_17).value}});
        let x_28 <- makeEnq_parentChildren000(x_27);
    endrule

    rule rule_exec_000_03;
        let x_0 <- deq_fifoL2E_000();
        Struct38 x_1 = ((x_0).lr_ir_pp);
        Bit#(4) x_2 = ((x_1).ir_msg_from);
        Struct1 x_3 = ((x_1).ir_msg);
        Bit#(2) x_4 = ((x_1).ir_mshr_id);
        Bool x_5 = ((x_1).ir_is_rs_rel);
        when (! (x_5), noAction);
        Struct39 x_6 = ((x_0).lr_ir);
        Struct10 x_7 = ((x_6).info);
        Struct37 x_8 = ((x_1).ir_by_victim);
        Vector#(4, Bit#(64)) x_9 = ((x_0).lr_value);
        let x_10 <- getMSHR_000(x_4);
        let x_11 <- getMSHRRq_000(x_4);
        Struct1 x_12 = (unpack(0));
        Vector#(4, Bit#(64)) x_13 = (unpack(0));
        Bool x_14 = ((x_7).mesi_owned);
        Bit#(3) x_15 = ((x_7).mesi_status);
        Struct15 x_16 = (Struct15 {dir_st : (((x_7).mesi_dir_st) ==
        ((Bit#(3))'(3'h0)) ? ((Bit#(3))'(3'h1)) : ((x_7).mesi_dir_st)),
        dir_excl : ((((x_7).mesi_dir_sharers)[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        ((((((x_7).mesi_dir_sharers)[3:1])[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        (((((((x_7).mesi_dir_sharers)[3:1])[2:1])[0:0]) == ((Bit#(1))'(1'h1))
        ? ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        ((((((((x_7).mesi_dir_sharers)[3:1])[2:1])[1:1])[0:0]) ==
        ((Bit#(1))'(1'h1)) ? ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        (unpack(0))))))))))))), dir_sharers : (x_7).mesi_dir_sharers});
        when ((x_2) == ((Bit#(4))'(4'h8)), noAction);
        when (((x_3).id) == ((Bit#(6))'(6'h5)), noAction);
        when (! ((x_3).type_), noAction);
        when (! ((x_15) < ((Bit#(3))'(3'h2))), noAction);
        Struct1 x_17 = (x_3);
        Struct42 x_18 = (Struct42 {addr : (x_3).addr, info_write :
        (Bool)'(False), info_hit : (x_6).info_hit, info_way : (x_6).info_way,
        edir_hit : (x_6).edir_hit, edir_way : (x_6).edir_way, edir_slot :
        (x_6).edir_slot, info : (x_6).info, value_write : (Bool)'(False),
        value : unpack(0), may_victim : (x_6).may_victim, reps :
        (x_6).reps});
        Struct42 x_19 = (Struct42 {addr : (x_18).addr, info_write :
        (Bool)'(True), info_hit : (x_18).info_hit, info_way :
        (x_18).info_way, edir_hit : (x_18).edir_hit, edir_way :
        (x_18).edir_way, edir_slot : (x_18).edir_slot, info : Struct10
        {mesi_owned : ((x_18).info).mesi_owned, mesi_status :
        (Bit#(3))'(3'h2), mesi_dir_st : ((x_18).info).mesi_dir_st,
        mesi_dir_sharers : ((x_18).info).mesi_dir_sharers}, value_write :
        (x_18).value_write, value : (x_18).value, may_victim :
        (x_18).may_victim, reps : (x_18).reps});
        Struct42 x_20 = (Struct42 {addr : (x_19).addr, info_write :
        (Bool)'(True), info_hit : (x_19).info_hit, info_way :
        (x_19).info_way, edir_hit : (x_19).edir_hit, edir_way :
        (x_19).edir_way, edir_slot : (x_19).edir_slot, info : Struct10
        {mesi_owned : (Bool)'(False), mesi_status :
        ((x_19).info).mesi_status, mesi_dir_st : ((x_19).info).mesi_dir_st,
        mesi_dir_sharers : ((x_19).info).mesi_dir_sharers}, value_write :
        (x_19).value_write, value : (x_19).value, may_victim :
        (x_19).may_victim, reps :
        (x_19).reps});
        let x_23 = ?;
        if ((x_8).valid) begin
            let x_21 <- victims__000__setVictim(Struct44 {victim_idx :
            (x_8).data, victim_info : (x_20).info, victim_value :
            ((x_20).value_write ? ((x_20).value) : (x_9))});
            x_23 = x_9;
        end else begin
            let x_22 <- cache__000__valueRsLineRq(x_20);
            x_23 = x_22;
        end
        Struct18 x_24 = (Struct18 {enq_type : ((((Bit#(4))'(4'h4))[3:2]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : (((((Bit#(4))'(4'h4))[3:2])
        == ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : ((Bit#(4))'(4'h4))[1:0], enq_msg : Struct1 {id :
        (Bit#(6))'(6'h6), type_ : (Bool)'(True), addr : (x_17).addr, value :
        x_23}});
        let x_25 <- makeEnq_parentChildren000(x_24);
        let x_26 <- releaseMSHR_000(x_4);
    endrule

    rule rule_exec_000_100;
        let x_0 <- deq_fifoL2E_000();
        Struct38 x_1 = ((x_0).lr_ir_pp);
        Bit#(4) x_2 = ((x_1).ir_msg_from);
        Struct1 x_3 = ((x_1).ir_msg);
        Bit#(2) x_4 = ((x_1).ir_mshr_id);
        Bool x_5 = ((x_1).ir_is_rs_rel);
        when (! (x_5), noAction);
        Struct39 x_6 = ((x_0).lr_ir);
        Struct10 x_7 = ((x_6).info);
        Struct37 x_8 = ((x_1).ir_by_victim);
        Vector#(4, Bit#(64)) x_9 = ((x_0).lr_value);
        let x_10 <- getMSHR_000(x_4);
        let x_11 <- getMSHRRq_000(x_4);
        Struct1 x_12 = (unpack(0));
        Vector#(4, Bit#(64)) x_13 = (unpack(0));
        Bool x_14 = ((x_7).mesi_owned);
        Bit#(3) x_15 = ((x_7).mesi_status);
        Struct15 x_16 = (Struct15 {dir_st : (((x_7).mesi_dir_st) ==
        ((Bit#(3))'(3'h0)) ? ((Bit#(3))'(3'h1)) : ((x_7).mesi_dir_st)),
        dir_excl : ((((x_7).mesi_dir_sharers)[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        ((((((x_7).mesi_dir_sharers)[3:1])[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        (((((((x_7).mesi_dir_sharers)[3:1])[2:1])[0:0]) == ((Bit#(1))'(1'h1))
        ? ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        ((((((((x_7).mesi_dir_sharers)[3:1])[2:1])[1:1])[0:0]) ==
        ((Bit#(1))'(1'h1)) ? ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        (unpack(0))))))))))))), dir_sharers : (x_7).mesi_dir_sharers});
        when ((x_2) == ((Bit#(4))'(4'h0)), noAction);
        when (((x_3).id) == ((Bit#(6))'(6'h8)), noAction);
        when (! ((x_3).type_), noAction);
        when ((x_15) == ((Bit#(3))'(3'h3)), noAction);
        Struct1 x_17 = (x_3);
        Struct42 x_18 = (Struct42 {addr : (x_3).addr, info_write :
        (Bool)'(False), info_hit : (x_6).info_hit, info_way : (x_6).info_way,
        edir_hit : (x_6).edir_hit, edir_way : (x_6).edir_way, edir_slot :
        (x_6).edir_slot, info : (x_6).info, value_write : (Bool)'(False),
        value : unpack(0), may_victim : (x_6).may_victim, reps :
        (x_6).reps});
        Struct42 x_19 = (Struct42 {addr : (x_18).addr, info_write :
        (x_18).info_write, info_hit : (x_18).info_hit, info_way :
        (x_18).info_way, edir_hit : (x_18).edir_hit, edir_way :
        (x_18).edir_way, edir_slot : (x_18).edir_slot, info : (x_18).info,
        value_write : (Bool)'(True), value : (x_17).value, may_victim :
        (x_18).may_victim, reps : (x_18).reps});
        Struct42 x_20 = (Struct42 {addr : (x_19).addr, info_write :
        (Bool)'(True), info_hit : (x_19).info_hit, info_way :
        (x_19).info_way, edir_hit : (x_19).edir_hit, edir_way :
        (x_19).edir_way, edir_slot : (x_19).edir_slot, info : Struct10
        {mesi_owned : ((x_19).info).mesi_owned, mesi_status :
        (Bit#(3))'(3'h4), mesi_dir_st : ((x_19).info).mesi_dir_st,
        mesi_dir_sharers : ((x_19).info).mesi_dir_sharers}, value_write :
        (x_19).value_write, value : (x_19).value, may_victim :
        (x_19).may_victim, reps : (x_19).reps});
        Struct42 x_21 = (Struct42 {addr : (x_20).addr, info_write :
        (Bool)'(True), info_hit : (x_20).info_hit, info_way :
        (x_20).info_way, edir_hit : (x_20).edir_hit, edir_way :
        (x_20).edir_way, edir_slot : (x_20).edir_slot, info : Struct10
        {mesi_owned : (Bool)'(True), mesi_status : ((x_20).info).mesi_status,
        mesi_dir_st : ((x_20).info).mesi_dir_st, mesi_dir_sharers :
        ((x_20).info).mesi_dir_sharers}, value_write : (x_20).value_write,
        value : (x_20).value, may_victim : (x_20).may_victim, reps :
        (x_20).reps});
        let x_24 = ?;
        if ((x_8).valid) begin
            let x_22 <- victims__000__setVictim(Struct44 {victim_idx :
            (x_8).data, victim_info : (x_21).info, victim_value :
            ((x_21).value_write ? ((x_21).value) : (x_9))});
            x_24 = x_9;
        end else begin
            let x_23 <- cache__000__valueRsLineRq(x_21);
            x_24 = x_23;
        end
        Struct18 x_25 = (Struct18 {enq_type : ((((Bit#(4))'(4'h8))[3:2]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : (((((Bit#(4))'(4'h8))[3:2])
        == ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : ((Bit#(4))'(4'h8))[1:0], enq_msg : Struct1 {id :
        (Bit#(6))'(6'h9), type_ : (Bool)'(True), addr : (x_17).addr, value :
        unpack(0)}});
        let x_26 <- makeEnq_parentChildren000(x_25);
        let x_27 <- releaseMSHR_000(x_4);
    endrule

    rule rule_exec_000_101;
        let x_0 <- deq_fifoL2E_000();
        Struct38 x_1 = ((x_0).lr_ir_pp);
        Bit#(4) x_2 = ((x_1).ir_msg_from);
        Struct1 x_3 = ((x_1).ir_msg);
        Bit#(2) x_4 = ((x_1).ir_mshr_id);
        Bool x_5 = ((x_1).ir_is_rs_rel);
        when (! (x_5), noAction);
        Struct39 x_6 = ((x_0).lr_ir);
        Struct10 x_7 = ((x_6).info);
        Struct37 x_8 = ((x_1).ir_by_victim);
        Vector#(4, Bit#(64)) x_9 = ((x_0).lr_value);
        let x_10 <- getMSHR_000(x_4);
        let x_11 <- getMSHRRq_000(x_4);
        Struct1 x_12 = (unpack(0));
        Vector#(4, Bit#(64)) x_13 = (unpack(0));
        Bool x_14 = ((x_7).mesi_owned);
        Bit#(3) x_15 = ((x_7).mesi_status);
        Struct15 x_16 = (Struct15 {dir_st : (((x_7).mesi_dir_st) ==
        ((Bit#(3))'(3'h0)) ? ((Bit#(3))'(3'h1)) : ((x_7).mesi_dir_st)),
        dir_excl : ((((x_7).mesi_dir_sharers)[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        ((((((x_7).mesi_dir_sharers)[3:1])[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        (((((((x_7).mesi_dir_sharers)[3:1])[2:1])[0:0]) == ((Bit#(1))'(1'h1))
        ? ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        ((((((((x_7).mesi_dir_sharers)[3:1])[2:1])[1:1])[0:0]) ==
        ((Bit#(1))'(1'h1)) ? ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        (unpack(0))))))))))))), dir_sharers : (x_7).mesi_dir_sharers});
        when ((x_2) == ((Bit#(4))'(4'h0)), noAction);
        when (((x_3).id) == ((Bit#(6))'(6'h8)), noAction);
        when (! ((x_3).type_), noAction);
        when (((x_14) == ((Bool)'(True))) && ((x_15) == ((Bit#(3))'(3'h4))),
        noAction);
        Struct1 x_17 = (x_3);
        Struct42 x_18 = (Struct42 {addr : (x_3).addr, info_write :
        (Bool)'(False), info_hit : (x_6).info_hit, info_way : (x_6).info_way,
        edir_hit : (x_6).edir_hit, edir_way : (x_6).edir_way, edir_slot :
        (x_6).edir_slot, info : (x_6).info, value_write : (Bool)'(False),
        value : unpack(0), may_victim : (x_6).may_victim, reps :
        (x_6).reps});
        Struct42 x_19 = (Struct42 {addr : (x_18).addr, info_write :
        (x_18).info_write, info_hit : (x_18).info_hit, info_way :
        (x_18).info_way, edir_hit : (x_18).edir_hit, edir_way :
        (x_18).edir_way, edir_slot : (x_18).edir_slot, info : (x_18).info,
        value_write : (Bool)'(True), value : (x_17).value, may_victim :
        (x_18).may_victim, reps :
        (x_18).reps});
        let x_22 = ?;
        if ((x_8).valid) begin
            let x_20 <- victims__000__setVictim(Struct44 {victim_idx :
            (x_8).data, victim_info : (x_19).info, victim_value :
            ((x_19).value_write ? ((x_19).value) : (x_9))});
            x_22 = x_9;
        end else begin
            let x_21 <- cache__000__valueRsLineRq(x_19);
            x_22 = x_21;
        end
        Struct18 x_23 = (Struct18 {enq_type : ((((Bit#(4))'(4'h8))[3:2]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : (((((Bit#(4))'(4'h8))[3:2])
        == ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : ((Bit#(4))'(4'h8))[1:0], enq_msg : Struct1 {id :
        (Bit#(6))'(6'h9), type_ : (Bool)'(True), addr : (x_17).addr, value :
        unpack(0)}});
        let x_24 <- makeEnq_parentChildren000(x_23);
        let x_25 <- releaseMSHR_000(x_4);
    endrule

    rule rule_exec_000_11;
        let x_0 <- deq_fifoL2E_000();
        Struct38 x_1 = ((x_0).lr_ir_pp);
        Bit#(4) x_2 = ((x_1).ir_msg_from);
        Struct1 x_3 = ((x_1).ir_msg);
        Bit#(2) x_4 = ((x_1).ir_mshr_id);
        Bool x_5 = ((x_1).ir_is_rs_rel);
        when (! (x_5), noAction);
        Struct39 x_6 = ((x_0).lr_ir);
        Struct10 x_7 = ((x_6).info);
        Struct37 x_8 = ((x_1).ir_by_victim);
        Vector#(4, Bit#(64)) x_9 = ((x_0).lr_value);
        let x_10 <- getMSHR_000(x_4);
        let x_11 <- getMSHRRq_000(x_4);
        Struct1 x_12 = (unpack(0));
        Vector#(4, Bit#(64)) x_13 = (unpack(0));
        Bool x_14 = ((x_7).mesi_owned);
        Bit#(3) x_15 = ((x_7).mesi_status);
        Struct15 x_16 = (Struct15 {dir_st : (((x_7).mesi_dir_st) ==
        ((Bit#(3))'(3'h0)) ? ((Bit#(3))'(3'h1)) : ((x_7).mesi_dir_st)),
        dir_excl : ((((x_7).mesi_dir_sharers)[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        ((((((x_7).mesi_dir_sharers)[3:1])[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        (((((((x_7).mesi_dir_sharers)[3:1])[2:1])[0:0]) == ((Bit#(1))'(1'h1))
        ? ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        ((((((((x_7).mesi_dir_sharers)[3:1])[2:1])[1:1])[0:0]) ==
        ((Bit#(1))'(1'h1)) ? ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        (unpack(0))))))))))))), dir_sharers : (x_7).mesi_dir_sharers});
        when ((x_2) == ((Bit#(4))'(4'h0)), noAction);
        when (((x_3).id) == ((Bit#(6))'(6'h8)), noAction);
        when (! ((x_3).type_), noAction);
        when (! (((Bit#(3))'(3'h2)) < (x_15)), noAction);
        Struct1 x_17 = (x_3);
        Struct42 x_18 = (Struct42 {addr : (x_3).addr, info_write :
        (Bool)'(False), info_hit : (x_6).info_hit, info_way : (x_6).info_way,
        edir_hit : (x_6).edir_hit, edir_way : (x_6).edir_way, edir_slot :
        (x_6).edir_slot, info : (x_6).info, value_write : (Bool)'(False),
        value : unpack(0), may_victim : (x_6).may_victim, reps :
        (x_6).reps});
        let x_20 = ?;
        if ((x_8).valid) begin
            x_20 = x_9;
        end else begin
            let x_19 <- cache__000__valueRsLineRq(unpack(0));
            x_20 = x_19;
        end
        let x_21 <- registerUL_000(Struct43 {r_id : x_4, r_ul_rsb :
        (Bool)'(True), r_ul_rsbTo : ((Bit#(4))'(4'h8))[1:0]});
        Struct18 x_22 = (Struct18 {enq_type : ((((Bit#(4))'(4'h0))[3:2]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : (((((Bit#(4))'(4'h0))[3:2])
        == ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : ((Bit#(4))'(4'h0))[1:0], enq_msg : Struct1 {id :
        (Bit#(6))'(6'ha), type_ : (Bool)'(False), addr : (x_17).addr, value :
        unpack(0)}});
        let x_23 <- makeEnq_parentChildren000(x_22);
    endrule

    rule rule_exec_000_12;
        let x_0 <- deq_fifoL2E_000();
        Struct38 x_1 = ((x_0).lr_ir_pp);
        Bit#(4) x_2 = ((x_1).ir_msg_from);
        Struct1 x_3 = ((x_1).ir_msg);
        Bit#(2) x_4 = ((x_1).ir_mshr_id);
        Bool x_5 = ((x_1).ir_is_rs_rel);
        when (! (x_5), noAction);
        Struct39 x_6 = ((x_0).lr_ir);
        Struct10 x_7 = ((x_6).info);
        Struct37 x_8 = ((x_1).ir_by_victim);
        Vector#(4, Bit#(64)) x_9 = ((x_0).lr_value);
        let x_10 <- getMSHR_000(x_4);
        let x_11 <- getMSHRRq_000(x_4);
        Struct1 x_12 = (unpack(0));
        Vector#(4, Bit#(64)) x_13 = (unpack(0));
        Bool x_14 = ((x_7).mesi_owned);
        Bit#(3) x_15 = ((x_7).mesi_status);
        Struct15 x_16 = (Struct15 {dir_st : (((x_7).mesi_dir_st) ==
        ((Bit#(3))'(3'h0)) ? ((Bit#(3))'(3'h1)) : ((x_7).mesi_dir_st)),
        dir_excl : ((((x_7).mesi_dir_sharers)[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        ((((((x_7).mesi_dir_sharers)[3:1])[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        (((((((x_7).mesi_dir_sharers)[3:1])[2:1])[0:0]) == ((Bit#(1))'(1'h1))
        ? ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        ((((((((x_7).mesi_dir_sharers)[3:1])[2:1])[1:1])[0:0]) ==
        ((Bit#(1))'(1'h1)) ? ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        (unpack(0))))))))))))), dir_sharers : (x_7).mesi_dir_sharers});
        when ((x_2) == ({((Bit#(2))'(2'h2)),((Bit#(2))'(2'h0))}),
        noAction);
        when (((x_3).id) == ((Bit#(6))'(6'hb)), noAction);
        when ((x_10).m_rsb, noAction);
        when (((x_11).type_) == ((Bool)'(False)), noAction);
        when (((x_11).id) == ((Bit#(6))'(6'h8)), noAction);
        when ((x_10).m_rsb, noAction);
        when ((x_3).type_, noAction);
        when ((Bool)'(True), noAction);
        Struct1 x_17 = (x_3);
        Struct1 x_18 = (x_11);
        Bit#(4) x_19 = ({((Bit#(2))'(2'h2)),(((x_10).m_qidx)[1:0])});
        Struct42 x_20 = (Struct42 {addr : (x_3).addr, info_write :
        (Bool)'(False), info_hit : (x_6).info_hit, info_way : (x_6).info_way,
        edir_hit : (x_6).edir_hit, edir_way : (x_6).edir_way, edir_slot :
        (x_6).edir_slot, info : (x_6).info, value_write : (Bool)'(False),
        value : unpack(0), may_victim : (x_6).may_victim, reps :
        (x_6).reps});
        Struct42 x_21 = (Struct42 {addr : (x_20).addr, info_write :
        (x_20).info_write, info_hit : (x_20).info_hit, info_way :
        (x_20).info_way, edir_hit : (x_20).edir_hit, edir_way :
        (x_20).edir_way, edir_slot : (x_20).edir_slot, info : (x_20).info,
        value_write : (Bool)'(True), value : (x_18).value, may_victim :
        (x_20).may_victim, reps : (x_20).reps});
        Struct42 x_22 = (Struct42 {addr : (x_21).addr, info_write :
        (Bool)'(True), info_hit : (x_21).info_hit, info_way :
        (x_21).info_way, edir_hit : (x_21).edir_hit, edir_way :
        (x_21).edir_way, edir_slot : (x_21).edir_slot, info : Struct10
        {mesi_owned : (Bool)'(True), mesi_status : ((x_21).info).mesi_status,
        mesi_dir_st : ((x_21).info).mesi_dir_st, mesi_dir_sharers :
        ((x_21).info).mesi_dir_sharers}, value_write : (x_21).value_write,
        value : (x_21).value, may_victim : (x_21).may_victim, reps :
        (x_21).reps});
        Struct42 x_23 = (Struct42 {addr : (x_22).addr, info_write :
        (Bool)'(True), info_hit : (x_22).info_hit, info_way :
        (x_22).info_way, edir_hit : (x_22).edir_hit, edir_way :
        (x_22).edir_way, edir_slot : (x_22).edir_slot, info : Struct10
        {mesi_owned : ((x_22).info).mesi_owned, mesi_status :
        (Bit#(3))'(3'h4), mesi_dir_st : ((x_22).info).mesi_dir_st,
        mesi_dir_sharers : ((x_22).info).mesi_dir_sharers}, value_write :
        (x_22).value_write, value : (x_22).value, may_victim :
        (x_22).may_victim, reps :
        (x_22).reps});
        let x_26 = ?;
        if ((x_8).valid) begin
            let x_24 <- victims__000__setVictim(Struct44 {victim_idx :
            (x_8).data, victim_info : (x_23).info, victim_value :
            ((x_23).value_write ? ((x_23).value) : (x_9))});
            x_26 = x_9;
        end else begin
            let x_25 <- cache__000__valueRsLineRq(x_23);
            x_26 = x_25;
        end
        let x_27 <- releaseMSHR_000(x_4);
        Struct18 x_28 = (Struct18 {enq_type : (((x_19)[3:2]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : ((((x_19)[3:2]) ==
        ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : (x_19)[1:0], enq_msg : Struct1 {id : (Bit#(6))'(6'h9),
        type_ : (Bool)'(True), addr : (x_17).addr, value : unpack(0)}});
        let x_29 <- makeEnq_parentChildren000(x_28);
    endrule

    rule rule_exec_000_130;
        let x_0 <- deq_fifoL2E_000();
        Struct38 x_1 = ((x_0).lr_ir_pp);
        Bit#(4) x_2 = ((x_1).ir_msg_from);
        Struct1 x_3 = ((x_1).ir_msg);
        Bit#(2) x_4 = ((x_1).ir_mshr_id);
        Bool x_5 = ((x_1).ir_is_rs_rel);
        when (! (x_5), noAction);
        Struct39 x_6 = ((x_0).lr_ir);
        Struct10 x_7 = ((x_6).info);
        Struct37 x_8 = ((x_1).ir_by_victim);
        Vector#(4, Bit#(64)) x_9 = ((x_0).lr_value);
        let x_10 <- getMSHR_000(x_4);
        let x_11 <- getMSHRRq_000(x_4);
        Struct1 x_12 = (unpack(0));
        Vector#(4, Bit#(64)) x_13 = (unpack(0));
        Bool x_14 = ((x_7).mesi_owned);
        Bit#(3) x_15 = ((x_7).mesi_status);
        Struct15 x_16 = (Struct15 {dir_st : (((x_7).mesi_dir_st) ==
        ((Bit#(3))'(3'h0)) ? ((Bit#(3))'(3'h1)) : ((x_7).mesi_dir_st)),
        dir_excl : ((((x_7).mesi_dir_sharers)[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        ((((((x_7).mesi_dir_sharers)[3:1])[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        (((((((x_7).mesi_dir_sharers)[3:1])[2:1])[0:0]) == ((Bit#(1))'(1'h1))
        ? ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        ((((((((x_7).mesi_dir_sharers)[3:1])[2:1])[1:1])[0:0]) ==
        ((Bit#(1))'(1'h1)) ? ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        (unpack(0))))))))))))), dir_sharers : (x_7).mesi_dir_sharers});
        when ((x_2) == ((Bit#(4))'(4'h8)), noAction);
        when (((x_3).id) == ((Bit#(6))'(6'hc)), noAction);
        when (! ((x_3).type_), noAction);
        when ((Bool)'(True), noAction);
        Struct1 x_17 = (x_3);
        Struct42 x_18 = (Struct42 {addr : (x_3).addr, info_write :
        (Bool)'(False), info_hit : (x_6).info_hit, info_way : (x_6).info_way,
        edir_hit : (x_6).edir_hit, edir_way : (x_6).edir_way, edir_slot :
        (x_6).edir_slot, info : (x_6).info, value_write : (Bool)'(False),
        value : unpack(0), may_victim : (x_6).may_victim, reps :
        (x_6).reps});
        Struct42 x_19 = (Struct42 {addr : (x_18).addr, info_write :
        (Bool)'(True), info_hit : (x_18).info_hit, info_way :
        (x_18).info_way, edir_hit : (x_18).edir_hit, edir_way :
        (x_18).edir_way, edir_slot : (x_18).edir_slot, info : Struct10
        {mesi_owned : ((x_18).info).mesi_owned, mesi_status :
        (Bit#(3))'(3'h1), mesi_dir_st : ((x_18).info).mesi_dir_st,
        mesi_dir_sharers : ((x_18).info).mesi_dir_sharers}, value_write :
        (x_18).value_write, value : (x_18).value, may_victim :
        (x_18).may_victim, reps : (x_18).reps});
        Struct42 x_20 = (Struct42 {addr : (x_19).addr, info_write :
        (Bool)'(True), info_hit : (x_19).info_hit, info_way :
        (x_19).info_way, edir_hit : (x_19).edir_hit, edir_way :
        (x_19).edir_way, edir_slot : (x_19).edir_slot, info : Struct10
        {mesi_owned : (Bool)'(False), mesi_status :
        ((x_19).info).mesi_status, mesi_dir_st : ((x_19).info).mesi_dir_st,
        mesi_dir_sharers : ((x_19).info).mesi_dir_sharers}, value_write :
        (x_19).value_write, value : (x_19).value, may_victim :
        (x_19).may_victim, reps :
        (x_19).reps});
        let x_23 = ?;
        if ((x_8).valid) begin
            let x_21 <- victims__000__setVictim(Struct44 {victim_idx :
            (x_8).data, victim_info : (x_20).info, victim_value :
            ((x_20).value_write ? ((x_20).value) : (x_9))});
            x_23 = x_9;
        end else begin
            let x_22 <- cache__000__valueRsLineRq(x_20);
            x_23 = x_22;
        end
        Struct18 x_24 = (Struct18 {enq_type : ((((Bit#(4))'(4'h4))[3:2]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : (((((Bit#(4))'(4'h4))[3:2])
        == ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : ((Bit#(4))'(4'h4))[1:0], enq_msg : Struct1 {id :
        (Bit#(6))'(6'hd), type_ : (Bool)'(True), addr : (x_17).addr, value :
        unpack(0)}});
        let x_25 <- makeEnq_parentChildren000(x_24);
        let x_26 <- releaseMSHR_000(x_4);
    endrule

    rule rule_exec_000_131;
        let x_0 <- deq_fifoL2E_000();
        Struct38 x_1 = ((x_0).lr_ir_pp);
        Bit#(4) x_2 = ((x_1).ir_msg_from);
        Struct1 x_3 = ((x_1).ir_msg);
        Bit#(2) x_4 = ((x_1).ir_mshr_id);
        Bool x_5 = ((x_1).ir_is_rs_rel);
        when (! (x_5), noAction);
        Struct39 x_6 = ((x_0).lr_ir);
        Struct10 x_7 = ((x_6).info);
        Struct37 x_8 = ((x_1).ir_by_victim);
        Vector#(4, Bit#(64)) x_9 = ((x_0).lr_value);
        let x_10 <- getMSHR_000(x_4);
        let x_11 <- getMSHRRq_000(x_4);
        Struct1 x_12 = (unpack(0));
        Vector#(4, Bit#(64)) x_13 = (unpack(0));
        Bool x_14 = ((x_7).mesi_owned);
        Bit#(3) x_15 = ((x_7).mesi_status);
        Struct15 x_16 = (Struct15 {dir_st : (((x_7).mesi_dir_st) ==
        ((Bit#(3))'(3'h0)) ? ((Bit#(3))'(3'h1)) : ((x_7).mesi_dir_st)),
        dir_excl : ((((x_7).mesi_dir_sharers)[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        ((((((x_7).mesi_dir_sharers)[3:1])[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        (((((((x_7).mesi_dir_sharers)[3:1])[2:1])[0:0]) == ((Bit#(1))'(1'h1))
        ? ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        ((((((((x_7).mesi_dir_sharers)[3:1])[2:1])[1:1])[0:0]) ==
        ((Bit#(1))'(1'h1)) ? ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        (unpack(0))))))))))))), dir_sharers : (x_7).mesi_dir_sharers});
        when ((x_2) == ((Bit#(4))'(4'h8)), noAction);
        when (((x_3).id) == ((Bit#(6))'(6'he)), noAction);
        when (! ((x_3).type_), noAction);
        when (! ((x_15) < ((Bit#(3))'(3'h3))), noAction);
        Struct1 x_17 = (x_3);
        Struct42 x_18 = (Struct42 {addr : (x_3).addr, info_write :
        (Bool)'(False), info_hit : (x_6).info_hit, info_way : (x_6).info_way,
        edir_hit : (x_6).edir_hit, edir_way : (x_6).edir_way, edir_slot :
        (x_6).edir_slot, info : (x_6).info, value_write : (Bool)'(False),
        value : unpack(0), may_victim : (x_6).may_victim, reps :
        (x_6).reps});
        Struct42 x_19 = (Struct42 {addr : (x_18).addr, info_write :
        (Bool)'(True), info_hit : (x_18).info_hit, info_way :
        (x_18).info_way, edir_hit : (x_18).edir_hit, edir_way :
        (x_18).edir_way, edir_slot : (x_18).edir_slot, info : Struct10
        {mesi_owned : ((x_18).info).mesi_owned, mesi_status :
        (Bit#(3))'(3'h1), mesi_dir_st : ((x_18).info).mesi_dir_st,
        mesi_dir_sharers : ((x_18).info).mesi_dir_sharers}, value_write :
        (x_18).value_write, value : (x_18).value, may_victim :
        (x_18).may_victim, reps : (x_18).reps});
        Struct42 x_20 = (Struct42 {addr : (x_19).addr, info_write :
        (Bool)'(True), info_hit : (x_19).info_hit, info_way :
        (x_19).info_way, edir_hit : (x_19).edir_hit, edir_way :
        (x_19).edir_way, edir_slot : (x_19).edir_slot, info : Struct10
        {mesi_owned : (Bool)'(False), mesi_status :
        ((x_19).info).mesi_status, mesi_dir_st : ((x_19).info).mesi_dir_st,
        mesi_dir_sharers : ((x_19).info).mesi_dir_sharers}, value_write :
        (x_19).value_write, value : (x_19).value, may_victim :
        (x_19).may_victim, reps :
        (x_19).reps});
        let x_23 = ?;
        if ((x_8).valid) begin
            let x_21 <- victims__000__setVictim(Struct44 {victim_idx :
            (x_8).data, victim_info : (x_20).info, victim_value :
            ((x_20).value_write ? ((x_20).value) : (x_9))});
            x_23 = x_9;
        end else begin
            let x_22 <- cache__000__valueRsLineRq(x_20);
            x_23 = x_22;
        end
        Struct18 x_24 = (Struct18 {enq_type : ((((Bit#(4))'(4'h4))[3:2]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : (((((Bit#(4))'(4'h4))[3:2])
        == ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : ((Bit#(4))'(4'h4))[1:0], enq_msg : Struct1 {id :
        (Bit#(6))'(6'hf), type_ : (Bool)'(True), addr : (x_17).addr, value :
        unpack(0)}});
        let x_25 <- makeEnq_parentChildren000(x_24);
        let x_26 <- releaseMSHR_000(x_4);
    endrule

    rule rule_exec_000_20;
        let x_0 <- victims__000__getFirstVictim();
        Bit#(64) x_1 = ((x_0).victim_addr);
        Struct10 x_2 = ((x_0).victim_info);
        Vector#(4, Bit#(64)) x_3 = ((x_0).victim_value);
        Struct1 x_4 = (Struct1 {id : unpack(0), type_ : (Bool)'(False), addr
        : x_1, value : unpack(0)});
        Struct14 x_5 = (Struct14 {m_is_ul : (Bool)'(True), m_qidx :
        unpack(0), m_rsb : (Bool)'(False), m_dl_rss_from : unpack(0),
        m_dl_rss_recv : unpack(0)});
        Struct1 x_6 = (unpack(0));
        Struct1 x_7 = (unpack(0));
        Vector#(4, Bit#(64)) x_8 = (unpack(0));
        Bool x_9 = ((x_2).mesi_owned);
        Bit#(3) x_10 = ((x_2).mesi_status);
        Struct15 x_11 = (Struct15 {dir_st : (((x_2).mesi_dir_st) ==
        ((Bit#(3))'(3'h0)) ? ((Bit#(3))'(3'h1)) : ((x_2).mesi_dir_st)),
        dir_excl : ((((x_2).mesi_dir_sharers)[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        ((((((x_2).mesi_dir_sharers)[3:1])[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        (((((((x_2).mesi_dir_sharers)[3:1])[2:1])[0:0]) == ((Bit#(1))'(1'h1))
        ? ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        ((((((((x_2).mesi_dir_sharers)[3:1])[2:1])[1:1])[0:0]) ==
        ((Bit#(1))'(1'h1)) ? ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        (unpack(0))))))))))))), dir_sharers : (x_2).mesi_dir_sharers});
        when (! ((x_4).type_), noAction);
        when (((x_9) == ((Bool)'(False))) && ((((Bit#(3))'(3'h0)) < (x_10))
        && ((x_10) < ((Bit#(3))'(3'h4)))), noAction);
        Struct18 x_12 = (Struct18 {enq_type : ((((Bit#(4))'(4'h0))[3:2]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : (((((Bit#(4))'(4'h0))[3:2])
        == ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : ((Bit#(4))'(4'h0))[1:0], enq_msg : Struct1 {id :
        (Bit#(6))'(6'h14), type_ : (Bool)'(False), addr : (x_4).addr, value :
        unpack(0)}});
        let x_13 <- makeEnq_parentChildren000(x_12);
        let x_14 <- setULImm_000(x_4);
        let x_15 <- victims__000__setVictimRq(x_1);
    endrule

    rule rule_exec_000_21;
        let x_0 <- victims__000__getFirstVictim();
        Bit#(64) x_1 = ((x_0).victim_addr);
        Struct10 x_2 = ((x_0).victim_info);
        Vector#(4, Bit#(64)) x_3 = ((x_0).victim_value);
        Struct1 x_4 = (Struct1 {id : unpack(0), type_ : (Bool)'(False), addr
        : x_1, value : unpack(0)});
        Struct14 x_5 = (Struct14 {m_is_ul : (Bool)'(True), m_qidx :
        unpack(0), m_rsb : (Bool)'(False), m_dl_rss_from : unpack(0),
        m_dl_rss_recv : unpack(0)});
        Struct1 x_6 = (unpack(0));
        Struct1 x_7 = (unpack(0));
        Vector#(4, Bit#(64)) x_8 = (unpack(0));
        Bool x_9 = ((x_2).mesi_owned);
        Bit#(3) x_10 = ((x_2).mesi_status);
        Struct15 x_11 = (Struct15 {dir_st : (((x_2).mesi_dir_st) ==
        ((Bit#(3))'(3'h0)) ? ((Bit#(3))'(3'h1)) : ((x_2).mesi_dir_st)),
        dir_excl : ((((x_2).mesi_dir_sharers)[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        ((((((x_2).mesi_dir_sharers)[3:1])[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        (((((((x_2).mesi_dir_sharers)[3:1])[2:1])[0:0]) == ((Bit#(1))'(1'h1))
        ? ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        ((((((((x_2).mesi_dir_sharers)[3:1])[2:1])[1:1])[0:0]) ==
        ((Bit#(1))'(1'h1)) ? ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        (unpack(0))))))))))))), dir_sharers : (x_2).mesi_dir_sharers});
        when (! ((x_4).type_), noAction);
        when (((Bit#(3))'(3'h0)) < (x_10), noAction);
        Struct18 x_12 = (Struct18 {enq_type : ((((Bit#(4))'(4'h0))[3:2]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : (((((Bit#(4))'(4'h0))[3:2])
        == ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : ((Bit#(4))'(4'h0))[1:0], enq_msg : Struct1 {id :
        (Bit#(6))'(6'h15), type_ : (Bool)'(False), addr : (x_4).addr, value :
        x_3}});
        let x_13 <- makeEnq_parentChildren000(x_12);
        let x_14 <- setULImm_000(x_4);
        let x_15 <- victims__000__setVictimRq(x_1);
    endrule

    // No methods in this module
endmodule

interface Module135;

endinterface

module mkModule135#(function Action victims__001__setVictimRq(Bit#(64) _),
    function Action setULImm_001(Struct1 _),
    function ActionValue#(Struct13) victims__001__getFirstVictim(),
    function Action victims__001__setVictim(Struct44 _),
    function Action registerUL_001(Struct43 _),
    function Action makeEnq_parentChildren001(Struct18 _),
    function ActionValue#(Vector#(4, Bit#(64))) cache__001__valueRsLineRq(Struct42 _),
    function ActionValue#(Struct1) getMSHRRq_001(Bit#(2) _),
    function ActionValue#(Struct14) getMSHR_001(Bit#(2) _),
    function ActionValue#(Struct41) deq_fifoL2E_001(),
    function ActionValue#(Struct13) victims__001__getVictim(Bit#(1) _),
    function Action enq_fifoL2E_001(Struct41 _),
    function ActionValue#(Struct39) cache__001__infoRsValueRq(Bit#(64) _),
    function ActionValue#(Struct38) deq_fifoI2L_001(),
    function Action enq_fifoI2L_001(Struct38 _),
    function Action cache__001__infoRq(Bit#(64) _),
    function ActionValue#(Struct38) deq_fifoN2I_001(),
    function ActionValue#(Struct36) getCRqSlot_001(Struct35 _),
    function ActionValue#(Bool) victims__001__hasVictim(),
    function ActionValue#(Struct2) deq_fifoCRqInput_001(),
    function Action releaseMSHR_001(Bit#(2) _),
    function Action victims__001__releaseVictim(Bit#(64) _),
    function ActionValue#(Struct35) getWait_001(),
    function Action startRelease_001(Bit#(2) _),
    function ActionValue#(Bit#(2)) getULReady_001(Bit#(64) _),
    function Action enq_fifoN2I_001(Struct38 _),
    function ActionValue#(Struct37) victims__001__findVictim(Bit#(64) _),
    function ActionValue#(Struct36) getPRqSlot_001(Struct35 _),
    function ActionValue#(Struct2) deq_fifoPInput_001())
    (Module135);

    rule rule_in_prq_001;
        let x_0 <- deq_fifoPInput_001();
        Bit#(4) x_1 = ((x_0).in_msg_from);
        when ((x_1) == ({((Bit#(2))'(2'h2)),((Bit#(2))'(2'h1))}),
        noAction);
        Struct1 x_2 = ((x_0).in_msg);
        when (! ((x_2).type_), noAction);
        let x_3 <- getPRqSlot_001(Struct35 {r_id : unpack(0), r_msg : x_2,
        r_msg_from : (x_0).in_msg_from});
        when ((x_3).s_has_slot,
        noAction);
        if (! ((x_3).s_conflict)) begin
            let x_4 <- victims__001__findVictim((x_2).addr);
            Struct38 x_5 = (Struct38 {ir_is_rs_rel : (Bool)'(False), ir_msg :
            (x_0).in_msg, ir_msg_from : x_1, ir_mshr_id : (x_3).s_id,
            ir_by_victim : x_4});
            let x_6 <- enq_fifoN2I_001(x_5);
        end else begin

        end
    endrule

    rule rule_in_prs_001;
        let x_0 <- deq_fifoPInput_001();
        Bit#(4) x_1 = ((x_0).in_msg_from);
        when ((x_1) == ({((Bit#(2))'(2'h2)),((Bit#(2))'(2'h1))}),
        noAction);
        Struct1 x_2 = ((x_0).in_msg);
        when (((x_2).type_) && (! (((x_2).id) == ((Bit#(6))'(6'h16)))),
        noAction);
        let x_3 <- getULReady_001((x_2).addr);
        let x_4 <- startRelease_001(x_3);
        let x_5 <- victims__001__findVictim((x_2).addr);
        Struct38 x_6 = (Struct38 {ir_is_rs_rel : (Bool)'(False), ir_msg :
        (x_0).in_msg, ir_msg_from : x_1, ir_mshr_id : x_3, ir_by_victim :
        x_5});
        let x_7 <- enq_fifoN2I_001(x_6);
    endrule

    rule rule_in_retry_001;
        let x_0 <- getWait_001();
        Struct1 x_1 = ((x_0).r_msg);
        let x_2 <- victims__001__findVictim((x_1).addr);
        Struct38 x_3 = (Struct38 {ir_is_rs_rel : (Bool)'(False), ir_msg :
        x_1, ir_msg_from : (x_0).r_msg_from, ir_mshr_id : (x_0).r_id,
        ir_by_victim : x_2});
        let x_4 <- enq_fifoN2I_001(x_3);
    endrule

    rule rule_in_invrs_001;
        let x_0 <- deq_fifoPInput_001();
        Bit#(4) x_1 = ((x_0).in_msg_from);
        when ((x_1) == ({((Bit#(2))'(2'h2)),((Bit#(2))'(2'h1))}),
        noAction);
        Struct1 x_2 = ((x_0).in_msg);
        when (((x_2).type_) && (((x_2).id) == ((Bit#(6))'(6'h16))),
        noAction);
        let x_3 <- getULReady_001((x_2).addr);
        let x_4 <- victims__001__releaseVictim((x_2).addr);
        let x_5 <- releaseMSHR_001(x_3);
    endrule

    rule rule_in_crq_001;
        let x_0 <- deq_fifoCRqInput_001();
        Bit#(4) x_1 = ((x_0).in_msg_from);
        when (((x_1)[3:2]) == ((Bit#(2))'(2'h0)), noAction);
        Struct1 x_2 = ((x_0).in_msg);
        when (! ((x_2).type_), noAction);
        let x_3 <- victims__001__hasVictim();
        when (! (x_3), noAction);
        let x_4 <- getCRqSlot_001(Struct35 {r_id : unpack(0), r_msg : x_2,
        r_msg_from : x_1});
        when ((x_4).s_has_slot,
        noAction);
        if (! ((x_4).s_conflict)) begin
            let x_5 <- victims__001__findVictim((x_2).addr);
            Struct38 x_6 = (Struct38 {ir_is_rs_rel : (Bool)'(False), ir_msg :
            (x_0).in_msg, ir_msg_from : x_1, ir_mshr_id : (x_4).s_id,
            ir_by_victim : x_5});
            let x_7 <- enq_fifoN2I_001(x_6);
        end else begin

        end
    endrule

    rule rule_ir_cache_001;
        let x_0 <- deq_fifoN2I_001();
        when (! (((x_0).ir_by_victim).valid), noAction);
        Struct1 x_1 = ((x_0).ir_msg);
        let x_2 <- cache__001__infoRq((x_1).addr);
        let x_3 <- enq_fifoI2L_001(x_0);
    endrule

    rule rule_ir_victims_001;
        let x_0 <- deq_fifoN2I_001();
        when (((x_0).ir_by_victim).valid, noAction);
        let x_1 <- enq_fifoI2L_001(x_0);
    endrule

    rule rule_lr_cache_001;
        let x_0 <- deq_fifoI2L_001();
        when (! (((x_0).ir_by_victim).valid), noAction);
        let x_1 <- cache__001__infoRsValueRq(((x_0).ir_msg).addr);
        Struct41 x_2 = (Struct41 {lr_ir_pp : x_0, lr_ir : x_1, lr_value :
        unpack(0)});
        let x_3 <- enq_fifoL2E_001(x_2);
    endrule

    rule rule_lr_victims_001;
        let x_0 <- deq_fifoI2L_001();
        when (((x_0).ir_by_victim).valid, noAction);
        Bit#(1) x_1 = (((x_0).ir_by_victim).data);
        let x_2 <- victims__001__getVictim(x_1);
        Struct39 x_3 = (Struct39 {info_index : unpack(0), info_hit :
        unpack(0), info_way : unpack(0), edir_hit : unpack(0), edir_way :
        unpack(0), edir_slot : unpack(0), info : (x_2).victim_info,
        may_victim : unpack(0), reps : unpack(0)});
        Struct41 x_4 = (Struct41 {lr_ir_pp : x_0, lr_ir : x_3, lr_value :
        (x_2).victim_value});
        let x_5 <- enq_fifoL2E_001(x_4);
    endrule

    rule rule_exec_001_00;
        let x_0 <- deq_fifoL2E_001();
        Struct38 x_1 = ((x_0).lr_ir_pp);
        Bit#(4) x_2 = ((x_1).ir_msg_from);
        Struct1 x_3 = ((x_1).ir_msg);
        Bit#(2) x_4 = ((x_1).ir_mshr_id);
        Bool x_5 = ((x_1).ir_is_rs_rel);
        when (! (x_5), noAction);
        Struct39 x_6 = ((x_0).lr_ir);
        Struct10 x_7 = ((x_6).info);
        Struct37 x_8 = ((x_1).ir_by_victim);
        Vector#(4, Bit#(64)) x_9 = ((x_0).lr_value);
        let x_10 <- getMSHR_001(x_4);
        let x_11 <- getMSHRRq_001(x_4);
        Struct1 x_12 = (unpack(0));
        Vector#(4, Bit#(64)) x_13 = (unpack(0));
        Bool x_14 = ((x_7).mesi_owned);
        Bit#(3) x_15 = ((x_7).mesi_status);
        Struct15 x_16 = (Struct15 {dir_st : (((x_7).mesi_dir_st) ==
        ((Bit#(3))'(3'h0)) ? ((Bit#(3))'(3'h1)) : ((x_7).mesi_dir_st)),
        dir_excl : ((((x_7).mesi_dir_sharers)[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        ((((((x_7).mesi_dir_sharers)[3:1])[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        (((((((x_7).mesi_dir_sharers)[3:1])[2:1])[0:0]) == ((Bit#(1))'(1'h1))
        ? ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        ((((((((x_7).mesi_dir_sharers)[3:1])[2:1])[1:1])[0:0]) ==
        ((Bit#(1))'(1'h1)) ? ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        (unpack(0))))))))))))), dir_sharers : (x_7).mesi_dir_sharers});
        when ((x_2) == ((Bit#(4))'(4'h0)), noAction);
        when (((x_3).id) == ((Bit#(6))'(6'h0)), noAction);
        when (! ((x_3).type_), noAction);
        when (! ((x_15) < ((Bit#(3))'(3'h2))), noAction);
        Struct1 x_17 = (x_3);
        Struct42 x_18 = (Struct42 {addr : (x_3).addr, info_write :
        (Bool)'(False), info_hit : (x_6).info_hit, info_way : (x_6).info_way,
        edir_hit : (x_6).edir_hit, edir_way : (x_6).edir_way, edir_slot :
        (x_6).edir_slot, info : (x_6).info, value_write : (Bool)'(False),
        value : unpack(0), may_victim : (x_6).may_victim, reps :
        (x_6).reps});
        let x_20 = ?;
        if ((x_8).valid) begin
            x_20 = x_9;
        end else begin
            let x_19 <- cache__001__valueRsLineRq(unpack(0));
            x_20 = x_19;
        end
        Struct18 x_21 = (Struct18 {enq_type : ((((Bit#(4))'(4'h8))[3:2]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : (((((Bit#(4))'(4'h8))[3:2])
        == ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : ((Bit#(4))'(4'h8))[1:0], enq_msg : Struct1 {id :
        (Bit#(6))'(6'h1), type_ : (Bool)'(True), addr : (x_17).addr, value :
        x_20}});
        let x_22 <- makeEnq_parentChildren001(x_21);
        let x_23 <- releaseMSHR_001(x_4);
    endrule

    rule rule_exec_001_01;
        let x_0 <- deq_fifoL2E_001();
        Struct38 x_1 = ((x_0).lr_ir_pp);
        Bit#(4) x_2 = ((x_1).ir_msg_from);
        Struct1 x_3 = ((x_1).ir_msg);
        Bit#(2) x_4 = ((x_1).ir_mshr_id);
        Bool x_5 = ((x_1).ir_is_rs_rel);
        when (! (x_5), noAction);
        Struct39 x_6 = ((x_0).lr_ir);
        Struct10 x_7 = ((x_6).info);
        Struct37 x_8 = ((x_1).ir_by_victim);
        Vector#(4, Bit#(64)) x_9 = ((x_0).lr_value);
        let x_10 <- getMSHR_001(x_4);
        let x_11 <- getMSHRRq_001(x_4);
        Struct1 x_12 = (unpack(0));
        Vector#(4, Bit#(64)) x_13 = (unpack(0));
        Bool x_14 = ((x_7).mesi_owned);
        Bit#(3) x_15 = ((x_7).mesi_status);
        Struct15 x_16 = (Struct15 {dir_st : (((x_7).mesi_dir_st) ==
        ((Bit#(3))'(3'h0)) ? ((Bit#(3))'(3'h1)) : ((x_7).mesi_dir_st)),
        dir_excl : ((((x_7).mesi_dir_sharers)[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        ((((((x_7).mesi_dir_sharers)[3:1])[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        (((((((x_7).mesi_dir_sharers)[3:1])[2:1])[0:0]) == ((Bit#(1))'(1'h1))
        ? ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        ((((((((x_7).mesi_dir_sharers)[3:1])[2:1])[1:1])[0:0]) ==
        ((Bit#(1))'(1'h1)) ? ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        (unpack(0))))))))))))), dir_sharers : (x_7).mesi_dir_sharers});
        when ((x_2) == ((Bit#(4))'(4'h0)), noAction);
        when (((x_3).id) == ((Bit#(6))'(6'h0)), noAction);
        when (! ((x_3).type_), noAction);
        when (! (((Bit#(3))'(3'h1)) < (x_15)), noAction);
        Struct1 x_17 = (x_3);
        Struct42 x_18 = (Struct42 {addr : (x_3).addr, info_write :
        (Bool)'(False), info_hit : (x_6).info_hit, info_way : (x_6).info_way,
        edir_hit : (x_6).edir_hit, edir_way : (x_6).edir_way, edir_slot :
        (x_6).edir_slot, info : (x_6).info, value_write : (Bool)'(False),
        value : unpack(0), may_victim : (x_6).may_victim, reps :
        (x_6).reps});
        let x_20 = ?;
        if ((x_8).valid) begin
            x_20 = x_9;
        end else begin
            let x_19 <- cache__001__valueRsLineRq(unpack(0));
            x_20 = x_19;
        end
        let x_21 <- registerUL_001(Struct43 {r_id : x_4, r_ul_rsb :
        (Bool)'(True), r_ul_rsbTo : ((Bit#(4))'(4'h8))[1:0]});
        Struct18 x_22 = (Struct18 {enq_type : ((((Bit#(4))'(4'h1))[3:2]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : (((((Bit#(4))'(4'h1))[3:2])
        == ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : ((Bit#(4))'(4'h1))[1:0], enq_msg : Struct1 {id :
        (Bit#(6))'(6'h2), type_ : (Bool)'(False), addr : (x_17).addr, value :
        unpack(0)}});
        let x_23 <- makeEnq_parentChildren001(x_22);
    endrule

    rule rule_exec_001_020;
        let x_0 <- deq_fifoL2E_001();
        Struct38 x_1 = ((x_0).lr_ir_pp);
        Bit#(4) x_2 = ((x_1).ir_msg_from);
        Struct1 x_3 = ((x_1).ir_msg);
        Bit#(2) x_4 = ((x_1).ir_mshr_id);
        Bool x_5 = ((x_1).ir_is_rs_rel);
        when (! (x_5), noAction);
        Struct39 x_6 = ((x_0).lr_ir);
        Struct10 x_7 = ((x_6).info);
        Struct37 x_8 = ((x_1).ir_by_victim);
        Vector#(4, Bit#(64)) x_9 = ((x_0).lr_value);
        let x_10 <- getMSHR_001(x_4);
        let x_11 <- getMSHRRq_001(x_4);
        Struct1 x_12 = (unpack(0));
        Vector#(4, Bit#(64)) x_13 = (unpack(0));
        Bool x_14 = ((x_7).mesi_owned);
        Bit#(3) x_15 = ((x_7).mesi_status);
        Struct15 x_16 = (Struct15 {dir_st : (((x_7).mesi_dir_st) ==
        ((Bit#(3))'(3'h0)) ? ((Bit#(3))'(3'h1)) : ((x_7).mesi_dir_st)),
        dir_excl : ((((x_7).mesi_dir_sharers)[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        ((((((x_7).mesi_dir_sharers)[3:1])[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        (((((((x_7).mesi_dir_sharers)[3:1])[2:1])[0:0]) == ((Bit#(1))'(1'h1))
        ? ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        ((((((((x_7).mesi_dir_sharers)[3:1])[2:1])[1:1])[0:0]) ==
        ((Bit#(1))'(1'h1)) ? ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        (unpack(0))))))))))))), dir_sharers : (x_7).mesi_dir_sharers});
        when ((x_2) == ({((Bit#(2))'(2'h2)),((Bit#(2))'(2'h1))}),
        noAction);
        when (((x_3).id) == ((Bit#(6))'(6'h3)), noAction);
        when ((x_10).m_rsb, noAction);
        when (((x_11).type_) == ((Bool)'(False)), noAction);
        when (((x_11).id) == ((Bit#(6))'(6'h0)), noAction);
        when ((x_10).m_rsb, noAction);
        when ((x_3).type_, noAction);
        when ((Bool)'(True), noAction);
        Struct1 x_17 = (x_3);
        Struct1 x_18 = (x_11);
        Bit#(4) x_19 = ({((Bit#(2))'(2'h2)),(((x_10).m_qidx)[1:0])});
        Struct42 x_20 = (Struct42 {addr : (x_3).addr, info_write :
        (Bool)'(False), info_hit : (x_6).info_hit, info_way : (x_6).info_way,
        edir_hit : (x_6).edir_hit, edir_way : (x_6).edir_way, edir_slot :
        (x_6).edir_slot, info : (x_6).info, value_write : (Bool)'(False),
        value : unpack(0), may_victim : (x_6).may_victim, reps :
        (x_6).reps});
        Struct42 x_21 = (Struct42 {addr : (x_20).addr, info_write :
        (Bool)'(True), info_hit : (x_20).info_hit, info_way :
        (x_20).info_way, edir_hit : (x_20).edir_hit, edir_way :
        (x_20).edir_way, edir_slot : (x_20).edir_slot, info : Struct10
        {mesi_owned : ((x_20).info).mesi_owned, mesi_status :
        (Bit#(3))'(3'h2), mesi_dir_st : ((x_20).info).mesi_dir_st,
        mesi_dir_sharers : ((x_20).info).mesi_dir_sharers}, value_write :
        (x_20).value_write, value : (x_20).value, may_victim :
        (x_20).may_victim, reps : (x_20).reps});
        Struct42 x_22 = (Struct42 {addr : (x_21).addr, info_write :
        (x_21).info_write, info_hit : (x_21).info_hit, info_way :
        (x_21).info_way, edir_hit : (x_21).edir_hit, edir_way :
        (x_21).edir_way, edir_slot : (x_21).edir_slot, info : (x_21).info,
        value_write : (Bool)'(True), value : (x_17).value, may_victim :
        (x_21).may_victim, reps :
        (x_21).reps});
        let x_25 = ?;
        if ((x_8).valid) begin
            let x_23 <- victims__001__setVictim(Struct44 {victim_idx :
            (x_8).data, victim_info : (x_22).info, victim_value :
            ((x_22).value_write ? ((x_22).value) : (x_9))});
            x_25 = x_9;
        end else begin
            let x_24 <- cache__001__valueRsLineRq(x_22);
            x_25 = x_24;
        end
        let x_26 <- releaseMSHR_001(x_4);
        Struct18 x_27 = (Struct18 {enq_type : (((x_19)[3:2]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : ((((x_19)[3:2]) ==
        ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : (x_19)[1:0], enq_msg : Struct1 {id : (Bit#(6))'(6'h1),
        type_ : (Bool)'(True), addr : (x_17).addr, value :
        (x_17).value}});
        let x_28 <- makeEnq_parentChildren001(x_27);
    endrule

    rule rule_exec_001_021;
        let x_0 <- deq_fifoL2E_001();
        Struct38 x_1 = ((x_0).lr_ir_pp);
        Bit#(4) x_2 = ((x_1).ir_msg_from);
        Struct1 x_3 = ((x_1).ir_msg);
        Bit#(2) x_4 = ((x_1).ir_mshr_id);
        Bool x_5 = ((x_1).ir_is_rs_rel);
        when (! (x_5), noAction);
        Struct39 x_6 = ((x_0).lr_ir);
        Struct10 x_7 = ((x_6).info);
        Struct37 x_8 = ((x_1).ir_by_victim);
        Vector#(4, Bit#(64)) x_9 = ((x_0).lr_value);
        let x_10 <- getMSHR_001(x_4);
        let x_11 <- getMSHRRq_001(x_4);
        Struct1 x_12 = (unpack(0));
        Vector#(4, Bit#(64)) x_13 = (unpack(0));
        Bool x_14 = ((x_7).mesi_owned);
        Bit#(3) x_15 = ((x_7).mesi_status);
        Struct15 x_16 = (Struct15 {dir_st : (((x_7).mesi_dir_st) ==
        ((Bit#(3))'(3'h0)) ? ((Bit#(3))'(3'h1)) : ((x_7).mesi_dir_st)),
        dir_excl : ((((x_7).mesi_dir_sharers)[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        ((((((x_7).mesi_dir_sharers)[3:1])[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        (((((((x_7).mesi_dir_sharers)[3:1])[2:1])[0:0]) == ((Bit#(1))'(1'h1))
        ? ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        ((((((((x_7).mesi_dir_sharers)[3:1])[2:1])[1:1])[0:0]) ==
        ((Bit#(1))'(1'h1)) ? ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        (unpack(0))))))))))))), dir_sharers : (x_7).mesi_dir_sharers});
        when ((x_2) == ({((Bit#(2))'(2'h2)),((Bit#(2))'(2'h1))}),
        noAction);
        when (((x_3).id) == ((Bit#(6))'(6'h4)), noAction);
        when ((x_10).m_rsb, noAction);
        when (((x_11).type_) == ((Bool)'(False)), noAction);
        when (((x_11).id) == ((Bit#(6))'(6'h0)), noAction);
        when ((x_10).m_rsb, noAction);
        when ((x_3).type_, noAction);
        when ((Bool)'(True), noAction);
        Struct1 x_17 = (x_3);
        Struct1 x_18 = (x_11);
        Bit#(4) x_19 = ({((Bit#(2))'(2'h2)),(((x_10).m_qidx)[1:0])});
        Struct42 x_20 = (Struct42 {addr : (x_3).addr, info_write :
        (Bool)'(False), info_hit : (x_6).info_hit, info_way : (x_6).info_way,
        edir_hit : (x_6).edir_hit, edir_way : (x_6).edir_way, edir_slot :
        (x_6).edir_slot, info : (x_6).info, value_write : (Bool)'(False),
        value : unpack(0), may_victim : (x_6).may_victim, reps :
        (x_6).reps});
        Struct42 x_21 = (Struct42 {addr : (x_20).addr, info_write :
        (Bool)'(True), info_hit : (x_20).info_hit, info_way :
        (x_20).info_way, edir_hit : (x_20).edir_hit, edir_way :
        (x_20).edir_way, edir_slot : (x_20).edir_slot, info : Struct10
        {mesi_owned : ((x_20).info).mesi_owned, mesi_status :
        (Bit#(3))'(3'h3), mesi_dir_st : ((x_20).info).mesi_dir_st,
        mesi_dir_sharers : ((x_20).info).mesi_dir_sharers}, value_write :
        (x_20).value_write, value : (x_20).value, may_victim :
        (x_20).may_victim, reps : (x_20).reps});
        Struct42 x_22 = (Struct42 {addr : (x_21).addr, info_write :
        (x_21).info_write, info_hit : (x_21).info_hit, info_way :
        (x_21).info_way, edir_hit : (x_21).edir_hit, edir_way :
        (x_21).edir_way, edir_slot : (x_21).edir_slot, info : (x_21).info,
        value_write : (Bool)'(True), value : (x_17).value, may_victim :
        (x_21).may_victim, reps :
        (x_21).reps});
        let x_25 = ?;
        if ((x_8).valid) begin
            let x_23 <- victims__001__setVictim(Struct44 {victim_idx :
            (x_8).data, victim_info : (x_22).info, victim_value :
            ((x_22).value_write ? ((x_22).value) : (x_9))});
            x_25 = x_9;
        end else begin
            let x_24 <- cache__001__valueRsLineRq(x_22);
            x_25 = x_24;
        end
        let x_26 <- releaseMSHR_001(x_4);
        Struct18 x_27 = (Struct18 {enq_type : (((x_19)[3:2]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : ((((x_19)[3:2]) ==
        ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : (x_19)[1:0], enq_msg : Struct1 {id : (Bit#(6))'(6'h1),
        type_ : (Bool)'(True), addr : (x_17).addr, value :
        (x_17).value}});
        let x_28 <- makeEnq_parentChildren001(x_27);
    endrule

    rule rule_exec_001_03;
        let x_0 <- deq_fifoL2E_001();
        Struct38 x_1 = ((x_0).lr_ir_pp);
        Bit#(4) x_2 = ((x_1).ir_msg_from);
        Struct1 x_3 = ((x_1).ir_msg);
        Bit#(2) x_4 = ((x_1).ir_mshr_id);
        Bool x_5 = ((x_1).ir_is_rs_rel);
        when (! (x_5), noAction);
        Struct39 x_6 = ((x_0).lr_ir);
        Struct10 x_7 = ((x_6).info);
        Struct37 x_8 = ((x_1).ir_by_victim);
        Vector#(4, Bit#(64)) x_9 = ((x_0).lr_value);
        let x_10 <- getMSHR_001(x_4);
        let x_11 <- getMSHRRq_001(x_4);
        Struct1 x_12 = (unpack(0));
        Vector#(4, Bit#(64)) x_13 = (unpack(0));
        Bool x_14 = ((x_7).mesi_owned);
        Bit#(3) x_15 = ((x_7).mesi_status);
        Struct15 x_16 = (Struct15 {dir_st : (((x_7).mesi_dir_st) ==
        ((Bit#(3))'(3'h0)) ? ((Bit#(3))'(3'h1)) : ((x_7).mesi_dir_st)),
        dir_excl : ((((x_7).mesi_dir_sharers)[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        ((((((x_7).mesi_dir_sharers)[3:1])[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        (((((((x_7).mesi_dir_sharers)[3:1])[2:1])[0:0]) == ((Bit#(1))'(1'h1))
        ? ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        ((((((((x_7).mesi_dir_sharers)[3:1])[2:1])[1:1])[0:0]) ==
        ((Bit#(1))'(1'h1)) ? ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        (unpack(0))))))))))))), dir_sharers : (x_7).mesi_dir_sharers});
        when ((x_2) == ((Bit#(4))'(4'h9)), noAction);
        when (((x_3).id) == ((Bit#(6))'(6'h5)), noAction);
        when (! ((x_3).type_), noAction);
        when (! ((x_15) < ((Bit#(3))'(3'h2))), noAction);
        Struct1 x_17 = (x_3);
        Struct42 x_18 = (Struct42 {addr : (x_3).addr, info_write :
        (Bool)'(False), info_hit : (x_6).info_hit, info_way : (x_6).info_way,
        edir_hit : (x_6).edir_hit, edir_way : (x_6).edir_way, edir_slot :
        (x_6).edir_slot, info : (x_6).info, value_write : (Bool)'(False),
        value : unpack(0), may_victim : (x_6).may_victim, reps :
        (x_6).reps});
        Struct42 x_19 = (Struct42 {addr : (x_18).addr, info_write :
        (Bool)'(True), info_hit : (x_18).info_hit, info_way :
        (x_18).info_way, edir_hit : (x_18).edir_hit, edir_way :
        (x_18).edir_way, edir_slot : (x_18).edir_slot, info : Struct10
        {mesi_owned : ((x_18).info).mesi_owned, mesi_status :
        (Bit#(3))'(3'h2), mesi_dir_st : ((x_18).info).mesi_dir_st,
        mesi_dir_sharers : ((x_18).info).mesi_dir_sharers}, value_write :
        (x_18).value_write, value : (x_18).value, may_victim :
        (x_18).may_victim, reps : (x_18).reps});
        Struct42 x_20 = (Struct42 {addr : (x_19).addr, info_write :
        (Bool)'(True), info_hit : (x_19).info_hit, info_way :
        (x_19).info_way, edir_hit : (x_19).edir_hit, edir_way :
        (x_19).edir_way, edir_slot : (x_19).edir_slot, info : Struct10
        {mesi_owned : (Bool)'(False), mesi_status :
        ((x_19).info).mesi_status, mesi_dir_st : ((x_19).info).mesi_dir_st,
        mesi_dir_sharers : ((x_19).info).mesi_dir_sharers}, value_write :
        (x_19).value_write, value : (x_19).value, may_victim :
        (x_19).may_victim, reps :
        (x_19).reps});
        let x_23 = ?;
        if ((x_8).valid) begin
            let x_21 <- victims__001__setVictim(Struct44 {victim_idx :
            (x_8).data, victim_info : (x_20).info, victim_value :
            ((x_20).value_write ? ((x_20).value) : (x_9))});
            x_23 = x_9;
        end else begin
            let x_22 <- cache__001__valueRsLineRq(x_20);
            x_23 = x_22;
        end
        Struct18 x_24 = (Struct18 {enq_type : ((((Bit#(4))'(4'h5))[3:2]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : (((((Bit#(4))'(4'h5))[3:2])
        == ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : ((Bit#(4))'(4'h5))[1:0], enq_msg : Struct1 {id :
        (Bit#(6))'(6'h6), type_ : (Bool)'(True), addr : (x_17).addr, value :
        x_23}});
        let x_25 <- makeEnq_parentChildren001(x_24);
        let x_26 <- releaseMSHR_001(x_4);
    endrule

    rule rule_exec_001_100;
        let x_0 <- deq_fifoL2E_001();
        Struct38 x_1 = ((x_0).lr_ir_pp);
        Bit#(4) x_2 = ((x_1).ir_msg_from);
        Struct1 x_3 = ((x_1).ir_msg);
        Bit#(2) x_4 = ((x_1).ir_mshr_id);
        Bool x_5 = ((x_1).ir_is_rs_rel);
        when (! (x_5), noAction);
        Struct39 x_6 = ((x_0).lr_ir);
        Struct10 x_7 = ((x_6).info);
        Struct37 x_8 = ((x_1).ir_by_victim);
        Vector#(4, Bit#(64)) x_9 = ((x_0).lr_value);
        let x_10 <- getMSHR_001(x_4);
        let x_11 <- getMSHRRq_001(x_4);
        Struct1 x_12 = (unpack(0));
        Vector#(4, Bit#(64)) x_13 = (unpack(0));
        Bool x_14 = ((x_7).mesi_owned);
        Bit#(3) x_15 = ((x_7).mesi_status);
        Struct15 x_16 = (Struct15 {dir_st : (((x_7).mesi_dir_st) ==
        ((Bit#(3))'(3'h0)) ? ((Bit#(3))'(3'h1)) : ((x_7).mesi_dir_st)),
        dir_excl : ((((x_7).mesi_dir_sharers)[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        ((((((x_7).mesi_dir_sharers)[3:1])[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        (((((((x_7).mesi_dir_sharers)[3:1])[2:1])[0:0]) == ((Bit#(1))'(1'h1))
        ? ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        ((((((((x_7).mesi_dir_sharers)[3:1])[2:1])[1:1])[0:0]) ==
        ((Bit#(1))'(1'h1)) ? ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        (unpack(0))))))))))))), dir_sharers : (x_7).mesi_dir_sharers});
        when ((x_2) == ((Bit#(4))'(4'h0)), noAction);
        when (((x_3).id) == ((Bit#(6))'(6'h8)), noAction);
        when (! ((x_3).type_), noAction);
        when ((x_15) == ((Bit#(3))'(3'h3)), noAction);
        Struct1 x_17 = (x_3);
        Struct42 x_18 = (Struct42 {addr : (x_3).addr, info_write :
        (Bool)'(False), info_hit : (x_6).info_hit, info_way : (x_6).info_way,
        edir_hit : (x_6).edir_hit, edir_way : (x_6).edir_way, edir_slot :
        (x_6).edir_slot, info : (x_6).info, value_write : (Bool)'(False),
        value : unpack(0), may_victim : (x_6).may_victim, reps :
        (x_6).reps});
        Struct42 x_19 = (Struct42 {addr : (x_18).addr, info_write :
        (x_18).info_write, info_hit : (x_18).info_hit, info_way :
        (x_18).info_way, edir_hit : (x_18).edir_hit, edir_way :
        (x_18).edir_way, edir_slot : (x_18).edir_slot, info : (x_18).info,
        value_write : (Bool)'(True), value : (x_17).value, may_victim :
        (x_18).may_victim, reps : (x_18).reps});
        Struct42 x_20 = (Struct42 {addr : (x_19).addr, info_write :
        (Bool)'(True), info_hit : (x_19).info_hit, info_way :
        (x_19).info_way, edir_hit : (x_19).edir_hit, edir_way :
        (x_19).edir_way, edir_slot : (x_19).edir_slot, info : Struct10
        {mesi_owned : ((x_19).info).mesi_owned, mesi_status :
        (Bit#(3))'(3'h4), mesi_dir_st : ((x_19).info).mesi_dir_st,
        mesi_dir_sharers : ((x_19).info).mesi_dir_sharers}, value_write :
        (x_19).value_write, value : (x_19).value, may_victim :
        (x_19).may_victim, reps : (x_19).reps});
        Struct42 x_21 = (Struct42 {addr : (x_20).addr, info_write :
        (Bool)'(True), info_hit : (x_20).info_hit, info_way :
        (x_20).info_way, edir_hit : (x_20).edir_hit, edir_way :
        (x_20).edir_way, edir_slot : (x_20).edir_slot, info : Struct10
        {mesi_owned : (Bool)'(True), mesi_status : ((x_20).info).mesi_status,
        mesi_dir_st : ((x_20).info).mesi_dir_st, mesi_dir_sharers :
        ((x_20).info).mesi_dir_sharers}, value_write : (x_20).value_write,
        value : (x_20).value, may_victim : (x_20).may_victim, reps :
        (x_20).reps});
        let x_24 = ?;
        if ((x_8).valid) begin
            let x_22 <- victims__001__setVictim(Struct44 {victim_idx :
            (x_8).data, victim_info : (x_21).info, victim_value :
            ((x_21).value_write ? ((x_21).value) : (x_9))});
            x_24 = x_9;
        end else begin
            let x_23 <- cache__001__valueRsLineRq(x_21);
            x_24 = x_23;
        end
        Struct18 x_25 = (Struct18 {enq_type : ((((Bit#(4))'(4'h8))[3:2]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : (((((Bit#(4))'(4'h8))[3:2])
        == ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : ((Bit#(4))'(4'h8))[1:0], enq_msg : Struct1 {id :
        (Bit#(6))'(6'h9), type_ : (Bool)'(True), addr : (x_17).addr, value :
        unpack(0)}});
        let x_26 <- makeEnq_parentChildren001(x_25);
        let x_27 <- releaseMSHR_001(x_4);
    endrule

    rule rule_exec_001_101;
        let x_0 <- deq_fifoL2E_001();
        Struct38 x_1 = ((x_0).lr_ir_pp);
        Bit#(4) x_2 = ((x_1).ir_msg_from);
        Struct1 x_3 = ((x_1).ir_msg);
        Bit#(2) x_4 = ((x_1).ir_mshr_id);
        Bool x_5 = ((x_1).ir_is_rs_rel);
        when (! (x_5), noAction);
        Struct39 x_6 = ((x_0).lr_ir);
        Struct10 x_7 = ((x_6).info);
        Struct37 x_8 = ((x_1).ir_by_victim);
        Vector#(4, Bit#(64)) x_9 = ((x_0).lr_value);
        let x_10 <- getMSHR_001(x_4);
        let x_11 <- getMSHRRq_001(x_4);
        Struct1 x_12 = (unpack(0));
        Vector#(4, Bit#(64)) x_13 = (unpack(0));
        Bool x_14 = ((x_7).mesi_owned);
        Bit#(3) x_15 = ((x_7).mesi_status);
        Struct15 x_16 = (Struct15 {dir_st : (((x_7).mesi_dir_st) ==
        ((Bit#(3))'(3'h0)) ? ((Bit#(3))'(3'h1)) : ((x_7).mesi_dir_st)),
        dir_excl : ((((x_7).mesi_dir_sharers)[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        ((((((x_7).mesi_dir_sharers)[3:1])[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        (((((((x_7).mesi_dir_sharers)[3:1])[2:1])[0:0]) == ((Bit#(1))'(1'h1))
        ? ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        ((((((((x_7).mesi_dir_sharers)[3:1])[2:1])[1:1])[0:0]) ==
        ((Bit#(1))'(1'h1)) ? ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        (unpack(0))))))))))))), dir_sharers : (x_7).mesi_dir_sharers});
        when ((x_2) == ((Bit#(4))'(4'h0)), noAction);
        when (((x_3).id) == ((Bit#(6))'(6'h8)), noAction);
        when (! ((x_3).type_), noAction);
        when (((x_14) == ((Bool)'(True))) && ((x_15) == ((Bit#(3))'(3'h4))),
        noAction);
        Struct1 x_17 = (x_3);
        Struct42 x_18 = (Struct42 {addr : (x_3).addr, info_write :
        (Bool)'(False), info_hit : (x_6).info_hit, info_way : (x_6).info_way,
        edir_hit : (x_6).edir_hit, edir_way : (x_6).edir_way, edir_slot :
        (x_6).edir_slot, info : (x_6).info, value_write : (Bool)'(False),
        value : unpack(0), may_victim : (x_6).may_victim, reps :
        (x_6).reps});
        Struct42 x_19 = (Struct42 {addr : (x_18).addr, info_write :
        (x_18).info_write, info_hit : (x_18).info_hit, info_way :
        (x_18).info_way, edir_hit : (x_18).edir_hit, edir_way :
        (x_18).edir_way, edir_slot : (x_18).edir_slot, info : (x_18).info,
        value_write : (Bool)'(True), value : (x_17).value, may_victim :
        (x_18).may_victim, reps :
        (x_18).reps});
        let x_22 = ?;
        if ((x_8).valid) begin
            let x_20 <- victims__001__setVictim(Struct44 {victim_idx :
            (x_8).data, victim_info : (x_19).info, victim_value :
            ((x_19).value_write ? ((x_19).value) : (x_9))});
            x_22 = x_9;
        end else begin
            let x_21 <- cache__001__valueRsLineRq(x_19);
            x_22 = x_21;
        end
        Struct18 x_23 = (Struct18 {enq_type : ((((Bit#(4))'(4'h8))[3:2]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : (((((Bit#(4))'(4'h8))[3:2])
        == ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : ((Bit#(4))'(4'h8))[1:0], enq_msg : Struct1 {id :
        (Bit#(6))'(6'h9), type_ : (Bool)'(True), addr : (x_17).addr, value :
        unpack(0)}});
        let x_24 <- makeEnq_parentChildren001(x_23);
        let x_25 <- releaseMSHR_001(x_4);
    endrule

    rule rule_exec_001_11;
        let x_0 <- deq_fifoL2E_001();
        Struct38 x_1 = ((x_0).lr_ir_pp);
        Bit#(4) x_2 = ((x_1).ir_msg_from);
        Struct1 x_3 = ((x_1).ir_msg);
        Bit#(2) x_4 = ((x_1).ir_mshr_id);
        Bool x_5 = ((x_1).ir_is_rs_rel);
        when (! (x_5), noAction);
        Struct39 x_6 = ((x_0).lr_ir);
        Struct10 x_7 = ((x_6).info);
        Struct37 x_8 = ((x_1).ir_by_victim);
        Vector#(4, Bit#(64)) x_9 = ((x_0).lr_value);
        let x_10 <- getMSHR_001(x_4);
        let x_11 <- getMSHRRq_001(x_4);
        Struct1 x_12 = (unpack(0));
        Vector#(4, Bit#(64)) x_13 = (unpack(0));
        Bool x_14 = ((x_7).mesi_owned);
        Bit#(3) x_15 = ((x_7).mesi_status);
        Struct15 x_16 = (Struct15 {dir_st : (((x_7).mesi_dir_st) ==
        ((Bit#(3))'(3'h0)) ? ((Bit#(3))'(3'h1)) : ((x_7).mesi_dir_st)),
        dir_excl : ((((x_7).mesi_dir_sharers)[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        ((((((x_7).mesi_dir_sharers)[3:1])[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        (((((((x_7).mesi_dir_sharers)[3:1])[2:1])[0:0]) == ((Bit#(1))'(1'h1))
        ? ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        ((((((((x_7).mesi_dir_sharers)[3:1])[2:1])[1:1])[0:0]) ==
        ((Bit#(1))'(1'h1)) ? ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        (unpack(0))))))))))))), dir_sharers : (x_7).mesi_dir_sharers});
        when ((x_2) == ((Bit#(4))'(4'h0)), noAction);
        when (((x_3).id) == ((Bit#(6))'(6'h8)), noAction);
        when (! ((x_3).type_), noAction);
        when (! (((Bit#(3))'(3'h2)) < (x_15)), noAction);
        Struct1 x_17 = (x_3);
        Struct42 x_18 = (Struct42 {addr : (x_3).addr, info_write :
        (Bool)'(False), info_hit : (x_6).info_hit, info_way : (x_6).info_way,
        edir_hit : (x_6).edir_hit, edir_way : (x_6).edir_way, edir_slot :
        (x_6).edir_slot, info : (x_6).info, value_write : (Bool)'(False),
        value : unpack(0), may_victim : (x_6).may_victim, reps :
        (x_6).reps});
        let x_20 = ?;
        if ((x_8).valid) begin
            x_20 = x_9;
        end else begin
            let x_19 <- cache__001__valueRsLineRq(unpack(0));
            x_20 = x_19;
        end
        let x_21 <- registerUL_001(Struct43 {r_id : x_4, r_ul_rsb :
        (Bool)'(True), r_ul_rsbTo : ((Bit#(4))'(4'h8))[1:0]});
        Struct18 x_22 = (Struct18 {enq_type : ((((Bit#(4))'(4'h1))[3:2]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : (((((Bit#(4))'(4'h1))[3:2])
        == ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : ((Bit#(4))'(4'h1))[1:0], enq_msg : Struct1 {id :
        (Bit#(6))'(6'ha), type_ : (Bool)'(False), addr : (x_17).addr, value :
        unpack(0)}});
        let x_23 <- makeEnq_parentChildren001(x_22);
    endrule

    rule rule_exec_001_12;
        let x_0 <- deq_fifoL2E_001();
        Struct38 x_1 = ((x_0).lr_ir_pp);
        Bit#(4) x_2 = ((x_1).ir_msg_from);
        Struct1 x_3 = ((x_1).ir_msg);
        Bit#(2) x_4 = ((x_1).ir_mshr_id);
        Bool x_5 = ((x_1).ir_is_rs_rel);
        when (! (x_5), noAction);
        Struct39 x_6 = ((x_0).lr_ir);
        Struct10 x_7 = ((x_6).info);
        Struct37 x_8 = ((x_1).ir_by_victim);
        Vector#(4, Bit#(64)) x_9 = ((x_0).lr_value);
        let x_10 <- getMSHR_001(x_4);
        let x_11 <- getMSHRRq_001(x_4);
        Struct1 x_12 = (unpack(0));
        Vector#(4, Bit#(64)) x_13 = (unpack(0));
        Bool x_14 = ((x_7).mesi_owned);
        Bit#(3) x_15 = ((x_7).mesi_status);
        Struct15 x_16 = (Struct15 {dir_st : (((x_7).mesi_dir_st) ==
        ((Bit#(3))'(3'h0)) ? ((Bit#(3))'(3'h1)) : ((x_7).mesi_dir_st)),
        dir_excl : ((((x_7).mesi_dir_sharers)[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        ((((((x_7).mesi_dir_sharers)[3:1])[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        (((((((x_7).mesi_dir_sharers)[3:1])[2:1])[0:0]) == ((Bit#(1))'(1'h1))
        ? ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        ((((((((x_7).mesi_dir_sharers)[3:1])[2:1])[1:1])[0:0]) ==
        ((Bit#(1))'(1'h1)) ? ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        (unpack(0))))))))))))), dir_sharers : (x_7).mesi_dir_sharers});
        when ((x_2) == ({((Bit#(2))'(2'h2)),((Bit#(2))'(2'h1))}),
        noAction);
        when (((x_3).id) == ((Bit#(6))'(6'hb)), noAction);
        when ((x_10).m_rsb, noAction);
        when (((x_11).type_) == ((Bool)'(False)), noAction);
        when (((x_11).id) == ((Bit#(6))'(6'h8)), noAction);
        when ((x_10).m_rsb, noAction);
        when ((x_3).type_, noAction);
        when ((Bool)'(True), noAction);
        Struct1 x_17 = (x_3);
        Struct1 x_18 = (x_11);
        Bit#(4) x_19 = ({((Bit#(2))'(2'h2)),(((x_10).m_qidx)[1:0])});
        Struct42 x_20 = (Struct42 {addr : (x_3).addr, info_write :
        (Bool)'(False), info_hit : (x_6).info_hit, info_way : (x_6).info_way,
        edir_hit : (x_6).edir_hit, edir_way : (x_6).edir_way, edir_slot :
        (x_6).edir_slot, info : (x_6).info, value_write : (Bool)'(False),
        value : unpack(0), may_victim : (x_6).may_victim, reps :
        (x_6).reps});
        Struct42 x_21 = (Struct42 {addr : (x_20).addr, info_write :
        (x_20).info_write, info_hit : (x_20).info_hit, info_way :
        (x_20).info_way, edir_hit : (x_20).edir_hit, edir_way :
        (x_20).edir_way, edir_slot : (x_20).edir_slot, info : (x_20).info,
        value_write : (Bool)'(True), value : (x_18).value, may_victim :
        (x_20).may_victim, reps : (x_20).reps});
        Struct42 x_22 = (Struct42 {addr : (x_21).addr, info_write :
        (Bool)'(True), info_hit : (x_21).info_hit, info_way :
        (x_21).info_way, edir_hit : (x_21).edir_hit, edir_way :
        (x_21).edir_way, edir_slot : (x_21).edir_slot, info : Struct10
        {mesi_owned : (Bool)'(True), mesi_status : ((x_21).info).mesi_status,
        mesi_dir_st : ((x_21).info).mesi_dir_st, mesi_dir_sharers :
        ((x_21).info).mesi_dir_sharers}, value_write : (x_21).value_write,
        value : (x_21).value, may_victim : (x_21).may_victim, reps :
        (x_21).reps});
        Struct42 x_23 = (Struct42 {addr : (x_22).addr, info_write :
        (Bool)'(True), info_hit : (x_22).info_hit, info_way :
        (x_22).info_way, edir_hit : (x_22).edir_hit, edir_way :
        (x_22).edir_way, edir_slot : (x_22).edir_slot, info : Struct10
        {mesi_owned : ((x_22).info).mesi_owned, mesi_status :
        (Bit#(3))'(3'h4), mesi_dir_st : ((x_22).info).mesi_dir_st,
        mesi_dir_sharers : ((x_22).info).mesi_dir_sharers}, value_write :
        (x_22).value_write, value : (x_22).value, may_victim :
        (x_22).may_victim, reps :
        (x_22).reps});
        let x_26 = ?;
        if ((x_8).valid) begin
            let x_24 <- victims__001__setVictim(Struct44 {victim_idx :
            (x_8).data, victim_info : (x_23).info, victim_value :
            ((x_23).value_write ? ((x_23).value) : (x_9))});
            x_26 = x_9;
        end else begin
            let x_25 <- cache__001__valueRsLineRq(x_23);
            x_26 = x_25;
        end
        let x_27 <- releaseMSHR_001(x_4);
        Struct18 x_28 = (Struct18 {enq_type : (((x_19)[3:2]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : ((((x_19)[3:2]) ==
        ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : (x_19)[1:0], enq_msg : Struct1 {id : (Bit#(6))'(6'h9),
        type_ : (Bool)'(True), addr : (x_17).addr, value : unpack(0)}});
        let x_29 <- makeEnq_parentChildren001(x_28);
    endrule

    rule rule_exec_001_130;
        let x_0 <- deq_fifoL2E_001();
        Struct38 x_1 = ((x_0).lr_ir_pp);
        Bit#(4) x_2 = ((x_1).ir_msg_from);
        Struct1 x_3 = ((x_1).ir_msg);
        Bit#(2) x_4 = ((x_1).ir_mshr_id);
        Bool x_5 = ((x_1).ir_is_rs_rel);
        when (! (x_5), noAction);
        Struct39 x_6 = ((x_0).lr_ir);
        Struct10 x_7 = ((x_6).info);
        Struct37 x_8 = ((x_1).ir_by_victim);
        Vector#(4, Bit#(64)) x_9 = ((x_0).lr_value);
        let x_10 <- getMSHR_001(x_4);
        let x_11 <- getMSHRRq_001(x_4);
        Struct1 x_12 = (unpack(0));
        Vector#(4, Bit#(64)) x_13 = (unpack(0));
        Bool x_14 = ((x_7).mesi_owned);
        Bit#(3) x_15 = ((x_7).mesi_status);
        Struct15 x_16 = (Struct15 {dir_st : (((x_7).mesi_dir_st) ==
        ((Bit#(3))'(3'h0)) ? ((Bit#(3))'(3'h1)) : ((x_7).mesi_dir_st)),
        dir_excl : ((((x_7).mesi_dir_sharers)[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        ((((((x_7).mesi_dir_sharers)[3:1])[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        (((((((x_7).mesi_dir_sharers)[3:1])[2:1])[0:0]) == ((Bit#(1))'(1'h1))
        ? ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        ((((((((x_7).mesi_dir_sharers)[3:1])[2:1])[1:1])[0:0]) ==
        ((Bit#(1))'(1'h1)) ? ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        (unpack(0))))))))))))), dir_sharers : (x_7).mesi_dir_sharers});
        when ((x_2) == ((Bit#(4))'(4'h9)), noAction);
        when (((x_3).id) == ((Bit#(6))'(6'hc)), noAction);
        when (! ((x_3).type_), noAction);
        when ((Bool)'(True), noAction);
        Struct1 x_17 = (x_3);
        Struct42 x_18 = (Struct42 {addr : (x_3).addr, info_write :
        (Bool)'(False), info_hit : (x_6).info_hit, info_way : (x_6).info_way,
        edir_hit : (x_6).edir_hit, edir_way : (x_6).edir_way, edir_slot :
        (x_6).edir_slot, info : (x_6).info, value_write : (Bool)'(False),
        value : unpack(0), may_victim : (x_6).may_victim, reps :
        (x_6).reps});
        Struct42 x_19 = (Struct42 {addr : (x_18).addr, info_write :
        (Bool)'(True), info_hit : (x_18).info_hit, info_way :
        (x_18).info_way, edir_hit : (x_18).edir_hit, edir_way :
        (x_18).edir_way, edir_slot : (x_18).edir_slot, info : Struct10
        {mesi_owned : ((x_18).info).mesi_owned, mesi_status :
        (Bit#(3))'(3'h1), mesi_dir_st : ((x_18).info).mesi_dir_st,
        mesi_dir_sharers : ((x_18).info).mesi_dir_sharers}, value_write :
        (x_18).value_write, value : (x_18).value, may_victim :
        (x_18).may_victim, reps : (x_18).reps});
        Struct42 x_20 = (Struct42 {addr : (x_19).addr, info_write :
        (Bool)'(True), info_hit : (x_19).info_hit, info_way :
        (x_19).info_way, edir_hit : (x_19).edir_hit, edir_way :
        (x_19).edir_way, edir_slot : (x_19).edir_slot, info : Struct10
        {mesi_owned : (Bool)'(False), mesi_status :
        ((x_19).info).mesi_status, mesi_dir_st : ((x_19).info).mesi_dir_st,
        mesi_dir_sharers : ((x_19).info).mesi_dir_sharers}, value_write :
        (x_19).value_write, value : (x_19).value, may_victim :
        (x_19).may_victim, reps :
        (x_19).reps});
        let x_23 = ?;
        if ((x_8).valid) begin
            let x_21 <- victims__001__setVictim(Struct44 {victim_idx :
            (x_8).data, victim_info : (x_20).info, victim_value :
            ((x_20).value_write ? ((x_20).value) : (x_9))});
            x_23 = x_9;
        end else begin
            let x_22 <- cache__001__valueRsLineRq(x_20);
            x_23 = x_22;
        end
        Struct18 x_24 = (Struct18 {enq_type : ((((Bit#(4))'(4'h5))[3:2]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : (((((Bit#(4))'(4'h5))[3:2])
        == ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : ((Bit#(4))'(4'h5))[1:0], enq_msg : Struct1 {id :
        (Bit#(6))'(6'hd), type_ : (Bool)'(True), addr : (x_17).addr, value :
        unpack(0)}});
        let x_25 <- makeEnq_parentChildren001(x_24);
        let x_26 <- releaseMSHR_001(x_4);
    endrule

    rule rule_exec_001_131;
        let x_0 <- deq_fifoL2E_001();
        Struct38 x_1 = ((x_0).lr_ir_pp);
        Bit#(4) x_2 = ((x_1).ir_msg_from);
        Struct1 x_3 = ((x_1).ir_msg);
        Bit#(2) x_4 = ((x_1).ir_mshr_id);
        Bool x_5 = ((x_1).ir_is_rs_rel);
        when (! (x_5), noAction);
        Struct39 x_6 = ((x_0).lr_ir);
        Struct10 x_7 = ((x_6).info);
        Struct37 x_8 = ((x_1).ir_by_victim);
        Vector#(4, Bit#(64)) x_9 = ((x_0).lr_value);
        let x_10 <- getMSHR_001(x_4);
        let x_11 <- getMSHRRq_001(x_4);
        Struct1 x_12 = (unpack(0));
        Vector#(4, Bit#(64)) x_13 = (unpack(0));
        Bool x_14 = ((x_7).mesi_owned);
        Bit#(3) x_15 = ((x_7).mesi_status);
        Struct15 x_16 = (Struct15 {dir_st : (((x_7).mesi_dir_st) ==
        ((Bit#(3))'(3'h0)) ? ((Bit#(3))'(3'h1)) : ((x_7).mesi_dir_st)),
        dir_excl : ((((x_7).mesi_dir_sharers)[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        ((((((x_7).mesi_dir_sharers)[3:1])[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        (((((((x_7).mesi_dir_sharers)[3:1])[2:1])[0:0]) == ((Bit#(1))'(1'h1))
        ? ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        ((((((((x_7).mesi_dir_sharers)[3:1])[2:1])[1:1])[0:0]) ==
        ((Bit#(1))'(1'h1)) ? ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        (unpack(0))))))))))))), dir_sharers : (x_7).mesi_dir_sharers});
        when ((x_2) == ((Bit#(4))'(4'h9)), noAction);
        when (((x_3).id) == ((Bit#(6))'(6'he)), noAction);
        when (! ((x_3).type_), noAction);
        when (! ((x_15) < ((Bit#(3))'(3'h3))), noAction);
        Struct1 x_17 = (x_3);
        Struct42 x_18 = (Struct42 {addr : (x_3).addr, info_write :
        (Bool)'(False), info_hit : (x_6).info_hit, info_way : (x_6).info_way,
        edir_hit : (x_6).edir_hit, edir_way : (x_6).edir_way, edir_slot :
        (x_6).edir_slot, info : (x_6).info, value_write : (Bool)'(False),
        value : unpack(0), may_victim : (x_6).may_victim, reps :
        (x_6).reps});
        Struct42 x_19 = (Struct42 {addr : (x_18).addr, info_write :
        (Bool)'(True), info_hit : (x_18).info_hit, info_way :
        (x_18).info_way, edir_hit : (x_18).edir_hit, edir_way :
        (x_18).edir_way, edir_slot : (x_18).edir_slot, info : Struct10
        {mesi_owned : ((x_18).info).mesi_owned, mesi_status :
        (Bit#(3))'(3'h1), mesi_dir_st : ((x_18).info).mesi_dir_st,
        mesi_dir_sharers : ((x_18).info).mesi_dir_sharers}, value_write :
        (x_18).value_write, value : (x_18).value, may_victim :
        (x_18).may_victim, reps : (x_18).reps});
        Struct42 x_20 = (Struct42 {addr : (x_19).addr, info_write :
        (Bool)'(True), info_hit : (x_19).info_hit, info_way :
        (x_19).info_way, edir_hit : (x_19).edir_hit, edir_way :
        (x_19).edir_way, edir_slot : (x_19).edir_slot, info : Struct10
        {mesi_owned : (Bool)'(False), mesi_status :
        ((x_19).info).mesi_status, mesi_dir_st : ((x_19).info).mesi_dir_st,
        mesi_dir_sharers : ((x_19).info).mesi_dir_sharers}, value_write :
        (x_19).value_write, value : (x_19).value, may_victim :
        (x_19).may_victim, reps :
        (x_19).reps});
        let x_23 = ?;
        if ((x_8).valid) begin
            let x_21 <- victims__001__setVictim(Struct44 {victim_idx :
            (x_8).data, victim_info : (x_20).info, victim_value :
            ((x_20).value_write ? ((x_20).value) : (x_9))});
            x_23 = x_9;
        end else begin
            let x_22 <- cache__001__valueRsLineRq(x_20);
            x_23 = x_22;
        end
        Struct18 x_24 = (Struct18 {enq_type : ((((Bit#(4))'(4'h5))[3:2]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : (((((Bit#(4))'(4'h5))[3:2])
        == ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : ((Bit#(4))'(4'h5))[1:0], enq_msg : Struct1 {id :
        (Bit#(6))'(6'hf), type_ : (Bool)'(True), addr : (x_17).addr, value :
        unpack(0)}});
        let x_25 <- makeEnq_parentChildren001(x_24);
        let x_26 <- releaseMSHR_001(x_4);
    endrule

    rule rule_exec_001_20;
        let x_0 <- victims__001__getFirstVictim();
        Bit#(64) x_1 = ((x_0).victim_addr);
        Struct10 x_2 = ((x_0).victim_info);
        Vector#(4, Bit#(64)) x_3 = ((x_0).victim_value);
        Struct1 x_4 = (Struct1 {id : unpack(0), type_ : (Bool)'(False), addr
        : x_1, value : unpack(0)});
        Struct14 x_5 = (Struct14 {m_is_ul : (Bool)'(True), m_qidx :
        unpack(0), m_rsb : (Bool)'(False), m_dl_rss_from : unpack(0),
        m_dl_rss_recv : unpack(0)});
        Struct1 x_6 = (unpack(0));
        Struct1 x_7 = (unpack(0));
        Vector#(4, Bit#(64)) x_8 = (unpack(0));
        Bool x_9 = ((x_2).mesi_owned);
        Bit#(3) x_10 = ((x_2).mesi_status);
        Struct15 x_11 = (Struct15 {dir_st : (((x_2).mesi_dir_st) ==
        ((Bit#(3))'(3'h0)) ? ((Bit#(3))'(3'h1)) : ((x_2).mesi_dir_st)),
        dir_excl : ((((x_2).mesi_dir_sharers)[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        ((((((x_2).mesi_dir_sharers)[3:1])[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        (((((((x_2).mesi_dir_sharers)[3:1])[2:1])[0:0]) == ((Bit#(1))'(1'h1))
        ? ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        ((((((((x_2).mesi_dir_sharers)[3:1])[2:1])[1:1])[0:0]) ==
        ((Bit#(1))'(1'h1)) ? ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        (unpack(0))))))))))))), dir_sharers : (x_2).mesi_dir_sharers});
        when (! ((x_4).type_), noAction);
        when (((x_9) == ((Bool)'(False))) && ((((Bit#(3))'(3'h0)) < (x_10))
        && ((x_10) < ((Bit#(3))'(3'h4)))), noAction);
        Struct18 x_12 = (Struct18 {enq_type : ((((Bit#(4))'(4'h1))[3:2]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : (((((Bit#(4))'(4'h1))[3:2])
        == ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : ((Bit#(4))'(4'h1))[1:0], enq_msg : Struct1 {id :
        (Bit#(6))'(6'h14), type_ : (Bool)'(False), addr : (x_4).addr, value :
        unpack(0)}});
        let x_13 <- makeEnq_parentChildren001(x_12);
        let x_14 <- setULImm_001(x_4);
        let x_15 <- victims__001__setVictimRq(x_1);
    endrule

    rule rule_exec_001_21;
        let x_0 <- victims__001__getFirstVictim();
        Bit#(64) x_1 = ((x_0).victim_addr);
        Struct10 x_2 = ((x_0).victim_info);
        Vector#(4, Bit#(64)) x_3 = ((x_0).victim_value);
        Struct1 x_4 = (Struct1 {id : unpack(0), type_ : (Bool)'(False), addr
        : x_1, value : unpack(0)});
        Struct14 x_5 = (Struct14 {m_is_ul : (Bool)'(True), m_qidx :
        unpack(0), m_rsb : (Bool)'(False), m_dl_rss_from : unpack(0),
        m_dl_rss_recv : unpack(0)});
        Struct1 x_6 = (unpack(0));
        Struct1 x_7 = (unpack(0));
        Vector#(4, Bit#(64)) x_8 = (unpack(0));
        Bool x_9 = ((x_2).mesi_owned);
        Bit#(3) x_10 = ((x_2).mesi_status);
        Struct15 x_11 = (Struct15 {dir_st : (((x_2).mesi_dir_st) ==
        ((Bit#(3))'(3'h0)) ? ((Bit#(3))'(3'h1)) : ((x_2).mesi_dir_st)),
        dir_excl : ((((x_2).mesi_dir_sharers)[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        ((((((x_2).mesi_dir_sharers)[3:1])[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        (((((((x_2).mesi_dir_sharers)[3:1])[2:1])[0:0]) == ((Bit#(1))'(1'h1))
        ? ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        ((((((((x_2).mesi_dir_sharers)[3:1])[2:1])[1:1])[0:0]) ==
        ((Bit#(1))'(1'h1)) ? ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        (unpack(0))))))))))))), dir_sharers : (x_2).mesi_dir_sharers});
        when (! ((x_4).type_), noAction);
        when (((Bit#(3))'(3'h0)) < (x_10), noAction);
        Struct18 x_12 = (Struct18 {enq_type : ((((Bit#(4))'(4'h1))[3:2]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : (((((Bit#(4))'(4'h1))[3:2])
        == ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : ((Bit#(4))'(4'h1))[1:0], enq_msg : Struct1 {id :
        (Bit#(6))'(6'h15), type_ : (Bool)'(False), addr : (x_4).addr, value :
        x_3}});
        let x_13 <- makeEnq_parentChildren001(x_12);
        let x_14 <- setULImm_001(x_4);
        let x_15 <- victims__001__setVictimRq(x_1);
    endrule

    // No methods in this module
endmodule

interface Module136;

endinterface

module mkModule136#(function Action victims__002__setVictimRq(Bit#(64) _),
    function Action setULImm_002(Struct1 _),
    function ActionValue#(Struct13) victims__002__getFirstVictim(),
    function Action victims__002__setVictim(Struct44 _),
    function Action registerUL_002(Struct43 _),
    function Action makeEnq_parentChildren002(Struct18 _),
    function ActionValue#(Vector#(4, Bit#(64))) cache__002__valueRsLineRq(Struct42 _),
    function ActionValue#(Struct1) getMSHRRq_002(Bit#(2) _),
    function ActionValue#(Struct14) getMSHR_002(Bit#(2) _),
    function ActionValue#(Struct41) deq_fifoL2E_002(),
    function ActionValue#(Struct13) victims__002__getVictim(Bit#(1) _),
    function Action enq_fifoL2E_002(Struct41 _),
    function ActionValue#(Struct39) cache__002__infoRsValueRq(Bit#(64) _),
    function ActionValue#(Struct38) deq_fifoI2L_002(),
    function Action enq_fifoI2L_002(Struct38 _),
    function Action cache__002__infoRq(Bit#(64) _),
    function ActionValue#(Struct38) deq_fifoN2I_002(),
    function ActionValue#(Struct36) getCRqSlot_002(Struct35 _),
    function ActionValue#(Bool) victims__002__hasVictim(),
    function ActionValue#(Struct2) deq_fifoCRqInput_002(),
    function Action releaseMSHR_002(Bit#(2) _),
    function Action victims__002__releaseVictim(Bit#(64) _),
    function ActionValue#(Struct35) getWait_002(),
    function Action startRelease_002(Bit#(2) _),
    function ActionValue#(Bit#(2)) getULReady_002(Bit#(64) _),
    function Action enq_fifoN2I_002(Struct38 _),
    function ActionValue#(Struct37) victims__002__findVictim(Bit#(64) _),
    function ActionValue#(Struct36) getPRqSlot_002(Struct35 _),
    function ActionValue#(Struct2) deq_fifoPInput_002())
    (Module136);

    rule rule_in_prq_002;
        let x_0 <- deq_fifoPInput_002();
        Bit#(4) x_1 = ((x_0).in_msg_from);
        when ((x_1) == ({((Bit#(2))'(2'h2)),((Bit#(2))'(2'h2))}),
        noAction);
        Struct1 x_2 = ((x_0).in_msg);
        when (! ((x_2).type_), noAction);
        let x_3 <- getPRqSlot_002(Struct35 {r_id : unpack(0), r_msg : x_2,
        r_msg_from : (x_0).in_msg_from});
        when ((x_3).s_has_slot,
        noAction);
        if (! ((x_3).s_conflict)) begin
            let x_4 <- victims__002__findVictim((x_2).addr);
            Struct38 x_5 = (Struct38 {ir_is_rs_rel : (Bool)'(False), ir_msg :
            (x_0).in_msg, ir_msg_from : x_1, ir_mshr_id : (x_3).s_id,
            ir_by_victim : x_4});
            let x_6 <- enq_fifoN2I_002(x_5);
        end else begin

        end
    endrule

    rule rule_in_prs_002;
        let x_0 <- deq_fifoPInput_002();
        Bit#(4) x_1 = ((x_0).in_msg_from);
        when ((x_1) == ({((Bit#(2))'(2'h2)),((Bit#(2))'(2'h2))}),
        noAction);
        Struct1 x_2 = ((x_0).in_msg);
        when (((x_2).type_) && (! (((x_2).id) == ((Bit#(6))'(6'h16)))),
        noAction);
        let x_3 <- getULReady_002((x_2).addr);
        let x_4 <- startRelease_002(x_3);
        let x_5 <- victims__002__findVictim((x_2).addr);
        Struct38 x_6 = (Struct38 {ir_is_rs_rel : (Bool)'(False), ir_msg :
        (x_0).in_msg, ir_msg_from : x_1, ir_mshr_id : x_3, ir_by_victim :
        x_5});
        let x_7 <- enq_fifoN2I_002(x_6);
    endrule

    rule rule_in_retry_002;
        let x_0 <- getWait_002();
        Struct1 x_1 = ((x_0).r_msg);
        let x_2 <- victims__002__findVictim((x_1).addr);
        Struct38 x_3 = (Struct38 {ir_is_rs_rel : (Bool)'(False), ir_msg :
        x_1, ir_msg_from : (x_0).r_msg_from, ir_mshr_id : (x_0).r_id,
        ir_by_victim : x_2});
        let x_4 <- enq_fifoN2I_002(x_3);
    endrule

    rule rule_in_invrs_002;
        let x_0 <- deq_fifoPInput_002();
        Bit#(4) x_1 = ((x_0).in_msg_from);
        when ((x_1) == ({((Bit#(2))'(2'h2)),((Bit#(2))'(2'h2))}),
        noAction);
        Struct1 x_2 = ((x_0).in_msg);
        when (((x_2).type_) && (((x_2).id) == ((Bit#(6))'(6'h16))),
        noAction);
        let x_3 <- getULReady_002((x_2).addr);
        let x_4 <- victims__002__releaseVictim((x_2).addr);
        let x_5 <- releaseMSHR_002(x_3);
    endrule

    rule rule_in_crq_002;
        let x_0 <- deq_fifoCRqInput_002();
        Bit#(4) x_1 = ((x_0).in_msg_from);
        when (((x_1)[3:2]) == ((Bit#(2))'(2'h0)), noAction);
        Struct1 x_2 = ((x_0).in_msg);
        when (! ((x_2).type_), noAction);
        let x_3 <- victims__002__hasVictim();
        when (! (x_3), noAction);
        let x_4 <- getCRqSlot_002(Struct35 {r_id : unpack(0), r_msg : x_2,
        r_msg_from : x_1});
        when ((x_4).s_has_slot,
        noAction);
        if (! ((x_4).s_conflict)) begin
            let x_5 <- victims__002__findVictim((x_2).addr);
            Struct38 x_6 = (Struct38 {ir_is_rs_rel : (Bool)'(False), ir_msg :
            (x_0).in_msg, ir_msg_from : x_1, ir_mshr_id : (x_4).s_id,
            ir_by_victim : x_5});
            let x_7 <- enq_fifoN2I_002(x_6);
        end else begin

        end
    endrule

    rule rule_ir_cache_002;
        let x_0 <- deq_fifoN2I_002();
        when (! (((x_0).ir_by_victim).valid), noAction);
        Struct1 x_1 = ((x_0).ir_msg);
        let x_2 <- cache__002__infoRq((x_1).addr);
        let x_3 <- enq_fifoI2L_002(x_0);
    endrule

    rule rule_ir_victims_002;
        let x_0 <- deq_fifoN2I_002();
        when (((x_0).ir_by_victim).valid, noAction);
        let x_1 <- enq_fifoI2L_002(x_0);
    endrule

    rule rule_lr_cache_002;
        let x_0 <- deq_fifoI2L_002();
        when (! (((x_0).ir_by_victim).valid), noAction);
        let x_1 <- cache__002__infoRsValueRq(((x_0).ir_msg).addr);
        Struct41 x_2 = (Struct41 {lr_ir_pp : x_0, lr_ir : x_1, lr_value :
        unpack(0)});
        let x_3 <- enq_fifoL2E_002(x_2);
    endrule

    rule rule_lr_victims_002;
        let x_0 <- deq_fifoI2L_002();
        when (((x_0).ir_by_victim).valid, noAction);
        Bit#(1) x_1 = (((x_0).ir_by_victim).data);
        let x_2 <- victims__002__getVictim(x_1);
        Struct39 x_3 = (Struct39 {info_index : unpack(0), info_hit :
        unpack(0), info_way : unpack(0), edir_hit : unpack(0), edir_way :
        unpack(0), edir_slot : unpack(0), info : (x_2).victim_info,
        may_victim : unpack(0), reps : unpack(0)});
        Struct41 x_4 = (Struct41 {lr_ir_pp : x_0, lr_ir : x_3, lr_value :
        (x_2).victim_value});
        let x_5 <- enq_fifoL2E_002(x_4);
    endrule

    rule rule_exec_002_00;
        let x_0 <- deq_fifoL2E_002();
        Struct38 x_1 = ((x_0).lr_ir_pp);
        Bit#(4) x_2 = ((x_1).ir_msg_from);
        Struct1 x_3 = ((x_1).ir_msg);
        Bit#(2) x_4 = ((x_1).ir_mshr_id);
        Bool x_5 = ((x_1).ir_is_rs_rel);
        when (! (x_5), noAction);
        Struct39 x_6 = ((x_0).lr_ir);
        Struct10 x_7 = ((x_6).info);
        Struct37 x_8 = ((x_1).ir_by_victim);
        Vector#(4, Bit#(64)) x_9 = ((x_0).lr_value);
        let x_10 <- getMSHR_002(x_4);
        let x_11 <- getMSHRRq_002(x_4);
        Struct1 x_12 = (unpack(0));
        Vector#(4, Bit#(64)) x_13 = (unpack(0));
        Bool x_14 = ((x_7).mesi_owned);
        Bit#(3) x_15 = ((x_7).mesi_status);
        Struct15 x_16 = (Struct15 {dir_st : (((x_7).mesi_dir_st) ==
        ((Bit#(3))'(3'h0)) ? ((Bit#(3))'(3'h1)) : ((x_7).mesi_dir_st)),
        dir_excl : ((((x_7).mesi_dir_sharers)[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        ((((((x_7).mesi_dir_sharers)[3:1])[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        (((((((x_7).mesi_dir_sharers)[3:1])[2:1])[0:0]) == ((Bit#(1))'(1'h1))
        ? ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        ((((((((x_7).mesi_dir_sharers)[3:1])[2:1])[1:1])[0:0]) ==
        ((Bit#(1))'(1'h1)) ? ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        (unpack(0))))))))))))), dir_sharers : (x_7).mesi_dir_sharers});
        when ((x_2) == ((Bit#(4))'(4'h0)), noAction);
        when (((x_3).id) == ((Bit#(6))'(6'h0)), noAction);
        when (! ((x_3).type_), noAction);
        when (! ((x_15) < ((Bit#(3))'(3'h2))), noAction);
        Struct1 x_17 = (x_3);
        Struct42 x_18 = (Struct42 {addr : (x_3).addr, info_write :
        (Bool)'(False), info_hit : (x_6).info_hit, info_way : (x_6).info_way,
        edir_hit : (x_6).edir_hit, edir_way : (x_6).edir_way, edir_slot :
        (x_6).edir_slot, info : (x_6).info, value_write : (Bool)'(False),
        value : unpack(0), may_victim : (x_6).may_victim, reps :
        (x_6).reps});
        let x_20 = ?;
        if ((x_8).valid) begin
            x_20 = x_9;
        end else begin
            let x_19 <- cache__002__valueRsLineRq(unpack(0));
            x_20 = x_19;
        end
        Struct18 x_21 = (Struct18 {enq_type : ((((Bit#(4))'(4'h8))[3:2]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : (((((Bit#(4))'(4'h8))[3:2])
        == ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : ((Bit#(4))'(4'h8))[1:0], enq_msg : Struct1 {id :
        (Bit#(6))'(6'h1), type_ : (Bool)'(True), addr : (x_17).addr, value :
        x_20}});
        let x_22 <- makeEnq_parentChildren002(x_21);
        let x_23 <- releaseMSHR_002(x_4);
    endrule

    rule rule_exec_002_01;
        let x_0 <- deq_fifoL2E_002();
        Struct38 x_1 = ((x_0).lr_ir_pp);
        Bit#(4) x_2 = ((x_1).ir_msg_from);
        Struct1 x_3 = ((x_1).ir_msg);
        Bit#(2) x_4 = ((x_1).ir_mshr_id);
        Bool x_5 = ((x_1).ir_is_rs_rel);
        when (! (x_5), noAction);
        Struct39 x_6 = ((x_0).lr_ir);
        Struct10 x_7 = ((x_6).info);
        Struct37 x_8 = ((x_1).ir_by_victim);
        Vector#(4, Bit#(64)) x_9 = ((x_0).lr_value);
        let x_10 <- getMSHR_002(x_4);
        let x_11 <- getMSHRRq_002(x_4);
        Struct1 x_12 = (unpack(0));
        Vector#(4, Bit#(64)) x_13 = (unpack(0));
        Bool x_14 = ((x_7).mesi_owned);
        Bit#(3) x_15 = ((x_7).mesi_status);
        Struct15 x_16 = (Struct15 {dir_st : (((x_7).mesi_dir_st) ==
        ((Bit#(3))'(3'h0)) ? ((Bit#(3))'(3'h1)) : ((x_7).mesi_dir_st)),
        dir_excl : ((((x_7).mesi_dir_sharers)[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        ((((((x_7).mesi_dir_sharers)[3:1])[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        (((((((x_7).mesi_dir_sharers)[3:1])[2:1])[0:0]) == ((Bit#(1))'(1'h1))
        ? ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        ((((((((x_7).mesi_dir_sharers)[3:1])[2:1])[1:1])[0:0]) ==
        ((Bit#(1))'(1'h1)) ? ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        (unpack(0))))))))))))), dir_sharers : (x_7).mesi_dir_sharers});
        when ((x_2) == ((Bit#(4))'(4'h0)), noAction);
        when (((x_3).id) == ((Bit#(6))'(6'h0)), noAction);
        when (! ((x_3).type_), noAction);
        when (! (((Bit#(3))'(3'h1)) < (x_15)), noAction);
        Struct1 x_17 = (x_3);
        Struct42 x_18 = (Struct42 {addr : (x_3).addr, info_write :
        (Bool)'(False), info_hit : (x_6).info_hit, info_way : (x_6).info_way,
        edir_hit : (x_6).edir_hit, edir_way : (x_6).edir_way, edir_slot :
        (x_6).edir_slot, info : (x_6).info, value_write : (Bool)'(False),
        value : unpack(0), may_victim : (x_6).may_victim, reps :
        (x_6).reps});
        let x_20 = ?;
        if ((x_8).valid) begin
            x_20 = x_9;
        end else begin
            let x_19 <- cache__002__valueRsLineRq(unpack(0));
            x_20 = x_19;
        end
        let x_21 <- registerUL_002(Struct43 {r_id : x_4, r_ul_rsb :
        (Bool)'(True), r_ul_rsbTo : ((Bit#(4))'(4'h8))[1:0]});
        Struct18 x_22 = (Struct18 {enq_type : ((((Bit#(4))'(4'h2))[3:2]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : (((((Bit#(4))'(4'h2))[3:2])
        == ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : ((Bit#(4))'(4'h2))[1:0], enq_msg : Struct1 {id :
        (Bit#(6))'(6'h2), type_ : (Bool)'(False), addr : (x_17).addr, value :
        unpack(0)}});
        let x_23 <- makeEnq_parentChildren002(x_22);
    endrule

    rule rule_exec_002_020;
        let x_0 <- deq_fifoL2E_002();
        Struct38 x_1 = ((x_0).lr_ir_pp);
        Bit#(4) x_2 = ((x_1).ir_msg_from);
        Struct1 x_3 = ((x_1).ir_msg);
        Bit#(2) x_4 = ((x_1).ir_mshr_id);
        Bool x_5 = ((x_1).ir_is_rs_rel);
        when (! (x_5), noAction);
        Struct39 x_6 = ((x_0).lr_ir);
        Struct10 x_7 = ((x_6).info);
        Struct37 x_8 = ((x_1).ir_by_victim);
        Vector#(4, Bit#(64)) x_9 = ((x_0).lr_value);
        let x_10 <- getMSHR_002(x_4);
        let x_11 <- getMSHRRq_002(x_4);
        Struct1 x_12 = (unpack(0));
        Vector#(4, Bit#(64)) x_13 = (unpack(0));
        Bool x_14 = ((x_7).mesi_owned);
        Bit#(3) x_15 = ((x_7).mesi_status);
        Struct15 x_16 = (Struct15 {dir_st : (((x_7).mesi_dir_st) ==
        ((Bit#(3))'(3'h0)) ? ((Bit#(3))'(3'h1)) : ((x_7).mesi_dir_st)),
        dir_excl : ((((x_7).mesi_dir_sharers)[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        ((((((x_7).mesi_dir_sharers)[3:1])[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        (((((((x_7).mesi_dir_sharers)[3:1])[2:1])[0:0]) == ((Bit#(1))'(1'h1))
        ? ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        ((((((((x_7).mesi_dir_sharers)[3:1])[2:1])[1:1])[0:0]) ==
        ((Bit#(1))'(1'h1)) ? ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        (unpack(0))))))))))))), dir_sharers : (x_7).mesi_dir_sharers});
        when ((x_2) == ({((Bit#(2))'(2'h2)),((Bit#(2))'(2'h2))}),
        noAction);
        when (((x_3).id) == ((Bit#(6))'(6'h3)), noAction);
        when ((x_10).m_rsb, noAction);
        when (((x_11).type_) == ((Bool)'(False)), noAction);
        when (((x_11).id) == ((Bit#(6))'(6'h0)), noAction);
        when ((x_10).m_rsb, noAction);
        when ((x_3).type_, noAction);
        when ((Bool)'(True), noAction);
        Struct1 x_17 = (x_3);
        Struct1 x_18 = (x_11);
        Bit#(4) x_19 = ({((Bit#(2))'(2'h2)),(((x_10).m_qidx)[1:0])});
        Struct42 x_20 = (Struct42 {addr : (x_3).addr, info_write :
        (Bool)'(False), info_hit : (x_6).info_hit, info_way : (x_6).info_way,
        edir_hit : (x_6).edir_hit, edir_way : (x_6).edir_way, edir_slot :
        (x_6).edir_slot, info : (x_6).info, value_write : (Bool)'(False),
        value : unpack(0), may_victim : (x_6).may_victim, reps :
        (x_6).reps});
        Struct42 x_21 = (Struct42 {addr : (x_20).addr, info_write :
        (Bool)'(True), info_hit : (x_20).info_hit, info_way :
        (x_20).info_way, edir_hit : (x_20).edir_hit, edir_way :
        (x_20).edir_way, edir_slot : (x_20).edir_slot, info : Struct10
        {mesi_owned : ((x_20).info).mesi_owned, mesi_status :
        (Bit#(3))'(3'h2), mesi_dir_st : ((x_20).info).mesi_dir_st,
        mesi_dir_sharers : ((x_20).info).mesi_dir_sharers}, value_write :
        (x_20).value_write, value : (x_20).value, may_victim :
        (x_20).may_victim, reps : (x_20).reps});
        Struct42 x_22 = (Struct42 {addr : (x_21).addr, info_write :
        (x_21).info_write, info_hit : (x_21).info_hit, info_way :
        (x_21).info_way, edir_hit : (x_21).edir_hit, edir_way :
        (x_21).edir_way, edir_slot : (x_21).edir_slot, info : (x_21).info,
        value_write : (Bool)'(True), value : (x_17).value, may_victim :
        (x_21).may_victim, reps :
        (x_21).reps});
        let x_25 = ?;
        if ((x_8).valid) begin
            let x_23 <- victims__002__setVictim(Struct44 {victim_idx :
            (x_8).data, victim_info : (x_22).info, victim_value :
            ((x_22).value_write ? ((x_22).value) : (x_9))});
            x_25 = x_9;
        end else begin
            let x_24 <- cache__002__valueRsLineRq(x_22);
            x_25 = x_24;
        end
        let x_26 <- releaseMSHR_002(x_4);
        Struct18 x_27 = (Struct18 {enq_type : (((x_19)[3:2]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : ((((x_19)[3:2]) ==
        ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : (x_19)[1:0], enq_msg : Struct1 {id : (Bit#(6))'(6'h1),
        type_ : (Bool)'(True), addr : (x_17).addr, value :
        (x_17).value}});
        let x_28 <- makeEnq_parentChildren002(x_27);
    endrule

    rule rule_exec_002_021;
        let x_0 <- deq_fifoL2E_002();
        Struct38 x_1 = ((x_0).lr_ir_pp);
        Bit#(4) x_2 = ((x_1).ir_msg_from);
        Struct1 x_3 = ((x_1).ir_msg);
        Bit#(2) x_4 = ((x_1).ir_mshr_id);
        Bool x_5 = ((x_1).ir_is_rs_rel);
        when (! (x_5), noAction);
        Struct39 x_6 = ((x_0).lr_ir);
        Struct10 x_7 = ((x_6).info);
        Struct37 x_8 = ((x_1).ir_by_victim);
        Vector#(4, Bit#(64)) x_9 = ((x_0).lr_value);
        let x_10 <- getMSHR_002(x_4);
        let x_11 <- getMSHRRq_002(x_4);
        Struct1 x_12 = (unpack(0));
        Vector#(4, Bit#(64)) x_13 = (unpack(0));
        Bool x_14 = ((x_7).mesi_owned);
        Bit#(3) x_15 = ((x_7).mesi_status);
        Struct15 x_16 = (Struct15 {dir_st : (((x_7).mesi_dir_st) ==
        ((Bit#(3))'(3'h0)) ? ((Bit#(3))'(3'h1)) : ((x_7).mesi_dir_st)),
        dir_excl : ((((x_7).mesi_dir_sharers)[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        ((((((x_7).mesi_dir_sharers)[3:1])[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        (((((((x_7).mesi_dir_sharers)[3:1])[2:1])[0:0]) == ((Bit#(1))'(1'h1))
        ? ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        ((((((((x_7).mesi_dir_sharers)[3:1])[2:1])[1:1])[0:0]) ==
        ((Bit#(1))'(1'h1)) ? ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        (unpack(0))))))))))))), dir_sharers : (x_7).mesi_dir_sharers});
        when ((x_2) == ({((Bit#(2))'(2'h2)),((Bit#(2))'(2'h2))}),
        noAction);
        when (((x_3).id) == ((Bit#(6))'(6'h4)), noAction);
        when ((x_10).m_rsb, noAction);
        when (((x_11).type_) == ((Bool)'(False)), noAction);
        when (((x_11).id) == ((Bit#(6))'(6'h0)), noAction);
        when ((x_10).m_rsb, noAction);
        when ((x_3).type_, noAction);
        when ((Bool)'(True), noAction);
        Struct1 x_17 = (x_3);
        Struct1 x_18 = (x_11);
        Bit#(4) x_19 = ({((Bit#(2))'(2'h2)),(((x_10).m_qidx)[1:0])});
        Struct42 x_20 = (Struct42 {addr : (x_3).addr, info_write :
        (Bool)'(False), info_hit : (x_6).info_hit, info_way : (x_6).info_way,
        edir_hit : (x_6).edir_hit, edir_way : (x_6).edir_way, edir_slot :
        (x_6).edir_slot, info : (x_6).info, value_write : (Bool)'(False),
        value : unpack(0), may_victim : (x_6).may_victim, reps :
        (x_6).reps});
        Struct42 x_21 = (Struct42 {addr : (x_20).addr, info_write :
        (Bool)'(True), info_hit : (x_20).info_hit, info_way :
        (x_20).info_way, edir_hit : (x_20).edir_hit, edir_way :
        (x_20).edir_way, edir_slot : (x_20).edir_slot, info : Struct10
        {mesi_owned : ((x_20).info).mesi_owned, mesi_status :
        (Bit#(3))'(3'h3), mesi_dir_st : ((x_20).info).mesi_dir_st,
        mesi_dir_sharers : ((x_20).info).mesi_dir_sharers}, value_write :
        (x_20).value_write, value : (x_20).value, may_victim :
        (x_20).may_victim, reps : (x_20).reps});
        Struct42 x_22 = (Struct42 {addr : (x_21).addr, info_write :
        (x_21).info_write, info_hit : (x_21).info_hit, info_way :
        (x_21).info_way, edir_hit : (x_21).edir_hit, edir_way :
        (x_21).edir_way, edir_slot : (x_21).edir_slot, info : (x_21).info,
        value_write : (Bool)'(True), value : (x_17).value, may_victim :
        (x_21).may_victim, reps :
        (x_21).reps});
        let x_25 = ?;
        if ((x_8).valid) begin
            let x_23 <- victims__002__setVictim(Struct44 {victim_idx :
            (x_8).data, victim_info : (x_22).info, victim_value :
            ((x_22).value_write ? ((x_22).value) : (x_9))});
            x_25 = x_9;
        end else begin
            let x_24 <- cache__002__valueRsLineRq(x_22);
            x_25 = x_24;
        end
        let x_26 <- releaseMSHR_002(x_4);
        Struct18 x_27 = (Struct18 {enq_type : (((x_19)[3:2]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : ((((x_19)[3:2]) ==
        ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : (x_19)[1:0], enq_msg : Struct1 {id : (Bit#(6))'(6'h1),
        type_ : (Bool)'(True), addr : (x_17).addr, value :
        (x_17).value}});
        let x_28 <- makeEnq_parentChildren002(x_27);
    endrule

    rule rule_exec_002_03;
        let x_0 <- deq_fifoL2E_002();
        Struct38 x_1 = ((x_0).lr_ir_pp);
        Bit#(4) x_2 = ((x_1).ir_msg_from);
        Struct1 x_3 = ((x_1).ir_msg);
        Bit#(2) x_4 = ((x_1).ir_mshr_id);
        Bool x_5 = ((x_1).ir_is_rs_rel);
        when (! (x_5), noAction);
        Struct39 x_6 = ((x_0).lr_ir);
        Struct10 x_7 = ((x_6).info);
        Struct37 x_8 = ((x_1).ir_by_victim);
        Vector#(4, Bit#(64)) x_9 = ((x_0).lr_value);
        let x_10 <- getMSHR_002(x_4);
        let x_11 <- getMSHRRq_002(x_4);
        Struct1 x_12 = (unpack(0));
        Vector#(4, Bit#(64)) x_13 = (unpack(0));
        Bool x_14 = ((x_7).mesi_owned);
        Bit#(3) x_15 = ((x_7).mesi_status);
        Struct15 x_16 = (Struct15 {dir_st : (((x_7).mesi_dir_st) ==
        ((Bit#(3))'(3'h0)) ? ((Bit#(3))'(3'h1)) : ((x_7).mesi_dir_st)),
        dir_excl : ((((x_7).mesi_dir_sharers)[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        ((((((x_7).mesi_dir_sharers)[3:1])[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        (((((((x_7).mesi_dir_sharers)[3:1])[2:1])[0:0]) == ((Bit#(1))'(1'h1))
        ? ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        ((((((((x_7).mesi_dir_sharers)[3:1])[2:1])[1:1])[0:0]) ==
        ((Bit#(1))'(1'h1)) ? ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        (unpack(0))))))))))))), dir_sharers : (x_7).mesi_dir_sharers});
        when ((x_2) == ((Bit#(4))'(4'ha)), noAction);
        when (((x_3).id) == ((Bit#(6))'(6'h5)), noAction);
        when (! ((x_3).type_), noAction);
        when (! ((x_15) < ((Bit#(3))'(3'h2))), noAction);
        Struct1 x_17 = (x_3);
        Struct42 x_18 = (Struct42 {addr : (x_3).addr, info_write :
        (Bool)'(False), info_hit : (x_6).info_hit, info_way : (x_6).info_way,
        edir_hit : (x_6).edir_hit, edir_way : (x_6).edir_way, edir_slot :
        (x_6).edir_slot, info : (x_6).info, value_write : (Bool)'(False),
        value : unpack(0), may_victim : (x_6).may_victim, reps :
        (x_6).reps});
        Struct42 x_19 = (Struct42 {addr : (x_18).addr, info_write :
        (Bool)'(True), info_hit : (x_18).info_hit, info_way :
        (x_18).info_way, edir_hit : (x_18).edir_hit, edir_way :
        (x_18).edir_way, edir_slot : (x_18).edir_slot, info : Struct10
        {mesi_owned : ((x_18).info).mesi_owned, mesi_status :
        (Bit#(3))'(3'h2), mesi_dir_st : ((x_18).info).mesi_dir_st,
        mesi_dir_sharers : ((x_18).info).mesi_dir_sharers}, value_write :
        (x_18).value_write, value : (x_18).value, may_victim :
        (x_18).may_victim, reps : (x_18).reps});
        Struct42 x_20 = (Struct42 {addr : (x_19).addr, info_write :
        (Bool)'(True), info_hit : (x_19).info_hit, info_way :
        (x_19).info_way, edir_hit : (x_19).edir_hit, edir_way :
        (x_19).edir_way, edir_slot : (x_19).edir_slot, info : Struct10
        {mesi_owned : (Bool)'(False), mesi_status :
        ((x_19).info).mesi_status, mesi_dir_st : ((x_19).info).mesi_dir_st,
        mesi_dir_sharers : ((x_19).info).mesi_dir_sharers}, value_write :
        (x_19).value_write, value : (x_19).value, may_victim :
        (x_19).may_victim, reps :
        (x_19).reps});
        let x_23 = ?;
        if ((x_8).valid) begin
            let x_21 <- victims__002__setVictim(Struct44 {victim_idx :
            (x_8).data, victim_info : (x_20).info, victim_value :
            ((x_20).value_write ? ((x_20).value) : (x_9))});
            x_23 = x_9;
        end else begin
            let x_22 <- cache__002__valueRsLineRq(x_20);
            x_23 = x_22;
        end
        Struct18 x_24 = (Struct18 {enq_type : ((((Bit#(4))'(4'h6))[3:2]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : (((((Bit#(4))'(4'h6))[3:2])
        == ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : ((Bit#(4))'(4'h6))[1:0], enq_msg : Struct1 {id :
        (Bit#(6))'(6'h6), type_ : (Bool)'(True), addr : (x_17).addr, value :
        x_23}});
        let x_25 <- makeEnq_parentChildren002(x_24);
        let x_26 <- releaseMSHR_002(x_4);
    endrule

    rule rule_exec_002_100;
        let x_0 <- deq_fifoL2E_002();
        Struct38 x_1 = ((x_0).lr_ir_pp);
        Bit#(4) x_2 = ((x_1).ir_msg_from);
        Struct1 x_3 = ((x_1).ir_msg);
        Bit#(2) x_4 = ((x_1).ir_mshr_id);
        Bool x_5 = ((x_1).ir_is_rs_rel);
        when (! (x_5), noAction);
        Struct39 x_6 = ((x_0).lr_ir);
        Struct10 x_7 = ((x_6).info);
        Struct37 x_8 = ((x_1).ir_by_victim);
        Vector#(4, Bit#(64)) x_9 = ((x_0).lr_value);
        let x_10 <- getMSHR_002(x_4);
        let x_11 <- getMSHRRq_002(x_4);
        Struct1 x_12 = (unpack(0));
        Vector#(4, Bit#(64)) x_13 = (unpack(0));
        Bool x_14 = ((x_7).mesi_owned);
        Bit#(3) x_15 = ((x_7).mesi_status);
        Struct15 x_16 = (Struct15 {dir_st : (((x_7).mesi_dir_st) ==
        ((Bit#(3))'(3'h0)) ? ((Bit#(3))'(3'h1)) : ((x_7).mesi_dir_st)),
        dir_excl : ((((x_7).mesi_dir_sharers)[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        ((((((x_7).mesi_dir_sharers)[3:1])[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        (((((((x_7).mesi_dir_sharers)[3:1])[2:1])[0:0]) == ((Bit#(1))'(1'h1))
        ? ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        ((((((((x_7).mesi_dir_sharers)[3:1])[2:1])[1:1])[0:0]) ==
        ((Bit#(1))'(1'h1)) ? ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        (unpack(0))))))))))))), dir_sharers : (x_7).mesi_dir_sharers});
        when ((x_2) == ((Bit#(4))'(4'h0)), noAction);
        when (((x_3).id) == ((Bit#(6))'(6'h8)), noAction);
        when (! ((x_3).type_), noAction);
        when ((x_15) == ((Bit#(3))'(3'h3)), noAction);
        Struct1 x_17 = (x_3);
        Struct42 x_18 = (Struct42 {addr : (x_3).addr, info_write :
        (Bool)'(False), info_hit : (x_6).info_hit, info_way : (x_6).info_way,
        edir_hit : (x_6).edir_hit, edir_way : (x_6).edir_way, edir_slot :
        (x_6).edir_slot, info : (x_6).info, value_write : (Bool)'(False),
        value : unpack(0), may_victim : (x_6).may_victim, reps :
        (x_6).reps});
        Struct42 x_19 = (Struct42 {addr : (x_18).addr, info_write :
        (x_18).info_write, info_hit : (x_18).info_hit, info_way :
        (x_18).info_way, edir_hit : (x_18).edir_hit, edir_way :
        (x_18).edir_way, edir_slot : (x_18).edir_slot, info : (x_18).info,
        value_write : (Bool)'(True), value : (x_17).value, may_victim :
        (x_18).may_victim, reps : (x_18).reps});
        Struct42 x_20 = (Struct42 {addr : (x_19).addr, info_write :
        (Bool)'(True), info_hit : (x_19).info_hit, info_way :
        (x_19).info_way, edir_hit : (x_19).edir_hit, edir_way :
        (x_19).edir_way, edir_slot : (x_19).edir_slot, info : Struct10
        {mesi_owned : ((x_19).info).mesi_owned, mesi_status :
        (Bit#(3))'(3'h4), mesi_dir_st : ((x_19).info).mesi_dir_st,
        mesi_dir_sharers : ((x_19).info).mesi_dir_sharers}, value_write :
        (x_19).value_write, value : (x_19).value, may_victim :
        (x_19).may_victim, reps : (x_19).reps});
        Struct42 x_21 = (Struct42 {addr : (x_20).addr, info_write :
        (Bool)'(True), info_hit : (x_20).info_hit, info_way :
        (x_20).info_way, edir_hit : (x_20).edir_hit, edir_way :
        (x_20).edir_way, edir_slot : (x_20).edir_slot, info : Struct10
        {mesi_owned : (Bool)'(True), mesi_status : ((x_20).info).mesi_status,
        mesi_dir_st : ((x_20).info).mesi_dir_st, mesi_dir_sharers :
        ((x_20).info).mesi_dir_sharers}, value_write : (x_20).value_write,
        value : (x_20).value, may_victim : (x_20).may_victim, reps :
        (x_20).reps});
        let x_24 = ?;
        if ((x_8).valid) begin
            let x_22 <- victims__002__setVictim(Struct44 {victim_idx :
            (x_8).data, victim_info : (x_21).info, victim_value :
            ((x_21).value_write ? ((x_21).value) : (x_9))});
            x_24 = x_9;
        end else begin
            let x_23 <- cache__002__valueRsLineRq(x_21);
            x_24 = x_23;
        end
        Struct18 x_25 = (Struct18 {enq_type : ((((Bit#(4))'(4'h8))[3:2]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : (((((Bit#(4))'(4'h8))[3:2])
        == ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : ((Bit#(4))'(4'h8))[1:0], enq_msg : Struct1 {id :
        (Bit#(6))'(6'h9), type_ : (Bool)'(True), addr : (x_17).addr, value :
        unpack(0)}});
        let x_26 <- makeEnq_parentChildren002(x_25);
        let x_27 <- releaseMSHR_002(x_4);
    endrule

    rule rule_exec_002_101;
        let x_0 <- deq_fifoL2E_002();
        Struct38 x_1 = ((x_0).lr_ir_pp);
        Bit#(4) x_2 = ((x_1).ir_msg_from);
        Struct1 x_3 = ((x_1).ir_msg);
        Bit#(2) x_4 = ((x_1).ir_mshr_id);
        Bool x_5 = ((x_1).ir_is_rs_rel);
        when (! (x_5), noAction);
        Struct39 x_6 = ((x_0).lr_ir);
        Struct10 x_7 = ((x_6).info);
        Struct37 x_8 = ((x_1).ir_by_victim);
        Vector#(4, Bit#(64)) x_9 = ((x_0).lr_value);
        let x_10 <- getMSHR_002(x_4);
        let x_11 <- getMSHRRq_002(x_4);
        Struct1 x_12 = (unpack(0));
        Vector#(4, Bit#(64)) x_13 = (unpack(0));
        Bool x_14 = ((x_7).mesi_owned);
        Bit#(3) x_15 = ((x_7).mesi_status);
        Struct15 x_16 = (Struct15 {dir_st : (((x_7).mesi_dir_st) ==
        ((Bit#(3))'(3'h0)) ? ((Bit#(3))'(3'h1)) : ((x_7).mesi_dir_st)),
        dir_excl : ((((x_7).mesi_dir_sharers)[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        ((((((x_7).mesi_dir_sharers)[3:1])[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        (((((((x_7).mesi_dir_sharers)[3:1])[2:1])[0:0]) == ((Bit#(1))'(1'h1))
        ? ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        ((((((((x_7).mesi_dir_sharers)[3:1])[2:1])[1:1])[0:0]) ==
        ((Bit#(1))'(1'h1)) ? ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        (unpack(0))))))))))))), dir_sharers : (x_7).mesi_dir_sharers});
        when ((x_2) == ((Bit#(4))'(4'h0)), noAction);
        when (((x_3).id) == ((Bit#(6))'(6'h8)), noAction);
        when (! ((x_3).type_), noAction);
        when (((x_14) == ((Bool)'(True))) && ((x_15) == ((Bit#(3))'(3'h4))),
        noAction);
        Struct1 x_17 = (x_3);
        Struct42 x_18 = (Struct42 {addr : (x_3).addr, info_write :
        (Bool)'(False), info_hit : (x_6).info_hit, info_way : (x_6).info_way,
        edir_hit : (x_6).edir_hit, edir_way : (x_6).edir_way, edir_slot :
        (x_6).edir_slot, info : (x_6).info, value_write : (Bool)'(False),
        value : unpack(0), may_victim : (x_6).may_victim, reps :
        (x_6).reps});
        Struct42 x_19 = (Struct42 {addr : (x_18).addr, info_write :
        (x_18).info_write, info_hit : (x_18).info_hit, info_way :
        (x_18).info_way, edir_hit : (x_18).edir_hit, edir_way :
        (x_18).edir_way, edir_slot : (x_18).edir_slot, info : (x_18).info,
        value_write : (Bool)'(True), value : (x_17).value, may_victim :
        (x_18).may_victim, reps :
        (x_18).reps});
        let x_22 = ?;
        if ((x_8).valid) begin
            let x_20 <- victims__002__setVictim(Struct44 {victim_idx :
            (x_8).data, victim_info : (x_19).info, victim_value :
            ((x_19).value_write ? ((x_19).value) : (x_9))});
            x_22 = x_9;
        end else begin
            let x_21 <- cache__002__valueRsLineRq(x_19);
            x_22 = x_21;
        end
        Struct18 x_23 = (Struct18 {enq_type : ((((Bit#(4))'(4'h8))[3:2]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : (((((Bit#(4))'(4'h8))[3:2])
        == ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : ((Bit#(4))'(4'h8))[1:0], enq_msg : Struct1 {id :
        (Bit#(6))'(6'h9), type_ : (Bool)'(True), addr : (x_17).addr, value :
        unpack(0)}});
        let x_24 <- makeEnq_parentChildren002(x_23);
        let x_25 <- releaseMSHR_002(x_4);
    endrule

    rule rule_exec_002_11;
        let x_0 <- deq_fifoL2E_002();
        Struct38 x_1 = ((x_0).lr_ir_pp);
        Bit#(4) x_2 = ((x_1).ir_msg_from);
        Struct1 x_3 = ((x_1).ir_msg);
        Bit#(2) x_4 = ((x_1).ir_mshr_id);
        Bool x_5 = ((x_1).ir_is_rs_rel);
        when (! (x_5), noAction);
        Struct39 x_6 = ((x_0).lr_ir);
        Struct10 x_7 = ((x_6).info);
        Struct37 x_8 = ((x_1).ir_by_victim);
        Vector#(4, Bit#(64)) x_9 = ((x_0).lr_value);
        let x_10 <- getMSHR_002(x_4);
        let x_11 <- getMSHRRq_002(x_4);
        Struct1 x_12 = (unpack(0));
        Vector#(4, Bit#(64)) x_13 = (unpack(0));
        Bool x_14 = ((x_7).mesi_owned);
        Bit#(3) x_15 = ((x_7).mesi_status);
        Struct15 x_16 = (Struct15 {dir_st : (((x_7).mesi_dir_st) ==
        ((Bit#(3))'(3'h0)) ? ((Bit#(3))'(3'h1)) : ((x_7).mesi_dir_st)),
        dir_excl : ((((x_7).mesi_dir_sharers)[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        ((((((x_7).mesi_dir_sharers)[3:1])[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        (((((((x_7).mesi_dir_sharers)[3:1])[2:1])[0:0]) == ((Bit#(1))'(1'h1))
        ? ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        ((((((((x_7).mesi_dir_sharers)[3:1])[2:1])[1:1])[0:0]) ==
        ((Bit#(1))'(1'h1)) ? ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        (unpack(0))))))))))))), dir_sharers : (x_7).mesi_dir_sharers});
        when ((x_2) == ((Bit#(4))'(4'h0)), noAction);
        when (((x_3).id) == ((Bit#(6))'(6'h8)), noAction);
        when (! ((x_3).type_), noAction);
        when (! (((Bit#(3))'(3'h2)) < (x_15)), noAction);
        Struct1 x_17 = (x_3);
        Struct42 x_18 = (Struct42 {addr : (x_3).addr, info_write :
        (Bool)'(False), info_hit : (x_6).info_hit, info_way : (x_6).info_way,
        edir_hit : (x_6).edir_hit, edir_way : (x_6).edir_way, edir_slot :
        (x_6).edir_slot, info : (x_6).info, value_write : (Bool)'(False),
        value : unpack(0), may_victim : (x_6).may_victim, reps :
        (x_6).reps});
        let x_20 = ?;
        if ((x_8).valid) begin
            x_20 = x_9;
        end else begin
            let x_19 <- cache__002__valueRsLineRq(unpack(0));
            x_20 = x_19;
        end
        let x_21 <- registerUL_002(Struct43 {r_id : x_4, r_ul_rsb :
        (Bool)'(True), r_ul_rsbTo : ((Bit#(4))'(4'h8))[1:0]});
        Struct18 x_22 = (Struct18 {enq_type : ((((Bit#(4))'(4'h2))[3:2]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : (((((Bit#(4))'(4'h2))[3:2])
        == ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : ((Bit#(4))'(4'h2))[1:0], enq_msg : Struct1 {id :
        (Bit#(6))'(6'ha), type_ : (Bool)'(False), addr : (x_17).addr, value :
        unpack(0)}});
        let x_23 <- makeEnq_parentChildren002(x_22);
    endrule

    rule rule_exec_002_12;
        let x_0 <- deq_fifoL2E_002();
        Struct38 x_1 = ((x_0).lr_ir_pp);
        Bit#(4) x_2 = ((x_1).ir_msg_from);
        Struct1 x_3 = ((x_1).ir_msg);
        Bit#(2) x_4 = ((x_1).ir_mshr_id);
        Bool x_5 = ((x_1).ir_is_rs_rel);
        when (! (x_5), noAction);
        Struct39 x_6 = ((x_0).lr_ir);
        Struct10 x_7 = ((x_6).info);
        Struct37 x_8 = ((x_1).ir_by_victim);
        Vector#(4, Bit#(64)) x_9 = ((x_0).lr_value);
        let x_10 <- getMSHR_002(x_4);
        let x_11 <- getMSHRRq_002(x_4);
        Struct1 x_12 = (unpack(0));
        Vector#(4, Bit#(64)) x_13 = (unpack(0));
        Bool x_14 = ((x_7).mesi_owned);
        Bit#(3) x_15 = ((x_7).mesi_status);
        Struct15 x_16 = (Struct15 {dir_st : (((x_7).mesi_dir_st) ==
        ((Bit#(3))'(3'h0)) ? ((Bit#(3))'(3'h1)) : ((x_7).mesi_dir_st)),
        dir_excl : ((((x_7).mesi_dir_sharers)[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        ((((((x_7).mesi_dir_sharers)[3:1])[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        (((((((x_7).mesi_dir_sharers)[3:1])[2:1])[0:0]) == ((Bit#(1))'(1'h1))
        ? ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        ((((((((x_7).mesi_dir_sharers)[3:1])[2:1])[1:1])[0:0]) ==
        ((Bit#(1))'(1'h1)) ? ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        (unpack(0))))))))))))), dir_sharers : (x_7).mesi_dir_sharers});
        when ((x_2) == ({((Bit#(2))'(2'h2)),((Bit#(2))'(2'h2))}),
        noAction);
        when (((x_3).id) == ((Bit#(6))'(6'hb)), noAction);
        when ((x_10).m_rsb, noAction);
        when (((x_11).type_) == ((Bool)'(False)), noAction);
        when (((x_11).id) == ((Bit#(6))'(6'h8)), noAction);
        when ((x_10).m_rsb, noAction);
        when ((x_3).type_, noAction);
        when ((Bool)'(True), noAction);
        Struct1 x_17 = (x_3);
        Struct1 x_18 = (x_11);
        Bit#(4) x_19 = ({((Bit#(2))'(2'h2)),(((x_10).m_qidx)[1:0])});
        Struct42 x_20 = (Struct42 {addr : (x_3).addr, info_write :
        (Bool)'(False), info_hit : (x_6).info_hit, info_way : (x_6).info_way,
        edir_hit : (x_6).edir_hit, edir_way : (x_6).edir_way, edir_slot :
        (x_6).edir_slot, info : (x_6).info, value_write : (Bool)'(False),
        value : unpack(0), may_victim : (x_6).may_victim, reps :
        (x_6).reps});
        Struct42 x_21 = (Struct42 {addr : (x_20).addr, info_write :
        (x_20).info_write, info_hit : (x_20).info_hit, info_way :
        (x_20).info_way, edir_hit : (x_20).edir_hit, edir_way :
        (x_20).edir_way, edir_slot : (x_20).edir_slot, info : (x_20).info,
        value_write : (Bool)'(True), value : (x_18).value, may_victim :
        (x_20).may_victim, reps : (x_20).reps});
        Struct42 x_22 = (Struct42 {addr : (x_21).addr, info_write :
        (Bool)'(True), info_hit : (x_21).info_hit, info_way :
        (x_21).info_way, edir_hit : (x_21).edir_hit, edir_way :
        (x_21).edir_way, edir_slot : (x_21).edir_slot, info : Struct10
        {mesi_owned : (Bool)'(True), mesi_status : ((x_21).info).mesi_status,
        mesi_dir_st : ((x_21).info).mesi_dir_st, mesi_dir_sharers :
        ((x_21).info).mesi_dir_sharers}, value_write : (x_21).value_write,
        value : (x_21).value, may_victim : (x_21).may_victim, reps :
        (x_21).reps});
        Struct42 x_23 = (Struct42 {addr : (x_22).addr, info_write :
        (Bool)'(True), info_hit : (x_22).info_hit, info_way :
        (x_22).info_way, edir_hit : (x_22).edir_hit, edir_way :
        (x_22).edir_way, edir_slot : (x_22).edir_slot, info : Struct10
        {mesi_owned : ((x_22).info).mesi_owned, mesi_status :
        (Bit#(3))'(3'h4), mesi_dir_st : ((x_22).info).mesi_dir_st,
        mesi_dir_sharers : ((x_22).info).mesi_dir_sharers}, value_write :
        (x_22).value_write, value : (x_22).value, may_victim :
        (x_22).may_victim, reps :
        (x_22).reps});
        let x_26 = ?;
        if ((x_8).valid) begin
            let x_24 <- victims__002__setVictim(Struct44 {victim_idx :
            (x_8).data, victim_info : (x_23).info, victim_value :
            ((x_23).value_write ? ((x_23).value) : (x_9))});
            x_26 = x_9;
        end else begin
            let x_25 <- cache__002__valueRsLineRq(x_23);
            x_26 = x_25;
        end
        let x_27 <- releaseMSHR_002(x_4);
        Struct18 x_28 = (Struct18 {enq_type : (((x_19)[3:2]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : ((((x_19)[3:2]) ==
        ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : (x_19)[1:0], enq_msg : Struct1 {id : (Bit#(6))'(6'h9),
        type_ : (Bool)'(True), addr : (x_17).addr, value : unpack(0)}});
        let x_29 <- makeEnq_parentChildren002(x_28);
    endrule

    rule rule_exec_002_130;
        let x_0 <- deq_fifoL2E_002();
        Struct38 x_1 = ((x_0).lr_ir_pp);
        Bit#(4) x_2 = ((x_1).ir_msg_from);
        Struct1 x_3 = ((x_1).ir_msg);
        Bit#(2) x_4 = ((x_1).ir_mshr_id);
        Bool x_5 = ((x_1).ir_is_rs_rel);
        when (! (x_5), noAction);
        Struct39 x_6 = ((x_0).lr_ir);
        Struct10 x_7 = ((x_6).info);
        Struct37 x_8 = ((x_1).ir_by_victim);
        Vector#(4, Bit#(64)) x_9 = ((x_0).lr_value);
        let x_10 <- getMSHR_002(x_4);
        let x_11 <- getMSHRRq_002(x_4);
        Struct1 x_12 = (unpack(0));
        Vector#(4, Bit#(64)) x_13 = (unpack(0));
        Bool x_14 = ((x_7).mesi_owned);
        Bit#(3) x_15 = ((x_7).mesi_status);
        Struct15 x_16 = (Struct15 {dir_st : (((x_7).mesi_dir_st) ==
        ((Bit#(3))'(3'h0)) ? ((Bit#(3))'(3'h1)) : ((x_7).mesi_dir_st)),
        dir_excl : ((((x_7).mesi_dir_sharers)[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        ((((((x_7).mesi_dir_sharers)[3:1])[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        (((((((x_7).mesi_dir_sharers)[3:1])[2:1])[0:0]) == ((Bit#(1))'(1'h1))
        ? ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        ((((((((x_7).mesi_dir_sharers)[3:1])[2:1])[1:1])[0:0]) ==
        ((Bit#(1))'(1'h1)) ? ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        (unpack(0))))))))))))), dir_sharers : (x_7).mesi_dir_sharers});
        when ((x_2) == ((Bit#(4))'(4'ha)), noAction);
        when (((x_3).id) == ((Bit#(6))'(6'hc)), noAction);
        when (! ((x_3).type_), noAction);
        when ((Bool)'(True), noAction);
        Struct1 x_17 = (x_3);
        Struct42 x_18 = (Struct42 {addr : (x_3).addr, info_write :
        (Bool)'(False), info_hit : (x_6).info_hit, info_way : (x_6).info_way,
        edir_hit : (x_6).edir_hit, edir_way : (x_6).edir_way, edir_slot :
        (x_6).edir_slot, info : (x_6).info, value_write : (Bool)'(False),
        value : unpack(0), may_victim : (x_6).may_victim, reps :
        (x_6).reps});
        Struct42 x_19 = (Struct42 {addr : (x_18).addr, info_write :
        (Bool)'(True), info_hit : (x_18).info_hit, info_way :
        (x_18).info_way, edir_hit : (x_18).edir_hit, edir_way :
        (x_18).edir_way, edir_slot : (x_18).edir_slot, info : Struct10
        {mesi_owned : ((x_18).info).mesi_owned, mesi_status :
        (Bit#(3))'(3'h1), mesi_dir_st : ((x_18).info).mesi_dir_st,
        mesi_dir_sharers : ((x_18).info).mesi_dir_sharers}, value_write :
        (x_18).value_write, value : (x_18).value, may_victim :
        (x_18).may_victim, reps : (x_18).reps});
        Struct42 x_20 = (Struct42 {addr : (x_19).addr, info_write :
        (Bool)'(True), info_hit : (x_19).info_hit, info_way :
        (x_19).info_way, edir_hit : (x_19).edir_hit, edir_way :
        (x_19).edir_way, edir_slot : (x_19).edir_slot, info : Struct10
        {mesi_owned : (Bool)'(False), mesi_status :
        ((x_19).info).mesi_status, mesi_dir_st : ((x_19).info).mesi_dir_st,
        mesi_dir_sharers : ((x_19).info).mesi_dir_sharers}, value_write :
        (x_19).value_write, value : (x_19).value, may_victim :
        (x_19).may_victim, reps :
        (x_19).reps});
        let x_23 = ?;
        if ((x_8).valid) begin
            let x_21 <- victims__002__setVictim(Struct44 {victim_idx :
            (x_8).data, victim_info : (x_20).info, victim_value :
            ((x_20).value_write ? ((x_20).value) : (x_9))});
            x_23 = x_9;
        end else begin
            let x_22 <- cache__002__valueRsLineRq(x_20);
            x_23 = x_22;
        end
        Struct18 x_24 = (Struct18 {enq_type : ((((Bit#(4))'(4'h6))[3:2]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : (((((Bit#(4))'(4'h6))[3:2])
        == ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : ((Bit#(4))'(4'h6))[1:0], enq_msg : Struct1 {id :
        (Bit#(6))'(6'hd), type_ : (Bool)'(True), addr : (x_17).addr, value :
        unpack(0)}});
        let x_25 <- makeEnq_parentChildren002(x_24);
        let x_26 <- releaseMSHR_002(x_4);
    endrule

    rule rule_exec_002_131;
        let x_0 <- deq_fifoL2E_002();
        Struct38 x_1 = ((x_0).lr_ir_pp);
        Bit#(4) x_2 = ((x_1).ir_msg_from);
        Struct1 x_3 = ((x_1).ir_msg);
        Bit#(2) x_4 = ((x_1).ir_mshr_id);
        Bool x_5 = ((x_1).ir_is_rs_rel);
        when (! (x_5), noAction);
        Struct39 x_6 = ((x_0).lr_ir);
        Struct10 x_7 = ((x_6).info);
        Struct37 x_8 = ((x_1).ir_by_victim);
        Vector#(4, Bit#(64)) x_9 = ((x_0).lr_value);
        let x_10 <- getMSHR_002(x_4);
        let x_11 <- getMSHRRq_002(x_4);
        Struct1 x_12 = (unpack(0));
        Vector#(4, Bit#(64)) x_13 = (unpack(0));
        Bool x_14 = ((x_7).mesi_owned);
        Bit#(3) x_15 = ((x_7).mesi_status);
        Struct15 x_16 = (Struct15 {dir_st : (((x_7).mesi_dir_st) ==
        ((Bit#(3))'(3'h0)) ? ((Bit#(3))'(3'h1)) : ((x_7).mesi_dir_st)),
        dir_excl : ((((x_7).mesi_dir_sharers)[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        ((((((x_7).mesi_dir_sharers)[3:1])[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        (((((((x_7).mesi_dir_sharers)[3:1])[2:1])[0:0]) == ((Bit#(1))'(1'h1))
        ? ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        ((((((((x_7).mesi_dir_sharers)[3:1])[2:1])[1:1])[0:0]) ==
        ((Bit#(1))'(1'h1)) ? ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        (unpack(0))))))))))))), dir_sharers : (x_7).mesi_dir_sharers});
        when ((x_2) == ((Bit#(4))'(4'ha)), noAction);
        when (((x_3).id) == ((Bit#(6))'(6'he)), noAction);
        when (! ((x_3).type_), noAction);
        when (! ((x_15) < ((Bit#(3))'(3'h3))), noAction);
        Struct1 x_17 = (x_3);
        Struct42 x_18 = (Struct42 {addr : (x_3).addr, info_write :
        (Bool)'(False), info_hit : (x_6).info_hit, info_way : (x_6).info_way,
        edir_hit : (x_6).edir_hit, edir_way : (x_6).edir_way, edir_slot :
        (x_6).edir_slot, info : (x_6).info, value_write : (Bool)'(False),
        value : unpack(0), may_victim : (x_6).may_victim, reps :
        (x_6).reps});
        Struct42 x_19 = (Struct42 {addr : (x_18).addr, info_write :
        (Bool)'(True), info_hit : (x_18).info_hit, info_way :
        (x_18).info_way, edir_hit : (x_18).edir_hit, edir_way :
        (x_18).edir_way, edir_slot : (x_18).edir_slot, info : Struct10
        {mesi_owned : ((x_18).info).mesi_owned, mesi_status :
        (Bit#(3))'(3'h1), mesi_dir_st : ((x_18).info).mesi_dir_st,
        mesi_dir_sharers : ((x_18).info).mesi_dir_sharers}, value_write :
        (x_18).value_write, value : (x_18).value, may_victim :
        (x_18).may_victim, reps : (x_18).reps});
        Struct42 x_20 = (Struct42 {addr : (x_19).addr, info_write :
        (Bool)'(True), info_hit : (x_19).info_hit, info_way :
        (x_19).info_way, edir_hit : (x_19).edir_hit, edir_way :
        (x_19).edir_way, edir_slot : (x_19).edir_slot, info : Struct10
        {mesi_owned : (Bool)'(False), mesi_status :
        ((x_19).info).mesi_status, mesi_dir_st : ((x_19).info).mesi_dir_st,
        mesi_dir_sharers : ((x_19).info).mesi_dir_sharers}, value_write :
        (x_19).value_write, value : (x_19).value, may_victim :
        (x_19).may_victim, reps :
        (x_19).reps});
        let x_23 = ?;
        if ((x_8).valid) begin
            let x_21 <- victims__002__setVictim(Struct44 {victim_idx :
            (x_8).data, victim_info : (x_20).info, victim_value :
            ((x_20).value_write ? ((x_20).value) : (x_9))});
            x_23 = x_9;
        end else begin
            let x_22 <- cache__002__valueRsLineRq(x_20);
            x_23 = x_22;
        end
        Struct18 x_24 = (Struct18 {enq_type : ((((Bit#(4))'(4'h6))[3:2]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : (((((Bit#(4))'(4'h6))[3:2])
        == ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : ((Bit#(4))'(4'h6))[1:0], enq_msg : Struct1 {id :
        (Bit#(6))'(6'hf), type_ : (Bool)'(True), addr : (x_17).addr, value :
        unpack(0)}});
        let x_25 <- makeEnq_parentChildren002(x_24);
        let x_26 <- releaseMSHR_002(x_4);
    endrule

    rule rule_exec_002_20;
        let x_0 <- victims__002__getFirstVictim();
        Bit#(64) x_1 = ((x_0).victim_addr);
        Struct10 x_2 = ((x_0).victim_info);
        Vector#(4, Bit#(64)) x_3 = ((x_0).victim_value);
        Struct1 x_4 = (Struct1 {id : unpack(0), type_ : (Bool)'(False), addr
        : x_1, value : unpack(0)});
        Struct14 x_5 = (Struct14 {m_is_ul : (Bool)'(True), m_qidx :
        unpack(0), m_rsb : (Bool)'(False), m_dl_rss_from : unpack(0),
        m_dl_rss_recv : unpack(0)});
        Struct1 x_6 = (unpack(0));
        Struct1 x_7 = (unpack(0));
        Vector#(4, Bit#(64)) x_8 = (unpack(0));
        Bool x_9 = ((x_2).mesi_owned);
        Bit#(3) x_10 = ((x_2).mesi_status);
        Struct15 x_11 = (Struct15 {dir_st : (((x_2).mesi_dir_st) ==
        ((Bit#(3))'(3'h0)) ? ((Bit#(3))'(3'h1)) : ((x_2).mesi_dir_st)),
        dir_excl : ((((x_2).mesi_dir_sharers)[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        ((((((x_2).mesi_dir_sharers)[3:1])[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        (((((((x_2).mesi_dir_sharers)[3:1])[2:1])[0:0]) == ((Bit#(1))'(1'h1))
        ? ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        ((((((((x_2).mesi_dir_sharers)[3:1])[2:1])[1:1])[0:0]) ==
        ((Bit#(1))'(1'h1)) ? ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        (unpack(0))))))))))))), dir_sharers : (x_2).mesi_dir_sharers});
        when (! ((x_4).type_), noAction);
        when (((x_9) == ((Bool)'(False))) && ((((Bit#(3))'(3'h0)) < (x_10))
        && ((x_10) < ((Bit#(3))'(3'h4)))), noAction);
        Struct18 x_12 = (Struct18 {enq_type : ((((Bit#(4))'(4'h2))[3:2]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : (((((Bit#(4))'(4'h2))[3:2])
        == ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : ((Bit#(4))'(4'h2))[1:0], enq_msg : Struct1 {id :
        (Bit#(6))'(6'h14), type_ : (Bool)'(False), addr : (x_4).addr, value :
        unpack(0)}});
        let x_13 <- makeEnq_parentChildren002(x_12);
        let x_14 <- setULImm_002(x_4);
        let x_15 <- victims__002__setVictimRq(x_1);
    endrule

    rule rule_exec_002_21;
        let x_0 <- victims__002__getFirstVictim();
        Bit#(64) x_1 = ((x_0).victim_addr);
        Struct10 x_2 = ((x_0).victim_info);
        Vector#(4, Bit#(64)) x_3 = ((x_0).victim_value);
        Struct1 x_4 = (Struct1 {id : unpack(0), type_ : (Bool)'(False), addr
        : x_1, value : unpack(0)});
        Struct14 x_5 = (Struct14 {m_is_ul : (Bool)'(True), m_qidx :
        unpack(0), m_rsb : (Bool)'(False), m_dl_rss_from : unpack(0),
        m_dl_rss_recv : unpack(0)});
        Struct1 x_6 = (unpack(0));
        Struct1 x_7 = (unpack(0));
        Vector#(4, Bit#(64)) x_8 = (unpack(0));
        Bool x_9 = ((x_2).mesi_owned);
        Bit#(3) x_10 = ((x_2).mesi_status);
        Struct15 x_11 = (Struct15 {dir_st : (((x_2).mesi_dir_st) ==
        ((Bit#(3))'(3'h0)) ? ((Bit#(3))'(3'h1)) : ((x_2).mesi_dir_st)),
        dir_excl : ((((x_2).mesi_dir_sharers)[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        ((((((x_2).mesi_dir_sharers)[3:1])[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        (((((((x_2).mesi_dir_sharers)[3:1])[2:1])[0:0]) == ((Bit#(1))'(1'h1))
        ? ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        ((((((((x_2).mesi_dir_sharers)[3:1])[2:1])[1:1])[0:0]) ==
        ((Bit#(1))'(1'h1)) ? ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        (unpack(0))))))))))))), dir_sharers : (x_2).mesi_dir_sharers});
        when (! ((x_4).type_), noAction);
        when (((Bit#(3))'(3'h0)) < (x_10), noAction);
        Struct18 x_12 = (Struct18 {enq_type : ((((Bit#(4))'(4'h2))[3:2]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : (((((Bit#(4))'(4'h2))[3:2])
        == ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : ((Bit#(4))'(4'h2))[1:0], enq_msg : Struct1 {id :
        (Bit#(6))'(6'h15), type_ : (Bool)'(False), addr : (x_4).addr, value :
        x_3}});
        let x_13 <- makeEnq_parentChildren002(x_12);
        let x_14 <- setULImm_002(x_4);
        let x_15 <- victims__002__setVictimRq(x_1);
    endrule

    // No methods in this module
endmodule

interface Module137;

endinterface

module mkModule137#(function Action victims__003__setVictimRq(Bit#(64) _),
    function Action setULImm_003(Struct1 _),
    function ActionValue#(Struct13) victims__003__getFirstVictim(),
    function Action victims__003__setVictim(Struct44 _),
    function Action registerUL_003(Struct43 _),
    function Action makeEnq_parentChildren003(Struct18 _),
    function ActionValue#(Vector#(4, Bit#(64))) cache__003__valueRsLineRq(Struct42 _),
    function ActionValue#(Struct1) getMSHRRq_003(Bit#(2) _),
    function ActionValue#(Struct14) getMSHR_003(Bit#(2) _),
    function ActionValue#(Struct41) deq_fifoL2E_003(),
    function ActionValue#(Struct13) victims__003__getVictim(Bit#(1) _),
    function Action enq_fifoL2E_003(Struct41 _),
    function ActionValue#(Struct39) cache__003__infoRsValueRq(Bit#(64) _),
    function ActionValue#(Struct38) deq_fifoI2L_003(),
    function Action enq_fifoI2L_003(Struct38 _),
    function Action cache__003__infoRq(Bit#(64) _),
    function ActionValue#(Struct38) deq_fifoN2I_003(),
    function ActionValue#(Struct36) getCRqSlot_003(Struct35 _),
    function ActionValue#(Bool) victims__003__hasVictim(),
    function ActionValue#(Struct2) deq_fifoCRqInput_003(),
    function Action releaseMSHR_003(Bit#(2) _),
    function Action victims__003__releaseVictim(Bit#(64) _),
    function ActionValue#(Struct35) getWait_003(),
    function Action startRelease_003(Bit#(2) _),
    function ActionValue#(Bit#(2)) getULReady_003(Bit#(64) _),
    function Action enq_fifoN2I_003(Struct38 _),
    function ActionValue#(Struct37) victims__003__findVictim(Bit#(64) _),
    function ActionValue#(Struct36) getPRqSlot_003(Struct35 _),
    function ActionValue#(Struct2) deq_fifoPInput_003())
    (Module137);

    rule rule_in_prq_003;
        let x_0 <- deq_fifoPInput_003();
        Bit#(4) x_1 = ((x_0).in_msg_from);
        when ((x_1) == ({((Bit#(2))'(2'h2)),((Bit#(2))'(2'h3))}),
        noAction);
        Struct1 x_2 = ((x_0).in_msg);
        when (! ((x_2).type_), noAction);
        let x_3 <- getPRqSlot_003(Struct35 {r_id : unpack(0), r_msg : x_2,
        r_msg_from : (x_0).in_msg_from});
        when ((x_3).s_has_slot,
        noAction);
        if (! ((x_3).s_conflict)) begin
            let x_4 <- victims__003__findVictim((x_2).addr);
            Struct38 x_5 = (Struct38 {ir_is_rs_rel : (Bool)'(False), ir_msg :
            (x_0).in_msg, ir_msg_from : x_1, ir_mshr_id : (x_3).s_id,
            ir_by_victim : x_4});
            let x_6 <- enq_fifoN2I_003(x_5);
        end else begin

        end
    endrule

    rule rule_in_prs_003;
        let x_0 <- deq_fifoPInput_003();
        Bit#(4) x_1 = ((x_0).in_msg_from);
        when ((x_1) == ({((Bit#(2))'(2'h2)),((Bit#(2))'(2'h3))}),
        noAction);
        Struct1 x_2 = ((x_0).in_msg);
        when (((x_2).type_) && (! (((x_2).id) == ((Bit#(6))'(6'h16)))),
        noAction);
        let x_3 <- getULReady_003((x_2).addr);
        let x_4 <- startRelease_003(x_3);
        let x_5 <- victims__003__findVictim((x_2).addr);
        Struct38 x_6 = (Struct38 {ir_is_rs_rel : (Bool)'(False), ir_msg :
        (x_0).in_msg, ir_msg_from : x_1, ir_mshr_id : x_3, ir_by_victim :
        x_5});
        let x_7 <- enq_fifoN2I_003(x_6);
    endrule

    rule rule_in_retry_003;
        let x_0 <- getWait_003();
        Struct1 x_1 = ((x_0).r_msg);
        let x_2 <- victims__003__findVictim((x_1).addr);
        Struct38 x_3 = (Struct38 {ir_is_rs_rel : (Bool)'(False), ir_msg :
        x_1, ir_msg_from : (x_0).r_msg_from, ir_mshr_id : (x_0).r_id,
        ir_by_victim : x_2});
        let x_4 <- enq_fifoN2I_003(x_3);
    endrule

    rule rule_in_invrs_003;
        let x_0 <- deq_fifoPInput_003();
        Bit#(4) x_1 = ((x_0).in_msg_from);
        when ((x_1) == ({((Bit#(2))'(2'h2)),((Bit#(2))'(2'h3))}),
        noAction);
        Struct1 x_2 = ((x_0).in_msg);
        when (((x_2).type_) && (((x_2).id) == ((Bit#(6))'(6'h16))),
        noAction);
        let x_3 <- getULReady_003((x_2).addr);
        let x_4 <- victims__003__releaseVictim((x_2).addr);
        let x_5 <- releaseMSHR_003(x_3);
    endrule

    rule rule_in_crq_003;
        let x_0 <- deq_fifoCRqInput_003();
        Bit#(4) x_1 = ((x_0).in_msg_from);
        when (((x_1)[3:2]) == ((Bit#(2))'(2'h0)), noAction);
        Struct1 x_2 = ((x_0).in_msg);
        when (! ((x_2).type_), noAction);
        let x_3 <- victims__003__hasVictim();
        when (! (x_3), noAction);
        let x_4 <- getCRqSlot_003(Struct35 {r_id : unpack(0), r_msg : x_2,
        r_msg_from : x_1});
        when ((x_4).s_has_slot,
        noAction);
        if (! ((x_4).s_conflict)) begin
            let x_5 <- victims__003__findVictim((x_2).addr);
            Struct38 x_6 = (Struct38 {ir_is_rs_rel : (Bool)'(False), ir_msg :
            (x_0).in_msg, ir_msg_from : x_1, ir_mshr_id : (x_4).s_id,
            ir_by_victim : x_5});
            let x_7 <- enq_fifoN2I_003(x_6);
        end else begin

        end
    endrule

    rule rule_ir_cache_003;
        let x_0 <- deq_fifoN2I_003();
        when (! (((x_0).ir_by_victim).valid), noAction);
        Struct1 x_1 = ((x_0).ir_msg);
        let x_2 <- cache__003__infoRq((x_1).addr);
        let x_3 <- enq_fifoI2L_003(x_0);
    endrule

    rule rule_ir_victims_003;
        let x_0 <- deq_fifoN2I_003();
        when (((x_0).ir_by_victim).valid, noAction);
        let x_1 <- enq_fifoI2L_003(x_0);
    endrule

    rule rule_lr_cache_003;
        let x_0 <- deq_fifoI2L_003();
        when (! (((x_0).ir_by_victim).valid), noAction);
        let x_1 <- cache__003__infoRsValueRq(((x_0).ir_msg).addr);
        Struct41 x_2 = (Struct41 {lr_ir_pp : x_0, lr_ir : x_1, lr_value :
        unpack(0)});
        let x_3 <- enq_fifoL2E_003(x_2);
    endrule

    rule rule_lr_victims_003;
        let x_0 <- deq_fifoI2L_003();
        when (((x_0).ir_by_victim).valid, noAction);
        Bit#(1) x_1 = (((x_0).ir_by_victim).data);
        let x_2 <- victims__003__getVictim(x_1);
        Struct39 x_3 = (Struct39 {info_index : unpack(0), info_hit :
        unpack(0), info_way : unpack(0), edir_hit : unpack(0), edir_way :
        unpack(0), edir_slot : unpack(0), info : (x_2).victim_info,
        may_victim : unpack(0), reps : unpack(0)});
        Struct41 x_4 = (Struct41 {lr_ir_pp : x_0, lr_ir : x_3, lr_value :
        (x_2).victim_value});
        let x_5 <- enq_fifoL2E_003(x_4);
    endrule

    rule rule_exec_003_00;
        let x_0 <- deq_fifoL2E_003();
        Struct38 x_1 = ((x_0).lr_ir_pp);
        Bit#(4) x_2 = ((x_1).ir_msg_from);
        Struct1 x_3 = ((x_1).ir_msg);
        Bit#(2) x_4 = ((x_1).ir_mshr_id);
        Bool x_5 = ((x_1).ir_is_rs_rel);
        when (! (x_5), noAction);
        Struct39 x_6 = ((x_0).lr_ir);
        Struct10 x_7 = ((x_6).info);
        Struct37 x_8 = ((x_1).ir_by_victim);
        Vector#(4, Bit#(64)) x_9 = ((x_0).lr_value);
        let x_10 <- getMSHR_003(x_4);
        let x_11 <- getMSHRRq_003(x_4);
        Struct1 x_12 = (unpack(0));
        Vector#(4, Bit#(64)) x_13 = (unpack(0));
        Bool x_14 = ((x_7).mesi_owned);
        Bit#(3) x_15 = ((x_7).mesi_status);
        Struct15 x_16 = (Struct15 {dir_st : (((x_7).mesi_dir_st) ==
        ((Bit#(3))'(3'h0)) ? ((Bit#(3))'(3'h1)) : ((x_7).mesi_dir_st)),
        dir_excl : ((((x_7).mesi_dir_sharers)[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        ((((((x_7).mesi_dir_sharers)[3:1])[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        (((((((x_7).mesi_dir_sharers)[3:1])[2:1])[0:0]) == ((Bit#(1))'(1'h1))
        ? ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        ((((((((x_7).mesi_dir_sharers)[3:1])[2:1])[1:1])[0:0]) ==
        ((Bit#(1))'(1'h1)) ? ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        (unpack(0))))))))))))), dir_sharers : (x_7).mesi_dir_sharers});
        when ((x_2) == ((Bit#(4))'(4'h0)), noAction);
        when (((x_3).id) == ((Bit#(6))'(6'h0)), noAction);
        when (! ((x_3).type_), noAction);
        when (! ((x_15) < ((Bit#(3))'(3'h2))), noAction);
        Struct1 x_17 = (x_3);
        Struct42 x_18 = (Struct42 {addr : (x_3).addr, info_write :
        (Bool)'(False), info_hit : (x_6).info_hit, info_way : (x_6).info_way,
        edir_hit : (x_6).edir_hit, edir_way : (x_6).edir_way, edir_slot :
        (x_6).edir_slot, info : (x_6).info, value_write : (Bool)'(False),
        value : unpack(0), may_victim : (x_6).may_victim, reps :
        (x_6).reps});
        let x_20 = ?;
        if ((x_8).valid) begin
            x_20 = x_9;
        end else begin
            let x_19 <- cache__003__valueRsLineRq(unpack(0));
            x_20 = x_19;
        end
        Struct18 x_21 = (Struct18 {enq_type : ((((Bit#(4))'(4'h8))[3:2]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : (((((Bit#(4))'(4'h8))[3:2])
        == ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : ((Bit#(4))'(4'h8))[1:0], enq_msg : Struct1 {id :
        (Bit#(6))'(6'h1), type_ : (Bool)'(True), addr : (x_17).addr, value :
        x_20}});
        let x_22 <- makeEnq_parentChildren003(x_21);
        let x_23 <- releaseMSHR_003(x_4);
    endrule

    rule rule_exec_003_01;
        let x_0 <- deq_fifoL2E_003();
        Struct38 x_1 = ((x_0).lr_ir_pp);
        Bit#(4) x_2 = ((x_1).ir_msg_from);
        Struct1 x_3 = ((x_1).ir_msg);
        Bit#(2) x_4 = ((x_1).ir_mshr_id);
        Bool x_5 = ((x_1).ir_is_rs_rel);
        when (! (x_5), noAction);
        Struct39 x_6 = ((x_0).lr_ir);
        Struct10 x_7 = ((x_6).info);
        Struct37 x_8 = ((x_1).ir_by_victim);
        Vector#(4, Bit#(64)) x_9 = ((x_0).lr_value);
        let x_10 <- getMSHR_003(x_4);
        let x_11 <- getMSHRRq_003(x_4);
        Struct1 x_12 = (unpack(0));
        Vector#(4, Bit#(64)) x_13 = (unpack(0));
        Bool x_14 = ((x_7).mesi_owned);
        Bit#(3) x_15 = ((x_7).mesi_status);
        Struct15 x_16 = (Struct15 {dir_st : (((x_7).mesi_dir_st) ==
        ((Bit#(3))'(3'h0)) ? ((Bit#(3))'(3'h1)) : ((x_7).mesi_dir_st)),
        dir_excl : ((((x_7).mesi_dir_sharers)[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        ((((((x_7).mesi_dir_sharers)[3:1])[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        (((((((x_7).mesi_dir_sharers)[3:1])[2:1])[0:0]) == ((Bit#(1))'(1'h1))
        ? ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        ((((((((x_7).mesi_dir_sharers)[3:1])[2:1])[1:1])[0:0]) ==
        ((Bit#(1))'(1'h1)) ? ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        (unpack(0))))))))))))), dir_sharers : (x_7).mesi_dir_sharers});
        when ((x_2) == ((Bit#(4))'(4'h0)), noAction);
        when (((x_3).id) == ((Bit#(6))'(6'h0)), noAction);
        when (! ((x_3).type_), noAction);
        when (! (((Bit#(3))'(3'h1)) < (x_15)), noAction);
        Struct1 x_17 = (x_3);
        Struct42 x_18 = (Struct42 {addr : (x_3).addr, info_write :
        (Bool)'(False), info_hit : (x_6).info_hit, info_way : (x_6).info_way,
        edir_hit : (x_6).edir_hit, edir_way : (x_6).edir_way, edir_slot :
        (x_6).edir_slot, info : (x_6).info, value_write : (Bool)'(False),
        value : unpack(0), may_victim : (x_6).may_victim, reps :
        (x_6).reps});
        let x_20 = ?;
        if ((x_8).valid) begin
            x_20 = x_9;
        end else begin
            let x_19 <- cache__003__valueRsLineRq(unpack(0));
            x_20 = x_19;
        end
        let x_21 <- registerUL_003(Struct43 {r_id : x_4, r_ul_rsb :
        (Bool)'(True), r_ul_rsbTo : ((Bit#(4))'(4'h8))[1:0]});
        Struct18 x_22 = (Struct18 {enq_type : ((((Bit#(4))'(4'h3))[3:2]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : (((((Bit#(4))'(4'h3))[3:2])
        == ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : ((Bit#(4))'(4'h3))[1:0], enq_msg : Struct1 {id :
        (Bit#(6))'(6'h2), type_ : (Bool)'(False), addr : (x_17).addr, value :
        unpack(0)}});
        let x_23 <- makeEnq_parentChildren003(x_22);
    endrule

    rule rule_exec_003_020;
        let x_0 <- deq_fifoL2E_003();
        Struct38 x_1 = ((x_0).lr_ir_pp);
        Bit#(4) x_2 = ((x_1).ir_msg_from);
        Struct1 x_3 = ((x_1).ir_msg);
        Bit#(2) x_4 = ((x_1).ir_mshr_id);
        Bool x_5 = ((x_1).ir_is_rs_rel);
        when (! (x_5), noAction);
        Struct39 x_6 = ((x_0).lr_ir);
        Struct10 x_7 = ((x_6).info);
        Struct37 x_8 = ((x_1).ir_by_victim);
        Vector#(4, Bit#(64)) x_9 = ((x_0).lr_value);
        let x_10 <- getMSHR_003(x_4);
        let x_11 <- getMSHRRq_003(x_4);
        Struct1 x_12 = (unpack(0));
        Vector#(4, Bit#(64)) x_13 = (unpack(0));
        Bool x_14 = ((x_7).mesi_owned);
        Bit#(3) x_15 = ((x_7).mesi_status);
        Struct15 x_16 = (Struct15 {dir_st : (((x_7).mesi_dir_st) ==
        ((Bit#(3))'(3'h0)) ? ((Bit#(3))'(3'h1)) : ((x_7).mesi_dir_st)),
        dir_excl : ((((x_7).mesi_dir_sharers)[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        ((((((x_7).mesi_dir_sharers)[3:1])[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        (((((((x_7).mesi_dir_sharers)[3:1])[2:1])[0:0]) == ((Bit#(1))'(1'h1))
        ? ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        ((((((((x_7).mesi_dir_sharers)[3:1])[2:1])[1:1])[0:0]) ==
        ((Bit#(1))'(1'h1)) ? ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        (unpack(0))))))))))))), dir_sharers : (x_7).mesi_dir_sharers});
        when ((x_2) == ({((Bit#(2))'(2'h2)),((Bit#(2))'(2'h3))}),
        noAction);
        when (((x_3).id) == ((Bit#(6))'(6'h3)), noAction);
        when ((x_10).m_rsb, noAction);
        when (((x_11).type_) == ((Bool)'(False)), noAction);
        when (((x_11).id) == ((Bit#(6))'(6'h0)), noAction);
        when ((x_10).m_rsb, noAction);
        when ((x_3).type_, noAction);
        when ((Bool)'(True), noAction);
        Struct1 x_17 = (x_3);
        Struct1 x_18 = (x_11);
        Bit#(4) x_19 = ({((Bit#(2))'(2'h2)),(((x_10).m_qidx)[1:0])});
        Struct42 x_20 = (Struct42 {addr : (x_3).addr, info_write :
        (Bool)'(False), info_hit : (x_6).info_hit, info_way : (x_6).info_way,
        edir_hit : (x_6).edir_hit, edir_way : (x_6).edir_way, edir_slot :
        (x_6).edir_slot, info : (x_6).info, value_write : (Bool)'(False),
        value : unpack(0), may_victim : (x_6).may_victim, reps :
        (x_6).reps});
        Struct42 x_21 = (Struct42 {addr : (x_20).addr, info_write :
        (Bool)'(True), info_hit : (x_20).info_hit, info_way :
        (x_20).info_way, edir_hit : (x_20).edir_hit, edir_way :
        (x_20).edir_way, edir_slot : (x_20).edir_slot, info : Struct10
        {mesi_owned : ((x_20).info).mesi_owned, mesi_status :
        (Bit#(3))'(3'h2), mesi_dir_st : ((x_20).info).mesi_dir_st,
        mesi_dir_sharers : ((x_20).info).mesi_dir_sharers}, value_write :
        (x_20).value_write, value : (x_20).value, may_victim :
        (x_20).may_victim, reps : (x_20).reps});
        Struct42 x_22 = (Struct42 {addr : (x_21).addr, info_write :
        (x_21).info_write, info_hit : (x_21).info_hit, info_way :
        (x_21).info_way, edir_hit : (x_21).edir_hit, edir_way :
        (x_21).edir_way, edir_slot : (x_21).edir_slot, info : (x_21).info,
        value_write : (Bool)'(True), value : (x_17).value, may_victim :
        (x_21).may_victim, reps :
        (x_21).reps});
        let x_25 = ?;
        if ((x_8).valid) begin
            let x_23 <- victims__003__setVictim(Struct44 {victim_idx :
            (x_8).data, victim_info : (x_22).info, victim_value :
            ((x_22).value_write ? ((x_22).value) : (x_9))});
            x_25 = x_9;
        end else begin
            let x_24 <- cache__003__valueRsLineRq(x_22);
            x_25 = x_24;
        end
        let x_26 <- releaseMSHR_003(x_4);
        Struct18 x_27 = (Struct18 {enq_type : (((x_19)[3:2]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : ((((x_19)[3:2]) ==
        ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : (x_19)[1:0], enq_msg : Struct1 {id : (Bit#(6))'(6'h1),
        type_ : (Bool)'(True), addr : (x_17).addr, value :
        (x_17).value}});
        let x_28 <- makeEnq_parentChildren003(x_27);
    endrule

    rule rule_exec_003_021;
        let x_0 <- deq_fifoL2E_003();
        Struct38 x_1 = ((x_0).lr_ir_pp);
        Bit#(4) x_2 = ((x_1).ir_msg_from);
        Struct1 x_3 = ((x_1).ir_msg);
        Bit#(2) x_4 = ((x_1).ir_mshr_id);
        Bool x_5 = ((x_1).ir_is_rs_rel);
        when (! (x_5), noAction);
        Struct39 x_6 = ((x_0).lr_ir);
        Struct10 x_7 = ((x_6).info);
        Struct37 x_8 = ((x_1).ir_by_victim);
        Vector#(4, Bit#(64)) x_9 = ((x_0).lr_value);
        let x_10 <- getMSHR_003(x_4);
        let x_11 <- getMSHRRq_003(x_4);
        Struct1 x_12 = (unpack(0));
        Vector#(4, Bit#(64)) x_13 = (unpack(0));
        Bool x_14 = ((x_7).mesi_owned);
        Bit#(3) x_15 = ((x_7).mesi_status);
        Struct15 x_16 = (Struct15 {dir_st : (((x_7).mesi_dir_st) ==
        ((Bit#(3))'(3'h0)) ? ((Bit#(3))'(3'h1)) : ((x_7).mesi_dir_st)),
        dir_excl : ((((x_7).mesi_dir_sharers)[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        ((((((x_7).mesi_dir_sharers)[3:1])[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        (((((((x_7).mesi_dir_sharers)[3:1])[2:1])[0:0]) == ((Bit#(1))'(1'h1))
        ? ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        ((((((((x_7).mesi_dir_sharers)[3:1])[2:1])[1:1])[0:0]) ==
        ((Bit#(1))'(1'h1)) ? ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        (unpack(0))))))))))))), dir_sharers : (x_7).mesi_dir_sharers});
        when ((x_2) == ({((Bit#(2))'(2'h2)),((Bit#(2))'(2'h3))}),
        noAction);
        when (((x_3).id) == ((Bit#(6))'(6'h4)), noAction);
        when ((x_10).m_rsb, noAction);
        when (((x_11).type_) == ((Bool)'(False)), noAction);
        when (((x_11).id) == ((Bit#(6))'(6'h0)), noAction);
        when ((x_10).m_rsb, noAction);
        when ((x_3).type_, noAction);
        when ((Bool)'(True), noAction);
        Struct1 x_17 = (x_3);
        Struct1 x_18 = (x_11);
        Bit#(4) x_19 = ({((Bit#(2))'(2'h2)),(((x_10).m_qidx)[1:0])});
        Struct42 x_20 = (Struct42 {addr : (x_3).addr, info_write :
        (Bool)'(False), info_hit : (x_6).info_hit, info_way : (x_6).info_way,
        edir_hit : (x_6).edir_hit, edir_way : (x_6).edir_way, edir_slot :
        (x_6).edir_slot, info : (x_6).info, value_write : (Bool)'(False),
        value : unpack(0), may_victim : (x_6).may_victim, reps :
        (x_6).reps});
        Struct42 x_21 = (Struct42 {addr : (x_20).addr, info_write :
        (Bool)'(True), info_hit : (x_20).info_hit, info_way :
        (x_20).info_way, edir_hit : (x_20).edir_hit, edir_way :
        (x_20).edir_way, edir_slot : (x_20).edir_slot, info : Struct10
        {mesi_owned : ((x_20).info).mesi_owned, mesi_status :
        (Bit#(3))'(3'h3), mesi_dir_st : ((x_20).info).mesi_dir_st,
        mesi_dir_sharers : ((x_20).info).mesi_dir_sharers}, value_write :
        (x_20).value_write, value : (x_20).value, may_victim :
        (x_20).may_victim, reps : (x_20).reps});
        Struct42 x_22 = (Struct42 {addr : (x_21).addr, info_write :
        (x_21).info_write, info_hit : (x_21).info_hit, info_way :
        (x_21).info_way, edir_hit : (x_21).edir_hit, edir_way :
        (x_21).edir_way, edir_slot : (x_21).edir_slot, info : (x_21).info,
        value_write : (Bool)'(True), value : (x_17).value, may_victim :
        (x_21).may_victim, reps :
        (x_21).reps});
        let x_25 = ?;
        if ((x_8).valid) begin
            let x_23 <- victims__003__setVictim(Struct44 {victim_idx :
            (x_8).data, victim_info : (x_22).info, victim_value :
            ((x_22).value_write ? ((x_22).value) : (x_9))});
            x_25 = x_9;
        end else begin
            let x_24 <- cache__003__valueRsLineRq(x_22);
            x_25 = x_24;
        end
        let x_26 <- releaseMSHR_003(x_4);
        Struct18 x_27 = (Struct18 {enq_type : (((x_19)[3:2]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : ((((x_19)[3:2]) ==
        ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : (x_19)[1:0], enq_msg : Struct1 {id : (Bit#(6))'(6'h1),
        type_ : (Bool)'(True), addr : (x_17).addr, value :
        (x_17).value}});
        let x_28 <- makeEnq_parentChildren003(x_27);
    endrule

    rule rule_exec_003_03;
        let x_0 <- deq_fifoL2E_003();
        Struct38 x_1 = ((x_0).lr_ir_pp);
        Bit#(4) x_2 = ((x_1).ir_msg_from);
        Struct1 x_3 = ((x_1).ir_msg);
        Bit#(2) x_4 = ((x_1).ir_mshr_id);
        Bool x_5 = ((x_1).ir_is_rs_rel);
        when (! (x_5), noAction);
        Struct39 x_6 = ((x_0).lr_ir);
        Struct10 x_7 = ((x_6).info);
        Struct37 x_8 = ((x_1).ir_by_victim);
        Vector#(4, Bit#(64)) x_9 = ((x_0).lr_value);
        let x_10 <- getMSHR_003(x_4);
        let x_11 <- getMSHRRq_003(x_4);
        Struct1 x_12 = (unpack(0));
        Vector#(4, Bit#(64)) x_13 = (unpack(0));
        Bool x_14 = ((x_7).mesi_owned);
        Bit#(3) x_15 = ((x_7).mesi_status);
        Struct15 x_16 = (Struct15 {dir_st : (((x_7).mesi_dir_st) ==
        ((Bit#(3))'(3'h0)) ? ((Bit#(3))'(3'h1)) : ((x_7).mesi_dir_st)),
        dir_excl : ((((x_7).mesi_dir_sharers)[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        ((((((x_7).mesi_dir_sharers)[3:1])[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        (((((((x_7).mesi_dir_sharers)[3:1])[2:1])[0:0]) == ((Bit#(1))'(1'h1))
        ? ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        ((((((((x_7).mesi_dir_sharers)[3:1])[2:1])[1:1])[0:0]) ==
        ((Bit#(1))'(1'h1)) ? ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        (unpack(0))))))))))))), dir_sharers : (x_7).mesi_dir_sharers});
        when ((x_2) == ((Bit#(4))'(4'hb)), noAction);
        when (((x_3).id) == ((Bit#(6))'(6'h5)), noAction);
        when (! ((x_3).type_), noAction);
        when (! ((x_15) < ((Bit#(3))'(3'h2))), noAction);
        Struct1 x_17 = (x_3);
        Struct42 x_18 = (Struct42 {addr : (x_3).addr, info_write :
        (Bool)'(False), info_hit : (x_6).info_hit, info_way : (x_6).info_way,
        edir_hit : (x_6).edir_hit, edir_way : (x_6).edir_way, edir_slot :
        (x_6).edir_slot, info : (x_6).info, value_write : (Bool)'(False),
        value : unpack(0), may_victim : (x_6).may_victim, reps :
        (x_6).reps});
        Struct42 x_19 = (Struct42 {addr : (x_18).addr, info_write :
        (Bool)'(True), info_hit : (x_18).info_hit, info_way :
        (x_18).info_way, edir_hit : (x_18).edir_hit, edir_way :
        (x_18).edir_way, edir_slot : (x_18).edir_slot, info : Struct10
        {mesi_owned : ((x_18).info).mesi_owned, mesi_status :
        (Bit#(3))'(3'h2), mesi_dir_st : ((x_18).info).mesi_dir_st,
        mesi_dir_sharers : ((x_18).info).mesi_dir_sharers}, value_write :
        (x_18).value_write, value : (x_18).value, may_victim :
        (x_18).may_victim, reps : (x_18).reps});
        Struct42 x_20 = (Struct42 {addr : (x_19).addr, info_write :
        (Bool)'(True), info_hit : (x_19).info_hit, info_way :
        (x_19).info_way, edir_hit : (x_19).edir_hit, edir_way :
        (x_19).edir_way, edir_slot : (x_19).edir_slot, info : Struct10
        {mesi_owned : (Bool)'(False), mesi_status :
        ((x_19).info).mesi_status, mesi_dir_st : ((x_19).info).mesi_dir_st,
        mesi_dir_sharers : ((x_19).info).mesi_dir_sharers}, value_write :
        (x_19).value_write, value : (x_19).value, may_victim :
        (x_19).may_victim, reps :
        (x_19).reps});
        let x_23 = ?;
        if ((x_8).valid) begin
            let x_21 <- victims__003__setVictim(Struct44 {victim_idx :
            (x_8).data, victim_info : (x_20).info, victim_value :
            ((x_20).value_write ? ((x_20).value) : (x_9))});
            x_23 = x_9;
        end else begin
            let x_22 <- cache__003__valueRsLineRq(x_20);
            x_23 = x_22;
        end
        Struct18 x_24 = (Struct18 {enq_type : ((((Bit#(4))'(4'h7))[3:2]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : (((((Bit#(4))'(4'h7))[3:2])
        == ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : ((Bit#(4))'(4'h7))[1:0], enq_msg : Struct1 {id :
        (Bit#(6))'(6'h6), type_ : (Bool)'(True), addr : (x_17).addr, value :
        x_23}});
        let x_25 <- makeEnq_parentChildren003(x_24);
        let x_26 <- releaseMSHR_003(x_4);
    endrule

    rule rule_exec_003_100;
        let x_0 <- deq_fifoL2E_003();
        Struct38 x_1 = ((x_0).lr_ir_pp);
        Bit#(4) x_2 = ((x_1).ir_msg_from);
        Struct1 x_3 = ((x_1).ir_msg);
        Bit#(2) x_4 = ((x_1).ir_mshr_id);
        Bool x_5 = ((x_1).ir_is_rs_rel);
        when (! (x_5), noAction);
        Struct39 x_6 = ((x_0).lr_ir);
        Struct10 x_7 = ((x_6).info);
        Struct37 x_8 = ((x_1).ir_by_victim);
        Vector#(4, Bit#(64)) x_9 = ((x_0).lr_value);
        let x_10 <- getMSHR_003(x_4);
        let x_11 <- getMSHRRq_003(x_4);
        Struct1 x_12 = (unpack(0));
        Vector#(4, Bit#(64)) x_13 = (unpack(0));
        Bool x_14 = ((x_7).mesi_owned);
        Bit#(3) x_15 = ((x_7).mesi_status);
        Struct15 x_16 = (Struct15 {dir_st : (((x_7).mesi_dir_st) ==
        ((Bit#(3))'(3'h0)) ? ((Bit#(3))'(3'h1)) : ((x_7).mesi_dir_st)),
        dir_excl : ((((x_7).mesi_dir_sharers)[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        ((((((x_7).mesi_dir_sharers)[3:1])[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        (((((((x_7).mesi_dir_sharers)[3:1])[2:1])[0:0]) == ((Bit#(1))'(1'h1))
        ? ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        ((((((((x_7).mesi_dir_sharers)[3:1])[2:1])[1:1])[0:0]) ==
        ((Bit#(1))'(1'h1)) ? ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        (unpack(0))))))))))))), dir_sharers : (x_7).mesi_dir_sharers});
        when ((x_2) == ((Bit#(4))'(4'h0)), noAction);
        when (((x_3).id) == ((Bit#(6))'(6'h8)), noAction);
        when (! ((x_3).type_), noAction);
        when ((x_15) == ((Bit#(3))'(3'h3)), noAction);
        Struct1 x_17 = (x_3);
        Struct42 x_18 = (Struct42 {addr : (x_3).addr, info_write :
        (Bool)'(False), info_hit : (x_6).info_hit, info_way : (x_6).info_way,
        edir_hit : (x_6).edir_hit, edir_way : (x_6).edir_way, edir_slot :
        (x_6).edir_slot, info : (x_6).info, value_write : (Bool)'(False),
        value : unpack(0), may_victim : (x_6).may_victim, reps :
        (x_6).reps});
        Struct42 x_19 = (Struct42 {addr : (x_18).addr, info_write :
        (x_18).info_write, info_hit : (x_18).info_hit, info_way :
        (x_18).info_way, edir_hit : (x_18).edir_hit, edir_way :
        (x_18).edir_way, edir_slot : (x_18).edir_slot, info : (x_18).info,
        value_write : (Bool)'(True), value : (x_17).value, may_victim :
        (x_18).may_victim, reps : (x_18).reps});
        Struct42 x_20 = (Struct42 {addr : (x_19).addr, info_write :
        (Bool)'(True), info_hit : (x_19).info_hit, info_way :
        (x_19).info_way, edir_hit : (x_19).edir_hit, edir_way :
        (x_19).edir_way, edir_slot : (x_19).edir_slot, info : Struct10
        {mesi_owned : ((x_19).info).mesi_owned, mesi_status :
        (Bit#(3))'(3'h4), mesi_dir_st : ((x_19).info).mesi_dir_st,
        mesi_dir_sharers : ((x_19).info).mesi_dir_sharers}, value_write :
        (x_19).value_write, value : (x_19).value, may_victim :
        (x_19).may_victim, reps : (x_19).reps});
        Struct42 x_21 = (Struct42 {addr : (x_20).addr, info_write :
        (Bool)'(True), info_hit : (x_20).info_hit, info_way :
        (x_20).info_way, edir_hit : (x_20).edir_hit, edir_way :
        (x_20).edir_way, edir_slot : (x_20).edir_slot, info : Struct10
        {mesi_owned : (Bool)'(True), mesi_status : ((x_20).info).mesi_status,
        mesi_dir_st : ((x_20).info).mesi_dir_st, mesi_dir_sharers :
        ((x_20).info).mesi_dir_sharers}, value_write : (x_20).value_write,
        value : (x_20).value, may_victim : (x_20).may_victim, reps :
        (x_20).reps});
        let x_24 = ?;
        if ((x_8).valid) begin
            let x_22 <- victims__003__setVictim(Struct44 {victim_idx :
            (x_8).data, victim_info : (x_21).info, victim_value :
            ((x_21).value_write ? ((x_21).value) : (x_9))});
            x_24 = x_9;
        end else begin
            let x_23 <- cache__003__valueRsLineRq(x_21);
            x_24 = x_23;
        end
        Struct18 x_25 = (Struct18 {enq_type : ((((Bit#(4))'(4'h8))[3:2]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : (((((Bit#(4))'(4'h8))[3:2])
        == ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : ((Bit#(4))'(4'h8))[1:0], enq_msg : Struct1 {id :
        (Bit#(6))'(6'h9), type_ : (Bool)'(True), addr : (x_17).addr, value :
        unpack(0)}});
        let x_26 <- makeEnq_parentChildren003(x_25);
        let x_27 <- releaseMSHR_003(x_4);
    endrule

    rule rule_exec_003_101;
        let x_0 <- deq_fifoL2E_003();
        Struct38 x_1 = ((x_0).lr_ir_pp);
        Bit#(4) x_2 = ((x_1).ir_msg_from);
        Struct1 x_3 = ((x_1).ir_msg);
        Bit#(2) x_4 = ((x_1).ir_mshr_id);
        Bool x_5 = ((x_1).ir_is_rs_rel);
        when (! (x_5), noAction);
        Struct39 x_6 = ((x_0).lr_ir);
        Struct10 x_7 = ((x_6).info);
        Struct37 x_8 = ((x_1).ir_by_victim);
        Vector#(4, Bit#(64)) x_9 = ((x_0).lr_value);
        let x_10 <- getMSHR_003(x_4);
        let x_11 <- getMSHRRq_003(x_4);
        Struct1 x_12 = (unpack(0));
        Vector#(4, Bit#(64)) x_13 = (unpack(0));
        Bool x_14 = ((x_7).mesi_owned);
        Bit#(3) x_15 = ((x_7).mesi_status);
        Struct15 x_16 = (Struct15 {dir_st : (((x_7).mesi_dir_st) ==
        ((Bit#(3))'(3'h0)) ? ((Bit#(3))'(3'h1)) : ((x_7).mesi_dir_st)),
        dir_excl : ((((x_7).mesi_dir_sharers)[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        ((((((x_7).mesi_dir_sharers)[3:1])[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        (((((((x_7).mesi_dir_sharers)[3:1])[2:1])[0:0]) == ((Bit#(1))'(1'h1))
        ? ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        ((((((((x_7).mesi_dir_sharers)[3:1])[2:1])[1:1])[0:0]) ==
        ((Bit#(1))'(1'h1)) ? ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        (unpack(0))))))))))))), dir_sharers : (x_7).mesi_dir_sharers});
        when ((x_2) == ((Bit#(4))'(4'h0)), noAction);
        when (((x_3).id) == ((Bit#(6))'(6'h8)), noAction);
        when (! ((x_3).type_), noAction);
        when (((x_14) == ((Bool)'(True))) && ((x_15) == ((Bit#(3))'(3'h4))),
        noAction);
        Struct1 x_17 = (x_3);
        Struct42 x_18 = (Struct42 {addr : (x_3).addr, info_write :
        (Bool)'(False), info_hit : (x_6).info_hit, info_way : (x_6).info_way,
        edir_hit : (x_6).edir_hit, edir_way : (x_6).edir_way, edir_slot :
        (x_6).edir_slot, info : (x_6).info, value_write : (Bool)'(False),
        value : unpack(0), may_victim : (x_6).may_victim, reps :
        (x_6).reps});
        Struct42 x_19 = (Struct42 {addr : (x_18).addr, info_write :
        (x_18).info_write, info_hit : (x_18).info_hit, info_way :
        (x_18).info_way, edir_hit : (x_18).edir_hit, edir_way :
        (x_18).edir_way, edir_slot : (x_18).edir_slot, info : (x_18).info,
        value_write : (Bool)'(True), value : (x_17).value, may_victim :
        (x_18).may_victim, reps :
        (x_18).reps});
        let x_22 = ?;
        if ((x_8).valid) begin
            let x_20 <- victims__003__setVictim(Struct44 {victim_idx :
            (x_8).data, victim_info : (x_19).info, victim_value :
            ((x_19).value_write ? ((x_19).value) : (x_9))});
            x_22 = x_9;
        end else begin
            let x_21 <- cache__003__valueRsLineRq(x_19);
            x_22 = x_21;
        end
        Struct18 x_23 = (Struct18 {enq_type : ((((Bit#(4))'(4'h8))[3:2]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : (((((Bit#(4))'(4'h8))[3:2])
        == ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : ((Bit#(4))'(4'h8))[1:0], enq_msg : Struct1 {id :
        (Bit#(6))'(6'h9), type_ : (Bool)'(True), addr : (x_17).addr, value :
        unpack(0)}});
        let x_24 <- makeEnq_parentChildren003(x_23);
        let x_25 <- releaseMSHR_003(x_4);
    endrule

    rule rule_exec_003_11;
        let x_0 <- deq_fifoL2E_003();
        Struct38 x_1 = ((x_0).lr_ir_pp);
        Bit#(4) x_2 = ((x_1).ir_msg_from);
        Struct1 x_3 = ((x_1).ir_msg);
        Bit#(2) x_4 = ((x_1).ir_mshr_id);
        Bool x_5 = ((x_1).ir_is_rs_rel);
        when (! (x_5), noAction);
        Struct39 x_6 = ((x_0).lr_ir);
        Struct10 x_7 = ((x_6).info);
        Struct37 x_8 = ((x_1).ir_by_victim);
        Vector#(4, Bit#(64)) x_9 = ((x_0).lr_value);
        let x_10 <- getMSHR_003(x_4);
        let x_11 <- getMSHRRq_003(x_4);
        Struct1 x_12 = (unpack(0));
        Vector#(4, Bit#(64)) x_13 = (unpack(0));
        Bool x_14 = ((x_7).mesi_owned);
        Bit#(3) x_15 = ((x_7).mesi_status);
        Struct15 x_16 = (Struct15 {dir_st : (((x_7).mesi_dir_st) ==
        ((Bit#(3))'(3'h0)) ? ((Bit#(3))'(3'h1)) : ((x_7).mesi_dir_st)),
        dir_excl : ((((x_7).mesi_dir_sharers)[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        ((((((x_7).mesi_dir_sharers)[3:1])[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        (((((((x_7).mesi_dir_sharers)[3:1])[2:1])[0:0]) == ((Bit#(1))'(1'h1))
        ? ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        ((((((((x_7).mesi_dir_sharers)[3:1])[2:1])[1:1])[0:0]) ==
        ((Bit#(1))'(1'h1)) ? ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        (unpack(0))))))))))))), dir_sharers : (x_7).mesi_dir_sharers});
        when ((x_2) == ((Bit#(4))'(4'h0)), noAction);
        when (((x_3).id) == ((Bit#(6))'(6'h8)), noAction);
        when (! ((x_3).type_), noAction);
        when (! (((Bit#(3))'(3'h2)) < (x_15)), noAction);
        Struct1 x_17 = (x_3);
        Struct42 x_18 = (Struct42 {addr : (x_3).addr, info_write :
        (Bool)'(False), info_hit : (x_6).info_hit, info_way : (x_6).info_way,
        edir_hit : (x_6).edir_hit, edir_way : (x_6).edir_way, edir_slot :
        (x_6).edir_slot, info : (x_6).info, value_write : (Bool)'(False),
        value : unpack(0), may_victim : (x_6).may_victim, reps :
        (x_6).reps});
        let x_20 = ?;
        if ((x_8).valid) begin
            x_20 = x_9;
        end else begin
            let x_19 <- cache__003__valueRsLineRq(unpack(0));
            x_20 = x_19;
        end
        let x_21 <- registerUL_003(Struct43 {r_id : x_4, r_ul_rsb :
        (Bool)'(True), r_ul_rsbTo : ((Bit#(4))'(4'h8))[1:0]});
        Struct18 x_22 = (Struct18 {enq_type : ((((Bit#(4))'(4'h3))[3:2]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : (((((Bit#(4))'(4'h3))[3:2])
        == ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : ((Bit#(4))'(4'h3))[1:0], enq_msg : Struct1 {id :
        (Bit#(6))'(6'ha), type_ : (Bool)'(False), addr : (x_17).addr, value :
        unpack(0)}});
        let x_23 <- makeEnq_parentChildren003(x_22);
    endrule

    rule rule_exec_003_12;
        let x_0 <- deq_fifoL2E_003();
        Struct38 x_1 = ((x_0).lr_ir_pp);
        Bit#(4) x_2 = ((x_1).ir_msg_from);
        Struct1 x_3 = ((x_1).ir_msg);
        Bit#(2) x_4 = ((x_1).ir_mshr_id);
        Bool x_5 = ((x_1).ir_is_rs_rel);
        when (! (x_5), noAction);
        Struct39 x_6 = ((x_0).lr_ir);
        Struct10 x_7 = ((x_6).info);
        Struct37 x_8 = ((x_1).ir_by_victim);
        Vector#(4, Bit#(64)) x_9 = ((x_0).lr_value);
        let x_10 <- getMSHR_003(x_4);
        let x_11 <- getMSHRRq_003(x_4);
        Struct1 x_12 = (unpack(0));
        Vector#(4, Bit#(64)) x_13 = (unpack(0));
        Bool x_14 = ((x_7).mesi_owned);
        Bit#(3) x_15 = ((x_7).mesi_status);
        Struct15 x_16 = (Struct15 {dir_st : (((x_7).mesi_dir_st) ==
        ((Bit#(3))'(3'h0)) ? ((Bit#(3))'(3'h1)) : ((x_7).mesi_dir_st)),
        dir_excl : ((((x_7).mesi_dir_sharers)[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        ((((((x_7).mesi_dir_sharers)[3:1])[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        (((((((x_7).mesi_dir_sharers)[3:1])[2:1])[0:0]) == ((Bit#(1))'(1'h1))
        ? ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        ((((((((x_7).mesi_dir_sharers)[3:1])[2:1])[1:1])[0:0]) ==
        ((Bit#(1))'(1'h1)) ? ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        (unpack(0))))))))))))), dir_sharers : (x_7).mesi_dir_sharers});
        when ((x_2) == ({((Bit#(2))'(2'h2)),((Bit#(2))'(2'h3))}),
        noAction);
        when (((x_3).id) == ((Bit#(6))'(6'hb)), noAction);
        when ((x_10).m_rsb, noAction);
        when (((x_11).type_) == ((Bool)'(False)), noAction);
        when (((x_11).id) == ((Bit#(6))'(6'h8)), noAction);
        when ((x_10).m_rsb, noAction);
        when ((x_3).type_, noAction);
        when ((Bool)'(True), noAction);
        Struct1 x_17 = (x_3);
        Struct1 x_18 = (x_11);
        Bit#(4) x_19 = ({((Bit#(2))'(2'h2)),(((x_10).m_qidx)[1:0])});
        Struct42 x_20 = (Struct42 {addr : (x_3).addr, info_write :
        (Bool)'(False), info_hit : (x_6).info_hit, info_way : (x_6).info_way,
        edir_hit : (x_6).edir_hit, edir_way : (x_6).edir_way, edir_slot :
        (x_6).edir_slot, info : (x_6).info, value_write : (Bool)'(False),
        value : unpack(0), may_victim : (x_6).may_victim, reps :
        (x_6).reps});
        Struct42 x_21 = (Struct42 {addr : (x_20).addr, info_write :
        (x_20).info_write, info_hit : (x_20).info_hit, info_way :
        (x_20).info_way, edir_hit : (x_20).edir_hit, edir_way :
        (x_20).edir_way, edir_slot : (x_20).edir_slot, info : (x_20).info,
        value_write : (Bool)'(True), value : (x_18).value, may_victim :
        (x_20).may_victim, reps : (x_20).reps});
        Struct42 x_22 = (Struct42 {addr : (x_21).addr, info_write :
        (Bool)'(True), info_hit : (x_21).info_hit, info_way :
        (x_21).info_way, edir_hit : (x_21).edir_hit, edir_way :
        (x_21).edir_way, edir_slot : (x_21).edir_slot, info : Struct10
        {mesi_owned : (Bool)'(True), mesi_status : ((x_21).info).mesi_status,
        mesi_dir_st : ((x_21).info).mesi_dir_st, mesi_dir_sharers :
        ((x_21).info).mesi_dir_sharers}, value_write : (x_21).value_write,
        value : (x_21).value, may_victim : (x_21).may_victim, reps :
        (x_21).reps});
        Struct42 x_23 = (Struct42 {addr : (x_22).addr, info_write :
        (Bool)'(True), info_hit : (x_22).info_hit, info_way :
        (x_22).info_way, edir_hit : (x_22).edir_hit, edir_way :
        (x_22).edir_way, edir_slot : (x_22).edir_slot, info : Struct10
        {mesi_owned : ((x_22).info).mesi_owned, mesi_status :
        (Bit#(3))'(3'h4), mesi_dir_st : ((x_22).info).mesi_dir_st,
        mesi_dir_sharers : ((x_22).info).mesi_dir_sharers}, value_write :
        (x_22).value_write, value : (x_22).value, may_victim :
        (x_22).may_victim, reps :
        (x_22).reps});
        let x_26 = ?;
        if ((x_8).valid) begin
            let x_24 <- victims__003__setVictim(Struct44 {victim_idx :
            (x_8).data, victim_info : (x_23).info, victim_value :
            ((x_23).value_write ? ((x_23).value) : (x_9))});
            x_26 = x_9;
        end else begin
            let x_25 <- cache__003__valueRsLineRq(x_23);
            x_26 = x_25;
        end
        let x_27 <- releaseMSHR_003(x_4);
        Struct18 x_28 = (Struct18 {enq_type : (((x_19)[3:2]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : ((((x_19)[3:2]) ==
        ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : (x_19)[1:0], enq_msg : Struct1 {id : (Bit#(6))'(6'h9),
        type_ : (Bool)'(True), addr : (x_17).addr, value : unpack(0)}});
        let x_29 <- makeEnq_parentChildren003(x_28);
    endrule

    rule rule_exec_003_130;
        let x_0 <- deq_fifoL2E_003();
        Struct38 x_1 = ((x_0).lr_ir_pp);
        Bit#(4) x_2 = ((x_1).ir_msg_from);
        Struct1 x_3 = ((x_1).ir_msg);
        Bit#(2) x_4 = ((x_1).ir_mshr_id);
        Bool x_5 = ((x_1).ir_is_rs_rel);
        when (! (x_5), noAction);
        Struct39 x_6 = ((x_0).lr_ir);
        Struct10 x_7 = ((x_6).info);
        Struct37 x_8 = ((x_1).ir_by_victim);
        Vector#(4, Bit#(64)) x_9 = ((x_0).lr_value);
        let x_10 <- getMSHR_003(x_4);
        let x_11 <- getMSHRRq_003(x_4);
        Struct1 x_12 = (unpack(0));
        Vector#(4, Bit#(64)) x_13 = (unpack(0));
        Bool x_14 = ((x_7).mesi_owned);
        Bit#(3) x_15 = ((x_7).mesi_status);
        Struct15 x_16 = (Struct15 {dir_st : (((x_7).mesi_dir_st) ==
        ((Bit#(3))'(3'h0)) ? ((Bit#(3))'(3'h1)) : ((x_7).mesi_dir_st)),
        dir_excl : ((((x_7).mesi_dir_sharers)[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        ((((((x_7).mesi_dir_sharers)[3:1])[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        (((((((x_7).mesi_dir_sharers)[3:1])[2:1])[0:0]) == ((Bit#(1))'(1'h1))
        ? ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        ((((((((x_7).mesi_dir_sharers)[3:1])[2:1])[1:1])[0:0]) ==
        ((Bit#(1))'(1'h1)) ? ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        (unpack(0))))))))))))), dir_sharers : (x_7).mesi_dir_sharers});
        when ((x_2) == ((Bit#(4))'(4'hb)), noAction);
        when (((x_3).id) == ((Bit#(6))'(6'hc)), noAction);
        when (! ((x_3).type_), noAction);
        when ((Bool)'(True), noAction);
        Struct1 x_17 = (x_3);
        Struct42 x_18 = (Struct42 {addr : (x_3).addr, info_write :
        (Bool)'(False), info_hit : (x_6).info_hit, info_way : (x_6).info_way,
        edir_hit : (x_6).edir_hit, edir_way : (x_6).edir_way, edir_slot :
        (x_6).edir_slot, info : (x_6).info, value_write : (Bool)'(False),
        value : unpack(0), may_victim : (x_6).may_victim, reps :
        (x_6).reps});
        Struct42 x_19 = (Struct42 {addr : (x_18).addr, info_write :
        (Bool)'(True), info_hit : (x_18).info_hit, info_way :
        (x_18).info_way, edir_hit : (x_18).edir_hit, edir_way :
        (x_18).edir_way, edir_slot : (x_18).edir_slot, info : Struct10
        {mesi_owned : ((x_18).info).mesi_owned, mesi_status :
        (Bit#(3))'(3'h1), mesi_dir_st : ((x_18).info).mesi_dir_st,
        mesi_dir_sharers : ((x_18).info).mesi_dir_sharers}, value_write :
        (x_18).value_write, value : (x_18).value, may_victim :
        (x_18).may_victim, reps : (x_18).reps});
        Struct42 x_20 = (Struct42 {addr : (x_19).addr, info_write :
        (Bool)'(True), info_hit : (x_19).info_hit, info_way :
        (x_19).info_way, edir_hit : (x_19).edir_hit, edir_way :
        (x_19).edir_way, edir_slot : (x_19).edir_slot, info : Struct10
        {mesi_owned : (Bool)'(False), mesi_status :
        ((x_19).info).mesi_status, mesi_dir_st : ((x_19).info).mesi_dir_st,
        mesi_dir_sharers : ((x_19).info).mesi_dir_sharers}, value_write :
        (x_19).value_write, value : (x_19).value, may_victim :
        (x_19).may_victim, reps :
        (x_19).reps});
        let x_23 = ?;
        if ((x_8).valid) begin
            let x_21 <- victims__003__setVictim(Struct44 {victim_idx :
            (x_8).data, victim_info : (x_20).info, victim_value :
            ((x_20).value_write ? ((x_20).value) : (x_9))});
            x_23 = x_9;
        end else begin
            let x_22 <- cache__003__valueRsLineRq(x_20);
            x_23 = x_22;
        end
        Struct18 x_24 = (Struct18 {enq_type : ((((Bit#(4))'(4'h7))[3:2]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : (((((Bit#(4))'(4'h7))[3:2])
        == ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : ((Bit#(4))'(4'h7))[1:0], enq_msg : Struct1 {id :
        (Bit#(6))'(6'hd), type_ : (Bool)'(True), addr : (x_17).addr, value :
        unpack(0)}});
        let x_25 <- makeEnq_parentChildren003(x_24);
        let x_26 <- releaseMSHR_003(x_4);
    endrule

    rule rule_exec_003_131;
        let x_0 <- deq_fifoL2E_003();
        Struct38 x_1 = ((x_0).lr_ir_pp);
        Bit#(4) x_2 = ((x_1).ir_msg_from);
        Struct1 x_3 = ((x_1).ir_msg);
        Bit#(2) x_4 = ((x_1).ir_mshr_id);
        Bool x_5 = ((x_1).ir_is_rs_rel);
        when (! (x_5), noAction);
        Struct39 x_6 = ((x_0).lr_ir);
        Struct10 x_7 = ((x_6).info);
        Struct37 x_8 = ((x_1).ir_by_victim);
        Vector#(4, Bit#(64)) x_9 = ((x_0).lr_value);
        let x_10 <- getMSHR_003(x_4);
        let x_11 <- getMSHRRq_003(x_4);
        Struct1 x_12 = (unpack(0));
        Vector#(4, Bit#(64)) x_13 = (unpack(0));
        Bool x_14 = ((x_7).mesi_owned);
        Bit#(3) x_15 = ((x_7).mesi_status);
        Struct15 x_16 = (Struct15 {dir_st : (((x_7).mesi_dir_st) ==
        ((Bit#(3))'(3'h0)) ? ((Bit#(3))'(3'h1)) : ((x_7).mesi_dir_st)),
        dir_excl : ((((x_7).mesi_dir_sharers)[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        ((((((x_7).mesi_dir_sharers)[3:1])[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        (((((((x_7).mesi_dir_sharers)[3:1])[2:1])[0:0]) == ((Bit#(1))'(1'h1))
        ? ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        ((((((((x_7).mesi_dir_sharers)[3:1])[2:1])[1:1])[0:0]) ==
        ((Bit#(1))'(1'h1)) ? ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        (unpack(0))))))))))))), dir_sharers : (x_7).mesi_dir_sharers});
        when ((x_2) == ((Bit#(4))'(4'hb)), noAction);
        when (((x_3).id) == ((Bit#(6))'(6'he)), noAction);
        when (! ((x_3).type_), noAction);
        when (! ((x_15) < ((Bit#(3))'(3'h3))), noAction);
        Struct1 x_17 = (x_3);
        Struct42 x_18 = (Struct42 {addr : (x_3).addr, info_write :
        (Bool)'(False), info_hit : (x_6).info_hit, info_way : (x_6).info_way,
        edir_hit : (x_6).edir_hit, edir_way : (x_6).edir_way, edir_slot :
        (x_6).edir_slot, info : (x_6).info, value_write : (Bool)'(False),
        value : unpack(0), may_victim : (x_6).may_victim, reps :
        (x_6).reps});
        Struct42 x_19 = (Struct42 {addr : (x_18).addr, info_write :
        (Bool)'(True), info_hit : (x_18).info_hit, info_way :
        (x_18).info_way, edir_hit : (x_18).edir_hit, edir_way :
        (x_18).edir_way, edir_slot : (x_18).edir_slot, info : Struct10
        {mesi_owned : ((x_18).info).mesi_owned, mesi_status :
        (Bit#(3))'(3'h1), mesi_dir_st : ((x_18).info).mesi_dir_st,
        mesi_dir_sharers : ((x_18).info).mesi_dir_sharers}, value_write :
        (x_18).value_write, value : (x_18).value, may_victim :
        (x_18).may_victim, reps : (x_18).reps});
        Struct42 x_20 = (Struct42 {addr : (x_19).addr, info_write :
        (Bool)'(True), info_hit : (x_19).info_hit, info_way :
        (x_19).info_way, edir_hit : (x_19).edir_hit, edir_way :
        (x_19).edir_way, edir_slot : (x_19).edir_slot, info : Struct10
        {mesi_owned : (Bool)'(False), mesi_status :
        ((x_19).info).mesi_status, mesi_dir_st : ((x_19).info).mesi_dir_st,
        mesi_dir_sharers : ((x_19).info).mesi_dir_sharers}, value_write :
        (x_19).value_write, value : (x_19).value, may_victim :
        (x_19).may_victim, reps :
        (x_19).reps});
        let x_23 = ?;
        if ((x_8).valid) begin
            let x_21 <- victims__003__setVictim(Struct44 {victim_idx :
            (x_8).data, victim_info : (x_20).info, victim_value :
            ((x_20).value_write ? ((x_20).value) : (x_9))});
            x_23 = x_9;
        end else begin
            let x_22 <- cache__003__valueRsLineRq(x_20);
            x_23 = x_22;
        end
        Struct18 x_24 = (Struct18 {enq_type : ((((Bit#(4))'(4'h7))[3:2]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : (((((Bit#(4))'(4'h7))[3:2])
        == ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : ((Bit#(4))'(4'h7))[1:0], enq_msg : Struct1 {id :
        (Bit#(6))'(6'hf), type_ : (Bool)'(True), addr : (x_17).addr, value :
        unpack(0)}});
        let x_25 <- makeEnq_parentChildren003(x_24);
        let x_26 <- releaseMSHR_003(x_4);
    endrule

    rule rule_exec_003_20;
        let x_0 <- victims__003__getFirstVictim();
        Bit#(64) x_1 = ((x_0).victim_addr);
        Struct10 x_2 = ((x_0).victim_info);
        Vector#(4, Bit#(64)) x_3 = ((x_0).victim_value);
        Struct1 x_4 = (Struct1 {id : unpack(0), type_ : (Bool)'(False), addr
        : x_1, value : unpack(0)});
        Struct14 x_5 = (Struct14 {m_is_ul : (Bool)'(True), m_qidx :
        unpack(0), m_rsb : (Bool)'(False), m_dl_rss_from : unpack(0),
        m_dl_rss_recv : unpack(0)});
        Struct1 x_6 = (unpack(0));
        Struct1 x_7 = (unpack(0));
        Vector#(4, Bit#(64)) x_8 = (unpack(0));
        Bool x_9 = ((x_2).mesi_owned);
        Bit#(3) x_10 = ((x_2).mesi_status);
        Struct15 x_11 = (Struct15 {dir_st : (((x_2).mesi_dir_st) ==
        ((Bit#(3))'(3'h0)) ? ((Bit#(3))'(3'h1)) : ((x_2).mesi_dir_st)),
        dir_excl : ((((x_2).mesi_dir_sharers)[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        ((((((x_2).mesi_dir_sharers)[3:1])[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        (((((((x_2).mesi_dir_sharers)[3:1])[2:1])[0:0]) == ((Bit#(1))'(1'h1))
        ? ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        ((((((((x_2).mesi_dir_sharers)[3:1])[2:1])[1:1])[0:0]) ==
        ((Bit#(1))'(1'h1)) ? ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        (unpack(0))))))))))))), dir_sharers : (x_2).mesi_dir_sharers});
        when (! ((x_4).type_), noAction);
        when (((x_9) == ((Bool)'(False))) && ((((Bit#(3))'(3'h0)) < (x_10))
        && ((x_10) < ((Bit#(3))'(3'h4)))), noAction);
        Struct18 x_12 = (Struct18 {enq_type : ((((Bit#(4))'(4'h3))[3:2]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : (((((Bit#(4))'(4'h3))[3:2])
        == ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : ((Bit#(4))'(4'h3))[1:0], enq_msg : Struct1 {id :
        (Bit#(6))'(6'h14), type_ : (Bool)'(False), addr : (x_4).addr, value :
        unpack(0)}});
        let x_13 <- makeEnq_parentChildren003(x_12);
        let x_14 <- setULImm_003(x_4);
        let x_15 <- victims__003__setVictimRq(x_1);
    endrule

    rule rule_exec_003_21;
        let x_0 <- victims__003__getFirstVictim();
        Bit#(64) x_1 = ((x_0).victim_addr);
        Struct10 x_2 = ((x_0).victim_info);
        Vector#(4, Bit#(64)) x_3 = ((x_0).victim_value);
        Struct1 x_4 = (Struct1 {id : unpack(0), type_ : (Bool)'(False), addr
        : x_1, value : unpack(0)});
        Struct14 x_5 = (Struct14 {m_is_ul : (Bool)'(True), m_qidx :
        unpack(0), m_rsb : (Bool)'(False), m_dl_rss_from : unpack(0),
        m_dl_rss_recv : unpack(0)});
        Struct1 x_6 = (unpack(0));
        Struct1 x_7 = (unpack(0));
        Vector#(4, Bit#(64)) x_8 = (unpack(0));
        Bool x_9 = ((x_2).mesi_owned);
        Bit#(3) x_10 = ((x_2).mesi_status);
        Struct15 x_11 = (Struct15 {dir_st : (((x_2).mesi_dir_st) ==
        ((Bit#(3))'(3'h0)) ? ((Bit#(3))'(3'h1)) : ((x_2).mesi_dir_st)),
        dir_excl : ((((x_2).mesi_dir_sharers)[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        ((((((x_2).mesi_dir_sharers)[3:1])[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        (((((((x_2).mesi_dir_sharers)[3:1])[2:1])[0:0]) == ((Bit#(1))'(1'h1))
        ? ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        ((((((((x_2).mesi_dir_sharers)[3:1])[2:1])[1:1])[0:0]) ==
        ((Bit#(1))'(1'h1)) ? ((Bit#(2))'(2'h0)) : (((Bit#(2))'(2'h1)) +
        (unpack(0))))))))))))), dir_sharers : (x_2).mesi_dir_sharers});
        when (! ((x_4).type_), noAction);
        when (((Bit#(3))'(3'h0)) < (x_10), noAction);
        Struct18 x_12 = (Struct18 {enq_type : ((((Bit#(4))'(4'h3))[3:2]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : (((((Bit#(4))'(4'h3))[3:2])
        == ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : ((Bit#(4))'(4'h3))[1:0], enq_msg : Struct1 {id :
        (Bit#(6))'(6'h15), type_ : (Bool)'(False), addr : (x_4).addr, value :
        x_3}});
        let x_13 <- makeEnq_parentChildren003(x_12);
        let x_14 <- setULImm_003(x_4);
        let x_15 <- victims__003__setVictimRq(x_1);
    endrule

    // No methods in this module
endmodule

// The CC interface is defined in the header part (thus in Header.bsv)

module mkCC#(function ActionValue#(Struct1) deq_fifo002(),
function Action enq_fifo001(Struct1 _),
function Action enq_fifo000(Struct1 _)) (CC);
    Module1 m1 <- mkModule1 ();
    Module2 m2 <- mkModule2 ();
    Module3 m3 <- mkModule3 ();
    Module4 m4 <- mkModule4 ();
    Module5 m5 <- mkModule5 ();
    Module6 m6 <- mkModule6 ();
    Module7 m7 <- mkModule7 ();
    Module8 m8 <- mkModule8 ();
    Module9 m9 <- mkModule9 ();
    Module10 m10 <- mkModule10 ();
    Module11 m11 <- mkModule11 ();
    Module12 m12 <- mkModule12 ();
    Module13 m13 <- mkModule13 ();
    Module14 m14 <- mkModule14 ();
    Module15 m15 <- mkModule15 ();
    Module16 m16 <- mkModule16 ();
    Module17 m17 <- mkModule17 ();
    Module18 m18 <- mkModule18 ();
    Module19 m19 <- mkModule19 ();
    Module20 m20 <- mkModule20 ();
    Module21 m21 <- mkModule21 ();
    Module22 m22 <- mkModule22 ();
    Module23 m23 <- mkModule23 ();
    Module24 m24 <- mkModule24 ();
    Module25 m25 <- mkModule25 ();
    Module26 m26 <- mkModule26 ();
    Module27 m27 <- mkModule27 ();
    Module28 m28 <- mkModule28 ();
    Module29 m29 <- mkModule29 ();
    Module30 m30 <- mkModule30 ();
    Module31 m31 <- mkModule31 ();
    Module32 m32 <- mkModule32 ();
    Module33 m33 <- mkModule33 ();
    Module34 m34 <- mkModule34 ();
    Module35 m35 <- mkModule35 ();
    Module36 m36 <- mkModule36 ();
    Module37 m37 <- mkModule37 ();
    Module38 m38 <- mkModule38 ();
    Module39 m39 <- mkModule39 ();
    Module40 m40 <- mkModule40 ();
    Module41 m41 <- mkModule41 ();
    Module42 m42 <- mkModule42 ();
    Module43 m43 <- mkModule43 ();
    Module44 m44 <- mkModule44 ();
    Module45 m45 <- mkModule45 ();
    Module46 m46 <- mkModule46 ();
    Module47 m47 <- mkModule47 ();
    Module48 m48 <- mkModule48 ();
    Module49 m49 <- mkModule49 ();
    Module50 m50 <- mkModule50 ();
    Module51 m51 <- mkModule51 ();
    Module52 m52 <- mkModule52 ();
    Module53 m53 <- mkModule53 ();
    Module54 m54 <- mkModule54 ();
    Module55 m55 <- mkModule55 ();
    Module56 m56 <- mkModule56 ();
    Module57 m57 <- mkModule57 ();
    Module58 m58 <- mkModule58 ();
    Module59 m59 <- mkModule59 ();
    Module60 m60 <- mkModule60 ();
    Module61 m61 <- mkModule61 ();
    Module62 m62 <- mkModule62 ();
    Module63 m63 <- mkModule63 ();
    Module64 m64 <- mkModule64 ();
    Module65 m65 <- mkModule65 ();
    Module66 m66 <- mkModule66 ();
    Module67 m67 <- mkModule67 ();
    Module68 m68 <- mkModule68 ();
    Module69 m69 <- mkModule69 ();
    Module70 m70 <- mkModule70 ();
    Module71 m71 <- mkModule71 ();
    Module72 m72 <- mkModule72 ();
    Module73 m73 <- mkModule73 ();
    Module74 m74 <- mkModule74 ();
    Module75 m75 <- mkModule75 ();
    Module76 m76 <- mkModule76 ();
    Module77 m77 <- mkModule77 ();
    Module78 m78 <- mkModule78 ();
    Module79 m79 <- mkModule79 ();
    Module80 m80 <- mkModule80 ();
    Module81 m81 <- mkModule81 ();
    Module82 m82 <- mkModule82 ();
    Module83 m83 <- mkModule83 ();
    Module84 m84 <- mkModule84 ();
    Module85 m85 <- mkModule85 ();
    Module86 m86 <- mkModule86 ();
    Module87 m87 <- mkModule87 ();
    Module88 m88 <- mkModule88 ();
    Module89 m89 <- mkModule89 ();
    Module90 m90 <- mkModule90 ();
    Module91 m91 <- mkModule91 ();
    Module92 m92 <- mkModule92 ();
    Module93 m93 <- mkModule93 ();
    Module94 m94 <- mkModule94 ();
    Module95 m95 <- mkModule95 ();
    Module96 m96 <- mkModule96 ();
    Module97 m97 <- mkModule97 ();
    Module98 m98 <- mkModule98 ();
    Module99 m99 <- mkModule99 ();
    Module100 m100 <- mkModule100 ();
    Module101 m101 <- mkModule101 ();
    Module102 m102 <- mkModule102 ();
    Module103 m103 <- mkModule103 ();
    Module104 m104 <- mkModule104 ();
    Module105 m105 <- mkModule105 ();
    Module106 m106 <- mkModule106 ();
    Module107 m107 <- mkModule107 (m94.deq_fifo0030, m76.deq_fifo0020,
    m58.deq_fifo0010, m1.enq_fifoCRqInput_00, m40.deq_fifo0000);
    Module108 m108 <- mkModule108 (m95.deq_fifo0031, m77.deq_fifo0021,
    m59.deq_fifo0011, m2.enq_fifoCRsInput_00, m41.deq_fifo0001);
    Module109 m109 <- mkModule109 (m3.enq_fifoPInput_00, deq_fifo002);

    Module110 m110 <- mkModule110 (m42.enq_fifo0002, m60.enq_fifo0012,
    m78.enq_fifo0022, m96.enq_fifo0032, enq_fifo001, enq_fifo000);
    Module111 m111 <- mkModule111 (m33.wrReq_repRam__00,
    m33.rdResp_repRam__00, m33.rdReq_repRam__00);
    Module112 m112 <- mkModule112 (m35.enq_fifoCRqInput_000,
    m43.deq_fifo00000);
    Module113 m113 <- mkModule113 (m36.enq_fifoPInput_000, m42.deq_fifo0002);

    Module114 m114 <- mkModule114 (m44.enq_fifo00002, m41.enq_fifo0001,
    m40.enq_fifo0000);
    Module115 m115 <- mkModule115 (m51.wrReq_repRam__000,
    m51.rdResp_repRam__000, m51.rdReq_repRam__000);
    Module116 m116 <- mkModule116 (m53.enq_fifoCRqInput_001,
    m61.deq_fifo00100);
    Module117 m117 <- mkModule117 (m54.enq_fifoPInput_001, m60.deq_fifo0012);

    Module118 m118 <- mkModule118 (m62.enq_fifo00102, m59.enq_fifo0011,
    m58.enq_fifo0010);
    Module119 m119 <- mkModule119 (m69.wrReq_repRam__001,
    m69.rdResp_repRam__001, m69.rdReq_repRam__001);
    Module120 m120 <- mkModule120 (m71.enq_fifoCRqInput_002,
    m79.deq_fifo00200);
    Module121 m121 <- mkModule121 (m72.enq_fifoPInput_002, m78.deq_fifo0022);

    Module122 m122 <- mkModule122 (m80.enq_fifo00202, m77.enq_fifo0021,
    m76.enq_fifo0020);
    Module123 m123 <- mkModule123 (m87.wrReq_repRam__002,
    m87.rdResp_repRam__002, m87.rdReq_repRam__002);
    Module124 m124 <- mkModule124 (m89.enq_fifoCRqInput_003,
    m97.deq_fifo00300);
    Module125 m125 <- mkModule125 (m90.enq_fifoPInput_003, m96.deq_fifo0032);

    Module126 m126 <- mkModule126 (m98.enq_fifo00302, m95.enq_fifo0031,
    m94.enq_fifo0030);
    Module127 m127 <- mkModule127 (m105.wrReq_repRam__003,
    m105.rdResp_repRam__003, m105.rdReq_repRam__003);
    Module128 m128 <- mkModule128 (m32.wrReq_dataRam__00,
    m24.wrReq_edirRam__00__7, m25.wrReq_edirRam__00__6,
    m26.wrReq_edirRam__00__5, m27.wrReq_edirRam__00__4,
    m28.wrReq_edirRam__00__3, m29.wrReq_edirRam__00__2,
    m30.wrReq_edirRam__00__1, m31.wrReq_edirRam__00__0, m111.repAccess__00,
    m7.victims__00__registerVictim, m8.wrReq_infoRam__00__15,
    m9.wrReq_infoRam__00__14, m10.wrReq_infoRam__00__13,
    m11.wrReq_infoRam__00__12, m12.wrReq_infoRam__00__11,
    m13.wrReq_infoRam__00__10, m14.wrReq_infoRam__00__9,
    m15.wrReq_infoRam__00__8, m16.wrReq_infoRam__00__7,
    m17.wrReq_infoRam__00__6, m18.wrReq_infoRam__00__5,
    m19.wrReq_infoRam__00__4, m20.wrReq_infoRam__00__3,
    m21.wrReq_infoRam__00__2, m22.wrReq_infoRam__00__1,
    m23.wrReq_infoRam__00__0, m32.rdResp_dataRam__00, m32.rdReq_dataRam__00,
    m111.repGetRs__00, m24.rdResp_edirRam__00__7, m25.rdResp_edirRam__00__6,
    m26.rdResp_edirRam__00__5, m27.rdResp_edirRam__00__4,
    m28.rdResp_edirRam__00__3, m29.rdResp_edirRam__00__2,
    m30.rdResp_edirRam__00__1, m31.rdResp_edirRam__00__0,
    m8.rdResp_infoRam__00__15, m9.rdResp_infoRam__00__14,
    m10.rdResp_infoRam__00__13, m11.rdResp_infoRam__00__12,
    m12.rdResp_infoRam__00__11, m13.rdResp_infoRam__00__10,
    m14.rdResp_infoRam__00__9, m15.rdResp_infoRam__00__8,
    m16.rdResp_infoRam__00__7, m17.rdResp_infoRam__00__6,
    m18.rdResp_infoRam__00__5, m19.rdResp_infoRam__00__4,
    m20.rdResp_infoRam__00__3, m21.rdResp_infoRam__00__2,
    m22.rdResp_infoRam__00__1, m23.rdResp_infoRam__00__0, m111.repGetRq__00,
    m24.rdReq_edirRam__00__7, m25.rdReq_edirRam__00__6,
    m26.rdReq_edirRam__00__5, m27.rdReq_edirRam__00__4,
    m28.rdReq_edirRam__00__3, m29.rdReq_edirRam__00__2,
    m30.rdReq_edirRam__00__1, m31.rdReq_edirRam__00__0,
    m8.rdReq_infoRam__00__15, m9.rdReq_infoRam__00__14,
    m10.rdReq_infoRam__00__13, m11.rdReq_infoRam__00__12,
    m12.rdReq_infoRam__00__11, m13.rdReq_infoRam__00__10,
    m14.rdReq_infoRam__00__9, m15.rdReq_infoRam__00__8,
    m16.rdReq_infoRam__00__7, m17.rdReq_infoRam__00__6,
    m18.rdReq_infoRam__00__5, m19.rdReq_infoRam__00__4,
    m20.rdReq_infoRam__00__3, m21.rdReq_infoRam__00__2,
    m22.rdReq_infoRam__00__1, m23.rdReq_infoRam__00__0);
    Module129 m129 <- mkModule129 (m50.wrReq_dataRam__000,
    m115.repAccess__000, m45.victims__000__registerVictim,
    m46.wrReq_infoRam__000__3, m47.wrReq_infoRam__000__2,
    m48.wrReq_infoRam__000__1, m49.wrReq_infoRam__000__0,
    m50.rdResp_dataRam__000, m50.rdReq_dataRam__000, m115.repGetRs__000,
    m46.rdResp_infoRam__000__3, m47.rdResp_infoRam__000__2,
    m48.rdResp_infoRam__000__1, m49.rdResp_infoRam__000__0,
    m115.repGetRq__000, m46.rdReq_infoRam__000__3, m47.rdReq_infoRam__000__2,
    m48.rdReq_infoRam__000__1, m49.rdReq_infoRam__000__0);
    Module130 m130 <- mkModule130 (m68.wrReq_dataRam__001,
    m119.repAccess__001, m63.victims__001__registerVictim,
    m64.wrReq_infoRam__001__3, m65.wrReq_infoRam__001__2,
    m66.wrReq_infoRam__001__1, m67.wrReq_infoRam__001__0,
    m68.rdResp_dataRam__001, m68.rdReq_dataRam__001, m119.repGetRs__001,
    m64.rdResp_infoRam__001__3, m65.rdResp_infoRam__001__2,
    m66.rdResp_infoRam__001__1, m67.rdResp_infoRam__001__0,
    m119.repGetRq__001, m64.rdReq_infoRam__001__3, m65.rdReq_infoRam__001__2,
    m66.rdReq_infoRam__001__1, m67.rdReq_infoRam__001__0);
    Module131 m131 <- mkModule131 (m86.wrReq_dataRam__002,
    m123.repAccess__002, m81.victims__002__registerVictim,
    m82.wrReq_infoRam__002__3, m83.wrReq_infoRam__002__2,
    m84.wrReq_infoRam__002__1, m85.wrReq_infoRam__002__0,
    m86.rdResp_dataRam__002, m86.rdReq_dataRam__002, m123.repGetRs__002,
    m82.rdResp_infoRam__002__3, m83.rdResp_infoRam__002__2,
    m84.rdResp_infoRam__002__1, m85.rdResp_infoRam__002__0,
    m123.repGetRq__002, m82.rdReq_infoRam__002__3, m83.rdReq_infoRam__002__2,
    m84.rdReq_infoRam__002__1, m85.rdReq_infoRam__002__0);
    Module132 m132 <- mkModule132 (m104.wrReq_dataRam__003,
    m127.repAccess__003, m99.victims__003__registerVictim,
    m100.wrReq_infoRam__003__3, m101.wrReq_infoRam__003__2,
    m102.wrReq_infoRam__003__1, m103.wrReq_infoRam__003__0,
    m104.rdResp_dataRam__003, m104.rdReq_dataRam__003, m127.repGetRs__003,
    m100.rdResp_infoRam__003__3, m101.rdResp_infoRam__003__2,
    m102.rdResp_infoRam__003__1, m103.rdResp_infoRam__003__0,
    m127.repGetRq__003, m100.rdReq_infoRam__003__3,
    m101.rdReq_infoRam__003__2, m102.rdReq_infoRam__003__1,
    m103.rdReq_infoRam__003__0);
    Module133 m133 <- mkModule133 (m34.canImm_00,
    m7.victims__00__setVictimRq, m34.setULImm_00,
    m7.victims__00__getFirstVictim, m34.transferUpDown_00,
    m34.getMSHRFirstRs_00, m110.broadcast_parentChildren00,
    m34.registerDL_00, m34.registerUL_00, m110.makeEnq_parentChildren00,
    m128.cache__00__valueRsLineRq, m7.victims__00__setVictim,
    m34.getMSHRRq_00, m34.getMSHR_00, m6.deq_fifoL2E_00,
    m7.victims__00__getVictim, m6.enq_fifoL2E_00,
    m128.cache__00__infoRsValueRq, m5.deq_fifoI2L_00, m5.enq_fifoI2L_00,
    m128.cache__00__infoRq, m4.deq_fifoN2I_00, m34.getDLReady_00,
    m34.addRs_00, m2.deq_fifoCRsInput_00, m34.getCRqSlot_00,
    m7.victims__00__hasVictim, m1.deq_fifoCRqInput_00, m34.releaseMSHR_00,
    m7.victims__00__releaseVictim, m34.getWait_00, m34.startRelease_00,
    m34.getULReady_00, m4.enq_fifoN2I_00, m7.victims__00__findVictim,
    m34.getPRqSlot_00, m3.deq_fifoPInput_00);
    Module134 m134 <- mkModule134 (m45.victims__000__setVictimRq,
    m52.setULImm_000, m45.victims__000__getFirstVictim,
    m45.victims__000__setVictim, m52.registerUL_000,
    m114.makeEnq_parentChildren000, m129.cache__000__valueRsLineRq,
    m52.getMSHRRq_000, m52.getMSHR_000, m39.deq_fifoL2E_000,
    m45.victims__000__getVictim, m39.enq_fifoL2E_000,
    m129.cache__000__infoRsValueRq, m38.deq_fifoI2L_000, m38.enq_fifoI2L_000,
    m129.cache__000__infoRq, m37.deq_fifoN2I_000, m52.getCRqSlot_000,
    m45.victims__000__hasVictim, m35.deq_fifoCRqInput_000,
    m52.releaseMSHR_000, m45.victims__000__releaseVictim, m52.getWait_000,
    m52.startRelease_000, m52.getULReady_000, m37.enq_fifoN2I_000,
    m45.victims__000__findVictim, m52.getPRqSlot_000,
    m36.deq_fifoPInput_000);
    Module135 m135 <- mkModule135 (m63.victims__001__setVictimRq,
    m70.setULImm_001, m63.victims__001__getFirstVictim,
    m63.victims__001__setVictim, m70.registerUL_001,
    m118.makeEnq_parentChildren001, m130.cache__001__valueRsLineRq,
    m70.getMSHRRq_001, m70.getMSHR_001, m57.deq_fifoL2E_001,
    m63.victims__001__getVictim, m57.enq_fifoL2E_001,
    m130.cache__001__infoRsValueRq, m56.deq_fifoI2L_001, m56.enq_fifoI2L_001,
    m130.cache__001__infoRq, m55.deq_fifoN2I_001, m70.getCRqSlot_001,
    m63.victims__001__hasVictim, m53.deq_fifoCRqInput_001,
    m70.releaseMSHR_001, m63.victims__001__releaseVictim, m70.getWait_001,
    m70.startRelease_001, m70.getULReady_001, m55.enq_fifoN2I_001,
    m63.victims__001__findVictim, m70.getPRqSlot_001,
    m54.deq_fifoPInput_001);
    Module136 m136 <- mkModule136 (m81.victims__002__setVictimRq,
    m88.setULImm_002, m81.victims__002__getFirstVictim,
    m81.victims__002__setVictim, m88.registerUL_002,
    m122.makeEnq_parentChildren002, m131.cache__002__valueRsLineRq,
    m88.getMSHRRq_002, m88.getMSHR_002, m75.deq_fifoL2E_002,
    m81.victims__002__getVictim, m75.enq_fifoL2E_002,
    m131.cache__002__infoRsValueRq, m74.deq_fifoI2L_002, m74.enq_fifoI2L_002,
    m131.cache__002__infoRq, m73.deq_fifoN2I_002, m88.getCRqSlot_002,
    m81.victims__002__hasVictim, m71.deq_fifoCRqInput_002,
    m88.releaseMSHR_002, m81.victims__002__releaseVictim, m88.getWait_002,
    m88.startRelease_002, m88.getULReady_002, m73.enq_fifoN2I_002,
    m81.victims__002__findVictim, m88.getPRqSlot_002,
    m72.deq_fifoPInput_002);
    Module137 m137 <- mkModule137 (m99.victims__003__setVictimRq,
    m106.setULImm_003, m99.victims__003__getFirstVictim,
    m99.victims__003__setVictim, m106.registerUL_003,
    m126.makeEnq_parentChildren003, m132.cache__003__valueRsLineRq,
    m106.getMSHRRq_003, m106.getMSHR_003, m93.deq_fifoL2E_003,
    m99.victims__003__getVictim, m93.enq_fifoL2E_003,
    m132.cache__003__infoRsValueRq, m92.deq_fifoI2L_003, m92.enq_fifoI2L_003,
    m132.cache__003__infoRq, m91.deq_fifoN2I_003, m106.getCRqSlot_003,
    m99.victims__003__hasVictim, m89.deq_fifoCRqInput_003,
    m106.releaseMSHR_003, m99.victims__003__releaseVictim, m106.getWait_003,
    m106.startRelease_003, m106.getULReady_003, m91.enq_fifoN2I_003,
    m99.victims__003__findVictim, m106.getPRqSlot_003,
    m90.deq_fifoPInput_003);
    //// Interface

    function MemRqRs#(Struct1) getMemRqRs (function Action enq_rq (Struct1 _),
                                           function ActionValue#(Struct1) deq_rs ());
        return interface MemRqRs;
                   method mem_enq_rq = enq_rq;
                   method mem_deq_rs = deq_rs;
               endinterface;
    endfunction

    Vector#(L1Num, MemRqRs#(Struct1)) _l1Ifc = newVector();
    _l1Ifc[0] = getMemRqRs(m43.enq_fifo00000, m44.deq_fifo00002);
    _l1Ifc[1] = getMemRqRs(m61.enq_fifo00100, m62.deq_fifo00102);
    _l1Ifc[2] = getMemRqRs(m79.enq_fifo00200, m80.deq_fifo00202);
    _l1Ifc[3] = getMemRqRs(m97.enq_fifo00300, m98.deq_fifo00302);
    interface l1Ifc = _l1Ifc;

    interface DMA llDma;
        method dma_rdReq = m32.rdReq_dataRam__00;
        method dma_wrReq = m32.wrReq_dataRam__00;
        method dma_rdResp = m32.rdResp_dataRam__00;
    endinterface

endmodule
