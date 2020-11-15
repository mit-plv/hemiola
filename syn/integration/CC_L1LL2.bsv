import Vector::*;
import BuildVector::*;
import FIFO::*;
import FIFOF::*;
import RWBramCore::*;
import SpecialFIFOs::*;
import HCCIfc::*;

interface CC;
    interface Vector#(L1Num, MemRqRs#(Struct1)) l1Ifc;
    interface DMA#(Bit#(12), Struct34, Vector#(4, Bit#(64))) llDma;
endinterface

typedef struct { Bit#(6) id; Bool type_; Bit#(64) addr; Vector#(4, Bit#(64)) value;  } Struct1 deriving(Eq, Bits);
typedef struct { Bool valid; Bit#(2) data;  } Struct10 deriving(Eq, Bits);
typedef struct { Bool mesi_owned; Bit#(3) mesi_status; Bit#(3) mesi_dir_st; Bit#(2) mesi_dir_sharers;  } Struct11 deriving(Eq, Bits);
typedef struct { Bit#(64) mv_addr; Struct11 mv_info;  } Struct12 deriving(Eq, Bits);
typedef struct { Struct6 lr_ir_pp; Struct9 lr_ir; Vector#(4, Bit#(64)) lr_value;  } Struct13 deriving(Eq, Bits);
typedef struct { Bool victim_valid; Bit#(64) victim_addr; Struct11 victim_info; Vector#(4, Bit#(64)) victim_value; Bool victim_req;  } Struct14 deriving(Eq, Bits);
typedef struct { Bit#(3) m_status; Struct16 m_next; Bool m_is_ul; Bit#(64) m_addr; Bit#(3) m_qidx; Bool m_rsb; Bit#(2) m_dl_rss_from; Bit#(2) m_dl_rss_recv;  } Struct15 deriving(Eq, Bits);
typedef struct { Bool valid; Bit#(4) data;  } Struct16 deriving(Eq, Bits);
typedef struct { Bit#(3) dir_st; Bit#(1) dir_excl; Bit#(2) dir_sharers;  } Struct17 deriving(Eq, Bits);
typedef struct { Bit#(64) addr; Bool info_write; Bool info_hit; Bit#(3) info_way; Bool edir_hit; Bit#(2) edir_way; Struct10 edir_slot; Struct11 info; Bool value_write; Vector#(4, Bit#(64)) value; Struct12 may_victim; Vector#(8, Bit#(8)) reps;  } Struct18 deriving(Eq, Bits);
typedef struct { Bit#(3) victim_idx; Struct11 victim_info; Vector#(4, Bit#(64)) victim_value;  } Struct19 deriving(Eq, Bits);
typedef struct { Struct1 in_msg; Bit#(3) in_msg_from;  } Struct2 deriving(Eq, Bits);
typedef struct { Bit#(2) enq_type; Bit#(1) enq_ch_idx; Struct1 enq_msg;  } Struct20 deriving(Eq, Bits);
typedef struct { Bit#(4) r_id; Bool r_ul_rsb; Bit#(1) r_ul_rsbTo;  } Struct21 deriving(Eq, Bits);
typedef struct { Bit#(4) r_id; Bit#(2) r_dl_rss_from; Bool r_dl_rsb; Bit#(3) r_dl_rsbTo;  } Struct22 deriving(Eq, Bits);
typedef struct { Bit#(2) cs_inds; Struct1 cs_msg;  } Struct23 deriving(Eq, Bits);
typedef struct { Bit#(3) cidx; Struct1 msg;  } Struct24 deriving(Eq, Bits);
typedef struct { Bit#(4) r_id; Bit#(2) r_dl_rss_from;  } Struct25 deriving(Eq, Bits);
typedef struct { Bit#(50) tag; Struct11 value;  } Struct26 deriving(Eq, Bits);
typedef struct { Bool tm_hit; Bit#(3) tm_way; Struct11 tm_value;  } Struct27 deriving(Eq, Bits);
typedef struct { Bit#(50) tag; Struct29 value;  } Struct28 deriving(Eq, Bits);
typedef struct { Bool mesi_edir_owned; Bit#(3) mesi_edir_st; Bit#(2) mesi_edir_sharers;  } Struct29 deriving(Eq, Bits);
typedef struct { Bit#(4) r_id; Struct1 r_msg; Bit#(3) r_msg_from;  } Struct3 deriving(Eq, Bits);
typedef struct { Bool tm_hit; Bit#(2) tm_way; Struct29 tm_value;  } Struct30 deriving(Eq, Bits);
typedef struct { Bit#(9) addr; Struct26 datain;  } Struct31 deriving(Eq, Bits);
typedef struct { Bit#(1) acc_type; Vector#(8, Bit#(8)) acc_reps; Bit#(9) acc_index; Bit#(3) acc_way;  } Struct32 deriving(Eq, Bits);
typedef struct { Bit#(9) addr; Struct28 datain;  } Struct33 deriving(Eq, Bits);
typedef struct { Bit#(12) addr; Vector#(4, Bit#(64)) datain;  } Struct34 deriving(Eq, Bits);
typedef struct { Bool valid; Struct14 data;  } Struct35 deriving(Eq, Bits);
typedef struct { Bit#(9) addr; Vector#(8, Bit#(8)) datain;  } Struct36 deriving(Eq, Bits);
typedef struct { Vector#(2, Struct1) m_dl_rss;  } Struct37 deriving(Eq, Bits);
typedef struct { Bit#(3) r_id; Struct1 r_msg; Bit#(3) r_msg_from;  } Struct38 deriving(Eq, Bits);
typedef struct { Bool s_has_slot; Bool s_conflict; Bit#(3) s_id;  } Struct39 deriving(Eq, Bits);
typedef struct { Bool s_has_slot; Bool s_conflict; Bit#(4) s_id;  } Struct4 deriving(Eq, Bits);
typedef struct { Bool ir_is_rs_rel; Struct1 ir_msg; Bit#(3) ir_msg_from; Bit#(3) ir_mshr_id; Struct10 ir_by_victim;  } Struct40 deriving(Eq, Bits);
typedef struct { Bit#(8) info_index; Bool info_hit; Bit#(2) info_way; Bool edir_hit; void edir_way; Struct42 edir_slot; Struct11 info; Struct12 may_victim; Vector#(4, Bit#(8)) reps;  } Struct41 deriving(Eq, Bits);
typedef struct { Bool valid; void data;  } Struct42 deriving(Eq, Bits);
typedef struct { Struct40 lr_ir_pp; Struct41 lr_ir; Vector#(4, Bit#(64)) lr_value;  } Struct43 deriving(Eq, Bits);
typedef struct { Bit#(3) m_status; Struct5 m_next; Bool m_is_ul; Bit#(64) m_addr; Bit#(3) m_qidx; Bool m_rsb; Bit#(2) m_dl_rss_from; Bit#(2) m_dl_rss_recv;  } Struct44 deriving(Eq, Bits);
typedef struct { Bit#(64) addr; Bool info_write; Bool info_hit; Bit#(2) info_way; Bool edir_hit; void edir_way; Struct42 edir_slot; Struct11 info; Bool value_write; Vector#(4, Bit#(64)) value; Struct12 may_victim; Vector#(4, Bit#(8)) reps;  } Struct45 deriving(Eq, Bits);
typedef struct { Bit#(3) r_id; Bool r_ul_rsb; Bit#(1) r_ul_rsbTo;  } Struct46 deriving(Eq, Bits);
typedef struct { Bit#(2) victim_idx; Struct11 victim_info; Vector#(4, Bit#(64)) victim_value;  } Struct47 deriving(Eq, Bits);
typedef struct { Bit#(51) tag; Struct11 value;  } Struct48 deriving(Eq, Bits);
typedef struct { Bool tm_hit; Bit#(2) tm_way; Struct11 tm_value;  } Struct49 deriving(Eq, Bits);
typedef struct { Bool valid; Bit#(3) data;  } Struct5 deriving(Eq, Bits);
typedef struct { Bit#(8) addr; Struct48 datain;  } Struct50 deriving(Eq, Bits);
typedef struct { Bit#(1) acc_type; Vector#(4, Bit#(8)) acc_reps; Bit#(8) acc_index; Bit#(2) acc_way;  } Struct51 deriving(Eq, Bits);
typedef struct { Bit#(10) addr; Vector#(4, Bit#(64)) datain;  } Struct52 deriving(Eq, Bits);
typedef struct { Bit#(8) addr; Vector#(4, Bit#(8)) datain;  } Struct53 deriving(Eq, Bits);
typedef struct { Bit#(3) r_id; Bit#(2) r_dl_rss_from; Bool r_dl_rsb; Bit#(3) r_dl_rsbTo;  } Struct54 deriving(Eq, Bits);
typedef struct { Bit#(3) r_id; Bit#(2) r_dl_rss_from;  } Struct55 deriving(Eq, Bits);
typedef struct { Bit#(3) r_id; Bit#(64) r_addr;  } Struct56 deriving(Eq, Bits);
typedef struct { Bool ir_is_rs_rel; Struct1 ir_msg; Bit#(3) ir_msg_from; Bit#(4) ir_mshr_id; Struct5 ir_by_victim;  } Struct6 deriving(Eq, Bits);
typedef struct { Bit#(1) r_midx; Struct1 r_msg;  } Struct7 deriving(Eq, Bits);
typedef struct { Bit#(4) r_id; Bit#(64) r_addr;  } Struct8 deriving(Eq, Bits);
typedef struct { Bit#(9) info_index; Bool info_hit; Bit#(3) info_way; Bool edir_hit; Bit#(2) edir_way; Struct10 edir_slot; Struct11 info; Struct12 may_victim; Vector#(8, Bit#(8)) reps;  } Struct9 deriving(Eq, Bits);

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
    method Action enq_fifoL2E_00 (Struct13 x_0);
    method ActionValue#(Struct13) deq_fifoL2E_00 ();
endinterface

module mkModule6 (Module6);
    FIFOF#(Struct13) pff <- mkPipelineFIFOF();

    method Action enq_fifoL2E_00 (Struct13 x_0);
        pff.enq(x_0);
    endmethod

    method ActionValue#(Struct13) deq_fifoL2E_00 ();
        pff.deq();
        return pff.first();
    endmethod

endmodule

interface Module7;
    method ActionValue#(Struct5) victims__00__findVictim (Bit#(64) x_0);
    method ActionValue#(Struct14) victims__00__getVictim (Bit#(3) x_0);
    method Action victims__00__setVictim (Struct19 x_0);
    method Action victims__00__registerVictim (Struct14 x_0);
    method ActionValue#(Struct14) victims__00__getFirstVictim ();
    method ActionValue#(Bool) victims__00__hasVictim ();
    method Action victims__00__setVictimRq (Bit#(64) x_0);
    method Action victims__00__releaseVictim (Bit#(64) x_0);
endinterface

module mkModule7
    (Module7);
    Reg#(Vector#(8, Struct14)) victimRegs__00 <- mkReg(unpack(0));

    // No rules in this module

    method ActionValue#(Struct5) victims__00__findVictim (Bit#(64) x_0);
        let x_1 = (victimRegs__00);
        Struct14 x_2 =
        ((x_1)[(Bit#(3))'(3'h0)]);
        let x_17 = ?;
        if (((x_2).victim_valid) && (((x_2).victim_addr) == (x_0))) begin
            x_17 = Struct5 {valid : (Bool)'(True), data : (Bit#(3))'(3'h0)};
        end else begin
            Struct14 x_3 =
            ((x_1)[(Bit#(3))'(3'h1)]);
            let x_16 = ?;
            if (((x_3).victim_valid) && (((x_3).victim_addr) == (x_0)))
                begin
                x_16 = Struct5 {valid : (Bool)'(True), data :
                (Bit#(3))'(3'h1)};
            end else begin
                Struct14 x_4 =
                ((x_1)[(Bit#(3))'(3'h2)]);
                let x_15 = ?;
                if (((x_4).victim_valid) && (((x_4).victim_addr) == (x_0)))
                    begin
                    x_15 = Struct5 {valid : (Bool)'(True), data :
                    (Bit#(3))'(3'h2)};
                end else begin
                    Struct14 x_5 =
                    ((x_1)[(Bit#(3))'(3'h3)]);
                    let x_14 = ?;
                    if (((x_5).victim_valid) && (((x_5).victim_addr) ==
                        (x_0))) begin
                        x_14 = Struct5 {valid : (Bool)'(True), data :
                        (Bit#(3))'(3'h3)};
                    end else begin
                        Struct14 x_6 =
                        ((x_1)[(Bit#(3))'(3'h4)]);
                        let x_13 = ?;
                        if (((x_6).victim_valid) && (((x_6).victim_addr) ==
                            (x_0))) begin
                            x_13 = Struct5 {valid : (Bool)'(True), data :
                            (Bit#(3))'(3'h4)};
                        end else begin
                            Struct14 x_7 =
                            ((x_1)[(Bit#(3))'(3'h5)]);
                            let x_12 = ?;
                            if (((x_7).victim_valid) && (((x_7).victim_addr)
                                == (x_0))) begin
                                x_12 = Struct5 {valid : (Bool)'(True), data :
                                (Bit#(3))'(3'h5)};
                            end else begin
                                Struct14 x_8 =
                                ((x_1)[(Bit#(3))'(3'h6)]);
                                let x_11 = ?;
                                if (((x_8).victim_valid) &&
                                    (((x_8).victim_addr) == (x_0))) begin
                                    x_11 = Struct5 {valid : (Bool)'(True),
                                    data : (Bit#(3))'(3'h6)};
                                end else begin
                                    Struct14 x_9 =
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

    method ActionValue#(Struct14) victims__00__getVictim (Bit#(3) x_0);
        let x_1 = (victimRegs__00);
        return (x_1)[x_0];
    endmethod

    method Action victims__00__setVictim (Struct19 x_0);
        let x_1 = (victimRegs__00);
        Struct14 x_2 = ((x_1)[(x_0).victim_idx]);
        Struct14 x_3 = (Struct14 {victim_valid : (Bool)'(True), victim_addr :
        (x_2).victim_addr, victim_info : (x_0).victim_info, victim_value :
        (x_0).victim_value, victim_req : (x_2).victim_req});
        victimRegs__00 <= update (x_1, (x_0).victim_idx, x_3);
    endmethod

    method Action victims__00__registerVictim (Struct14 x_0);
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

    method ActionValue#(Struct14) victims__00__getFirstVictim ();
        let x_1 = (victimRegs__00);
        Struct35 x_2 = (((((x_1)[(Bit#(3))'(3'h7)]).victim_valid) && (!
        (((x_1)[(Bit#(3))'(3'h7)]).victim_req)) ? (Struct35 {valid :
        (Bool)'(True), data : (x_1)[(Bit#(3))'(3'h7)]}) :
        (((((x_1)[(Bit#(3))'(3'h6)]).victim_valid) && (!
        (((x_1)[(Bit#(3))'(3'h6)]).victim_req)) ? (Struct35 {valid :
        (Bool)'(True), data : (x_1)[(Bit#(3))'(3'h6)]}) :
        (((((x_1)[(Bit#(3))'(3'h5)]).victim_valid) && (!
        (((x_1)[(Bit#(3))'(3'h5)]).victim_req)) ? (Struct35 {valid :
        (Bool)'(True), data : (x_1)[(Bit#(3))'(3'h5)]}) :
        (((((x_1)[(Bit#(3))'(3'h4)]).victim_valid) && (!
        (((x_1)[(Bit#(3))'(3'h4)]).victim_req)) ? (Struct35 {valid :
        (Bool)'(True), data : (x_1)[(Bit#(3))'(3'h4)]}) :
        (((((x_1)[(Bit#(3))'(3'h3)]).victim_valid) && (!
        (((x_1)[(Bit#(3))'(3'h3)]).victim_req)) ? (Struct35 {valid :
        (Bool)'(True), data : (x_1)[(Bit#(3))'(3'h3)]}) :
        (((((x_1)[(Bit#(3))'(3'h2)]).victim_valid) && (!
        (((x_1)[(Bit#(3))'(3'h2)]).victim_req)) ? (Struct35 {valid :
        (Bool)'(True), data : (x_1)[(Bit#(3))'(3'h2)]}) :
        (((((x_1)[(Bit#(3))'(3'h1)]).victim_valid) && (!
        (((x_1)[(Bit#(3))'(3'h1)]).victim_req)) ? (Struct35 {valid :
        (Bool)'(True), data : (x_1)[(Bit#(3))'(3'h1)]}) :
        (((((x_1)[(Bit#(3))'(3'h0)]).victim_valid) && (!
        (((x_1)[(Bit#(3))'(3'h0)]).victim_req)) ? (Struct35 {valid :
        (Bool)'(True), data : (x_1)[(Bit#(3))'(3'h0)]}) : (Struct35 {valid :
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
        Struct14 x_2 =
        ((x_1)[(Bit#(3))'(3'h7)]);
        if (((x_2).victim_valid) && (((x_2).victim_addr) == (x_0)))
            begin
            Struct14 x_3 = (Struct14 {victim_valid : (x_2).victim_valid,
            victim_addr : (x_2).victim_addr, victim_info : (x_2).victim_info,
            victim_value : (x_2).victim_value, victim_req :
            (Bool)'(True)});
            victimRegs__00 <= update (x_1, (Bit#(3))'(3'h7), x_3);
        end else begin
            Struct14 x_4 =
            ((x_1)[(Bit#(3))'(3'h6)]);
            if (((x_4).victim_valid) && (((x_4).victim_addr) == (x_0)))
                begin
                Struct14 x_5 = (Struct14 {victim_valid : (x_4).victim_valid,
                victim_addr : (x_4).victim_addr, victim_info :
                (x_4).victim_info, victim_value : (x_4).victim_value,
                victim_req : (Bool)'(True)});
                victimRegs__00 <= update (x_1, (Bit#(3))'(3'h6), x_5);
            end else begin
                Struct14 x_6 =
                ((x_1)[(Bit#(3))'(3'h5)]);
                if (((x_6).victim_valid) && (((x_6).victim_addr) == (x_0)))
                    begin
                    Struct14 x_7 = (Struct14 {victim_valid :
                    (x_6).victim_valid, victim_addr : (x_6).victim_addr,
                    victim_info : (x_6).victim_info, victim_value :
                    (x_6).victim_value, victim_req :
                    (Bool)'(True)});
                    victimRegs__00 <= update (x_1, (Bit#(3))'(3'h5), x_7);
                end else begin
                    Struct14 x_8 =
                    ((x_1)[(Bit#(3))'(3'h4)]);
                    if (((x_8).victim_valid) && (((x_8).victim_addr) ==
                        (x_0))) begin
                        Struct14 x_9 = (Struct14 {victim_valid :
                        (x_8).victim_valid, victim_addr : (x_8).victim_addr,
                        victim_info : (x_8).victim_info, victim_value :
                        (x_8).victim_value, victim_req :
                        (Bool)'(True)});
                        victimRegs__00 <= update (x_1, (Bit#(3))'(3'h4),
                        x_9);
                    end else begin
                        Struct14 x_10 =
                        ((x_1)[(Bit#(3))'(3'h3)]);
                        if (((x_10).victim_valid) && (((x_10).victim_addr) ==
                            (x_0))) begin
                            Struct14 x_11 = (Struct14 {victim_valid :
                            (x_10).victim_valid, victim_addr :
                            (x_10).victim_addr, victim_info :
                            (x_10).victim_info, victim_value :
                            (x_10).victim_value, victim_req :
                            (Bool)'(True)});
                            victimRegs__00 <= update (x_1, (Bit#(3))'(3'h3),
                            x_11);
                        end else begin
                            Struct14 x_12 =
                            ((x_1)[(Bit#(3))'(3'h2)]);
                            if (((x_12).victim_valid) &&
                                (((x_12).victim_addr) == (x_0)))
                                begin
                                Struct14 x_13 = (Struct14 {victim_valid :
                                (x_12).victim_valid, victim_addr :
                                (x_12).victim_addr, victim_info :
                                (x_12).victim_info, victim_value :
                                (x_12).victim_value, victim_req :
                                (Bool)'(True)});
                                victimRegs__00 <= update (x_1,
                                (Bit#(3))'(3'h2), x_13);
                            end else begin
                                Struct14 x_14 =
                                ((x_1)[(Bit#(3))'(3'h1)]);
                                if (((x_14).victim_valid) &&
                                    (((x_14).victim_addr) == (x_0)))
                                    begin
                                    Struct14 x_15 = (Struct14 {victim_valid :
                                    (x_14).victim_valid, victim_addr :
                                    (x_14).victim_addr, victim_info :
                                    (x_14).victim_info, victim_value :
                                    (x_14).victim_value, victim_req :
                                    (Bool)'(True)});
                                    victimRegs__00 <= update (x_1,
                                    (Bit#(3))'(3'h1), x_15);
                                end else begin
                                    Struct14 x_16 =
                                    ((x_1)[(Bit#(3))'(3'h0)]);
                                    if (((x_16).victim_valid) &&
                                        (((x_16).victim_addr) == (x_0)))
                                        begin
                                        Struct14 x_17 = (Struct14
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
        Struct14 x_2 =
        ((x_1)[(Bit#(3))'(3'h0)]);
        if (((x_2).victim_valid) && (((x_2).victim_addr) == (x_0)))
            begin
            victimRegs__00 <= update (x_1, (Bit#(3))'(3'h0), unpack(0));
        end else begin
            Struct14 x_3 =
            ((x_1)[(Bit#(3))'(3'h1)]);
            if (((x_3).victim_valid) && (((x_3).victim_addr) == (x_0)))
                begin
                victimRegs__00 <= update (x_1, (Bit#(3))'(3'h1), unpack(0));
            end else begin
                Struct14 x_4 =
                ((x_1)[(Bit#(3))'(3'h2)]);
                if (((x_4).victim_valid) && (((x_4).victim_addr) == (x_0)))
                    begin
                    victimRegs__00 <= update (x_1, (Bit#(3))'(3'h2),
                    unpack(0));
                end else begin
                    Struct14 x_5 =
                    ((x_1)[(Bit#(3))'(3'h3)]);
                    if (((x_5).victim_valid) && (((x_5).victim_addr) ==
                        (x_0))) begin
                        victimRegs__00 <= update (x_1, (Bit#(3))'(3'h3),
                        unpack(0));
                    end else begin
                        Struct14 x_6 =
                        ((x_1)[(Bit#(3))'(3'h4)]);
                        if (((x_6).victim_valid) && (((x_6).victim_addr) ==
                            (x_0))) begin
                            victimRegs__00 <= update (x_1, (Bit#(3))'(3'h4),
                            unpack(0));
                        end else begin
                            Struct14 x_7 =
                            ((x_1)[(Bit#(3))'(3'h5)]);
                            if (((x_7).victim_valid) && (((x_7).victim_addr)
                                == (x_0))) begin
                                victimRegs__00 <= update (x_1,
                                (Bit#(3))'(3'h5), unpack(0));
                            end else begin
                                Struct14 x_8 =
                                ((x_1)[(Bit#(3))'(3'h6)]);
                                if (((x_8).victim_valid) &&
                                    (((x_8).victim_addr) == (x_0)))
                                    begin
                                    victimRegs__00 <= update (x_1,
                                    (Bit#(3))'(3'h6), unpack(0));
                                end else begin
                                    Struct14 x_9 =
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
    method Action rdReq_infoRam__00__7 (Bit#(9) x_0);
    method Action wrReq_infoRam__00__7 (Struct31 x_0);
    method ActionValue#(Struct26) rdResp_infoRam__00__7 ();
endinterface

module mkModule8 (Module8);
    RWBramCore#(Bit#(9), Struct26) bram <- mkRWBramCore();
    Reg#(Bool) initDone <- mkReg(False);
    Reg#(Bit#(9)) initIdx <- mkReg(0);

    rule init (!initDone);
        let initData = Struct26 {tag: 50'hf, value: Struct11 {mesi_owned: False, mesi_status: 3'h1, mesi_dir_st: 3'h1, mesi_dir_sharers: 2'h0}};
        bram.wrReq(initIdx, initData);
        initIdx <= initIdx + 1;
        initDone <= (initIdx == maxBound);
    endrule

    method Action rdReq_infoRam__00__7 (Bit#(9) x_0) if(initDone);
        bram.rdReq(x_0);
    endmethod

    method Action wrReq_infoRam__00__7 (Struct31 x_0) if(initDone);
        bram.wrReq(x_0.addr, x_0.datain);
    endmethod

    method ActionValue#(Struct26) rdResp_infoRam__00__7 () if(initDone);
        bram.deqRdResp ();
        let data = bram.rdResp ();
        return data;
    endmethod


endmodule

interface Module9;
    method Action rdReq_infoRam__00__6 (Bit#(9) x_0);
    method Action wrReq_infoRam__00__6 (Struct31 x_0);
    method ActionValue#(Struct26) rdResp_infoRam__00__6 ();
endinterface

module mkModule9 (Module9);
    RWBramCore#(Bit#(9), Struct26) bram <- mkRWBramCore();
    Reg#(Bool) initDone <- mkReg(False);
    Reg#(Bit#(9)) initIdx <- mkReg(0);

    rule init (!initDone);
        let initData = Struct26 {tag: 50'he, value: Struct11 {mesi_owned: False, mesi_status: 3'h1, mesi_dir_st: 3'h1, mesi_dir_sharers: 2'h0}};
        bram.wrReq(initIdx, initData);
        initIdx <= initIdx + 1;
        initDone <= (initIdx == maxBound);
    endrule

    method Action rdReq_infoRam__00__6 (Bit#(9) x_0) if(initDone);
        bram.rdReq(x_0);
    endmethod

    method Action wrReq_infoRam__00__6 (Struct31 x_0) if(initDone);
        bram.wrReq(x_0.addr, x_0.datain);
    endmethod

    method ActionValue#(Struct26) rdResp_infoRam__00__6 () if(initDone);
        bram.deqRdResp ();
        let data = bram.rdResp ();
        return data;
    endmethod


endmodule

interface Module10;
    method Action rdReq_infoRam__00__5 (Bit#(9) x_0);
    method Action wrReq_infoRam__00__5 (Struct31 x_0);
    method ActionValue#(Struct26) rdResp_infoRam__00__5 ();
endinterface

module mkModule10 (Module10);
    RWBramCore#(Bit#(9), Struct26) bram <- mkRWBramCore();
    Reg#(Bool) initDone <- mkReg(False);
    Reg#(Bit#(9)) initIdx <- mkReg(0);

    rule init (!initDone);
        let initData = Struct26 {tag: 50'hd, value: Struct11 {mesi_owned: False, mesi_status: 3'h1, mesi_dir_st: 3'h1, mesi_dir_sharers: 2'h0}};
        bram.wrReq(initIdx, initData);
        initIdx <= initIdx + 1;
        initDone <= (initIdx == maxBound);
    endrule

    method Action rdReq_infoRam__00__5 (Bit#(9) x_0) if(initDone);
        bram.rdReq(x_0);
    endmethod

    method Action wrReq_infoRam__00__5 (Struct31 x_0) if(initDone);
        bram.wrReq(x_0.addr, x_0.datain);
    endmethod

    method ActionValue#(Struct26) rdResp_infoRam__00__5 () if(initDone);
        bram.deqRdResp ();
        let data = bram.rdResp ();
        return data;
    endmethod


endmodule

interface Module11;
    method Action rdReq_infoRam__00__4 (Bit#(9) x_0);
    method Action wrReq_infoRam__00__4 (Struct31 x_0);
    method ActionValue#(Struct26) rdResp_infoRam__00__4 ();
endinterface

module mkModule11 (Module11);
    RWBramCore#(Bit#(9), Struct26) bram <- mkRWBramCore();
    Reg#(Bool) initDone <- mkReg(False);
    Reg#(Bit#(9)) initIdx <- mkReg(0);

    rule init (!initDone);
        let initData = Struct26 {tag: 50'hc, value: Struct11 {mesi_owned: False, mesi_status: 3'h1, mesi_dir_st: 3'h1, mesi_dir_sharers: 2'h0}};
        bram.wrReq(initIdx, initData);
        initIdx <= initIdx + 1;
        initDone <= (initIdx == maxBound);
    endrule

    method Action rdReq_infoRam__00__4 (Bit#(9) x_0) if(initDone);
        bram.rdReq(x_0);
    endmethod

    method Action wrReq_infoRam__00__4 (Struct31 x_0) if(initDone);
        bram.wrReq(x_0.addr, x_0.datain);
    endmethod

    method ActionValue#(Struct26) rdResp_infoRam__00__4 () if(initDone);
        bram.deqRdResp ();
        let data = bram.rdResp ();
        return data;
    endmethod


endmodule

interface Module12;
    method Action rdReq_infoRam__00__3 (Bit#(9) x_0);
    method Action wrReq_infoRam__00__3 (Struct31 x_0);
    method ActionValue#(Struct26) rdResp_infoRam__00__3 ();
endinterface

module mkModule12 (Module12);
    RWBramCore#(Bit#(9), Struct26) bram <- mkRWBramCore();
    Reg#(Bool) initDone <- mkReg(False);
    Reg#(Bit#(9)) initIdx <- mkReg(0);

    rule init (!initDone);
        let initData = Struct26 {tag: 50'hb, value: Struct11 {mesi_owned: False, mesi_status: 3'h1, mesi_dir_st: 3'h1, mesi_dir_sharers: 2'h0}};
        bram.wrReq(initIdx, initData);
        initIdx <= initIdx + 1;
        initDone <= (initIdx == maxBound);
    endrule

    method Action rdReq_infoRam__00__3 (Bit#(9) x_0) if(initDone);
        bram.rdReq(x_0);
    endmethod

    method Action wrReq_infoRam__00__3 (Struct31 x_0) if(initDone);
        bram.wrReq(x_0.addr, x_0.datain);
    endmethod

    method ActionValue#(Struct26) rdResp_infoRam__00__3 () if(initDone);
        bram.deqRdResp ();
        let data = bram.rdResp ();
        return data;
    endmethod


endmodule

interface Module13;
    method Action rdReq_infoRam__00__2 (Bit#(9) x_0);
    method Action wrReq_infoRam__00__2 (Struct31 x_0);
    method ActionValue#(Struct26) rdResp_infoRam__00__2 ();
endinterface

module mkModule13 (Module13);
    RWBramCore#(Bit#(9), Struct26) bram <- mkRWBramCore();
    Reg#(Bool) initDone <- mkReg(False);
    Reg#(Bit#(9)) initIdx <- mkReg(0);

    rule init (!initDone);
        let initData = Struct26 {tag: 50'ha, value: Struct11 {mesi_owned: False, mesi_status: 3'h1, mesi_dir_st: 3'h1, mesi_dir_sharers: 2'h0}};
        bram.wrReq(initIdx, initData);
        initIdx <= initIdx + 1;
        initDone <= (initIdx == maxBound);
    endrule

    method Action rdReq_infoRam__00__2 (Bit#(9) x_0) if(initDone);
        bram.rdReq(x_0);
    endmethod

    method Action wrReq_infoRam__00__2 (Struct31 x_0) if(initDone);
        bram.wrReq(x_0.addr, x_0.datain);
    endmethod

    method ActionValue#(Struct26) rdResp_infoRam__00__2 () if(initDone);
        bram.deqRdResp ();
        let data = bram.rdResp ();
        return data;
    endmethod


endmodule

interface Module14;
    method Action rdReq_infoRam__00__1 (Bit#(9) x_0);
    method Action wrReq_infoRam__00__1 (Struct31 x_0);
    method ActionValue#(Struct26) rdResp_infoRam__00__1 ();
endinterface

module mkModule14 (Module14);
    RWBramCore#(Bit#(9), Struct26) bram <- mkRWBramCore();
    Reg#(Bool) initDone <- mkReg(False);
    Reg#(Bit#(9)) initIdx <- mkReg(0);

    rule init (!initDone);
        let initData = Struct26 {tag: 50'h9, value: Struct11 {mesi_owned: False, mesi_status: 3'h1, mesi_dir_st: 3'h1, mesi_dir_sharers: 2'h0}};
        bram.wrReq(initIdx, initData);
        initIdx <= initIdx + 1;
        initDone <= (initIdx == maxBound);
    endrule

    method Action rdReq_infoRam__00__1 (Bit#(9) x_0) if(initDone);
        bram.rdReq(x_0);
    endmethod

    method Action wrReq_infoRam__00__1 (Struct31 x_0) if(initDone);
        bram.wrReq(x_0.addr, x_0.datain);
    endmethod

    method ActionValue#(Struct26) rdResp_infoRam__00__1 () if(initDone);
        bram.deqRdResp ();
        let data = bram.rdResp ();
        return data;
    endmethod


endmodule

interface Module15;
    method Action rdReq_infoRam__00__0 (Bit#(9) x_0);
    method Action wrReq_infoRam__00__0 (Struct31 x_0);
    method ActionValue#(Struct26) rdResp_infoRam__00__0 ();
endinterface

module mkModule15 (Module15);
    RWBramCore#(Bit#(9), Struct26) bram <- mkRWBramCore();
    Reg#(Bool) initDone <- mkReg(False);
    Reg#(Bit#(9)) initIdx <- mkReg(0);

    rule init (!initDone);
        let initData = Struct26 {tag: 50'h8, value: Struct11 {mesi_owned: False, mesi_status: 3'h1, mesi_dir_st: 3'h1, mesi_dir_sharers: 2'h0}};
        bram.wrReq(initIdx, initData);
        initIdx <= initIdx + 1;
        initDone <= (initIdx == maxBound);
    endrule

    method Action rdReq_infoRam__00__0 (Bit#(9) x_0) if(initDone);
        bram.rdReq(x_0);
    endmethod

    method Action wrReq_infoRam__00__0 (Struct31 x_0) if(initDone);
        bram.wrReq(x_0.addr, x_0.datain);
    endmethod

    method ActionValue#(Struct26) rdResp_infoRam__00__0 () if(initDone);
        bram.deqRdResp ();
        let data = bram.rdResp ();
        return data;
    endmethod


endmodule

interface Module16;
    method Action rdReq_edirRam__00__3 (Bit#(9) x_0);
    method Action wrReq_edirRam__00__3 (Struct33 x_0);
    method ActionValue#(Struct28) rdResp_edirRam__00__3 ();
endinterface

module mkModule16 (Module16);
    RWBramCore#(Bit#(9), Struct28) bram <- mkRWBramCore();
    Reg#(Bool) initDone <- mkReg(False);
    Reg#(Bit#(9)) initIdx <- mkReg(0);

    rule init (!initDone);
        let initData = Struct28 {tag: 50'h13, value: Struct29 {mesi_edir_owned: False, mesi_edir_st: 3'h1, mesi_edir_sharers: 2'h0}};
        bram.wrReq(initIdx, initData);
        initIdx <= initIdx + 1;
        initDone <= (initIdx == maxBound);
    endrule

    method Action rdReq_edirRam__00__3 (Bit#(9) x_0) if(initDone);
        bram.rdReq(x_0);
    endmethod

    method Action wrReq_edirRam__00__3 (Struct33 x_0) if(initDone);
        bram.wrReq(x_0.addr, x_0.datain);
    endmethod

    method ActionValue#(Struct28) rdResp_edirRam__00__3 () if(initDone);
        bram.deqRdResp ();
        let data = bram.rdResp ();
        return data;
    endmethod


endmodule

interface Module17;
    method Action rdReq_edirRam__00__2 (Bit#(9) x_0);
    method Action wrReq_edirRam__00__2 (Struct33 x_0);
    method ActionValue#(Struct28) rdResp_edirRam__00__2 ();
endinterface

module mkModule17 (Module17);
    RWBramCore#(Bit#(9), Struct28) bram <- mkRWBramCore();
    Reg#(Bool) initDone <- mkReg(False);
    Reg#(Bit#(9)) initIdx <- mkReg(0);

    rule init (!initDone);
        let initData = Struct28 {tag: 50'h12, value: Struct29 {mesi_edir_owned: False, mesi_edir_st: 3'h1, mesi_edir_sharers: 2'h0}};
        bram.wrReq(initIdx, initData);
        initIdx <= initIdx + 1;
        initDone <= (initIdx == maxBound);
    endrule

    method Action rdReq_edirRam__00__2 (Bit#(9) x_0) if(initDone);
        bram.rdReq(x_0);
    endmethod

    method Action wrReq_edirRam__00__2 (Struct33 x_0) if(initDone);
        bram.wrReq(x_0.addr, x_0.datain);
    endmethod

    method ActionValue#(Struct28) rdResp_edirRam__00__2 () if(initDone);
        bram.deqRdResp ();
        let data = bram.rdResp ();
        return data;
    endmethod


endmodule

interface Module18;
    method Action rdReq_edirRam__00__1 (Bit#(9) x_0);
    method Action wrReq_edirRam__00__1 (Struct33 x_0);
    method ActionValue#(Struct28) rdResp_edirRam__00__1 ();
endinterface

module mkModule18 (Module18);
    RWBramCore#(Bit#(9), Struct28) bram <- mkRWBramCore();
    Reg#(Bool) initDone <- mkReg(False);
    Reg#(Bit#(9)) initIdx <- mkReg(0);

    rule init (!initDone);
        let initData = Struct28 {tag: 50'h11, value: Struct29 {mesi_edir_owned: False, mesi_edir_st: 3'h1, mesi_edir_sharers: 2'h0}};
        bram.wrReq(initIdx, initData);
        initIdx <= initIdx + 1;
        initDone <= (initIdx == maxBound);
    endrule

    method Action rdReq_edirRam__00__1 (Bit#(9) x_0) if(initDone);
        bram.rdReq(x_0);
    endmethod

    method Action wrReq_edirRam__00__1 (Struct33 x_0) if(initDone);
        bram.wrReq(x_0.addr, x_0.datain);
    endmethod

    method ActionValue#(Struct28) rdResp_edirRam__00__1 () if(initDone);
        bram.deqRdResp ();
        let data = bram.rdResp ();
        return data;
    endmethod


endmodule

interface Module19;
    method Action rdReq_edirRam__00__0 (Bit#(9) x_0);
    method Action wrReq_edirRam__00__0 (Struct33 x_0);
    method ActionValue#(Struct28) rdResp_edirRam__00__0 ();
endinterface

module mkModule19 (Module19);
    RWBramCore#(Bit#(9), Struct28) bram <- mkRWBramCore();
    Reg#(Bool) initDone <- mkReg(False);
    Reg#(Bit#(9)) initIdx <- mkReg(0);

    rule init (!initDone);
        let initData = Struct28 {tag: 50'h10, value: Struct29 {mesi_edir_owned: False, mesi_edir_st: 3'h1, mesi_edir_sharers: 2'h0}};
        bram.wrReq(initIdx, initData);
        initIdx <= initIdx + 1;
        initDone <= (initIdx == maxBound);
    endrule

    method Action rdReq_edirRam__00__0 (Bit#(9) x_0) if(initDone);
        bram.rdReq(x_0);
    endmethod

    method Action wrReq_edirRam__00__0 (Struct33 x_0) if(initDone);
        bram.wrReq(x_0.addr, x_0.datain);
    endmethod

    method ActionValue#(Struct28) rdResp_edirRam__00__0 () if(initDone);
        bram.deqRdResp ();
        let data = bram.rdResp ();
        return data;
    endmethod


endmodule

interface Module20;
    method Action rdReq_dataRam__00 (Bit#(12) x_0);
    method Action wrReq_dataRam__00 (Struct34 x_0);
    method ActionValue#(Vector#(4, Bit#(64))) rdResp_dataRam__00 ();
endinterface

module mkModule20 (Module20);
    RWBramCore#(Bit#(12), Vector#(4, Bit#(64))) bram <- mkRWBramCore();
    Reg#(Bool) initDone <- mkReg(False);
    Reg#(Bit#(12)) initIdx <- mkReg(0);

    rule init (!initDone);
        let initData = vec(64'h0, 64'h0, 64'h0, 64'h0);
        bram.wrReq(initIdx, initData);
        initIdx <= initIdx + 1;
        initDone <= (initIdx == maxBound);
    endrule

    method Action rdReq_dataRam__00 (Bit#(12) x_0) if(initDone);
        bram.rdReq(x_0);
    endmethod

    method Action wrReq_dataRam__00 (Struct34 x_0) if(initDone);
        bram.wrReq(x_0.addr, x_0.datain);
    endmethod

    method ActionValue#(Vector#(4, Bit#(64))) rdResp_dataRam__00 ()
    if(initDone);
        bram.deqRdResp ();
        let data = bram.rdResp ();
        return data;
    endmethod


endmodule

interface Module21;
    method Action rdReq_repRam__00 (Bit#(9) x_0);
    method Action wrReq_repRam__00 (Struct36 x_0);
    method ActionValue#(Vector#(8, Bit#(8))) rdResp_repRam__00 ();
endinterface

module mkModule21 (Module21);
    RWBramCore#(Bit#(9), Vector#(8, Bit#(8))) bram <- mkRWBramCore();
    Reg#(Bool) initDone <- mkReg(False);
    Reg#(Bit#(9)) initIdx <- mkReg(0);

    rule init (!initDone);
        let initData = vec(8'h1, 8'h1, 8'h1, 8'h1, 8'h1, 8'h1, 8'h1, 8'h1);
        bram.wrReq(initIdx, initData);
        initIdx <= initIdx + 1;
        initDone <= (initIdx == maxBound);
    endrule

    method Action rdReq_repRam__00 (Bit#(9) x_0) if(initDone);
        bram.rdReq(x_0);
    endmethod

    method Action wrReq_repRam__00 (Struct36 x_0) if(initDone);
        bram.wrReq(x_0.addr, x_0.datain);
    endmethod

    method ActionValue#(Vector#(8, Bit#(8))) rdResp_repRam__00 ()
    if(initDone);
        bram.deqRdResp ();
        let data = bram.rdResp ();
        return data;
    endmethod


endmodule

interface Module22;
    method ActionValue#(Struct15) getMSHR_00 (Bit#(4) x_0);
    method ActionValue#(Struct1) getMSHRRq_00 (Bit#(4) x_0);
    method ActionValue#(Struct1) getMSHRFirstRs_00 (Bit#(4) x_0);
    method ActionValue#(Struct4) getPRqSlot_00 (Struct3 x_0);
    method ActionValue#(Struct4) getCRqSlot_00 (Struct3 x_0);
    method ActionValue#(Struct3) getWait_00 ();
    method Action registerUL_00 (Struct21 x_0);
    method Action registerDL_00 (Struct22 x_0);
    method Action canImm_00 (Bit#(64) x_0);
    method Action setULImm_00 (Struct1 x_0);
    method Action transferUpDown_00 (Struct25 x_0);
    method Action addRs_00 (Struct7 x_0);
    method ActionValue#(Bit#(4)) getULReady_00 (Bit#(64) x_0);
    method ActionValue#(Struct8) getDLReady_00 ();
    method Action startRelease_00 (Bit#(4) x_0);
    method Action releaseMSHR_00 (Bit#(4) x_0);
endinterface

module mkModule22
    (Module22);
    Reg#(Vector#(12, Struct15)) mshrs_00 <- mkReg(unpack(0));
    Reg#(Vector#(12, Struct1)) rqs_00 <- mkReg(unpack(0));
    Reg#(Vector#(12, Struct37)) rss_00 <- mkReg(unpack(0));

    // No rules in this module

    method ActionValue#(Struct15) getMSHR_00 (Bit#(4) x_0);
        let x_1 = (mshrs_00);
        return (x_1)[x_0];
    endmethod

    method ActionValue#(Struct1) getMSHRRq_00 (Bit#(4) x_0);
        let x_1 = (rqs_00);
        return (x_1)[x_0];
    endmethod

    method ActionValue#(Struct1) getMSHRFirstRs_00 (Bit#(4) x_0);
        let x_1 = (mshrs_00);
        Struct15 x_2 = ((x_1)[x_0]);
        Bit#(2) x_3 = ((x_2).m_dl_rss_recv);
        Bit#(1) x_4 = ((((x_3)[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(1))'(1'h0)) : (((Bit#(1))'(1'h1)) + (((((x_3)[1:1])[0:0]) ==
        ((Bit#(1))'(1'h1)) ? ((Bit#(1))'(1'h0)) : (((Bit#(1))'(1'h1)) +
        (unpack(0))))))));
        let x_5 = (rss_00);
        Struct37 x_6 = ((x_5)[x_0]);
        Struct1 x_7 = (((x_6).m_dl_rss)[x_4]);
        return x_7;
    endmethod

    method ActionValue#(Struct4) getPRqSlot_00 (Struct3 x_0);
        let x_1 = (mshrs_00);
        Struct16 x_2 = (((((x_1)[(Bit#(4))'(4'h0)]).m_status) ==
        ((Bit#(3))'(3'h0)) ? (Struct16 {valid : (Bool)'(True), data :
        (Bit#(4))'(4'h0)}) : (((((x_1)[(Bit#(4))'(4'h1)]).m_status) ==
        ((Bit#(3))'(3'h0)) ? (Struct16 {valid : (Bool)'(True), data :
        (Bit#(4))'(4'h1)}) : (((((x_1)[(Bit#(4))'(4'h2)]).m_status) ==
        ((Bit#(3))'(3'h0)) ? (Struct16 {valid : (Bool)'(True), data :
        (Bit#(4))'(4'h2)}) : (((((x_1)[(Bit#(4))'(4'h3)]).m_status) ==
        ((Bit#(3))'(3'h0)) ? (Struct16 {valid : (Bool)'(True), data :
        (Bit#(4))'(4'h3)}) : (Struct16 {valid : (Bool)'(False), data :
        unpack(0)})))))))));
        Bool x_3 = ((x_2).valid);
        Bit#(4) x_4 = ((x_2).data);
        Bit#(64) x_5 = (((x_0).r_msg).addr);
        Bool x_6 = (((((((x_1)[(Bit#(4))'(4'h0)]).m_status) ==
        ((Bit#(3))'(3'h4))) || ((((x_1)[(Bit#(4))'(4'h0)]).m_status) ==
        ((Bit#(3))'(3'h6)))) && (((! ((((x_1)[(Bit#(4))'(4'h0)]).m_addr) ==
        (x_5))) && (((((x_1)[(Bit#(4))'(4'h0)]).m_addr)[13:5]) ==
        ((x_5)[13:5]))) || ((((x_1)[(Bit#(4))'(4'h0)]).m_addr) == (x_5))) ?
        ((Bool)'(True)) : (((((((x_1)[(Bit#(4))'(4'h1)]).m_status) ==
        ((Bit#(3))'(3'h4))) || ((((x_1)[(Bit#(4))'(4'h1)]).m_status) ==
        ((Bit#(3))'(3'h6)))) && (((! ((((x_1)[(Bit#(4))'(4'h1)]).m_addr) ==
        (x_5))) && (((((x_1)[(Bit#(4))'(4'h1)]).m_addr)[13:5]) ==
        ((x_5)[13:5]))) || ((((x_1)[(Bit#(4))'(4'h1)]).m_addr) == (x_5))) ?
        ((Bool)'(True)) : (((((((x_1)[(Bit#(4))'(4'h2)]).m_status) ==
        ((Bit#(3))'(3'h4))) || ((((x_1)[(Bit#(4))'(4'h2)]).m_status) ==
        ((Bit#(3))'(3'h6)))) && (((! ((((x_1)[(Bit#(4))'(4'h2)]).m_addr) ==
        (x_5))) && (((((x_1)[(Bit#(4))'(4'h2)]).m_addr)[13:5]) ==
        ((x_5)[13:5]))) || ((((x_1)[(Bit#(4))'(4'h2)]).m_addr) == (x_5))) ?
        ((Bool)'(True)) : (((((((x_1)[(Bit#(4))'(4'h3)]).m_status) ==
        ((Bit#(3))'(3'h4))) || ((((x_1)[(Bit#(4))'(4'h3)]).m_status) ==
        ((Bit#(3))'(3'h6)))) && (((! ((((x_1)[(Bit#(4))'(4'h3)]).m_addr) ==
        (x_5))) && (((((x_1)[(Bit#(4))'(4'h3)]).m_addr)[13:5]) ==
        ((x_5)[13:5]))) || ((((x_1)[(Bit#(4))'(4'h3)]).m_addr) == (x_5))) ?
        ((Bool)'(True)) : (((((((x_1)[(Bit#(4))'(4'h4)]).m_status) ==
        ((Bit#(3))'(3'h4))) || ((((x_1)[(Bit#(4))'(4'h4)]).m_status) ==
        ((Bit#(3))'(3'h6)))) && (((! ((((x_1)[(Bit#(4))'(4'h4)]).m_addr) ==
        (x_5))) && (((((x_1)[(Bit#(4))'(4'h4)]).m_addr)[13:5]) ==
        ((x_5)[13:5]))) || ((((x_1)[(Bit#(4))'(4'h4)]).m_addr) == (x_5))) ?
        ((Bool)'(True)) : (((((((x_1)[(Bit#(4))'(4'h5)]).m_status) ==
        ((Bit#(3))'(3'h4))) || ((((x_1)[(Bit#(4))'(4'h5)]).m_status) ==
        ((Bit#(3))'(3'h6)))) && (((! ((((x_1)[(Bit#(4))'(4'h5)]).m_addr) ==
        (x_5))) && (((((x_1)[(Bit#(4))'(4'h5)]).m_addr)[13:5]) ==
        ((x_5)[13:5]))) || ((((x_1)[(Bit#(4))'(4'h5)]).m_addr) == (x_5))) ?
        ((Bool)'(True)) : (((((((x_1)[(Bit#(4))'(4'h6)]).m_status) ==
        ((Bit#(3))'(3'h4))) || ((((x_1)[(Bit#(4))'(4'h6)]).m_status) ==
        ((Bit#(3))'(3'h6)))) && (((! ((((x_1)[(Bit#(4))'(4'h6)]).m_addr) ==
        (x_5))) && (((((x_1)[(Bit#(4))'(4'h6)]).m_addr)[13:5]) ==
        ((x_5)[13:5]))) || ((((x_1)[(Bit#(4))'(4'h6)]).m_addr) == (x_5))) ?
        ((Bool)'(True)) : (((((((x_1)[(Bit#(4))'(4'h7)]).m_status) ==
        ((Bit#(3))'(3'h4))) || ((((x_1)[(Bit#(4))'(4'h7)]).m_status) ==
        ((Bit#(3))'(3'h6)))) && (((! ((((x_1)[(Bit#(4))'(4'h7)]).m_addr) ==
        (x_5))) && (((((x_1)[(Bit#(4))'(4'h7)]).m_addr)[13:5]) ==
        ((x_5)[13:5]))) || ((((x_1)[(Bit#(4))'(4'h7)]).m_addr) == (x_5))) ?
        ((Bool)'(True)) : (((((((x_1)[(Bit#(4))'(4'h8)]).m_status) ==
        ((Bit#(3))'(3'h4))) || ((((x_1)[(Bit#(4))'(4'h8)]).m_status) ==
        ((Bit#(3))'(3'h6)))) && (((! ((((x_1)[(Bit#(4))'(4'h8)]).m_addr) ==
        (x_5))) && (((((x_1)[(Bit#(4))'(4'h8)]).m_addr)[13:5]) ==
        ((x_5)[13:5]))) || ((((x_1)[(Bit#(4))'(4'h8)]).m_addr) == (x_5))) ?
        ((Bool)'(True)) : (((((((x_1)[(Bit#(4))'(4'h9)]).m_status) ==
        ((Bit#(3))'(3'h4))) || ((((x_1)[(Bit#(4))'(4'h9)]).m_status) ==
        ((Bit#(3))'(3'h6)))) && (((! ((((x_1)[(Bit#(4))'(4'h9)]).m_addr) ==
        (x_5))) && (((((x_1)[(Bit#(4))'(4'h9)]).m_addr)[13:5]) ==
        ((x_5)[13:5]))) || ((((x_1)[(Bit#(4))'(4'h9)]).m_addr) == (x_5))) ?
        ((Bool)'(True)) : (((((((x_1)[(Bit#(4))'(4'ha)]).m_status) ==
        ((Bit#(3))'(3'h4))) || ((((x_1)[(Bit#(4))'(4'ha)]).m_status) ==
        ((Bit#(3))'(3'h6)))) && (((! ((((x_1)[(Bit#(4))'(4'ha)]).m_addr) ==
        (x_5))) && (((((x_1)[(Bit#(4))'(4'ha)]).m_addr)[13:5]) ==
        ((x_5)[13:5]))) || ((((x_1)[(Bit#(4))'(4'ha)]).m_addr) == (x_5))) ?
        ((Bool)'(True)) : (((((((x_1)[(Bit#(4))'(4'hb)]).m_status) ==
        ((Bit#(3))'(3'h4))) || ((((x_1)[(Bit#(4))'(4'hb)]).m_status) ==
        ((Bit#(3))'(3'h6)))) && (((! ((((x_1)[(Bit#(4))'(4'hb)]).m_addr) ==
        (x_5))) && (((((x_1)[(Bit#(4))'(4'hb)]).m_addr)[13:5]) ==
        ((x_5)[13:5]))) || ((((x_1)[(Bit#(4))'(4'hb)]).m_addr) == (x_5))) ?
        ((Bool)'(True)) : ((Bool)'(False))))))))))))))))))))))))));
        Struct16 x_7 = (((((((x_1)[(Bit#(4))'(4'h0)]).m_status) ==
        ((Bit#(3))'(3'h5))) && (! (((x_1)[(Bit#(4))'(4'h0)]).m_is_ul))) &&
        ((((x_1)[(Bit#(4))'(4'h0)]).m_addr) == (x_5)) ? (Struct16 {valid :
        (Bool)'(True), data : (Bit#(4))'(4'h0)}) :
        (((((((x_1)[(Bit#(4))'(4'h1)]).m_status) == ((Bit#(3))'(3'h5))) && (!
        (((x_1)[(Bit#(4))'(4'h1)]).m_is_ul))) &&
        ((((x_1)[(Bit#(4))'(4'h1)]).m_addr) == (x_5)) ? (Struct16 {valid :
        (Bool)'(True), data : (Bit#(4))'(4'h1)}) :
        (((((((x_1)[(Bit#(4))'(4'h2)]).m_status) == ((Bit#(3))'(3'h5))) && (!
        (((x_1)[(Bit#(4))'(4'h2)]).m_is_ul))) &&
        ((((x_1)[(Bit#(4))'(4'h2)]).m_addr) == (x_5)) ? (Struct16 {valid :
        (Bool)'(True), data : (Bit#(4))'(4'h2)}) :
        (((((((x_1)[(Bit#(4))'(4'h3)]).m_status) == ((Bit#(3))'(3'h5))) && (!
        (((x_1)[(Bit#(4))'(4'h3)]).m_is_ul))) &&
        ((((x_1)[(Bit#(4))'(4'h3)]).m_addr) == (x_5)) ? (Struct16 {valid :
        (Bool)'(True), data : (Bit#(4))'(4'h3)}) :
        (((((((x_1)[(Bit#(4))'(4'h4)]).m_status) == ((Bit#(3))'(3'h5))) && (!
        (((x_1)[(Bit#(4))'(4'h4)]).m_is_ul))) &&
        ((((x_1)[(Bit#(4))'(4'h4)]).m_addr) == (x_5)) ? (Struct16 {valid :
        (Bool)'(True), data : (Bit#(4))'(4'h4)}) :
        (((((((x_1)[(Bit#(4))'(4'h5)]).m_status) == ((Bit#(3))'(3'h5))) && (!
        (((x_1)[(Bit#(4))'(4'h5)]).m_is_ul))) &&
        ((((x_1)[(Bit#(4))'(4'h5)]).m_addr) == (x_5)) ? (Struct16 {valid :
        (Bool)'(True), data : (Bit#(4))'(4'h5)}) :
        (((((((x_1)[(Bit#(4))'(4'h6)]).m_status) == ((Bit#(3))'(3'h5))) && (!
        (((x_1)[(Bit#(4))'(4'h6)]).m_is_ul))) &&
        ((((x_1)[(Bit#(4))'(4'h6)]).m_addr) == (x_5)) ? (Struct16 {valid :
        (Bool)'(True), data : (Bit#(4))'(4'h6)}) :
        (((((((x_1)[(Bit#(4))'(4'h7)]).m_status) == ((Bit#(3))'(3'h5))) && (!
        (((x_1)[(Bit#(4))'(4'h7)]).m_is_ul))) &&
        ((((x_1)[(Bit#(4))'(4'h7)]).m_addr) == (x_5)) ? (Struct16 {valid :
        (Bool)'(True), data : (Bit#(4))'(4'h7)}) :
        (((((((x_1)[(Bit#(4))'(4'h8)]).m_status) == ((Bit#(3))'(3'h5))) && (!
        (((x_1)[(Bit#(4))'(4'h8)]).m_is_ul))) &&
        ((((x_1)[(Bit#(4))'(4'h8)]).m_addr) == (x_5)) ? (Struct16 {valid :
        (Bool)'(True), data : (Bit#(4))'(4'h8)}) :
        (((((((x_1)[(Bit#(4))'(4'h9)]).m_status) == ((Bit#(3))'(3'h5))) && (!
        (((x_1)[(Bit#(4))'(4'h9)]).m_is_ul))) &&
        ((((x_1)[(Bit#(4))'(4'h9)]).m_addr) == (x_5)) ? (Struct16 {valid :
        (Bool)'(True), data : (Bit#(4))'(4'h9)}) :
        (((((((x_1)[(Bit#(4))'(4'ha)]).m_status) == ((Bit#(3))'(3'h5))) && (!
        (((x_1)[(Bit#(4))'(4'ha)]).m_is_ul))) &&
        ((((x_1)[(Bit#(4))'(4'ha)]).m_addr) == (x_5)) ? (Struct16 {valid :
        (Bool)'(True), data : (Bit#(4))'(4'ha)}) :
        (((((((x_1)[(Bit#(4))'(4'hb)]).m_status) == ((Bit#(3))'(3'h5))) && (!
        (((x_1)[(Bit#(4))'(4'hb)]).m_is_ul))) &&
        ((((x_1)[(Bit#(4))'(4'hb)]).m_addr) == (x_5)) ? (Struct16 {valid :
        (Bool)'(True), data : (Bit#(4))'(4'hb)}) : (Struct16 {valid :
        (Bool)'(False), data : unpack(0)})))))))))))))))))))))))));
        Bool x_8 = ((x_7).valid);
        Struct4 x_9 = (Struct4 {s_has_slot : (x_3) && (! (x_6)), s_conflict :
        x_8, s_id :
        x_4});
        if ((x_3) && (! (x_6))) begin
            Vector#(12, Struct15) x_10 = (update (x_1, x_4, Struct15
            {m_status : (x_8 ? ((Bit#(3))'(3'h1)) : ((Bit#(3))'(3'h4))),
            m_next : Struct16 {valid : (Bool)'(False), data : unpack(0)},
            m_is_ul : unpack(0), m_addr : ((x_0).r_msg).addr, m_qidx :
            (x_0).r_msg_from, m_rsb : unpack(0), m_dl_rss_from : unpack(0),
            m_dl_rss_recv : unpack(0)}));
            let x_11 = (rqs_00);
            rqs_00 <= update (x_11, x_4,
            (x_0).r_msg);
            let x_15 = ?;
            if (x_8) begin
                Bit#(4) x_12 = ((((! ((((x_1)[(Bit#(4))'(4'h0)]).m_status) ==
                ((Bit#(3))'(3'h0)))) && (!
                ((((x_1)[(Bit#(4))'(4'h0)]).m_next).valid))) &&
                ((((x_1)[(Bit#(4))'(4'h0)]).m_addr) == (x_5)) ?
                ((Bit#(4))'(4'h0)) : ((((!
                ((((x_1)[(Bit#(4))'(4'h1)]).m_status) == ((Bit#(3))'(3'h0))))
                && (! ((((x_1)[(Bit#(4))'(4'h1)]).m_next).valid))) &&
                ((((x_1)[(Bit#(4))'(4'h1)]).m_addr) == (x_5)) ?
                ((Bit#(4))'(4'h1)) : ((((!
                ((((x_1)[(Bit#(4))'(4'h2)]).m_status) == ((Bit#(3))'(3'h0))))
                && (! ((((x_1)[(Bit#(4))'(4'h2)]).m_next).valid))) &&
                ((((x_1)[(Bit#(4))'(4'h2)]).m_addr) == (x_5)) ?
                ((Bit#(4))'(4'h2)) : ((((!
                ((((x_1)[(Bit#(4))'(4'h3)]).m_status) == ((Bit#(3))'(3'h0))))
                && (! ((((x_1)[(Bit#(4))'(4'h3)]).m_next).valid))) &&
                ((((x_1)[(Bit#(4))'(4'h3)]).m_addr) == (x_5)) ?
                ((Bit#(4))'(4'h3)) : ((((!
                ((((x_1)[(Bit#(4))'(4'h4)]).m_status) == ((Bit#(3))'(3'h0))))
                && (! ((((x_1)[(Bit#(4))'(4'h4)]).m_next).valid))) &&
                ((((x_1)[(Bit#(4))'(4'h4)]).m_addr) == (x_5)) ?
                ((Bit#(4))'(4'h4)) : ((((!
                ((((x_1)[(Bit#(4))'(4'h5)]).m_status) == ((Bit#(3))'(3'h0))))
                && (! ((((x_1)[(Bit#(4))'(4'h5)]).m_next).valid))) &&
                ((((x_1)[(Bit#(4))'(4'h5)]).m_addr) == (x_5)) ?
                ((Bit#(4))'(4'h5)) : ((((!
                ((((x_1)[(Bit#(4))'(4'h6)]).m_status) == ((Bit#(3))'(3'h0))))
                && (! ((((x_1)[(Bit#(4))'(4'h6)]).m_next).valid))) &&
                ((((x_1)[(Bit#(4))'(4'h6)]).m_addr) == (x_5)) ?
                ((Bit#(4))'(4'h6)) : ((((!
                ((((x_1)[(Bit#(4))'(4'h7)]).m_status) == ((Bit#(3))'(3'h0))))
                && (! ((((x_1)[(Bit#(4))'(4'h7)]).m_next).valid))) &&
                ((((x_1)[(Bit#(4))'(4'h7)]).m_addr) == (x_5)) ?
                ((Bit#(4))'(4'h7)) : ((((!
                ((((x_1)[(Bit#(4))'(4'h8)]).m_status) == ((Bit#(3))'(3'h0))))
                && (! ((((x_1)[(Bit#(4))'(4'h8)]).m_next).valid))) &&
                ((((x_1)[(Bit#(4))'(4'h8)]).m_addr) == (x_5)) ?
                ((Bit#(4))'(4'h8)) : ((((!
                ((((x_1)[(Bit#(4))'(4'h9)]).m_status) == ((Bit#(3))'(3'h0))))
                && (! ((((x_1)[(Bit#(4))'(4'h9)]).m_next).valid))) &&
                ((((x_1)[(Bit#(4))'(4'h9)]).m_addr) == (x_5)) ?
                ((Bit#(4))'(4'h9)) : ((((!
                ((((x_1)[(Bit#(4))'(4'ha)]).m_status) == ((Bit#(3))'(3'h0))))
                && (! ((((x_1)[(Bit#(4))'(4'ha)]).m_next).valid))) &&
                ((((x_1)[(Bit#(4))'(4'ha)]).m_addr) == (x_5)) ?
                ((Bit#(4))'(4'ha)) : ((((!
                ((((x_1)[(Bit#(4))'(4'hb)]).m_status) == ((Bit#(3))'(3'h0))))
                && (! ((((x_1)[(Bit#(4))'(4'hb)]).m_next).valid))) &&
                ((((x_1)[(Bit#(4))'(4'hb)]).m_addr) == (x_5)) ?
                ((Bit#(4))'(4'hb)) :
                (unpack(0))))))))))))))))))))))))));
                Struct15 x_13 = ((x_1)[x_12]);
                Vector#(12, Struct15) x_14 = (update (x_10, x_12, Struct15
                {m_status : (x_13).m_status, m_next : (x_8 ? (Struct16 {valid
                : (Bool)'(True), data : x_4}) : ((x_13).m_next)), m_is_ul :
                (x_13).m_is_ul, m_addr : (x_13).m_addr, m_qidx :
                (x_13).m_qidx, m_rsb : (x_13).m_rsb, m_dl_rss_from :
                (x_13).m_dl_rss_from, m_dl_rss_recv :
                (x_13).m_dl_rss_recv}));
                x_15 = x_14;
            end else begin
                x_15 = x_10;
            end
            mshrs_00 <= x_15;
        end else begin

        end
        return x_9;
    endmethod

    method ActionValue#(Struct4) getCRqSlot_00 (Struct3 x_0);
        let x_1 = (mshrs_00);
        Struct16 x_2 = (((((x_1)[(Bit#(4))'(4'h4)]).m_status) ==
        ((Bit#(3))'(3'h0)) ? (Struct16 {valid : (Bool)'(True), data :
        (Bit#(4))'(4'h4)}) : (((((x_1)[(Bit#(4))'(4'h5)]).m_status) ==
        ((Bit#(3))'(3'h0)) ? (Struct16 {valid : (Bool)'(True), data :
        (Bit#(4))'(4'h5)}) : (((((x_1)[(Bit#(4))'(4'h6)]).m_status) ==
        ((Bit#(3))'(3'h0)) ? (Struct16 {valid : (Bool)'(True), data :
        (Bit#(4))'(4'h6)}) : (((((x_1)[(Bit#(4))'(4'h7)]).m_status) ==
        ((Bit#(3))'(3'h0)) ? (Struct16 {valid : (Bool)'(True), data :
        (Bit#(4))'(4'h7)}) : (((((x_1)[(Bit#(4))'(4'h8)]).m_status) ==
        ((Bit#(3))'(3'h0)) ? (Struct16 {valid : (Bool)'(True), data :
        (Bit#(4))'(4'h8)}) : (((((x_1)[(Bit#(4))'(4'h9)]).m_status) ==
        ((Bit#(3))'(3'h0)) ? (Struct16 {valid : (Bool)'(True), data :
        (Bit#(4))'(4'h9)}) : (((((x_1)[(Bit#(4))'(4'ha)]).m_status) ==
        ((Bit#(3))'(3'h0)) ? (Struct16 {valid : (Bool)'(True), data :
        (Bit#(4))'(4'ha)}) : (((((x_1)[(Bit#(4))'(4'hb)]).m_status) ==
        ((Bit#(3))'(3'h0)) ? (Struct16 {valid : (Bool)'(True), data :
        (Bit#(4))'(4'hb)}) : (Struct16 {valid : (Bool)'(False), data :
        unpack(0)})))))))))))))))));
        Bool x_3 = ((x_2).valid);
        Bit#(4) x_4 = ((x_2).data);
        Bit#(64) x_5 = (((x_0).r_msg).addr);
        Bool x_6 = (((((((x_1)[(Bit#(4))'(4'h0)]).m_status) ==
        ((Bit#(3))'(3'h4))) || ((((x_1)[(Bit#(4))'(4'h0)]).m_status) ==
        ((Bit#(3))'(3'h6)))) && ((! ((((x_1)[(Bit#(4))'(4'h0)]).m_addr) ==
        (x_5))) && (((((x_1)[(Bit#(4))'(4'h0)]).m_addr)[13:5]) ==
        ((x_5)[13:5]))) ? ((Bool)'(True)) :
        (((((((x_1)[(Bit#(4))'(4'h1)]).m_status) == ((Bit#(3))'(3'h4))) ||
        ((((x_1)[(Bit#(4))'(4'h1)]).m_status) == ((Bit#(3))'(3'h6)))) && ((!
        ((((x_1)[(Bit#(4))'(4'h1)]).m_addr) == (x_5))) &&
        (((((x_1)[(Bit#(4))'(4'h1)]).m_addr)[13:5]) == ((x_5)[13:5]))) ?
        ((Bool)'(True)) : (((((((x_1)[(Bit#(4))'(4'h2)]).m_status) ==
        ((Bit#(3))'(3'h4))) || ((((x_1)[(Bit#(4))'(4'h2)]).m_status) ==
        ((Bit#(3))'(3'h6)))) && ((! ((((x_1)[(Bit#(4))'(4'h2)]).m_addr) ==
        (x_5))) && (((((x_1)[(Bit#(4))'(4'h2)]).m_addr)[13:5]) ==
        ((x_5)[13:5]))) ? ((Bool)'(True)) :
        (((((((x_1)[(Bit#(4))'(4'h3)]).m_status) == ((Bit#(3))'(3'h4))) ||
        ((((x_1)[(Bit#(4))'(4'h3)]).m_status) == ((Bit#(3))'(3'h6)))) && ((!
        ((((x_1)[(Bit#(4))'(4'h3)]).m_addr) == (x_5))) &&
        (((((x_1)[(Bit#(4))'(4'h3)]).m_addr)[13:5]) == ((x_5)[13:5]))) ?
        ((Bool)'(True)) : (((((((x_1)[(Bit#(4))'(4'h4)]).m_status) ==
        ((Bit#(3))'(3'h4))) || ((((x_1)[(Bit#(4))'(4'h4)]).m_status) ==
        ((Bit#(3))'(3'h6)))) && ((! ((((x_1)[(Bit#(4))'(4'h4)]).m_addr) ==
        (x_5))) && (((((x_1)[(Bit#(4))'(4'h4)]).m_addr)[13:5]) ==
        ((x_5)[13:5]))) ? ((Bool)'(True)) :
        (((((((x_1)[(Bit#(4))'(4'h5)]).m_status) == ((Bit#(3))'(3'h4))) ||
        ((((x_1)[(Bit#(4))'(4'h5)]).m_status) == ((Bit#(3))'(3'h6)))) && ((!
        ((((x_1)[(Bit#(4))'(4'h5)]).m_addr) == (x_5))) &&
        (((((x_1)[(Bit#(4))'(4'h5)]).m_addr)[13:5]) == ((x_5)[13:5]))) ?
        ((Bool)'(True)) : (((((((x_1)[(Bit#(4))'(4'h6)]).m_status) ==
        ((Bit#(3))'(3'h4))) || ((((x_1)[(Bit#(4))'(4'h6)]).m_status) ==
        ((Bit#(3))'(3'h6)))) && ((! ((((x_1)[(Bit#(4))'(4'h6)]).m_addr) ==
        (x_5))) && (((((x_1)[(Bit#(4))'(4'h6)]).m_addr)[13:5]) ==
        ((x_5)[13:5]))) ? ((Bool)'(True)) :
        (((((((x_1)[(Bit#(4))'(4'h7)]).m_status) == ((Bit#(3))'(3'h4))) ||
        ((((x_1)[(Bit#(4))'(4'h7)]).m_status) == ((Bit#(3))'(3'h6)))) && ((!
        ((((x_1)[(Bit#(4))'(4'h7)]).m_addr) == (x_5))) &&
        (((((x_1)[(Bit#(4))'(4'h7)]).m_addr)[13:5]) == ((x_5)[13:5]))) ?
        ((Bool)'(True)) : (((((((x_1)[(Bit#(4))'(4'h8)]).m_status) ==
        ((Bit#(3))'(3'h4))) || ((((x_1)[(Bit#(4))'(4'h8)]).m_status) ==
        ((Bit#(3))'(3'h6)))) && ((! ((((x_1)[(Bit#(4))'(4'h8)]).m_addr) ==
        (x_5))) && (((((x_1)[(Bit#(4))'(4'h8)]).m_addr)[13:5]) ==
        ((x_5)[13:5]))) ? ((Bool)'(True)) :
        (((((((x_1)[(Bit#(4))'(4'h9)]).m_status) == ((Bit#(3))'(3'h4))) ||
        ((((x_1)[(Bit#(4))'(4'h9)]).m_status) == ((Bit#(3))'(3'h6)))) && ((!
        ((((x_1)[(Bit#(4))'(4'h9)]).m_addr) == (x_5))) &&
        (((((x_1)[(Bit#(4))'(4'h9)]).m_addr)[13:5]) == ((x_5)[13:5]))) ?
        ((Bool)'(True)) : (((((((x_1)[(Bit#(4))'(4'ha)]).m_status) ==
        ((Bit#(3))'(3'h4))) || ((((x_1)[(Bit#(4))'(4'ha)]).m_status) ==
        ((Bit#(3))'(3'h6)))) && ((! ((((x_1)[(Bit#(4))'(4'ha)]).m_addr) ==
        (x_5))) && (((((x_1)[(Bit#(4))'(4'ha)]).m_addr)[13:5]) ==
        ((x_5)[13:5]))) ? ((Bool)'(True)) :
        (((((((x_1)[(Bit#(4))'(4'hb)]).m_status) == ((Bit#(3))'(3'h4))) ||
        ((((x_1)[(Bit#(4))'(4'hb)]).m_status) == ((Bit#(3))'(3'h6)))) && ((!
        ((((x_1)[(Bit#(4))'(4'hb)]).m_addr) == (x_5))) &&
        (((((x_1)[(Bit#(4))'(4'hb)]).m_addr)[13:5]) == ((x_5)[13:5]))) ?
        ((Bool)'(True)) : ((Bool)'(False))))))))))))))))))))))))));
        Struct16 x_7 = (((((! ((((x_1)[(Bit#(4))'(4'h4)]).m_status) ==
        ((Bit#(3))'(3'h0)))) && (!
        ((((x_1)[(Bit#(4))'(4'h4)]).m_next).valid))) &&
        (((x_1)[(Bit#(4))'(4'h4)]).m_is_ul)) &&
        ((((x_1)[(Bit#(4))'(4'h4)]).m_addr) == (x_5)) ? (Struct16 {valid :
        (Bool)'(True), data : (Bit#(4))'(4'h4)}) : (((((!
        ((((x_1)[(Bit#(4))'(4'h5)]).m_status) == ((Bit#(3))'(3'h0)))) && (!
        ((((x_1)[(Bit#(4))'(4'h5)]).m_next).valid))) &&
        (((x_1)[(Bit#(4))'(4'h5)]).m_is_ul)) &&
        ((((x_1)[(Bit#(4))'(4'h5)]).m_addr) == (x_5)) ? (Struct16 {valid :
        (Bool)'(True), data : (Bit#(4))'(4'h5)}) : (((((!
        ((((x_1)[(Bit#(4))'(4'h6)]).m_status) == ((Bit#(3))'(3'h0)))) && (!
        ((((x_1)[(Bit#(4))'(4'h6)]).m_next).valid))) &&
        (((x_1)[(Bit#(4))'(4'h6)]).m_is_ul)) &&
        ((((x_1)[(Bit#(4))'(4'h6)]).m_addr) == (x_5)) ? (Struct16 {valid :
        (Bool)'(True), data : (Bit#(4))'(4'h6)}) : (((((!
        ((((x_1)[(Bit#(4))'(4'h7)]).m_status) == ((Bit#(3))'(3'h0)))) && (!
        ((((x_1)[(Bit#(4))'(4'h7)]).m_next).valid))) &&
        (((x_1)[(Bit#(4))'(4'h7)]).m_is_ul)) &&
        ((((x_1)[(Bit#(4))'(4'h7)]).m_addr) == (x_5)) ? (Struct16 {valid :
        (Bool)'(True), data : (Bit#(4))'(4'h7)}) : (((((!
        ((((x_1)[(Bit#(4))'(4'h8)]).m_status) == ((Bit#(3))'(3'h0)))) && (!
        ((((x_1)[(Bit#(4))'(4'h8)]).m_next).valid))) &&
        (((x_1)[(Bit#(4))'(4'h8)]).m_is_ul)) &&
        ((((x_1)[(Bit#(4))'(4'h8)]).m_addr) == (x_5)) ? (Struct16 {valid :
        (Bool)'(True), data : (Bit#(4))'(4'h8)}) : (((((!
        ((((x_1)[(Bit#(4))'(4'h9)]).m_status) == ((Bit#(3))'(3'h0)))) && (!
        ((((x_1)[(Bit#(4))'(4'h9)]).m_next).valid))) &&
        (((x_1)[(Bit#(4))'(4'h9)]).m_is_ul)) &&
        ((((x_1)[(Bit#(4))'(4'h9)]).m_addr) == (x_5)) ? (Struct16 {valid :
        (Bool)'(True), data : (Bit#(4))'(4'h9)}) : (((((!
        ((((x_1)[(Bit#(4))'(4'ha)]).m_status) == ((Bit#(3))'(3'h0)))) && (!
        ((((x_1)[(Bit#(4))'(4'ha)]).m_next).valid))) &&
        (((x_1)[(Bit#(4))'(4'ha)]).m_is_ul)) &&
        ((((x_1)[(Bit#(4))'(4'ha)]).m_addr) == (x_5)) ? (Struct16 {valid :
        (Bool)'(True), data : (Bit#(4))'(4'ha)}) : (((((!
        ((((x_1)[(Bit#(4))'(4'hb)]).m_status) == ((Bit#(3))'(3'h0)))) && (!
        ((((x_1)[(Bit#(4))'(4'hb)]).m_next).valid))) &&
        (((x_1)[(Bit#(4))'(4'hb)]).m_is_ul)) &&
        ((((x_1)[(Bit#(4))'(4'hb)]).m_addr) == (x_5)) ? (Struct16 {valid :
        (Bool)'(True), data : (Bit#(4))'(4'hb)}) : (Struct16 {valid :
        (Bool)'(False), data : unpack(0)})))))))))))))))));
        Struct16 x_8 = (((((! ((((x_1)[(Bit#(4))'(4'h0)]).m_status) ==
        ((Bit#(3))'(3'h0)))) && (!
        ((((x_1)[(Bit#(4))'(4'h0)]).m_next).valid))) && (!
        (((x_1)[(Bit#(4))'(4'h0)]).m_is_ul))) &&
        ((((x_1)[(Bit#(4))'(4'h0)]).m_addr) == (x_5)) ? (Struct16 {valid :
        (Bool)'(True), data : (Bit#(4))'(4'h0)}) : (((((!
        ((((x_1)[(Bit#(4))'(4'h1)]).m_status) == ((Bit#(3))'(3'h0)))) && (!
        ((((x_1)[(Bit#(4))'(4'h1)]).m_next).valid))) && (!
        (((x_1)[(Bit#(4))'(4'h1)]).m_is_ul))) &&
        ((((x_1)[(Bit#(4))'(4'h1)]).m_addr) == (x_5)) ? (Struct16 {valid :
        (Bool)'(True), data : (Bit#(4))'(4'h1)}) : (((((!
        ((((x_1)[(Bit#(4))'(4'h2)]).m_status) == ((Bit#(3))'(3'h0)))) && (!
        ((((x_1)[(Bit#(4))'(4'h2)]).m_next).valid))) && (!
        (((x_1)[(Bit#(4))'(4'h2)]).m_is_ul))) &&
        ((((x_1)[(Bit#(4))'(4'h2)]).m_addr) == (x_5)) ? (Struct16 {valid :
        (Bool)'(True), data : (Bit#(4))'(4'h2)}) : (((((!
        ((((x_1)[(Bit#(4))'(4'h3)]).m_status) == ((Bit#(3))'(3'h0)))) && (!
        ((((x_1)[(Bit#(4))'(4'h3)]).m_next).valid))) && (!
        (((x_1)[(Bit#(4))'(4'h3)]).m_is_ul))) &&
        ((((x_1)[(Bit#(4))'(4'h3)]).m_addr) == (x_5)) ? (Struct16 {valid :
        (Bool)'(True), data : (Bit#(4))'(4'h3)}) : (((((!
        ((((x_1)[(Bit#(4))'(4'h4)]).m_status) == ((Bit#(3))'(3'h0)))) && (!
        ((((x_1)[(Bit#(4))'(4'h4)]).m_next).valid))) && (!
        (((x_1)[(Bit#(4))'(4'h4)]).m_is_ul))) &&
        ((((x_1)[(Bit#(4))'(4'h4)]).m_addr) == (x_5)) ? (Struct16 {valid :
        (Bool)'(True), data : (Bit#(4))'(4'h4)}) : (((((!
        ((((x_1)[(Bit#(4))'(4'h5)]).m_status) == ((Bit#(3))'(3'h0)))) && (!
        ((((x_1)[(Bit#(4))'(4'h5)]).m_next).valid))) && (!
        (((x_1)[(Bit#(4))'(4'h5)]).m_is_ul))) &&
        ((((x_1)[(Bit#(4))'(4'h5)]).m_addr) == (x_5)) ? (Struct16 {valid :
        (Bool)'(True), data : (Bit#(4))'(4'h5)}) : (((((!
        ((((x_1)[(Bit#(4))'(4'h6)]).m_status) == ((Bit#(3))'(3'h0)))) && (!
        ((((x_1)[(Bit#(4))'(4'h6)]).m_next).valid))) && (!
        (((x_1)[(Bit#(4))'(4'h6)]).m_is_ul))) &&
        ((((x_1)[(Bit#(4))'(4'h6)]).m_addr) == (x_5)) ? (Struct16 {valid :
        (Bool)'(True), data : (Bit#(4))'(4'h6)}) : (((((!
        ((((x_1)[(Bit#(4))'(4'h7)]).m_status) == ((Bit#(3))'(3'h0)))) && (!
        ((((x_1)[(Bit#(4))'(4'h7)]).m_next).valid))) && (!
        (((x_1)[(Bit#(4))'(4'h7)]).m_is_ul))) &&
        ((((x_1)[(Bit#(4))'(4'h7)]).m_addr) == (x_5)) ? (Struct16 {valid :
        (Bool)'(True), data : (Bit#(4))'(4'h7)}) : (((((!
        ((((x_1)[(Bit#(4))'(4'h8)]).m_status) == ((Bit#(3))'(3'h0)))) && (!
        ((((x_1)[(Bit#(4))'(4'h8)]).m_next).valid))) && (!
        (((x_1)[(Bit#(4))'(4'h8)]).m_is_ul))) &&
        ((((x_1)[(Bit#(4))'(4'h8)]).m_addr) == (x_5)) ? (Struct16 {valid :
        (Bool)'(True), data : (Bit#(4))'(4'h8)}) : (((((!
        ((((x_1)[(Bit#(4))'(4'h9)]).m_status) == ((Bit#(3))'(3'h0)))) && (!
        ((((x_1)[(Bit#(4))'(4'h9)]).m_next).valid))) && (!
        (((x_1)[(Bit#(4))'(4'h9)]).m_is_ul))) &&
        ((((x_1)[(Bit#(4))'(4'h9)]).m_addr) == (x_5)) ? (Struct16 {valid :
        (Bool)'(True), data : (Bit#(4))'(4'h9)}) : (((((!
        ((((x_1)[(Bit#(4))'(4'ha)]).m_status) == ((Bit#(3))'(3'h0)))) && (!
        ((((x_1)[(Bit#(4))'(4'ha)]).m_next).valid))) && (!
        (((x_1)[(Bit#(4))'(4'ha)]).m_is_ul))) &&
        ((((x_1)[(Bit#(4))'(4'ha)]).m_addr) == (x_5)) ? (Struct16 {valid :
        (Bool)'(True), data : (Bit#(4))'(4'ha)}) : (((((!
        ((((x_1)[(Bit#(4))'(4'hb)]).m_status) == ((Bit#(3))'(3'h0)))) && (!
        ((((x_1)[(Bit#(4))'(4'hb)]).m_next).valid))) && (!
        (((x_1)[(Bit#(4))'(4'hb)]).m_is_ul))) &&
        ((((x_1)[(Bit#(4))'(4'hb)]).m_addr) == (x_5)) ? (Struct16 {valid :
        (Bool)'(True), data : (Bit#(4))'(4'hb)}) : (Struct16 {valid :
        (Bool)'(False), data : unpack(0)})))))))))))))))))))))))));
        Bool x_9 = ((x_7).valid);
        Bool x_10 = ((x_8).valid);
        Bool x_11 = ((x_9) || (x_10));
        Struct4 x_12 = (Struct4 {s_has_slot : (x_3) && (! (x_6)), s_conflict
        : x_11, s_id :
        x_4});
        if ((x_3) && (! (x_6))) begin
            Vector#(12, Struct15) x_13 = (update (x_1, x_4, Struct15
            {m_status : (x_11 ? ((Bit#(3))'(3'h1)) : ((Bit#(3))'(3'h4))),
            m_next : Struct16 {valid : (Bool)'(False), data : unpack(0)},
            m_is_ul : unpack(0), m_addr : ((x_0).r_msg).addr, m_qidx :
            (x_0).r_msg_from, m_rsb : unpack(0), m_dl_rss_from : unpack(0),
            m_dl_rss_recv : unpack(0)}));
            let x_14 = (rqs_00);
            rqs_00 <= update (x_14, x_4,
            (x_0).r_msg);
            let x_18 = ?;
            if (x_11) begin
                Bit#(4) x_15 = ((x_9 ? ((x_7).data) : ((x_8).data)));
                Struct15 x_16 = ((x_1)[x_15]);
                Vector#(12, Struct15) x_17 = (update (x_13, x_15, Struct15
                {m_status : (x_16).m_status, m_next : (x_11 ? (Struct16
                {valid : (Bool)'(True), data : x_4}) : ((x_16).m_next)),
                m_is_ul : (x_16).m_is_ul, m_addr : (x_16).m_addr, m_qidx :
                (x_16).m_qidx, m_rsb : (x_16).m_rsb, m_dl_rss_from :
                (x_16).m_dl_rss_from, m_dl_rss_recv :
                (x_16).m_dl_rss_recv}));
                x_18 = x_17;
            end else begin
                x_18 = x_13;
            end
            mshrs_00 <= x_18;
        end else begin

        end
        return x_12;
    endmethod

    method ActionValue#(Struct3) getWait_00 ();
        let x_1 = (mshrs_00);
        let x_2 = (rqs_00);
        Struct16 x_3 = (((((x_1)[(Bit#(4))'(4'h0)]).m_status) ==
        ((Bit#(3))'(3'h2)) ? (Struct16 {valid : (Bool)'(True), data :
        (Bit#(4))'(4'h0)}) : (((((x_1)[(Bit#(4))'(4'h1)]).m_status) ==
        ((Bit#(3))'(3'h2)) ? (Struct16 {valid : (Bool)'(True), data :
        (Bit#(4))'(4'h1)}) : (((((x_1)[(Bit#(4))'(4'h2)]).m_status) ==
        ((Bit#(3))'(3'h2)) ? (Struct16 {valid : (Bool)'(True), data :
        (Bit#(4))'(4'h2)}) : (((((x_1)[(Bit#(4))'(4'h3)]).m_status) ==
        ((Bit#(3))'(3'h2)) ? (Struct16 {valid : (Bool)'(True), data :
        (Bit#(4))'(4'h3)}) : (((((x_1)[(Bit#(4))'(4'h4)]).m_status) ==
        ((Bit#(3))'(3'h2)) ? (Struct16 {valid : (Bool)'(True), data :
        (Bit#(4))'(4'h4)}) : (((((x_1)[(Bit#(4))'(4'h5)]).m_status) ==
        ((Bit#(3))'(3'h2)) ? (Struct16 {valid : (Bool)'(True), data :
        (Bit#(4))'(4'h5)}) : (((((x_1)[(Bit#(4))'(4'h6)]).m_status) ==
        ((Bit#(3))'(3'h2)) ? (Struct16 {valid : (Bool)'(True), data :
        (Bit#(4))'(4'h6)}) : (((((x_1)[(Bit#(4))'(4'h7)]).m_status) ==
        ((Bit#(3))'(3'h2)) ? (Struct16 {valid : (Bool)'(True), data :
        (Bit#(4))'(4'h7)}) : (((((x_1)[(Bit#(4))'(4'h8)]).m_status) ==
        ((Bit#(3))'(3'h2)) ? (Struct16 {valid : (Bool)'(True), data :
        (Bit#(4))'(4'h8)}) : (((((x_1)[(Bit#(4))'(4'h9)]).m_status) ==
        ((Bit#(3))'(3'h2)) ? (Struct16 {valid : (Bool)'(True), data :
        (Bit#(4))'(4'h9)}) : (((((x_1)[(Bit#(4))'(4'ha)]).m_status) ==
        ((Bit#(3))'(3'h2)) ? (Struct16 {valid : (Bool)'(True), data :
        (Bit#(4))'(4'ha)}) : (((((x_1)[(Bit#(4))'(4'hb)]).m_status) ==
        ((Bit#(3))'(3'h2)) ? (Struct16 {valid : (Bool)'(True), data :
        (Bit#(4))'(4'hb)}) : (Struct16 {valid : (Bool)'(False), data :
        unpack(0)})))))))))))))))))))))))));
        when ((x_3).valid, noAction);
        Bit#(4) x_4 = ((x_3).data);
        Struct15 x_5 = ((x_1)[x_4]);
        Struct1 x_6 = ((x_2)[x_4]);
        Bit#(64) x_7 = ((x_5).m_addr);
        Bool x_8 = ((((! ((((x_1)[(Bit#(4))'(4'h0)]).m_status) <
        ((Bit#(3))'(3'h4)))) && ((((x_1)[(Bit#(4))'(4'h0)]).m_addr) ==
        (x_7))) || ((((((x_1)[(Bit#(4))'(4'h0)]).m_status) ==
        ((Bit#(3))'(3'h4))) || ((((x_1)[(Bit#(4))'(4'h0)]).m_status) ==
        ((Bit#(3))'(3'h6)))) && ((! ((((x_1)[(Bit#(4))'(4'h0)]).m_addr) ==
        (x_7))) && (((((x_1)[(Bit#(4))'(4'h0)]).m_addr)[13:5]) ==
        ((x_7)[13:5])))) ? ((Bool)'(True)) : ((((!
        ((((x_1)[(Bit#(4))'(4'h1)]).m_status) < ((Bit#(3))'(3'h4)))) &&
        ((((x_1)[(Bit#(4))'(4'h1)]).m_addr) == (x_7))) ||
        ((((((x_1)[(Bit#(4))'(4'h1)]).m_status) == ((Bit#(3))'(3'h4))) ||
        ((((x_1)[(Bit#(4))'(4'h1)]).m_status) == ((Bit#(3))'(3'h6)))) && ((!
        ((((x_1)[(Bit#(4))'(4'h1)]).m_addr) == (x_7))) &&
        (((((x_1)[(Bit#(4))'(4'h1)]).m_addr)[13:5]) == ((x_7)[13:5])))) ?
        ((Bool)'(True)) : ((((! ((((x_1)[(Bit#(4))'(4'h2)]).m_status) <
        ((Bit#(3))'(3'h4)))) && ((((x_1)[(Bit#(4))'(4'h2)]).m_addr) ==
        (x_7))) || ((((((x_1)[(Bit#(4))'(4'h2)]).m_status) ==
        ((Bit#(3))'(3'h4))) || ((((x_1)[(Bit#(4))'(4'h2)]).m_status) ==
        ((Bit#(3))'(3'h6)))) && ((! ((((x_1)[(Bit#(4))'(4'h2)]).m_addr) ==
        (x_7))) && (((((x_1)[(Bit#(4))'(4'h2)]).m_addr)[13:5]) ==
        ((x_7)[13:5])))) ? ((Bool)'(True)) : ((((!
        ((((x_1)[(Bit#(4))'(4'h3)]).m_status) < ((Bit#(3))'(3'h4)))) &&
        ((((x_1)[(Bit#(4))'(4'h3)]).m_addr) == (x_7))) ||
        ((((((x_1)[(Bit#(4))'(4'h3)]).m_status) == ((Bit#(3))'(3'h4))) ||
        ((((x_1)[(Bit#(4))'(4'h3)]).m_status) == ((Bit#(3))'(3'h6)))) && ((!
        ((((x_1)[(Bit#(4))'(4'h3)]).m_addr) == (x_7))) &&
        (((((x_1)[(Bit#(4))'(4'h3)]).m_addr)[13:5]) == ((x_7)[13:5])))) ?
        ((Bool)'(True)) : ((((! ((((x_1)[(Bit#(4))'(4'h4)]).m_status) <
        ((Bit#(3))'(3'h4)))) && ((((x_1)[(Bit#(4))'(4'h4)]).m_addr) ==
        (x_7))) || ((((((x_1)[(Bit#(4))'(4'h4)]).m_status) ==
        ((Bit#(3))'(3'h4))) || ((((x_1)[(Bit#(4))'(4'h4)]).m_status) ==
        ((Bit#(3))'(3'h6)))) && ((! ((((x_1)[(Bit#(4))'(4'h4)]).m_addr) ==
        (x_7))) && (((((x_1)[(Bit#(4))'(4'h4)]).m_addr)[13:5]) ==
        ((x_7)[13:5])))) ? ((Bool)'(True)) : ((((!
        ((((x_1)[(Bit#(4))'(4'h5)]).m_status) < ((Bit#(3))'(3'h4)))) &&
        ((((x_1)[(Bit#(4))'(4'h5)]).m_addr) == (x_7))) ||
        ((((((x_1)[(Bit#(4))'(4'h5)]).m_status) == ((Bit#(3))'(3'h4))) ||
        ((((x_1)[(Bit#(4))'(4'h5)]).m_status) == ((Bit#(3))'(3'h6)))) && ((!
        ((((x_1)[(Bit#(4))'(4'h5)]).m_addr) == (x_7))) &&
        (((((x_1)[(Bit#(4))'(4'h5)]).m_addr)[13:5]) == ((x_7)[13:5])))) ?
        ((Bool)'(True)) : ((((! ((((x_1)[(Bit#(4))'(4'h6)]).m_status) <
        ((Bit#(3))'(3'h4)))) && ((((x_1)[(Bit#(4))'(4'h6)]).m_addr) ==
        (x_7))) || ((((((x_1)[(Bit#(4))'(4'h6)]).m_status) ==
        ((Bit#(3))'(3'h4))) || ((((x_1)[(Bit#(4))'(4'h6)]).m_status) ==
        ((Bit#(3))'(3'h6)))) && ((! ((((x_1)[(Bit#(4))'(4'h6)]).m_addr) ==
        (x_7))) && (((((x_1)[(Bit#(4))'(4'h6)]).m_addr)[13:5]) ==
        ((x_7)[13:5])))) ? ((Bool)'(True)) : ((((!
        ((((x_1)[(Bit#(4))'(4'h7)]).m_status) < ((Bit#(3))'(3'h4)))) &&
        ((((x_1)[(Bit#(4))'(4'h7)]).m_addr) == (x_7))) ||
        ((((((x_1)[(Bit#(4))'(4'h7)]).m_status) == ((Bit#(3))'(3'h4))) ||
        ((((x_1)[(Bit#(4))'(4'h7)]).m_status) == ((Bit#(3))'(3'h6)))) && ((!
        ((((x_1)[(Bit#(4))'(4'h7)]).m_addr) == (x_7))) &&
        (((((x_1)[(Bit#(4))'(4'h7)]).m_addr)[13:5]) == ((x_7)[13:5])))) ?
        ((Bool)'(True)) : ((((! ((((x_1)[(Bit#(4))'(4'h8)]).m_status) <
        ((Bit#(3))'(3'h4)))) && ((((x_1)[(Bit#(4))'(4'h8)]).m_addr) ==
        (x_7))) || ((((((x_1)[(Bit#(4))'(4'h8)]).m_status) ==
        ((Bit#(3))'(3'h4))) || ((((x_1)[(Bit#(4))'(4'h8)]).m_status) ==
        ((Bit#(3))'(3'h6)))) && ((! ((((x_1)[(Bit#(4))'(4'h8)]).m_addr) ==
        (x_7))) && (((((x_1)[(Bit#(4))'(4'h8)]).m_addr)[13:5]) ==
        ((x_7)[13:5])))) ? ((Bool)'(True)) : ((((!
        ((((x_1)[(Bit#(4))'(4'h9)]).m_status) < ((Bit#(3))'(3'h4)))) &&
        ((((x_1)[(Bit#(4))'(4'h9)]).m_addr) == (x_7))) ||
        ((((((x_1)[(Bit#(4))'(4'h9)]).m_status) == ((Bit#(3))'(3'h4))) ||
        ((((x_1)[(Bit#(4))'(4'h9)]).m_status) == ((Bit#(3))'(3'h6)))) && ((!
        ((((x_1)[(Bit#(4))'(4'h9)]).m_addr) == (x_7))) &&
        (((((x_1)[(Bit#(4))'(4'h9)]).m_addr)[13:5]) == ((x_7)[13:5])))) ?
        ((Bool)'(True)) : ((((! ((((x_1)[(Bit#(4))'(4'ha)]).m_status) <
        ((Bit#(3))'(3'h4)))) && ((((x_1)[(Bit#(4))'(4'ha)]).m_addr) ==
        (x_7))) || ((((((x_1)[(Bit#(4))'(4'ha)]).m_status) ==
        ((Bit#(3))'(3'h4))) || ((((x_1)[(Bit#(4))'(4'ha)]).m_status) ==
        ((Bit#(3))'(3'h6)))) && ((! ((((x_1)[(Bit#(4))'(4'ha)]).m_addr) ==
        (x_7))) && (((((x_1)[(Bit#(4))'(4'ha)]).m_addr)[13:5]) ==
        ((x_7)[13:5])))) ? ((Bool)'(True)) : ((((!
        ((((x_1)[(Bit#(4))'(4'hb)]).m_status) < ((Bit#(3))'(3'h4)))) &&
        ((((x_1)[(Bit#(4))'(4'hb)]).m_addr) == (x_7))) ||
        ((((((x_1)[(Bit#(4))'(4'hb)]).m_status) == ((Bit#(3))'(3'h4))) ||
        ((((x_1)[(Bit#(4))'(4'hb)]).m_status) == ((Bit#(3))'(3'h6)))) && ((!
        ((((x_1)[(Bit#(4))'(4'hb)]).m_addr) == (x_7))) &&
        (((((x_1)[(Bit#(4))'(4'hb)]).m_addr)[13:5]) == ((x_7)[13:5])))) ?
        ((Bool)'(True)) : ((Bool)'(False))))))))))))))))))))))))));
        when (! (x_8), noAction);
        mshrs_00 <= update (x_1, x_4, Struct15 {m_status : (Bit#(3))'(3'h4),
        m_next : (x_5).m_next, m_is_ul : (x_5).m_is_ul, m_addr :
        (x_5).m_addr, m_qidx : (x_5).m_qidx, m_rsb : (x_5).m_rsb,
        m_dl_rss_from : (x_5).m_dl_rss_from, m_dl_rss_recv :
        (x_5).m_dl_rss_recv});
        Struct3 x_9 = (Struct3 {r_id : x_4, r_msg : x_6, r_msg_from :
        (x_5).m_qidx});
        return x_9;
    endmethod

    method Action registerUL_00 (Struct21 x_0);
        let x_1 = (mshrs_00);
        Bit#(4) x_2 = ((x_0).r_id);
        Struct15 x_3 = ((x_1)[x_2]);
        Struct15 x_4 = (Struct15 {m_status : (Bit#(3))'(3'h5), m_next :
        (x_3).m_next, m_is_ul : (Bool)'(True), m_addr : (x_3).m_addr, m_qidx
        : {((Bit#(2))'(2'h2)),((x_0).r_ul_rsbTo)}, m_rsb : (x_0).r_ul_rsb,
        m_dl_rss_from : unpack(0), m_dl_rss_recv : unpack(0)});
        mshrs_00 <= update (x_1, x_2, x_4);
    endmethod

    method Action registerDL_00 (Struct22 x_0);
        Bit#(4) x_1 = ((x_0).r_id);
        let x_2 = (mshrs_00);
        Struct15 x_3 = ((x_2)[x_1]);
        Struct15 x_4 = (Struct15 {m_status : (Bit#(3))'(3'h5), m_next :
        (x_3).m_next, m_is_ul : (Bool)'(False), m_addr : (x_3).m_addr, m_qidx
        : (x_0).r_dl_rsbTo, m_rsb : (x_0).r_dl_rsb, m_dl_rss_from :
        (x_0).r_dl_rss_from, m_dl_rss_recv : unpack(0)});
        mshrs_00 <= update (x_2, x_1, x_4);
    endmethod

    method Action canImm_00 (Bit#(64) x_0);
        let x_1 = (mshrs_00);
        Struct16 x_2 = (((((x_1)[(Bit#(4))'(4'h4)]).m_status) ==
        ((Bit#(3))'(3'h0)) ? (Struct16 {valid : (Bool)'(True), data :
        (Bit#(4))'(4'h4)}) : (((((x_1)[(Bit#(4))'(4'h5)]).m_status) ==
        ((Bit#(3))'(3'h0)) ? (Struct16 {valid : (Bool)'(True), data :
        (Bit#(4))'(4'h5)}) : (((((x_1)[(Bit#(4))'(4'h6)]).m_status) ==
        ((Bit#(3))'(3'h0)) ? (Struct16 {valid : (Bool)'(True), data :
        (Bit#(4))'(4'h6)}) : (((((x_1)[(Bit#(4))'(4'h7)]).m_status) ==
        ((Bit#(3))'(3'h0)) ? (Struct16 {valid : (Bool)'(True), data :
        (Bit#(4))'(4'h7)}) : (((((x_1)[(Bit#(4))'(4'h8)]).m_status) ==
        ((Bit#(3))'(3'h0)) ? (Struct16 {valid : (Bool)'(True), data :
        (Bit#(4))'(4'h8)}) : (((((x_1)[(Bit#(4))'(4'h9)]).m_status) ==
        ((Bit#(3))'(3'h0)) ? (Struct16 {valid : (Bool)'(True), data :
        (Bit#(4))'(4'h9)}) : (((((x_1)[(Bit#(4))'(4'ha)]).m_status) ==
        ((Bit#(3))'(3'h0)) ? (Struct16 {valid : (Bool)'(True), data :
        (Bit#(4))'(4'ha)}) : (((((x_1)[(Bit#(4))'(4'hb)]).m_status) ==
        ((Bit#(3))'(3'h0)) ? (Struct16 {valid : (Bool)'(True), data :
        (Bit#(4))'(4'hb)}) : (Struct16 {valid : (Bool)'(False), data :
        unpack(0)})))))))))))))))));
        when ((x_2).valid, noAction);
        Struct16 x_3 = ((((! ((((x_1)[(Bit#(4))'(4'h0)]).m_status) ==
        ((Bit#(3))'(3'h0)))) && (!
        ((((x_1)[(Bit#(4))'(4'h0)]).m_next).valid))) &&
        ((((x_1)[(Bit#(4))'(4'h0)]).m_addr) == (x_0)) ? (Struct16 {valid :
        (Bool)'(True), data : (Bit#(4))'(4'h0)}) : ((((!
        ((((x_1)[(Bit#(4))'(4'h1)]).m_status) == ((Bit#(3))'(3'h0)))) && (!
        ((((x_1)[(Bit#(4))'(4'h1)]).m_next).valid))) &&
        ((((x_1)[(Bit#(4))'(4'h1)]).m_addr) == (x_0)) ? (Struct16 {valid :
        (Bool)'(True), data : (Bit#(4))'(4'h1)}) : ((((!
        ((((x_1)[(Bit#(4))'(4'h2)]).m_status) == ((Bit#(3))'(3'h0)))) && (!
        ((((x_1)[(Bit#(4))'(4'h2)]).m_next).valid))) &&
        ((((x_1)[(Bit#(4))'(4'h2)]).m_addr) == (x_0)) ? (Struct16 {valid :
        (Bool)'(True), data : (Bit#(4))'(4'h2)}) : ((((!
        ((((x_1)[(Bit#(4))'(4'h3)]).m_status) == ((Bit#(3))'(3'h0)))) && (!
        ((((x_1)[(Bit#(4))'(4'h3)]).m_next).valid))) &&
        ((((x_1)[(Bit#(4))'(4'h3)]).m_addr) == (x_0)) ? (Struct16 {valid :
        (Bool)'(True), data : (Bit#(4))'(4'h3)}) : ((((!
        ((((x_1)[(Bit#(4))'(4'h4)]).m_status) == ((Bit#(3))'(3'h0)))) && (!
        ((((x_1)[(Bit#(4))'(4'h4)]).m_next).valid))) &&
        ((((x_1)[(Bit#(4))'(4'h4)]).m_addr) == (x_0)) ? (Struct16 {valid :
        (Bool)'(True), data : (Bit#(4))'(4'h4)}) : ((((!
        ((((x_1)[(Bit#(4))'(4'h5)]).m_status) == ((Bit#(3))'(3'h0)))) && (!
        ((((x_1)[(Bit#(4))'(4'h5)]).m_next).valid))) &&
        ((((x_1)[(Bit#(4))'(4'h5)]).m_addr) == (x_0)) ? (Struct16 {valid :
        (Bool)'(True), data : (Bit#(4))'(4'h5)}) : ((((!
        ((((x_1)[(Bit#(4))'(4'h6)]).m_status) == ((Bit#(3))'(3'h0)))) && (!
        ((((x_1)[(Bit#(4))'(4'h6)]).m_next).valid))) &&
        ((((x_1)[(Bit#(4))'(4'h6)]).m_addr) == (x_0)) ? (Struct16 {valid :
        (Bool)'(True), data : (Bit#(4))'(4'h6)}) : ((((!
        ((((x_1)[(Bit#(4))'(4'h7)]).m_status) == ((Bit#(3))'(3'h0)))) && (!
        ((((x_1)[(Bit#(4))'(4'h7)]).m_next).valid))) &&
        ((((x_1)[(Bit#(4))'(4'h7)]).m_addr) == (x_0)) ? (Struct16 {valid :
        (Bool)'(True), data : (Bit#(4))'(4'h7)}) : ((((!
        ((((x_1)[(Bit#(4))'(4'h8)]).m_status) == ((Bit#(3))'(3'h0)))) && (!
        ((((x_1)[(Bit#(4))'(4'h8)]).m_next).valid))) &&
        ((((x_1)[(Bit#(4))'(4'h8)]).m_addr) == (x_0)) ? (Struct16 {valid :
        (Bool)'(True), data : (Bit#(4))'(4'h8)}) : ((((!
        ((((x_1)[(Bit#(4))'(4'h9)]).m_status) == ((Bit#(3))'(3'h0)))) && (!
        ((((x_1)[(Bit#(4))'(4'h9)]).m_next).valid))) &&
        ((((x_1)[(Bit#(4))'(4'h9)]).m_addr) == (x_0)) ? (Struct16 {valid :
        (Bool)'(True), data : (Bit#(4))'(4'h9)}) : ((((!
        ((((x_1)[(Bit#(4))'(4'ha)]).m_status) == ((Bit#(3))'(3'h0)))) && (!
        ((((x_1)[(Bit#(4))'(4'ha)]).m_next).valid))) &&
        ((((x_1)[(Bit#(4))'(4'ha)]).m_addr) == (x_0)) ? (Struct16 {valid :
        (Bool)'(True), data : (Bit#(4))'(4'ha)}) : ((((!
        ((((x_1)[(Bit#(4))'(4'hb)]).m_status) == ((Bit#(3))'(3'h0)))) && (!
        ((((x_1)[(Bit#(4))'(4'hb)]).m_next).valid))) &&
        ((((x_1)[(Bit#(4))'(4'hb)]).m_addr) == (x_0)) ? (Struct16 {valid :
        (Bool)'(True), data : (Bit#(4))'(4'hb)}) : (Struct16 {valid :
        (Bool)'(False), data : unpack(0)})))))))))))))))))))))))));
        when (! ((x_3).valid), noAction);
    endmethod

    method Action setULImm_00 (Struct1 x_0);
        let x_1 = (mshrs_00);
        let x_2 = (rqs_00);
        Struct16 x_3 = (((((x_1)[(Bit#(4))'(4'h4)]).m_status) ==
        ((Bit#(3))'(3'h0)) ? (Struct16 {valid : (Bool)'(True), data :
        (Bit#(4))'(4'h4)}) : (((((x_1)[(Bit#(4))'(4'h5)]).m_status) ==
        ((Bit#(3))'(3'h0)) ? (Struct16 {valid : (Bool)'(True), data :
        (Bit#(4))'(4'h5)}) : (((((x_1)[(Bit#(4))'(4'h6)]).m_status) ==
        ((Bit#(3))'(3'h0)) ? (Struct16 {valid : (Bool)'(True), data :
        (Bit#(4))'(4'h6)}) : (((((x_1)[(Bit#(4))'(4'h7)]).m_status) ==
        ((Bit#(3))'(3'h0)) ? (Struct16 {valid : (Bool)'(True), data :
        (Bit#(4))'(4'h7)}) : (((((x_1)[(Bit#(4))'(4'h8)]).m_status) ==
        ((Bit#(3))'(3'h0)) ? (Struct16 {valid : (Bool)'(True), data :
        (Bit#(4))'(4'h8)}) : (((((x_1)[(Bit#(4))'(4'h9)]).m_status) ==
        ((Bit#(3))'(3'h0)) ? (Struct16 {valid : (Bool)'(True), data :
        (Bit#(4))'(4'h9)}) : (((((x_1)[(Bit#(4))'(4'ha)]).m_status) ==
        ((Bit#(3))'(3'h0)) ? (Struct16 {valid : (Bool)'(True), data :
        (Bit#(4))'(4'ha)}) : (((((x_1)[(Bit#(4))'(4'hb)]).m_status) ==
        ((Bit#(3))'(3'h0)) ? (Struct16 {valid : (Bool)'(True), data :
        (Bit#(4))'(4'hb)}) : (Struct16 {valid : (Bool)'(False), data :
        unpack(0)})))))))))))))))));
        when ((x_3).valid, noAction);
        Bit#(4) x_4 = ((x_3).data);
        Bit#(64) x_5 = ((x_0).addr);
        Struct16 x_6 = (((! ((((x_1)[(Bit#(4))'(4'h0)]).m_status) ==
        ((Bit#(3))'(3'h0)))) && ((((x_1)[(Bit#(4))'(4'h0)]).m_addr) == (x_5))
        ? (Struct16 {valid : (Bool)'(True), data : (Bit#(4))'(4'h0)}) : (((!
        ((((x_1)[(Bit#(4))'(4'h1)]).m_status) == ((Bit#(3))'(3'h0)))) &&
        ((((x_1)[(Bit#(4))'(4'h1)]).m_addr) == (x_5)) ? (Struct16 {valid :
        (Bool)'(True), data : (Bit#(4))'(4'h1)}) : (((!
        ((((x_1)[(Bit#(4))'(4'h2)]).m_status) == ((Bit#(3))'(3'h0)))) &&
        ((((x_1)[(Bit#(4))'(4'h2)]).m_addr) == (x_5)) ? (Struct16 {valid :
        (Bool)'(True), data : (Bit#(4))'(4'h2)}) : (((!
        ((((x_1)[(Bit#(4))'(4'h3)]).m_status) == ((Bit#(3))'(3'h0)))) &&
        ((((x_1)[(Bit#(4))'(4'h3)]).m_addr) == (x_5)) ? (Struct16 {valid :
        (Bool)'(True), data : (Bit#(4))'(4'h3)}) : (((!
        ((((x_1)[(Bit#(4))'(4'h4)]).m_status) == ((Bit#(3))'(3'h0)))) &&
        ((((x_1)[(Bit#(4))'(4'h4)]).m_addr) == (x_5)) ? (Struct16 {valid :
        (Bool)'(True), data : (Bit#(4))'(4'h4)}) : (((!
        ((((x_1)[(Bit#(4))'(4'h5)]).m_status) == ((Bit#(3))'(3'h0)))) &&
        ((((x_1)[(Bit#(4))'(4'h5)]).m_addr) == (x_5)) ? (Struct16 {valid :
        (Bool)'(True), data : (Bit#(4))'(4'h5)}) : (((!
        ((((x_1)[(Bit#(4))'(4'h6)]).m_status) == ((Bit#(3))'(3'h0)))) &&
        ((((x_1)[(Bit#(4))'(4'h6)]).m_addr) == (x_5)) ? (Struct16 {valid :
        (Bool)'(True), data : (Bit#(4))'(4'h6)}) : (((!
        ((((x_1)[(Bit#(4))'(4'h7)]).m_status) == ((Bit#(3))'(3'h0)))) &&
        ((((x_1)[(Bit#(4))'(4'h7)]).m_addr) == (x_5)) ? (Struct16 {valid :
        (Bool)'(True), data : (Bit#(4))'(4'h7)}) : (((!
        ((((x_1)[(Bit#(4))'(4'h8)]).m_status) == ((Bit#(3))'(3'h0)))) &&
        ((((x_1)[(Bit#(4))'(4'h8)]).m_addr) == (x_5)) ? (Struct16 {valid :
        (Bool)'(True), data : (Bit#(4))'(4'h8)}) : (((!
        ((((x_1)[(Bit#(4))'(4'h9)]).m_status) == ((Bit#(3))'(3'h0)))) &&
        ((((x_1)[(Bit#(4))'(4'h9)]).m_addr) == (x_5)) ? (Struct16 {valid :
        (Bool)'(True), data : (Bit#(4))'(4'h9)}) : (((!
        ((((x_1)[(Bit#(4))'(4'ha)]).m_status) == ((Bit#(3))'(3'h0)))) &&
        ((((x_1)[(Bit#(4))'(4'ha)]).m_addr) == (x_5)) ? (Struct16 {valid :
        (Bool)'(True), data : (Bit#(4))'(4'ha)}) : (((!
        ((((x_1)[(Bit#(4))'(4'hb)]).m_status) == ((Bit#(3))'(3'h0)))) &&
        ((((x_1)[(Bit#(4))'(4'hb)]).m_addr) == (x_5)) ? (Struct16 {valid :
        (Bool)'(True), data : (Bit#(4))'(4'hb)}) : (Struct16 {valid :
        (Bool)'(False), data : unpack(0)})))))))))))))))))))))))));
        when (! ((x_6).valid), noAction);
        mshrs_00 <= update (x_1, x_4, Struct15 {m_status : (Bit#(3))'(3'h5),
        m_next : Struct16 {valid : (Bool)'(False), data : unpack(0)}, m_is_ul
        : (Bool)'(True), m_addr : (x_0).addr, m_qidx : unpack(0), m_rsb :
        (Bool)'(False), m_dl_rss_from : unpack(0), m_dl_rss_recv :
        unpack(0)});
        rqs_00 <= update (x_2, x_4, x_0);
    endmethod

    method Action transferUpDown_00 (Struct25 x_0);
        Bit#(4) x_1 = ((x_0).r_id);
        let x_2 = (mshrs_00);
        Struct15 x_3 = ((x_2)[x_1]);
        Struct15 x_4 = (Struct15 {m_status : (Bit#(3))'(3'h5), m_next :
        (x_3).m_next, m_is_ul : (Bool)'(False), m_addr : (x_3).m_addr, m_qidx
        : (x_3).m_qidx, m_rsb : (x_3).m_rsb, m_dl_rss_from :
        (x_0).r_dl_rss_from, m_dl_rss_recv : unpack(0)});
        mshrs_00 <= update (x_2, x_1, x_4);
    endmethod

    method Action addRs_00 (Struct7 x_0);
        let x_1 = (mshrs_00);
        Bit#(64) x_2 = (((x_0).r_msg).addr);
        Struct16 x_3 = (((((((x_1)[(Bit#(4))'(4'h0)]).m_status) ==
        ((Bit#(3))'(3'h5))) && (! (((x_1)[(Bit#(4))'(4'h0)]).m_is_ul))) &&
        ((((x_1)[(Bit#(4))'(4'h0)]).m_addr) == (x_2)) ? (Struct16 {valid :
        (Bool)'(True), data : (Bit#(4))'(4'h0)}) :
        (((((((x_1)[(Bit#(4))'(4'h1)]).m_status) == ((Bit#(3))'(3'h5))) && (!
        (((x_1)[(Bit#(4))'(4'h1)]).m_is_ul))) &&
        ((((x_1)[(Bit#(4))'(4'h1)]).m_addr) == (x_2)) ? (Struct16 {valid :
        (Bool)'(True), data : (Bit#(4))'(4'h1)}) :
        (((((((x_1)[(Bit#(4))'(4'h2)]).m_status) == ((Bit#(3))'(3'h5))) && (!
        (((x_1)[(Bit#(4))'(4'h2)]).m_is_ul))) &&
        ((((x_1)[(Bit#(4))'(4'h2)]).m_addr) == (x_2)) ? (Struct16 {valid :
        (Bool)'(True), data : (Bit#(4))'(4'h2)}) :
        (((((((x_1)[(Bit#(4))'(4'h3)]).m_status) == ((Bit#(3))'(3'h5))) && (!
        (((x_1)[(Bit#(4))'(4'h3)]).m_is_ul))) &&
        ((((x_1)[(Bit#(4))'(4'h3)]).m_addr) == (x_2)) ? (Struct16 {valid :
        (Bool)'(True), data : (Bit#(4))'(4'h3)}) :
        (((((((x_1)[(Bit#(4))'(4'h4)]).m_status) == ((Bit#(3))'(3'h5))) && (!
        (((x_1)[(Bit#(4))'(4'h4)]).m_is_ul))) &&
        ((((x_1)[(Bit#(4))'(4'h4)]).m_addr) == (x_2)) ? (Struct16 {valid :
        (Bool)'(True), data : (Bit#(4))'(4'h4)}) :
        (((((((x_1)[(Bit#(4))'(4'h5)]).m_status) == ((Bit#(3))'(3'h5))) && (!
        (((x_1)[(Bit#(4))'(4'h5)]).m_is_ul))) &&
        ((((x_1)[(Bit#(4))'(4'h5)]).m_addr) == (x_2)) ? (Struct16 {valid :
        (Bool)'(True), data : (Bit#(4))'(4'h5)}) :
        (((((((x_1)[(Bit#(4))'(4'h6)]).m_status) == ((Bit#(3))'(3'h5))) && (!
        (((x_1)[(Bit#(4))'(4'h6)]).m_is_ul))) &&
        ((((x_1)[(Bit#(4))'(4'h6)]).m_addr) == (x_2)) ? (Struct16 {valid :
        (Bool)'(True), data : (Bit#(4))'(4'h6)}) :
        (((((((x_1)[(Bit#(4))'(4'h7)]).m_status) == ((Bit#(3))'(3'h5))) && (!
        (((x_1)[(Bit#(4))'(4'h7)]).m_is_ul))) &&
        ((((x_1)[(Bit#(4))'(4'h7)]).m_addr) == (x_2)) ? (Struct16 {valid :
        (Bool)'(True), data : (Bit#(4))'(4'h7)}) :
        (((((((x_1)[(Bit#(4))'(4'h8)]).m_status) == ((Bit#(3))'(3'h5))) && (!
        (((x_1)[(Bit#(4))'(4'h8)]).m_is_ul))) &&
        ((((x_1)[(Bit#(4))'(4'h8)]).m_addr) == (x_2)) ? (Struct16 {valid :
        (Bool)'(True), data : (Bit#(4))'(4'h8)}) :
        (((((((x_1)[(Bit#(4))'(4'h9)]).m_status) == ((Bit#(3))'(3'h5))) && (!
        (((x_1)[(Bit#(4))'(4'h9)]).m_is_ul))) &&
        ((((x_1)[(Bit#(4))'(4'h9)]).m_addr) == (x_2)) ? (Struct16 {valid :
        (Bool)'(True), data : (Bit#(4))'(4'h9)}) :
        (((((((x_1)[(Bit#(4))'(4'ha)]).m_status) == ((Bit#(3))'(3'h5))) && (!
        (((x_1)[(Bit#(4))'(4'ha)]).m_is_ul))) &&
        ((((x_1)[(Bit#(4))'(4'ha)]).m_addr) == (x_2)) ? (Struct16 {valid :
        (Bool)'(True), data : (Bit#(4))'(4'ha)}) :
        (((((((x_1)[(Bit#(4))'(4'hb)]).m_status) == ((Bit#(3))'(3'h5))) && (!
        (((x_1)[(Bit#(4))'(4'hb)]).m_is_ul))) &&
        ((((x_1)[(Bit#(4))'(4'hb)]).m_addr) == (x_2)) ? (Struct16 {valid :
        (Bool)'(True), data : (Bit#(4))'(4'hb)}) : (Struct16 {valid :
        (Bool)'(False), data : unpack(0)})))))))))))))))))))))))));
        when ((x_3).valid, noAction);
        Bit#(4) x_4 = ((x_3).data);
        Struct15 x_5 = ((x_1)[x_4]);
        mshrs_00 <= update (x_1, x_4, Struct15 {m_status : (x_5).m_status,
        m_next : (x_5).m_next, m_is_ul : (x_5).m_is_ul, m_addr :
        (x_5).m_addr, m_qidx : (x_5).m_qidx, m_rsb : (x_5).m_rsb,
        m_dl_rss_from : (x_5).m_dl_rss_from, m_dl_rss_recv :
        ((x_5).m_dl_rss_recv) | (((Bit#(2))'(2'h1)) << ((x_0).r_midx))});
        let x_6 = (rss_00);
        Struct37 x_7 = ((x_6)[x_4]);
        rss_00 <= update (x_6, x_4, Struct37 {m_dl_rss : update
        ((x_7).m_dl_rss, (x_0).r_midx, (x_0).r_msg)});
    endmethod

    method ActionValue#(Bit#(4)) getULReady_00 (Bit#(64) x_0);
        let x_1 = (mshrs_00);
        Bool x_2 = (((((((x_1)[(Bit#(4))'(4'h0)]).m_status) ==
        ((Bit#(3))'(3'h4))) || ((((x_1)[(Bit#(4))'(4'h0)]).m_status) ==
        ((Bit#(3))'(3'h6)))) && ((! ((((x_1)[(Bit#(4))'(4'h0)]).m_addr) ==
        (x_0))) && (((((x_1)[(Bit#(4))'(4'h0)]).m_addr)[13:5]) ==
        ((x_0)[13:5]))) ? ((Bool)'(True)) :
        (((((((x_1)[(Bit#(4))'(4'h1)]).m_status) == ((Bit#(3))'(3'h4))) ||
        ((((x_1)[(Bit#(4))'(4'h1)]).m_status) == ((Bit#(3))'(3'h6)))) && ((!
        ((((x_1)[(Bit#(4))'(4'h1)]).m_addr) == (x_0))) &&
        (((((x_1)[(Bit#(4))'(4'h1)]).m_addr)[13:5]) == ((x_0)[13:5]))) ?
        ((Bool)'(True)) : (((((((x_1)[(Bit#(4))'(4'h2)]).m_status) ==
        ((Bit#(3))'(3'h4))) || ((((x_1)[(Bit#(4))'(4'h2)]).m_status) ==
        ((Bit#(3))'(3'h6)))) && ((! ((((x_1)[(Bit#(4))'(4'h2)]).m_addr) ==
        (x_0))) && (((((x_1)[(Bit#(4))'(4'h2)]).m_addr)[13:5]) ==
        ((x_0)[13:5]))) ? ((Bool)'(True)) :
        (((((((x_1)[(Bit#(4))'(4'h3)]).m_status) == ((Bit#(3))'(3'h4))) ||
        ((((x_1)[(Bit#(4))'(4'h3)]).m_status) == ((Bit#(3))'(3'h6)))) && ((!
        ((((x_1)[(Bit#(4))'(4'h3)]).m_addr) == (x_0))) &&
        (((((x_1)[(Bit#(4))'(4'h3)]).m_addr)[13:5]) == ((x_0)[13:5]))) ?
        ((Bool)'(True)) : (((((((x_1)[(Bit#(4))'(4'h4)]).m_status) ==
        ((Bit#(3))'(3'h4))) || ((((x_1)[(Bit#(4))'(4'h4)]).m_status) ==
        ((Bit#(3))'(3'h6)))) && ((! ((((x_1)[(Bit#(4))'(4'h4)]).m_addr) ==
        (x_0))) && (((((x_1)[(Bit#(4))'(4'h4)]).m_addr)[13:5]) ==
        ((x_0)[13:5]))) ? ((Bool)'(True)) :
        (((((((x_1)[(Bit#(4))'(4'h5)]).m_status) == ((Bit#(3))'(3'h4))) ||
        ((((x_1)[(Bit#(4))'(4'h5)]).m_status) == ((Bit#(3))'(3'h6)))) && ((!
        ((((x_1)[(Bit#(4))'(4'h5)]).m_addr) == (x_0))) &&
        (((((x_1)[(Bit#(4))'(4'h5)]).m_addr)[13:5]) == ((x_0)[13:5]))) ?
        ((Bool)'(True)) : (((((((x_1)[(Bit#(4))'(4'h6)]).m_status) ==
        ((Bit#(3))'(3'h4))) || ((((x_1)[(Bit#(4))'(4'h6)]).m_status) ==
        ((Bit#(3))'(3'h6)))) && ((! ((((x_1)[(Bit#(4))'(4'h6)]).m_addr) ==
        (x_0))) && (((((x_1)[(Bit#(4))'(4'h6)]).m_addr)[13:5]) ==
        ((x_0)[13:5]))) ? ((Bool)'(True)) :
        (((((((x_1)[(Bit#(4))'(4'h7)]).m_status) == ((Bit#(3))'(3'h4))) ||
        ((((x_1)[(Bit#(4))'(4'h7)]).m_status) == ((Bit#(3))'(3'h6)))) && ((!
        ((((x_1)[(Bit#(4))'(4'h7)]).m_addr) == (x_0))) &&
        (((((x_1)[(Bit#(4))'(4'h7)]).m_addr)[13:5]) == ((x_0)[13:5]))) ?
        ((Bool)'(True)) : (((((((x_1)[(Bit#(4))'(4'h8)]).m_status) ==
        ((Bit#(3))'(3'h4))) || ((((x_1)[(Bit#(4))'(4'h8)]).m_status) ==
        ((Bit#(3))'(3'h6)))) && ((! ((((x_1)[(Bit#(4))'(4'h8)]).m_addr) ==
        (x_0))) && (((((x_1)[(Bit#(4))'(4'h8)]).m_addr)[13:5]) ==
        ((x_0)[13:5]))) ? ((Bool)'(True)) :
        (((((((x_1)[(Bit#(4))'(4'h9)]).m_status) == ((Bit#(3))'(3'h4))) ||
        ((((x_1)[(Bit#(4))'(4'h9)]).m_status) == ((Bit#(3))'(3'h6)))) && ((!
        ((((x_1)[(Bit#(4))'(4'h9)]).m_addr) == (x_0))) &&
        (((((x_1)[(Bit#(4))'(4'h9)]).m_addr)[13:5]) == ((x_0)[13:5]))) ?
        ((Bool)'(True)) : (((((((x_1)[(Bit#(4))'(4'ha)]).m_status) ==
        ((Bit#(3))'(3'h4))) || ((((x_1)[(Bit#(4))'(4'ha)]).m_status) ==
        ((Bit#(3))'(3'h6)))) && ((! ((((x_1)[(Bit#(4))'(4'ha)]).m_addr) ==
        (x_0))) && (((((x_1)[(Bit#(4))'(4'ha)]).m_addr)[13:5]) ==
        ((x_0)[13:5]))) ? ((Bool)'(True)) :
        (((((((x_1)[(Bit#(4))'(4'hb)]).m_status) == ((Bit#(3))'(3'h4))) ||
        ((((x_1)[(Bit#(4))'(4'hb)]).m_status) == ((Bit#(3))'(3'h6)))) && ((!
        ((((x_1)[(Bit#(4))'(4'hb)]).m_addr) == (x_0))) &&
        (((((x_1)[(Bit#(4))'(4'hb)]).m_addr)[13:5]) == ((x_0)[13:5]))) ?
        ((Bool)'(True)) : ((Bool)'(False))))))))))))))))))))))))));
        when (! (x_2), noAction);
        Struct16 x_3 = ((((! ((((x_1)[(Bit#(4))'(4'h0)]).m_status) <
        ((Bit#(3))'(3'h4)))) && (! (((x_1)[(Bit#(4))'(4'h0)]).m_is_ul))) &&
        ((((x_1)[(Bit#(4))'(4'h0)]).m_addr) == (x_0)) ? (Struct16 {valid :
        (Bool)'(True), data : (Bit#(4))'(4'h0)}) : ((((!
        ((((x_1)[(Bit#(4))'(4'h1)]).m_status) < ((Bit#(3))'(3'h4)))) && (!
        (((x_1)[(Bit#(4))'(4'h1)]).m_is_ul))) &&
        ((((x_1)[(Bit#(4))'(4'h1)]).m_addr) == (x_0)) ? (Struct16 {valid :
        (Bool)'(True), data : (Bit#(4))'(4'h1)}) : ((((!
        ((((x_1)[(Bit#(4))'(4'h2)]).m_status) < ((Bit#(3))'(3'h4)))) && (!
        (((x_1)[(Bit#(4))'(4'h2)]).m_is_ul))) &&
        ((((x_1)[(Bit#(4))'(4'h2)]).m_addr) == (x_0)) ? (Struct16 {valid :
        (Bool)'(True), data : (Bit#(4))'(4'h2)}) : ((((!
        ((((x_1)[(Bit#(4))'(4'h3)]).m_status) < ((Bit#(3))'(3'h4)))) && (!
        (((x_1)[(Bit#(4))'(4'h3)]).m_is_ul))) &&
        ((((x_1)[(Bit#(4))'(4'h3)]).m_addr) == (x_0)) ? (Struct16 {valid :
        (Bool)'(True), data : (Bit#(4))'(4'h3)}) : ((((!
        ((((x_1)[(Bit#(4))'(4'h4)]).m_status) < ((Bit#(3))'(3'h4)))) && (!
        (((x_1)[(Bit#(4))'(4'h4)]).m_is_ul))) &&
        ((((x_1)[(Bit#(4))'(4'h4)]).m_addr) == (x_0)) ? (Struct16 {valid :
        (Bool)'(True), data : (Bit#(4))'(4'h4)}) : ((((!
        ((((x_1)[(Bit#(4))'(4'h5)]).m_status) < ((Bit#(3))'(3'h4)))) && (!
        (((x_1)[(Bit#(4))'(4'h5)]).m_is_ul))) &&
        ((((x_1)[(Bit#(4))'(4'h5)]).m_addr) == (x_0)) ? (Struct16 {valid :
        (Bool)'(True), data : (Bit#(4))'(4'h5)}) : ((((!
        ((((x_1)[(Bit#(4))'(4'h6)]).m_status) < ((Bit#(3))'(3'h4)))) && (!
        (((x_1)[(Bit#(4))'(4'h6)]).m_is_ul))) &&
        ((((x_1)[(Bit#(4))'(4'h6)]).m_addr) == (x_0)) ? (Struct16 {valid :
        (Bool)'(True), data : (Bit#(4))'(4'h6)}) : ((((!
        ((((x_1)[(Bit#(4))'(4'h7)]).m_status) < ((Bit#(3))'(3'h4)))) && (!
        (((x_1)[(Bit#(4))'(4'h7)]).m_is_ul))) &&
        ((((x_1)[(Bit#(4))'(4'h7)]).m_addr) == (x_0)) ? (Struct16 {valid :
        (Bool)'(True), data : (Bit#(4))'(4'h7)}) : ((((!
        ((((x_1)[(Bit#(4))'(4'h8)]).m_status) < ((Bit#(3))'(3'h4)))) && (!
        (((x_1)[(Bit#(4))'(4'h8)]).m_is_ul))) &&
        ((((x_1)[(Bit#(4))'(4'h8)]).m_addr) == (x_0)) ? (Struct16 {valid :
        (Bool)'(True), data : (Bit#(4))'(4'h8)}) : ((((!
        ((((x_1)[(Bit#(4))'(4'h9)]).m_status) < ((Bit#(3))'(3'h4)))) && (!
        (((x_1)[(Bit#(4))'(4'h9)]).m_is_ul))) &&
        ((((x_1)[(Bit#(4))'(4'h9)]).m_addr) == (x_0)) ? (Struct16 {valid :
        (Bool)'(True), data : (Bit#(4))'(4'h9)}) : ((((!
        ((((x_1)[(Bit#(4))'(4'ha)]).m_status) < ((Bit#(3))'(3'h4)))) && (!
        (((x_1)[(Bit#(4))'(4'ha)]).m_is_ul))) &&
        ((((x_1)[(Bit#(4))'(4'ha)]).m_addr) == (x_0)) ? (Struct16 {valid :
        (Bool)'(True), data : (Bit#(4))'(4'ha)}) : ((((!
        ((((x_1)[(Bit#(4))'(4'hb)]).m_status) < ((Bit#(3))'(3'h4)))) && (!
        (((x_1)[(Bit#(4))'(4'hb)]).m_is_ul))) &&
        ((((x_1)[(Bit#(4))'(4'hb)]).m_addr) == (x_0)) ? (Struct16 {valid :
        (Bool)'(True), data : (Bit#(4))'(4'hb)}) : (Struct16 {valid :
        (Bool)'(False), data : unpack(0)})))))))))))))))))))))))));
        when (! ((x_3).valid), noAction);
        Struct16 x_4 = (((((((x_1)[(Bit#(4))'(4'h4)]).m_status) ==
        ((Bit#(3))'(3'h5))) && (((x_1)[(Bit#(4))'(4'h4)]).m_is_ul)) &&
        ((((x_1)[(Bit#(4))'(4'h4)]).m_addr) == (x_0)) ? (Struct16 {valid :
        (Bool)'(True), data : (Bit#(4))'(4'h4)}) :
        (((((((x_1)[(Bit#(4))'(4'h5)]).m_status) == ((Bit#(3))'(3'h5))) &&
        (((x_1)[(Bit#(4))'(4'h5)]).m_is_ul)) &&
        ((((x_1)[(Bit#(4))'(4'h5)]).m_addr) == (x_0)) ? (Struct16 {valid :
        (Bool)'(True), data : (Bit#(4))'(4'h5)}) :
        (((((((x_1)[(Bit#(4))'(4'h6)]).m_status) == ((Bit#(3))'(3'h5))) &&
        (((x_1)[(Bit#(4))'(4'h6)]).m_is_ul)) &&
        ((((x_1)[(Bit#(4))'(4'h6)]).m_addr) == (x_0)) ? (Struct16 {valid :
        (Bool)'(True), data : (Bit#(4))'(4'h6)}) :
        (((((((x_1)[(Bit#(4))'(4'h7)]).m_status) == ((Bit#(3))'(3'h5))) &&
        (((x_1)[(Bit#(4))'(4'h7)]).m_is_ul)) &&
        ((((x_1)[(Bit#(4))'(4'h7)]).m_addr) == (x_0)) ? (Struct16 {valid :
        (Bool)'(True), data : (Bit#(4))'(4'h7)}) :
        (((((((x_1)[(Bit#(4))'(4'h8)]).m_status) == ((Bit#(3))'(3'h5))) &&
        (((x_1)[(Bit#(4))'(4'h8)]).m_is_ul)) &&
        ((((x_1)[(Bit#(4))'(4'h8)]).m_addr) == (x_0)) ? (Struct16 {valid :
        (Bool)'(True), data : (Bit#(4))'(4'h8)}) :
        (((((((x_1)[(Bit#(4))'(4'h9)]).m_status) == ((Bit#(3))'(3'h5))) &&
        (((x_1)[(Bit#(4))'(4'h9)]).m_is_ul)) &&
        ((((x_1)[(Bit#(4))'(4'h9)]).m_addr) == (x_0)) ? (Struct16 {valid :
        (Bool)'(True), data : (Bit#(4))'(4'h9)}) :
        (((((((x_1)[(Bit#(4))'(4'ha)]).m_status) == ((Bit#(3))'(3'h5))) &&
        (((x_1)[(Bit#(4))'(4'ha)]).m_is_ul)) &&
        ((((x_1)[(Bit#(4))'(4'ha)]).m_addr) == (x_0)) ? (Struct16 {valid :
        (Bool)'(True), data : (Bit#(4))'(4'ha)}) :
        (((((((x_1)[(Bit#(4))'(4'hb)]).m_status) == ((Bit#(3))'(3'h5))) &&
        (((x_1)[(Bit#(4))'(4'hb)]).m_is_ul)) &&
        ((((x_1)[(Bit#(4))'(4'hb)]).m_addr) == (x_0)) ? (Struct16 {valid :
        (Bool)'(True), data : (Bit#(4))'(4'hb)}) : (Struct16 {valid :
        (Bool)'(False), data : unpack(0)})))))))))))))))));
        when ((x_4).valid, noAction);
        Bit#(4) x_5 = ((x_4).data);
        return x_5;
    endmethod

    method ActionValue#(Struct8) getDLReady_00 ();
        let x_1 = (mshrs_00);
        Struct16 x_2 = (((((((x_1)[(Bit#(4))'(4'h0)]).m_status) ==
        ((Bit#(3))'(3'h5))) && (! (((x_1)[(Bit#(4))'(4'h0)]).m_is_ul))) &&
        ((((x_1)[(Bit#(4))'(4'h0)]).m_dl_rss_from) ==
        (((x_1)[(Bit#(4))'(4'h0)]).m_dl_rss_recv)) ? (Struct16 {valid :
        (Bool)'(True), data : (Bit#(4))'(4'h0)}) :
        (((((((x_1)[(Bit#(4))'(4'h1)]).m_status) == ((Bit#(3))'(3'h5))) && (!
        (((x_1)[(Bit#(4))'(4'h1)]).m_is_ul))) &&
        ((((x_1)[(Bit#(4))'(4'h1)]).m_dl_rss_from) ==
        (((x_1)[(Bit#(4))'(4'h1)]).m_dl_rss_recv)) ? (Struct16 {valid :
        (Bool)'(True), data : (Bit#(4))'(4'h1)}) :
        (((((((x_1)[(Bit#(4))'(4'h2)]).m_status) == ((Bit#(3))'(3'h5))) && (!
        (((x_1)[(Bit#(4))'(4'h2)]).m_is_ul))) &&
        ((((x_1)[(Bit#(4))'(4'h2)]).m_dl_rss_from) ==
        (((x_1)[(Bit#(4))'(4'h2)]).m_dl_rss_recv)) ? (Struct16 {valid :
        (Bool)'(True), data : (Bit#(4))'(4'h2)}) :
        (((((((x_1)[(Bit#(4))'(4'h3)]).m_status) == ((Bit#(3))'(3'h5))) && (!
        (((x_1)[(Bit#(4))'(4'h3)]).m_is_ul))) &&
        ((((x_1)[(Bit#(4))'(4'h3)]).m_dl_rss_from) ==
        (((x_1)[(Bit#(4))'(4'h3)]).m_dl_rss_recv)) ? (Struct16 {valid :
        (Bool)'(True), data : (Bit#(4))'(4'h3)}) :
        (((((((x_1)[(Bit#(4))'(4'h4)]).m_status) == ((Bit#(3))'(3'h5))) && (!
        (((x_1)[(Bit#(4))'(4'h4)]).m_is_ul))) &&
        ((((x_1)[(Bit#(4))'(4'h4)]).m_dl_rss_from) ==
        (((x_1)[(Bit#(4))'(4'h4)]).m_dl_rss_recv)) ? (Struct16 {valid :
        (Bool)'(True), data : (Bit#(4))'(4'h4)}) :
        (((((((x_1)[(Bit#(4))'(4'h5)]).m_status) == ((Bit#(3))'(3'h5))) && (!
        (((x_1)[(Bit#(4))'(4'h5)]).m_is_ul))) &&
        ((((x_1)[(Bit#(4))'(4'h5)]).m_dl_rss_from) ==
        (((x_1)[(Bit#(4))'(4'h5)]).m_dl_rss_recv)) ? (Struct16 {valid :
        (Bool)'(True), data : (Bit#(4))'(4'h5)}) :
        (((((((x_1)[(Bit#(4))'(4'h6)]).m_status) == ((Bit#(3))'(3'h5))) && (!
        (((x_1)[(Bit#(4))'(4'h6)]).m_is_ul))) &&
        ((((x_1)[(Bit#(4))'(4'h6)]).m_dl_rss_from) ==
        (((x_1)[(Bit#(4))'(4'h6)]).m_dl_rss_recv)) ? (Struct16 {valid :
        (Bool)'(True), data : (Bit#(4))'(4'h6)}) :
        (((((((x_1)[(Bit#(4))'(4'h7)]).m_status) == ((Bit#(3))'(3'h5))) && (!
        (((x_1)[(Bit#(4))'(4'h7)]).m_is_ul))) &&
        ((((x_1)[(Bit#(4))'(4'h7)]).m_dl_rss_from) ==
        (((x_1)[(Bit#(4))'(4'h7)]).m_dl_rss_recv)) ? (Struct16 {valid :
        (Bool)'(True), data : (Bit#(4))'(4'h7)}) :
        (((((((x_1)[(Bit#(4))'(4'h8)]).m_status) == ((Bit#(3))'(3'h5))) && (!
        (((x_1)[(Bit#(4))'(4'h8)]).m_is_ul))) &&
        ((((x_1)[(Bit#(4))'(4'h8)]).m_dl_rss_from) ==
        (((x_1)[(Bit#(4))'(4'h8)]).m_dl_rss_recv)) ? (Struct16 {valid :
        (Bool)'(True), data : (Bit#(4))'(4'h8)}) :
        (((((((x_1)[(Bit#(4))'(4'h9)]).m_status) == ((Bit#(3))'(3'h5))) && (!
        (((x_1)[(Bit#(4))'(4'h9)]).m_is_ul))) &&
        ((((x_1)[(Bit#(4))'(4'h9)]).m_dl_rss_from) ==
        (((x_1)[(Bit#(4))'(4'h9)]).m_dl_rss_recv)) ? (Struct16 {valid :
        (Bool)'(True), data : (Bit#(4))'(4'h9)}) :
        (((((((x_1)[(Bit#(4))'(4'ha)]).m_status) == ((Bit#(3))'(3'h5))) && (!
        (((x_1)[(Bit#(4))'(4'ha)]).m_is_ul))) &&
        ((((x_1)[(Bit#(4))'(4'ha)]).m_dl_rss_from) ==
        (((x_1)[(Bit#(4))'(4'ha)]).m_dl_rss_recv)) ? (Struct16 {valid :
        (Bool)'(True), data : (Bit#(4))'(4'ha)}) :
        (((((((x_1)[(Bit#(4))'(4'hb)]).m_status) == ((Bit#(3))'(3'h5))) && (!
        (((x_1)[(Bit#(4))'(4'hb)]).m_is_ul))) &&
        ((((x_1)[(Bit#(4))'(4'hb)]).m_dl_rss_from) ==
        (((x_1)[(Bit#(4))'(4'hb)]).m_dl_rss_recv)) ? (Struct16 {valid :
        (Bool)'(True), data : (Bit#(4))'(4'hb)}) : (Struct16 {valid :
        (Bool)'(False), data : unpack(0)})))))))))))))))))))))))));
        when ((x_2).valid, noAction);
        Bit#(4) x_3 = ((x_2).data);
        Struct15 x_4 = ((x_1)[x_3]);
        Bit#(64) x_5 = ((x_4).m_addr);
        Bool x_6 = (((((((x_1)[(Bit#(4))'(4'h0)]).m_status) ==
        ((Bit#(3))'(3'h4))) || ((((x_1)[(Bit#(4))'(4'h0)]).m_status) ==
        ((Bit#(3))'(3'h6)))) && ((! ((((x_1)[(Bit#(4))'(4'h0)]).m_addr) ==
        (x_5))) && (((((x_1)[(Bit#(4))'(4'h0)]).m_addr)[13:5]) ==
        ((x_5)[13:5]))) ? ((Bool)'(True)) :
        (((((((x_1)[(Bit#(4))'(4'h1)]).m_status) == ((Bit#(3))'(3'h4))) ||
        ((((x_1)[(Bit#(4))'(4'h1)]).m_status) == ((Bit#(3))'(3'h6)))) && ((!
        ((((x_1)[(Bit#(4))'(4'h1)]).m_addr) == (x_5))) &&
        (((((x_1)[(Bit#(4))'(4'h1)]).m_addr)[13:5]) == ((x_5)[13:5]))) ?
        ((Bool)'(True)) : (((((((x_1)[(Bit#(4))'(4'h2)]).m_status) ==
        ((Bit#(3))'(3'h4))) || ((((x_1)[(Bit#(4))'(4'h2)]).m_status) ==
        ((Bit#(3))'(3'h6)))) && ((! ((((x_1)[(Bit#(4))'(4'h2)]).m_addr) ==
        (x_5))) && (((((x_1)[(Bit#(4))'(4'h2)]).m_addr)[13:5]) ==
        ((x_5)[13:5]))) ? ((Bool)'(True)) :
        (((((((x_1)[(Bit#(4))'(4'h3)]).m_status) == ((Bit#(3))'(3'h4))) ||
        ((((x_1)[(Bit#(4))'(4'h3)]).m_status) == ((Bit#(3))'(3'h6)))) && ((!
        ((((x_1)[(Bit#(4))'(4'h3)]).m_addr) == (x_5))) &&
        (((((x_1)[(Bit#(4))'(4'h3)]).m_addr)[13:5]) == ((x_5)[13:5]))) ?
        ((Bool)'(True)) : (((((((x_1)[(Bit#(4))'(4'h4)]).m_status) ==
        ((Bit#(3))'(3'h4))) || ((((x_1)[(Bit#(4))'(4'h4)]).m_status) ==
        ((Bit#(3))'(3'h6)))) && ((! ((((x_1)[(Bit#(4))'(4'h4)]).m_addr) ==
        (x_5))) && (((((x_1)[(Bit#(4))'(4'h4)]).m_addr)[13:5]) ==
        ((x_5)[13:5]))) ? ((Bool)'(True)) :
        (((((((x_1)[(Bit#(4))'(4'h5)]).m_status) == ((Bit#(3))'(3'h4))) ||
        ((((x_1)[(Bit#(4))'(4'h5)]).m_status) == ((Bit#(3))'(3'h6)))) && ((!
        ((((x_1)[(Bit#(4))'(4'h5)]).m_addr) == (x_5))) &&
        (((((x_1)[(Bit#(4))'(4'h5)]).m_addr)[13:5]) == ((x_5)[13:5]))) ?
        ((Bool)'(True)) : (((((((x_1)[(Bit#(4))'(4'h6)]).m_status) ==
        ((Bit#(3))'(3'h4))) || ((((x_1)[(Bit#(4))'(4'h6)]).m_status) ==
        ((Bit#(3))'(3'h6)))) && ((! ((((x_1)[(Bit#(4))'(4'h6)]).m_addr) ==
        (x_5))) && (((((x_1)[(Bit#(4))'(4'h6)]).m_addr)[13:5]) ==
        ((x_5)[13:5]))) ? ((Bool)'(True)) :
        (((((((x_1)[(Bit#(4))'(4'h7)]).m_status) == ((Bit#(3))'(3'h4))) ||
        ((((x_1)[(Bit#(4))'(4'h7)]).m_status) == ((Bit#(3))'(3'h6)))) && ((!
        ((((x_1)[(Bit#(4))'(4'h7)]).m_addr) == (x_5))) &&
        (((((x_1)[(Bit#(4))'(4'h7)]).m_addr)[13:5]) == ((x_5)[13:5]))) ?
        ((Bool)'(True)) : (((((((x_1)[(Bit#(4))'(4'h8)]).m_status) ==
        ((Bit#(3))'(3'h4))) || ((((x_1)[(Bit#(4))'(4'h8)]).m_status) ==
        ((Bit#(3))'(3'h6)))) && ((! ((((x_1)[(Bit#(4))'(4'h8)]).m_addr) ==
        (x_5))) && (((((x_1)[(Bit#(4))'(4'h8)]).m_addr)[13:5]) ==
        ((x_5)[13:5]))) ? ((Bool)'(True)) :
        (((((((x_1)[(Bit#(4))'(4'h9)]).m_status) == ((Bit#(3))'(3'h4))) ||
        ((((x_1)[(Bit#(4))'(4'h9)]).m_status) == ((Bit#(3))'(3'h6)))) && ((!
        ((((x_1)[(Bit#(4))'(4'h9)]).m_addr) == (x_5))) &&
        (((((x_1)[(Bit#(4))'(4'h9)]).m_addr)[13:5]) == ((x_5)[13:5]))) ?
        ((Bool)'(True)) : (((((((x_1)[(Bit#(4))'(4'ha)]).m_status) ==
        ((Bit#(3))'(3'h4))) || ((((x_1)[(Bit#(4))'(4'ha)]).m_status) ==
        ((Bit#(3))'(3'h6)))) && ((! ((((x_1)[(Bit#(4))'(4'ha)]).m_addr) ==
        (x_5))) && (((((x_1)[(Bit#(4))'(4'ha)]).m_addr)[13:5]) ==
        ((x_5)[13:5]))) ? ((Bool)'(True)) :
        (((((((x_1)[(Bit#(4))'(4'hb)]).m_status) == ((Bit#(3))'(3'h4))) ||
        ((((x_1)[(Bit#(4))'(4'hb)]).m_status) == ((Bit#(3))'(3'h6)))) && ((!
        ((((x_1)[(Bit#(4))'(4'hb)]).m_addr) == (x_5))) &&
        (((((x_1)[(Bit#(4))'(4'hb)]).m_addr)[13:5]) == ((x_5)[13:5]))) ?
        ((Bool)'(True)) : ((Bool)'(False))))))))))))))))))))))))));
        when (! (x_6), noAction);
        Struct8 x_7 = (Struct8 {r_id : x_3, r_addr : x_5});
        return x_7;
    endmethod

    method Action startRelease_00 (Bit#(4) x_0);
        let x_1 = (mshrs_00);
        Struct15 x_2 = ((x_1)[x_0]);
        Struct15 x_3 = (Struct15 {m_status : (Bit#(3))'(3'h6), m_next :
        (x_2).m_next, m_is_ul : (x_2).m_is_ul, m_addr : (x_2).m_addr, m_qidx
        : (x_2).m_qidx, m_rsb : (x_2).m_rsb, m_dl_rss_from :
        (x_2).m_dl_rss_from, m_dl_rss_recv : (x_2).m_dl_rss_recv});
        mshrs_00 <= update (x_1, x_0, x_3);
    endmethod

    method Action releaseMSHR_00 (Bit#(4) x_0);
        let x_1 = (mshrs_00);
        Struct15 x_2 = ((x_1)[x_0]);
        Vector#(12, Struct15) x_3 = (update (x_1, x_0,
        unpack(0)));
        let x_7 = ?;
        if (((x_2).m_next).valid) begin
            Bit#(4) x_4 = (((x_2).m_next).data);
            Struct15 x_5 = ((x_1)[x_4]);
            Vector#(12, Struct15) x_6 = (update (x_3, x_4, Struct15 {m_status
            : (Bit#(3))'(3'h2), m_next : (x_5).m_next, m_is_ul :
            (x_5).m_is_ul, m_addr : (x_5).m_addr, m_qidx : (x_5).m_qidx,
            m_rsb : (x_5).m_rsb, m_dl_rss_from : (x_5).m_dl_rss_from,
            m_dl_rss_recv : (x_5).m_dl_rss_recv}));
            x_7 = x_6;
        end else begin
            x_7 = x_3;
        end
        mshrs_00 <= x_7;
    endmethod
endmodule

interface Module23;
    method Action enq_fifoCRqInput_000 (Struct2 x_0);
    method ActionValue#(Struct2) deq_fifoCRqInput_000 ();
endinterface

module mkModule23 (Module23);
    FIFOF#(Struct2) pff <- mkSizedFIFOF(4);

    method Action enq_fifoCRqInput_000 (Struct2 x_0);
        pff.enq(x_0);
    endmethod

    method ActionValue#(Struct2) deq_fifoCRqInput_000 ();
        pff.deq();
        return pff.first();
    endmethod

endmodule

interface Module24;
    method Action enq_fifoPInput_000 (Struct2 x_0);
    method ActionValue#(Struct2) deq_fifoPInput_000 ();
endinterface

module mkModule24 (Module24);
    FIFOF#(Struct2) pff <- mkSizedFIFOF(4);

    method Action enq_fifoPInput_000 (Struct2 x_0);
        pff.enq(x_0);
    endmethod

    method ActionValue#(Struct2) deq_fifoPInput_000 ();
        pff.deq();
        return pff.first();
    endmethod

endmodule

interface Module25;
    method Action enq_fifoN2I_000 (Struct40 x_0);
    method ActionValue#(Struct40) deq_fifoN2I_000 ();
endinterface

module mkModule25 (Module25);
    FIFOF#(Struct40) pff <- mkPipelineFIFOF();

    method Action enq_fifoN2I_000 (Struct40 x_0);
        pff.enq(x_0);
    endmethod

    method ActionValue#(Struct40) deq_fifoN2I_000 ();
        pff.deq();
        return pff.first();
    endmethod

endmodule

interface Module26;
    method Action enq_fifoI2L_000 (Struct40 x_0);
    method ActionValue#(Struct40) deq_fifoI2L_000 ();
endinterface

module mkModule26 (Module26);
    FIFOF#(Struct40) pff <- mkPipelineFIFOF();

    method Action enq_fifoI2L_000 (Struct40 x_0);
        pff.enq(x_0);
    endmethod

    method ActionValue#(Struct40) deq_fifoI2L_000 ();
        pff.deq();
        return pff.first();
    endmethod

endmodule

interface Module27;
    method Action enq_fifoL2E_000 (Struct43 x_0);
    method ActionValue#(Struct43) deq_fifoL2E_000 ();
endinterface

module mkModule27 (Module27);
    FIFOF#(Struct43) pff <- mkPipelineFIFOF();

    method Action enq_fifoL2E_000 (Struct43 x_0);
        pff.enq(x_0);
    endmethod

    method ActionValue#(Struct43) deq_fifoL2E_000 ();
        pff.deq();
        return pff.first();
    endmethod

endmodule

interface Module28;
    method Action enq_fifo0000 (Struct1 x_0);
    method ActionValue#(Struct1) deq_fifo0000 ();
endinterface

module mkModule28 (Module28);
    FIFOF#(Struct1) pff <- mkSizedFIFOF(2);

    method Action enq_fifo0000 (Struct1 x_0);
        pff.enq(x_0);
    endmethod

    method ActionValue#(Struct1) deq_fifo0000 ();
        pff.deq();
        return pff.first();
    endmethod

endmodule

interface Module29;
    method Action enq_fifo0001 (Struct1 x_0);
    method ActionValue#(Struct1) deq_fifo0001 ();
endinterface

module mkModule29 (Module29);
    FIFOF#(Struct1) pff <- mkSizedFIFOF(2);

    method Action enq_fifo0001 (Struct1 x_0);
        pff.enq(x_0);
    endmethod

    method ActionValue#(Struct1) deq_fifo0001 ();
        pff.deq();
        return pff.first();
    endmethod

endmodule

interface Module30;
    method Action enq_fifo0002 (Struct1 x_0);
    method ActionValue#(Struct1) deq_fifo0002 ();
endinterface

module mkModule30 (Module30);
    FIFOF#(Struct1) pff <- mkSizedFIFOF(2);

    method Action enq_fifo0002 (Struct1 x_0);
        pff.enq(x_0);
    endmethod

    method ActionValue#(Struct1) deq_fifo0002 ();
        pff.deq();
        return pff.first();
    endmethod

endmodule

interface Module31;
    method Action enq_fifo00000 (Struct1 x_0);
    method ActionValue#(Struct1) deq_fifo00000 ();
endinterface

module mkModule31 (Module31);
    FIFOF#(Struct1) pff <- mkSizedFIFOF(2);

    method Action enq_fifo00000 (Struct1 x_0);
        pff.enq(x_0);
    endmethod

    method ActionValue#(Struct1) deq_fifo00000 ();
        pff.deq();
        return pff.first();
    endmethod

endmodule

interface Module32;
    method Action enq_fifo00002 (Struct1 x_0);
    method ActionValue#(Struct1) deq_fifo00002 ();
endinterface

module mkModule32 (Module32);
    FIFOF#(Struct1) pff <- mkSizedFIFOF(2);

    method Action enq_fifo00002 (Struct1 x_0);
        pff.enq(x_0);
    endmethod

    method ActionValue#(Struct1) deq_fifo00002 ();
        pff.deq();
        return pff.first();
    endmethod

endmodule

interface Module33;
    method ActionValue#(Struct10) victims__000__findVictim (Bit#(64) x_0);
    method ActionValue#(Struct14) victims__000__getVictim (Bit#(2) x_0);
    method Action victims__000__setVictim (Struct47 x_0);
    method Action victims__000__registerVictim (Struct14 x_0);
    method ActionValue#(Struct14) victims__000__getFirstVictim ();
    method ActionValue#(Bool) victims__000__hasVictim ();
    method Action victims__000__setVictimRq (Bit#(64) x_0);
    method Action victims__000__releaseVictim (Bit#(64) x_0);
endinterface

module mkModule33
    (Module33);
    Reg#(Vector#(4, Struct14)) victimRegs__000 <- mkReg(unpack(0));

    // No rules in this module

    method ActionValue#(Struct10) victims__000__findVictim (Bit#(64) x_0);
        let x_1 = (victimRegs__000);
        Struct14 x_2 =
        ((x_1)[(Bit#(2))'(2'h0)]);
        let x_9 = ?;
        if (((x_2).victim_valid) && (((x_2).victim_addr) == (x_0))) begin
            x_9 = Struct10 {valid : (Bool)'(True), data : (Bit#(2))'(2'h0)};
        end else begin
            Struct14 x_3 =
            ((x_1)[(Bit#(2))'(2'h1)]);
            let x_8 = ?;
            if (((x_3).victim_valid) && (((x_3).victim_addr) == (x_0)))
                begin
                x_8 = Struct10 {valid : (Bool)'(True), data :
                (Bit#(2))'(2'h1)};
            end else begin
                Struct14 x_4 =
                ((x_1)[(Bit#(2))'(2'h2)]);
                let x_7 = ?;
                if (((x_4).victim_valid) && (((x_4).victim_addr) == (x_0)))
                    begin
                    x_7 = Struct10 {valid : (Bool)'(True), data :
                    (Bit#(2))'(2'h2)};
                end else begin
                    Struct14 x_5 =
                    ((x_1)[(Bit#(2))'(2'h3)]);
                    let x_6 = ?;
                    if (((x_5).victim_valid) && (((x_5).victim_addr) ==
                        (x_0))) begin
                        x_6 = Struct10 {valid : (Bool)'(True), data :
                        (Bit#(2))'(2'h3)};
                    end else begin
                        x_6 = Struct10 {valid : (Bool)'(False), data :
                        unpack(0)};
                    end
                    x_7 = x_6;
                end
                x_8 = x_7;
            end
            x_9 = x_8;
        end
        return x_9;
    endmethod

    method ActionValue#(Struct14) victims__000__getVictim (Bit#(2) x_0);
        let x_1 = (victimRegs__000);
        return (x_1)[x_0];
    endmethod

    method Action victims__000__setVictim (Struct47 x_0);
        let x_1 = (victimRegs__000);
        Struct14 x_2 = ((x_1)[(x_0).victim_idx]);
        Struct14 x_3 = (Struct14 {victim_valid : (Bool)'(True), victim_addr :
        (x_2).victim_addr, victim_info : (x_0).victim_info, victim_value :
        (x_0).victim_value, victim_req : (x_2).victim_req});
        victimRegs__000 <= update (x_1, (x_0).victim_idx, x_3);
    endmethod

    method Action victims__000__registerVictim (Struct14 x_0);
        let x_1 = (victimRegs__000);
        Struct10 x_2 = ((((x_1)[(Bit#(2))'(2'h3)]).victim_valid ?
        ((((x_1)[(Bit#(2))'(2'h2)]).victim_valid ?
        ((((x_1)[(Bit#(2))'(2'h1)]).victim_valid ?
        ((((x_1)[(Bit#(2))'(2'h0)]).victim_valid ? (Struct10 {valid :
        (Bool)'(False), data : unpack(0)}) : (Struct10 {valid :
        (Bool)'(True), data : (Bit#(2))'(2'h0)}))) : (Struct10 {valid :
        (Bool)'(True), data : (Bit#(2))'(2'h1)}))) : (Struct10 {valid :
        (Bool)'(True), data : (Bit#(2))'(2'h2)}))) : (Struct10 {valid :
        (Bool)'(True), data : (Bit#(2))'(2'h3)})));
        when ((x_2).valid, noAction);
        Bit#(2) x_3 = ((x_2).data);
        victimRegs__000 <= update (x_1, x_3, x_0);
    endmethod

    method ActionValue#(Struct14) victims__000__getFirstVictim ();
        let x_1 = (victimRegs__000);
        Struct35 x_2 = (((((x_1)[(Bit#(2))'(2'h3)]).victim_valid) && (!
        (((x_1)[(Bit#(2))'(2'h3)]).victim_req)) ? (Struct35 {valid :
        (Bool)'(True), data : (x_1)[(Bit#(2))'(2'h3)]}) :
        (((((x_1)[(Bit#(2))'(2'h2)]).victim_valid) && (!
        (((x_1)[(Bit#(2))'(2'h2)]).victim_req)) ? (Struct35 {valid :
        (Bool)'(True), data : (x_1)[(Bit#(2))'(2'h2)]}) :
        (((((x_1)[(Bit#(2))'(2'h1)]).victim_valid) && (!
        (((x_1)[(Bit#(2))'(2'h1)]).victim_req)) ? (Struct35 {valid :
        (Bool)'(True), data : (x_1)[(Bit#(2))'(2'h1)]}) :
        (((((x_1)[(Bit#(2))'(2'h0)]).victim_valid) && (!
        (((x_1)[(Bit#(2))'(2'h0)]).victim_req)) ? (Struct35 {valid :
        (Bool)'(True), data : (x_1)[(Bit#(2))'(2'h0)]}) : (Struct35 {valid :
        (Bool)'(False), data : unpack(0)})))))))));
        when ((x_2).valid, noAction);
        return (x_2).data;
    endmethod

    method ActionValue#(Bool) victims__000__hasVictim ();
        let x_1 = (victimRegs__000);
        Bool x_2 = (((((x_1)[(Bit#(2))'(2'h3)]).victim_valid) && (!
        (((x_1)[(Bit#(2))'(2'h3)]).victim_req)) ? ((Bool)'(True)) :
        (((((x_1)[(Bit#(2))'(2'h2)]).victim_valid) && (!
        (((x_1)[(Bit#(2))'(2'h2)]).victim_req)) ? ((Bool)'(True)) :
        (((((x_1)[(Bit#(2))'(2'h1)]).victim_valid) && (!
        (((x_1)[(Bit#(2))'(2'h1)]).victim_req)) ? ((Bool)'(True)) :
        (((((x_1)[(Bit#(2))'(2'h0)]).victim_valid) && (!
        (((x_1)[(Bit#(2))'(2'h0)]).victim_req)) ? ((Bool)'(True)) :
        ((Bool)'(False))))))))));
        return x_2;
    endmethod

    method Action victims__000__setVictimRq (Bit#(64) x_0);
        let x_1 = (victimRegs__000);
        Struct14 x_2 =
        ((x_1)[(Bit#(2))'(2'h3)]);
        if (((x_2).victim_valid) && (((x_2).victim_addr) == (x_0)))
            begin
            Struct14 x_3 = (Struct14 {victim_valid : (x_2).victim_valid,
            victim_addr : (x_2).victim_addr, victim_info : (x_2).victim_info,
            victim_value : (x_2).victim_value, victim_req :
            (Bool)'(True)});
            victimRegs__000 <= update (x_1, (Bit#(2))'(2'h3), x_3);
        end else begin
            Struct14 x_4 =
            ((x_1)[(Bit#(2))'(2'h2)]);
            if (((x_4).victim_valid) && (((x_4).victim_addr) == (x_0)))
                begin
                Struct14 x_5 = (Struct14 {victim_valid : (x_4).victim_valid,
                victim_addr : (x_4).victim_addr, victim_info :
                (x_4).victim_info, victim_value : (x_4).victim_value,
                victim_req : (Bool)'(True)});
                victimRegs__000 <= update (x_1, (Bit#(2))'(2'h2), x_5);
            end else begin
                Struct14 x_6 =
                ((x_1)[(Bit#(2))'(2'h1)]);
                if (((x_6).victim_valid) && (((x_6).victim_addr) == (x_0)))
                    begin
                    Struct14 x_7 = (Struct14 {victim_valid :
                    (x_6).victim_valid, victim_addr : (x_6).victim_addr,
                    victim_info : (x_6).victim_info, victim_value :
                    (x_6).victim_value, victim_req :
                    (Bool)'(True)});
                    victimRegs__000 <= update (x_1, (Bit#(2))'(2'h1), x_7);
                end else begin
                    Struct14 x_8 =
                    ((x_1)[(Bit#(2))'(2'h0)]);
                    if (((x_8).victim_valid) && (((x_8).victim_addr) ==
                        (x_0))) begin
                        Struct14 x_9 = (Struct14 {victim_valid :
                        (x_8).victim_valid, victim_addr : (x_8).victim_addr,
                        victim_info : (x_8).victim_info, victim_value :
                        (x_8).victim_value, victim_req :
                        (Bool)'(True)});
                        victimRegs__000 <= update (x_1, (Bit#(2))'(2'h0),
                        x_9);
                    end else begin

                    end
                end
            end
        end
    endmethod

    method Action victims__000__releaseVictim (Bit#(64) x_0);
        let x_1 = (victimRegs__000);
        Struct14 x_2 =
        ((x_1)[(Bit#(2))'(2'h0)]);
        if (((x_2).victim_valid) && (((x_2).victim_addr) == (x_0)))
            begin
            victimRegs__000 <= update (x_1, (Bit#(2))'(2'h0), unpack(0));
        end else begin
            Struct14 x_3 =
            ((x_1)[(Bit#(2))'(2'h1)]);
            if (((x_3).victim_valid) && (((x_3).victim_addr) == (x_0)))
                begin
                victimRegs__000 <= update (x_1, (Bit#(2))'(2'h1), unpack(0));
            end else begin
                Struct14 x_4 =
                ((x_1)[(Bit#(2))'(2'h2)]);
                if (((x_4).victim_valid) && (((x_4).victim_addr) == (x_0)))
                    begin
                    victimRegs__000 <= update (x_1, (Bit#(2))'(2'h2),
                    unpack(0));
                end else begin
                    Struct14 x_5 =
                    ((x_1)[(Bit#(2))'(2'h3)]);
                    if (((x_5).victim_valid) && (((x_5).victim_addr) ==
                        (x_0))) begin
                        victimRegs__000 <= update (x_1, (Bit#(2))'(2'h3),
                        unpack(0));
                    end else begin

                    end
                end
            end
        end
    endmethod
endmodule

interface Module34;
    method Action rdReq_infoRam__000__3 (Bit#(8) x_0);
    method Action wrReq_infoRam__000__3 (Struct50 x_0);
    method ActionValue#(Struct48) rdResp_infoRam__000__3 ();
endinterface

module mkModule34 (Module34);
    RWBramCore#(Bit#(8), Struct48) bram <- mkRWBramCore();
    Reg#(Bool) initDone <- mkReg(False);
    Reg#(Bit#(8)) initIdx <- mkReg(0);

    rule init (!initDone);
        let initData = Struct48 {tag: 51'h7, value: Struct11 {mesi_owned: False, mesi_status: 3'h1, mesi_dir_st: 3'h1, mesi_dir_sharers: 2'h0}};
        bram.wrReq(initIdx, initData);
        initIdx <= initIdx + 1;
        initDone <= (initIdx == maxBound);
    endrule

    method Action rdReq_infoRam__000__3 (Bit#(8) x_0) if(initDone);
        bram.rdReq(x_0);
    endmethod

    method Action wrReq_infoRam__000__3 (Struct50 x_0) if(initDone);
        bram.wrReq(x_0.addr, x_0.datain);
    endmethod

    method ActionValue#(Struct48) rdResp_infoRam__000__3 () if(initDone);
        bram.deqRdResp ();
        let data = bram.rdResp ();
        return data;
    endmethod


endmodule

interface Module35;
    method Action rdReq_infoRam__000__2 (Bit#(8) x_0);
    method Action wrReq_infoRam__000__2 (Struct50 x_0);
    method ActionValue#(Struct48) rdResp_infoRam__000__2 ();
endinterface

module mkModule35 (Module35);
    RWBramCore#(Bit#(8), Struct48) bram <- mkRWBramCore();
    Reg#(Bool) initDone <- mkReg(False);
    Reg#(Bit#(8)) initIdx <- mkReg(0);

    rule init (!initDone);
        let initData = Struct48 {tag: 51'h6, value: Struct11 {mesi_owned: False, mesi_status: 3'h1, mesi_dir_st: 3'h1, mesi_dir_sharers: 2'h0}};
        bram.wrReq(initIdx, initData);
        initIdx <= initIdx + 1;
        initDone <= (initIdx == maxBound);
    endrule

    method Action rdReq_infoRam__000__2 (Bit#(8) x_0) if(initDone);
        bram.rdReq(x_0);
    endmethod

    method Action wrReq_infoRam__000__2 (Struct50 x_0) if(initDone);
        bram.wrReq(x_0.addr, x_0.datain);
    endmethod

    method ActionValue#(Struct48) rdResp_infoRam__000__2 () if(initDone);
        bram.deqRdResp ();
        let data = bram.rdResp ();
        return data;
    endmethod


endmodule

interface Module36;
    method Action rdReq_infoRam__000__1 (Bit#(8) x_0);
    method Action wrReq_infoRam__000__1 (Struct50 x_0);
    method ActionValue#(Struct48) rdResp_infoRam__000__1 ();
endinterface

module mkModule36 (Module36);
    RWBramCore#(Bit#(8), Struct48) bram <- mkRWBramCore();
    Reg#(Bool) initDone <- mkReg(False);
    Reg#(Bit#(8)) initIdx <- mkReg(0);

    rule init (!initDone);
        let initData = Struct48 {tag: 51'h5, value: Struct11 {mesi_owned: False, mesi_status: 3'h1, mesi_dir_st: 3'h1, mesi_dir_sharers: 2'h0}};
        bram.wrReq(initIdx, initData);
        initIdx <= initIdx + 1;
        initDone <= (initIdx == maxBound);
    endrule

    method Action rdReq_infoRam__000__1 (Bit#(8) x_0) if(initDone);
        bram.rdReq(x_0);
    endmethod

    method Action wrReq_infoRam__000__1 (Struct50 x_0) if(initDone);
        bram.wrReq(x_0.addr, x_0.datain);
    endmethod

    method ActionValue#(Struct48) rdResp_infoRam__000__1 () if(initDone);
        bram.deqRdResp ();
        let data = bram.rdResp ();
        return data;
    endmethod


endmodule

interface Module37;
    method Action rdReq_infoRam__000__0 (Bit#(8) x_0);
    method Action wrReq_infoRam__000__0 (Struct50 x_0);
    method ActionValue#(Struct48) rdResp_infoRam__000__0 ();
endinterface

module mkModule37 (Module37);
    RWBramCore#(Bit#(8), Struct48) bram <- mkRWBramCore();
    Reg#(Bool) initDone <- mkReg(False);
    Reg#(Bit#(8)) initIdx <- mkReg(0);

    rule init (!initDone);
        let initData = Struct48 {tag: 51'h4, value: Struct11 {mesi_owned: False, mesi_status: 3'h1, mesi_dir_st: 3'h1, mesi_dir_sharers: 2'h0}};
        bram.wrReq(initIdx, initData);
        initIdx <= initIdx + 1;
        initDone <= (initIdx == maxBound);
    endrule

    method Action rdReq_infoRam__000__0 (Bit#(8) x_0) if(initDone);
        bram.rdReq(x_0);
    endmethod

    method Action wrReq_infoRam__000__0 (Struct50 x_0) if(initDone);
        bram.wrReq(x_0.addr, x_0.datain);
    endmethod

    method ActionValue#(Struct48) rdResp_infoRam__000__0 () if(initDone);
        bram.deqRdResp ();
        let data = bram.rdResp ();
        return data;
    endmethod


endmodule

interface Module38;
    method Action rdReq_dataRam__000 (Bit#(10) x_0);
    method Action wrReq_dataRam__000 (Struct52 x_0);
    method ActionValue#(Vector#(4, Bit#(64))) rdResp_dataRam__000 ();
endinterface

module mkModule38 (Module38);
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

    method Action wrReq_dataRam__000 (Struct52 x_0) if(initDone);
        bram.wrReq(x_0.addr, x_0.datain);
    endmethod

    method ActionValue#(Vector#(4, Bit#(64))) rdResp_dataRam__000 ()
    if(initDone);
        bram.deqRdResp ();
        let data = bram.rdResp ();
        return data;
    endmethod


endmodule

interface Module39;
    method Action rdReq_repRam__000 (Bit#(8) x_0);
    method Action wrReq_repRam__000 (Struct53 x_0);
    method ActionValue#(Vector#(4, Bit#(8))) rdResp_repRam__000 ();
endinterface

module mkModule39 (Module39);
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

    method Action wrReq_repRam__000 (Struct53 x_0) if(initDone);
        bram.wrReq(x_0.addr, x_0.datain);
    endmethod

    method ActionValue#(Vector#(4, Bit#(8))) rdResp_repRam__000 ()
    if(initDone);
        bram.deqRdResp ();
        let data = bram.rdResp ();
        return data;
    endmethod


endmodule

interface Module40;
    method ActionValue#(Struct44) getMSHR_000 (Bit#(3) x_0);
    method ActionValue#(Struct1) getMSHRRq_000 (Bit#(3) x_0);
    method ActionValue#(Struct1) getMSHRFirstRs_000 (Bit#(3) x_0);
    method ActionValue#(Struct39) getPRqSlot_000 (Struct38 x_0);
    method ActionValue#(Struct39) getCRqSlot_000 (Struct38 x_0);
    method ActionValue#(Struct38) getWait_000 ();
    method Action registerUL_000 (Struct46 x_0);
    method Action registerDL_000 (Struct54 x_0);
    method Action canImm_000 (Bit#(64) x_0);
    method Action setULImm_000 (Struct1 x_0);
    method Action transferUpDown_000 (Struct55 x_0);
    method Action addRs_000 (Struct7 x_0);
    method ActionValue#(Bit#(3)) getULReady_000 (Bit#(64) x_0);
    method ActionValue#(Struct56) getDLReady_000 ();
    method Action startRelease_000 (Bit#(3) x_0);
    method Action releaseMSHR_000 (Bit#(3) x_0);
endinterface

module mkModule40
    (Module40);
    Reg#(Vector#(6, Struct44)) mshrs_000 <- mkReg(unpack(0));
    Reg#(Vector#(6, Struct1)) rqs_000 <- mkReg(unpack(0));
    Reg#(Vector#(6, Struct37)) rss_000 <- mkReg(unpack(0));

    // No rules in this module

    method ActionValue#(Struct44) getMSHR_000 (Bit#(3) x_0);
        let x_1 = (mshrs_000);
        return (x_1)[x_0];
    endmethod

    method ActionValue#(Struct1) getMSHRRq_000 (Bit#(3) x_0);
        let x_1 = (rqs_000);
        return (x_1)[x_0];
    endmethod

    method ActionValue#(Struct1) getMSHRFirstRs_000 (Bit#(3) x_0);
        let x_1 = (mshrs_000);
        Struct44 x_2 = ((x_1)[x_0]);
        Bit#(2) x_3 = ((x_2).m_dl_rss_recv);
        Bit#(1) x_4 = ((((x_3)[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(1))'(1'h0)) : (((Bit#(1))'(1'h1)) + (((((x_3)[1:1])[0:0]) ==
        ((Bit#(1))'(1'h1)) ? ((Bit#(1))'(1'h0)) : (((Bit#(1))'(1'h1)) +
        (unpack(0))))))));
        let x_5 = (rss_000);
        Struct37 x_6 = ((x_5)[x_0]);
        Struct1 x_7 = (((x_6).m_dl_rss)[x_4]);
        return x_7;
    endmethod

    method ActionValue#(Struct39) getPRqSlot_000 (Struct38 x_0);
        let x_1 = (mshrs_000);
        Struct5 x_2 = (((((x_1)[(Bit#(3))'(3'h0)]).m_status) ==
        ((Bit#(3))'(3'h0)) ? (Struct5 {valid : (Bool)'(True), data :
        (Bit#(3))'(3'h0)}) : (((((x_1)[(Bit#(3))'(3'h1)]).m_status) ==
        ((Bit#(3))'(3'h0)) ? (Struct5 {valid : (Bool)'(True), data :
        (Bit#(3))'(3'h1)}) : (Struct5 {valid : (Bool)'(False), data :
        unpack(0)})))));
        Bool x_3 = ((x_2).valid);
        Bit#(3) x_4 = ((x_2).data);
        Bit#(64) x_5 = (((x_0).r_msg).addr);
        Bool x_6 = (((((((x_1)[(Bit#(3))'(3'h0)]).m_status) ==
        ((Bit#(3))'(3'h4))) || ((((x_1)[(Bit#(3))'(3'h0)]).m_status) ==
        ((Bit#(3))'(3'h6)))) && (((! ((((x_1)[(Bit#(3))'(3'h0)]).m_addr) ==
        (x_5))) && (((((x_1)[(Bit#(3))'(3'h0)]).m_addr)[12:5]) ==
        ((x_5)[12:5]))) || ((((x_1)[(Bit#(3))'(3'h0)]).m_addr) == (x_5))) ?
        ((Bool)'(True)) : (((((((x_1)[(Bit#(3))'(3'h1)]).m_status) ==
        ((Bit#(3))'(3'h4))) || ((((x_1)[(Bit#(3))'(3'h1)]).m_status) ==
        ((Bit#(3))'(3'h6)))) && (((! ((((x_1)[(Bit#(3))'(3'h1)]).m_addr) ==
        (x_5))) && (((((x_1)[(Bit#(3))'(3'h1)]).m_addr)[12:5]) ==
        ((x_5)[12:5]))) || ((((x_1)[(Bit#(3))'(3'h1)]).m_addr) == (x_5))) ?
        ((Bool)'(True)) : (((((((x_1)[(Bit#(3))'(3'h2)]).m_status) ==
        ((Bit#(3))'(3'h4))) || ((((x_1)[(Bit#(3))'(3'h2)]).m_status) ==
        ((Bit#(3))'(3'h6)))) && (((! ((((x_1)[(Bit#(3))'(3'h2)]).m_addr) ==
        (x_5))) && (((((x_1)[(Bit#(3))'(3'h2)]).m_addr)[12:5]) ==
        ((x_5)[12:5]))) || ((((x_1)[(Bit#(3))'(3'h2)]).m_addr) == (x_5))) ?
        ((Bool)'(True)) : (((((((x_1)[(Bit#(3))'(3'h3)]).m_status) ==
        ((Bit#(3))'(3'h4))) || ((((x_1)[(Bit#(3))'(3'h3)]).m_status) ==
        ((Bit#(3))'(3'h6)))) && (((! ((((x_1)[(Bit#(3))'(3'h3)]).m_addr) ==
        (x_5))) && (((((x_1)[(Bit#(3))'(3'h3)]).m_addr)[12:5]) ==
        ((x_5)[12:5]))) || ((((x_1)[(Bit#(3))'(3'h3)]).m_addr) == (x_5))) ?
        ((Bool)'(True)) : (((((((x_1)[(Bit#(3))'(3'h4)]).m_status) ==
        ((Bit#(3))'(3'h4))) || ((((x_1)[(Bit#(3))'(3'h4)]).m_status) ==
        ((Bit#(3))'(3'h6)))) && (((! ((((x_1)[(Bit#(3))'(3'h4)]).m_addr) ==
        (x_5))) && (((((x_1)[(Bit#(3))'(3'h4)]).m_addr)[12:5]) ==
        ((x_5)[12:5]))) || ((((x_1)[(Bit#(3))'(3'h4)]).m_addr) == (x_5))) ?
        ((Bool)'(True)) : (((((((x_1)[(Bit#(3))'(3'h5)]).m_status) ==
        ((Bit#(3))'(3'h4))) || ((((x_1)[(Bit#(3))'(3'h5)]).m_status) ==
        ((Bit#(3))'(3'h6)))) && (((! ((((x_1)[(Bit#(3))'(3'h5)]).m_addr) ==
        (x_5))) && (((((x_1)[(Bit#(3))'(3'h5)]).m_addr)[12:5]) ==
        ((x_5)[12:5]))) || ((((x_1)[(Bit#(3))'(3'h5)]).m_addr) == (x_5))) ?
        ((Bool)'(True)) : ((Bool)'(False))))))))))))));
        Struct5 x_7 = (((((((x_1)[(Bit#(3))'(3'h0)]).m_status) ==
        ((Bit#(3))'(3'h5))) && (! (((x_1)[(Bit#(3))'(3'h0)]).m_is_ul))) &&
        ((((x_1)[(Bit#(3))'(3'h0)]).m_addr) == (x_5)) ? (Struct5 {valid :
        (Bool)'(True), data : (Bit#(3))'(3'h0)}) :
        (((((((x_1)[(Bit#(3))'(3'h1)]).m_status) == ((Bit#(3))'(3'h5))) && (!
        (((x_1)[(Bit#(3))'(3'h1)]).m_is_ul))) &&
        ((((x_1)[(Bit#(3))'(3'h1)]).m_addr) == (x_5)) ? (Struct5 {valid :
        (Bool)'(True), data : (Bit#(3))'(3'h1)}) :
        (((((((x_1)[(Bit#(3))'(3'h2)]).m_status) == ((Bit#(3))'(3'h5))) && (!
        (((x_1)[(Bit#(3))'(3'h2)]).m_is_ul))) &&
        ((((x_1)[(Bit#(3))'(3'h2)]).m_addr) == (x_5)) ? (Struct5 {valid :
        (Bool)'(True), data : (Bit#(3))'(3'h2)}) :
        (((((((x_1)[(Bit#(3))'(3'h3)]).m_status) == ((Bit#(3))'(3'h5))) && (!
        (((x_1)[(Bit#(3))'(3'h3)]).m_is_ul))) &&
        ((((x_1)[(Bit#(3))'(3'h3)]).m_addr) == (x_5)) ? (Struct5 {valid :
        (Bool)'(True), data : (Bit#(3))'(3'h3)}) :
        (((((((x_1)[(Bit#(3))'(3'h4)]).m_status) == ((Bit#(3))'(3'h5))) && (!
        (((x_1)[(Bit#(3))'(3'h4)]).m_is_ul))) &&
        ((((x_1)[(Bit#(3))'(3'h4)]).m_addr) == (x_5)) ? (Struct5 {valid :
        (Bool)'(True), data : (Bit#(3))'(3'h4)}) :
        (((((((x_1)[(Bit#(3))'(3'h5)]).m_status) == ((Bit#(3))'(3'h5))) && (!
        (((x_1)[(Bit#(3))'(3'h5)]).m_is_ul))) &&
        ((((x_1)[(Bit#(3))'(3'h5)]).m_addr) == (x_5)) ? (Struct5 {valid :
        (Bool)'(True), data : (Bit#(3))'(3'h5)}) : (Struct5 {valid :
        (Bool)'(False), data : unpack(0)})))))))))))));
        Bool x_8 = ((x_7).valid);
        Struct39 x_9 = (Struct39 {s_has_slot : (x_3) && (! (x_6)), s_conflict
        : x_8, s_id :
        x_4});
        if ((x_3) && (! (x_6))) begin
            Vector#(6, Struct44) x_10 = (update (x_1, x_4, Struct44 {m_status
            : (x_8 ? ((Bit#(3))'(3'h1)) : ((Bit#(3))'(3'h4))), m_next :
            Struct5 {valid : (Bool)'(False), data : unpack(0)}, m_is_ul :
            unpack(0), m_addr : ((x_0).r_msg).addr, m_qidx :
            (x_0).r_msg_from, m_rsb : unpack(0), m_dl_rss_from : unpack(0),
            m_dl_rss_recv : unpack(0)}));
            let x_11 = (rqs_000);
            rqs_000 <= update (x_11, x_4,
            (x_0).r_msg);
            let x_15 = ?;
            if (x_8) begin
                Bit#(3) x_12 = ((((! ((((x_1)[(Bit#(3))'(3'h0)]).m_status) ==
                ((Bit#(3))'(3'h0)))) && (!
                ((((x_1)[(Bit#(3))'(3'h0)]).m_next).valid))) &&
                ((((x_1)[(Bit#(3))'(3'h0)]).m_addr) == (x_5)) ?
                ((Bit#(3))'(3'h0)) : ((((!
                ((((x_1)[(Bit#(3))'(3'h1)]).m_status) == ((Bit#(3))'(3'h0))))
                && (! ((((x_1)[(Bit#(3))'(3'h1)]).m_next).valid))) &&
                ((((x_1)[(Bit#(3))'(3'h1)]).m_addr) == (x_5)) ?
                ((Bit#(3))'(3'h1)) : ((((!
                ((((x_1)[(Bit#(3))'(3'h2)]).m_status) == ((Bit#(3))'(3'h0))))
                && (! ((((x_1)[(Bit#(3))'(3'h2)]).m_next).valid))) &&
                ((((x_1)[(Bit#(3))'(3'h2)]).m_addr) == (x_5)) ?
                ((Bit#(3))'(3'h2)) : ((((!
                ((((x_1)[(Bit#(3))'(3'h3)]).m_status) == ((Bit#(3))'(3'h0))))
                && (! ((((x_1)[(Bit#(3))'(3'h3)]).m_next).valid))) &&
                ((((x_1)[(Bit#(3))'(3'h3)]).m_addr) == (x_5)) ?
                ((Bit#(3))'(3'h3)) : ((((!
                ((((x_1)[(Bit#(3))'(3'h4)]).m_status) == ((Bit#(3))'(3'h0))))
                && (! ((((x_1)[(Bit#(3))'(3'h4)]).m_next).valid))) &&
                ((((x_1)[(Bit#(3))'(3'h4)]).m_addr) == (x_5)) ?
                ((Bit#(3))'(3'h4)) : ((((!
                ((((x_1)[(Bit#(3))'(3'h5)]).m_status) == ((Bit#(3))'(3'h0))))
                && (! ((((x_1)[(Bit#(3))'(3'h5)]).m_next).valid))) &&
                ((((x_1)[(Bit#(3))'(3'h5)]).m_addr) == (x_5)) ?
                ((Bit#(3))'(3'h5)) : (unpack(0))))))))))))));
                Struct44 x_13 = ((x_1)[x_12]);
                Vector#(6, Struct44) x_14 = (update (x_10, x_12, Struct44
                {m_status : (x_13).m_status, m_next : (x_8 ? (Struct5 {valid
                : (Bool)'(True), data : x_4}) : ((x_13).m_next)), m_is_ul :
                (x_13).m_is_ul, m_addr : (x_13).m_addr, m_qidx :
                (x_13).m_qidx, m_rsb : (x_13).m_rsb, m_dl_rss_from :
                (x_13).m_dl_rss_from, m_dl_rss_recv :
                (x_13).m_dl_rss_recv}));
                x_15 = x_14;
            end else begin
                x_15 = x_10;
            end
            mshrs_000 <= x_15;
        end else begin

        end
        return x_9;
    endmethod

    method ActionValue#(Struct39) getCRqSlot_000 (Struct38 x_0);
        let x_1 = (mshrs_000);
        Struct5 x_2 = (((((x_1)[(Bit#(3))'(3'h2)]).m_status) ==
        ((Bit#(3))'(3'h0)) ? (Struct5 {valid : (Bool)'(True), data :
        (Bit#(3))'(3'h2)}) : (((((x_1)[(Bit#(3))'(3'h3)]).m_status) ==
        ((Bit#(3))'(3'h0)) ? (Struct5 {valid : (Bool)'(True), data :
        (Bit#(3))'(3'h3)}) : (((((x_1)[(Bit#(3))'(3'h4)]).m_status) ==
        ((Bit#(3))'(3'h0)) ? (Struct5 {valid : (Bool)'(True), data :
        (Bit#(3))'(3'h4)}) : (((((x_1)[(Bit#(3))'(3'h5)]).m_status) ==
        ((Bit#(3))'(3'h0)) ? (Struct5 {valid : (Bool)'(True), data :
        (Bit#(3))'(3'h5)}) : (Struct5 {valid : (Bool)'(False), data :
        unpack(0)})))))))));
        Bool x_3 = ((x_2).valid);
        Bit#(3) x_4 = ((x_2).data);
        Bit#(64) x_5 = (((x_0).r_msg).addr);
        Bool x_6 = (((((((x_1)[(Bit#(3))'(3'h0)]).m_status) ==
        ((Bit#(3))'(3'h4))) || ((((x_1)[(Bit#(3))'(3'h0)]).m_status) ==
        ((Bit#(3))'(3'h6)))) && ((! ((((x_1)[(Bit#(3))'(3'h0)]).m_addr) ==
        (x_5))) && (((((x_1)[(Bit#(3))'(3'h0)]).m_addr)[12:5]) ==
        ((x_5)[12:5]))) ? ((Bool)'(True)) :
        (((((((x_1)[(Bit#(3))'(3'h1)]).m_status) == ((Bit#(3))'(3'h4))) ||
        ((((x_1)[(Bit#(3))'(3'h1)]).m_status) == ((Bit#(3))'(3'h6)))) && ((!
        ((((x_1)[(Bit#(3))'(3'h1)]).m_addr) == (x_5))) &&
        (((((x_1)[(Bit#(3))'(3'h1)]).m_addr)[12:5]) == ((x_5)[12:5]))) ?
        ((Bool)'(True)) : (((((((x_1)[(Bit#(3))'(3'h2)]).m_status) ==
        ((Bit#(3))'(3'h4))) || ((((x_1)[(Bit#(3))'(3'h2)]).m_status) ==
        ((Bit#(3))'(3'h6)))) && ((! ((((x_1)[(Bit#(3))'(3'h2)]).m_addr) ==
        (x_5))) && (((((x_1)[(Bit#(3))'(3'h2)]).m_addr)[12:5]) ==
        ((x_5)[12:5]))) ? ((Bool)'(True)) :
        (((((((x_1)[(Bit#(3))'(3'h3)]).m_status) == ((Bit#(3))'(3'h4))) ||
        ((((x_1)[(Bit#(3))'(3'h3)]).m_status) == ((Bit#(3))'(3'h6)))) && ((!
        ((((x_1)[(Bit#(3))'(3'h3)]).m_addr) == (x_5))) &&
        (((((x_1)[(Bit#(3))'(3'h3)]).m_addr)[12:5]) == ((x_5)[12:5]))) ?
        ((Bool)'(True)) : (((((((x_1)[(Bit#(3))'(3'h4)]).m_status) ==
        ((Bit#(3))'(3'h4))) || ((((x_1)[(Bit#(3))'(3'h4)]).m_status) ==
        ((Bit#(3))'(3'h6)))) && ((! ((((x_1)[(Bit#(3))'(3'h4)]).m_addr) ==
        (x_5))) && (((((x_1)[(Bit#(3))'(3'h4)]).m_addr)[12:5]) ==
        ((x_5)[12:5]))) ? ((Bool)'(True)) :
        (((((((x_1)[(Bit#(3))'(3'h5)]).m_status) == ((Bit#(3))'(3'h4))) ||
        ((((x_1)[(Bit#(3))'(3'h5)]).m_status) == ((Bit#(3))'(3'h6)))) && ((!
        ((((x_1)[(Bit#(3))'(3'h5)]).m_addr) == (x_5))) &&
        (((((x_1)[(Bit#(3))'(3'h5)]).m_addr)[12:5]) == ((x_5)[12:5]))) ?
        ((Bool)'(True)) : ((Bool)'(False))))))))))))));
        Struct5 x_7 = (((((! ((((x_1)[(Bit#(3))'(3'h2)]).m_status) ==
        ((Bit#(3))'(3'h0)))) && (!
        ((((x_1)[(Bit#(3))'(3'h2)]).m_next).valid))) &&
        (((x_1)[(Bit#(3))'(3'h2)]).m_is_ul)) &&
        ((((x_1)[(Bit#(3))'(3'h2)]).m_addr) == (x_5)) ? (Struct5 {valid :
        (Bool)'(True), data : (Bit#(3))'(3'h2)}) : (((((!
        ((((x_1)[(Bit#(3))'(3'h3)]).m_status) == ((Bit#(3))'(3'h0)))) && (!
        ((((x_1)[(Bit#(3))'(3'h3)]).m_next).valid))) &&
        (((x_1)[(Bit#(3))'(3'h3)]).m_is_ul)) &&
        ((((x_1)[(Bit#(3))'(3'h3)]).m_addr) == (x_5)) ? (Struct5 {valid :
        (Bool)'(True), data : (Bit#(3))'(3'h3)}) : (((((!
        ((((x_1)[(Bit#(3))'(3'h4)]).m_status) == ((Bit#(3))'(3'h0)))) && (!
        ((((x_1)[(Bit#(3))'(3'h4)]).m_next).valid))) &&
        (((x_1)[(Bit#(3))'(3'h4)]).m_is_ul)) &&
        ((((x_1)[(Bit#(3))'(3'h4)]).m_addr) == (x_5)) ? (Struct5 {valid :
        (Bool)'(True), data : (Bit#(3))'(3'h4)}) : (((((!
        ((((x_1)[(Bit#(3))'(3'h5)]).m_status) == ((Bit#(3))'(3'h0)))) && (!
        ((((x_1)[(Bit#(3))'(3'h5)]).m_next).valid))) &&
        (((x_1)[(Bit#(3))'(3'h5)]).m_is_ul)) &&
        ((((x_1)[(Bit#(3))'(3'h5)]).m_addr) == (x_5)) ? (Struct5 {valid :
        (Bool)'(True), data : (Bit#(3))'(3'h5)}) : (Struct5 {valid :
        (Bool)'(False), data : unpack(0)})))))))));
        Struct5 x_8 = (((((! ((((x_1)[(Bit#(3))'(3'h0)]).m_status) ==
        ((Bit#(3))'(3'h0)))) && (!
        ((((x_1)[(Bit#(3))'(3'h0)]).m_next).valid))) && (!
        (((x_1)[(Bit#(3))'(3'h0)]).m_is_ul))) &&
        ((((x_1)[(Bit#(3))'(3'h0)]).m_addr) == (x_5)) ? (Struct5 {valid :
        (Bool)'(True), data : (Bit#(3))'(3'h0)}) : (((((!
        ((((x_1)[(Bit#(3))'(3'h1)]).m_status) == ((Bit#(3))'(3'h0)))) && (!
        ((((x_1)[(Bit#(3))'(3'h1)]).m_next).valid))) && (!
        (((x_1)[(Bit#(3))'(3'h1)]).m_is_ul))) &&
        ((((x_1)[(Bit#(3))'(3'h1)]).m_addr) == (x_5)) ? (Struct5 {valid :
        (Bool)'(True), data : (Bit#(3))'(3'h1)}) : (((((!
        ((((x_1)[(Bit#(3))'(3'h2)]).m_status) == ((Bit#(3))'(3'h0)))) && (!
        ((((x_1)[(Bit#(3))'(3'h2)]).m_next).valid))) && (!
        (((x_1)[(Bit#(3))'(3'h2)]).m_is_ul))) &&
        ((((x_1)[(Bit#(3))'(3'h2)]).m_addr) == (x_5)) ? (Struct5 {valid :
        (Bool)'(True), data : (Bit#(3))'(3'h2)}) : (((((!
        ((((x_1)[(Bit#(3))'(3'h3)]).m_status) == ((Bit#(3))'(3'h0)))) && (!
        ((((x_1)[(Bit#(3))'(3'h3)]).m_next).valid))) && (!
        (((x_1)[(Bit#(3))'(3'h3)]).m_is_ul))) &&
        ((((x_1)[(Bit#(3))'(3'h3)]).m_addr) == (x_5)) ? (Struct5 {valid :
        (Bool)'(True), data : (Bit#(3))'(3'h3)}) : (((((!
        ((((x_1)[(Bit#(3))'(3'h4)]).m_status) == ((Bit#(3))'(3'h0)))) && (!
        ((((x_1)[(Bit#(3))'(3'h4)]).m_next).valid))) && (!
        (((x_1)[(Bit#(3))'(3'h4)]).m_is_ul))) &&
        ((((x_1)[(Bit#(3))'(3'h4)]).m_addr) == (x_5)) ? (Struct5 {valid :
        (Bool)'(True), data : (Bit#(3))'(3'h4)}) : (((((!
        ((((x_1)[(Bit#(3))'(3'h5)]).m_status) == ((Bit#(3))'(3'h0)))) && (!
        ((((x_1)[(Bit#(3))'(3'h5)]).m_next).valid))) && (!
        (((x_1)[(Bit#(3))'(3'h5)]).m_is_ul))) &&
        ((((x_1)[(Bit#(3))'(3'h5)]).m_addr) == (x_5)) ? (Struct5 {valid :
        (Bool)'(True), data : (Bit#(3))'(3'h5)}) : (Struct5 {valid :
        (Bool)'(False), data : unpack(0)})))))))))))));
        Bool x_9 = ((x_7).valid);
        Bool x_10 = ((x_8).valid);
        Bool x_11 = ((x_9) || (x_10));
        Struct39 x_12 = (Struct39 {s_has_slot : (x_3) && (! (x_6)),
        s_conflict : x_11, s_id :
        x_4});
        if ((x_3) && (! (x_6))) begin
            Vector#(6, Struct44) x_13 = (update (x_1, x_4, Struct44 {m_status
            : (x_11 ? ((Bit#(3))'(3'h1)) : ((Bit#(3))'(3'h4))), m_next :
            Struct5 {valid : (Bool)'(False), data : unpack(0)}, m_is_ul :
            unpack(0), m_addr : ((x_0).r_msg).addr, m_qidx :
            (x_0).r_msg_from, m_rsb : unpack(0), m_dl_rss_from : unpack(0),
            m_dl_rss_recv : unpack(0)}));
            let x_14 = (rqs_000);
            rqs_000 <= update (x_14, x_4,
            (x_0).r_msg);
            let x_18 = ?;
            if (x_11) begin
                Bit#(3) x_15 = ((x_9 ? ((x_7).data) : ((x_8).data)));
                Struct44 x_16 = ((x_1)[x_15]);
                Vector#(6, Struct44) x_17 = (update (x_13, x_15, Struct44
                {m_status : (x_16).m_status, m_next : (x_11 ? (Struct5 {valid
                : (Bool)'(True), data : x_4}) : ((x_16).m_next)), m_is_ul :
                (x_16).m_is_ul, m_addr : (x_16).m_addr, m_qidx :
                (x_16).m_qidx, m_rsb : (x_16).m_rsb, m_dl_rss_from :
                (x_16).m_dl_rss_from, m_dl_rss_recv :
                (x_16).m_dl_rss_recv}));
                x_18 = x_17;
            end else begin
                x_18 = x_13;
            end
            mshrs_000 <= x_18;
        end else begin

        end
        return x_12;
    endmethod

    method ActionValue#(Struct38) getWait_000 ();
        let x_1 = (mshrs_000);
        let x_2 = (rqs_000);
        Struct5 x_3 = (((((x_1)[(Bit#(3))'(3'h0)]).m_status) ==
        ((Bit#(3))'(3'h2)) ? (Struct5 {valid : (Bool)'(True), data :
        (Bit#(3))'(3'h0)}) : (((((x_1)[(Bit#(3))'(3'h1)]).m_status) ==
        ((Bit#(3))'(3'h2)) ? (Struct5 {valid : (Bool)'(True), data :
        (Bit#(3))'(3'h1)}) : (((((x_1)[(Bit#(3))'(3'h2)]).m_status) ==
        ((Bit#(3))'(3'h2)) ? (Struct5 {valid : (Bool)'(True), data :
        (Bit#(3))'(3'h2)}) : (((((x_1)[(Bit#(3))'(3'h3)]).m_status) ==
        ((Bit#(3))'(3'h2)) ? (Struct5 {valid : (Bool)'(True), data :
        (Bit#(3))'(3'h3)}) : (((((x_1)[(Bit#(3))'(3'h4)]).m_status) ==
        ((Bit#(3))'(3'h2)) ? (Struct5 {valid : (Bool)'(True), data :
        (Bit#(3))'(3'h4)}) : (((((x_1)[(Bit#(3))'(3'h5)]).m_status) ==
        ((Bit#(3))'(3'h2)) ? (Struct5 {valid : (Bool)'(True), data :
        (Bit#(3))'(3'h5)}) : (Struct5 {valid : (Bool)'(False), data :
        unpack(0)})))))))))))));
        when ((x_3).valid, noAction);
        Bit#(3) x_4 = ((x_3).data);
        Struct44 x_5 = ((x_1)[x_4]);
        Struct1 x_6 = ((x_2)[x_4]);
        Bit#(64) x_7 = ((x_5).m_addr);
        Bool x_8 = ((((! ((((x_1)[(Bit#(3))'(3'h0)]).m_status) <
        ((Bit#(3))'(3'h4)))) && ((((x_1)[(Bit#(3))'(3'h0)]).m_addr) ==
        (x_7))) || ((((((x_1)[(Bit#(3))'(3'h0)]).m_status) ==
        ((Bit#(3))'(3'h4))) || ((((x_1)[(Bit#(3))'(3'h0)]).m_status) ==
        ((Bit#(3))'(3'h6)))) && ((! ((((x_1)[(Bit#(3))'(3'h0)]).m_addr) ==
        (x_7))) && (((((x_1)[(Bit#(3))'(3'h0)]).m_addr)[12:5]) ==
        ((x_7)[12:5])))) ? ((Bool)'(True)) : ((((!
        ((((x_1)[(Bit#(3))'(3'h1)]).m_status) < ((Bit#(3))'(3'h4)))) &&
        ((((x_1)[(Bit#(3))'(3'h1)]).m_addr) == (x_7))) ||
        ((((((x_1)[(Bit#(3))'(3'h1)]).m_status) == ((Bit#(3))'(3'h4))) ||
        ((((x_1)[(Bit#(3))'(3'h1)]).m_status) == ((Bit#(3))'(3'h6)))) && ((!
        ((((x_1)[(Bit#(3))'(3'h1)]).m_addr) == (x_7))) &&
        (((((x_1)[(Bit#(3))'(3'h1)]).m_addr)[12:5]) == ((x_7)[12:5])))) ?
        ((Bool)'(True)) : ((((! ((((x_1)[(Bit#(3))'(3'h2)]).m_status) <
        ((Bit#(3))'(3'h4)))) && ((((x_1)[(Bit#(3))'(3'h2)]).m_addr) ==
        (x_7))) || ((((((x_1)[(Bit#(3))'(3'h2)]).m_status) ==
        ((Bit#(3))'(3'h4))) || ((((x_1)[(Bit#(3))'(3'h2)]).m_status) ==
        ((Bit#(3))'(3'h6)))) && ((! ((((x_1)[(Bit#(3))'(3'h2)]).m_addr) ==
        (x_7))) && (((((x_1)[(Bit#(3))'(3'h2)]).m_addr)[12:5]) ==
        ((x_7)[12:5])))) ? ((Bool)'(True)) : ((((!
        ((((x_1)[(Bit#(3))'(3'h3)]).m_status) < ((Bit#(3))'(3'h4)))) &&
        ((((x_1)[(Bit#(3))'(3'h3)]).m_addr) == (x_7))) ||
        ((((((x_1)[(Bit#(3))'(3'h3)]).m_status) == ((Bit#(3))'(3'h4))) ||
        ((((x_1)[(Bit#(3))'(3'h3)]).m_status) == ((Bit#(3))'(3'h6)))) && ((!
        ((((x_1)[(Bit#(3))'(3'h3)]).m_addr) == (x_7))) &&
        (((((x_1)[(Bit#(3))'(3'h3)]).m_addr)[12:5]) == ((x_7)[12:5])))) ?
        ((Bool)'(True)) : ((((! ((((x_1)[(Bit#(3))'(3'h4)]).m_status) <
        ((Bit#(3))'(3'h4)))) && ((((x_1)[(Bit#(3))'(3'h4)]).m_addr) ==
        (x_7))) || ((((((x_1)[(Bit#(3))'(3'h4)]).m_status) ==
        ((Bit#(3))'(3'h4))) || ((((x_1)[(Bit#(3))'(3'h4)]).m_status) ==
        ((Bit#(3))'(3'h6)))) && ((! ((((x_1)[(Bit#(3))'(3'h4)]).m_addr) ==
        (x_7))) && (((((x_1)[(Bit#(3))'(3'h4)]).m_addr)[12:5]) ==
        ((x_7)[12:5])))) ? ((Bool)'(True)) : ((((!
        ((((x_1)[(Bit#(3))'(3'h5)]).m_status) < ((Bit#(3))'(3'h4)))) &&
        ((((x_1)[(Bit#(3))'(3'h5)]).m_addr) == (x_7))) ||
        ((((((x_1)[(Bit#(3))'(3'h5)]).m_status) == ((Bit#(3))'(3'h4))) ||
        ((((x_1)[(Bit#(3))'(3'h5)]).m_status) == ((Bit#(3))'(3'h6)))) && ((!
        ((((x_1)[(Bit#(3))'(3'h5)]).m_addr) == (x_7))) &&
        (((((x_1)[(Bit#(3))'(3'h5)]).m_addr)[12:5]) == ((x_7)[12:5])))) ?
        ((Bool)'(True)) : ((Bool)'(False))))))))))))));
        when (! (x_8), noAction);
        mshrs_000 <= update (x_1, x_4, Struct44 {m_status : (Bit#(3))'(3'h4),
        m_next : (x_5).m_next, m_is_ul : (x_5).m_is_ul, m_addr :
        (x_5).m_addr, m_qidx : (x_5).m_qidx, m_rsb : (x_5).m_rsb,
        m_dl_rss_from : (x_5).m_dl_rss_from, m_dl_rss_recv :
        (x_5).m_dl_rss_recv});
        Struct38 x_9 = (Struct38 {r_id : x_4, r_msg : x_6, r_msg_from :
        (x_5).m_qidx});
        return x_9;
    endmethod

    method Action registerUL_000 (Struct46 x_0);
        let x_1 = (mshrs_000);
        Bit#(3) x_2 = ((x_0).r_id);
        Struct44 x_3 = ((x_1)[x_2]);
        Struct44 x_4 = (Struct44 {m_status : (Bit#(3))'(3'h5), m_next :
        (x_3).m_next, m_is_ul : (Bool)'(True), m_addr : (x_3).m_addr, m_qidx
        : {((Bit#(2))'(2'h2)),((x_0).r_ul_rsbTo)}, m_rsb : (x_0).r_ul_rsb,
        m_dl_rss_from : unpack(0), m_dl_rss_recv : unpack(0)});
        mshrs_000 <= update (x_1, x_2, x_4);
    endmethod

    method Action registerDL_000 (Struct54 x_0);
        Bit#(3) x_1 = ((x_0).r_id);
        let x_2 = (mshrs_000);
        Struct44 x_3 = ((x_2)[x_1]);
        Struct44 x_4 = (Struct44 {m_status : (Bit#(3))'(3'h5), m_next :
        (x_3).m_next, m_is_ul : (Bool)'(False), m_addr : (x_3).m_addr, m_qidx
        : (x_0).r_dl_rsbTo, m_rsb : (x_0).r_dl_rsb, m_dl_rss_from :
        (x_0).r_dl_rss_from, m_dl_rss_recv : unpack(0)});
        mshrs_000 <= update (x_2, x_1, x_4);
    endmethod

    method Action canImm_000 (Bit#(64) x_0);
        let x_1 = (mshrs_000);
        Struct5 x_2 = (((((x_1)[(Bit#(3))'(3'h2)]).m_status) ==
        ((Bit#(3))'(3'h0)) ? (Struct5 {valid : (Bool)'(True), data :
        (Bit#(3))'(3'h2)}) : (((((x_1)[(Bit#(3))'(3'h3)]).m_status) ==
        ((Bit#(3))'(3'h0)) ? (Struct5 {valid : (Bool)'(True), data :
        (Bit#(3))'(3'h3)}) : (((((x_1)[(Bit#(3))'(3'h4)]).m_status) ==
        ((Bit#(3))'(3'h0)) ? (Struct5 {valid : (Bool)'(True), data :
        (Bit#(3))'(3'h4)}) : (((((x_1)[(Bit#(3))'(3'h5)]).m_status) ==
        ((Bit#(3))'(3'h0)) ? (Struct5 {valid : (Bool)'(True), data :
        (Bit#(3))'(3'h5)}) : (Struct5 {valid : (Bool)'(False), data :
        unpack(0)})))))))));
        when ((x_2).valid, noAction);
        Struct5 x_3 = ((((! ((((x_1)[(Bit#(3))'(3'h0)]).m_status) ==
        ((Bit#(3))'(3'h0)))) && (!
        ((((x_1)[(Bit#(3))'(3'h0)]).m_next).valid))) &&
        ((((x_1)[(Bit#(3))'(3'h0)]).m_addr) == (x_0)) ? (Struct5 {valid :
        (Bool)'(True), data : (Bit#(3))'(3'h0)}) : ((((!
        ((((x_1)[(Bit#(3))'(3'h1)]).m_status) == ((Bit#(3))'(3'h0)))) && (!
        ((((x_1)[(Bit#(3))'(3'h1)]).m_next).valid))) &&
        ((((x_1)[(Bit#(3))'(3'h1)]).m_addr) == (x_0)) ? (Struct5 {valid :
        (Bool)'(True), data : (Bit#(3))'(3'h1)}) : ((((!
        ((((x_1)[(Bit#(3))'(3'h2)]).m_status) == ((Bit#(3))'(3'h0)))) && (!
        ((((x_1)[(Bit#(3))'(3'h2)]).m_next).valid))) &&
        ((((x_1)[(Bit#(3))'(3'h2)]).m_addr) == (x_0)) ? (Struct5 {valid :
        (Bool)'(True), data : (Bit#(3))'(3'h2)}) : ((((!
        ((((x_1)[(Bit#(3))'(3'h3)]).m_status) == ((Bit#(3))'(3'h0)))) && (!
        ((((x_1)[(Bit#(3))'(3'h3)]).m_next).valid))) &&
        ((((x_1)[(Bit#(3))'(3'h3)]).m_addr) == (x_0)) ? (Struct5 {valid :
        (Bool)'(True), data : (Bit#(3))'(3'h3)}) : ((((!
        ((((x_1)[(Bit#(3))'(3'h4)]).m_status) == ((Bit#(3))'(3'h0)))) && (!
        ((((x_1)[(Bit#(3))'(3'h4)]).m_next).valid))) &&
        ((((x_1)[(Bit#(3))'(3'h4)]).m_addr) == (x_0)) ? (Struct5 {valid :
        (Bool)'(True), data : (Bit#(3))'(3'h4)}) : ((((!
        ((((x_1)[(Bit#(3))'(3'h5)]).m_status) == ((Bit#(3))'(3'h0)))) && (!
        ((((x_1)[(Bit#(3))'(3'h5)]).m_next).valid))) &&
        ((((x_1)[(Bit#(3))'(3'h5)]).m_addr) == (x_0)) ? (Struct5 {valid :
        (Bool)'(True), data : (Bit#(3))'(3'h5)}) : (Struct5 {valid :
        (Bool)'(False), data : unpack(0)})))))))))))));
        when (! ((x_3).valid), noAction);
    endmethod

    method Action setULImm_000 (Struct1 x_0);
        let x_1 = (mshrs_000);
        let x_2 = (rqs_000);
        Struct5 x_3 = (((((x_1)[(Bit#(3))'(3'h2)]).m_status) ==
        ((Bit#(3))'(3'h0)) ? (Struct5 {valid : (Bool)'(True), data :
        (Bit#(3))'(3'h2)}) : (((((x_1)[(Bit#(3))'(3'h3)]).m_status) ==
        ((Bit#(3))'(3'h0)) ? (Struct5 {valid : (Bool)'(True), data :
        (Bit#(3))'(3'h3)}) : (((((x_1)[(Bit#(3))'(3'h4)]).m_status) ==
        ((Bit#(3))'(3'h0)) ? (Struct5 {valid : (Bool)'(True), data :
        (Bit#(3))'(3'h4)}) : (((((x_1)[(Bit#(3))'(3'h5)]).m_status) ==
        ((Bit#(3))'(3'h0)) ? (Struct5 {valid : (Bool)'(True), data :
        (Bit#(3))'(3'h5)}) : (Struct5 {valid : (Bool)'(False), data :
        unpack(0)})))))))));
        when ((x_3).valid, noAction);
        Bit#(3) x_4 = ((x_3).data);
        Bit#(64) x_5 = ((x_0).addr);
        Struct5 x_6 = (((! ((((x_1)[(Bit#(3))'(3'h0)]).m_status) ==
        ((Bit#(3))'(3'h0)))) && ((((x_1)[(Bit#(3))'(3'h0)]).m_addr) == (x_5))
        ? (Struct5 {valid : (Bool)'(True), data : (Bit#(3))'(3'h0)}) : (((!
        ((((x_1)[(Bit#(3))'(3'h1)]).m_status) == ((Bit#(3))'(3'h0)))) &&
        ((((x_1)[(Bit#(3))'(3'h1)]).m_addr) == (x_5)) ? (Struct5 {valid :
        (Bool)'(True), data : (Bit#(3))'(3'h1)}) : (((!
        ((((x_1)[(Bit#(3))'(3'h2)]).m_status) == ((Bit#(3))'(3'h0)))) &&
        ((((x_1)[(Bit#(3))'(3'h2)]).m_addr) == (x_5)) ? (Struct5 {valid :
        (Bool)'(True), data : (Bit#(3))'(3'h2)}) : (((!
        ((((x_1)[(Bit#(3))'(3'h3)]).m_status) == ((Bit#(3))'(3'h0)))) &&
        ((((x_1)[(Bit#(3))'(3'h3)]).m_addr) == (x_5)) ? (Struct5 {valid :
        (Bool)'(True), data : (Bit#(3))'(3'h3)}) : (((!
        ((((x_1)[(Bit#(3))'(3'h4)]).m_status) == ((Bit#(3))'(3'h0)))) &&
        ((((x_1)[(Bit#(3))'(3'h4)]).m_addr) == (x_5)) ? (Struct5 {valid :
        (Bool)'(True), data : (Bit#(3))'(3'h4)}) : (((!
        ((((x_1)[(Bit#(3))'(3'h5)]).m_status) == ((Bit#(3))'(3'h0)))) &&
        ((((x_1)[(Bit#(3))'(3'h5)]).m_addr) == (x_5)) ? (Struct5 {valid :
        (Bool)'(True), data : (Bit#(3))'(3'h5)}) : (Struct5 {valid :
        (Bool)'(False), data : unpack(0)})))))))))))));
        when (! ((x_6).valid), noAction);
        mshrs_000 <= update (x_1, x_4, Struct44 {m_status : (Bit#(3))'(3'h5),
        m_next : Struct5 {valid : (Bool)'(False), data : unpack(0)}, m_is_ul
        : (Bool)'(True), m_addr : (x_0).addr, m_qidx : unpack(0), m_rsb :
        (Bool)'(False), m_dl_rss_from : unpack(0), m_dl_rss_recv :
        unpack(0)});
        rqs_000 <= update (x_2, x_4, x_0);
    endmethod

    method Action transferUpDown_000 (Struct55 x_0);
        Bit#(3) x_1 = ((x_0).r_id);
        let x_2 = (mshrs_000);
        Struct44 x_3 = ((x_2)[x_1]);
        Struct44 x_4 = (Struct44 {m_status : (Bit#(3))'(3'h5), m_next :
        (x_3).m_next, m_is_ul : (Bool)'(False), m_addr : (x_3).m_addr, m_qidx
        : (x_3).m_qidx, m_rsb : (x_3).m_rsb, m_dl_rss_from :
        (x_0).r_dl_rss_from, m_dl_rss_recv : unpack(0)});
        mshrs_000 <= update (x_2, x_1, x_4);
    endmethod

    method Action addRs_000 (Struct7 x_0);
        let x_1 = (mshrs_000);
        Bit#(64) x_2 = (((x_0).r_msg).addr);
        Struct5 x_3 = (((((((x_1)[(Bit#(3))'(3'h0)]).m_status) ==
        ((Bit#(3))'(3'h5))) && (! (((x_1)[(Bit#(3))'(3'h0)]).m_is_ul))) &&
        ((((x_1)[(Bit#(3))'(3'h0)]).m_addr) == (x_2)) ? (Struct5 {valid :
        (Bool)'(True), data : (Bit#(3))'(3'h0)}) :
        (((((((x_1)[(Bit#(3))'(3'h1)]).m_status) == ((Bit#(3))'(3'h5))) && (!
        (((x_1)[(Bit#(3))'(3'h1)]).m_is_ul))) &&
        ((((x_1)[(Bit#(3))'(3'h1)]).m_addr) == (x_2)) ? (Struct5 {valid :
        (Bool)'(True), data : (Bit#(3))'(3'h1)}) :
        (((((((x_1)[(Bit#(3))'(3'h2)]).m_status) == ((Bit#(3))'(3'h5))) && (!
        (((x_1)[(Bit#(3))'(3'h2)]).m_is_ul))) &&
        ((((x_1)[(Bit#(3))'(3'h2)]).m_addr) == (x_2)) ? (Struct5 {valid :
        (Bool)'(True), data : (Bit#(3))'(3'h2)}) :
        (((((((x_1)[(Bit#(3))'(3'h3)]).m_status) == ((Bit#(3))'(3'h5))) && (!
        (((x_1)[(Bit#(3))'(3'h3)]).m_is_ul))) &&
        ((((x_1)[(Bit#(3))'(3'h3)]).m_addr) == (x_2)) ? (Struct5 {valid :
        (Bool)'(True), data : (Bit#(3))'(3'h3)}) :
        (((((((x_1)[(Bit#(3))'(3'h4)]).m_status) == ((Bit#(3))'(3'h5))) && (!
        (((x_1)[(Bit#(3))'(3'h4)]).m_is_ul))) &&
        ((((x_1)[(Bit#(3))'(3'h4)]).m_addr) == (x_2)) ? (Struct5 {valid :
        (Bool)'(True), data : (Bit#(3))'(3'h4)}) :
        (((((((x_1)[(Bit#(3))'(3'h5)]).m_status) == ((Bit#(3))'(3'h5))) && (!
        (((x_1)[(Bit#(3))'(3'h5)]).m_is_ul))) &&
        ((((x_1)[(Bit#(3))'(3'h5)]).m_addr) == (x_2)) ? (Struct5 {valid :
        (Bool)'(True), data : (Bit#(3))'(3'h5)}) : (Struct5 {valid :
        (Bool)'(False), data : unpack(0)})))))))))))));
        when ((x_3).valid, noAction);
        Bit#(3) x_4 = ((x_3).data);
        Struct44 x_5 = ((x_1)[x_4]);
        mshrs_000 <= update (x_1, x_4, Struct44 {m_status : (x_5).m_status,
        m_next : (x_5).m_next, m_is_ul : (x_5).m_is_ul, m_addr :
        (x_5).m_addr, m_qidx : (x_5).m_qidx, m_rsb : (x_5).m_rsb,
        m_dl_rss_from : (x_5).m_dl_rss_from, m_dl_rss_recv :
        ((x_5).m_dl_rss_recv) | (((Bit#(2))'(2'h1)) << ((x_0).r_midx))});
        let x_6 = (rss_000);
        Struct37 x_7 = ((x_6)[x_4]);
        rss_000 <= update (x_6, x_4, Struct37 {m_dl_rss : update
        ((x_7).m_dl_rss, (x_0).r_midx, (x_0).r_msg)});
    endmethod

    method ActionValue#(Bit#(3)) getULReady_000 (Bit#(64) x_0);
        let x_1 = (mshrs_000);
        Bool x_2 = (((((((x_1)[(Bit#(3))'(3'h0)]).m_status) ==
        ((Bit#(3))'(3'h4))) || ((((x_1)[(Bit#(3))'(3'h0)]).m_status) ==
        ((Bit#(3))'(3'h6)))) && ((! ((((x_1)[(Bit#(3))'(3'h0)]).m_addr) ==
        (x_0))) && (((((x_1)[(Bit#(3))'(3'h0)]).m_addr)[12:5]) ==
        ((x_0)[12:5]))) ? ((Bool)'(True)) :
        (((((((x_1)[(Bit#(3))'(3'h1)]).m_status) == ((Bit#(3))'(3'h4))) ||
        ((((x_1)[(Bit#(3))'(3'h1)]).m_status) == ((Bit#(3))'(3'h6)))) && ((!
        ((((x_1)[(Bit#(3))'(3'h1)]).m_addr) == (x_0))) &&
        (((((x_1)[(Bit#(3))'(3'h1)]).m_addr)[12:5]) == ((x_0)[12:5]))) ?
        ((Bool)'(True)) : (((((((x_1)[(Bit#(3))'(3'h2)]).m_status) ==
        ((Bit#(3))'(3'h4))) || ((((x_1)[(Bit#(3))'(3'h2)]).m_status) ==
        ((Bit#(3))'(3'h6)))) && ((! ((((x_1)[(Bit#(3))'(3'h2)]).m_addr) ==
        (x_0))) && (((((x_1)[(Bit#(3))'(3'h2)]).m_addr)[12:5]) ==
        ((x_0)[12:5]))) ? ((Bool)'(True)) :
        (((((((x_1)[(Bit#(3))'(3'h3)]).m_status) == ((Bit#(3))'(3'h4))) ||
        ((((x_1)[(Bit#(3))'(3'h3)]).m_status) == ((Bit#(3))'(3'h6)))) && ((!
        ((((x_1)[(Bit#(3))'(3'h3)]).m_addr) == (x_0))) &&
        (((((x_1)[(Bit#(3))'(3'h3)]).m_addr)[12:5]) == ((x_0)[12:5]))) ?
        ((Bool)'(True)) : (((((((x_1)[(Bit#(3))'(3'h4)]).m_status) ==
        ((Bit#(3))'(3'h4))) || ((((x_1)[(Bit#(3))'(3'h4)]).m_status) ==
        ((Bit#(3))'(3'h6)))) && ((! ((((x_1)[(Bit#(3))'(3'h4)]).m_addr) ==
        (x_0))) && (((((x_1)[(Bit#(3))'(3'h4)]).m_addr)[12:5]) ==
        ((x_0)[12:5]))) ? ((Bool)'(True)) :
        (((((((x_1)[(Bit#(3))'(3'h5)]).m_status) == ((Bit#(3))'(3'h4))) ||
        ((((x_1)[(Bit#(3))'(3'h5)]).m_status) == ((Bit#(3))'(3'h6)))) && ((!
        ((((x_1)[(Bit#(3))'(3'h5)]).m_addr) == (x_0))) &&
        (((((x_1)[(Bit#(3))'(3'h5)]).m_addr)[12:5]) == ((x_0)[12:5]))) ?
        ((Bool)'(True)) : ((Bool)'(False))))))))))))));
        when (! (x_2), noAction);
        Struct5 x_3 = ((((! ((((x_1)[(Bit#(3))'(3'h0)]).m_status) <
        ((Bit#(3))'(3'h4)))) && (! (((x_1)[(Bit#(3))'(3'h0)]).m_is_ul))) &&
        ((((x_1)[(Bit#(3))'(3'h0)]).m_addr) == (x_0)) ? (Struct5 {valid :
        (Bool)'(True), data : (Bit#(3))'(3'h0)}) : ((((!
        ((((x_1)[(Bit#(3))'(3'h1)]).m_status) < ((Bit#(3))'(3'h4)))) && (!
        (((x_1)[(Bit#(3))'(3'h1)]).m_is_ul))) &&
        ((((x_1)[(Bit#(3))'(3'h1)]).m_addr) == (x_0)) ? (Struct5 {valid :
        (Bool)'(True), data : (Bit#(3))'(3'h1)}) : ((((!
        ((((x_1)[(Bit#(3))'(3'h2)]).m_status) < ((Bit#(3))'(3'h4)))) && (!
        (((x_1)[(Bit#(3))'(3'h2)]).m_is_ul))) &&
        ((((x_1)[(Bit#(3))'(3'h2)]).m_addr) == (x_0)) ? (Struct5 {valid :
        (Bool)'(True), data : (Bit#(3))'(3'h2)}) : ((((!
        ((((x_1)[(Bit#(3))'(3'h3)]).m_status) < ((Bit#(3))'(3'h4)))) && (!
        (((x_1)[(Bit#(3))'(3'h3)]).m_is_ul))) &&
        ((((x_1)[(Bit#(3))'(3'h3)]).m_addr) == (x_0)) ? (Struct5 {valid :
        (Bool)'(True), data : (Bit#(3))'(3'h3)}) : ((((!
        ((((x_1)[(Bit#(3))'(3'h4)]).m_status) < ((Bit#(3))'(3'h4)))) && (!
        (((x_1)[(Bit#(3))'(3'h4)]).m_is_ul))) &&
        ((((x_1)[(Bit#(3))'(3'h4)]).m_addr) == (x_0)) ? (Struct5 {valid :
        (Bool)'(True), data : (Bit#(3))'(3'h4)}) : ((((!
        ((((x_1)[(Bit#(3))'(3'h5)]).m_status) < ((Bit#(3))'(3'h4)))) && (!
        (((x_1)[(Bit#(3))'(3'h5)]).m_is_ul))) &&
        ((((x_1)[(Bit#(3))'(3'h5)]).m_addr) == (x_0)) ? (Struct5 {valid :
        (Bool)'(True), data : (Bit#(3))'(3'h5)}) : (Struct5 {valid :
        (Bool)'(False), data : unpack(0)})))))))))))));
        when (! ((x_3).valid), noAction);
        Struct5 x_4 = (((((((x_1)[(Bit#(3))'(3'h2)]).m_status) ==
        ((Bit#(3))'(3'h5))) && (((x_1)[(Bit#(3))'(3'h2)]).m_is_ul)) &&
        ((((x_1)[(Bit#(3))'(3'h2)]).m_addr) == (x_0)) ? (Struct5 {valid :
        (Bool)'(True), data : (Bit#(3))'(3'h2)}) :
        (((((((x_1)[(Bit#(3))'(3'h3)]).m_status) == ((Bit#(3))'(3'h5))) &&
        (((x_1)[(Bit#(3))'(3'h3)]).m_is_ul)) &&
        ((((x_1)[(Bit#(3))'(3'h3)]).m_addr) == (x_0)) ? (Struct5 {valid :
        (Bool)'(True), data : (Bit#(3))'(3'h3)}) :
        (((((((x_1)[(Bit#(3))'(3'h4)]).m_status) == ((Bit#(3))'(3'h5))) &&
        (((x_1)[(Bit#(3))'(3'h4)]).m_is_ul)) &&
        ((((x_1)[(Bit#(3))'(3'h4)]).m_addr) == (x_0)) ? (Struct5 {valid :
        (Bool)'(True), data : (Bit#(3))'(3'h4)}) :
        (((((((x_1)[(Bit#(3))'(3'h5)]).m_status) == ((Bit#(3))'(3'h5))) &&
        (((x_1)[(Bit#(3))'(3'h5)]).m_is_ul)) &&
        ((((x_1)[(Bit#(3))'(3'h5)]).m_addr) == (x_0)) ? (Struct5 {valid :
        (Bool)'(True), data : (Bit#(3))'(3'h5)}) : (Struct5 {valid :
        (Bool)'(False), data : unpack(0)})))))))));
        when ((x_4).valid, noAction);
        Bit#(3) x_5 = ((x_4).data);
        return x_5;
    endmethod

    method ActionValue#(Struct56) getDLReady_000 ();
        let x_1 = (mshrs_000);
        Struct5 x_2 = (((((((x_1)[(Bit#(3))'(3'h0)]).m_status) ==
        ((Bit#(3))'(3'h5))) && (! (((x_1)[(Bit#(3))'(3'h0)]).m_is_ul))) &&
        ((((x_1)[(Bit#(3))'(3'h0)]).m_dl_rss_from) ==
        (((x_1)[(Bit#(3))'(3'h0)]).m_dl_rss_recv)) ? (Struct5 {valid :
        (Bool)'(True), data : (Bit#(3))'(3'h0)}) :
        (((((((x_1)[(Bit#(3))'(3'h1)]).m_status) == ((Bit#(3))'(3'h5))) && (!
        (((x_1)[(Bit#(3))'(3'h1)]).m_is_ul))) &&
        ((((x_1)[(Bit#(3))'(3'h1)]).m_dl_rss_from) ==
        (((x_1)[(Bit#(3))'(3'h1)]).m_dl_rss_recv)) ? (Struct5 {valid :
        (Bool)'(True), data : (Bit#(3))'(3'h1)}) :
        (((((((x_1)[(Bit#(3))'(3'h2)]).m_status) == ((Bit#(3))'(3'h5))) && (!
        (((x_1)[(Bit#(3))'(3'h2)]).m_is_ul))) &&
        ((((x_1)[(Bit#(3))'(3'h2)]).m_dl_rss_from) ==
        (((x_1)[(Bit#(3))'(3'h2)]).m_dl_rss_recv)) ? (Struct5 {valid :
        (Bool)'(True), data : (Bit#(3))'(3'h2)}) :
        (((((((x_1)[(Bit#(3))'(3'h3)]).m_status) == ((Bit#(3))'(3'h5))) && (!
        (((x_1)[(Bit#(3))'(3'h3)]).m_is_ul))) &&
        ((((x_1)[(Bit#(3))'(3'h3)]).m_dl_rss_from) ==
        (((x_1)[(Bit#(3))'(3'h3)]).m_dl_rss_recv)) ? (Struct5 {valid :
        (Bool)'(True), data : (Bit#(3))'(3'h3)}) :
        (((((((x_1)[(Bit#(3))'(3'h4)]).m_status) == ((Bit#(3))'(3'h5))) && (!
        (((x_1)[(Bit#(3))'(3'h4)]).m_is_ul))) &&
        ((((x_1)[(Bit#(3))'(3'h4)]).m_dl_rss_from) ==
        (((x_1)[(Bit#(3))'(3'h4)]).m_dl_rss_recv)) ? (Struct5 {valid :
        (Bool)'(True), data : (Bit#(3))'(3'h4)}) :
        (((((((x_1)[(Bit#(3))'(3'h5)]).m_status) == ((Bit#(3))'(3'h5))) && (!
        (((x_1)[(Bit#(3))'(3'h5)]).m_is_ul))) &&
        ((((x_1)[(Bit#(3))'(3'h5)]).m_dl_rss_from) ==
        (((x_1)[(Bit#(3))'(3'h5)]).m_dl_rss_recv)) ? (Struct5 {valid :
        (Bool)'(True), data : (Bit#(3))'(3'h5)}) : (Struct5 {valid :
        (Bool)'(False), data : unpack(0)})))))))))))));
        when ((x_2).valid, noAction);
        Bit#(3) x_3 = ((x_2).data);
        Struct44 x_4 = ((x_1)[x_3]);
        Bit#(64) x_5 = ((x_4).m_addr);
        Bool x_6 = (((((((x_1)[(Bit#(3))'(3'h0)]).m_status) ==
        ((Bit#(3))'(3'h4))) || ((((x_1)[(Bit#(3))'(3'h0)]).m_status) ==
        ((Bit#(3))'(3'h6)))) && ((! ((((x_1)[(Bit#(3))'(3'h0)]).m_addr) ==
        (x_5))) && (((((x_1)[(Bit#(3))'(3'h0)]).m_addr)[12:5]) ==
        ((x_5)[12:5]))) ? ((Bool)'(True)) :
        (((((((x_1)[(Bit#(3))'(3'h1)]).m_status) == ((Bit#(3))'(3'h4))) ||
        ((((x_1)[(Bit#(3))'(3'h1)]).m_status) == ((Bit#(3))'(3'h6)))) && ((!
        ((((x_1)[(Bit#(3))'(3'h1)]).m_addr) == (x_5))) &&
        (((((x_1)[(Bit#(3))'(3'h1)]).m_addr)[12:5]) == ((x_5)[12:5]))) ?
        ((Bool)'(True)) : (((((((x_1)[(Bit#(3))'(3'h2)]).m_status) ==
        ((Bit#(3))'(3'h4))) || ((((x_1)[(Bit#(3))'(3'h2)]).m_status) ==
        ((Bit#(3))'(3'h6)))) && ((! ((((x_1)[(Bit#(3))'(3'h2)]).m_addr) ==
        (x_5))) && (((((x_1)[(Bit#(3))'(3'h2)]).m_addr)[12:5]) ==
        ((x_5)[12:5]))) ? ((Bool)'(True)) :
        (((((((x_1)[(Bit#(3))'(3'h3)]).m_status) == ((Bit#(3))'(3'h4))) ||
        ((((x_1)[(Bit#(3))'(3'h3)]).m_status) == ((Bit#(3))'(3'h6)))) && ((!
        ((((x_1)[(Bit#(3))'(3'h3)]).m_addr) == (x_5))) &&
        (((((x_1)[(Bit#(3))'(3'h3)]).m_addr)[12:5]) == ((x_5)[12:5]))) ?
        ((Bool)'(True)) : (((((((x_1)[(Bit#(3))'(3'h4)]).m_status) ==
        ((Bit#(3))'(3'h4))) || ((((x_1)[(Bit#(3))'(3'h4)]).m_status) ==
        ((Bit#(3))'(3'h6)))) && ((! ((((x_1)[(Bit#(3))'(3'h4)]).m_addr) ==
        (x_5))) && (((((x_1)[(Bit#(3))'(3'h4)]).m_addr)[12:5]) ==
        ((x_5)[12:5]))) ? ((Bool)'(True)) :
        (((((((x_1)[(Bit#(3))'(3'h5)]).m_status) == ((Bit#(3))'(3'h4))) ||
        ((((x_1)[(Bit#(3))'(3'h5)]).m_status) == ((Bit#(3))'(3'h6)))) && ((!
        ((((x_1)[(Bit#(3))'(3'h5)]).m_addr) == (x_5))) &&
        (((((x_1)[(Bit#(3))'(3'h5)]).m_addr)[12:5]) == ((x_5)[12:5]))) ?
        ((Bool)'(True)) : ((Bool)'(False))))))))))))));
        when (! (x_6), noAction);
        Struct56 x_7 = (Struct56 {r_id : x_3, r_addr : x_5});
        return x_7;
    endmethod

    method Action startRelease_000 (Bit#(3) x_0);
        let x_1 = (mshrs_000);
        Struct44 x_2 = ((x_1)[x_0]);
        Struct44 x_3 = (Struct44 {m_status : (Bit#(3))'(3'h6), m_next :
        (x_2).m_next, m_is_ul : (x_2).m_is_ul, m_addr : (x_2).m_addr, m_qidx
        : (x_2).m_qidx, m_rsb : (x_2).m_rsb, m_dl_rss_from :
        (x_2).m_dl_rss_from, m_dl_rss_recv : (x_2).m_dl_rss_recv});
        mshrs_000 <= update (x_1, x_0, x_3);
    endmethod

    method Action releaseMSHR_000 (Bit#(3) x_0);
        let x_1 = (mshrs_000);
        Struct44 x_2 = ((x_1)[x_0]);
        Vector#(6, Struct44) x_3 = (update (x_1, x_0,
        unpack(0)));
        let x_7 = ?;
        if (((x_2).m_next).valid) begin
            Bit#(3) x_4 = (((x_2).m_next).data);
            Struct44 x_5 = ((x_1)[x_4]);
            Vector#(6, Struct44) x_6 = (update (x_3, x_4, Struct44 {m_status
            : (Bit#(3))'(3'h2), m_next : (x_5).m_next, m_is_ul :
            (x_5).m_is_ul, m_addr : (x_5).m_addr, m_qidx : (x_5).m_qidx,
            m_rsb : (x_5).m_rsb, m_dl_rss_from : (x_5).m_dl_rss_from,
            m_dl_rss_recv : (x_5).m_dl_rss_recv}));
            x_7 = x_6;
        end else begin
            x_7 = x_3;
        end
        mshrs_000 <= x_7;
    endmethod
endmodule

interface Module41;
    method Action enq_fifoCRqInput_001 (Struct2 x_0);
    method ActionValue#(Struct2) deq_fifoCRqInput_001 ();
endinterface

module mkModule41 (Module41);
    FIFOF#(Struct2) pff <- mkSizedFIFOF(4);

    method Action enq_fifoCRqInput_001 (Struct2 x_0);
        pff.enq(x_0);
    endmethod

    method ActionValue#(Struct2) deq_fifoCRqInput_001 ();
        pff.deq();
        return pff.first();
    endmethod

endmodule

interface Module42;
    method Action enq_fifoPInput_001 (Struct2 x_0);
    method ActionValue#(Struct2) deq_fifoPInput_001 ();
endinterface

module mkModule42 (Module42);
    FIFOF#(Struct2) pff <- mkSizedFIFOF(4);

    method Action enq_fifoPInput_001 (Struct2 x_0);
        pff.enq(x_0);
    endmethod

    method ActionValue#(Struct2) deq_fifoPInput_001 ();
        pff.deq();
        return pff.first();
    endmethod

endmodule

interface Module43;
    method Action enq_fifoN2I_001 (Struct40 x_0);
    method ActionValue#(Struct40) deq_fifoN2I_001 ();
endinterface

module mkModule43 (Module43);
    FIFOF#(Struct40) pff <- mkPipelineFIFOF();

    method Action enq_fifoN2I_001 (Struct40 x_0);
        pff.enq(x_0);
    endmethod

    method ActionValue#(Struct40) deq_fifoN2I_001 ();
        pff.deq();
        return pff.first();
    endmethod

endmodule

interface Module44;
    method Action enq_fifoI2L_001 (Struct40 x_0);
    method ActionValue#(Struct40) deq_fifoI2L_001 ();
endinterface

module mkModule44 (Module44);
    FIFOF#(Struct40) pff <- mkPipelineFIFOF();

    method Action enq_fifoI2L_001 (Struct40 x_0);
        pff.enq(x_0);
    endmethod

    method ActionValue#(Struct40) deq_fifoI2L_001 ();
        pff.deq();
        return pff.first();
    endmethod

endmodule

interface Module45;
    method Action enq_fifoL2E_001 (Struct43 x_0);
    method ActionValue#(Struct43) deq_fifoL2E_001 ();
endinterface

module mkModule45 (Module45);
    FIFOF#(Struct43) pff <- mkPipelineFIFOF();

    method Action enq_fifoL2E_001 (Struct43 x_0);
        pff.enq(x_0);
    endmethod

    method ActionValue#(Struct43) deq_fifoL2E_001 ();
        pff.deq();
        return pff.first();
    endmethod

endmodule

interface Module46;
    method Action enq_fifo0010 (Struct1 x_0);
    method ActionValue#(Struct1) deq_fifo0010 ();
endinterface

module mkModule46 (Module46);
    FIFOF#(Struct1) pff <- mkSizedFIFOF(2);

    method Action enq_fifo0010 (Struct1 x_0);
        pff.enq(x_0);
    endmethod

    method ActionValue#(Struct1) deq_fifo0010 ();
        pff.deq();
        return pff.first();
    endmethod

endmodule

interface Module47;
    method Action enq_fifo0011 (Struct1 x_0);
    method ActionValue#(Struct1) deq_fifo0011 ();
endinterface

module mkModule47 (Module47);
    FIFOF#(Struct1) pff <- mkSizedFIFOF(2);

    method Action enq_fifo0011 (Struct1 x_0);
        pff.enq(x_0);
    endmethod

    method ActionValue#(Struct1) deq_fifo0011 ();
        pff.deq();
        return pff.first();
    endmethod

endmodule

interface Module48;
    method Action enq_fifo0012 (Struct1 x_0);
    method ActionValue#(Struct1) deq_fifo0012 ();
endinterface

module mkModule48 (Module48);
    FIFOF#(Struct1) pff <- mkSizedFIFOF(2);

    method Action enq_fifo0012 (Struct1 x_0);
        pff.enq(x_0);
    endmethod

    method ActionValue#(Struct1) deq_fifo0012 ();
        pff.deq();
        return pff.first();
    endmethod

endmodule

interface Module49;
    method Action enq_fifo00100 (Struct1 x_0);
    method ActionValue#(Struct1) deq_fifo00100 ();
endinterface

module mkModule49 (Module49);
    FIFOF#(Struct1) pff <- mkSizedFIFOF(2);

    method Action enq_fifo00100 (Struct1 x_0);
        pff.enq(x_0);
    endmethod

    method ActionValue#(Struct1) deq_fifo00100 ();
        pff.deq();
        return pff.first();
    endmethod

endmodule

interface Module50;
    method Action enq_fifo00102 (Struct1 x_0);
    method ActionValue#(Struct1) deq_fifo00102 ();
endinterface

module mkModule50 (Module50);
    FIFOF#(Struct1) pff <- mkSizedFIFOF(2);

    method Action enq_fifo00102 (Struct1 x_0);
        pff.enq(x_0);
    endmethod

    method ActionValue#(Struct1) deq_fifo00102 ();
        pff.deq();
        return pff.first();
    endmethod

endmodule

interface Module51;
    method ActionValue#(Struct10) victims__001__findVictim (Bit#(64) x_0);
    method ActionValue#(Struct14) victims__001__getVictim (Bit#(2) x_0);
    method Action victims__001__setVictim (Struct47 x_0);
    method Action victims__001__registerVictim (Struct14 x_0);
    method ActionValue#(Struct14) victims__001__getFirstVictim ();
    method ActionValue#(Bool) victims__001__hasVictim ();
    method Action victims__001__setVictimRq (Bit#(64) x_0);
    method Action victims__001__releaseVictim (Bit#(64) x_0);
endinterface

module mkModule51
    (Module51);
    Reg#(Vector#(4, Struct14)) victimRegs__001 <- mkReg(unpack(0));

    // No rules in this module

    method ActionValue#(Struct10) victims__001__findVictim (Bit#(64) x_0);
        let x_1 = (victimRegs__001);
        Struct14 x_2 =
        ((x_1)[(Bit#(2))'(2'h0)]);
        let x_9 = ?;
        if (((x_2).victim_valid) && (((x_2).victim_addr) == (x_0))) begin
            x_9 = Struct10 {valid : (Bool)'(True), data : (Bit#(2))'(2'h0)};
        end else begin
            Struct14 x_3 =
            ((x_1)[(Bit#(2))'(2'h1)]);
            let x_8 = ?;
            if (((x_3).victim_valid) && (((x_3).victim_addr) == (x_0)))
                begin
                x_8 = Struct10 {valid : (Bool)'(True), data :
                (Bit#(2))'(2'h1)};
            end else begin
                Struct14 x_4 =
                ((x_1)[(Bit#(2))'(2'h2)]);
                let x_7 = ?;
                if (((x_4).victim_valid) && (((x_4).victim_addr) == (x_0)))
                    begin
                    x_7 = Struct10 {valid : (Bool)'(True), data :
                    (Bit#(2))'(2'h2)};
                end else begin
                    Struct14 x_5 =
                    ((x_1)[(Bit#(2))'(2'h3)]);
                    let x_6 = ?;
                    if (((x_5).victim_valid) && (((x_5).victim_addr) ==
                        (x_0))) begin
                        x_6 = Struct10 {valid : (Bool)'(True), data :
                        (Bit#(2))'(2'h3)};
                    end else begin
                        x_6 = Struct10 {valid : (Bool)'(False), data :
                        unpack(0)};
                    end
                    x_7 = x_6;
                end
                x_8 = x_7;
            end
            x_9 = x_8;
        end
        return x_9;
    endmethod

    method ActionValue#(Struct14) victims__001__getVictim (Bit#(2) x_0);
        let x_1 = (victimRegs__001);
        return (x_1)[x_0];
    endmethod

    method Action victims__001__setVictim (Struct47 x_0);
        let x_1 = (victimRegs__001);
        Struct14 x_2 = ((x_1)[(x_0).victim_idx]);
        Struct14 x_3 = (Struct14 {victim_valid : (Bool)'(True), victim_addr :
        (x_2).victim_addr, victim_info : (x_0).victim_info, victim_value :
        (x_0).victim_value, victim_req : (x_2).victim_req});
        victimRegs__001 <= update (x_1, (x_0).victim_idx, x_3);
    endmethod

    method Action victims__001__registerVictim (Struct14 x_0);
        let x_1 = (victimRegs__001);
        Struct10 x_2 = ((((x_1)[(Bit#(2))'(2'h3)]).victim_valid ?
        ((((x_1)[(Bit#(2))'(2'h2)]).victim_valid ?
        ((((x_1)[(Bit#(2))'(2'h1)]).victim_valid ?
        ((((x_1)[(Bit#(2))'(2'h0)]).victim_valid ? (Struct10 {valid :
        (Bool)'(False), data : unpack(0)}) : (Struct10 {valid :
        (Bool)'(True), data : (Bit#(2))'(2'h0)}))) : (Struct10 {valid :
        (Bool)'(True), data : (Bit#(2))'(2'h1)}))) : (Struct10 {valid :
        (Bool)'(True), data : (Bit#(2))'(2'h2)}))) : (Struct10 {valid :
        (Bool)'(True), data : (Bit#(2))'(2'h3)})));
        when ((x_2).valid, noAction);
        Bit#(2) x_3 = ((x_2).data);
        victimRegs__001 <= update (x_1, x_3, x_0);
    endmethod

    method ActionValue#(Struct14) victims__001__getFirstVictim ();
        let x_1 = (victimRegs__001);
        Struct35 x_2 = (((((x_1)[(Bit#(2))'(2'h3)]).victim_valid) && (!
        (((x_1)[(Bit#(2))'(2'h3)]).victim_req)) ? (Struct35 {valid :
        (Bool)'(True), data : (x_1)[(Bit#(2))'(2'h3)]}) :
        (((((x_1)[(Bit#(2))'(2'h2)]).victim_valid) && (!
        (((x_1)[(Bit#(2))'(2'h2)]).victim_req)) ? (Struct35 {valid :
        (Bool)'(True), data : (x_1)[(Bit#(2))'(2'h2)]}) :
        (((((x_1)[(Bit#(2))'(2'h1)]).victim_valid) && (!
        (((x_1)[(Bit#(2))'(2'h1)]).victim_req)) ? (Struct35 {valid :
        (Bool)'(True), data : (x_1)[(Bit#(2))'(2'h1)]}) :
        (((((x_1)[(Bit#(2))'(2'h0)]).victim_valid) && (!
        (((x_1)[(Bit#(2))'(2'h0)]).victim_req)) ? (Struct35 {valid :
        (Bool)'(True), data : (x_1)[(Bit#(2))'(2'h0)]}) : (Struct35 {valid :
        (Bool)'(False), data : unpack(0)})))))))));
        when ((x_2).valid, noAction);
        return (x_2).data;
    endmethod

    method ActionValue#(Bool) victims__001__hasVictim ();
        let x_1 = (victimRegs__001);
        Bool x_2 = (((((x_1)[(Bit#(2))'(2'h3)]).victim_valid) && (!
        (((x_1)[(Bit#(2))'(2'h3)]).victim_req)) ? ((Bool)'(True)) :
        (((((x_1)[(Bit#(2))'(2'h2)]).victim_valid) && (!
        (((x_1)[(Bit#(2))'(2'h2)]).victim_req)) ? ((Bool)'(True)) :
        (((((x_1)[(Bit#(2))'(2'h1)]).victim_valid) && (!
        (((x_1)[(Bit#(2))'(2'h1)]).victim_req)) ? ((Bool)'(True)) :
        (((((x_1)[(Bit#(2))'(2'h0)]).victim_valid) && (!
        (((x_1)[(Bit#(2))'(2'h0)]).victim_req)) ? ((Bool)'(True)) :
        ((Bool)'(False))))))))));
        return x_2;
    endmethod

    method Action victims__001__setVictimRq (Bit#(64) x_0);
        let x_1 = (victimRegs__001);
        Struct14 x_2 =
        ((x_1)[(Bit#(2))'(2'h3)]);
        if (((x_2).victim_valid) && (((x_2).victim_addr) == (x_0)))
            begin
            Struct14 x_3 = (Struct14 {victim_valid : (x_2).victim_valid,
            victim_addr : (x_2).victim_addr, victim_info : (x_2).victim_info,
            victim_value : (x_2).victim_value, victim_req :
            (Bool)'(True)});
            victimRegs__001 <= update (x_1, (Bit#(2))'(2'h3), x_3);
        end else begin
            Struct14 x_4 =
            ((x_1)[(Bit#(2))'(2'h2)]);
            if (((x_4).victim_valid) && (((x_4).victim_addr) == (x_0)))
                begin
                Struct14 x_5 = (Struct14 {victim_valid : (x_4).victim_valid,
                victim_addr : (x_4).victim_addr, victim_info :
                (x_4).victim_info, victim_value : (x_4).victim_value,
                victim_req : (Bool)'(True)});
                victimRegs__001 <= update (x_1, (Bit#(2))'(2'h2), x_5);
            end else begin
                Struct14 x_6 =
                ((x_1)[(Bit#(2))'(2'h1)]);
                if (((x_6).victim_valid) && (((x_6).victim_addr) == (x_0)))
                    begin
                    Struct14 x_7 = (Struct14 {victim_valid :
                    (x_6).victim_valid, victim_addr : (x_6).victim_addr,
                    victim_info : (x_6).victim_info, victim_value :
                    (x_6).victim_value, victim_req :
                    (Bool)'(True)});
                    victimRegs__001 <= update (x_1, (Bit#(2))'(2'h1), x_7);
                end else begin
                    Struct14 x_8 =
                    ((x_1)[(Bit#(2))'(2'h0)]);
                    if (((x_8).victim_valid) && (((x_8).victim_addr) ==
                        (x_0))) begin
                        Struct14 x_9 = (Struct14 {victim_valid :
                        (x_8).victim_valid, victim_addr : (x_8).victim_addr,
                        victim_info : (x_8).victim_info, victim_value :
                        (x_8).victim_value, victim_req :
                        (Bool)'(True)});
                        victimRegs__001 <= update (x_1, (Bit#(2))'(2'h0),
                        x_9);
                    end else begin

                    end
                end
            end
        end
    endmethod

    method Action victims__001__releaseVictim (Bit#(64) x_0);
        let x_1 = (victimRegs__001);
        Struct14 x_2 =
        ((x_1)[(Bit#(2))'(2'h0)]);
        if (((x_2).victim_valid) && (((x_2).victim_addr) == (x_0)))
            begin
            victimRegs__001 <= update (x_1, (Bit#(2))'(2'h0), unpack(0));
        end else begin
            Struct14 x_3 =
            ((x_1)[(Bit#(2))'(2'h1)]);
            if (((x_3).victim_valid) && (((x_3).victim_addr) == (x_0)))
                begin
                victimRegs__001 <= update (x_1, (Bit#(2))'(2'h1), unpack(0));
            end else begin
                Struct14 x_4 =
                ((x_1)[(Bit#(2))'(2'h2)]);
                if (((x_4).victim_valid) && (((x_4).victim_addr) == (x_0)))
                    begin
                    victimRegs__001 <= update (x_1, (Bit#(2))'(2'h2),
                    unpack(0));
                end else begin
                    Struct14 x_5 =
                    ((x_1)[(Bit#(2))'(2'h3)]);
                    if (((x_5).victim_valid) && (((x_5).victim_addr) ==
                        (x_0))) begin
                        victimRegs__001 <= update (x_1, (Bit#(2))'(2'h3),
                        unpack(0));
                    end else begin

                    end
                end
            end
        end
    endmethod
endmodule

interface Module52;
    method Action rdReq_infoRam__001__3 (Bit#(8) x_0);
    method Action wrReq_infoRam__001__3 (Struct50 x_0);
    method ActionValue#(Struct48) rdResp_infoRam__001__3 ();
endinterface

module mkModule52 (Module52);
    RWBramCore#(Bit#(8), Struct48) bram <- mkRWBramCore();
    Reg#(Bool) initDone <- mkReg(False);
    Reg#(Bit#(8)) initIdx <- mkReg(0);

    rule init (!initDone);
        let initData = Struct48 {tag: 51'h7, value: Struct11 {mesi_owned: False, mesi_status: 3'h1, mesi_dir_st: 3'h1, mesi_dir_sharers: 2'h0}};
        bram.wrReq(initIdx, initData);
        initIdx <= initIdx + 1;
        initDone <= (initIdx == maxBound);
    endrule

    method Action rdReq_infoRam__001__3 (Bit#(8) x_0) if(initDone);
        bram.rdReq(x_0);
    endmethod

    method Action wrReq_infoRam__001__3 (Struct50 x_0) if(initDone);
        bram.wrReq(x_0.addr, x_0.datain);
    endmethod

    method ActionValue#(Struct48) rdResp_infoRam__001__3 () if(initDone);
        bram.deqRdResp ();
        let data = bram.rdResp ();
        return data;
    endmethod


endmodule

interface Module53;
    method Action rdReq_infoRam__001__2 (Bit#(8) x_0);
    method Action wrReq_infoRam__001__2 (Struct50 x_0);
    method ActionValue#(Struct48) rdResp_infoRam__001__2 ();
endinterface

module mkModule53 (Module53);
    RWBramCore#(Bit#(8), Struct48) bram <- mkRWBramCore();
    Reg#(Bool) initDone <- mkReg(False);
    Reg#(Bit#(8)) initIdx <- mkReg(0);

    rule init (!initDone);
        let initData = Struct48 {tag: 51'h6, value: Struct11 {mesi_owned: False, mesi_status: 3'h1, mesi_dir_st: 3'h1, mesi_dir_sharers: 2'h0}};
        bram.wrReq(initIdx, initData);
        initIdx <= initIdx + 1;
        initDone <= (initIdx == maxBound);
    endrule

    method Action rdReq_infoRam__001__2 (Bit#(8) x_0) if(initDone);
        bram.rdReq(x_0);
    endmethod

    method Action wrReq_infoRam__001__2 (Struct50 x_0) if(initDone);
        bram.wrReq(x_0.addr, x_0.datain);
    endmethod

    method ActionValue#(Struct48) rdResp_infoRam__001__2 () if(initDone);
        bram.deqRdResp ();
        let data = bram.rdResp ();
        return data;
    endmethod


endmodule

interface Module54;
    method Action rdReq_infoRam__001__1 (Bit#(8) x_0);
    method Action wrReq_infoRam__001__1 (Struct50 x_0);
    method ActionValue#(Struct48) rdResp_infoRam__001__1 ();
endinterface

module mkModule54 (Module54);
    RWBramCore#(Bit#(8), Struct48) bram <- mkRWBramCore();
    Reg#(Bool) initDone <- mkReg(False);
    Reg#(Bit#(8)) initIdx <- mkReg(0);

    rule init (!initDone);
        let initData = Struct48 {tag: 51'h5, value: Struct11 {mesi_owned: False, mesi_status: 3'h1, mesi_dir_st: 3'h1, mesi_dir_sharers: 2'h0}};
        bram.wrReq(initIdx, initData);
        initIdx <= initIdx + 1;
        initDone <= (initIdx == maxBound);
    endrule

    method Action rdReq_infoRam__001__1 (Bit#(8) x_0) if(initDone);
        bram.rdReq(x_0);
    endmethod

    method Action wrReq_infoRam__001__1 (Struct50 x_0) if(initDone);
        bram.wrReq(x_0.addr, x_0.datain);
    endmethod

    method ActionValue#(Struct48) rdResp_infoRam__001__1 () if(initDone);
        bram.deqRdResp ();
        let data = bram.rdResp ();
        return data;
    endmethod


endmodule

interface Module55;
    method Action rdReq_infoRam__001__0 (Bit#(8) x_0);
    method Action wrReq_infoRam__001__0 (Struct50 x_0);
    method ActionValue#(Struct48) rdResp_infoRam__001__0 ();
endinterface

module mkModule55 (Module55);
    RWBramCore#(Bit#(8), Struct48) bram <- mkRWBramCore();
    Reg#(Bool) initDone <- mkReg(False);
    Reg#(Bit#(8)) initIdx <- mkReg(0);

    rule init (!initDone);
        let initData = Struct48 {tag: 51'h4, value: Struct11 {mesi_owned: False, mesi_status: 3'h1, mesi_dir_st: 3'h1, mesi_dir_sharers: 2'h0}};
        bram.wrReq(initIdx, initData);
        initIdx <= initIdx + 1;
        initDone <= (initIdx == maxBound);
    endrule

    method Action rdReq_infoRam__001__0 (Bit#(8) x_0) if(initDone);
        bram.rdReq(x_0);
    endmethod

    method Action wrReq_infoRam__001__0 (Struct50 x_0) if(initDone);
        bram.wrReq(x_0.addr, x_0.datain);
    endmethod

    method ActionValue#(Struct48) rdResp_infoRam__001__0 () if(initDone);
        bram.deqRdResp ();
        let data = bram.rdResp ();
        return data;
    endmethod


endmodule

interface Module56;
    method Action rdReq_dataRam__001 (Bit#(10) x_0);
    method Action wrReq_dataRam__001 (Struct52 x_0);
    method ActionValue#(Vector#(4, Bit#(64))) rdResp_dataRam__001 ();
endinterface

module mkModule56 (Module56);
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

    method Action wrReq_dataRam__001 (Struct52 x_0) if(initDone);
        bram.wrReq(x_0.addr, x_0.datain);
    endmethod

    method ActionValue#(Vector#(4, Bit#(64))) rdResp_dataRam__001 ()
    if(initDone);
        bram.deqRdResp ();
        let data = bram.rdResp ();
        return data;
    endmethod


endmodule

interface Module57;
    method Action rdReq_repRam__001 (Bit#(8) x_0);
    method Action wrReq_repRam__001 (Struct53 x_0);
    method ActionValue#(Vector#(4, Bit#(8))) rdResp_repRam__001 ();
endinterface

module mkModule57 (Module57);
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

    method Action wrReq_repRam__001 (Struct53 x_0) if(initDone);
        bram.wrReq(x_0.addr, x_0.datain);
    endmethod

    method ActionValue#(Vector#(4, Bit#(8))) rdResp_repRam__001 ()
    if(initDone);
        bram.deqRdResp ();
        let data = bram.rdResp ();
        return data;
    endmethod


endmodule

interface Module58;
    method ActionValue#(Struct44) getMSHR_001 (Bit#(3) x_0);
    method ActionValue#(Struct1) getMSHRRq_001 (Bit#(3) x_0);
    method ActionValue#(Struct1) getMSHRFirstRs_001 (Bit#(3) x_0);
    method ActionValue#(Struct39) getPRqSlot_001 (Struct38 x_0);
    method ActionValue#(Struct39) getCRqSlot_001 (Struct38 x_0);
    method ActionValue#(Struct38) getWait_001 ();
    method Action registerUL_001 (Struct46 x_0);
    method Action registerDL_001 (Struct54 x_0);
    method Action canImm_001 (Bit#(64) x_0);
    method Action setULImm_001 (Struct1 x_0);
    method Action transferUpDown_001 (Struct55 x_0);
    method Action addRs_001 (Struct7 x_0);
    method ActionValue#(Bit#(3)) getULReady_001 (Bit#(64) x_0);
    method ActionValue#(Struct56) getDLReady_001 ();
    method Action startRelease_001 (Bit#(3) x_0);
    method Action releaseMSHR_001 (Bit#(3) x_0);
endinterface

module mkModule58
    (Module58);
    Reg#(Vector#(6, Struct44)) mshrs_001 <- mkReg(unpack(0));
    Reg#(Vector#(6, Struct1)) rqs_001 <- mkReg(unpack(0));
    Reg#(Vector#(6, Struct37)) rss_001 <- mkReg(unpack(0));

    // No rules in this module

    method ActionValue#(Struct44) getMSHR_001 (Bit#(3) x_0);
        let x_1 = (mshrs_001);
        return (x_1)[x_0];
    endmethod

    method ActionValue#(Struct1) getMSHRRq_001 (Bit#(3) x_0);
        let x_1 = (rqs_001);
        return (x_1)[x_0];
    endmethod

    method ActionValue#(Struct1) getMSHRFirstRs_001 (Bit#(3) x_0);
        let x_1 = (mshrs_001);
        Struct44 x_2 = ((x_1)[x_0]);
        Bit#(2) x_3 = ((x_2).m_dl_rss_recv);
        Bit#(1) x_4 = ((((x_3)[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(1))'(1'h0)) : (((Bit#(1))'(1'h1)) + (((((x_3)[1:1])[0:0]) ==
        ((Bit#(1))'(1'h1)) ? ((Bit#(1))'(1'h0)) : (((Bit#(1))'(1'h1)) +
        (unpack(0))))))));
        let x_5 = (rss_001);
        Struct37 x_6 = ((x_5)[x_0]);
        Struct1 x_7 = (((x_6).m_dl_rss)[x_4]);
        return x_7;
    endmethod

    method ActionValue#(Struct39) getPRqSlot_001 (Struct38 x_0);
        let x_1 = (mshrs_001);
        Struct5 x_2 = (((((x_1)[(Bit#(3))'(3'h0)]).m_status) ==
        ((Bit#(3))'(3'h0)) ? (Struct5 {valid : (Bool)'(True), data :
        (Bit#(3))'(3'h0)}) : (((((x_1)[(Bit#(3))'(3'h1)]).m_status) ==
        ((Bit#(3))'(3'h0)) ? (Struct5 {valid : (Bool)'(True), data :
        (Bit#(3))'(3'h1)}) : (Struct5 {valid : (Bool)'(False), data :
        unpack(0)})))));
        Bool x_3 = ((x_2).valid);
        Bit#(3) x_4 = ((x_2).data);
        Bit#(64) x_5 = (((x_0).r_msg).addr);
        Bool x_6 = (((((((x_1)[(Bit#(3))'(3'h0)]).m_status) ==
        ((Bit#(3))'(3'h4))) || ((((x_1)[(Bit#(3))'(3'h0)]).m_status) ==
        ((Bit#(3))'(3'h6)))) && (((! ((((x_1)[(Bit#(3))'(3'h0)]).m_addr) ==
        (x_5))) && (((((x_1)[(Bit#(3))'(3'h0)]).m_addr)[12:5]) ==
        ((x_5)[12:5]))) || ((((x_1)[(Bit#(3))'(3'h0)]).m_addr) == (x_5))) ?
        ((Bool)'(True)) : (((((((x_1)[(Bit#(3))'(3'h1)]).m_status) ==
        ((Bit#(3))'(3'h4))) || ((((x_1)[(Bit#(3))'(3'h1)]).m_status) ==
        ((Bit#(3))'(3'h6)))) && (((! ((((x_1)[(Bit#(3))'(3'h1)]).m_addr) ==
        (x_5))) && (((((x_1)[(Bit#(3))'(3'h1)]).m_addr)[12:5]) ==
        ((x_5)[12:5]))) || ((((x_1)[(Bit#(3))'(3'h1)]).m_addr) == (x_5))) ?
        ((Bool)'(True)) : (((((((x_1)[(Bit#(3))'(3'h2)]).m_status) ==
        ((Bit#(3))'(3'h4))) || ((((x_1)[(Bit#(3))'(3'h2)]).m_status) ==
        ((Bit#(3))'(3'h6)))) && (((! ((((x_1)[(Bit#(3))'(3'h2)]).m_addr) ==
        (x_5))) && (((((x_1)[(Bit#(3))'(3'h2)]).m_addr)[12:5]) ==
        ((x_5)[12:5]))) || ((((x_1)[(Bit#(3))'(3'h2)]).m_addr) == (x_5))) ?
        ((Bool)'(True)) : (((((((x_1)[(Bit#(3))'(3'h3)]).m_status) ==
        ((Bit#(3))'(3'h4))) || ((((x_1)[(Bit#(3))'(3'h3)]).m_status) ==
        ((Bit#(3))'(3'h6)))) && (((! ((((x_1)[(Bit#(3))'(3'h3)]).m_addr) ==
        (x_5))) && (((((x_1)[(Bit#(3))'(3'h3)]).m_addr)[12:5]) ==
        ((x_5)[12:5]))) || ((((x_1)[(Bit#(3))'(3'h3)]).m_addr) == (x_5))) ?
        ((Bool)'(True)) : (((((((x_1)[(Bit#(3))'(3'h4)]).m_status) ==
        ((Bit#(3))'(3'h4))) || ((((x_1)[(Bit#(3))'(3'h4)]).m_status) ==
        ((Bit#(3))'(3'h6)))) && (((! ((((x_1)[(Bit#(3))'(3'h4)]).m_addr) ==
        (x_5))) && (((((x_1)[(Bit#(3))'(3'h4)]).m_addr)[12:5]) ==
        ((x_5)[12:5]))) || ((((x_1)[(Bit#(3))'(3'h4)]).m_addr) == (x_5))) ?
        ((Bool)'(True)) : (((((((x_1)[(Bit#(3))'(3'h5)]).m_status) ==
        ((Bit#(3))'(3'h4))) || ((((x_1)[(Bit#(3))'(3'h5)]).m_status) ==
        ((Bit#(3))'(3'h6)))) && (((! ((((x_1)[(Bit#(3))'(3'h5)]).m_addr) ==
        (x_5))) && (((((x_1)[(Bit#(3))'(3'h5)]).m_addr)[12:5]) ==
        ((x_5)[12:5]))) || ((((x_1)[(Bit#(3))'(3'h5)]).m_addr) == (x_5))) ?
        ((Bool)'(True)) : ((Bool)'(False))))))))))))));
        Struct5 x_7 = (((((((x_1)[(Bit#(3))'(3'h0)]).m_status) ==
        ((Bit#(3))'(3'h5))) && (! (((x_1)[(Bit#(3))'(3'h0)]).m_is_ul))) &&
        ((((x_1)[(Bit#(3))'(3'h0)]).m_addr) == (x_5)) ? (Struct5 {valid :
        (Bool)'(True), data : (Bit#(3))'(3'h0)}) :
        (((((((x_1)[(Bit#(3))'(3'h1)]).m_status) == ((Bit#(3))'(3'h5))) && (!
        (((x_1)[(Bit#(3))'(3'h1)]).m_is_ul))) &&
        ((((x_1)[(Bit#(3))'(3'h1)]).m_addr) == (x_5)) ? (Struct5 {valid :
        (Bool)'(True), data : (Bit#(3))'(3'h1)}) :
        (((((((x_1)[(Bit#(3))'(3'h2)]).m_status) == ((Bit#(3))'(3'h5))) && (!
        (((x_1)[(Bit#(3))'(3'h2)]).m_is_ul))) &&
        ((((x_1)[(Bit#(3))'(3'h2)]).m_addr) == (x_5)) ? (Struct5 {valid :
        (Bool)'(True), data : (Bit#(3))'(3'h2)}) :
        (((((((x_1)[(Bit#(3))'(3'h3)]).m_status) == ((Bit#(3))'(3'h5))) && (!
        (((x_1)[(Bit#(3))'(3'h3)]).m_is_ul))) &&
        ((((x_1)[(Bit#(3))'(3'h3)]).m_addr) == (x_5)) ? (Struct5 {valid :
        (Bool)'(True), data : (Bit#(3))'(3'h3)}) :
        (((((((x_1)[(Bit#(3))'(3'h4)]).m_status) == ((Bit#(3))'(3'h5))) && (!
        (((x_1)[(Bit#(3))'(3'h4)]).m_is_ul))) &&
        ((((x_1)[(Bit#(3))'(3'h4)]).m_addr) == (x_5)) ? (Struct5 {valid :
        (Bool)'(True), data : (Bit#(3))'(3'h4)}) :
        (((((((x_1)[(Bit#(3))'(3'h5)]).m_status) == ((Bit#(3))'(3'h5))) && (!
        (((x_1)[(Bit#(3))'(3'h5)]).m_is_ul))) &&
        ((((x_1)[(Bit#(3))'(3'h5)]).m_addr) == (x_5)) ? (Struct5 {valid :
        (Bool)'(True), data : (Bit#(3))'(3'h5)}) : (Struct5 {valid :
        (Bool)'(False), data : unpack(0)})))))))))))));
        Bool x_8 = ((x_7).valid);
        Struct39 x_9 = (Struct39 {s_has_slot : (x_3) && (! (x_6)), s_conflict
        : x_8, s_id :
        x_4});
        if ((x_3) && (! (x_6))) begin
            Vector#(6, Struct44) x_10 = (update (x_1, x_4, Struct44 {m_status
            : (x_8 ? ((Bit#(3))'(3'h1)) : ((Bit#(3))'(3'h4))), m_next :
            Struct5 {valid : (Bool)'(False), data : unpack(0)}, m_is_ul :
            unpack(0), m_addr : ((x_0).r_msg).addr, m_qidx :
            (x_0).r_msg_from, m_rsb : unpack(0), m_dl_rss_from : unpack(0),
            m_dl_rss_recv : unpack(0)}));
            let x_11 = (rqs_001);
            rqs_001 <= update (x_11, x_4,
            (x_0).r_msg);
            let x_15 = ?;
            if (x_8) begin
                Bit#(3) x_12 = ((((! ((((x_1)[(Bit#(3))'(3'h0)]).m_status) ==
                ((Bit#(3))'(3'h0)))) && (!
                ((((x_1)[(Bit#(3))'(3'h0)]).m_next).valid))) &&
                ((((x_1)[(Bit#(3))'(3'h0)]).m_addr) == (x_5)) ?
                ((Bit#(3))'(3'h0)) : ((((!
                ((((x_1)[(Bit#(3))'(3'h1)]).m_status) == ((Bit#(3))'(3'h0))))
                && (! ((((x_1)[(Bit#(3))'(3'h1)]).m_next).valid))) &&
                ((((x_1)[(Bit#(3))'(3'h1)]).m_addr) == (x_5)) ?
                ((Bit#(3))'(3'h1)) : ((((!
                ((((x_1)[(Bit#(3))'(3'h2)]).m_status) == ((Bit#(3))'(3'h0))))
                && (! ((((x_1)[(Bit#(3))'(3'h2)]).m_next).valid))) &&
                ((((x_1)[(Bit#(3))'(3'h2)]).m_addr) == (x_5)) ?
                ((Bit#(3))'(3'h2)) : ((((!
                ((((x_1)[(Bit#(3))'(3'h3)]).m_status) == ((Bit#(3))'(3'h0))))
                && (! ((((x_1)[(Bit#(3))'(3'h3)]).m_next).valid))) &&
                ((((x_1)[(Bit#(3))'(3'h3)]).m_addr) == (x_5)) ?
                ((Bit#(3))'(3'h3)) : ((((!
                ((((x_1)[(Bit#(3))'(3'h4)]).m_status) == ((Bit#(3))'(3'h0))))
                && (! ((((x_1)[(Bit#(3))'(3'h4)]).m_next).valid))) &&
                ((((x_1)[(Bit#(3))'(3'h4)]).m_addr) == (x_5)) ?
                ((Bit#(3))'(3'h4)) : ((((!
                ((((x_1)[(Bit#(3))'(3'h5)]).m_status) == ((Bit#(3))'(3'h0))))
                && (! ((((x_1)[(Bit#(3))'(3'h5)]).m_next).valid))) &&
                ((((x_1)[(Bit#(3))'(3'h5)]).m_addr) == (x_5)) ?
                ((Bit#(3))'(3'h5)) : (unpack(0))))))))))))));
                Struct44 x_13 = ((x_1)[x_12]);
                Vector#(6, Struct44) x_14 = (update (x_10, x_12, Struct44
                {m_status : (x_13).m_status, m_next : (x_8 ? (Struct5 {valid
                : (Bool)'(True), data : x_4}) : ((x_13).m_next)), m_is_ul :
                (x_13).m_is_ul, m_addr : (x_13).m_addr, m_qidx :
                (x_13).m_qidx, m_rsb : (x_13).m_rsb, m_dl_rss_from :
                (x_13).m_dl_rss_from, m_dl_rss_recv :
                (x_13).m_dl_rss_recv}));
                x_15 = x_14;
            end else begin
                x_15 = x_10;
            end
            mshrs_001 <= x_15;
        end else begin

        end
        return x_9;
    endmethod

    method ActionValue#(Struct39) getCRqSlot_001 (Struct38 x_0);
        let x_1 = (mshrs_001);
        Struct5 x_2 = (((((x_1)[(Bit#(3))'(3'h2)]).m_status) ==
        ((Bit#(3))'(3'h0)) ? (Struct5 {valid : (Bool)'(True), data :
        (Bit#(3))'(3'h2)}) : (((((x_1)[(Bit#(3))'(3'h3)]).m_status) ==
        ((Bit#(3))'(3'h0)) ? (Struct5 {valid : (Bool)'(True), data :
        (Bit#(3))'(3'h3)}) : (((((x_1)[(Bit#(3))'(3'h4)]).m_status) ==
        ((Bit#(3))'(3'h0)) ? (Struct5 {valid : (Bool)'(True), data :
        (Bit#(3))'(3'h4)}) : (((((x_1)[(Bit#(3))'(3'h5)]).m_status) ==
        ((Bit#(3))'(3'h0)) ? (Struct5 {valid : (Bool)'(True), data :
        (Bit#(3))'(3'h5)}) : (Struct5 {valid : (Bool)'(False), data :
        unpack(0)})))))))));
        Bool x_3 = ((x_2).valid);
        Bit#(3) x_4 = ((x_2).data);
        Bit#(64) x_5 = (((x_0).r_msg).addr);
        Bool x_6 = (((((((x_1)[(Bit#(3))'(3'h0)]).m_status) ==
        ((Bit#(3))'(3'h4))) || ((((x_1)[(Bit#(3))'(3'h0)]).m_status) ==
        ((Bit#(3))'(3'h6)))) && ((! ((((x_1)[(Bit#(3))'(3'h0)]).m_addr) ==
        (x_5))) && (((((x_1)[(Bit#(3))'(3'h0)]).m_addr)[12:5]) ==
        ((x_5)[12:5]))) ? ((Bool)'(True)) :
        (((((((x_1)[(Bit#(3))'(3'h1)]).m_status) == ((Bit#(3))'(3'h4))) ||
        ((((x_1)[(Bit#(3))'(3'h1)]).m_status) == ((Bit#(3))'(3'h6)))) && ((!
        ((((x_1)[(Bit#(3))'(3'h1)]).m_addr) == (x_5))) &&
        (((((x_1)[(Bit#(3))'(3'h1)]).m_addr)[12:5]) == ((x_5)[12:5]))) ?
        ((Bool)'(True)) : (((((((x_1)[(Bit#(3))'(3'h2)]).m_status) ==
        ((Bit#(3))'(3'h4))) || ((((x_1)[(Bit#(3))'(3'h2)]).m_status) ==
        ((Bit#(3))'(3'h6)))) && ((! ((((x_1)[(Bit#(3))'(3'h2)]).m_addr) ==
        (x_5))) && (((((x_1)[(Bit#(3))'(3'h2)]).m_addr)[12:5]) ==
        ((x_5)[12:5]))) ? ((Bool)'(True)) :
        (((((((x_1)[(Bit#(3))'(3'h3)]).m_status) == ((Bit#(3))'(3'h4))) ||
        ((((x_1)[(Bit#(3))'(3'h3)]).m_status) == ((Bit#(3))'(3'h6)))) && ((!
        ((((x_1)[(Bit#(3))'(3'h3)]).m_addr) == (x_5))) &&
        (((((x_1)[(Bit#(3))'(3'h3)]).m_addr)[12:5]) == ((x_5)[12:5]))) ?
        ((Bool)'(True)) : (((((((x_1)[(Bit#(3))'(3'h4)]).m_status) ==
        ((Bit#(3))'(3'h4))) || ((((x_1)[(Bit#(3))'(3'h4)]).m_status) ==
        ((Bit#(3))'(3'h6)))) && ((! ((((x_1)[(Bit#(3))'(3'h4)]).m_addr) ==
        (x_5))) && (((((x_1)[(Bit#(3))'(3'h4)]).m_addr)[12:5]) ==
        ((x_5)[12:5]))) ? ((Bool)'(True)) :
        (((((((x_1)[(Bit#(3))'(3'h5)]).m_status) == ((Bit#(3))'(3'h4))) ||
        ((((x_1)[(Bit#(3))'(3'h5)]).m_status) == ((Bit#(3))'(3'h6)))) && ((!
        ((((x_1)[(Bit#(3))'(3'h5)]).m_addr) == (x_5))) &&
        (((((x_1)[(Bit#(3))'(3'h5)]).m_addr)[12:5]) == ((x_5)[12:5]))) ?
        ((Bool)'(True)) : ((Bool)'(False))))))))))))));
        Struct5 x_7 = (((((! ((((x_1)[(Bit#(3))'(3'h2)]).m_status) ==
        ((Bit#(3))'(3'h0)))) && (!
        ((((x_1)[(Bit#(3))'(3'h2)]).m_next).valid))) &&
        (((x_1)[(Bit#(3))'(3'h2)]).m_is_ul)) &&
        ((((x_1)[(Bit#(3))'(3'h2)]).m_addr) == (x_5)) ? (Struct5 {valid :
        (Bool)'(True), data : (Bit#(3))'(3'h2)}) : (((((!
        ((((x_1)[(Bit#(3))'(3'h3)]).m_status) == ((Bit#(3))'(3'h0)))) && (!
        ((((x_1)[(Bit#(3))'(3'h3)]).m_next).valid))) &&
        (((x_1)[(Bit#(3))'(3'h3)]).m_is_ul)) &&
        ((((x_1)[(Bit#(3))'(3'h3)]).m_addr) == (x_5)) ? (Struct5 {valid :
        (Bool)'(True), data : (Bit#(3))'(3'h3)}) : (((((!
        ((((x_1)[(Bit#(3))'(3'h4)]).m_status) == ((Bit#(3))'(3'h0)))) && (!
        ((((x_1)[(Bit#(3))'(3'h4)]).m_next).valid))) &&
        (((x_1)[(Bit#(3))'(3'h4)]).m_is_ul)) &&
        ((((x_1)[(Bit#(3))'(3'h4)]).m_addr) == (x_5)) ? (Struct5 {valid :
        (Bool)'(True), data : (Bit#(3))'(3'h4)}) : (((((!
        ((((x_1)[(Bit#(3))'(3'h5)]).m_status) == ((Bit#(3))'(3'h0)))) && (!
        ((((x_1)[(Bit#(3))'(3'h5)]).m_next).valid))) &&
        (((x_1)[(Bit#(3))'(3'h5)]).m_is_ul)) &&
        ((((x_1)[(Bit#(3))'(3'h5)]).m_addr) == (x_5)) ? (Struct5 {valid :
        (Bool)'(True), data : (Bit#(3))'(3'h5)}) : (Struct5 {valid :
        (Bool)'(False), data : unpack(0)})))))))));
        Struct5 x_8 = (((((! ((((x_1)[(Bit#(3))'(3'h0)]).m_status) ==
        ((Bit#(3))'(3'h0)))) && (!
        ((((x_1)[(Bit#(3))'(3'h0)]).m_next).valid))) && (!
        (((x_1)[(Bit#(3))'(3'h0)]).m_is_ul))) &&
        ((((x_1)[(Bit#(3))'(3'h0)]).m_addr) == (x_5)) ? (Struct5 {valid :
        (Bool)'(True), data : (Bit#(3))'(3'h0)}) : (((((!
        ((((x_1)[(Bit#(3))'(3'h1)]).m_status) == ((Bit#(3))'(3'h0)))) && (!
        ((((x_1)[(Bit#(3))'(3'h1)]).m_next).valid))) && (!
        (((x_1)[(Bit#(3))'(3'h1)]).m_is_ul))) &&
        ((((x_1)[(Bit#(3))'(3'h1)]).m_addr) == (x_5)) ? (Struct5 {valid :
        (Bool)'(True), data : (Bit#(3))'(3'h1)}) : (((((!
        ((((x_1)[(Bit#(3))'(3'h2)]).m_status) == ((Bit#(3))'(3'h0)))) && (!
        ((((x_1)[(Bit#(3))'(3'h2)]).m_next).valid))) && (!
        (((x_1)[(Bit#(3))'(3'h2)]).m_is_ul))) &&
        ((((x_1)[(Bit#(3))'(3'h2)]).m_addr) == (x_5)) ? (Struct5 {valid :
        (Bool)'(True), data : (Bit#(3))'(3'h2)}) : (((((!
        ((((x_1)[(Bit#(3))'(3'h3)]).m_status) == ((Bit#(3))'(3'h0)))) && (!
        ((((x_1)[(Bit#(3))'(3'h3)]).m_next).valid))) && (!
        (((x_1)[(Bit#(3))'(3'h3)]).m_is_ul))) &&
        ((((x_1)[(Bit#(3))'(3'h3)]).m_addr) == (x_5)) ? (Struct5 {valid :
        (Bool)'(True), data : (Bit#(3))'(3'h3)}) : (((((!
        ((((x_1)[(Bit#(3))'(3'h4)]).m_status) == ((Bit#(3))'(3'h0)))) && (!
        ((((x_1)[(Bit#(3))'(3'h4)]).m_next).valid))) && (!
        (((x_1)[(Bit#(3))'(3'h4)]).m_is_ul))) &&
        ((((x_1)[(Bit#(3))'(3'h4)]).m_addr) == (x_5)) ? (Struct5 {valid :
        (Bool)'(True), data : (Bit#(3))'(3'h4)}) : (((((!
        ((((x_1)[(Bit#(3))'(3'h5)]).m_status) == ((Bit#(3))'(3'h0)))) && (!
        ((((x_1)[(Bit#(3))'(3'h5)]).m_next).valid))) && (!
        (((x_1)[(Bit#(3))'(3'h5)]).m_is_ul))) &&
        ((((x_1)[(Bit#(3))'(3'h5)]).m_addr) == (x_5)) ? (Struct5 {valid :
        (Bool)'(True), data : (Bit#(3))'(3'h5)}) : (Struct5 {valid :
        (Bool)'(False), data : unpack(0)})))))))))))));
        Bool x_9 = ((x_7).valid);
        Bool x_10 = ((x_8).valid);
        Bool x_11 = ((x_9) || (x_10));
        Struct39 x_12 = (Struct39 {s_has_slot : (x_3) && (! (x_6)),
        s_conflict : x_11, s_id :
        x_4});
        if ((x_3) && (! (x_6))) begin
            Vector#(6, Struct44) x_13 = (update (x_1, x_4, Struct44 {m_status
            : (x_11 ? ((Bit#(3))'(3'h1)) : ((Bit#(3))'(3'h4))), m_next :
            Struct5 {valid : (Bool)'(False), data : unpack(0)}, m_is_ul :
            unpack(0), m_addr : ((x_0).r_msg).addr, m_qidx :
            (x_0).r_msg_from, m_rsb : unpack(0), m_dl_rss_from : unpack(0),
            m_dl_rss_recv : unpack(0)}));
            let x_14 = (rqs_001);
            rqs_001 <= update (x_14, x_4,
            (x_0).r_msg);
            let x_18 = ?;
            if (x_11) begin
                Bit#(3) x_15 = ((x_9 ? ((x_7).data) : ((x_8).data)));
                Struct44 x_16 = ((x_1)[x_15]);
                Vector#(6, Struct44) x_17 = (update (x_13, x_15, Struct44
                {m_status : (x_16).m_status, m_next : (x_11 ? (Struct5 {valid
                : (Bool)'(True), data : x_4}) : ((x_16).m_next)), m_is_ul :
                (x_16).m_is_ul, m_addr : (x_16).m_addr, m_qidx :
                (x_16).m_qidx, m_rsb : (x_16).m_rsb, m_dl_rss_from :
                (x_16).m_dl_rss_from, m_dl_rss_recv :
                (x_16).m_dl_rss_recv}));
                x_18 = x_17;
            end else begin
                x_18 = x_13;
            end
            mshrs_001 <= x_18;
        end else begin

        end
        return x_12;
    endmethod

    method ActionValue#(Struct38) getWait_001 ();
        let x_1 = (mshrs_001);
        let x_2 = (rqs_001);
        Struct5 x_3 = (((((x_1)[(Bit#(3))'(3'h0)]).m_status) ==
        ((Bit#(3))'(3'h2)) ? (Struct5 {valid : (Bool)'(True), data :
        (Bit#(3))'(3'h0)}) : (((((x_1)[(Bit#(3))'(3'h1)]).m_status) ==
        ((Bit#(3))'(3'h2)) ? (Struct5 {valid : (Bool)'(True), data :
        (Bit#(3))'(3'h1)}) : (((((x_1)[(Bit#(3))'(3'h2)]).m_status) ==
        ((Bit#(3))'(3'h2)) ? (Struct5 {valid : (Bool)'(True), data :
        (Bit#(3))'(3'h2)}) : (((((x_1)[(Bit#(3))'(3'h3)]).m_status) ==
        ((Bit#(3))'(3'h2)) ? (Struct5 {valid : (Bool)'(True), data :
        (Bit#(3))'(3'h3)}) : (((((x_1)[(Bit#(3))'(3'h4)]).m_status) ==
        ((Bit#(3))'(3'h2)) ? (Struct5 {valid : (Bool)'(True), data :
        (Bit#(3))'(3'h4)}) : (((((x_1)[(Bit#(3))'(3'h5)]).m_status) ==
        ((Bit#(3))'(3'h2)) ? (Struct5 {valid : (Bool)'(True), data :
        (Bit#(3))'(3'h5)}) : (Struct5 {valid : (Bool)'(False), data :
        unpack(0)})))))))))))));
        when ((x_3).valid, noAction);
        Bit#(3) x_4 = ((x_3).data);
        Struct44 x_5 = ((x_1)[x_4]);
        Struct1 x_6 = ((x_2)[x_4]);
        Bit#(64) x_7 = ((x_5).m_addr);
        Bool x_8 = ((((! ((((x_1)[(Bit#(3))'(3'h0)]).m_status) <
        ((Bit#(3))'(3'h4)))) && ((((x_1)[(Bit#(3))'(3'h0)]).m_addr) ==
        (x_7))) || ((((((x_1)[(Bit#(3))'(3'h0)]).m_status) ==
        ((Bit#(3))'(3'h4))) || ((((x_1)[(Bit#(3))'(3'h0)]).m_status) ==
        ((Bit#(3))'(3'h6)))) && ((! ((((x_1)[(Bit#(3))'(3'h0)]).m_addr) ==
        (x_7))) && (((((x_1)[(Bit#(3))'(3'h0)]).m_addr)[12:5]) ==
        ((x_7)[12:5])))) ? ((Bool)'(True)) : ((((!
        ((((x_1)[(Bit#(3))'(3'h1)]).m_status) < ((Bit#(3))'(3'h4)))) &&
        ((((x_1)[(Bit#(3))'(3'h1)]).m_addr) == (x_7))) ||
        ((((((x_1)[(Bit#(3))'(3'h1)]).m_status) == ((Bit#(3))'(3'h4))) ||
        ((((x_1)[(Bit#(3))'(3'h1)]).m_status) == ((Bit#(3))'(3'h6)))) && ((!
        ((((x_1)[(Bit#(3))'(3'h1)]).m_addr) == (x_7))) &&
        (((((x_1)[(Bit#(3))'(3'h1)]).m_addr)[12:5]) == ((x_7)[12:5])))) ?
        ((Bool)'(True)) : ((((! ((((x_1)[(Bit#(3))'(3'h2)]).m_status) <
        ((Bit#(3))'(3'h4)))) && ((((x_1)[(Bit#(3))'(3'h2)]).m_addr) ==
        (x_7))) || ((((((x_1)[(Bit#(3))'(3'h2)]).m_status) ==
        ((Bit#(3))'(3'h4))) || ((((x_1)[(Bit#(3))'(3'h2)]).m_status) ==
        ((Bit#(3))'(3'h6)))) && ((! ((((x_1)[(Bit#(3))'(3'h2)]).m_addr) ==
        (x_7))) && (((((x_1)[(Bit#(3))'(3'h2)]).m_addr)[12:5]) ==
        ((x_7)[12:5])))) ? ((Bool)'(True)) : ((((!
        ((((x_1)[(Bit#(3))'(3'h3)]).m_status) < ((Bit#(3))'(3'h4)))) &&
        ((((x_1)[(Bit#(3))'(3'h3)]).m_addr) == (x_7))) ||
        ((((((x_1)[(Bit#(3))'(3'h3)]).m_status) == ((Bit#(3))'(3'h4))) ||
        ((((x_1)[(Bit#(3))'(3'h3)]).m_status) == ((Bit#(3))'(3'h6)))) && ((!
        ((((x_1)[(Bit#(3))'(3'h3)]).m_addr) == (x_7))) &&
        (((((x_1)[(Bit#(3))'(3'h3)]).m_addr)[12:5]) == ((x_7)[12:5])))) ?
        ((Bool)'(True)) : ((((! ((((x_1)[(Bit#(3))'(3'h4)]).m_status) <
        ((Bit#(3))'(3'h4)))) && ((((x_1)[(Bit#(3))'(3'h4)]).m_addr) ==
        (x_7))) || ((((((x_1)[(Bit#(3))'(3'h4)]).m_status) ==
        ((Bit#(3))'(3'h4))) || ((((x_1)[(Bit#(3))'(3'h4)]).m_status) ==
        ((Bit#(3))'(3'h6)))) && ((! ((((x_1)[(Bit#(3))'(3'h4)]).m_addr) ==
        (x_7))) && (((((x_1)[(Bit#(3))'(3'h4)]).m_addr)[12:5]) ==
        ((x_7)[12:5])))) ? ((Bool)'(True)) : ((((!
        ((((x_1)[(Bit#(3))'(3'h5)]).m_status) < ((Bit#(3))'(3'h4)))) &&
        ((((x_1)[(Bit#(3))'(3'h5)]).m_addr) == (x_7))) ||
        ((((((x_1)[(Bit#(3))'(3'h5)]).m_status) == ((Bit#(3))'(3'h4))) ||
        ((((x_1)[(Bit#(3))'(3'h5)]).m_status) == ((Bit#(3))'(3'h6)))) && ((!
        ((((x_1)[(Bit#(3))'(3'h5)]).m_addr) == (x_7))) &&
        (((((x_1)[(Bit#(3))'(3'h5)]).m_addr)[12:5]) == ((x_7)[12:5])))) ?
        ((Bool)'(True)) : ((Bool)'(False))))))))))))));
        when (! (x_8), noAction);
        mshrs_001 <= update (x_1, x_4, Struct44 {m_status : (Bit#(3))'(3'h4),
        m_next : (x_5).m_next, m_is_ul : (x_5).m_is_ul, m_addr :
        (x_5).m_addr, m_qidx : (x_5).m_qidx, m_rsb : (x_5).m_rsb,
        m_dl_rss_from : (x_5).m_dl_rss_from, m_dl_rss_recv :
        (x_5).m_dl_rss_recv});
        Struct38 x_9 = (Struct38 {r_id : x_4, r_msg : x_6, r_msg_from :
        (x_5).m_qidx});
        return x_9;
    endmethod

    method Action registerUL_001 (Struct46 x_0);
        let x_1 = (mshrs_001);
        Bit#(3) x_2 = ((x_0).r_id);
        Struct44 x_3 = ((x_1)[x_2]);
        Struct44 x_4 = (Struct44 {m_status : (Bit#(3))'(3'h5), m_next :
        (x_3).m_next, m_is_ul : (Bool)'(True), m_addr : (x_3).m_addr, m_qidx
        : {((Bit#(2))'(2'h2)),((x_0).r_ul_rsbTo)}, m_rsb : (x_0).r_ul_rsb,
        m_dl_rss_from : unpack(0), m_dl_rss_recv : unpack(0)});
        mshrs_001 <= update (x_1, x_2, x_4);
    endmethod

    method Action registerDL_001 (Struct54 x_0);
        Bit#(3) x_1 = ((x_0).r_id);
        let x_2 = (mshrs_001);
        Struct44 x_3 = ((x_2)[x_1]);
        Struct44 x_4 = (Struct44 {m_status : (Bit#(3))'(3'h5), m_next :
        (x_3).m_next, m_is_ul : (Bool)'(False), m_addr : (x_3).m_addr, m_qidx
        : (x_0).r_dl_rsbTo, m_rsb : (x_0).r_dl_rsb, m_dl_rss_from :
        (x_0).r_dl_rss_from, m_dl_rss_recv : unpack(0)});
        mshrs_001 <= update (x_2, x_1, x_4);
    endmethod

    method Action canImm_001 (Bit#(64) x_0);
        let x_1 = (mshrs_001);
        Struct5 x_2 = (((((x_1)[(Bit#(3))'(3'h2)]).m_status) ==
        ((Bit#(3))'(3'h0)) ? (Struct5 {valid : (Bool)'(True), data :
        (Bit#(3))'(3'h2)}) : (((((x_1)[(Bit#(3))'(3'h3)]).m_status) ==
        ((Bit#(3))'(3'h0)) ? (Struct5 {valid : (Bool)'(True), data :
        (Bit#(3))'(3'h3)}) : (((((x_1)[(Bit#(3))'(3'h4)]).m_status) ==
        ((Bit#(3))'(3'h0)) ? (Struct5 {valid : (Bool)'(True), data :
        (Bit#(3))'(3'h4)}) : (((((x_1)[(Bit#(3))'(3'h5)]).m_status) ==
        ((Bit#(3))'(3'h0)) ? (Struct5 {valid : (Bool)'(True), data :
        (Bit#(3))'(3'h5)}) : (Struct5 {valid : (Bool)'(False), data :
        unpack(0)})))))))));
        when ((x_2).valid, noAction);
        Struct5 x_3 = ((((! ((((x_1)[(Bit#(3))'(3'h0)]).m_status) ==
        ((Bit#(3))'(3'h0)))) && (!
        ((((x_1)[(Bit#(3))'(3'h0)]).m_next).valid))) &&
        ((((x_1)[(Bit#(3))'(3'h0)]).m_addr) == (x_0)) ? (Struct5 {valid :
        (Bool)'(True), data : (Bit#(3))'(3'h0)}) : ((((!
        ((((x_1)[(Bit#(3))'(3'h1)]).m_status) == ((Bit#(3))'(3'h0)))) && (!
        ((((x_1)[(Bit#(3))'(3'h1)]).m_next).valid))) &&
        ((((x_1)[(Bit#(3))'(3'h1)]).m_addr) == (x_0)) ? (Struct5 {valid :
        (Bool)'(True), data : (Bit#(3))'(3'h1)}) : ((((!
        ((((x_1)[(Bit#(3))'(3'h2)]).m_status) == ((Bit#(3))'(3'h0)))) && (!
        ((((x_1)[(Bit#(3))'(3'h2)]).m_next).valid))) &&
        ((((x_1)[(Bit#(3))'(3'h2)]).m_addr) == (x_0)) ? (Struct5 {valid :
        (Bool)'(True), data : (Bit#(3))'(3'h2)}) : ((((!
        ((((x_1)[(Bit#(3))'(3'h3)]).m_status) == ((Bit#(3))'(3'h0)))) && (!
        ((((x_1)[(Bit#(3))'(3'h3)]).m_next).valid))) &&
        ((((x_1)[(Bit#(3))'(3'h3)]).m_addr) == (x_0)) ? (Struct5 {valid :
        (Bool)'(True), data : (Bit#(3))'(3'h3)}) : ((((!
        ((((x_1)[(Bit#(3))'(3'h4)]).m_status) == ((Bit#(3))'(3'h0)))) && (!
        ((((x_1)[(Bit#(3))'(3'h4)]).m_next).valid))) &&
        ((((x_1)[(Bit#(3))'(3'h4)]).m_addr) == (x_0)) ? (Struct5 {valid :
        (Bool)'(True), data : (Bit#(3))'(3'h4)}) : ((((!
        ((((x_1)[(Bit#(3))'(3'h5)]).m_status) == ((Bit#(3))'(3'h0)))) && (!
        ((((x_1)[(Bit#(3))'(3'h5)]).m_next).valid))) &&
        ((((x_1)[(Bit#(3))'(3'h5)]).m_addr) == (x_0)) ? (Struct5 {valid :
        (Bool)'(True), data : (Bit#(3))'(3'h5)}) : (Struct5 {valid :
        (Bool)'(False), data : unpack(0)})))))))))))));
        when (! ((x_3).valid), noAction);
    endmethod

    method Action setULImm_001 (Struct1 x_0);
        let x_1 = (mshrs_001);
        let x_2 = (rqs_001);
        Struct5 x_3 = (((((x_1)[(Bit#(3))'(3'h2)]).m_status) ==
        ((Bit#(3))'(3'h0)) ? (Struct5 {valid : (Bool)'(True), data :
        (Bit#(3))'(3'h2)}) : (((((x_1)[(Bit#(3))'(3'h3)]).m_status) ==
        ((Bit#(3))'(3'h0)) ? (Struct5 {valid : (Bool)'(True), data :
        (Bit#(3))'(3'h3)}) : (((((x_1)[(Bit#(3))'(3'h4)]).m_status) ==
        ((Bit#(3))'(3'h0)) ? (Struct5 {valid : (Bool)'(True), data :
        (Bit#(3))'(3'h4)}) : (((((x_1)[(Bit#(3))'(3'h5)]).m_status) ==
        ((Bit#(3))'(3'h0)) ? (Struct5 {valid : (Bool)'(True), data :
        (Bit#(3))'(3'h5)}) : (Struct5 {valid : (Bool)'(False), data :
        unpack(0)})))))))));
        when ((x_3).valid, noAction);
        Bit#(3) x_4 = ((x_3).data);
        Bit#(64) x_5 = ((x_0).addr);
        Struct5 x_6 = (((! ((((x_1)[(Bit#(3))'(3'h0)]).m_status) ==
        ((Bit#(3))'(3'h0)))) && ((((x_1)[(Bit#(3))'(3'h0)]).m_addr) == (x_5))
        ? (Struct5 {valid : (Bool)'(True), data : (Bit#(3))'(3'h0)}) : (((!
        ((((x_1)[(Bit#(3))'(3'h1)]).m_status) == ((Bit#(3))'(3'h0)))) &&
        ((((x_1)[(Bit#(3))'(3'h1)]).m_addr) == (x_5)) ? (Struct5 {valid :
        (Bool)'(True), data : (Bit#(3))'(3'h1)}) : (((!
        ((((x_1)[(Bit#(3))'(3'h2)]).m_status) == ((Bit#(3))'(3'h0)))) &&
        ((((x_1)[(Bit#(3))'(3'h2)]).m_addr) == (x_5)) ? (Struct5 {valid :
        (Bool)'(True), data : (Bit#(3))'(3'h2)}) : (((!
        ((((x_1)[(Bit#(3))'(3'h3)]).m_status) == ((Bit#(3))'(3'h0)))) &&
        ((((x_1)[(Bit#(3))'(3'h3)]).m_addr) == (x_5)) ? (Struct5 {valid :
        (Bool)'(True), data : (Bit#(3))'(3'h3)}) : (((!
        ((((x_1)[(Bit#(3))'(3'h4)]).m_status) == ((Bit#(3))'(3'h0)))) &&
        ((((x_1)[(Bit#(3))'(3'h4)]).m_addr) == (x_5)) ? (Struct5 {valid :
        (Bool)'(True), data : (Bit#(3))'(3'h4)}) : (((!
        ((((x_1)[(Bit#(3))'(3'h5)]).m_status) == ((Bit#(3))'(3'h0)))) &&
        ((((x_1)[(Bit#(3))'(3'h5)]).m_addr) == (x_5)) ? (Struct5 {valid :
        (Bool)'(True), data : (Bit#(3))'(3'h5)}) : (Struct5 {valid :
        (Bool)'(False), data : unpack(0)})))))))))))));
        when (! ((x_6).valid), noAction);
        mshrs_001 <= update (x_1, x_4, Struct44 {m_status : (Bit#(3))'(3'h5),
        m_next : Struct5 {valid : (Bool)'(False), data : unpack(0)}, m_is_ul
        : (Bool)'(True), m_addr : (x_0).addr, m_qidx : unpack(0), m_rsb :
        (Bool)'(False), m_dl_rss_from : unpack(0), m_dl_rss_recv :
        unpack(0)});
        rqs_001 <= update (x_2, x_4, x_0);
    endmethod

    method Action transferUpDown_001 (Struct55 x_0);
        Bit#(3) x_1 = ((x_0).r_id);
        let x_2 = (mshrs_001);
        Struct44 x_3 = ((x_2)[x_1]);
        Struct44 x_4 = (Struct44 {m_status : (Bit#(3))'(3'h5), m_next :
        (x_3).m_next, m_is_ul : (Bool)'(False), m_addr : (x_3).m_addr, m_qidx
        : (x_3).m_qidx, m_rsb : (x_3).m_rsb, m_dl_rss_from :
        (x_0).r_dl_rss_from, m_dl_rss_recv : unpack(0)});
        mshrs_001 <= update (x_2, x_1, x_4);
    endmethod

    method Action addRs_001 (Struct7 x_0);
        let x_1 = (mshrs_001);
        Bit#(64) x_2 = (((x_0).r_msg).addr);
        Struct5 x_3 = (((((((x_1)[(Bit#(3))'(3'h0)]).m_status) ==
        ((Bit#(3))'(3'h5))) && (! (((x_1)[(Bit#(3))'(3'h0)]).m_is_ul))) &&
        ((((x_1)[(Bit#(3))'(3'h0)]).m_addr) == (x_2)) ? (Struct5 {valid :
        (Bool)'(True), data : (Bit#(3))'(3'h0)}) :
        (((((((x_1)[(Bit#(3))'(3'h1)]).m_status) == ((Bit#(3))'(3'h5))) && (!
        (((x_1)[(Bit#(3))'(3'h1)]).m_is_ul))) &&
        ((((x_1)[(Bit#(3))'(3'h1)]).m_addr) == (x_2)) ? (Struct5 {valid :
        (Bool)'(True), data : (Bit#(3))'(3'h1)}) :
        (((((((x_1)[(Bit#(3))'(3'h2)]).m_status) == ((Bit#(3))'(3'h5))) && (!
        (((x_1)[(Bit#(3))'(3'h2)]).m_is_ul))) &&
        ((((x_1)[(Bit#(3))'(3'h2)]).m_addr) == (x_2)) ? (Struct5 {valid :
        (Bool)'(True), data : (Bit#(3))'(3'h2)}) :
        (((((((x_1)[(Bit#(3))'(3'h3)]).m_status) == ((Bit#(3))'(3'h5))) && (!
        (((x_1)[(Bit#(3))'(3'h3)]).m_is_ul))) &&
        ((((x_1)[(Bit#(3))'(3'h3)]).m_addr) == (x_2)) ? (Struct5 {valid :
        (Bool)'(True), data : (Bit#(3))'(3'h3)}) :
        (((((((x_1)[(Bit#(3))'(3'h4)]).m_status) == ((Bit#(3))'(3'h5))) && (!
        (((x_1)[(Bit#(3))'(3'h4)]).m_is_ul))) &&
        ((((x_1)[(Bit#(3))'(3'h4)]).m_addr) == (x_2)) ? (Struct5 {valid :
        (Bool)'(True), data : (Bit#(3))'(3'h4)}) :
        (((((((x_1)[(Bit#(3))'(3'h5)]).m_status) == ((Bit#(3))'(3'h5))) && (!
        (((x_1)[(Bit#(3))'(3'h5)]).m_is_ul))) &&
        ((((x_1)[(Bit#(3))'(3'h5)]).m_addr) == (x_2)) ? (Struct5 {valid :
        (Bool)'(True), data : (Bit#(3))'(3'h5)}) : (Struct5 {valid :
        (Bool)'(False), data : unpack(0)})))))))))))));
        when ((x_3).valid, noAction);
        Bit#(3) x_4 = ((x_3).data);
        Struct44 x_5 = ((x_1)[x_4]);
        mshrs_001 <= update (x_1, x_4, Struct44 {m_status : (x_5).m_status,
        m_next : (x_5).m_next, m_is_ul : (x_5).m_is_ul, m_addr :
        (x_5).m_addr, m_qidx : (x_5).m_qidx, m_rsb : (x_5).m_rsb,
        m_dl_rss_from : (x_5).m_dl_rss_from, m_dl_rss_recv :
        ((x_5).m_dl_rss_recv) | (((Bit#(2))'(2'h1)) << ((x_0).r_midx))});
        let x_6 = (rss_001);
        Struct37 x_7 = ((x_6)[x_4]);
        rss_001 <= update (x_6, x_4, Struct37 {m_dl_rss : update
        ((x_7).m_dl_rss, (x_0).r_midx, (x_0).r_msg)});
    endmethod

    method ActionValue#(Bit#(3)) getULReady_001 (Bit#(64) x_0);
        let x_1 = (mshrs_001);
        Bool x_2 = (((((((x_1)[(Bit#(3))'(3'h0)]).m_status) ==
        ((Bit#(3))'(3'h4))) || ((((x_1)[(Bit#(3))'(3'h0)]).m_status) ==
        ((Bit#(3))'(3'h6)))) && ((! ((((x_1)[(Bit#(3))'(3'h0)]).m_addr) ==
        (x_0))) && (((((x_1)[(Bit#(3))'(3'h0)]).m_addr)[12:5]) ==
        ((x_0)[12:5]))) ? ((Bool)'(True)) :
        (((((((x_1)[(Bit#(3))'(3'h1)]).m_status) == ((Bit#(3))'(3'h4))) ||
        ((((x_1)[(Bit#(3))'(3'h1)]).m_status) == ((Bit#(3))'(3'h6)))) && ((!
        ((((x_1)[(Bit#(3))'(3'h1)]).m_addr) == (x_0))) &&
        (((((x_1)[(Bit#(3))'(3'h1)]).m_addr)[12:5]) == ((x_0)[12:5]))) ?
        ((Bool)'(True)) : (((((((x_1)[(Bit#(3))'(3'h2)]).m_status) ==
        ((Bit#(3))'(3'h4))) || ((((x_1)[(Bit#(3))'(3'h2)]).m_status) ==
        ((Bit#(3))'(3'h6)))) && ((! ((((x_1)[(Bit#(3))'(3'h2)]).m_addr) ==
        (x_0))) && (((((x_1)[(Bit#(3))'(3'h2)]).m_addr)[12:5]) ==
        ((x_0)[12:5]))) ? ((Bool)'(True)) :
        (((((((x_1)[(Bit#(3))'(3'h3)]).m_status) == ((Bit#(3))'(3'h4))) ||
        ((((x_1)[(Bit#(3))'(3'h3)]).m_status) == ((Bit#(3))'(3'h6)))) && ((!
        ((((x_1)[(Bit#(3))'(3'h3)]).m_addr) == (x_0))) &&
        (((((x_1)[(Bit#(3))'(3'h3)]).m_addr)[12:5]) == ((x_0)[12:5]))) ?
        ((Bool)'(True)) : (((((((x_1)[(Bit#(3))'(3'h4)]).m_status) ==
        ((Bit#(3))'(3'h4))) || ((((x_1)[(Bit#(3))'(3'h4)]).m_status) ==
        ((Bit#(3))'(3'h6)))) && ((! ((((x_1)[(Bit#(3))'(3'h4)]).m_addr) ==
        (x_0))) && (((((x_1)[(Bit#(3))'(3'h4)]).m_addr)[12:5]) ==
        ((x_0)[12:5]))) ? ((Bool)'(True)) :
        (((((((x_1)[(Bit#(3))'(3'h5)]).m_status) == ((Bit#(3))'(3'h4))) ||
        ((((x_1)[(Bit#(3))'(3'h5)]).m_status) == ((Bit#(3))'(3'h6)))) && ((!
        ((((x_1)[(Bit#(3))'(3'h5)]).m_addr) == (x_0))) &&
        (((((x_1)[(Bit#(3))'(3'h5)]).m_addr)[12:5]) == ((x_0)[12:5]))) ?
        ((Bool)'(True)) : ((Bool)'(False))))))))))))));
        when (! (x_2), noAction);
        Struct5 x_3 = ((((! ((((x_1)[(Bit#(3))'(3'h0)]).m_status) <
        ((Bit#(3))'(3'h4)))) && (! (((x_1)[(Bit#(3))'(3'h0)]).m_is_ul))) &&
        ((((x_1)[(Bit#(3))'(3'h0)]).m_addr) == (x_0)) ? (Struct5 {valid :
        (Bool)'(True), data : (Bit#(3))'(3'h0)}) : ((((!
        ((((x_1)[(Bit#(3))'(3'h1)]).m_status) < ((Bit#(3))'(3'h4)))) && (!
        (((x_1)[(Bit#(3))'(3'h1)]).m_is_ul))) &&
        ((((x_1)[(Bit#(3))'(3'h1)]).m_addr) == (x_0)) ? (Struct5 {valid :
        (Bool)'(True), data : (Bit#(3))'(3'h1)}) : ((((!
        ((((x_1)[(Bit#(3))'(3'h2)]).m_status) < ((Bit#(3))'(3'h4)))) && (!
        (((x_1)[(Bit#(3))'(3'h2)]).m_is_ul))) &&
        ((((x_1)[(Bit#(3))'(3'h2)]).m_addr) == (x_0)) ? (Struct5 {valid :
        (Bool)'(True), data : (Bit#(3))'(3'h2)}) : ((((!
        ((((x_1)[(Bit#(3))'(3'h3)]).m_status) < ((Bit#(3))'(3'h4)))) && (!
        (((x_1)[(Bit#(3))'(3'h3)]).m_is_ul))) &&
        ((((x_1)[(Bit#(3))'(3'h3)]).m_addr) == (x_0)) ? (Struct5 {valid :
        (Bool)'(True), data : (Bit#(3))'(3'h3)}) : ((((!
        ((((x_1)[(Bit#(3))'(3'h4)]).m_status) < ((Bit#(3))'(3'h4)))) && (!
        (((x_1)[(Bit#(3))'(3'h4)]).m_is_ul))) &&
        ((((x_1)[(Bit#(3))'(3'h4)]).m_addr) == (x_0)) ? (Struct5 {valid :
        (Bool)'(True), data : (Bit#(3))'(3'h4)}) : ((((!
        ((((x_1)[(Bit#(3))'(3'h5)]).m_status) < ((Bit#(3))'(3'h4)))) && (!
        (((x_1)[(Bit#(3))'(3'h5)]).m_is_ul))) &&
        ((((x_1)[(Bit#(3))'(3'h5)]).m_addr) == (x_0)) ? (Struct5 {valid :
        (Bool)'(True), data : (Bit#(3))'(3'h5)}) : (Struct5 {valid :
        (Bool)'(False), data : unpack(0)})))))))))))));
        when (! ((x_3).valid), noAction);
        Struct5 x_4 = (((((((x_1)[(Bit#(3))'(3'h2)]).m_status) ==
        ((Bit#(3))'(3'h5))) && (((x_1)[(Bit#(3))'(3'h2)]).m_is_ul)) &&
        ((((x_1)[(Bit#(3))'(3'h2)]).m_addr) == (x_0)) ? (Struct5 {valid :
        (Bool)'(True), data : (Bit#(3))'(3'h2)}) :
        (((((((x_1)[(Bit#(3))'(3'h3)]).m_status) == ((Bit#(3))'(3'h5))) &&
        (((x_1)[(Bit#(3))'(3'h3)]).m_is_ul)) &&
        ((((x_1)[(Bit#(3))'(3'h3)]).m_addr) == (x_0)) ? (Struct5 {valid :
        (Bool)'(True), data : (Bit#(3))'(3'h3)}) :
        (((((((x_1)[(Bit#(3))'(3'h4)]).m_status) == ((Bit#(3))'(3'h5))) &&
        (((x_1)[(Bit#(3))'(3'h4)]).m_is_ul)) &&
        ((((x_1)[(Bit#(3))'(3'h4)]).m_addr) == (x_0)) ? (Struct5 {valid :
        (Bool)'(True), data : (Bit#(3))'(3'h4)}) :
        (((((((x_1)[(Bit#(3))'(3'h5)]).m_status) == ((Bit#(3))'(3'h5))) &&
        (((x_1)[(Bit#(3))'(3'h5)]).m_is_ul)) &&
        ((((x_1)[(Bit#(3))'(3'h5)]).m_addr) == (x_0)) ? (Struct5 {valid :
        (Bool)'(True), data : (Bit#(3))'(3'h5)}) : (Struct5 {valid :
        (Bool)'(False), data : unpack(0)})))))))));
        when ((x_4).valid, noAction);
        Bit#(3) x_5 = ((x_4).data);
        return x_5;
    endmethod

    method ActionValue#(Struct56) getDLReady_001 ();
        let x_1 = (mshrs_001);
        Struct5 x_2 = (((((((x_1)[(Bit#(3))'(3'h0)]).m_status) ==
        ((Bit#(3))'(3'h5))) && (! (((x_1)[(Bit#(3))'(3'h0)]).m_is_ul))) &&
        ((((x_1)[(Bit#(3))'(3'h0)]).m_dl_rss_from) ==
        (((x_1)[(Bit#(3))'(3'h0)]).m_dl_rss_recv)) ? (Struct5 {valid :
        (Bool)'(True), data : (Bit#(3))'(3'h0)}) :
        (((((((x_1)[(Bit#(3))'(3'h1)]).m_status) == ((Bit#(3))'(3'h5))) && (!
        (((x_1)[(Bit#(3))'(3'h1)]).m_is_ul))) &&
        ((((x_1)[(Bit#(3))'(3'h1)]).m_dl_rss_from) ==
        (((x_1)[(Bit#(3))'(3'h1)]).m_dl_rss_recv)) ? (Struct5 {valid :
        (Bool)'(True), data : (Bit#(3))'(3'h1)}) :
        (((((((x_1)[(Bit#(3))'(3'h2)]).m_status) == ((Bit#(3))'(3'h5))) && (!
        (((x_1)[(Bit#(3))'(3'h2)]).m_is_ul))) &&
        ((((x_1)[(Bit#(3))'(3'h2)]).m_dl_rss_from) ==
        (((x_1)[(Bit#(3))'(3'h2)]).m_dl_rss_recv)) ? (Struct5 {valid :
        (Bool)'(True), data : (Bit#(3))'(3'h2)}) :
        (((((((x_1)[(Bit#(3))'(3'h3)]).m_status) == ((Bit#(3))'(3'h5))) && (!
        (((x_1)[(Bit#(3))'(3'h3)]).m_is_ul))) &&
        ((((x_1)[(Bit#(3))'(3'h3)]).m_dl_rss_from) ==
        (((x_1)[(Bit#(3))'(3'h3)]).m_dl_rss_recv)) ? (Struct5 {valid :
        (Bool)'(True), data : (Bit#(3))'(3'h3)}) :
        (((((((x_1)[(Bit#(3))'(3'h4)]).m_status) == ((Bit#(3))'(3'h5))) && (!
        (((x_1)[(Bit#(3))'(3'h4)]).m_is_ul))) &&
        ((((x_1)[(Bit#(3))'(3'h4)]).m_dl_rss_from) ==
        (((x_1)[(Bit#(3))'(3'h4)]).m_dl_rss_recv)) ? (Struct5 {valid :
        (Bool)'(True), data : (Bit#(3))'(3'h4)}) :
        (((((((x_1)[(Bit#(3))'(3'h5)]).m_status) == ((Bit#(3))'(3'h5))) && (!
        (((x_1)[(Bit#(3))'(3'h5)]).m_is_ul))) &&
        ((((x_1)[(Bit#(3))'(3'h5)]).m_dl_rss_from) ==
        (((x_1)[(Bit#(3))'(3'h5)]).m_dl_rss_recv)) ? (Struct5 {valid :
        (Bool)'(True), data : (Bit#(3))'(3'h5)}) : (Struct5 {valid :
        (Bool)'(False), data : unpack(0)})))))))))))));
        when ((x_2).valid, noAction);
        Bit#(3) x_3 = ((x_2).data);
        Struct44 x_4 = ((x_1)[x_3]);
        Bit#(64) x_5 = ((x_4).m_addr);
        Bool x_6 = (((((((x_1)[(Bit#(3))'(3'h0)]).m_status) ==
        ((Bit#(3))'(3'h4))) || ((((x_1)[(Bit#(3))'(3'h0)]).m_status) ==
        ((Bit#(3))'(3'h6)))) && ((! ((((x_1)[(Bit#(3))'(3'h0)]).m_addr) ==
        (x_5))) && (((((x_1)[(Bit#(3))'(3'h0)]).m_addr)[12:5]) ==
        ((x_5)[12:5]))) ? ((Bool)'(True)) :
        (((((((x_1)[(Bit#(3))'(3'h1)]).m_status) == ((Bit#(3))'(3'h4))) ||
        ((((x_1)[(Bit#(3))'(3'h1)]).m_status) == ((Bit#(3))'(3'h6)))) && ((!
        ((((x_1)[(Bit#(3))'(3'h1)]).m_addr) == (x_5))) &&
        (((((x_1)[(Bit#(3))'(3'h1)]).m_addr)[12:5]) == ((x_5)[12:5]))) ?
        ((Bool)'(True)) : (((((((x_1)[(Bit#(3))'(3'h2)]).m_status) ==
        ((Bit#(3))'(3'h4))) || ((((x_1)[(Bit#(3))'(3'h2)]).m_status) ==
        ((Bit#(3))'(3'h6)))) && ((! ((((x_1)[(Bit#(3))'(3'h2)]).m_addr) ==
        (x_5))) && (((((x_1)[(Bit#(3))'(3'h2)]).m_addr)[12:5]) ==
        ((x_5)[12:5]))) ? ((Bool)'(True)) :
        (((((((x_1)[(Bit#(3))'(3'h3)]).m_status) == ((Bit#(3))'(3'h4))) ||
        ((((x_1)[(Bit#(3))'(3'h3)]).m_status) == ((Bit#(3))'(3'h6)))) && ((!
        ((((x_1)[(Bit#(3))'(3'h3)]).m_addr) == (x_5))) &&
        (((((x_1)[(Bit#(3))'(3'h3)]).m_addr)[12:5]) == ((x_5)[12:5]))) ?
        ((Bool)'(True)) : (((((((x_1)[(Bit#(3))'(3'h4)]).m_status) ==
        ((Bit#(3))'(3'h4))) || ((((x_1)[(Bit#(3))'(3'h4)]).m_status) ==
        ((Bit#(3))'(3'h6)))) && ((! ((((x_1)[(Bit#(3))'(3'h4)]).m_addr) ==
        (x_5))) && (((((x_1)[(Bit#(3))'(3'h4)]).m_addr)[12:5]) ==
        ((x_5)[12:5]))) ? ((Bool)'(True)) :
        (((((((x_1)[(Bit#(3))'(3'h5)]).m_status) == ((Bit#(3))'(3'h4))) ||
        ((((x_1)[(Bit#(3))'(3'h5)]).m_status) == ((Bit#(3))'(3'h6)))) && ((!
        ((((x_1)[(Bit#(3))'(3'h5)]).m_addr) == (x_5))) &&
        (((((x_1)[(Bit#(3))'(3'h5)]).m_addr)[12:5]) == ((x_5)[12:5]))) ?
        ((Bool)'(True)) : ((Bool)'(False))))))))))))));
        when (! (x_6), noAction);
        Struct56 x_7 = (Struct56 {r_id : x_3, r_addr : x_5});
        return x_7;
    endmethod

    method Action startRelease_001 (Bit#(3) x_0);
        let x_1 = (mshrs_001);
        Struct44 x_2 = ((x_1)[x_0]);
        Struct44 x_3 = (Struct44 {m_status : (Bit#(3))'(3'h6), m_next :
        (x_2).m_next, m_is_ul : (x_2).m_is_ul, m_addr : (x_2).m_addr, m_qidx
        : (x_2).m_qidx, m_rsb : (x_2).m_rsb, m_dl_rss_from :
        (x_2).m_dl_rss_from, m_dl_rss_recv : (x_2).m_dl_rss_recv});
        mshrs_001 <= update (x_1, x_0, x_3);
    endmethod

    method Action releaseMSHR_001 (Bit#(3) x_0);
        let x_1 = (mshrs_001);
        Struct44 x_2 = ((x_1)[x_0]);
        Vector#(6, Struct44) x_3 = (update (x_1, x_0,
        unpack(0)));
        let x_7 = ?;
        if (((x_2).m_next).valid) begin
            Bit#(3) x_4 = (((x_2).m_next).data);
            Struct44 x_5 = ((x_1)[x_4]);
            Vector#(6, Struct44) x_6 = (update (x_3, x_4, Struct44 {m_status
            : (Bit#(3))'(3'h2), m_next : (x_5).m_next, m_is_ul :
            (x_5).m_is_ul, m_addr : (x_5).m_addr, m_qidx : (x_5).m_qidx,
            m_rsb : (x_5).m_rsb, m_dl_rss_from : (x_5).m_dl_rss_from,
            m_dl_rss_recv : (x_5).m_dl_rss_recv}));
            x_7 = x_6;
        end else begin
            x_7 = x_3;
        end
        mshrs_001 <= x_7;
    endmethod
endmodule

interface Module59;

endinterface

module mkModule59#(function ActionValue#(Struct1) deq_fifo0010(),
    function Action enq_fifoCRqInput_00(Struct2 _),
    function ActionValue#(Struct1) deq_fifo0000())
    (Module59);
    Reg#(Bit#(1)) rr_cRq2_00 <- mkReg(unpack(0));

    rule inc_rr_cRq2_00;
        $display ("Rule fired: inc_rr_cRq2_00 at %t", $time);
        let x_0 = (rr_cRq2_00);
        rr_cRq2_00 <= (x_0) + ((Bit#(1))'(1'h1));
    endrule

    rule accept0_cRq2_00;
        $display ("Rule fired: accept0_cRq2_00 at %t", $time);
        let x_0 = (rr_cRq2_00);
        when ((x_0) == ((Bit#(1))'(1'h0)), noAction);
        let x_1 <- deq_fifo0000();
        Struct2 x_2 = (Struct2 {in_msg : x_1, in_msg_from :
        {((Bit#(2))'(2'h0)),((Bit#(1))'(1'h0))}});
        let x_3 <- enq_fifoCRqInput_00(x_2);
    endrule

    rule accept1_cRq2_00;
        $display ("Rule fired: accept1_cRq2_00 at %t", $time);
        let x_0 = (rr_cRq2_00);
        when ((x_0) == ((Bit#(1))'(1'h1)), noAction);
        let x_1 <- deq_fifo0010();
        Struct2 x_2 = (Struct2 {in_msg : x_1, in_msg_from :
        {((Bit#(2))'(2'h0)),((Bit#(1))'(1'h1))}});
        let x_3 <- enq_fifoCRqInput_00(x_2);
    endrule

    // No methods in this module
endmodule

interface Module60;

endinterface

module mkModule60#(function ActionValue#(Struct1) deq_fifo0011(),
    function Action enq_fifoCRsInput_00(Struct2 _),
    function ActionValue#(Struct1) deq_fifo0001())
    (Module60);
    Reg#(Bit#(1)) rr_cRs2_00 <- mkReg(unpack(0));

    rule inc_rr_cRs2_00;
        $display ("Rule fired: inc_rr_cRs2_00 at %t", $time);
        let x_0 = (rr_cRs2_00);
        rr_cRs2_00 <= (x_0) + ((Bit#(1))'(1'h1));
    endrule

    rule accept0_cRs2_00;
        $display ("Rule fired: accept0_cRs2_00 at %t", $time);
        let x_0 = (rr_cRs2_00);
        when ((x_0) == ((Bit#(1))'(1'h0)), noAction);
        let x_1 <- deq_fifo0001();
        Struct2 x_2 = (Struct2 {in_msg : x_1, in_msg_from :
        {((Bit#(2))'(2'h1)),((Bit#(1))'(1'h0))}});
        let x_3 <- enq_fifoCRsInput_00(x_2);
    endrule

    rule accept1_cRs2_00;
        $display ("Rule fired: accept1_cRs2_00 at %t", $time);
        let x_0 = (rr_cRs2_00);
        when ((x_0) == ((Bit#(1))'(1'h1)), noAction);
        let x_1 <- deq_fifo0011();
        Struct2 x_2 = (Struct2 {in_msg : x_1, in_msg_from :
        {((Bit#(2))'(2'h1)),((Bit#(1))'(1'h1))}});
        let x_3 <- enq_fifoCRsInput_00(x_2);
    endrule

    // No methods in this module
endmodule

interface Module61;

endinterface

module mkModule61#(function Action enq_fifoPInput_00(Struct2 _),
    function ActionValue#(Struct1) deq_fifo002())
    (Module61);

    rule parent_convert_00;
        $display ("Rule fired: parent_convert_00 at %t", $time);
        let x_0 <- deq_fifo002();
        Struct2 x_1 = (Struct2 {in_msg : x_0, in_msg_from :
        {((Bit#(2))'(2'h2)),((Bit#(1))'(1'h0))}});
        let x_2 <- enq_fifoPInput_00(x_1);
    endrule

    // No methods in this module
endmodule

interface Module62;
    method Action makeEnq_parentChildren00 (Struct20 x_0);
    method Action broadcast_parentChildren00 (Struct23 x_0);
endinterface

module mkModule62#(function Action enq_fifo0002(Struct1 _),
    function Action enq_fifo0012(Struct1 _),
    function Action enq_fifo001(Struct1 _),
    function Action enq_fifo000(Struct1 _))
    (Module62);

    // No rules in this module

    method Action makeEnq_parentChildren00 (Struct20 x_0);
        if (((x_0).enq_type) == ((Bit#(2))'(2'h0))) begin
            let x_1 <- enq_fifo000((x_0).enq_msg);
        end else
            begin
            if (((x_0).enq_type) == ((Bit#(2))'(2'h1))) begin
                let x_2 <- enq_fifo001((x_0).enq_msg);
            end else begin
                Bit#(1) x_3 = ((x_0).enq_ch_idx);
                Struct1 x_4 =
                ((x_0).enq_msg);
                if ((x_3) == ((Bit#(1))'(1'h1))) begin
                    let x_5 <- enq_fifo0012(x_4);
                end else
                    begin
                    if ((x_3) == ((Bit#(1))'(1'h0))) begin
                        let x_6 <- enq_fifo0002(x_4);
                    end else begin

                    end
                end
            end
        end
    endmethod

    method Action broadcast_parentChildren00 (Struct23 x_0);
        Bit#(2) x_1 = ((x_0).cs_inds);
        Struct1 x_2 =
        ((x_0).cs_msg);
        if (((x_1) | (((Bit#(2))'(2'h1)) << ((Bit#(1))'(1'h1)))) == (x_1))
            begin
            let x_3 <- enq_fifo0012(x_2);
        end else begin

        end
        if (((x_1) | (((Bit#(2))'(2'h1)) << ((Bit#(1))'(1'h0)))) == (x_1))
            begin
            let x_5 <- enq_fifo0002(x_2);
        end else begin

        end
    endmethod
endmodule

interface Module63;
    method Action repGetRq__00 (Bit#(9) x_0);
    method ActionValue#(Vector#(8, Bit#(8))) repGetRs__00 ();
    method Action repAccess__00 (Struct32 x_0);
endinterface

module mkModule63#(function Action wrReq_repRam__00(Struct36 _),
    function ActionValue#(Vector#(8, Bit#(8))) rdResp_repRam__00(),
    function Action rdReq_repRam__00(Bit#(9) _))
    (Module63);

    // No rules in this module

    method Action repGetRq__00 (Bit#(9) x_0);
        let x_1 <- rdReq_repRam__00(x_0);
    endmethod

    method ActionValue#(Vector#(8, Bit#(8))) repGetRs__00 ();
        let x_1 <- rdResp_repRam__00();
        return x_1;
    endmethod

    method Action repAccess__00 (Struct32 x_0);
        Vector#(8, Bit#(8)) x_1 = ((x_0).acc_reps);
        Bit#(8) x_2 = (((x_1)[(Bit#(3))'(3'h7)]) +
        (((((x_1)[(Bit#(3))'(3'h7)]) == ((Bit#(8))'(8'h0))) ||
        (((x_1)[(Bit#(3))'(3'h7)]) == ((Bit#(8))'(8'hff))) ?
        ((Bit#(8))'(8'h0)) : ((Bit#(8))'(8'h1)))));
        Vector#(8, Bit#(8)) x_3 = (update (x_1, (Bit#(3))'(3'h7),
        x_2));
        Bit#(8) x_4 = (((x_3)[(Bit#(3))'(3'h6)]) +
        (((((x_3)[(Bit#(3))'(3'h6)]) == ((Bit#(8))'(8'h0))) ||
        (((x_3)[(Bit#(3))'(3'h6)]) == ((Bit#(8))'(8'hff))) ?
        ((Bit#(8))'(8'h0)) : ((Bit#(8))'(8'h1)))));
        Vector#(8, Bit#(8)) x_5 = (update (x_3, (Bit#(3))'(3'h6),
        x_4));
        Bit#(8) x_6 = (((x_5)[(Bit#(3))'(3'h5)]) +
        (((((x_5)[(Bit#(3))'(3'h5)]) == ((Bit#(8))'(8'h0))) ||
        (((x_5)[(Bit#(3))'(3'h5)]) == ((Bit#(8))'(8'hff))) ?
        ((Bit#(8))'(8'h0)) : ((Bit#(8))'(8'h1)))));
        Vector#(8, Bit#(8)) x_7 = (update (x_5, (Bit#(3))'(3'h5),
        x_6));
        Bit#(8) x_8 = (((x_7)[(Bit#(3))'(3'h4)]) +
        (((((x_7)[(Bit#(3))'(3'h4)]) == ((Bit#(8))'(8'h0))) ||
        (((x_7)[(Bit#(3))'(3'h4)]) == ((Bit#(8))'(8'hff))) ?
        ((Bit#(8))'(8'h0)) : ((Bit#(8))'(8'h1)))));
        Vector#(8, Bit#(8)) x_9 = (update (x_7, (Bit#(3))'(3'h4),
        x_8));
        Bit#(8) x_10 = (((x_9)[(Bit#(3))'(3'h3)]) +
        (((((x_9)[(Bit#(3))'(3'h3)]) == ((Bit#(8))'(8'h0))) ||
        (((x_9)[(Bit#(3))'(3'h3)]) == ((Bit#(8))'(8'hff))) ?
        ((Bit#(8))'(8'h0)) : ((Bit#(8))'(8'h1)))));
        Vector#(8, Bit#(8)) x_11 = (update (x_9, (Bit#(3))'(3'h3),
        x_10));
        Bit#(8) x_12 = (((x_11)[(Bit#(3))'(3'h2)]) +
        (((((x_11)[(Bit#(3))'(3'h2)]) == ((Bit#(8))'(8'h0))) ||
        (((x_11)[(Bit#(3))'(3'h2)]) == ((Bit#(8))'(8'hff))) ?
        ((Bit#(8))'(8'h0)) : ((Bit#(8))'(8'h1)))));
        Vector#(8, Bit#(8)) x_13 = (update (x_11, (Bit#(3))'(3'h2),
        x_12));
        Bit#(8) x_14 = (((x_13)[(Bit#(3))'(3'h1)]) +
        (((((x_13)[(Bit#(3))'(3'h1)]) == ((Bit#(8))'(8'h0))) ||
        (((x_13)[(Bit#(3))'(3'h1)]) == ((Bit#(8))'(8'hff))) ?
        ((Bit#(8))'(8'h0)) : ((Bit#(8))'(8'h1)))));
        Vector#(8, Bit#(8)) x_15 = (update (x_13, (Bit#(3))'(3'h1),
        x_14));
        Bit#(8) x_16 = (((x_15)[(Bit#(3))'(3'h0)]) +
        (((((x_15)[(Bit#(3))'(3'h0)]) == ((Bit#(8))'(8'h0))) ||
        (((x_15)[(Bit#(3))'(3'h0)]) == ((Bit#(8))'(8'hff))) ?
        ((Bit#(8))'(8'h0)) : ((Bit#(8))'(8'h1)))));
        Vector#(8, Bit#(8)) x_17 = (update (x_15, (Bit#(3))'(3'h0),
        x_16));
        let x_20 = ?;
        if (((x_0).acc_type) == ((Bit#(1))'(1'h0))) begin
            Vector#(8, Bit#(8)) x_18 = (update (x_17, (x_0).acc_way,
            (Bit#(8))'(8'h1)));
            x_20 = x_18;
        end else begin
            Vector#(8, Bit#(8)) x_19 = (update (x_17, (x_0).acc_way,
            (Bit#(8))'(8'h0)));
            x_20 = x_19;
        end
        Struct36 x_21 = (Struct36 {addr : (x_0).acc_index, datain :
        x_20});
        let x_22 <- wrReq_repRam__00(x_21);
    endmethod
endmodule

interface Module64;

endinterface

module mkModule64#(function Action enq_fifoCRqInput_000(Struct2 _),
    function ActionValue#(Struct1) deq_fifo00000())
    (Module64);

    rule child_convert_000;
        $display ("Rule fired: child_convert_000 at %t", $time);
        let x_0 <- deq_fifo00000();
        Struct2 x_1 = (Struct2 {in_msg : x_0, in_msg_from :
        {((Bit#(2))'(2'h0)),((Bit#(1))'(1'h0))}});
        let x_2 <- enq_fifoCRqInput_000(x_1);
    endrule

    // No methods in this module
endmodule

interface Module65;

endinterface

module mkModule65#(function Action enq_fifoPInput_000(Struct2 _),
    function ActionValue#(Struct1) deq_fifo0002())
    (Module65);

    rule parent_convert_000;
        $display ("Rule fired: parent_convert_000 at %t", $time);
        let x_0 <- deq_fifo0002();
        Struct2 x_1 = (Struct2 {in_msg : x_0, in_msg_from :
        {((Bit#(2))'(2'h2)),((Bit#(1))'(1'h0))}});
        let x_2 <- enq_fifoPInput_000(x_1);
    endrule

    // No methods in this module
endmodule

interface Module66;
    method Action makeEnq_parentChildren000 (Struct20 x_0);
endinterface

module mkModule66#(function Action enq_fifo00002(Struct1 _),
    function Action enq_fifo0001(Struct1 _),
    function Action enq_fifo0000(Struct1 _))
    (Module66);

    // No rules in this module

    method Action makeEnq_parentChildren000 (Struct20 x_0);
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

interface Module67;
    method Action repGetRq__000 (Bit#(8) x_0);
    method ActionValue#(Vector#(4, Bit#(8))) repGetRs__000 ();
    method Action repAccess__000 (Struct51 x_0);
endinterface

module mkModule67#(function Action wrReq_repRam__000(Struct53 _),
    function ActionValue#(Vector#(4, Bit#(8))) rdResp_repRam__000(),
    function Action rdReq_repRam__000(Bit#(8) _))
    (Module67);

    // No rules in this module

    method Action repGetRq__000 (Bit#(8) x_0);
        let x_1 <- rdReq_repRam__000(x_0);
    endmethod

    method ActionValue#(Vector#(4, Bit#(8))) repGetRs__000 ();
        let x_1 <- rdResp_repRam__000();
        return x_1;
    endmethod

    method Action repAccess__000 (Struct51 x_0);
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
        Struct53 x_13 = (Struct53 {addr : (x_0).acc_index, datain :
        x_12});
        let x_14 <- wrReq_repRam__000(x_13);
    endmethod
endmodule

interface Module68;

endinterface

module mkModule68#(function Action enq_fifoCRqInput_001(Struct2 _),
    function ActionValue#(Struct1) deq_fifo00100())
    (Module68);

    rule child_convert_001;
        $display ("Rule fired: child_convert_001 at %t", $time);
        let x_0 <- deq_fifo00100();
        Struct2 x_1 = (Struct2 {in_msg : x_0, in_msg_from :
        {((Bit#(2))'(2'h0)),((Bit#(1))'(1'h0))}});
        let x_2 <- enq_fifoCRqInput_001(x_1);
    endrule

    // No methods in this module
endmodule

interface Module69;

endinterface

module mkModule69#(function Action enq_fifoPInput_001(Struct2 _),
    function ActionValue#(Struct1) deq_fifo0012())
    (Module69);

    rule parent_convert_001;
        $display ("Rule fired: parent_convert_001 at %t", $time);
        let x_0 <- deq_fifo0012();
        Struct2 x_1 = (Struct2 {in_msg : x_0, in_msg_from :
        {((Bit#(2))'(2'h2)),((Bit#(1))'(1'h1))}});
        let x_2 <- enq_fifoPInput_001(x_1);
    endrule

    // No methods in this module
endmodule

interface Module70;
    method Action makeEnq_parentChildren001 (Struct20 x_0);
endinterface

module mkModule70#(function Action enq_fifo00102(Struct1 _),
    function Action enq_fifo0011(Struct1 _),
    function Action enq_fifo0010(Struct1 _))
    (Module70);

    // No rules in this module

    method Action makeEnq_parentChildren001 (Struct20 x_0);
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

interface Module71;
    method Action repGetRq__001 (Bit#(8) x_0);
    method ActionValue#(Vector#(4, Bit#(8))) repGetRs__001 ();
    method Action repAccess__001 (Struct51 x_0);
endinterface

module mkModule71#(function Action wrReq_repRam__001(Struct53 _),
    function ActionValue#(Vector#(4, Bit#(8))) rdResp_repRam__001(),
    function Action rdReq_repRam__001(Bit#(8) _))
    (Module71);

    // No rules in this module

    method Action repGetRq__001 (Bit#(8) x_0);
        let x_1 <- rdReq_repRam__001(x_0);
    endmethod

    method ActionValue#(Vector#(4, Bit#(8))) repGetRs__001 ();
        let x_1 <- rdResp_repRam__001();
        return x_1;
    endmethod

    method Action repAccess__001 (Struct51 x_0);
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
        Struct53 x_13 = (Struct53 {addr : (x_0).acc_index, datain :
        x_12});
        let x_14 <- wrReq_repRam__001(x_13);
    endmethod
endmodule

interface Module72;
    method Action cache__00__infoRq (Bit#(64) x_0);
    method ActionValue#(Struct9) cache__00__infoRsValueRq (Bit#(64) x_0);
    method ActionValue#(Vector#(4, Bit#(64))) cache__00__valueRsLineRq
    (Struct18 x_0);
endinterface

module mkModule72#(function Action wrReq_dataRam__00(Struct34 _),
    function Action wrReq_edirRam__00__3(Struct33 _),
    function Action wrReq_edirRam__00__2(Struct33 _),
    function Action wrReq_edirRam__00__1(Struct33 _),
    function Action wrReq_edirRam__00__0(Struct33 _),
    function Action repAccess__00(Struct32 _),
    function Action victims__00__registerVictim(Struct14 _),
    function Action wrReq_infoRam__00__7(Struct31 _),
    function Action wrReq_infoRam__00__6(Struct31 _),
    function Action wrReq_infoRam__00__5(Struct31 _),
    function Action wrReq_infoRam__00__4(Struct31 _),
    function Action wrReq_infoRam__00__3(Struct31 _),
    function Action wrReq_infoRam__00__2(Struct31 _),
    function Action wrReq_infoRam__00__1(Struct31 _),
    function Action wrReq_infoRam__00__0(Struct31 _),
    function ActionValue#(Vector#(4, Bit#(64))) rdResp_dataRam__00(),
    function Action rdReq_dataRam__00(Bit#(12) _),
    function ActionValue#(Vector#(8, Bit#(8))) repGetRs__00(),
    function ActionValue#(Struct28) rdResp_edirRam__00__3(),
    function ActionValue#(Struct28) rdResp_edirRam__00__2(),
    function ActionValue#(Struct28) rdResp_edirRam__00__1(),
    function ActionValue#(Struct28) rdResp_edirRam__00__0(),
    function ActionValue#(Struct26) rdResp_infoRam__00__7(),
    function ActionValue#(Struct26) rdResp_infoRam__00__6(),
    function ActionValue#(Struct26) rdResp_infoRam__00__5(),
    function ActionValue#(Struct26) rdResp_infoRam__00__4(),
    function ActionValue#(Struct26) rdResp_infoRam__00__3(),
    function ActionValue#(Struct26) rdResp_infoRam__00__2(),
    function ActionValue#(Struct26) rdResp_infoRam__00__1(),
    function ActionValue#(Struct26) rdResp_infoRam__00__0(),
    function Action repGetRq__00(Bit#(9) _),
    function Action rdReq_edirRam__00__3(Bit#(9) _),
    function Action rdReq_edirRam__00__2(Bit#(9) _),
    function Action rdReq_edirRam__00__1(Bit#(9) _),
    function Action rdReq_edirRam__00__0(Bit#(9) _),
    function Action rdReq_infoRam__00__7(Bit#(9) _),
    function Action rdReq_infoRam__00__6(Bit#(9) _),
    function Action rdReq_infoRam__00__5(Bit#(9) _),
    function Action rdReq_infoRam__00__4(Bit#(9) _),
    function Action rdReq_infoRam__00__3(Bit#(9) _),
    function Action rdReq_infoRam__00__2(Bit#(9) _),
    function Action rdReq_infoRam__00__1(Bit#(9) _),
    function Action rdReq_infoRam__00__0(Bit#(9) _))
    (Module72);

    // No rules in this module

    method Action cache__00__infoRq (Bit#(64) x_0);
        Bit#(9) x_1 = ((x_0)[13:5]);
        let x_2 <- rdReq_infoRam__00__0(x_1);
        let x_3 <- rdReq_infoRam__00__1(x_1);
        let x_4 <- rdReq_infoRam__00__2(x_1);
        let x_5 <- rdReq_infoRam__00__3(x_1);
        let x_6 <- rdReq_infoRam__00__4(x_1);
        let x_7 <- rdReq_infoRam__00__5(x_1);
        let x_8 <- rdReq_infoRam__00__6(x_1);
        let x_9 <- rdReq_infoRam__00__7(x_1);
        let x_10 <- rdReq_edirRam__00__0(x_1);
        let x_11 <- rdReq_edirRam__00__1(x_1);
        let x_12 <- rdReq_edirRam__00__2(x_1);
        let x_13 <- rdReq_edirRam__00__3(x_1);
        let x_14 <- repGetRq__00(x_1);
    endmethod

    method ActionValue#(Struct9) cache__00__infoRsValueRq (Bit#(64) x_0);
        Bit#(50) x_1 = ((x_0)[63:14]);
        Bit#(9) x_2 = ((x_0)[13:5]);
        Vector#(8, Struct26) x_3 = (unpack(0));
        let x_4 <- rdResp_infoRam__00__0();
        Vector#(8, Struct26) x_5 = (update (x_3, (Bit#(3))'(3'h0), x_4));
        let x_6 <- rdResp_infoRam__00__1();
        Vector#(8, Struct26) x_7 = (update (x_5, (Bit#(3))'(3'h1), x_6));
        let x_8 <- rdResp_infoRam__00__2();
        Vector#(8, Struct26) x_9 = (update (x_7, (Bit#(3))'(3'h2), x_8));
        let x_10 <- rdResp_infoRam__00__3();
        Vector#(8, Struct26) x_11 = (update (x_9, (Bit#(3))'(3'h3),
        x_10));
        let x_12 <- rdResp_infoRam__00__4();
        Vector#(8, Struct26) x_13 = (update (x_11, (Bit#(3))'(3'h4),
        x_12));
        let x_14 <- rdResp_infoRam__00__5();
        Vector#(8, Struct26) x_15 = (update (x_13, (Bit#(3))'(3'h5),
        x_14));
        let x_16 <- rdResp_infoRam__00__6();
        Vector#(8, Struct26) x_17 = (update (x_15, (Bit#(3))'(3'h6),
        x_16));
        let x_18 <- rdResp_infoRam__00__7();
        Vector#(8, Struct26) x_19 = (update (x_17, (Bit#(3))'(3'h7),
        x_18));
        Struct27 x_20 = (((((x_19)[(Bit#(3))'(3'h0)]).tag) == (x_1) ?
        (Struct27 {tm_hit : (Bool)'(True), tm_way : (Bit#(3))'(3'h0),
        tm_value : ((x_19)[(Bit#(3))'(3'h0)]).value}) :
        (((((x_19)[(Bit#(3))'(3'h1)]).tag) == (x_1) ? (Struct27 {tm_hit :
        (Bool)'(True), tm_way : (Bit#(3))'(3'h1), tm_value :
        ((x_19)[(Bit#(3))'(3'h1)]).value}) :
        (((((x_19)[(Bit#(3))'(3'h2)]).tag) == (x_1) ? (Struct27 {tm_hit :
        (Bool)'(True), tm_way : (Bit#(3))'(3'h2), tm_value :
        ((x_19)[(Bit#(3))'(3'h2)]).value}) :
        (((((x_19)[(Bit#(3))'(3'h3)]).tag) == (x_1) ? (Struct27 {tm_hit :
        (Bool)'(True), tm_way : (Bit#(3))'(3'h3), tm_value :
        ((x_19)[(Bit#(3))'(3'h3)]).value}) :
        (((((x_19)[(Bit#(3))'(3'h4)]).tag) == (x_1) ? (Struct27 {tm_hit :
        (Bool)'(True), tm_way : (Bit#(3))'(3'h4), tm_value :
        ((x_19)[(Bit#(3))'(3'h4)]).value}) :
        (((((x_19)[(Bit#(3))'(3'h5)]).tag) == (x_1) ? (Struct27 {tm_hit :
        (Bool)'(True), tm_way : (Bit#(3))'(3'h5), tm_value :
        ((x_19)[(Bit#(3))'(3'h5)]).value}) :
        (((((x_19)[(Bit#(3))'(3'h6)]).tag) == (x_1) ? (Struct27 {tm_hit :
        (Bool)'(True), tm_way : (Bit#(3))'(3'h6), tm_value :
        ((x_19)[(Bit#(3))'(3'h6)]).value}) :
        (((((x_19)[(Bit#(3))'(3'h7)]).tag) == (x_1) ? (Struct27 {tm_hit :
        (Bool)'(True), tm_way : (Bit#(3))'(3'h7), tm_value :
        ((x_19)[(Bit#(3))'(3'h7)]).value}) :
        (unpack(0))))))))))))))))));
        Vector#(4, Struct28) x_21 = (unpack(0));
        let x_22 <- rdResp_edirRam__00__0();
        Vector#(4, Struct28) x_23 = (update (x_21, (Bit#(2))'(2'h0),
        x_22));
        let x_24 <- rdResp_edirRam__00__1();
        Vector#(4, Struct28) x_25 = (update (x_23, (Bit#(2))'(2'h1),
        x_24));
        let x_26 <- rdResp_edirRam__00__2();
        Vector#(4, Struct28) x_27 = (update (x_25, (Bit#(2))'(2'h2),
        x_26));
        let x_28 <- rdResp_edirRam__00__3();
        Vector#(4, Struct28) x_29 = (update (x_27, (Bit#(2))'(2'h3),
        x_28));
        Struct30 x_30 = (((((x_29)[(Bit#(2))'(2'h0)]).tag) == (x_1) ?
        (Struct30 {tm_hit : (Bool)'(True), tm_way : (Bit#(2))'(2'h0),
        tm_value : ((x_29)[(Bit#(2))'(2'h0)]).value}) :
        (((((x_29)[(Bit#(2))'(2'h1)]).tag) == (x_1) ? (Struct30 {tm_hit :
        (Bool)'(True), tm_way : (Bit#(2))'(2'h1), tm_value :
        ((x_29)[(Bit#(2))'(2'h1)]).value}) :
        (((((x_29)[(Bit#(2))'(2'h2)]).tag) == (x_1) ? (Struct30 {tm_hit :
        (Bool)'(True), tm_way : (Bit#(2))'(2'h2), tm_value :
        ((x_29)[(Bit#(2))'(2'h2)]).value}) :
        (((((x_29)[(Bit#(2))'(2'h3)]).tag) == (x_1) ? (Struct30 {tm_hit :
        (Bool)'(True), tm_way : (Bit#(2))'(2'h3), tm_value :
        ((x_29)[(Bit#(2))'(2'h3)]).value}) : (unpack(0))))))))));
        Struct29 x_31 = ((x_30).tm_value);
        Struct10 x_32 = ((! (((Bit#(3))'(3'h1)) <
        ((((x_29)[(Bit#(2))'(2'h0)]).value).mesi_edir_st)) ? (Struct10 {valid
        : (Bool)'(True), data : (Bit#(2))'(2'h0)}) : ((! (((Bit#(3))'(3'h1))
        < ((((x_29)[(Bit#(2))'(2'h1)]).value).mesi_edir_st)) ? (Struct10
        {valid : (Bool)'(True), data : (Bit#(2))'(2'h1)}) : ((!
        (((Bit#(3))'(3'h1)) <
        ((((x_29)[(Bit#(2))'(2'h2)]).value).mesi_edir_st)) ? (Struct10 {valid
        : (Bool)'(True), data : (Bit#(2))'(2'h2)}) : ((! (((Bit#(3))'(3'h1))
        < ((((x_29)[(Bit#(2))'(2'h3)]).value).mesi_edir_st)) ? (Struct10
        {valid : (Bool)'(True), data : (Bit#(2))'(2'h3)}) : (Struct10 {valid
        : (Bool)'(False), data : unpack(0)})))))))));
        let x_33 <- repGetRs__00();
        Bit#(3) x_34 = (unpack(0));
        Bit#(8) x_35 = (unpack(0));
        Bit#(3) x_36 = ((! (((x_33)[(Bit#(3))'(3'h7)]) < (x_35)) ?
        ((Bit#(3))'(3'h7)) : (x_34)));
        Bit#(8) x_37 = ((! (((x_33)[(Bit#(3))'(3'h7)]) < (x_35)) ?
        ((x_33)[(Bit#(3))'(3'h7)]) : (x_35)));
        Bit#(3) x_38 = ((! (((x_33)[(Bit#(3))'(3'h6)]) < (x_37)) ?
        ((Bit#(3))'(3'h6)) : (x_36)));
        Bit#(8) x_39 = ((! (((x_33)[(Bit#(3))'(3'h6)]) < (x_37)) ?
        ((x_33)[(Bit#(3))'(3'h6)]) : (x_37)));
        Bit#(3) x_40 = ((! (((x_33)[(Bit#(3))'(3'h5)]) < (x_39)) ?
        ((Bit#(3))'(3'h5)) : (x_38)));
        Bit#(8) x_41 = ((! (((x_33)[(Bit#(3))'(3'h5)]) < (x_39)) ?
        ((x_33)[(Bit#(3))'(3'h5)]) : (x_39)));
        Bit#(3) x_42 = ((! (((x_33)[(Bit#(3))'(3'h4)]) < (x_41)) ?
        ((Bit#(3))'(3'h4)) : (x_40)));
        Bit#(8) x_43 = ((! (((x_33)[(Bit#(3))'(3'h4)]) < (x_41)) ?
        ((x_33)[(Bit#(3))'(3'h4)]) : (x_41)));
        Bit#(3) x_44 = ((! (((x_33)[(Bit#(3))'(3'h3)]) < (x_43)) ?
        ((Bit#(3))'(3'h3)) : (x_42)));
        Bit#(8) x_45 = ((! (((x_33)[(Bit#(3))'(3'h3)]) < (x_43)) ?
        ((x_33)[(Bit#(3))'(3'h3)]) : (x_43)));
        Bit#(3) x_46 = ((! (((x_33)[(Bit#(3))'(3'h2)]) < (x_45)) ?
        ((Bit#(3))'(3'h2)) : (x_44)));
        Bit#(8) x_47 = ((! (((x_33)[(Bit#(3))'(3'h2)]) < (x_45)) ?
        ((x_33)[(Bit#(3))'(3'h2)]) : (x_45)));
        Bit#(3) x_48 = ((! (((x_33)[(Bit#(3))'(3'h1)]) < (x_47)) ?
        ((Bit#(3))'(3'h1)) : (x_46)));
        Bit#(8) x_49 = ((! (((x_33)[(Bit#(3))'(3'h1)]) < (x_47)) ?
        ((x_33)[(Bit#(3))'(3'h1)]) : (x_47)));
        Bit#(3) x_50 = ((! (((x_33)[(Bit#(3))'(3'h0)]) < (x_49)) ?
        ((Bit#(3))'(3'h0)) : (x_48)));
        Bit#(8) x_51 = ((! (((x_33)[(Bit#(3))'(3'h0)]) < (x_49)) ?
        ((x_33)[(Bit#(3))'(3'h0)]) : (x_49)));
        when (! ((x_51) == ((Bit#(8))'(8'h0))), noAction);
        Struct26 x_52 = ((x_19)[x_50]);
        Bit#(50) x_53 = ((x_52).tag);
        Struct11 x_54 = ((x_52).value);
        Bit#(3) x_55 = (((x_20).tm_hit ? ((x_20).tm_way) : (x_50)));
        Struct9 x_56 = (Struct9 {info_index : x_2, info_hit : (x_20).tm_hit,
        info_way : x_55, edir_hit : (x_30).tm_hit, edir_way : (x_30).tm_way,
        edir_slot : x_32, info : ((x_20).tm_hit ? ((x_20).tm_value) :
        (Struct11 {mesi_owned : (x_31).mesi_edir_owned, mesi_status :
        (Bit#(3))'(3'h1), mesi_dir_st : (x_31).mesi_edir_st, mesi_dir_sharers
        : (x_31).mesi_edir_sharers})), may_victim : Struct12 {mv_addr :
        {(x_53),({(x_2),((Bit#(5))'(5'h0))})}, mv_info : x_54}, reps :
        x_33});
        let x_57 <- rdReq_dataRam__00({(x_55),(x_2)});
        return x_56;
    endmethod

    method ActionValue#(Vector#(4, Bit#(64))) cache__00__valueRsLineRq
    (Struct18 x_0);
        let x_1 <- rdResp_dataRam__00();
        Bit#(64) x_2 = ((x_0).addr);
        Bit#(9) x_3 = ((x_2)[13:5]);
        Bit#(3) x_4 = ((x_0).info_way);
        Struct11 x_5 = ((x_0).info);
        Bool x_6 = ((! (((Bit#(3))'(3'h1)) < ((x_5).mesi_status))) && (!
        (((x_5).mesi_dir_st) == ((Bit#(3))'(3'h3)))));
        Struct10 x_7 = ((x_0).edir_slot);
        Bool x_8 = ((x_7).valid);
        Bit#(2) x_9 =
        ((x_7).data);
        if ((x_0).info_write)
            begin
            if ((((x_0).info_hit) || (! (x_6))) || (((! ((x_0).edir_hit)) &&
                (x_6)) && (! (x_8)))) begin
                Struct31 x_10 = (Struct31 {addr : x_3, datain : Struct26 {tag
                : (x_2)[63:14], value :
                x_5}});
                if ((x_4) == ((Bit#(3))'(3'h0))) begin
                    let x_11 <- wrReq_infoRam__00__0(x_10);
                end else begin

                end
                if ((x_4) == ((Bit#(3))'(3'h1))) begin
                    let x_13 <- wrReq_infoRam__00__1(x_10);
                end else begin

                end
                if ((x_4) == ((Bit#(3))'(3'h2))) begin
                    let x_15 <- wrReq_infoRam__00__2(x_10);
                end else begin

                end
                if ((x_4) == ((Bit#(3))'(3'h3))) begin
                    let x_17 <- wrReq_infoRam__00__3(x_10);
                end else begin

                end
                if ((x_4) == ((Bit#(3))'(3'h4))) begin
                    let x_19 <- wrReq_infoRam__00__4(x_10);
                end else begin

                end
                if ((x_4) == ((Bit#(3))'(3'h5))) begin
                    let x_21 <- wrReq_infoRam__00__5(x_10);
                end else begin

                end
                if ((x_4) == ((Bit#(3))'(3'h6))) begin
                    let x_23 <- wrReq_infoRam__00__6(x_10);
                end else begin

                end
                if ((x_4) == ((Bit#(3))'(3'h7))) begin
                    let x_25 <- wrReq_infoRam__00__7(x_10);
                end else begin

                end
                if (! ((x_0).info_hit)) begin
                    Struct12 x_27 = ((x_0).may_victim);
                    Struct14 x_28 = (Struct14 {victim_valid : (Bool)'(True),
                    victim_addr : (x_27).mv_addr, victim_info :
                    (x_27).mv_info, victim_value : x_1, victim_req :
                    (Bool)'(False)});
                    let x_29 <- victims__00__registerVictim(x_28);
                end else begin

                end
                let x_31 <- repAccess__00(Struct32 {acc_type : (!
                (((Bit#(3))'(3'h1)) < ((x_5).mesi_dir_st)) ?
                ((Bit#(1))'(1'h0)) : ((Bit#(1))'(1'h1))), acc_reps :
                (x_0).reps, acc_index : x_3, acc_way : x_4});
            end else begin

            end
            if (((! ((x_0).info_hit)) && (x_6)) && (((x_0).edir_hit) ||
                (x_8))) begin
                Bit#(2) x_33 = (((x_0).edir_hit ? ((x_0).edir_way) :
                (x_9)));
                Struct33 x_34 = (Struct33 {addr : (x_2)[13:5], datain :
                Struct28 {tag : (x_2)[63:14], value : Struct29
                {mesi_edir_owned : (x_5).mesi_owned, mesi_edir_st :
                (x_5).mesi_dir_st, mesi_edir_sharers :
                (x_5).mesi_dir_sharers}}});
                if ((x_33) == ((Bit#(2))'(2'h0))) begin
                    let x_35 <- wrReq_edirRam__00__0(x_34);
                end else begin

                end
                if ((x_33) == ((Bit#(2))'(2'h1))) begin
                    let x_37 <- wrReq_edirRam__00__1(x_34);
                end else begin

                end
                if ((x_33) == ((Bit#(2))'(2'h2))) begin
                    let x_39 <- wrReq_edirRam__00__2(x_34);
                end else begin

                end
                if ((x_33) == ((Bit#(2))'(2'h3))) begin
                    let x_41 <- wrReq_edirRam__00__3(x_34);
                end else begin

                end
            end else
                begin
                if ((x_0).edir_hit) begin
                    Bit#(2) x_43 = ((x_0).edir_way);
                    Struct33 x_44 = (Struct33 {addr : (x_2)[13:5], datain :
                    Struct28 {tag : (x_2)[63:14], value : Struct29
                    {mesi_edir_owned : (x_5).mesi_owned, mesi_edir_st :
                    (x_5).mesi_dir_st, mesi_edir_sharers :
                    (x_5).mesi_dir_sharers}}});
                    if ((x_43) == ((Bit#(2))'(2'h0))) begin
                        let x_45 <- wrReq_edirRam__00__0(x_44);
                    end else begin

                    end
                    if ((x_43) == ((Bit#(2))'(2'h1))) begin
                        let x_47 <- wrReq_edirRam__00__1(x_44);
                    end else begin

                    end
                    if ((x_43) == ((Bit#(2))'(2'h2))) begin
                        let x_49 <- wrReq_edirRam__00__2(x_44);
                    end else begin

                    end
                    if ((x_43) == ((Bit#(2))'(2'h3))) begin
                        let x_51 <- wrReq_edirRam__00__3(x_44);
                    end else begin

                    end
                end else begin

                end
            end
        end else begin

        end
        if ((x_0).value_write) begin
            Struct34 x_56 = (Struct34 {addr : {(x_4),((x_2)[13:5])}, datain :
            (x_0).value});
            let x_57 <- wrReq_dataRam__00(x_56);
        end else begin

        end
        return x_1;
    endmethod
endmodule

interface Module73;
    method Action cache__000__infoRq (Bit#(64) x_0);
    method ActionValue#(Struct41) cache__000__infoRsValueRq (Bit#(64) x_0);
    method ActionValue#(Vector#(4, Bit#(64))) cache__000__valueRsLineRq
    (Struct45 x_0);
endinterface

module mkModule73#(function Action wrReq_dataRam__000(Struct52 _),
    function Action repAccess__000(Struct51 _),
    function Action victims__000__registerVictim(Struct14 _),
    function Action wrReq_infoRam__000__3(Struct50 _),
    function Action wrReq_infoRam__000__2(Struct50 _),
    function Action wrReq_infoRam__000__1(Struct50 _),
    function Action wrReq_infoRam__000__0(Struct50 _),
    function ActionValue#(Vector#(4, Bit#(64))) rdResp_dataRam__000(),
    function Action rdReq_dataRam__000(Bit#(10) _),
    function ActionValue#(Vector#(4, Bit#(8))) repGetRs__000(),
    function ActionValue#(Struct48) rdResp_infoRam__000__3(),
    function ActionValue#(Struct48) rdResp_infoRam__000__2(),
    function ActionValue#(Struct48) rdResp_infoRam__000__1(),
    function ActionValue#(Struct48) rdResp_infoRam__000__0(),
    function Action repGetRq__000(Bit#(8) _),
    function Action rdReq_infoRam__000__3(Bit#(8) _),
    function Action rdReq_infoRam__000__2(Bit#(8) _),
    function Action rdReq_infoRam__000__1(Bit#(8) _),
    function Action rdReq_infoRam__000__0(Bit#(8) _))
    (Module73);

    // No rules in this module

    method Action cache__000__infoRq (Bit#(64) x_0);
        Bit#(8) x_1 = ((x_0)[12:5]);
        let x_2 <- rdReq_infoRam__000__0(x_1);
        let x_3 <- rdReq_infoRam__000__1(x_1);
        let x_4 <- rdReq_infoRam__000__2(x_1);
        let x_5 <- rdReq_infoRam__000__3(x_1);
        let x_6 <- repGetRq__000(x_1);
    endmethod

    method ActionValue#(Struct41) cache__000__infoRsValueRq (Bit#(64) x_0);
        Bit#(51) x_1 = ((x_0)[63:13]);
        Bit#(8) x_2 = ((x_0)[12:5]);
        Vector#(4, Struct48) x_3 = (unpack(0));
        let x_4 <- rdResp_infoRam__000__0();
        Vector#(4, Struct48) x_5 = (update (x_3, (Bit#(2))'(2'h0), x_4));
        let x_6 <- rdResp_infoRam__000__1();
        Vector#(4, Struct48) x_7 = (update (x_5, (Bit#(2))'(2'h1), x_6));
        let x_8 <- rdResp_infoRam__000__2();
        Vector#(4, Struct48) x_9 = (update (x_7, (Bit#(2))'(2'h2), x_8));
        let x_10 <- rdResp_infoRam__000__3();
        Vector#(4, Struct48) x_11 = (update (x_9, (Bit#(2))'(2'h3),
        x_10));
        Struct49 x_12 = (((((x_11)[(Bit#(2))'(2'h0)]).tag) == (x_1) ?
        (Struct49 {tm_hit : (Bool)'(True), tm_way : (Bit#(2))'(2'h0),
        tm_value : ((x_11)[(Bit#(2))'(2'h0)]).value}) :
        (((((x_11)[(Bit#(2))'(2'h1)]).tag) == (x_1) ? (Struct49 {tm_hit :
        (Bool)'(True), tm_way : (Bit#(2))'(2'h1), tm_value :
        ((x_11)[(Bit#(2))'(2'h1)]).value}) :
        (((((x_11)[(Bit#(2))'(2'h2)]).tag) == (x_1) ? (Struct49 {tm_hit :
        (Bool)'(True), tm_way : (Bit#(2))'(2'h2), tm_value :
        ((x_11)[(Bit#(2))'(2'h2)]).value}) :
        (((((x_11)[(Bit#(2))'(2'h3)]).tag) == (x_1) ? (Struct49 {tm_hit :
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
        Struct48 x_24 = ((x_11)[x_22]);
        Bit#(51) x_25 = ((x_24).tag);
        Struct11 x_26 = ((x_24).value);
        Bit#(2) x_27 = (((x_12).tm_hit ? ((x_12).tm_way) : (x_22)));
        Struct41 x_28 = (Struct41 {info_index : x_2, info_hit :
        (x_12).tm_hit, info_way : x_27, edir_hit : unpack(0), edir_way :
        unpack(0), edir_slot : unpack(0), info : (x_12).tm_value, may_victim
        : Struct12 {mv_addr : {(x_25),({(x_2),((Bit#(5))'(5'h0))})}, mv_info
        : x_26}, reps : x_13});
        let x_29 <- rdReq_dataRam__000({(x_27),(x_2)});
        return x_28;
    endmethod

    method ActionValue#(Vector#(4, Bit#(64))) cache__000__valueRsLineRq
    (Struct45 x_0);
        let x_1 <- rdResp_dataRam__000();
        Bit#(64) x_2 = ((x_0).addr);
        Bit#(8) x_3 = ((x_2)[12:5]);
        Bit#(2) x_4 = ((x_0).info_way);
        Struct11 x_5 =
        ((x_0).info);
        if ((x_0).info_write) begin
            Struct50 x_6 = (Struct50 {addr : x_3, datain : Struct48 {tag :
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
                Struct12 x_15 = ((x_0).may_victim);
                Struct14 x_16 = (Struct14 {victim_valid : (Bool)'(True),
                victim_addr : (x_15).mv_addr, victim_info : (x_15).mv_info,
                victim_value : x_1, victim_req : (Bool)'(False)});
                let x_17 <- victims__000__registerVictim(x_16);
            end else begin

            end
            let x_19 <- repAccess__000(Struct51 {acc_type : (!
            (((Bit#(3))'(3'h1)) < ((x_5).mesi_dir_st)) ? ((Bit#(1))'(1'h0)) :
            ((Bit#(1))'(1'h1))), acc_reps : (x_0).reps, acc_index : x_3,
            acc_way : x_4});
        end else begin

        end
        if ((x_0).value_write) begin
            Struct52 x_21 = (Struct52 {addr : {(x_4),((x_2)[12:5])}, datain :
            (x_0).value});
            let x_22 <- wrReq_dataRam__000(x_21);
        end else begin

        end
        return x_1;
    endmethod
endmodule

interface Module74;
    method Action cache__001__infoRq (Bit#(64) x_0);
    method ActionValue#(Struct41) cache__001__infoRsValueRq (Bit#(64) x_0);
    method ActionValue#(Vector#(4, Bit#(64))) cache__001__valueRsLineRq
    (Struct45 x_0);
endinterface

module mkModule74#(function Action wrReq_dataRam__001(Struct52 _),
    function Action repAccess__001(Struct51 _),
    function Action victims__001__registerVictim(Struct14 _),
    function Action wrReq_infoRam__001__3(Struct50 _),
    function Action wrReq_infoRam__001__2(Struct50 _),
    function Action wrReq_infoRam__001__1(Struct50 _),
    function Action wrReq_infoRam__001__0(Struct50 _),
    function ActionValue#(Vector#(4, Bit#(64))) rdResp_dataRam__001(),
    function Action rdReq_dataRam__001(Bit#(10) _),
    function ActionValue#(Vector#(4, Bit#(8))) repGetRs__001(),
    function ActionValue#(Struct48) rdResp_infoRam__001__3(),
    function ActionValue#(Struct48) rdResp_infoRam__001__2(),
    function ActionValue#(Struct48) rdResp_infoRam__001__1(),
    function ActionValue#(Struct48) rdResp_infoRam__001__0(),
    function Action repGetRq__001(Bit#(8) _),
    function Action rdReq_infoRam__001__3(Bit#(8) _),
    function Action rdReq_infoRam__001__2(Bit#(8) _),
    function Action rdReq_infoRam__001__1(Bit#(8) _),
    function Action rdReq_infoRam__001__0(Bit#(8) _))
    (Module74);

    // No rules in this module

    method Action cache__001__infoRq (Bit#(64) x_0);
        Bit#(8) x_1 = ((x_0)[12:5]);
        let x_2 <- rdReq_infoRam__001__0(x_1);
        let x_3 <- rdReq_infoRam__001__1(x_1);
        let x_4 <- rdReq_infoRam__001__2(x_1);
        let x_5 <- rdReq_infoRam__001__3(x_1);
        let x_6 <- repGetRq__001(x_1);
    endmethod

    method ActionValue#(Struct41) cache__001__infoRsValueRq (Bit#(64) x_0);
        Bit#(51) x_1 = ((x_0)[63:13]);
        Bit#(8) x_2 = ((x_0)[12:5]);
        Vector#(4, Struct48) x_3 = (unpack(0));
        let x_4 <- rdResp_infoRam__001__0();
        Vector#(4, Struct48) x_5 = (update (x_3, (Bit#(2))'(2'h0), x_4));
        let x_6 <- rdResp_infoRam__001__1();
        Vector#(4, Struct48) x_7 = (update (x_5, (Bit#(2))'(2'h1), x_6));
        let x_8 <- rdResp_infoRam__001__2();
        Vector#(4, Struct48) x_9 = (update (x_7, (Bit#(2))'(2'h2), x_8));
        let x_10 <- rdResp_infoRam__001__3();
        Vector#(4, Struct48) x_11 = (update (x_9, (Bit#(2))'(2'h3),
        x_10));
        Struct49 x_12 = (((((x_11)[(Bit#(2))'(2'h0)]).tag) == (x_1) ?
        (Struct49 {tm_hit : (Bool)'(True), tm_way : (Bit#(2))'(2'h0),
        tm_value : ((x_11)[(Bit#(2))'(2'h0)]).value}) :
        (((((x_11)[(Bit#(2))'(2'h1)]).tag) == (x_1) ? (Struct49 {tm_hit :
        (Bool)'(True), tm_way : (Bit#(2))'(2'h1), tm_value :
        ((x_11)[(Bit#(2))'(2'h1)]).value}) :
        (((((x_11)[(Bit#(2))'(2'h2)]).tag) == (x_1) ? (Struct49 {tm_hit :
        (Bool)'(True), tm_way : (Bit#(2))'(2'h2), tm_value :
        ((x_11)[(Bit#(2))'(2'h2)]).value}) :
        (((((x_11)[(Bit#(2))'(2'h3)]).tag) == (x_1) ? (Struct49 {tm_hit :
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
        Struct48 x_24 = ((x_11)[x_22]);
        Bit#(51) x_25 = ((x_24).tag);
        Struct11 x_26 = ((x_24).value);
        Bit#(2) x_27 = (((x_12).tm_hit ? ((x_12).tm_way) : (x_22)));
        Struct41 x_28 = (Struct41 {info_index : x_2, info_hit :
        (x_12).tm_hit, info_way : x_27, edir_hit : unpack(0), edir_way :
        unpack(0), edir_slot : unpack(0), info : (x_12).tm_value, may_victim
        : Struct12 {mv_addr : {(x_25),({(x_2),((Bit#(5))'(5'h0))})}, mv_info
        : x_26}, reps : x_13});
        let x_29 <- rdReq_dataRam__001({(x_27),(x_2)});
        return x_28;
    endmethod

    method ActionValue#(Vector#(4, Bit#(64))) cache__001__valueRsLineRq
    (Struct45 x_0);
        let x_1 <- rdResp_dataRam__001();
        Bit#(64) x_2 = ((x_0).addr);
        Bit#(8) x_3 = ((x_2)[12:5]);
        Bit#(2) x_4 = ((x_0).info_way);
        Struct11 x_5 =
        ((x_0).info);
        if ((x_0).info_write) begin
            Struct50 x_6 = (Struct50 {addr : x_3, datain : Struct48 {tag :
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
                Struct12 x_15 = ((x_0).may_victim);
                Struct14 x_16 = (Struct14 {victim_valid : (Bool)'(True),
                victim_addr : (x_15).mv_addr, victim_info : (x_15).mv_info,
                victim_value : x_1, victim_req : (Bool)'(False)});
                let x_17 <- victims__001__registerVictim(x_16);
            end else begin

            end
            let x_19 <- repAccess__001(Struct51 {acc_type : (!
            (((Bit#(3))'(3'h1)) < ((x_5).mesi_dir_st)) ? ((Bit#(1))'(1'h0)) :
            ((Bit#(1))'(1'h1))), acc_reps : (x_0).reps, acc_index : x_3,
            acc_way : x_4});
        end else begin

        end
        if ((x_0).value_write) begin
            Struct52 x_21 = (Struct52 {addr : {(x_4),((x_2)[12:5])}, datain :
            (x_0).value});
            let x_22 <- wrReq_dataRam__001(x_21);
        end else begin

        end
        return x_1;
    endmethod
endmodule

interface Module75;

endinterface

module mkModule75#(function Action canImm_00(Bit#(64) _),
    function Action victims__00__setVictimRq(Bit#(64) _),
    function Action setULImm_00(Struct1 _),
    function ActionValue#(Struct14) victims__00__getFirstVictim(),
    function Action transferUpDown_00(Struct25 _),
    function Action broadcast_parentChildren00(Struct23 _),
    function Action registerDL_00(Struct22 _),
    function Action registerUL_00(Struct21 _),
    function Action makeEnq_parentChildren00(Struct20 _),
    function ActionValue#(Vector#(4, Bit#(64))) cache__00__valueRsLineRq(Struct18 _),
    function Action victims__00__setVictim(Struct19 _),
    function ActionValue#(Struct1) getMSHRFirstRs_00(Bit#(4) _),
    function ActionValue#(Struct1) getMSHRRq_00(Bit#(4) _),
    function ActionValue#(Struct15) getMSHR_00(Bit#(4) _),
    function ActionValue#(Struct13) deq_fifoL2E_00(),
    function ActionValue#(Struct14) victims__00__getVictim(Bit#(3) _),
    function Action enq_fifoL2E_00(Struct13 _),
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
    function Action releaseMSHR_00(Bit#(4) _),
    function Action victims__00__releaseVictim(Bit#(64) _),
    function ActionValue#(Struct3) getWait_00(),
    function Action startRelease_00(Bit#(4) _),
    function ActionValue#(Bit#(4)) getULReady_00(Bit#(64) _),
    function Action enq_fifoN2I_00(Struct6 _),
    function ActionValue#(Struct5) victims__00__findVictim(Bit#(64) _),
    function ActionValue#(Struct4) getPRqSlot_00(Struct3 _),
    function ActionValue#(Struct2) deq_fifoPInput_00())
    (Module75);

    rule rule_in_prq_00;
        $display ("Rule fired: rule_in_prq_00 at %t", $time);
        let x_0 <- deq_fifoPInput_00();
        Bit#(3) x_1 = ((x_0).in_msg_from);
        when ((x_1) == ({((Bit#(2))'(2'h2)),((Bit#(1))'(1'h0))}),
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
        $display ("Rule fired: rule_in_prs_00 at %t", $time);
        let x_0 <- deq_fifoPInput_00();
        Bit#(3) x_1 = ((x_0).in_msg_from);
        when ((x_1) == ({((Bit#(2))'(2'h2)),((Bit#(1))'(1'h0))}),
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
        $display ("Rule fired: rule_in_retry_00 at %t", $time);
        let x_0 <- getWait_00();
        Struct1 x_1 = ((x_0).r_msg);
        let x_2 <- victims__00__findVictim((x_1).addr);
        Struct6 x_3 = (Struct6 {ir_is_rs_rel : (Bool)'(False), ir_msg : x_1,
        ir_msg_from : (x_0).r_msg_from, ir_mshr_id : (x_0).r_id, ir_by_victim
        : x_2});
        let x_4 <- enq_fifoN2I_00(x_3);
    endrule

    rule rule_in_invrs_00;
        $display ("Rule fired: rule_in_invrs_00 at %t", $time);
        let x_0 <- deq_fifoPInput_00();
        Bit#(3) x_1 = ((x_0).in_msg_from);
        when ((x_1) == ({((Bit#(2))'(2'h2)),((Bit#(1))'(1'h0))}),
        noAction);
        Struct1 x_2 = ((x_0).in_msg);
        when (((x_2).type_) && (((x_2).id) == ((Bit#(6))'(6'h16))),
        noAction);
        let x_3 <- getULReady_00((x_2).addr);
        let x_4 <- victims__00__releaseVictim((x_2).addr);
        let x_5 <- releaseMSHR_00(x_3);
    endrule

    rule rule_in_crq_00;
        $display ("Rule fired: rule_in_crq_00 at %t", $time);
        let x_0 <- deq_fifoCRqInput_00();
        Bit#(3) x_1 = ((x_0).in_msg_from);
        when (((x_1)[2:1]) == ((Bit#(2))'(2'h0)), noAction);
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
        $display ("Rule fired: rule_in_crs_00 at %t", $time);
        let x_0 <- deq_fifoCRsInput_00();
        Bit#(3) x_1 = ((x_0).in_msg_from);
        when (((x_1)[2:1]) == ((Bit#(2))'(2'h1)), noAction);
        Struct1 x_2 = ((x_0).in_msg);
        when ((x_2).type_, noAction);
        let x_3 <- addRs_00(Struct7 {r_midx : (x_1)[0:0], r_msg : x_2});
    endrule

    rule rule_in_rsrel_00;
        $display ("Rule fired: rule_in_rsrel_00 at %t", $time);
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
        $display ("Rule fired: rule_ir_cache_00 at %t", $time);
        let x_0 <- deq_fifoN2I_00();
        when (! (((x_0).ir_by_victim).valid), noAction);
        Struct1 x_1 = ((x_0).ir_msg);
        let x_2 <- cache__00__infoRq((x_1).addr);
        let x_3 <- enq_fifoI2L_00(x_0);
    endrule

    rule rule_ir_victims_00;
        $display ("Rule fired: rule_ir_victims_00 at %t", $time);
        let x_0 <- deq_fifoN2I_00();
        when (((x_0).ir_by_victim).valid, noAction);
        let x_1 <- enq_fifoI2L_00(x_0);
    endrule

    rule rule_lr_cache_00;
        $display ("Rule fired: rule_lr_cache_00 at %t", $time);
        let x_0 <- deq_fifoI2L_00();
        when (! (((x_0).ir_by_victim).valid), noAction);
        let x_1 <- cache__00__infoRsValueRq(((x_0).ir_msg).addr);
        Struct13 x_2 = (Struct13 {lr_ir_pp : x_0, lr_ir : x_1, lr_value :
        unpack(0)});
        let x_3 <- enq_fifoL2E_00(x_2);
    endrule

    rule rule_lr_victims_00;
        $display ("Rule fired: rule_lr_victims_00 at %t", $time);
        let x_0 <- deq_fifoI2L_00();
        when (((x_0).ir_by_victim).valid, noAction);
        Bit#(3) x_1 = (((x_0).ir_by_victim).data);
        let x_2 <- victims__00__getVictim(x_1);
        Struct9 x_3 = (Struct9 {info_index : unpack(0), info_hit : unpack(0),
        info_way : unpack(0), edir_hit : unpack(0), edir_way : unpack(0),
        edir_slot : unpack(0), info : (x_2).victim_info, may_victim :
        unpack(0), reps : unpack(0)});
        Struct13 x_4 = (Struct13 {lr_ir_pp : x_0, lr_ir : x_3, lr_value :
        (x_2).victim_value});
        let x_5 <- enq_fifoL2E_00(x_4);
    endrule

    rule rule_exec_00_000000;
        $display ("Rule fired: rule_exec_00_000000 at %t", $time);
        let x_0 <- deq_fifoL2E_00();
        Struct6 x_1 = ((x_0).lr_ir_pp);
        Bit#(3) x_2 = ((x_1).ir_msg_from);
        Struct1 x_3 = ((x_1).ir_msg);
        Bit#(4) x_4 = ((x_1).ir_mshr_id);
        Bool x_5 = ((x_1).ir_is_rs_rel);
        when (! (x_5), noAction);
        Struct9 x_6 = ((x_0).lr_ir);
        Struct11 x_7 = ((x_6).info);
        Struct5 x_8 = ((x_1).ir_by_victim);
        Vector#(4, Bit#(64)) x_9 = ((x_0).lr_value);
        let x_10 <- getMSHR_00(x_4);
        let x_11 <- getMSHRRq_00(x_4);
        let x_12 <- getMSHRFirstRs_00(x_4);
        Vector#(4, Bit#(64)) x_13 = (unpack(0));
        Bool x_14 = ((x_7).mesi_owned);
        Bit#(3) x_15 = ((x_7).mesi_status);
        Struct17 x_16 = (Struct17 {dir_st : (((x_7).mesi_dir_st) ==
        ((Bit#(3))'(3'h0)) ? ((Bit#(3))'(3'h1)) : ((x_7).mesi_dir_st)),
        dir_excl : ((((x_7).mesi_dir_sharers)[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(1))'(1'h0)) : (((Bit#(1))'(1'h1)) +
        ((((((x_7).mesi_dir_sharers)[1:1])[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(1))'(1'h0)) : (((Bit#(1))'(1'h1)) + (unpack(0))))))),
        dir_sharers : (x_7).mesi_dir_sharers});
        when ((x_2) == ((Bit#(3))'(3'h0)), noAction);
        when (((x_3).id) == ((Bit#(6))'(6'h2)), noAction);
        when (! ((x_3).type_), noAction);
        when ((! (((Bit#(3))'(3'h2)) < ((x_16).dir_st))) && ((x_15) ==
        ((Bit#(3))'(3'h2))), noAction);
        Struct1 x_17 = (x_3);
        Struct18 x_18 = (Struct18 {addr : (x_3).addr, info_write :
        (Bool)'(False), info_hit : (x_6).info_hit, info_way : (x_6).info_way,
        edir_hit : (x_6).edir_hit, edir_way : (x_6).edir_way, edir_slot :
        (x_6).edir_slot, info : (x_6).info, value_write : (Bool)'(False),
        value : unpack(0), may_victim : (x_6).may_victim, reps :
        (x_6).reps});
        Struct18 x_19 = (Struct18 {addr : (x_18).addr, info_write :
        (Bool)'(True), info_hit : (x_18).info_hit, info_way :
        (x_18).info_way, edir_hit : (x_18).edir_hit, edir_way :
        (x_18).edir_way, edir_slot : (x_18).edir_slot, info : Struct11
        {mesi_owned : ((x_18).info).mesi_owned, mesi_status :
        ((x_18).info).mesi_status, mesi_dir_st : (Struct17 {dir_st :
        (Bit#(3))'(3'h2), dir_excl : (x_16).dir_excl, dir_sharers :
        (((x_16).dir_st) == ((Bit#(3))'(3'h2)) ? (((x_16).dir_sharers) |
        (((Bit#(2))'(2'h1)) << ((Bit#(1))'(1'h0)))) : (((Bit#(2))'(2'h1)) <<
        ((Bit#(1))'(1'h0))))}).dir_st, mesi_dir_sharers : (((Struct17 {dir_st
        : (Bit#(3))'(3'h2), dir_excl : (x_16).dir_excl, dir_sharers :
        (((x_16).dir_st) == ((Bit#(3))'(3'h2)) ? (((x_16).dir_sharers) |
        (((Bit#(2))'(2'h1)) << ((Bit#(1))'(1'h0)))) : (((Bit#(2))'(2'h1)) <<
        ((Bit#(1))'(1'h0))))}).dir_st) == ((Bit#(3))'(3'h2)) ? ((Struct17
        {dir_st : (Bit#(3))'(3'h2), dir_excl : (x_16).dir_excl, dir_sharers :
        (((x_16).dir_st) == ((Bit#(3))'(3'h2)) ? (((x_16).dir_sharers) |
        (((Bit#(2))'(2'h1)) << ((Bit#(1))'(1'h0)))) : (((Bit#(2))'(2'h1)) <<
        ((Bit#(1))'(1'h0))))}).dir_sharers) : (((Bit#(2))'(2'h1)) <<
        ((Struct17 {dir_st : (Bit#(3))'(3'h2), dir_excl : (x_16).dir_excl,
        dir_sharers : (((x_16).dir_st) == ((Bit#(3))'(3'h2)) ?
        (((x_16).dir_sharers) | (((Bit#(2))'(2'h1)) << ((Bit#(1))'(1'h0)))) :
        (((Bit#(2))'(2'h1)) << ((Bit#(1))'(1'h0))))}).dir_excl)))},
        value_write : (x_18).value_write, value : (x_18).value, may_victim :
        (x_18).may_victim, reps :
        (x_18).reps});
        let x_22 = ?;
        if ((x_8).valid) begin
            let x_20 <- victims__00__setVictim(Struct19 {victim_idx :
            (x_8).data, victim_info : (x_19).info, victim_value :
            ((x_19).value_write ? ((x_19).value) : (x_9))});
            x_22 = x_9;
        end else begin
            let x_21 <- cache__00__valueRsLineRq(x_19);
            x_22 = x_21;
        end
        Struct20 x_23 = (Struct20 {enq_type : ((((Bit#(3))'(3'h4))[2:1]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : (((((Bit#(3))'(3'h4))[2:1])
        == ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : ((Bit#(3))'(3'h4))[0:0], enq_msg : Struct1 {id :
        (Bit#(6))'(6'h3), type_ : (Bool)'(True), addr : (x_17).addr, value :
        x_22}});
        let x_24 <- makeEnq_parentChildren00(x_23);
        let x_25 <- releaseMSHR_00(x_4);
    endrule

    rule rule_exec_00_001000;
        $display ("Rule fired: rule_exec_00_001000 at %t", $time);
        let x_0 <- deq_fifoL2E_00();
        Struct6 x_1 = ((x_0).lr_ir_pp);
        Bit#(3) x_2 = ((x_1).ir_msg_from);
        Struct1 x_3 = ((x_1).ir_msg);
        Bit#(4) x_4 = ((x_1).ir_mshr_id);
        Bool x_5 = ((x_1).ir_is_rs_rel);
        when (! (x_5), noAction);
        Struct9 x_6 = ((x_0).lr_ir);
        Struct11 x_7 = ((x_6).info);
        Struct5 x_8 = ((x_1).ir_by_victim);
        Vector#(4, Bit#(64)) x_9 = ((x_0).lr_value);
        let x_10 <- getMSHR_00(x_4);
        let x_11 <- getMSHRRq_00(x_4);
        let x_12 <- getMSHRFirstRs_00(x_4);
        Vector#(4, Bit#(64)) x_13 = (unpack(0));
        Bool x_14 = ((x_7).mesi_owned);
        Bit#(3) x_15 = ((x_7).mesi_status);
        Struct17 x_16 = (Struct17 {dir_st : (((x_7).mesi_dir_st) ==
        ((Bit#(3))'(3'h0)) ? ((Bit#(3))'(3'h1)) : ((x_7).mesi_dir_st)),
        dir_excl : ((((x_7).mesi_dir_sharers)[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(1))'(1'h0)) : (((Bit#(1))'(1'h1)) +
        ((((((x_7).mesi_dir_sharers)[1:1])[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(1))'(1'h0)) : (((Bit#(1))'(1'h1)) + (unpack(0))))))),
        dir_sharers : (x_7).mesi_dir_sharers});
        when ((x_2) == ((Bit#(3))'(3'h0)), noAction);
        when (((x_3).id) == ((Bit#(6))'(6'h2)), noAction);
        when (! ((x_3).type_), noAction);
        when ((! ((x_15) < ((Bit#(3))'(3'h3)))) && (((x_16).dir_st) ==
        ((Bit#(3))'(3'h1))), noAction);
        Struct1 x_17 = (x_3);
        Struct18 x_18 = (Struct18 {addr : (x_3).addr, info_write :
        (Bool)'(False), info_hit : (x_6).info_hit, info_way : (x_6).info_way,
        edir_hit : (x_6).edir_hit, edir_way : (x_6).edir_way, edir_slot :
        (x_6).edir_slot, info : (x_6).info, value_write : (Bool)'(False),
        value : unpack(0), may_victim : (x_6).may_victim, reps :
        (x_6).reps});
        Struct18 x_19 = (Struct18 {addr : (x_18).addr, info_write :
        (Bool)'(True), info_hit : (x_18).info_hit, info_way :
        (x_18).info_way, edir_hit : (x_18).edir_hit, edir_way :
        (x_18).edir_way, edir_slot : (x_18).edir_slot, info : Struct11
        {mesi_owned : ((x_18).info).mesi_owned, mesi_status :
        ((x_18).info).mesi_status, mesi_dir_st : (Struct17 {dir_st :
        (Bit#(3))'(3'h3), dir_excl : (Bit#(1))'(1'h0), dir_sharers :
        unpack(0)}).dir_st, mesi_dir_sharers : (((Struct17 {dir_st :
        (Bit#(3))'(3'h3), dir_excl : (Bit#(1))'(1'h0), dir_sharers :
        unpack(0)}).dir_st) == ((Bit#(3))'(3'h2)) ? ((Struct17 {dir_st :
        (Bit#(3))'(3'h3), dir_excl : (Bit#(1))'(1'h0), dir_sharers :
        unpack(0)}).dir_sharers) : (((Bit#(2))'(2'h1)) << ((Struct17 {dir_st
        : (Bit#(3))'(3'h3), dir_excl : (Bit#(1))'(1'h0), dir_sharers :
        unpack(0)}).dir_excl)))}, value_write : (x_18).value_write, value :
        (x_18).value, may_victim : (x_18).may_victim, reps :
        (x_18).reps});
        Struct18 x_20 = (Struct18 {addr : (x_19).addr, info_write :
        (Bool)'(True), info_hit : (x_19).info_hit, info_way :
        (x_19).info_way, edir_hit : (x_19).edir_hit, edir_way :
        (x_19).edir_way, edir_slot : (x_19).edir_slot, info : Struct11
        {mesi_owned : ((x_19).info).mesi_owned, mesi_status :
        (Bit#(3))'(3'h1), mesi_dir_st : ((x_19).info).mesi_dir_st,
        mesi_dir_sharers : ((x_19).info).mesi_dir_sharers}, value_write :
        (x_19).value_write, value : (x_19).value, may_victim :
        (x_19).may_victim, reps :
        (x_19).reps});
        let x_23 = ?;
        if ((x_8).valid) begin
            let x_21 <- victims__00__setVictim(Struct19 {victim_idx :
            (x_8).data, victim_info : (x_20).info, victim_value :
            ((x_20).value_write ? ((x_20).value) : (x_9))});
            x_23 = x_9;
        end else begin
            let x_22 <- cache__00__valueRsLineRq(x_20);
            x_23 = x_22;
        end
        Struct20 x_24 = (Struct20 {enq_type : ((((Bit#(3))'(3'h4))[2:1]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : (((((Bit#(3))'(3'h4))[2:1])
        == ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : ((Bit#(3))'(3'h4))[0:0], enq_msg : Struct1 {id :
        (Bit#(6))'(6'h4), type_ : (Bool)'(True), addr : (x_17).addr, value :
        x_23}});
        let x_25 <- makeEnq_parentChildren00(x_24);
        let x_26 <- releaseMSHR_00(x_4);
    endrule

    rule rule_exec_00_01000;
        $display ("Rule fired: rule_exec_00_01000 at %t", $time);
        let x_0 <- deq_fifoL2E_00();
        Struct6 x_1 = ((x_0).lr_ir_pp);
        Bit#(3) x_2 = ((x_1).ir_msg_from);
        Struct1 x_3 = ((x_1).ir_msg);
        Bit#(4) x_4 = ((x_1).ir_mshr_id);
        Bool x_5 = ((x_1).ir_is_rs_rel);
        when (! (x_5), noAction);
        Struct9 x_6 = ((x_0).lr_ir);
        Struct11 x_7 = ((x_6).info);
        Struct5 x_8 = ((x_1).ir_by_victim);
        Vector#(4, Bit#(64)) x_9 = ((x_0).lr_value);
        let x_10 <- getMSHR_00(x_4);
        let x_11 <- getMSHRRq_00(x_4);
        let x_12 <- getMSHRFirstRs_00(x_4);
        Vector#(4, Bit#(64)) x_13 = (unpack(0));
        Bool x_14 = ((x_7).mesi_owned);
        Bit#(3) x_15 = ((x_7).mesi_status);
        Struct17 x_16 = (Struct17 {dir_st : (((x_7).mesi_dir_st) ==
        ((Bit#(3))'(3'h0)) ? ((Bit#(3))'(3'h1)) : ((x_7).mesi_dir_st)),
        dir_excl : ((((x_7).mesi_dir_sharers)[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(1))'(1'h0)) : (((Bit#(1))'(1'h1)) +
        ((((((x_7).mesi_dir_sharers)[1:1])[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(1))'(1'h0)) : (((Bit#(1))'(1'h1)) + (unpack(0))))))),
        dir_sharers : (x_7).mesi_dir_sharers});
        when ((x_2) == ((Bit#(3))'(3'h0)), noAction);
        when (((x_3).id) == ((Bit#(6))'(6'h2)), noAction);
        when (! ((x_3).type_), noAction);
        when (((x_14) == ((Bool)'(False))) && ((! (((Bit#(3))'(3'h1)) <
        (x_15))) && (! (((Bit#(3))'(3'h2)) < ((x_16).dir_st)))),
        noAction);
        Struct1 x_17 = (x_3);
        Struct18 x_18 = (Struct18 {addr : (x_3).addr, info_write :
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
        let x_21 <- registerUL_00(Struct21 {r_id : x_4, r_ul_rsb :
        (Bool)'(True), r_ul_rsbTo : ((Bit#(3))'(3'h4))[0:0]});
        Struct20 x_22 = (Struct20 {enq_type : ((((Bit#(3))'(3'h0))[2:1]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : (((((Bit#(3))'(3'h0))[2:1])
        == ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : ((Bit#(3))'(3'h0))[0:0], enq_msg : Struct1 {id :
        (Bit#(6))'(6'h2), type_ : (Bool)'(False), addr : (x_17).addr, value :
        unpack(0)}});
        let x_23 <- makeEnq_parentChildren00(x_22);
    endrule

    rule rule_exec_00_03000;
        $display ("Rule fired: rule_exec_00_03000 at %t", $time);
        let x_0 <- deq_fifoL2E_00();
        Struct6 x_1 = ((x_0).lr_ir_pp);
        Bit#(3) x_2 = ((x_1).ir_msg_from);
        Struct1 x_3 = ((x_1).ir_msg);
        Bit#(4) x_4 = ((x_1).ir_mshr_id);
        Bool x_5 = ((x_1).ir_is_rs_rel);
        when (! (x_5), noAction);
        Struct9 x_6 = ((x_0).lr_ir);
        Struct11 x_7 = ((x_6).info);
        Struct5 x_8 = ((x_1).ir_by_victim);
        Vector#(4, Bit#(64)) x_9 = ((x_0).lr_value);
        let x_10 <- getMSHR_00(x_4);
        let x_11 <- getMSHRRq_00(x_4);
        let x_12 <- getMSHRFirstRs_00(x_4);
        Vector#(4, Bit#(64)) x_13 = (unpack(0));
        Bool x_14 = ((x_7).mesi_owned);
        Bit#(3) x_15 = ((x_7).mesi_status);
        Struct17 x_16 = (Struct17 {dir_st : (((x_7).mesi_dir_st) ==
        ((Bit#(3))'(3'h0)) ? ((Bit#(3))'(3'h1)) : ((x_7).mesi_dir_st)),
        dir_excl : ((((x_7).mesi_dir_sharers)[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(1))'(1'h0)) : (((Bit#(1))'(1'h1)) +
        ((((((x_7).mesi_dir_sharers)[1:1])[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(1))'(1'h0)) : (((Bit#(1))'(1'h1)) + (unpack(0))))))),
        dir_sharers : (x_7).mesi_dir_sharers});
        when ((x_2) == ((Bit#(3))'(3'h0)), noAction);
        when (((x_3).id) == ((Bit#(6))'(6'h2)), noAction);
        when (! ((x_3).type_), noAction);
        when (((Bool)'(True)) && (((Bool)'(True)) && ((! (((Bit#(3))'(3'h1))
        < (x_15))) && ((! (((x_16).dir_st) < ((Bit#(3))'(3'h3)))) && (!
        (((Bit#(3))'(3'h4)) < ((x_16).dir_st)))))), noAction);
        Struct1 x_17 = (x_3);
        Struct18 x_18 = (Struct18 {addr : (x_3).addr, info_write :
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
        let x_21 <- registerDL_00(Struct22 {r_id : x_4, r_dl_rss_from :
        (unpack(0)) | (((Bit#(2))'(2'h1)) <<
        (({((Bit#(2))'(2'h1)),((x_16).dir_excl)})[0:0])), r_dl_rsb :
        (Bool)'(True), r_dl_rsbTo : (Bit#(3))'(3'h4)});
        Struct20 x_22 = (Struct20 {enq_type :
        ((({((Bit#(2))'(2'h2)),((x_16).dir_excl)})[2:1]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) :
        (((({((Bit#(2))'(2'h2)),((x_16).dir_excl)})[2:1]) ==
        ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : ({((Bit#(2))'(2'h2)),((x_16).dir_excl)})[0:0], enq_msg :
        Struct1 {id : (Bit#(6))'(6'h5), type_ : (Bool)'(False), addr :
        (x_17).addr, value : unpack(0)}});
        let x_23 <- makeEnq_parentChildren00(x_22);
    endrule

    rule rule_exec_00_10000;
        $display ("Rule fired: rule_exec_00_10000 at %t", $time);
        let x_0 <- deq_fifoL2E_00();
        Struct6 x_1 = ((x_0).lr_ir_pp);
        Bit#(3) x_2 = ((x_1).ir_msg_from);
        Struct1 x_3 = ((x_1).ir_msg);
        Bit#(4) x_4 = ((x_1).ir_mshr_id);
        Bool x_5 = ((x_1).ir_is_rs_rel);
        when (! (x_5), noAction);
        Struct9 x_6 = ((x_0).lr_ir);
        Struct11 x_7 = ((x_6).info);
        Struct5 x_8 = ((x_1).ir_by_victim);
        Vector#(4, Bit#(64)) x_9 = ((x_0).lr_value);
        let x_10 <- getMSHR_00(x_4);
        let x_11 <- getMSHRRq_00(x_4);
        let x_12 <- getMSHRFirstRs_00(x_4);
        Vector#(4, Bit#(64)) x_13 = (unpack(0));
        Bool x_14 = ((x_7).mesi_owned);
        Bit#(3) x_15 = ((x_7).mesi_status);
        Struct17 x_16 = (Struct17 {dir_st : (((x_7).mesi_dir_st) ==
        ((Bit#(3))'(3'h0)) ? ((Bit#(3))'(3'h1)) : ((x_7).mesi_dir_st)),
        dir_excl : ((((x_7).mesi_dir_sharers)[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(1))'(1'h0)) : (((Bit#(1))'(1'h1)) +
        ((((((x_7).mesi_dir_sharers)[1:1])[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(1))'(1'h0)) : (((Bit#(1))'(1'h1)) + (unpack(0))))))),
        dir_sharers : (x_7).mesi_dir_sharers});
        when ((x_2) == ((Bit#(3))'(3'h0)), noAction);
        when (((x_3).id) == ((Bit#(6))'(6'ha)), noAction);
        when (! ((x_3).type_), noAction);
        when ((! ((x_15) < ((Bit#(3))'(3'h3)))) || (((x_15) ==
        ((Bit#(3))'(3'h2))) && (((x_14) == ((Bool)'(True))) &&
        ((((x_16).dir_st) == ((Bit#(3))'(3'h2))) && (((x_16).dir_sharers) ==
        (((Bit#(2))'(2'h1)) << ((Bit#(1))'(1'h0))))))), noAction);
        Struct1 x_17 = (x_3);
        Struct18 x_18 = (Struct18 {addr : (x_3).addr, info_write :
        (Bool)'(False), info_hit : (x_6).info_hit, info_way : (x_6).info_way,
        edir_hit : (x_6).edir_hit, edir_way : (x_6).edir_way, edir_slot :
        (x_6).edir_slot, info : (x_6).info, value_write : (Bool)'(False),
        value : unpack(0), may_victim : (x_6).may_victim, reps :
        (x_6).reps});
        Struct18 x_19 = (Struct18 {addr : (x_18).addr, info_write :
        (Bool)'(True), info_hit : (x_18).info_hit, info_way :
        (x_18).info_way, edir_hit : (x_18).edir_hit, edir_way :
        (x_18).edir_way, edir_slot : (x_18).edir_slot, info : Struct11
        {mesi_owned : ((x_18).info).mesi_owned, mesi_status :
        ((x_18).info).mesi_status, mesi_dir_st : (Struct17 {dir_st :
        (Bit#(3))'(3'h4), dir_excl : (Bit#(1))'(1'h0), dir_sharers :
        unpack(0)}).dir_st, mesi_dir_sharers : (((Struct17 {dir_st :
        (Bit#(3))'(3'h4), dir_excl : (Bit#(1))'(1'h0), dir_sharers :
        unpack(0)}).dir_st) == ((Bit#(3))'(3'h2)) ? ((Struct17 {dir_st :
        (Bit#(3))'(3'h4), dir_excl : (Bit#(1))'(1'h0), dir_sharers :
        unpack(0)}).dir_sharers) : (((Bit#(2))'(2'h1)) << ((Struct17 {dir_st
        : (Bit#(3))'(3'h4), dir_excl : (Bit#(1))'(1'h0), dir_sharers :
        unpack(0)}).dir_excl)))}, value_write : (x_18).value_write, value :
        (x_18).value, may_victim : (x_18).may_victim, reps :
        (x_18).reps});
        Struct18 x_20 = (Struct18 {addr : (x_19).addr, info_write :
        (Bool)'(True), info_hit : (x_19).info_hit, info_way :
        (x_19).info_way, edir_hit : (x_19).edir_hit, edir_way :
        (x_19).edir_way, edir_slot : (x_19).edir_slot, info : Struct11
        {mesi_owned : ((x_19).info).mesi_owned, mesi_status :
        (Bit#(3))'(3'h1), mesi_dir_st : ((x_19).info).mesi_dir_st,
        mesi_dir_sharers : ((x_19).info).mesi_dir_sharers}, value_write :
        (x_19).value_write, value : (x_19).value, may_victim :
        (x_19).may_victim, reps : (x_19).reps});
        Struct18 x_21 = (Struct18 {addr : (x_20).addr, info_write :
        (Bool)'(True), info_hit : (x_20).info_hit, info_way :
        (x_20).info_way, edir_hit : (x_20).edir_hit, edir_way :
        (x_20).edir_way, edir_slot : (x_20).edir_slot, info : Struct11
        {mesi_owned : (Bool)'(False), mesi_status :
        ((x_20).info).mesi_status, mesi_dir_st : ((x_20).info).mesi_dir_st,
        mesi_dir_sharers : ((x_20).info).mesi_dir_sharers}, value_write :
        (x_20).value_write, value : (x_20).value, may_victim :
        (x_20).may_victim, reps :
        (x_20).reps});
        let x_24 = ?;
        if ((x_8).valid) begin
            let x_22 <- victims__00__setVictim(Struct19 {victim_idx :
            (x_8).data, victim_info : (x_21).info, victim_value :
            ((x_21).value_write ? ((x_21).value) : (x_9))});
            x_24 = x_9;
        end else begin
            let x_23 <- cache__00__valueRsLineRq(x_21);
            x_24 = x_23;
        end
        Struct20 x_25 = (Struct20 {enq_type : ((((Bit#(3))'(3'h4))[2:1]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : (((((Bit#(3))'(3'h4))[2:1])
        == ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : ((Bit#(3))'(3'h4))[0:0], enq_msg : Struct1 {id :
        (Bit#(6))'(6'hb), type_ : (Bool)'(True), addr : (x_17).addr, value :
        unpack(0)}});
        let x_26 <- makeEnq_parentChildren00(x_25);
        let x_27 <- releaseMSHR_00(x_4);
    endrule

    rule rule_exec_00_11000;
        $display ("Rule fired: rule_exec_00_11000 at %t", $time);
        let x_0 <- deq_fifoL2E_00();
        Struct6 x_1 = ((x_0).lr_ir_pp);
        Bit#(3) x_2 = ((x_1).ir_msg_from);
        Struct1 x_3 = ((x_1).ir_msg);
        Bit#(4) x_4 = ((x_1).ir_mshr_id);
        Bool x_5 = ((x_1).ir_is_rs_rel);
        when (! (x_5), noAction);
        Struct9 x_6 = ((x_0).lr_ir);
        Struct11 x_7 = ((x_6).info);
        Struct5 x_8 = ((x_1).ir_by_victim);
        Vector#(4, Bit#(64)) x_9 = ((x_0).lr_value);
        let x_10 <- getMSHR_00(x_4);
        let x_11 <- getMSHRRq_00(x_4);
        let x_12 <- getMSHRFirstRs_00(x_4);
        Vector#(4, Bit#(64)) x_13 = (unpack(0));
        Bool x_14 = ((x_7).mesi_owned);
        Bit#(3) x_15 = ((x_7).mesi_status);
        Struct17 x_16 = (Struct17 {dir_st : (((x_7).mesi_dir_st) ==
        ((Bit#(3))'(3'h0)) ? ((Bit#(3))'(3'h1)) : ((x_7).mesi_dir_st)),
        dir_excl : ((((x_7).mesi_dir_sharers)[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(1))'(1'h0)) : (((Bit#(1))'(1'h1)) +
        ((((((x_7).mesi_dir_sharers)[1:1])[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(1))'(1'h0)) : (((Bit#(1))'(1'h1)) + (unpack(0))))))),
        dir_sharers : (x_7).mesi_dir_sharers});
        when ((x_2) == ((Bit#(3))'(3'h0)), noAction);
        when (((x_3).id) == ((Bit#(6))'(6'ha)), noAction);
        when (! ((x_3).type_), noAction);
        when (((x_14) == ((Bool)'(False))) && ((! (((Bit#(3))'(3'h2)) <
        (x_15))) && (! (((Bit#(3))'(3'h2)) < ((x_16).dir_st)))),
        noAction);
        Struct1 x_17 = (x_3);
        Struct18 x_18 = (Struct18 {addr : (x_3).addr, info_write :
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
        let x_21 <- registerUL_00(Struct21 {r_id : x_4, r_ul_rsb :
        (Bool)'(True), r_ul_rsbTo : ((Bit#(3))'(3'h4))[0:0]});
        Struct20 x_22 = (Struct20 {enq_type : ((((Bit#(3))'(3'h0))[2:1]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : (((((Bit#(3))'(3'h0))[2:1])
        == ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : ((Bit#(3))'(3'h0))[0:0], enq_msg : Struct1 {id :
        (Bit#(6))'(6'ha), type_ : (Bool)'(False), addr : (x_17).addr, value :
        unpack(0)}});
        let x_23 <- makeEnq_parentChildren00(x_22);
    endrule

    rule rule_exec_00_14000;
        $display ("Rule fired: rule_exec_00_14000 at %t", $time);
        let x_0 <- deq_fifoL2E_00();
        Struct6 x_1 = ((x_0).lr_ir_pp);
        Bit#(3) x_2 = ((x_1).ir_msg_from);
        Struct1 x_3 = ((x_1).ir_msg);
        Bit#(4) x_4 = ((x_1).ir_mshr_id);
        Bool x_5 = ((x_1).ir_is_rs_rel);
        when (! (x_5), noAction);
        Struct9 x_6 = ((x_0).lr_ir);
        Struct11 x_7 = ((x_6).info);
        Struct5 x_8 = ((x_1).ir_by_victim);
        Vector#(4, Bit#(64)) x_9 = ((x_0).lr_value);
        let x_10 <- getMSHR_00(x_4);
        let x_11 <- getMSHRRq_00(x_4);
        let x_12 <- getMSHRFirstRs_00(x_4);
        Vector#(4, Bit#(64)) x_13 = (unpack(0));
        Bool x_14 = ((x_7).mesi_owned);
        Bit#(3) x_15 = ((x_7).mesi_status);
        Struct17 x_16 = (Struct17 {dir_st : (((x_7).mesi_dir_st) ==
        ((Bit#(3))'(3'h0)) ? ((Bit#(3))'(3'h1)) : ((x_7).mesi_dir_st)),
        dir_excl : ((((x_7).mesi_dir_sharers)[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(1))'(1'h0)) : (((Bit#(1))'(1'h1)) +
        ((((((x_7).mesi_dir_sharers)[1:1])[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(1))'(1'h0)) : (((Bit#(1))'(1'h1)) + (unpack(0))))))),
        dir_sharers : (x_7).mesi_dir_sharers});
        when ((x_2) == ((Bit#(3))'(3'h0)), noAction);
        when (((x_3).id) == ((Bit#(6))'(6'ha)), noAction);
        when (! ((x_3).type_), noAction);
        when (((Bool)'(True)) && (((Bool)'(True)) && ((! (((Bit#(3))'(3'h1))
        < (x_15))) && ((! (((x_16).dir_st) < ((Bit#(3))'(3'h3)))) && (!
        (((Bit#(3))'(3'h4)) < ((x_16).dir_st)))))), noAction);
        Struct1 x_17 = (x_3);
        Struct18 x_18 = (Struct18 {addr : (x_3).addr, info_write :
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
        let x_21 <- registerDL_00(Struct22 {r_id : x_4, r_dl_rss_from :
        (unpack(0)) | (((Bit#(2))'(2'h1)) <<
        (({((Bit#(2))'(2'h1)),((x_16).dir_excl)})[0:0])), r_dl_rsb :
        (Bool)'(True), r_dl_rsbTo : (Bit#(3))'(3'h4)});
        Struct20 x_22 = (Struct20 {enq_type :
        ((({((Bit#(2))'(2'h2)),((x_16).dir_excl)})[2:1]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) :
        (((({((Bit#(2))'(2'h2)),((x_16).dir_excl)})[2:1]) ==
        ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : ({((Bit#(2))'(2'h2)),((x_16).dir_excl)})[0:0], enq_msg :
        Struct1 {id : (Bit#(6))'(6'he), type_ : (Bool)'(False), addr :
        (x_17).addr, value : unpack(0)}});
        let x_23 <- makeEnq_parentChildren00(x_22);
    endrule

    rule rule_exec_00_15000;
        $display ("Rule fired: rule_exec_00_15000 at %t", $time);
        let x_0 <- deq_fifoL2E_00();
        Struct6 x_1 = ((x_0).lr_ir_pp);
        Bit#(3) x_2 = ((x_1).ir_msg_from);
        Struct1 x_3 = ((x_1).ir_msg);
        Bit#(4) x_4 = ((x_1).ir_mshr_id);
        Bool x_5 = ((x_1).ir_is_rs_rel);
        when (! (x_5), noAction);
        Struct9 x_6 = ((x_0).lr_ir);
        Struct11 x_7 = ((x_6).info);
        Struct5 x_8 = ((x_1).ir_by_victim);
        Vector#(4, Bit#(64)) x_9 = ((x_0).lr_value);
        let x_10 <- getMSHR_00(x_4);
        let x_11 <- getMSHRRq_00(x_4);
        let x_12 <- getMSHRFirstRs_00(x_4);
        Vector#(4, Bit#(64)) x_13 = (unpack(0));
        Bool x_14 = ((x_7).mesi_owned);
        Bit#(3) x_15 = ((x_7).mesi_status);
        Struct17 x_16 = (Struct17 {dir_st : (((x_7).mesi_dir_st) ==
        ((Bit#(3))'(3'h0)) ? ((Bit#(3))'(3'h1)) : ((x_7).mesi_dir_st)),
        dir_excl : ((((x_7).mesi_dir_sharers)[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(1))'(1'h0)) : (((Bit#(1))'(1'h1)) +
        ((((((x_7).mesi_dir_sharers)[1:1])[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(1))'(1'h0)) : (((Bit#(1))'(1'h1)) + (unpack(0))))))),
        dir_sharers : (x_7).mesi_dir_sharers});
        when ((x_2) == ((Bit#(3))'(3'h0)), noAction);
        when (((x_3).id) == ((Bit#(6))'(6'ha)), noAction);
        when (! ((x_3).type_), noAction);
        when (((Bool)'(True)) && (((Bool)'(True)) && ((!
        ((((x_16).dir_sharers) & (~(((Bit#(2))'(2'h1)) <<
        ((Bit#(1))'(1'h0))))) == ((Bit#(2))'(2'h0)))) && (((x_14) ==
        ((Bool)'(True))) && ((! (((Bit#(3))'(3'h2)) < (x_15))) &&
        (((x_16).dir_st) == ((Bit#(3))'(3'h2))))))), noAction);
        Struct1 x_17 = (x_3);
        Struct18 x_18 = (Struct18 {addr : (x_3).addr, info_write :
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
        let x_21 <- registerDL_00(Struct22 {r_id : x_4, r_dl_rss_from :
        ((x_16).dir_sharers) & (~(((Bit#(2))'(2'h1)) << ((Bit#(1))'(1'h0)))),
        r_dl_rsb : (Bool)'(True), r_dl_rsbTo : (Bit#(3))'(3'h4)});
        let x_22 <- broadcast_parentChildren00(Struct23 {cs_inds :
        ((x_16).dir_sharers) & (~(((Bit#(2))'(2'h1)) << ((Bit#(1))'(1'h0)))),
        cs_msg : Struct1 {id : (Bit#(6))'(6'hc), type_ : (Bool)'(False), addr
        : (x_17).addr, value : unpack(0)}});
    endrule

    rule rule_exec_00_25000;
        $display ("Rule fired: rule_exec_00_25000 at %t", $time);
        let x_0 <- deq_fifoL2E_00();
        Struct6 x_1 = ((x_0).lr_ir_pp);
        Bit#(3) x_2 = ((x_1).ir_msg_from);
        Struct1 x_3 = ((x_1).ir_msg);
        Bit#(4) x_4 = ((x_1).ir_mshr_id);
        Bool x_5 = ((x_1).ir_is_rs_rel);
        when (! (x_5), noAction);
        Struct9 x_6 = ((x_0).lr_ir);
        Struct11 x_7 = ((x_6).info);
        Struct5 x_8 = ((x_1).ir_by_victim);
        Vector#(4, Bit#(64)) x_9 = ((x_0).lr_value);
        let x_10 <- getMSHR_00(x_4);
        let x_11 <- getMSHRRq_00(x_4);
        let x_12 <- getMSHRFirstRs_00(x_4);
        Vector#(4, Bit#(64)) x_13 = (unpack(0));
        Bool x_14 = ((x_7).mesi_owned);
        Bit#(3) x_15 = ((x_7).mesi_status);
        Struct17 x_16 = (Struct17 {dir_st : (((x_7).mesi_dir_st) ==
        ((Bit#(3))'(3'h0)) ? ((Bit#(3))'(3'h1)) : ((x_7).mesi_dir_st)),
        dir_excl : ((((x_7).mesi_dir_sharers)[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(1))'(1'h0)) : (((Bit#(1))'(1'h1)) +
        ((((((x_7).mesi_dir_sharers)[1:1])[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(1))'(1'h0)) : (((Bit#(1))'(1'h1)) + (unpack(0))))))),
        dir_sharers : (x_7).mesi_dir_sharers});
        when ((x_2) == ((Bit#(3))'(3'h0)), noAction);
        when (((x_3).id) == ((Bit#(6))'(6'h14)), noAction);
        when (! ((x_3).type_), noAction);
        when ((((((x_16).dir_st) == ((Bit#(3))'(3'h4))) && (((x_16).dir_excl)
        == ((Bit#(1))'(1'h0))) ? ((Bit#(3))'(3'h4)) : (((((x_16).dir_st) ==
        ((Bit#(3))'(3'h3))) && (((x_16).dir_excl) == ((Bit#(1))'(1'h0))) ?
        ((Bit#(3))'(3'h3)) : (((((x_16).dir_st) == ((Bit#(3))'(3'h2))) &&
        ((((x_16).dir_sharers) | (((Bit#(2))'(2'h1)) << ((Bit#(1))'(1'h0))))
        == ((x_16).dir_sharers)) ? ((Bit#(3))'(3'h2)) :
        ((Bit#(3))'(3'h1)))))))) == ((Bit#(3))'(3'h1)), noAction);
        Struct1 x_17 = (x_3);
        Struct18 x_18 = (Struct18 {addr : (x_3).addr, info_write :
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
        Struct20 x_21 = (Struct20 {enq_type : ((((Bit#(3))'(3'h4))[2:1]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : (((((Bit#(3))'(3'h4))[2:1])
        == ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : ((Bit#(3))'(3'h4))[0:0], enq_msg : Struct1 {id :
        (Bit#(6))'(6'h16), type_ : (Bool)'(True), addr : (x_17).addr, value :
        unpack(0)}});
        let x_22 <- makeEnq_parentChildren00(x_21);
        let x_23 <- releaseMSHR_00(x_4);
    endrule

    rule rule_exec_00_2600000;
        $display ("Rule fired: rule_exec_00_2600000 at %t", $time);
        let x_0 <- deq_fifoL2E_00();
        Struct6 x_1 = ((x_0).lr_ir_pp);
        Bit#(3) x_2 = ((x_1).ir_msg_from);
        Struct1 x_3 = ((x_1).ir_msg);
        Bit#(4) x_4 = ((x_1).ir_mshr_id);
        Bool x_5 = ((x_1).ir_is_rs_rel);
        when (! (x_5), noAction);
        Struct9 x_6 = ((x_0).lr_ir);
        Struct11 x_7 = ((x_6).info);
        Struct5 x_8 = ((x_1).ir_by_victim);
        Vector#(4, Bit#(64)) x_9 = ((x_0).lr_value);
        let x_10 <- getMSHR_00(x_4);
        let x_11 <- getMSHRRq_00(x_4);
        let x_12 <- getMSHRFirstRs_00(x_4);
        Vector#(4, Bit#(64)) x_13 = (unpack(0));
        Bool x_14 = ((x_7).mesi_owned);
        Bit#(3) x_15 = ((x_7).mesi_status);
        Struct17 x_16 = (Struct17 {dir_st : (((x_7).mesi_dir_st) ==
        ((Bit#(3))'(3'h0)) ? ((Bit#(3))'(3'h1)) : ((x_7).mesi_dir_st)),
        dir_excl : ((((x_7).mesi_dir_sharers)[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(1))'(1'h0)) : (((Bit#(1))'(1'h1)) +
        ((((((x_7).mesi_dir_sharers)[1:1])[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(1))'(1'h0)) : (((Bit#(1))'(1'h1)) + (unpack(0))))))),
        dir_sharers : (x_7).mesi_dir_sharers});
        when ((x_2) == ((Bit#(3))'(3'h0)), noAction);
        when (((x_3).id) == ((Bit#(6))'(6'h14)), noAction);
        when (! ((x_3).type_), noAction);
        when (((x_14) == ((Bool)'(False))) && (((((((x_16).dir_st) ==
        ((Bit#(3))'(3'h4))) && (((x_16).dir_excl) == ((Bit#(1))'(1'h0))) ?
        ((Bit#(3))'(3'h4)) : (((((x_16).dir_st) == ((Bit#(3))'(3'h3))) &&
        (((x_16).dir_excl) == ((Bit#(1))'(1'h0))) ? ((Bit#(3))'(3'h3)) :
        (((((x_16).dir_st) == ((Bit#(3))'(3'h2))) && ((((x_16).dir_sharers) |
        (((Bit#(2))'(2'h1)) << ((Bit#(1))'(1'h0)))) == ((x_16).dir_sharers))
        ? ((Bit#(3))'(3'h2)) : ((Bit#(3))'(3'h1)))))))) ==
        ((Bit#(3))'(3'h2))) && (((x_16).dir_sharers) == (((Bit#(2))'(2'h1))
        << ((Bit#(1))'(1'h0))))), noAction);
        Struct1 x_17 = (x_3);
        Struct18 x_18 = (Struct18 {addr : (x_3).addr, info_write :
        (Bool)'(False), info_hit : (x_6).info_hit, info_way : (x_6).info_way,
        edir_hit : (x_6).edir_hit, edir_way : (x_6).edir_way, edir_slot :
        (x_6).edir_slot, info : (x_6).info, value_write : (Bool)'(False),
        value : unpack(0), may_victim : (x_6).may_victim, reps :
        (x_6).reps});
        Struct18 x_19 = (Struct18 {addr : (x_18).addr, info_write :
        (Bool)'(True), info_hit : (x_18).info_hit, info_way :
        (x_18).info_way, edir_hit : (x_18).edir_hit, edir_way :
        (x_18).edir_way, edir_slot : (x_18).edir_slot, info : Struct11
        {mesi_owned : ((x_18).info).mesi_owned, mesi_status :
        ((x_18).info).mesi_status, mesi_dir_st : (Struct17 {dir_st :
        (Bit#(3))'(3'h1), dir_excl : unpack(0), dir_sharers :
        unpack(0)}).dir_st, mesi_dir_sharers : (((Struct17 {dir_st :
        (Bit#(3))'(3'h1), dir_excl : unpack(0), dir_sharers :
        unpack(0)}).dir_st) == ((Bit#(3))'(3'h2)) ? ((Struct17 {dir_st :
        (Bit#(3))'(3'h1), dir_excl : unpack(0), dir_sharers :
        unpack(0)}).dir_sharers) : (((Bit#(2))'(2'h1)) << ((Struct17 {dir_st
        : (Bit#(3))'(3'h1), dir_excl : unpack(0), dir_sharers :
        unpack(0)}).dir_excl)))}, value_write : (x_18).value_write, value :
        (x_18).value, may_victim : (x_18).may_victim, reps :
        (x_18).reps});
        let x_22 = ?;
        if ((x_8).valid) begin
            let x_20 <- victims__00__setVictim(Struct19 {victim_idx :
            (x_8).data, victim_info : (x_19).info, victim_value :
            ((x_19).value_write ? ((x_19).value) : (x_9))});
            x_22 = x_9;
        end else begin
            let x_21 <- cache__00__valueRsLineRq(x_19);
            x_22 = x_21;
        end
        Struct20 x_23 = (Struct20 {enq_type : ((((Bit#(3))'(3'h4))[2:1]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : (((((Bit#(3))'(3'h4))[2:1])
        == ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : ((Bit#(3))'(3'h4))[0:0], enq_msg : Struct1 {id :
        (Bit#(6))'(6'h16), type_ : (Bool)'(True), addr : (x_17).addr, value :
        unpack(0)}});
        let x_24 <- makeEnq_parentChildren00(x_23);
        let x_25 <- releaseMSHR_00(x_4);
    endrule

    rule rule_exec_00_2601000;
        $display ("Rule fired: rule_exec_00_2601000 at %t", $time);
        let x_0 <- deq_fifoL2E_00();
        Struct6 x_1 = ((x_0).lr_ir_pp);
        Bit#(3) x_2 = ((x_1).ir_msg_from);
        Struct1 x_3 = ((x_1).ir_msg);
        Bit#(4) x_4 = ((x_1).ir_mshr_id);
        Bool x_5 = ((x_1).ir_is_rs_rel);
        when (! (x_5), noAction);
        Struct9 x_6 = ((x_0).lr_ir);
        Struct11 x_7 = ((x_6).info);
        Struct5 x_8 = ((x_1).ir_by_victim);
        Vector#(4, Bit#(64)) x_9 = ((x_0).lr_value);
        let x_10 <- getMSHR_00(x_4);
        let x_11 <- getMSHRRq_00(x_4);
        let x_12 <- getMSHRFirstRs_00(x_4);
        Vector#(4, Bit#(64)) x_13 = (unpack(0));
        Bool x_14 = ((x_7).mesi_owned);
        Bit#(3) x_15 = ((x_7).mesi_status);
        Struct17 x_16 = (Struct17 {dir_st : (((x_7).mesi_dir_st) ==
        ((Bit#(3))'(3'h0)) ? ((Bit#(3))'(3'h1)) : ((x_7).mesi_dir_st)),
        dir_excl : ((((x_7).mesi_dir_sharers)[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(1))'(1'h0)) : (((Bit#(1))'(1'h1)) +
        ((((((x_7).mesi_dir_sharers)[1:1])[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(1))'(1'h0)) : (((Bit#(1))'(1'h1)) + (unpack(0))))))),
        dir_sharers : (x_7).mesi_dir_sharers});
        when ((x_2) == ((Bit#(3))'(3'h0)), noAction);
        when (((x_3).id) == ((Bit#(6))'(6'h14)), noAction);
        when (! ((x_3).type_), noAction);
        when (((x_14) == ((Bool)'(True))) && (((x_15) == ((Bit#(3))'(3'h2)))
        && (((((((x_16).dir_st) == ((Bit#(3))'(3'h4))) && (((x_16).dir_excl)
        == ((Bit#(1))'(1'h0))) ? ((Bit#(3))'(3'h4)) : (((((x_16).dir_st) ==
        ((Bit#(3))'(3'h3))) && (((x_16).dir_excl) == ((Bit#(1))'(1'h0))) ?
        ((Bit#(3))'(3'h3)) : (((((x_16).dir_st) == ((Bit#(3))'(3'h2))) &&
        ((((x_16).dir_sharers) | (((Bit#(2))'(2'h1)) << ((Bit#(1))'(1'h0))))
        == ((x_16).dir_sharers)) ? ((Bit#(3))'(3'h2)) :
        ((Bit#(3))'(3'h1)))))))) == ((Bit#(3))'(3'h2))) &&
        (((x_16).dir_sharers) == (((Bit#(2))'(2'h1)) <<
        ((Bit#(1))'(1'h0)))))), noAction);
        Struct1 x_17 = (x_3);
        Struct18 x_18 = (Struct18 {addr : (x_3).addr, info_write :
        (Bool)'(False), info_hit : (x_6).info_hit, info_way : (x_6).info_way,
        edir_hit : (x_6).edir_hit, edir_way : (x_6).edir_way, edir_slot :
        (x_6).edir_slot, info : (x_6).info, value_write : (Bool)'(False),
        value : unpack(0), may_victim : (x_6).may_victim, reps :
        (x_6).reps});
        Struct18 x_19 = (Struct18 {addr : (x_18).addr, info_write :
        (Bool)'(True), info_hit : (x_18).info_hit, info_way :
        (x_18).info_way, edir_hit : (x_18).edir_hit, edir_way :
        (x_18).edir_way, edir_slot : (x_18).edir_slot, info : Struct11
        {mesi_owned : ((x_18).info).mesi_owned, mesi_status :
        ((x_18).info).mesi_status, mesi_dir_st : (Struct17 {dir_st :
        (Bit#(3))'(3'h1), dir_excl : unpack(0), dir_sharers :
        unpack(0)}).dir_st, mesi_dir_sharers : (((Struct17 {dir_st :
        (Bit#(3))'(3'h1), dir_excl : unpack(0), dir_sharers :
        unpack(0)}).dir_st) == ((Bit#(3))'(3'h2)) ? ((Struct17 {dir_st :
        (Bit#(3))'(3'h1), dir_excl : unpack(0), dir_sharers :
        unpack(0)}).dir_sharers) : (((Bit#(2))'(2'h1)) << ((Struct17 {dir_st
        : (Bit#(3))'(3'h1), dir_excl : unpack(0), dir_sharers :
        unpack(0)}).dir_excl)))}, value_write : (x_18).value_write, value :
        (x_18).value, may_victim : (x_18).may_victim, reps :
        (x_18).reps});
        Struct18 x_20 = (Struct18 {addr : (x_19).addr, info_write :
        (Bool)'(True), info_hit : (x_19).info_hit, info_way :
        (x_19).info_way, edir_hit : (x_19).edir_hit, edir_way :
        (x_19).edir_way, edir_slot : (x_19).edir_slot, info : Struct11
        {mesi_owned : ((x_19).info).mesi_owned, mesi_status :
        (Bit#(3))'(3'h4), mesi_dir_st : ((x_19).info).mesi_dir_st,
        mesi_dir_sharers : ((x_19).info).mesi_dir_sharers}, value_write :
        (x_19).value_write, value : (x_19).value, may_victim :
        (x_19).may_victim, reps :
        (x_19).reps});
        let x_23 = ?;
        if ((x_8).valid) begin
            let x_21 <- victims__00__setVictim(Struct19 {victim_idx :
            (x_8).data, victim_info : (x_20).info, victim_value :
            ((x_20).value_write ? ((x_20).value) : (x_9))});
            x_23 = x_9;
        end else begin
            let x_22 <- cache__00__valueRsLineRq(x_20);
            x_23 = x_22;
        end
        Struct20 x_24 = (Struct20 {enq_type : ((((Bit#(3))'(3'h4))[2:1]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : (((((Bit#(3))'(3'h4))[2:1])
        == ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : ((Bit#(3))'(3'h4))[0:0], enq_msg : Struct1 {id :
        (Bit#(6))'(6'h16), type_ : (Bool)'(True), addr : (x_17).addr, value :
        unpack(0)}});
        let x_25 <- makeEnq_parentChildren00(x_24);
        let x_26 <- releaseMSHR_00(x_4);
    endrule

    rule rule_exec_00_261000;
        $display ("Rule fired: rule_exec_00_261000 at %t", $time);
        let x_0 <- deq_fifoL2E_00();
        Struct6 x_1 = ((x_0).lr_ir_pp);
        Bit#(3) x_2 = ((x_1).ir_msg_from);
        Struct1 x_3 = ((x_1).ir_msg);
        Bit#(4) x_4 = ((x_1).ir_mshr_id);
        Bool x_5 = ((x_1).ir_is_rs_rel);
        when (! (x_5), noAction);
        Struct9 x_6 = ((x_0).lr_ir);
        Struct11 x_7 = ((x_6).info);
        Struct5 x_8 = ((x_1).ir_by_victim);
        Vector#(4, Bit#(64)) x_9 = ((x_0).lr_value);
        let x_10 <- getMSHR_00(x_4);
        let x_11 <- getMSHRRq_00(x_4);
        let x_12 <- getMSHRFirstRs_00(x_4);
        Vector#(4, Bit#(64)) x_13 = (unpack(0));
        Bool x_14 = ((x_7).mesi_owned);
        Bit#(3) x_15 = ((x_7).mesi_status);
        Struct17 x_16 = (Struct17 {dir_st : (((x_7).mesi_dir_st) ==
        ((Bit#(3))'(3'h0)) ? ((Bit#(3))'(3'h1)) : ((x_7).mesi_dir_st)),
        dir_excl : ((((x_7).mesi_dir_sharers)[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(1))'(1'h0)) : (((Bit#(1))'(1'h1)) +
        ((((((x_7).mesi_dir_sharers)[1:1])[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(1))'(1'h0)) : (((Bit#(1))'(1'h1)) + (unpack(0))))))),
        dir_sharers : (x_7).mesi_dir_sharers});
        when ((x_2) == ((Bit#(3))'(3'h0)), noAction);
        when (((x_3).id) == ((Bit#(6))'(6'h14)), noAction);
        when (! ((x_3).type_), noAction);
        when (((((((x_16).dir_st) == ((Bit#(3))'(3'h4))) &&
        (((x_16).dir_excl) == ((Bit#(1))'(1'h0))) ? ((Bit#(3))'(3'h4)) :
        (((((x_16).dir_st) == ((Bit#(3))'(3'h3))) && (((x_16).dir_excl) ==
        ((Bit#(1))'(1'h0))) ? ((Bit#(3))'(3'h3)) : (((((x_16).dir_st) ==
        ((Bit#(3))'(3'h2))) && ((((x_16).dir_sharers) | (((Bit#(2))'(2'h1))
        << ((Bit#(1))'(1'h0)))) == ((x_16).dir_sharers)) ? ((Bit#(3))'(3'h2))
        : ((Bit#(3))'(3'h1)))))))) == ((Bit#(3))'(3'h2))) &&
        (((Bit#(2))'(2'h1)) < ((((((x_16).dir_sharers)[0:0]) ==
        ((Bit#(1))'(1'h1)) ? ((Bit#(2))'(2'h1)) : ((Bit#(2))'(2'h0)))) +
        (((((((x_16).dir_sharers)[1:1])[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(2))'(2'h1)) : ((Bit#(2))'(2'h0)))) + (unpack(0))))),
        noAction);
        Struct1 x_17 = (x_3);
        Struct18 x_18 = (Struct18 {addr : (x_3).addr, info_write :
        (Bool)'(False), info_hit : (x_6).info_hit, info_way : (x_6).info_way,
        edir_hit : (x_6).edir_hit, edir_way : (x_6).edir_way, edir_slot :
        (x_6).edir_slot, info : (x_6).info, value_write : (Bool)'(False),
        value : unpack(0), may_victim : (x_6).may_victim, reps :
        (x_6).reps});
        Struct18 x_19 = (Struct18 {addr : (x_18).addr, info_write :
        (Bool)'(True), info_hit : (x_18).info_hit, info_way :
        (x_18).info_way, edir_hit : (x_18).edir_hit, edir_way :
        (x_18).edir_way, edir_slot : (x_18).edir_slot, info : Struct11
        {mesi_owned : ((x_18).info).mesi_owned, mesi_status :
        ((x_18).info).mesi_status, mesi_dir_st : (Struct17 {dir_st :
        (Bit#(3))'(3'h2), dir_excl : (x_16).dir_excl, dir_sharers :
        ((x_16).dir_sharers) & (~(((Bit#(2))'(2'h1)) <<
        ((Bit#(1))'(1'h0))))}).dir_st, mesi_dir_sharers : (((Struct17 {dir_st
        : (Bit#(3))'(3'h2), dir_excl : (x_16).dir_excl, dir_sharers :
        ((x_16).dir_sharers) & (~(((Bit#(2))'(2'h1)) <<
        ((Bit#(1))'(1'h0))))}).dir_st) == ((Bit#(3))'(3'h2)) ? ((Struct17
        {dir_st : (Bit#(3))'(3'h2), dir_excl : (x_16).dir_excl, dir_sharers :
        ((x_16).dir_sharers) & (~(((Bit#(2))'(2'h1)) <<
        ((Bit#(1))'(1'h0))))}).dir_sharers) : (((Bit#(2))'(2'h1)) <<
        ((Struct17 {dir_st : (Bit#(3))'(3'h2), dir_excl : (x_16).dir_excl,
        dir_sharers : ((x_16).dir_sharers) & (~(((Bit#(2))'(2'h1)) <<
        ((Bit#(1))'(1'h0))))}).dir_excl)))}, value_write :
        (x_18).value_write, value : (x_18).value, may_victim :
        (x_18).may_victim, reps :
        (x_18).reps});
        let x_22 = ?;
        if ((x_8).valid) begin
            let x_20 <- victims__00__setVictim(Struct19 {victim_idx :
            (x_8).data, victim_info : (x_19).info, victim_value :
            ((x_19).value_write ? ((x_19).value) : (x_9))});
            x_22 = x_9;
        end else begin
            let x_21 <- cache__00__valueRsLineRq(x_19);
            x_22 = x_21;
        end
        Struct20 x_23 = (Struct20 {enq_type : ((((Bit#(3))'(3'h4))[2:1]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : (((((Bit#(3))'(3'h4))[2:1])
        == ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : ((Bit#(3))'(3'h4))[0:0], enq_msg : Struct1 {id :
        (Bit#(6))'(6'h16), type_ : (Bool)'(True), addr : (x_17).addr, value :
        unpack(0)}});
        let x_24 <- makeEnq_parentChildren00(x_23);
        let x_25 <- releaseMSHR_00(x_4);
    endrule

    rule rule_exec_00_27000;
        $display ("Rule fired: rule_exec_00_27000 at %t", $time);
        let x_0 <- deq_fifoL2E_00();
        Struct6 x_1 = ((x_0).lr_ir_pp);
        Bit#(3) x_2 = ((x_1).ir_msg_from);
        Struct1 x_3 = ((x_1).ir_msg);
        Bit#(4) x_4 = ((x_1).ir_mshr_id);
        Bool x_5 = ((x_1).ir_is_rs_rel);
        when (! (x_5), noAction);
        Struct9 x_6 = ((x_0).lr_ir);
        Struct11 x_7 = ((x_6).info);
        Struct5 x_8 = ((x_1).ir_by_victim);
        Vector#(4, Bit#(64)) x_9 = ((x_0).lr_value);
        let x_10 <- getMSHR_00(x_4);
        let x_11 <- getMSHRRq_00(x_4);
        let x_12 <- getMSHRFirstRs_00(x_4);
        Vector#(4, Bit#(64)) x_13 = (unpack(0));
        Bool x_14 = ((x_7).mesi_owned);
        Bit#(3) x_15 = ((x_7).mesi_status);
        Struct17 x_16 = (Struct17 {dir_st : (((x_7).mesi_dir_st) ==
        ((Bit#(3))'(3'h0)) ? ((Bit#(3))'(3'h1)) : ((x_7).mesi_dir_st)),
        dir_excl : ((((x_7).mesi_dir_sharers)[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(1))'(1'h0)) : (((Bit#(1))'(1'h1)) +
        ((((((x_7).mesi_dir_sharers)[1:1])[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(1))'(1'h0)) : (((Bit#(1))'(1'h1)) + (unpack(0))))))),
        dir_sharers : (x_7).mesi_dir_sharers});
        when ((x_2) == ((Bit#(3))'(3'h0)), noAction);
        when (((x_3).id) == ((Bit#(6))'(6'h14)), noAction);
        when (! ((x_3).type_), noAction);
        when ((((((x_16).dir_st) == ((Bit#(3))'(3'h4))) && (((x_16).dir_excl)
        == ((Bit#(1))'(1'h0))) ? ((Bit#(3))'(3'h4)) : (((((x_16).dir_st) ==
        ((Bit#(3))'(3'h3))) && (((x_16).dir_excl) == ((Bit#(1))'(1'h0))) ?
        ((Bit#(3))'(3'h3)) : (((((x_16).dir_st) == ((Bit#(3))'(3'h2))) &&
        ((((x_16).dir_sharers) | (((Bit#(2))'(2'h1)) << ((Bit#(1))'(1'h0))))
        == ((x_16).dir_sharers)) ? ((Bit#(3))'(3'h2)) :
        ((Bit#(3))'(3'h1)))))))) == ((Bit#(3))'(3'h3)), noAction);
        Struct1 x_17 = (x_3);
        Struct18 x_18 = (Struct18 {addr : (x_3).addr, info_write :
        (Bool)'(False), info_hit : (x_6).info_hit, info_way : (x_6).info_way,
        edir_hit : (x_6).edir_hit, edir_way : (x_6).edir_way, edir_slot :
        (x_6).edir_slot, info : (x_6).info, value_write : (Bool)'(False),
        value : unpack(0), may_victim : (x_6).may_victim, reps :
        (x_6).reps});
        Struct18 x_19 = (Struct18 {addr : (x_18).addr, info_write :
        (Bool)'(True), info_hit : (x_18).info_hit, info_way :
        (x_18).info_way, edir_hit : (x_18).edir_hit, edir_way :
        (x_18).edir_way, edir_slot : (x_18).edir_slot, info : Struct11
        {mesi_owned : ((x_18).info).mesi_owned, mesi_status :
        ((x_18).info).mesi_status, mesi_dir_st : (Struct17 {dir_st :
        (Bit#(3))'(3'h1), dir_excl : unpack(0), dir_sharers :
        unpack(0)}).dir_st, mesi_dir_sharers : (((Struct17 {dir_st :
        (Bit#(3))'(3'h1), dir_excl : unpack(0), dir_sharers :
        unpack(0)}).dir_st) == ((Bit#(3))'(3'h2)) ? ((Struct17 {dir_st :
        (Bit#(3))'(3'h1), dir_excl : unpack(0), dir_sharers :
        unpack(0)}).dir_sharers) : (((Bit#(2))'(2'h1)) << ((Struct17 {dir_st
        : (Bit#(3))'(3'h1), dir_excl : unpack(0), dir_sharers :
        unpack(0)}).dir_excl)))}, value_write : (x_18).value_write, value :
        (x_18).value, may_victim : (x_18).may_victim, reps :
        (x_18).reps});
        Struct18 x_20 = (Struct18 {addr : (x_19).addr, info_write :
        (Bool)'(True), info_hit : (x_19).info_hit, info_way :
        (x_19).info_way, edir_hit : (x_19).edir_hit, edir_way :
        (x_19).edir_way, edir_slot : (x_19).edir_slot, info : Struct11
        {mesi_owned : ((x_19).info).mesi_owned, mesi_status :
        (Bit#(3))'(3'h3), mesi_dir_st : ((x_19).info).mesi_dir_st,
        mesi_dir_sharers : ((x_19).info).mesi_dir_sharers}, value_write :
        (x_19).value_write, value : (x_19).value, may_victim :
        (x_19).may_victim, reps :
        (x_19).reps});
        let x_23 = ?;
        if ((x_8).valid) begin
            let x_21 <- victims__00__setVictim(Struct19 {victim_idx :
            (x_8).data, victim_info : (x_20).info, victim_value :
            ((x_20).value_write ? ((x_20).value) : (x_9))});
            x_23 = x_9;
        end else begin
            let x_22 <- cache__00__valueRsLineRq(x_20);
            x_23 = x_22;
        end
        Struct20 x_24 = (Struct20 {enq_type : ((((Bit#(3))'(3'h4))[2:1]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : (((((Bit#(3))'(3'h4))[2:1])
        == ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : ((Bit#(3))'(3'h4))[0:0], enq_msg : Struct1 {id :
        (Bit#(6))'(6'h16), type_ : (Bool)'(True), addr : (x_17).addr, value :
        unpack(0)}});
        let x_25 <- makeEnq_parentChildren00(x_24);
        let x_26 <- releaseMSHR_00(x_4);
    endrule

    rule rule_exec_00_28000;
        $display ("Rule fired: rule_exec_00_28000 at %t", $time);
        let x_0 <- deq_fifoL2E_00();
        Struct6 x_1 = ((x_0).lr_ir_pp);
        Bit#(3) x_2 = ((x_1).ir_msg_from);
        Struct1 x_3 = ((x_1).ir_msg);
        Bit#(4) x_4 = ((x_1).ir_mshr_id);
        Bool x_5 = ((x_1).ir_is_rs_rel);
        when (! (x_5), noAction);
        Struct9 x_6 = ((x_0).lr_ir);
        Struct11 x_7 = ((x_6).info);
        Struct5 x_8 = ((x_1).ir_by_victim);
        Vector#(4, Bit#(64)) x_9 = ((x_0).lr_value);
        let x_10 <- getMSHR_00(x_4);
        let x_11 <- getMSHRRq_00(x_4);
        let x_12 <- getMSHRFirstRs_00(x_4);
        Vector#(4, Bit#(64)) x_13 = (unpack(0));
        Bool x_14 = ((x_7).mesi_owned);
        Bit#(3) x_15 = ((x_7).mesi_status);
        Struct17 x_16 = (Struct17 {dir_st : (((x_7).mesi_dir_st) ==
        ((Bit#(3))'(3'h0)) ? ((Bit#(3))'(3'h1)) : ((x_7).mesi_dir_st)),
        dir_excl : ((((x_7).mesi_dir_sharers)[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(1))'(1'h0)) : (((Bit#(1))'(1'h1)) +
        ((((((x_7).mesi_dir_sharers)[1:1])[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(1))'(1'h0)) : (((Bit#(1))'(1'h1)) + (unpack(0))))))),
        dir_sharers : (x_7).mesi_dir_sharers});
        when ((x_2) == ((Bit#(3))'(3'h0)), noAction);
        when (((x_3).id) == ((Bit#(6))'(6'h15)), noAction);
        when (! ((x_3).type_), noAction);
        when ((((((x_16).dir_st) == ((Bit#(3))'(3'h4))) && (((x_16).dir_excl)
        == ((Bit#(1))'(1'h0))) ? ((Bit#(3))'(3'h4)) : (((((x_16).dir_st) ==
        ((Bit#(3))'(3'h3))) && (((x_16).dir_excl) == ((Bit#(1))'(1'h0))) ?
        ((Bit#(3))'(3'h3)) : (((((x_16).dir_st) == ((Bit#(3))'(3'h2))) &&
        ((((x_16).dir_sharers) | (((Bit#(2))'(2'h1)) << ((Bit#(1))'(1'h0))))
        == ((x_16).dir_sharers)) ? ((Bit#(3))'(3'h2)) :
        ((Bit#(3))'(3'h1)))))))) == ((Bit#(3))'(3'h1)), noAction);
        Struct1 x_17 = (x_3);
        Struct18 x_18 = (Struct18 {addr : (x_3).addr, info_write :
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
        Struct20 x_21 = (Struct20 {enq_type : ((((Bit#(3))'(3'h4))[2:1]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : (((((Bit#(3))'(3'h4))[2:1])
        == ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : ((Bit#(3))'(3'h4))[0:0], enq_msg : Struct1 {id :
        (Bit#(6))'(6'h16), type_ : (Bool)'(True), addr : (x_17).addr, value :
        unpack(0)}});
        let x_22 <- makeEnq_parentChildren00(x_21);
        let x_23 <- releaseMSHR_00(x_4);
    endrule

    rule rule_exec_00_290000;
        $display ("Rule fired: rule_exec_00_290000 at %t", $time);
        let x_0 <- deq_fifoL2E_00();
        Struct6 x_1 = ((x_0).lr_ir_pp);
        Bit#(3) x_2 = ((x_1).ir_msg_from);
        Struct1 x_3 = ((x_1).ir_msg);
        Bit#(4) x_4 = ((x_1).ir_mshr_id);
        Bool x_5 = ((x_1).ir_is_rs_rel);
        when (! (x_5), noAction);
        Struct9 x_6 = ((x_0).lr_ir);
        Struct11 x_7 = ((x_6).info);
        Struct5 x_8 = ((x_1).ir_by_victim);
        Vector#(4, Bit#(64)) x_9 = ((x_0).lr_value);
        let x_10 <- getMSHR_00(x_4);
        let x_11 <- getMSHRRq_00(x_4);
        let x_12 <- getMSHRFirstRs_00(x_4);
        Vector#(4, Bit#(64)) x_13 = (unpack(0));
        Bool x_14 = ((x_7).mesi_owned);
        Bit#(3) x_15 = ((x_7).mesi_status);
        Struct17 x_16 = (Struct17 {dir_st : (((x_7).mesi_dir_st) ==
        ((Bit#(3))'(3'h0)) ? ((Bit#(3))'(3'h1)) : ((x_7).mesi_dir_st)),
        dir_excl : ((((x_7).mesi_dir_sharers)[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(1))'(1'h0)) : (((Bit#(1))'(1'h1)) +
        ((((((x_7).mesi_dir_sharers)[1:1])[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(1))'(1'h0)) : (((Bit#(1))'(1'h1)) + (unpack(0))))))),
        dir_sharers : (x_7).mesi_dir_sharers});
        when ((x_2) == ((Bit#(3))'(3'h0)), noAction);
        when (((x_3).id) == ((Bit#(6))'(6'h15)), noAction);
        when (! ((x_3).type_), noAction);
        when (((x_14) == ((Bool)'(False))) && (((((((x_16).dir_st) ==
        ((Bit#(3))'(3'h4))) && (((x_16).dir_excl) == ((Bit#(1))'(1'h0))) ?
        ((Bit#(3))'(3'h4)) : (((((x_16).dir_st) == ((Bit#(3))'(3'h3))) &&
        (((x_16).dir_excl) == ((Bit#(1))'(1'h0))) ? ((Bit#(3))'(3'h3)) :
        (((((x_16).dir_st) == ((Bit#(3))'(3'h2))) && ((((x_16).dir_sharers) |
        (((Bit#(2))'(2'h1)) << ((Bit#(1))'(1'h0)))) == ((x_16).dir_sharers))
        ? ((Bit#(3))'(3'h2)) : ((Bit#(3))'(3'h1)))))))) ==
        ((Bit#(3))'(3'h2))) && (((x_16).dir_sharers) == (((Bit#(2))'(2'h1))
        << ((Bit#(1))'(1'h0))))), noAction);
        Struct1 x_17 = (x_3);
        Struct18 x_18 = (Struct18 {addr : (x_3).addr, info_write :
        (Bool)'(False), info_hit : (x_6).info_hit, info_way : (x_6).info_way,
        edir_hit : (x_6).edir_hit, edir_way : (x_6).edir_way, edir_slot :
        (x_6).edir_slot, info : (x_6).info, value_write : (Bool)'(False),
        value : unpack(0), may_victim : (x_6).may_victim, reps :
        (x_6).reps});
        Struct18 x_19 = (Struct18 {addr : (x_18).addr, info_write :
        (Bool)'(True), info_hit : (x_18).info_hit, info_way :
        (x_18).info_way, edir_hit : (x_18).edir_hit, edir_way :
        (x_18).edir_way, edir_slot : (x_18).edir_slot, info : Struct11
        {mesi_owned : ((x_18).info).mesi_owned, mesi_status :
        ((x_18).info).mesi_status, mesi_dir_st : (Struct17 {dir_st :
        (Bit#(3))'(3'h1), dir_excl : unpack(0), dir_sharers :
        unpack(0)}).dir_st, mesi_dir_sharers : (((Struct17 {dir_st :
        (Bit#(3))'(3'h1), dir_excl : unpack(0), dir_sharers :
        unpack(0)}).dir_st) == ((Bit#(3))'(3'h2)) ? ((Struct17 {dir_st :
        (Bit#(3))'(3'h1), dir_excl : unpack(0), dir_sharers :
        unpack(0)}).dir_sharers) : (((Bit#(2))'(2'h1)) << ((Struct17 {dir_st
        : (Bit#(3))'(3'h1), dir_excl : unpack(0), dir_sharers :
        unpack(0)}).dir_excl)))}, value_write : (x_18).value_write, value :
        (x_18).value, may_victim : (x_18).may_victim, reps :
        (x_18).reps});
        let x_22 = ?;
        if ((x_8).valid) begin
            let x_20 <- victims__00__setVictim(Struct19 {victim_idx :
            (x_8).data, victim_info : (x_19).info, victim_value :
            ((x_19).value_write ? ((x_19).value) : (x_9))});
            x_22 = x_9;
        end else begin
            let x_21 <- cache__00__valueRsLineRq(x_19);
            x_22 = x_21;
        end
        Struct20 x_23 = (Struct20 {enq_type : ((((Bit#(3))'(3'h4))[2:1]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : (((((Bit#(3))'(3'h4))[2:1])
        == ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : ((Bit#(3))'(3'h4))[0:0], enq_msg : Struct1 {id :
        (Bit#(6))'(6'h16), type_ : (Bool)'(True), addr : (x_17).addr, value :
        unpack(0)}});
        let x_24 <- makeEnq_parentChildren00(x_23);
        let x_25 <- releaseMSHR_00(x_4);
    endrule

    rule rule_exec_00_291000;
        $display ("Rule fired: rule_exec_00_291000 at %t", $time);
        let x_0 <- deq_fifoL2E_00();
        Struct6 x_1 = ((x_0).lr_ir_pp);
        Bit#(3) x_2 = ((x_1).ir_msg_from);
        Struct1 x_3 = ((x_1).ir_msg);
        Bit#(4) x_4 = ((x_1).ir_mshr_id);
        Bool x_5 = ((x_1).ir_is_rs_rel);
        when (! (x_5), noAction);
        Struct9 x_6 = ((x_0).lr_ir);
        Struct11 x_7 = ((x_6).info);
        Struct5 x_8 = ((x_1).ir_by_victim);
        Vector#(4, Bit#(64)) x_9 = ((x_0).lr_value);
        let x_10 <- getMSHR_00(x_4);
        let x_11 <- getMSHRRq_00(x_4);
        let x_12 <- getMSHRFirstRs_00(x_4);
        Vector#(4, Bit#(64)) x_13 = (unpack(0));
        Bool x_14 = ((x_7).mesi_owned);
        Bit#(3) x_15 = ((x_7).mesi_status);
        Struct17 x_16 = (Struct17 {dir_st : (((x_7).mesi_dir_st) ==
        ((Bit#(3))'(3'h0)) ? ((Bit#(3))'(3'h1)) : ((x_7).mesi_dir_st)),
        dir_excl : ((((x_7).mesi_dir_sharers)[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(1))'(1'h0)) : (((Bit#(1))'(1'h1)) +
        ((((((x_7).mesi_dir_sharers)[1:1])[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(1))'(1'h0)) : (((Bit#(1))'(1'h1)) + (unpack(0))))))),
        dir_sharers : (x_7).mesi_dir_sharers});
        when ((x_2) == ((Bit#(3))'(3'h0)), noAction);
        when (((x_3).id) == ((Bit#(6))'(6'h15)), noAction);
        when (! ((x_3).type_), noAction);
        when (((((((x_16).dir_st) == ((Bit#(3))'(3'h4))) &&
        (((x_16).dir_excl) == ((Bit#(1))'(1'h0))) ? ((Bit#(3))'(3'h4)) :
        (((((x_16).dir_st) == ((Bit#(3))'(3'h3))) && (((x_16).dir_excl) ==
        ((Bit#(1))'(1'h0))) ? ((Bit#(3))'(3'h3)) : (((((x_16).dir_st) ==
        ((Bit#(3))'(3'h2))) && ((((x_16).dir_sharers) | (((Bit#(2))'(2'h1))
        << ((Bit#(1))'(1'h0)))) == ((x_16).dir_sharers)) ? ((Bit#(3))'(3'h2))
        : ((Bit#(3))'(3'h1)))))))) == ((Bit#(3))'(3'h2))) &&
        (((Bit#(2))'(2'h1)) < ((((((x_16).dir_sharers)[0:0]) ==
        ((Bit#(1))'(1'h1)) ? ((Bit#(2))'(2'h1)) : ((Bit#(2))'(2'h0)))) +
        (((((((x_16).dir_sharers)[1:1])[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(2))'(2'h1)) : ((Bit#(2))'(2'h0)))) + (unpack(0))))),
        noAction);
        Struct1 x_17 = (x_3);
        Struct18 x_18 = (Struct18 {addr : (x_3).addr, info_write :
        (Bool)'(False), info_hit : (x_6).info_hit, info_way : (x_6).info_way,
        edir_hit : (x_6).edir_hit, edir_way : (x_6).edir_way, edir_slot :
        (x_6).edir_slot, info : (x_6).info, value_write : (Bool)'(False),
        value : unpack(0), may_victim : (x_6).may_victim, reps :
        (x_6).reps});
        Struct18 x_19 = (Struct18 {addr : (x_18).addr, info_write :
        (Bool)'(True), info_hit : (x_18).info_hit, info_way :
        (x_18).info_way, edir_hit : (x_18).edir_hit, edir_way :
        (x_18).edir_way, edir_slot : (x_18).edir_slot, info : Struct11
        {mesi_owned : ((x_18).info).mesi_owned, mesi_status :
        ((x_18).info).mesi_status, mesi_dir_st : (Struct17 {dir_st :
        (Bit#(3))'(3'h2), dir_excl : (x_16).dir_excl, dir_sharers :
        ((x_16).dir_sharers) & (~(((Bit#(2))'(2'h1)) <<
        ((Bit#(1))'(1'h0))))}).dir_st, mesi_dir_sharers : (((Struct17 {dir_st
        : (Bit#(3))'(3'h2), dir_excl : (x_16).dir_excl, dir_sharers :
        ((x_16).dir_sharers) & (~(((Bit#(2))'(2'h1)) <<
        ((Bit#(1))'(1'h0))))}).dir_st) == ((Bit#(3))'(3'h2)) ? ((Struct17
        {dir_st : (Bit#(3))'(3'h2), dir_excl : (x_16).dir_excl, dir_sharers :
        ((x_16).dir_sharers) & (~(((Bit#(2))'(2'h1)) <<
        ((Bit#(1))'(1'h0))))}).dir_sharers) : (((Bit#(2))'(2'h1)) <<
        ((Struct17 {dir_st : (Bit#(3))'(3'h2), dir_excl : (x_16).dir_excl,
        dir_sharers : ((x_16).dir_sharers) & (~(((Bit#(2))'(2'h1)) <<
        ((Bit#(1))'(1'h0))))}).dir_excl)))}, value_write :
        (x_18).value_write, value : (x_18).value, may_victim :
        (x_18).may_victim, reps :
        (x_18).reps});
        let x_22 = ?;
        if ((x_8).valid) begin
            let x_20 <- victims__00__setVictim(Struct19 {victim_idx :
            (x_8).data, victim_info : (x_19).info, victim_value :
            ((x_19).value_write ? ((x_19).value) : (x_9))});
            x_22 = x_9;
        end else begin
            let x_21 <- cache__00__valueRsLineRq(x_19);
            x_22 = x_21;
        end
        Struct20 x_23 = (Struct20 {enq_type : ((((Bit#(3))'(3'h4))[2:1]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : (((((Bit#(3))'(3'h4))[2:1])
        == ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : ((Bit#(3))'(3'h4))[0:0], enq_msg : Struct1 {id :
        (Bit#(6))'(6'h16), type_ : (Bool)'(True), addr : (x_17).addr, value :
        unpack(0)}});
        let x_24 <- makeEnq_parentChildren00(x_23);
        let x_25 <- releaseMSHR_00(x_4);
    endrule

    rule rule_exec_00_210000;
        $display ("Rule fired: rule_exec_00_210000 at %t", $time);
        let x_0 <- deq_fifoL2E_00();
        Struct6 x_1 = ((x_0).lr_ir_pp);
        Bit#(3) x_2 = ((x_1).ir_msg_from);
        Struct1 x_3 = ((x_1).ir_msg);
        Bit#(4) x_4 = ((x_1).ir_mshr_id);
        Bool x_5 = ((x_1).ir_is_rs_rel);
        when (! (x_5), noAction);
        Struct9 x_6 = ((x_0).lr_ir);
        Struct11 x_7 = ((x_6).info);
        Struct5 x_8 = ((x_1).ir_by_victim);
        Vector#(4, Bit#(64)) x_9 = ((x_0).lr_value);
        let x_10 <- getMSHR_00(x_4);
        let x_11 <- getMSHRRq_00(x_4);
        let x_12 <- getMSHRFirstRs_00(x_4);
        Vector#(4, Bit#(64)) x_13 = (unpack(0));
        Bool x_14 = ((x_7).mesi_owned);
        Bit#(3) x_15 = ((x_7).mesi_status);
        Struct17 x_16 = (Struct17 {dir_st : (((x_7).mesi_dir_st) ==
        ((Bit#(3))'(3'h0)) ? ((Bit#(3))'(3'h1)) : ((x_7).mesi_dir_st)),
        dir_excl : ((((x_7).mesi_dir_sharers)[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(1))'(1'h0)) : (((Bit#(1))'(1'h1)) +
        ((((((x_7).mesi_dir_sharers)[1:1])[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(1))'(1'h0)) : (((Bit#(1))'(1'h1)) + (unpack(0))))))),
        dir_sharers : (x_7).mesi_dir_sharers});
        when ((x_2) == ((Bit#(3))'(3'h0)), noAction);
        when (((x_3).id) == ((Bit#(6))'(6'h15)), noAction);
        when (! ((x_3).type_), noAction);
        when (((x_14) == ((Bool)'(True))) && (((x_15) == ((Bit#(3))'(3'h2)))
        && (((((((x_16).dir_st) == ((Bit#(3))'(3'h4))) && (((x_16).dir_excl)
        == ((Bit#(1))'(1'h0))) ? ((Bit#(3))'(3'h4)) : (((((x_16).dir_st) ==
        ((Bit#(3))'(3'h3))) && (((x_16).dir_excl) == ((Bit#(1))'(1'h0))) ?
        ((Bit#(3))'(3'h3)) : (((((x_16).dir_st) == ((Bit#(3))'(3'h2))) &&
        ((((x_16).dir_sharers) | (((Bit#(2))'(2'h1)) << ((Bit#(1))'(1'h0))))
        == ((x_16).dir_sharers)) ? ((Bit#(3))'(3'h2)) :
        ((Bit#(3))'(3'h1)))))))) == ((Bit#(3))'(3'h2))) &&
        (((x_16).dir_sharers) == (((Bit#(2))'(2'h1)) <<
        ((Bit#(1))'(1'h0)))))), noAction);
        Struct1 x_17 = (x_3);
        Struct18 x_18 = (Struct18 {addr : (x_3).addr, info_write :
        (Bool)'(False), info_hit : (x_6).info_hit, info_way : (x_6).info_way,
        edir_hit : (x_6).edir_hit, edir_way : (x_6).edir_way, edir_slot :
        (x_6).edir_slot, info : (x_6).info, value_write : (Bool)'(False),
        value : unpack(0), may_victim : (x_6).may_victim, reps :
        (x_6).reps});
        Struct18 x_19 = (Struct18 {addr : (x_18).addr, info_write :
        (Bool)'(True), info_hit : (x_18).info_hit, info_way :
        (x_18).info_way, edir_hit : (x_18).edir_hit, edir_way :
        (x_18).edir_way, edir_slot : (x_18).edir_slot, info : Struct11
        {mesi_owned : ((x_18).info).mesi_owned, mesi_status :
        ((x_18).info).mesi_status, mesi_dir_st : (Struct17 {dir_st :
        (Bit#(3))'(3'h1), dir_excl : unpack(0), dir_sharers :
        unpack(0)}).dir_st, mesi_dir_sharers : (((Struct17 {dir_st :
        (Bit#(3))'(3'h1), dir_excl : unpack(0), dir_sharers :
        unpack(0)}).dir_st) == ((Bit#(3))'(3'h2)) ? ((Struct17 {dir_st :
        (Bit#(3))'(3'h1), dir_excl : unpack(0), dir_sharers :
        unpack(0)}).dir_sharers) : (((Bit#(2))'(2'h1)) << ((Struct17 {dir_st
        : (Bit#(3))'(3'h1), dir_excl : unpack(0), dir_sharers :
        unpack(0)}).dir_excl)))}, value_write : (x_18).value_write, value :
        (x_18).value, may_victim : (x_18).may_victim, reps :
        (x_18).reps});
        Struct18 x_20 = (Struct18 {addr : (x_19).addr, info_write :
        (Bool)'(True), info_hit : (x_19).info_hit, info_way :
        (x_19).info_way, edir_hit : (x_19).edir_hit, edir_way :
        (x_19).edir_way, edir_slot : (x_19).edir_slot, info : Struct11
        {mesi_owned : ((x_19).info).mesi_owned, mesi_status :
        (Bit#(3))'(3'h4), mesi_dir_st : ((x_19).info).mesi_dir_st,
        mesi_dir_sharers : ((x_19).info).mesi_dir_sharers}, value_write :
        (x_19).value_write, value : (x_19).value, may_victim :
        (x_19).may_victim, reps :
        (x_19).reps});
        let x_23 = ?;
        if ((x_8).valid) begin
            let x_21 <- victims__00__setVictim(Struct19 {victim_idx :
            (x_8).data, victim_info : (x_20).info, victim_value :
            ((x_20).value_write ? ((x_20).value) : (x_9))});
            x_23 = x_9;
        end else begin
            let x_22 <- cache__00__valueRsLineRq(x_20);
            x_23 = x_22;
        end
        Struct20 x_24 = (Struct20 {enq_type : ((((Bit#(3))'(3'h4))[2:1]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : (((((Bit#(3))'(3'h4))[2:1])
        == ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : ((Bit#(3))'(3'h4))[0:0], enq_msg : Struct1 {id :
        (Bit#(6))'(6'h16), type_ : (Bool)'(True), addr : (x_17).addr, value :
        unpack(0)}});
        let x_25 <- makeEnq_parentChildren00(x_24);
        let x_26 <- releaseMSHR_00(x_4);
    endrule

    rule rule_exec_00_211000;
        $display ("Rule fired: rule_exec_00_211000 at %t", $time);
        let x_0 <- deq_fifoL2E_00();
        Struct6 x_1 = ((x_0).lr_ir_pp);
        Bit#(3) x_2 = ((x_1).ir_msg_from);
        Struct1 x_3 = ((x_1).ir_msg);
        Bit#(4) x_4 = ((x_1).ir_mshr_id);
        Bool x_5 = ((x_1).ir_is_rs_rel);
        when (! (x_5), noAction);
        Struct9 x_6 = ((x_0).lr_ir);
        Struct11 x_7 = ((x_6).info);
        Struct5 x_8 = ((x_1).ir_by_victim);
        Vector#(4, Bit#(64)) x_9 = ((x_0).lr_value);
        let x_10 <- getMSHR_00(x_4);
        let x_11 <- getMSHRRq_00(x_4);
        let x_12 <- getMSHRFirstRs_00(x_4);
        Vector#(4, Bit#(64)) x_13 = (unpack(0));
        Bool x_14 = ((x_7).mesi_owned);
        Bit#(3) x_15 = ((x_7).mesi_status);
        Struct17 x_16 = (Struct17 {dir_st : (((x_7).mesi_dir_st) ==
        ((Bit#(3))'(3'h0)) ? ((Bit#(3))'(3'h1)) : ((x_7).mesi_dir_st)),
        dir_excl : ((((x_7).mesi_dir_sharers)[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(1))'(1'h0)) : (((Bit#(1))'(1'h1)) +
        ((((((x_7).mesi_dir_sharers)[1:1])[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(1))'(1'h0)) : (((Bit#(1))'(1'h1)) + (unpack(0))))))),
        dir_sharers : (x_7).mesi_dir_sharers});
        when ((x_2) == ((Bit#(3))'(3'h0)), noAction);
        when (((x_3).id) == ((Bit#(6))'(6'h15)), noAction);
        when (! ((x_3).type_), noAction);
        when (! ((((((x_16).dir_st) == ((Bit#(3))'(3'h4))) &&
        (((x_16).dir_excl) == ((Bit#(1))'(1'h0))) ? ((Bit#(3))'(3'h4)) :
        (((((x_16).dir_st) == ((Bit#(3))'(3'h3))) && (((x_16).dir_excl) ==
        ((Bit#(1))'(1'h0))) ? ((Bit#(3))'(3'h3)) : (((((x_16).dir_st) ==
        ((Bit#(3))'(3'h2))) && ((((x_16).dir_sharers) | (((Bit#(2))'(2'h1))
        << ((Bit#(1))'(1'h0)))) == ((x_16).dir_sharers)) ? ((Bit#(3))'(3'h2))
        : ((Bit#(3))'(3'h1)))))))) < ((Bit#(3))'(3'h3))), noAction);
        Struct1 x_17 = (x_3);
        Struct18 x_18 = (Struct18 {addr : (x_3).addr, info_write :
        (Bool)'(False), info_hit : (x_6).info_hit, info_way : (x_6).info_way,
        edir_hit : (x_6).edir_hit, edir_way : (x_6).edir_way, edir_slot :
        (x_6).edir_slot, info : (x_6).info, value_write : (Bool)'(False),
        value : unpack(0), may_victim : (x_6).may_victim, reps :
        (x_6).reps});
        Struct18 x_19 = (Struct18 {addr : (x_18).addr, info_write :
        (x_18).info_write, info_hit : (x_18).info_hit, info_way :
        (x_18).info_way, edir_hit : (x_18).edir_hit, edir_way :
        (x_18).edir_way, edir_slot : (x_18).edir_slot, info : (x_18).info,
        value_write : (Bool)'(True), value : (x_17).value, may_victim :
        (x_18).may_victim, reps : (x_18).reps});
        Struct18 x_20 = (Struct18 {addr : (x_19).addr, info_write :
        (Bool)'(True), info_hit : (x_19).info_hit, info_way :
        (x_19).info_way, edir_hit : (x_19).edir_hit, edir_way :
        (x_19).edir_way, edir_slot : (x_19).edir_slot, info : Struct11
        {mesi_owned : ((x_19).info).mesi_owned, mesi_status :
        (Bit#(3))'(3'h4), mesi_dir_st : ((x_19).info).mesi_dir_st,
        mesi_dir_sharers : ((x_19).info).mesi_dir_sharers}, value_write :
        (x_19).value_write, value : (x_19).value, may_victim :
        (x_19).may_victim, reps : (x_19).reps});
        Struct18 x_21 = (Struct18 {addr : (x_20).addr, info_write :
        (Bool)'(True), info_hit : (x_20).info_hit, info_way :
        (x_20).info_way, edir_hit : (x_20).edir_hit, edir_way :
        (x_20).edir_way, edir_slot : (x_20).edir_slot, info : Struct11
        {mesi_owned : (Bool)'(True), mesi_status : ((x_20).info).mesi_status,
        mesi_dir_st : ((x_20).info).mesi_dir_st, mesi_dir_sharers :
        ((x_20).info).mesi_dir_sharers}, value_write : (x_20).value_write,
        value : (x_20).value, may_victim : (x_20).may_victim, reps :
        (x_20).reps});
        Struct18 x_22 = (Struct18 {addr : (x_21).addr, info_write :
        (Bool)'(True), info_hit : (x_21).info_hit, info_way :
        (x_21).info_way, edir_hit : (x_21).edir_hit, edir_way :
        (x_21).edir_way, edir_slot : (x_21).edir_slot, info : Struct11
        {mesi_owned : ((x_21).info).mesi_owned, mesi_status :
        ((x_21).info).mesi_status, mesi_dir_st : (Struct17 {dir_st :
        (Bit#(3))'(3'h1), dir_excl : unpack(0), dir_sharers :
        unpack(0)}).dir_st, mesi_dir_sharers : (((Struct17 {dir_st :
        (Bit#(3))'(3'h1), dir_excl : unpack(0), dir_sharers :
        unpack(0)}).dir_st) == ((Bit#(3))'(3'h2)) ? ((Struct17 {dir_st :
        (Bit#(3))'(3'h1), dir_excl : unpack(0), dir_sharers :
        unpack(0)}).dir_sharers) : (((Bit#(2))'(2'h1)) << ((Struct17 {dir_st
        : (Bit#(3))'(3'h1), dir_excl : unpack(0), dir_sharers :
        unpack(0)}).dir_excl)))}, value_write : (x_21).value_write, value :
        (x_21).value, may_victim : (x_21).may_victim, reps :
        (x_21).reps});
        let x_25 = ?;
        if ((x_8).valid) begin
            let x_23 <- victims__00__setVictim(Struct19 {victim_idx :
            (x_8).data, victim_info : (x_22).info, victim_value :
            ((x_22).value_write ? ((x_22).value) : (x_9))});
            x_25 = x_9;
        end else begin
            let x_24 <- cache__00__valueRsLineRq(x_22);
            x_25 = x_24;
        end
        Struct20 x_26 = (Struct20 {enq_type : ((((Bit#(3))'(3'h4))[2:1]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : (((((Bit#(3))'(3'h4))[2:1])
        == ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : ((Bit#(3))'(3'h4))[0:0], enq_msg : Struct1 {id :
        (Bit#(6))'(6'h16), type_ : (Bool)'(True), addr : (x_17).addr, value :
        unpack(0)}});
        let x_27 <- makeEnq_parentChildren00(x_26);
        let x_28 <- releaseMSHR_00(x_4);
    endrule

    rule rule_exec_00_000001;
        $display ("Rule fired: rule_exec_00_000001 at %t", $time);
        let x_0 <- deq_fifoL2E_00();
        Struct6 x_1 = ((x_0).lr_ir_pp);
        Bit#(3) x_2 = ((x_1).ir_msg_from);
        Struct1 x_3 = ((x_1).ir_msg);
        Bit#(4) x_4 = ((x_1).ir_mshr_id);
        Bool x_5 = ((x_1).ir_is_rs_rel);
        when (! (x_5), noAction);
        Struct9 x_6 = ((x_0).lr_ir);
        Struct11 x_7 = ((x_6).info);
        Struct5 x_8 = ((x_1).ir_by_victim);
        Vector#(4, Bit#(64)) x_9 = ((x_0).lr_value);
        let x_10 <- getMSHR_00(x_4);
        let x_11 <- getMSHRRq_00(x_4);
        let x_12 <- getMSHRFirstRs_00(x_4);
        Vector#(4, Bit#(64)) x_13 = (unpack(0));
        Bool x_14 = ((x_7).mesi_owned);
        Bit#(3) x_15 = ((x_7).mesi_status);
        Struct17 x_16 = (Struct17 {dir_st : (((x_7).mesi_dir_st) ==
        ((Bit#(3))'(3'h0)) ? ((Bit#(3))'(3'h1)) : ((x_7).mesi_dir_st)),
        dir_excl : ((((x_7).mesi_dir_sharers)[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(1))'(1'h0)) : (((Bit#(1))'(1'h1)) +
        ((((((x_7).mesi_dir_sharers)[1:1])[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(1))'(1'h0)) : (((Bit#(1))'(1'h1)) + (unpack(0))))))),
        dir_sharers : (x_7).mesi_dir_sharers});
        when ((x_2) == ((Bit#(3))'(3'h1)), noAction);
        when (((x_3).id) == ((Bit#(6))'(6'h2)), noAction);
        when (! ((x_3).type_), noAction);
        when ((! (((Bit#(3))'(3'h2)) < ((x_16).dir_st))) && ((x_15) ==
        ((Bit#(3))'(3'h2))), noAction);
        Struct1 x_17 = (x_3);
        Struct18 x_18 = (Struct18 {addr : (x_3).addr, info_write :
        (Bool)'(False), info_hit : (x_6).info_hit, info_way : (x_6).info_way,
        edir_hit : (x_6).edir_hit, edir_way : (x_6).edir_way, edir_slot :
        (x_6).edir_slot, info : (x_6).info, value_write : (Bool)'(False),
        value : unpack(0), may_victim : (x_6).may_victim, reps :
        (x_6).reps});
        Struct18 x_19 = (Struct18 {addr : (x_18).addr, info_write :
        (Bool)'(True), info_hit : (x_18).info_hit, info_way :
        (x_18).info_way, edir_hit : (x_18).edir_hit, edir_way :
        (x_18).edir_way, edir_slot : (x_18).edir_slot, info : Struct11
        {mesi_owned : ((x_18).info).mesi_owned, mesi_status :
        ((x_18).info).mesi_status, mesi_dir_st : (Struct17 {dir_st :
        (Bit#(3))'(3'h2), dir_excl : (x_16).dir_excl, dir_sharers :
        (((x_16).dir_st) == ((Bit#(3))'(3'h2)) ? (((x_16).dir_sharers) |
        (((Bit#(2))'(2'h1)) << ((Bit#(1))'(1'h1)))) : (((Bit#(2))'(2'h1)) <<
        ((Bit#(1))'(1'h1))))}).dir_st, mesi_dir_sharers : (((Struct17 {dir_st
        : (Bit#(3))'(3'h2), dir_excl : (x_16).dir_excl, dir_sharers :
        (((x_16).dir_st) == ((Bit#(3))'(3'h2)) ? (((x_16).dir_sharers) |
        (((Bit#(2))'(2'h1)) << ((Bit#(1))'(1'h1)))) : (((Bit#(2))'(2'h1)) <<
        ((Bit#(1))'(1'h1))))}).dir_st) == ((Bit#(3))'(3'h2)) ? ((Struct17
        {dir_st : (Bit#(3))'(3'h2), dir_excl : (x_16).dir_excl, dir_sharers :
        (((x_16).dir_st) == ((Bit#(3))'(3'h2)) ? (((x_16).dir_sharers) |
        (((Bit#(2))'(2'h1)) << ((Bit#(1))'(1'h1)))) : (((Bit#(2))'(2'h1)) <<
        ((Bit#(1))'(1'h1))))}).dir_sharers) : (((Bit#(2))'(2'h1)) <<
        ((Struct17 {dir_st : (Bit#(3))'(3'h2), dir_excl : (x_16).dir_excl,
        dir_sharers : (((x_16).dir_st) == ((Bit#(3))'(3'h2)) ?
        (((x_16).dir_sharers) | (((Bit#(2))'(2'h1)) << ((Bit#(1))'(1'h1)))) :
        (((Bit#(2))'(2'h1)) << ((Bit#(1))'(1'h1))))}).dir_excl)))},
        value_write : (x_18).value_write, value : (x_18).value, may_victim :
        (x_18).may_victim, reps :
        (x_18).reps});
        let x_22 = ?;
        if ((x_8).valid) begin
            let x_20 <- victims__00__setVictim(Struct19 {victim_idx :
            (x_8).data, victim_info : (x_19).info, victim_value :
            ((x_19).value_write ? ((x_19).value) : (x_9))});
            x_22 = x_9;
        end else begin
            let x_21 <- cache__00__valueRsLineRq(x_19);
            x_22 = x_21;
        end
        Struct20 x_23 = (Struct20 {enq_type : ((((Bit#(3))'(3'h5))[2:1]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : (((((Bit#(3))'(3'h5))[2:1])
        == ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : ((Bit#(3))'(3'h5))[0:0], enq_msg : Struct1 {id :
        (Bit#(6))'(6'h3), type_ : (Bool)'(True), addr : (x_17).addr, value :
        x_22}});
        let x_24 <- makeEnq_parentChildren00(x_23);
        let x_25 <- releaseMSHR_00(x_4);
    endrule

    rule rule_exec_00_001001;
        $display ("Rule fired: rule_exec_00_001001 at %t", $time);
        let x_0 <- deq_fifoL2E_00();
        Struct6 x_1 = ((x_0).lr_ir_pp);
        Bit#(3) x_2 = ((x_1).ir_msg_from);
        Struct1 x_3 = ((x_1).ir_msg);
        Bit#(4) x_4 = ((x_1).ir_mshr_id);
        Bool x_5 = ((x_1).ir_is_rs_rel);
        when (! (x_5), noAction);
        Struct9 x_6 = ((x_0).lr_ir);
        Struct11 x_7 = ((x_6).info);
        Struct5 x_8 = ((x_1).ir_by_victim);
        Vector#(4, Bit#(64)) x_9 = ((x_0).lr_value);
        let x_10 <- getMSHR_00(x_4);
        let x_11 <- getMSHRRq_00(x_4);
        let x_12 <- getMSHRFirstRs_00(x_4);
        Vector#(4, Bit#(64)) x_13 = (unpack(0));
        Bool x_14 = ((x_7).mesi_owned);
        Bit#(3) x_15 = ((x_7).mesi_status);
        Struct17 x_16 = (Struct17 {dir_st : (((x_7).mesi_dir_st) ==
        ((Bit#(3))'(3'h0)) ? ((Bit#(3))'(3'h1)) : ((x_7).mesi_dir_st)),
        dir_excl : ((((x_7).mesi_dir_sharers)[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(1))'(1'h0)) : (((Bit#(1))'(1'h1)) +
        ((((((x_7).mesi_dir_sharers)[1:1])[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(1))'(1'h0)) : (((Bit#(1))'(1'h1)) + (unpack(0))))))),
        dir_sharers : (x_7).mesi_dir_sharers});
        when ((x_2) == ((Bit#(3))'(3'h1)), noAction);
        when (((x_3).id) == ((Bit#(6))'(6'h2)), noAction);
        when (! ((x_3).type_), noAction);
        when ((! ((x_15) < ((Bit#(3))'(3'h3)))) && (((x_16).dir_st) ==
        ((Bit#(3))'(3'h1))), noAction);
        Struct1 x_17 = (x_3);
        Struct18 x_18 = (Struct18 {addr : (x_3).addr, info_write :
        (Bool)'(False), info_hit : (x_6).info_hit, info_way : (x_6).info_way,
        edir_hit : (x_6).edir_hit, edir_way : (x_6).edir_way, edir_slot :
        (x_6).edir_slot, info : (x_6).info, value_write : (Bool)'(False),
        value : unpack(0), may_victim : (x_6).may_victim, reps :
        (x_6).reps});
        Struct18 x_19 = (Struct18 {addr : (x_18).addr, info_write :
        (Bool)'(True), info_hit : (x_18).info_hit, info_way :
        (x_18).info_way, edir_hit : (x_18).edir_hit, edir_way :
        (x_18).edir_way, edir_slot : (x_18).edir_slot, info : Struct11
        {mesi_owned : ((x_18).info).mesi_owned, mesi_status :
        ((x_18).info).mesi_status, mesi_dir_st : (Struct17 {dir_st :
        (Bit#(3))'(3'h3), dir_excl : (Bit#(1))'(1'h1), dir_sharers :
        unpack(0)}).dir_st, mesi_dir_sharers : (((Struct17 {dir_st :
        (Bit#(3))'(3'h3), dir_excl : (Bit#(1))'(1'h1), dir_sharers :
        unpack(0)}).dir_st) == ((Bit#(3))'(3'h2)) ? ((Struct17 {dir_st :
        (Bit#(3))'(3'h3), dir_excl : (Bit#(1))'(1'h1), dir_sharers :
        unpack(0)}).dir_sharers) : (((Bit#(2))'(2'h1)) << ((Struct17 {dir_st
        : (Bit#(3))'(3'h3), dir_excl : (Bit#(1))'(1'h1), dir_sharers :
        unpack(0)}).dir_excl)))}, value_write : (x_18).value_write, value :
        (x_18).value, may_victim : (x_18).may_victim, reps :
        (x_18).reps});
        Struct18 x_20 = (Struct18 {addr : (x_19).addr, info_write :
        (Bool)'(True), info_hit : (x_19).info_hit, info_way :
        (x_19).info_way, edir_hit : (x_19).edir_hit, edir_way :
        (x_19).edir_way, edir_slot : (x_19).edir_slot, info : Struct11
        {mesi_owned : ((x_19).info).mesi_owned, mesi_status :
        (Bit#(3))'(3'h1), mesi_dir_st : ((x_19).info).mesi_dir_st,
        mesi_dir_sharers : ((x_19).info).mesi_dir_sharers}, value_write :
        (x_19).value_write, value : (x_19).value, may_victim :
        (x_19).may_victim, reps :
        (x_19).reps});
        let x_23 = ?;
        if ((x_8).valid) begin
            let x_21 <- victims__00__setVictim(Struct19 {victim_idx :
            (x_8).data, victim_info : (x_20).info, victim_value :
            ((x_20).value_write ? ((x_20).value) : (x_9))});
            x_23 = x_9;
        end else begin
            let x_22 <- cache__00__valueRsLineRq(x_20);
            x_23 = x_22;
        end
        Struct20 x_24 = (Struct20 {enq_type : ((((Bit#(3))'(3'h5))[2:1]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : (((((Bit#(3))'(3'h5))[2:1])
        == ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : ((Bit#(3))'(3'h5))[0:0], enq_msg : Struct1 {id :
        (Bit#(6))'(6'h4), type_ : (Bool)'(True), addr : (x_17).addr, value :
        x_23}});
        let x_25 <- makeEnq_parentChildren00(x_24);
        let x_26 <- releaseMSHR_00(x_4);
    endrule

    rule rule_exec_00_01001;
        $display ("Rule fired: rule_exec_00_01001 at %t", $time);
        let x_0 <- deq_fifoL2E_00();
        Struct6 x_1 = ((x_0).lr_ir_pp);
        Bit#(3) x_2 = ((x_1).ir_msg_from);
        Struct1 x_3 = ((x_1).ir_msg);
        Bit#(4) x_4 = ((x_1).ir_mshr_id);
        Bool x_5 = ((x_1).ir_is_rs_rel);
        when (! (x_5), noAction);
        Struct9 x_6 = ((x_0).lr_ir);
        Struct11 x_7 = ((x_6).info);
        Struct5 x_8 = ((x_1).ir_by_victim);
        Vector#(4, Bit#(64)) x_9 = ((x_0).lr_value);
        let x_10 <- getMSHR_00(x_4);
        let x_11 <- getMSHRRq_00(x_4);
        let x_12 <- getMSHRFirstRs_00(x_4);
        Vector#(4, Bit#(64)) x_13 = (unpack(0));
        Bool x_14 = ((x_7).mesi_owned);
        Bit#(3) x_15 = ((x_7).mesi_status);
        Struct17 x_16 = (Struct17 {dir_st : (((x_7).mesi_dir_st) ==
        ((Bit#(3))'(3'h0)) ? ((Bit#(3))'(3'h1)) : ((x_7).mesi_dir_st)),
        dir_excl : ((((x_7).mesi_dir_sharers)[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(1))'(1'h0)) : (((Bit#(1))'(1'h1)) +
        ((((((x_7).mesi_dir_sharers)[1:1])[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(1))'(1'h0)) : (((Bit#(1))'(1'h1)) + (unpack(0))))))),
        dir_sharers : (x_7).mesi_dir_sharers});
        when ((x_2) == ((Bit#(3))'(3'h1)), noAction);
        when (((x_3).id) == ((Bit#(6))'(6'h2)), noAction);
        when (! ((x_3).type_), noAction);
        when (((x_14) == ((Bool)'(False))) && ((! (((Bit#(3))'(3'h1)) <
        (x_15))) && (! (((Bit#(3))'(3'h2)) < ((x_16).dir_st)))),
        noAction);
        Struct1 x_17 = (x_3);
        Struct18 x_18 = (Struct18 {addr : (x_3).addr, info_write :
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
        let x_21 <- registerUL_00(Struct21 {r_id : x_4, r_ul_rsb :
        (Bool)'(True), r_ul_rsbTo : ((Bit#(3))'(3'h5))[0:0]});
        Struct20 x_22 = (Struct20 {enq_type : ((((Bit#(3))'(3'h0))[2:1]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : (((((Bit#(3))'(3'h0))[2:1])
        == ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : ((Bit#(3))'(3'h0))[0:0], enq_msg : Struct1 {id :
        (Bit#(6))'(6'h2), type_ : (Bool)'(False), addr : (x_17).addr, value :
        unpack(0)}});
        let x_23 <- makeEnq_parentChildren00(x_22);
    endrule

    rule rule_exec_00_03001;
        $display ("Rule fired: rule_exec_00_03001 at %t", $time);
        let x_0 <- deq_fifoL2E_00();
        Struct6 x_1 = ((x_0).lr_ir_pp);
        Bit#(3) x_2 = ((x_1).ir_msg_from);
        Struct1 x_3 = ((x_1).ir_msg);
        Bit#(4) x_4 = ((x_1).ir_mshr_id);
        Bool x_5 = ((x_1).ir_is_rs_rel);
        when (! (x_5), noAction);
        Struct9 x_6 = ((x_0).lr_ir);
        Struct11 x_7 = ((x_6).info);
        Struct5 x_8 = ((x_1).ir_by_victim);
        Vector#(4, Bit#(64)) x_9 = ((x_0).lr_value);
        let x_10 <- getMSHR_00(x_4);
        let x_11 <- getMSHRRq_00(x_4);
        let x_12 <- getMSHRFirstRs_00(x_4);
        Vector#(4, Bit#(64)) x_13 = (unpack(0));
        Bool x_14 = ((x_7).mesi_owned);
        Bit#(3) x_15 = ((x_7).mesi_status);
        Struct17 x_16 = (Struct17 {dir_st : (((x_7).mesi_dir_st) ==
        ((Bit#(3))'(3'h0)) ? ((Bit#(3))'(3'h1)) : ((x_7).mesi_dir_st)),
        dir_excl : ((((x_7).mesi_dir_sharers)[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(1))'(1'h0)) : (((Bit#(1))'(1'h1)) +
        ((((((x_7).mesi_dir_sharers)[1:1])[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(1))'(1'h0)) : (((Bit#(1))'(1'h1)) + (unpack(0))))))),
        dir_sharers : (x_7).mesi_dir_sharers});
        when ((x_2) == ((Bit#(3))'(3'h1)), noAction);
        when (((x_3).id) == ((Bit#(6))'(6'h2)), noAction);
        when (! ((x_3).type_), noAction);
        when (((Bool)'(True)) && (((Bool)'(True)) && ((! (((Bit#(3))'(3'h1))
        < (x_15))) && ((! (((x_16).dir_st) < ((Bit#(3))'(3'h3)))) && (!
        (((Bit#(3))'(3'h4)) < ((x_16).dir_st)))))), noAction);
        Struct1 x_17 = (x_3);
        Struct18 x_18 = (Struct18 {addr : (x_3).addr, info_write :
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
        let x_21 <- registerDL_00(Struct22 {r_id : x_4, r_dl_rss_from :
        (unpack(0)) | (((Bit#(2))'(2'h1)) <<
        (({((Bit#(2))'(2'h1)),((x_16).dir_excl)})[0:0])), r_dl_rsb :
        (Bool)'(True), r_dl_rsbTo : (Bit#(3))'(3'h5)});
        Struct20 x_22 = (Struct20 {enq_type :
        ((({((Bit#(2))'(2'h2)),((x_16).dir_excl)})[2:1]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) :
        (((({((Bit#(2))'(2'h2)),((x_16).dir_excl)})[2:1]) ==
        ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : ({((Bit#(2))'(2'h2)),((x_16).dir_excl)})[0:0], enq_msg :
        Struct1 {id : (Bit#(6))'(6'h5), type_ : (Bool)'(False), addr :
        (x_17).addr, value : unpack(0)}});
        let x_23 <- makeEnq_parentChildren00(x_22);
    endrule

    rule rule_exec_00_10001;
        $display ("Rule fired: rule_exec_00_10001 at %t", $time);
        let x_0 <- deq_fifoL2E_00();
        Struct6 x_1 = ((x_0).lr_ir_pp);
        Bit#(3) x_2 = ((x_1).ir_msg_from);
        Struct1 x_3 = ((x_1).ir_msg);
        Bit#(4) x_4 = ((x_1).ir_mshr_id);
        Bool x_5 = ((x_1).ir_is_rs_rel);
        when (! (x_5), noAction);
        Struct9 x_6 = ((x_0).lr_ir);
        Struct11 x_7 = ((x_6).info);
        Struct5 x_8 = ((x_1).ir_by_victim);
        Vector#(4, Bit#(64)) x_9 = ((x_0).lr_value);
        let x_10 <- getMSHR_00(x_4);
        let x_11 <- getMSHRRq_00(x_4);
        let x_12 <- getMSHRFirstRs_00(x_4);
        Vector#(4, Bit#(64)) x_13 = (unpack(0));
        Bool x_14 = ((x_7).mesi_owned);
        Bit#(3) x_15 = ((x_7).mesi_status);
        Struct17 x_16 = (Struct17 {dir_st : (((x_7).mesi_dir_st) ==
        ((Bit#(3))'(3'h0)) ? ((Bit#(3))'(3'h1)) : ((x_7).mesi_dir_st)),
        dir_excl : ((((x_7).mesi_dir_sharers)[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(1))'(1'h0)) : (((Bit#(1))'(1'h1)) +
        ((((((x_7).mesi_dir_sharers)[1:1])[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(1))'(1'h0)) : (((Bit#(1))'(1'h1)) + (unpack(0))))))),
        dir_sharers : (x_7).mesi_dir_sharers});
        when ((x_2) == ((Bit#(3))'(3'h1)), noAction);
        when (((x_3).id) == ((Bit#(6))'(6'ha)), noAction);
        when (! ((x_3).type_), noAction);
        when ((! ((x_15) < ((Bit#(3))'(3'h3)))) || (((x_15) ==
        ((Bit#(3))'(3'h2))) && (((x_14) == ((Bool)'(True))) &&
        ((((x_16).dir_st) == ((Bit#(3))'(3'h2))) && (((x_16).dir_sharers) ==
        (((Bit#(2))'(2'h1)) << ((Bit#(1))'(1'h1))))))), noAction);
        Struct1 x_17 = (x_3);
        Struct18 x_18 = (Struct18 {addr : (x_3).addr, info_write :
        (Bool)'(False), info_hit : (x_6).info_hit, info_way : (x_6).info_way,
        edir_hit : (x_6).edir_hit, edir_way : (x_6).edir_way, edir_slot :
        (x_6).edir_slot, info : (x_6).info, value_write : (Bool)'(False),
        value : unpack(0), may_victim : (x_6).may_victim, reps :
        (x_6).reps});
        Struct18 x_19 = (Struct18 {addr : (x_18).addr, info_write :
        (Bool)'(True), info_hit : (x_18).info_hit, info_way :
        (x_18).info_way, edir_hit : (x_18).edir_hit, edir_way :
        (x_18).edir_way, edir_slot : (x_18).edir_slot, info : Struct11
        {mesi_owned : ((x_18).info).mesi_owned, mesi_status :
        ((x_18).info).mesi_status, mesi_dir_st : (Struct17 {dir_st :
        (Bit#(3))'(3'h4), dir_excl : (Bit#(1))'(1'h1), dir_sharers :
        unpack(0)}).dir_st, mesi_dir_sharers : (((Struct17 {dir_st :
        (Bit#(3))'(3'h4), dir_excl : (Bit#(1))'(1'h1), dir_sharers :
        unpack(0)}).dir_st) == ((Bit#(3))'(3'h2)) ? ((Struct17 {dir_st :
        (Bit#(3))'(3'h4), dir_excl : (Bit#(1))'(1'h1), dir_sharers :
        unpack(0)}).dir_sharers) : (((Bit#(2))'(2'h1)) << ((Struct17 {dir_st
        : (Bit#(3))'(3'h4), dir_excl : (Bit#(1))'(1'h1), dir_sharers :
        unpack(0)}).dir_excl)))}, value_write : (x_18).value_write, value :
        (x_18).value, may_victim : (x_18).may_victim, reps :
        (x_18).reps});
        Struct18 x_20 = (Struct18 {addr : (x_19).addr, info_write :
        (Bool)'(True), info_hit : (x_19).info_hit, info_way :
        (x_19).info_way, edir_hit : (x_19).edir_hit, edir_way :
        (x_19).edir_way, edir_slot : (x_19).edir_slot, info : Struct11
        {mesi_owned : ((x_19).info).mesi_owned, mesi_status :
        (Bit#(3))'(3'h1), mesi_dir_st : ((x_19).info).mesi_dir_st,
        mesi_dir_sharers : ((x_19).info).mesi_dir_sharers}, value_write :
        (x_19).value_write, value : (x_19).value, may_victim :
        (x_19).may_victim, reps : (x_19).reps});
        Struct18 x_21 = (Struct18 {addr : (x_20).addr, info_write :
        (Bool)'(True), info_hit : (x_20).info_hit, info_way :
        (x_20).info_way, edir_hit : (x_20).edir_hit, edir_way :
        (x_20).edir_way, edir_slot : (x_20).edir_slot, info : Struct11
        {mesi_owned : (Bool)'(False), mesi_status :
        ((x_20).info).mesi_status, mesi_dir_st : ((x_20).info).mesi_dir_st,
        mesi_dir_sharers : ((x_20).info).mesi_dir_sharers}, value_write :
        (x_20).value_write, value : (x_20).value, may_victim :
        (x_20).may_victim, reps :
        (x_20).reps});
        let x_24 = ?;
        if ((x_8).valid) begin
            let x_22 <- victims__00__setVictim(Struct19 {victim_idx :
            (x_8).data, victim_info : (x_21).info, victim_value :
            ((x_21).value_write ? ((x_21).value) : (x_9))});
            x_24 = x_9;
        end else begin
            let x_23 <- cache__00__valueRsLineRq(x_21);
            x_24 = x_23;
        end
        Struct20 x_25 = (Struct20 {enq_type : ((((Bit#(3))'(3'h5))[2:1]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : (((((Bit#(3))'(3'h5))[2:1])
        == ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : ((Bit#(3))'(3'h5))[0:0], enq_msg : Struct1 {id :
        (Bit#(6))'(6'hb), type_ : (Bool)'(True), addr : (x_17).addr, value :
        unpack(0)}});
        let x_26 <- makeEnq_parentChildren00(x_25);
        let x_27 <- releaseMSHR_00(x_4);
    endrule

    rule rule_exec_00_11001;
        $display ("Rule fired: rule_exec_00_11001 at %t", $time);
        let x_0 <- deq_fifoL2E_00();
        Struct6 x_1 = ((x_0).lr_ir_pp);
        Bit#(3) x_2 = ((x_1).ir_msg_from);
        Struct1 x_3 = ((x_1).ir_msg);
        Bit#(4) x_4 = ((x_1).ir_mshr_id);
        Bool x_5 = ((x_1).ir_is_rs_rel);
        when (! (x_5), noAction);
        Struct9 x_6 = ((x_0).lr_ir);
        Struct11 x_7 = ((x_6).info);
        Struct5 x_8 = ((x_1).ir_by_victim);
        Vector#(4, Bit#(64)) x_9 = ((x_0).lr_value);
        let x_10 <- getMSHR_00(x_4);
        let x_11 <- getMSHRRq_00(x_4);
        let x_12 <- getMSHRFirstRs_00(x_4);
        Vector#(4, Bit#(64)) x_13 = (unpack(0));
        Bool x_14 = ((x_7).mesi_owned);
        Bit#(3) x_15 = ((x_7).mesi_status);
        Struct17 x_16 = (Struct17 {dir_st : (((x_7).mesi_dir_st) ==
        ((Bit#(3))'(3'h0)) ? ((Bit#(3))'(3'h1)) : ((x_7).mesi_dir_st)),
        dir_excl : ((((x_7).mesi_dir_sharers)[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(1))'(1'h0)) : (((Bit#(1))'(1'h1)) +
        ((((((x_7).mesi_dir_sharers)[1:1])[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(1))'(1'h0)) : (((Bit#(1))'(1'h1)) + (unpack(0))))))),
        dir_sharers : (x_7).mesi_dir_sharers});
        when ((x_2) == ((Bit#(3))'(3'h1)), noAction);
        when (((x_3).id) == ((Bit#(6))'(6'ha)), noAction);
        when (! ((x_3).type_), noAction);
        when (((x_14) == ((Bool)'(False))) && ((! (((Bit#(3))'(3'h2)) <
        (x_15))) && (! (((Bit#(3))'(3'h2)) < ((x_16).dir_st)))),
        noAction);
        Struct1 x_17 = (x_3);
        Struct18 x_18 = (Struct18 {addr : (x_3).addr, info_write :
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
        let x_21 <- registerUL_00(Struct21 {r_id : x_4, r_ul_rsb :
        (Bool)'(True), r_ul_rsbTo : ((Bit#(3))'(3'h5))[0:0]});
        Struct20 x_22 = (Struct20 {enq_type : ((((Bit#(3))'(3'h0))[2:1]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : (((((Bit#(3))'(3'h0))[2:1])
        == ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : ((Bit#(3))'(3'h0))[0:0], enq_msg : Struct1 {id :
        (Bit#(6))'(6'ha), type_ : (Bool)'(False), addr : (x_17).addr, value :
        unpack(0)}});
        let x_23 <- makeEnq_parentChildren00(x_22);
    endrule

    rule rule_exec_00_14001;
        $display ("Rule fired: rule_exec_00_14001 at %t", $time);
        let x_0 <- deq_fifoL2E_00();
        Struct6 x_1 = ((x_0).lr_ir_pp);
        Bit#(3) x_2 = ((x_1).ir_msg_from);
        Struct1 x_3 = ((x_1).ir_msg);
        Bit#(4) x_4 = ((x_1).ir_mshr_id);
        Bool x_5 = ((x_1).ir_is_rs_rel);
        when (! (x_5), noAction);
        Struct9 x_6 = ((x_0).lr_ir);
        Struct11 x_7 = ((x_6).info);
        Struct5 x_8 = ((x_1).ir_by_victim);
        Vector#(4, Bit#(64)) x_9 = ((x_0).lr_value);
        let x_10 <- getMSHR_00(x_4);
        let x_11 <- getMSHRRq_00(x_4);
        let x_12 <- getMSHRFirstRs_00(x_4);
        Vector#(4, Bit#(64)) x_13 = (unpack(0));
        Bool x_14 = ((x_7).mesi_owned);
        Bit#(3) x_15 = ((x_7).mesi_status);
        Struct17 x_16 = (Struct17 {dir_st : (((x_7).mesi_dir_st) ==
        ((Bit#(3))'(3'h0)) ? ((Bit#(3))'(3'h1)) : ((x_7).mesi_dir_st)),
        dir_excl : ((((x_7).mesi_dir_sharers)[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(1))'(1'h0)) : (((Bit#(1))'(1'h1)) +
        ((((((x_7).mesi_dir_sharers)[1:1])[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(1))'(1'h0)) : (((Bit#(1))'(1'h1)) + (unpack(0))))))),
        dir_sharers : (x_7).mesi_dir_sharers});
        when ((x_2) == ((Bit#(3))'(3'h1)), noAction);
        when (((x_3).id) == ((Bit#(6))'(6'ha)), noAction);
        when (! ((x_3).type_), noAction);
        when (((Bool)'(True)) && (((Bool)'(True)) && ((! (((Bit#(3))'(3'h1))
        < (x_15))) && ((! (((x_16).dir_st) < ((Bit#(3))'(3'h3)))) && (!
        (((Bit#(3))'(3'h4)) < ((x_16).dir_st)))))), noAction);
        Struct1 x_17 = (x_3);
        Struct18 x_18 = (Struct18 {addr : (x_3).addr, info_write :
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
        let x_21 <- registerDL_00(Struct22 {r_id : x_4, r_dl_rss_from :
        (unpack(0)) | (((Bit#(2))'(2'h1)) <<
        (({((Bit#(2))'(2'h1)),((x_16).dir_excl)})[0:0])), r_dl_rsb :
        (Bool)'(True), r_dl_rsbTo : (Bit#(3))'(3'h5)});
        Struct20 x_22 = (Struct20 {enq_type :
        ((({((Bit#(2))'(2'h2)),((x_16).dir_excl)})[2:1]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) :
        (((({((Bit#(2))'(2'h2)),((x_16).dir_excl)})[2:1]) ==
        ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : ({((Bit#(2))'(2'h2)),((x_16).dir_excl)})[0:0], enq_msg :
        Struct1 {id : (Bit#(6))'(6'he), type_ : (Bool)'(False), addr :
        (x_17).addr, value : unpack(0)}});
        let x_23 <- makeEnq_parentChildren00(x_22);
    endrule

    rule rule_exec_00_15001;
        $display ("Rule fired: rule_exec_00_15001 at %t", $time);
        let x_0 <- deq_fifoL2E_00();
        Struct6 x_1 = ((x_0).lr_ir_pp);
        Bit#(3) x_2 = ((x_1).ir_msg_from);
        Struct1 x_3 = ((x_1).ir_msg);
        Bit#(4) x_4 = ((x_1).ir_mshr_id);
        Bool x_5 = ((x_1).ir_is_rs_rel);
        when (! (x_5), noAction);
        Struct9 x_6 = ((x_0).lr_ir);
        Struct11 x_7 = ((x_6).info);
        Struct5 x_8 = ((x_1).ir_by_victim);
        Vector#(4, Bit#(64)) x_9 = ((x_0).lr_value);
        let x_10 <- getMSHR_00(x_4);
        let x_11 <- getMSHRRq_00(x_4);
        let x_12 <- getMSHRFirstRs_00(x_4);
        Vector#(4, Bit#(64)) x_13 = (unpack(0));
        Bool x_14 = ((x_7).mesi_owned);
        Bit#(3) x_15 = ((x_7).mesi_status);
        Struct17 x_16 = (Struct17 {dir_st : (((x_7).mesi_dir_st) ==
        ((Bit#(3))'(3'h0)) ? ((Bit#(3))'(3'h1)) : ((x_7).mesi_dir_st)),
        dir_excl : ((((x_7).mesi_dir_sharers)[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(1))'(1'h0)) : (((Bit#(1))'(1'h1)) +
        ((((((x_7).mesi_dir_sharers)[1:1])[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(1))'(1'h0)) : (((Bit#(1))'(1'h1)) + (unpack(0))))))),
        dir_sharers : (x_7).mesi_dir_sharers});
        when ((x_2) == ((Bit#(3))'(3'h1)), noAction);
        when (((x_3).id) == ((Bit#(6))'(6'ha)), noAction);
        when (! ((x_3).type_), noAction);
        when (((Bool)'(True)) && (((Bool)'(True)) && ((!
        ((((x_16).dir_sharers) & (~(((Bit#(2))'(2'h1)) <<
        ((Bit#(1))'(1'h1))))) == ((Bit#(2))'(2'h0)))) && (((x_14) ==
        ((Bool)'(True))) && ((! (((Bit#(3))'(3'h2)) < (x_15))) &&
        (((x_16).dir_st) == ((Bit#(3))'(3'h2))))))), noAction);
        Struct1 x_17 = (x_3);
        Struct18 x_18 = (Struct18 {addr : (x_3).addr, info_write :
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
        let x_21 <- registerDL_00(Struct22 {r_id : x_4, r_dl_rss_from :
        ((x_16).dir_sharers) & (~(((Bit#(2))'(2'h1)) << ((Bit#(1))'(1'h1)))),
        r_dl_rsb : (Bool)'(True), r_dl_rsbTo : (Bit#(3))'(3'h5)});
        let x_22 <- broadcast_parentChildren00(Struct23 {cs_inds :
        ((x_16).dir_sharers) & (~(((Bit#(2))'(2'h1)) << ((Bit#(1))'(1'h1)))),
        cs_msg : Struct1 {id : (Bit#(6))'(6'hc), type_ : (Bool)'(False), addr
        : (x_17).addr, value : unpack(0)}});
    endrule

    rule rule_exec_00_25001;
        $display ("Rule fired: rule_exec_00_25001 at %t", $time);
        let x_0 <- deq_fifoL2E_00();
        Struct6 x_1 = ((x_0).lr_ir_pp);
        Bit#(3) x_2 = ((x_1).ir_msg_from);
        Struct1 x_3 = ((x_1).ir_msg);
        Bit#(4) x_4 = ((x_1).ir_mshr_id);
        Bool x_5 = ((x_1).ir_is_rs_rel);
        when (! (x_5), noAction);
        Struct9 x_6 = ((x_0).lr_ir);
        Struct11 x_7 = ((x_6).info);
        Struct5 x_8 = ((x_1).ir_by_victim);
        Vector#(4, Bit#(64)) x_9 = ((x_0).lr_value);
        let x_10 <- getMSHR_00(x_4);
        let x_11 <- getMSHRRq_00(x_4);
        let x_12 <- getMSHRFirstRs_00(x_4);
        Vector#(4, Bit#(64)) x_13 = (unpack(0));
        Bool x_14 = ((x_7).mesi_owned);
        Bit#(3) x_15 = ((x_7).mesi_status);
        Struct17 x_16 = (Struct17 {dir_st : (((x_7).mesi_dir_st) ==
        ((Bit#(3))'(3'h0)) ? ((Bit#(3))'(3'h1)) : ((x_7).mesi_dir_st)),
        dir_excl : ((((x_7).mesi_dir_sharers)[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(1))'(1'h0)) : (((Bit#(1))'(1'h1)) +
        ((((((x_7).mesi_dir_sharers)[1:1])[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(1))'(1'h0)) : (((Bit#(1))'(1'h1)) + (unpack(0))))))),
        dir_sharers : (x_7).mesi_dir_sharers});
        when ((x_2) == ((Bit#(3))'(3'h1)), noAction);
        when (((x_3).id) == ((Bit#(6))'(6'h14)), noAction);
        when (! ((x_3).type_), noAction);
        when ((((((x_16).dir_st) == ((Bit#(3))'(3'h4))) && (((x_16).dir_excl)
        == ((Bit#(1))'(1'h1))) ? ((Bit#(3))'(3'h4)) : (((((x_16).dir_st) ==
        ((Bit#(3))'(3'h3))) && (((x_16).dir_excl) == ((Bit#(1))'(1'h1))) ?
        ((Bit#(3))'(3'h3)) : (((((x_16).dir_st) == ((Bit#(3))'(3'h2))) &&
        ((((x_16).dir_sharers) | (((Bit#(2))'(2'h1)) << ((Bit#(1))'(1'h1))))
        == ((x_16).dir_sharers)) ? ((Bit#(3))'(3'h2)) :
        ((Bit#(3))'(3'h1)))))))) == ((Bit#(3))'(3'h1)), noAction);
        Struct1 x_17 = (x_3);
        Struct18 x_18 = (Struct18 {addr : (x_3).addr, info_write :
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
        Struct20 x_21 = (Struct20 {enq_type : ((((Bit#(3))'(3'h5))[2:1]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : (((((Bit#(3))'(3'h5))[2:1])
        == ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : ((Bit#(3))'(3'h5))[0:0], enq_msg : Struct1 {id :
        (Bit#(6))'(6'h16), type_ : (Bool)'(True), addr : (x_17).addr, value :
        unpack(0)}});
        let x_22 <- makeEnq_parentChildren00(x_21);
        let x_23 <- releaseMSHR_00(x_4);
    endrule

    rule rule_exec_00_2600001;
        $display ("Rule fired: rule_exec_00_2600001 at %t", $time);
        let x_0 <- deq_fifoL2E_00();
        Struct6 x_1 = ((x_0).lr_ir_pp);
        Bit#(3) x_2 = ((x_1).ir_msg_from);
        Struct1 x_3 = ((x_1).ir_msg);
        Bit#(4) x_4 = ((x_1).ir_mshr_id);
        Bool x_5 = ((x_1).ir_is_rs_rel);
        when (! (x_5), noAction);
        Struct9 x_6 = ((x_0).lr_ir);
        Struct11 x_7 = ((x_6).info);
        Struct5 x_8 = ((x_1).ir_by_victim);
        Vector#(4, Bit#(64)) x_9 = ((x_0).lr_value);
        let x_10 <- getMSHR_00(x_4);
        let x_11 <- getMSHRRq_00(x_4);
        let x_12 <- getMSHRFirstRs_00(x_4);
        Vector#(4, Bit#(64)) x_13 = (unpack(0));
        Bool x_14 = ((x_7).mesi_owned);
        Bit#(3) x_15 = ((x_7).mesi_status);
        Struct17 x_16 = (Struct17 {dir_st : (((x_7).mesi_dir_st) ==
        ((Bit#(3))'(3'h0)) ? ((Bit#(3))'(3'h1)) : ((x_7).mesi_dir_st)),
        dir_excl : ((((x_7).mesi_dir_sharers)[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(1))'(1'h0)) : (((Bit#(1))'(1'h1)) +
        ((((((x_7).mesi_dir_sharers)[1:1])[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(1))'(1'h0)) : (((Bit#(1))'(1'h1)) + (unpack(0))))))),
        dir_sharers : (x_7).mesi_dir_sharers});
        when ((x_2) == ((Bit#(3))'(3'h1)), noAction);
        when (((x_3).id) == ((Bit#(6))'(6'h14)), noAction);
        when (! ((x_3).type_), noAction);
        when (((x_14) == ((Bool)'(False))) && (((((((x_16).dir_st) ==
        ((Bit#(3))'(3'h4))) && (((x_16).dir_excl) == ((Bit#(1))'(1'h1))) ?
        ((Bit#(3))'(3'h4)) : (((((x_16).dir_st) == ((Bit#(3))'(3'h3))) &&
        (((x_16).dir_excl) == ((Bit#(1))'(1'h1))) ? ((Bit#(3))'(3'h3)) :
        (((((x_16).dir_st) == ((Bit#(3))'(3'h2))) && ((((x_16).dir_sharers) |
        (((Bit#(2))'(2'h1)) << ((Bit#(1))'(1'h1)))) == ((x_16).dir_sharers))
        ? ((Bit#(3))'(3'h2)) : ((Bit#(3))'(3'h1)))))))) ==
        ((Bit#(3))'(3'h2))) && (((x_16).dir_sharers) == (((Bit#(2))'(2'h1))
        << ((Bit#(1))'(1'h1))))), noAction);
        Struct1 x_17 = (x_3);
        Struct18 x_18 = (Struct18 {addr : (x_3).addr, info_write :
        (Bool)'(False), info_hit : (x_6).info_hit, info_way : (x_6).info_way,
        edir_hit : (x_6).edir_hit, edir_way : (x_6).edir_way, edir_slot :
        (x_6).edir_slot, info : (x_6).info, value_write : (Bool)'(False),
        value : unpack(0), may_victim : (x_6).may_victim, reps :
        (x_6).reps});
        Struct18 x_19 = (Struct18 {addr : (x_18).addr, info_write :
        (Bool)'(True), info_hit : (x_18).info_hit, info_way :
        (x_18).info_way, edir_hit : (x_18).edir_hit, edir_way :
        (x_18).edir_way, edir_slot : (x_18).edir_slot, info : Struct11
        {mesi_owned : ((x_18).info).mesi_owned, mesi_status :
        ((x_18).info).mesi_status, mesi_dir_st : (Struct17 {dir_st :
        (Bit#(3))'(3'h1), dir_excl : unpack(0), dir_sharers :
        unpack(0)}).dir_st, mesi_dir_sharers : (((Struct17 {dir_st :
        (Bit#(3))'(3'h1), dir_excl : unpack(0), dir_sharers :
        unpack(0)}).dir_st) == ((Bit#(3))'(3'h2)) ? ((Struct17 {dir_st :
        (Bit#(3))'(3'h1), dir_excl : unpack(0), dir_sharers :
        unpack(0)}).dir_sharers) : (((Bit#(2))'(2'h1)) << ((Struct17 {dir_st
        : (Bit#(3))'(3'h1), dir_excl : unpack(0), dir_sharers :
        unpack(0)}).dir_excl)))}, value_write : (x_18).value_write, value :
        (x_18).value, may_victim : (x_18).may_victim, reps :
        (x_18).reps});
        let x_22 = ?;
        if ((x_8).valid) begin
            let x_20 <- victims__00__setVictim(Struct19 {victim_idx :
            (x_8).data, victim_info : (x_19).info, victim_value :
            ((x_19).value_write ? ((x_19).value) : (x_9))});
            x_22 = x_9;
        end else begin
            let x_21 <- cache__00__valueRsLineRq(x_19);
            x_22 = x_21;
        end
        Struct20 x_23 = (Struct20 {enq_type : ((((Bit#(3))'(3'h5))[2:1]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : (((((Bit#(3))'(3'h5))[2:1])
        == ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : ((Bit#(3))'(3'h5))[0:0], enq_msg : Struct1 {id :
        (Bit#(6))'(6'h16), type_ : (Bool)'(True), addr : (x_17).addr, value :
        unpack(0)}});
        let x_24 <- makeEnq_parentChildren00(x_23);
        let x_25 <- releaseMSHR_00(x_4);
    endrule

    rule rule_exec_00_2601001;
        $display ("Rule fired: rule_exec_00_2601001 at %t", $time);
        let x_0 <- deq_fifoL2E_00();
        Struct6 x_1 = ((x_0).lr_ir_pp);
        Bit#(3) x_2 = ((x_1).ir_msg_from);
        Struct1 x_3 = ((x_1).ir_msg);
        Bit#(4) x_4 = ((x_1).ir_mshr_id);
        Bool x_5 = ((x_1).ir_is_rs_rel);
        when (! (x_5), noAction);
        Struct9 x_6 = ((x_0).lr_ir);
        Struct11 x_7 = ((x_6).info);
        Struct5 x_8 = ((x_1).ir_by_victim);
        Vector#(4, Bit#(64)) x_9 = ((x_0).lr_value);
        let x_10 <- getMSHR_00(x_4);
        let x_11 <- getMSHRRq_00(x_4);
        let x_12 <- getMSHRFirstRs_00(x_4);
        Vector#(4, Bit#(64)) x_13 = (unpack(0));
        Bool x_14 = ((x_7).mesi_owned);
        Bit#(3) x_15 = ((x_7).mesi_status);
        Struct17 x_16 = (Struct17 {dir_st : (((x_7).mesi_dir_st) ==
        ((Bit#(3))'(3'h0)) ? ((Bit#(3))'(3'h1)) : ((x_7).mesi_dir_st)),
        dir_excl : ((((x_7).mesi_dir_sharers)[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(1))'(1'h0)) : (((Bit#(1))'(1'h1)) +
        ((((((x_7).mesi_dir_sharers)[1:1])[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(1))'(1'h0)) : (((Bit#(1))'(1'h1)) + (unpack(0))))))),
        dir_sharers : (x_7).mesi_dir_sharers});
        when ((x_2) == ((Bit#(3))'(3'h1)), noAction);
        when (((x_3).id) == ((Bit#(6))'(6'h14)), noAction);
        when (! ((x_3).type_), noAction);
        when (((x_14) == ((Bool)'(True))) && (((x_15) == ((Bit#(3))'(3'h2)))
        && (((((((x_16).dir_st) == ((Bit#(3))'(3'h4))) && (((x_16).dir_excl)
        == ((Bit#(1))'(1'h1))) ? ((Bit#(3))'(3'h4)) : (((((x_16).dir_st) ==
        ((Bit#(3))'(3'h3))) && (((x_16).dir_excl) == ((Bit#(1))'(1'h1))) ?
        ((Bit#(3))'(3'h3)) : (((((x_16).dir_st) == ((Bit#(3))'(3'h2))) &&
        ((((x_16).dir_sharers) | (((Bit#(2))'(2'h1)) << ((Bit#(1))'(1'h1))))
        == ((x_16).dir_sharers)) ? ((Bit#(3))'(3'h2)) :
        ((Bit#(3))'(3'h1)))))))) == ((Bit#(3))'(3'h2))) &&
        (((x_16).dir_sharers) == (((Bit#(2))'(2'h1)) <<
        ((Bit#(1))'(1'h1)))))), noAction);
        Struct1 x_17 = (x_3);
        Struct18 x_18 = (Struct18 {addr : (x_3).addr, info_write :
        (Bool)'(False), info_hit : (x_6).info_hit, info_way : (x_6).info_way,
        edir_hit : (x_6).edir_hit, edir_way : (x_6).edir_way, edir_slot :
        (x_6).edir_slot, info : (x_6).info, value_write : (Bool)'(False),
        value : unpack(0), may_victim : (x_6).may_victim, reps :
        (x_6).reps});
        Struct18 x_19 = (Struct18 {addr : (x_18).addr, info_write :
        (Bool)'(True), info_hit : (x_18).info_hit, info_way :
        (x_18).info_way, edir_hit : (x_18).edir_hit, edir_way :
        (x_18).edir_way, edir_slot : (x_18).edir_slot, info : Struct11
        {mesi_owned : ((x_18).info).mesi_owned, mesi_status :
        ((x_18).info).mesi_status, mesi_dir_st : (Struct17 {dir_st :
        (Bit#(3))'(3'h1), dir_excl : unpack(0), dir_sharers :
        unpack(0)}).dir_st, mesi_dir_sharers : (((Struct17 {dir_st :
        (Bit#(3))'(3'h1), dir_excl : unpack(0), dir_sharers :
        unpack(0)}).dir_st) == ((Bit#(3))'(3'h2)) ? ((Struct17 {dir_st :
        (Bit#(3))'(3'h1), dir_excl : unpack(0), dir_sharers :
        unpack(0)}).dir_sharers) : (((Bit#(2))'(2'h1)) << ((Struct17 {dir_st
        : (Bit#(3))'(3'h1), dir_excl : unpack(0), dir_sharers :
        unpack(0)}).dir_excl)))}, value_write : (x_18).value_write, value :
        (x_18).value, may_victim : (x_18).may_victim, reps :
        (x_18).reps});
        Struct18 x_20 = (Struct18 {addr : (x_19).addr, info_write :
        (Bool)'(True), info_hit : (x_19).info_hit, info_way :
        (x_19).info_way, edir_hit : (x_19).edir_hit, edir_way :
        (x_19).edir_way, edir_slot : (x_19).edir_slot, info : Struct11
        {mesi_owned : ((x_19).info).mesi_owned, mesi_status :
        (Bit#(3))'(3'h4), mesi_dir_st : ((x_19).info).mesi_dir_st,
        mesi_dir_sharers : ((x_19).info).mesi_dir_sharers}, value_write :
        (x_19).value_write, value : (x_19).value, may_victim :
        (x_19).may_victim, reps :
        (x_19).reps});
        let x_23 = ?;
        if ((x_8).valid) begin
            let x_21 <- victims__00__setVictim(Struct19 {victim_idx :
            (x_8).data, victim_info : (x_20).info, victim_value :
            ((x_20).value_write ? ((x_20).value) : (x_9))});
            x_23 = x_9;
        end else begin
            let x_22 <- cache__00__valueRsLineRq(x_20);
            x_23 = x_22;
        end
        Struct20 x_24 = (Struct20 {enq_type : ((((Bit#(3))'(3'h5))[2:1]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : (((((Bit#(3))'(3'h5))[2:1])
        == ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : ((Bit#(3))'(3'h5))[0:0], enq_msg : Struct1 {id :
        (Bit#(6))'(6'h16), type_ : (Bool)'(True), addr : (x_17).addr, value :
        unpack(0)}});
        let x_25 <- makeEnq_parentChildren00(x_24);
        let x_26 <- releaseMSHR_00(x_4);
    endrule

    rule rule_exec_00_261001;
        $display ("Rule fired: rule_exec_00_261001 at %t", $time);
        let x_0 <- deq_fifoL2E_00();
        Struct6 x_1 = ((x_0).lr_ir_pp);
        Bit#(3) x_2 = ((x_1).ir_msg_from);
        Struct1 x_3 = ((x_1).ir_msg);
        Bit#(4) x_4 = ((x_1).ir_mshr_id);
        Bool x_5 = ((x_1).ir_is_rs_rel);
        when (! (x_5), noAction);
        Struct9 x_6 = ((x_0).lr_ir);
        Struct11 x_7 = ((x_6).info);
        Struct5 x_8 = ((x_1).ir_by_victim);
        Vector#(4, Bit#(64)) x_9 = ((x_0).lr_value);
        let x_10 <- getMSHR_00(x_4);
        let x_11 <- getMSHRRq_00(x_4);
        let x_12 <- getMSHRFirstRs_00(x_4);
        Vector#(4, Bit#(64)) x_13 = (unpack(0));
        Bool x_14 = ((x_7).mesi_owned);
        Bit#(3) x_15 = ((x_7).mesi_status);
        Struct17 x_16 = (Struct17 {dir_st : (((x_7).mesi_dir_st) ==
        ((Bit#(3))'(3'h0)) ? ((Bit#(3))'(3'h1)) : ((x_7).mesi_dir_st)),
        dir_excl : ((((x_7).mesi_dir_sharers)[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(1))'(1'h0)) : (((Bit#(1))'(1'h1)) +
        ((((((x_7).mesi_dir_sharers)[1:1])[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(1))'(1'h0)) : (((Bit#(1))'(1'h1)) + (unpack(0))))))),
        dir_sharers : (x_7).mesi_dir_sharers});
        when ((x_2) == ((Bit#(3))'(3'h1)), noAction);
        when (((x_3).id) == ((Bit#(6))'(6'h14)), noAction);
        when (! ((x_3).type_), noAction);
        when (((((((x_16).dir_st) == ((Bit#(3))'(3'h4))) &&
        (((x_16).dir_excl) == ((Bit#(1))'(1'h1))) ? ((Bit#(3))'(3'h4)) :
        (((((x_16).dir_st) == ((Bit#(3))'(3'h3))) && (((x_16).dir_excl) ==
        ((Bit#(1))'(1'h1))) ? ((Bit#(3))'(3'h3)) : (((((x_16).dir_st) ==
        ((Bit#(3))'(3'h2))) && ((((x_16).dir_sharers) | (((Bit#(2))'(2'h1))
        << ((Bit#(1))'(1'h1)))) == ((x_16).dir_sharers)) ? ((Bit#(3))'(3'h2))
        : ((Bit#(3))'(3'h1)))))))) == ((Bit#(3))'(3'h2))) &&
        (((Bit#(2))'(2'h1)) < ((((((x_16).dir_sharers)[0:0]) ==
        ((Bit#(1))'(1'h1)) ? ((Bit#(2))'(2'h1)) : ((Bit#(2))'(2'h0)))) +
        (((((((x_16).dir_sharers)[1:1])[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(2))'(2'h1)) : ((Bit#(2))'(2'h0)))) + (unpack(0))))),
        noAction);
        Struct1 x_17 = (x_3);
        Struct18 x_18 = (Struct18 {addr : (x_3).addr, info_write :
        (Bool)'(False), info_hit : (x_6).info_hit, info_way : (x_6).info_way,
        edir_hit : (x_6).edir_hit, edir_way : (x_6).edir_way, edir_slot :
        (x_6).edir_slot, info : (x_6).info, value_write : (Bool)'(False),
        value : unpack(0), may_victim : (x_6).may_victim, reps :
        (x_6).reps});
        Struct18 x_19 = (Struct18 {addr : (x_18).addr, info_write :
        (Bool)'(True), info_hit : (x_18).info_hit, info_way :
        (x_18).info_way, edir_hit : (x_18).edir_hit, edir_way :
        (x_18).edir_way, edir_slot : (x_18).edir_slot, info : Struct11
        {mesi_owned : ((x_18).info).mesi_owned, mesi_status :
        ((x_18).info).mesi_status, mesi_dir_st : (Struct17 {dir_st :
        (Bit#(3))'(3'h2), dir_excl : (x_16).dir_excl, dir_sharers :
        ((x_16).dir_sharers) & (~(((Bit#(2))'(2'h1)) <<
        ((Bit#(1))'(1'h1))))}).dir_st, mesi_dir_sharers : (((Struct17 {dir_st
        : (Bit#(3))'(3'h2), dir_excl : (x_16).dir_excl, dir_sharers :
        ((x_16).dir_sharers) & (~(((Bit#(2))'(2'h1)) <<
        ((Bit#(1))'(1'h1))))}).dir_st) == ((Bit#(3))'(3'h2)) ? ((Struct17
        {dir_st : (Bit#(3))'(3'h2), dir_excl : (x_16).dir_excl, dir_sharers :
        ((x_16).dir_sharers) & (~(((Bit#(2))'(2'h1)) <<
        ((Bit#(1))'(1'h1))))}).dir_sharers) : (((Bit#(2))'(2'h1)) <<
        ((Struct17 {dir_st : (Bit#(3))'(3'h2), dir_excl : (x_16).dir_excl,
        dir_sharers : ((x_16).dir_sharers) & (~(((Bit#(2))'(2'h1)) <<
        ((Bit#(1))'(1'h1))))}).dir_excl)))}, value_write :
        (x_18).value_write, value : (x_18).value, may_victim :
        (x_18).may_victim, reps :
        (x_18).reps});
        let x_22 = ?;
        if ((x_8).valid) begin
            let x_20 <- victims__00__setVictim(Struct19 {victim_idx :
            (x_8).data, victim_info : (x_19).info, victim_value :
            ((x_19).value_write ? ((x_19).value) : (x_9))});
            x_22 = x_9;
        end else begin
            let x_21 <- cache__00__valueRsLineRq(x_19);
            x_22 = x_21;
        end
        Struct20 x_23 = (Struct20 {enq_type : ((((Bit#(3))'(3'h5))[2:1]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : (((((Bit#(3))'(3'h5))[2:1])
        == ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : ((Bit#(3))'(3'h5))[0:0], enq_msg : Struct1 {id :
        (Bit#(6))'(6'h16), type_ : (Bool)'(True), addr : (x_17).addr, value :
        unpack(0)}});
        let x_24 <- makeEnq_parentChildren00(x_23);
        let x_25 <- releaseMSHR_00(x_4);
    endrule

    rule rule_exec_00_27001;
        $display ("Rule fired: rule_exec_00_27001 at %t", $time);
        let x_0 <- deq_fifoL2E_00();
        Struct6 x_1 = ((x_0).lr_ir_pp);
        Bit#(3) x_2 = ((x_1).ir_msg_from);
        Struct1 x_3 = ((x_1).ir_msg);
        Bit#(4) x_4 = ((x_1).ir_mshr_id);
        Bool x_5 = ((x_1).ir_is_rs_rel);
        when (! (x_5), noAction);
        Struct9 x_6 = ((x_0).lr_ir);
        Struct11 x_7 = ((x_6).info);
        Struct5 x_8 = ((x_1).ir_by_victim);
        Vector#(4, Bit#(64)) x_9 = ((x_0).lr_value);
        let x_10 <- getMSHR_00(x_4);
        let x_11 <- getMSHRRq_00(x_4);
        let x_12 <- getMSHRFirstRs_00(x_4);
        Vector#(4, Bit#(64)) x_13 = (unpack(0));
        Bool x_14 = ((x_7).mesi_owned);
        Bit#(3) x_15 = ((x_7).mesi_status);
        Struct17 x_16 = (Struct17 {dir_st : (((x_7).mesi_dir_st) ==
        ((Bit#(3))'(3'h0)) ? ((Bit#(3))'(3'h1)) : ((x_7).mesi_dir_st)),
        dir_excl : ((((x_7).mesi_dir_sharers)[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(1))'(1'h0)) : (((Bit#(1))'(1'h1)) +
        ((((((x_7).mesi_dir_sharers)[1:1])[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(1))'(1'h0)) : (((Bit#(1))'(1'h1)) + (unpack(0))))))),
        dir_sharers : (x_7).mesi_dir_sharers});
        when ((x_2) == ((Bit#(3))'(3'h1)), noAction);
        when (((x_3).id) == ((Bit#(6))'(6'h14)), noAction);
        when (! ((x_3).type_), noAction);
        when ((((((x_16).dir_st) == ((Bit#(3))'(3'h4))) && (((x_16).dir_excl)
        == ((Bit#(1))'(1'h1))) ? ((Bit#(3))'(3'h4)) : (((((x_16).dir_st) ==
        ((Bit#(3))'(3'h3))) && (((x_16).dir_excl) == ((Bit#(1))'(1'h1))) ?
        ((Bit#(3))'(3'h3)) : (((((x_16).dir_st) == ((Bit#(3))'(3'h2))) &&
        ((((x_16).dir_sharers) | (((Bit#(2))'(2'h1)) << ((Bit#(1))'(1'h1))))
        == ((x_16).dir_sharers)) ? ((Bit#(3))'(3'h2)) :
        ((Bit#(3))'(3'h1)))))))) == ((Bit#(3))'(3'h3)), noAction);
        Struct1 x_17 = (x_3);
        Struct18 x_18 = (Struct18 {addr : (x_3).addr, info_write :
        (Bool)'(False), info_hit : (x_6).info_hit, info_way : (x_6).info_way,
        edir_hit : (x_6).edir_hit, edir_way : (x_6).edir_way, edir_slot :
        (x_6).edir_slot, info : (x_6).info, value_write : (Bool)'(False),
        value : unpack(0), may_victim : (x_6).may_victim, reps :
        (x_6).reps});
        Struct18 x_19 = (Struct18 {addr : (x_18).addr, info_write :
        (Bool)'(True), info_hit : (x_18).info_hit, info_way :
        (x_18).info_way, edir_hit : (x_18).edir_hit, edir_way :
        (x_18).edir_way, edir_slot : (x_18).edir_slot, info : Struct11
        {mesi_owned : ((x_18).info).mesi_owned, mesi_status :
        ((x_18).info).mesi_status, mesi_dir_st : (Struct17 {dir_st :
        (Bit#(3))'(3'h1), dir_excl : unpack(0), dir_sharers :
        unpack(0)}).dir_st, mesi_dir_sharers : (((Struct17 {dir_st :
        (Bit#(3))'(3'h1), dir_excl : unpack(0), dir_sharers :
        unpack(0)}).dir_st) == ((Bit#(3))'(3'h2)) ? ((Struct17 {dir_st :
        (Bit#(3))'(3'h1), dir_excl : unpack(0), dir_sharers :
        unpack(0)}).dir_sharers) : (((Bit#(2))'(2'h1)) << ((Struct17 {dir_st
        : (Bit#(3))'(3'h1), dir_excl : unpack(0), dir_sharers :
        unpack(0)}).dir_excl)))}, value_write : (x_18).value_write, value :
        (x_18).value, may_victim : (x_18).may_victim, reps :
        (x_18).reps});
        Struct18 x_20 = (Struct18 {addr : (x_19).addr, info_write :
        (Bool)'(True), info_hit : (x_19).info_hit, info_way :
        (x_19).info_way, edir_hit : (x_19).edir_hit, edir_way :
        (x_19).edir_way, edir_slot : (x_19).edir_slot, info : Struct11
        {mesi_owned : ((x_19).info).mesi_owned, mesi_status :
        (Bit#(3))'(3'h3), mesi_dir_st : ((x_19).info).mesi_dir_st,
        mesi_dir_sharers : ((x_19).info).mesi_dir_sharers}, value_write :
        (x_19).value_write, value : (x_19).value, may_victim :
        (x_19).may_victim, reps :
        (x_19).reps});
        let x_23 = ?;
        if ((x_8).valid) begin
            let x_21 <- victims__00__setVictim(Struct19 {victim_idx :
            (x_8).data, victim_info : (x_20).info, victim_value :
            ((x_20).value_write ? ((x_20).value) : (x_9))});
            x_23 = x_9;
        end else begin
            let x_22 <- cache__00__valueRsLineRq(x_20);
            x_23 = x_22;
        end
        Struct20 x_24 = (Struct20 {enq_type : ((((Bit#(3))'(3'h5))[2:1]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : (((((Bit#(3))'(3'h5))[2:1])
        == ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : ((Bit#(3))'(3'h5))[0:0], enq_msg : Struct1 {id :
        (Bit#(6))'(6'h16), type_ : (Bool)'(True), addr : (x_17).addr, value :
        unpack(0)}});
        let x_25 <- makeEnq_parentChildren00(x_24);
        let x_26 <- releaseMSHR_00(x_4);
    endrule

    rule rule_exec_00_28001;
        $display ("Rule fired: rule_exec_00_28001 at %t", $time);
        let x_0 <- deq_fifoL2E_00();
        Struct6 x_1 = ((x_0).lr_ir_pp);
        Bit#(3) x_2 = ((x_1).ir_msg_from);
        Struct1 x_3 = ((x_1).ir_msg);
        Bit#(4) x_4 = ((x_1).ir_mshr_id);
        Bool x_5 = ((x_1).ir_is_rs_rel);
        when (! (x_5), noAction);
        Struct9 x_6 = ((x_0).lr_ir);
        Struct11 x_7 = ((x_6).info);
        Struct5 x_8 = ((x_1).ir_by_victim);
        Vector#(4, Bit#(64)) x_9 = ((x_0).lr_value);
        let x_10 <- getMSHR_00(x_4);
        let x_11 <- getMSHRRq_00(x_4);
        let x_12 <- getMSHRFirstRs_00(x_4);
        Vector#(4, Bit#(64)) x_13 = (unpack(0));
        Bool x_14 = ((x_7).mesi_owned);
        Bit#(3) x_15 = ((x_7).mesi_status);
        Struct17 x_16 = (Struct17 {dir_st : (((x_7).mesi_dir_st) ==
        ((Bit#(3))'(3'h0)) ? ((Bit#(3))'(3'h1)) : ((x_7).mesi_dir_st)),
        dir_excl : ((((x_7).mesi_dir_sharers)[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(1))'(1'h0)) : (((Bit#(1))'(1'h1)) +
        ((((((x_7).mesi_dir_sharers)[1:1])[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(1))'(1'h0)) : (((Bit#(1))'(1'h1)) + (unpack(0))))))),
        dir_sharers : (x_7).mesi_dir_sharers});
        when ((x_2) == ((Bit#(3))'(3'h1)), noAction);
        when (((x_3).id) == ((Bit#(6))'(6'h15)), noAction);
        when (! ((x_3).type_), noAction);
        when ((((((x_16).dir_st) == ((Bit#(3))'(3'h4))) && (((x_16).dir_excl)
        == ((Bit#(1))'(1'h1))) ? ((Bit#(3))'(3'h4)) : (((((x_16).dir_st) ==
        ((Bit#(3))'(3'h3))) && (((x_16).dir_excl) == ((Bit#(1))'(1'h1))) ?
        ((Bit#(3))'(3'h3)) : (((((x_16).dir_st) == ((Bit#(3))'(3'h2))) &&
        ((((x_16).dir_sharers) | (((Bit#(2))'(2'h1)) << ((Bit#(1))'(1'h1))))
        == ((x_16).dir_sharers)) ? ((Bit#(3))'(3'h2)) :
        ((Bit#(3))'(3'h1)))))))) == ((Bit#(3))'(3'h1)), noAction);
        Struct1 x_17 = (x_3);
        Struct18 x_18 = (Struct18 {addr : (x_3).addr, info_write :
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
        Struct20 x_21 = (Struct20 {enq_type : ((((Bit#(3))'(3'h5))[2:1]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : (((((Bit#(3))'(3'h5))[2:1])
        == ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : ((Bit#(3))'(3'h5))[0:0], enq_msg : Struct1 {id :
        (Bit#(6))'(6'h16), type_ : (Bool)'(True), addr : (x_17).addr, value :
        unpack(0)}});
        let x_22 <- makeEnq_parentChildren00(x_21);
        let x_23 <- releaseMSHR_00(x_4);
    endrule

    rule rule_exec_00_290001;
        $display ("Rule fired: rule_exec_00_290001 at %t", $time);
        let x_0 <- deq_fifoL2E_00();
        Struct6 x_1 = ((x_0).lr_ir_pp);
        Bit#(3) x_2 = ((x_1).ir_msg_from);
        Struct1 x_3 = ((x_1).ir_msg);
        Bit#(4) x_4 = ((x_1).ir_mshr_id);
        Bool x_5 = ((x_1).ir_is_rs_rel);
        when (! (x_5), noAction);
        Struct9 x_6 = ((x_0).lr_ir);
        Struct11 x_7 = ((x_6).info);
        Struct5 x_8 = ((x_1).ir_by_victim);
        Vector#(4, Bit#(64)) x_9 = ((x_0).lr_value);
        let x_10 <- getMSHR_00(x_4);
        let x_11 <- getMSHRRq_00(x_4);
        let x_12 <- getMSHRFirstRs_00(x_4);
        Vector#(4, Bit#(64)) x_13 = (unpack(0));
        Bool x_14 = ((x_7).mesi_owned);
        Bit#(3) x_15 = ((x_7).mesi_status);
        Struct17 x_16 = (Struct17 {dir_st : (((x_7).mesi_dir_st) ==
        ((Bit#(3))'(3'h0)) ? ((Bit#(3))'(3'h1)) : ((x_7).mesi_dir_st)),
        dir_excl : ((((x_7).mesi_dir_sharers)[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(1))'(1'h0)) : (((Bit#(1))'(1'h1)) +
        ((((((x_7).mesi_dir_sharers)[1:1])[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(1))'(1'h0)) : (((Bit#(1))'(1'h1)) + (unpack(0))))))),
        dir_sharers : (x_7).mesi_dir_sharers});
        when ((x_2) == ((Bit#(3))'(3'h1)), noAction);
        when (((x_3).id) == ((Bit#(6))'(6'h15)), noAction);
        when (! ((x_3).type_), noAction);
        when (((x_14) == ((Bool)'(False))) && (((((((x_16).dir_st) ==
        ((Bit#(3))'(3'h4))) && (((x_16).dir_excl) == ((Bit#(1))'(1'h1))) ?
        ((Bit#(3))'(3'h4)) : (((((x_16).dir_st) == ((Bit#(3))'(3'h3))) &&
        (((x_16).dir_excl) == ((Bit#(1))'(1'h1))) ? ((Bit#(3))'(3'h3)) :
        (((((x_16).dir_st) == ((Bit#(3))'(3'h2))) && ((((x_16).dir_sharers) |
        (((Bit#(2))'(2'h1)) << ((Bit#(1))'(1'h1)))) == ((x_16).dir_sharers))
        ? ((Bit#(3))'(3'h2)) : ((Bit#(3))'(3'h1)))))))) ==
        ((Bit#(3))'(3'h2))) && (((x_16).dir_sharers) == (((Bit#(2))'(2'h1))
        << ((Bit#(1))'(1'h1))))), noAction);
        Struct1 x_17 = (x_3);
        Struct18 x_18 = (Struct18 {addr : (x_3).addr, info_write :
        (Bool)'(False), info_hit : (x_6).info_hit, info_way : (x_6).info_way,
        edir_hit : (x_6).edir_hit, edir_way : (x_6).edir_way, edir_slot :
        (x_6).edir_slot, info : (x_6).info, value_write : (Bool)'(False),
        value : unpack(0), may_victim : (x_6).may_victim, reps :
        (x_6).reps});
        Struct18 x_19 = (Struct18 {addr : (x_18).addr, info_write :
        (Bool)'(True), info_hit : (x_18).info_hit, info_way :
        (x_18).info_way, edir_hit : (x_18).edir_hit, edir_way :
        (x_18).edir_way, edir_slot : (x_18).edir_slot, info : Struct11
        {mesi_owned : ((x_18).info).mesi_owned, mesi_status :
        ((x_18).info).mesi_status, mesi_dir_st : (Struct17 {dir_st :
        (Bit#(3))'(3'h1), dir_excl : unpack(0), dir_sharers :
        unpack(0)}).dir_st, mesi_dir_sharers : (((Struct17 {dir_st :
        (Bit#(3))'(3'h1), dir_excl : unpack(0), dir_sharers :
        unpack(0)}).dir_st) == ((Bit#(3))'(3'h2)) ? ((Struct17 {dir_st :
        (Bit#(3))'(3'h1), dir_excl : unpack(0), dir_sharers :
        unpack(0)}).dir_sharers) : (((Bit#(2))'(2'h1)) << ((Struct17 {dir_st
        : (Bit#(3))'(3'h1), dir_excl : unpack(0), dir_sharers :
        unpack(0)}).dir_excl)))}, value_write : (x_18).value_write, value :
        (x_18).value, may_victim : (x_18).may_victim, reps :
        (x_18).reps});
        let x_22 = ?;
        if ((x_8).valid) begin
            let x_20 <- victims__00__setVictim(Struct19 {victim_idx :
            (x_8).data, victim_info : (x_19).info, victim_value :
            ((x_19).value_write ? ((x_19).value) : (x_9))});
            x_22 = x_9;
        end else begin
            let x_21 <- cache__00__valueRsLineRq(x_19);
            x_22 = x_21;
        end
        Struct20 x_23 = (Struct20 {enq_type : ((((Bit#(3))'(3'h5))[2:1]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : (((((Bit#(3))'(3'h5))[2:1])
        == ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : ((Bit#(3))'(3'h5))[0:0], enq_msg : Struct1 {id :
        (Bit#(6))'(6'h16), type_ : (Bool)'(True), addr : (x_17).addr, value :
        unpack(0)}});
        let x_24 <- makeEnq_parentChildren00(x_23);
        let x_25 <- releaseMSHR_00(x_4);
    endrule

    rule rule_exec_00_291001;
        $display ("Rule fired: rule_exec_00_291001 at %t", $time);
        let x_0 <- deq_fifoL2E_00();
        Struct6 x_1 = ((x_0).lr_ir_pp);
        Bit#(3) x_2 = ((x_1).ir_msg_from);
        Struct1 x_3 = ((x_1).ir_msg);
        Bit#(4) x_4 = ((x_1).ir_mshr_id);
        Bool x_5 = ((x_1).ir_is_rs_rel);
        when (! (x_5), noAction);
        Struct9 x_6 = ((x_0).lr_ir);
        Struct11 x_7 = ((x_6).info);
        Struct5 x_8 = ((x_1).ir_by_victim);
        Vector#(4, Bit#(64)) x_9 = ((x_0).lr_value);
        let x_10 <- getMSHR_00(x_4);
        let x_11 <- getMSHRRq_00(x_4);
        let x_12 <- getMSHRFirstRs_00(x_4);
        Vector#(4, Bit#(64)) x_13 = (unpack(0));
        Bool x_14 = ((x_7).mesi_owned);
        Bit#(3) x_15 = ((x_7).mesi_status);
        Struct17 x_16 = (Struct17 {dir_st : (((x_7).mesi_dir_st) ==
        ((Bit#(3))'(3'h0)) ? ((Bit#(3))'(3'h1)) : ((x_7).mesi_dir_st)),
        dir_excl : ((((x_7).mesi_dir_sharers)[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(1))'(1'h0)) : (((Bit#(1))'(1'h1)) +
        ((((((x_7).mesi_dir_sharers)[1:1])[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(1))'(1'h0)) : (((Bit#(1))'(1'h1)) + (unpack(0))))))),
        dir_sharers : (x_7).mesi_dir_sharers});
        when ((x_2) == ((Bit#(3))'(3'h1)), noAction);
        when (((x_3).id) == ((Bit#(6))'(6'h15)), noAction);
        when (! ((x_3).type_), noAction);
        when (((((((x_16).dir_st) == ((Bit#(3))'(3'h4))) &&
        (((x_16).dir_excl) == ((Bit#(1))'(1'h1))) ? ((Bit#(3))'(3'h4)) :
        (((((x_16).dir_st) == ((Bit#(3))'(3'h3))) && (((x_16).dir_excl) ==
        ((Bit#(1))'(1'h1))) ? ((Bit#(3))'(3'h3)) : (((((x_16).dir_st) ==
        ((Bit#(3))'(3'h2))) && ((((x_16).dir_sharers) | (((Bit#(2))'(2'h1))
        << ((Bit#(1))'(1'h1)))) == ((x_16).dir_sharers)) ? ((Bit#(3))'(3'h2))
        : ((Bit#(3))'(3'h1)))))))) == ((Bit#(3))'(3'h2))) &&
        (((Bit#(2))'(2'h1)) < ((((((x_16).dir_sharers)[0:0]) ==
        ((Bit#(1))'(1'h1)) ? ((Bit#(2))'(2'h1)) : ((Bit#(2))'(2'h0)))) +
        (((((((x_16).dir_sharers)[1:1])[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(2))'(2'h1)) : ((Bit#(2))'(2'h0)))) + (unpack(0))))),
        noAction);
        Struct1 x_17 = (x_3);
        Struct18 x_18 = (Struct18 {addr : (x_3).addr, info_write :
        (Bool)'(False), info_hit : (x_6).info_hit, info_way : (x_6).info_way,
        edir_hit : (x_6).edir_hit, edir_way : (x_6).edir_way, edir_slot :
        (x_6).edir_slot, info : (x_6).info, value_write : (Bool)'(False),
        value : unpack(0), may_victim : (x_6).may_victim, reps :
        (x_6).reps});
        Struct18 x_19 = (Struct18 {addr : (x_18).addr, info_write :
        (Bool)'(True), info_hit : (x_18).info_hit, info_way :
        (x_18).info_way, edir_hit : (x_18).edir_hit, edir_way :
        (x_18).edir_way, edir_slot : (x_18).edir_slot, info : Struct11
        {mesi_owned : ((x_18).info).mesi_owned, mesi_status :
        ((x_18).info).mesi_status, mesi_dir_st : (Struct17 {dir_st :
        (Bit#(3))'(3'h2), dir_excl : (x_16).dir_excl, dir_sharers :
        ((x_16).dir_sharers) & (~(((Bit#(2))'(2'h1)) <<
        ((Bit#(1))'(1'h1))))}).dir_st, mesi_dir_sharers : (((Struct17 {dir_st
        : (Bit#(3))'(3'h2), dir_excl : (x_16).dir_excl, dir_sharers :
        ((x_16).dir_sharers) & (~(((Bit#(2))'(2'h1)) <<
        ((Bit#(1))'(1'h1))))}).dir_st) == ((Bit#(3))'(3'h2)) ? ((Struct17
        {dir_st : (Bit#(3))'(3'h2), dir_excl : (x_16).dir_excl, dir_sharers :
        ((x_16).dir_sharers) & (~(((Bit#(2))'(2'h1)) <<
        ((Bit#(1))'(1'h1))))}).dir_sharers) : (((Bit#(2))'(2'h1)) <<
        ((Struct17 {dir_st : (Bit#(3))'(3'h2), dir_excl : (x_16).dir_excl,
        dir_sharers : ((x_16).dir_sharers) & (~(((Bit#(2))'(2'h1)) <<
        ((Bit#(1))'(1'h1))))}).dir_excl)))}, value_write :
        (x_18).value_write, value : (x_18).value, may_victim :
        (x_18).may_victim, reps :
        (x_18).reps});
        let x_22 = ?;
        if ((x_8).valid) begin
            let x_20 <- victims__00__setVictim(Struct19 {victim_idx :
            (x_8).data, victim_info : (x_19).info, victim_value :
            ((x_19).value_write ? ((x_19).value) : (x_9))});
            x_22 = x_9;
        end else begin
            let x_21 <- cache__00__valueRsLineRq(x_19);
            x_22 = x_21;
        end
        Struct20 x_23 = (Struct20 {enq_type : ((((Bit#(3))'(3'h5))[2:1]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : (((((Bit#(3))'(3'h5))[2:1])
        == ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : ((Bit#(3))'(3'h5))[0:0], enq_msg : Struct1 {id :
        (Bit#(6))'(6'h16), type_ : (Bool)'(True), addr : (x_17).addr, value :
        unpack(0)}});
        let x_24 <- makeEnq_parentChildren00(x_23);
        let x_25 <- releaseMSHR_00(x_4);
    endrule

    rule rule_exec_00_210001;
        $display ("Rule fired: rule_exec_00_210001 at %t", $time);
        let x_0 <- deq_fifoL2E_00();
        Struct6 x_1 = ((x_0).lr_ir_pp);
        Bit#(3) x_2 = ((x_1).ir_msg_from);
        Struct1 x_3 = ((x_1).ir_msg);
        Bit#(4) x_4 = ((x_1).ir_mshr_id);
        Bool x_5 = ((x_1).ir_is_rs_rel);
        when (! (x_5), noAction);
        Struct9 x_6 = ((x_0).lr_ir);
        Struct11 x_7 = ((x_6).info);
        Struct5 x_8 = ((x_1).ir_by_victim);
        Vector#(4, Bit#(64)) x_9 = ((x_0).lr_value);
        let x_10 <- getMSHR_00(x_4);
        let x_11 <- getMSHRRq_00(x_4);
        let x_12 <- getMSHRFirstRs_00(x_4);
        Vector#(4, Bit#(64)) x_13 = (unpack(0));
        Bool x_14 = ((x_7).mesi_owned);
        Bit#(3) x_15 = ((x_7).mesi_status);
        Struct17 x_16 = (Struct17 {dir_st : (((x_7).mesi_dir_st) ==
        ((Bit#(3))'(3'h0)) ? ((Bit#(3))'(3'h1)) : ((x_7).mesi_dir_st)),
        dir_excl : ((((x_7).mesi_dir_sharers)[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(1))'(1'h0)) : (((Bit#(1))'(1'h1)) +
        ((((((x_7).mesi_dir_sharers)[1:1])[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(1))'(1'h0)) : (((Bit#(1))'(1'h1)) + (unpack(0))))))),
        dir_sharers : (x_7).mesi_dir_sharers});
        when ((x_2) == ((Bit#(3))'(3'h1)), noAction);
        when (((x_3).id) == ((Bit#(6))'(6'h15)), noAction);
        when (! ((x_3).type_), noAction);
        when (((x_14) == ((Bool)'(True))) && (((x_15) == ((Bit#(3))'(3'h2)))
        && (((((((x_16).dir_st) == ((Bit#(3))'(3'h4))) && (((x_16).dir_excl)
        == ((Bit#(1))'(1'h1))) ? ((Bit#(3))'(3'h4)) : (((((x_16).dir_st) ==
        ((Bit#(3))'(3'h3))) && (((x_16).dir_excl) == ((Bit#(1))'(1'h1))) ?
        ((Bit#(3))'(3'h3)) : (((((x_16).dir_st) == ((Bit#(3))'(3'h2))) &&
        ((((x_16).dir_sharers) | (((Bit#(2))'(2'h1)) << ((Bit#(1))'(1'h1))))
        == ((x_16).dir_sharers)) ? ((Bit#(3))'(3'h2)) :
        ((Bit#(3))'(3'h1)))))))) == ((Bit#(3))'(3'h2))) &&
        (((x_16).dir_sharers) == (((Bit#(2))'(2'h1)) <<
        ((Bit#(1))'(1'h1)))))), noAction);
        Struct1 x_17 = (x_3);
        Struct18 x_18 = (Struct18 {addr : (x_3).addr, info_write :
        (Bool)'(False), info_hit : (x_6).info_hit, info_way : (x_6).info_way,
        edir_hit : (x_6).edir_hit, edir_way : (x_6).edir_way, edir_slot :
        (x_6).edir_slot, info : (x_6).info, value_write : (Bool)'(False),
        value : unpack(0), may_victim : (x_6).may_victim, reps :
        (x_6).reps});
        Struct18 x_19 = (Struct18 {addr : (x_18).addr, info_write :
        (Bool)'(True), info_hit : (x_18).info_hit, info_way :
        (x_18).info_way, edir_hit : (x_18).edir_hit, edir_way :
        (x_18).edir_way, edir_slot : (x_18).edir_slot, info : Struct11
        {mesi_owned : ((x_18).info).mesi_owned, mesi_status :
        ((x_18).info).mesi_status, mesi_dir_st : (Struct17 {dir_st :
        (Bit#(3))'(3'h1), dir_excl : unpack(0), dir_sharers :
        unpack(0)}).dir_st, mesi_dir_sharers : (((Struct17 {dir_st :
        (Bit#(3))'(3'h1), dir_excl : unpack(0), dir_sharers :
        unpack(0)}).dir_st) == ((Bit#(3))'(3'h2)) ? ((Struct17 {dir_st :
        (Bit#(3))'(3'h1), dir_excl : unpack(0), dir_sharers :
        unpack(0)}).dir_sharers) : (((Bit#(2))'(2'h1)) << ((Struct17 {dir_st
        : (Bit#(3))'(3'h1), dir_excl : unpack(0), dir_sharers :
        unpack(0)}).dir_excl)))}, value_write : (x_18).value_write, value :
        (x_18).value, may_victim : (x_18).may_victim, reps :
        (x_18).reps});
        Struct18 x_20 = (Struct18 {addr : (x_19).addr, info_write :
        (Bool)'(True), info_hit : (x_19).info_hit, info_way :
        (x_19).info_way, edir_hit : (x_19).edir_hit, edir_way :
        (x_19).edir_way, edir_slot : (x_19).edir_slot, info : Struct11
        {mesi_owned : ((x_19).info).mesi_owned, mesi_status :
        (Bit#(3))'(3'h4), mesi_dir_st : ((x_19).info).mesi_dir_st,
        mesi_dir_sharers : ((x_19).info).mesi_dir_sharers}, value_write :
        (x_19).value_write, value : (x_19).value, may_victim :
        (x_19).may_victim, reps :
        (x_19).reps});
        let x_23 = ?;
        if ((x_8).valid) begin
            let x_21 <- victims__00__setVictim(Struct19 {victim_idx :
            (x_8).data, victim_info : (x_20).info, victim_value :
            ((x_20).value_write ? ((x_20).value) : (x_9))});
            x_23 = x_9;
        end else begin
            let x_22 <- cache__00__valueRsLineRq(x_20);
            x_23 = x_22;
        end
        Struct20 x_24 = (Struct20 {enq_type : ((((Bit#(3))'(3'h5))[2:1]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : (((((Bit#(3))'(3'h5))[2:1])
        == ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : ((Bit#(3))'(3'h5))[0:0], enq_msg : Struct1 {id :
        (Bit#(6))'(6'h16), type_ : (Bool)'(True), addr : (x_17).addr, value :
        unpack(0)}});
        let x_25 <- makeEnq_parentChildren00(x_24);
        let x_26 <- releaseMSHR_00(x_4);
    endrule

    rule rule_exec_00_211001;
        $display ("Rule fired: rule_exec_00_211001 at %t", $time);
        let x_0 <- deq_fifoL2E_00();
        Struct6 x_1 = ((x_0).lr_ir_pp);
        Bit#(3) x_2 = ((x_1).ir_msg_from);
        Struct1 x_3 = ((x_1).ir_msg);
        Bit#(4) x_4 = ((x_1).ir_mshr_id);
        Bool x_5 = ((x_1).ir_is_rs_rel);
        when (! (x_5), noAction);
        Struct9 x_6 = ((x_0).lr_ir);
        Struct11 x_7 = ((x_6).info);
        Struct5 x_8 = ((x_1).ir_by_victim);
        Vector#(4, Bit#(64)) x_9 = ((x_0).lr_value);
        let x_10 <- getMSHR_00(x_4);
        let x_11 <- getMSHRRq_00(x_4);
        let x_12 <- getMSHRFirstRs_00(x_4);
        Vector#(4, Bit#(64)) x_13 = (unpack(0));
        Bool x_14 = ((x_7).mesi_owned);
        Bit#(3) x_15 = ((x_7).mesi_status);
        Struct17 x_16 = (Struct17 {dir_st : (((x_7).mesi_dir_st) ==
        ((Bit#(3))'(3'h0)) ? ((Bit#(3))'(3'h1)) : ((x_7).mesi_dir_st)),
        dir_excl : ((((x_7).mesi_dir_sharers)[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(1))'(1'h0)) : (((Bit#(1))'(1'h1)) +
        ((((((x_7).mesi_dir_sharers)[1:1])[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(1))'(1'h0)) : (((Bit#(1))'(1'h1)) + (unpack(0))))))),
        dir_sharers : (x_7).mesi_dir_sharers});
        when ((x_2) == ((Bit#(3))'(3'h1)), noAction);
        when (((x_3).id) == ((Bit#(6))'(6'h15)), noAction);
        when (! ((x_3).type_), noAction);
        when (! ((((((x_16).dir_st) == ((Bit#(3))'(3'h4))) &&
        (((x_16).dir_excl) == ((Bit#(1))'(1'h1))) ? ((Bit#(3))'(3'h4)) :
        (((((x_16).dir_st) == ((Bit#(3))'(3'h3))) && (((x_16).dir_excl) ==
        ((Bit#(1))'(1'h1))) ? ((Bit#(3))'(3'h3)) : (((((x_16).dir_st) ==
        ((Bit#(3))'(3'h2))) && ((((x_16).dir_sharers) | (((Bit#(2))'(2'h1))
        << ((Bit#(1))'(1'h1)))) == ((x_16).dir_sharers)) ? ((Bit#(3))'(3'h2))
        : ((Bit#(3))'(3'h1)))))))) < ((Bit#(3))'(3'h3))), noAction);
        Struct1 x_17 = (x_3);
        Struct18 x_18 = (Struct18 {addr : (x_3).addr, info_write :
        (Bool)'(False), info_hit : (x_6).info_hit, info_way : (x_6).info_way,
        edir_hit : (x_6).edir_hit, edir_way : (x_6).edir_way, edir_slot :
        (x_6).edir_slot, info : (x_6).info, value_write : (Bool)'(False),
        value : unpack(0), may_victim : (x_6).may_victim, reps :
        (x_6).reps});
        Struct18 x_19 = (Struct18 {addr : (x_18).addr, info_write :
        (x_18).info_write, info_hit : (x_18).info_hit, info_way :
        (x_18).info_way, edir_hit : (x_18).edir_hit, edir_way :
        (x_18).edir_way, edir_slot : (x_18).edir_slot, info : (x_18).info,
        value_write : (Bool)'(True), value : (x_17).value, may_victim :
        (x_18).may_victim, reps : (x_18).reps});
        Struct18 x_20 = (Struct18 {addr : (x_19).addr, info_write :
        (Bool)'(True), info_hit : (x_19).info_hit, info_way :
        (x_19).info_way, edir_hit : (x_19).edir_hit, edir_way :
        (x_19).edir_way, edir_slot : (x_19).edir_slot, info : Struct11
        {mesi_owned : ((x_19).info).mesi_owned, mesi_status :
        (Bit#(3))'(3'h4), mesi_dir_st : ((x_19).info).mesi_dir_st,
        mesi_dir_sharers : ((x_19).info).mesi_dir_sharers}, value_write :
        (x_19).value_write, value : (x_19).value, may_victim :
        (x_19).may_victim, reps : (x_19).reps});
        Struct18 x_21 = (Struct18 {addr : (x_20).addr, info_write :
        (Bool)'(True), info_hit : (x_20).info_hit, info_way :
        (x_20).info_way, edir_hit : (x_20).edir_hit, edir_way :
        (x_20).edir_way, edir_slot : (x_20).edir_slot, info : Struct11
        {mesi_owned : (Bool)'(True), mesi_status : ((x_20).info).mesi_status,
        mesi_dir_st : ((x_20).info).mesi_dir_st, mesi_dir_sharers :
        ((x_20).info).mesi_dir_sharers}, value_write : (x_20).value_write,
        value : (x_20).value, may_victim : (x_20).may_victim, reps :
        (x_20).reps});
        Struct18 x_22 = (Struct18 {addr : (x_21).addr, info_write :
        (Bool)'(True), info_hit : (x_21).info_hit, info_way :
        (x_21).info_way, edir_hit : (x_21).edir_hit, edir_way :
        (x_21).edir_way, edir_slot : (x_21).edir_slot, info : Struct11
        {mesi_owned : ((x_21).info).mesi_owned, mesi_status :
        ((x_21).info).mesi_status, mesi_dir_st : (Struct17 {dir_st :
        (Bit#(3))'(3'h1), dir_excl : unpack(0), dir_sharers :
        unpack(0)}).dir_st, mesi_dir_sharers : (((Struct17 {dir_st :
        (Bit#(3))'(3'h1), dir_excl : unpack(0), dir_sharers :
        unpack(0)}).dir_st) == ((Bit#(3))'(3'h2)) ? ((Struct17 {dir_st :
        (Bit#(3))'(3'h1), dir_excl : unpack(0), dir_sharers :
        unpack(0)}).dir_sharers) : (((Bit#(2))'(2'h1)) << ((Struct17 {dir_st
        : (Bit#(3))'(3'h1), dir_excl : unpack(0), dir_sharers :
        unpack(0)}).dir_excl)))}, value_write : (x_21).value_write, value :
        (x_21).value, may_victim : (x_21).may_victim, reps :
        (x_21).reps});
        let x_25 = ?;
        if ((x_8).valid) begin
            let x_23 <- victims__00__setVictim(Struct19 {victim_idx :
            (x_8).data, victim_info : (x_22).info, victim_value :
            ((x_22).value_write ? ((x_22).value) : (x_9))});
            x_25 = x_9;
        end else begin
            let x_24 <- cache__00__valueRsLineRq(x_22);
            x_25 = x_24;
        end
        Struct20 x_26 = (Struct20 {enq_type : ((((Bit#(3))'(3'h5))[2:1]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : (((((Bit#(3))'(3'h5))[2:1])
        == ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : ((Bit#(3))'(3'h5))[0:0], enq_msg : Struct1 {id :
        (Bit#(6))'(6'h16), type_ : (Bool)'(True), addr : (x_17).addr, value :
        unpack(0)}});
        let x_27 <- makeEnq_parentChildren00(x_26);
        let x_28 <- releaseMSHR_00(x_4);
    endrule

    rule rule_exec_00_020;
        $display ("Rule fired: rule_exec_00_020 at %t", $time);
        let x_0 <- deq_fifoL2E_00();
        Struct6 x_1 = ((x_0).lr_ir_pp);
        Bit#(3) x_2 = ((x_1).ir_msg_from);
        Struct1 x_3 = ((x_1).ir_msg);
        Bit#(4) x_4 = ((x_1).ir_mshr_id);
        Bool x_5 = ((x_1).ir_is_rs_rel);
        when (! (x_5), noAction);
        Struct9 x_6 = ((x_0).lr_ir);
        Struct11 x_7 = ((x_6).info);
        Struct5 x_8 = ((x_1).ir_by_victim);
        Vector#(4, Bit#(64)) x_9 = ((x_0).lr_value);
        let x_10 <- getMSHR_00(x_4);
        let x_11 <- getMSHRRq_00(x_4);
        let x_12 <- getMSHRFirstRs_00(x_4);
        Vector#(4, Bit#(64)) x_13 = (unpack(0));
        Bool x_14 = ((x_7).mesi_owned);
        Bit#(3) x_15 = ((x_7).mesi_status);
        Struct17 x_16 = (Struct17 {dir_st : (((x_7).mesi_dir_st) ==
        ((Bit#(3))'(3'h0)) ? ((Bit#(3))'(3'h1)) : ((x_7).mesi_dir_st)),
        dir_excl : ((((x_7).mesi_dir_sharers)[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(1))'(1'h0)) : (((Bit#(1))'(1'h1)) +
        ((((((x_7).mesi_dir_sharers)[1:1])[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(1))'(1'h0)) : (((Bit#(1))'(1'h1)) + (unpack(0))))))),
        dir_sharers : (x_7).mesi_dir_sharers});
        when ((x_2) == ({((Bit#(2))'(2'h2)),((Bit#(1))'(1'h0))}),
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
        Bit#(3) x_19 = ({((Bit#(2))'(2'h2)),(((x_10).m_qidx)[0:0])});
        Struct18 x_20 = (Struct18 {addr : (x_3).addr, info_write :
        (Bool)'(False), info_hit : (x_6).info_hit, info_way : (x_6).info_way,
        edir_hit : (x_6).edir_hit, edir_way : (x_6).edir_way, edir_slot :
        (x_6).edir_slot, info : (x_6).info, value_write : (Bool)'(False),
        value : unpack(0), may_victim : (x_6).may_victim, reps :
        (x_6).reps});
        Struct18 x_21 = (Struct18 {addr : (x_20).addr, info_write :
        (Bool)'(True), info_hit : (x_20).info_hit, info_way :
        (x_20).info_way, edir_hit : (x_20).edir_hit, edir_way :
        (x_20).edir_way, edir_slot : (x_20).edir_slot, info : Struct11
        {mesi_owned : ((x_20).info).mesi_owned, mesi_status :
        ((x_20).info).mesi_status, mesi_dir_st : (Struct17 {dir_st :
        (Bit#(3))'(3'h2), dir_excl : (x_16).dir_excl, dir_sharers :
        (((x_16).dir_st) == ((Bit#(3))'(3'h2)) ? (((x_16).dir_sharers) |
        (((Bit#(2))'(2'h1)) << ((x_19)[0:0]))) : (((Bit#(2))'(2'h1)) <<
        ((x_19)[0:0])))}).dir_st, mesi_dir_sharers : (((Struct17 {dir_st :
        (Bit#(3))'(3'h2), dir_excl : (x_16).dir_excl, dir_sharers :
        (((x_16).dir_st) == ((Bit#(3))'(3'h2)) ? (((x_16).dir_sharers) |
        (((Bit#(2))'(2'h1)) << ((x_19)[0:0]))) : (((Bit#(2))'(2'h1)) <<
        ((x_19)[0:0])))}).dir_st) == ((Bit#(3))'(3'h2)) ? ((Struct17 {dir_st
        : (Bit#(3))'(3'h2), dir_excl : (x_16).dir_excl, dir_sharers :
        (((x_16).dir_st) == ((Bit#(3))'(3'h2)) ? (((x_16).dir_sharers) |
        (((Bit#(2))'(2'h1)) << ((x_19)[0:0]))) : (((Bit#(2))'(2'h1)) <<
        ((x_19)[0:0])))}).dir_sharers) : (((Bit#(2))'(2'h1)) << ((Struct17
        {dir_st : (Bit#(3))'(3'h2), dir_excl : (x_16).dir_excl, dir_sharers :
        (((x_16).dir_st) == ((Bit#(3))'(3'h2)) ? (((x_16).dir_sharers) |
        (((Bit#(2))'(2'h1)) << ((x_19)[0:0]))) : (((Bit#(2))'(2'h1)) <<
        ((x_19)[0:0])))}).dir_excl)))}, value_write : (x_20).value_write,
        value : (x_20).value, may_victim : (x_20).may_victim, reps :
        (x_20).reps});
        Struct18 x_22 = (Struct18 {addr : (x_21).addr, info_write :
        (Bool)'(True), info_hit : (x_21).info_hit, info_way :
        (x_21).info_way, edir_hit : (x_21).edir_hit, edir_way :
        (x_21).edir_way, edir_slot : (x_21).edir_slot, info : Struct11
        {mesi_owned : ((x_21).info).mesi_owned, mesi_status :
        (Bit#(3))'(3'h2), mesi_dir_st : ((x_21).info).mesi_dir_st,
        mesi_dir_sharers : ((x_21).info).mesi_dir_sharers}, value_write :
        (x_21).value_write, value : (x_21).value, may_victim :
        (x_21).may_victim, reps : (x_21).reps});
        Struct18 x_23 = (Struct18 {addr : (x_22).addr, info_write :
        (Bool)'(True), info_hit : (x_22).info_hit, info_way :
        (x_22).info_way, edir_hit : (x_22).edir_hit, edir_way :
        (x_22).edir_way, edir_slot : (x_22).edir_slot, info : Struct11
        {mesi_owned : (Bool)'(False), mesi_status :
        ((x_22).info).mesi_status, mesi_dir_st : ((x_22).info).mesi_dir_st,
        mesi_dir_sharers : ((x_22).info).mesi_dir_sharers}, value_write :
        (x_22).value_write, value : (x_22).value, may_victim :
        (x_22).may_victim, reps : (x_22).reps});
        Struct18 x_24 = (Struct18 {addr : (x_23).addr, info_write :
        (x_23).info_write, info_hit : (x_23).info_hit, info_way :
        (x_23).info_way, edir_hit : (x_23).edir_hit, edir_way :
        (x_23).edir_way, edir_slot : (x_23).edir_slot, info : (x_23).info,
        value_write : (Bool)'(True), value : (x_17).value, may_victim :
        (x_23).may_victim, reps :
        (x_23).reps});
        let x_27 = ?;
        if ((x_8).valid) begin
            let x_25 <- victims__00__setVictim(Struct19 {victim_idx :
            (x_8).data, victim_info : (x_24).info, victim_value :
            ((x_24).value_write ? ((x_24).value) : (x_9))});
            x_27 = x_9;
        end else begin
            let x_26 <- cache__00__valueRsLineRq(x_24);
            x_27 = x_26;
        end
        let x_28 <- releaseMSHR_00(x_4);
        Struct20 x_29 = (Struct20 {enq_type : (((x_19)[2:1]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : ((((x_19)[2:1]) ==
        ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : (x_19)[0:0], enq_msg : Struct1 {id : (Bit#(6))'(6'h3),
        type_ : (Bool)'(True), addr : (x_17).addr, value :
        (x_17).value}});
        let x_30 <- makeEnq_parentChildren00(x_29);
    endrule

    rule rule_exec_00_021;
        $display ("Rule fired: rule_exec_00_021 at %t", $time);
        let x_0 <- deq_fifoL2E_00();
        Struct6 x_1 = ((x_0).lr_ir_pp);
        Bit#(3) x_2 = ((x_1).ir_msg_from);
        Struct1 x_3 = ((x_1).ir_msg);
        Bit#(4) x_4 = ((x_1).ir_mshr_id);
        Bool x_5 = ((x_1).ir_is_rs_rel);
        when (! (x_5), noAction);
        Struct9 x_6 = ((x_0).lr_ir);
        Struct11 x_7 = ((x_6).info);
        Struct5 x_8 = ((x_1).ir_by_victim);
        Vector#(4, Bit#(64)) x_9 = ((x_0).lr_value);
        let x_10 <- getMSHR_00(x_4);
        let x_11 <- getMSHRRq_00(x_4);
        let x_12 <- getMSHRFirstRs_00(x_4);
        Vector#(4, Bit#(64)) x_13 = (unpack(0));
        Bool x_14 = ((x_7).mesi_owned);
        Bit#(3) x_15 = ((x_7).mesi_status);
        Struct17 x_16 = (Struct17 {dir_st : (((x_7).mesi_dir_st) ==
        ((Bit#(3))'(3'h0)) ? ((Bit#(3))'(3'h1)) : ((x_7).mesi_dir_st)),
        dir_excl : ((((x_7).mesi_dir_sharers)[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(1))'(1'h0)) : (((Bit#(1))'(1'h1)) +
        ((((((x_7).mesi_dir_sharers)[1:1])[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(1))'(1'h0)) : (((Bit#(1))'(1'h1)) + (unpack(0))))))),
        dir_sharers : (x_7).mesi_dir_sharers});
        when ((x_2) == ({((Bit#(2))'(2'h2)),((Bit#(1))'(1'h0))}),
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
        Bit#(3) x_19 = ({((Bit#(2))'(2'h2)),(((x_10).m_qidx)[0:0])});
        Struct18 x_20 = (Struct18 {addr : (x_3).addr, info_write :
        (Bool)'(False), info_hit : (x_6).info_hit, info_way : (x_6).info_way,
        edir_hit : (x_6).edir_hit, edir_way : (x_6).edir_way, edir_slot :
        (x_6).edir_slot, info : (x_6).info, value_write : (Bool)'(False),
        value : unpack(0), may_victim : (x_6).may_victim, reps :
        (x_6).reps});
        Struct18 x_21 = (Struct18 {addr : (x_20).addr, info_write :
        (Bool)'(True), info_hit : (x_20).info_hit, info_way :
        (x_20).info_way, edir_hit : (x_20).edir_hit, edir_way :
        (x_20).edir_way, edir_slot : (x_20).edir_slot, info : Struct11
        {mesi_owned : ((x_20).info).mesi_owned, mesi_status :
        ((x_20).info).mesi_status, mesi_dir_st : (Struct17 {dir_st :
        (Bit#(3))'(3'h3), dir_excl : (x_19)[0:0], dir_sharers :
        unpack(0)}).dir_st, mesi_dir_sharers : (((Struct17 {dir_st :
        (Bit#(3))'(3'h3), dir_excl : (x_19)[0:0], dir_sharers :
        unpack(0)}).dir_st) == ((Bit#(3))'(3'h2)) ? ((Struct17 {dir_st :
        (Bit#(3))'(3'h3), dir_excl : (x_19)[0:0], dir_sharers :
        unpack(0)}).dir_sharers) : (((Bit#(2))'(2'h1)) << ((Struct17 {dir_st
        : (Bit#(3))'(3'h3), dir_excl : (x_19)[0:0], dir_sharers :
        unpack(0)}).dir_excl)))}, value_write : (x_20).value_write, value :
        (x_20).value, may_victim : (x_20).may_victim, reps :
        (x_20).reps});
        Struct18 x_22 = (Struct18 {addr : (x_21).addr, info_write :
        (Bool)'(True), info_hit : (x_21).info_hit, info_way :
        (x_21).info_way, edir_hit : (x_21).edir_hit, edir_way :
        (x_21).edir_way, edir_slot : (x_21).edir_slot, info : Struct11
        {mesi_owned : ((x_21).info).mesi_owned, mesi_status :
        (Bit#(3))'(3'h1), mesi_dir_st : ((x_21).info).mesi_dir_st,
        mesi_dir_sharers : ((x_21).info).mesi_dir_sharers}, value_write :
        (x_21).value_write, value : (x_21).value, may_victim :
        (x_21).may_victim, reps : (x_21).reps});
        Struct18 x_23 = (Struct18 {addr : (x_22).addr, info_write :
        (Bool)'(True), info_hit : (x_22).info_hit, info_way :
        (x_22).info_way, edir_hit : (x_22).edir_hit, edir_way :
        (x_22).edir_way, edir_slot : (x_22).edir_slot, info : Struct11
        {mesi_owned : (Bool)'(False), mesi_status :
        ((x_22).info).mesi_status, mesi_dir_st : ((x_22).info).mesi_dir_st,
        mesi_dir_sharers : ((x_22).info).mesi_dir_sharers}, value_write :
        (x_22).value_write, value : (x_22).value, may_victim :
        (x_22).may_victim, reps : (x_22).reps});
        Struct18 x_24 = (Struct18 {addr : (x_23).addr, info_write :
        (x_23).info_write, info_hit : (x_23).info_hit, info_way :
        (x_23).info_way, edir_hit : (x_23).edir_hit, edir_way :
        (x_23).edir_way, edir_slot : (x_23).edir_slot, info : (x_23).info,
        value_write : (Bool)'(True), value : (x_17).value, may_victim :
        (x_23).may_victim, reps :
        (x_23).reps});
        let x_27 = ?;
        if ((x_8).valid) begin
            let x_25 <- victims__00__setVictim(Struct19 {victim_idx :
            (x_8).data, victim_info : (x_24).info, victim_value :
            ((x_24).value_write ? ((x_24).value) : (x_9))});
            x_27 = x_9;
        end else begin
            let x_26 <- cache__00__valueRsLineRq(x_24);
            x_27 = x_26;
        end
        let x_28 <- releaseMSHR_00(x_4);
        Struct20 x_29 = (Struct20 {enq_type : (((x_19)[2:1]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : ((((x_19)[2:1]) ==
        ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : (x_19)[0:0], enq_msg : Struct1 {id : (Bit#(6))'(6'h4),
        type_ : (Bool)'(True), addr : (x_17).addr, value :
        (x_17).value}});
        let x_30 <- makeEnq_parentChildren00(x_29);
    endrule

    rule rule_exec_00_041;
        $display ("Rule fired: rule_exec_00_041 at %t", $time);
        let x_0 <- deq_fifoL2E_00();
        Struct6 x_1 = ((x_0).lr_ir_pp);
        Bit#(3) x_2 = ((x_1).ir_msg_from);
        Struct1 x_3 = ((x_1).ir_msg);
        Bit#(4) x_4 = ((x_1).ir_mshr_id);
        Bool x_5 = ((x_1).ir_is_rs_rel);
        when (x_5, noAction);
        Struct9 x_6 = ((x_0).lr_ir);
        Struct11 x_7 = ((x_6).info);
        Struct5 x_8 = ((x_1).ir_by_victim);
        Vector#(4, Bit#(64)) x_9 = ((x_0).lr_value);
        let x_10 <- getMSHR_00(x_4);
        let x_11 <- getMSHRRq_00(x_4);
        let x_12 <- getMSHRFirstRs_00(x_4);
        Vector#(4, Bit#(64)) x_13 = (unpack(0));
        Bool x_14 = ((x_7).mesi_owned);
        Bit#(3) x_15 = ((x_7).mesi_status);
        Struct17 x_16 = (Struct17 {dir_st : (((x_7).mesi_dir_st) ==
        ((Bit#(3))'(3'h0)) ? ((Bit#(3))'(3'h1)) : ((x_7).mesi_dir_st)),
        dir_excl : ((((x_7).mesi_dir_sharers)[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(1))'(1'h0)) : (((Bit#(1))'(1'h1)) +
        ((((((x_7).mesi_dir_sharers)[1:1])[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(1))'(1'h0)) : (((Bit#(1))'(1'h1)) + (unpack(0))))))),
        dir_sharers : (x_7).mesi_dir_sharers});
        when ((x_10).m_rsb, noAction);
        when (((x_11).type_) == ((Bool)'(False)), noAction);
        when (((x_11).id) == ((Bit#(6))'(6'h2)), noAction);
        when ((Bool)'(True), noAction);
        Struct24 x_17 = (Struct24 {cidx :
        {((Bit#(2))'(2'h1)),(((((x_10).m_dl_rss_from)[0:0]) ==
        ((Bit#(1))'(1'h1)) ? ((Bit#(1))'(1'h0)) : (((Bit#(1))'(1'h1)) +
        ((((((x_10).m_dl_rss_from)[1:1])[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(1))'(1'h0)) : (((Bit#(1))'(1'h1)) + (unpack(0))))))))}, msg :
        x_12});
        Struct1 x_18 = (x_11);
        Bit#(3) x_19 = ((x_10).m_qidx);
        Struct18 x_20 = (Struct18 {addr : (x_3).addr, info_write :
        (Bool)'(False), info_hit : (x_6).info_hit, info_way : (x_6).info_way,
        edir_hit : (x_6).edir_hit, edir_way : (x_6).edir_way, edir_slot :
        (x_6).edir_slot, info : (x_6).info, value_write : (Bool)'(False),
        value : unpack(0), may_victim : (x_6).may_victim, reps :
        (x_6).reps});
        Struct18 x_21 = (Struct18 {addr : (x_20).addr, info_write :
        (Bool)'(True), info_hit : (x_20).info_hit, info_way :
        (x_20).info_way, edir_hit : (x_20).edir_hit, edir_way :
        (x_20).edir_way, edir_slot : (x_20).edir_slot, info : Struct11
        {mesi_owned : ((x_20).info).mesi_owned, mesi_status :
        ((x_20).info).mesi_status, mesi_dir_st : (Struct17 {dir_st :
        (Bit#(3))'(3'h2), dir_excl : unpack(0), dir_sharers : ((unpack(0)) |
        (((Bit#(2))'(2'h1)) << ((x_19)[0:0]))) | (((Bit#(2))'(2'h1)) <<
        (((x_17).cidx)[0:0]))}).dir_st, mesi_dir_sharers : (((Struct17
        {dir_st : (Bit#(3))'(3'h2), dir_excl : unpack(0), dir_sharers :
        ((unpack(0)) | (((Bit#(2))'(2'h1)) << ((x_19)[0:0]))) |
        (((Bit#(2))'(2'h1)) << (((x_17).cidx)[0:0]))}).dir_st) ==
        ((Bit#(3))'(3'h2)) ? ((Struct17 {dir_st : (Bit#(3))'(3'h2), dir_excl
        : unpack(0), dir_sharers : ((unpack(0)) | (((Bit#(2))'(2'h1)) <<
        ((x_19)[0:0]))) | (((Bit#(2))'(2'h1)) <<
        (((x_17).cidx)[0:0]))}).dir_sharers) : (((Bit#(2))'(2'h1)) <<
        ((Struct17 {dir_st : (Bit#(3))'(3'h2), dir_excl : unpack(0),
        dir_sharers : ((unpack(0)) | (((Bit#(2))'(2'h1)) << ((x_19)[0:0]))) |
        (((Bit#(2))'(2'h1)) << (((x_17).cidx)[0:0]))}).dir_excl)))},
        value_write : (x_20).value_write, value : (x_20).value, may_victim :
        (x_20).may_victim, reps : (x_20).reps});
        Struct18 x_22 = (Struct18 {addr : (x_21).addr, info_write :
        (Bool)'(True), info_hit : (x_21).info_hit, info_way :
        (x_21).info_way, edir_hit : (x_21).edir_hit, edir_way :
        (x_21).edir_way, edir_slot : (x_21).edir_slot, info : Struct11
        {mesi_owned : ((x_21).info).mesi_owned, mesi_status :
        (Bit#(3))'(3'h2), mesi_dir_st : ((x_21).info).mesi_dir_st,
        mesi_dir_sharers : ((x_21).info).mesi_dir_sharers}, value_write :
        (x_21).value_write, value : (x_21).value, may_victim :
        (x_21).may_victim, reps : (x_21).reps});
        Struct18 x_23 = (Struct18 {addr : (x_22).addr, info_write :
        (x_22).info_write, info_hit : (x_22).info_hit, info_way :
        (x_22).info_way, edir_hit : (x_22).edir_hit, edir_way :
        (x_22).edir_way, edir_slot : (x_22).edir_slot, info : (x_22).info,
        value_write : (Bool)'(True), value : ((x_17).msg).value, may_victim :
        (x_22).may_victim, reps : (x_22).reps});
        Struct18 x_24 = (Struct18 {addr : (x_23).addr, info_write :
        (Bool)'(True), info_hit : (x_23).info_hit, info_way :
        (x_23).info_way, edir_hit : (x_23).edir_hit, edir_way :
        (x_23).edir_way, edir_slot : (x_23).edir_slot, info : Struct11
        {mesi_owned : (Bool)'(True), mesi_status : ((x_23).info).mesi_status,
        mesi_dir_st : ((x_23).info).mesi_dir_st, mesi_dir_sharers :
        ((x_23).info).mesi_dir_sharers}, value_write : (x_23).value_write,
        value : (x_23).value, may_victim : (x_23).may_victim, reps :
        (x_23).reps});
        let x_27 = ?;
        if ((x_8).valid) begin
            let x_25 <- victims__00__setVictim(Struct19 {victim_idx :
            (x_8).data, victim_info : (x_24).info, victim_value :
            ((x_24).value_write ? ((x_24).value) : (x_9))});
            x_27 = x_9;
        end else begin
            let x_26 <- cache__00__valueRsLineRq(x_24);
            x_27 = x_26;
        end
        let x_28 <- releaseMSHR_00(x_4);
        Struct20 x_29 = (Struct20 {enq_type : (((x_19)[2:1]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : ((((x_19)[2:1]) ==
        ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : (x_19)[0:0], enq_msg : Struct1 {id : (Bit#(6))'(6'h3),
        type_ : (Bool)'(True), addr : (x_18).addr, value :
        ((x_17).msg).value}});
        let x_30 <- makeEnq_parentChildren00(x_29);
    endrule

    rule rule_exec_00_05;
        $display ("Rule fired: rule_exec_00_05 at %t", $time);
        let x_0 <- deq_fifoL2E_00();
        Struct6 x_1 = ((x_0).lr_ir_pp);
        Bit#(3) x_2 = ((x_1).ir_msg_from);
        Struct1 x_3 = ((x_1).ir_msg);
        Bit#(4) x_4 = ((x_1).ir_mshr_id);
        Bool x_5 = ((x_1).ir_is_rs_rel);
        when (! (x_5), noAction);
        Struct9 x_6 = ((x_0).lr_ir);
        Struct11 x_7 = ((x_6).info);
        Struct5 x_8 = ((x_1).ir_by_victim);
        Vector#(4, Bit#(64)) x_9 = ((x_0).lr_value);
        let x_10 <- getMSHR_00(x_4);
        let x_11 <- getMSHRRq_00(x_4);
        let x_12 <- getMSHRFirstRs_00(x_4);
        Vector#(4, Bit#(64)) x_13 = (unpack(0));
        Bool x_14 = ((x_7).mesi_owned);
        Bit#(3) x_15 = ((x_7).mesi_status);
        Struct17 x_16 = (Struct17 {dir_st : (((x_7).mesi_dir_st) ==
        ((Bit#(3))'(3'h0)) ? ((Bit#(3))'(3'h1)) : ((x_7).mesi_dir_st)),
        dir_excl : ((((x_7).mesi_dir_sharers)[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(1))'(1'h0)) : (((Bit#(1))'(1'h1)) +
        ((((((x_7).mesi_dir_sharers)[1:1])[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(1))'(1'h0)) : (((Bit#(1))'(1'h1)) + (unpack(0))))))),
        dir_sharers : (x_7).mesi_dir_sharers});
        when ((x_2) == ((Bit#(3))'(3'h4)), noAction);
        when (((x_3).id) == ((Bit#(6))'(6'h5)), noAction);
        when (! ((x_3).type_), noAction);
        when ((! ((x_15) < ((Bit#(3))'(3'h2)))) && (! (((Bit#(3))'(3'h2)) <
        ((x_16).dir_st))), noAction);
        Struct1 x_17 = (x_3);
        Struct18 x_18 = (Struct18 {addr : (x_3).addr, info_write :
        (Bool)'(False), info_hit : (x_6).info_hit, info_way : (x_6).info_way,
        edir_hit : (x_6).edir_hit, edir_way : (x_6).edir_way, edir_slot :
        (x_6).edir_slot, info : (x_6).info, value_write : (Bool)'(False),
        value : unpack(0), may_victim : (x_6).may_victim, reps :
        (x_6).reps});
        Struct18 x_19 = (Struct18 {addr : (x_18).addr, info_write :
        (Bool)'(True), info_hit : (x_18).info_hit, info_way :
        (x_18).info_way, edir_hit : (x_18).edir_hit, edir_way :
        (x_18).edir_way, edir_slot : (x_18).edir_slot, info : Struct11
        {mesi_owned : ((x_18).info).mesi_owned, mesi_status :
        (Bit#(3))'(3'h2), mesi_dir_st : ((x_18).info).mesi_dir_st,
        mesi_dir_sharers : ((x_18).info).mesi_dir_sharers}, value_write :
        (x_18).value_write, value : (x_18).value, may_victim :
        (x_18).may_victim, reps : (x_18).reps});
        Struct18 x_20 = (Struct18 {addr : (x_19).addr, info_write :
        (Bool)'(True), info_hit : (x_19).info_hit, info_way :
        (x_19).info_way, edir_hit : (x_19).edir_hit, edir_way :
        (x_19).edir_way, edir_slot : (x_19).edir_slot, info : Struct11
        {mesi_owned : (Bool)'(False), mesi_status :
        ((x_19).info).mesi_status, mesi_dir_st : ((x_19).info).mesi_dir_st,
        mesi_dir_sharers : ((x_19).info).mesi_dir_sharers}, value_write :
        (x_19).value_write, value : (x_19).value, may_victim :
        (x_19).may_victim, reps :
        (x_19).reps});
        let x_23 = ?;
        if ((x_8).valid) begin
            let x_21 <- victims__00__setVictim(Struct19 {victim_idx :
            (x_8).data, victim_info : (x_20).info, victim_value :
            ((x_20).value_write ? ((x_20).value) : (x_9))});
            x_23 = x_9;
        end else begin
            let x_22 <- cache__00__valueRsLineRq(x_20);
            x_23 = x_22;
        end
        Struct20 x_24 = (Struct20 {enq_type : ((((Bit#(3))'(3'h2))[2:1]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : (((((Bit#(3))'(3'h2))[2:1])
        == ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : ((Bit#(3))'(3'h2))[0:0], enq_msg : Struct1 {id :
        (Bit#(6))'(6'h6), type_ : (Bool)'(True), addr : (x_17).addr, value :
        x_23}});
        let x_25 <- makeEnq_parentChildren00(x_24);
        let x_26 <- releaseMSHR_00(x_4);
    endrule

    rule rule_exec_00_06;
        $display ("Rule fired: rule_exec_00_06 at %t", $time);
        let x_0 <- deq_fifoL2E_00();
        Struct6 x_1 = ((x_0).lr_ir_pp);
        Bit#(3) x_2 = ((x_1).ir_msg_from);
        Struct1 x_3 = ((x_1).ir_msg);
        Bit#(4) x_4 = ((x_1).ir_mshr_id);
        Bool x_5 = ((x_1).ir_is_rs_rel);
        when (! (x_5), noAction);
        Struct9 x_6 = ((x_0).lr_ir);
        Struct11 x_7 = ((x_6).info);
        Struct5 x_8 = ((x_1).ir_by_victim);
        Vector#(4, Bit#(64)) x_9 = ((x_0).lr_value);
        let x_10 <- getMSHR_00(x_4);
        let x_11 <- getMSHRRq_00(x_4);
        let x_12 <- getMSHRFirstRs_00(x_4);
        Vector#(4, Bit#(64)) x_13 = (unpack(0));
        Bool x_14 = ((x_7).mesi_owned);
        Bit#(3) x_15 = ((x_7).mesi_status);
        Struct17 x_16 = (Struct17 {dir_st : (((x_7).mesi_dir_st) ==
        ((Bit#(3))'(3'h0)) ? ((Bit#(3))'(3'h1)) : ((x_7).mesi_dir_st)),
        dir_excl : ((((x_7).mesi_dir_sharers)[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(1))'(1'h0)) : (((Bit#(1))'(1'h1)) +
        ((((((x_7).mesi_dir_sharers)[1:1])[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(1))'(1'h0)) : (((Bit#(1))'(1'h1)) + (unpack(0))))))),
        dir_sharers : (x_7).mesi_dir_sharers});
        when ((x_2) == ((Bit#(3))'(3'h4)), noAction);
        when (((x_3).id) == ((Bit#(6))'(6'h5)), noAction);
        when (! ((x_3).type_), noAction);
        when (((Bool)'(True)) && ((! (((Bit#(3))'(3'h1)) < (x_15))) && ((!
        (((x_16).dir_st) < ((Bit#(3))'(3'h3)))) && (! (((Bit#(3))'(3'h4)) <
        ((x_16).dir_st))))), noAction);
        Struct1 x_17 = (x_3);
        Struct18 x_18 = (Struct18 {addr : (x_3).addr, info_write :
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
        let x_21 <- registerDL_00(Struct22 {r_id : x_4, r_dl_rss_from :
        (unpack(0)) | (((Bit#(2))'(2'h1)) <<
        (({((Bit#(2))'(2'h1)),((x_16).dir_excl)})[0:0])), r_dl_rsb :
        (Bool)'(True), r_dl_rsbTo : (Bit#(3))'(3'h2)});
        Struct20 x_22 = (Struct20 {enq_type :
        ((({((Bit#(2))'(2'h2)),((x_16).dir_excl)})[2:1]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) :
        (((({((Bit#(2))'(2'h2)),((x_16).dir_excl)})[2:1]) ==
        ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : ({((Bit#(2))'(2'h2)),((x_16).dir_excl)})[0:0], enq_msg :
        Struct1 {id : (Bit#(6))'(6'h5), type_ : (Bool)'(False), addr :
        (x_17).addr, value : unpack(0)}});
        let x_23 <- makeEnq_parentChildren00(x_22);
    endrule

    rule rule_exec_00_071;
        $display ("Rule fired: rule_exec_00_071 at %t", $time);
        let x_0 <- deq_fifoL2E_00();
        Struct6 x_1 = ((x_0).lr_ir_pp);
        Bit#(3) x_2 = ((x_1).ir_msg_from);
        Struct1 x_3 = ((x_1).ir_msg);
        Bit#(4) x_4 = ((x_1).ir_mshr_id);
        Bool x_5 = ((x_1).ir_is_rs_rel);
        when (x_5, noAction);
        Struct9 x_6 = ((x_0).lr_ir);
        Struct11 x_7 = ((x_6).info);
        Struct5 x_8 = ((x_1).ir_by_victim);
        Vector#(4, Bit#(64)) x_9 = ((x_0).lr_value);
        let x_10 <- getMSHR_00(x_4);
        let x_11 <- getMSHRRq_00(x_4);
        let x_12 <- getMSHRFirstRs_00(x_4);
        Vector#(4, Bit#(64)) x_13 = (unpack(0));
        Bool x_14 = ((x_7).mesi_owned);
        Bit#(3) x_15 = ((x_7).mesi_status);
        Struct17 x_16 = (Struct17 {dir_st : (((x_7).mesi_dir_st) ==
        ((Bit#(3))'(3'h0)) ? ((Bit#(3))'(3'h1)) : ((x_7).mesi_dir_st)),
        dir_excl : ((((x_7).mesi_dir_sharers)[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(1))'(1'h0)) : (((Bit#(1))'(1'h1)) +
        ((((((x_7).mesi_dir_sharers)[1:1])[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(1))'(1'h0)) : (((Bit#(1))'(1'h1)) + (unpack(0))))))),
        dir_sharers : (x_7).mesi_dir_sharers});
        when ((x_10).m_rsb, noAction);
        when (((x_11).type_) == ((Bool)'(False)), noAction);
        when (((x_11).id) == ((Bit#(6))'(6'h5)), noAction);
        when ((Bool)'(True), noAction);
        Struct24 x_17 = (Struct24 {cidx :
        {((Bit#(2))'(2'h1)),(((((x_10).m_dl_rss_from)[0:0]) ==
        ((Bit#(1))'(1'h1)) ? ((Bit#(1))'(1'h0)) : (((Bit#(1))'(1'h1)) +
        ((((((x_10).m_dl_rss_from)[1:1])[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(1))'(1'h0)) : (((Bit#(1))'(1'h1)) + (unpack(0))))))))}, msg :
        x_12});
        Struct1 x_18 = (x_11);
        Bit#(3) x_19 = ((x_10).m_qidx);
        Struct18 x_20 = (Struct18 {addr : (x_3).addr, info_write :
        (Bool)'(False), info_hit : (x_6).info_hit, info_way : (x_6).info_way,
        edir_hit : (x_6).edir_hit, edir_way : (x_6).edir_way, edir_slot :
        (x_6).edir_slot, info : (x_6).info, value_write : (Bool)'(False),
        value : unpack(0), may_victim : (x_6).may_victim, reps :
        (x_6).reps});
        Struct18 x_21 = (Struct18 {addr : (x_20).addr, info_write :
        (Bool)'(True), info_hit : (x_20).info_hit, info_way :
        (x_20).info_way, edir_hit : (x_20).edir_hit, edir_way :
        (x_20).edir_way, edir_slot : (x_20).edir_slot, info : Struct11
        {mesi_owned : ((x_20).info).mesi_owned, mesi_status :
        ((x_20).info).mesi_status, mesi_dir_st : (Struct17 {dir_st :
        (Bit#(3))'(3'h2), dir_excl : unpack(0), dir_sharers : (unpack(0)) |
        (((Bit#(2))'(2'h1)) << (((x_17).cidx)[0:0]))}).dir_st,
        mesi_dir_sharers : (((Struct17 {dir_st : (Bit#(3))'(3'h2), dir_excl :
        unpack(0), dir_sharers : (unpack(0)) | (((Bit#(2))'(2'h1)) <<
        (((x_17).cidx)[0:0]))}).dir_st) == ((Bit#(3))'(3'h2)) ? ((Struct17
        {dir_st : (Bit#(3))'(3'h2), dir_excl : unpack(0), dir_sharers :
        (unpack(0)) | (((Bit#(2))'(2'h1)) <<
        (((x_17).cidx)[0:0]))}).dir_sharers) : (((Bit#(2))'(2'h1)) <<
        ((Struct17 {dir_st : (Bit#(3))'(3'h2), dir_excl : unpack(0),
        dir_sharers : (unpack(0)) | (((Bit#(2))'(2'h1)) <<
        (((x_17).cidx)[0:0]))}).dir_excl)))}, value_write :
        (x_20).value_write, value : (x_20).value, may_victim :
        (x_20).may_victim, reps : (x_20).reps});
        Struct18 x_22 = (Struct18 {addr : (x_21).addr, info_write :
        (Bool)'(True), info_hit : (x_21).info_hit, info_way :
        (x_21).info_way, edir_hit : (x_21).edir_hit, edir_way :
        (x_21).edir_way, edir_slot : (x_21).edir_slot, info : Struct11
        {mesi_owned : ((x_21).info).mesi_owned, mesi_status :
        (Bit#(3))'(3'h2), mesi_dir_st : ((x_21).info).mesi_dir_st,
        mesi_dir_sharers : ((x_21).info).mesi_dir_sharers}, value_write :
        (x_21).value_write, value : (x_21).value, may_victim :
        (x_21).may_victim, reps : (x_21).reps});
        Struct18 x_23 = (Struct18 {addr : (x_22).addr, info_write :
        (Bool)'(True), info_hit : (x_22).info_hit, info_way :
        (x_22).info_way, edir_hit : (x_22).edir_hit, edir_way :
        (x_22).edir_way, edir_slot : (x_22).edir_slot, info : Struct11
        {mesi_owned : (Bool)'(False), mesi_status :
        ((x_22).info).mesi_status, mesi_dir_st : ((x_22).info).mesi_dir_st,
        mesi_dir_sharers : ((x_22).info).mesi_dir_sharers}, value_write :
        (x_22).value_write, value : (x_22).value, may_victim :
        (x_22).may_victim, reps : (x_22).reps});
        Struct18 x_24 = (Struct18 {addr : (x_23).addr, info_write :
        (x_23).info_write, info_hit : (x_23).info_hit, info_way :
        (x_23).info_way, edir_hit : (x_23).edir_hit, edir_way :
        (x_23).edir_way, edir_slot : (x_23).edir_slot, info : (x_23).info,
        value_write : (Bool)'(True), value : ((x_17).msg).value, may_victim :
        (x_23).may_victim, reps :
        (x_23).reps});
        let x_27 = ?;
        if ((x_8).valid) begin
            let x_25 <- victims__00__setVictim(Struct19 {victim_idx :
            (x_8).data, victim_info : (x_24).info, victim_value :
            ((x_24).value_write ? ((x_24).value) : (x_9))});
            x_27 = x_9;
        end else begin
            let x_26 <- cache__00__valueRsLineRq(x_24);
            x_27 = x_26;
        end
        let x_28 <- releaseMSHR_00(x_4);
        Struct20 x_29 = (Struct20 {enq_type : (((x_19)[2:1]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : ((((x_19)[2:1]) ==
        ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : (x_19)[0:0], enq_msg : Struct1 {id : (Bit#(6))'(6'h6),
        type_ : (Bool)'(True), addr : (x_18).addr, value :
        ((x_17).msg).value}});
        let x_30 <- makeEnq_parentChildren00(x_29);
    endrule

    rule rule_exec_00_12;
        $display ("Rule fired: rule_exec_00_12 at %t", $time);
        let x_0 <- deq_fifoL2E_00();
        Struct6 x_1 = ((x_0).lr_ir_pp);
        Bit#(3) x_2 = ((x_1).ir_msg_from);
        Struct1 x_3 = ((x_1).ir_msg);
        Bit#(4) x_4 = ((x_1).ir_mshr_id);
        Bool x_5 = ((x_1).ir_is_rs_rel);
        when (! (x_5), noAction);
        Struct9 x_6 = ((x_0).lr_ir);
        Struct11 x_7 = ((x_6).info);
        Struct5 x_8 = ((x_1).ir_by_victim);
        Vector#(4, Bit#(64)) x_9 = ((x_0).lr_value);
        let x_10 <- getMSHR_00(x_4);
        let x_11 <- getMSHRRq_00(x_4);
        let x_12 <- getMSHRFirstRs_00(x_4);
        Vector#(4, Bit#(64)) x_13 = (unpack(0));
        Bool x_14 = ((x_7).mesi_owned);
        Bit#(3) x_15 = ((x_7).mesi_status);
        Struct17 x_16 = (Struct17 {dir_st : (((x_7).mesi_dir_st) ==
        ((Bit#(3))'(3'h0)) ? ((Bit#(3))'(3'h1)) : ((x_7).mesi_dir_st)),
        dir_excl : ((((x_7).mesi_dir_sharers)[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(1))'(1'h0)) : (((Bit#(1))'(1'h1)) +
        ((((((x_7).mesi_dir_sharers)[1:1])[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(1))'(1'h0)) : (((Bit#(1))'(1'h1)) + (unpack(0))))))),
        dir_sharers : (x_7).mesi_dir_sharers});
        when ((x_2) == ({((Bit#(2))'(2'h2)),((Bit#(1))'(1'h0))}),
        noAction);
        when (((x_3).id) == ((Bit#(6))'(6'hb)), noAction);
        when ((x_10).m_rsb, noAction);
        when (((x_11).type_) == ((Bool)'(False)), noAction);
        when (((x_11).id) == ((Bit#(6))'(6'ha)), noAction);
        when ((x_10).m_rsb, noAction);
        when ((x_3).type_, noAction);
        when ((((x_16).dir_st) == ((Bit#(3))'(3'h1))) || ((((x_16).dir_st) ==
        ((Bit#(3))'(3'h2))) && (((x_16).dir_sharers) == (((Bit#(2))'(2'h1))
        << (({((Bit#(2))'(2'h2)),(((x_10).m_qidx)[0:0])})[0:0])))),
        noAction);
        Struct1 x_17 = (x_3);
        Struct1 x_18 = (x_11);
        Bit#(3) x_19 = ({((Bit#(2))'(2'h2)),(((x_10).m_qidx)[0:0])});
        Struct18 x_20 = (Struct18 {addr : (x_3).addr, info_write :
        (Bool)'(False), info_hit : (x_6).info_hit, info_way : (x_6).info_way,
        edir_hit : (x_6).edir_hit, edir_way : (x_6).edir_way, edir_slot :
        (x_6).edir_slot, info : (x_6).info, value_write : (Bool)'(False),
        value : unpack(0), may_victim : (x_6).may_victim, reps :
        (x_6).reps});
        Struct18 x_21 = (Struct18 {addr : (x_20).addr, info_write :
        (Bool)'(True), info_hit : (x_20).info_hit, info_way :
        (x_20).info_way, edir_hit : (x_20).edir_hit, edir_way :
        (x_20).edir_way, edir_slot : (x_20).edir_slot, info : Struct11
        {mesi_owned : ((x_20).info).mesi_owned, mesi_status :
        ((x_20).info).mesi_status, mesi_dir_st : (Struct17 {dir_st :
        (Bit#(3))'(3'h4), dir_excl : (x_19)[0:0], dir_sharers :
        unpack(0)}).dir_st, mesi_dir_sharers : (((Struct17 {dir_st :
        (Bit#(3))'(3'h4), dir_excl : (x_19)[0:0], dir_sharers :
        unpack(0)}).dir_st) == ((Bit#(3))'(3'h2)) ? ((Struct17 {dir_st :
        (Bit#(3))'(3'h4), dir_excl : (x_19)[0:0], dir_sharers :
        unpack(0)}).dir_sharers) : (((Bit#(2))'(2'h1)) << ((Struct17 {dir_st
        : (Bit#(3))'(3'h4), dir_excl : (x_19)[0:0], dir_sharers :
        unpack(0)}).dir_excl)))}, value_write : (x_20).value_write, value :
        (x_20).value, may_victim : (x_20).may_victim, reps :
        (x_20).reps});
        Struct18 x_22 = (Struct18 {addr : (x_21).addr, info_write :
        (Bool)'(True), info_hit : (x_21).info_hit, info_way :
        (x_21).info_way, edir_hit : (x_21).edir_hit, edir_way :
        (x_21).edir_way, edir_slot : (x_21).edir_slot, info : Struct11
        {mesi_owned : ((x_21).info).mesi_owned, mesi_status :
        (Bit#(3))'(3'h1), mesi_dir_st : ((x_21).info).mesi_dir_st,
        mesi_dir_sharers : ((x_21).info).mesi_dir_sharers}, value_write :
        (x_21).value_write, value : (x_21).value, may_victim :
        (x_21).may_victim, reps : (x_21).reps});
        Struct18 x_23 = (Struct18 {addr : (x_22).addr, info_write :
        (Bool)'(True), info_hit : (x_22).info_hit, info_way :
        (x_22).info_way, edir_hit : (x_22).edir_hit, edir_way :
        (x_22).edir_way, edir_slot : (x_22).edir_slot, info : Struct11
        {mesi_owned : (Bool)'(False), mesi_status :
        ((x_22).info).mesi_status, mesi_dir_st : ((x_22).info).mesi_dir_st,
        mesi_dir_sharers : ((x_22).info).mesi_dir_sharers}, value_write :
        (x_22).value_write, value : (x_22).value, may_victim :
        (x_22).may_victim, reps :
        (x_22).reps});
        let x_26 = ?;
        if ((x_8).valid) begin
            let x_24 <- victims__00__setVictim(Struct19 {victim_idx :
            (x_8).data, victim_info : (x_23).info, victim_value :
            ((x_23).value_write ? ((x_23).value) : (x_9))});
            x_26 = x_9;
        end else begin
            let x_25 <- cache__00__valueRsLineRq(x_23);
            x_26 = x_25;
        end
        let x_27 <- releaseMSHR_00(x_4);
        Struct20 x_28 = (Struct20 {enq_type : (((x_19)[2:1]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : ((((x_19)[2:1]) ==
        ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : (x_19)[0:0], enq_msg : Struct1 {id : (Bit#(6))'(6'hb),
        type_ : (Bool)'(True), addr : (x_17).addr, value : unpack(0)}});
        let x_29 <- makeEnq_parentChildren00(x_28);
    endrule

    rule rule_exec_00_13;
        $display ("Rule fired: rule_exec_00_13 at %t", $time);
        let x_0 <- deq_fifoL2E_00();
        Struct6 x_1 = ((x_0).lr_ir_pp);
        Bit#(3) x_2 = ((x_1).ir_msg_from);
        Struct1 x_3 = ((x_1).ir_msg);
        Bit#(4) x_4 = ((x_1).ir_mshr_id);
        Bool x_5 = ((x_1).ir_is_rs_rel);
        when (! (x_5), noAction);
        Struct9 x_6 = ((x_0).lr_ir);
        Struct11 x_7 = ((x_6).info);
        Struct5 x_8 = ((x_1).ir_by_victim);
        Vector#(4, Bit#(64)) x_9 = ((x_0).lr_value);
        let x_10 <- getMSHR_00(x_4);
        let x_11 <- getMSHRRq_00(x_4);
        let x_12 <- getMSHRFirstRs_00(x_4);
        Vector#(4, Bit#(64)) x_13 = (unpack(0));
        Bool x_14 = ((x_7).mesi_owned);
        Bit#(3) x_15 = ((x_7).mesi_status);
        Struct17 x_16 = (Struct17 {dir_st : (((x_7).mesi_dir_st) ==
        ((Bit#(3))'(3'h0)) ? ((Bit#(3))'(3'h1)) : ((x_7).mesi_dir_st)),
        dir_excl : ((((x_7).mesi_dir_sharers)[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(1))'(1'h0)) : (((Bit#(1))'(1'h1)) +
        ((((((x_7).mesi_dir_sharers)[1:1])[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(1))'(1'h0)) : (((Bit#(1))'(1'h1)) + (unpack(0))))))),
        dir_sharers : (x_7).mesi_dir_sharers});
        when ((x_2) == ({((Bit#(2))'(2'h2)),((Bit#(1))'(1'h0))}),
        noAction);
        when (((x_3).id) == ((Bit#(6))'(6'hb)), noAction);
        when ((x_10).m_rsb, noAction);
        when (((x_11).type_) == ((Bool)'(False)), noAction);
        when (((x_11).id) == ((Bit#(6))'(6'ha)), noAction);
        when ((x_10).m_rsb, noAction);
        when ((x_3).type_, noAction);
        when (((Bool)'(True)) && (((Bool)'(True)) && (((Bool)'(True)) && ((!
        ((((x_16).dir_sharers) & (~(((Bit#(2))'(2'h1)) <<
        (({((Bit#(2))'(2'h2)),(((x_10).m_qidx)[0:0])})[0:0])))) ==
        ((Bit#(2))'(2'h0)))) && (((x_16).dir_st) == ((Bit#(3))'(3'h2)))))),
        noAction);
        Struct1 x_17 = (x_11);
        Bit#(3) x_18 = ({((Bit#(2))'(2'h2)),(((x_10).m_qidx)[0:0])});
        Struct18 x_19 = (Struct18 {addr : (x_3).addr, info_write :
        (Bool)'(False), info_hit : (x_6).info_hit, info_way : (x_6).info_way,
        edir_hit : (x_6).edir_hit, edir_way : (x_6).edir_way, edir_slot :
        (x_6).edir_slot, info : (x_6).info, value_write : (Bool)'(False),
        value : unpack(0), may_victim : (x_6).may_victim, reps :
        (x_6).reps});
        Struct18 x_20 = (Struct18 {addr : (x_19).addr, info_write :
        (Bool)'(True), info_hit : (x_19).info_hit, info_way :
        (x_19).info_way, edir_hit : (x_19).edir_hit, edir_way :
        (x_19).edir_way, edir_slot : (x_19).edir_slot, info : Struct11
        {mesi_owned : (Bool)'(True), mesi_status : ((x_19).info).mesi_status,
        mesi_dir_st : ((x_19).info).mesi_dir_st, mesi_dir_sharers :
        ((x_19).info).mesi_dir_sharers}, value_write : (x_19).value_write,
        value : (x_19).value, may_victim : (x_19).may_victim, reps :
        (x_19).reps});
        let x_23 = ?;
        if ((x_8).valid) begin
            let x_21 <- victims__00__setVictim(Struct19 {victim_idx :
            (x_8).data, victim_info : (x_20).info, victim_value :
            ((x_20).value_write ? ((x_20).value) : (x_9))});
            x_23 = x_9;
        end else begin
            let x_22 <- cache__00__valueRsLineRq(x_20);
            x_23 = x_22;
        end
        let x_24 <- transferUpDown_00(Struct25 {r_id : x_4, r_dl_rss_from :
        ((x_16).dir_sharers) & (~(((Bit#(2))'(2'h1)) << ((x_18)[0:0])))});
        let x_25 <- broadcast_parentChildren00(Struct23 {cs_inds :
        ((x_16).dir_sharers) & (~(((Bit#(2))'(2'h1)) << ((x_18)[0:0]))),
        cs_msg : Struct1 {id : (Bit#(6))'(6'hc), type_ : (Bool)'(False), addr
        : (x_17).addr, value : unpack(0)}});
    endrule

    rule rule_exec_00_161;
        $display ("Rule fired: rule_exec_00_161 at %t", $time);
        let x_0 <- deq_fifoL2E_00();
        Struct6 x_1 = ((x_0).lr_ir_pp);
        Bit#(3) x_2 = ((x_1).ir_msg_from);
        Struct1 x_3 = ((x_1).ir_msg);
        Bit#(4) x_4 = ((x_1).ir_mshr_id);
        Bool x_5 = ((x_1).ir_is_rs_rel);
        when (x_5, noAction);
        Struct9 x_6 = ((x_0).lr_ir);
        Struct11 x_7 = ((x_6).info);
        Struct5 x_8 = ((x_1).ir_by_victim);
        Vector#(4, Bit#(64)) x_9 = ((x_0).lr_value);
        let x_10 <- getMSHR_00(x_4);
        let x_11 <- getMSHRRq_00(x_4);
        let x_12 <- getMSHRFirstRs_00(x_4);
        Vector#(4, Bit#(64)) x_13 = (unpack(0));
        Bool x_14 = ((x_7).mesi_owned);
        Bit#(3) x_15 = ((x_7).mesi_status);
        Struct17 x_16 = (Struct17 {dir_st : (((x_7).mesi_dir_st) ==
        ((Bit#(3))'(3'h0)) ? ((Bit#(3))'(3'h1)) : ((x_7).mesi_dir_st)),
        dir_excl : ((((x_7).mesi_dir_sharers)[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(1))'(1'h0)) : (((Bit#(1))'(1'h1)) +
        ((((((x_7).mesi_dir_sharers)[1:1])[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(1))'(1'h0)) : (((Bit#(1))'(1'h1)) + (unpack(0))))))),
        dir_sharers : (x_7).mesi_dir_sharers});
        when ((x_10).m_rsb, noAction);
        when (((x_11).type_) == ((Bool)'(False)), noAction);
        when (((x_11).id) == ((Bit#(6))'(6'ha)), noAction);
        when ((Bool)'(True), noAction);
        Struct1 x_17 = (x_11);
        Bit#(3) x_18 = ((x_10).m_qidx);
        Struct18 x_19 = (Struct18 {addr : (x_3).addr, info_write :
        (Bool)'(False), info_hit : (x_6).info_hit, info_way : (x_6).info_way,
        edir_hit : (x_6).edir_hit, edir_way : (x_6).edir_way, edir_slot :
        (x_6).edir_slot, info : (x_6).info, value_write : (Bool)'(False),
        value : unpack(0), may_victim : (x_6).may_victim, reps :
        (x_6).reps});
        Struct18 x_20 = (Struct18 {addr : (x_19).addr, info_write :
        (Bool)'(True), info_hit : (x_19).info_hit, info_way :
        (x_19).info_way, edir_hit : (x_19).edir_hit, edir_way :
        (x_19).edir_way, edir_slot : (x_19).edir_slot, info : Struct11
        {mesi_owned : ((x_19).info).mesi_owned, mesi_status :
        ((x_19).info).mesi_status, mesi_dir_st : (Struct17 {dir_st :
        (Bit#(3))'(3'h4), dir_excl : (x_18)[0:0], dir_sharers :
        unpack(0)}).dir_st, mesi_dir_sharers : (((Struct17 {dir_st :
        (Bit#(3))'(3'h4), dir_excl : (x_18)[0:0], dir_sharers :
        unpack(0)}).dir_st) == ((Bit#(3))'(3'h2)) ? ((Struct17 {dir_st :
        (Bit#(3))'(3'h4), dir_excl : (x_18)[0:0], dir_sharers :
        unpack(0)}).dir_sharers) : (((Bit#(2))'(2'h1)) << ((Struct17 {dir_st
        : (Bit#(3))'(3'h4), dir_excl : (x_18)[0:0], dir_sharers :
        unpack(0)}).dir_excl)))}, value_write : (x_19).value_write, value :
        (x_19).value, may_victim : (x_19).may_victim, reps :
        (x_19).reps});
        Struct18 x_21 = (Struct18 {addr : (x_20).addr, info_write :
        (Bool)'(True), info_hit : (x_20).info_hit, info_way :
        (x_20).info_way, edir_hit : (x_20).edir_hit, edir_way :
        (x_20).edir_way, edir_slot : (x_20).edir_slot, info : Struct11
        {mesi_owned : ((x_20).info).mesi_owned, mesi_status :
        (Bit#(3))'(3'h1), mesi_dir_st : ((x_20).info).mesi_dir_st,
        mesi_dir_sharers : ((x_20).info).mesi_dir_sharers}, value_write :
        (x_20).value_write, value : (x_20).value, may_victim :
        (x_20).may_victim, reps : (x_20).reps});
        Struct18 x_22 = (Struct18 {addr : (x_21).addr, info_write :
        (Bool)'(True), info_hit : (x_21).info_hit, info_way :
        (x_21).info_way, edir_hit : (x_21).edir_hit, edir_way :
        (x_21).edir_way, edir_slot : (x_21).edir_slot, info : Struct11
        {mesi_owned : (Bool)'(False), mesi_status :
        ((x_21).info).mesi_status, mesi_dir_st : ((x_21).info).mesi_dir_st,
        mesi_dir_sharers : ((x_21).info).mesi_dir_sharers}, value_write :
        (x_21).value_write, value : (x_21).value, may_victim :
        (x_21).may_victim, reps :
        (x_21).reps});
        let x_25 = ?;
        if ((x_8).valid) begin
            let x_23 <- victims__00__setVictim(Struct19 {victim_idx :
            (x_8).data, victim_info : (x_22).info, victim_value :
            ((x_22).value_write ? ((x_22).value) : (x_9))});
            x_25 = x_9;
        end else begin
            let x_24 <- cache__00__valueRsLineRq(x_22);
            x_25 = x_24;
        end
        let x_26 <- releaseMSHR_00(x_4);
        Struct20 x_27 = (Struct20 {enq_type : (((x_18)[2:1]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : ((((x_18)[2:1]) ==
        ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : (x_18)[0:0], enq_msg : Struct1 {id : (Bit#(6))'(6'hb),
        type_ : (Bool)'(True), addr : (x_17).addr, value : unpack(0)}});
        let x_28 <- makeEnq_parentChildren00(x_27);
    endrule

    rule rule_exec_00_170;
        $display ("Rule fired: rule_exec_00_170 at %t", $time);
        let x_0 <- deq_fifoL2E_00();
        Struct6 x_1 = ((x_0).lr_ir_pp);
        Bit#(3) x_2 = ((x_1).ir_msg_from);
        Struct1 x_3 = ((x_1).ir_msg);
        Bit#(4) x_4 = ((x_1).ir_mshr_id);
        Bool x_5 = ((x_1).ir_is_rs_rel);
        when (! (x_5), noAction);
        Struct9 x_6 = ((x_0).lr_ir);
        Struct11 x_7 = ((x_6).info);
        Struct5 x_8 = ((x_1).ir_by_victim);
        Vector#(4, Bit#(64)) x_9 = ((x_0).lr_value);
        let x_10 <- getMSHR_00(x_4);
        let x_11 <- getMSHRRq_00(x_4);
        let x_12 <- getMSHRFirstRs_00(x_4);
        Vector#(4, Bit#(64)) x_13 = (unpack(0));
        Bool x_14 = ((x_7).mesi_owned);
        Bit#(3) x_15 = ((x_7).mesi_status);
        Struct17 x_16 = (Struct17 {dir_st : (((x_7).mesi_dir_st) ==
        ((Bit#(3))'(3'h0)) ? ((Bit#(3))'(3'h1)) : ((x_7).mesi_dir_st)),
        dir_excl : ((((x_7).mesi_dir_sharers)[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(1))'(1'h0)) : (((Bit#(1))'(1'h1)) +
        ((((((x_7).mesi_dir_sharers)[1:1])[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(1))'(1'h0)) : (((Bit#(1))'(1'h1)) + (unpack(0))))))),
        dir_sharers : (x_7).mesi_dir_sharers});
        when ((x_2) == ((Bit#(3))'(3'h4)), noAction);
        when (((x_3).id) == ((Bit#(6))'(6'hc)), noAction);
        when (! ((x_3).type_), noAction);
        when (((x_16).dir_st) == ((Bit#(3))'(3'h1)), noAction);
        Struct1 x_17 = (x_3);
        Struct18 x_18 = (Struct18 {addr : (x_3).addr, info_write :
        (Bool)'(False), info_hit : (x_6).info_hit, info_way : (x_6).info_way,
        edir_hit : (x_6).edir_hit, edir_way : (x_6).edir_way, edir_slot :
        (x_6).edir_slot, info : (x_6).info, value_write : (Bool)'(False),
        value : unpack(0), may_victim : (x_6).may_victim, reps :
        (x_6).reps});
        Struct18 x_19 = (Struct18 {addr : (x_18).addr, info_write :
        (Bool)'(True), info_hit : (x_18).info_hit, info_way :
        (x_18).info_way, edir_hit : (x_18).edir_hit, edir_way :
        (x_18).edir_way, edir_slot : (x_18).edir_slot, info : Struct11
        {mesi_owned : ((x_18).info).mesi_owned, mesi_status :
        (Bit#(3))'(3'h1), mesi_dir_st : ((x_18).info).mesi_dir_st,
        mesi_dir_sharers : ((x_18).info).mesi_dir_sharers}, value_write :
        (x_18).value_write, value : (x_18).value, may_victim :
        (x_18).may_victim, reps : (x_18).reps});
        Struct18 x_20 = (Struct18 {addr : (x_19).addr, info_write :
        (Bool)'(True), info_hit : (x_19).info_hit, info_way :
        (x_19).info_way, edir_hit : (x_19).edir_hit, edir_way :
        (x_19).edir_way, edir_slot : (x_19).edir_slot, info : Struct11
        {mesi_owned : (Bool)'(False), mesi_status :
        ((x_19).info).mesi_status, mesi_dir_st : ((x_19).info).mesi_dir_st,
        mesi_dir_sharers : ((x_19).info).mesi_dir_sharers}, value_write :
        (x_19).value_write, value : (x_19).value, may_victim :
        (x_19).may_victim, reps :
        (x_19).reps});
        let x_23 = ?;
        if ((x_8).valid) begin
            let x_21 <- victims__00__setVictim(Struct19 {victim_idx :
            (x_8).data, victim_info : (x_20).info, victim_value :
            ((x_20).value_write ? ((x_20).value) : (x_9))});
            x_23 = x_9;
        end else begin
            let x_22 <- cache__00__valueRsLineRq(x_20);
            x_23 = x_22;
        end
        Struct20 x_24 = (Struct20 {enq_type : ((((Bit#(3))'(3'h2))[2:1]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : (((((Bit#(3))'(3'h2))[2:1])
        == ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : ((Bit#(3))'(3'h2))[0:0], enq_msg : Struct1 {id :
        (Bit#(6))'(6'hd), type_ : (Bool)'(True), addr : (x_17).addr, value :
        unpack(0)}});
        let x_25 <- makeEnq_parentChildren00(x_24);
        let x_26 <- releaseMSHR_00(x_4);
    endrule

    rule rule_exec_00_171;
        $display ("Rule fired: rule_exec_00_171 at %t", $time);
        let x_0 <- deq_fifoL2E_00();
        Struct6 x_1 = ((x_0).lr_ir_pp);
        Bit#(3) x_2 = ((x_1).ir_msg_from);
        Struct1 x_3 = ((x_1).ir_msg);
        Bit#(4) x_4 = ((x_1).ir_mshr_id);
        Bool x_5 = ((x_1).ir_is_rs_rel);
        when (! (x_5), noAction);
        Struct9 x_6 = ((x_0).lr_ir);
        Struct11 x_7 = ((x_6).info);
        Struct5 x_8 = ((x_1).ir_by_victim);
        Vector#(4, Bit#(64)) x_9 = ((x_0).lr_value);
        let x_10 <- getMSHR_00(x_4);
        let x_11 <- getMSHRRq_00(x_4);
        let x_12 <- getMSHRFirstRs_00(x_4);
        Vector#(4, Bit#(64)) x_13 = (unpack(0));
        Bool x_14 = ((x_7).mesi_owned);
        Bit#(3) x_15 = ((x_7).mesi_status);
        Struct17 x_16 = (Struct17 {dir_st : (((x_7).mesi_dir_st) ==
        ((Bit#(3))'(3'h0)) ? ((Bit#(3))'(3'h1)) : ((x_7).mesi_dir_st)),
        dir_excl : ((((x_7).mesi_dir_sharers)[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(1))'(1'h0)) : (((Bit#(1))'(1'h1)) +
        ((((((x_7).mesi_dir_sharers)[1:1])[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(1))'(1'h0)) : (((Bit#(1))'(1'h1)) + (unpack(0))))))),
        dir_sharers : (x_7).mesi_dir_sharers});
        when ((x_2) == ((Bit#(3))'(3'h4)), noAction);
        when (((x_3).id) == ((Bit#(6))'(6'he)), noAction);
        when (! ((x_3).type_), noAction);
        when ((! ((x_15) < ((Bit#(3))'(3'h3)))) && (((x_16).dir_st) ==
        ((Bit#(3))'(3'h1))), noAction);
        Struct1 x_17 = (x_3);
        Struct18 x_18 = (Struct18 {addr : (x_3).addr, info_write :
        (Bool)'(False), info_hit : (x_6).info_hit, info_way : (x_6).info_way,
        edir_hit : (x_6).edir_hit, edir_way : (x_6).edir_way, edir_slot :
        (x_6).edir_slot, info : (x_6).info, value_write : (Bool)'(False),
        value : unpack(0), may_victim : (x_6).may_victim, reps :
        (x_6).reps});
        Struct18 x_19 = (Struct18 {addr : (x_18).addr, info_write :
        (Bool)'(True), info_hit : (x_18).info_hit, info_way :
        (x_18).info_way, edir_hit : (x_18).edir_hit, edir_way :
        (x_18).edir_way, edir_slot : (x_18).edir_slot, info : Struct11
        {mesi_owned : ((x_18).info).mesi_owned, mesi_status :
        (Bit#(3))'(3'h1), mesi_dir_st : ((x_18).info).mesi_dir_st,
        mesi_dir_sharers : ((x_18).info).mesi_dir_sharers}, value_write :
        (x_18).value_write, value : (x_18).value, may_victim :
        (x_18).may_victim, reps : (x_18).reps});
        Struct18 x_20 = (Struct18 {addr : (x_19).addr, info_write :
        (Bool)'(True), info_hit : (x_19).info_hit, info_way :
        (x_19).info_way, edir_hit : (x_19).edir_hit, edir_way :
        (x_19).edir_way, edir_slot : (x_19).edir_slot, info : Struct11
        {mesi_owned : (Bool)'(False), mesi_status :
        ((x_19).info).mesi_status, mesi_dir_st : ((x_19).info).mesi_dir_st,
        mesi_dir_sharers : ((x_19).info).mesi_dir_sharers}, value_write :
        (x_19).value_write, value : (x_19).value, may_victim :
        (x_19).may_victim, reps :
        (x_19).reps});
        let x_23 = ?;
        if ((x_8).valid) begin
            let x_21 <- victims__00__setVictim(Struct19 {victim_idx :
            (x_8).data, victim_info : (x_20).info, victim_value :
            ((x_20).value_write ? ((x_20).value) : (x_9))});
            x_23 = x_9;
        end else begin
            let x_22 <- cache__00__valueRsLineRq(x_20);
            x_23 = x_22;
        end
        Struct20 x_24 = (Struct20 {enq_type : ((((Bit#(3))'(3'h2))[2:1]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : (((((Bit#(3))'(3'h2))[2:1])
        == ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : ((Bit#(3))'(3'h2))[0:0], enq_msg : Struct1 {id :
        (Bit#(6))'(6'hf), type_ : (Bool)'(True), addr : (x_17).addr, value :
        unpack(0)}});
        let x_25 <- makeEnq_parentChildren00(x_24);
        let x_26 <- releaseMSHR_00(x_4);
    endrule

    rule rule_exec_00_190;
        $display ("Rule fired: rule_exec_00_190 at %t", $time);
        let x_0 <- deq_fifoL2E_00();
        Struct6 x_1 = ((x_0).lr_ir_pp);
        Bit#(3) x_2 = ((x_1).ir_msg_from);
        Struct1 x_3 = ((x_1).ir_msg);
        Bit#(4) x_4 = ((x_1).ir_mshr_id);
        Bool x_5 = ((x_1).ir_is_rs_rel);
        when (! (x_5), noAction);
        Struct9 x_6 = ((x_0).lr_ir);
        Struct11 x_7 = ((x_6).info);
        Struct5 x_8 = ((x_1).ir_by_victim);
        Vector#(4, Bit#(64)) x_9 = ((x_0).lr_value);
        let x_10 <- getMSHR_00(x_4);
        let x_11 <- getMSHRRq_00(x_4);
        let x_12 <- getMSHRFirstRs_00(x_4);
        Vector#(4, Bit#(64)) x_13 = (unpack(0));
        Bool x_14 = ((x_7).mesi_owned);
        Bit#(3) x_15 = ((x_7).mesi_status);
        Struct17 x_16 = (Struct17 {dir_st : (((x_7).mesi_dir_st) ==
        ((Bit#(3))'(3'h0)) ? ((Bit#(3))'(3'h1)) : ((x_7).mesi_dir_st)),
        dir_excl : ((((x_7).mesi_dir_sharers)[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(1))'(1'h0)) : (((Bit#(1))'(1'h1)) +
        ((((((x_7).mesi_dir_sharers)[1:1])[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(1))'(1'h0)) : (((Bit#(1))'(1'h1)) + (unpack(0))))))),
        dir_sharers : (x_7).mesi_dir_sharers});
        when ((x_2) == ((Bit#(3))'(3'h4)), noAction);
        when (((x_3).id) == ((Bit#(6))'(6'hc)), noAction);
        when (! ((x_3).type_), noAction);
        when (((Bool)'(True)) && (((Bool)'(True)) && (((x_16).dir_st) ==
        ((Bit#(3))'(3'h2)))), noAction);
        Struct1 x_17 = (x_3);
        Struct18 x_18 = (Struct18 {addr : (x_3).addr, info_write :
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
        let x_21 <- registerDL_00(Struct22 {r_id : x_4, r_dl_rss_from :
        (x_16).dir_sharers, r_dl_rsb : (Bool)'(True), r_dl_rsbTo :
        (Bit#(3))'(3'h2)});
        let x_22 <- broadcast_parentChildren00(Struct23 {cs_inds :
        (x_16).dir_sharers, cs_msg : Struct1 {id : (Bit#(6))'(6'hc), type_ :
        (Bool)'(False), addr : (x_17).addr, value : unpack(0)}});
    endrule

    rule rule_exec_00_191;
        $display ("Rule fired: rule_exec_00_191 at %t", $time);
        let x_0 <- deq_fifoL2E_00();
        Struct6 x_1 = ((x_0).lr_ir_pp);
        Bit#(3) x_2 = ((x_1).ir_msg_from);
        Struct1 x_3 = ((x_1).ir_msg);
        Bit#(4) x_4 = ((x_1).ir_mshr_id);
        Bool x_5 = ((x_1).ir_is_rs_rel);
        when (! (x_5), noAction);
        Struct9 x_6 = ((x_0).lr_ir);
        Struct11 x_7 = ((x_6).info);
        Struct5 x_8 = ((x_1).ir_by_victim);
        Vector#(4, Bit#(64)) x_9 = ((x_0).lr_value);
        let x_10 <- getMSHR_00(x_4);
        let x_11 <- getMSHRRq_00(x_4);
        let x_12 <- getMSHRFirstRs_00(x_4);
        Vector#(4, Bit#(64)) x_13 = (unpack(0));
        Bool x_14 = ((x_7).mesi_owned);
        Bit#(3) x_15 = ((x_7).mesi_status);
        Struct17 x_16 = (Struct17 {dir_st : (((x_7).mesi_dir_st) ==
        ((Bit#(3))'(3'h0)) ? ((Bit#(3))'(3'h1)) : ((x_7).mesi_dir_st)),
        dir_excl : ((((x_7).mesi_dir_sharers)[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(1))'(1'h0)) : (((Bit#(1))'(1'h1)) +
        ((((((x_7).mesi_dir_sharers)[1:1])[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(1))'(1'h0)) : (((Bit#(1))'(1'h1)) + (unpack(0))))))),
        dir_sharers : (x_7).mesi_dir_sharers});
        when ((x_2) == ((Bit#(3))'(3'h4)), noAction);
        when (((x_3).id) == ((Bit#(6))'(6'he)), noAction);
        when (! ((x_3).type_), noAction);
        when (((Bool)'(True)) && ((! (((x_16).dir_st) < ((Bit#(3))'(3'h3))))
        && (! (((Bit#(3))'(3'h4)) < ((x_16).dir_st)))), noAction);
        Struct1 x_17 = (x_3);
        Struct18 x_18 = (Struct18 {addr : (x_3).addr, info_write :
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
        let x_21 <- registerDL_00(Struct22 {r_id : x_4, r_dl_rss_from :
        (unpack(0)) | (((Bit#(2))'(2'h1)) <<
        (({((Bit#(2))'(2'h1)),((x_16).dir_excl)})[0:0])), r_dl_rsb :
        (Bool)'(True), r_dl_rsbTo : (Bit#(3))'(3'h2)});
        Struct20 x_22 = (Struct20 {enq_type :
        ((({((Bit#(2))'(2'h2)),((x_16).dir_excl)})[2:1]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) :
        (((({((Bit#(2))'(2'h2)),((x_16).dir_excl)})[2:1]) ==
        ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : ({((Bit#(2))'(2'h2)),((x_16).dir_excl)})[0:0], enq_msg :
        Struct1 {id : (Bit#(6))'(6'he), type_ : (Bool)'(False), addr :
        (x_17).addr, value : unpack(0)}});
        let x_23 <- makeEnq_parentChildren00(x_22);
    endrule

    rule rule_exec_00_192;
        $display ("Rule fired: rule_exec_00_192 at %t", $time);
        let x_0 <- deq_fifoL2E_00();
        Struct6 x_1 = ((x_0).lr_ir_pp);
        Bit#(3) x_2 = ((x_1).ir_msg_from);
        Struct1 x_3 = ((x_1).ir_msg);
        Bit#(4) x_4 = ((x_1).ir_mshr_id);
        Bool x_5 = ((x_1).ir_is_rs_rel);
        when (! (x_5), noAction);
        Struct9 x_6 = ((x_0).lr_ir);
        Struct11 x_7 = ((x_6).info);
        Struct5 x_8 = ((x_1).ir_by_victim);
        Vector#(4, Bit#(64)) x_9 = ((x_0).lr_value);
        let x_10 <- getMSHR_00(x_4);
        let x_11 <- getMSHRRq_00(x_4);
        let x_12 <- getMSHRFirstRs_00(x_4);
        Vector#(4, Bit#(64)) x_13 = (unpack(0));
        Bool x_14 = ((x_7).mesi_owned);
        Bit#(3) x_15 = ((x_7).mesi_status);
        Struct17 x_16 = (Struct17 {dir_st : (((x_7).mesi_dir_st) ==
        ((Bit#(3))'(3'h0)) ? ((Bit#(3))'(3'h1)) : ((x_7).mesi_dir_st)),
        dir_excl : ((((x_7).mesi_dir_sharers)[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(1))'(1'h0)) : (((Bit#(1))'(1'h1)) +
        ((((((x_7).mesi_dir_sharers)[1:1])[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(1))'(1'h0)) : (((Bit#(1))'(1'h1)) + (unpack(0))))))),
        dir_sharers : (x_7).mesi_dir_sharers});
        when ((x_2) == ((Bit#(3))'(3'h4)), noAction);
        when (((x_3).id) == ((Bit#(6))'(6'he)), noAction);
        when (! ((x_3).type_), noAction);
        when (((Bool)'(True)) && (((Bool)'(True)) && (((x_16).dir_st) ==
        ((Bit#(3))'(3'h2)))), noAction);
        Struct1 x_17 = (x_3);
        Struct18 x_18 = (Struct18 {addr : (x_3).addr, info_write :
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
        let x_21 <- registerDL_00(Struct22 {r_id : x_4, r_dl_rss_from :
        (x_16).dir_sharers, r_dl_rsb : (Bool)'(True), r_dl_rsbTo :
        (Bit#(3))'(3'h2)});
        let x_22 <- broadcast_parentChildren00(Struct23 {cs_inds :
        (x_16).dir_sharers, cs_msg : Struct1 {id : (Bit#(6))'(6'hc), type_ :
        (Bool)'(False), addr : (x_17).addr, value : unpack(0)}});
    endrule

    rule rule_exec_00_11010;
        $display ("Rule fired: rule_exec_00_11010 at %t", $time);
        let x_0 <- deq_fifoL2E_00();
        Struct6 x_1 = ((x_0).lr_ir_pp);
        Bit#(3) x_2 = ((x_1).ir_msg_from);
        Struct1 x_3 = ((x_1).ir_msg);
        Bit#(4) x_4 = ((x_1).ir_mshr_id);
        Bool x_5 = ((x_1).ir_is_rs_rel);
        when (x_5, noAction);
        Struct9 x_6 = ((x_0).lr_ir);
        Struct11 x_7 = ((x_6).info);
        Struct5 x_8 = ((x_1).ir_by_victim);
        Vector#(4, Bit#(64)) x_9 = ((x_0).lr_value);
        let x_10 <- getMSHR_00(x_4);
        let x_11 <- getMSHRRq_00(x_4);
        let x_12 <- getMSHRFirstRs_00(x_4);
        Vector#(4, Bit#(64)) x_13 = (unpack(0));
        Bool x_14 = ((x_7).mesi_owned);
        Bit#(3) x_15 = ((x_7).mesi_status);
        Struct17 x_16 = (Struct17 {dir_st : (((x_7).mesi_dir_st) ==
        ((Bit#(3))'(3'h0)) ? ((Bit#(3))'(3'h1)) : ((x_7).mesi_dir_st)),
        dir_excl : ((((x_7).mesi_dir_sharers)[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(1))'(1'h0)) : (((Bit#(1))'(1'h1)) +
        ((((((x_7).mesi_dir_sharers)[1:1])[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(1))'(1'h0)) : (((Bit#(1))'(1'h1)) + (unpack(0))))))),
        dir_sharers : (x_7).mesi_dir_sharers});
        when ((x_10).m_rsb, noAction);
        when (((x_11).type_) == ((Bool)'(False)), noAction);
        when (((x_11).id) == ((Bit#(6))'(6'hc)), noAction);
        when ((Bool)'(True), noAction);
        Struct1 x_17 = (x_11);
        Bit#(3) x_18 = ((x_10).m_qidx);
        Struct18 x_19 = (Struct18 {addr : (x_3).addr, info_write :
        (Bool)'(False), info_hit : (x_6).info_hit, info_way : (x_6).info_way,
        edir_hit : (x_6).edir_hit, edir_way : (x_6).edir_way, edir_slot :
        (x_6).edir_slot, info : (x_6).info, value_write : (Bool)'(False),
        value : unpack(0), may_victim : (x_6).may_victim, reps :
        (x_6).reps});
        Struct18 x_20 = (Struct18 {addr : (x_19).addr, info_write :
        (Bool)'(True), info_hit : (x_19).info_hit, info_way :
        (x_19).info_way, edir_hit : (x_19).edir_hit, edir_way :
        (x_19).edir_way, edir_slot : (x_19).edir_slot, info : Struct11
        {mesi_owned : ((x_19).info).mesi_owned, mesi_status :
        ((x_19).info).mesi_status, mesi_dir_st : (Struct17 {dir_st :
        (Bit#(3))'(3'h1), dir_excl : unpack(0), dir_sharers :
        unpack(0)}).dir_st, mesi_dir_sharers : (((Struct17 {dir_st :
        (Bit#(3))'(3'h1), dir_excl : unpack(0), dir_sharers :
        unpack(0)}).dir_st) == ((Bit#(3))'(3'h2)) ? ((Struct17 {dir_st :
        (Bit#(3))'(3'h1), dir_excl : unpack(0), dir_sharers :
        unpack(0)}).dir_sharers) : (((Bit#(2))'(2'h1)) << ((Struct17 {dir_st
        : (Bit#(3))'(3'h1), dir_excl : unpack(0), dir_sharers :
        unpack(0)}).dir_excl)))}, value_write : (x_19).value_write, value :
        (x_19).value, may_victim : (x_19).may_victim, reps :
        (x_19).reps});
        Struct18 x_21 = (Struct18 {addr : (x_20).addr, info_write :
        (Bool)'(True), info_hit : (x_20).info_hit, info_way :
        (x_20).info_way, edir_hit : (x_20).edir_hit, edir_way :
        (x_20).edir_way, edir_slot : (x_20).edir_slot, info : Struct11
        {mesi_owned : ((x_20).info).mesi_owned, mesi_status :
        (Bit#(3))'(3'h1), mesi_dir_st : ((x_20).info).mesi_dir_st,
        mesi_dir_sharers : ((x_20).info).mesi_dir_sharers}, value_write :
        (x_20).value_write, value : (x_20).value, may_victim :
        (x_20).may_victim, reps : (x_20).reps});
        Struct18 x_22 = (Struct18 {addr : (x_21).addr, info_write :
        (Bool)'(True), info_hit : (x_21).info_hit, info_way :
        (x_21).info_way, edir_hit : (x_21).edir_hit, edir_way :
        (x_21).edir_way, edir_slot : (x_21).edir_slot, info : Struct11
        {mesi_owned : (Bool)'(False), mesi_status :
        ((x_21).info).mesi_status, mesi_dir_st : ((x_21).info).mesi_dir_st,
        mesi_dir_sharers : ((x_21).info).mesi_dir_sharers}, value_write :
        (x_21).value_write, value : (x_21).value, may_victim :
        (x_21).may_victim, reps :
        (x_21).reps});
        let x_25 = ?;
        if ((x_8).valid) begin
            let x_23 <- victims__00__setVictim(Struct19 {victim_idx :
            (x_8).data, victim_info : (x_22).info, victim_value :
            ((x_22).value_write ? ((x_22).value) : (x_9))});
            x_25 = x_9;
        end else begin
            let x_24 <- cache__00__valueRsLineRq(x_22);
            x_25 = x_24;
        end
        let x_26 <- releaseMSHR_00(x_4);
        Struct20 x_27 = (Struct20 {enq_type : (((x_18)[2:1]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : ((((x_18)[2:1]) ==
        ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : (x_18)[0:0], enq_msg : Struct1 {id : (Bit#(6))'(6'hd),
        type_ : (Bool)'(True), addr : (x_17).addr, value : unpack(0)}});
        let x_28 <- makeEnq_parentChildren00(x_27);
    endrule

    rule rule_exec_00_11011;
        $display ("Rule fired: rule_exec_00_11011 at %t", $time);
        let x_0 <- deq_fifoL2E_00();
        Struct6 x_1 = ((x_0).lr_ir_pp);
        Bit#(3) x_2 = ((x_1).ir_msg_from);
        Struct1 x_3 = ((x_1).ir_msg);
        Bit#(4) x_4 = ((x_1).ir_mshr_id);
        Bool x_5 = ((x_1).ir_is_rs_rel);
        when (x_5, noAction);
        Struct9 x_6 = ((x_0).lr_ir);
        Struct11 x_7 = ((x_6).info);
        Struct5 x_8 = ((x_1).ir_by_victim);
        Vector#(4, Bit#(64)) x_9 = ((x_0).lr_value);
        let x_10 <- getMSHR_00(x_4);
        let x_11 <- getMSHRRq_00(x_4);
        let x_12 <- getMSHRFirstRs_00(x_4);
        Vector#(4, Bit#(64)) x_13 = (unpack(0));
        Bool x_14 = ((x_7).mesi_owned);
        Bit#(3) x_15 = ((x_7).mesi_status);
        Struct17 x_16 = (Struct17 {dir_st : (((x_7).mesi_dir_st) ==
        ((Bit#(3))'(3'h0)) ? ((Bit#(3))'(3'h1)) : ((x_7).mesi_dir_st)),
        dir_excl : ((((x_7).mesi_dir_sharers)[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(1))'(1'h0)) : (((Bit#(1))'(1'h1)) +
        ((((((x_7).mesi_dir_sharers)[1:1])[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(1))'(1'h0)) : (((Bit#(1))'(1'h1)) + (unpack(0))))))),
        dir_sharers : (x_7).mesi_dir_sharers});
        when ((x_10).m_rsb, noAction);
        when (((x_11).type_) == ((Bool)'(False)), noAction);
        when (((x_11).id) == ((Bit#(6))'(6'he)), noAction);
        when ((Bool)'(True), noAction);
        Struct1 x_17 = (x_11);
        Bit#(3) x_18 = ((x_10).m_qidx);
        Struct18 x_19 = (Struct18 {addr : (x_3).addr, info_write :
        (Bool)'(False), info_hit : (x_6).info_hit, info_way : (x_6).info_way,
        edir_hit : (x_6).edir_hit, edir_way : (x_6).edir_way, edir_slot :
        (x_6).edir_slot, info : (x_6).info, value_write : (Bool)'(False),
        value : unpack(0), may_victim : (x_6).may_victim, reps :
        (x_6).reps});
        Struct18 x_20 = (Struct18 {addr : (x_19).addr, info_write :
        (Bool)'(True), info_hit : (x_19).info_hit, info_way :
        (x_19).info_way, edir_hit : (x_19).edir_hit, edir_way :
        (x_19).edir_way, edir_slot : (x_19).edir_slot, info : Struct11
        {mesi_owned : ((x_19).info).mesi_owned, mesi_status :
        ((x_19).info).mesi_status, mesi_dir_st : (Struct17 {dir_st :
        (Bit#(3))'(3'h1), dir_excl : unpack(0), dir_sharers :
        unpack(0)}).dir_st, mesi_dir_sharers : (((Struct17 {dir_st :
        (Bit#(3))'(3'h1), dir_excl : unpack(0), dir_sharers :
        unpack(0)}).dir_st) == ((Bit#(3))'(3'h2)) ? ((Struct17 {dir_st :
        (Bit#(3))'(3'h1), dir_excl : unpack(0), dir_sharers :
        unpack(0)}).dir_sharers) : (((Bit#(2))'(2'h1)) << ((Struct17 {dir_st
        : (Bit#(3))'(3'h1), dir_excl : unpack(0), dir_sharers :
        unpack(0)}).dir_excl)))}, value_write : (x_19).value_write, value :
        (x_19).value, may_victim : (x_19).may_victim, reps :
        (x_19).reps});
        Struct18 x_21 = (Struct18 {addr : (x_20).addr, info_write :
        (Bool)'(True), info_hit : (x_20).info_hit, info_way :
        (x_20).info_way, edir_hit : (x_20).edir_hit, edir_way :
        (x_20).edir_way, edir_slot : (x_20).edir_slot, info : Struct11
        {mesi_owned : ((x_20).info).mesi_owned, mesi_status :
        (Bit#(3))'(3'h1), mesi_dir_st : ((x_20).info).mesi_dir_st,
        mesi_dir_sharers : ((x_20).info).mesi_dir_sharers}, value_write :
        (x_20).value_write, value : (x_20).value, may_victim :
        (x_20).may_victim, reps : (x_20).reps});
        Struct18 x_22 = (Struct18 {addr : (x_21).addr, info_write :
        (Bool)'(True), info_hit : (x_21).info_hit, info_way :
        (x_21).info_way, edir_hit : (x_21).edir_hit, edir_way :
        (x_21).edir_way, edir_slot : (x_21).edir_slot, info : Struct11
        {mesi_owned : (Bool)'(False), mesi_status :
        ((x_21).info).mesi_status, mesi_dir_st : ((x_21).info).mesi_dir_st,
        mesi_dir_sharers : ((x_21).info).mesi_dir_sharers}, value_write :
        (x_21).value_write, value : (x_21).value, may_victim :
        (x_21).may_victim, reps :
        (x_21).reps});
        let x_25 = ?;
        if ((x_8).valid) begin
            let x_23 <- victims__00__setVictim(Struct19 {victim_idx :
            (x_8).data, victim_info : (x_22).info, victim_value :
            ((x_22).value_write ? ((x_22).value) : (x_9))});
            x_25 = x_9;
        end else begin
            let x_24 <- cache__00__valueRsLineRq(x_22);
            x_25 = x_24;
        end
        let x_26 <- releaseMSHR_00(x_4);
        Struct20 x_27 = (Struct20 {enq_type : (((x_18)[2:1]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : ((((x_18)[2:1]) ==
        ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : (x_18)[0:0], enq_msg : Struct1 {id : (Bit#(6))'(6'hf),
        type_ : (Bool)'(True), addr : (x_17).addr, value : unpack(0)}});
        let x_28 <- makeEnq_parentChildren00(x_27);
    endrule

    rule rule_exec_00_20;
        $display ("Rule fired: rule_exec_00_20 at %t", $time);
        let x_0 <- victims__00__getFirstVictim();
        Bit#(64) x_1 = ((x_0).victim_addr);
        Struct11 x_2 = ((x_0).victim_info);
        Vector#(4, Bit#(64)) x_3 = ((x_0).victim_value);
        Struct1 x_4 = (Struct1 {id : unpack(0), type_ : (Bool)'(False), addr
        : x_1, value : unpack(0)});
        Struct15 x_5 = (Struct15 {m_status : (Bit#(3))'(3'h5), m_next :
        unpack(0), m_is_ul : (Bool)'(True), m_addr : x_1, m_qidx : unpack(0),
        m_rsb : (Bool)'(False), m_dl_rss_from : unpack(0), m_dl_rss_recv :
        unpack(0)});
        Struct1 x_6 = (unpack(0));
        Struct1 x_7 = (unpack(0));
        Vector#(4, Bit#(64)) x_8 = (unpack(0));
        Bool x_9 = ((x_2).mesi_owned);
        Bit#(3) x_10 = ((x_2).mesi_status);
        Struct17 x_11 = (Struct17 {dir_st : (((x_2).mesi_dir_st) ==
        ((Bit#(3))'(3'h0)) ? ((Bit#(3))'(3'h1)) : ((x_2).mesi_dir_st)),
        dir_excl : ((((x_2).mesi_dir_sharers)[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(1))'(1'h0)) : (((Bit#(1))'(1'h1)) +
        ((((((x_2).mesi_dir_sharers)[1:1])[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(1))'(1'h0)) : (((Bit#(1))'(1'h1)) + (unpack(0))))))),
        dir_sharers : (x_2).mesi_dir_sharers});
        when (! ((x_4).type_), noAction);
        when (((x_9) == ((Bool)'(False))) && (((((Bit#(3))'(3'h0)) < (x_10))
        && ((x_10) < ((Bit#(3))'(3'h4)))) && (((x_11).dir_st) ==
        ((Bit#(3))'(3'h1)))), noAction);
        Struct20 x_12 = (Struct20 {enq_type : ((((Bit#(3))'(3'h0))[2:1]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : (((((Bit#(3))'(3'h0))[2:1])
        == ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : ((Bit#(3))'(3'h0))[0:0], enq_msg : Struct1 {id :
        (Bit#(6))'(6'h14), type_ : (Bool)'(False), addr : (x_4).addr, value :
        unpack(0)}});
        let x_13 <- makeEnq_parentChildren00(x_12);
        let x_14 <- setULImm_00(x_4);
        let x_15 <- victims__00__setVictimRq(x_1);
    endrule

    rule rule_exec_00_21;
        $display ("Rule fired: rule_exec_00_21 at %t", $time);
        let x_0 <- victims__00__getFirstVictim();
        Bit#(64) x_1 = ((x_0).victim_addr);
        Struct11 x_2 = ((x_0).victim_info);
        Vector#(4, Bit#(64)) x_3 = ((x_0).victim_value);
        Struct1 x_4 = (Struct1 {id : unpack(0), type_ : (Bool)'(False), addr
        : x_1, value : unpack(0)});
        Struct15 x_5 = (Struct15 {m_status : (Bit#(3))'(3'h5), m_next :
        unpack(0), m_is_ul : (Bool)'(True), m_addr : x_1, m_qidx : unpack(0),
        m_rsb : (Bool)'(False), m_dl_rss_from : unpack(0), m_dl_rss_recv :
        unpack(0)});
        Struct1 x_6 = (unpack(0));
        Struct1 x_7 = (unpack(0));
        Vector#(4, Bit#(64)) x_8 = (unpack(0));
        Bool x_9 = ((x_2).mesi_owned);
        Bit#(3) x_10 = ((x_2).mesi_status);
        Struct17 x_11 = (Struct17 {dir_st : (((x_2).mesi_dir_st) ==
        ((Bit#(3))'(3'h0)) ? ((Bit#(3))'(3'h1)) : ((x_2).mesi_dir_st)),
        dir_excl : ((((x_2).mesi_dir_sharers)[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(1))'(1'h0)) : (((Bit#(1))'(1'h1)) +
        ((((((x_2).mesi_dir_sharers)[1:1])[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(1))'(1'h0)) : (((Bit#(1))'(1'h1)) + (unpack(0))))))),
        dir_sharers : (x_2).mesi_dir_sharers});
        when (! ((x_4).type_), noAction);
        when ((((x_11).dir_st) == ((Bit#(3))'(3'h1))) && ((((x_9) ==
        ((Bool)'(True))) && (((Bit#(3))'(3'h1)) < (x_10))) || (((x_9) ==
        ((Bool)'(False))) && ((((Bit#(3))'(3'h0)) < (x_10)) && ((x_10) <
        ((Bit#(3))'(3'h3)))))), noAction);
        Struct20 x_12 = (Struct20 {enq_type : ((((Bit#(3))'(3'h0))[2:1]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : (((((Bit#(3))'(3'h0))[2:1])
        == ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : ((Bit#(3))'(3'h0))[0:0], enq_msg : Struct1 {id :
        (Bit#(6))'(6'h15), type_ : (Bool)'(False), addr : (x_4).addr, value :
        x_3}});
        let x_13 <- makeEnq_parentChildren00(x_12);
        let x_14 <- setULImm_00(x_4);
        let x_15 <- victims__00__setVictimRq(x_1);
    endrule

    rule rule_exec_00_23;
        $display ("Rule fired: rule_exec_00_23 at %t", $time);
        let x_0 <- victims__00__getFirstVictim();
        Bit#(64) x_1 = ((x_0).victim_addr);
        Struct11 x_2 = ((x_0).victim_info);
        Vector#(4, Bit#(64)) x_3 = ((x_0).victim_value);
        Struct1 x_4 = (Struct1 {id : unpack(0), type_ : (Bool)'(False), addr
        : x_1, value : unpack(0)});
        Struct15 x_5 = (Struct15 {m_status : (Bit#(3))'(3'h5), m_next :
        unpack(0), m_is_ul : (Bool)'(True), m_addr : x_1, m_qidx : unpack(0),
        m_rsb : (Bool)'(False), m_dl_rss_from : unpack(0), m_dl_rss_recv :
        unpack(0)});
        Struct1 x_6 = (unpack(0));
        Struct1 x_7 = (unpack(0));
        Vector#(4, Bit#(64)) x_8 = (unpack(0));
        Bool x_9 = ((x_2).mesi_owned);
        Bit#(3) x_10 = ((x_2).mesi_status);
        Struct17 x_11 = (Struct17 {dir_st : (((x_2).mesi_dir_st) ==
        ((Bit#(3))'(3'h0)) ? ((Bit#(3))'(3'h1)) : ((x_2).mesi_dir_st)),
        dir_excl : ((((x_2).mesi_dir_sharers)[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(1))'(1'h0)) : (((Bit#(1))'(1'h1)) +
        ((((((x_2).mesi_dir_sharers)[1:1])[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(1))'(1'h0)) : (((Bit#(1))'(1'h1)) + (unpack(0))))))),
        dir_sharers : (x_2).mesi_dir_sharers});
        when ((((x_10) == ((Bit#(3))'(3'h1))) && (! (((x_11).dir_st) ==
        ((Bit#(3))'(3'h3))))) || (((x_10) == ((Bit#(3))'(3'h2))) && ((x_9) ==
        ((Bool)'(False)))), noAction);
        let x_12 <- canImm_00(x_1);
        let x_13 <- victims__00__releaseVictim(x_1);
    endrule

    // No methods in this module
endmodule

interface Module76;

endinterface

module mkModule76#(function Action victims__000__setVictimRq(Bit#(64) _),
    function Action setULImm_000(Struct1 _),
    function ActionValue#(Struct14) victims__000__getFirstVictim(),
    function Action victims__000__setVictim(Struct47 _),
    function Action registerUL_000(Struct46 _),
    function Action makeEnq_parentChildren000(Struct20 _),
    function ActionValue#(Vector#(4, Bit#(64))) cache__000__valueRsLineRq(Struct45 _),
    function ActionValue#(Struct1) getMSHRFirstRs_000(Bit#(3) _),
    function ActionValue#(Struct1) getMSHRRq_000(Bit#(3) _),
    function ActionValue#(Struct44) getMSHR_000(Bit#(3) _),
    function ActionValue#(Struct43) deq_fifoL2E_000(),
    function ActionValue#(Struct14) victims__000__getVictim(Bit#(2) _),
    function Action enq_fifoL2E_000(Struct43 _),
    function ActionValue#(Struct41) cache__000__infoRsValueRq(Bit#(64) _),
    function ActionValue#(Struct40) deq_fifoI2L_000(),
    function Action enq_fifoI2L_000(Struct40 _),
    function Action cache__000__infoRq(Bit#(64) _),
    function ActionValue#(Struct40) deq_fifoN2I_000(),
    function ActionValue#(Struct39) getCRqSlot_000(Struct38 _),
    function ActionValue#(Bool) victims__000__hasVictim(),
    function ActionValue#(Struct2) deq_fifoCRqInput_000(),
    function Action releaseMSHR_000(Bit#(3) _),
    function Action victims__000__releaseVictim(Bit#(64) _),
    function ActionValue#(Struct38) getWait_000(),
    function Action startRelease_000(Bit#(3) _),
    function ActionValue#(Bit#(3)) getULReady_000(Bit#(64) _),
    function Action enq_fifoN2I_000(Struct40 _),
    function ActionValue#(Struct10) victims__000__findVictim(Bit#(64) _),
    function ActionValue#(Struct39) getPRqSlot_000(Struct38 _),
    function ActionValue#(Struct2) deq_fifoPInput_000())
    (Module76);

    rule rule_in_prq_000;
        $display ("Rule fired: rule_in_prq_000 at %t", $time);
        let x_0 <- deq_fifoPInput_000();
        Bit#(3) x_1 = ((x_0).in_msg_from);
        when ((x_1) == ({((Bit#(2))'(2'h2)),((Bit#(1))'(1'h0))}),
        noAction);
        Struct1 x_2 = ((x_0).in_msg);
        when (! ((x_2).type_), noAction);
        let x_3 <- getPRqSlot_000(Struct38 {r_id : unpack(0), r_msg : x_2,
        r_msg_from : (x_0).in_msg_from});
        when ((x_3).s_has_slot,
        noAction);
        if (! ((x_3).s_conflict)) begin
            let x_4 <- victims__000__findVictim((x_2).addr);
            Struct40 x_5 = (Struct40 {ir_is_rs_rel : (Bool)'(False), ir_msg :
            (x_0).in_msg, ir_msg_from : x_1, ir_mshr_id : (x_3).s_id,
            ir_by_victim : x_4});
            let x_6 <- enq_fifoN2I_000(x_5);
        end else begin

        end
    endrule

    rule rule_in_prs_000;
        $display ("Rule fired: rule_in_prs_000 at %t", $time);
        let x_0 <- deq_fifoPInput_000();
        Bit#(3) x_1 = ((x_0).in_msg_from);
        when ((x_1) == ({((Bit#(2))'(2'h2)),((Bit#(1))'(1'h0))}),
        noAction);
        Struct1 x_2 = ((x_0).in_msg);
        when (((x_2).type_) && (! (((x_2).id) == ((Bit#(6))'(6'h16)))),
        noAction);
        let x_3 <- getULReady_000((x_2).addr);
        let x_4 <- startRelease_000(x_3);
        let x_5 <- victims__000__findVictim((x_2).addr);
        Struct40 x_6 = (Struct40 {ir_is_rs_rel : (Bool)'(False), ir_msg :
        (x_0).in_msg, ir_msg_from : x_1, ir_mshr_id : x_3, ir_by_victim :
        x_5});
        let x_7 <- enq_fifoN2I_000(x_6);
    endrule

    rule rule_in_retry_000;
        $display ("Rule fired: rule_in_retry_000 at %t", $time);
        let x_0 <- getWait_000();
        Struct1 x_1 = ((x_0).r_msg);
        let x_2 <- victims__000__findVictim((x_1).addr);
        Struct40 x_3 = (Struct40 {ir_is_rs_rel : (Bool)'(False), ir_msg :
        x_1, ir_msg_from : (x_0).r_msg_from, ir_mshr_id : (x_0).r_id,
        ir_by_victim : x_2});
        let x_4 <- enq_fifoN2I_000(x_3);
    endrule

    rule rule_in_invrs_000;
        $display ("Rule fired: rule_in_invrs_000 at %t", $time);
        let x_0 <- deq_fifoPInput_000();
        Bit#(3) x_1 = ((x_0).in_msg_from);
        when ((x_1) == ({((Bit#(2))'(2'h2)),((Bit#(1))'(1'h0))}),
        noAction);
        Struct1 x_2 = ((x_0).in_msg);
        when (((x_2).type_) && (((x_2).id) == ((Bit#(6))'(6'h16))),
        noAction);
        let x_3 <- getULReady_000((x_2).addr);
        let x_4 <- victims__000__releaseVictim((x_2).addr);
        let x_5 <- releaseMSHR_000(x_3);
    endrule

    rule rule_in_crq_000;
        $display ("Rule fired: rule_in_crq_000 at %t", $time);
        let x_0 <- deq_fifoCRqInput_000();
        Bit#(3) x_1 = ((x_0).in_msg_from);
        when (((x_1)[2:1]) == ((Bit#(2))'(2'h0)), noAction);
        Struct1 x_2 = ((x_0).in_msg);
        when (! ((x_2).type_), noAction);
        let x_3 <- victims__000__hasVictim();
        when (! (x_3), noAction);
        let x_4 <- getCRqSlot_000(Struct38 {r_id : unpack(0), r_msg : x_2,
        r_msg_from : x_1});
        when ((x_4).s_has_slot,
        noAction);
        if (! ((x_4).s_conflict)) begin
            let x_5 <- victims__000__findVictim((x_2).addr);
            Struct40 x_6 = (Struct40 {ir_is_rs_rel : (Bool)'(False), ir_msg :
            (x_0).in_msg, ir_msg_from : x_1, ir_mshr_id : (x_4).s_id,
            ir_by_victim : x_5});
            let x_7 <- enq_fifoN2I_000(x_6);
        end else begin

        end
    endrule

    rule rule_ir_cache_000;
        $display ("Rule fired: rule_ir_cache_000 at %t", $time);
        let x_0 <- deq_fifoN2I_000();
        when (! (((x_0).ir_by_victim).valid), noAction);
        Struct1 x_1 = ((x_0).ir_msg);
        let x_2 <- cache__000__infoRq((x_1).addr);
        let x_3 <- enq_fifoI2L_000(x_0);
    endrule

    rule rule_ir_victims_000;
        $display ("Rule fired: rule_ir_victims_000 at %t", $time);
        let x_0 <- deq_fifoN2I_000();
        when (((x_0).ir_by_victim).valid, noAction);
        let x_1 <- enq_fifoI2L_000(x_0);
    endrule

    rule rule_lr_cache_000;
        $display ("Rule fired: rule_lr_cache_000 at %t", $time);
        let x_0 <- deq_fifoI2L_000();
        when (! (((x_0).ir_by_victim).valid), noAction);
        let x_1 <- cache__000__infoRsValueRq(((x_0).ir_msg).addr);
        Struct43 x_2 = (Struct43 {lr_ir_pp : x_0, lr_ir : x_1, lr_value :
        unpack(0)});
        let x_3 <- enq_fifoL2E_000(x_2);
    endrule

    rule rule_lr_victims_000;
        $display ("Rule fired: rule_lr_victims_000 at %t", $time);
        let x_0 <- deq_fifoI2L_000();
        when (((x_0).ir_by_victim).valid, noAction);
        Bit#(2) x_1 = (((x_0).ir_by_victim).data);
        let x_2 <- victims__000__getVictim(x_1);
        Struct41 x_3 = (Struct41 {info_index : unpack(0), info_hit :
        unpack(0), info_way : unpack(0), edir_hit : unpack(0), edir_way :
        unpack(0), edir_slot : unpack(0), info : (x_2).victim_info,
        may_victim : unpack(0), reps : unpack(0)});
        Struct43 x_4 = (Struct43 {lr_ir_pp : x_0, lr_ir : x_3, lr_value :
        (x_2).victim_value});
        let x_5 <- enq_fifoL2E_000(x_4);
    endrule

    rule rule_exec_000_00;
        $display ("Rule fired: rule_exec_000_00 at %t", $time);
        let x_0 <- deq_fifoL2E_000();
        Struct40 x_1 = ((x_0).lr_ir_pp);
        Bit#(3) x_2 = ((x_1).ir_msg_from);
        Struct1 x_3 = ((x_1).ir_msg);
        Bit#(3) x_4 = ((x_1).ir_mshr_id);
        Bool x_5 = ((x_1).ir_is_rs_rel);
        when (! (x_5), noAction);
        Struct41 x_6 = ((x_0).lr_ir);
        Struct11 x_7 = ((x_6).info);
        Struct10 x_8 = ((x_1).ir_by_victim);
        Vector#(4, Bit#(64)) x_9 = ((x_0).lr_value);
        let x_10 <- getMSHR_000(x_4);
        let x_11 <- getMSHRRq_000(x_4);
        let x_12 <- getMSHRFirstRs_000(x_4);
        Vector#(4, Bit#(64)) x_13 = (unpack(0));
        Bool x_14 = ((x_7).mesi_owned);
        Bit#(3) x_15 = ((x_7).mesi_status);
        Struct17 x_16 = (Struct17 {dir_st : (((x_7).mesi_dir_st) ==
        ((Bit#(3))'(3'h0)) ? ((Bit#(3))'(3'h1)) : ((x_7).mesi_dir_st)),
        dir_excl : ((((x_7).mesi_dir_sharers)[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(1))'(1'h0)) : (((Bit#(1))'(1'h1)) +
        ((((((x_7).mesi_dir_sharers)[1:1])[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(1))'(1'h0)) : (((Bit#(1))'(1'h1)) + (unpack(0))))))),
        dir_sharers : (x_7).mesi_dir_sharers});
        when ((x_2) == ((Bit#(3))'(3'h0)), noAction);
        when (((x_3).id) == ((Bit#(6))'(6'h0)), noAction);
        when (! ((x_3).type_), noAction);
        when (! ((x_15) < ((Bit#(3))'(3'h2))), noAction);
        Struct1 x_17 = (x_3);
        Struct45 x_18 = (Struct45 {addr : (x_3).addr, info_write :
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
        Struct20 x_21 = (Struct20 {enq_type : ((((Bit#(3))'(3'h4))[2:1]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : (((((Bit#(3))'(3'h4))[2:1])
        == ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : ((Bit#(3))'(3'h4))[0:0], enq_msg : Struct1 {id :
        (Bit#(6))'(6'h1), type_ : (Bool)'(True), addr : (x_17).addr, value :
        x_20}});
        let x_22 <- makeEnq_parentChildren000(x_21);
        let x_23 <- releaseMSHR_000(x_4);
    endrule

    rule rule_exec_000_01;
        $display ("Rule fired: rule_exec_000_01 at %t", $time);
        let x_0 <- deq_fifoL2E_000();
        Struct40 x_1 = ((x_0).lr_ir_pp);
        Bit#(3) x_2 = ((x_1).ir_msg_from);
        Struct1 x_3 = ((x_1).ir_msg);
        Bit#(3) x_4 = ((x_1).ir_mshr_id);
        Bool x_5 = ((x_1).ir_is_rs_rel);
        when (! (x_5), noAction);
        Struct41 x_6 = ((x_0).lr_ir);
        Struct11 x_7 = ((x_6).info);
        Struct10 x_8 = ((x_1).ir_by_victim);
        Vector#(4, Bit#(64)) x_9 = ((x_0).lr_value);
        let x_10 <- getMSHR_000(x_4);
        let x_11 <- getMSHRRq_000(x_4);
        let x_12 <- getMSHRFirstRs_000(x_4);
        Vector#(4, Bit#(64)) x_13 = (unpack(0));
        Bool x_14 = ((x_7).mesi_owned);
        Bit#(3) x_15 = ((x_7).mesi_status);
        Struct17 x_16 = (Struct17 {dir_st : (((x_7).mesi_dir_st) ==
        ((Bit#(3))'(3'h0)) ? ((Bit#(3))'(3'h1)) : ((x_7).mesi_dir_st)),
        dir_excl : ((((x_7).mesi_dir_sharers)[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(1))'(1'h0)) : (((Bit#(1))'(1'h1)) +
        ((((((x_7).mesi_dir_sharers)[1:1])[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(1))'(1'h0)) : (((Bit#(1))'(1'h1)) + (unpack(0))))))),
        dir_sharers : (x_7).mesi_dir_sharers});
        when ((x_2) == ((Bit#(3))'(3'h0)), noAction);
        when (((x_3).id) == ((Bit#(6))'(6'h0)), noAction);
        when (! ((x_3).type_), noAction);
        when (! (((Bit#(3))'(3'h1)) < (x_15)), noAction);
        Struct1 x_17 = (x_3);
        Struct45 x_18 = (Struct45 {addr : (x_3).addr, info_write :
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
        let x_21 <- registerUL_000(Struct46 {r_id : x_4, r_ul_rsb :
        (Bool)'(True), r_ul_rsbTo : ((Bit#(3))'(3'h4))[0:0]});
        Struct20 x_22 = (Struct20 {enq_type : ((((Bit#(3))'(3'h0))[2:1]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : (((((Bit#(3))'(3'h0))[2:1])
        == ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : ((Bit#(3))'(3'h0))[0:0], enq_msg : Struct1 {id :
        (Bit#(6))'(6'h2), type_ : (Bool)'(False), addr : (x_17).addr, value :
        unpack(0)}});
        let x_23 <- makeEnq_parentChildren000(x_22);
    endrule

    rule rule_exec_000_020;
        $display ("Rule fired: rule_exec_000_020 at %t", $time);
        let x_0 <- deq_fifoL2E_000();
        Struct40 x_1 = ((x_0).lr_ir_pp);
        Bit#(3) x_2 = ((x_1).ir_msg_from);
        Struct1 x_3 = ((x_1).ir_msg);
        Bit#(3) x_4 = ((x_1).ir_mshr_id);
        Bool x_5 = ((x_1).ir_is_rs_rel);
        when (! (x_5), noAction);
        Struct41 x_6 = ((x_0).lr_ir);
        Struct11 x_7 = ((x_6).info);
        Struct10 x_8 = ((x_1).ir_by_victim);
        Vector#(4, Bit#(64)) x_9 = ((x_0).lr_value);
        let x_10 <- getMSHR_000(x_4);
        let x_11 <- getMSHRRq_000(x_4);
        let x_12 <- getMSHRFirstRs_000(x_4);
        Vector#(4, Bit#(64)) x_13 = (unpack(0));
        Bool x_14 = ((x_7).mesi_owned);
        Bit#(3) x_15 = ((x_7).mesi_status);
        Struct17 x_16 = (Struct17 {dir_st : (((x_7).mesi_dir_st) ==
        ((Bit#(3))'(3'h0)) ? ((Bit#(3))'(3'h1)) : ((x_7).mesi_dir_st)),
        dir_excl : ((((x_7).mesi_dir_sharers)[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(1))'(1'h0)) : (((Bit#(1))'(1'h1)) +
        ((((((x_7).mesi_dir_sharers)[1:1])[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(1))'(1'h0)) : (((Bit#(1))'(1'h1)) + (unpack(0))))))),
        dir_sharers : (x_7).mesi_dir_sharers});
        when ((x_2) == ({((Bit#(2))'(2'h2)),((Bit#(1))'(1'h0))}),
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
        Bit#(3) x_19 = ({((Bit#(2))'(2'h2)),(((x_10).m_qidx)[0:0])});
        Struct45 x_20 = (Struct45 {addr : (x_3).addr, info_write :
        (Bool)'(False), info_hit : (x_6).info_hit, info_way : (x_6).info_way,
        edir_hit : (x_6).edir_hit, edir_way : (x_6).edir_way, edir_slot :
        (x_6).edir_slot, info : (x_6).info, value_write : (Bool)'(False),
        value : unpack(0), may_victim : (x_6).may_victim, reps :
        (x_6).reps});
        Struct45 x_21 = (Struct45 {addr : (x_20).addr, info_write :
        (Bool)'(True), info_hit : (x_20).info_hit, info_way :
        (x_20).info_way, edir_hit : (x_20).edir_hit, edir_way :
        (x_20).edir_way, edir_slot : (x_20).edir_slot, info : Struct11
        {mesi_owned : ((x_20).info).mesi_owned, mesi_status :
        (Bit#(3))'(3'h2), mesi_dir_st : ((x_20).info).mesi_dir_st,
        mesi_dir_sharers : ((x_20).info).mesi_dir_sharers}, value_write :
        (x_20).value_write, value : (x_20).value, may_victim :
        (x_20).may_victim, reps : (x_20).reps});
        Struct45 x_22 = (Struct45 {addr : (x_21).addr, info_write :
        (x_21).info_write, info_hit : (x_21).info_hit, info_way :
        (x_21).info_way, edir_hit : (x_21).edir_hit, edir_way :
        (x_21).edir_way, edir_slot : (x_21).edir_slot, info : (x_21).info,
        value_write : (Bool)'(True), value : (x_17).value, may_victim :
        (x_21).may_victim, reps :
        (x_21).reps});
        let x_25 = ?;
        if ((x_8).valid) begin
            let x_23 <- victims__000__setVictim(Struct47 {victim_idx :
            (x_8).data, victim_info : (x_22).info, victim_value :
            ((x_22).value_write ? ((x_22).value) : (x_9))});
            x_25 = x_9;
        end else begin
            let x_24 <- cache__000__valueRsLineRq(x_22);
            x_25 = x_24;
        end
        let x_26 <- releaseMSHR_000(x_4);
        Struct20 x_27 = (Struct20 {enq_type : (((x_19)[2:1]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : ((((x_19)[2:1]) ==
        ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : (x_19)[0:0], enq_msg : Struct1 {id : (Bit#(6))'(6'h1),
        type_ : (Bool)'(True), addr : (x_17).addr, value :
        (x_17).value}});
        let x_28 <- makeEnq_parentChildren000(x_27);
    endrule

    rule rule_exec_000_021;
        $display ("Rule fired: rule_exec_000_021 at %t", $time);
        let x_0 <- deq_fifoL2E_000();
        Struct40 x_1 = ((x_0).lr_ir_pp);
        Bit#(3) x_2 = ((x_1).ir_msg_from);
        Struct1 x_3 = ((x_1).ir_msg);
        Bit#(3) x_4 = ((x_1).ir_mshr_id);
        Bool x_5 = ((x_1).ir_is_rs_rel);
        when (! (x_5), noAction);
        Struct41 x_6 = ((x_0).lr_ir);
        Struct11 x_7 = ((x_6).info);
        Struct10 x_8 = ((x_1).ir_by_victim);
        Vector#(4, Bit#(64)) x_9 = ((x_0).lr_value);
        let x_10 <- getMSHR_000(x_4);
        let x_11 <- getMSHRRq_000(x_4);
        let x_12 <- getMSHRFirstRs_000(x_4);
        Vector#(4, Bit#(64)) x_13 = (unpack(0));
        Bool x_14 = ((x_7).mesi_owned);
        Bit#(3) x_15 = ((x_7).mesi_status);
        Struct17 x_16 = (Struct17 {dir_st : (((x_7).mesi_dir_st) ==
        ((Bit#(3))'(3'h0)) ? ((Bit#(3))'(3'h1)) : ((x_7).mesi_dir_st)),
        dir_excl : ((((x_7).mesi_dir_sharers)[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(1))'(1'h0)) : (((Bit#(1))'(1'h1)) +
        ((((((x_7).mesi_dir_sharers)[1:1])[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(1))'(1'h0)) : (((Bit#(1))'(1'h1)) + (unpack(0))))))),
        dir_sharers : (x_7).mesi_dir_sharers});
        when ((x_2) == ({((Bit#(2))'(2'h2)),((Bit#(1))'(1'h0))}),
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
        Bit#(3) x_19 = ({((Bit#(2))'(2'h2)),(((x_10).m_qidx)[0:0])});
        Struct45 x_20 = (Struct45 {addr : (x_3).addr, info_write :
        (Bool)'(False), info_hit : (x_6).info_hit, info_way : (x_6).info_way,
        edir_hit : (x_6).edir_hit, edir_way : (x_6).edir_way, edir_slot :
        (x_6).edir_slot, info : (x_6).info, value_write : (Bool)'(False),
        value : unpack(0), may_victim : (x_6).may_victim, reps :
        (x_6).reps});
        Struct45 x_21 = (Struct45 {addr : (x_20).addr, info_write :
        (Bool)'(True), info_hit : (x_20).info_hit, info_way :
        (x_20).info_way, edir_hit : (x_20).edir_hit, edir_way :
        (x_20).edir_way, edir_slot : (x_20).edir_slot, info : Struct11
        {mesi_owned : ((x_20).info).mesi_owned, mesi_status :
        (Bit#(3))'(3'h3), mesi_dir_st : ((x_20).info).mesi_dir_st,
        mesi_dir_sharers : ((x_20).info).mesi_dir_sharers}, value_write :
        (x_20).value_write, value : (x_20).value, may_victim :
        (x_20).may_victim, reps : (x_20).reps});
        Struct45 x_22 = (Struct45 {addr : (x_21).addr, info_write :
        (x_21).info_write, info_hit : (x_21).info_hit, info_way :
        (x_21).info_way, edir_hit : (x_21).edir_hit, edir_way :
        (x_21).edir_way, edir_slot : (x_21).edir_slot, info : (x_21).info,
        value_write : (Bool)'(True), value : (x_17).value, may_victim :
        (x_21).may_victim, reps :
        (x_21).reps});
        let x_25 = ?;
        if ((x_8).valid) begin
            let x_23 <- victims__000__setVictim(Struct47 {victim_idx :
            (x_8).data, victim_info : (x_22).info, victim_value :
            ((x_22).value_write ? ((x_22).value) : (x_9))});
            x_25 = x_9;
        end else begin
            let x_24 <- cache__000__valueRsLineRq(x_22);
            x_25 = x_24;
        end
        let x_26 <- releaseMSHR_000(x_4);
        Struct20 x_27 = (Struct20 {enq_type : (((x_19)[2:1]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : ((((x_19)[2:1]) ==
        ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : (x_19)[0:0], enq_msg : Struct1 {id : (Bit#(6))'(6'h1),
        type_ : (Bool)'(True), addr : (x_17).addr, value :
        (x_17).value}});
        let x_28 <- makeEnq_parentChildren000(x_27);
    endrule

    rule rule_exec_000_03;
        $display ("Rule fired: rule_exec_000_03 at %t", $time);
        let x_0 <- deq_fifoL2E_000();
        Struct40 x_1 = ((x_0).lr_ir_pp);
        Bit#(3) x_2 = ((x_1).ir_msg_from);
        Struct1 x_3 = ((x_1).ir_msg);
        Bit#(3) x_4 = ((x_1).ir_mshr_id);
        Bool x_5 = ((x_1).ir_is_rs_rel);
        when (! (x_5), noAction);
        Struct41 x_6 = ((x_0).lr_ir);
        Struct11 x_7 = ((x_6).info);
        Struct10 x_8 = ((x_1).ir_by_victim);
        Vector#(4, Bit#(64)) x_9 = ((x_0).lr_value);
        let x_10 <- getMSHR_000(x_4);
        let x_11 <- getMSHRRq_000(x_4);
        let x_12 <- getMSHRFirstRs_000(x_4);
        Vector#(4, Bit#(64)) x_13 = (unpack(0));
        Bool x_14 = ((x_7).mesi_owned);
        Bit#(3) x_15 = ((x_7).mesi_status);
        Struct17 x_16 = (Struct17 {dir_st : (((x_7).mesi_dir_st) ==
        ((Bit#(3))'(3'h0)) ? ((Bit#(3))'(3'h1)) : ((x_7).mesi_dir_st)),
        dir_excl : ((((x_7).mesi_dir_sharers)[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(1))'(1'h0)) : (((Bit#(1))'(1'h1)) +
        ((((((x_7).mesi_dir_sharers)[1:1])[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(1))'(1'h0)) : (((Bit#(1))'(1'h1)) + (unpack(0))))))),
        dir_sharers : (x_7).mesi_dir_sharers});
        when ((x_2) == ((Bit#(3))'(3'h4)), noAction);
        when (((x_3).id) == ((Bit#(6))'(6'h5)), noAction);
        when (! ((x_3).type_), noAction);
        when (! ((x_15) < ((Bit#(3))'(3'h2))), noAction);
        Struct1 x_17 = (x_3);
        Struct45 x_18 = (Struct45 {addr : (x_3).addr, info_write :
        (Bool)'(False), info_hit : (x_6).info_hit, info_way : (x_6).info_way,
        edir_hit : (x_6).edir_hit, edir_way : (x_6).edir_way, edir_slot :
        (x_6).edir_slot, info : (x_6).info, value_write : (Bool)'(False),
        value : unpack(0), may_victim : (x_6).may_victim, reps :
        (x_6).reps});
        Struct45 x_19 = (Struct45 {addr : (x_18).addr, info_write :
        (Bool)'(True), info_hit : (x_18).info_hit, info_way :
        (x_18).info_way, edir_hit : (x_18).edir_hit, edir_way :
        (x_18).edir_way, edir_slot : (x_18).edir_slot, info : Struct11
        {mesi_owned : ((x_18).info).mesi_owned, mesi_status :
        (Bit#(3))'(3'h2), mesi_dir_st : ((x_18).info).mesi_dir_st,
        mesi_dir_sharers : ((x_18).info).mesi_dir_sharers}, value_write :
        (x_18).value_write, value : (x_18).value, may_victim :
        (x_18).may_victim, reps : (x_18).reps});
        Struct45 x_20 = (Struct45 {addr : (x_19).addr, info_write :
        (Bool)'(True), info_hit : (x_19).info_hit, info_way :
        (x_19).info_way, edir_hit : (x_19).edir_hit, edir_way :
        (x_19).edir_way, edir_slot : (x_19).edir_slot, info : Struct11
        {mesi_owned : (Bool)'(False), mesi_status :
        ((x_19).info).mesi_status, mesi_dir_st : ((x_19).info).mesi_dir_st,
        mesi_dir_sharers : ((x_19).info).mesi_dir_sharers}, value_write :
        (x_19).value_write, value : (x_19).value, may_victim :
        (x_19).may_victim, reps :
        (x_19).reps});
        let x_23 = ?;
        if ((x_8).valid) begin
            let x_21 <- victims__000__setVictim(Struct47 {victim_idx :
            (x_8).data, victim_info : (x_20).info, victim_value :
            ((x_20).value_write ? ((x_20).value) : (x_9))});
            x_23 = x_9;
        end else begin
            let x_22 <- cache__000__valueRsLineRq(x_20);
            x_23 = x_22;
        end
        Struct20 x_24 = (Struct20 {enq_type : ((((Bit#(3))'(3'h2))[2:1]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : (((((Bit#(3))'(3'h2))[2:1])
        == ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : ((Bit#(3))'(3'h2))[0:0], enq_msg : Struct1 {id :
        (Bit#(6))'(6'h6), type_ : (Bool)'(True), addr : (x_17).addr, value :
        x_23}});
        let x_25 <- makeEnq_parentChildren000(x_24);
        let x_26 <- releaseMSHR_000(x_4);
    endrule

    rule rule_exec_000_100;
        $display ("Rule fired: rule_exec_000_100 at %t", $time);
        let x_0 <- deq_fifoL2E_000();
        Struct40 x_1 = ((x_0).lr_ir_pp);
        Bit#(3) x_2 = ((x_1).ir_msg_from);
        Struct1 x_3 = ((x_1).ir_msg);
        Bit#(3) x_4 = ((x_1).ir_mshr_id);
        Bool x_5 = ((x_1).ir_is_rs_rel);
        when (! (x_5), noAction);
        Struct41 x_6 = ((x_0).lr_ir);
        Struct11 x_7 = ((x_6).info);
        Struct10 x_8 = ((x_1).ir_by_victim);
        Vector#(4, Bit#(64)) x_9 = ((x_0).lr_value);
        let x_10 <- getMSHR_000(x_4);
        let x_11 <- getMSHRRq_000(x_4);
        let x_12 <- getMSHRFirstRs_000(x_4);
        Vector#(4, Bit#(64)) x_13 = (unpack(0));
        Bool x_14 = ((x_7).mesi_owned);
        Bit#(3) x_15 = ((x_7).mesi_status);
        Struct17 x_16 = (Struct17 {dir_st : (((x_7).mesi_dir_st) ==
        ((Bit#(3))'(3'h0)) ? ((Bit#(3))'(3'h1)) : ((x_7).mesi_dir_st)),
        dir_excl : ((((x_7).mesi_dir_sharers)[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(1))'(1'h0)) : (((Bit#(1))'(1'h1)) +
        ((((((x_7).mesi_dir_sharers)[1:1])[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(1))'(1'h0)) : (((Bit#(1))'(1'h1)) + (unpack(0))))))),
        dir_sharers : (x_7).mesi_dir_sharers});
        when ((x_2) == ((Bit#(3))'(3'h0)), noAction);
        when (((x_3).id) == ((Bit#(6))'(6'h8)), noAction);
        when (! ((x_3).type_), noAction);
        when ((x_15) == ((Bit#(3))'(3'h3)), noAction);
        Struct1 x_17 = (x_3);
        Struct45 x_18 = (Struct45 {addr : (x_3).addr, info_write :
        (Bool)'(False), info_hit : (x_6).info_hit, info_way : (x_6).info_way,
        edir_hit : (x_6).edir_hit, edir_way : (x_6).edir_way, edir_slot :
        (x_6).edir_slot, info : (x_6).info, value_write : (Bool)'(False),
        value : unpack(0), may_victim : (x_6).may_victim, reps :
        (x_6).reps});
        Struct45 x_19 = (Struct45 {addr : (x_18).addr, info_write :
        (x_18).info_write, info_hit : (x_18).info_hit, info_way :
        (x_18).info_way, edir_hit : (x_18).edir_hit, edir_way :
        (x_18).edir_way, edir_slot : (x_18).edir_slot, info : (x_18).info,
        value_write : (Bool)'(True), value : (x_17).value, may_victim :
        (x_18).may_victim, reps : (x_18).reps});
        Struct45 x_20 = (Struct45 {addr : (x_19).addr, info_write :
        (Bool)'(True), info_hit : (x_19).info_hit, info_way :
        (x_19).info_way, edir_hit : (x_19).edir_hit, edir_way :
        (x_19).edir_way, edir_slot : (x_19).edir_slot, info : Struct11
        {mesi_owned : ((x_19).info).mesi_owned, mesi_status :
        (Bit#(3))'(3'h4), mesi_dir_st : ((x_19).info).mesi_dir_st,
        mesi_dir_sharers : ((x_19).info).mesi_dir_sharers}, value_write :
        (x_19).value_write, value : (x_19).value, may_victim :
        (x_19).may_victim, reps : (x_19).reps});
        Struct45 x_21 = (Struct45 {addr : (x_20).addr, info_write :
        (Bool)'(True), info_hit : (x_20).info_hit, info_way :
        (x_20).info_way, edir_hit : (x_20).edir_hit, edir_way :
        (x_20).edir_way, edir_slot : (x_20).edir_slot, info : Struct11
        {mesi_owned : (Bool)'(True), mesi_status : ((x_20).info).mesi_status,
        mesi_dir_st : ((x_20).info).mesi_dir_st, mesi_dir_sharers :
        ((x_20).info).mesi_dir_sharers}, value_write : (x_20).value_write,
        value : (x_20).value, may_victim : (x_20).may_victim, reps :
        (x_20).reps});
        let x_24 = ?;
        if ((x_8).valid) begin
            let x_22 <- victims__000__setVictim(Struct47 {victim_idx :
            (x_8).data, victim_info : (x_21).info, victim_value :
            ((x_21).value_write ? ((x_21).value) : (x_9))});
            x_24 = x_9;
        end else begin
            let x_23 <- cache__000__valueRsLineRq(x_21);
            x_24 = x_23;
        end
        Struct20 x_25 = (Struct20 {enq_type : ((((Bit#(3))'(3'h4))[2:1]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : (((((Bit#(3))'(3'h4))[2:1])
        == ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : ((Bit#(3))'(3'h4))[0:0], enq_msg : Struct1 {id :
        (Bit#(6))'(6'h9), type_ : (Bool)'(True), addr : (x_17).addr, value :
        unpack(0)}});
        let x_26 <- makeEnq_parentChildren000(x_25);
        let x_27 <- releaseMSHR_000(x_4);
    endrule

    rule rule_exec_000_101;
        $display ("Rule fired: rule_exec_000_101 at %t", $time);
        let x_0 <- deq_fifoL2E_000();
        Struct40 x_1 = ((x_0).lr_ir_pp);
        Bit#(3) x_2 = ((x_1).ir_msg_from);
        Struct1 x_3 = ((x_1).ir_msg);
        Bit#(3) x_4 = ((x_1).ir_mshr_id);
        Bool x_5 = ((x_1).ir_is_rs_rel);
        when (! (x_5), noAction);
        Struct41 x_6 = ((x_0).lr_ir);
        Struct11 x_7 = ((x_6).info);
        Struct10 x_8 = ((x_1).ir_by_victim);
        Vector#(4, Bit#(64)) x_9 = ((x_0).lr_value);
        let x_10 <- getMSHR_000(x_4);
        let x_11 <- getMSHRRq_000(x_4);
        let x_12 <- getMSHRFirstRs_000(x_4);
        Vector#(4, Bit#(64)) x_13 = (unpack(0));
        Bool x_14 = ((x_7).mesi_owned);
        Bit#(3) x_15 = ((x_7).mesi_status);
        Struct17 x_16 = (Struct17 {dir_st : (((x_7).mesi_dir_st) ==
        ((Bit#(3))'(3'h0)) ? ((Bit#(3))'(3'h1)) : ((x_7).mesi_dir_st)),
        dir_excl : ((((x_7).mesi_dir_sharers)[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(1))'(1'h0)) : (((Bit#(1))'(1'h1)) +
        ((((((x_7).mesi_dir_sharers)[1:1])[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(1))'(1'h0)) : (((Bit#(1))'(1'h1)) + (unpack(0))))))),
        dir_sharers : (x_7).mesi_dir_sharers});
        when ((x_2) == ((Bit#(3))'(3'h0)), noAction);
        when (((x_3).id) == ((Bit#(6))'(6'h8)), noAction);
        when (! ((x_3).type_), noAction);
        when (((x_14) == ((Bool)'(True))) && ((x_15) == ((Bit#(3))'(3'h4))),
        noAction);
        Struct1 x_17 = (x_3);
        Struct45 x_18 = (Struct45 {addr : (x_3).addr, info_write :
        (Bool)'(False), info_hit : (x_6).info_hit, info_way : (x_6).info_way,
        edir_hit : (x_6).edir_hit, edir_way : (x_6).edir_way, edir_slot :
        (x_6).edir_slot, info : (x_6).info, value_write : (Bool)'(False),
        value : unpack(0), may_victim : (x_6).may_victim, reps :
        (x_6).reps});
        Struct45 x_19 = (Struct45 {addr : (x_18).addr, info_write :
        (x_18).info_write, info_hit : (x_18).info_hit, info_way :
        (x_18).info_way, edir_hit : (x_18).edir_hit, edir_way :
        (x_18).edir_way, edir_slot : (x_18).edir_slot, info : (x_18).info,
        value_write : (Bool)'(True), value : (x_17).value, may_victim :
        (x_18).may_victim, reps :
        (x_18).reps});
        let x_22 = ?;
        if ((x_8).valid) begin
            let x_20 <- victims__000__setVictim(Struct47 {victim_idx :
            (x_8).data, victim_info : (x_19).info, victim_value :
            ((x_19).value_write ? ((x_19).value) : (x_9))});
            x_22 = x_9;
        end else begin
            let x_21 <- cache__000__valueRsLineRq(x_19);
            x_22 = x_21;
        end
        Struct20 x_23 = (Struct20 {enq_type : ((((Bit#(3))'(3'h4))[2:1]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : (((((Bit#(3))'(3'h4))[2:1])
        == ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : ((Bit#(3))'(3'h4))[0:0], enq_msg : Struct1 {id :
        (Bit#(6))'(6'h9), type_ : (Bool)'(True), addr : (x_17).addr, value :
        unpack(0)}});
        let x_24 <- makeEnq_parentChildren000(x_23);
        let x_25 <- releaseMSHR_000(x_4);
    endrule

    rule rule_exec_000_11;
        $display ("Rule fired: rule_exec_000_11 at %t", $time);
        let x_0 <- deq_fifoL2E_000();
        Struct40 x_1 = ((x_0).lr_ir_pp);
        Bit#(3) x_2 = ((x_1).ir_msg_from);
        Struct1 x_3 = ((x_1).ir_msg);
        Bit#(3) x_4 = ((x_1).ir_mshr_id);
        Bool x_5 = ((x_1).ir_is_rs_rel);
        when (! (x_5), noAction);
        Struct41 x_6 = ((x_0).lr_ir);
        Struct11 x_7 = ((x_6).info);
        Struct10 x_8 = ((x_1).ir_by_victim);
        Vector#(4, Bit#(64)) x_9 = ((x_0).lr_value);
        let x_10 <- getMSHR_000(x_4);
        let x_11 <- getMSHRRq_000(x_4);
        let x_12 <- getMSHRFirstRs_000(x_4);
        Vector#(4, Bit#(64)) x_13 = (unpack(0));
        Bool x_14 = ((x_7).mesi_owned);
        Bit#(3) x_15 = ((x_7).mesi_status);
        Struct17 x_16 = (Struct17 {dir_st : (((x_7).mesi_dir_st) ==
        ((Bit#(3))'(3'h0)) ? ((Bit#(3))'(3'h1)) : ((x_7).mesi_dir_st)),
        dir_excl : ((((x_7).mesi_dir_sharers)[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(1))'(1'h0)) : (((Bit#(1))'(1'h1)) +
        ((((((x_7).mesi_dir_sharers)[1:1])[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(1))'(1'h0)) : (((Bit#(1))'(1'h1)) + (unpack(0))))))),
        dir_sharers : (x_7).mesi_dir_sharers});
        when ((x_2) == ((Bit#(3))'(3'h0)), noAction);
        when (((x_3).id) == ((Bit#(6))'(6'h8)), noAction);
        when (! ((x_3).type_), noAction);
        when (! (((Bit#(3))'(3'h2)) < (x_15)), noAction);
        Struct1 x_17 = (x_3);
        Struct45 x_18 = (Struct45 {addr : (x_3).addr, info_write :
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
        let x_21 <- registerUL_000(Struct46 {r_id : x_4, r_ul_rsb :
        (Bool)'(True), r_ul_rsbTo : ((Bit#(3))'(3'h4))[0:0]});
        Struct20 x_22 = (Struct20 {enq_type : ((((Bit#(3))'(3'h0))[2:1]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : (((((Bit#(3))'(3'h0))[2:1])
        == ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : ((Bit#(3))'(3'h0))[0:0], enq_msg : Struct1 {id :
        (Bit#(6))'(6'ha), type_ : (Bool)'(False), addr : (x_17).addr, value :
        unpack(0)}});
        let x_23 <- makeEnq_parentChildren000(x_22);
    endrule

    rule rule_exec_000_12;
        $display ("Rule fired: rule_exec_000_12 at %t", $time);
        let x_0 <- deq_fifoL2E_000();
        Struct40 x_1 = ((x_0).lr_ir_pp);
        Bit#(3) x_2 = ((x_1).ir_msg_from);
        Struct1 x_3 = ((x_1).ir_msg);
        Bit#(3) x_4 = ((x_1).ir_mshr_id);
        Bool x_5 = ((x_1).ir_is_rs_rel);
        when (! (x_5), noAction);
        Struct41 x_6 = ((x_0).lr_ir);
        Struct11 x_7 = ((x_6).info);
        Struct10 x_8 = ((x_1).ir_by_victim);
        Vector#(4, Bit#(64)) x_9 = ((x_0).lr_value);
        let x_10 <- getMSHR_000(x_4);
        let x_11 <- getMSHRRq_000(x_4);
        let x_12 <- getMSHRFirstRs_000(x_4);
        Vector#(4, Bit#(64)) x_13 = (unpack(0));
        Bool x_14 = ((x_7).mesi_owned);
        Bit#(3) x_15 = ((x_7).mesi_status);
        Struct17 x_16 = (Struct17 {dir_st : (((x_7).mesi_dir_st) ==
        ((Bit#(3))'(3'h0)) ? ((Bit#(3))'(3'h1)) : ((x_7).mesi_dir_st)),
        dir_excl : ((((x_7).mesi_dir_sharers)[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(1))'(1'h0)) : (((Bit#(1))'(1'h1)) +
        ((((((x_7).mesi_dir_sharers)[1:1])[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(1))'(1'h0)) : (((Bit#(1))'(1'h1)) + (unpack(0))))))),
        dir_sharers : (x_7).mesi_dir_sharers});
        when ((x_2) == ({((Bit#(2))'(2'h2)),((Bit#(1))'(1'h0))}),
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
        Bit#(3) x_19 = ({((Bit#(2))'(2'h2)),(((x_10).m_qidx)[0:0])});
        Struct45 x_20 = (Struct45 {addr : (x_3).addr, info_write :
        (Bool)'(False), info_hit : (x_6).info_hit, info_way : (x_6).info_way,
        edir_hit : (x_6).edir_hit, edir_way : (x_6).edir_way, edir_slot :
        (x_6).edir_slot, info : (x_6).info, value_write : (Bool)'(False),
        value : unpack(0), may_victim : (x_6).may_victim, reps :
        (x_6).reps});
        Struct45 x_21 = (Struct45 {addr : (x_20).addr, info_write :
        (x_20).info_write, info_hit : (x_20).info_hit, info_way :
        (x_20).info_way, edir_hit : (x_20).edir_hit, edir_way :
        (x_20).edir_way, edir_slot : (x_20).edir_slot, info : (x_20).info,
        value_write : (Bool)'(True), value : (x_18).value, may_victim :
        (x_20).may_victim, reps : (x_20).reps});
        Struct45 x_22 = (Struct45 {addr : (x_21).addr, info_write :
        (Bool)'(True), info_hit : (x_21).info_hit, info_way :
        (x_21).info_way, edir_hit : (x_21).edir_hit, edir_way :
        (x_21).edir_way, edir_slot : (x_21).edir_slot, info : Struct11
        {mesi_owned : (Bool)'(True), mesi_status : ((x_21).info).mesi_status,
        mesi_dir_st : ((x_21).info).mesi_dir_st, mesi_dir_sharers :
        ((x_21).info).mesi_dir_sharers}, value_write : (x_21).value_write,
        value : (x_21).value, may_victim : (x_21).may_victim, reps :
        (x_21).reps});
        Struct45 x_23 = (Struct45 {addr : (x_22).addr, info_write :
        (Bool)'(True), info_hit : (x_22).info_hit, info_way :
        (x_22).info_way, edir_hit : (x_22).edir_hit, edir_way :
        (x_22).edir_way, edir_slot : (x_22).edir_slot, info : Struct11
        {mesi_owned : ((x_22).info).mesi_owned, mesi_status :
        (Bit#(3))'(3'h4), mesi_dir_st : ((x_22).info).mesi_dir_st,
        mesi_dir_sharers : ((x_22).info).mesi_dir_sharers}, value_write :
        (x_22).value_write, value : (x_22).value, may_victim :
        (x_22).may_victim, reps :
        (x_22).reps});
        let x_26 = ?;
        if ((x_8).valid) begin
            let x_24 <- victims__000__setVictim(Struct47 {victim_idx :
            (x_8).data, victim_info : (x_23).info, victim_value :
            ((x_23).value_write ? ((x_23).value) : (x_9))});
            x_26 = x_9;
        end else begin
            let x_25 <- cache__000__valueRsLineRq(x_23);
            x_26 = x_25;
        end
        let x_27 <- releaseMSHR_000(x_4);
        Struct20 x_28 = (Struct20 {enq_type : (((x_19)[2:1]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : ((((x_19)[2:1]) ==
        ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : (x_19)[0:0], enq_msg : Struct1 {id : (Bit#(6))'(6'h9),
        type_ : (Bool)'(True), addr : (x_17).addr, value : unpack(0)}});
        let x_29 <- makeEnq_parentChildren000(x_28);
    endrule

    rule rule_exec_000_130;
        $display ("Rule fired: rule_exec_000_130 at %t", $time);
        let x_0 <- deq_fifoL2E_000();
        Struct40 x_1 = ((x_0).lr_ir_pp);
        Bit#(3) x_2 = ((x_1).ir_msg_from);
        Struct1 x_3 = ((x_1).ir_msg);
        Bit#(3) x_4 = ((x_1).ir_mshr_id);
        Bool x_5 = ((x_1).ir_is_rs_rel);
        when (! (x_5), noAction);
        Struct41 x_6 = ((x_0).lr_ir);
        Struct11 x_7 = ((x_6).info);
        Struct10 x_8 = ((x_1).ir_by_victim);
        Vector#(4, Bit#(64)) x_9 = ((x_0).lr_value);
        let x_10 <- getMSHR_000(x_4);
        let x_11 <- getMSHRRq_000(x_4);
        let x_12 <- getMSHRFirstRs_000(x_4);
        Vector#(4, Bit#(64)) x_13 = (unpack(0));
        Bool x_14 = ((x_7).mesi_owned);
        Bit#(3) x_15 = ((x_7).mesi_status);
        Struct17 x_16 = (Struct17 {dir_st : (((x_7).mesi_dir_st) ==
        ((Bit#(3))'(3'h0)) ? ((Bit#(3))'(3'h1)) : ((x_7).mesi_dir_st)),
        dir_excl : ((((x_7).mesi_dir_sharers)[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(1))'(1'h0)) : (((Bit#(1))'(1'h1)) +
        ((((((x_7).mesi_dir_sharers)[1:1])[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(1))'(1'h0)) : (((Bit#(1))'(1'h1)) + (unpack(0))))))),
        dir_sharers : (x_7).mesi_dir_sharers});
        when ((x_2) == ((Bit#(3))'(3'h4)), noAction);
        when (((x_3).id) == ((Bit#(6))'(6'hc)), noAction);
        when (! ((x_3).type_), noAction);
        when ((Bool)'(True), noAction);
        Struct1 x_17 = (x_3);
        Struct45 x_18 = (Struct45 {addr : (x_3).addr, info_write :
        (Bool)'(False), info_hit : (x_6).info_hit, info_way : (x_6).info_way,
        edir_hit : (x_6).edir_hit, edir_way : (x_6).edir_way, edir_slot :
        (x_6).edir_slot, info : (x_6).info, value_write : (Bool)'(False),
        value : unpack(0), may_victim : (x_6).may_victim, reps :
        (x_6).reps});
        Struct45 x_19 = (Struct45 {addr : (x_18).addr, info_write :
        (Bool)'(True), info_hit : (x_18).info_hit, info_way :
        (x_18).info_way, edir_hit : (x_18).edir_hit, edir_way :
        (x_18).edir_way, edir_slot : (x_18).edir_slot, info : Struct11
        {mesi_owned : ((x_18).info).mesi_owned, mesi_status :
        (Bit#(3))'(3'h1), mesi_dir_st : ((x_18).info).mesi_dir_st,
        mesi_dir_sharers : ((x_18).info).mesi_dir_sharers}, value_write :
        (x_18).value_write, value : (x_18).value, may_victim :
        (x_18).may_victim, reps : (x_18).reps});
        Struct45 x_20 = (Struct45 {addr : (x_19).addr, info_write :
        (Bool)'(True), info_hit : (x_19).info_hit, info_way :
        (x_19).info_way, edir_hit : (x_19).edir_hit, edir_way :
        (x_19).edir_way, edir_slot : (x_19).edir_slot, info : Struct11
        {mesi_owned : (Bool)'(False), mesi_status :
        ((x_19).info).mesi_status, mesi_dir_st : ((x_19).info).mesi_dir_st,
        mesi_dir_sharers : ((x_19).info).mesi_dir_sharers}, value_write :
        (x_19).value_write, value : (x_19).value, may_victim :
        (x_19).may_victim, reps :
        (x_19).reps});
        let x_23 = ?;
        if ((x_8).valid) begin
            let x_21 <- victims__000__setVictim(Struct47 {victim_idx :
            (x_8).data, victim_info : (x_20).info, victim_value :
            ((x_20).value_write ? ((x_20).value) : (x_9))});
            x_23 = x_9;
        end else begin
            let x_22 <- cache__000__valueRsLineRq(x_20);
            x_23 = x_22;
        end
        Struct20 x_24 = (Struct20 {enq_type : ((((Bit#(3))'(3'h2))[2:1]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : (((((Bit#(3))'(3'h2))[2:1])
        == ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : ((Bit#(3))'(3'h2))[0:0], enq_msg : Struct1 {id :
        (Bit#(6))'(6'hd), type_ : (Bool)'(True), addr : (x_17).addr, value :
        unpack(0)}});
        let x_25 <- makeEnq_parentChildren000(x_24);
        let x_26 <- releaseMSHR_000(x_4);
    endrule

    rule rule_exec_000_131;
        $display ("Rule fired: rule_exec_000_131 at %t", $time);
        let x_0 <- deq_fifoL2E_000();
        Struct40 x_1 = ((x_0).lr_ir_pp);
        Bit#(3) x_2 = ((x_1).ir_msg_from);
        Struct1 x_3 = ((x_1).ir_msg);
        Bit#(3) x_4 = ((x_1).ir_mshr_id);
        Bool x_5 = ((x_1).ir_is_rs_rel);
        when (! (x_5), noAction);
        Struct41 x_6 = ((x_0).lr_ir);
        Struct11 x_7 = ((x_6).info);
        Struct10 x_8 = ((x_1).ir_by_victim);
        Vector#(4, Bit#(64)) x_9 = ((x_0).lr_value);
        let x_10 <- getMSHR_000(x_4);
        let x_11 <- getMSHRRq_000(x_4);
        let x_12 <- getMSHRFirstRs_000(x_4);
        Vector#(4, Bit#(64)) x_13 = (unpack(0));
        Bool x_14 = ((x_7).mesi_owned);
        Bit#(3) x_15 = ((x_7).mesi_status);
        Struct17 x_16 = (Struct17 {dir_st : (((x_7).mesi_dir_st) ==
        ((Bit#(3))'(3'h0)) ? ((Bit#(3))'(3'h1)) : ((x_7).mesi_dir_st)),
        dir_excl : ((((x_7).mesi_dir_sharers)[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(1))'(1'h0)) : (((Bit#(1))'(1'h1)) +
        ((((((x_7).mesi_dir_sharers)[1:1])[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(1))'(1'h0)) : (((Bit#(1))'(1'h1)) + (unpack(0))))))),
        dir_sharers : (x_7).mesi_dir_sharers});
        when ((x_2) == ((Bit#(3))'(3'h4)), noAction);
        when (((x_3).id) == ((Bit#(6))'(6'he)), noAction);
        when (! ((x_3).type_), noAction);
        when (! ((x_15) < ((Bit#(3))'(3'h3))), noAction);
        Struct1 x_17 = (x_3);
        Struct45 x_18 = (Struct45 {addr : (x_3).addr, info_write :
        (Bool)'(False), info_hit : (x_6).info_hit, info_way : (x_6).info_way,
        edir_hit : (x_6).edir_hit, edir_way : (x_6).edir_way, edir_slot :
        (x_6).edir_slot, info : (x_6).info, value_write : (Bool)'(False),
        value : unpack(0), may_victim : (x_6).may_victim, reps :
        (x_6).reps});
        Struct45 x_19 = (Struct45 {addr : (x_18).addr, info_write :
        (Bool)'(True), info_hit : (x_18).info_hit, info_way :
        (x_18).info_way, edir_hit : (x_18).edir_hit, edir_way :
        (x_18).edir_way, edir_slot : (x_18).edir_slot, info : Struct11
        {mesi_owned : ((x_18).info).mesi_owned, mesi_status :
        (Bit#(3))'(3'h1), mesi_dir_st : ((x_18).info).mesi_dir_st,
        mesi_dir_sharers : ((x_18).info).mesi_dir_sharers}, value_write :
        (x_18).value_write, value : (x_18).value, may_victim :
        (x_18).may_victim, reps : (x_18).reps});
        Struct45 x_20 = (Struct45 {addr : (x_19).addr, info_write :
        (Bool)'(True), info_hit : (x_19).info_hit, info_way :
        (x_19).info_way, edir_hit : (x_19).edir_hit, edir_way :
        (x_19).edir_way, edir_slot : (x_19).edir_slot, info : Struct11
        {mesi_owned : (Bool)'(False), mesi_status :
        ((x_19).info).mesi_status, mesi_dir_st : ((x_19).info).mesi_dir_st,
        mesi_dir_sharers : ((x_19).info).mesi_dir_sharers}, value_write :
        (x_19).value_write, value : (x_19).value, may_victim :
        (x_19).may_victim, reps :
        (x_19).reps});
        let x_23 = ?;
        if ((x_8).valid) begin
            let x_21 <- victims__000__setVictim(Struct47 {victim_idx :
            (x_8).data, victim_info : (x_20).info, victim_value :
            ((x_20).value_write ? ((x_20).value) : (x_9))});
            x_23 = x_9;
        end else begin
            let x_22 <- cache__000__valueRsLineRq(x_20);
            x_23 = x_22;
        end
        Struct20 x_24 = (Struct20 {enq_type : ((((Bit#(3))'(3'h2))[2:1]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : (((((Bit#(3))'(3'h2))[2:1])
        == ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : ((Bit#(3))'(3'h2))[0:0], enq_msg : Struct1 {id :
        (Bit#(6))'(6'hf), type_ : (Bool)'(True), addr : (x_17).addr, value :
        unpack(0)}});
        let x_25 <- makeEnq_parentChildren000(x_24);
        let x_26 <- releaseMSHR_000(x_4);
    endrule

    rule rule_exec_000_20;
        $display ("Rule fired: rule_exec_000_20 at %t", $time);
        let x_0 <- victims__000__getFirstVictim();
        Bit#(64) x_1 = ((x_0).victim_addr);
        Struct11 x_2 = ((x_0).victim_info);
        Vector#(4, Bit#(64)) x_3 = ((x_0).victim_value);
        Struct1 x_4 = (Struct1 {id : unpack(0), type_ : (Bool)'(False), addr
        : x_1, value : unpack(0)});
        Struct44 x_5 = (Struct44 {m_status : (Bit#(3))'(3'h5), m_next :
        unpack(0), m_is_ul : (Bool)'(True), m_addr : x_1, m_qidx : unpack(0),
        m_rsb : (Bool)'(False), m_dl_rss_from : unpack(0), m_dl_rss_recv :
        unpack(0)});
        Struct1 x_6 = (unpack(0));
        Struct1 x_7 = (unpack(0));
        Vector#(4, Bit#(64)) x_8 = (unpack(0));
        Bool x_9 = ((x_2).mesi_owned);
        Bit#(3) x_10 = ((x_2).mesi_status);
        Struct17 x_11 = (Struct17 {dir_st : (((x_2).mesi_dir_st) ==
        ((Bit#(3))'(3'h0)) ? ((Bit#(3))'(3'h1)) : ((x_2).mesi_dir_st)),
        dir_excl : ((((x_2).mesi_dir_sharers)[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(1))'(1'h0)) : (((Bit#(1))'(1'h1)) +
        ((((((x_2).mesi_dir_sharers)[1:1])[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(1))'(1'h0)) : (((Bit#(1))'(1'h1)) + (unpack(0))))))),
        dir_sharers : (x_2).mesi_dir_sharers});
        when (! ((x_4).type_), noAction);
        when (((x_9) == ((Bool)'(False))) && ((((Bit#(3))'(3'h0)) < (x_10))
        && ((x_10) < ((Bit#(3))'(3'h4)))), noAction);
        Struct20 x_12 = (Struct20 {enq_type : ((((Bit#(3))'(3'h0))[2:1]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : (((((Bit#(3))'(3'h0))[2:1])
        == ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : ((Bit#(3))'(3'h0))[0:0], enq_msg : Struct1 {id :
        (Bit#(6))'(6'h14), type_ : (Bool)'(False), addr : (x_4).addr, value :
        unpack(0)}});
        let x_13 <- makeEnq_parentChildren000(x_12);
        let x_14 <- setULImm_000(x_4);
        let x_15 <- victims__000__setVictimRq(x_1);
    endrule

    rule rule_exec_000_21;
        $display ("Rule fired: rule_exec_000_21 at %t", $time);
        let x_0 <- victims__000__getFirstVictim();
        Bit#(64) x_1 = ((x_0).victim_addr);
        Struct11 x_2 = ((x_0).victim_info);
        Vector#(4, Bit#(64)) x_3 = ((x_0).victim_value);
        Struct1 x_4 = (Struct1 {id : unpack(0), type_ : (Bool)'(False), addr
        : x_1, value : unpack(0)});
        Struct44 x_5 = (Struct44 {m_status : (Bit#(3))'(3'h5), m_next :
        unpack(0), m_is_ul : (Bool)'(True), m_addr : x_1, m_qidx : unpack(0),
        m_rsb : (Bool)'(False), m_dl_rss_from : unpack(0), m_dl_rss_recv :
        unpack(0)});
        Struct1 x_6 = (unpack(0));
        Struct1 x_7 = (unpack(0));
        Vector#(4, Bit#(64)) x_8 = (unpack(0));
        Bool x_9 = ((x_2).mesi_owned);
        Bit#(3) x_10 = ((x_2).mesi_status);
        Struct17 x_11 = (Struct17 {dir_st : (((x_2).mesi_dir_st) ==
        ((Bit#(3))'(3'h0)) ? ((Bit#(3))'(3'h1)) : ((x_2).mesi_dir_st)),
        dir_excl : ((((x_2).mesi_dir_sharers)[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(1))'(1'h0)) : (((Bit#(1))'(1'h1)) +
        ((((((x_2).mesi_dir_sharers)[1:1])[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(1))'(1'h0)) : (((Bit#(1))'(1'h1)) + (unpack(0))))))),
        dir_sharers : (x_2).mesi_dir_sharers});
        when (! ((x_4).type_), noAction);
        when (((Bit#(3))'(3'h0)) < (x_10), noAction);
        Struct20 x_12 = (Struct20 {enq_type : ((((Bit#(3))'(3'h0))[2:1]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : (((((Bit#(3))'(3'h0))[2:1])
        == ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : ((Bit#(3))'(3'h0))[0:0], enq_msg : Struct1 {id :
        (Bit#(6))'(6'h15), type_ : (Bool)'(False), addr : (x_4).addr, value :
        x_3}});
        let x_13 <- makeEnq_parentChildren000(x_12);
        let x_14 <- setULImm_000(x_4);
        let x_15 <- victims__000__setVictimRq(x_1);
    endrule

    // No methods in this module
endmodule

interface Module77;

endinterface

module mkModule77#(function Action victims__001__setVictimRq(Bit#(64) _),
    function Action setULImm_001(Struct1 _),
    function ActionValue#(Struct14) victims__001__getFirstVictim(),
    function Action victims__001__setVictim(Struct47 _),
    function Action registerUL_001(Struct46 _),
    function Action makeEnq_parentChildren001(Struct20 _),
    function ActionValue#(Vector#(4, Bit#(64))) cache__001__valueRsLineRq(Struct45 _),
    function ActionValue#(Struct1) getMSHRFirstRs_001(Bit#(3) _),
    function ActionValue#(Struct1) getMSHRRq_001(Bit#(3) _),
    function ActionValue#(Struct44) getMSHR_001(Bit#(3) _),
    function ActionValue#(Struct43) deq_fifoL2E_001(),
    function ActionValue#(Struct14) victims__001__getVictim(Bit#(2) _),
    function Action enq_fifoL2E_001(Struct43 _),
    function ActionValue#(Struct41) cache__001__infoRsValueRq(Bit#(64) _),
    function ActionValue#(Struct40) deq_fifoI2L_001(),
    function Action enq_fifoI2L_001(Struct40 _),
    function Action cache__001__infoRq(Bit#(64) _),
    function ActionValue#(Struct40) deq_fifoN2I_001(),
    function ActionValue#(Struct39) getCRqSlot_001(Struct38 _),
    function ActionValue#(Bool) victims__001__hasVictim(),
    function ActionValue#(Struct2) deq_fifoCRqInput_001(),
    function Action releaseMSHR_001(Bit#(3) _),
    function Action victims__001__releaseVictim(Bit#(64) _),
    function ActionValue#(Struct38) getWait_001(),
    function Action startRelease_001(Bit#(3) _),
    function ActionValue#(Bit#(3)) getULReady_001(Bit#(64) _),
    function Action enq_fifoN2I_001(Struct40 _),
    function ActionValue#(Struct10) victims__001__findVictim(Bit#(64) _),
    function ActionValue#(Struct39) getPRqSlot_001(Struct38 _),
    function ActionValue#(Struct2) deq_fifoPInput_001())
    (Module77);

    rule rule_in_prq_001;
        $display ("Rule fired: rule_in_prq_001 at %t", $time);
        let x_0 <- deq_fifoPInput_001();
        Bit#(3) x_1 = ((x_0).in_msg_from);
        when ((x_1) == ({((Bit#(2))'(2'h2)),((Bit#(1))'(1'h1))}),
        noAction);
        Struct1 x_2 = ((x_0).in_msg);
        when (! ((x_2).type_), noAction);
        let x_3 <- getPRqSlot_001(Struct38 {r_id : unpack(0), r_msg : x_2,
        r_msg_from : (x_0).in_msg_from});
        when ((x_3).s_has_slot,
        noAction);
        if (! ((x_3).s_conflict)) begin
            let x_4 <- victims__001__findVictim((x_2).addr);
            Struct40 x_5 = (Struct40 {ir_is_rs_rel : (Bool)'(False), ir_msg :
            (x_0).in_msg, ir_msg_from : x_1, ir_mshr_id : (x_3).s_id,
            ir_by_victim : x_4});
            let x_6 <- enq_fifoN2I_001(x_5);
        end else begin

        end
    endrule

    rule rule_in_prs_001;
        $display ("Rule fired: rule_in_prs_001 at %t", $time);
        let x_0 <- deq_fifoPInput_001();
        Bit#(3) x_1 = ((x_0).in_msg_from);
        when ((x_1) == ({((Bit#(2))'(2'h2)),((Bit#(1))'(1'h1))}),
        noAction);
        Struct1 x_2 = ((x_0).in_msg);
        when (((x_2).type_) && (! (((x_2).id) == ((Bit#(6))'(6'h16)))),
        noAction);
        let x_3 <- getULReady_001((x_2).addr);
        let x_4 <- startRelease_001(x_3);
        let x_5 <- victims__001__findVictim((x_2).addr);
        Struct40 x_6 = (Struct40 {ir_is_rs_rel : (Bool)'(False), ir_msg :
        (x_0).in_msg, ir_msg_from : x_1, ir_mshr_id : x_3, ir_by_victim :
        x_5});
        let x_7 <- enq_fifoN2I_001(x_6);
    endrule

    rule rule_in_retry_001;
        $display ("Rule fired: rule_in_retry_001 at %t", $time);
        let x_0 <- getWait_001();
        Struct1 x_1 = ((x_0).r_msg);
        let x_2 <- victims__001__findVictim((x_1).addr);
        Struct40 x_3 = (Struct40 {ir_is_rs_rel : (Bool)'(False), ir_msg :
        x_1, ir_msg_from : (x_0).r_msg_from, ir_mshr_id : (x_0).r_id,
        ir_by_victim : x_2});
        let x_4 <- enq_fifoN2I_001(x_3);
    endrule

    rule rule_in_invrs_001;
        $display ("Rule fired: rule_in_invrs_001 at %t", $time);
        let x_0 <- deq_fifoPInput_001();
        Bit#(3) x_1 = ((x_0).in_msg_from);
        when ((x_1) == ({((Bit#(2))'(2'h2)),((Bit#(1))'(1'h1))}),
        noAction);
        Struct1 x_2 = ((x_0).in_msg);
        when (((x_2).type_) && (((x_2).id) == ((Bit#(6))'(6'h16))),
        noAction);
        let x_3 <- getULReady_001((x_2).addr);
        let x_4 <- victims__001__releaseVictim((x_2).addr);
        let x_5 <- releaseMSHR_001(x_3);
    endrule

    rule rule_in_crq_001;
        $display ("Rule fired: rule_in_crq_001 at %t", $time);
        let x_0 <- deq_fifoCRqInput_001();
        Bit#(3) x_1 = ((x_0).in_msg_from);
        when (((x_1)[2:1]) == ((Bit#(2))'(2'h0)), noAction);
        Struct1 x_2 = ((x_0).in_msg);
        when (! ((x_2).type_), noAction);
        let x_3 <- victims__001__hasVictim();
        when (! (x_3), noAction);
        let x_4 <- getCRqSlot_001(Struct38 {r_id : unpack(0), r_msg : x_2,
        r_msg_from : x_1});
        when ((x_4).s_has_slot,
        noAction);
        if (! ((x_4).s_conflict)) begin
            let x_5 <- victims__001__findVictim((x_2).addr);
            Struct40 x_6 = (Struct40 {ir_is_rs_rel : (Bool)'(False), ir_msg :
            (x_0).in_msg, ir_msg_from : x_1, ir_mshr_id : (x_4).s_id,
            ir_by_victim : x_5});
            let x_7 <- enq_fifoN2I_001(x_6);
        end else begin

        end
    endrule

    rule rule_ir_cache_001;
        $display ("Rule fired: rule_ir_cache_001 at %t", $time);
        let x_0 <- deq_fifoN2I_001();
        when (! (((x_0).ir_by_victim).valid), noAction);
        Struct1 x_1 = ((x_0).ir_msg);
        let x_2 <- cache__001__infoRq((x_1).addr);
        let x_3 <- enq_fifoI2L_001(x_0);
    endrule

    rule rule_ir_victims_001;
        $display ("Rule fired: rule_ir_victims_001 at %t", $time);
        let x_0 <- deq_fifoN2I_001();
        when (((x_0).ir_by_victim).valid, noAction);
        let x_1 <- enq_fifoI2L_001(x_0);
    endrule

    rule rule_lr_cache_001;
        $display ("Rule fired: rule_lr_cache_001 at %t", $time);
        let x_0 <- deq_fifoI2L_001();
        when (! (((x_0).ir_by_victim).valid), noAction);
        let x_1 <- cache__001__infoRsValueRq(((x_0).ir_msg).addr);
        Struct43 x_2 = (Struct43 {lr_ir_pp : x_0, lr_ir : x_1, lr_value :
        unpack(0)});
        let x_3 <- enq_fifoL2E_001(x_2);
    endrule

    rule rule_lr_victims_001;
        $display ("Rule fired: rule_lr_victims_001 at %t", $time);
        let x_0 <- deq_fifoI2L_001();
        when (((x_0).ir_by_victim).valid, noAction);
        Bit#(2) x_1 = (((x_0).ir_by_victim).data);
        let x_2 <- victims__001__getVictim(x_1);
        Struct41 x_3 = (Struct41 {info_index : unpack(0), info_hit :
        unpack(0), info_way : unpack(0), edir_hit : unpack(0), edir_way :
        unpack(0), edir_slot : unpack(0), info : (x_2).victim_info,
        may_victim : unpack(0), reps : unpack(0)});
        Struct43 x_4 = (Struct43 {lr_ir_pp : x_0, lr_ir : x_3, lr_value :
        (x_2).victim_value});
        let x_5 <- enq_fifoL2E_001(x_4);
    endrule

    rule rule_exec_001_00;
        $display ("Rule fired: rule_exec_001_00 at %t", $time);
        let x_0 <- deq_fifoL2E_001();
        Struct40 x_1 = ((x_0).lr_ir_pp);
        Bit#(3) x_2 = ((x_1).ir_msg_from);
        Struct1 x_3 = ((x_1).ir_msg);
        Bit#(3) x_4 = ((x_1).ir_mshr_id);
        Bool x_5 = ((x_1).ir_is_rs_rel);
        when (! (x_5), noAction);
        Struct41 x_6 = ((x_0).lr_ir);
        Struct11 x_7 = ((x_6).info);
        Struct10 x_8 = ((x_1).ir_by_victim);
        Vector#(4, Bit#(64)) x_9 = ((x_0).lr_value);
        let x_10 <- getMSHR_001(x_4);
        let x_11 <- getMSHRRq_001(x_4);
        let x_12 <- getMSHRFirstRs_001(x_4);
        Vector#(4, Bit#(64)) x_13 = (unpack(0));
        Bool x_14 = ((x_7).mesi_owned);
        Bit#(3) x_15 = ((x_7).mesi_status);
        Struct17 x_16 = (Struct17 {dir_st : (((x_7).mesi_dir_st) ==
        ((Bit#(3))'(3'h0)) ? ((Bit#(3))'(3'h1)) : ((x_7).mesi_dir_st)),
        dir_excl : ((((x_7).mesi_dir_sharers)[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(1))'(1'h0)) : (((Bit#(1))'(1'h1)) +
        ((((((x_7).mesi_dir_sharers)[1:1])[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(1))'(1'h0)) : (((Bit#(1))'(1'h1)) + (unpack(0))))))),
        dir_sharers : (x_7).mesi_dir_sharers});
        when ((x_2) == ((Bit#(3))'(3'h0)), noAction);
        when (((x_3).id) == ((Bit#(6))'(6'h0)), noAction);
        when (! ((x_3).type_), noAction);
        when (! ((x_15) < ((Bit#(3))'(3'h2))), noAction);
        Struct1 x_17 = (x_3);
        Struct45 x_18 = (Struct45 {addr : (x_3).addr, info_write :
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
        Struct20 x_21 = (Struct20 {enq_type : ((((Bit#(3))'(3'h4))[2:1]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : (((((Bit#(3))'(3'h4))[2:1])
        == ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : ((Bit#(3))'(3'h4))[0:0], enq_msg : Struct1 {id :
        (Bit#(6))'(6'h1), type_ : (Bool)'(True), addr : (x_17).addr, value :
        x_20}});
        let x_22 <- makeEnq_parentChildren001(x_21);
        let x_23 <- releaseMSHR_001(x_4);
    endrule

    rule rule_exec_001_01;
        $display ("Rule fired: rule_exec_001_01 at %t", $time);
        let x_0 <- deq_fifoL2E_001();
        Struct40 x_1 = ((x_0).lr_ir_pp);
        Bit#(3) x_2 = ((x_1).ir_msg_from);
        Struct1 x_3 = ((x_1).ir_msg);
        Bit#(3) x_4 = ((x_1).ir_mshr_id);
        Bool x_5 = ((x_1).ir_is_rs_rel);
        when (! (x_5), noAction);
        Struct41 x_6 = ((x_0).lr_ir);
        Struct11 x_7 = ((x_6).info);
        Struct10 x_8 = ((x_1).ir_by_victim);
        Vector#(4, Bit#(64)) x_9 = ((x_0).lr_value);
        let x_10 <- getMSHR_001(x_4);
        let x_11 <- getMSHRRq_001(x_4);
        let x_12 <- getMSHRFirstRs_001(x_4);
        Vector#(4, Bit#(64)) x_13 = (unpack(0));
        Bool x_14 = ((x_7).mesi_owned);
        Bit#(3) x_15 = ((x_7).mesi_status);
        Struct17 x_16 = (Struct17 {dir_st : (((x_7).mesi_dir_st) ==
        ((Bit#(3))'(3'h0)) ? ((Bit#(3))'(3'h1)) : ((x_7).mesi_dir_st)),
        dir_excl : ((((x_7).mesi_dir_sharers)[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(1))'(1'h0)) : (((Bit#(1))'(1'h1)) +
        ((((((x_7).mesi_dir_sharers)[1:1])[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(1))'(1'h0)) : (((Bit#(1))'(1'h1)) + (unpack(0))))))),
        dir_sharers : (x_7).mesi_dir_sharers});
        when ((x_2) == ((Bit#(3))'(3'h0)), noAction);
        when (((x_3).id) == ((Bit#(6))'(6'h0)), noAction);
        when (! ((x_3).type_), noAction);
        when (! (((Bit#(3))'(3'h1)) < (x_15)), noAction);
        Struct1 x_17 = (x_3);
        Struct45 x_18 = (Struct45 {addr : (x_3).addr, info_write :
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
        let x_21 <- registerUL_001(Struct46 {r_id : x_4, r_ul_rsb :
        (Bool)'(True), r_ul_rsbTo : ((Bit#(3))'(3'h4))[0:0]});
        Struct20 x_22 = (Struct20 {enq_type : ((((Bit#(3))'(3'h1))[2:1]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : (((((Bit#(3))'(3'h1))[2:1])
        == ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : ((Bit#(3))'(3'h1))[0:0], enq_msg : Struct1 {id :
        (Bit#(6))'(6'h2), type_ : (Bool)'(False), addr : (x_17).addr, value :
        unpack(0)}});
        let x_23 <- makeEnq_parentChildren001(x_22);
    endrule

    rule rule_exec_001_020;
        $display ("Rule fired: rule_exec_001_020 at %t", $time);
        let x_0 <- deq_fifoL2E_001();
        Struct40 x_1 = ((x_0).lr_ir_pp);
        Bit#(3) x_2 = ((x_1).ir_msg_from);
        Struct1 x_3 = ((x_1).ir_msg);
        Bit#(3) x_4 = ((x_1).ir_mshr_id);
        Bool x_5 = ((x_1).ir_is_rs_rel);
        when (! (x_5), noAction);
        Struct41 x_6 = ((x_0).lr_ir);
        Struct11 x_7 = ((x_6).info);
        Struct10 x_8 = ((x_1).ir_by_victim);
        Vector#(4, Bit#(64)) x_9 = ((x_0).lr_value);
        let x_10 <- getMSHR_001(x_4);
        let x_11 <- getMSHRRq_001(x_4);
        let x_12 <- getMSHRFirstRs_001(x_4);
        Vector#(4, Bit#(64)) x_13 = (unpack(0));
        Bool x_14 = ((x_7).mesi_owned);
        Bit#(3) x_15 = ((x_7).mesi_status);
        Struct17 x_16 = (Struct17 {dir_st : (((x_7).mesi_dir_st) ==
        ((Bit#(3))'(3'h0)) ? ((Bit#(3))'(3'h1)) : ((x_7).mesi_dir_st)),
        dir_excl : ((((x_7).mesi_dir_sharers)[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(1))'(1'h0)) : (((Bit#(1))'(1'h1)) +
        ((((((x_7).mesi_dir_sharers)[1:1])[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(1))'(1'h0)) : (((Bit#(1))'(1'h1)) + (unpack(0))))))),
        dir_sharers : (x_7).mesi_dir_sharers});
        when ((x_2) == ({((Bit#(2))'(2'h2)),((Bit#(1))'(1'h1))}),
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
        Bit#(3) x_19 = ({((Bit#(2))'(2'h2)),(((x_10).m_qidx)[0:0])});
        Struct45 x_20 = (Struct45 {addr : (x_3).addr, info_write :
        (Bool)'(False), info_hit : (x_6).info_hit, info_way : (x_6).info_way,
        edir_hit : (x_6).edir_hit, edir_way : (x_6).edir_way, edir_slot :
        (x_6).edir_slot, info : (x_6).info, value_write : (Bool)'(False),
        value : unpack(0), may_victim : (x_6).may_victim, reps :
        (x_6).reps});
        Struct45 x_21 = (Struct45 {addr : (x_20).addr, info_write :
        (Bool)'(True), info_hit : (x_20).info_hit, info_way :
        (x_20).info_way, edir_hit : (x_20).edir_hit, edir_way :
        (x_20).edir_way, edir_slot : (x_20).edir_slot, info : Struct11
        {mesi_owned : ((x_20).info).mesi_owned, mesi_status :
        (Bit#(3))'(3'h2), mesi_dir_st : ((x_20).info).mesi_dir_st,
        mesi_dir_sharers : ((x_20).info).mesi_dir_sharers}, value_write :
        (x_20).value_write, value : (x_20).value, may_victim :
        (x_20).may_victim, reps : (x_20).reps});
        Struct45 x_22 = (Struct45 {addr : (x_21).addr, info_write :
        (x_21).info_write, info_hit : (x_21).info_hit, info_way :
        (x_21).info_way, edir_hit : (x_21).edir_hit, edir_way :
        (x_21).edir_way, edir_slot : (x_21).edir_slot, info : (x_21).info,
        value_write : (Bool)'(True), value : (x_17).value, may_victim :
        (x_21).may_victim, reps :
        (x_21).reps});
        let x_25 = ?;
        if ((x_8).valid) begin
            let x_23 <- victims__001__setVictim(Struct47 {victim_idx :
            (x_8).data, victim_info : (x_22).info, victim_value :
            ((x_22).value_write ? ((x_22).value) : (x_9))});
            x_25 = x_9;
        end else begin
            let x_24 <- cache__001__valueRsLineRq(x_22);
            x_25 = x_24;
        end
        let x_26 <- releaseMSHR_001(x_4);
        Struct20 x_27 = (Struct20 {enq_type : (((x_19)[2:1]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : ((((x_19)[2:1]) ==
        ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : (x_19)[0:0], enq_msg : Struct1 {id : (Bit#(6))'(6'h1),
        type_ : (Bool)'(True), addr : (x_17).addr, value :
        (x_17).value}});
        let x_28 <- makeEnq_parentChildren001(x_27);
    endrule

    rule rule_exec_001_021;
        $display ("Rule fired: rule_exec_001_021 at %t", $time);
        let x_0 <- deq_fifoL2E_001();
        Struct40 x_1 = ((x_0).lr_ir_pp);
        Bit#(3) x_2 = ((x_1).ir_msg_from);
        Struct1 x_3 = ((x_1).ir_msg);
        Bit#(3) x_4 = ((x_1).ir_mshr_id);
        Bool x_5 = ((x_1).ir_is_rs_rel);
        when (! (x_5), noAction);
        Struct41 x_6 = ((x_0).lr_ir);
        Struct11 x_7 = ((x_6).info);
        Struct10 x_8 = ((x_1).ir_by_victim);
        Vector#(4, Bit#(64)) x_9 = ((x_0).lr_value);
        let x_10 <- getMSHR_001(x_4);
        let x_11 <- getMSHRRq_001(x_4);
        let x_12 <- getMSHRFirstRs_001(x_4);
        Vector#(4, Bit#(64)) x_13 = (unpack(0));
        Bool x_14 = ((x_7).mesi_owned);
        Bit#(3) x_15 = ((x_7).mesi_status);
        Struct17 x_16 = (Struct17 {dir_st : (((x_7).mesi_dir_st) ==
        ((Bit#(3))'(3'h0)) ? ((Bit#(3))'(3'h1)) : ((x_7).mesi_dir_st)),
        dir_excl : ((((x_7).mesi_dir_sharers)[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(1))'(1'h0)) : (((Bit#(1))'(1'h1)) +
        ((((((x_7).mesi_dir_sharers)[1:1])[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(1))'(1'h0)) : (((Bit#(1))'(1'h1)) + (unpack(0))))))),
        dir_sharers : (x_7).mesi_dir_sharers});
        when ((x_2) == ({((Bit#(2))'(2'h2)),((Bit#(1))'(1'h1))}),
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
        Bit#(3) x_19 = ({((Bit#(2))'(2'h2)),(((x_10).m_qidx)[0:0])});
        Struct45 x_20 = (Struct45 {addr : (x_3).addr, info_write :
        (Bool)'(False), info_hit : (x_6).info_hit, info_way : (x_6).info_way,
        edir_hit : (x_6).edir_hit, edir_way : (x_6).edir_way, edir_slot :
        (x_6).edir_slot, info : (x_6).info, value_write : (Bool)'(False),
        value : unpack(0), may_victim : (x_6).may_victim, reps :
        (x_6).reps});
        Struct45 x_21 = (Struct45 {addr : (x_20).addr, info_write :
        (Bool)'(True), info_hit : (x_20).info_hit, info_way :
        (x_20).info_way, edir_hit : (x_20).edir_hit, edir_way :
        (x_20).edir_way, edir_slot : (x_20).edir_slot, info : Struct11
        {mesi_owned : ((x_20).info).mesi_owned, mesi_status :
        (Bit#(3))'(3'h3), mesi_dir_st : ((x_20).info).mesi_dir_st,
        mesi_dir_sharers : ((x_20).info).mesi_dir_sharers}, value_write :
        (x_20).value_write, value : (x_20).value, may_victim :
        (x_20).may_victim, reps : (x_20).reps});
        Struct45 x_22 = (Struct45 {addr : (x_21).addr, info_write :
        (x_21).info_write, info_hit : (x_21).info_hit, info_way :
        (x_21).info_way, edir_hit : (x_21).edir_hit, edir_way :
        (x_21).edir_way, edir_slot : (x_21).edir_slot, info : (x_21).info,
        value_write : (Bool)'(True), value : (x_17).value, may_victim :
        (x_21).may_victim, reps :
        (x_21).reps});
        let x_25 = ?;
        if ((x_8).valid) begin
            let x_23 <- victims__001__setVictim(Struct47 {victim_idx :
            (x_8).data, victim_info : (x_22).info, victim_value :
            ((x_22).value_write ? ((x_22).value) : (x_9))});
            x_25 = x_9;
        end else begin
            let x_24 <- cache__001__valueRsLineRq(x_22);
            x_25 = x_24;
        end
        let x_26 <- releaseMSHR_001(x_4);
        Struct20 x_27 = (Struct20 {enq_type : (((x_19)[2:1]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : ((((x_19)[2:1]) ==
        ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : (x_19)[0:0], enq_msg : Struct1 {id : (Bit#(6))'(6'h1),
        type_ : (Bool)'(True), addr : (x_17).addr, value :
        (x_17).value}});
        let x_28 <- makeEnq_parentChildren001(x_27);
    endrule

    rule rule_exec_001_03;
        $display ("Rule fired: rule_exec_001_03 at %t", $time);
        let x_0 <- deq_fifoL2E_001();
        Struct40 x_1 = ((x_0).lr_ir_pp);
        Bit#(3) x_2 = ((x_1).ir_msg_from);
        Struct1 x_3 = ((x_1).ir_msg);
        Bit#(3) x_4 = ((x_1).ir_mshr_id);
        Bool x_5 = ((x_1).ir_is_rs_rel);
        when (! (x_5), noAction);
        Struct41 x_6 = ((x_0).lr_ir);
        Struct11 x_7 = ((x_6).info);
        Struct10 x_8 = ((x_1).ir_by_victim);
        Vector#(4, Bit#(64)) x_9 = ((x_0).lr_value);
        let x_10 <- getMSHR_001(x_4);
        let x_11 <- getMSHRRq_001(x_4);
        let x_12 <- getMSHRFirstRs_001(x_4);
        Vector#(4, Bit#(64)) x_13 = (unpack(0));
        Bool x_14 = ((x_7).mesi_owned);
        Bit#(3) x_15 = ((x_7).mesi_status);
        Struct17 x_16 = (Struct17 {dir_st : (((x_7).mesi_dir_st) ==
        ((Bit#(3))'(3'h0)) ? ((Bit#(3))'(3'h1)) : ((x_7).mesi_dir_st)),
        dir_excl : ((((x_7).mesi_dir_sharers)[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(1))'(1'h0)) : (((Bit#(1))'(1'h1)) +
        ((((((x_7).mesi_dir_sharers)[1:1])[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(1))'(1'h0)) : (((Bit#(1))'(1'h1)) + (unpack(0))))))),
        dir_sharers : (x_7).mesi_dir_sharers});
        when ((x_2) == ((Bit#(3))'(3'h5)), noAction);
        when (((x_3).id) == ((Bit#(6))'(6'h5)), noAction);
        when (! ((x_3).type_), noAction);
        when (! ((x_15) < ((Bit#(3))'(3'h2))), noAction);
        Struct1 x_17 = (x_3);
        Struct45 x_18 = (Struct45 {addr : (x_3).addr, info_write :
        (Bool)'(False), info_hit : (x_6).info_hit, info_way : (x_6).info_way,
        edir_hit : (x_6).edir_hit, edir_way : (x_6).edir_way, edir_slot :
        (x_6).edir_slot, info : (x_6).info, value_write : (Bool)'(False),
        value : unpack(0), may_victim : (x_6).may_victim, reps :
        (x_6).reps});
        Struct45 x_19 = (Struct45 {addr : (x_18).addr, info_write :
        (Bool)'(True), info_hit : (x_18).info_hit, info_way :
        (x_18).info_way, edir_hit : (x_18).edir_hit, edir_way :
        (x_18).edir_way, edir_slot : (x_18).edir_slot, info : Struct11
        {mesi_owned : ((x_18).info).mesi_owned, mesi_status :
        (Bit#(3))'(3'h2), mesi_dir_st : ((x_18).info).mesi_dir_st,
        mesi_dir_sharers : ((x_18).info).mesi_dir_sharers}, value_write :
        (x_18).value_write, value : (x_18).value, may_victim :
        (x_18).may_victim, reps : (x_18).reps});
        Struct45 x_20 = (Struct45 {addr : (x_19).addr, info_write :
        (Bool)'(True), info_hit : (x_19).info_hit, info_way :
        (x_19).info_way, edir_hit : (x_19).edir_hit, edir_way :
        (x_19).edir_way, edir_slot : (x_19).edir_slot, info : Struct11
        {mesi_owned : (Bool)'(False), mesi_status :
        ((x_19).info).mesi_status, mesi_dir_st : ((x_19).info).mesi_dir_st,
        mesi_dir_sharers : ((x_19).info).mesi_dir_sharers}, value_write :
        (x_19).value_write, value : (x_19).value, may_victim :
        (x_19).may_victim, reps :
        (x_19).reps});
        let x_23 = ?;
        if ((x_8).valid) begin
            let x_21 <- victims__001__setVictim(Struct47 {victim_idx :
            (x_8).data, victim_info : (x_20).info, victim_value :
            ((x_20).value_write ? ((x_20).value) : (x_9))});
            x_23 = x_9;
        end else begin
            let x_22 <- cache__001__valueRsLineRq(x_20);
            x_23 = x_22;
        end
        Struct20 x_24 = (Struct20 {enq_type : ((((Bit#(3))'(3'h3))[2:1]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : (((((Bit#(3))'(3'h3))[2:1])
        == ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : ((Bit#(3))'(3'h3))[0:0], enq_msg : Struct1 {id :
        (Bit#(6))'(6'h6), type_ : (Bool)'(True), addr : (x_17).addr, value :
        x_23}});
        let x_25 <- makeEnq_parentChildren001(x_24);
        let x_26 <- releaseMSHR_001(x_4);
    endrule

    rule rule_exec_001_100;
        $display ("Rule fired: rule_exec_001_100 at %t", $time);
        let x_0 <- deq_fifoL2E_001();
        Struct40 x_1 = ((x_0).lr_ir_pp);
        Bit#(3) x_2 = ((x_1).ir_msg_from);
        Struct1 x_3 = ((x_1).ir_msg);
        Bit#(3) x_4 = ((x_1).ir_mshr_id);
        Bool x_5 = ((x_1).ir_is_rs_rel);
        when (! (x_5), noAction);
        Struct41 x_6 = ((x_0).lr_ir);
        Struct11 x_7 = ((x_6).info);
        Struct10 x_8 = ((x_1).ir_by_victim);
        Vector#(4, Bit#(64)) x_9 = ((x_0).lr_value);
        let x_10 <- getMSHR_001(x_4);
        let x_11 <- getMSHRRq_001(x_4);
        let x_12 <- getMSHRFirstRs_001(x_4);
        Vector#(4, Bit#(64)) x_13 = (unpack(0));
        Bool x_14 = ((x_7).mesi_owned);
        Bit#(3) x_15 = ((x_7).mesi_status);
        Struct17 x_16 = (Struct17 {dir_st : (((x_7).mesi_dir_st) ==
        ((Bit#(3))'(3'h0)) ? ((Bit#(3))'(3'h1)) : ((x_7).mesi_dir_st)),
        dir_excl : ((((x_7).mesi_dir_sharers)[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(1))'(1'h0)) : (((Bit#(1))'(1'h1)) +
        ((((((x_7).mesi_dir_sharers)[1:1])[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(1))'(1'h0)) : (((Bit#(1))'(1'h1)) + (unpack(0))))))),
        dir_sharers : (x_7).mesi_dir_sharers});
        when ((x_2) == ((Bit#(3))'(3'h0)), noAction);
        when (((x_3).id) == ((Bit#(6))'(6'h8)), noAction);
        when (! ((x_3).type_), noAction);
        when ((x_15) == ((Bit#(3))'(3'h3)), noAction);
        Struct1 x_17 = (x_3);
        Struct45 x_18 = (Struct45 {addr : (x_3).addr, info_write :
        (Bool)'(False), info_hit : (x_6).info_hit, info_way : (x_6).info_way,
        edir_hit : (x_6).edir_hit, edir_way : (x_6).edir_way, edir_slot :
        (x_6).edir_slot, info : (x_6).info, value_write : (Bool)'(False),
        value : unpack(0), may_victim : (x_6).may_victim, reps :
        (x_6).reps});
        Struct45 x_19 = (Struct45 {addr : (x_18).addr, info_write :
        (x_18).info_write, info_hit : (x_18).info_hit, info_way :
        (x_18).info_way, edir_hit : (x_18).edir_hit, edir_way :
        (x_18).edir_way, edir_slot : (x_18).edir_slot, info : (x_18).info,
        value_write : (Bool)'(True), value : (x_17).value, may_victim :
        (x_18).may_victim, reps : (x_18).reps});
        Struct45 x_20 = (Struct45 {addr : (x_19).addr, info_write :
        (Bool)'(True), info_hit : (x_19).info_hit, info_way :
        (x_19).info_way, edir_hit : (x_19).edir_hit, edir_way :
        (x_19).edir_way, edir_slot : (x_19).edir_slot, info : Struct11
        {mesi_owned : ((x_19).info).mesi_owned, mesi_status :
        (Bit#(3))'(3'h4), mesi_dir_st : ((x_19).info).mesi_dir_st,
        mesi_dir_sharers : ((x_19).info).mesi_dir_sharers}, value_write :
        (x_19).value_write, value : (x_19).value, may_victim :
        (x_19).may_victim, reps : (x_19).reps});
        Struct45 x_21 = (Struct45 {addr : (x_20).addr, info_write :
        (Bool)'(True), info_hit : (x_20).info_hit, info_way :
        (x_20).info_way, edir_hit : (x_20).edir_hit, edir_way :
        (x_20).edir_way, edir_slot : (x_20).edir_slot, info : Struct11
        {mesi_owned : (Bool)'(True), mesi_status : ((x_20).info).mesi_status,
        mesi_dir_st : ((x_20).info).mesi_dir_st, mesi_dir_sharers :
        ((x_20).info).mesi_dir_sharers}, value_write : (x_20).value_write,
        value : (x_20).value, may_victim : (x_20).may_victim, reps :
        (x_20).reps});
        let x_24 = ?;
        if ((x_8).valid) begin
            let x_22 <- victims__001__setVictim(Struct47 {victim_idx :
            (x_8).data, victim_info : (x_21).info, victim_value :
            ((x_21).value_write ? ((x_21).value) : (x_9))});
            x_24 = x_9;
        end else begin
            let x_23 <- cache__001__valueRsLineRq(x_21);
            x_24 = x_23;
        end
        Struct20 x_25 = (Struct20 {enq_type : ((((Bit#(3))'(3'h4))[2:1]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : (((((Bit#(3))'(3'h4))[2:1])
        == ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : ((Bit#(3))'(3'h4))[0:0], enq_msg : Struct1 {id :
        (Bit#(6))'(6'h9), type_ : (Bool)'(True), addr : (x_17).addr, value :
        unpack(0)}});
        let x_26 <- makeEnq_parentChildren001(x_25);
        let x_27 <- releaseMSHR_001(x_4);
    endrule

    rule rule_exec_001_101;
        $display ("Rule fired: rule_exec_001_101 at %t", $time);
        let x_0 <- deq_fifoL2E_001();
        Struct40 x_1 = ((x_0).lr_ir_pp);
        Bit#(3) x_2 = ((x_1).ir_msg_from);
        Struct1 x_3 = ((x_1).ir_msg);
        Bit#(3) x_4 = ((x_1).ir_mshr_id);
        Bool x_5 = ((x_1).ir_is_rs_rel);
        when (! (x_5), noAction);
        Struct41 x_6 = ((x_0).lr_ir);
        Struct11 x_7 = ((x_6).info);
        Struct10 x_8 = ((x_1).ir_by_victim);
        Vector#(4, Bit#(64)) x_9 = ((x_0).lr_value);
        let x_10 <- getMSHR_001(x_4);
        let x_11 <- getMSHRRq_001(x_4);
        let x_12 <- getMSHRFirstRs_001(x_4);
        Vector#(4, Bit#(64)) x_13 = (unpack(0));
        Bool x_14 = ((x_7).mesi_owned);
        Bit#(3) x_15 = ((x_7).mesi_status);
        Struct17 x_16 = (Struct17 {dir_st : (((x_7).mesi_dir_st) ==
        ((Bit#(3))'(3'h0)) ? ((Bit#(3))'(3'h1)) : ((x_7).mesi_dir_st)),
        dir_excl : ((((x_7).mesi_dir_sharers)[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(1))'(1'h0)) : (((Bit#(1))'(1'h1)) +
        ((((((x_7).mesi_dir_sharers)[1:1])[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(1))'(1'h0)) : (((Bit#(1))'(1'h1)) + (unpack(0))))))),
        dir_sharers : (x_7).mesi_dir_sharers});
        when ((x_2) == ((Bit#(3))'(3'h0)), noAction);
        when (((x_3).id) == ((Bit#(6))'(6'h8)), noAction);
        when (! ((x_3).type_), noAction);
        when (((x_14) == ((Bool)'(True))) && ((x_15) == ((Bit#(3))'(3'h4))),
        noAction);
        Struct1 x_17 = (x_3);
        Struct45 x_18 = (Struct45 {addr : (x_3).addr, info_write :
        (Bool)'(False), info_hit : (x_6).info_hit, info_way : (x_6).info_way,
        edir_hit : (x_6).edir_hit, edir_way : (x_6).edir_way, edir_slot :
        (x_6).edir_slot, info : (x_6).info, value_write : (Bool)'(False),
        value : unpack(0), may_victim : (x_6).may_victim, reps :
        (x_6).reps});
        Struct45 x_19 = (Struct45 {addr : (x_18).addr, info_write :
        (x_18).info_write, info_hit : (x_18).info_hit, info_way :
        (x_18).info_way, edir_hit : (x_18).edir_hit, edir_way :
        (x_18).edir_way, edir_slot : (x_18).edir_slot, info : (x_18).info,
        value_write : (Bool)'(True), value : (x_17).value, may_victim :
        (x_18).may_victim, reps :
        (x_18).reps});
        let x_22 = ?;
        if ((x_8).valid) begin
            let x_20 <- victims__001__setVictim(Struct47 {victim_idx :
            (x_8).data, victim_info : (x_19).info, victim_value :
            ((x_19).value_write ? ((x_19).value) : (x_9))});
            x_22 = x_9;
        end else begin
            let x_21 <- cache__001__valueRsLineRq(x_19);
            x_22 = x_21;
        end
        Struct20 x_23 = (Struct20 {enq_type : ((((Bit#(3))'(3'h4))[2:1]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : (((((Bit#(3))'(3'h4))[2:1])
        == ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : ((Bit#(3))'(3'h4))[0:0], enq_msg : Struct1 {id :
        (Bit#(6))'(6'h9), type_ : (Bool)'(True), addr : (x_17).addr, value :
        unpack(0)}});
        let x_24 <- makeEnq_parentChildren001(x_23);
        let x_25 <- releaseMSHR_001(x_4);
    endrule

    rule rule_exec_001_11;
        $display ("Rule fired: rule_exec_001_11 at %t", $time);
        let x_0 <- deq_fifoL2E_001();
        Struct40 x_1 = ((x_0).lr_ir_pp);
        Bit#(3) x_2 = ((x_1).ir_msg_from);
        Struct1 x_3 = ((x_1).ir_msg);
        Bit#(3) x_4 = ((x_1).ir_mshr_id);
        Bool x_5 = ((x_1).ir_is_rs_rel);
        when (! (x_5), noAction);
        Struct41 x_6 = ((x_0).lr_ir);
        Struct11 x_7 = ((x_6).info);
        Struct10 x_8 = ((x_1).ir_by_victim);
        Vector#(4, Bit#(64)) x_9 = ((x_0).lr_value);
        let x_10 <- getMSHR_001(x_4);
        let x_11 <- getMSHRRq_001(x_4);
        let x_12 <- getMSHRFirstRs_001(x_4);
        Vector#(4, Bit#(64)) x_13 = (unpack(0));
        Bool x_14 = ((x_7).mesi_owned);
        Bit#(3) x_15 = ((x_7).mesi_status);
        Struct17 x_16 = (Struct17 {dir_st : (((x_7).mesi_dir_st) ==
        ((Bit#(3))'(3'h0)) ? ((Bit#(3))'(3'h1)) : ((x_7).mesi_dir_st)),
        dir_excl : ((((x_7).mesi_dir_sharers)[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(1))'(1'h0)) : (((Bit#(1))'(1'h1)) +
        ((((((x_7).mesi_dir_sharers)[1:1])[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(1))'(1'h0)) : (((Bit#(1))'(1'h1)) + (unpack(0))))))),
        dir_sharers : (x_7).mesi_dir_sharers});
        when ((x_2) == ((Bit#(3))'(3'h0)), noAction);
        when (((x_3).id) == ((Bit#(6))'(6'h8)), noAction);
        when (! ((x_3).type_), noAction);
        when (! (((Bit#(3))'(3'h2)) < (x_15)), noAction);
        Struct1 x_17 = (x_3);
        Struct45 x_18 = (Struct45 {addr : (x_3).addr, info_write :
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
        let x_21 <- registerUL_001(Struct46 {r_id : x_4, r_ul_rsb :
        (Bool)'(True), r_ul_rsbTo : ((Bit#(3))'(3'h4))[0:0]});
        Struct20 x_22 = (Struct20 {enq_type : ((((Bit#(3))'(3'h1))[2:1]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : (((((Bit#(3))'(3'h1))[2:1])
        == ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : ((Bit#(3))'(3'h1))[0:0], enq_msg : Struct1 {id :
        (Bit#(6))'(6'ha), type_ : (Bool)'(False), addr : (x_17).addr, value :
        unpack(0)}});
        let x_23 <- makeEnq_parentChildren001(x_22);
    endrule

    rule rule_exec_001_12;
        $display ("Rule fired: rule_exec_001_12 at %t", $time);
        let x_0 <- deq_fifoL2E_001();
        Struct40 x_1 = ((x_0).lr_ir_pp);
        Bit#(3) x_2 = ((x_1).ir_msg_from);
        Struct1 x_3 = ((x_1).ir_msg);
        Bit#(3) x_4 = ((x_1).ir_mshr_id);
        Bool x_5 = ((x_1).ir_is_rs_rel);
        when (! (x_5), noAction);
        Struct41 x_6 = ((x_0).lr_ir);
        Struct11 x_7 = ((x_6).info);
        Struct10 x_8 = ((x_1).ir_by_victim);
        Vector#(4, Bit#(64)) x_9 = ((x_0).lr_value);
        let x_10 <- getMSHR_001(x_4);
        let x_11 <- getMSHRRq_001(x_4);
        let x_12 <- getMSHRFirstRs_001(x_4);
        Vector#(4, Bit#(64)) x_13 = (unpack(0));
        Bool x_14 = ((x_7).mesi_owned);
        Bit#(3) x_15 = ((x_7).mesi_status);
        Struct17 x_16 = (Struct17 {dir_st : (((x_7).mesi_dir_st) ==
        ((Bit#(3))'(3'h0)) ? ((Bit#(3))'(3'h1)) : ((x_7).mesi_dir_st)),
        dir_excl : ((((x_7).mesi_dir_sharers)[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(1))'(1'h0)) : (((Bit#(1))'(1'h1)) +
        ((((((x_7).mesi_dir_sharers)[1:1])[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(1))'(1'h0)) : (((Bit#(1))'(1'h1)) + (unpack(0))))))),
        dir_sharers : (x_7).mesi_dir_sharers});
        when ((x_2) == ({((Bit#(2))'(2'h2)),((Bit#(1))'(1'h1))}),
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
        Bit#(3) x_19 = ({((Bit#(2))'(2'h2)),(((x_10).m_qidx)[0:0])});
        Struct45 x_20 = (Struct45 {addr : (x_3).addr, info_write :
        (Bool)'(False), info_hit : (x_6).info_hit, info_way : (x_6).info_way,
        edir_hit : (x_6).edir_hit, edir_way : (x_6).edir_way, edir_slot :
        (x_6).edir_slot, info : (x_6).info, value_write : (Bool)'(False),
        value : unpack(0), may_victim : (x_6).may_victim, reps :
        (x_6).reps});
        Struct45 x_21 = (Struct45 {addr : (x_20).addr, info_write :
        (x_20).info_write, info_hit : (x_20).info_hit, info_way :
        (x_20).info_way, edir_hit : (x_20).edir_hit, edir_way :
        (x_20).edir_way, edir_slot : (x_20).edir_slot, info : (x_20).info,
        value_write : (Bool)'(True), value : (x_18).value, may_victim :
        (x_20).may_victim, reps : (x_20).reps});
        Struct45 x_22 = (Struct45 {addr : (x_21).addr, info_write :
        (Bool)'(True), info_hit : (x_21).info_hit, info_way :
        (x_21).info_way, edir_hit : (x_21).edir_hit, edir_way :
        (x_21).edir_way, edir_slot : (x_21).edir_slot, info : Struct11
        {mesi_owned : (Bool)'(True), mesi_status : ((x_21).info).mesi_status,
        mesi_dir_st : ((x_21).info).mesi_dir_st, mesi_dir_sharers :
        ((x_21).info).mesi_dir_sharers}, value_write : (x_21).value_write,
        value : (x_21).value, may_victim : (x_21).may_victim, reps :
        (x_21).reps});
        Struct45 x_23 = (Struct45 {addr : (x_22).addr, info_write :
        (Bool)'(True), info_hit : (x_22).info_hit, info_way :
        (x_22).info_way, edir_hit : (x_22).edir_hit, edir_way :
        (x_22).edir_way, edir_slot : (x_22).edir_slot, info : Struct11
        {mesi_owned : ((x_22).info).mesi_owned, mesi_status :
        (Bit#(3))'(3'h4), mesi_dir_st : ((x_22).info).mesi_dir_st,
        mesi_dir_sharers : ((x_22).info).mesi_dir_sharers}, value_write :
        (x_22).value_write, value : (x_22).value, may_victim :
        (x_22).may_victim, reps :
        (x_22).reps});
        let x_26 = ?;
        if ((x_8).valid) begin
            let x_24 <- victims__001__setVictim(Struct47 {victim_idx :
            (x_8).data, victim_info : (x_23).info, victim_value :
            ((x_23).value_write ? ((x_23).value) : (x_9))});
            x_26 = x_9;
        end else begin
            let x_25 <- cache__001__valueRsLineRq(x_23);
            x_26 = x_25;
        end
        let x_27 <- releaseMSHR_001(x_4);
        Struct20 x_28 = (Struct20 {enq_type : (((x_19)[2:1]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : ((((x_19)[2:1]) ==
        ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : (x_19)[0:0], enq_msg : Struct1 {id : (Bit#(6))'(6'h9),
        type_ : (Bool)'(True), addr : (x_17).addr, value : unpack(0)}});
        let x_29 <- makeEnq_parentChildren001(x_28);
    endrule

    rule rule_exec_001_130;
        $display ("Rule fired: rule_exec_001_130 at %t", $time);
        let x_0 <- deq_fifoL2E_001();
        Struct40 x_1 = ((x_0).lr_ir_pp);
        Bit#(3) x_2 = ((x_1).ir_msg_from);
        Struct1 x_3 = ((x_1).ir_msg);
        Bit#(3) x_4 = ((x_1).ir_mshr_id);
        Bool x_5 = ((x_1).ir_is_rs_rel);
        when (! (x_5), noAction);
        Struct41 x_6 = ((x_0).lr_ir);
        Struct11 x_7 = ((x_6).info);
        Struct10 x_8 = ((x_1).ir_by_victim);
        Vector#(4, Bit#(64)) x_9 = ((x_0).lr_value);
        let x_10 <- getMSHR_001(x_4);
        let x_11 <- getMSHRRq_001(x_4);
        let x_12 <- getMSHRFirstRs_001(x_4);
        Vector#(4, Bit#(64)) x_13 = (unpack(0));
        Bool x_14 = ((x_7).mesi_owned);
        Bit#(3) x_15 = ((x_7).mesi_status);
        Struct17 x_16 = (Struct17 {dir_st : (((x_7).mesi_dir_st) ==
        ((Bit#(3))'(3'h0)) ? ((Bit#(3))'(3'h1)) : ((x_7).mesi_dir_st)),
        dir_excl : ((((x_7).mesi_dir_sharers)[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(1))'(1'h0)) : (((Bit#(1))'(1'h1)) +
        ((((((x_7).mesi_dir_sharers)[1:1])[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(1))'(1'h0)) : (((Bit#(1))'(1'h1)) + (unpack(0))))))),
        dir_sharers : (x_7).mesi_dir_sharers});
        when ((x_2) == ((Bit#(3))'(3'h5)), noAction);
        when (((x_3).id) == ((Bit#(6))'(6'hc)), noAction);
        when (! ((x_3).type_), noAction);
        when ((Bool)'(True), noAction);
        Struct1 x_17 = (x_3);
        Struct45 x_18 = (Struct45 {addr : (x_3).addr, info_write :
        (Bool)'(False), info_hit : (x_6).info_hit, info_way : (x_6).info_way,
        edir_hit : (x_6).edir_hit, edir_way : (x_6).edir_way, edir_slot :
        (x_6).edir_slot, info : (x_6).info, value_write : (Bool)'(False),
        value : unpack(0), may_victim : (x_6).may_victim, reps :
        (x_6).reps});
        Struct45 x_19 = (Struct45 {addr : (x_18).addr, info_write :
        (Bool)'(True), info_hit : (x_18).info_hit, info_way :
        (x_18).info_way, edir_hit : (x_18).edir_hit, edir_way :
        (x_18).edir_way, edir_slot : (x_18).edir_slot, info : Struct11
        {mesi_owned : ((x_18).info).mesi_owned, mesi_status :
        (Bit#(3))'(3'h1), mesi_dir_st : ((x_18).info).mesi_dir_st,
        mesi_dir_sharers : ((x_18).info).mesi_dir_sharers}, value_write :
        (x_18).value_write, value : (x_18).value, may_victim :
        (x_18).may_victim, reps : (x_18).reps});
        Struct45 x_20 = (Struct45 {addr : (x_19).addr, info_write :
        (Bool)'(True), info_hit : (x_19).info_hit, info_way :
        (x_19).info_way, edir_hit : (x_19).edir_hit, edir_way :
        (x_19).edir_way, edir_slot : (x_19).edir_slot, info : Struct11
        {mesi_owned : (Bool)'(False), mesi_status :
        ((x_19).info).mesi_status, mesi_dir_st : ((x_19).info).mesi_dir_st,
        mesi_dir_sharers : ((x_19).info).mesi_dir_sharers}, value_write :
        (x_19).value_write, value : (x_19).value, may_victim :
        (x_19).may_victim, reps :
        (x_19).reps});
        let x_23 = ?;
        if ((x_8).valid) begin
            let x_21 <- victims__001__setVictim(Struct47 {victim_idx :
            (x_8).data, victim_info : (x_20).info, victim_value :
            ((x_20).value_write ? ((x_20).value) : (x_9))});
            x_23 = x_9;
        end else begin
            let x_22 <- cache__001__valueRsLineRq(x_20);
            x_23 = x_22;
        end
        Struct20 x_24 = (Struct20 {enq_type : ((((Bit#(3))'(3'h3))[2:1]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : (((((Bit#(3))'(3'h3))[2:1])
        == ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : ((Bit#(3))'(3'h3))[0:0], enq_msg : Struct1 {id :
        (Bit#(6))'(6'hd), type_ : (Bool)'(True), addr : (x_17).addr, value :
        unpack(0)}});
        let x_25 <- makeEnq_parentChildren001(x_24);
        let x_26 <- releaseMSHR_001(x_4);
    endrule

    rule rule_exec_001_131;
        $display ("Rule fired: rule_exec_001_131 at %t", $time);
        let x_0 <- deq_fifoL2E_001();
        Struct40 x_1 = ((x_0).lr_ir_pp);
        Bit#(3) x_2 = ((x_1).ir_msg_from);
        Struct1 x_3 = ((x_1).ir_msg);
        Bit#(3) x_4 = ((x_1).ir_mshr_id);
        Bool x_5 = ((x_1).ir_is_rs_rel);
        when (! (x_5), noAction);
        Struct41 x_6 = ((x_0).lr_ir);
        Struct11 x_7 = ((x_6).info);
        Struct10 x_8 = ((x_1).ir_by_victim);
        Vector#(4, Bit#(64)) x_9 = ((x_0).lr_value);
        let x_10 <- getMSHR_001(x_4);
        let x_11 <- getMSHRRq_001(x_4);
        let x_12 <- getMSHRFirstRs_001(x_4);
        Vector#(4, Bit#(64)) x_13 = (unpack(0));
        Bool x_14 = ((x_7).mesi_owned);
        Bit#(3) x_15 = ((x_7).mesi_status);
        Struct17 x_16 = (Struct17 {dir_st : (((x_7).mesi_dir_st) ==
        ((Bit#(3))'(3'h0)) ? ((Bit#(3))'(3'h1)) : ((x_7).mesi_dir_st)),
        dir_excl : ((((x_7).mesi_dir_sharers)[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(1))'(1'h0)) : (((Bit#(1))'(1'h1)) +
        ((((((x_7).mesi_dir_sharers)[1:1])[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(1))'(1'h0)) : (((Bit#(1))'(1'h1)) + (unpack(0))))))),
        dir_sharers : (x_7).mesi_dir_sharers});
        when ((x_2) == ((Bit#(3))'(3'h5)), noAction);
        when (((x_3).id) == ((Bit#(6))'(6'he)), noAction);
        when (! ((x_3).type_), noAction);
        when (! ((x_15) < ((Bit#(3))'(3'h3))), noAction);
        Struct1 x_17 = (x_3);
        Struct45 x_18 = (Struct45 {addr : (x_3).addr, info_write :
        (Bool)'(False), info_hit : (x_6).info_hit, info_way : (x_6).info_way,
        edir_hit : (x_6).edir_hit, edir_way : (x_6).edir_way, edir_slot :
        (x_6).edir_slot, info : (x_6).info, value_write : (Bool)'(False),
        value : unpack(0), may_victim : (x_6).may_victim, reps :
        (x_6).reps});
        Struct45 x_19 = (Struct45 {addr : (x_18).addr, info_write :
        (Bool)'(True), info_hit : (x_18).info_hit, info_way :
        (x_18).info_way, edir_hit : (x_18).edir_hit, edir_way :
        (x_18).edir_way, edir_slot : (x_18).edir_slot, info : Struct11
        {mesi_owned : ((x_18).info).mesi_owned, mesi_status :
        (Bit#(3))'(3'h1), mesi_dir_st : ((x_18).info).mesi_dir_st,
        mesi_dir_sharers : ((x_18).info).mesi_dir_sharers}, value_write :
        (x_18).value_write, value : (x_18).value, may_victim :
        (x_18).may_victim, reps : (x_18).reps});
        Struct45 x_20 = (Struct45 {addr : (x_19).addr, info_write :
        (Bool)'(True), info_hit : (x_19).info_hit, info_way :
        (x_19).info_way, edir_hit : (x_19).edir_hit, edir_way :
        (x_19).edir_way, edir_slot : (x_19).edir_slot, info : Struct11
        {mesi_owned : (Bool)'(False), mesi_status :
        ((x_19).info).mesi_status, mesi_dir_st : ((x_19).info).mesi_dir_st,
        mesi_dir_sharers : ((x_19).info).mesi_dir_sharers}, value_write :
        (x_19).value_write, value : (x_19).value, may_victim :
        (x_19).may_victim, reps :
        (x_19).reps});
        let x_23 = ?;
        if ((x_8).valid) begin
            let x_21 <- victims__001__setVictim(Struct47 {victim_idx :
            (x_8).data, victim_info : (x_20).info, victim_value :
            ((x_20).value_write ? ((x_20).value) : (x_9))});
            x_23 = x_9;
        end else begin
            let x_22 <- cache__001__valueRsLineRq(x_20);
            x_23 = x_22;
        end
        Struct20 x_24 = (Struct20 {enq_type : ((((Bit#(3))'(3'h3))[2:1]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : (((((Bit#(3))'(3'h3))[2:1])
        == ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : ((Bit#(3))'(3'h3))[0:0], enq_msg : Struct1 {id :
        (Bit#(6))'(6'hf), type_ : (Bool)'(True), addr : (x_17).addr, value :
        unpack(0)}});
        let x_25 <- makeEnq_parentChildren001(x_24);
        let x_26 <- releaseMSHR_001(x_4);
    endrule

    rule rule_exec_001_20;
        $display ("Rule fired: rule_exec_001_20 at %t", $time);
        let x_0 <- victims__001__getFirstVictim();
        Bit#(64) x_1 = ((x_0).victim_addr);
        Struct11 x_2 = ((x_0).victim_info);
        Vector#(4, Bit#(64)) x_3 = ((x_0).victim_value);
        Struct1 x_4 = (Struct1 {id : unpack(0), type_ : (Bool)'(False), addr
        : x_1, value : unpack(0)});
        Struct44 x_5 = (Struct44 {m_status : (Bit#(3))'(3'h5), m_next :
        unpack(0), m_is_ul : (Bool)'(True), m_addr : x_1, m_qidx : unpack(0),
        m_rsb : (Bool)'(False), m_dl_rss_from : unpack(0), m_dl_rss_recv :
        unpack(0)});
        Struct1 x_6 = (unpack(0));
        Struct1 x_7 = (unpack(0));
        Vector#(4, Bit#(64)) x_8 = (unpack(0));
        Bool x_9 = ((x_2).mesi_owned);
        Bit#(3) x_10 = ((x_2).mesi_status);
        Struct17 x_11 = (Struct17 {dir_st : (((x_2).mesi_dir_st) ==
        ((Bit#(3))'(3'h0)) ? ((Bit#(3))'(3'h1)) : ((x_2).mesi_dir_st)),
        dir_excl : ((((x_2).mesi_dir_sharers)[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(1))'(1'h0)) : (((Bit#(1))'(1'h1)) +
        ((((((x_2).mesi_dir_sharers)[1:1])[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(1))'(1'h0)) : (((Bit#(1))'(1'h1)) + (unpack(0))))))),
        dir_sharers : (x_2).mesi_dir_sharers});
        when (! ((x_4).type_), noAction);
        when (((x_9) == ((Bool)'(False))) && ((((Bit#(3))'(3'h0)) < (x_10))
        && ((x_10) < ((Bit#(3))'(3'h4)))), noAction);
        Struct20 x_12 = (Struct20 {enq_type : ((((Bit#(3))'(3'h1))[2:1]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : (((((Bit#(3))'(3'h1))[2:1])
        == ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : ((Bit#(3))'(3'h1))[0:0], enq_msg : Struct1 {id :
        (Bit#(6))'(6'h14), type_ : (Bool)'(False), addr : (x_4).addr, value :
        unpack(0)}});
        let x_13 <- makeEnq_parentChildren001(x_12);
        let x_14 <- setULImm_001(x_4);
        let x_15 <- victims__001__setVictimRq(x_1);
    endrule

    rule rule_exec_001_21;
        $display ("Rule fired: rule_exec_001_21 at %t", $time);
        let x_0 <- victims__001__getFirstVictim();
        Bit#(64) x_1 = ((x_0).victim_addr);
        Struct11 x_2 = ((x_0).victim_info);
        Vector#(4, Bit#(64)) x_3 = ((x_0).victim_value);
        Struct1 x_4 = (Struct1 {id : unpack(0), type_ : (Bool)'(False), addr
        : x_1, value : unpack(0)});
        Struct44 x_5 = (Struct44 {m_status : (Bit#(3))'(3'h5), m_next :
        unpack(0), m_is_ul : (Bool)'(True), m_addr : x_1, m_qidx : unpack(0),
        m_rsb : (Bool)'(False), m_dl_rss_from : unpack(0), m_dl_rss_recv :
        unpack(0)});
        Struct1 x_6 = (unpack(0));
        Struct1 x_7 = (unpack(0));
        Vector#(4, Bit#(64)) x_8 = (unpack(0));
        Bool x_9 = ((x_2).mesi_owned);
        Bit#(3) x_10 = ((x_2).mesi_status);
        Struct17 x_11 = (Struct17 {dir_st : (((x_2).mesi_dir_st) ==
        ((Bit#(3))'(3'h0)) ? ((Bit#(3))'(3'h1)) : ((x_2).mesi_dir_st)),
        dir_excl : ((((x_2).mesi_dir_sharers)[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(1))'(1'h0)) : (((Bit#(1))'(1'h1)) +
        ((((((x_2).mesi_dir_sharers)[1:1])[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(1))'(1'h0)) : (((Bit#(1))'(1'h1)) + (unpack(0))))))),
        dir_sharers : (x_2).mesi_dir_sharers});
        when (! ((x_4).type_), noAction);
        when (((Bit#(3))'(3'h0)) < (x_10), noAction);
        Struct20 x_12 = (Struct20 {enq_type : ((((Bit#(3))'(3'h1))[2:1]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : (((((Bit#(3))'(3'h1))[2:1])
        == ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : ((Bit#(3))'(3'h1))[0:0], enq_msg : Struct1 {id :
        (Bit#(6))'(6'h15), type_ : (Bool)'(False), addr : (x_4).addr, value :
        x_3}});
        let x_13 <- makeEnq_parentChildren001(x_12);
        let x_14 <- setULImm_001(x_4);
        let x_15 <- victims__001__setVictimRq(x_1);
    endrule

    // No methods in this module
endmodule

typedef 2 L1Num;

interface MemRqRs#(type msgT);
    method Action mem_enq_rq (msgT rq);
    method ActionValue#(msgT) mem_deq_rs ();
endinterface

interface DMA#(type rdReqT, type wrReqT, type valueT);
    method Action dma_rdReq (rdReqT addr);
    method Action dma_wrReq (wrReqT rq);
    method ActionValue#(valueT) dma_rdResp ();
endinterface


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
    Module59 m59 <- mkModule59 (m46.deq_fifo0010, m1.enq_fifoCRqInput_00,
    m28.deq_fifo0000);
    Module60 m60 <- mkModule60 (m47.deq_fifo0011, m2.enq_fifoCRsInput_00,
    m29.deq_fifo0001);
    Module61 m61 <- mkModule61 (m3.enq_fifoPInput_00, deq_fifo002);
    Module62 m62 <- mkModule62 (m30.enq_fifo0002, m48.enq_fifo0012,
    enq_fifo001, enq_fifo000);
    Module63 m63 <- mkModule63 (m21.wrReq_repRam__00, m21.rdResp_repRam__00,
    m21.rdReq_repRam__00);
    Module64 m64 <- mkModule64 (m23.enq_fifoCRqInput_000, m31.deq_fifo00000);

    Module65 m65 <- mkModule65 (m24.enq_fifoPInput_000, m30.deq_fifo0002);

    Module66 m66 <- mkModule66 (m32.enq_fifo00002, m29.enq_fifo0001,
    m28.enq_fifo0000);
    Module67 m67 <- mkModule67 (m39.wrReq_repRam__000,
    m39.rdResp_repRam__000, m39.rdReq_repRam__000);
    Module68 m68 <- mkModule68 (m41.enq_fifoCRqInput_001, m49.deq_fifo00100);

    Module69 m69 <- mkModule69 (m42.enq_fifoPInput_001, m48.deq_fifo0012);

    Module70 m70 <- mkModule70 (m50.enq_fifo00102, m47.enq_fifo0011,
    m46.enq_fifo0010);
    Module71 m71 <- mkModule71 (m57.wrReq_repRam__001,
    m57.rdResp_repRam__001, m57.rdReq_repRam__001);
    Module72 m72 <- mkModule72 (m20.wrReq_dataRam__00,
    m16.wrReq_edirRam__00__3, m17.wrReq_edirRam__00__2,
    m18.wrReq_edirRam__00__1, m19.wrReq_edirRam__00__0, m63.repAccess__00,
    m7.victims__00__registerVictim, m8.wrReq_infoRam__00__7,
    m9.wrReq_infoRam__00__6, m10.wrReq_infoRam__00__5,
    m11.wrReq_infoRam__00__4, m12.wrReq_infoRam__00__3,
    m13.wrReq_infoRam__00__2, m14.wrReq_infoRam__00__1,
    m15.wrReq_infoRam__00__0, m20.rdResp_dataRam__00, m20.rdReq_dataRam__00,
    m63.repGetRs__00, m16.rdResp_edirRam__00__3, m17.rdResp_edirRam__00__2,
    m18.rdResp_edirRam__00__1, m19.rdResp_edirRam__00__0,
    m8.rdResp_infoRam__00__7, m9.rdResp_infoRam__00__6,
    m10.rdResp_infoRam__00__5, m11.rdResp_infoRam__00__4,
    m12.rdResp_infoRam__00__3, m13.rdResp_infoRam__00__2,
    m14.rdResp_infoRam__00__1, m15.rdResp_infoRam__00__0, m63.repGetRq__00,
    m16.rdReq_edirRam__00__3, m17.rdReq_edirRam__00__2,
    m18.rdReq_edirRam__00__1, m19.rdReq_edirRam__00__0,
    m8.rdReq_infoRam__00__7, m9.rdReq_infoRam__00__6,
    m10.rdReq_infoRam__00__5, m11.rdReq_infoRam__00__4,
    m12.rdReq_infoRam__00__3, m13.rdReq_infoRam__00__2,
    m14.rdReq_infoRam__00__1, m15.rdReq_infoRam__00__0);
    Module73 m73 <- mkModule73 (m38.wrReq_dataRam__000, m67.repAccess__000,
    m33.victims__000__registerVictim, m34.wrReq_infoRam__000__3,
    m35.wrReq_infoRam__000__2, m36.wrReq_infoRam__000__1,
    m37.wrReq_infoRam__000__0, m38.rdResp_dataRam__000,
    m38.rdReq_dataRam__000, m67.repGetRs__000, m34.rdResp_infoRam__000__3,
    m35.rdResp_infoRam__000__2, m36.rdResp_infoRam__000__1,
    m37.rdResp_infoRam__000__0, m67.repGetRq__000, m34.rdReq_infoRam__000__3,
    m35.rdReq_infoRam__000__2, m36.rdReq_infoRam__000__1,
    m37.rdReq_infoRam__000__0);
    Module74 m74 <- mkModule74 (m56.wrReq_dataRam__001, m71.repAccess__001,
    m51.victims__001__registerVictim, m52.wrReq_infoRam__001__3,
    m53.wrReq_infoRam__001__2, m54.wrReq_infoRam__001__1,
    m55.wrReq_infoRam__001__0, m56.rdResp_dataRam__001,
    m56.rdReq_dataRam__001, m71.repGetRs__001, m52.rdResp_infoRam__001__3,
    m53.rdResp_infoRam__001__2, m54.rdResp_infoRam__001__1,
    m55.rdResp_infoRam__001__0, m71.repGetRq__001, m52.rdReq_infoRam__001__3,
    m53.rdReq_infoRam__001__2, m54.rdReq_infoRam__001__1,
    m55.rdReq_infoRam__001__0);
    Module75 m75 <- mkModule75 (m22.canImm_00, m7.victims__00__setVictimRq,
    m22.setULImm_00, m7.victims__00__getFirstVictim, m22.transferUpDown_00,
    m62.broadcast_parentChildren00, m22.registerDL_00, m22.registerUL_00,
    m62.makeEnq_parentChildren00, m72.cache__00__valueRsLineRq,
    m7.victims__00__setVictim, m22.getMSHRFirstRs_00, m22.getMSHRRq_00,
    m22.getMSHR_00, m6.deq_fifoL2E_00, m7.victims__00__getVictim,
    m6.enq_fifoL2E_00, m72.cache__00__infoRsValueRq, m5.deq_fifoI2L_00,
    m5.enq_fifoI2L_00, m72.cache__00__infoRq, m4.deq_fifoN2I_00,
    m22.getDLReady_00, m22.addRs_00, m2.deq_fifoCRsInput_00,
    m22.getCRqSlot_00, m7.victims__00__hasVictim, m1.deq_fifoCRqInput_00,
    m22.releaseMSHR_00, m7.victims__00__releaseVictim, m22.getWait_00,
    m22.startRelease_00, m22.getULReady_00, m4.enq_fifoN2I_00,
    m7.victims__00__findVictim, m22.getPRqSlot_00, m3.deq_fifoPInput_00);

    Module76 m76 <- mkModule76 (m33.victims__000__setVictimRq,
    m40.setULImm_000, m33.victims__000__getFirstVictim,
    m33.victims__000__setVictim, m40.registerUL_000,
    m66.makeEnq_parentChildren000, m73.cache__000__valueRsLineRq,
    m40.getMSHRFirstRs_000, m40.getMSHRRq_000, m40.getMSHR_000,
    m27.deq_fifoL2E_000, m33.victims__000__getVictim, m27.enq_fifoL2E_000,
    m73.cache__000__infoRsValueRq, m26.deq_fifoI2L_000, m26.enq_fifoI2L_000,
    m73.cache__000__infoRq, m25.deq_fifoN2I_000, m40.getCRqSlot_000,
    m33.victims__000__hasVictim, m23.deq_fifoCRqInput_000,
    m40.releaseMSHR_000, m33.victims__000__releaseVictim, m40.getWait_000,
    m40.startRelease_000, m40.getULReady_000, m25.enq_fifoN2I_000,
    m33.victims__000__findVictim, m40.getPRqSlot_000,
    m24.deq_fifoPInput_000);
    Module77 m77 <- mkModule77 (m51.victims__001__setVictimRq,
    m58.setULImm_001, m51.victims__001__getFirstVictim,
    m51.victims__001__setVictim, m58.registerUL_001,
    m70.makeEnq_parentChildren001, m74.cache__001__valueRsLineRq,
    m58.getMSHRFirstRs_001, m58.getMSHRRq_001, m58.getMSHR_001,
    m45.deq_fifoL2E_001, m51.victims__001__getVictim, m45.enq_fifoL2E_001,
    m74.cache__001__infoRsValueRq, m44.deq_fifoI2L_001, m44.enq_fifoI2L_001,
    m74.cache__001__infoRq, m43.deq_fifoN2I_001, m58.getCRqSlot_001,
    m51.victims__001__hasVictim, m41.deq_fifoCRqInput_001,
    m58.releaseMSHR_001, m51.victims__001__releaseVictim, m58.getWait_001,
    m58.startRelease_001, m58.getULReady_001, m43.enq_fifoN2I_001,
    m51.victims__001__findVictim, m58.getPRqSlot_001,
    m42.deq_fifoPInput_001);
    //// Interface

    function MemRqRs#(Struct1) getMemRqRs (function Action enq_rq (Struct1 _),
                                           function ActionValue#(Struct1) deq_rs ());
        return interface MemRqRs;
                   method mem_enq_rq = enq_rq;
                   method mem_deq_rs = deq_rs;
               endinterface;
    endfunction

    Vector#(L1Num, MemRqRs#(Struct1)) _l1Ifc = newVector();
    _l1Ifc[0] = getMemRqRs(m31.enq_fifo00000, m32.deq_fifo00002);
    _l1Ifc[1] = getMemRqRs(m49.enq_fifo00100, m50.deq_fifo00102);
    interface l1Ifc = _l1Ifc;

    interface DMA llDma;
        method dma_rdReq = m20.rdReq_dataRam__00;
        method dma_wrReq = m20.wrReq_dataRam__00;
        method dma_rdResp = m20.rdResp_dataRam__00;
    endinterface

endmodule
