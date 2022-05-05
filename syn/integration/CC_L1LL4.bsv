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
    method Action enq_fifoCRqInput__0_0 (Struct2 x_0);
    method ActionValue#(Struct2) deq_fifoCRqInput__0_0 ();
endinterface

module mkModule1 (Module1);
    FIFOF#(Struct2) pff <- mkSizedFIFOF(4);
    
    method Action enq_fifoCRqInput__0_0 (Struct2 x_0);
        pff.enq(x_0);
    endmethod
    
    method ActionValue#(Struct2) deq_fifoCRqInput__0_0 ();
        pff.deq();
        return pff.first();
    endmethod

endmodule

interface Module2;
    method Action enq_fifoCRsInput__0_0 (Struct2 x_0);
    method ActionValue#(Struct2) deq_fifoCRsInput__0_0 ();
endinterface

module mkModule2 (Module2);
    FIFOF#(Struct2) pff <- mkSizedFIFOF(4);
    
    method Action enq_fifoCRsInput__0_0 (Struct2 x_0);
        pff.enq(x_0);
    endmethod
    
    method ActionValue#(Struct2) deq_fifoCRsInput__0_0 ();
        pff.deq();
        return pff.first();
    endmethod

endmodule

interface Module3;
    method Action enq_fifoPInput__0_0 (Struct2 x_0);
    method ActionValue#(Struct2) deq_fifoPInput__0_0 ();
endinterface

module mkModule3 (Module3);
    FIFOF#(Struct2) pff <- mkSizedFIFOF(4);
    
    method Action enq_fifoPInput__0_0 (Struct2 x_0);
        pff.enq(x_0);
    endmethod
    
    method ActionValue#(Struct2) deq_fifoPInput__0_0 ();
        pff.deq();
        return pff.first();
    endmethod

endmodule

interface Module4;
    method Action enq_fifoN2I__0_0 (Struct6 x_0);
    method ActionValue#(Struct6) deq_fifoN2I__0_0 ();
endinterface

module mkModule4 (Module4);
    FIFOF#(Struct6) pff <- mkPipelineFIFOF();
    
    method Action enq_fifoN2I__0_0 (Struct6 x_0);
        pff.enq(x_0);
    endmethod
    
    method ActionValue#(Struct6) deq_fifoN2I__0_0 ();
        pff.deq();
        return pff.first();
    endmethod

endmodule

interface Module5;
    method Action enq_fifoI2L__0_0 (Struct6 x_0);
    method ActionValue#(Struct6) deq_fifoI2L__0_0 ();
endinterface

module mkModule5 (Module5);
    FIFOF#(Struct6) pff <- mkPipelineFIFOF();
    
    method Action enq_fifoI2L__0_0 (Struct6 x_0);
        pff.enq(x_0);
    endmethod
    
    method ActionValue#(Struct6) deq_fifoI2L__0_0 ();
        pff.deq();
        return pff.first();
    endmethod

endmodule

interface Module6;
    method Action enq_fifoL2E__0_0 (Struct12 x_0);
    method ActionValue#(Struct12) deq_fifoL2E__0_0 ();
endinterface

module mkModule6 (Module6);
    FIFOF#(Struct12) pff <- mkPipelineFIFOF();
    
    method Action enq_fifoL2E__0_0 (Struct12 x_0);
        pff.enq(x_0);
    endmethod
    
    method ActionValue#(Struct12) deq_fifoL2E__0_0 ();
        pff.deq();
        return pff.first();
    endmethod

endmodule

interface Module7;
    method ActionValue#(Struct5) victims___0_0__findVictim (Bit#(64) x_0);
    method ActionValue#(Struct13) victims___0_0__getVictim (Bit#(3) x_0);
    method Action victims___0_0__setVictim (Struct17 x_0);
    method Action victims___0_0__registerVictim (Struct13 x_0);
    method ActionValue#(Struct13) victims___0_0__getFirstVictim ();
    method ActionValue#(Bool) victims___0_0__hasVictim ();
    method Action victims___0_0__setVictimRq (Bit#(64) x_0);
    method Action victims___0_0__releaseVictim (Bit#(64) x_0);
endinterface

module mkModule7
    (Module7);
    Reg#(Vector#(8, Struct13)) victimRegs___0_0 <- mkReg(unpack(0));
    
    // No rules in this module
    
    method ActionValue#(Struct5) victims___0_0__findVictim (Bit#(64) x_0);
        let x_1 = (victimRegs___0_0);
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
    
    method ActionValue#(Struct13) victims___0_0__getVictim (Bit#(3) x_0);
        let x_1 = (victimRegs___0_0);
        return (x_1)[x_0];
    endmethod
    
    method Action victims___0_0__setVictim (Struct17 x_0);
        let x_1 = (victimRegs___0_0);
        Struct13 x_2 = ((x_1)[(x_0).victim_idx]);
        Struct13 x_3 = (Struct13 {victim_valid : (Bool)'(True), victim_addr :
        (x_2).victim_addr, victim_info : (x_0).victim_info, victim_value :
        (x_0).victim_value, victim_req : (x_2).victim_req});
        victimRegs___0_0 <= update (x_1, (x_0).victim_idx, x_3);
    endmethod
    
    method Action victims___0_0__registerVictim (Struct13 x_0);
        let x_1 = (victimRegs___0_0);
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
        victimRegs___0_0 <= update (x_1, x_3, x_0);
    endmethod
    
    method ActionValue#(Struct13) victims___0_0__getFirstVictim ();
        let x_1 = (victimRegs___0_0);
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
    
    method ActionValue#(Bool) victims___0_0__hasVictim ();
        let x_1 = (victimRegs___0_0);
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
    
    method Action victims___0_0__setVictimRq (Bit#(64) x_0);
        let x_1 = (victimRegs___0_0);
        Struct13 x_2 =
        ((x_1)[(Bit#(3))'(3'h7)]);
        if (((x_2).victim_valid) && (((x_2).victim_addr) == (x_0)))
            begin
            Struct13 x_3 = (Struct13 {victim_valid : (x_2).victim_valid,
            victim_addr : (x_2).victim_addr, victim_info : (x_2).victim_info,
            victim_value : (x_2).victim_value, victim_req :
            (Bool)'(True)});
            victimRegs___0_0 <= update (x_1, (Bit#(3))'(3'h7), x_3);
        end else begin
            Struct13 x_4 =
            ((x_1)[(Bit#(3))'(3'h6)]);
            if (((x_4).victim_valid) && (((x_4).victim_addr) == (x_0)))
                begin
                Struct13 x_5 = (Struct13 {victim_valid : (x_4).victim_valid,
                victim_addr : (x_4).victim_addr, victim_info :
                (x_4).victim_info, victim_value : (x_4).victim_value,
                victim_req : (Bool)'(True)});
                victimRegs___0_0 <= update (x_1, (Bit#(3))'(3'h6), x_5);
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
                    victimRegs___0_0 <= update (x_1, (Bit#(3))'(3'h5), x_7);
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
                        victimRegs___0_0 <= update (x_1, (Bit#(3))'(3'h4),
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
                            victimRegs___0_0 <= update (x_1,
                            (Bit#(3))'(3'h3), x_11);
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
                                victimRegs___0_0 <= update (x_1,
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
                                    victimRegs___0_0 <= update (x_1,
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
                                        victimRegs___0_0 <= update (x_1,
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
    
    method Action victims___0_0__releaseVictim (Bit#(64) x_0);
        let x_1 = (victimRegs___0_0);
        Struct13 x_2 =
        ((x_1)[(Bit#(3))'(3'h0)]);
        if (((x_2).victim_valid) && (((x_2).victim_addr) == (x_0)))
            begin
            victimRegs___0_0 <= update (x_1, (Bit#(3))'(3'h0), unpack(0));
        end else begin
            Struct13 x_3 =
            ((x_1)[(Bit#(3))'(3'h1)]);
            if (((x_3).victim_valid) && (((x_3).victim_addr) == (x_0)))
                begin
                victimRegs___0_0 <= update (x_1, (Bit#(3))'(3'h1),
                unpack(0));
            end else begin
                Struct13 x_4 =
                ((x_1)[(Bit#(3))'(3'h2)]);
                if (((x_4).victim_valid) && (((x_4).victim_addr) == (x_0)))
                    begin
                    victimRegs___0_0 <= update (x_1, (Bit#(3))'(3'h2),
                    unpack(0));
                end else begin
                    Struct13 x_5 =
                    ((x_1)[(Bit#(3))'(3'h3)]);
                    if (((x_5).victim_valid) && (((x_5).victim_addr) ==
                        (x_0))) begin
                        victimRegs___0_0 <= update (x_1, (Bit#(3))'(3'h3),
                        unpack(0));
                    end else begin
                        Struct13 x_6 =
                        ((x_1)[(Bit#(3))'(3'h4)]);
                        if (((x_6).victim_valid) && (((x_6).victim_addr) ==
                            (x_0))) begin
                            victimRegs___0_0 <= update (x_1,
                            (Bit#(3))'(3'h4), unpack(0));
                        end else begin
                            Struct13 x_7 =
                            ((x_1)[(Bit#(3))'(3'h5)]);
                            if (((x_7).victim_valid) && (((x_7).victim_addr)
                                == (x_0))) begin
                                victimRegs___0_0 <= update (x_1,
                                (Bit#(3))'(3'h5), unpack(0));
                            end else begin
                                Struct13 x_8 =
                                ((x_1)[(Bit#(3))'(3'h6)]);
                                if (((x_8).victim_valid) &&
                                    (((x_8).victim_addr) == (x_0)))
                                    begin
                                    victimRegs___0_0 <= update (x_1,
                                    (Bit#(3))'(3'h6), unpack(0));
                                end else begin
                                    Struct13 x_9 =
                                    ((x_1)[(Bit#(3))'(3'h7)]);
                                    if (((x_9).victim_valid) &&
                                        (((x_9).victim_addr) == (x_0)))
                                        begin
                                        victimRegs___0_0 <= update (x_1,
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
    method Action rdReq_infoRam___0_0__15 (Bit#(10) x_0);
    method Action wrReq_infoRam___0_0__15 (Struct29 x_0);
    method ActionValue#(Struct24) rdResp_infoRam___0_0__15 ();
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
    
    method Action rdReq_infoRam___0_0__15 (Bit#(10) x_0) if(initDone);
        bram.rdReq(x_0);
    endmethod
    
    method Action wrReq_infoRam___0_0__15 (Struct29 x_0) if(initDone);
        bram.wrReq(x_0.addr, x_0.datain);
    endmethod
    
    method ActionValue#(Struct24) rdResp_infoRam___0_0__15 () if(initDone);
        bram.deqRdResp ();
        let data = bram.rdResp ();
        return data;
    endmethod
    

endmodule

interface Module9;
    method Action rdReq_infoRam___0_0__14 (Bit#(10) x_0);
    method Action wrReq_infoRam___0_0__14 (Struct29 x_0);
    method ActionValue#(Struct24) rdResp_infoRam___0_0__14 ();
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
    
    method Action rdReq_infoRam___0_0__14 (Bit#(10) x_0) if(initDone);
        bram.rdReq(x_0);
    endmethod
    
    method Action wrReq_infoRam___0_0__14 (Struct29 x_0) if(initDone);
        bram.wrReq(x_0.addr, x_0.datain);
    endmethod
    
    method ActionValue#(Struct24) rdResp_infoRam___0_0__14 () if(initDone);
        bram.deqRdResp ();
        let data = bram.rdResp ();
        return data;
    endmethod
    

endmodule

interface Module10;
    method Action rdReq_infoRam___0_0__13 (Bit#(10) x_0);
    method Action wrReq_infoRam___0_0__13 (Struct29 x_0);
    method ActionValue#(Struct24) rdResp_infoRam___0_0__13 ();
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
    
    method Action rdReq_infoRam___0_0__13 (Bit#(10) x_0) if(initDone);
        bram.rdReq(x_0);
    endmethod
    
    method Action wrReq_infoRam___0_0__13 (Struct29 x_0) if(initDone);
        bram.wrReq(x_0.addr, x_0.datain);
    endmethod
    
    method ActionValue#(Struct24) rdResp_infoRam___0_0__13 () if(initDone);
        bram.deqRdResp ();
        let data = bram.rdResp ();
        return data;
    endmethod
    

endmodule

interface Module11;
    method Action rdReq_infoRam___0_0__12 (Bit#(10) x_0);
    method Action wrReq_infoRam___0_0__12 (Struct29 x_0);
    method ActionValue#(Struct24) rdResp_infoRam___0_0__12 ();
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
    
    method Action rdReq_infoRam___0_0__12 (Bit#(10) x_0) if(initDone);
        bram.rdReq(x_0);
    endmethod
    
    method Action wrReq_infoRam___0_0__12 (Struct29 x_0) if(initDone);
        bram.wrReq(x_0.addr, x_0.datain);
    endmethod
    
    method ActionValue#(Struct24) rdResp_infoRam___0_0__12 () if(initDone);
        bram.deqRdResp ();
        let data = bram.rdResp ();
        return data;
    endmethod
    

endmodule

interface Module12;
    method Action rdReq_infoRam___0_0__11 (Bit#(10) x_0);
    method Action wrReq_infoRam___0_0__11 (Struct29 x_0);
    method ActionValue#(Struct24) rdResp_infoRam___0_0__11 ();
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
    
    method Action rdReq_infoRam___0_0__11 (Bit#(10) x_0) if(initDone);
        bram.rdReq(x_0);
    endmethod
    
    method Action wrReq_infoRam___0_0__11 (Struct29 x_0) if(initDone);
        bram.wrReq(x_0.addr, x_0.datain);
    endmethod
    
    method ActionValue#(Struct24) rdResp_infoRam___0_0__11 () if(initDone);
        bram.deqRdResp ();
        let data = bram.rdResp ();
        return data;
    endmethod
    

endmodule

interface Module13;
    method Action rdReq_infoRam___0_0__10 (Bit#(10) x_0);
    method Action wrReq_infoRam___0_0__10 (Struct29 x_0);
    method ActionValue#(Struct24) rdResp_infoRam___0_0__10 ();
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
    
    method Action rdReq_infoRam___0_0__10 (Bit#(10) x_0) if(initDone);
        bram.rdReq(x_0);
    endmethod
    
    method Action wrReq_infoRam___0_0__10 (Struct29 x_0) if(initDone);
        bram.wrReq(x_0.addr, x_0.datain);
    endmethod
    
    method ActionValue#(Struct24) rdResp_infoRam___0_0__10 () if(initDone);
        bram.deqRdResp ();
        let data = bram.rdResp ();
        return data;
    endmethod
    

endmodule

interface Module14;
    method Action rdReq_infoRam___0_0__9 (Bit#(10) x_0);
    method Action wrReq_infoRam___0_0__9 (Struct29 x_0);
    method ActionValue#(Struct24) rdResp_infoRam___0_0__9 ();
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
    
    method Action rdReq_infoRam___0_0__9 (Bit#(10) x_0) if(initDone);
        bram.rdReq(x_0);
    endmethod
    
    method Action wrReq_infoRam___0_0__9 (Struct29 x_0) if(initDone);
        bram.wrReq(x_0.addr, x_0.datain);
    endmethod
    
    method ActionValue#(Struct24) rdResp_infoRam___0_0__9 () if(initDone);
        bram.deqRdResp ();
        let data = bram.rdResp ();
        return data;
    endmethod
    

endmodule

interface Module15;
    method Action rdReq_infoRam___0_0__8 (Bit#(10) x_0);
    method Action wrReq_infoRam___0_0__8 (Struct29 x_0);
    method ActionValue#(Struct24) rdResp_infoRam___0_0__8 ();
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
    
    method Action rdReq_infoRam___0_0__8 (Bit#(10) x_0) if(initDone);
        bram.rdReq(x_0);
    endmethod
    
    method Action wrReq_infoRam___0_0__8 (Struct29 x_0) if(initDone);
        bram.wrReq(x_0.addr, x_0.datain);
    endmethod
    
    method ActionValue#(Struct24) rdResp_infoRam___0_0__8 () if(initDone);
        bram.deqRdResp ();
        let data = bram.rdResp ();
        return data;
    endmethod
    

endmodule

interface Module16;
    method Action rdReq_infoRam___0_0__7 (Bit#(10) x_0);
    method Action wrReq_infoRam___0_0__7 (Struct29 x_0);
    method ActionValue#(Struct24) rdResp_infoRam___0_0__7 ();
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
    
    method Action rdReq_infoRam___0_0__7 (Bit#(10) x_0) if(initDone);
        bram.rdReq(x_0);
    endmethod
    
    method Action wrReq_infoRam___0_0__7 (Struct29 x_0) if(initDone);
        bram.wrReq(x_0.addr, x_0.datain);
    endmethod
    
    method ActionValue#(Struct24) rdResp_infoRam___0_0__7 () if(initDone);
        bram.deqRdResp ();
        let data = bram.rdResp ();
        return data;
    endmethod
    

endmodule

interface Module17;
    method Action rdReq_infoRam___0_0__6 (Bit#(10) x_0);
    method Action wrReq_infoRam___0_0__6 (Struct29 x_0);
    method ActionValue#(Struct24) rdResp_infoRam___0_0__6 ();
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
    
    method Action rdReq_infoRam___0_0__6 (Bit#(10) x_0) if(initDone);
        bram.rdReq(x_0);
    endmethod
    
    method Action wrReq_infoRam___0_0__6 (Struct29 x_0) if(initDone);
        bram.wrReq(x_0.addr, x_0.datain);
    endmethod
    
    method ActionValue#(Struct24) rdResp_infoRam___0_0__6 () if(initDone);
        bram.deqRdResp ();
        let data = bram.rdResp ();
        return data;
    endmethod
    

endmodule

interface Module18;
    method Action rdReq_infoRam___0_0__5 (Bit#(10) x_0);
    method Action wrReq_infoRam___0_0__5 (Struct29 x_0);
    method ActionValue#(Struct24) rdResp_infoRam___0_0__5 ();
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
    
    method Action rdReq_infoRam___0_0__5 (Bit#(10) x_0) if(initDone);
        bram.rdReq(x_0);
    endmethod
    
    method Action wrReq_infoRam___0_0__5 (Struct29 x_0) if(initDone);
        bram.wrReq(x_0.addr, x_0.datain);
    endmethod
    
    method ActionValue#(Struct24) rdResp_infoRam___0_0__5 () if(initDone);
        bram.deqRdResp ();
        let data = bram.rdResp ();
        return data;
    endmethod
    

endmodule

interface Module19;
    method Action rdReq_infoRam___0_0__4 (Bit#(10) x_0);
    method Action wrReq_infoRam___0_0__4 (Struct29 x_0);
    method ActionValue#(Struct24) rdResp_infoRam___0_0__4 ();
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
    
    method Action rdReq_infoRam___0_0__4 (Bit#(10) x_0) if(initDone);
        bram.rdReq(x_0);
    endmethod
    
    method Action wrReq_infoRam___0_0__4 (Struct29 x_0) if(initDone);
        bram.wrReq(x_0.addr, x_0.datain);
    endmethod
    
    method ActionValue#(Struct24) rdResp_infoRam___0_0__4 () if(initDone);
        bram.deqRdResp ();
        let data = bram.rdResp ();
        return data;
    endmethod
    

endmodule

interface Module20;
    method Action rdReq_infoRam___0_0__3 (Bit#(10) x_0);
    method Action wrReq_infoRam___0_0__3 (Struct29 x_0);
    method ActionValue#(Struct24) rdResp_infoRam___0_0__3 ();
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
    
    method Action rdReq_infoRam___0_0__3 (Bit#(10) x_0) if(initDone);
        bram.rdReq(x_0);
    endmethod
    
    method Action wrReq_infoRam___0_0__3 (Struct29 x_0) if(initDone);
        bram.wrReq(x_0.addr, x_0.datain);
    endmethod
    
    method ActionValue#(Struct24) rdResp_infoRam___0_0__3 () if(initDone);
        bram.deqRdResp ();
        let data = bram.rdResp ();
        return data;
    endmethod
    

endmodule

interface Module21;
    method Action rdReq_infoRam___0_0__2 (Bit#(10) x_0);
    method Action wrReq_infoRam___0_0__2 (Struct29 x_0);
    method ActionValue#(Struct24) rdResp_infoRam___0_0__2 ();
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
    
    method Action rdReq_infoRam___0_0__2 (Bit#(10) x_0) if(initDone);
        bram.rdReq(x_0);
    endmethod
    
    method Action wrReq_infoRam___0_0__2 (Struct29 x_0) if(initDone);
        bram.wrReq(x_0.addr, x_0.datain);
    endmethod
    
    method ActionValue#(Struct24) rdResp_infoRam___0_0__2 () if(initDone);
        bram.deqRdResp ();
        let data = bram.rdResp ();
        return data;
    endmethod
    

endmodule

interface Module22;
    method Action rdReq_infoRam___0_0__1 (Bit#(10) x_0);
    method Action wrReq_infoRam___0_0__1 (Struct29 x_0);
    method ActionValue#(Struct24) rdResp_infoRam___0_0__1 ();
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
    
    method Action rdReq_infoRam___0_0__1 (Bit#(10) x_0) if(initDone);
        bram.rdReq(x_0);
    endmethod
    
    method Action wrReq_infoRam___0_0__1 (Struct29 x_0) if(initDone);
        bram.wrReq(x_0.addr, x_0.datain);
    endmethod
    
    method ActionValue#(Struct24) rdResp_infoRam___0_0__1 () if(initDone);
        bram.deqRdResp ();
        let data = bram.rdResp ();
        return data;
    endmethod
    

endmodule

interface Module23;
    method Action rdReq_infoRam___0_0__0 (Bit#(10) x_0);
    method Action wrReq_infoRam___0_0__0 (Struct29 x_0);
    method ActionValue#(Struct24) rdResp_infoRam___0_0__0 ();
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
    
    method Action rdReq_infoRam___0_0__0 (Bit#(10) x_0) if(initDone);
        bram.rdReq(x_0);
    endmethod
    
    method Action wrReq_infoRam___0_0__0 (Struct29 x_0) if(initDone);
        bram.wrReq(x_0.addr, x_0.datain);
    endmethod
    
    method ActionValue#(Struct24) rdResp_infoRam___0_0__0 () if(initDone);
        bram.deqRdResp ();
        let data = bram.rdResp ();
        return data;
    endmethod
    

endmodule

interface Module24;
    method Action rdReq_edirRam___0_0__7 (Bit#(10) x_0);
    method Action wrReq_edirRam___0_0__7 (Struct31 x_0);
    method ActionValue#(Struct26) rdResp_edirRam___0_0__7 ();
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
    
    method Action rdReq_edirRam___0_0__7 (Bit#(10) x_0) if(initDone);
        bram.rdReq(x_0);
    endmethod
    
    method Action wrReq_edirRam___0_0__7 (Struct31 x_0) if(initDone);
        bram.wrReq(x_0.addr, x_0.datain);
    endmethod
    
    method ActionValue#(Struct26) rdResp_edirRam___0_0__7 () if(initDone);
        bram.deqRdResp ();
        let data = bram.rdResp ();
        return data;
    endmethod
    

endmodule

interface Module25;
    method Action rdReq_edirRam___0_0__6 (Bit#(10) x_0);
    method Action wrReq_edirRam___0_0__6 (Struct31 x_0);
    method ActionValue#(Struct26) rdResp_edirRam___0_0__6 ();
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
    
    method Action rdReq_edirRam___0_0__6 (Bit#(10) x_0) if(initDone);
        bram.rdReq(x_0);
    endmethod
    
    method Action wrReq_edirRam___0_0__6 (Struct31 x_0) if(initDone);
        bram.wrReq(x_0.addr, x_0.datain);
    endmethod
    
    method ActionValue#(Struct26) rdResp_edirRam___0_0__6 () if(initDone);
        bram.deqRdResp ();
        let data = bram.rdResp ();
        return data;
    endmethod
    

endmodule

interface Module26;
    method Action rdReq_edirRam___0_0__5 (Bit#(10) x_0);
    method Action wrReq_edirRam___0_0__5 (Struct31 x_0);
    method ActionValue#(Struct26) rdResp_edirRam___0_0__5 ();
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
    
    method Action rdReq_edirRam___0_0__5 (Bit#(10) x_0) if(initDone);
        bram.rdReq(x_0);
    endmethod
    
    method Action wrReq_edirRam___0_0__5 (Struct31 x_0) if(initDone);
        bram.wrReq(x_0.addr, x_0.datain);
    endmethod
    
    method ActionValue#(Struct26) rdResp_edirRam___0_0__5 () if(initDone);
        bram.deqRdResp ();
        let data = bram.rdResp ();
        return data;
    endmethod
    

endmodule

interface Module27;
    method Action rdReq_edirRam___0_0__4 (Bit#(10) x_0);
    method Action wrReq_edirRam___0_0__4 (Struct31 x_0);
    method ActionValue#(Struct26) rdResp_edirRam___0_0__4 ();
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
    
    method Action rdReq_edirRam___0_0__4 (Bit#(10) x_0) if(initDone);
        bram.rdReq(x_0);
    endmethod
    
    method Action wrReq_edirRam___0_0__4 (Struct31 x_0) if(initDone);
        bram.wrReq(x_0.addr, x_0.datain);
    endmethod
    
    method ActionValue#(Struct26) rdResp_edirRam___0_0__4 () if(initDone);
        bram.deqRdResp ();
        let data = bram.rdResp ();
        return data;
    endmethod
    

endmodule

interface Module28;
    method Action rdReq_edirRam___0_0__3 (Bit#(10) x_0);
    method Action wrReq_edirRam___0_0__3 (Struct31 x_0);
    method ActionValue#(Struct26) rdResp_edirRam___0_0__3 ();
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
    
    method Action rdReq_edirRam___0_0__3 (Bit#(10) x_0) if(initDone);
        bram.rdReq(x_0);
    endmethod
    
    method Action wrReq_edirRam___0_0__3 (Struct31 x_0) if(initDone);
        bram.wrReq(x_0.addr, x_0.datain);
    endmethod
    
    method ActionValue#(Struct26) rdResp_edirRam___0_0__3 () if(initDone);
        bram.deqRdResp ();
        let data = bram.rdResp ();
        return data;
    endmethod
    

endmodule

interface Module29;
    method Action rdReq_edirRam___0_0__2 (Bit#(10) x_0);
    method Action wrReq_edirRam___0_0__2 (Struct31 x_0);
    method ActionValue#(Struct26) rdResp_edirRam___0_0__2 ();
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
    
    method Action rdReq_edirRam___0_0__2 (Bit#(10) x_0) if(initDone);
        bram.rdReq(x_0);
    endmethod
    
    method Action wrReq_edirRam___0_0__2 (Struct31 x_0) if(initDone);
        bram.wrReq(x_0.addr, x_0.datain);
    endmethod
    
    method ActionValue#(Struct26) rdResp_edirRam___0_0__2 () if(initDone);
        bram.deqRdResp ();
        let data = bram.rdResp ();
        return data;
    endmethod
    

endmodule

interface Module30;
    method Action rdReq_edirRam___0_0__1 (Bit#(10) x_0);
    method Action wrReq_edirRam___0_0__1 (Struct31 x_0);
    method ActionValue#(Struct26) rdResp_edirRam___0_0__1 ();
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
    
    method Action rdReq_edirRam___0_0__1 (Bit#(10) x_0) if(initDone);
        bram.rdReq(x_0);
    endmethod
    
    method Action wrReq_edirRam___0_0__1 (Struct31 x_0) if(initDone);
        bram.wrReq(x_0.addr, x_0.datain);
    endmethod
    
    method ActionValue#(Struct26) rdResp_edirRam___0_0__1 () if(initDone);
        bram.deqRdResp ();
        let data = bram.rdResp ();
        return data;
    endmethod
    

endmodule

interface Module31;
    method Action rdReq_edirRam___0_0__0 (Bit#(10) x_0);
    method Action wrReq_edirRam___0_0__0 (Struct31 x_0);
    method ActionValue#(Struct26) rdResp_edirRam___0_0__0 ();
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
    
    method Action rdReq_edirRam___0_0__0 (Bit#(10) x_0) if(initDone);
        bram.rdReq(x_0);
    endmethod
    
    method Action wrReq_edirRam___0_0__0 (Struct31 x_0) if(initDone);
        bram.wrReq(x_0.addr, x_0.datain);
    endmethod
    
    method ActionValue#(Struct26) rdResp_edirRam___0_0__0 () if(initDone);
        bram.deqRdResp ();
        let data = bram.rdResp ();
        return data;
    endmethod
    

endmodule

interface Module32;
    method Action rdReq_dataRam___0_0 (Bit#(14) x_0);
    method Action wrReq_dataRam___0_0 (Struct32 x_0);
    method ActionValue#(Vector#(4, Bit#(64))) rdResp_dataRam___0_0 ();
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
    
    method Action rdReq_dataRam___0_0 (Bit#(14) x_0) if(initDone);
        bram.rdReq(x_0);
    endmethod
    
    method Action wrReq_dataRam___0_0 (Struct32 x_0) if(initDone);
        bram.wrReq(x_0.addr, x_0.datain);
    endmethod
    
    method ActionValue#(Vector#(4, Bit#(64))) rdResp_dataRam___0_0 ()
    if(initDone);
        bram.deqRdResp ();
        let data = bram.rdResp ();
        return data;
    endmethod
    

endmodule

interface Module33;
    method Action rdReq_repRam___0_0 (Bit#(10) x_0);
    method Action wrReq_repRam___0_0 (Struct34 x_0);
    method ActionValue#(Vector#(16, Bit#(8))) rdResp_repRam___0_0 ();
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
    
    method Action rdReq_repRam___0_0 (Bit#(10) x_0) if(initDone);
        bram.rdReq(x_0);
    endmethod
    
    method Action wrReq_repRam___0_0 (Struct34 x_0) if(initDone);
        bram.wrReq(x_0.addr, x_0.datain);
    endmethod
    
    method ActionValue#(Vector#(16, Bit#(8))) rdResp_repRam___0_0 ()
    if(initDone);
        bram.deqRdResp ();
        let data = bram.rdResp ();
        return data;
    endmethod
    

endmodule

interface Module34;
    method ActionValue#(Struct14) getMSHR__0_0 (Bit#(3) x_0);
    method ActionValue#(Struct1) getMSHRRq__0_0 (Bit#(3) x_0);
    method ActionValue#(Struct1) getMSHRFirstRs__0_0 (Bit#(3) x_0);
    method ActionValue#(Struct4) getPRqSlot__0_0 (Struct3 x_0);
    method ActionValue#(Struct4) getCRqSlot__0_0 (Struct3 x_0);
    method ActionValue#(Struct3) getWait__0_0 ();
    method Action registerUL__0_0 (Struct19 x_0);
    method Action registerDL__0_0 (Struct20 x_0);
    method Action canImm__0_0 (Bit#(64) x_0);
    method Action setULImm__0_0 (Struct1 x_0);
    method Action transferUpDown__0_0 (Struct23 x_0);
    method Action addRs__0_0 (Struct7 x_0);
    method ActionValue#(Bit#(3)) getULReady__0_0 (Bit#(64) x_0);
    method ActionValue#(Struct8) getDLReady__0_0 ();
    method Action startRelease__0_0 (Bit#(3) x_0);
    method Action releaseMSHR__0_0 (Bit#(3) x_0);
endinterface

module mkModule34
    (Module34);
    Reg#(Vector#(8, Struct14)) mshrs__0_0 <- mkReg(unpack(0));
    Reg#(Vector#(8, Bit#(64))) maddrs__0_0 <- mkReg(unpack(0));
    Reg#(Vector#(8, Bit#(3))) msts__0_0 <- mkReg(unpack(0));
    Reg#(Vector#(8, Struct5)) mnexts__0_0 <- mkReg(unpack(0));
    Reg#(Vector#(8, Struct1)) rqs__0_0 <- mkReg(unpack(0));
    Reg#(Vector#(8, Struct1)) rss__0_0 <- mkReg(unpack(0));
    
    // No rules in this module
    
    method ActionValue#(Struct14) getMSHR__0_0 (Bit#(3) x_0);
        let x_1 = (mshrs__0_0);
        return (x_1)[x_0];
    endmethod
    
    method ActionValue#(Struct1) getMSHRRq__0_0 (Bit#(3) x_0);
        let x_1 = (rqs__0_0);
        return (x_1)[x_0];
    endmethod
    
    method ActionValue#(Struct1) getMSHRFirstRs__0_0 (Bit#(3) x_0);
        let x_1 = (rss__0_0);
        return (x_1)[x_0];
    endmethod
    
    method ActionValue#(Struct4) getPRqSlot__0_0 (Struct3 x_0);
        let x_1 = (mshrs__0_0);
        let x_2 = (maddrs__0_0);
        let x_3 = (msts__0_0);
        let x_4 = (mnexts__0_0);
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
            mshrs__0_0 <= update (x_1, x_7, Struct14 {m_is_ul : unpack(0),
            m_qidx : (x_0).r_msg_from, m_rsb : unpack(0), m_dl_rss_from :
            unpack(0), m_dl_rss_recv : unpack(0)});
            maddrs__0_0 <= update (x_2, x_7, ((x_0).r_msg).addr);
            msts__0_0 <= update (x_3, x_7, (x_11 ? ((Bit#(3))'(3'h1)) :
            ((Bit#(3))'(3'h4))));
            let x_13 = (rqs__0_0);
            rqs__0_0 <= update (x_13, x_7,
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
                mnexts__0_0 <= update (x_4, x_14, Struct5 {valid :
                (Bool)'(True), data : x_7});
            end else begin
                
            end
        end else begin
            
        end
        return x_12;
    endmethod
    
    method ActionValue#(Struct4) getCRqSlot__0_0 (Struct3 x_0);
        let x_1 = (mshrs__0_0);
        let x_2 = (maddrs__0_0);
        let x_3 = (msts__0_0);
        let x_4 = (mnexts__0_0);
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
            mshrs__0_0 <= update (x_1, x_7, Struct14 {m_is_ul : unpack(0),
            m_qidx : (x_0).r_msg_from, m_rsb : unpack(0), m_dl_rss_from :
            unpack(0), m_dl_rss_recv : unpack(0)});
            maddrs__0_0 <= update (x_2, x_7, ((x_0).r_msg).addr);
            msts__0_0 <= update (x_3, x_7, (x_14 ? ((Bit#(3))'(3'h1)) :
            ((Bit#(3))'(3'h4))));
            let x_16 = (rqs__0_0);
            rqs__0_0 <= update (x_16, x_7,
            (x_0).r_msg);
            if (x_14) begin
                Bit#(3) x_17 = ((x_12 ? ((x_10).data) :
                ((x_11).data)));
                Struct5 x_18 = ((x_4)[x_17]);
                mnexts__0_0 <= update (x_4, x_17, Struct5 {valid :
                (Bool)'(True), data : x_7});
            end else begin
                
            end
        end else begin
            
        end
        return x_15;
    endmethod
    
    method ActionValue#(Struct3) getWait__0_0 ();
        let x_1 = (mshrs__0_0);
        let x_2 = (maddrs__0_0);
        let x_3 = (msts__0_0);
        let x_4 = (rqs__0_0);
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
        msts__0_0 <= update (x_3, x_6, (Bit#(3))'(3'h4));
        Struct3 x_11 = (Struct3 {r_id : x_6, r_msg : x_9, r_msg_from :
        (x_7).m_qidx});
        return x_11;
    endmethod
    
    method Action registerUL__0_0 (Struct19 x_0);
        let x_1 = (mshrs__0_0);
        let x_2 = (msts__0_0);
        Bit#(3) x_3 = ((x_0).r_id);
        mshrs__0_0 <= update (x_1, x_3, Struct14 {m_is_ul : (Bool)'(True),
        m_qidx : {((Bit#(2))'(2'h2)),((x_0).r_ul_rsbTo)}, m_rsb :
        (x_0).r_ul_rsb, m_dl_rss_from : unpack(0), m_dl_rss_recv :
        unpack(0)});
        msts__0_0 <= update (x_2, x_3, (Bit#(3))'(3'h5));
    endmethod
    
    method Action registerDL__0_0 (Struct20 x_0);
        let x_1 = (mshrs__0_0);
        let x_2 = (msts__0_0);
        Bit#(3) x_3 = ((x_0).r_id);
        mshrs__0_0 <= update (x_1, x_3, Struct14 {m_is_ul : (Bool)'(False),
        m_qidx : (x_0).r_dl_rsbTo, m_rsb : (x_0).r_dl_rsb, m_dl_rss_from :
        (x_0).r_dl_rss_from, m_dl_rss_recv : unpack(0)});
        msts__0_0 <= update (x_2, x_3, (Bit#(3))'(3'h5));
    endmethod
    
    method Action canImm__0_0 (Bit#(64) x_0);
        let x_1 = (maddrs__0_0);
        let x_2 = (msts__0_0);
        let x_3 = (mnexts__0_0);
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
    
    method Action setULImm__0_0 (Struct1 x_0);
        let x_1 = (mshrs__0_0);
        let x_2 = (maddrs__0_0);
        let x_3 = (msts__0_0);
        let x_4 = (rqs__0_0);
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
        mshrs__0_0 <= update (x_1, x_6, Struct14 {m_is_ul : (Bool)'(True),
        m_qidx : unpack(0), m_rsb : (Bool)'(False), m_dl_rss_from :
        unpack(0), m_dl_rss_recv : unpack(0)});
        maddrs__0_0 <= update (x_2, x_6, (x_0).addr);
        msts__0_0 <= update (x_3, x_6, (Bit#(3))'(3'h5));
        rqs__0_0 <= update (x_4, x_6, x_0);
    endmethod
    
    method Action transferUpDown__0_0 (Struct23 x_0);
        let x_1 = (mshrs__0_0);
        let x_2 = (msts__0_0);
        Bit#(3) x_3 = ((x_0).r_id);
        Struct14 x_4 = ((x_1)[x_3]);
        mshrs__0_0 <= update (x_1, x_3, Struct14 {m_is_ul : (Bool)'(False),
        m_qidx : (x_4).m_qidx, m_rsb : (x_4).m_rsb, m_dl_rss_from :
        (x_0).r_dl_rss_from, m_dl_rss_recv : unpack(0)});
        msts__0_0 <= update (x_2, x_3, (Bit#(3))'(3'h5));
    endmethod
    
    method Action addRs__0_0 (Struct7 x_0);
        let x_1 = (mshrs__0_0);
        let x_2 = (maddrs__0_0);
        let x_3 = (msts__0_0);
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
        mshrs__0_0 <= update (x_1, x_6, Struct14 {m_is_ul : (x_7).m_is_ul,
        m_qidx : (x_7).m_qidx, m_rsb : (x_7).m_rsb, m_dl_rss_from :
        (x_7).m_dl_rss_from, m_dl_rss_recv : ((x_7).m_dl_rss_recv) |
        (((Bit#(4))'(4'h1)) << ((x_0).r_midx))});
        let x_8 = (rss__0_0);
        Struct1 x_9 = ((x_8)[x_6]);
        rss__0_0 <= update (x_8, x_6, (x_0).r_msg);
    endmethod
    
    method ActionValue#(Bit#(3)) getULReady__0_0 (Bit#(64) x_0);
        let x_1 = (mshrs__0_0);
        let x_2 = (maddrs__0_0);
        let x_3 = (msts__0_0);
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
    
    method ActionValue#(Struct8) getDLReady__0_0 ();
        let x_1 = (mshrs__0_0);
        let x_2 = (maddrs__0_0);
        let x_3 = (msts__0_0);
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
    
    method Action startRelease__0_0 (Bit#(3) x_0);
        let x_1 = (msts__0_0);
        msts__0_0 <= update (x_1, x_0, (Bit#(3))'(3'h6));
    endmethod
    
    method Action releaseMSHR__0_0 (Bit#(3) x_0);
        let x_1 = (mshrs__0_0);
        let x_2 = (msts__0_0);
        let x_3 = (mnexts__0_0);
        mshrs__0_0 <= update (x_1, x_0, unpack(0));
        mnexts__0_0 <= update (x_3, x_0, unpack(0));
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
        msts__0_0 <= x_8;
    endmethod
endmodule

interface Module35;
    method Action enq_fifoCRqInput__0_0_0 (Struct2 x_0);
    method ActionValue#(Struct2) deq_fifoCRqInput__0_0_0 ();
endinterface

module mkModule35 (Module35);
    FIFOF#(Struct2) pff <- mkSizedFIFOF(4);
    
    method Action enq_fifoCRqInput__0_0_0 (Struct2 x_0);
        pff.enq(x_0);
    endmethod
    
    method ActionValue#(Struct2) deq_fifoCRqInput__0_0_0 ();
        pff.deq();
        return pff.first();
    endmethod

endmodule

interface Module36;
    method Action enq_fifoPInput__0_0_0 (Struct2 x_0);
    method ActionValue#(Struct2) deq_fifoPInput__0_0_0 ();
endinterface

module mkModule36 (Module36);
    FIFOF#(Struct2) pff <- mkSizedFIFOF(4);
    
    method Action enq_fifoPInput__0_0_0 (Struct2 x_0);
        pff.enq(x_0);
    endmethod
    
    method ActionValue#(Struct2) deq_fifoPInput__0_0_0 ();
        pff.deq();
        return pff.first();
    endmethod

endmodule

interface Module37;
    method Action enq_fifoN2I__0_0_0 (Struct38 x_0);
    method ActionValue#(Struct38) deq_fifoN2I__0_0_0 ();
endinterface

module mkModule37 (Module37);
    FIFOF#(Struct38) pff <- mkPipelineFIFOF();
    
    method Action enq_fifoN2I__0_0_0 (Struct38 x_0);
        pff.enq(x_0);
    endmethod
    
    method ActionValue#(Struct38) deq_fifoN2I__0_0_0 ();
        pff.deq();
        return pff.first();
    endmethod

endmodule

interface Module38;
    method Action enq_fifoI2L__0_0_0 (Struct38 x_0);
    method ActionValue#(Struct38) deq_fifoI2L__0_0_0 ();
endinterface

module mkModule38 (Module38);
    FIFOF#(Struct38) pff <- mkPipelineFIFOF();
    
    method Action enq_fifoI2L__0_0_0 (Struct38 x_0);
        pff.enq(x_0);
    endmethod
    
    method ActionValue#(Struct38) deq_fifoI2L__0_0_0 ();
        pff.deq();
        return pff.first();
    endmethod

endmodule

interface Module39;
    method Action enq_fifoL2E__0_0_0 (Struct41 x_0);
    method ActionValue#(Struct41) deq_fifoL2E__0_0_0 ();
endinterface

module mkModule39 (Module39);
    FIFOF#(Struct41) pff <- mkPipelineFIFOF();
    
    method Action enq_fifoL2E__0_0_0 (Struct41 x_0);
        pff.enq(x_0);
    endmethod
    
    method ActionValue#(Struct41) deq_fifoL2E__0_0_0 ();
        pff.deq();
        return pff.first();
    endmethod

endmodule

interface Module40;
    method Action enq_fifo_0_0_0_0 (Struct1 x_0);
    method ActionValue#(Struct1) deq_fifo_0_0_0_0 ();
endinterface

module mkModule40 (Module40);
    FIFOF#(Struct1) pff <- mkSizedFIFOF(2);
    
    method Action enq_fifo_0_0_0_0 (Struct1 x_0);
        pff.enq(x_0);
    endmethod
    
    method ActionValue#(Struct1) deq_fifo_0_0_0_0 ();
        pff.deq();
        return pff.first();
    endmethod

endmodule

interface Module41;
    method Action enq_fifo_0_0_0_1 (Struct1 x_0);
    method ActionValue#(Struct1) deq_fifo_0_0_0_1 ();
endinterface

module mkModule41 (Module41);
    FIFOF#(Struct1) pff <- mkSizedFIFOF(2);
    
    method Action enq_fifo_0_0_0_1 (Struct1 x_0);
        pff.enq(x_0);
    endmethod
    
    method ActionValue#(Struct1) deq_fifo_0_0_0_1 ();
        pff.deq();
        return pff.first();
    endmethod

endmodule

interface Module42;
    method Action enq_fifo_0_0_0_2 (Struct1 x_0);
    method ActionValue#(Struct1) deq_fifo_0_0_0_2 ();
endinterface

module mkModule42 (Module42);
    FIFOF#(Struct1) pff <- mkSizedFIFOF(2);
    
    method Action enq_fifo_0_0_0_2 (Struct1 x_0);
        pff.enq(x_0);
    endmethod
    
    method ActionValue#(Struct1) deq_fifo_0_0_0_2 ();
        pff.deq();
        return pff.first();
    endmethod

endmodule

interface Module43;
    method Action enq_fifo_0_0_0_0_0 (Struct1 x_0);
    method ActionValue#(Struct1) deq_fifo_0_0_0_0_0 ();
endinterface

module mkModule43 (Module43);
    FIFOF#(Struct1) pff <- mkSizedFIFOF(2);
    
    method Action enq_fifo_0_0_0_0_0 (Struct1 x_0);
        pff.enq(x_0);
    endmethod
    
    method ActionValue#(Struct1) deq_fifo_0_0_0_0_0 ();
        pff.deq();
        return pff.first();
    endmethod

endmodule

interface Module44;
    method Action enq_fifo_0_0_0_0_2 (Struct1 x_0);
    method ActionValue#(Struct1) deq_fifo_0_0_0_0_2 ();
endinterface

module mkModule44 (Module44);
    FIFOF#(Struct1) pff <- mkSizedFIFOF(2);
    
    method Action enq_fifo_0_0_0_0_2 (Struct1 x_0);
        pff.enq(x_0);
    endmethod
    
    method ActionValue#(Struct1) deq_fifo_0_0_0_0_2 ();
        pff.deq();
        return pff.first();
    endmethod

endmodule

interface Module45;
    method ActionValue#(Struct37) victims___0_0_0__findVictim (Bit#(64) x_0);
    method ActionValue#(Struct13) victims___0_0_0__getVictim (Bit#(1) x_0);
    method Action victims___0_0_0__setVictim (Struct44 x_0);
    method Action victims___0_0_0__registerVictim (Struct13 x_0);
    method ActionValue#(Struct13) victims___0_0_0__getFirstVictim ();
    method ActionValue#(Bool) victims___0_0_0__hasVictim ();
    method Action victims___0_0_0__setVictimRq (Bit#(64) x_0);
    method Action victims___0_0_0__releaseVictim (Bit#(64) x_0);
endinterface

module mkModule45
    (Module45);
    Reg#(Vector#(2, Struct13)) victimRegs___0_0_0 <- mkReg(unpack(0));
    
    // No rules in this module
    
    method ActionValue#(Struct37) victims___0_0_0__findVictim (Bit#(64) x_0);
        let x_1 = (victimRegs___0_0_0);
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
    
    method ActionValue#(Struct13) victims___0_0_0__getVictim (Bit#(1) x_0);
        let x_1 = (victimRegs___0_0_0);
        return (x_1)[x_0];
    endmethod
    
    method Action victims___0_0_0__setVictim (Struct44 x_0);
        let x_1 = (victimRegs___0_0_0);
        Struct13 x_2 = ((x_1)[(x_0).victim_idx]);
        Struct13 x_3 = (Struct13 {victim_valid : (Bool)'(True), victim_addr :
        (x_2).victim_addr, victim_info : (x_0).victim_info, victim_value :
        (x_0).victim_value, victim_req :
        (x_2).victim_req});
        victimRegs___0_0_0 <= update (x_1, (x_0).victim_idx, x_3);
    endmethod
    
    method Action victims___0_0_0__registerVictim (Struct13 x_0);
        let x_1 = (victimRegs___0_0_0);
        Struct37 x_2 = ((((x_1)[(Bit#(1))'(1'h1)]).victim_valid ?
        ((((x_1)[(Bit#(1))'(1'h0)]).victim_valid ? (Struct37 {valid :
        (Bool)'(False), data : unpack(0)}) : (Struct37 {valid :
        (Bool)'(True), data : (Bit#(1))'(1'h0)}))) : (Struct37 {valid :
        (Bool)'(True), data : (Bit#(1))'(1'h1)})));
        when ((x_2).valid, noAction);
        Bit#(1) x_3 = ((x_2).data);
        victimRegs___0_0_0 <= update (x_1, x_3, x_0);
    endmethod
    
    method ActionValue#(Struct13) victims___0_0_0__getFirstVictim ();
        let x_1 = (victimRegs___0_0_0);
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
    
    method ActionValue#(Bool) victims___0_0_0__hasVictim ();
        let x_1 = (victimRegs___0_0_0);
        Bool x_2 = (((((x_1)[(Bit#(1))'(1'h1)]).victim_valid) && (!
        (((x_1)[(Bit#(1))'(1'h1)]).victim_req)) ? ((Bool)'(True)) :
        (((((x_1)[(Bit#(1))'(1'h0)]).victim_valid) && (!
        (((x_1)[(Bit#(1))'(1'h0)]).victim_req)) ? ((Bool)'(True)) :
        ((Bool)'(False))))));
        return x_2;
    endmethod
    
    method Action victims___0_0_0__setVictimRq (Bit#(64) x_0);
        let x_1 = (victimRegs___0_0_0);
        Struct13 x_2 =
        ((x_1)[(Bit#(1))'(1'h1)]);
        if (((x_2).victim_valid) && (((x_2).victim_addr) == (x_0)))
            begin
            Struct13 x_3 = (Struct13 {victim_valid : (x_2).victim_valid,
            victim_addr : (x_2).victim_addr, victim_info : (x_2).victim_info,
            victim_value : (x_2).victim_value, victim_req :
            (Bool)'(True)});
            victimRegs___0_0_0 <= update (x_1, (Bit#(1))'(1'h1), x_3);
        end else begin
            Struct13 x_4 =
            ((x_1)[(Bit#(1))'(1'h0)]);
            if (((x_4).victim_valid) && (((x_4).victim_addr) == (x_0)))
                begin
                Struct13 x_5 = (Struct13 {victim_valid : (x_4).victim_valid,
                victim_addr : (x_4).victim_addr, victim_info :
                (x_4).victim_info, victim_value : (x_4).victim_value,
                victim_req : (Bool)'(True)});
                victimRegs___0_0_0 <= update (x_1, (Bit#(1))'(1'h0), x_5);
            end else begin
                
            end
        end
    endmethod
    
    method Action victims___0_0_0__releaseVictim (Bit#(64) x_0);
        let x_1 = (victimRegs___0_0_0);
        Struct13 x_2 =
        ((x_1)[(Bit#(1))'(1'h0)]);
        if (((x_2).victim_valid) && (((x_2).victim_addr) == (x_0)))
            begin
            victimRegs___0_0_0 <= update (x_1, (Bit#(1))'(1'h0), unpack(0));
        end else begin
            Struct13 x_3 =
            ((x_1)[(Bit#(1))'(1'h1)]);
            if (((x_3).victim_valid) && (((x_3).victim_addr) == (x_0)))
                begin
                victimRegs___0_0_0 <= update (x_1, (Bit#(1))'(1'h1),
                unpack(0));
            end else begin
                
            end
        end
    endmethod
endmodule

interface Module46;
    method Action rdReq_infoRam___0_0_0__3 (Bit#(8) x_0);
    method Action wrReq_infoRam___0_0_0__3 (Struct47 x_0);
    method ActionValue#(Struct45) rdResp_infoRam___0_0_0__3 ();
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
    
    method Action rdReq_infoRam___0_0_0__3 (Bit#(8) x_0) if(initDone);
        bram.rdReq(x_0);
    endmethod
    
    method Action wrReq_infoRam___0_0_0__3 (Struct47 x_0) if(initDone);
        bram.wrReq(x_0.addr, x_0.datain);
    endmethod
    
    method ActionValue#(Struct45) rdResp_infoRam___0_0_0__3 () if(initDone);
        bram.deqRdResp ();
        let data = bram.rdResp ();
        return data;
    endmethod
    

endmodule

interface Module47;
    method Action rdReq_infoRam___0_0_0__2 (Bit#(8) x_0);
    method Action wrReq_infoRam___0_0_0__2 (Struct47 x_0);
    method ActionValue#(Struct45) rdResp_infoRam___0_0_0__2 ();
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
    
    method Action rdReq_infoRam___0_0_0__2 (Bit#(8) x_0) if(initDone);
        bram.rdReq(x_0);
    endmethod
    
    method Action wrReq_infoRam___0_0_0__2 (Struct47 x_0) if(initDone);
        bram.wrReq(x_0.addr, x_0.datain);
    endmethod
    
    method ActionValue#(Struct45) rdResp_infoRam___0_0_0__2 () if(initDone);
        bram.deqRdResp ();
        let data = bram.rdResp ();
        return data;
    endmethod
    

endmodule

interface Module48;
    method Action rdReq_infoRam___0_0_0__1 (Bit#(8) x_0);
    method Action wrReq_infoRam___0_0_0__1 (Struct47 x_0);
    method ActionValue#(Struct45) rdResp_infoRam___0_0_0__1 ();
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
    
    method Action rdReq_infoRam___0_0_0__1 (Bit#(8) x_0) if(initDone);
        bram.rdReq(x_0);
    endmethod
    
    method Action wrReq_infoRam___0_0_0__1 (Struct47 x_0) if(initDone);
        bram.wrReq(x_0.addr, x_0.datain);
    endmethod
    
    method ActionValue#(Struct45) rdResp_infoRam___0_0_0__1 () if(initDone);
        bram.deqRdResp ();
        let data = bram.rdResp ();
        return data;
    endmethod
    

endmodule

interface Module49;
    method Action rdReq_infoRam___0_0_0__0 (Bit#(8) x_0);
    method Action wrReq_infoRam___0_0_0__0 (Struct47 x_0);
    method ActionValue#(Struct45) rdResp_infoRam___0_0_0__0 ();
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
    
    method Action rdReq_infoRam___0_0_0__0 (Bit#(8) x_0) if(initDone);
        bram.rdReq(x_0);
    endmethod
    
    method Action wrReq_infoRam___0_0_0__0 (Struct47 x_0) if(initDone);
        bram.wrReq(x_0.addr, x_0.datain);
    endmethod
    
    method ActionValue#(Struct45) rdResp_infoRam___0_0_0__0 () if(initDone);
        bram.deqRdResp ();
        let data = bram.rdResp ();
        return data;
    endmethod
    

endmodule

interface Module50;
    method Action rdReq_dataRam___0_0_0 (Bit#(10) x_0);
    method Action wrReq_dataRam___0_0_0 (Struct49 x_0);
    method ActionValue#(Vector#(4, Bit#(64))) rdResp_dataRam___0_0_0 ();
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
    
    method Action rdReq_dataRam___0_0_0 (Bit#(10) x_0) if(initDone);
        bram.rdReq(x_0);
    endmethod
    
    method Action wrReq_dataRam___0_0_0 (Struct49 x_0) if(initDone);
        bram.wrReq(x_0.addr, x_0.datain);
    endmethod
    
    method ActionValue#(Vector#(4, Bit#(64))) rdResp_dataRam___0_0_0 ()
    if(initDone);
        bram.deqRdResp ();
        let data = bram.rdResp ();
        return data;
    endmethod
    

endmodule

interface Module51;
    method Action rdReq_repRam___0_0_0 (Bit#(8) x_0);
    method Action wrReq_repRam___0_0_0 (Struct50 x_0);
    method ActionValue#(Vector#(4, Bit#(8))) rdResp_repRam___0_0_0 ();
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
    
    method Action rdReq_repRam___0_0_0 (Bit#(8) x_0) if(initDone);
        bram.rdReq(x_0);
    endmethod
    
    method Action wrReq_repRam___0_0_0 (Struct50 x_0) if(initDone);
        bram.wrReq(x_0.addr, x_0.datain);
    endmethod
    
    method ActionValue#(Vector#(4, Bit#(8))) rdResp_repRam___0_0_0 ()
    if(initDone);
        bram.deqRdResp ();
        let data = bram.rdResp ();
        return data;
    endmethod
    

endmodule

interface Module52;
    method ActionValue#(Struct14) getMSHR__0_0_0 (Bit#(2) x_0);
    method ActionValue#(Struct1) getMSHRRq__0_0_0 (Bit#(2) x_0);
    method ActionValue#(Struct36) getPRqSlot__0_0_0 (Struct35 x_0);
    method ActionValue#(Struct36) getCRqSlot__0_0_0 (Struct35 x_0);
    method ActionValue#(Struct35) getWait__0_0_0 ();
    method Action registerUL__0_0_0 (Struct43 x_0);
    method Action canImm__0_0_0 (Bit#(64) x_0);
    method Action setULImm__0_0_0 (Struct1 x_0);
    method ActionValue#(Bit#(2)) getULReady__0_0_0 (Bit#(64) x_0);
    method Action startRelease__0_0_0 (Bit#(2) x_0);
    method Action releaseMSHR__0_0_0 (Bit#(2) x_0);
endinterface

module mkModule52
    (Module52);
    Reg#(Vector#(4, Struct14)) mshrs__0_0_0 <- mkReg(unpack(0));
    Reg#(Vector#(4, Bit#(64))) maddrs__0_0_0 <- mkReg(unpack(0));
    Reg#(Vector#(4, Bit#(3))) msts__0_0_0 <- mkReg(unpack(0));
    Reg#(Vector#(4, Struct51)) mnexts__0_0_0 <- mkReg(unpack(0));
    Reg#(Vector#(4, Struct1)) rqs__0_0_0 <- mkReg(unpack(0));
    
    // No rules in this module
    
    method ActionValue#(Struct14) getMSHR__0_0_0 (Bit#(2) x_0);
        let x_1 = (mshrs__0_0_0);
        return (x_1)[x_0];
    endmethod
    
    method ActionValue#(Struct1) getMSHRRq__0_0_0 (Bit#(2) x_0);
        let x_1 = (rqs__0_0_0);
        return (x_1)[x_0];
    endmethod
    
    method ActionValue#(Struct36) getPRqSlot__0_0_0 (Struct35 x_0);
        let x_1 = (mshrs__0_0_0);
        let x_2 = (maddrs__0_0_0);
        let x_3 = (msts__0_0_0);
        let x_4 = (mnexts__0_0_0);
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
            mshrs__0_0_0 <= update (x_1, x_7, Struct14 {m_is_ul : unpack(0),
            m_qidx : (x_0).r_msg_from, m_rsb : unpack(0), m_dl_rss_from :
            unpack(0), m_dl_rss_recv : unpack(0)});
            maddrs__0_0_0 <= update (x_2, x_7,
            ((x_0).r_msg).addr);
            msts__0_0_0 <= update (x_3, x_7, (x_11 ? ((Bit#(3))'(3'h1)) :
            ((Bit#(3))'(3'h4))));
            let x_13 = (rqs__0_0_0);
            rqs__0_0_0 <= update (x_13, x_7,
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
                mnexts__0_0_0 <= update (x_4, x_14, Struct51 {valid :
                (Bool)'(True), data : x_7});
            end else begin
                
            end
        end else begin
            
        end
        return x_12;
    endmethod
    
    method ActionValue#(Struct36) getCRqSlot__0_0_0 (Struct35 x_0);
        let x_1 = (mshrs__0_0_0);
        let x_2 = (maddrs__0_0_0);
        let x_3 = (msts__0_0_0);
        let x_4 = (mnexts__0_0_0);
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
            mshrs__0_0_0 <= update (x_1, x_7, Struct14 {m_is_ul : unpack(0),
            m_qidx : (x_0).r_msg_from, m_rsb : unpack(0), m_dl_rss_from :
            unpack(0), m_dl_rss_recv : unpack(0)});
            maddrs__0_0_0 <= update (x_2, x_7,
            ((x_0).r_msg).addr);
            msts__0_0_0 <= update (x_3, x_7, (x_14 ? ((Bit#(3))'(3'h1)) :
            ((Bit#(3))'(3'h4))));
            let x_16 = (rqs__0_0_0);
            rqs__0_0_0 <= update (x_16, x_7,
            (x_0).r_msg);
            if (x_14) begin
                Bit#(2) x_17 = ((x_12 ? ((x_10).data) :
                ((x_11).data)));
                Struct51 x_18 = ((x_4)[x_17]);
                mnexts__0_0_0 <= update (x_4, x_17, Struct51 {valid :
                (Bool)'(True), data : x_7});
            end else begin
                
            end
        end else begin
            
        end
        return x_15;
    endmethod
    
    method ActionValue#(Struct35) getWait__0_0_0 ();
        let x_1 = (mshrs__0_0_0);
        let x_2 = (maddrs__0_0_0);
        let x_3 = (msts__0_0_0);
        let x_4 = (rqs__0_0_0);
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
        msts__0_0_0 <= update (x_3, x_6, (Bit#(3))'(3'h4));
        Struct35 x_11 = (Struct35 {r_id : x_6, r_msg : x_9, r_msg_from :
        (x_7).m_qidx});
        return x_11;
    endmethod
    
    method Action registerUL__0_0_0 (Struct43 x_0);
        let x_1 = (mshrs__0_0_0);
        let x_2 = (msts__0_0_0);
        Bit#(2) x_3 = ((x_0).r_id);
        mshrs__0_0_0 <= update (x_1, x_3, Struct14 {m_is_ul : (Bool)'(True),
        m_qidx : {((Bit#(2))'(2'h2)),((x_0).r_ul_rsbTo)}, m_rsb :
        (x_0).r_ul_rsb, m_dl_rss_from : unpack(0), m_dl_rss_recv :
        unpack(0)});
        msts__0_0_0 <= update (x_2, x_3, (Bit#(3))'(3'h5));
    endmethod
    
    method Action canImm__0_0_0 (Bit#(64) x_0);
        let x_1 = (maddrs__0_0_0);
        let x_2 = (msts__0_0_0);
        let x_3 = (mnexts__0_0_0);
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
    
    method Action setULImm__0_0_0 (Struct1 x_0);
        let x_1 = (mshrs__0_0_0);
        let x_2 = (maddrs__0_0_0);
        let x_3 = (msts__0_0_0);
        let x_4 = (rqs__0_0_0);
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
        mshrs__0_0_0 <= update (x_1, x_6, Struct14 {m_is_ul : (Bool)'(True),
        m_qidx : unpack(0), m_rsb : (Bool)'(False), m_dl_rss_from :
        unpack(0), m_dl_rss_recv : unpack(0)});
        maddrs__0_0_0 <= update (x_2, x_6, (x_0).addr);
        msts__0_0_0 <= update (x_3, x_6, (Bit#(3))'(3'h5));
        rqs__0_0_0 <= update (x_4, x_6, x_0);
    endmethod
    
    method ActionValue#(Bit#(2)) getULReady__0_0_0 (Bit#(64) x_0);
        let x_1 = (mshrs__0_0_0);
        let x_2 = (maddrs__0_0_0);
        let x_3 = (msts__0_0_0);
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
    
    method Action startRelease__0_0_0 (Bit#(2) x_0);
        let x_1 = (msts__0_0_0);
        msts__0_0_0 <= update (x_1, x_0, (Bit#(3))'(3'h6));
    endmethod
    
    method Action releaseMSHR__0_0_0 (Bit#(2) x_0);
        let x_1 = (mshrs__0_0_0);
        let x_2 = (msts__0_0_0);
        let x_3 = (mnexts__0_0_0);
        mshrs__0_0_0 <= update (x_1, x_0, unpack(0));
        mnexts__0_0_0 <= update (x_3, x_0, unpack(0));
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
        msts__0_0_0 <= x_8;
    endmethod
endmodule

interface Module53;
    method Action enq_fifoCRqInput__0_0_1 (Struct2 x_0);
    method ActionValue#(Struct2) deq_fifoCRqInput__0_0_1 ();
endinterface

module mkModule53 (Module53);
    FIFOF#(Struct2) pff <- mkSizedFIFOF(4);
    
    method Action enq_fifoCRqInput__0_0_1 (Struct2 x_0);
        pff.enq(x_0);
    endmethod
    
    method ActionValue#(Struct2) deq_fifoCRqInput__0_0_1 ();
        pff.deq();
        return pff.first();
    endmethod

endmodule

interface Module54;
    method Action enq_fifoPInput__0_0_1 (Struct2 x_0);
    method ActionValue#(Struct2) deq_fifoPInput__0_0_1 ();
endinterface

module mkModule54 (Module54);
    FIFOF#(Struct2) pff <- mkSizedFIFOF(4);
    
    method Action enq_fifoPInput__0_0_1 (Struct2 x_0);
        pff.enq(x_0);
    endmethod
    
    method ActionValue#(Struct2) deq_fifoPInput__0_0_1 ();
        pff.deq();
        return pff.first();
    endmethod

endmodule

interface Module55;
    method Action enq_fifoN2I__0_0_1 (Struct38 x_0);
    method ActionValue#(Struct38) deq_fifoN2I__0_0_1 ();
endinterface

module mkModule55 (Module55);
    FIFOF#(Struct38) pff <- mkPipelineFIFOF();
    
    method Action enq_fifoN2I__0_0_1 (Struct38 x_0);
        pff.enq(x_0);
    endmethod
    
    method ActionValue#(Struct38) deq_fifoN2I__0_0_1 ();
        pff.deq();
        return pff.first();
    endmethod

endmodule

interface Module56;
    method Action enq_fifoI2L__0_0_1 (Struct38 x_0);
    method ActionValue#(Struct38) deq_fifoI2L__0_0_1 ();
endinterface

module mkModule56 (Module56);
    FIFOF#(Struct38) pff <- mkPipelineFIFOF();
    
    method Action enq_fifoI2L__0_0_1 (Struct38 x_0);
        pff.enq(x_0);
    endmethod
    
    method ActionValue#(Struct38) deq_fifoI2L__0_0_1 ();
        pff.deq();
        return pff.first();
    endmethod

endmodule

interface Module57;
    method Action enq_fifoL2E__0_0_1 (Struct41 x_0);
    method ActionValue#(Struct41) deq_fifoL2E__0_0_1 ();
endinterface

module mkModule57 (Module57);
    FIFOF#(Struct41) pff <- mkPipelineFIFOF();
    
    method Action enq_fifoL2E__0_0_1 (Struct41 x_0);
        pff.enq(x_0);
    endmethod
    
    method ActionValue#(Struct41) deq_fifoL2E__0_0_1 ();
        pff.deq();
        return pff.first();
    endmethod

endmodule

interface Module58;
    method Action enq_fifo_0_0_1_0 (Struct1 x_0);
    method ActionValue#(Struct1) deq_fifo_0_0_1_0 ();
endinterface

module mkModule58 (Module58);
    FIFOF#(Struct1) pff <- mkSizedFIFOF(2);
    
    method Action enq_fifo_0_0_1_0 (Struct1 x_0);
        pff.enq(x_0);
    endmethod
    
    method ActionValue#(Struct1) deq_fifo_0_0_1_0 ();
        pff.deq();
        return pff.first();
    endmethod

endmodule

interface Module59;
    method Action enq_fifo_0_0_1_1 (Struct1 x_0);
    method ActionValue#(Struct1) deq_fifo_0_0_1_1 ();
endinterface

module mkModule59 (Module59);
    FIFOF#(Struct1) pff <- mkSizedFIFOF(2);
    
    method Action enq_fifo_0_0_1_1 (Struct1 x_0);
        pff.enq(x_0);
    endmethod
    
    method ActionValue#(Struct1) deq_fifo_0_0_1_1 ();
        pff.deq();
        return pff.first();
    endmethod

endmodule

interface Module60;
    method Action enq_fifo_0_0_1_2 (Struct1 x_0);
    method ActionValue#(Struct1) deq_fifo_0_0_1_2 ();
endinterface

module mkModule60 (Module60);
    FIFOF#(Struct1) pff <- mkSizedFIFOF(2);
    
    method Action enq_fifo_0_0_1_2 (Struct1 x_0);
        pff.enq(x_0);
    endmethod
    
    method ActionValue#(Struct1) deq_fifo_0_0_1_2 ();
        pff.deq();
        return pff.first();
    endmethod

endmodule

interface Module61;
    method Action enq_fifo_0_0_1_0_0 (Struct1 x_0);
    method ActionValue#(Struct1) deq_fifo_0_0_1_0_0 ();
endinterface

module mkModule61 (Module61);
    FIFOF#(Struct1) pff <- mkSizedFIFOF(2);
    
    method Action enq_fifo_0_0_1_0_0 (Struct1 x_0);
        pff.enq(x_0);
    endmethod
    
    method ActionValue#(Struct1) deq_fifo_0_0_1_0_0 ();
        pff.deq();
        return pff.first();
    endmethod

endmodule

interface Module62;
    method Action enq_fifo_0_0_1_0_2 (Struct1 x_0);
    method ActionValue#(Struct1) deq_fifo_0_0_1_0_2 ();
endinterface

module mkModule62 (Module62);
    FIFOF#(Struct1) pff <- mkSizedFIFOF(2);
    
    method Action enq_fifo_0_0_1_0_2 (Struct1 x_0);
        pff.enq(x_0);
    endmethod
    
    method ActionValue#(Struct1) deq_fifo_0_0_1_0_2 ();
        pff.deq();
        return pff.first();
    endmethod

endmodule

interface Module63;
    method ActionValue#(Struct37) victims___0_0_1__findVictim (Bit#(64) x_0);
    method ActionValue#(Struct13) victims___0_0_1__getVictim (Bit#(1) x_0);
    method Action victims___0_0_1__setVictim (Struct44 x_0);
    method Action victims___0_0_1__registerVictim (Struct13 x_0);
    method ActionValue#(Struct13) victims___0_0_1__getFirstVictim ();
    method ActionValue#(Bool) victims___0_0_1__hasVictim ();
    method Action victims___0_0_1__setVictimRq (Bit#(64) x_0);
    method Action victims___0_0_1__releaseVictim (Bit#(64) x_0);
endinterface

module mkModule63
    (Module63);
    Reg#(Vector#(2, Struct13)) victimRegs___0_0_1 <- mkReg(unpack(0));
    
    // No rules in this module
    
    method ActionValue#(Struct37) victims___0_0_1__findVictim (Bit#(64) x_0);
        let x_1 = (victimRegs___0_0_1);
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
    
    method ActionValue#(Struct13) victims___0_0_1__getVictim (Bit#(1) x_0);
        let x_1 = (victimRegs___0_0_1);
        return (x_1)[x_0];
    endmethod
    
    method Action victims___0_0_1__setVictim (Struct44 x_0);
        let x_1 = (victimRegs___0_0_1);
        Struct13 x_2 = ((x_1)[(x_0).victim_idx]);
        Struct13 x_3 = (Struct13 {victim_valid : (Bool)'(True), victim_addr :
        (x_2).victim_addr, victim_info : (x_0).victim_info, victim_value :
        (x_0).victim_value, victim_req :
        (x_2).victim_req});
        victimRegs___0_0_1 <= update (x_1, (x_0).victim_idx, x_3);
    endmethod
    
    method Action victims___0_0_1__registerVictim (Struct13 x_0);
        let x_1 = (victimRegs___0_0_1);
        Struct37 x_2 = ((((x_1)[(Bit#(1))'(1'h1)]).victim_valid ?
        ((((x_1)[(Bit#(1))'(1'h0)]).victim_valid ? (Struct37 {valid :
        (Bool)'(False), data : unpack(0)}) : (Struct37 {valid :
        (Bool)'(True), data : (Bit#(1))'(1'h0)}))) : (Struct37 {valid :
        (Bool)'(True), data : (Bit#(1))'(1'h1)})));
        when ((x_2).valid, noAction);
        Bit#(1) x_3 = ((x_2).data);
        victimRegs___0_0_1 <= update (x_1, x_3, x_0);
    endmethod
    
    method ActionValue#(Struct13) victims___0_0_1__getFirstVictim ();
        let x_1 = (victimRegs___0_0_1);
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
    
    method ActionValue#(Bool) victims___0_0_1__hasVictim ();
        let x_1 = (victimRegs___0_0_1);
        Bool x_2 = (((((x_1)[(Bit#(1))'(1'h1)]).victim_valid) && (!
        (((x_1)[(Bit#(1))'(1'h1)]).victim_req)) ? ((Bool)'(True)) :
        (((((x_1)[(Bit#(1))'(1'h0)]).victim_valid) && (!
        (((x_1)[(Bit#(1))'(1'h0)]).victim_req)) ? ((Bool)'(True)) :
        ((Bool)'(False))))));
        return x_2;
    endmethod
    
    method Action victims___0_0_1__setVictimRq (Bit#(64) x_0);
        let x_1 = (victimRegs___0_0_1);
        Struct13 x_2 =
        ((x_1)[(Bit#(1))'(1'h1)]);
        if (((x_2).victim_valid) && (((x_2).victim_addr) == (x_0)))
            begin
            Struct13 x_3 = (Struct13 {victim_valid : (x_2).victim_valid,
            victim_addr : (x_2).victim_addr, victim_info : (x_2).victim_info,
            victim_value : (x_2).victim_value, victim_req :
            (Bool)'(True)});
            victimRegs___0_0_1 <= update (x_1, (Bit#(1))'(1'h1), x_3);
        end else begin
            Struct13 x_4 =
            ((x_1)[(Bit#(1))'(1'h0)]);
            if (((x_4).victim_valid) && (((x_4).victim_addr) == (x_0)))
                begin
                Struct13 x_5 = (Struct13 {victim_valid : (x_4).victim_valid,
                victim_addr : (x_4).victim_addr, victim_info :
                (x_4).victim_info, victim_value : (x_4).victim_value,
                victim_req : (Bool)'(True)});
                victimRegs___0_0_1 <= update (x_1, (Bit#(1))'(1'h0), x_5);
            end else begin
                
            end
        end
    endmethod
    
    method Action victims___0_0_1__releaseVictim (Bit#(64) x_0);
        let x_1 = (victimRegs___0_0_1);
        Struct13 x_2 =
        ((x_1)[(Bit#(1))'(1'h0)]);
        if (((x_2).victim_valid) && (((x_2).victim_addr) == (x_0)))
            begin
            victimRegs___0_0_1 <= update (x_1, (Bit#(1))'(1'h0), unpack(0));
        end else begin
            Struct13 x_3 =
            ((x_1)[(Bit#(1))'(1'h1)]);
            if (((x_3).victim_valid) && (((x_3).victim_addr) == (x_0)))
                begin
                victimRegs___0_0_1 <= update (x_1, (Bit#(1))'(1'h1),
                unpack(0));
            end else begin
                
            end
        end
    endmethod
endmodule

interface Module64;
    method Action rdReq_infoRam___0_0_1__3 (Bit#(8) x_0);
    method Action wrReq_infoRam___0_0_1__3 (Struct47 x_0);
    method ActionValue#(Struct45) rdResp_infoRam___0_0_1__3 ();
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
    
    method Action rdReq_infoRam___0_0_1__3 (Bit#(8) x_0) if(initDone);
        bram.rdReq(x_0);
    endmethod
    
    method Action wrReq_infoRam___0_0_1__3 (Struct47 x_0) if(initDone);
        bram.wrReq(x_0.addr, x_0.datain);
    endmethod
    
    method ActionValue#(Struct45) rdResp_infoRam___0_0_1__3 () if(initDone);
        bram.deqRdResp ();
        let data = bram.rdResp ();
        return data;
    endmethod
    

endmodule

interface Module65;
    method Action rdReq_infoRam___0_0_1__2 (Bit#(8) x_0);
    method Action wrReq_infoRam___0_0_1__2 (Struct47 x_0);
    method ActionValue#(Struct45) rdResp_infoRam___0_0_1__2 ();
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
    
    method Action rdReq_infoRam___0_0_1__2 (Bit#(8) x_0) if(initDone);
        bram.rdReq(x_0);
    endmethod
    
    method Action wrReq_infoRam___0_0_1__2 (Struct47 x_0) if(initDone);
        bram.wrReq(x_0.addr, x_0.datain);
    endmethod
    
    method ActionValue#(Struct45) rdResp_infoRam___0_0_1__2 () if(initDone);
        bram.deqRdResp ();
        let data = bram.rdResp ();
        return data;
    endmethod
    

endmodule

interface Module66;
    method Action rdReq_infoRam___0_0_1__1 (Bit#(8) x_0);
    method Action wrReq_infoRam___0_0_1__1 (Struct47 x_0);
    method ActionValue#(Struct45) rdResp_infoRam___0_0_1__1 ();
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
    
    method Action rdReq_infoRam___0_0_1__1 (Bit#(8) x_0) if(initDone);
        bram.rdReq(x_0);
    endmethod
    
    method Action wrReq_infoRam___0_0_1__1 (Struct47 x_0) if(initDone);
        bram.wrReq(x_0.addr, x_0.datain);
    endmethod
    
    method ActionValue#(Struct45) rdResp_infoRam___0_0_1__1 () if(initDone);
        bram.deqRdResp ();
        let data = bram.rdResp ();
        return data;
    endmethod
    

endmodule

interface Module67;
    method Action rdReq_infoRam___0_0_1__0 (Bit#(8) x_0);
    method Action wrReq_infoRam___0_0_1__0 (Struct47 x_0);
    method ActionValue#(Struct45) rdResp_infoRam___0_0_1__0 ();
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
    
    method Action rdReq_infoRam___0_0_1__0 (Bit#(8) x_0) if(initDone);
        bram.rdReq(x_0);
    endmethod
    
    method Action wrReq_infoRam___0_0_1__0 (Struct47 x_0) if(initDone);
        bram.wrReq(x_0.addr, x_0.datain);
    endmethod
    
    method ActionValue#(Struct45) rdResp_infoRam___0_0_1__0 () if(initDone);
        bram.deqRdResp ();
        let data = bram.rdResp ();
        return data;
    endmethod
    

endmodule

interface Module68;
    method Action rdReq_dataRam___0_0_1 (Bit#(10) x_0);
    method Action wrReq_dataRam___0_0_1 (Struct49 x_0);
    method ActionValue#(Vector#(4, Bit#(64))) rdResp_dataRam___0_0_1 ();
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
    
    method Action rdReq_dataRam___0_0_1 (Bit#(10) x_0) if(initDone);
        bram.rdReq(x_0);
    endmethod
    
    method Action wrReq_dataRam___0_0_1 (Struct49 x_0) if(initDone);
        bram.wrReq(x_0.addr, x_0.datain);
    endmethod
    
    method ActionValue#(Vector#(4, Bit#(64))) rdResp_dataRam___0_0_1 ()
    if(initDone);
        bram.deqRdResp ();
        let data = bram.rdResp ();
        return data;
    endmethod
    

endmodule

interface Module69;
    method Action rdReq_repRam___0_0_1 (Bit#(8) x_0);
    method Action wrReq_repRam___0_0_1 (Struct50 x_0);
    method ActionValue#(Vector#(4, Bit#(8))) rdResp_repRam___0_0_1 ();
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
    
    method Action rdReq_repRam___0_0_1 (Bit#(8) x_0) if(initDone);
        bram.rdReq(x_0);
    endmethod
    
    method Action wrReq_repRam___0_0_1 (Struct50 x_0) if(initDone);
        bram.wrReq(x_0.addr, x_0.datain);
    endmethod
    
    method ActionValue#(Vector#(4, Bit#(8))) rdResp_repRam___0_0_1 ()
    if(initDone);
        bram.deqRdResp ();
        let data = bram.rdResp ();
        return data;
    endmethod
    

endmodule

interface Module70;
    method ActionValue#(Struct14) getMSHR__0_0_1 (Bit#(2) x_0);
    method ActionValue#(Struct1) getMSHRRq__0_0_1 (Bit#(2) x_0);
    method ActionValue#(Struct36) getPRqSlot__0_0_1 (Struct35 x_0);
    method ActionValue#(Struct36) getCRqSlot__0_0_1 (Struct35 x_0);
    method ActionValue#(Struct35) getWait__0_0_1 ();
    method Action registerUL__0_0_1 (Struct43 x_0);
    method Action canImm__0_0_1 (Bit#(64) x_0);
    method Action setULImm__0_0_1 (Struct1 x_0);
    method ActionValue#(Bit#(2)) getULReady__0_0_1 (Bit#(64) x_0);
    method Action startRelease__0_0_1 (Bit#(2) x_0);
    method Action releaseMSHR__0_0_1 (Bit#(2) x_0);
endinterface

module mkModule70
    (Module70);
    Reg#(Vector#(4, Struct14)) mshrs__0_0_1 <- mkReg(unpack(0));
    Reg#(Vector#(4, Bit#(64))) maddrs__0_0_1 <- mkReg(unpack(0));
    Reg#(Vector#(4, Bit#(3))) msts__0_0_1 <- mkReg(unpack(0));
    Reg#(Vector#(4, Struct51)) mnexts__0_0_1 <- mkReg(unpack(0));
    Reg#(Vector#(4, Struct1)) rqs__0_0_1 <- mkReg(unpack(0));
    
    // No rules in this module
    
    method ActionValue#(Struct14) getMSHR__0_0_1 (Bit#(2) x_0);
        let x_1 = (mshrs__0_0_1);
        return (x_1)[x_0];
    endmethod
    
    method ActionValue#(Struct1) getMSHRRq__0_0_1 (Bit#(2) x_0);
        let x_1 = (rqs__0_0_1);
        return (x_1)[x_0];
    endmethod
    
    method ActionValue#(Struct36) getPRqSlot__0_0_1 (Struct35 x_0);
        let x_1 = (mshrs__0_0_1);
        let x_2 = (maddrs__0_0_1);
        let x_3 = (msts__0_0_1);
        let x_4 = (mnexts__0_0_1);
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
            mshrs__0_0_1 <= update (x_1, x_7, Struct14 {m_is_ul : unpack(0),
            m_qidx : (x_0).r_msg_from, m_rsb : unpack(0), m_dl_rss_from :
            unpack(0), m_dl_rss_recv : unpack(0)});
            maddrs__0_0_1 <= update (x_2, x_7,
            ((x_0).r_msg).addr);
            msts__0_0_1 <= update (x_3, x_7, (x_11 ? ((Bit#(3))'(3'h1)) :
            ((Bit#(3))'(3'h4))));
            let x_13 = (rqs__0_0_1);
            rqs__0_0_1 <= update (x_13, x_7,
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
                mnexts__0_0_1 <= update (x_4, x_14, Struct51 {valid :
                (Bool)'(True), data : x_7});
            end else begin
                
            end
        end else begin
            
        end
        return x_12;
    endmethod
    
    method ActionValue#(Struct36) getCRqSlot__0_0_1 (Struct35 x_0);
        let x_1 = (mshrs__0_0_1);
        let x_2 = (maddrs__0_0_1);
        let x_3 = (msts__0_0_1);
        let x_4 = (mnexts__0_0_1);
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
            mshrs__0_0_1 <= update (x_1, x_7, Struct14 {m_is_ul : unpack(0),
            m_qidx : (x_0).r_msg_from, m_rsb : unpack(0), m_dl_rss_from :
            unpack(0), m_dl_rss_recv : unpack(0)});
            maddrs__0_0_1 <= update (x_2, x_7,
            ((x_0).r_msg).addr);
            msts__0_0_1 <= update (x_3, x_7, (x_14 ? ((Bit#(3))'(3'h1)) :
            ((Bit#(3))'(3'h4))));
            let x_16 = (rqs__0_0_1);
            rqs__0_0_1 <= update (x_16, x_7,
            (x_0).r_msg);
            if (x_14) begin
                Bit#(2) x_17 = ((x_12 ? ((x_10).data) :
                ((x_11).data)));
                Struct51 x_18 = ((x_4)[x_17]);
                mnexts__0_0_1 <= update (x_4, x_17, Struct51 {valid :
                (Bool)'(True), data : x_7});
            end else begin
                
            end
        end else begin
            
        end
        return x_15;
    endmethod
    
    method ActionValue#(Struct35) getWait__0_0_1 ();
        let x_1 = (mshrs__0_0_1);
        let x_2 = (maddrs__0_0_1);
        let x_3 = (msts__0_0_1);
        let x_4 = (rqs__0_0_1);
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
        msts__0_0_1 <= update (x_3, x_6, (Bit#(3))'(3'h4));
        Struct35 x_11 = (Struct35 {r_id : x_6, r_msg : x_9, r_msg_from :
        (x_7).m_qidx});
        return x_11;
    endmethod
    
    method Action registerUL__0_0_1 (Struct43 x_0);
        let x_1 = (mshrs__0_0_1);
        let x_2 = (msts__0_0_1);
        Bit#(2) x_3 = ((x_0).r_id);
        mshrs__0_0_1 <= update (x_1, x_3, Struct14 {m_is_ul : (Bool)'(True),
        m_qidx : {((Bit#(2))'(2'h2)),((x_0).r_ul_rsbTo)}, m_rsb :
        (x_0).r_ul_rsb, m_dl_rss_from : unpack(0), m_dl_rss_recv :
        unpack(0)});
        msts__0_0_1 <= update (x_2, x_3, (Bit#(3))'(3'h5));
    endmethod
    
    method Action canImm__0_0_1 (Bit#(64) x_0);
        let x_1 = (maddrs__0_0_1);
        let x_2 = (msts__0_0_1);
        let x_3 = (mnexts__0_0_1);
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
    
    method Action setULImm__0_0_1 (Struct1 x_0);
        let x_1 = (mshrs__0_0_1);
        let x_2 = (maddrs__0_0_1);
        let x_3 = (msts__0_0_1);
        let x_4 = (rqs__0_0_1);
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
        mshrs__0_0_1 <= update (x_1, x_6, Struct14 {m_is_ul : (Bool)'(True),
        m_qidx : unpack(0), m_rsb : (Bool)'(False), m_dl_rss_from :
        unpack(0), m_dl_rss_recv : unpack(0)});
        maddrs__0_0_1 <= update (x_2, x_6, (x_0).addr);
        msts__0_0_1 <= update (x_3, x_6, (Bit#(3))'(3'h5));
        rqs__0_0_1 <= update (x_4, x_6, x_0);
    endmethod
    
    method ActionValue#(Bit#(2)) getULReady__0_0_1 (Bit#(64) x_0);
        let x_1 = (mshrs__0_0_1);
        let x_2 = (maddrs__0_0_1);
        let x_3 = (msts__0_0_1);
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
    
    method Action startRelease__0_0_1 (Bit#(2) x_0);
        let x_1 = (msts__0_0_1);
        msts__0_0_1 <= update (x_1, x_0, (Bit#(3))'(3'h6));
    endmethod
    
    method Action releaseMSHR__0_0_1 (Bit#(2) x_0);
        let x_1 = (mshrs__0_0_1);
        let x_2 = (msts__0_0_1);
        let x_3 = (mnexts__0_0_1);
        mshrs__0_0_1 <= update (x_1, x_0, unpack(0));
        mnexts__0_0_1 <= update (x_3, x_0, unpack(0));
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
        msts__0_0_1 <= x_8;
    endmethod
endmodule

interface Module71;
    method Action enq_fifoCRqInput__0_0_2 (Struct2 x_0);
    method ActionValue#(Struct2) deq_fifoCRqInput__0_0_2 ();
endinterface

module mkModule71 (Module71);
    FIFOF#(Struct2) pff <- mkSizedFIFOF(4);
    
    method Action enq_fifoCRqInput__0_0_2 (Struct2 x_0);
        pff.enq(x_0);
    endmethod
    
    method ActionValue#(Struct2) deq_fifoCRqInput__0_0_2 ();
        pff.deq();
        return pff.first();
    endmethod

endmodule

interface Module72;
    method Action enq_fifoPInput__0_0_2 (Struct2 x_0);
    method ActionValue#(Struct2) deq_fifoPInput__0_0_2 ();
endinterface

module mkModule72 (Module72);
    FIFOF#(Struct2) pff <- mkSizedFIFOF(4);
    
    method Action enq_fifoPInput__0_0_2 (Struct2 x_0);
        pff.enq(x_0);
    endmethod
    
    method ActionValue#(Struct2) deq_fifoPInput__0_0_2 ();
        pff.deq();
        return pff.first();
    endmethod

endmodule

interface Module73;
    method Action enq_fifoN2I__0_0_2 (Struct38 x_0);
    method ActionValue#(Struct38) deq_fifoN2I__0_0_2 ();
endinterface

module mkModule73 (Module73);
    FIFOF#(Struct38) pff <- mkPipelineFIFOF();
    
    method Action enq_fifoN2I__0_0_2 (Struct38 x_0);
        pff.enq(x_0);
    endmethod
    
    method ActionValue#(Struct38) deq_fifoN2I__0_0_2 ();
        pff.deq();
        return pff.first();
    endmethod

endmodule

interface Module74;
    method Action enq_fifoI2L__0_0_2 (Struct38 x_0);
    method ActionValue#(Struct38) deq_fifoI2L__0_0_2 ();
endinterface

module mkModule74 (Module74);
    FIFOF#(Struct38) pff <- mkPipelineFIFOF();
    
    method Action enq_fifoI2L__0_0_2 (Struct38 x_0);
        pff.enq(x_0);
    endmethod
    
    method ActionValue#(Struct38) deq_fifoI2L__0_0_2 ();
        pff.deq();
        return pff.first();
    endmethod

endmodule

interface Module75;
    method Action enq_fifoL2E__0_0_2 (Struct41 x_0);
    method ActionValue#(Struct41) deq_fifoL2E__0_0_2 ();
endinterface

module mkModule75 (Module75);
    FIFOF#(Struct41) pff <- mkPipelineFIFOF();
    
    method Action enq_fifoL2E__0_0_2 (Struct41 x_0);
        pff.enq(x_0);
    endmethod
    
    method ActionValue#(Struct41) deq_fifoL2E__0_0_2 ();
        pff.deq();
        return pff.first();
    endmethod

endmodule

interface Module76;
    method Action enq_fifo_0_0_2_0 (Struct1 x_0);
    method ActionValue#(Struct1) deq_fifo_0_0_2_0 ();
endinterface

module mkModule76 (Module76);
    FIFOF#(Struct1) pff <- mkSizedFIFOF(2);
    
    method Action enq_fifo_0_0_2_0 (Struct1 x_0);
        pff.enq(x_0);
    endmethod
    
    method ActionValue#(Struct1) deq_fifo_0_0_2_0 ();
        pff.deq();
        return pff.first();
    endmethod

endmodule

interface Module77;
    method Action enq_fifo_0_0_2_1 (Struct1 x_0);
    method ActionValue#(Struct1) deq_fifo_0_0_2_1 ();
endinterface

module mkModule77 (Module77);
    FIFOF#(Struct1) pff <- mkSizedFIFOF(2);
    
    method Action enq_fifo_0_0_2_1 (Struct1 x_0);
        pff.enq(x_0);
    endmethod
    
    method ActionValue#(Struct1) deq_fifo_0_0_2_1 ();
        pff.deq();
        return pff.first();
    endmethod

endmodule

interface Module78;
    method Action enq_fifo_0_0_2_2 (Struct1 x_0);
    method ActionValue#(Struct1) deq_fifo_0_0_2_2 ();
endinterface

module mkModule78 (Module78);
    FIFOF#(Struct1) pff <- mkSizedFIFOF(2);
    
    method Action enq_fifo_0_0_2_2 (Struct1 x_0);
        pff.enq(x_0);
    endmethod
    
    method ActionValue#(Struct1) deq_fifo_0_0_2_2 ();
        pff.deq();
        return pff.first();
    endmethod

endmodule

interface Module79;
    method Action enq_fifo_0_0_2_0_0 (Struct1 x_0);
    method ActionValue#(Struct1) deq_fifo_0_0_2_0_0 ();
endinterface

module mkModule79 (Module79);
    FIFOF#(Struct1) pff <- mkSizedFIFOF(2);
    
    method Action enq_fifo_0_0_2_0_0 (Struct1 x_0);
        pff.enq(x_0);
    endmethod
    
    method ActionValue#(Struct1) deq_fifo_0_0_2_0_0 ();
        pff.deq();
        return pff.first();
    endmethod

endmodule

interface Module80;
    method Action enq_fifo_0_0_2_0_2 (Struct1 x_0);
    method ActionValue#(Struct1) deq_fifo_0_0_2_0_2 ();
endinterface

module mkModule80 (Module80);
    FIFOF#(Struct1) pff <- mkSizedFIFOF(2);
    
    method Action enq_fifo_0_0_2_0_2 (Struct1 x_0);
        pff.enq(x_0);
    endmethod
    
    method ActionValue#(Struct1) deq_fifo_0_0_2_0_2 ();
        pff.deq();
        return pff.first();
    endmethod

endmodule

interface Module81;
    method ActionValue#(Struct37) victims___0_0_2__findVictim (Bit#(64) x_0);
    method ActionValue#(Struct13) victims___0_0_2__getVictim (Bit#(1) x_0);
    method Action victims___0_0_2__setVictim (Struct44 x_0);
    method Action victims___0_0_2__registerVictim (Struct13 x_0);
    method ActionValue#(Struct13) victims___0_0_2__getFirstVictim ();
    method ActionValue#(Bool) victims___0_0_2__hasVictim ();
    method Action victims___0_0_2__setVictimRq (Bit#(64) x_0);
    method Action victims___0_0_2__releaseVictim (Bit#(64) x_0);
endinterface

module mkModule81
    (Module81);
    Reg#(Vector#(2, Struct13)) victimRegs___0_0_2 <- mkReg(unpack(0));
    
    // No rules in this module
    
    method ActionValue#(Struct37) victims___0_0_2__findVictim (Bit#(64) x_0);
        let x_1 = (victimRegs___0_0_2);
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
    
    method ActionValue#(Struct13) victims___0_0_2__getVictim (Bit#(1) x_0);
        let x_1 = (victimRegs___0_0_2);
        return (x_1)[x_0];
    endmethod
    
    method Action victims___0_0_2__setVictim (Struct44 x_0);
        let x_1 = (victimRegs___0_0_2);
        Struct13 x_2 = ((x_1)[(x_0).victim_idx]);
        Struct13 x_3 = (Struct13 {victim_valid : (Bool)'(True), victim_addr :
        (x_2).victim_addr, victim_info : (x_0).victim_info, victim_value :
        (x_0).victim_value, victim_req :
        (x_2).victim_req});
        victimRegs___0_0_2 <= update (x_1, (x_0).victim_idx, x_3);
    endmethod
    
    method Action victims___0_0_2__registerVictim (Struct13 x_0);
        let x_1 = (victimRegs___0_0_2);
        Struct37 x_2 = ((((x_1)[(Bit#(1))'(1'h1)]).victim_valid ?
        ((((x_1)[(Bit#(1))'(1'h0)]).victim_valid ? (Struct37 {valid :
        (Bool)'(False), data : unpack(0)}) : (Struct37 {valid :
        (Bool)'(True), data : (Bit#(1))'(1'h0)}))) : (Struct37 {valid :
        (Bool)'(True), data : (Bit#(1))'(1'h1)})));
        when ((x_2).valid, noAction);
        Bit#(1) x_3 = ((x_2).data);
        victimRegs___0_0_2 <= update (x_1, x_3, x_0);
    endmethod
    
    method ActionValue#(Struct13) victims___0_0_2__getFirstVictim ();
        let x_1 = (victimRegs___0_0_2);
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
    
    method ActionValue#(Bool) victims___0_0_2__hasVictim ();
        let x_1 = (victimRegs___0_0_2);
        Bool x_2 = (((((x_1)[(Bit#(1))'(1'h1)]).victim_valid) && (!
        (((x_1)[(Bit#(1))'(1'h1)]).victim_req)) ? ((Bool)'(True)) :
        (((((x_1)[(Bit#(1))'(1'h0)]).victim_valid) && (!
        (((x_1)[(Bit#(1))'(1'h0)]).victim_req)) ? ((Bool)'(True)) :
        ((Bool)'(False))))));
        return x_2;
    endmethod
    
    method Action victims___0_0_2__setVictimRq (Bit#(64) x_0);
        let x_1 = (victimRegs___0_0_2);
        Struct13 x_2 =
        ((x_1)[(Bit#(1))'(1'h1)]);
        if (((x_2).victim_valid) && (((x_2).victim_addr) == (x_0)))
            begin
            Struct13 x_3 = (Struct13 {victim_valid : (x_2).victim_valid,
            victim_addr : (x_2).victim_addr, victim_info : (x_2).victim_info,
            victim_value : (x_2).victim_value, victim_req :
            (Bool)'(True)});
            victimRegs___0_0_2 <= update (x_1, (Bit#(1))'(1'h1), x_3);
        end else begin
            Struct13 x_4 =
            ((x_1)[(Bit#(1))'(1'h0)]);
            if (((x_4).victim_valid) && (((x_4).victim_addr) == (x_0)))
                begin
                Struct13 x_5 = (Struct13 {victim_valid : (x_4).victim_valid,
                victim_addr : (x_4).victim_addr, victim_info :
                (x_4).victim_info, victim_value : (x_4).victim_value,
                victim_req : (Bool)'(True)});
                victimRegs___0_0_2 <= update (x_1, (Bit#(1))'(1'h0), x_5);
            end else begin
                
            end
        end
    endmethod
    
    method Action victims___0_0_2__releaseVictim (Bit#(64) x_0);
        let x_1 = (victimRegs___0_0_2);
        Struct13 x_2 =
        ((x_1)[(Bit#(1))'(1'h0)]);
        if (((x_2).victim_valid) && (((x_2).victim_addr) == (x_0)))
            begin
            victimRegs___0_0_2 <= update (x_1, (Bit#(1))'(1'h0), unpack(0));
        end else begin
            Struct13 x_3 =
            ((x_1)[(Bit#(1))'(1'h1)]);
            if (((x_3).victim_valid) && (((x_3).victim_addr) == (x_0)))
                begin
                victimRegs___0_0_2 <= update (x_1, (Bit#(1))'(1'h1),
                unpack(0));
            end else begin
                
            end
        end
    endmethod
endmodule

interface Module82;
    method Action rdReq_infoRam___0_0_2__3 (Bit#(8) x_0);
    method Action wrReq_infoRam___0_0_2__3 (Struct47 x_0);
    method ActionValue#(Struct45) rdResp_infoRam___0_0_2__3 ();
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
    
    method Action rdReq_infoRam___0_0_2__3 (Bit#(8) x_0) if(initDone);
        bram.rdReq(x_0);
    endmethod
    
    method Action wrReq_infoRam___0_0_2__3 (Struct47 x_0) if(initDone);
        bram.wrReq(x_0.addr, x_0.datain);
    endmethod
    
    method ActionValue#(Struct45) rdResp_infoRam___0_0_2__3 () if(initDone);
        bram.deqRdResp ();
        let data = bram.rdResp ();
        return data;
    endmethod
    

endmodule

interface Module83;
    method Action rdReq_infoRam___0_0_2__2 (Bit#(8) x_0);
    method Action wrReq_infoRam___0_0_2__2 (Struct47 x_0);
    method ActionValue#(Struct45) rdResp_infoRam___0_0_2__2 ();
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
    
    method Action rdReq_infoRam___0_0_2__2 (Bit#(8) x_0) if(initDone);
        bram.rdReq(x_0);
    endmethod
    
    method Action wrReq_infoRam___0_0_2__2 (Struct47 x_0) if(initDone);
        bram.wrReq(x_0.addr, x_0.datain);
    endmethod
    
    method ActionValue#(Struct45) rdResp_infoRam___0_0_2__2 () if(initDone);
        bram.deqRdResp ();
        let data = bram.rdResp ();
        return data;
    endmethod
    

endmodule

interface Module84;
    method Action rdReq_infoRam___0_0_2__1 (Bit#(8) x_0);
    method Action wrReq_infoRam___0_0_2__1 (Struct47 x_0);
    method ActionValue#(Struct45) rdResp_infoRam___0_0_2__1 ();
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
    
    method Action rdReq_infoRam___0_0_2__1 (Bit#(8) x_0) if(initDone);
        bram.rdReq(x_0);
    endmethod
    
    method Action wrReq_infoRam___0_0_2__1 (Struct47 x_0) if(initDone);
        bram.wrReq(x_0.addr, x_0.datain);
    endmethod
    
    method ActionValue#(Struct45) rdResp_infoRam___0_0_2__1 () if(initDone);
        bram.deqRdResp ();
        let data = bram.rdResp ();
        return data;
    endmethod
    

endmodule

interface Module85;
    method Action rdReq_infoRam___0_0_2__0 (Bit#(8) x_0);
    method Action wrReq_infoRam___0_0_2__0 (Struct47 x_0);
    method ActionValue#(Struct45) rdResp_infoRam___0_0_2__0 ();
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
    
    method Action rdReq_infoRam___0_0_2__0 (Bit#(8) x_0) if(initDone);
        bram.rdReq(x_0);
    endmethod
    
    method Action wrReq_infoRam___0_0_2__0 (Struct47 x_0) if(initDone);
        bram.wrReq(x_0.addr, x_0.datain);
    endmethod
    
    method ActionValue#(Struct45) rdResp_infoRam___0_0_2__0 () if(initDone);
        bram.deqRdResp ();
        let data = bram.rdResp ();
        return data;
    endmethod
    

endmodule

interface Module86;
    method Action rdReq_dataRam___0_0_2 (Bit#(10) x_0);
    method Action wrReq_dataRam___0_0_2 (Struct49 x_0);
    method ActionValue#(Vector#(4, Bit#(64))) rdResp_dataRam___0_0_2 ();
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
    
    method Action rdReq_dataRam___0_0_2 (Bit#(10) x_0) if(initDone);
        bram.rdReq(x_0);
    endmethod
    
    method Action wrReq_dataRam___0_0_2 (Struct49 x_0) if(initDone);
        bram.wrReq(x_0.addr, x_0.datain);
    endmethod
    
    method ActionValue#(Vector#(4, Bit#(64))) rdResp_dataRam___0_0_2 ()
    if(initDone);
        bram.deqRdResp ();
        let data = bram.rdResp ();
        return data;
    endmethod
    

endmodule

interface Module87;
    method Action rdReq_repRam___0_0_2 (Bit#(8) x_0);
    method Action wrReq_repRam___0_0_2 (Struct50 x_0);
    method ActionValue#(Vector#(4, Bit#(8))) rdResp_repRam___0_0_2 ();
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
    
    method Action rdReq_repRam___0_0_2 (Bit#(8) x_0) if(initDone);
        bram.rdReq(x_0);
    endmethod
    
    method Action wrReq_repRam___0_0_2 (Struct50 x_0) if(initDone);
        bram.wrReq(x_0.addr, x_0.datain);
    endmethod
    
    method ActionValue#(Vector#(4, Bit#(8))) rdResp_repRam___0_0_2 ()
    if(initDone);
        bram.deqRdResp ();
        let data = bram.rdResp ();
        return data;
    endmethod
    

endmodule

interface Module88;
    method ActionValue#(Struct14) getMSHR__0_0_2 (Bit#(2) x_0);
    method ActionValue#(Struct1) getMSHRRq__0_0_2 (Bit#(2) x_0);
    method ActionValue#(Struct36) getPRqSlot__0_0_2 (Struct35 x_0);
    method ActionValue#(Struct36) getCRqSlot__0_0_2 (Struct35 x_0);
    method ActionValue#(Struct35) getWait__0_0_2 ();
    method Action registerUL__0_0_2 (Struct43 x_0);
    method Action canImm__0_0_2 (Bit#(64) x_0);
    method Action setULImm__0_0_2 (Struct1 x_0);
    method ActionValue#(Bit#(2)) getULReady__0_0_2 (Bit#(64) x_0);
    method Action startRelease__0_0_2 (Bit#(2) x_0);
    method Action releaseMSHR__0_0_2 (Bit#(2) x_0);
endinterface

module mkModule88
    (Module88);
    Reg#(Vector#(4, Struct14)) mshrs__0_0_2 <- mkReg(unpack(0));
    Reg#(Vector#(4, Bit#(64))) maddrs__0_0_2 <- mkReg(unpack(0));
    Reg#(Vector#(4, Bit#(3))) msts__0_0_2 <- mkReg(unpack(0));
    Reg#(Vector#(4, Struct51)) mnexts__0_0_2 <- mkReg(unpack(0));
    Reg#(Vector#(4, Struct1)) rqs__0_0_2 <- mkReg(unpack(0));
    
    // No rules in this module
    
    method ActionValue#(Struct14) getMSHR__0_0_2 (Bit#(2) x_0);
        let x_1 = (mshrs__0_0_2);
        return (x_1)[x_0];
    endmethod
    
    method ActionValue#(Struct1) getMSHRRq__0_0_2 (Bit#(2) x_0);
        let x_1 = (rqs__0_0_2);
        return (x_1)[x_0];
    endmethod
    
    method ActionValue#(Struct36) getPRqSlot__0_0_2 (Struct35 x_0);
        let x_1 = (mshrs__0_0_2);
        let x_2 = (maddrs__0_0_2);
        let x_3 = (msts__0_0_2);
        let x_4 = (mnexts__0_0_2);
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
            mshrs__0_0_2 <= update (x_1, x_7, Struct14 {m_is_ul : unpack(0),
            m_qidx : (x_0).r_msg_from, m_rsb : unpack(0), m_dl_rss_from :
            unpack(0), m_dl_rss_recv : unpack(0)});
            maddrs__0_0_2 <= update (x_2, x_7,
            ((x_0).r_msg).addr);
            msts__0_0_2 <= update (x_3, x_7, (x_11 ? ((Bit#(3))'(3'h1)) :
            ((Bit#(3))'(3'h4))));
            let x_13 = (rqs__0_0_2);
            rqs__0_0_2 <= update (x_13, x_7,
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
                mnexts__0_0_2 <= update (x_4, x_14, Struct51 {valid :
                (Bool)'(True), data : x_7});
            end else begin
                
            end
        end else begin
            
        end
        return x_12;
    endmethod
    
    method ActionValue#(Struct36) getCRqSlot__0_0_2 (Struct35 x_0);
        let x_1 = (mshrs__0_0_2);
        let x_2 = (maddrs__0_0_2);
        let x_3 = (msts__0_0_2);
        let x_4 = (mnexts__0_0_2);
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
            mshrs__0_0_2 <= update (x_1, x_7, Struct14 {m_is_ul : unpack(0),
            m_qidx : (x_0).r_msg_from, m_rsb : unpack(0), m_dl_rss_from :
            unpack(0), m_dl_rss_recv : unpack(0)});
            maddrs__0_0_2 <= update (x_2, x_7,
            ((x_0).r_msg).addr);
            msts__0_0_2 <= update (x_3, x_7, (x_14 ? ((Bit#(3))'(3'h1)) :
            ((Bit#(3))'(3'h4))));
            let x_16 = (rqs__0_0_2);
            rqs__0_0_2 <= update (x_16, x_7,
            (x_0).r_msg);
            if (x_14) begin
                Bit#(2) x_17 = ((x_12 ? ((x_10).data) :
                ((x_11).data)));
                Struct51 x_18 = ((x_4)[x_17]);
                mnexts__0_0_2 <= update (x_4, x_17, Struct51 {valid :
                (Bool)'(True), data : x_7});
            end else begin
                
            end
        end else begin
            
        end
        return x_15;
    endmethod
    
    method ActionValue#(Struct35) getWait__0_0_2 ();
        let x_1 = (mshrs__0_0_2);
        let x_2 = (maddrs__0_0_2);
        let x_3 = (msts__0_0_2);
        let x_4 = (rqs__0_0_2);
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
        msts__0_0_2 <= update (x_3, x_6, (Bit#(3))'(3'h4));
        Struct35 x_11 = (Struct35 {r_id : x_6, r_msg : x_9, r_msg_from :
        (x_7).m_qidx});
        return x_11;
    endmethod
    
    method Action registerUL__0_0_2 (Struct43 x_0);
        let x_1 = (mshrs__0_0_2);
        let x_2 = (msts__0_0_2);
        Bit#(2) x_3 = ((x_0).r_id);
        mshrs__0_0_2 <= update (x_1, x_3, Struct14 {m_is_ul : (Bool)'(True),
        m_qidx : {((Bit#(2))'(2'h2)),((x_0).r_ul_rsbTo)}, m_rsb :
        (x_0).r_ul_rsb, m_dl_rss_from : unpack(0), m_dl_rss_recv :
        unpack(0)});
        msts__0_0_2 <= update (x_2, x_3, (Bit#(3))'(3'h5));
    endmethod
    
    method Action canImm__0_0_2 (Bit#(64) x_0);
        let x_1 = (maddrs__0_0_2);
        let x_2 = (msts__0_0_2);
        let x_3 = (mnexts__0_0_2);
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
    
    method Action setULImm__0_0_2 (Struct1 x_0);
        let x_1 = (mshrs__0_0_2);
        let x_2 = (maddrs__0_0_2);
        let x_3 = (msts__0_0_2);
        let x_4 = (rqs__0_0_2);
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
        mshrs__0_0_2 <= update (x_1, x_6, Struct14 {m_is_ul : (Bool)'(True),
        m_qidx : unpack(0), m_rsb : (Bool)'(False), m_dl_rss_from :
        unpack(0), m_dl_rss_recv : unpack(0)});
        maddrs__0_0_2 <= update (x_2, x_6, (x_0).addr);
        msts__0_0_2 <= update (x_3, x_6, (Bit#(3))'(3'h5));
        rqs__0_0_2 <= update (x_4, x_6, x_0);
    endmethod
    
    method ActionValue#(Bit#(2)) getULReady__0_0_2 (Bit#(64) x_0);
        let x_1 = (mshrs__0_0_2);
        let x_2 = (maddrs__0_0_2);
        let x_3 = (msts__0_0_2);
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
    
    method Action startRelease__0_0_2 (Bit#(2) x_0);
        let x_1 = (msts__0_0_2);
        msts__0_0_2 <= update (x_1, x_0, (Bit#(3))'(3'h6));
    endmethod
    
    method Action releaseMSHR__0_0_2 (Bit#(2) x_0);
        let x_1 = (mshrs__0_0_2);
        let x_2 = (msts__0_0_2);
        let x_3 = (mnexts__0_0_2);
        mshrs__0_0_2 <= update (x_1, x_0, unpack(0));
        mnexts__0_0_2 <= update (x_3, x_0, unpack(0));
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
        msts__0_0_2 <= x_8;
    endmethod
endmodule

interface Module89;
    method Action enq_fifoCRqInput__0_0_3 (Struct2 x_0);
    method ActionValue#(Struct2) deq_fifoCRqInput__0_0_3 ();
endinterface

module mkModule89 (Module89);
    FIFOF#(Struct2) pff <- mkSizedFIFOF(4);
    
    method Action enq_fifoCRqInput__0_0_3 (Struct2 x_0);
        pff.enq(x_0);
    endmethod
    
    method ActionValue#(Struct2) deq_fifoCRqInput__0_0_3 ();
        pff.deq();
        return pff.first();
    endmethod

endmodule

interface Module90;
    method Action enq_fifoPInput__0_0_3 (Struct2 x_0);
    method ActionValue#(Struct2) deq_fifoPInput__0_0_3 ();
endinterface

module mkModule90 (Module90);
    FIFOF#(Struct2) pff <- mkSizedFIFOF(4);
    
    method Action enq_fifoPInput__0_0_3 (Struct2 x_0);
        pff.enq(x_0);
    endmethod
    
    method ActionValue#(Struct2) deq_fifoPInput__0_0_3 ();
        pff.deq();
        return pff.first();
    endmethod

endmodule

interface Module91;
    method Action enq_fifoN2I__0_0_3 (Struct38 x_0);
    method ActionValue#(Struct38) deq_fifoN2I__0_0_3 ();
endinterface

module mkModule91 (Module91);
    FIFOF#(Struct38) pff <- mkPipelineFIFOF();
    
    method Action enq_fifoN2I__0_0_3 (Struct38 x_0);
        pff.enq(x_0);
    endmethod
    
    method ActionValue#(Struct38) deq_fifoN2I__0_0_3 ();
        pff.deq();
        return pff.first();
    endmethod

endmodule

interface Module92;
    method Action enq_fifoI2L__0_0_3 (Struct38 x_0);
    method ActionValue#(Struct38) deq_fifoI2L__0_0_3 ();
endinterface

module mkModule92 (Module92);
    FIFOF#(Struct38) pff <- mkPipelineFIFOF();
    
    method Action enq_fifoI2L__0_0_3 (Struct38 x_0);
        pff.enq(x_0);
    endmethod
    
    method ActionValue#(Struct38) deq_fifoI2L__0_0_3 ();
        pff.deq();
        return pff.first();
    endmethod

endmodule

interface Module93;
    method Action enq_fifoL2E__0_0_3 (Struct41 x_0);
    method ActionValue#(Struct41) deq_fifoL2E__0_0_3 ();
endinterface

module mkModule93 (Module93);
    FIFOF#(Struct41) pff <- mkPipelineFIFOF();
    
    method Action enq_fifoL2E__0_0_3 (Struct41 x_0);
        pff.enq(x_0);
    endmethod
    
    method ActionValue#(Struct41) deq_fifoL2E__0_0_3 ();
        pff.deq();
        return pff.first();
    endmethod

endmodule

interface Module94;
    method Action enq_fifo_0_0_3_0 (Struct1 x_0);
    method ActionValue#(Struct1) deq_fifo_0_0_3_0 ();
endinterface

module mkModule94 (Module94);
    FIFOF#(Struct1) pff <- mkSizedFIFOF(2);
    
    method Action enq_fifo_0_0_3_0 (Struct1 x_0);
        pff.enq(x_0);
    endmethod
    
    method ActionValue#(Struct1) deq_fifo_0_0_3_0 ();
        pff.deq();
        return pff.first();
    endmethod

endmodule

interface Module95;
    method Action enq_fifo_0_0_3_1 (Struct1 x_0);
    method ActionValue#(Struct1) deq_fifo_0_0_3_1 ();
endinterface

module mkModule95 (Module95);
    FIFOF#(Struct1) pff <- mkSizedFIFOF(2);
    
    method Action enq_fifo_0_0_3_1 (Struct1 x_0);
        pff.enq(x_0);
    endmethod
    
    method ActionValue#(Struct1) deq_fifo_0_0_3_1 ();
        pff.deq();
        return pff.first();
    endmethod

endmodule

interface Module96;
    method Action enq_fifo_0_0_3_2 (Struct1 x_0);
    method ActionValue#(Struct1) deq_fifo_0_0_3_2 ();
endinterface

module mkModule96 (Module96);
    FIFOF#(Struct1) pff <- mkSizedFIFOF(2);
    
    method Action enq_fifo_0_0_3_2 (Struct1 x_0);
        pff.enq(x_0);
    endmethod
    
    method ActionValue#(Struct1) deq_fifo_0_0_3_2 ();
        pff.deq();
        return pff.first();
    endmethod

endmodule

interface Module97;
    method Action enq_fifo_0_0_3_0_0 (Struct1 x_0);
    method ActionValue#(Struct1) deq_fifo_0_0_3_0_0 ();
endinterface

module mkModule97 (Module97);
    FIFOF#(Struct1) pff <- mkSizedFIFOF(2);
    
    method Action enq_fifo_0_0_3_0_0 (Struct1 x_0);
        pff.enq(x_0);
    endmethod
    
    method ActionValue#(Struct1) deq_fifo_0_0_3_0_0 ();
        pff.deq();
        return pff.first();
    endmethod

endmodule

interface Module98;
    method Action enq_fifo_0_0_3_0_2 (Struct1 x_0);
    method ActionValue#(Struct1) deq_fifo_0_0_3_0_2 ();
endinterface

module mkModule98 (Module98);
    FIFOF#(Struct1) pff <- mkSizedFIFOF(2);
    
    method Action enq_fifo_0_0_3_0_2 (Struct1 x_0);
        pff.enq(x_0);
    endmethod
    
    method ActionValue#(Struct1) deq_fifo_0_0_3_0_2 ();
        pff.deq();
        return pff.first();
    endmethod

endmodule

interface Module99;
    method ActionValue#(Struct37) victims___0_0_3__findVictim (Bit#(64) x_0);
    method ActionValue#(Struct13) victims___0_0_3__getVictim (Bit#(1) x_0);
    method Action victims___0_0_3__setVictim (Struct44 x_0);
    method Action victims___0_0_3__registerVictim (Struct13 x_0);
    method ActionValue#(Struct13) victims___0_0_3__getFirstVictim ();
    method ActionValue#(Bool) victims___0_0_3__hasVictim ();
    method Action victims___0_0_3__setVictimRq (Bit#(64) x_0);
    method Action victims___0_0_3__releaseVictim (Bit#(64) x_0);
endinterface

module mkModule99
    (Module99);
    Reg#(Vector#(2, Struct13)) victimRegs___0_0_3 <- mkReg(unpack(0));
    
    // No rules in this module
    
    method ActionValue#(Struct37) victims___0_0_3__findVictim (Bit#(64) x_0);
        let x_1 = (victimRegs___0_0_3);
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
    
    method ActionValue#(Struct13) victims___0_0_3__getVictim (Bit#(1) x_0);
        let x_1 = (victimRegs___0_0_3);
        return (x_1)[x_0];
    endmethod
    
    method Action victims___0_0_3__setVictim (Struct44 x_0);
        let x_1 = (victimRegs___0_0_3);
        Struct13 x_2 = ((x_1)[(x_0).victim_idx]);
        Struct13 x_3 = (Struct13 {victim_valid : (Bool)'(True), victim_addr :
        (x_2).victim_addr, victim_info : (x_0).victim_info, victim_value :
        (x_0).victim_value, victim_req :
        (x_2).victim_req});
        victimRegs___0_0_3 <= update (x_1, (x_0).victim_idx, x_3);
    endmethod
    
    method Action victims___0_0_3__registerVictim (Struct13 x_0);
        let x_1 = (victimRegs___0_0_3);
        Struct37 x_2 = ((((x_1)[(Bit#(1))'(1'h1)]).victim_valid ?
        ((((x_1)[(Bit#(1))'(1'h0)]).victim_valid ? (Struct37 {valid :
        (Bool)'(False), data : unpack(0)}) : (Struct37 {valid :
        (Bool)'(True), data : (Bit#(1))'(1'h0)}))) : (Struct37 {valid :
        (Bool)'(True), data : (Bit#(1))'(1'h1)})));
        when ((x_2).valid, noAction);
        Bit#(1) x_3 = ((x_2).data);
        victimRegs___0_0_3 <= update (x_1, x_3, x_0);
    endmethod
    
    method ActionValue#(Struct13) victims___0_0_3__getFirstVictim ();
        let x_1 = (victimRegs___0_0_3);
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
    
    method ActionValue#(Bool) victims___0_0_3__hasVictim ();
        let x_1 = (victimRegs___0_0_3);
        Bool x_2 = (((((x_1)[(Bit#(1))'(1'h1)]).victim_valid) && (!
        (((x_1)[(Bit#(1))'(1'h1)]).victim_req)) ? ((Bool)'(True)) :
        (((((x_1)[(Bit#(1))'(1'h0)]).victim_valid) && (!
        (((x_1)[(Bit#(1))'(1'h0)]).victim_req)) ? ((Bool)'(True)) :
        ((Bool)'(False))))));
        return x_2;
    endmethod
    
    method Action victims___0_0_3__setVictimRq (Bit#(64) x_0);
        let x_1 = (victimRegs___0_0_3);
        Struct13 x_2 =
        ((x_1)[(Bit#(1))'(1'h1)]);
        if (((x_2).victim_valid) && (((x_2).victim_addr) == (x_0)))
            begin
            Struct13 x_3 = (Struct13 {victim_valid : (x_2).victim_valid,
            victim_addr : (x_2).victim_addr, victim_info : (x_2).victim_info,
            victim_value : (x_2).victim_value, victim_req :
            (Bool)'(True)});
            victimRegs___0_0_3 <= update (x_1, (Bit#(1))'(1'h1), x_3);
        end else begin
            Struct13 x_4 =
            ((x_1)[(Bit#(1))'(1'h0)]);
            if (((x_4).victim_valid) && (((x_4).victim_addr) == (x_0)))
                begin
                Struct13 x_5 = (Struct13 {victim_valid : (x_4).victim_valid,
                victim_addr : (x_4).victim_addr, victim_info :
                (x_4).victim_info, victim_value : (x_4).victim_value,
                victim_req : (Bool)'(True)});
                victimRegs___0_0_3 <= update (x_1, (Bit#(1))'(1'h0), x_5);
            end else begin
                
            end
        end
    endmethod
    
    method Action victims___0_0_3__releaseVictim (Bit#(64) x_0);
        let x_1 = (victimRegs___0_0_3);
        Struct13 x_2 =
        ((x_1)[(Bit#(1))'(1'h0)]);
        if (((x_2).victim_valid) && (((x_2).victim_addr) == (x_0)))
            begin
            victimRegs___0_0_3 <= update (x_1, (Bit#(1))'(1'h0), unpack(0));
        end else begin
            Struct13 x_3 =
            ((x_1)[(Bit#(1))'(1'h1)]);
            if (((x_3).victim_valid) && (((x_3).victim_addr) == (x_0)))
                begin
                victimRegs___0_0_3 <= update (x_1, (Bit#(1))'(1'h1),
                unpack(0));
            end else begin
                
            end
        end
    endmethod
endmodule

interface Module100;
    method Action rdReq_infoRam___0_0_3__3 (Bit#(8) x_0);
    method Action wrReq_infoRam___0_0_3__3 (Struct47 x_0);
    method ActionValue#(Struct45) rdResp_infoRam___0_0_3__3 ();
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
    
    method Action rdReq_infoRam___0_0_3__3 (Bit#(8) x_0) if(initDone);
        bram.rdReq(x_0);
    endmethod
    
    method Action wrReq_infoRam___0_0_3__3 (Struct47 x_0) if(initDone);
        bram.wrReq(x_0.addr, x_0.datain);
    endmethod
    
    method ActionValue#(Struct45) rdResp_infoRam___0_0_3__3 () if(initDone);
        bram.deqRdResp ();
        let data = bram.rdResp ();
        return data;
    endmethod
    

endmodule

interface Module101;
    method Action rdReq_infoRam___0_0_3__2 (Bit#(8) x_0);
    method Action wrReq_infoRam___0_0_3__2 (Struct47 x_0);
    method ActionValue#(Struct45) rdResp_infoRam___0_0_3__2 ();
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
    
    method Action rdReq_infoRam___0_0_3__2 (Bit#(8) x_0) if(initDone);
        bram.rdReq(x_0);
    endmethod
    
    method Action wrReq_infoRam___0_0_3__2 (Struct47 x_0) if(initDone);
        bram.wrReq(x_0.addr, x_0.datain);
    endmethod
    
    method ActionValue#(Struct45) rdResp_infoRam___0_0_3__2 () if(initDone);
        bram.deqRdResp ();
        let data = bram.rdResp ();
        return data;
    endmethod
    

endmodule

interface Module102;
    method Action rdReq_infoRam___0_0_3__1 (Bit#(8) x_0);
    method Action wrReq_infoRam___0_0_3__1 (Struct47 x_0);
    method ActionValue#(Struct45) rdResp_infoRam___0_0_3__1 ();
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
    
    method Action rdReq_infoRam___0_0_3__1 (Bit#(8) x_0) if(initDone);
        bram.rdReq(x_0);
    endmethod
    
    method Action wrReq_infoRam___0_0_3__1 (Struct47 x_0) if(initDone);
        bram.wrReq(x_0.addr, x_0.datain);
    endmethod
    
    method ActionValue#(Struct45) rdResp_infoRam___0_0_3__1 () if(initDone);
        bram.deqRdResp ();
        let data = bram.rdResp ();
        return data;
    endmethod
    

endmodule

interface Module103;
    method Action rdReq_infoRam___0_0_3__0 (Bit#(8) x_0);
    method Action wrReq_infoRam___0_0_3__0 (Struct47 x_0);
    method ActionValue#(Struct45) rdResp_infoRam___0_0_3__0 ();
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
    
    method Action rdReq_infoRam___0_0_3__0 (Bit#(8) x_0) if(initDone);
        bram.rdReq(x_0);
    endmethod
    
    method Action wrReq_infoRam___0_0_3__0 (Struct47 x_0) if(initDone);
        bram.wrReq(x_0.addr, x_0.datain);
    endmethod
    
    method ActionValue#(Struct45) rdResp_infoRam___0_0_3__0 () if(initDone);
        bram.deqRdResp ();
        let data = bram.rdResp ();
        return data;
    endmethod
    

endmodule

interface Module104;
    method Action rdReq_dataRam___0_0_3 (Bit#(10) x_0);
    method Action wrReq_dataRam___0_0_3 (Struct49 x_0);
    method ActionValue#(Vector#(4, Bit#(64))) rdResp_dataRam___0_0_3 ();
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
    
    method Action rdReq_dataRam___0_0_3 (Bit#(10) x_0) if(initDone);
        bram.rdReq(x_0);
    endmethod
    
    method Action wrReq_dataRam___0_0_3 (Struct49 x_0) if(initDone);
        bram.wrReq(x_0.addr, x_0.datain);
    endmethod
    
    method ActionValue#(Vector#(4, Bit#(64))) rdResp_dataRam___0_0_3 ()
    if(initDone);
        bram.deqRdResp ();
        let data = bram.rdResp ();
        return data;
    endmethod
    

endmodule

interface Module105;
    method Action rdReq_repRam___0_0_3 (Bit#(8) x_0);
    method Action wrReq_repRam___0_0_3 (Struct50 x_0);
    method ActionValue#(Vector#(4, Bit#(8))) rdResp_repRam___0_0_3 ();
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
    
    method Action rdReq_repRam___0_0_3 (Bit#(8) x_0) if(initDone);
        bram.rdReq(x_0);
    endmethod
    
    method Action wrReq_repRam___0_0_3 (Struct50 x_0) if(initDone);
        bram.wrReq(x_0.addr, x_0.datain);
    endmethod
    
    method ActionValue#(Vector#(4, Bit#(8))) rdResp_repRam___0_0_3 ()
    if(initDone);
        bram.deqRdResp ();
        let data = bram.rdResp ();
        return data;
    endmethod
    

endmodule

interface Module106;
    method ActionValue#(Struct14) getMSHR__0_0_3 (Bit#(2) x_0);
    method ActionValue#(Struct1) getMSHRRq__0_0_3 (Bit#(2) x_0);
    method ActionValue#(Struct36) getPRqSlot__0_0_3 (Struct35 x_0);
    method ActionValue#(Struct36) getCRqSlot__0_0_3 (Struct35 x_0);
    method ActionValue#(Struct35) getWait__0_0_3 ();
    method Action registerUL__0_0_3 (Struct43 x_0);
    method Action canImm__0_0_3 (Bit#(64) x_0);
    method Action setULImm__0_0_3 (Struct1 x_0);
    method ActionValue#(Bit#(2)) getULReady__0_0_3 (Bit#(64) x_0);
    method Action startRelease__0_0_3 (Bit#(2) x_0);
    method Action releaseMSHR__0_0_3 (Bit#(2) x_0);
endinterface

module mkModule106
    (Module106);
    Reg#(Vector#(4, Struct14)) mshrs__0_0_3 <- mkReg(unpack(0));
    Reg#(Vector#(4, Bit#(64))) maddrs__0_0_3 <- mkReg(unpack(0));
    Reg#(Vector#(4, Bit#(3))) msts__0_0_3 <- mkReg(unpack(0));
    Reg#(Vector#(4, Struct51)) mnexts__0_0_3 <- mkReg(unpack(0));
    Reg#(Vector#(4, Struct1)) rqs__0_0_3 <- mkReg(unpack(0));
    
    // No rules in this module
    
    method ActionValue#(Struct14) getMSHR__0_0_3 (Bit#(2) x_0);
        let x_1 = (mshrs__0_0_3);
        return (x_1)[x_0];
    endmethod
    
    method ActionValue#(Struct1) getMSHRRq__0_0_3 (Bit#(2) x_0);
        let x_1 = (rqs__0_0_3);
        return (x_1)[x_0];
    endmethod
    
    method ActionValue#(Struct36) getPRqSlot__0_0_3 (Struct35 x_0);
        let x_1 = (mshrs__0_0_3);
        let x_2 = (maddrs__0_0_3);
        let x_3 = (msts__0_0_3);
        let x_4 = (mnexts__0_0_3);
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
            mshrs__0_0_3 <= update (x_1, x_7, Struct14 {m_is_ul : unpack(0),
            m_qidx : (x_0).r_msg_from, m_rsb : unpack(0), m_dl_rss_from :
            unpack(0), m_dl_rss_recv : unpack(0)});
            maddrs__0_0_3 <= update (x_2, x_7,
            ((x_0).r_msg).addr);
            msts__0_0_3 <= update (x_3, x_7, (x_11 ? ((Bit#(3))'(3'h1)) :
            ((Bit#(3))'(3'h4))));
            let x_13 = (rqs__0_0_3);
            rqs__0_0_3 <= update (x_13, x_7,
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
                mnexts__0_0_3 <= update (x_4, x_14, Struct51 {valid :
                (Bool)'(True), data : x_7});
            end else begin
                
            end
        end else begin
            
        end
        return x_12;
    endmethod
    
    method ActionValue#(Struct36) getCRqSlot__0_0_3 (Struct35 x_0);
        let x_1 = (mshrs__0_0_3);
        let x_2 = (maddrs__0_0_3);
        let x_3 = (msts__0_0_3);
        let x_4 = (mnexts__0_0_3);
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
            mshrs__0_0_3 <= update (x_1, x_7, Struct14 {m_is_ul : unpack(0),
            m_qidx : (x_0).r_msg_from, m_rsb : unpack(0), m_dl_rss_from :
            unpack(0), m_dl_rss_recv : unpack(0)});
            maddrs__0_0_3 <= update (x_2, x_7,
            ((x_0).r_msg).addr);
            msts__0_0_3 <= update (x_3, x_7, (x_14 ? ((Bit#(3))'(3'h1)) :
            ((Bit#(3))'(3'h4))));
            let x_16 = (rqs__0_0_3);
            rqs__0_0_3 <= update (x_16, x_7,
            (x_0).r_msg);
            if (x_14) begin
                Bit#(2) x_17 = ((x_12 ? ((x_10).data) :
                ((x_11).data)));
                Struct51 x_18 = ((x_4)[x_17]);
                mnexts__0_0_3 <= update (x_4, x_17, Struct51 {valid :
                (Bool)'(True), data : x_7});
            end else begin
                
            end
        end else begin
            
        end
        return x_15;
    endmethod
    
    method ActionValue#(Struct35) getWait__0_0_3 ();
        let x_1 = (mshrs__0_0_3);
        let x_2 = (maddrs__0_0_3);
        let x_3 = (msts__0_0_3);
        let x_4 = (rqs__0_0_3);
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
        msts__0_0_3 <= update (x_3, x_6, (Bit#(3))'(3'h4));
        Struct35 x_11 = (Struct35 {r_id : x_6, r_msg : x_9, r_msg_from :
        (x_7).m_qidx});
        return x_11;
    endmethod
    
    method Action registerUL__0_0_3 (Struct43 x_0);
        let x_1 = (mshrs__0_0_3);
        let x_2 = (msts__0_0_3);
        Bit#(2) x_3 = ((x_0).r_id);
        mshrs__0_0_3 <= update (x_1, x_3, Struct14 {m_is_ul : (Bool)'(True),
        m_qidx : {((Bit#(2))'(2'h2)),((x_0).r_ul_rsbTo)}, m_rsb :
        (x_0).r_ul_rsb, m_dl_rss_from : unpack(0), m_dl_rss_recv :
        unpack(0)});
        msts__0_0_3 <= update (x_2, x_3, (Bit#(3))'(3'h5));
    endmethod
    
    method Action canImm__0_0_3 (Bit#(64) x_0);
        let x_1 = (maddrs__0_0_3);
        let x_2 = (msts__0_0_3);
        let x_3 = (mnexts__0_0_3);
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
    
    method Action setULImm__0_0_3 (Struct1 x_0);
        let x_1 = (mshrs__0_0_3);
        let x_2 = (maddrs__0_0_3);
        let x_3 = (msts__0_0_3);
        let x_4 = (rqs__0_0_3);
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
        mshrs__0_0_3 <= update (x_1, x_6, Struct14 {m_is_ul : (Bool)'(True),
        m_qidx : unpack(0), m_rsb : (Bool)'(False), m_dl_rss_from :
        unpack(0), m_dl_rss_recv : unpack(0)});
        maddrs__0_0_3 <= update (x_2, x_6, (x_0).addr);
        msts__0_0_3 <= update (x_3, x_6, (Bit#(3))'(3'h5));
        rqs__0_0_3 <= update (x_4, x_6, x_0);
    endmethod
    
    method ActionValue#(Bit#(2)) getULReady__0_0_3 (Bit#(64) x_0);
        let x_1 = (mshrs__0_0_3);
        let x_2 = (maddrs__0_0_3);
        let x_3 = (msts__0_0_3);
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
    
    method Action startRelease__0_0_3 (Bit#(2) x_0);
        let x_1 = (msts__0_0_3);
        msts__0_0_3 <= update (x_1, x_0, (Bit#(3))'(3'h6));
    endmethod
    
    method Action releaseMSHR__0_0_3 (Bit#(2) x_0);
        let x_1 = (mshrs__0_0_3);
        let x_2 = (msts__0_0_3);
        let x_3 = (mnexts__0_0_3);
        mshrs__0_0_3 <= update (x_1, x_0, unpack(0));
        mnexts__0_0_3 <= update (x_3, x_0, unpack(0));
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
        msts__0_0_3 <= x_8;
    endmethod
endmodule

interface Module107;
    
endinterface

module mkModule107#(function ActionValue#(Struct1) deq_fifo_0_0_3_0(),
    function ActionValue#(Struct1) deq_fifo_0_0_2_0(),
    function ActionValue#(Struct1) deq_fifo_0_0_1_0(),
    function Action enq_fifoCRqInput__0_0(Struct2 _),
    function ActionValue#(Struct1) deq_fifo_0_0_0_0())
    (Module107);
    Reg#(Bit#(2)) rr_cRq4__0_0 <- mkReg(unpack(0));
    
    rule inc_rr_cRq4__0_0;
        let x_0 = (rr_cRq4__0_0);
        rr_cRq4__0_0 <= (x_0) + ((Bit#(2))'(2'h1));
    endrule
    
    rule accept0_cRq4__0_0;
        let x_0 = (rr_cRq4__0_0);
        when ((x_0) == ((Bit#(2))'(2'h0)), noAction);
        let x_1 <- deq_fifo_0_0_0_0();
        Struct2 x_2 = (Struct2 {in_msg : x_1, in_msg_from :
        {((Bit#(2))'(2'h0)),((Bit#(2))'(2'h0))}});
        let x_3 <- enq_fifoCRqInput__0_0(x_2);
    endrule
    
    rule accept1_cRq4__0_0;
        let x_0 = (rr_cRq4__0_0);
        when ((x_0) == ((Bit#(2))'(2'h1)), noAction);
        let x_1 <- deq_fifo_0_0_1_0();
        Struct2 x_2 = (Struct2 {in_msg : x_1, in_msg_from :
        {((Bit#(2))'(2'h0)),((Bit#(2))'(2'h1))}});
        let x_3 <- enq_fifoCRqInput__0_0(x_2);
    endrule
    
    rule accept2_cRq4__0_0;
        let x_0 = (rr_cRq4__0_0);
        when ((x_0) == ((Bit#(2))'(2'h2)), noAction);
        let x_1 <- deq_fifo_0_0_2_0();
        Struct2 x_2 = (Struct2 {in_msg : x_1, in_msg_from :
        {((Bit#(2))'(2'h0)),((Bit#(2))'(2'h2))}});
        let x_3 <- enq_fifoCRqInput__0_0(x_2);
    endrule
    
    rule accept3_cRq4__0_0;
        let x_0 = (rr_cRq4__0_0);
        when ((x_0) == ((Bit#(2))'(2'h3)), noAction);
        let x_1 <- deq_fifo_0_0_3_0();
        Struct2 x_2 = (Struct2 {in_msg : x_1, in_msg_from :
        {((Bit#(2))'(2'h0)),((Bit#(2))'(2'h3))}});
        let x_3 <- enq_fifoCRqInput__0_0(x_2);
    endrule
    
    // No methods in this module
endmodule

interface Module108;
    
endinterface

module mkModule108#(function ActionValue#(Struct1) deq_fifo_0_0_3_1(),
    function ActionValue#(Struct1) deq_fifo_0_0_2_1(),
    function ActionValue#(Struct1) deq_fifo_0_0_1_1(),
    function Action enq_fifoCRsInput__0_0(Struct2 _),
    function ActionValue#(Struct1) deq_fifo_0_0_0_1())
    (Module108);
    Reg#(Bit#(2)) rr_cRs4__0_0 <- mkReg(unpack(0));
    
    rule inc_rr_cRs4__0_0;
        let x_0 = (rr_cRs4__0_0);
        rr_cRs4__0_0 <= (x_0) + ((Bit#(2))'(2'h1));
    endrule
    
    rule accept0_cRs4__0_0;
        let x_0 = (rr_cRs4__0_0);
        when ((x_0) == ((Bit#(2))'(2'h0)), noAction);
        let x_1 <- deq_fifo_0_0_0_1();
        Struct2 x_2 = (Struct2 {in_msg : x_1, in_msg_from :
        {((Bit#(2))'(2'h1)),((Bit#(2))'(2'h0))}});
        let x_3 <- enq_fifoCRsInput__0_0(x_2);
    endrule
    
    rule accept1_cRs4__0_0;
        let x_0 = (rr_cRs4__0_0);
        when ((x_0) == ((Bit#(2))'(2'h1)), noAction);
        let x_1 <- deq_fifo_0_0_1_1();
        Struct2 x_2 = (Struct2 {in_msg : x_1, in_msg_from :
        {((Bit#(2))'(2'h1)),((Bit#(2))'(2'h1))}});
        let x_3 <- enq_fifoCRsInput__0_0(x_2);
    endrule
    
    rule accept2_cRs4__0_0;
        let x_0 = (rr_cRs4__0_0);
        when ((x_0) == ((Bit#(2))'(2'h2)), noAction);
        let x_1 <- deq_fifo_0_0_2_1();
        Struct2 x_2 = (Struct2 {in_msg : x_1, in_msg_from :
        {((Bit#(2))'(2'h1)),((Bit#(2))'(2'h2))}});
        let x_3 <- enq_fifoCRsInput__0_0(x_2);
    endrule
    
    rule accept3_cRs4__0_0;
        let x_0 = (rr_cRs4__0_0);
        when ((x_0) == ((Bit#(2))'(2'h3)), noAction);
        let x_1 <- deq_fifo_0_0_3_1();
        Struct2 x_2 = (Struct2 {in_msg : x_1, in_msg_from :
        {((Bit#(2))'(2'h1)),((Bit#(2))'(2'h3))}});
        let x_3 <- enq_fifoCRsInput__0_0(x_2);
    endrule
    
    // No methods in this module
endmodule

interface Module109;
    
endinterface

module mkModule109#(function Action enq_fifoPInput__0_0(Struct2 _),
    function ActionValue#(Struct1) deq_fifo_0_0_2())
    (Module109);
    
    rule parent_convert__0_0;
        let x_0 <- deq_fifo_0_0_2();
        Struct2 x_1 = (Struct2 {in_msg : x_0, in_msg_from :
        {((Bit#(2))'(2'h2)),((Bit#(2))'(2'h0))}});
        let x_2 <- enq_fifoPInput__0_0(x_1);
    endrule
    
    // No methods in this module
endmodule

interface Module110;
    method Action makeEnq_parentChildren_0_0 (Struct18 x_0);
    method Action broadcast_parentChildren_0_0 (Struct21 x_0);
endinterface

module mkModule110#(function Action enq_fifo_0_0_0_2(Struct1 _),
    function Action enq_fifo_0_0_1_2(Struct1 _),
    function Action enq_fifo_0_0_2_2(Struct1 _),
    function Action enq_fifo_0_0_3_2(Struct1 _),
    function Action enq_fifo_0_0_1(Struct1 _),
    function Action enq_fifo_0_0_0(Struct1 _))
    (Module110);
    
    // No rules in this module
    
    method Action makeEnq_parentChildren_0_0 (Struct18 x_0);
        if (((x_0).enq_type) == ((Bit#(2))'(2'h0))) begin
            let x_1 <- enq_fifo_0_0_0((x_0).enq_msg);
        end else
            begin
            if (((x_0).enq_type) == ((Bit#(2))'(2'h1))) begin
                let x_2 <- enq_fifo_0_0_1((x_0).enq_msg);
            end else begin
                Bit#(2) x_3 = ((x_0).enq_ch_idx);
                Struct1 x_4 =
                ((x_0).enq_msg);
                if ((x_3) == ((Bit#(2))'(2'h3))) begin
                    let x_5 <- enq_fifo_0_0_3_2(x_4);
                end else
                    begin
                    if ((x_3) == ((Bit#(2))'(2'h2))) begin
                        let x_6 <- enq_fifo_0_0_2_2(x_4);
                    end else
                        begin
                        if ((x_3) == ((Bit#(2))'(2'h1))) begin
                            let x_7 <- enq_fifo_0_0_1_2(x_4);
                        end else
                            begin
                            if ((x_3) == ((Bit#(2))'(2'h0))) begin
                                let x_8 <- enq_fifo_0_0_0_2(x_4);
                            end else begin
                                
                            end
                        end
                    end
                end
            end
        end
    endmethod
    
    method Action broadcast_parentChildren_0_0 (Struct21 x_0);
        Bit#(4) x_1 = ((x_0).cs_inds);
        Struct1 x_2 =
        ((x_0).cs_msg);
        if (((x_1) | (((Bit#(4))'(4'h1)) << ((Bit#(2))'(2'h3)))) == (x_1))
            begin
            let x_3 <- enq_fifo_0_0_3_2(x_2);
        end else begin
            
        end
        if (((x_1) | (((Bit#(4))'(4'h1)) << ((Bit#(2))'(2'h2)))) == (x_1))
            begin
            let x_5 <- enq_fifo_0_0_2_2(x_2);
        end else begin
            
        end
        if (((x_1) | (((Bit#(4))'(4'h1)) << ((Bit#(2))'(2'h1)))) == (x_1))
            begin
            let x_7 <- enq_fifo_0_0_1_2(x_2);
        end else begin
            
        end
        if (((x_1) | (((Bit#(4))'(4'h1)) << ((Bit#(2))'(2'h0)))) == (x_1))
            begin
            let x_9 <- enq_fifo_0_0_0_2(x_2);
        end else begin
            
        end
    endmethod
endmodule

interface Module111;
    method Action repGetRq___0_0 (Bit#(10) x_0);
    method ActionValue#(Vector#(16, Bit#(8))) repGetRs___0_0 ();
    method Action repAccess___0_0 (Struct30 x_0);
endinterface

module mkModule111#(function Action wrReq_repRam___0_0(Struct34 _),
    function ActionValue#(Vector#(16, Bit#(8))) rdResp_repRam___0_0(),
    function Action rdReq_repRam___0_0(Bit#(10) _))
    (Module111);
    
    // No rules in this module
    
    method Action repGetRq___0_0 (Bit#(10) x_0);
        let x_1 <- rdReq_repRam___0_0(x_0);
    endmethod
    
    method ActionValue#(Vector#(16, Bit#(8))) repGetRs___0_0 ();
        let x_1 <- rdResp_repRam___0_0();
        return x_1;
    endmethod
    
    method Action repAccess___0_0 (Struct30 x_0);
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
        let x_38 <- wrReq_repRam___0_0(x_37);
    endmethod
endmodule

interface Module112;
    
endinterface

module mkModule112#(function Action enq_fifoCRqInput__0_0_0(Struct2 _),
    function ActionValue#(Struct1) deq_fifo_0_0_0_0_0())
    (Module112);
    
    rule child_convert__0_0_0;
        let x_0 <- deq_fifo_0_0_0_0_0();
        Struct2 x_1 = (Struct2 {in_msg : x_0, in_msg_from :
        {((Bit#(2))'(2'h0)),((Bit#(2))'(2'h0))}});
        let x_2 <- enq_fifoCRqInput__0_0_0(x_1);
    endrule
    
    // No methods in this module
endmodule

interface Module113;
    
endinterface

module mkModule113#(function Action enq_fifoPInput__0_0_0(Struct2 _),
    function ActionValue#(Struct1) deq_fifo_0_0_0_2())
    (Module113);
    
    rule parent_convert__0_0_0;
        let x_0 <- deq_fifo_0_0_0_2();
        Struct2 x_1 = (Struct2 {in_msg : x_0, in_msg_from :
        {((Bit#(2))'(2'h2)),((Bit#(2))'(2'h0))}});
        let x_2 <- enq_fifoPInput__0_0_0(x_1);
    endrule
    
    // No methods in this module
endmodule

interface Module114;
    method Action makeEnq_parentChildren_0_0_0 (Struct18 x_0);
endinterface

module mkModule114#(function Action enq_fifo_0_0_0_0_2(Struct1 _),
    function Action enq_fifo_0_0_0_1(Struct1 _),
    function Action enq_fifo_0_0_0_0(Struct1 _))
    (Module114);
    
    // No rules in this module
    
    method Action makeEnq_parentChildren_0_0_0 (Struct18 x_0);
        if (((x_0).enq_type) == ((Bit#(2))'(2'h0))) begin
            let x_1 <- enq_fifo_0_0_0_0((x_0).enq_msg);
        end else
            begin
            if (((x_0).enq_type) == ((Bit#(2))'(2'h1))) begin
                let x_2 <- enq_fifo_0_0_0_1((x_0).enq_msg);
            end else begin
                Struct1 x_3 = ((x_0).enq_msg);
                let x_4 <- enq_fifo_0_0_0_0_2(x_3);
            end
        end
    endmethod
endmodule

interface Module115;
    method Action repGetRq___0_0_0 (Bit#(8) x_0);
    method ActionValue#(Vector#(4, Bit#(8))) repGetRs___0_0_0 ();
    method Action repAccess___0_0_0 (Struct48 x_0);
endinterface

module mkModule115#(function Action wrReq_repRam___0_0_0(Struct50 _),
    function ActionValue#(Vector#(4, Bit#(8))) rdResp_repRam___0_0_0(),
    function Action rdReq_repRam___0_0_0(Bit#(8) _))
    (Module115);
    
    // No rules in this module
    
    method Action repGetRq___0_0_0 (Bit#(8) x_0);
        let x_1 <- rdReq_repRam___0_0_0(x_0);
    endmethod
    
    method ActionValue#(Vector#(4, Bit#(8))) repGetRs___0_0_0 ();
        let x_1 <- rdResp_repRam___0_0_0();
        return x_1;
    endmethod
    
    method Action repAccess___0_0_0 (Struct48 x_0);
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
        let x_14 <- wrReq_repRam___0_0_0(x_13);
    endmethod
endmodule

interface Module116;
    
endinterface

module mkModule116#(function Action enq_fifoCRqInput__0_0_1(Struct2 _),
    function ActionValue#(Struct1) deq_fifo_0_0_1_0_0())
    (Module116);
    
    rule child_convert__0_0_1;
        let x_0 <- deq_fifo_0_0_1_0_0();
        Struct2 x_1 = (Struct2 {in_msg : x_0, in_msg_from :
        {((Bit#(2))'(2'h0)),((Bit#(2))'(2'h0))}});
        let x_2 <- enq_fifoCRqInput__0_0_1(x_1);
    endrule
    
    // No methods in this module
endmodule

interface Module117;
    
endinterface

module mkModule117#(function Action enq_fifoPInput__0_0_1(Struct2 _),
    function ActionValue#(Struct1) deq_fifo_0_0_1_2())
    (Module117);
    
    rule parent_convert__0_0_1;
        let x_0 <- deq_fifo_0_0_1_2();
        Struct2 x_1 = (Struct2 {in_msg : x_0, in_msg_from :
        {((Bit#(2))'(2'h2)),((Bit#(2))'(2'h1))}});
        let x_2 <- enq_fifoPInput__0_0_1(x_1);
    endrule
    
    // No methods in this module
endmodule

interface Module118;
    method Action makeEnq_parentChildren_0_0_1 (Struct18 x_0);
endinterface

module mkModule118#(function Action enq_fifo_0_0_1_0_2(Struct1 _),
    function Action enq_fifo_0_0_1_1(Struct1 _),
    function Action enq_fifo_0_0_1_0(Struct1 _))
    (Module118);
    
    // No rules in this module
    
    method Action makeEnq_parentChildren_0_0_1 (Struct18 x_0);
        if (((x_0).enq_type) == ((Bit#(2))'(2'h0))) begin
            let x_1 <- enq_fifo_0_0_1_0((x_0).enq_msg);
        end else
            begin
            if (((x_0).enq_type) == ((Bit#(2))'(2'h1))) begin
                let x_2 <- enq_fifo_0_0_1_1((x_0).enq_msg);
            end else begin
                Struct1 x_3 = ((x_0).enq_msg);
                let x_4 <- enq_fifo_0_0_1_0_2(x_3);
            end
        end
    endmethod
endmodule

interface Module119;
    method Action repGetRq___0_0_1 (Bit#(8) x_0);
    method ActionValue#(Vector#(4, Bit#(8))) repGetRs___0_0_1 ();
    method Action repAccess___0_0_1 (Struct48 x_0);
endinterface

module mkModule119#(function Action wrReq_repRam___0_0_1(Struct50 _),
    function ActionValue#(Vector#(4, Bit#(8))) rdResp_repRam___0_0_1(),
    function Action rdReq_repRam___0_0_1(Bit#(8) _))
    (Module119);
    
    // No rules in this module
    
    method Action repGetRq___0_0_1 (Bit#(8) x_0);
        let x_1 <- rdReq_repRam___0_0_1(x_0);
    endmethod
    
    method ActionValue#(Vector#(4, Bit#(8))) repGetRs___0_0_1 ();
        let x_1 <- rdResp_repRam___0_0_1();
        return x_1;
    endmethod
    
    method Action repAccess___0_0_1 (Struct48 x_0);
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
        let x_14 <- wrReq_repRam___0_0_1(x_13);
    endmethod
endmodule

interface Module120;
    
endinterface

module mkModule120#(function Action enq_fifoCRqInput__0_0_2(Struct2 _),
    function ActionValue#(Struct1) deq_fifo_0_0_2_0_0())
    (Module120);
    
    rule child_convert__0_0_2;
        let x_0 <- deq_fifo_0_0_2_0_0();
        Struct2 x_1 = (Struct2 {in_msg : x_0, in_msg_from :
        {((Bit#(2))'(2'h0)),((Bit#(2))'(2'h0))}});
        let x_2 <- enq_fifoCRqInput__0_0_2(x_1);
    endrule
    
    // No methods in this module
endmodule

interface Module121;
    
endinterface

module mkModule121#(function Action enq_fifoPInput__0_0_2(Struct2 _),
    function ActionValue#(Struct1) deq_fifo_0_0_2_2())
    (Module121);
    
    rule parent_convert__0_0_2;
        let x_0 <- deq_fifo_0_0_2_2();
        Struct2 x_1 = (Struct2 {in_msg : x_0, in_msg_from :
        {((Bit#(2))'(2'h2)),((Bit#(2))'(2'h2))}});
        let x_2 <- enq_fifoPInput__0_0_2(x_1);
    endrule
    
    // No methods in this module
endmodule

interface Module122;
    method Action makeEnq_parentChildren_0_0_2 (Struct18 x_0);
endinterface

module mkModule122#(function Action enq_fifo_0_0_2_0_2(Struct1 _),
    function Action enq_fifo_0_0_2_1(Struct1 _),
    function Action enq_fifo_0_0_2_0(Struct1 _))
    (Module122);
    
    // No rules in this module
    
    method Action makeEnq_parentChildren_0_0_2 (Struct18 x_0);
        if (((x_0).enq_type) == ((Bit#(2))'(2'h0))) begin
            let x_1 <- enq_fifo_0_0_2_0((x_0).enq_msg);
        end else
            begin
            if (((x_0).enq_type) == ((Bit#(2))'(2'h1))) begin
                let x_2 <- enq_fifo_0_0_2_1((x_0).enq_msg);
            end else begin
                Struct1 x_3 = ((x_0).enq_msg);
                let x_4 <- enq_fifo_0_0_2_0_2(x_3);
            end
        end
    endmethod
endmodule

interface Module123;
    method Action repGetRq___0_0_2 (Bit#(8) x_0);
    method ActionValue#(Vector#(4, Bit#(8))) repGetRs___0_0_2 ();
    method Action repAccess___0_0_2 (Struct48 x_0);
endinterface

module mkModule123#(function Action wrReq_repRam___0_0_2(Struct50 _),
    function ActionValue#(Vector#(4, Bit#(8))) rdResp_repRam___0_0_2(),
    function Action rdReq_repRam___0_0_2(Bit#(8) _))
    (Module123);
    
    // No rules in this module
    
    method Action repGetRq___0_0_2 (Bit#(8) x_0);
        let x_1 <- rdReq_repRam___0_0_2(x_0);
    endmethod
    
    method ActionValue#(Vector#(4, Bit#(8))) repGetRs___0_0_2 ();
        let x_1 <- rdResp_repRam___0_0_2();
        return x_1;
    endmethod
    
    method Action repAccess___0_0_2 (Struct48 x_0);
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
        let x_14 <- wrReq_repRam___0_0_2(x_13);
    endmethod
endmodule

interface Module124;
    
endinterface

module mkModule124#(function Action enq_fifoCRqInput__0_0_3(Struct2 _),
    function ActionValue#(Struct1) deq_fifo_0_0_3_0_0())
    (Module124);
    
    rule child_convert__0_0_3;
        let x_0 <- deq_fifo_0_0_3_0_0();
        Struct2 x_1 = (Struct2 {in_msg : x_0, in_msg_from :
        {((Bit#(2))'(2'h0)),((Bit#(2))'(2'h0))}});
        let x_2 <- enq_fifoCRqInput__0_0_3(x_1);
    endrule
    
    // No methods in this module
endmodule

interface Module125;
    
endinterface

module mkModule125#(function Action enq_fifoPInput__0_0_3(Struct2 _),
    function ActionValue#(Struct1) deq_fifo_0_0_3_2())
    (Module125);
    
    rule parent_convert__0_0_3;
        let x_0 <- deq_fifo_0_0_3_2();
        Struct2 x_1 = (Struct2 {in_msg : x_0, in_msg_from :
        {((Bit#(2))'(2'h2)),((Bit#(2))'(2'h3))}});
        let x_2 <- enq_fifoPInput__0_0_3(x_1);
    endrule
    
    // No methods in this module
endmodule

interface Module126;
    method Action makeEnq_parentChildren_0_0_3 (Struct18 x_0);
endinterface

module mkModule126#(function Action enq_fifo_0_0_3_0_2(Struct1 _),
    function Action enq_fifo_0_0_3_1(Struct1 _),
    function Action enq_fifo_0_0_3_0(Struct1 _))
    (Module126);
    
    // No rules in this module
    
    method Action makeEnq_parentChildren_0_0_3 (Struct18 x_0);
        if (((x_0).enq_type) == ((Bit#(2))'(2'h0))) begin
            let x_1 <- enq_fifo_0_0_3_0((x_0).enq_msg);
        end else
            begin
            if (((x_0).enq_type) == ((Bit#(2))'(2'h1))) begin
                let x_2 <- enq_fifo_0_0_3_1((x_0).enq_msg);
            end else begin
                Struct1 x_3 = ((x_0).enq_msg);
                let x_4 <- enq_fifo_0_0_3_0_2(x_3);
            end
        end
    endmethod
endmodule

interface Module127;
    method Action repGetRq___0_0_3 (Bit#(8) x_0);
    method ActionValue#(Vector#(4, Bit#(8))) repGetRs___0_0_3 ();
    method Action repAccess___0_0_3 (Struct48 x_0);
endinterface

module mkModule127#(function Action wrReq_repRam___0_0_3(Struct50 _),
    function ActionValue#(Vector#(4, Bit#(8))) rdResp_repRam___0_0_3(),
    function Action rdReq_repRam___0_0_3(Bit#(8) _))
    (Module127);
    
    // No rules in this module
    
    method Action repGetRq___0_0_3 (Bit#(8) x_0);
        let x_1 <- rdReq_repRam___0_0_3(x_0);
    endmethod
    
    method ActionValue#(Vector#(4, Bit#(8))) repGetRs___0_0_3 ();
        let x_1 <- rdResp_repRam___0_0_3();
        return x_1;
    endmethod
    
    method Action repAccess___0_0_3 (Struct48 x_0);
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
        let x_14 <- wrReq_repRam___0_0_3(x_13);
    endmethod
endmodule

interface Module128;
    method Action cache___0_0__infoRq (Bit#(64) x_0);
    method ActionValue#(Struct9) cache___0_0__infoRsValueRq (Bit#(64) x_0);
    method ActionValue#(Vector#(4, Bit#(64))) cache___0_0__valueRsLineRq
    (Struct16 x_0);
endinterface

module mkModule128#(function Action wrReq_dataRam___0_0(Struct32 _),
    function Action wrReq_edirRam___0_0__7(Struct31 _),
    function Action wrReq_edirRam___0_0__6(Struct31 _),
    function Action wrReq_edirRam___0_0__5(Struct31 _),
    function Action wrReq_edirRam___0_0__4(Struct31 _),
    function Action wrReq_edirRam___0_0__3(Struct31 _),
    function Action wrReq_edirRam___0_0__2(Struct31 _),
    function Action wrReq_edirRam___0_0__1(Struct31 _),
    function Action wrReq_edirRam___0_0__0(Struct31 _),
    function Action repAccess___0_0(Struct30 _),
    function Action victims___0_0__registerVictim(Struct13 _),
    function Action wrReq_infoRam___0_0__15(Struct29 _),
    function Action wrReq_infoRam___0_0__14(Struct29 _),
    function Action wrReq_infoRam___0_0__13(Struct29 _),
    function Action wrReq_infoRam___0_0__12(Struct29 _),
    function Action wrReq_infoRam___0_0__11(Struct29 _),
    function Action wrReq_infoRam___0_0__10(Struct29 _),
    function Action wrReq_infoRam___0_0__9(Struct29 _),
    function Action wrReq_infoRam___0_0__8(Struct29 _),
    function Action wrReq_infoRam___0_0__7(Struct29 _),
    function Action wrReq_infoRam___0_0__6(Struct29 _),
    function Action wrReq_infoRam___0_0__5(Struct29 _),
    function Action wrReq_infoRam___0_0__4(Struct29 _),
    function Action wrReq_infoRam___0_0__3(Struct29 _),
    function Action wrReq_infoRam___0_0__2(Struct29 _),
    function Action wrReq_infoRam___0_0__1(Struct29 _),
    function Action wrReq_infoRam___0_0__0(Struct29 _),
    function ActionValue#(Vector#(4, Bit#(64))) rdResp_dataRam___0_0(),
    function Action rdReq_dataRam___0_0(Bit#(14) _),
    function ActionValue#(Vector#(16, Bit#(8))) repGetRs___0_0(),
    function ActionValue#(Struct26) rdResp_edirRam___0_0__7(),
    function ActionValue#(Struct26) rdResp_edirRam___0_0__6(),
    function ActionValue#(Struct26) rdResp_edirRam___0_0__5(),
    function ActionValue#(Struct26) rdResp_edirRam___0_0__4(),
    function ActionValue#(Struct26) rdResp_edirRam___0_0__3(),
    function ActionValue#(Struct26) rdResp_edirRam___0_0__2(),
    function ActionValue#(Struct26) rdResp_edirRam___0_0__1(),
    function ActionValue#(Struct26) rdResp_edirRam___0_0__0(),
    function ActionValue#(Struct24) rdResp_infoRam___0_0__15(),
    function ActionValue#(Struct24) rdResp_infoRam___0_0__14(),
    function ActionValue#(Struct24) rdResp_infoRam___0_0__13(),
    function ActionValue#(Struct24) rdResp_infoRam___0_0__12(),
    function ActionValue#(Struct24) rdResp_infoRam___0_0__11(),
    function ActionValue#(Struct24) rdResp_infoRam___0_0__10(),
    function ActionValue#(Struct24) rdResp_infoRam___0_0__9(),
    function ActionValue#(Struct24) rdResp_infoRam___0_0__8(),
    function ActionValue#(Struct24) rdResp_infoRam___0_0__7(),
    function ActionValue#(Struct24) rdResp_infoRam___0_0__6(),
    function ActionValue#(Struct24) rdResp_infoRam___0_0__5(),
    function ActionValue#(Struct24) rdResp_infoRam___0_0__4(),
    function ActionValue#(Struct24) rdResp_infoRam___0_0__3(),
    function ActionValue#(Struct24) rdResp_infoRam___0_0__2(),
    function ActionValue#(Struct24) rdResp_infoRam___0_0__1(),
    function ActionValue#(Struct24) rdResp_infoRam___0_0__0(),
    function Action repGetRq___0_0(Bit#(10) _),
    function Action rdReq_edirRam___0_0__7(Bit#(10) _),
    function Action rdReq_edirRam___0_0__6(Bit#(10) _),
    function Action rdReq_edirRam___0_0__5(Bit#(10) _),
    function Action rdReq_edirRam___0_0__4(Bit#(10) _),
    function Action rdReq_edirRam___0_0__3(Bit#(10) _),
    function Action rdReq_edirRam___0_0__2(Bit#(10) _),
    function Action rdReq_edirRam___0_0__1(Bit#(10) _),
    function Action rdReq_edirRam___0_0__0(Bit#(10) _),
    function Action rdReq_infoRam___0_0__15(Bit#(10) _),
    function Action rdReq_infoRam___0_0__14(Bit#(10) _),
    function Action rdReq_infoRam___0_0__13(Bit#(10) _),
    function Action rdReq_infoRam___0_0__12(Bit#(10) _),
    function Action rdReq_infoRam___0_0__11(Bit#(10) _),
    function Action rdReq_infoRam___0_0__10(Bit#(10) _),
    function Action rdReq_infoRam___0_0__9(Bit#(10) _),
    function Action rdReq_infoRam___0_0__8(Bit#(10) _),
    function Action rdReq_infoRam___0_0__7(Bit#(10) _),
    function Action rdReq_infoRam___0_0__6(Bit#(10) _),
    function Action rdReq_infoRam___0_0__5(Bit#(10) _),
    function Action rdReq_infoRam___0_0__4(Bit#(10) _),
    function Action rdReq_infoRam___0_0__3(Bit#(10) _),
    function Action rdReq_infoRam___0_0__2(Bit#(10) _),
    function Action rdReq_infoRam___0_0__1(Bit#(10) _),
    function Action rdReq_infoRam___0_0__0(Bit#(10) _))
    (Module128);
    
    // No rules in this module
    
    method Action cache___0_0__infoRq (Bit#(64) x_0);
        Bit#(10) x_1 = ((x_0)[14:5]);
        let x_2 <- rdReq_infoRam___0_0__0(x_1);
        let x_3 <- rdReq_infoRam___0_0__1(x_1);
        let x_4 <- rdReq_infoRam___0_0__2(x_1);
        let x_5 <- rdReq_infoRam___0_0__3(x_1);
        let x_6 <- rdReq_infoRam___0_0__4(x_1);
        let x_7 <- rdReq_infoRam___0_0__5(x_1);
        let x_8 <- rdReq_infoRam___0_0__6(x_1);
        let x_9 <- rdReq_infoRam___0_0__7(x_1);
        let x_10 <- rdReq_infoRam___0_0__8(x_1);
        let x_11 <- rdReq_infoRam___0_0__9(x_1);
        let x_12 <- rdReq_infoRam___0_0__10(x_1);
        let x_13 <- rdReq_infoRam___0_0__11(x_1);
        let x_14 <- rdReq_infoRam___0_0__12(x_1);
        let x_15 <- rdReq_infoRam___0_0__13(x_1);
        let x_16 <- rdReq_infoRam___0_0__14(x_1);
        let x_17 <- rdReq_infoRam___0_0__15(x_1);
        let x_18 <- rdReq_edirRam___0_0__0(x_1);
        let x_19 <- rdReq_edirRam___0_0__1(x_1);
        let x_20 <- rdReq_edirRam___0_0__2(x_1);
        let x_21 <- rdReq_edirRam___0_0__3(x_1);
        let x_22 <- rdReq_edirRam___0_0__4(x_1);
        let x_23 <- rdReq_edirRam___0_0__5(x_1);
        let x_24 <- rdReq_edirRam___0_0__6(x_1);
        let x_25 <- rdReq_edirRam___0_0__7(x_1);
        let x_26 <- repGetRq___0_0(x_1);
    endmethod
    
    method ActionValue#(Struct9) cache___0_0__infoRsValueRq (Bit#(64) x_0);
        Bit#(49) x_1 = ((x_0)[63:15]);
        Bit#(10) x_2 = ((x_0)[14:5]);
        Vector#(16, Struct24) x_3 = (unpack(0));
        let x_4 <- rdResp_infoRam___0_0__0();
        Vector#(16, Struct24) x_5 = (update (x_3, (Bit#(4))'(4'h0), x_4));
        let x_6 <- rdResp_infoRam___0_0__1();
        Vector#(16, Struct24) x_7 = (update (x_5, (Bit#(4))'(4'h1), x_6));
        let x_8 <- rdResp_infoRam___0_0__2();
        Vector#(16, Struct24) x_9 = (update (x_7, (Bit#(4))'(4'h2), x_8));
        let x_10 <- rdResp_infoRam___0_0__3();
        Vector#(16, Struct24) x_11 = (update (x_9, (Bit#(4))'(4'h3),
        x_10));
        let x_12 <- rdResp_infoRam___0_0__4();
        Vector#(16, Struct24) x_13 = (update (x_11, (Bit#(4))'(4'h4),
        x_12));
        let x_14 <- rdResp_infoRam___0_0__5();
        Vector#(16, Struct24) x_15 = (update (x_13, (Bit#(4))'(4'h5),
        x_14));
        let x_16 <- rdResp_infoRam___0_0__6();
        Vector#(16, Struct24) x_17 = (update (x_15, (Bit#(4))'(4'h6),
        x_16));
        let x_18 <- rdResp_infoRam___0_0__7();
        Vector#(16, Struct24) x_19 = (update (x_17, (Bit#(4))'(4'h7),
        x_18));
        let x_20 <- rdResp_infoRam___0_0__8();
        Vector#(16, Struct24) x_21 = (update (x_19, (Bit#(4))'(4'h8),
        x_20));
        let x_22 <- rdResp_infoRam___0_0__9();
        Vector#(16, Struct24) x_23 = (update (x_21, (Bit#(4))'(4'h9),
        x_22));
        let x_24 <- rdResp_infoRam___0_0__10();
        Vector#(16, Struct24) x_25 = (update (x_23, (Bit#(4))'(4'ha),
        x_24));
        let x_26 <- rdResp_infoRam___0_0__11();
        Vector#(16, Struct24) x_27 = (update (x_25, (Bit#(4))'(4'hb),
        x_26));
        let x_28 <- rdResp_infoRam___0_0__12();
        Vector#(16, Struct24) x_29 = (update (x_27, (Bit#(4))'(4'hc),
        x_28));
        let x_30 <- rdResp_infoRam___0_0__13();
        Vector#(16, Struct24) x_31 = (update (x_29, (Bit#(4))'(4'hd),
        x_30));
        let x_32 <- rdResp_infoRam___0_0__14();
        Vector#(16, Struct24) x_33 = (update (x_31, (Bit#(4))'(4'he),
        x_32));
        let x_34 <- rdResp_infoRam___0_0__15();
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
        let x_38 <- rdResp_edirRam___0_0__0();
        Vector#(8, Struct26) x_39 = (update (x_37, (Bit#(3))'(3'h0),
        x_38));
        let x_40 <- rdResp_edirRam___0_0__1();
        Vector#(8, Struct26) x_41 = (update (x_39, (Bit#(3))'(3'h1),
        x_40));
        let x_42 <- rdResp_edirRam___0_0__2();
        Vector#(8, Struct26) x_43 = (update (x_41, (Bit#(3))'(3'h2),
        x_42));
        let x_44 <- rdResp_edirRam___0_0__3();
        Vector#(8, Struct26) x_45 = (update (x_43, (Bit#(3))'(3'h3),
        x_44));
        let x_46 <- rdResp_edirRam___0_0__4();
        Vector#(8, Struct26) x_47 = (update (x_45, (Bit#(3))'(3'h4),
        x_46));
        let x_48 <- rdResp_edirRam___0_0__5();
        Vector#(8, Struct26) x_49 = (update (x_47, (Bit#(3))'(3'h5),
        x_48));
        let x_50 <- rdResp_edirRam___0_0__6();
        Vector#(8, Struct26) x_51 = (update (x_49, (Bit#(3))'(3'h6),
        x_50));
        let x_52 <- rdResp_edirRam___0_0__7();
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
        let x_57 <- repGetRs___0_0();
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
        let x_97 <- rdReq_dataRam___0_0({(x_95),(x_2)});
        return x_96;
    endmethod
    
    method ActionValue#(Vector#(4, Bit#(64))) cache___0_0__valueRsLineRq
    (Struct16 x_0);
        let x_1 <- rdResp_dataRam___0_0();
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
                    let x_11 <- wrReq_infoRam___0_0__0(x_10);
                end else begin
                    
                end
                if ((x_4) == ((Bit#(4))'(4'h1))) begin
                    let x_13 <- wrReq_infoRam___0_0__1(x_10);
                end else begin
                    
                end
                if ((x_4) == ((Bit#(4))'(4'h2))) begin
                    let x_15 <- wrReq_infoRam___0_0__2(x_10);
                end else begin
                    
                end
                if ((x_4) == ((Bit#(4))'(4'h3))) begin
                    let x_17 <- wrReq_infoRam___0_0__3(x_10);
                end else begin
                    
                end
                if ((x_4) == ((Bit#(4))'(4'h4))) begin
                    let x_19 <- wrReq_infoRam___0_0__4(x_10);
                end else begin
                    
                end
                if ((x_4) == ((Bit#(4))'(4'h5))) begin
                    let x_21 <- wrReq_infoRam___0_0__5(x_10);
                end else begin
                    
                end
                if ((x_4) == ((Bit#(4))'(4'h6))) begin
                    let x_23 <- wrReq_infoRam___0_0__6(x_10);
                end else begin
                    
                end
                if ((x_4) == ((Bit#(4))'(4'h7))) begin
                    let x_25 <- wrReq_infoRam___0_0__7(x_10);
                end else begin
                    
                end
                if ((x_4) == ((Bit#(4))'(4'h8))) begin
                    let x_27 <- wrReq_infoRam___0_0__8(x_10);
                end else begin
                    
                end
                if ((x_4) == ((Bit#(4))'(4'h9))) begin
                    let x_29 <- wrReq_infoRam___0_0__9(x_10);
                end else begin
                    
                end
                if ((x_4) == ((Bit#(4))'(4'ha))) begin
                    let x_31 <- wrReq_infoRam___0_0__10(x_10);
                end else begin
                    
                end
                if ((x_4) == ((Bit#(4))'(4'hb))) begin
                    let x_33 <- wrReq_infoRam___0_0__11(x_10);
                end else begin
                    
                end
                if ((x_4) == ((Bit#(4))'(4'hc))) begin
                    let x_35 <- wrReq_infoRam___0_0__12(x_10);
                end else begin
                    
                end
                if ((x_4) == ((Bit#(4))'(4'hd))) begin
                    let x_37 <- wrReq_infoRam___0_0__13(x_10);
                end else begin
                    
                end
                if ((x_4) == ((Bit#(4))'(4'he))) begin
                    let x_39 <- wrReq_infoRam___0_0__14(x_10);
                end else begin
                    
                end
                if ((x_4) == ((Bit#(4))'(4'hf))) begin
                    let x_41 <- wrReq_infoRam___0_0__15(x_10);
                end else begin
                    
                end
                if (! ((x_0).info_hit)) begin
                    Struct11 x_43 = ((x_0).may_victim);
                    Struct13 x_44 = (Struct13 {victim_valid : (Bool)'(True),
                    victim_addr : (x_43).mv_addr, victim_info :
                    (x_43).mv_info, victim_value : x_1, victim_req :
                    (Bool)'(False)});
                    let x_45 <- victims___0_0__registerVictim(x_44);
                end else begin
                    
                end
                let x_47 <- repAccess___0_0(Struct30 {acc_type : (!
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
                    let x_51 <- wrReq_edirRam___0_0__0(x_50);
                end else begin
                    
                end
                if ((x_49) == ((Bit#(3))'(3'h1))) begin
                    let x_53 <- wrReq_edirRam___0_0__1(x_50);
                end else begin
                    
                end
                if ((x_49) == ((Bit#(3))'(3'h2))) begin
                    let x_55 <- wrReq_edirRam___0_0__2(x_50);
                end else begin
                    
                end
                if ((x_49) == ((Bit#(3))'(3'h3))) begin
                    let x_57 <- wrReq_edirRam___0_0__3(x_50);
                end else begin
                    
                end
                if ((x_49) == ((Bit#(3))'(3'h4))) begin
                    let x_59 <- wrReq_edirRam___0_0__4(x_50);
                end else begin
                    
                end
                if ((x_49) == ((Bit#(3))'(3'h5))) begin
                    let x_61 <- wrReq_edirRam___0_0__5(x_50);
                end else begin
                    
                end
                if ((x_49) == ((Bit#(3))'(3'h6))) begin
                    let x_63 <- wrReq_edirRam___0_0__6(x_50);
                end else begin
                    
                end
                if ((x_49) == ((Bit#(3))'(3'h7))) begin
                    let x_65 <- wrReq_edirRam___0_0__7(x_50);
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
                        let x_69 <- wrReq_edirRam___0_0__0(x_68);
                    end else begin
                        
                    end
                    if ((x_67) == ((Bit#(3))'(3'h1))) begin
                        let x_71 <- wrReq_edirRam___0_0__1(x_68);
                    end else begin
                        
                    end
                    if ((x_67) == ((Bit#(3))'(3'h2))) begin
                        let x_73 <- wrReq_edirRam___0_0__2(x_68);
                    end else begin
                        
                    end
                    if ((x_67) == ((Bit#(3))'(3'h3))) begin
                        let x_75 <- wrReq_edirRam___0_0__3(x_68);
                    end else begin
                        
                    end
                    if ((x_67) == ((Bit#(3))'(3'h4))) begin
                        let x_77 <- wrReq_edirRam___0_0__4(x_68);
                    end else begin
                        
                    end
                    if ((x_67) == ((Bit#(3))'(3'h5))) begin
                        let x_79 <- wrReq_edirRam___0_0__5(x_68);
                    end else begin
                        
                    end
                    if ((x_67) == ((Bit#(3))'(3'h6))) begin
                        let x_81 <- wrReq_edirRam___0_0__6(x_68);
                    end else begin
                        
                    end
                    if ((x_67) == ((Bit#(3))'(3'h7))) begin
                        let x_83 <- wrReq_edirRam___0_0__7(x_68);
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
            let x_89 <- wrReq_dataRam___0_0(x_88);
        end else begin
            
        end
        return x_1;
    endmethod
endmodule

interface Module129;
    method Action cache___0_0_0__infoRq (Bit#(64) x_0);
    method ActionValue#(Struct39) cache___0_0_0__infoRsValueRq (Bit#(64)
    x_0);
    method ActionValue#(Vector#(4, Bit#(64))) cache___0_0_0__valueRsLineRq
    (Struct42 x_0);
endinterface

module mkModule129#(function Action wrReq_dataRam___0_0_0(Struct49 _),
    function Action repAccess___0_0_0(Struct48 _),
    function Action victims___0_0_0__registerVictim(Struct13 _),
    function Action wrReq_infoRam___0_0_0__3(Struct47 _),
    function Action wrReq_infoRam___0_0_0__2(Struct47 _),
    function Action wrReq_infoRam___0_0_0__1(Struct47 _),
    function Action wrReq_infoRam___0_0_0__0(Struct47 _),
    function ActionValue#(Vector#(4, Bit#(64))) rdResp_dataRam___0_0_0(),
    function Action rdReq_dataRam___0_0_0(Bit#(10) _),
    function ActionValue#(Vector#(4, Bit#(8))) repGetRs___0_0_0(),
    function ActionValue#(Struct45) rdResp_infoRam___0_0_0__3(),
    function ActionValue#(Struct45) rdResp_infoRam___0_0_0__2(),
    function ActionValue#(Struct45) rdResp_infoRam___0_0_0__1(),
    function ActionValue#(Struct45) rdResp_infoRam___0_0_0__0(),
    function Action repGetRq___0_0_0(Bit#(8) _),
    function Action rdReq_infoRam___0_0_0__3(Bit#(8) _),
    function Action rdReq_infoRam___0_0_0__2(Bit#(8) _),
    function Action rdReq_infoRam___0_0_0__1(Bit#(8) _),
    function Action rdReq_infoRam___0_0_0__0(Bit#(8) _))
    (Module129);
    
    // No rules in this module
    
    method Action cache___0_0_0__infoRq (Bit#(64) x_0);
        Bit#(8) x_1 = ((x_0)[12:5]);
        let x_2 <- rdReq_infoRam___0_0_0__0(x_1);
        let x_3 <- rdReq_infoRam___0_0_0__1(x_1);
        let x_4 <- rdReq_infoRam___0_0_0__2(x_1);
        let x_5 <- rdReq_infoRam___0_0_0__3(x_1);
        let x_6 <- repGetRq___0_0_0(x_1);
    endmethod
    
    method ActionValue#(Struct39) cache___0_0_0__infoRsValueRq (Bit#(64)
    x_0);
        Bit#(51) x_1 = ((x_0)[63:13]);
        Bit#(8) x_2 = ((x_0)[12:5]);
        Vector#(4, Struct45) x_3 = (unpack(0));
        let x_4 <- rdResp_infoRam___0_0_0__0();
        Vector#(4, Struct45) x_5 = (update (x_3, (Bit#(2))'(2'h0), x_4));
        let x_6 <- rdResp_infoRam___0_0_0__1();
        Vector#(4, Struct45) x_7 = (update (x_5, (Bit#(2))'(2'h1), x_6));
        let x_8 <- rdResp_infoRam___0_0_0__2();
        Vector#(4, Struct45) x_9 = (update (x_7, (Bit#(2))'(2'h2), x_8));
        let x_10 <- rdResp_infoRam___0_0_0__3();
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
        let x_13 <- repGetRs___0_0_0();
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
        let x_29 <- rdReq_dataRam___0_0_0({(x_27),(x_2)});
        return x_28;
    endmethod
    
    method ActionValue#(Vector#(4, Bit#(64))) cache___0_0_0__valueRsLineRq
    (Struct42 x_0);
        let x_1 <- rdResp_dataRam___0_0_0();
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
                let x_7 <- wrReq_infoRam___0_0_0__0(x_6);
            end else begin
                
            end
            if ((x_4) == ((Bit#(2))'(2'h1))) begin
                let x_9 <- wrReq_infoRam___0_0_0__1(x_6);
            end else begin
                
            end
            if ((x_4) == ((Bit#(2))'(2'h2))) begin
                let x_11 <- wrReq_infoRam___0_0_0__2(x_6);
            end else begin
                
            end
            if ((x_4) == ((Bit#(2))'(2'h3))) begin
                let x_13 <- wrReq_infoRam___0_0_0__3(x_6);
            end else begin
                
            end
            if (! ((x_0).info_hit)) begin
                Struct11 x_15 = ((x_0).may_victim);
                Struct13 x_16 = (Struct13 {victim_valid : (Bool)'(True),
                victim_addr : (x_15).mv_addr, victim_info : (x_15).mv_info,
                victim_value : x_1, victim_req : (Bool)'(False)});
                let x_17 <- victims___0_0_0__registerVictim(x_16);
            end else begin
                
            end
            let x_19 <- repAccess___0_0_0(Struct48 {acc_type : (!
            (((Bit#(3))'(3'h1)) < ((x_5).mesi_dir_st)) ? ((Bit#(1))'(1'h0)) :
            ((Bit#(1))'(1'h1))), acc_reps : (x_0).reps, acc_index : x_3,
            acc_way : x_4});
        end else begin
            
        end
        if ((x_0).value_write) begin
            Struct49 x_21 = (Struct49 {addr : {(x_4),((x_2)[12:5])}, datain :
            (x_0).value});
            let x_22 <- wrReq_dataRam___0_0_0(x_21);
        end else begin
            
        end
        return x_1;
    endmethod
endmodule

interface Module130;
    method Action cache___0_0_1__infoRq (Bit#(64) x_0);
    method ActionValue#(Struct39) cache___0_0_1__infoRsValueRq (Bit#(64)
    x_0);
    method ActionValue#(Vector#(4, Bit#(64))) cache___0_0_1__valueRsLineRq
    (Struct42 x_0);
endinterface

module mkModule130#(function Action wrReq_dataRam___0_0_1(Struct49 _),
    function Action repAccess___0_0_1(Struct48 _),
    function Action victims___0_0_1__registerVictim(Struct13 _),
    function Action wrReq_infoRam___0_0_1__3(Struct47 _),
    function Action wrReq_infoRam___0_0_1__2(Struct47 _),
    function Action wrReq_infoRam___0_0_1__1(Struct47 _),
    function Action wrReq_infoRam___0_0_1__0(Struct47 _),
    function ActionValue#(Vector#(4, Bit#(64))) rdResp_dataRam___0_0_1(),
    function Action rdReq_dataRam___0_0_1(Bit#(10) _),
    function ActionValue#(Vector#(4, Bit#(8))) repGetRs___0_0_1(),
    function ActionValue#(Struct45) rdResp_infoRam___0_0_1__3(),
    function ActionValue#(Struct45) rdResp_infoRam___0_0_1__2(),
    function ActionValue#(Struct45) rdResp_infoRam___0_0_1__1(),
    function ActionValue#(Struct45) rdResp_infoRam___0_0_1__0(),
    function Action repGetRq___0_0_1(Bit#(8) _),
    function Action rdReq_infoRam___0_0_1__3(Bit#(8) _),
    function Action rdReq_infoRam___0_0_1__2(Bit#(8) _),
    function Action rdReq_infoRam___0_0_1__1(Bit#(8) _),
    function Action rdReq_infoRam___0_0_1__0(Bit#(8) _))
    (Module130);
    
    // No rules in this module
    
    method Action cache___0_0_1__infoRq (Bit#(64) x_0);
        Bit#(8) x_1 = ((x_0)[12:5]);
        let x_2 <- rdReq_infoRam___0_0_1__0(x_1);
        let x_3 <- rdReq_infoRam___0_0_1__1(x_1);
        let x_4 <- rdReq_infoRam___0_0_1__2(x_1);
        let x_5 <- rdReq_infoRam___0_0_1__3(x_1);
        let x_6 <- repGetRq___0_0_1(x_1);
    endmethod
    
    method ActionValue#(Struct39) cache___0_0_1__infoRsValueRq (Bit#(64)
    x_0);
        Bit#(51) x_1 = ((x_0)[63:13]);
        Bit#(8) x_2 = ((x_0)[12:5]);
        Vector#(4, Struct45) x_3 = (unpack(0));
        let x_4 <- rdResp_infoRam___0_0_1__0();
        Vector#(4, Struct45) x_5 = (update (x_3, (Bit#(2))'(2'h0), x_4));
        let x_6 <- rdResp_infoRam___0_0_1__1();
        Vector#(4, Struct45) x_7 = (update (x_5, (Bit#(2))'(2'h1), x_6));
        let x_8 <- rdResp_infoRam___0_0_1__2();
        Vector#(4, Struct45) x_9 = (update (x_7, (Bit#(2))'(2'h2), x_8));
        let x_10 <- rdResp_infoRam___0_0_1__3();
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
        let x_13 <- repGetRs___0_0_1();
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
        let x_29 <- rdReq_dataRam___0_0_1({(x_27),(x_2)});
        return x_28;
    endmethod
    
    method ActionValue#(Vector#(4, Bit#(64))) cache___0_0_1__valueRsLineRq
    (Struct42 x_0);
        let x_1 <- rdResp_dataRam___0_0_1();
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
                let x_7 <- wrReq_infoRam___0_0_1__0(x_6);
            end else begin
                
            end
            if ((x_4) == ((Bit#(2))'(2'h1))) begin
                let x_9 <- wrReq_infoRam___0_0_1__1(x_6);
            end else begin
                
            end
            if ((x_4) == ((Bit#(2))'(2'h2))) begin
                let x_11 <- wrReq_infoRam___0_0_1__2(x_6);
            end else begin
                
            end
            if ((x_4) == ((Bit#(2))'(2'h3))) begin
                let x_13 <- wrReq_infoRam___0_0_1__3(x_6);
            end else begin
                
            end
            if (! ((x_0).info_hit)) begin
                Struct11 x_15 = ((x_0).may_victim);
                Struct13 x_16 = (Struct13 {victim_valid : (Bool)'(True),
                victim_addr : (x_15).mv_addr, victim_info : (x_15).mv_info,
                victim_value : x_1, victim_req : (Bool)'(False)});
                let x_17 <- victims___0_0_1__registerVictim(x_16);
            end else begin
                
            end
            let x_19 <- repAccess___0_0_1(Struct48 {acc_type : (!
            (((Bit#(3))'(3'h1)) < ((x_5).mesi_dir_st)) ? ((Bit#(1))'(1'h0)) :
            ((Bit#(1))'(1'h1))), acc_reps : (x_0).reps, acc_index : x_3,
            acc_way : x_4});
        end else begin
            
        end
        if ((x_0).value_write) begin
            Struct49 x_21 = (Struct49 {addr : {(x_4),((x_2)[12:5])}, datain :
            (x_0).value});
            let x_22 <- wrReq_dataRam___0_0_1(x_21);
        end else begin
            
        end
        return x_1;
    endmethod
endmodule

interface Module131;
    method Action cache___0_0_2__infoRq (Bit#(64) x_0);
    method ActionValue#(Struct39) cache___0_0_2__infoRsValueRq (Bit#(64)
    x_0);
    method ActionValue#(Vector#(4, Bit#(64))) cache___0_0_2__valueRsLineRq
    (Struct42 x_0);
endinterface

module mkModule131#(function Action wrReq_dataRam___0_0_2(Struct49 _),
    function Action repAccess___0_0_2(Struct48 _),
    function Action victims___0_0_2__registerVictim(Struct13 _),
    function Action wrReq_infoRam___0_0_2__3(Struct47 _),
    function Action wrReq_infoRam___0_0_2__2(Struct47 _),
    function Action wrReq_infoRam___0_0_2__1(Struct47 _),
    function Action wrReq_infoRam___0_0_2__0(Struct47 _),
    function ActionValue#(Vector#(4, Bit#(64))) rdResp_dataRam___0_0_2(),
    function Action rdReq_dataRam___0_0_2(Bit#(10) _),
    function ActionValue#(Vector#(4, Bit#(8))) repGetRs___0_0_2(),
    function ActionValue#(Struct45) rdResp_infoRam___0_0_2__3(),
    function ActionValue#(Struct45) rdResp_infoRam___0_0_2__2(),
    function ActionValue#(Struct45) rdResp_infoRam___0_0_2__1(),
    function ActionValue#(Struct45) rdResp_infoRam___0_0_2__0(),
    function Action repGetRq___0_0_2(Bit#(8) _),
    function Action rdReq_infoRam___0_0_2__3(Bit#(8) _),
    function Action rdReq_infoRam___0_0_2__2(Bit#(8) _),
    function Action rdReq_infoRam___0_0_2__1(Bit#(8) _),
    function Action rdReq_infoRam___0_0_2__0(Bit#(8) _))
    (Module131);
    
    // No rules in this module
    
    method Action cache___0_0_2__infoRq (Bit#(64) x_0);
        Bit#(8) x_1 = ((x_0)[12:5]);
        let x_2 <- rdReq_infoRam___0_0_2__0(x_1);
        let x_3 <- rdReq_infoRam___0_0_2__1(x_1);
        let x_4 <- rdReq_infoRam___0_0_2__2(x_1);
        let x_5 <- rdReq_infoRam___0_0_2__3(x_1);
        let x_6 <- repGetRq___0_0_2(x_1);
    endmethod
    
    method ActionValue#(Struct39) cache___0_0_2__infoRsValueRq (Bit#(64)
    x_0);
        Bit#(51) x_1 = ((x_0)[63:13]);
        Bit#(8) x_2 = ((x_0)[12:5]);
        Vector#(4, Struct45) x_3 = (unpack(0));
        let x_4 <- rdResp_infoRam___0_0_2__0();
        Vector#(4, Struct45) x_5 = (update (x_3, (Bit#(2))'(2'h0), x_4));
        let x_6 <- rdResp_infoRam___0_0_2__1();
        Vector#(4, Struct45) x_7 = (update (x_5, (Bit#(2))'(2'h1), x_6));
        let x_8 <- rdResp_infoRam___0_0_2__2();
        Vector#(4, Struct45) x_9 = (update (x_7, (Bit#(2))'(2'h2), x_8));
        let x_10 <- rdResp_infoRam___0_0_2__3();
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
        let x_13 <- repGetRs___0_0_2();
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
        let x_29 <- rdReq_dataRam___0_0_2({(x_27),(x_2)});
        return x_28;
    endmethod
    
    method ActionValue#(Vector#(4, Bit#(64))) cache___0_0_2__valueRsLineRq
    (Struct42 x_0);
        let x_1 <- rdResp_dataRam___0_0_2();
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
                let x_7 <- wrReq_infoRam___0_0_2__0(x_6);
            end else begin
                
            end
            if ((x_4) == ((Bit#(2))'(2'h1))) begin
                let x_9 <- wrReq_infoRam___0_0_2__1(x_6);
            end else begin
                
            end
            if ((x_4) == ((Bit#(2))'(2'h2))) begin
                let x_11 <- wrReq_infoRam___0_0_2__2(x_6);
            end else begin
                
            end
            if ((x_4) == ((Bit#(2))'(2'h3))) begin
                let x_13 <- wrReq_infoRam___0_0_2__3(x_6);
            end else begin
                
            end
            if (! ((x_0).info_hit)) begin
                Struct11 x_15 = ((x_0).may_victim);
                Struct13 x_16 = (Struct13 {victim_valid : (Bool)'(True),
                victim_addr : (x_15).mv_addr, victim_info : (x_15).mv_info,
                victim_value : x_1, victim_req : (Bool)'(False)});
                let x_17 <- victims___0_0_2__registerVictim(x_16);
            end else begin
                
            end
            let x_19 <- repAccess___0_0_2(Struct48 {acc_type : (!
            (((Bit#(3))'(3'h1)) < ((x_5).mesi_dir_st)) ? ((Bit#(1))'(1'h0)) :
            ((Bit#(1))'(1'h1))), acc_reps : (x_0).reps, acc_index : x_3,
            acc_way : x_4});
        end else begin
            
        end
        if ((x_0).value_write) begin
            Struct49 x_21 = (Struct49 {addr : {(x_4),((x_2)[12:5])}, datain :
            (x_0).value});
            let x_22 <- wrReq_dataRam___0_0_2(x_21);
        end else begin
            
        end
        return x_1;
    endmethod
endmodule

interface Module132;
    method Action cache___0_0_3__infoRq (Bit#(64) x_0);
    method ActionValue#(Struct39) cache___0_0_3__infoRsValueRq (Bit#(64)
    x_0);
    method ActionValue#(Vector#(4, Bit#(64))) cache___0_0_3__valueRsLineRq
    (Struct42 x_0);
endinterface

module mkModule132#(function Action wrReq_dataRam___0_0_3(Struct49 _),
    function Action repAccess___0_0_3(Struct48 _),
    function Action victims___0_0_3__registerVictim(Struct13 _),
    function Action wrReq_infoRam___0_0_3__3(Struct47 _),
    function Action wrReq_infoRam___0_0_3__2(Struct47 _),
    function Action wrReq_infoRam___0_0_3__1(Struct47 _),
    function Action wrReq_infoRam___0_0_3__0(Struct47 _),
    function ActionValue#(Vector#(4, Bit#(64))) rdResp_dataRam___0_0_3(),
    function Action rdReq_dataRam___0_0_3(Bit#(10) _),
    function ActionValue#(Vector#(4, Bit#(8))) repGetRs___0_0_3(),
    function ActionValue#(Struct45) rdResp_infoRam___0_0_3__3(),
    function ActionValue#(Struct45) rdResp_infoRam___0_0_3__2(),
    function ActionValue#(Struct45) rdResp_infoRam___0_0_3__1(),
    function ActionValue#(Struct45) rdResp_infoRam___0_0_3__0(),
    function Action repGetRq___0_0_3(Bit#(8) _),
    function Action rdReq_infoRam___0_0_3__3(Bit#(8) _),
    function Action rdReq_infoRam___0_0_3__2(Bit#(8) _),
    function Action rdReq_infoRam___0_0_3__1(Bit#(8) _),
    function Action rdReq_infoRam___0_0_3__0(Bit#(8) _))
    (Module132);
    
    // No rules in this module
    
    method Action cache___0_0_3__infoRq (Bit#(64) x_0);
        Bit#(8) x_1 = ((x_0)[12:5]);
        let x_2 <- rdReq_infoRam___0_0_3__0(x_1);
        let x_3 <- rdReq_infoRam___0_0_3__1(x_1);
        let x_4 <- rdReq_infoRam___0_0_3__2(x_1);
        let x_5 <- rdReq_infoRam___0_0_3__3(x_1);
        let x_6 <- repGetRq___0_0_3(x_1);
    endmethod
    
    method ActionValue#(Struct39) cache___0_0_3__infoRsValueRq (Bit#(64)
    x_0);
        Bit#(51) x_1 = ((x_0)[63:13]);
        Bit#(8) x_2 = ((x_0)[12:5]);
        Vector#(4, Struct45) x_3 = (unpack(0));
        let x_4 <- rdResp_infoRam___0_0_3__0();
        Vector#(4, Struct45) x_5 = (update (x_3, (Bit#(2))'(2'h0), x_4));
        let x_6 <- rdResp_infoRam___0_0_3__1();
        Vector#(4, Struct45) x_7 = (update (x_5, (Bit#(2))'(2'h1), x_6));
        let x_8 <- rdResp_infoRam___0_0_3__2();
        Vector#(4, Struct45) x_9 = (update (x_7, (Bit#(2))'(2'h2), x_8));
        let x_10 <- rdResp_infoRam___0_0_3__3();
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
        let x_13 <- repGetRs___0_0_3();
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
        let x_29 <- rdReq_dataRam___0_0_3({(x_27),(x_2)});
        return x_28;
    endmethod
    
    method ActionValue#(Vector#(4, Bit#(64))) cache___0_0_3__valueRsLineRq
    (Struct42 x_0);
        let x_1 <- rdResp_dataRam___0_0_3();
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
                let x_7 <- wrReq_infoRam___0_0_3__0(x_6);
            end else begin
                
            end
            if ((x_4) == ((Bit#(2))'(2'h1))) begin
                let x_9 <- wrReq_infoRam___0_0_3__1(x_6);
            end else begin
                
            end
            if ((x_4) == ((Bit#(2))'(2'h2))) begin
                let x_11 <- wrReq_infoRam___0_0_3__2(x_6);
            end else begin
                
            end
            if ((x_4) == ((Bit#(2))'(2'h3))) begin
                let x_13 <- wrReq_infoRam___0_0_3__3(x_6);
            end else begin
                
            end
            if (! ((x_0).info_hit)) begin
                Struct11 x_15 = ((x_0).may_victim);
                Struct13 x_16 = (Struct13 {victim_valid : (Bool)'(True),
                victim_addr : (x_15).mv_addr, victim_info : (x_15).mv_info,
                victim_value : x_1, victim_req : (Bool)'(False)});
                let x_17 <- victims___0_0_3__registerVictim(x_16);
            end else begin
                
            end
            let x_19 <- repAccess___0_0_3(Struct48 {acc_type : (!
            (((Bit#(3))'(3'h1)) < ((x_5).mesi_dir_st)) ? ((Bit#(1))'(1'h0)) :
            ((Bit#(1))'(1'h1))), acc_reps : (x_0).reps, acc_index : x_3,
            acc_way : x_4});
        end else begin
            
        end
        if ((x_0).value_write) begin
            Struct49 x_21 = (Struct49 {addr : {(x_4),((x_2)[12:5])}, datain :
            (x_0).value});
            let x_22 <- wrReq_dataRam___0_0_3(x_21);
        end else begin
            
        end
        return x_1;
    endmethod
endmodule

interface Module133;
    
endinterface

module mkModule133#(function Action canImm__0_0(Bit#(64) _),
    function Action victims___0_0__setVictimRq(Bit#(64) _),
    function Action setULImm__0_0(Struct1 _),
    function ActionValue#(Struct13) victims___0_0__getFirstVictim(),
    function Action transferUpDown__0_0(Struct23 _),
    function ActionValue#(Struct1) getMSHRFirstRs__0_0(Bit#(3) _),
    function Action broadcast_parentChildren_0_0(Struct21 _),
    function Action registerDL__0_0(Struct20 _),
    function Action registerUL__0_0(Struct19 _),
    function Action makeEnq_parentChildren_0_0(Struct18 _),
    function ActionValue#(Vector#(4, Bit#(64))) cache___0_0__valueRsLineRq(Struct16 _),
    function Action victims___0_0__setVictim(Struct17 _),
    function ActionValue#(Struct1) getMSHRRq__0_0(Bit#(3) _),
    function ActionValue#(Struct14) getMSHR__0_0(Bit#(3) _),
    function ActionValue#(Struct12) deq_fifoL2E__0_0(),
    function ActionValue#(Struct13) victims___0_0__getVictim(Bit#(3) _),
    function Action enq_fifoL2E__0_0(Struct12 _),
    function ActionValue#(Struct9) cache___0_0__infoRsValueRq(Bit#(64) _),
    function ActionValue#(Struct6) deq_fifoI2L__0_0(),
    function Action enq_fifoI2L__0_0(Struct6 _),
    function Action cache___0_0__infoRq(Bit#(64) _),
    function ActionValue#(Struct6) deq_fifoN2I__0_0(),
    function ActionValue#(Struct8) getDLReady__0_0(),
    function Action addRs__0_0(Struct7 _),
    function ActionValue#(Struct2) deq_fifoCRsInput__0_0(),
    function ActionValue#(Struct4) getCRqSlot__0_0(Struct3 _),
    function ActionValue#(Bool) victims___0_0__hasVictim(),
    function ActionValue#(Struct2) deq_fifoCRqInput__0_0(),
    function Action releaseMSHR__0_0(Bit#(3) _),
    function Action victims___0_0__releaseVictim(Bit#(64) _),
    function ActionValue#(Struct3) getWait__0_0(),
    function Action startRelease__0_0(Bit#(3) _),
    function ActionValue#(Bit#(3)) getULReady__0_0(Bit#(64) _),
    function Action enq_fifoN2I__0_0(Struct6 _),
    function ActionValue#(Struct5) victims___0_0__findVictim(Bit#(64) _),
    function ActionValue#(Struct4) getPRqSlot__0_0(Struct3 _),
    function ActionValue#(Struct2) deq_fifoPInput__0_0())
    (Module133);
    
    rule rule_in_prq__0_0;
        let x_0 <- deq_fifoPInput__0_0();
        Bit#(4) x_1 = ((x_0).in_msg_from);
        when ((x_1) == ({((Bit#(2))'(2'h2)),((Bit#(2))'(2'h0))}),
        noAction);
        Struct1 x_2 = ((x_0).in_msg);
        when (! ((x_2).type_), noAction);
        let x_3 <- getPRqSlot__0_0(Struct3 {r_id : unpack(0), r_msg : x_2,
        r_msg_from : (x_0).in_msg_from});
        when ((x_3).s_has_slot,
        noAction);
        if (! ((x_3).s_conflict)) begin
            let x_4 <- victims___0_0__findVictim((x_2).addr);
            Struct6 x_5 = (Struct6 {ir_is_rs_rel : (Bool)'(False), ir_msg :
            (x_0).in_msg, ir_msg_from : x_1, ir_mshr_id : (x_3).s_id,
            ir_by_victim : x_4});
            let x_6 <- enq_fifoN2I__0_0(x_5);
        end else begin
            
        end
    endrule
    
    rule rule_in_prs__0_0;
        let x_0 <- deq_fifoPInput__0_0();
        Bit#(4) x_1 = ((x_0).in_msg_from);
        when ((x_1) == ({((Bit#(2))'(2'h2)),((Bit#(2))'(2'h0))}),
        noAction);
        Struct1 x_2 = ((x_0).in_msg);
        when (((x_2).type_) && (! (((x_2).id) == ((Bit#(6))'(6'h16)))),
        noAction);
        let x_3 <- getULReady__0_0((x_2).addr);
        let x_4 <- startRelease__0_0(x_3);
        let x_5 <- victims___0_0__findVictim((x_2).addr);
        Struct6 x_6 = (Struct6 {ir_is_rs_rel : (Bool)'(False), ir_msg :
        (x_0).in_msg, ir_msg_from : x_1, ir_mshr_id : x_3, ir_by_victim :
        x_5});
        let x_7 <- enq_fifoN2I__0_0(x_6);
    endrule
    
    rule rule_in_retry__0_0;
        let x_0 <- getWait__0_0();
        Struct1 x_1 = ((x_0).r_msg);
        let x_2 <- victims___0_0__findVictim((x_1).addr);
        Struct6 x_3 = (Struct6 {ir_is_rs_rel : (Bool)'(False), ir_msg : x_1,
        ir_msg_from : (x_0).r_msg_from, ir_mshr_id : (x_0).r_id, ir_by_victim
        : x_2});
        let x_4 <- enq_fifoN2I__0_0(x_3);
    endrule
    
    rule rule_in_invrs__0_0;
        let x_0 <- deq_fifoPInput__0_0();
        Bit#(4) x_1 = ((x_0).in_msg_from);
        when ((x_1) == ({((Bit#(2))'(2'h2)),((Bit#(2))'(2'h0))}),
        noAction);
        Struct1 x_2 = ((x_0).in_msg);
        when (((x_2).type_) && (((x_2).id) == ((Bit#(6))'(6'h16))),
        noAction);
        let x_3 <- getULReady__0_0((x_2).addr);
        let x_4 <- victims___0_0__releaseVictim((x_2).addr);
        let x_5 <- releaseMSHR__0_0(x_3);
    endrule
    
    rule rule_in_crq__0_0;
        let x_0 <- deq_fifoCRqInput__0_0();
        Bit#(4) x_1 = ((x_0).in_msg_from);
        when (((x_1)[3:2]) == ((Bit#(2))'(2'h0)), noAction);
        Struct1 x_2 = ((x_0).in_msg);
        when (! ((x_2).type_), noAction);
        let x_3 <- victims___0_0__hasVictim();
        when (! (x_3), noAction);
        let x_4 <- getCRqSlot__0_0(Struct3 {r_id : unpack(0), r_msg : x_2,
        r_msg_from : x_1});
        when ((x_4).s_has_slot,
        noAction);
        if (! ((x_4).s_conflict)) begin
            let x_5 <- victims___0_0__findVictim((x_2).addr);
            Struct6 x_6 = (Struct6 {ir_is_rs_rel : (Bool)'(False), ir_msg :
            (x_0).in_msg, ir_msg_from : x_1, ir_mshr_id : (x_4).s_id,
            ir_by_victim : x_5});
            let x_7 <- enq_fifoN2I__0_0(x_6);
        end else begin
            
        end
    endrule
    
    rule rule_in_crs__0_0;
        let x_0 <- deq_fifoCRsInput__0_0();
        Bit#(4) x_1 = ((x_0).in_msg_from);
        when (((x_1)[3:2]) == ((Bit#(2))'(2'h1)), noAction);
        Struct1 x_2 = ((x_0).in_msg);
        when ((x_2).type_, noAction);
        let x_3 <- addRs__0_0(Struct7 {r_midx : (x_1)[1:0], r_msg : x_2});
    endrule
    
    rule rule_in_rsrel__0_0;
        let x_0 <- getDLReady__0_0();
        let x_1 <- startRelease__0_0((x_0).r_id);
        Struct1 x_2 = (Struct1 {id : unpack(0), type_ : unpack(0), addr :
        (x_0).r_addr, value : unpack(0)});
        Struct6 x_3 = (Struct6 {ir_is_rs_rel : (Bool)'(True), ir_msg : x_2,
        ir_msg_from : unpack(0), ir_mshr_id : (x_0).r_id, ir_by_victim :
        Struct5 {valid : (Bool)'(False), data : unpack(0)}});
        let x_4 <- enq_fifoN2I__0_0(x_3);
    endrule
    
    rule rule_ir_cache__0_0;
        let x_0 <- deq_fifoN2I__0_0();
        when (! (((x_0).ir_by_victim).valid), noAction);
        Struct1 x_1 = ((x_0).ir_msg);
        let x_2 <- cache___0_0__infoRq((x_1).addr);
        let x_3 <- enq_fifoI2L__0_0(x_0);
    endrule
    
    rule rule_ir_victims__0_0;
        let x_0 <- deq_fifoN2I__0_0();
        when (((x_0).ir_by_victim).valid, noAction);
        let x_1 <- enq_fifoI2L__0_0(x_0);
    endrule
    
    rule rule_lr_cache__0_0;
        let x_0 <- deq_fifoI2L__0_0();
        when (! (((x_0).ir_by_victim).valid), noAction);
        let x_1 <- cache___0_0__infoRsValueRq(((x_0).ir_msg).addr);
        Struct12 x_2 = (Struct12 {lr_ir_pp : x_0, lr_ir : x_1, lr_value :
        unpack(0)});
        let x_3 <- enq_fifoL2E__0_0(x_2);
    endrule
    
    rule rule_lr_victims__0_0;
        let x_0 <- deq_fifoI2L__0_0();
        when (((x_0).ir_by_victim).valid, noAction);
        Bit#(3) x_1 = (((x_0).ir_by_victim).data);
        let x_2 <- victims___0_0__getVictim(x_1);
        Struct9 x_3 = (Struct9 {info_index : unpack(0), info_hit : unpack(0),
        info_way : unpack(0), edir_hit : unpack(0), edir_way : unpack(0),
        edir_slot : unpack(0), info : (x_2).victim_info, may_victim :
        unpack(0), reps : unpack(0)});
        Struct12 x_4 = (Struct12 {lr_ir_pp : x_0, lr_ir : x_3, lr_value :
        (x_2).victim_value});
        let x_5 <- enq_fifoL2E__0_0(x_4);
    endrule
    
    rule rule_exec__0_0__0_0_0_0_0_0;
        let x_0 <- deq_fifoL2E__0_0();
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
        let x_10 <- getMSHR__0_0(x_4);
        let x_11 <- getMSHRRq__0_0(x_4);
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
            let x_20 <- victims___0_0__setVictim(Struct17 {victim_idx :
            (x_8).data, victim_info : (x_19).info, victim_value :
            ((x_19).value_write ? ((x_19).value) : (x_9))});
            x_22 = x_9;
        end else begin
            let x_21 <- cache___0_0__valueRsLineRq(x_19);
            x_22 = x_21;
        end
        Struct18 x_23 = (Struct18 {enq_type : ((((Bit#(4))'(4'h8))[3:2]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : (((((Bit#(4))'(4'h8))[3:2])
        == ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : ((Bit#(4))'(4'h8))[1:0], enq_msg : Struct1 {id :
        (Bit#(6))'(6'h3), type_ : (Bool)'(True), addr : (x_17).addr, value :
        x_22}});
        let x_24 <- makeEnq_parentChildren_0_0(x_23);
        let x_25 <- releaseMSHR__0_0(x_4);
    endrule
    
    rule rule_exec__0_0__0_0_1_0_0_0;
        let x_0 <- deq_fifoL2E__0_0();
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
        let x_10 <- getMSHR__0_0(x_4);
        let x_11 <- getMSHRRq__0_0(x_4);
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
            let x_21 <- victims___0_0__setVictim(Struct17 {victim_idx :
            (x_8).data, victim_info : (x_20).info, victim_value :
            ((x_20).value_write ? ((x_20).value) : (x_9))});
            x_23 = x_9;
        end else begin
            let x_22 <- cache___0_0__valueRsLineRq(x_20);
            x_23 = x_22;
        end
        Struct18 x_24 = (Struct18 {enq_type : ((((Bit#(4))'(4'h8))[3:2]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : (((((Bit#(4))'(4'h8))[3:2])
        == ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : ((Bit#(4))'(4'h8))[1:0], enq_msg : Struct1 {id :
        (Bit#(6))'(6'h4), type_ : (Bool)'(True), addr : (x_17).addr, value :
        x_23}});
        let x_25 <- makeEnq_parentChildren_0_0(x_24);
        let x_26 <- releaseMSHR__0_0(x_4);
    endrule
    
    rule rule_exec__0_0__0_1_0_0_0;
        let x_0 <- deq_fifoL2E__0_0();
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
        let x_10 <- getMSHR__0_0(x_4);
        let x_11 <- getMSHRRq__0_0(x_4);
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
            let x_19 <- cache___0_0__valueRsLineRq(unpack(0));
            x_20 = x_19;
        end
        let x_21 <- registerUL__0_0(Struct19 {r_id : x_4, r_ul_rsb :
        (Bool)'(True), r_ul_rsbTo : ((Bit#(4))'(4'h8))[1:0]});
        Struct18 x_22 = (Struct18 {enq_type : ((((Bit#(4))'(4'h0))[3:2]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : (((((Bit#(4))'(4'h0))[3:2])
        == ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : ((Bit#(4))'(4'h0))[1:0], enq_msg : Struct1 {id :
        (Bit#(6))'(6'h2), type_ : (Bool)'(False), addr : (x_17).addr, value :
        unpack(0)}});
        let x_23 <- makeEnq_parentChildren_0_0(x_22);
    endrule
    
    rule rule_exec__0_0__0_3_0_0_0;
        let x_0 <- deq_fifoL2E__0_0();
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
        let x_10 <- getMSHR__0_0(x_4);
        let x_11 <- getMSHRRq__0_0(x_4);
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
            let x_19 <- cache___0_0__valueRsLineRq(unpack(0));
            x_20 = x_19;
        end
        let x_21 <- registerDL__0_0(Struct20 {r_id : x_4, r_dl_rss_from :
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
        let x_23 <- makeEnq_parentChildren_0_0(x_22);
    endrule
    
    rule rule_exec__0_0__1_0_0_0_0;
        let x_0 <- deq_fifoL2E__0_0();
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
        let x_10 <- getMSHR__0_0(x_4);
        let x_11 <- getMSHRRq__0_0(x_4);
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
            let x_22 <- victims___0_0__setVictim(Struct17 {victim_idx :
            (x_8).data, victim_info : (x_21).info, victim_value :
            ((x_21).value_write ? ((x_21).value) : (x_9))});
            x_24 = x_9;
        end else begin
            let x_23 <- cache___0_0__valueRsLineRq(x_21);
            x_24 = x_23;
        end
        Struct18 x_25 = (Struct18 {enq_type : ((((Bit#(4))'(4'h8))[3:2]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : (((((Bit#(4))'(4'h8))[3:2])
        == ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : ((Bit#(4))'(4'h8))[1:0], enq_msg : Struct1 {id :
        (Bit#(6))'(6'hb), type_ : (Bool)'(True), addr : (x_17).addr, value :
        unpack(0)}});
        let x_26 <- makeEnq_parentChildren_0_0(x_25);
        let x_27 <- releaseMSHR__0_0(x_4);
    endrule
    
    rule rule_exec__0_0__1_1_0_0_0;
        let x_0 <- deq_fifoL2E__0_0();
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
        let x_10 <- getMSHR__0_0(x_4);
        let x_11 <- getMSHRRq__0_0(x_4);
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
            let x_19 <- cache___0_0__valueRsLineRq(unpack(0));
            x_20 = x_19;
        end
        let x_21 <- registerUL__0_0(Struct19 {r_id : x_4, r_ul_rsb :
        (Bool)'(True), r_ul_rsbTo : ((Bit#(4))'(4'h8))[1:0]});
        Struct18 x_22 = (Struct18 {enq_type : ((((Bit#(4))'(4'h0))[3:2]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : (((((Bit#(4))'(4'h0))[3:2])
        == ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : ((Bit#(4))'(4'h0))[1:0], enq_msg : Struct1 {id :
        (Bit#(6))'(6'ha), type_ : (Bool)'(False), addr : (x_17).addr, value :
        unpack(0)}});
        let x_23 <- makeEnq_parentChildren_0_0(x_22);
    endrule
    
    rule rule_exec__0_0__1_4_0_0_0;
        let x_0 <- deq_fifoL2E__0_0();
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
        let x_10 <- getMSHR__0_0(x_4);
        let x_11 <- getMSHRRq__0_0(x_4);
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
            let x_19 <- cache___0_0__valueRsLineRq(unpack(0));
            x_20 = x_19;
        end
        let x_21 <- registerDL__0_0(Struct20 {r_id : x_4, r_dl_rss_from :
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
        let x_23 <- makeEnq_parentChildren_0_0(x_22);
    endrule
    
    rule rule_exec__0_0__1_5_0_0_0;
        let x_0 <- deq_fifoL2E__0_0();
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
        let x_10 <- getMSHR__0_0(x_4);
        let x_11 <- getMSHRRq__0_0(x_4);
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
            let x_19 <- cache___0_0__valueRsLineRq(unpack(0));
            x_20 = x_19;
        end
        let x_21 <- registerDL__0_0(Struct20 {r_id : x_4, r_dl_rss_from :
        ((x_16).dir_sharers) & (~(((Bit#(4))'(4'h1)) << ((Bit#(2))'(2'h0)))),
        r_dl_rsb : (Bool)'(True), r_dl_rsbTo : (Bit#(4))'(4'h8)});
        let x_22 <- broadcast_parentChildren_0_0(Struct21 {cs_inds :
        ((x_16).dir_sharers) & (~(((Bit#(4))'(4'h1)) << ((Bit#(2))'(2'h0)))),
        cs_msg : Struct1 {id : (Bit#(6))'(6'hc), type_ : (Bool)'(False), addr
        : (x_17).addr, value : unpack(0)}});
    endrule
    
    rule rule_exec__0_0__2_5_0_0_0;
        let x_0 <- deq_fifoL2E__0_0();
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
        let x_10 <- getMSHR__0_0(x_4);
        let x_11 <- getMSHRRq__0_0(x_4);
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
            let x_19 <- cache___0_0__valueRsLineRq(unpack(0));
            x_20 = x_19;
        end
        Struct18 x_21 = (Struct18 {enq_type : ((((Bit#(4))'(4'h8))[3:2]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : (((((Bit#(4))'(4'h8))[3:2])
        == ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : ((Bit#(4))'(4'h8))[1:0], enq_msg : Struct1 {id :
        (Bit#(6))'(6'h16), type_ : (Bool)'(True), addr : (x_17).addr, value :
        unpack(0)}});
        let x_22 <- makeEnq_parentChildren_0_0(x_21);
        let x_23 <- releaseMSHR__0_0(x_4);
    endrule
    
    rule rule_exec__0_0__2_6_0_0_0_0_0;
        let x_0 <- deq_fifoL2E__0_0();
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
        let x_10 <- getMSHR__0_0(x_4);
        let x_11 <- getMSHRRq__0_0(x_4);
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
            let x_20 <- victims___0_0__setVictim(Struct17 {victim_idx :
            (x_8).data, victim_info : (x_19).info, victim_value :
            ((x_19).value_write ? ((x_19).value) : (x_9))});
            x_22 = x_9;
        end else begin
            let x_21 <- cache___0_0__valueRsLineRq(x_19);
            x_22 = x_21;
        end
        Struct18 x_23 = (Struct18 {enq_type : ((((Bit#(4))'(4'h8))[3:2]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : (((((Bit#(4))'(4'h8))[3:2])
        == ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : ((Bit#(4))'(4'h8))[1:0], enq_msg : Struct1 {id :
        (Bit#(6))'(6'h16), type_ : (Bool)'(True), addr : (x_17).addr, value :
        unpack(0)}});
        let x_24 <- makeEnq_parentChildren_0_0(x_23);
        let x_25 <- releaseMSHR__0_0(x_4);
    endrule
    
    rule rule_exec__0_0__2_6_0_1_0_0_0;
        let x_0 <- deq_fifoL2E__0_0();
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
        let x_10 <- getMSHR__0_0(x_4);
        let x_11 <- getMSHRRq__0_0(x_4);
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
            let x_21 <- victims___0_0__setVictim(Struct17 {victim_idx :
            (x_8).data, victim_info : (x_20).info, victim_value :
            ((x_20).value_write ? ((x_20).value) : (x_9))});
            x_23 = x_9;
        end else begin
            let x_22 <- cache___0_0__valueRsLineRq(x_20);
            x_23 = x_22;
        end
        Struct18 x_24 = (Struct18 {enq_type : ((((Bit#(4))'(4'h8))[3:2]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : (((((Bit#(4))'(4'h8))[3:2])
        == ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : ((Bit#(4))'(4'h8))[1:0], enq_msg : Struct1 {id :
        (Bit#(6))'(6'h16), type_ : (Bool)'(True), addr : (x_17).addr, value :
        unpack(0)}});
        let x_25 <- makeEnq_parentChildren_0_0(x_24);
        let x_26 <- releaseMSHR__0_0(x_4);
    endrule
    
    rule rule_exec__0_0__2_6_1_0_0_0;
        let x_0 <- deq_fifoL2E__0_0();
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
        let x_10 <- getMSHR__0_0(x_4);
        let x_11 <- getMSHRRq__0_0(x_4);
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
            let x_20 <- victims___0_0__setVictim(Struct17 {victim_idx :
            (x_8).data, victim_info : (x_19).info, victim_value :
            ((x_19).value_write ? ((x_19).value) : (x_9))});
            x_22 = x_9;
        end else begin
            let x_21 <- cache___0_0__valueRsLineRq(x_19);
            x_22 = x_21;
        end
        Struct18 x_23 = (Struct18 {enq_type : ((((Bit#(4))'(4'h8))[3:2]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : (((((Bit#(4))'(4'h8))[3:2])
        == ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : ((Bit#(4))'(4'h8))[1:0], enq_msg : Struct1 {id :
        (Bit#(6))'(6'h16), type_ : (Bool)'(True), addr : (x_17).addr, value :
        unpack(0)}});
        let x_24 <- makeEnq_parentChildren_0_0(x_23);
        let x_25 <- releaseMSHR__0_0(x_4);
    endrule
    
    rule rule_exec__0_0__2_7_0_0_0;
        let x_0 <- deq_fifoL2E__0_0();
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
        let x_10 <- getMSHR__0_0(x_4);
        let x_11 <- getMSHRRq__0_0(x_4);
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
            let x_21 <- victims___0_0__setVictim(Struct17 {victim_idx :
            (x_8).data, victim_info : (x_20).info, victim_value :
            ((x_20).value_write ? ((x_20).value) : (x_9))});
            x_23 = x_9;
        end else begin
            let x_22 <- cache___0_0__valueRsLineRq(x_20);
            x_23 = x_22;
        end
        Struct18 x_24 = (Struct18 {enq_type : ((((Bit#(4))'(4'h8))[3:2]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : (((((Bit#(4))'(4'h8))[3:2])
        == ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : ((Bit#(4))'(4'h8))[1:0], enq_msg : Struct1 {id :
        (Bit#(6))'(6'h16), type_ : (Bool)'(True), addr : (x_17).addr, value :
        unpack(0)}});
        let x_25 <- makeEnq_parentChildren_0_0(x_24);
        let x_26 <- releaseMSHR__0_0(x_4);
    endrule
    
    rule rule_exec__0_0__2_8_0_0_0;
        let x_0 <- deq_fifoL2E__0_0();
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
        let x_10 <- getMSHR__0_0(x_4);
        let x_11 <- getMSHRRq__0_0(x_4);
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
            let x_19 <- cache___0_0__valueRsLineRq(unpack(0));
            x_20 = x_19;
        end
        Struct18 x_21 = (Struct18 {enq_type : ((((Bit#(4))'(4'h8))[3:2]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : (((((Bit#(4))'(4'h8))[3:2])
        == ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : ((Bit#(4))'(4'h8))[1:0], enq_msg : Struct1 {id :
        (Bit#(6))'(6'h16), type_ : (Bool)'(True), addr : (x_17).addr, value :
        unpack(0)}});
        let x_22 <- makeEnq_parentChildren_0_0(x_21);
        let x_23 <- releaseMSHR__0_0(x_4);
    endrule
    
    rule rule_exec__0_0__2_9_0_0_0_0;
        let x_0 <- deq_fifoL2E__0_0();
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
        let x_10 <- getMSHR__0_0(x_4);
        let x_11 <- getMSHRRq__0_0(x_4);
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
            let x_20 <- victims___0_0__setVictim(Struct17 {victim_idx :
            (x_8).data, victim_info : (x_19).info, victim_value :
            ((x_19).value_write ? ((x_19).value) : (x_9))});
            x_22 = x_9;
        end else begin
            let x_21 <- cache___0_0__valueRsLineRq(x_19);
            x_22 = x_21;
        end
        Struct18 x_23 = (Struct18 {enq_type : ((((Bit#(4))'(4'h8))[3:2]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : (((((Bit#(4))'(4'h8))[3:2])
        == ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : ((Bit#(4))'(4'h8))[1:0], enq_msg : Struct1 {id :
        (Bit#(6))'(6'h16), type_ : (Bool)'(True), addr : (x_17).addr, value :
        unpack(0)}});
        let x_24 <- makeEnq_parentChildren_0_0(x_23);
        let x_25 <- releaseMSHR__0_0(x_4);
    endrule
    
    rule rule_exec__0_0__2_9_1_0_0_0;
        let x_0 <- deq_fifoL2E__0_0();
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
        let x_10 <- getMSHR__0_0(x_4);
        let x_11 <- getMSHRRq__0_0(x_4);
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
            let x_20 <- victims___0_0__setVictim(Struct17 {victim_idx :
            (x_8).data, victim_info : (x_19).info, victim_value :
            ((x_19).value_write ? ((x_19).value) : (x_9))});
            x_22 = x_9;
        end else begin
            let x_21 <- cache___0_0__valueRsLineRq(x_19);
            x_22 = x_21;
        end
        Struct18 x_23 = (Struct18 {enq_type : ((((Bit#(4))'(4'h8))[3:2]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : (((((Bit#(4))'(4'h8))[3:2])
        == ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : ((Bit#(4))'(4'h8))[1:0], enq_msg : Struct1 {id :
        (Bit#(6))'(6'h16), type_ : (Bool)'(True), addr : (x_17).addr, value :
        unpack(0)}});
        let x_24 <- makeEnq_parentChildren_0_0(x_23);
        let x_25 <- releaseMSHR__0_0(x_4);
    endrule
    
    rule rule_exec__0_0__2_10_0_0_0;
        let x_0 <- deq_fifoL2E__0_0();
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
        let x_10 <- getMSHR__0_0(x_4);
        let x_11 <- getMSHRRq__0_0(x_4);
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
            let x_21 <- victims___0_0__setVictim(Struct17 {victim_idx :
            (x_8).data, victim_info : (x_20).info, victim_value :
            ((x_20).value_write ? ((x_20).value) : (x_9))});
            x_23 = x_9;
        end else begin
            let x_22 <- cache___0_0__valueRsLineRq(x_20);
            x_23 = x_22;
        end
        Struct18 x_24 = (Struct18 {enq_type : ((((Bit#(4))'(4'h8))[3:2]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : (((((Bit#(4))'(4'h8))[3:2])
        == ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : ((Bit#(4))'(4'h8))[1:0], enq_msg : Struct1 {id :
        (Bit#(6))'(6'h16), type_ : (Bool)'(True), addr : (x_17).addr, value :
        unpack(0)}});
        let x_25 <- makeEnq_parentChildren_0_0(x_24);
        let x_26 <- releaseMSHR__0_0(x_4);
    endrule
    
    rule rule_exec__0_0__2_11_0_0_0;
        let x_0 <- deq_fifoL2E__0_0();
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
        let x_10 <- getMSHR__0_0(x_4);
        let x_11 <- getMSHRRq__0_0(x_4);
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
            let x_23 <- victims___0_0__setVictim(Struct17 {victim_idx :
            (x_8).data, victim_info : (x_22).info, victim_value :
            ((x_22).value_write ? ((x_22).value) : (x_9))});
            x_25 = x_9;
        end else begin
            let x_24 <- cache___0_0__valueRsLineRq(x_22);
            x_25 = x_24;
        end
        Struct18 x_26 = (Struct18 {enq_type : ((((Bit#(4))'(4'h8))[3:2]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : (((((Bit#(4))'(4'h8))[3:2])
        == ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : ((Bit#(4))'(4'h8))[1:0], enq_msg : Struct1 {id :
        (Bit#(6))'(6'h16), type_ : (Bool)'(True), addr : (x_17).addr, value :
        unpack(0)}});
        let x_27 <- makeEnq_parentChildren_0_0(x_26);
        let x_28 <- releaseMSHR__0_0(x_4);
    endrule
    
    rule rule_exec__0_0__0_0_0_0_0_1;
        let x_0 <- deq_fifoL2E__0_0();
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
        let x_10 <- getMSHR__0_0(x_4);
        let x_11 <- getMSHRRq__0_0(x_4);
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
            let x_20 <- victims___0_0__setVictim(Struct17 {victim_idx :
            (x_8).data, victim_info : (x_19).info, victim_value :
            ((x_19).value_write ? ((x_19).value) : (x_9))});
            x_22 = x_9;
        end else begin
            let x_21 <- cache___0_0__valueRsLineRq(x_19);
            x_22 = x_21;
        end
        Struct18 x_23 = (Struct18 {enq_type : ((((Bit#(4))'(4'h9))[3:2]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : (((((Bit#(4))'(4'h9))[3:2])
        == ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : ((Bit#(4))'(4'h9))[1:0], enq_msg : Struct1 {id :
        (Bit#(6))'(6'h3), type_ : (Bool)'(True), addr : (x_17).addr, value :
        x_22}});
        let x_24 <- makeEnq_parentChildren_0_0(x_23);
        let x_25 <- releaseMSHR__0_0(x_4);
    endrule
    
    rule rule_exec__0_0__0_0_1_0_0_1;
        let x_0 <- deq_fifoL2E__0_0();
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
        let x_10 <- getMSHR__0_0(x_4);
        let x_11 <- getMSHRRq__0_0(x_4);
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
            let x_21 <- victims___0_0__setVictim(Struct17 {victim_idx :
            (x_8).data, victim_info : (x_20).info, victim_value :
            ((x_20).value_write ? ((x_20).value) : (x_9))});
            x_23 = x_9;
        end else begin
            let x_22 <- cache___0_0__valueRsLineRq(x_20);
            x_23 = x_22;
        end
        Struct18 x_24 = (Struct18 {enq_type : ((((Bit#(4))'(4'h9))[3:2]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : (((((Bit#(4))'(4'h9))[3:2])
        == ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : ((Bit#(4))'(4'h9))[1:0], enq_msg : Struct1 {id :
        (Bit#(6))'(6'h4), type_ : (Bool)'(True), addr : (x_17).addr, value :
        x_23}});
        let x_25 <- makeEnq_parentChildren_0_0(x_24);
        let x_26 <- releaseMSHR__0_0(x_4);
    endrule
    
    rule rule_exec__0_0__0_1_0_0_1;
        let x_0 <- deq_fifoL2E__0_0();
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
        let x_10 <- getMSHR__0_0(x_4);
        let x_11 <- getMSHRRq__0_0(x_4);
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
            let x_19 <- cache___0_0__valueRsLineRq(unpack(0));
            x_20 = x_19;
        end
        let x_21 <- registerUL__0_0(Struct19 {r_id : x_4, r_ul_rsb :
        (Bool)'(True), r_ul_rsbTo : ((Bit#(4))'(4'h9))[1:0]});
        Struct18 x_22 = (Struct18 {enq_type : ((((Bit#(4))'(4'h0))[3:2]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : (((((Bit#(4))'(4'h0))[3:2])
        == ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : ((Bit#(4))'(4'h0))[1:0], enq_msg : Struct1 {id :
        (Bit#(6))'(6'h2), type_ : (Bool)'(False), addr : (x_17).addr, value :
        unpack(0)}});
        let x_23 <- makeEnq_parentChildren_0_0(x_22);
    endrule
    
    rule rule_exec__0_0__0_3_0_0_1;
        let x_0 <- deq_fifoL2E__0_0();
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
        let x_10 <- getMSHR__0_0(x_4);
        let x_11 <- getMSHRRq__0_0(x_4);
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
            let x_19 <- cache___0_0__valueRsLineRq(unpack(0));
            x_20 = x_19;
        end
        let x_21 <- registerDL__0_0(Struct20 {r_id : x_4, r_dl_rss_from :
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
        let x_23 <- makeEnq_parentChildren_0_0(x_22);
    endrule
    
    rule rule_exec__0_0__1_0_0_0_1;
        let x_0 <- deq_fifoL2E__0_0();
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
        let x_10 <- getMSHR__0_0(x_4);
        let x_11 <- getMSHRRq__0_0(x_4);
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
            let x_22 <- victims___0_0__setVictim(Struct17 {victim_idx :
            (x_8).data, victim_info : (x_21).info, victim_value :
            ((x_21).value_write ? ((x_21).value) : (x_9))});
            x_24 = x_9;
        end else begin
            let x_23 <- cache___0_0__valueRsLineRq(x_21);
            x_24 = x_23;
        end
        Struct18 x_25 = (Struct18 {enq_type : ((((Bit#(4))'(4'h9))[3:2]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : (((((Bit#(4))'(4'h9))[3:2])
        == ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : ((Bit#(4))'(4'h9))[1:0], enq_msg : Struct1 {id :
        (Bit#(6))'(6'hb), type_ : (Bool)'(True), addr : (x_17).addr, value :
        unpack(0)}});
        let x_26 <- makeEnq_parentChildren_0_0(x_25);
        let x_27 <- releaseMSHR__0_0(x_4);
    endrule
    
    rule rule_exec__0_0__1_1_0_0_1;
        let x_0 <- deq_fifoL2E__0_0();
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
        let x_10 <- getMSHR__0_0(x_4);
        let x_11 <- getMSHRRq__0_0(x_4);
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
            let x_19 <- cache___0_0__valueRsLineRq(unpack(0));
            x_20 = x_19;
        end
        let x_21 <- registerUL__0_0(Struct19 {r_id : x_4, r_ul_rsb :
        (Bool)'(True), r_ul_rsbTo : ((Bit#(4))'(4'h9))[1:0]});
        Struct18 x_22 = (Struct18 {enq_type : ((((Bit#(4))'(4'h0))[3:2]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : (((((Bit#(4))'(4'h0))[3:2])
        == ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : ((Bit#(4))'(4'h0))[1:0], enq_msg : Struct1 {id :
        (Bit#(6))'(6'ha), type_ : (Bool)'(False), addr : (x_17).addr, value :
        unpack(0)}});
        let x_23 <- makeEnq_parentChildren_0_0(x_22);
    endrule
    
    rule rule_exec__0_0__1_4_0_0_1;
        let x_0 <- deq_fifoL2E__0_0();
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
        let x_10 <- getMSHR__0_0(x_4);
        let x_11 <- getMSHRRq__0_0(x_4);
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
            let x_19 <- cache___0_0__valueRsLineRq(unpack(0));
            x_20 = x_19;
        end
        let x_21 <- registerDL__0_0(Struct20 {r_id : x_4, r_dl_rss_from :
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
        let x_23 <- makeEnq_parentChildren_0_0(x_22);
    endrule
    
    rule rule_exec__0_0__1_5_0_0_1;
        let x_0 <- deq_fifoL2E__0_0();
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
        let x_10 <- getMSHR__0_0(x_4);
        let x_11 <- getMSHRRq__0_0(x_4);
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
            let x_19 <- cache___0_0__valueRsLineRq(unpack(0));
            x_20 = x_19;
        end
        let x_21 <- registerDL__0_0(Struct20 {r_id : x_4, r_dl_rss_from :
        ((x_16).dir_sharers) & (~(((Bit#(4))'(4'h1)) << ((Bit#(2))'(2'h1)))),
        r_dl_rsb : (Bool)'(True), r_dl_rsbTo : (Bit#(4))'(4'h9)});
        let x_22 <- broadcast_parentChildren_0_0(Struct21 {cs_inds :
        ((x_16).dir_sharers) & (~(((Bit#(4))'(4'h1)) << ((Bit#(2))'(2'h1)))),
        cs_msg : Struct1 {id : (Bit#(6))'(6'hc), type_ : (Bool)'(False), addr
        : (x_17).addr, value : unpack(0)}});
    endrule
    
    rule rule_exec__0_0__2_5_0_0_1;
        let x_0 <- deq_fifoL2E__0_0();
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
        let x_10 <- getMSHR__0_0(x_4);
        let x_11 <- getMSHRRq__0_0(x_4);
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
            let x_19 <- cache___0_0__valueRsLineRq(unpack(0));
            x_20 = x_19;
        end
        Struct18 x_21 = (Struct18 {enq_type : ((((Bit#(4))'(4'h9))[3:2]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : (((((Bit#(4))'(4'h9))[3:2])
        == ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : ((Bit#(4))'(4'h9))[1:0], enq_msg : Struct1 {id :
        (Bit#(6))'(6'h16), type_ : (Bool)'(True), addr : (x_17).addr, value :
        unpack(0)}});
        let x_22 <- makeEnq_parentChildren_0_0(x_21);
        let x_23 <- releaseMSHR__0_0(x_4);
    endrule
    
    rule rule_exec__0_0__2_6_0_0_0_0_1;
        let x_0 <- deq_fifoL2E__0_0();
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
        let x_10 <- getMSHR__0_0(x_4);
        let x_11 <- getMSHRRq__0_0(x_4);
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
            let x_20 <- victims___0_0__setVictim(Struct17 {victim_idx :
            (x_8).data, victim_info : (x_19).info, victim_value :
            ((x_19).value_write ? ((x_19).value) : (x_9))});
            x_22 = x_9;
        end else begin
            let x_21 <- cache___0_0__valueRsLineRq(x_19);
            x_22 = x_21;
        end
        Struct18 x_23 = (Struct18 {enq_type : ((((Bit#(4))'(4'h9))[3:2]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : (((((Bit#(4))'(4'h9))[3:2])
        == ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : ((Bit#(4))'(4'h9))[1:0], enq_msg : Struct1 {id :
        (Bit#(6))'(6'h16), type_ : (Bool)'(True), addr : (x_17).addr, value :
        unpack(0)}});
        let x_24 <- makeEnq_parentChildren_0_0(x_23);
        let x_25 <- releaseMSHR__0_0(x_4);
    endrule
    
    rule rule_exec__0_0__2_6_0_1_0_0_1;
        let x_0 <- deq_fifoL2E__0_0();
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
        let x_10 <- getMSHR__0_0(x_4);
        let x_11 <- getMSHRRq__0_0(x_4);
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
            let x_21 <- victims___0_0__setVictim(Struct17 {victim_idx :
            (x_8).data, victim_info : (x_20).info, victim_value :
            ((x_20).value_write ? ((x_20).value) : (x_9))});
            x_23 = x_9;
        end else begin
            let x_22 <- cache___0_0__valueRsLineRq(x_20);
            x_23 = x_22;
        end
        Struct18 x_24 = (Struct18 {enq_type : ((((Bit#(4))'(4'h9))[3:2]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : (((((Bit#(4))'(4'h9))[3:2])
        == ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : ((Bit#(4))'(4'h9))[1:0], enq_msg : Struct1 {id :
        (Bit#(6))'(6'h16), type_ : (Bool)'(True), addr : (x_17).addr, value :
        unpack(0)}});
        let x_25 <- makeEnq_parentChildren_0_0(x_24);
        let x_26 <- releaseMSHR__0_0(x_4);
    endrule
    
    rule rule_exec__0_0__2_6_1_0_0_1;
        let x_0 <- deq_fifoL2E__0_0();
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
        let x_10 <- getMSHR__0_0(x_4);
        let x_11 <- getMSHRRq__0_0(x_4);
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
            let x_20 <- victims___0_0__setVictim(Struct17 {victim_idx :
            (x_8).data, victim_info : (x_19).info, victim_value :
            ((x_19).value_write ? ((x_19).value) : (x_9))});
            x_22 = x_9;
        end else begin
            let x_21 <- cache___0_0__valueRsLineRq(x_19);
            x_22 = x_21;
        end
        Struct18 x_23 = (Struct18 {enq_type : ((((Bit#(4))'(4'h9))[3:2]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : (((((Bit#(4))'(4'h9))[3:2])
        == ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : ((Bit#(4))'(4'h9))[1:0], enq_msg : Struct1 {id :
        (Bit#(6))'(6'h16), type_ : (Bool)'(True), addr : (x_17).addr, value :
        unpack(0)}});
        let x_24 <- makeEnq_parentChildren_0_0(x_23);
        let x_25 <- releaseMSHR__0_0(x_4);
    endrule
    
    rule rule_exec__0_0__2_7_0_0_1;
        let x_0 <- deq_fifoL2E__0_0();
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
        let x_10 <- getMSHR__0_0(x_4);
        let x_11 <- getMSHRRq__0_0(x_4);
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
            let x_21 <- victims___0_0__setVictim(Struct17 {victim_idx :
            (x_8).data, victim_info : (x_20).info, victim_value :
            ((x_20).value_write ? ((x_20).value) : (x_9))});
            x_23 = x_9;
        end else begin
            let x_22 <- cache___0_0__valueRsLineRq(x_20);
            x_23 = x_22;
        end
        Struct18 x_24 = (Struct18 {enq_type : ((((Bit#(4))'(4'h9))[3:2]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : (((((Bit#(4))'(4'h9))[3:2])
        == ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : ((Bit#(4))'(4'h9))[1:0], enq_msg : Struct1 {id :
        (Bit#(6))'(6'h16), type_ : (Bool)'(True), addr : (x_17).addr, value :
        unpack(0)}});
        let x_25 <- makeEnq_parentChildren_0_0(x_24);
        let x_26 <- releaseMSHR__0_0(x_4);
    endrule
    
    rule rule_exec__0_0__2_8_0_0_1;
        let x_0 <- deq_fifoL2E__0_0();
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
        let x_10 <- getMSHR__0_0(x_4);
        let x_11 <- getMSHRRq__0_0(x_4);
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
            let x_19 <- cache___0_0__valueRsLineRq(unpack(0));
            x_20 = x_19;
        end
        Struct18 x_21 = (Struct18 {enq_type : ((((Bit#(4))'(4'h9))[3:2]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : (((((Bit#(4))'(4'h9))[3:2])
        == ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : ((Bit#(4))'(4'h9))[1:0], enq_msg : Struct1 {id :
        (Bit#(6))'(6'h16), type_ : (Bool)'(True), addr : (x_17).addr, value :
        unpack(0)}});
        let x_22 <- makeEnq_parentChildren_0_0(x_21);
        let x_23 <- releaseMSHR__0_0(x_4);
    endrule
    
    rule rule_exec__0_0__2_9_0_0_0_1;
        let x_0 <- deq_fifoL2E__0_0();
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
        let x_10 <- getMSHR__0_0(x_4);
        let x_11 <- getMSHRRq__0_0(x_4);
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
            let x_20 <- victims___0_0__setVictim(Struct17 {victim_idx :
            (x_8).data, victim_info : (x_19).info, victim_value :
            ((x_19).value_write ? ((x_19).value) : (x_9))});
            x_22 = x_9;
        end else begin
            let x_21 <- cache___0_0__valueRsLineRq(x_19);
            x_22 = x_21;
        end
        Struct18 x_23 = (Struct18 {enq_type : ((((Bit#(4))'(4'h9))[3:2]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : (((((Bit#(4))'(4'h9))[3:2])
        == ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : ((Bit#(4))'(4'h9))[1:0], enq_msg : Struct1 {id :
        (Bit#(6))'(6'h16), type_ : (Bool)'(True), addr : (x_17).addr, value :
        unpack(0)}});
        let x_24 <- makeEnq_parentChildren_0_0(x_23);
        let x_25 <- releaseMSHR__0_0(x_4);
    endrule
    
    rule rule_exec__0_0__2_9_1_0_0_1;
        let x_0 <- deq_fifoL2E__0_0();
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
        let x_10 <- getMSHR__0_0(x_4);
        let x_11 <- getMSHRRq__0_0(x_4);
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
            let x_20 <- victims___0_0__setVictim(Struct17 {victim_idx :
            (x_8).data, victim_info : (x_19).info, victim_value :
            ((x_19).value_write ? ((x_19).value) : (x_9))});
            x_22 = x_9;
        end else begin
            let x_21 <- cache___0_0__valueRsLineRq(x_19);
            x_22 = x_21;
        end
        Struct18 x_23 = (Struct18 {enq_type : ((((Bit#(4))'(4'h9))[3:2]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : (((((Bit#(4))'(4'h9))[3:2])
        == ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : ((Bit#(4))'(4'h9))[1:0], enq_msg : Struct1 {id :
        (Bit#(6))'(6'h16), type_ : (Bool)'(True), addr : (x_17).addr, value :
        unpack(0)}});
        let x_24 <- makeEnq_parentChildren_0_0(x_23);
        let x_25 <- releaseMSHR__0_0(x_4);
    endrule
    
    rule rule_exec__0_0__2_10_0_0_1;
        let x_0 <- deq_fifoL2E__0_0();
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
        let x_10 <- getMSHR__0_0(x_4);
        let x_11 <- getMSHRRq__0_0(x_4);
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
            let x_21 <- victims___0_0__setVictim(Struct17 {victim_idx :
            (x_8).data, victim_info : (x_20).info, victim_value :
            ((x_20).value_write ? ((x_20).value) : (x_9))});
            x_23 = x_9;
        end else begin
            let x_22 <- cache___0_0__valueRsLineRq(x_20);
            x_23 = x_22;
        end
        Struct18 x_24 = (Struct18 {enq_type : ((((Bit#(4))'(4'h9))[3:2]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : (((((Bit#(4))'(4'h9))[3:2])
        == ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : ((Bit#(4))'(4'h9))[1:0], enq_msg : Struct1 {id :
        (Bit#(6))'(6'h16), type_ : (Bool)'(True), addr : (x_17).addr, value :
        unpack(0)}});
        let x_25 <- makeEnq_parentChildren_0_0(x_24);
        let x_26 <- releaseMSHR__0_0(x_4);
    endrule
    
    rule rule_exec__0_0__2_11_0_0_1;
        let x_0 <- deq_fifoL2E__0_0();
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
        let x_10 <- getMSHR__0_0(x_4);
        let x_11 <- getMSHRRq__0_0(x_4);
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
            let x_23 <- victims___0_0__setVictim(Struct17 {victim_idx :
            (x_8).data, victim_info : (x_22).info, victim_value :
            ((x_22).value_write ? ((x_22).value) : (x_9))});
            x_25 = x_9;
        end else begin
            let x_24 <- cache___0_0__valueRsLineRq(x_22);
            x_25 = x_24;
        end
        Struct18 x_26 = (Struct18 {enq_type : ((((Bit#(4))'(4'h9))[3:2]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : (((((Bit#(4))'(4'h9))[3:2])
        == ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : ((Bit#(4))'(4'h9))[1:0], enq_msg : Struct1 {id :
        (Bit#(6))'(6'h16), type_ : (Bool)'(True), addr : (x_17).addr, value :
        unpack(0)}});
        let x_27 <- makeEnq_parentChildren_0_0(x_26);
        let x_28 <- releaseMSHR__0_0(x_4);
    endrule
    
    rule rule_exec__0_0__0_0_0_0_0_2;
        let x_0 <- deq_fifoL2E__0_0();
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
        let x_10 <- getMSHR__0_0(x_4);
        let x_11 <- getMSHRRq__0_0(x_4);
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
            let x_20 <- victims___0_0__setVictim(Struct17 {victim_idx :
            (x_8).data, victim_info : (x_19).info, victim_value :
            ((x_19).value_write ? ((x_19).value) : (x_9))});
            x_22 = x_9;
        end else begin
            let x_21 <- cache___0_0__valueRsLineRq(x_19);
            x_22 = x_21;
        end
        Struct18 x_23 = (Struct18 {enq_type : ((((Bit#(4))'(4'ha))[3:2]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : (((((Bit#(4))'(4'ha))[3:2])
        == ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : ((Bit#(4))'(4'ha))[1:0], enq_msg : Struct1 {id :
        (Bit#(6))'(6'h3), type_ : (Bool)'(True), addr : (x_17).addr, value :
        x_22}});
        let x_24 <- makeEnq_parentChildren_0_0(x_23);
        let x_25 <- releaseMSHR__0_0(x_4);
    endrule
    
    rule rule_exec__0_0__0_0_1_0_0_2;
        let x_0 <- deq_fifoL2E__0_0();
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
        let x_10 <- getMSHR__0_0(x_4);
        let x_11 <- getMSHRRq__0_0(x_4);
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
            let x_21 <- victims___0_0__setVictim(Struct17 {victim_idx :
            (x_8).data, victim_info : (x_20).info, victim_value :
            ((x_20).value_write ? ((x_20).value) : (x_9))});
            x_23 = x_9;
        end else begin
            let x_22 <- cache___0_0__valueRsLineRq(x_20);
            x_23 = x_22;
        end
        Struct18 x_24 = (Struct18 {enq_type : ((((Bit#(4))'(4'ha))[3:2]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : (((((Bit#(4))'(4'ha))[3:2])
        == ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : ((Bit#(4))'(4'ha))[1:0], enq_msg : Struct1 {id :
        (Bit#(6))'(6'h4), type_ : (Bool)'(True), addr : (x_17).addr, value :
        x_23}});
        let x_25 <- makeEnq_parentChildren_0_0(x_24);
        let x_26 <- releaseMSHR__0_0(x_4);
    endrule
    
    rule rule_exec__0_0__0_1_0_0_2;
        let x_0 <- deq_fifoL2E__0_0();
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
        let x_10 <- getMSHR__0_0(x_4);
        let x_11 <- getMSHRRq__0_0(x_4);
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
            let x_19 <- cache___0_0__valueRsLineRq(unpack(0));
            x_20 = x_19;
        end
        let x_21 <- registerUL__0_0(Struct19 {r_id : x_4, r_ul_rsb :
        (Bool)'(True), r_ul_rsbTo : ((Bit#(4))'(4'ha))[1:0]});
        Struct18 x_22 = (Struct18 {enq_type : ((((Bit#(4))'(4'h0))[3:2]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : (((((Bit#(4))'(4'h0))[3:2])
        == ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : ((Bit#(4))'(4'h0))[1:0], enq_msg : Struct1 {id :
        (Bit#(6))'(6'h2), type_ : (Bool)'(False), addr : (x_17).addr, value :
        unpack(0)}});
        let x_23 <- makeEnq_parentChildren_0_0(x_22);
    endrule
    
    rule rule_exec__0_0__0_3_0_0_2;
        let x_0 <- deq_fifoL2E__0_0();
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
        let x_10 <- getMSHR__0_0(x_4);
        let x_11 <- getMSHRRq__0_0(x_4);
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
            let x_19 <- cache___0_0__valueRsLineRq(unpack(0));
            x_20 = x_19;
        end
        let x_21 <- registerDL__0_0(Struct20 {r_id : x_4, r_dl_rss_from :
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
        let x_23 <- makeEnq_parentChildren_0_0(x_22);
    endrule
    
    rule rule_exec__0_0__1_0_0_0_2;
        let x_0 <- deq_fifoL2E__0_0();
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
        let x_10 <- getMSHR__0_0(x_4);
        let x_11 <- getMSHRRq__0_0(x_4);
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
            let x_22 <- victims___0_0__setVictim(Struct17 {victim_idx :
            (x_8).data, victim_info : (x_21).info, victim_value :
            ((x_21).value_write ? ((x_21).value) : (x_9))});
            x_24 = x_9;
        end else begin
            let x_23 <- cache___0_0__valueRsLineRq(x_21);
            x_24 = x_23;
        end
        Struct18 x_25 = (Struct18 {enq_type : ((((Bit#(4))'(4'ha))[3:2]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : (((((Bit#(4))'(4'ha))[3:2])
        == ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : ((Bit#(4))'(4'ha))[1:0], enq_msg : Struct1 {id :
        (Bit#(6))'(6'hb), type_ : (Bool)'(True), addr : (x_17).addr, value :
        unpack(0)}});
        let x_26 <- makeEnq_parentChildren_0_0(x_25);
        let x_27 <- releaseMSHR__0_0(x_4);
    endrule
    
    rule rule_exec__0_0__1_1_0_0_2;
        let x_0 <- deq_fifoL2E__0_0();
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
        let x_10 <- getMSHR__0_0(x_4);
        let x_11 <- getMSHRRq__0_0(x_4);
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
            let x_19 <- cache___0_0__valueRsLineRq(unpack(0));
            x_20 = x_19;
        end
        let x_21 <- registerUL__0_0(Struct19 {r_id : x_4, r_ul_rsb :
        (Bool)'(True), r_ul_rsbTo : ((Bit#(4))'(4'ha))[1:0]});
        Struct18 x_22 = (Struct18 {enq_type : ((((Bit#(4))'(4'h0))[3:2]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : (((((Bit#(4))'(4'h0))[3:2])
        == ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : ((Bit#(4))'(4'h0))[1:0], enq_msg : Struct1 {id :
        (Bit#(6))'(6'ha), type_ : (Bool)'(False), addr : (x_17).addr, value :
        unpack(0)}});
        let x_23 <- makeEnq_parentChildren_0_0(x_22);
    endrule
    
    rule rule_exec__0_0__1_4_0_0_2;
        let x_0 <- deq_fifoL2E__0_0();
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
        let x_10 <- getMSHR__0_0(x_4);
        let x_11 <- getMSHRRq__0_0(x_4);
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
            let x_19 <- cache___0_0__valueRsLineRq(unpack(0));
            x_20 = x_19;
        end
        let x_21 <- registerDL__0_0(Struct20 {r_id : x_4, r_dl_rss_from :
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
        let x_23 <- makeEnq_parentChildren_0_0(x_22);
    endrule
    
    rule rule_exec__0_0__1_5_0_0_2;
        let x_0 <- deq_fifoL2E__0_0();
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
        let x_10 <- getMSHR__0_0(x_4);
        let x_11 <- getMSHRRq__0_0(x_4);
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
            let x_19 <- cache___0_0__valueRsLineRq(unpack(0));
            x_20 = x_19;
        end
        let x_21 <- registerDL__0_0(Struct20 {r_id : x_4, r_dl_rss_from :
        ((x_16).dir_sharers) & (~(((Bit#(4))'(4'h1)) << ((Bit#(2))'(2'h2)))),
        r_dl_rsb : (Bool)'(True), r_dl_rsbTo : (Bit#(4))'(4'ha)});
        let x_22 <- broadcast_parentChildren_0_0(Struct21 {cs_inds :
        ((x_16).dir_sharers) & (~(((Bit#(4))'(4'h1)) << ((Bit#(2))'(2'h2)))),
        cs_msg : Struct1 {id : (Bit#(6))'(6'hc), type_ : (Bool)'(False), addr
        : (x_17).addr, value : unpack(0)}});
    endrule
    
    rule rule_exec__0_0__2_5_0_0_2;
        let x_0 <- deq_fifoL2E__0_0();
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
        let x_10 <- getMSHR__0_0(x_4);
        let x_11 <- getMSHRRq__0_0(x_4);
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
            let x_19 <- cache___0_0__valueRsLineRq(unpack(0));
            x_20 = x_19;
        end
        Struct18 x_21 = (Struct18 {enq_type : ((((Bit#(4))'(4'ha))[3:2]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : (((((Bit#(4))'(4'ha))[3:2])
        == ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : ((Bit#(4))'(4'ha))[1:0], enq_msg : Struct1 {id :
        (Bit#(6))'(6'h16), type_ : (Bool)'(True), addr : (x_17).addr, value :
        unpack(0)}});
        let x_22 <- makeEnq_parentChildren_0_0(x_21);
        let x_23 <- releaseMSHR__0_0(x_4);
    endrule
    
    rule rule_exec__0_0__2_6_0_0_0_0_2;
        let x_0 <- deq_fifoL2E__0_0();
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
        let x_10 <- getMSHR__0_0(x_4);
        let x_11 <- getMSHRRq__0_0(x_4);
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
            let x_20 <- victims___0_0__setVictim(Struct17 {victim_idx :
            (x_8).data, victim_info : (x_19).info, victim_value :
            ((x_19).value_write ? ((x_19).value) : (x_9))});
            x_22 = x_9;
        end else begin
            let x_21 <- cache___0_0__valueRsLineRq(x_19);
            x_22 = x_21;
        end
        Struct18 x_23 = (Struct18 {enq_type : ((((Bit#(4))'(4'ha))[3:2]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : (((((Bit#(4))'(4'ha))[3:2])
        == ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : ((Bit#(4))'(4'ha))[1:0], enq_msg : Struct1 {id :
        (Bit#(6))'(6'h16), type_ : (Bool)'(True), addr : (x_17).addr, value :
        unpack(0)}});
        let x_24 <- makeEnq_parentChildren_0_0(x_23);
        let x_25 <- releaseMSHR__0_0(x_4);
    endrule
    
    rule rule_exec__0_0__2_6_0_1_0_0_2;
        let x_0 <- deq_fifoL2E__0_0();
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
        let x_10 <- getMSHR__0_0(x_4);
        let x_11 <- getMSHRRq__0_0(x_4);
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
            let x_21 <- victims___0_0__setVictim(Struct17 {victim_idx :
            (x_8).data, victim_info : (x_20).info, victim_value :
            ((x_20).value_write ? ((x_20).value) : (x_9))});
            x_23 = x_9;
        end else begin
            let x_22 <- cache___0_0__valueRsLineRq(x_20);
            x_23 = x_22;
        end
        Struct18 x_24 = (Struct18 {enq_type : ((((Bit#(4))'(4'ha))[3:2]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : (((((Bit#(4))'(4'ha))[3:2])
        == ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : ((Bit#(4))'(4'ha))[1:0], enq_msg : Struct1 {id :
        (Bit#(6))'(6'h16), type_ : (Bool)'(True), addr : (x_17).addr, value :
        unpack(0)}});
        let x_25 <- makeEnq_parentChildren_0_0(x_24);
        let x_26 <- releaseMSHR__0_0(x_4);
    endrule
    
    rule rule_exec__0_0__2_6_1_0_0_2;
        let x_0 <- deq_fifoL2E__0_0();
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
        let x_10 <- getMSHR__0_0(x_4);
        let x_11 <- getMSHRRq__0_0(x_4);
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
            let x_20 <- victims___0_0__setVictim(Struct17 {victim_idx :
            (x_8).data, victim_info : (x_19).info, victim_value :
            ((x_19).value_write ? ((x_19).value) : (x_9))});
            x_22 = x_9;
        end else begin
            let x_21 <- cache___0_0__valueRsLineRq(x_19);
            x_22 = x_21;
        end
        Struct18 x_23 = (Struct18 {enq_type : ((((Bit#(4))'(4'ha))[3:2]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : (((((Bit#(4))'(4'ha))[3:2])
        == ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : ((Bit#(4))'(4'ha))[1:0], enq_msg : Struct1 {id :
        (Bit#(6))'(6'h16), type_ : (Bool)'(True), addr : (x_17).addr, value :
        unpack(0)}});
        let x_24 <- makeEnq_parentChildren_0_0(x_23);
        let x_25 <- releaseMSHR__0_0(x_4);
    endrule
    
    rule rule_exec__0_0__2_7_0_0_2;
        let x_0 <- deq_fifoL2E__0_0();
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
        let x_10 <- getMSHR__0_0(x_4);
        let x_11 <- getMSHRRq__0_0(x_4);
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
            let x_21 <- victims___0_0__setVictim(Struct17 {victim_idx :
            (x_8).data, victim_info : (x_20).info, victim_value :
            ((x_20).value_write ? ((x_20).value) : (x_9))});
            x_23 = x_9;
        end else begin
            let x_22 <- cache___0_0__valueRsLineRq(x_20);
            x_23 = x_22;
        end
        Struct18 x_24 = (Struct18 {enq_type : ((((Bit#(4))'(4'ha))[3:2]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : (((((Bit#(4))'(4'ha))[3:2])
        == ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : ((Bit#(4))'(4'ha))[1:0], enq_msg : Struct1 {id :
        (Bit#(6))'(6'h16), type_ : (Bool)'(True), addr : (x_17).addr, value :
        unpack(0)}});
        let x_25 <- makeEnq_parentChildren_0_0(x_24);
        let x_26 <- releaseMSHR__0_0(x_4);
    endrule
    
    rule rule_exec__0_0__2_8_0_0_2;
        let x_0 <- deq_fifoL2E__0_0();
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
        let x_10 <- getMSHR__0_0(x_4);
        let x_11 <- getMSHRRq__0_0(x_4);
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
            let x_19 <- cache___0_0__valueRsLineRq(unpack(0));
            x_20 = x_19;
        end
        Struct18 x_21 = (Struct18 {enq_type : ((((Bit#(4))'(4'ha))[3:2]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : (((((Bit#(4))'(4'ha))[3:2])
        == ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : ((Bit#(4))'(4'ha))[1:0], enq_msg : Struct1 {id :
        (Bit#(6))'(6'h16), type_ : (Bool)'(True), addr : (x_17).addr, value :
        unpack(0)}});
        let x_22 <- makeEnq_parentChildren_0_0(x_21);
        let x_23 <- releaseMSHR__0_0(x_4);
    endrule
    
    rule rule_exec__0_0__2_9_0_0_0_2;
        let x_0 <- deq_fifoL2E__0_0();
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
        let x_10 <- getMSHR__0_0(x_4);
        let x_11 <- getMSHRRq__0_0(x_4);
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
            let x_20 <- victims___0_0__setVictim(Struct17 {victim_idx :
            (x_8).data, victim_info : (x_19).info, victim_value :
            ((x_19).value_write ? ((x_19).value) : (x_9))});
            x_22 = x_9;
        end else begin
            let x_21 <- cache___0_0__valueRsLineRq(x_19);
            x_22 = x_21;
        end
        Struct18 x_23 = (Struct18 {enq_type : ((((Bit#(4))'(4'ha))[3:2]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : (((((Bit#(4))'(4'ha))[3:2])
        == ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : ((Bit#(4))'(4'ha))[1:0], enq_msg : Struct1 {id :
        (Bit#(6))'(6'h16), type_ : (Bool)'(True), addr : (x_17).addr, value :
        unpack(0)}});
        let x_24 <- makeEnq_parentChildren_0_0(x_23);
        let x_25 <- releaseMSHR__0_0(x_4);
    endrule
    
    rule rule_exec__0_0__2_9_1_0_0_2;
        let x_0 <- deq_fifoL2E__0_0();
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
        let x_10 <- getMSHR__0_0(x_4);
        let x_11 <- getMSHRRq__0_0(x_4);
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
            let x_20 <- victims___0_0__setVictim(Struct17 {victim_idx :
            (x_8).data, victim_info : (x_19).info, victim_value :
            ((x_19).value_write ? ((x_19).value) : (x_9))});
            x_22 = x_9;
        end else begin
            let x_21 <- cache___0_0__valueRsLineRq(x_19);
            x_22 = x_21;
        end
        Struct18 x_23 = (Struct18 {enq_type : ((((Bit#(4))'(4'ha))[3:2]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : (((((Bit#(4))'(4'ha))[3:2])
        == ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : ((Bit#(4))'(4'ha))[1:0], enq_msg : Struct1 {id :
        (Bit#(6))'(6'h16), type_ : (Bool)'(True), addr : (x_17).addr, value :
        unpack(0)}});
        let x_24 <- makeEnq_parentChildren_0_0(x_23);
        let x_25 <- releaseMSHR__0_0(x_4);
    endrule
    
    rule rule_exec__0_0__2_10_0_0_2;
        let x_0 <- deq_fifoL2E__0_0();
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
        let x_10 <- getMSHR__0_0(x_4);
        let x_11 <- getMSHRRq__0_0(x_4);
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
            let x_21 <- victims___0_0__setVictim(Struct17 {victim_idx :
            (x_8).data, victim_info : (x_20).info, victim_value :
            ((x_20).value_write ? ((x_20).value) : (x_9))});
            x_23 = x_9;
        end else begin
            let x_22 <- cache___0_0__valueRsLineRq(x_20);
            x_23 = x_22;
        end
        Struct18 x_24 = (Struct18 {enq_type : ((((Bit#(4))'(4'ha))[3:2]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : (((((Bit#(4))'(4'ha))[3:2])
        == ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : ((Bit#(4))'(4'ha))[1:0], enq_msg : Struct1 {id :
        (Bit#(6))'(6'h16), type_ : (Bool)'(True), addr : (x_17).addr, value :
        unpack(0)}});
        let x_25 <- makeEnq_parentChildren_0_0(x_24);
        let x_26 <- releaseMSHR__0_0(x_4);
    endrule
    
    rule rule_exec__0_0__2_11_0_0_2;
        let x_0 <- deq_fifoL2E__0_0();
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
        let x_10 <- getMSHR__0_0(x_4);
        let x_11 <- getMSHRRq__0_0(x_4);
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
            let x_23 <- victims___0_0__setVictim(Struct17 {victim_idx :
            (x_8).data, victim_info : (x_22).info, victim_value :
            ((x_22).value_write ? ((x_22).value) : (x_9))});
            x_25 = x_9;
        end else begin
            let x_24 <- cache___0_0__valueRsLineRq(x_22);
            x_25 = x_24;
        end
        Struct18 x_26 = (Struct18 {enq_type : ((((Bit#(4))'(4'ha))[3:2]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : (((((Bit#(4))'(4'ha))[3:2])
        == ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : ((Bit#(4))'(4'ha))[1:0], enq_msg : Struct1 {id :
        (Bit#(6))'(6'h16), type_ : (Bool)'(True), addr : (x_17).addr, value :
        unpack(0)}});
        let x_27 <- makeEnq_parentChildren_0_0(x_26);
        let x_28 <- releaseMSHR__0_0(x_4);
    endrule
    
    rule rule_exec__0_0__0_0_0_0_0_3;
        let x_0 <- deq_fifoL2E__0_0();
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
        let x_10 <- getMSHR__0_0(x_4);
        let x_11 <- getMSHRRq__0_0(x_4);
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
            let x_20 <- victims___0_0__setVictim(Struct17 {victim_idx :
            (x_8).data, victim_info : (x_19).info, victim_value :
            ((x_19).value_write ? ((x_19).value) : (x_9))});
            x_22 = x_9;
        end else begin
            let x_21 <- cache___0_0__valueRsLineRq(x_19);
            x_22 = x_21;
        end
        Struct18 x_23 = (Struct18 {enq_type : ((((Bit#(4))'(4'hb))[3:2]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : (((((Bit#(4))'(4'hb))[3:2])
        == ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : ((Bit#(4))'(4'hb))[1:0], enq_msg : Struct1 {id :
        (Bit#(6))'(6'h3), type_ : (Bool)'(True), addr : (x_17).addr, value :
        x_22}});
        let x_24 <- makeEnq_parentChildren_0_0(x_23);
        let x_25 <- releaseMSHR__0_0(x_4);
    endrule
    
    rule rule_exec__0_0__0_0_1_0_0_3;
        let x_0 <- deq_fifoL2E__0_0();
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
        let x_10 <- getMSHR__0_0(x_4);
        let x_11 <- getMSHRRq__0_0(x_4);
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
            let x_21 <- victims___0_0__setVictim(Struct17 {victim_idx :
            (x_8).data, victim_info : (x_20).info, victim_value :
            ((x_20).value_write ? ((x_20).value) : (x_9))});
            x_23 = x_9;
        end else begin
            let x_22 <- cache___0_0__valueRsLineRq(x_20);
            x_23 = x_22;
        end
        Struct18 x_24 = (Struct18 {enq_type : ((((Bit#(4))'(4'hb))[3:2]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : (((((Bit#(4))'(4'hb))[3:2])
        == ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : ((Bit#(4))'(4'hb))[1:0], enq_msg : Struct1 {id :
        (Bit#(6))'(6'h4), type_ : (Bool)'(True), addr : (x_17).addr, value :
        x_23}});
        let x_25 <- makeEnq_parentChildren_0_0(x_24);
        let x_26 <- releaseMSHR__0_0(x_4);
    endrule
    
    rule rule_exec__0_0__0_1_0_0_3;
        let x_0 <- deq_fifoL2E__0_0();
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
        let x_10 <- getMSHR__0_0(x_4);
        let x_11 <- getMSHRRq__0_0(x_4);
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
            let x_19 <- cache___0_0__valueRsLineRq(unpack(0));
            x_20 = x_19;
        end
        let x_21 <- registerUL__0_0(Struct19 {r_id : x_4, r_ul_rsb :
        (Bool)'(True), r_ul_rsbTo : ((Bit#(4))'(4'hb))[1:0]});
        Struct18 x_22 = (Struct18 {enq_type : ((((Bit#(4))'(4'h0))[3:2]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : (((((Bit#(4))'(4'h0))[3:2])
        == ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : ((Bit#(4))'(4'h0))[1:0], enq_msg : Struct1 {id :
        (Bit#(6))'(6'h2), type_ : (Bool)'(False), addr : (x_17).addr, value :
        unpack(0)}});
        let x_23 <- makeEnq_parentChildren_0_0(x_22);
    endrule
    
    rule rule_exec__0_0__0_3_0_0_3;
        let x_0 <- deq_fifoL2E__0_0();
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
        let x_10 <- getMSHR__0_0(x_4);
        let x_11 <- getMSHRRq__0_0(x_4);
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
            let x_19 <- cache___0_0__valueRsLineRq(unpack(0));
            x_20 = x_19;
        end
        let x_21 <- registerDL__0_0(Struct20 {r_id : x_4, r_dl_rss_from :
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
        let x_23 <- makeEnq_parentChildren_0_0(x_22);
    endrule
    
    rule rule_exec__0_0__1_0_0_0_3;
        let x_0 <- deq_fifoL2E__0_0();
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
        let x_10 <- getMSHR__0_0(x_4);
        let x_11 <- getMSHRRq__0_0(x_4);
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
            let x_22 <- victims___0_0__setVictim(Struct17 {victim_idx :
            (x_8).data, victim_info : (x_21).info, victim_value :
            ((x_21).value_write ? ((x_21).value) : (x_9))});
            x_24 = x_9;
        end else begin
            let x_23 <- cache___0_0__valueRsLineRq(x_21);
            x_24 = x_23;
        end
        Struct18 x_25 = (Struct18 {enq_type : ((((Bit#(4))'(4'hb))[3:2]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : (((((Bit#(4))'(4'hb))[3:2])
        == ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : ((Bit#(4))'(4'hb))[1:0], enq_msg : Struct1 {id :
        (Bit#(6))'(6'hb), type_ : (Bool)'(True), addr : (x_17).addr, value :
        unpack(0)}});
        let x_26 <- makeEnq_parentChildren_0_0(x_25);
        let x_27 <- releaseMSHR__0_0(x_4);
    endrule
    
    rule rule_exec__0_0__1_1_0_0_3;
        let x_0 <- deq_fifoL2E__0_0();
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
        let x_10 <- getMSHR__0_0(x_4);
        let x_11 <- getMSHRRq__0_0(x_4);
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
            let x_19 <- cache___0_0__valueRsLineRq(unpack(0));
            x_20 = x_19;
        end
        let x_21 <- registerUL__0_0(Struct19 {r_id : x_4, r_ul_rsb :
        (Bool)'(True), r_ul_rsbTo : ((Bit#(4))'(4'hb))[1:0]});
        Struct18 x_22 = (Struct18 {enq_type : ((((Bit#(4))'(4'h0))[3:2]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : (((((Bit#(4))'(4'h0))[3:2])
        == ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : ((Bit#(4))'(4'h0))[1:0], enq_msg : Struct1 {id :
        (Bit#(6))'(6'ha), type_ : (Bool)'(False), addr : (x_17).addr, value :
        unpack(0)}});
        let x_23 <- makeEnq_parentChildren_0_0(x_22);
    endrule
    
    rule rule_exec__0_0__1_4_0_0_3;
        let x_0 <- deq_fifoL2E__0_0();
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
        let x_10 <- getMSHR__0_0(x_4);
        let x_11 <- getMSHRRq__0_0(x_4);
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
            let x_19 <- cache___0_0__valueRsLineRq(unpack(0));
            x_20 = x_19;
        end
        let x_21 <- registerDL__0_0(Struct20 {r_id : x_4, r_dl_rss_from :
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
        let x_23 <- makeEnq_parentChildren_0_0(x_22);
    endrule
    
    rule rule_exec__0_0__1_5_0_0_3;
        let x_0 <- deq_fifoL2E__0_0();
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
        let x_10 <- getMSHR__0_0(x_4);
        let x_11 <- getMSHRRq__0_0(x_4);
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
            let x_19 <- cache___0_0__valueRsLineRq(unpack(0));
            x_20 = x_19;
        end
        let x_21 <- registerDL__0_0(Struct20 {r_id : x_4, r_dl_rss_from :
        ((x_16).dir_sharers) & (~(((Bit#(4))'(4'h1)) << ((Bit#(2))'(2'h3)))),
        r_dl_rsb : (Bool)'(True), r_dl_rsbTo : (Bit#(4))'(4'hb)});
        let x_22 <- broadcast_parentChildren_0_0(Struct21 {cs_inds :
        ((x_16).dir_sharers) & (~(((Bit#(4))'(4'h1)) << ((Bit#(2))'(2'h3)))),
        cs_msg : Struct1 {id : (Bit#(6))'(6'hc), type_ : (Bool)'(False), addr
        : (x_17).addr, value : unpack(0)}});
    endrule
    
    rule rule_exec__0_0__2_5_0_0_3;
        let x_0 <- deq_fifoL2E__0_0();
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
        let x_10 <- getMSHR__0_0(x_4);
        let x_11 <- getMSHRRq__0_0(x_4);
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
            let x_19 <- cache___0_0__valueRsLineRq(unpack(0));
            x_20 = x_19;
        end
        Struct18 x_21 = (Struct18 {enq_type : ((((Bit#(4))'(4'hb))[3:2]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : (((((Bit#(4))'(4'hb))[3:2])
        == ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : ((Bit#(4))'(4'hb))[1:0], enq_msg : Struct1 {id :
        (Bit#(6))'(6'h16), type_ : (Bool)'(True), addr : (x_17).addr, value :
        unpack(0)}});
        let x_22 <- makeEnq_parentChildren_0_0(x_21);
        let x_23 <- releaseMSHR__0_0(x_4);
    endrule
    
    rule rule_exec__0_0__2_6_0_0_0_0_3;
        let x_0 <- deq_fifoL2E__0_0();
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
        let x_10 <- getMSHR__0_0(x_4);
        let x_11 <- getMSHRRq__0_0(x_4);
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
            let x_20 <- victims___0_0__setVictim(Struct17 {victim_idx :
            (x_8).data, victim_info : (x_19).info, victim_value :
            ((x_19).value_write ? ((x_19).value) : (x_9))});
            x_22 = x_9;
        end else begin
            let x_21 <- cache___0_0__valueRsLineRq(x_19);
            x_22 = x_21;
        end
        Struct18 x_23 = (Struct18 {enq_type : ((((Bit#(4))'(4'hb))[3:2]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : (((((Bit#(4))'(4'hb))[3:2])
        == ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : ((Bit#(4))'(4'hb))[1:0], enq_msg : Struct1 {id :
        (Bit#(6))'(6'h16), type_ : (Bool)'(True), addr : (x_17).addr, value :
        unpack(0)}});
        let x_24 <- makeEnq_parentChildren_0_0(x_23);
        let x_25 <- releaseMSHR__0_0(x_4);
    endrule
    
    rule rule_exec__0_0__2_6_0_1_0_0_3;
        let x_0 <- deq_fifoL2E__0_0();
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
        let x_10 <- getMSHR__0_0(x_4);
        let x_11 <- getMSHRRq__0_0(x_4);
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
            let x_21 <- victims___0_0__setVictim(Struct17 {victim_idx :
            (x_8).data, victim_info : (x_20).info, victim_value :
            ((x_20).value_write ? ((x_20).value) : (x_9))});
            x_23 = x_9;
        end else begin
            let x_22 <- cache___0_0__valueRsLineRq(x_20);
            x_23 = x_22;
        end
        Struct18 x_24 = (Struct18 {enq_type : ((((Bit#(4))'(4'hb))[3:2]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : (((((Bit#(4))'(4'hb))[3:2])
        == ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : ((Bit#(4))'(4'hb))[1:0], enq_msg : Struct1 {id :
        (Bit#(6))'(6'h16), type_ : (Bool)'(True), addr : (x_17).addr, value :
        unpack(0)}});
        let x_25 <- makeEnq_parentChildren_0_0(x_24);
        let x_26 <- releaseMSHR__0_0(x_4);
    endrule
    
    rule rule_exec__0_0__2_6_1_0_0_3;
        let x_0 <- deq_fifoL2E__0_0();
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
        let x_10 <- getMSHR__0_0(x_4);
        let x_11 <- getMSHRRq__0_0(x_4);
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
            let x_20 <- victims___0_0__setVictim(Struct17 {victim_idx :
            (x_8).data, victim_info : (x_19).info, victim_value :
            ((x_19).value_write ? ((x_19).value) : (x_9))});
            x_22 = x_9;
        end else begin
            let x_21 <- cache___0_0__valueRsLineRq(x_19);
            x_22 = x_21;
        end
        Struct18 x_23 = (Struct18 {enq_type : ((((Bit#(4))'(4'hb))[3:2]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : (((((Bit#(4))'(4'hb))[3:2])
        == ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : ((Bit#(4))'(4'hb))[1:0], enq_msg : Struct1 {id :
        (Bit#(6))'(6'h16), type_ : (Bool)'(True), addr : (x_17).addr, value :
        unpack(0)}});
        let x_24 <- makeEnq_parentChildren_0_0(x_23);
        let x_25 <- releaseMSHR__0_0(x_4);
    endrule
    
    rule rule_exec__0_0__2_7_0_0_3;
        let x_0 <- deq_fifoL2E__0_0();
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
        let x_10 <- getMSHR__0_0(x_4);
        let x_11 <- getMSHRRq__0_0(x_4);
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
            let x_21 <- victims___0_0__setVictim(Struct17 {victim_idx :
            (x_8).data, victim_info : (x_20).info, victim_value :
            ((x_20).value_write ? ((x_20).value) : (x_9))});
            x_23 = x_9;
        end else begin
            let x_22 <- cache___0_0__valueRsLineRq(x_20);
            x_23 = x_22;
        end
        Struct18 x_24 = (Struct18 {enq_type : ((((Bit#(4))'(4'hb))[3:2]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : (((((Bit#(4))'(4'hb))[3:2])
        == ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : ((Bit#(4))'(4'hb))[1:0], enq_msg : Struct1 {id :
        (Bit#(6))'(6'h16), type_ : (Bool)'(True), addr : (x_17).addr, value :
        unpack(0)}});
        let x_25 <- makeEnq_parentChildren_0_0(x_24);
        let x_26 <- releaseMSHR__0_0(x_4);
    endrule
    
    rule rule_exec__0_0__2_8_0_0_3;
        let x_0 <- deq_fifoL2E__0_0();
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
        let x_10 <- getMSHR__0_0(x_4);
        let x_11 <- getMSHRRq__0_0(x_4);
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
            let x_19 <- cache___0_0__valueRsLineRq(unpack(0));
            x_20 = x_19;
        end
        Struct18 x_21 = (Struct18 {enq_type : ((((Bit#(4))'(4'hb))[3:2]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : (((((Bit#(4))'(4'hb))[3:2])
        == ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : ((Bit#(4))'(4'hb))[1:0], enq_msg : Struct1 {id :
        (Bit#(6))'(6'h16), type_ : (Bool)'(True), addr : (x_17).addr, value :
        unpack(0)}});
        let x_22 <- makeEnq_parentChildren_0_0(x_21);
        let x_23 <- releaseMSHR__0_0(x_4);
    endrule
    
    rule rule_exec__0_0__2_9_0_0_0_3;
        let x_0 <- deq_fifoL2E__0_0();
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
        let x_10 <- getMSHR__0_0(x_4);
        let x_11 <- getMSHRRq__0_0(x_4);
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
            let x_20 <- victims___0_0__setVictim(Struct17 {victim_idx :
            (x_8).data, victim_info : (x_19).info, victim_value :
            ((x_19).value_write ? ((x_19).value) : (x_9))});
            x_22 = x_9;
        end else begin
            let x_21 <- cache___0_0__valueRsLineRq(x_19);
            x_22 = x_21;
        end
        Struct18 x_23 = (Struct18 {enq_type : ((((Bit#(4))'(4'hb))[3:2]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : (((((Bit#(4))'(4'hb))[3:2])
        == ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : ((Bit#(4))'(4'hb))[1:0], enq_msg : Struct1 {id :
        (Bit#(6))'(6'h16), type_ : (Bool)'(True), addr : (x_17).addr, value :
        unpack(0)}});
        let x_24 <- makeEnq_parentChildren_0_0(x_23);
        let x_25 <- releaseMSHR__0_0(x_4);
    endrule
    
    rule rule_exec__0_0__2_9_1_0_0_3;
        let x_0 <- deq_fifoL2E__0_0();
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
        let x_10 <- getMSHR__0_0(x_4);
        let x_11 <- getMSHRRq__0_0(x_4);
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
            let x_20 <- victims___0_0__setVictim(Struct17 {victim_idx :
            (x_8).data, victim_info : (x_19).info, victim_value :
            ((x_19).value_write ? ((x_19).value) : (x_9))});
            x_22 = x_9;
        end else begin
            let x_21 <- cache___0_0__valueRsLineRq(x_19);
            x_22 = x_21;
        end
        Struct18 x_23 = (Struct18 {enq_type : ((((Bit#(4))'(4'hb))[3:2]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : (((((Bit#(4))'(4'hb))[3:2])
        == ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : ((Bit#(4))'(4'hb))[1:0], enq_msg : Struct1 {id :
        (Bit#(6))'(6'h16), type_ : (Bool)'(True), addr : (x_17).addr, value :
        unpack(0)}});
        let x_24 <- makeEnq_parentChildren_0_0(x_23);
        let x_25 <- releaseMSHR__0_0(x_4);
    endrule
    
    rule rule_exec__0_0__2_10_0_0_3;
        let x_0 <- deq_fifoL2E__0_0();
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
        let x_10 <- getMSHR__0_0(x_4);
        let x_11 <- getMSHRRq__0_0(x_4);
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
            let x_21 <- victims___0_0__setVictim(Struct17 {victim_idx :
            (x_8).data, victim_info : (x_20).info, victim_value :
            ((x_20).value_write ? ((x_20).value) : (x_9))});
            x_23 = x_9;
        end else begin
            let x_22 <- cache___0_0__valueRsLineRq(x_20);
            x_23 = x_22;
        end
        Struct18 x_24 = (Struct18 {enq_type : ((((Bit#(4))'(4'hb))[3:2]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : (((((Bit#(4))'(4'hb))[3:2])
        == ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : ((Bit#(4))'(4'hb))[1:0], enq_msg : Struct1 {id :
        (Bit#(6))'(6'h16), type_ : (Bool)'(True), addr : (x_17).addr, value :
        unpack(0)}});
        let x_25 <- makeEnq_parentChildren_0_0(x_24);
        let x_26 <- releaseMSHR__0_0(x_4);
    endrule
    
    rule rule_exec__0_0__2_11_0_0_3;
        let x_0 <- deq_fifoL2E__0_0();
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
        let x_10 <- getMSHR__0_0(x_4);
        let x_11 <- getMSHRRq__0_0(x_4);
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
            let x_23 <- victims___0_0__setVictim(Struct17 {victim_idx :
            (x_8).data, victim_info : (x_22).info, victim_value :
            ((x_22).value_write ? ((x_22).value) : (x_9))});
            x_25 = x_9;
        end else begin
            let x_24 <- cache___0_0__valueRsLineRq(x_22);
            x_25 = x_24;
        end
        Struct18 x_26 = (Struct18 {enq_type : ((((Bit#(4))'(4'hb))[3:2]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : (((((Bit#(4))'(4'hb))[3:2])
        == ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : ((Bit#(4))'(4'hb))[1:0], enq_msg : Struct1 {id :
        (Bit#(6))'(6'h16), type_ : (Bool)'(True), addr : (x_17).addr, value :
        unpack(0)}});
        let x_27 <- makeEnq_parentChildren_0_0(x_26);
        let x_28 <- releaseMSHR__0_0(x_4);
    endrule
    
    rule rule_exec__0_0__0_2_0;
        let x_0 <- deq_fifoL2E__0_0();
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
        let x_10 <- getMSHR__0_0(x_4);
        let x_11 <- getMSHRRq__0_0(x_4);
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
            let x_25 <- victims___0_0__setVictim(Struct17 {victim_idx :
            (x_8).data, victim_info : (x_24).info, victim_value :
            ((x_24).value_write ? ((x_24).value) : (x_9))});
            x_27 = x_9;
        end else begin
            let x_26 <- cache___0_0__valueRsLineRq(x_24);
            x_27 = x_26;
        end
        let x_28 <- releaseMSHR__0_0(x_4);
        Struct18 x_29 = (Struct18 {enq_type : (((x_19)[3:2]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : ((((x_19)[3:2]) ==
        ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : (x_19)[1:0], enq_msg : Struct1 {id : (Bit#(6))'(6'h3),
        type_ : (Bool)'(True), addr : (x_17).addr, value :
        (x_17).value}});
        let x_30 <- makeEnq_parentChildren_0_0(x_29);
    endrule
    
    rule rule_exec__0_0__0_2_1;
        let x_0 <- deq_fifoL2E__0_0();
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
        let x_10 <- getMSHR__0_0(x_4);
        let x_11 <- getMSHRRq__0_0(x_4);
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
            let x_25 <- victims___0_0__setVictim(Struct17 {victim_idx :
            (x_8).data, victim_info : (x_24).info, victim_value :
            ((x_24).value_write ? ((x_24).value) : (x_9))});
            x_27 = x_9;
        end else begin
            let x_26 <- cache___0_0__valueRsLineRq(x_24);
            x_27 = x_26;
        end
        let x_28 <- releaseMSHR__0_0(x_4);
        Struct18 x_29 = (Struct18 {enq_type : (((x_19)[3:2]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : ((((x_19)[3:2]) ==
        ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : (x_19)[1:0], enq_msg : Struct1 {id : (Bit#(6))'(6'h4),
        type_ : (Bool)'(True), addr : (x_17).addr, value :
        (x_17).value}});
        let x_30 <- makeEnq_parentChildren_0_0(x_29);
    endrule
    
    rule rule_exec__0_0__0_4_1;
        let x_0 <- deq_fifoL2E__0_0();
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
        let x_10 <- getMSHR__0_0(x_4);
        let x_11 <- getMSHRRq__0_0(x_4);
        let x_12 <- getMSHRFirstRs__0_0(x_4);
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
            let x_25 <- victims___0_0__setVictim(Struct17 {victim_idx :
            (x_8).data, victim_info : (x_24).info, victim_value :
            ((x_24).value_write ? ((x_24).value) : (x_9))});
            x_27 = x_9;
        end else begin
            let x_26 <- cache___0_0__valueRsLineRq(x_24);
            x_27 = x_26;
        end
        let x_28 <- releaseMSHR__0_0(x_4);
        Struct18 x_29 = (Struct18 {enq_type : (((x_19)[3:2]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : ((((x_19)[3:2]) ==
        ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : (x_19)[1:0], enq_msg : Struct1 {id : (Bit#(6))'(6'h3),
        type_ : (Bool)'(True), addr : (x_18).addr, value :
        ((x_17).msg).value}});
        let x_30 <- makeEnq_parentChildren_0_0(x_29);
    endrule
    
    rule rule_exec__0_0__0_5;
        let x_0 <- deq_fifoL2E__0_0();
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
        let x_10 <- getMSHR__0_0(x_4);
        let x_11 <- getMSHRRq__0_0(x_4);
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
            let x_21 <- victims___0_0__setVictim(Struct17 {victim_idx :
            (x_8).data, victim_info : (x_20).info, victim_value :
            ((x_20).value_write ? ((x_20).value) : (x_9))});
            x_23 = x_9;
        end else begin
            let x_22 <- cache___0_0__valueRsLineRq(x_20);
            x_23 = x_22;
        end
        Struct18 x_24 = (Struct18 {enq_type : ((((Bit#(4))'(4'h4))[3:2]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : (((((Bit#(4))'(4'h4))[3:2])
        == ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : ((Bit#(4))'(4'h4))[1:0], enq_msg : Struct1 {id :
        (Bit#(6))'(6'h6), type_ : (Bool)'(True), addr : (x_17).addr, value :
        x_23}});
        let x_25 <- makeEnq_parentChildren_0_0(x_24);
        let x_26 <- releaseMSHR__0_0(x_4);
    endrule
    
    rule rule_exec__0_0__0_6;
        let x_0 <- deq_fifoL2E__0_0();
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
        let x_10 <- getMSHR__0_0(x_4);
        let x_11 <- getMSHRRq__0_0(x_4);
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
            let x_19 <- cache___0_0__valueRsLineRq(unpack(0));
            x_20 = x_19;
        end
        let x_21 <- registerDL__0_0(Struct20 {r_id : x_4, r_dl_rss_from :
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
        let x_23 <- makeEnq_parentChildren_0_0(x_22);
    endrule
    
    rule rule_exec__0_0__0_7_1;
        let x_0 <- deq_fifoL2E__0_0();
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
        let x_10 <- getMSHR__0_0(x_4);
        let x_11 <- getMSHRRq__0_0(x_4);
        let x_12 <- getMSHRFirstRs__0_0(x_4);
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
            let x_25 <- victims___0_0__setVictim(Struct17 {victim_idx :
            (x_8).data, victim_info : (x_24).info, victim_value :
            ((x_24).value_write ? ((x_24).value) : (x_9))});
            x_27 = x_9;
        end else begin
            let x_26 <- cache___0_0__valueRsLineRq(x_24);
            x_27 = x_26;
        end
        let x_28 <- releaseMSHR__0_0(x_4);
        Struct18 x_29 = (Struct18 {enq_type : (((x_19)[3:2]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : ((((x_19)[3:2]) ==
        ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : (x_19)[1:0], enq_msg : Struct1 {id : (Bit#(6))'(6'h6),
        type_ : (Bool)'(True), addr : (x_18).addr, value :
        ((x_17).msg).value}});
        let x_30 <- makeEnq_parentChildren_0_0(x_29);
    endrule
    
    rule rule_exec__0_0__1_2;
        let x_0 <- deq_fifoL2E__0_0();
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
        let x_10 <- getMSHR__0_0(x_4);
        let x_11 <- getMSHRRq__0_0(x_4);
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
            let x_24 <- victims___0_0__setVictim(Struct17 {victim_idx :
            (x_8).data, victim_info : (x_23).info, victim_value :
            ((x_23).value_write ? ((x_23).value) : (x_9))});
            x_26 = x_9;
        end else begin
            let x_25 <- cache___0_0__valueRsLineRq(x_23);
            x_26 = x_25;
        end
        let x_27 <- releaseMSHR__0_0(x_4);
        Struct18 x_28 = (Struct18 {enq_type : (((x_19)[3:2]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : ((((x_19)[3:2]) ==
        ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : (x_19)[1:0], enq_msg : Struct1 {id : (Bit#(6))'(6'hb),
        type_ : (Bool)'(True), addr : (x_17).addr, value : unpack(0)}});
        let x_29 <- makeEnq_parentChildren_0_0(x_28);
    endrule
    
    rule rule_exec__0_0__1_3;
        let x_0 <- deq_fifoL2E__0_0();
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
        let x_10 <- getMSHR__0_0(x_4);
        let x_11 <- getMSHRRq__0_0(x_4);
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
            let x_21 <- victims___0_0__setVictim(Struct17 {victim_idx :
            (x_8).data, victim_info : (x_20).info, victim_value :
            ((x_20).value_write ? ((x_20).value) : (x_9))});
            x_23 = x_9;
        end else begin
            let x_22 <- cache___0_0__valueRsLineRq(x_20);
            x_23 = x_22;
        end
        let x_24 <- transferUpDown__0_0(Struct23 {r_id : x_4, r_dl_rss_from :
        ((x_16).dir_sharers) & (~(((Bit#(4))'(4'h1)) << ((x_18)[1:0])))});
        let x_25 <- broadcast_parentChildren_0_0(Struct21 {cs_inds :
        ((x_16).dir_sharers) & (~(((Bit#(4))'(4'h1)) << ((x_18)[1:0]))),
        cs_msg : Struct1 {id : (Bit#(6))'(6'hc), type_ : (Bool)'(False), addr
        : (x_17).addr, value : unpack(0)}});
    endrule
    
    rule rule_exec__0_0__1_6_1;
        let x_0 <- deq_fifoL2E__0_0();
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
        let x_10 <- getMSHR__0_0(x_4);
        let x_11 <- getMSHRRq__0_0(x_4);
        let x_12 <- getMSHRFirstRs__0_0(x_4);
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
            let x_23 <- victims___0_0__setVictim(Struct17 {victim_idx :
            (x_8).data, victim_info : (x_22).info, victim_value :
            ((x_22).value_write ? ((x_22).value) : (x_9))});
            x_25 = x_9;
        end else begin
            let x_24 <- cache___0_0__valueRsLineRq(x_22);
            x_25 = x_24;
        end
        let x_26 <- releaseMSHR__0_0(x_4);
        Struct18 x_27 = (Struct18 {enq_type : (((x_18)[3:2]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : ((((x_18)[3:2]) ==
        ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : (x_18)[1:0], enq_msg : Struct1 {id : (Bit#(6))'(6'hb),
        type_ : (Bool)'(True), addr : (x_17).addr, value : unpack(0)}});
        let x_28 <- makeEnq_parentChildren_0_0(x_27);
    endrule
    
    rule rule_exec__0_0__1_7_0;
        let x_0 <- deq_fifoL2E__0_0();
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
        let x_10 <- getMSHR__0_0(x_4);
        let x_11 <- getMSHRRq__0_0(x_4);
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
            let x_21 <- victims___0_0__setVictim(Struct17 {victim_idx :
            (x_8).data, victim_info : (x_20).info, victim_value :
            ((x_20).value_write ? ((x_20).value) : (x_9))});
            x_23 = x_9;
        end else begin
            let x_22 <- cache___0_0__valueRsLineRq(x_20);
            x_23 = x_22;
        end
        Struct18 x_24 = (Struct18 {enq_type : ((((Bit#(4))'(4'h4))[3:2]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : (((((Bit#(4))'(4'h4))[3:2])
        == ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : ((Bit#(4))'(4'h4))[1:0], enq_msg : Struct1 {id :
        (Bit#(6))'(6'hd), type_ : (Bool)'(True), addr : (x_17).addr, value :
        unpack(0)}});
        let x_25 <- makeEnq_parentChildren_0_0(x_24);
        let x_26 <- releaseMSHR__0_0(x_4);
    endrule
    
    rule rule_exec__0_0__1_7_1;
        let x_0 <- deq_fifoL2E__0_0();
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
        let x_10 <- getMSHR__0_0(x_4);
        let x_11 <- getMSHRRq__0_0(x_4);
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
            let x_21 <- victims___0_0__setVictim(Struct17 {victim_idx :
            (x_8).data, victim_info : (x_20).info, victim_value :
            ((x_20).value_write ? ((x_20).value) : (x_9))});
            x_23 = x_9;
        end else begin
            let x_22 <- cache___0_0__valueRsLineRq(x_20);
            x_23 = x_22;
        end
        Struct18 x_24 = (Struct18 {enq_type : ((((Bit#(4))'(4'h4))[3:2]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : (((((Bit#(4))'(4'h4))[3:2])
        == ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : ((Bit#(4))'(4'h4))[1:0], enq_msg : Struct1 {id :
        (Bit#(6))'(6'hf), type_ : (Bool)'(True), addr : (x_17).addr, value :
        unpack(0)}});
        let x_25 <- makeEnq_parentChildren_0_0(x_24);
        let x_26 <- releaseMSHR__0_0(x_4);
    endrule
    
    rule rule_exec__0_0__1_9_0;
        let x_0 <- deq_fifoL2E__0_0();
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
        let x_10 <- getMSHR__0_0(x_4);
        let x_11 <- getMSHRRq__0_0(x_4);
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
            let x_19 <- cache___0_0__valueRsLineRq(unpack(0));
            x_20 = x_19;
        end
        let x_21 <- registerDL__0_0(Struct20 {r_id : x_4, r_dl_rss_from :
        (x_16).dir_sharers, r_dl_rsb : (Bool)'(True), r_dl_rsbTo :
        (Bit#(4))'(4'h4)});
        let x_22 <- broadcast_parentChildren_0_0(Struct21 {cs_inds :
        (x_16).dir_sharers, cs_msg : Struct1 {id : (Bit#(6))'(6'hc), type_ :
        (Bool)'(False), addr : (x_17).addr, value : unpack(0)}});
    endrule
    
    rule rule_exec__0_0__1_9_1;
        let x_0 <- deq_fifoL2E__0_0();
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
        let x_10 <- getMSHR__0_0(x_4);
        let x_11 <- getMSHRRq__0_0(x_4);
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
            let x_19 <- cache___0_0__valueRsLineRq(unpack(0));
            x_20 = x_19;
        end
        let x_21 <- registerDL__0_0(Struct20 {r_id : x_4, r_dl_rss_from :
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
        let x_23 <- makeEnq_parentChildren_0_0(x_22);
    endrule
    
    rule rule_exec__0_0__1_9_2;
        let x_0 <- deq_fifoL2E__0_0();
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
        let x_10 <- getMSHR__0_0(x_4);
        let x_11 <- getMSHRRq__0_0(x_4);
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
            let x_19 <- cache___0_0__valueRsLineRq(unpack(0));
            x_20 = x_19;
        end
        let x_21 <- registerDL__0_0(Struct20 {r_id : x_4, r_dl_rss_from :
        (x_16).dir_sharers, r_dl_rsb : (Bool)'(True), r_dl_rsbTo :
        (Bit#(4))'(4'h4)});
        let x_22 <- broadcast_parentChildren_0_0(Struct21 {cs_inds :
        (x_16).dir_sharers, cs_msg : Struct1 {id : (Bit#(6))'(6'hc), type_ :
        (Bool)'(False), addr : (x_17).addr, value : unpack(0)}});
    endrule
    
    rule rule_exec__0_0__1_10_1_0;
        let x_0 <- deq_fifoL2E__0_0();
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
        let x_10 <- getMSHR__0_0(x_4);
        let x_11 <- getMSHRRq__0_0(x_4);
        let x_12 <- getMSHRFirstRs__0_0(x_4);
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
            let x_23 <- victims___0_0__setVictim(Struct17 {victim_idx :
            (x_8).data, victim_info : (x_22).info, victim_value :
            ((x_22).value_write ? ((x_22).value) : (x_9))});
            x_25 = x_9;
        end else begin
            let x_24 <- cache___0_0__valueRsLineRq(x_22);
            x_25 = x_24;
        end
        let x_26 <- releaseMSHR__0_0(x_4);
        Struct18 x_27 = (Struct18 {enq_type : (((x_18)[3:2]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : ((((x_18)[3:2]) ==
        ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : (x_18)[1:0], enq_msg : Struct1 {id : (Bit#(6))'(6'hd),
        type_ : (Bool)'(True), addr : (x_17).addr, value : unpack(0)}});
        let x_28 <- makeEnq_parentChildren_0_0(x_27);
    endrule
    
    rule rule_exec__0_0__1_10_1_1;
        let x_0 <- deq_fifoL2E__0_0();
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
        let x_10 <- getMSHR__0_0(x_4);
        let x_11 <- getMSHRRq__0_0(x_4);
        let x_12 <- getMSHRFirstRs__0_0(x_4);
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
            let x_23 <- victims___0_0__setVictim(Struct17 {victim_idx :
            (x_8).data, victim_info : (x_22).info, victim_value :
            ((x_22).value_write ? ((x_22).value) : (x_9))});
            x_25 = x_9;
        end else begin
            let x_24 <- cache___0_0__valueRsLineRq(x_22);
            x_25 = x_24;
        end
        let x_26 <- releaseMSHR__0_0(x_4);
        Struct18 x_27 = (Struct18 {enq_type : (((x_18)[3:2]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : ((((x_18)[3:2]) ==
        ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : (x_18)[1:0], enq_msg : Struct1 {id : (Bit#(6))'(6'hf),
        type_ : (Bool)'(True), addr : (x_17).addr, value : unpack(0)}});
        let x_28 <- makeEnq_parentChildren_0_0(x_27);
    endrule
    
    rule rule_exec__0_0__2_0;
        let x_0 <- victims___0_0__getFirstVictim();
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
        let x_13 <- makeEnq_parentChildren_0_0(x_12);
        let x_14 <- setULImm__0_0(x_4);
        let x_15 <- victims___0_0__setVictimRq(x_1);
    endrule
    
    rule rule_exec__0_0__2_1;
        let x_0 <- victims___0_0__getFirstVictim();
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
        let x_13 <- makeEnq_parentChildren_0_0(x_12);
        let x_14 <- setULImm__0_0(x_4);
        let x_15 <- victims___0_0__setVictimRq(x_1);
    endrule
    
    rule rule_exec__0_0__2_3;
        let x_0 <- victims___0_0__getFirstVictim();
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
        let x_12 <- canImm__0_0(x_1);
        let x_13 <- victims___0_0__releaseVictim(x_1);
    endrule
    
    // No methods in this module
endmodule

interface Module134;
    
endinterface

module mkModule134#(function Action victims___0_0_0__setVictimRq(Bit#(64) _),
    function Action setULImm__0_0_0(Struct1 _),
    function ActionValue#(Struct13) victims___0_0_0__getFirstVictim(),
    function Action victims___0_0_0__setVictim(Struct44 _),
    function Action registerUL__0_0_0(Struct43 _),
    function Action makeEnq_parentChildren_0_0_0(Struct18 _),
    function ActionValue#(Vector#(4, Bit#(64))) cache___0_0_0__valueRsLineRq(Struct42 _),
    function ActionValue#(Struct1) getMSHRRq__0_0_0(Bit#(2) _),
    function ActionValue#(Struct14) getMSHR__0_0_0(Bit#(2) _),
    function ActionValue#(Struct41) deq_fifoL2E__0_0_0(),
    function ActionValue#(Struct13) victims___0_0_0__getVictim(Bit#(1) _),
    function Action enq_fifoL2E__0_0_0(Struct41 _),
    function ActionValue#(Struct39) cache___0_0_0__infoRsValueRq(Bit#(64) _),
    function ActionValue#(Struct38) deq_fifoI2L__0_0_0(),
    function Action enq_fifoI2L__0_0_0(Struct38 _),
    function Action cache___0_0_0__infoRq(Bit#(64) _),
    function ActionValue#(Struct38) deq_fifoN2I__0_0_0(),
    function ActionValue#(Struct36) getCRqSlot__0_0_0(Struct35 _),
    function ActionValue#(Bool) victims___0_0_0__hasVictim(),
    function ActionValue#(Struct2) deq_fifoCRqInput__0_0_0(),
    function Action releaseMSHR__0_0_0(Bit#(2) _),
    function Action victims___0_0_0__releaseVictim(Bit#(64) _),
    function ActionValue#(Struct35) getWait__0_0_0(),
    function Action startRelease__0_0_0(Bit#(2) _),
    function ActionValue#(Bit#(2)) getULReady__0_0_0(Bit#(64) _),
    function Action enq_fifoN2I__0_0_0(Struct38 _),
    function ActionValue#(Struct37) victims___0_0_0__findVictim(Bit#(64) _),
    function ActionValue#(Struct36) getPRqSlot__0_0_0(Struct35 _),
    function ActionValue#(Struct2) deq_fifoPInput__0_0_0())
    (Module134);
    
    rule rule_in_prq__0_0_0;
        let x_0 <- deq_fifoPInput__0_0_0();
        Bit#(4) x_1 = ((x_0).in_msg_from);
        when ((x_1) == ({((Bit#(2))'(2'h2)),((Bit#(2))'(2'h0))}),
        noAction);
        Struct1 x_2 = ((x_0).in_msg);
        when (! ((x_2).type_), noAction);
        let x_3 <- getPRqSlot__0_0_0(Struct35 {r_id : unpack(0), r_msg : x_2,
        r_msg_from : (x_0).in_msg_from});
        when ((x_3).s_has_slot,
        noAction);
        if (! ((x_3).s_conflict)) begin
            let x_4 <- victims___0_0_0__findVictim((x_2).addr);
            Struct38 x_5 = (Struct38 {ir_is_rs_rel : (Bool)'(False), ir_msg :
            (x_0).in_msg, ir_msg_from : x_1, ir_mshr_id : (x_3).s_id,
            ir_by_victim : x_4});
            let x_6 <- enq_fifoN2I__0_0_0(x_5);
        end else begin
            
        end
    endrule
    
    rule rule_in_prs__0_0_0;
        let x_0 <- deq_fifoPInput__0_0_0();
        Bit#(4) x_1 = ((x_0).in_msg_from);
        when ((x_1) == ({((Bit#(2))'(2'h2)),((Bit#(2))'(2'h0))}),
        noAction);
        Struct1 x_2 = ((x_0).in_msg);
        when (((x_2).type_) && (! (((x_2).id) == ((Bit#(6))'(6'h16)))),
        noAction);
        let x_3 <- getULReady__0_0_0((x_2).addr);
        let x_4 <- startRelease__0_0_0(x_3);
        let x_5 <- victims___0_0_0__findVictim((x_2).addr);
        Struct38 x_6 = (Struct38 {ir_is_rs_rel : (Bool)'(False), ir_msg :
        (x_0).in_msg, ir_msg_from : x_1, ir_mshr_id : x_3, ir_by_victim :
        x_5});
        let x_7 <- enq_fifoN2I__0_0_0(x_6);
    endrule
    
    rule rule_in_retry__0_0_0;
        let x_0 <- getWait__0_0_0();
        Struct1 x_1 = ((x_0).r_msg);
        let x_2 <- victims___0_0_0__findVictim((x_1).addr);
        Struct38 x_3 = (Struct38 {ir_is_rs_rel : (Bool)'(False), ir_msg :
        x_1, ir_msg_from : (x_0).r_msg_from, ir_mshr_id : (x_0).r_id,
        ir_by_victim : x_2});
        let x_4 <- enq_fifoN2I__0_0_0(x_3);
    endrule
    
    rule rule_in_invrs__0_0_0;
        let x_0 <- deq_fifoPInput__0_0_0();
        Bit#(4) x_1 = ((x_0).in_msg_from);
        when ((x_1) == ({((Bit#(2))'(2'h2)),((Bit#(2))'(2'h0))}),
        noAction);
        Struct1 x_2 = ((x_0).in_msg);
        when (((x_2).type_) && (((x_2).id) == ((Bit#(6))'(6'h16))),
        noAction);
        let x_3 <- getULReady__0_0_0((x_2).addr);
        let x_4 <- victims___0_0_0__releaseVictim((x_2).addr);
        let x_5 <- releaseMSHR__0_0_0(x_3);
    endrule
    
    rule rule_in_crq__0_0_0;
        let x_0 <- deq_fifoCRqInput__0_0_0();
        Bit#(4) x_1 = ((x_0).in_msg_from);
        when (((x_1)[3:2]) == ((Bit#(2))'(2'h0)), noAction);
        Struct1 x_2 = ((x_0).in_msg);
        when (! ((x_2).type_), noAction);
        let x_3 <- victims___0_0_0__hasVictim();
        when (! (x_3), noAction);
        let x_4 <- getCRqSlot__0_0_0(Struct35 {r_id : unpack(0), r_msg : x_2,
        r_msg_from : x_1});
        when ((x_4).s_has_slot,
        noAction);
        if (! ((x_4).s_conflict)) begin
            let x_5 <- victims___0_0_0__findVictim((x_2).addr);
            Struct38 x_6 = (Struct38 {ir_is_rs_rel : (Bool)'(False), ir_msg :
            (x_0).in_msg, ir_msg_from : x_1, ir_mshr_id : (x_4).s_id,
            ir_by_victim : x_5});
            let x_7 <- enq_fifoN2I__0_0_0(x_6);
        end else begin
            
        end
    endrule
    
    rule rule_ir_cache__0_0_0;
        let x_0 <- deq_fifoN2I__0_0_0();
        when (! (((x_0).ir_by_victim).valid), noAction);
        Struct1 x_1 = ((x_0).ir_msg);
        let x_2 <- cache___0_0_0__infoRq((x_1).addr);
        let x_3 <- enq_fifoI2L__0_0_0(x_0);
    endrule
    
    rule rule_ir_victims__0_0_0;
        let x_0 <- deq_fifoN2I__0_0_0();
        when (((x_0).ir_by_victim).valid, noAction);
        let x_1 <- enq_fifoI2L__0_0_0(x_0);
    endrule
    
    rule rule_lr_cache__0_0_0;
        let x_0 <- deq_fifoI2L__0_0_0();
        when (! (((x_0).ir_by_victim).valid), noAction);
        let x_1 <- cache___0_0_0__infoRsValueRq(((x_0).ir_msg).addr);
        Struct41 x_2 = (Struct41 {lr_ir_pp : x_0, lr_ir : x_1, lr_value :
        unpack(0)});
        let x_3 <- enq_fifoL2E__0_0_0(x_2);
    endrule
    
    rule rule_lr_victims__0_0_0;
        let x_0 <- deq_fifoI2L__0_0_0();
        when (((x_0).ir_by_victim).valid, noAction);
        Bit#(1) x_1 = (((x_0).ir_by_victim).data);
        let x_2 <- victims___0_0_0__getVictim(x_1);
        Struct39 x_3 = (Struct39 {info_index : unpack(0), info_hit :
        unpack(0), info_way : unpack(0), edir_hit : unpack(0), edir_way :
        unpack(0), edir_slot : unpack(0), info : (x_2).victim_info,
        may_victim : unpack(0), reps : unpack(0)});
        Struct41 x_4 = (Struct41 {lr_ir_pp : x_0, lr_ir : x_3, lr_value :
        (x_2).victim_value});
        let x_5 <- enq_fifoL2E__0_0_0(x_4);
    endrule
    
    rule rule_exec__0_0_0__0_0;
        let x_0 <- deq_fifoL2E__0_0_0();
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
        let x_10 <- getMSHR__0_0_0(x_4);
        let x_11 <- getMSHRRq__0_0_0(x_4);
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
            let x_19 <- cache___0_0_0__valueRsLineRq(unpack(0));
            x_20 = x_19;
        end
        Struct18 x_21 = (Struct18 {enq_type : ((((Bit#(4))'(4'h8))[3:2]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : (((((Bit#(4))'(4'h8))[3:2])
        == ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : ((Bit#(4))'(4'h8))[1:0], enq_msg : Struct1 {id :
        (Bit#(6))'(6'h1), type_ : (Bool)'(True), addr : (x_17).addr, value :
        x_20}});
        let x_22 <- makeEnq_parentChildren_0_0_0(x_21);
        let x_23 <- releaseMSHR__0_0_0(x_4);
    endrule
    
    rule rule_exec__0_0_0__0_1;
        let x_0 <- deq_fifoL2E__0_0_0();
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
        let x_10 <- getMSHR__0_0_0(x_4);
        let x_11 <- getMSHRRq__0_0_0(x_4);
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
            let x_19 <- cache___0_0_0__valueRsLineRq(unpack(0));
            x_20 = x_19;
        end
        let x_21 <- registerUL__0_0_0(Struct43 {r_id : x_4, r_ul_rsb :
        (Bool)'(True), r_ul_rsbTo : ((Bit#(4))'(4'h8))[1:0]});
        Struct18 x_22 = (Struct18 {enq_type : ((((Bit#(4))'(4'h0))[3:2]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : (((((Bit#(4))'(4'h0))[3:2])
        == ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : ((Bit#(4))'(4'h0))[1:0], enq_msg : Struct1 {id :
        (Bit#(6))'(6'h2), type_ : (Bool)'(False), addr : (x_17).addr, value :
        unpack(0)}});
        let x_23 <- makeEnq_parentChildren_0_0_0(x_22);
    endrule
    
    rule rule_exec__0_0_0__0_2_0;
        let x_0 <- deq_fifoL2E__0_0_0();
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
        let x_10 <- getMSHR__0_0_0(x_4);
        let x_11 <- getMSHRRq__0_0_0(x_4);
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
            let x_23 <- victims___0_0_0__setVictim(Struct44 {victim_idx :
            (x_8).data, victim_info : (x_22).info, victim_value :
            ((x_22).value_write ? ((x_22).value) : (x_9))});
            x_25 = x_9;
        end else begin
            let x_24 <- cache___0_0_0__valueRsLineRq(x_22);
            x_25 = x_24;
        end
        let x_26 <- releaseMSHR__0_0_0(x_4);
        Struct18 x_27 = (Struct18 {enq_type : (((x_19)[3:2]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : ((((x_19)[3:2]) ==
        ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : (x_19)[1:0], enq_msg : Struct1 {id : (Bit#(6))'(6'h1),
        type_ : (Bool)'(True), addr : (x_17).addr, value :
        (x_17).value}});
        let x_28 <- makeEnq_parentChildren_0_0_0(x_27);
    endrule
    
    rule rule_exec__0_0_0__0_2_1;
        let x_0 <- deq_fifoL2E__0_0_0();
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
        let x_10 <- getMSHR__0_0_0(x_4);
        let x_11 <- getMSHRRq__0_0_0(x_4);
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
            let x_23 <- victims___0_0_0__setVictim(Struct44 {victim_idx :
            (x_8).data, victim_info : (x_22).info, victim_value :
            ((x_22).value_write ? ((x_22).value) : (x_9))});
            x_25 = x_9;
        end else begin
            let x_24 <- cache___0_0_0__valueRsLineRq(x_22);
            x_25 = x_24;
        end
        let x_26 <- releaseMSHR__0_0_0(x_4);
        Struct18 x_27 = (Struct18 {enq_type : (((x_19)[3:2]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : ((((x_19)[3:2]) ==
        ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : (x_19)[1:0], enq_msg : Struct1 {id : (Bit#(6))'(6'h1),
        type_ : (Bool)'(True), addr : (x_17).addr, value :
        (x_17).value}});
        let x_28 <- makeEnq_parentChildren_0_0_0(x_27);
    endrule
    
    rule rule_exec__0_0_0__0_3;
        let x_0 <- deq_fifoL2E__0_0_0();
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
        let x_10 <- getMSHR__0_0_0(x_4);
        let x_11 <- getMSHRRq__0_0_0(x_4);
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
            let x_21 <- victims___0_0_0__setVictim(Struct44 {victim_idx :
            (x_8).data, victim_info : (x_20).info, victim_value :
            ((x_20).value_write ? ((x_20).value) : (x_9))});
            x_23 = x_9;
        end else begin
            let x_22 <- cache___0_0_0__valueRsLineRq(x_20);
            x_23 = x_22;
        end
        Struct18 x_24 = (Struct18 {enq_type : ((((Bit#(4))'(4'h4))[3:2]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : (((((Bit#(4))'(4'h4))[3:2])
        == ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : ((Bit#(4))'(4'h4))[1:0], enq_msg : Struct1 {id :
        (Bit#(6))'(6'h6), type_ : (Bool)'(True), addr : (x_17).addr, value :
        x_23}});
        let x_25 <- makeEnq_parentChildren_0_0_0(x_24);
        let x_26 <- releaseMSHR__0_0_0(x_4);
    endrule
    
    rule rule_exec__0_0_0__1_0_0;
        let x_0 <- deq_fifoL2E__0_0_0();
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
        let x_10 <- getMSHR__0_0_0(x_4);
        let x_11 <- getMSHRRq__0_0_0(x_4);
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
            let x_22 <- victims___0_0_0__setVictim(Struct44 {victim_idx :
            (x_8).data, victim_info : (x_21).info, victim_value :
            ((x_21).value_write ? ((x_21).value) : (x_9))});
            x_24 = x_9;
        end else begin
            let x_23 <- cache___0_0_0__valueRsLineRq(x_21);
            x_24 = x_23;
        end
        Struct18 x_25 = (Struct18 {enq_type : ((((Bit#(4))'(4'h8))[3:2]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : (((((Bit#(4))'(4'h8))[3:2])
        == ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : ((Bit#(4))'(4'h8))[1:0], enq_msg : Struct1 {id :
        (Bit#(6))'(6'h9), type_ : (Bool)'(True), addr : (x_17).addr, value :
        unpack(0)}});
        let x_26 <- makeEnq_parentChildren_0_0_0(x_25);
        let x_27 <- releaseMSHR__0_0_0(x_4);
    endrule
    
    rule rule_exec__0_0_0__1_0_1;
        let x_0 <- deq_fifoL2E__0_0_0();
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
        let x_10 <- getMSHR__0_0_0(x_4);
        let x_11 <- getMSHRRq__0_0_0(x_4);
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
            let x_20 <- victims___0_0_0__setVictim(Struct44 {victim_idx :
            (x_8).data, victim_info : (x_19).info, victim_value :
            ((x_19).value_write ? ((x_19).value) : (x_9))});
            x_22 = x_9;
        end else begin
            let x_21 <- cache___0_0_0__valueRsLineRq(x_19);
            x_22 = x_21;
        end
        Struct18 x_23 = (Struct18 {enq_type : ((((Bit#(4))'(4'h8))[3:2]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : (((((Bit#(4))'(4'h8))[3:2])
        == ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : ((Bit#(4))'(4'h8))[1:0], enq_msg : Struct1 {id :
        (Bit#(6))'(6'h9), type_ : (Bool)'(True), addr : (x_17).addr, value :
        unpack(0)}});
        let x_24 <- makeEnq_parentChildren_0_0_0(x_23);
        let x_25 <- releaseMSHR__0_0_0(x_4);
    endrule
    
    rule rule_exec__0_0_0__1_1;
        let x_0 <- deq_fifoL2E__0_0_0();
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
        let x_10 <- getMSHR__0_0_0(x_4);
        let x_11 <- getMSHRRq__0_0_0(x_4);
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
            let x_19 <- cache___0_0_0__valueRsLineRq(unpack(0));
            x_20 = x_19;
        end
        let x_21 <- registerUL__0_0_0(Struct43 {r_id : x_4, r_ul_rsb :
        (Bool)'(True), r_ul_rsbTo : ((Bit#(4))'(4'h8))[1:0]});
        Struct18 x_22 = (Struct18 {enq_type : ((((Bit#(4))'(4'h0))[3:2]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : (((((Bit#(4))'(4'h0))[3:2])
        == ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : ((Bit#(4))'(4'h0))[1:0], enq_msg : Struct1 {id :
        (Bit#(6))'(6'ha), type_ : (Bool)'(False), addr : (x_17).addr, value :
        unpack(0)}});
        let x_23 <- makeEnq_parentChildren_0_0_0(x_22);
    endrule
    
    rule rule_exec__0_0_0__1_2;
        let x_0 <- deq_fifoL2E__0_0_0();
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
        let x_10 <- getMSHR__0_0_0(x_4);
        let x_11 <- getMSHRRq__0_0_0(x_4);
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
            let x_24 <- victims___0_0_0__setVictim(Struct44 {victim_idx :
            (x_8).data, victim_info : (x_23).info, victim_value :
            ((x_23).value_write ? ((x_23).value) : (x_9))});
            x_26 = x_9;
        end else begin
            let x_25 <- cache___0_0_0__valueRsLineRq(x_23);
            x_26 = x_25;
        end
        let x_27 <- releaseMSHR__0_0_0(x_4);
        Struct18 x_28 = (Struct18 {enq_type : (((x_19)[3:2]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : ((((x_19)[3:2]) ==
        ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : (x_19)[1:0], enq_msg : Struct1 {id : (Bit#(6))'(6'h9),
        type_ : (Bool)'(True), addr : (x_17).addr, value : unpack(0)}});
        let x_29 <- makeEnq_parentChildren_0_0_0(x_28);
    endrule
    
    rule rule_exec__0_0_0__1_3_0;
        let x_0 <- deq_fifoL2E__0_0_0();
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
        let x_10 <- getMSHR__0_0_0(x_4);
        let x_11 <- getMSHRRq__0_0_0(x_4);
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
            let x_21 <- victims___0_0_0__setVictim(Struct44 {victim_idx :
            (x_8).data, victim_info : (x_20).info, victim_value :
            ((x_20).value_write ? ((x_20).value) : (x_9))});
            x_23 = x_9;
        end else begin
            let x_22 <- cache___0_0_0__valueRsLineRq(x_20);
            x_23 = x_22;
        end
        Struct18 x_24 = (Struct18 {enq_type : ((((Bit#(4))'(4'h4))[3:2]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : (((((Bit#(4))'(4'h4))[3:2])
        == ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : ((Bit#(4))'(4'h4))[1:0], enq_msg : Struct1 {id :
        (Bit#(6))'(6'hd), type_ : (Bool)'(True), addr : (x_17).addr, value :
        unpack(0)}});
        let x_25 <- makeEnq_parentChildren_0_0_0(x_24);
        let x_26 <- releaseMSHR__0_0_0(x_4);
    endrule
    
    rule rule_exec__0_0_0__1_3_1;
        let x_0 <- deq_fifoL2E__0_0_0();
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
        let x_10 <- getMSHR__0_0_0(x_4);
        let x_11 <- getMSHRRq__0_0_0(x_4);
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
            let x_21 <- victims___0_0_0__setVictim(Struct44 {victim_idx :
            (x_8).data, victim_info : (x_20).info, victim_value :
            ((x_20).value_write ? ((x_20).value) : (x_9))});
            x_23 = x_9;
        end else begin
            let x_22 <- cache___0_0_0__valueRsLineRq(x_20);
            x_23 = x_22;
        end
        Struct18 x_24 = (Struct18 {enq_type : ((((Bit#(4))'(4'h4))[3:2]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : (((((Bit#(4))'(4'h4))[3:2])
        == ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : ((Bit#(4))'(4'h4))[1:0], enq_msg : Struct1 {id :
        (Bit#(6))'(6'hf), type_ : (Bool)'(True), addr : (x_17).addr, value :
        unpack(0)}});
        let x_25 <- makeEnq_parentChildren_0_0_0(x_24);
        let x_26 <- releaseMSHR__0_0_0(x_4);
    endrule
    
    rule rule_exec__0_0_0__2_0;
        let x_0 <- victims___0_0_0__getFirstVictim();
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
        let x_13 <- makeEnq_parentChildren_0_0_0(x_12);
        let x_14 <- setULImm__0_0_0(x_4);
        let x_15 <- victims___0_0_0__setVictimRq(x_1);
    endrule
    
    rule rule_exec__0_0_0__2_1;
        let x_0 <- victims___0_0_0__getFirstVictim();
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
        let x_13 <- makeEnq_parentChildren_0_0_0(x_12);
        let x_14 <- setULImm__0_0_0(x_4);
        let x_15 <- victims___0_0_0__setVictimRq(x_1);
    endrule
    
    // No methods in this module
endmodule

interface Module135;
    
endinterface

module mkModule135#(function Action victims___0_0_1__setVictimRq(Bit#(64) _),
    function Action setULImm__0_0_1(Struct1 _),
    function ActionValue#(Struct13) victims___0_0_1__getFirstVictim(),
    function Action victims___0_0_1__setVictim(Struct44 _),
    function Action registerUL__0_0_1(Struct43 _),
    function Action makeEnq_parentChildren_0_0_1(Struct18 _),
    function ActionValue#(Vector#(4, Bit#(64))) cache___0_0_1__valueRsLineRq(Struct42 _),
    function ActionValue#(Struct1) getMSHRRq__0_0_1(Bit#(2) _),
    function ActionValue#(Struct14) getMSHR__0_0_1(Bit#(2) _),
    function ActionValue#(Struct41) deq_fifoL2E__0_0_1(),
    function ActionValue#(Struct13) victims___0_0_1__getVictim(Bit#(1) _),
    function Action enq_fifoL2E__0_0_1(Struct41 _),
    function ActionValue#(Struct39) cache___0_0_1__infoRsValueRq(Bit#(64) _),
    function ActionValue#(Struct38) deq_fifoI2L__0_0_1(),
    function Action enq_fifoI2L__0_0_1(Struct38 _),
    function Action cache___0_0_1__infoRq(Bit#(64) _),
    function ActionValue#(Struct38) deq_fifoN2I__0_0_1(),
    function ActionValue#(Struct36) getCRqSlot__0_0_1(Struct35 _),
    function ActionValue#(Bool) victims___0_0_1__hasVictim(),
    function ActionValue#(Struct2) deq_fifoCRqInput__0_0_1(),
    function Action releaseMSHR__0_0_1(Bit#(2) _),
    function Action victims___0_0_1__releaseVictim(Bit#(64) _),
    function ActionValue#(Struct35) getWait__0_0_1(),
    function Action startRelease__0_0_1(Bit#(2) _),
    function ActionValue#(Bit#(2)) getULReady__0_0_1(Bit#(64) _),
    function Action enq_fifoN2I__0_0_1(Struct38 _),
    function ActionValue#(Struct37) victims___0_0_1__findVictim(Bit#(64) _),
    function ActionValue#(Struct36) getPRqSlot__0_0_1(Struct35 _),
    function ActionValue#(Struct2) deq_fifoPInput__0_0_1())
    (Module135);
    
    rule rule_in_prq__0_0_1;
        let x_0 <- deq_fifoPInput__0_0_1();
        Bit#(4) x_1 = ((x_0).in_msg_from);
        when ((x_1) == ({((Bit#(2))'(2'h2)),((Bit#(2))'(2'h1))}),
        noAction);
        Struct1 x_2 = ((x_0).in_msg);
        when (! ((x_2).type_), noAction);
        let x_3 <- getPRqSlot__0_0_1(Struct35 {r_id : unpack(0), r_msg : x_2,
        r_msg_from : (x_0).in_msg_from});
        when ((x_3).s_has_slot,
        noAction);
        if (! ((x_3).s_conflict)) begin
            let x_4 <- victims___0_0_1__findVictim((x_2).addr);
            Struct38 x_5 = (Struct38 {ir_is_rs_rel : (Bool)'(False), ir_msg :
            (x_0).in_msg, ir_msg_from : x_1, ir_mshr_id : (x_3).s_id,
            ir_by_victim : x_4});
            let x_6 <- enq_fifoN2I__0_0_1(x_5);
        end else begin
            
        end
    endrule
    
    rule rule_in_prs__0_0_1;
        let x_0 <- deq_fifoPInput__0_0_1();
        Bit#(4) x_1 = ((x_0).in_msg_from);
        when ((x_1) == ({((Bit#(2))'(2'h2)),((Bit#(2))'(2'h1))}),
        noAction);
        Struct1 x_2 = ((x_0).in_msg);
        when (((x_2).type_) && (! (((x_2).id) == ((Bit#(6))'(6'h16)))),
        noAction);
        let x_3 <- getULReady__0_0_1((x_2).addr);
        let x_4 <- startRelease__0_0_1(x_3);
        let x_5 <- victims___0_0_1__findVictim((x_2).addr);
        Struct38 x_6 = (Struct38 {ir_is_rs_rel : (Bool)'(False), ir_msg :
        (x_0).in_msg, ir_msg_from : x_1, ir_mshr_id : x_3, ir_by_victim :
        x_5});
        let x_7 <- enq_fifoN2I__0_0_1(x_6);
    endrule
    
    rule rule_in_retry__0_0_1;
        let x_0 <- getWait__0_0_1();
        Struct1 x_1 = ((x_0).r_msg);
        let x_2 <- victims___0_0_1__findVictim((x_1).addr);
        Struct38 x_3 = (Struct38 {ir_is_rs_rel : (Bool)'(False), ir_msg :
        x_1, ir_msg_from : (x_0).r_msg_from, ir_mshr_id : (x_0).r_id,
        ir_by_victim : x_2});
        let x_4 <- enq_fifoN2I__0_0_1(x_3);
    endrule
    
    rule rule_in_invrs__0_0_1;
        let x_0 <- deq_fifoPInput__0_0_1();
        Bit#(4) x_1 = ((x_0).in_msg_from);
        when ((x_1) == ({((Bit#(2))'(2'h2)),((Bit#(2))'(2'h1))}),
        noAction);
        Struct1 x_2 = ((x_0).in_msg);
        when (((x_2).type_) && (((x_2).id) == ((Bit#(6))'(6'h16))),
        noAction);
        let x_3 <- getULReady__0_0_1((x_2).addr);
        let x_4 <- victims___0_0_1__releaseVictim((x_2).addr);
        let x_5 <- releaseMSHR__0_0_1(x_3);
    endrule
    
    rule rule_in_crq__0_0_1;
        let x_0 <- deq_fifoCRqInput__0_0_1();
        Bit#(4) x_1 = ((x_0).in_msg_from);
        when (((x_1)[3:2]) == ((Bit#(2))'(2'h0)), noAction);
        Struct1 x_2 = ((x_0).in_msg);
        when (! ((x_2).type_), noAction);
        let x_3 <- victims___0_0_1__hasVictim();
        when (! (x_3), noAction);
        let x_4 <- getCRqSlot__0_0_1(Struct35 {r_id : unpack(0), r_msg : x_2,
        r_msg_from : x_1});
        when ((x_4).s_has_slot,
        noAction);
        if (! ((x_4).s_conflict)) begin
            let x_5 <- victims___0_0_1__findVictim((x_2).addr);
            Struct38 x_6 = (Struct38 {ir_is_rs_rel : (Bool)'(False), ir_msg :
            (x_0).in_msg, ir_msg_from : x_1, ir_mshr_id : (x_4).s_id,
            ir_by_victim : x_5});
            let x_7 <- enq_fifoN2I__0_0_1(x_6);
        end else begin
            
        end
    endrule
    
    rule rule_ir_cache__0_0_1;
        let x_0 <- deq_fifoN2I__0_0_1();
        when (! (((x_0).ir_by_victim).valid), noAction);
        Struct1 x_1 = ((x_0).ir_msg);
        let x_2 <- cache___0_0_1__infoRq((x_1).addr);
        let x_3 <- enq_fifoI2L__0_0_1(x_0);
    endrule
    
    rule rule_ir_victims__0_0_1;
        let x_0 <- deq_fifoN2I__0_0_1();
        when (((x_0).ir_by_victim).valid, noAction);
        let x_1 <- enq_fifoI2L__0_0_1(x_0);
    endrule
    
    rule rule_lr_cache__0_0_1;
        let x_0 <- deq_fifoI2L__0_0_1();
        when (! (((x_0).ir_by_victim).valid), noAction);
        let x_1 <- cache___0_0_1__infoRsValueRq(((x_0).ir_msg).addr);
        Struct41 x_2 = (Struct41 {lr_ir_pp : x_0, lr_ir : x_1, lr_value :
        unpack(0)});
        let x_3 <- enq_fifoL2E__0_0_1(x_2);
    endrule
    
    rule rule_lr_victims__0_0_1;
        let x_0 <- deq_fifoI2L__0_0_1();
        when (((x_0).ir_by_victim).valid, noAction);
        Bit#(1) x_1 = (((x_0).ir_by_victim).data);
        let x_2 <- victims___0_0_1__getVictim(x_1);
        Struct39 x_3 = (Struct39 {info_index : unpack(0), info_hit :
        unpack(0), info_way : unpack(0), edir_hit : unpack(0), edir_way :
        unpack(0), edir_slot : unpack(0), info : (x_2).victim_info,
        may_victim : unpack(0), reps : unpack(0)});
        Struct41 x_4 = (Struct41 {lr_ir_pp : x_0, lr_ir : x_3, lr_value :
        (x_2).victim_value});
        let x_5 <- enq_fifoL2E__0_0_1(x_4);
    endrule
    
    rule rule_exec__0_0_1__0_0;
        let x_0 <- deq_fifoL2E__0_0_1();
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
        let x_10 <- getMSHR__0_0_1(x_4);
        let x_11 <- getMSHRRq__0_0_1(x_4);
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
            let x_19 <- cache___0_0_1__valueRsLineRq(unpack(0));
            x_20 = x_19;
        end
        Struct18 x_21 = (Struct18 {enq_type : ((((Bit#(4))'(4'h8))[3:2]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : (((((Bit#(4))'(4'h8))[3:2])
        == ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : ((Bit#(4))'(4'h8))[1:0], enq_msg : Struct1 {id :
        (Bit#(6))'(6'h1), type_ : (Bool)'(True), addr : (x_17).addr, value :
        x_20}});
        let x_22 <- makeEnq_parentChildren_0_0_1(x_21);
        let x_23 <- releaseMSHR__0_0_1(x_4);
    endrule
    
    rule rule_exec__0_0_1__0_1;
        let x_0 <- deq_fifoL2E__0_0_1();
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
        let x_10 <- getMSHR__0_0_1(x_4);
        let x_11 <- getMSHRRq__0_0_1(x_4);
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
            let x_19 <- cache___0_0_1__valueRsLineRq(unpack(0));
            x_20 = x_19;
        end
        let x_21 <- registerUL__0_0_1(Struct43 {r_id : x_4, r_ul_rsb :
        (Bool)'(True), r_ul_rsbTo : ((Bit#(4))'(4'h8))[1:0]});
        Struct18 x_22 = (Struct18 {enq_type : ((((Bit#(4))'(4'h1))[3:2]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : (((((Bit#(4))'(4'h1))[3:2])
        == ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : ((Bit#(4))'(4'h1))[1:0], enq_msg : Struct1 {id :
        (Bit#(6))'(6'h2), type_ : (Bool)'(False), addr : (x_17).addr, value :
        unpack(0)}});
        let x_23 <- makeEnq_parentChildren_0_0_1(x_22);
    endrule
    
    rule rule_exec__0_0_1__0_2_0;
        let x_0 <- deq_fifoL2E__0_0_1();
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
        let x_10 <- getMSHR__0_0_1(x_4);
        let x_11 <- getMSHRRq__0_0_1(x_4);
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
            let x_23 <- victims___0_0_1__setVictim(Struct44 {victim_idx :
            (x_8).data, victim_info : (x_22).info, victim_value :
            ((x_22).value_write ? ((x_22).value) : (x_9))});
            x_25 = x_9;
        end else begin
            let x_24 <- cache___0_0_1__valueRsLineRq(x_22);
            x_25 = x_24;
        end
        let x_26 <- releaseMSHR__0_0_1(x_4);
        Struct18 x_27 = (Struct18 {enq_type : (((x_19)[3:2]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : ((((x_19)[3:2]) ==
        ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : (x_19)[1:0], enq_msg : Struct1 {id : (Bit#(6))'(6'h1),
        type_ : (Bool)'(True), addr : (x_17).addr, value :
        (x_17).value}});
        let x_28 <- makeEnq_parentChildren_0_0_1(x_27);
    endrule
    
    rule rule_exec__0_0_1__0_2_1;
        let x_0 <- deq_fifoL2E__0_0_1();
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
        let x_10 <- getMSHR__0_0_1(x_4);
        let x_11 <- getMSHRRq__0_0_1(x_4);
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
            let x_23 <- victims___0_0_1__setVictim(Struct44 {victim_idx :
            (x_8).data, victim_info : (x_22).info, victim_value :
            ((x_22).value_write ? ((x_22).value) : (x_9))});
            x_25 = x_9;
        end else begin
            let x_24 <- cache___0_0_1__valueRsLineRq(x_22);
            x_25 = x_24;
        end
        let x_26 <- releaseMSHR__0_0_1(x_4);
        Struct18 x_27 = (Struct18 {enq_type : (((x_19)[3:2]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : ((((x_19)[3:2]) ==
        ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : (x_19)[1:0], enq_msg : Struct1 {id : (Bit#(6))'(6'h1),
        type_ : (Bool)'(True), addr : (x_17).addr, value :
        (x_17).value}});
        let x_28 <- makeEnq_parentChildren_0_0_1(x_27);
    endrule
    
    rule rule_exec__0_0_1__0_3;
        let x_0 <- deq_fifoL2E__0_0_1();
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
        let x_10 <- getMSHR__0_0_1(x_4);
        let x_11 <- getMSHRRq__0_0_1(x_4);
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
            let x_21 <- victims___0_0_1__setVictim(Struct44 {victim_idx :
            (x_8).data, victim_info : (x_20).info, victim_value :
            ((x_20).value_write ? ((x_20).value) : (x_9))});
            x_23 = x_9;
        end else begin
            let x_22 <- cache___0_0_1__valueRsLineRq(x_20);
            x_23 = x_22;
        end
        Struct18 x_24 = (Struct18 {enq_type : ((((Bit#(4))'(4'h5))[3:2]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : (((((Bit#(4))'(4'h5))[3:2])
        == ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : ((Bit#(4))'(4'h5))[1:0], enq_msg : Struct1 {id :
        (Bit#(6))'(6'h6), type_ : (Bool)'(True), addr : (x_17).addr, value :
        x_23}});
        let x_25 <- makeEnq_parentChildren_0_0_1(x_24);
        let x_26 <- releaseMSHR__0_0_1(x_4);
    endrule
    
    rule rule_exec__0_0_1__1_0_0;
        let x_0 <- deq_fifoL2E__0_0_1();
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
        let x_10 <- getMSHR__0_0_1(x_4);
        let x_11 <- getMSHRRq__0_0_1(x_4);
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
            let x_22 <- victims___0_0_1__setVictim(Struct44 {victim_idx :
            (x_8).data, victim_info : (x_21).info, victim_value :
            ((x_21).value_write ? ((x_21).value) : (x_9))});
            x_24 = x_9;
        end else begin
            let x_23 <- cache___0_0_1__valueRsLineRq(x_21);
            x_24 = x_23;
        end
        Struct18 x_25 = (Struct18 {enq_type : ((((Bit#(4))'(4'h8))[3:2]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : (((((Bit#(4))'(4'h8))[3:2])
        == ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : ((Bit#(4))'(4'h8))[1:0], enq_msg : Struct1 {id :
        (Bit#(6))'(6'h9), type_ : (Bool)'(True), addr : (x_17).addr, value :
        unpack(0)}});
        let x_26 <- makeEnq_parentChildren_0_0_1(x_25);
        let x_27 <- releaseMSHR__0_0_1(x_4);
    endrule
    
    rule rule_exec__0_0_1__1_0_1;
        let x_0 <- deq_fifoL2E__0_0_1();
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
        let x_10 <- getMSHR__0_0_1(x_4);
        let x_11 <- getMSHRRq__0_0_1(x_4);
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
            let x_20 <- victims___0_0_1__setVictim(Struct44 {victim_idx :
            (x_8).data, victim_info : (x_19).info, victim_value :
            ((x_19).value_write ? ((x_19).value) : (x_9))});
            x_22 = x_9;
        end else begin
            let x_21 <- cache___0_0_1__valueRsLineRq(x_19);
            x_22 = x_21;
        end
        Struct18 x_23 = (Struct18 {enq_type : ((((Bit#(4))'(4'h8))[3:2]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : (((((Bit#(4))'(4'h8))[3:2])
        == ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : ((Bit#(4))'(4'h8))[1:0], enq_msg : Struct1 {id :
        (Bit#(6))'(6'h9), type_ : (Bool)'(True), addr : (x_17).addr, value :
        unpack(0)}});
        let x_24 <- makeEnq_parentChildren_0_0_1(x_23);
        let x_25 <- releaseMSHR__0_0_1(x_4);
    endrule
    
    rule rule_exec__0_0_1__1_1;
        let x_0 <- deq_fifoL2E__0_0_1();
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
        let x_10 <- getMSHR__0_0_1(x_4);
        let x_11 <- getMSHRRq__0_0_1(x_4);
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
            let x_19 <- cache___0_0_1__valueRsLineRq(unpack(0));
            x_20 = x_19;
        end
        let x_21 <- registerUL__0_0_1(Struct43 {r_id : x_4, r_ul_rsb :
        (Bool)'(True), r_ul_rsbTo : ((Bit#(4))'(4'h8))[1:0]});
        Struct18 x_22 = (Struct18 {enq_type : ((((Bit#(4))'(4'h1))[3:2]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : (((((Bit#(4))'(4'h1))[3:2])
        == ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : ((Bit#(4))'(4'h1))[1:0], enq_msg : Struct1 {id :
        (Bit#(6))'(6'ha), type_ : (Bool)'(False), addr : (x_17).addr, value :
        unpack(0)}});
        let x_23 <- makeEnq_parentChildren_0_0_1(x_22);
    endrule
    
    rule rule_exec__0_0_1__1_2;
        let x_0 <- deq_fifoL2E__0_0_1();
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
        let x_10 <- getMSHR__0_0_1(x_4);
        let x_11 <- getMSHRRq__0_0_1(x_4);
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
            let x_24 <- victims___0_0_1__setVictim(Struct44 {victim_idx :
            (x_8).data, victim_info : (x_23).info, victim_value :
            ((x_23).value_write ? ((x_23).value) : (x_9))});
            x_26 = x_9;
        end else begin
            let x_25 <- cache___0_0_1__valueRsLineRq(x_23);
            x_26 = x_25;
        end
        let x_27 <- releaseMSHR__0_0_1(x_4);
        Struct18 x_28 = (Struct18 {enq_type : (((x_19)[3:2]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : ((((x_19)[3:2]) ==
        ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : (x_19)[1:0], enq_msg : Struct1 {id : (Bit#(6))'(6'h9),
        type_ : (Bool)'(True), addr : (x_17).addr, value : unpack(0)}});
        let x_29 <- makeEnq_parentChildren_0_0_1(x_28);
    endrule
    
    rule rule_exec__0_0_1__1_3_0;
        let x_0 <- deq_fifoL2E__0_0_1();
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
        let x_10 <- getMSHR__0_0_1(x_4);
        let x_11 <- getMSHRRq__0_0_1(x_4);
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
            let x_21 <- victims___0_0_1__setVictim(Struct44 {victim_idx :
            (x_8).data, victim_info : (x_20).info, victim_value :
            ((x_20).value_write ? ((x_20).value) : (x_9))});
            x_23 = x_9;
        end else begin
            let x_22 <- cache___0_0_1__valueRsLineRq(x_20);
            x_23 = x_22;
        end
        Struct18 x_24 = (Struct18 {enq_type : ((((Bit#(4))'(4'h5))[3:2]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : (((((Bit#(4))'(4'h5))[3:2])
        == ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : ((Bit#(4))'(4'h5))[1:0], enq_msg : Struct1 {id :
        (Bit#(6))'(6'hd), type_ : (Bool)'(True), addr : (x_17).addr, value :
        unpack(0)}});
        let x_25 <- makeEnq_parentChildren_0_0_1(x_24);
        let x_26 <- releaseMSHR__0_0_1(x_4);
    endrule
    
    rule rule_exec__0_0_1__1_3_1;
        let x_0 <- deq_fifoL2E__0_0_1();
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
        let x_10 <- getMSHR__0_0_1(x_4);
        let x_11 <- getMSHRRq__0_0_1(x_4);
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
            let x_21 <- victims___0_0_1__setVictim(Struct44 {victim_idx :
            (x_8).data, victim_info : (x_20).info, victim_value :
            ((x_20).value_write ? ((x_20).value) : (x_9))});
            x_23 = x_9;
        end else begin
            let x_22 <- cache___0_0_1__valueRsLineRq(x_20);
            x_23 = x_22;
        end
        Struct18 x_24 = (Struct18 {enq_type : ((((Bit#(4))'(4'h5))[3:2]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : (((((Bit#(4))'(4'h5))[3:2])
        == ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : ((Bit#(4))'(4'h5))[1:0], enq_msg : Struct1 {id :
        (Bit#(6))'(6'hf), type_ : (Bool)'(True), addr : (x_17).addr, value :
        unpack(0)}});
        let x_25 <- makeEnq_parentChildren_0_0_1(x_24);
        let x_26 <- releaseMSHR__0_0_1(x_4);
    endrule
    
    rule rule_exec__0_0_1__2_0;
        let x_0 <- victims___0_0_1__getFirstVictim();
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
        let x_13 <- makeEnq_parentChildren_0_0_1(x_12);
        let x_14 <- setULImm__0_0_1(x_4);
        let x_15 <- victims___0_0_1__setVictimRq(x_1);
    endrule
    
    rule rule_exec__0_0_1__2_1;
        let x_0 <- victims___0_0_1__getFirstVictim();
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
        let x_13 <- makeEnq_parentChildren_0_0_1(x_12);
        let x_14 <- setULImm__0_0_1(x_4);
        let x_15 <- victims___0_0_1__setVictimRq(x_1);
    endrule
    
    // No methods in this module
endmodule

interface Module136;
    
endinterface

module mkModule136#(function Action victims___0_0_2__setVictimRq(Bit#(64) _),
    function Action setULImm__0_0_2(Struct1 _),
    function ActionValue#(Struct13) victims___0_0_2__getFirstVictim(),
    function Action victims___0_0_2__setVictim(Struct44 _),
    function Action registerUL__0_0_2(Struct43 _),
    function Action makeEnq_parentChildren_0_0_2(Struct18 _),
    function ActionValue#(Vector#(4, Bit#(64))) cache___0_0_2__valueRsLineRq(Struct42 _),
    function ActionValue#(Struct1) getMSHRRq__0_0_2(Bit#(2) _),
    function ActionValue#(Struct14) getMSHR__0_0_2(Bit#(2) _),
    function ActionValue#(Struct41) deq_fifoL2E__0_0_2(),
    function ActionValue#(Struct13) victims___0_0_2__getVictim(Bit#(1) _),
    function Action enq_fifoL2E__0_0_2(Struct41 _),
    function ActionValue#(Struct39) cache___0_0_2__infoRsValueRq(Bit#(64) _),
    function ActionValue#(Struct38) deq_fifoI2L__0_0_2(),
    function Action enq_fifoI2L__0_0_2(Struct38 _),
    function Action cache___0_0_2__infoRq(Bit#(64) _),
    function ActionValue#(Struct38) deq_fifoN2I__0_0_2(),
    function ActionValue#(Struct36) getCRqSlot__0_0_2(Struct35 _),
    function ActionValue#(Bool) victims___0_0_2__hasVictim(),
    function ActionValue#(Struct2) deq_fifoCRqInput__0_0_2(),
    function Action releaseMSHR__0_0_2(Bit#(2) _),
    function Action victims___0_0_2__releaseVictim(Bit#(64) _),
    function ActionValue#(Struct35) getWait__0_0_2(),
    function Action startRelease__0_0_2(Bit#(2) _),
    function ActionValue#(Bit#(2)) getULReady__0_0_2(Bit#(64) _),
    function Action enq_fifoN2I__0_0_2(Struct38 _),
    function ActionValue#(Struct37) victims___0_0_2__findVictim(Bit#(64) _),
    function ActionValue#(Struct36) getPRqSlot__0_0_2(Struct35 _),
    function ActionValue#(Struct2) deq_fifoPInput__0_0_2())
    (Module136);
    
    rule rule_in_prq__0_0_2;
        let x_0 <- deq_fifoPInput__0_0_2();
        Bit#(4) x_1 = ((x_0).in_msg_from);
        when ((x_1) == ({((Bit#(2))'(2'h2)),((Bit#(2))'(2'h2))}),
        noAction);
        Struct1 x_2 = ((x_0).in_msg);
        when (! ((x_2).type_), noAction);
        let x_3 <- getPRqSlot__0_0_2(Struct35 {r_id : unpack(0), r_msg : x_2,
        r_msg_from : (x_0).in_msg_from});
        when ((x_3).s_has_slot,
        noAction);
        if (! ((x_3).s_conflict)) begin
            let x_4 <- victims___0_0_2__findVictim((x_2).addr);
            Struct38 x_5 = (Struct38 {ir_is_rs_rel : (Bool)'(False), ir_msg :
            (x_0).in_msg, ir_msg_from : x_1, ir_mshr_id : (x_3).s_id,
            ir_by_victim : x_4});
            let x_6 <- enq_fifoN2I__0_0_2(x_5);
        end else begin
            
        end
    endrule
    
    rule rule_in_prs__0_0_2;
        let x_0 <- deq_fifoPInput__0_0_2();
        Bit#(4) x_1 = ((x_0).in_msg_from);
        when ((x_1) == ({((Bit#(2))'(2'h2)),((Bit#(2))'(2'h2))}),
        noAction);
        Struct1 x_2 = ((x_0).in_msg);
        when (((x_2).type_) && (! (((x_2).id) == ((Bit#(6))'(6'h16)))),
        noAction);
        let x_3 <- getULReady__0_0_2((x_2).addr);
        let x_4 <- startRelease__0_0_2(x_3);
        let x_5 <- victims___0_0_2__findVictim((x_2).addr);
        Struct38 x_6 = (Struct38 {ir_is_rs_rel : (Bool)'(False), ir_msg :
        (x_0).in_msg, ir_msg_from : x_1, ir_mshr_id : x_3, ir_by_victim :
        x_5});
        let x_7 <- enq_fifoN2I__0_0_2(x_6);
    endrule
    
    rule rule_in_retry__0_0_2;
        let x_0 <- getWait__0_0_2();
        Struct1 x_1 = ((x_0).r_msg);
        let x_2 <- victims___0_0_2__findVictim((x_1).addr);
        Struct38 x_3 = (Struct38 {ir_is_rs_rel : (Bool)'(False), ir_msg :
        x_1, ir_msg_from : (x_0).r_msg_from, ir_mshr_id : (x_0).r_id,
        ir_by_victim : x_2});
        let x_4 <- enq_fifoN2I__0_0_2(x_3);
    endrule
    
    rule rule_in_invrs__0_0_2;
        let x_0 <- deq_fifoPInput__0_0_2();
        Bit#(4) x_1 = ((x_0).in_msg_from);
        when ((x_1) == ({((Bit#(2))'(2'h2)),((Bit#(2))'(2'h2))}),
        noAction);
        Struct1 x_2 = ((x_0).in_msg);
        when (((x_2).type_) && (((x_2).id) == ((Bit#(6))'(6'h16))),
        noAction);
        let x_3 <- getULReady__0_0_2((x_2).addr);
        let x_4 <- victims___0_0_2__releaseVictim((x_2).addr);
        let x_5 <- releaseMSHR__0_0_2(x_3);
    endrule
    
    rule rule_in_crq__0_0_2;
        let x_0 <- deq_fifoCRqInput__0_0_2();
        Bit#(4) x_1 = ((x_0).in_msg_from);
        when (((x_1)[3:2]) == ((Bit#(2))'(2'h0)), noAction);
        Struct1 x_2 = ((x_0).in_msg);
        when (! ((x_2).type_), noAction);
        let x_3 <- victims___0_0_2__hasVictim();
        when (! (x_3), noAction);
        let x_4 <- getCRqSlot__0_0_2(Struct35 {r_id : unpack(0), r_msg : x_2,
        r_msg_from : x_1});
        when ((x_4).s_has_slot,
        noAction);
        if (! ((x_4).s_conflict)) begin
            let x_5 <- victims___0_0_2__findVictim((x_2).addr);
            Struct38 x_6 = (Struct38 {ir_is_rs_rel : (Bool)'(False), ir_msg :
            (x_0).in_msg, ir_msg_from : x_1, ir_mshr_id : (x_4).s_id,
            ir_by_victim : x_5});
            let x_7 <- enq_fifoN2I__0_0_2(x_6);
        end else begin
            
        end
    endrule
    
    rule rule_ir_cache__0_0_2;
        let x_0 <- deq_fifoN2I__0_0_2();
        when (! (((x_0).ir_by_victim).valid), noAction);
        Struct1 x_1 = ((x_0).ir_msg);
        let x_2 <- cache___0_0_2__infoRq((x_1).addr);
        let x_3 <- enq_fifoI2L__0_0_2(x_0);
    endrule
    
    rule rule_ir_victims__0_0_2;
        let x_0 <- deq_fifoN2I__0_0_2();
        when (((x_0).ir_by_victim).valid, noAction);
        let x_1 <- enq_fifoI2L__0_0_2(x_0);
    endrule
    
    rule rule_lr_cache__0_0_2;
        let x_0 <- deq_fifoI2L__0_0_2();
        when (! (((x_0).ir_by_victim).valid), noAction);
        let x_1 <- cache___0_0_2__infoRsValueRq(((x_0).ir_msg).addr);
        Struct41 x_2 = (Struct41 {lr_ir_pp : x_0, lr_ir : x_1, lr_value :
        unpack(0)});
        let x_3 <- enq_fifoL2E__0_0_2(x_2);
    endrule
    
    rule rule_lr_victims__0_0_2;
        let x_0 <- deq_fifoI2L__0_0_2();
        when (((x_0).ir_by_victim).valid, noAction);
        Bit#(1) x_1 = (((x_0).ir_by_victim).data);
        let x_2 <- victims___0_0_2__getVictim(x_1);
        Struct39 x_3 = (Struct39 {info_index : unpack(0), info_hit :
        unpack(0), info_way : unpack(0), edir_hit : unpack(0), edir_way :
        unpack(0), edir_slot : unpack(0), info : (x_2).victim_info,
        may_victim : unpack(0), reps : unpack(0)});
        Struct41 x_4 = (Struct41 {lr_ir_pp : x_0, lr_ir : x_3, lr_value :
        (x_2).victim_value});
        let x_5 <- enq_fifoL2E__0_0_2(x_4);
    endrule
    
    rule rule_exec__0_0_2__0_0;
        let x_0 <- deq_fifoL2E__0_0_2();
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
        let x_10 <- getMSHR__0_0_2(x_4);
        let x_11 <- getMSHRRq__0_0_2(x_4);
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
            let x_19 <- cache___0_0_2__valueRsLineRq(unpack(0));
            x_20 = x_19;
        end
        Struct18 x_21 = (Struct18 {enq_type : ((((Bit#(4))'(4'h8))[3:2]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : (((((Bit#(4))'(4'h8))[3:2])
        == ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : ((Bit#(4))'(4'h8))[1:0], enq_msg : Struct1 {id :
        (Bit#(6))'(6'h1), type_ : (Bool)'(True), addr : (x_17).addr, value :
        x_20}});
        let x_22 <- makeEnq_parentChildren_0_0_2(x_21);
        let x_23 <- releaseMSHR__0_0_2(x_4);
    endrule
    
    rule rule_exec__0_0_2__0_1;
        let x_0 <- deq_fifoL2E__0_0_2();
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
        let x_10 <- getMSHR__0_0_2(x_4);
        let x_11 <- getMSHRRq__0_0_2(x_4);
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
            let x_19 <- cache___0_0_2__valueRsLineRq(unpack(0));
            x_20 = x_19;
        end
        let x_21 <- registerUL__0_0_2(Struct43 {r_id : x_4, r_ul_rsb :
        (Bool)'(True), r_ul_rsbTo : ((Bit#(4))'(4'h8))[1:0]});
        Struct18 x_22 = (Struct18 {enq_type : ((((Bit#(4))'(4'h2))[3:2]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : (((((Bit#(4))'(4'h2))[3:2])
        == ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : ((Bit#(4))'(4'h2))[1:0], enq_msg : Struct1 {id :
        (Bit#(6))'(6'h2), type_ : (Bool)'(False), addr : (x_17).addr, value :
        unpack(0)}});
        let x_23 <- makeEnq_parentChildren_0_0_2(x_22);
    endrule
    
    rule rule_exec__0_0_2__0_2_0;
        let x_0 <- deq_fifoL2E__0_0_2();
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
        let x_10 <- getMSHR__0_0_2(x_4);
        let x_11 <- getMSHRRq__0_0_2(x_4);
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
            let x_23 <- victims___0_0_2__setVictim(Struct44 {victim_idx :
            (x_8).data, victim_info : (x_22).info, victim_value :
            ((x_22).value_write ? ((x_22).value) : (x_9))});
            x_25 = x_9;
        end else begin
            let x_24 <- cache___0_0_2__valueRsLineRq(x_22);
            x_25 = x_24;
        end
        let x_26 <- releaseMSHR__0_0_2(x_4);
        Struct18 x_27 = (Struct18 {enq_type : (((x_19)[3:2]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : ((((x_19)[3:2]) ==
        ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : (x_19)[1:0], enq_msg : Struct1 {id : (Bit#(6))'(6'h1),
        type_ : (Bool)'(True), addr : (x_17).addr, value :
        (x_17).value}});
        let x_28 <- makeEnq_parentChildren_0_0_2(x_27);
    endrule
    
    rule rule_exec__0_0_2__0_2_1;
        let x_0 <- deq_fifoL2E__0_0_2();
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
        let x_10 <- getMSHR__0_0_2(x_4);
        let x_11 <- getMSHRRq__0_0_2(x_4);
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
            let x_23 <- victims___0_0_2__setVictim(Struct44 {victim_idx :
            (x_8).data, victim_info : (x_22).info, victim_value :
            ((x_22).value_write ? ((x_22).value) : (x_9))});
            x_25 = x_9;
        end else begin
            let x_24 <- cache___0_0_2__valueRsLineRq(x_22);
            x_25 = x_24;
        end
        let x_26 <- releaseMSHR__0_0_2(x_4);
        Struct18 x_27 = (Struct18 {enq_type : (((x_19)[3:2]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : ((((x_19)[3:2]) ==
        ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : (x_19)[1:0], enq_msg : Struct1 {id : (Bit#(6))'(6'h1),
        type_ : (Bool)'(True), addr : (x_17).addr, value :
        (x_17).value}});
        let x_28 <- makeEnq_parentChildren_0_0_2(x_27);
    endrule
    
    rule rule_exec__0_0_2__0_3;
        let x_0 <- deq_fifoL2E__0_0_2();
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
        let x_10 <- getMSHR__0_0_2(x_4);
        let x_11 <- getMSHRRq__0_0_2(x_4);
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
            let x_21 <- victims___0_0_2__setVictim(Struct44 {victim_idx :
            (x_8).data, victim_info : (x_20).info, victim_value :
            ((x_20).value_write ? ((x_20).value) : (x_9))});
            x_23 = x_9;
        end else begin
            let x_22 <- cache___0_0_2__valueRsLineRq(x_20);
            x_23 = x_22;
        end
        Struct18 x_24 = (Struct18 {enq_type : ((((Bit#(4))'(4'h6))[3:2]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : (((((Bit#(4))'(4'h6))[3:2])
        == ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : ((Bit#(4))'(4'h6))[1:0], enq_msg : Struct1 {id :
        (Bit#(6))'(6'h6), type_ : (Bool)'(True), addr : (x_17).addr, value :
        x_23}});
        let x_25 <- makeEnq_parentChildren_0_0_2(x_24);
        let x_26 <- releaseMSHR__0_0_2(x_4);
    endrule
    
    rule rule_exec__0_0_2__1_0_0;
        let x_0 <- deq_fifoL2E__0_0_2();
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
        let x_10 <- getMSHR__0_0_2(x_4);
        let x_11 <- getMSHRRq__0_0_2(x_4);
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
            let x_22 <- victims___0_0_2__setVictim(Struct44 {victim_idx :
            (x_8).data, victim_info : (x_21).info, victim_value :
            ((x_21).value_write ? ((x_21).value) : (x_9))});
            x_24 = x_9;
        end else begin
            let x_23 <- cache___0_0_2__valueRsLineRq(x_21);
            x_24 = x_23;
        end
        Struct18 x_25 = (Struct18 {enq_type : ((((Bit#(4))'(4'h8))[3:2]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : (((((Bit#(4))'(4'h8))[3:2])
        == ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : ((Bit#(4))'(4'h8))[1:0], enq_msg : Struct1 {id :
        (Bit#(6))'(6'h9), type_ : (Bool)'(True), addr : (x_17).addr, value :
        unpack(0)}});
        let x_26 <- makeEnq_parentChildren_0_0_2(x_25);
        let x_27 <- releaseMSHR__0_0_2(x_4);
    endrule
    
    rule rule_exec__0_0_2__1_0_1;
        let x_0 <- deq_fifoL2E__0_0_2();
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
        let x_10 <- getMSHR__0_0_2(x_4);
        let x_11 <- getMSHRRq__0_0_2(x_4);
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
            let x_20 <- victims___0_0_2__setVictim(Struct44 {victim_idx :
            (x_8).data, victim_info : (x_19).info, victim_value :
            ((x_19).value_write ? ((x_19).value) : (x_9))});
            x_22 = x_9;
        end else begin
            let x_21 <- cache___0_0_2__valueRsLineRq(x_19);
            x_22 = x_21;
        end
        Struct18 x_23 = (Struct18 {enq_type : ((((Bit#(4))'(4'h8))[3:2]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : (((((Bit#(4))'(4'h8))[3:2])
        == ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : ((Bit#(4))'(4'h8))[1:0], enq_msg : Struct1 {id :
        (Bit#(6))'(6'h9), type_ : (Bool)'(True), addr : (x_17).addr, value :
        unpack(0)}});
        let x_24 <- makeEnq_parentChildren_0_0_2(x_23);
        let x_25 <- releaseMSHR__0_0_2(x_4);
    endrule
    
    rule rule_exec__0_0_2__1_1;
        let x_0 <- deq_fifoL2E__0_0_2();
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
        let x_10 <- getMSHR__0_0_2(x_4);
        let x_11 <- getMSHRRq__0_0_2(x_4);
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
            let x_19 <- cache___0_0_2__valueRsLineRq(unpack(0));
            x_20 = x_19;
        end
        let x_21 <- registerUL__0_0_2(Struct43 {r_id : x_4, r_ul_rsb :
        (Bool)'(True), r_ul_rsbTo : ((Bit#(4))'(4'h8))[1:0]});
        Struct18 x_22 = (Struct18 {enq_type : ((((Bit#(4))'(4'h2))[3:2]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : (((((Bit#(4))'(4'h2))[3:2])
        == ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : ((Bit#(4))'(4'h2))[1:0], enq_msg : Struct1 {id :
        (Bit#(6))'(6'ha), type_ : (Bool)'(False), addr : (x_17).addr, value :
        unpack(0)}});
        let x_23 <- makeEnq_parentChildren_0_0_2(x_22);
    endrule
    
    rule rule_exec__0_0_2__1_2;
        let x_0 <- deq_fifoL2E__0_0_2();
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
        let x_10 <- getMSHR__0_0_2(x_4);
        let x_11 <- getMSHRRq__0_0_2(x_4);
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
            let x_24 <- victims___0_0_2__setVictim(Struct44 {victim_idx :
            (x_8).data, victim_info : (x_23).info, victim_value :
            ((x_23).value_write ? ((x_23).value) : (x_9))});
            x_26 = x_9;
        end else begin
            let x_25 <- cache___0_0_2__valueRsLineRq(x_23);
            x_26 = x_25;
        end
        let x_27 <- releaseMSHR__0_0_2(x_4);
        Struct18 x_28 = (Struct18 {enq_type : (((x_19)[3:2]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : ((((x_19)[3:2]) ==
        ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : (x_19)[1:0], enq_msg : Struct1 {id : (Bit#(6))'(6'h9),
        type_ : (Bool)'(True), addr : (x_17).addr, value : unpack(0)}});
        let x_29 <- makeEnq_parentChildren_0_0_2(x_28);
    endrule
    
    rule rule_exec__0_0_2__1_3_0;
        let x_0 <- deq_fifoL2E__0_0_2();
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
        let x_10 <- getMSHR__0_0_2(x_4);
        let x_11 <- getMSHRRq__0_0_2(x_4);
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
            let x_21 <- victims___0_0_2__setVictim(Struct44 {victim_idx :
            (x_8).data, victim_info : (x_20).info, victim_value :
            ((x_20).value_write ? ((x_20).value) : (x_9))});
            x_23 = x_9;
        end else begin
            let x_22 <- cache___0_0_2__valueRsLineRq(x_20);
            x_23 = x_22;
        end
        Struct18 x_24 = (Struct18 {enq_type : ((((Bit#(4))'(4'h6))[3:2]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : (((((Bit#(4))'(4'h6))[3:2])
        == ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : ((Bit#(4))'(4'h6))[1:0], enq_msg : Struct1 {id :
        (Bit#(6))'(6'hd), type_ : (Bool)'(True), addr : (x_17).addr, value :
        unpack(0)}});
        let x_25 <- makeEnq_parentChildren_0_0_2(x_24);
        let x_26 <- releaseMSHR__0_0_2(x_4);
    endrule
    
    rule rule_exec__0_0_2__1_3_1;
        let x_0 <- deq_fifoL2E__0_0_2();
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
        let x_10 <- getMSHR__0_0_2(x_4);
        let x_11 <- getMSHRRq__0_0_2(x_4);
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
            let x_21 <- victims___0_0_2__setVictim(Struct44 {victim_idx :
            (x_8).data, victim_info : (x_20).info, victim_value :
            ((x_20).value_write ? ((x_20).value) : (x_9))});
            x_23 = x_9;
        end else begin
            let x_22 <- cache___0_0_2__valueRsLineRq(x_20);
            x_23 = x_22;
        end
        Struct18 x_24 = (Struct18 {enq_type : ((((Bit#(4))'(4'h6))[3:2]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : (((((Bit#(4))'(4'h6))[3:2])
        == ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : ((Bit#(4))'(4'h6))[1:0], enq_msg : Struct1 {id :
        (Bit#(6))'(6'hf), type_ : (Bool)'(True), addr : (x_17).addr, value :
        unpack(0)}});
        let x_25 <- makeEnq_parentChildren_0_0_2(x_24);
        let x_26 <- releaseMSHR__0_0_2(x_4);
    endrule
    
    rule rule_exec__0_0_2__2_0;
        let x_0 <- victims___0_0_2__getFirstVictim();
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
        let x_13 <- makeEnq_parentChildren_0_0_2(x_12);
        let x_14 <- setULImm__0_0_2(x_4);
        let x_15 <- victims___0_0_2__setVictimRq(x_1);
    endrule
    
    rule rule_exec__0_0_2__2_1;
        let x_0 <- victims___0_0_2__getFirstVictim();
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
        let x_13 <- makeEnq_parentChildren_0_0_2(x_12);
        let x_14 <- setULImm__0_0_2(x_4);
        let x_15 <- victims___0_0_2__setVictimRq(x_1);
    endrule
    
    // No methods in this module
endmodule

interface Module137;
    
endinterface

module mkModule137#(function Action victims___0_0_3__setVictimRq(Bit#(64) _),
    function Action setULImm__0_0_3(Struct1 _),
    function ActionValue#(Struct13) victims___0_0_3__getFirstVictim(),
    function Action victims___0_0_3__setVictim(Struct44 _),
    function Action registerUL__0_0_3(Struct43 _),
    function Action makeEnq_parentChildren_0_0_3(Struct18 _),
    function ActionValue#(Vector#(4, Bit#(64))) cache___0_0_3__valueRsLineRq(Struct42 _),
    function ActionValue#(Struct1) getMSHRRq__0_0_3(Bit#(2) _),
    function ActionValue#(Struct14) getMSHR__0_0_3(Bit#(2) _),
    function ActionValue#(Struct41) deq_fifoL2E__0_0_3(),
    function ActionValue#(Struct13) victims___0_0_3__getVictim(Bit#(1) _),
    function Action enq_fifoL2E__0_0_3(Struct41 _),
    function ActionValue#(Struct39) cache___0_0_3__infoRsValueRq(Bit#(64) _),
    function ActionValue#(Struct38) deq_fifoI2L__0_0_3(),
    function Action enq_fifoI2L__0_0_3(Struct38 _),
    function Action cache___0_0_3__infoRq(Bit#(64) _),
    function ActionValue#(Struct38) deq_fifoN2I__0_0_3(),
    function ActionValue#(Struct36) getCRqSlot__0_0_3(Struct35 _),
    function ActionValue#(Bool) victims___0_0_3__hasVictim(),
    function ActionValue#(Struct2) deq_fifoCRqInput__0_0_3(),
    function Action releaseMSHR__0_0_3(Bit#(2) _),
    function Action victims___0_0_3__releaseVictim(Bit#(64) _),
    function ActionValue#(Struct35) getWait__0_0_3(),
    function Action startRelease__0_0_3(Bit#(2) _),
    function ActionValue#(Bit#(2)) getULReady__0_0_3(Bit#(64) _),
    function Action enq_fifoN2I__0_0_3(Struct38 _),
    function ActionValue#(Struct37) victims___0_0_3__findVictim(Bit#(64) _),
    function ActionValue#(Struct36) getPRqSlot__0_0_3(Struct35 _),
    function ActionValue#(Struct2) deq_fifoPInput__0_0_3())
    (Module137);
    
    rule rule_in_prq__0_0_3;
        let x_0 <- deq_fifoPInput__0_0_3();
        Bit#(4) x_1 = ((x_0).in_msg_from);
        when ((x_1) == ({((Bit#(2))'(2'h2)),((Bit#(2))'(2'h3))}),
        noAction);
        Struct1 x_2 = ((x_0).in_msg);
        when (! ((x_2).type_), noAction);
        let x_3 <- getPRqSlot__0_0_3(Struct35 {r_id : unpack(0), r_msg : x_2,
        r_msg_from : (x_0).in_msg_from});
        when ((x_3).s_has_slot,
        noAction);
        if (! ((x_3).s_conflict)) begin
            let x_4 <- victims___0_0_3__findVictim((x_2).addr);
            Struct38 x_5 = (Struct38 {ir_is_rs_rel : (Bool)'(False), ir_msg :
            (x_0).in_msg, ir_msg_from : x_1, ir_mshr_id : (x_3).s_id,
            ir_by_victim : x_4});
            let x_6 <- enq_fifoN2I__0_0_3(x_5);
        end else begin
            
        end
    endrule
    
    rule rule_in_prs__0_0_3;
        let x_0 <- deq_fifoPInput__0_0_3();
        Bit#(4) x_1 = ((x_0).in_msg_from);
        when ((x_1) == ({((Bit#(2))'(2'h2)),((Bit#(2))'(2'h3))}),
        noAction);
        Struct1 x_2 = ((x_0).in_msg);
        when (((x_2).type_) && (! (((x_2).id) == ((Bit#(6))'(6'h16)))),
        noAction);
        let x_3 <- getULReady__0_0_3((x_2).addr);
        let x_4 <- startRelease__0_0_3(x_3);
        let x_5 <- victims___0_0_3__findVictim((x_2).addr);
        Struct38 x_6 = (Struct38 {ir_is_rs_rel : (Bool)'(False), ir_msg :
        (x_0).in_msg, ir_msg_from : x_1, ir_mshr_id : x_3, ir_by_victim :
        x_5});
        let x_7 <- enq_fifoN2I__0_0_3(x_6);
    endrule
    
    rule rule_in_retry__0_0_3;
        let x_0 <- getWait__0_0_3();
        Struct1 x_1 = ((x_0).r_msg);
        let x_2 <- victims___0_0_3__findVictim((x_1).addr);
        Struct38 x_3 = (Struct38 {ir_is_rs_rel : (Bool)'(False), ir_msg :
        x_1, ir_msg_from : (x_0).r_msg_from, ir_mshr_id : (x_0).r_id,
        ir_by_victim : x_2});
        let x_4 <- enq_fifoN2I__0_0_3(x_3);
    endrule
    
    rule rule_in_invrs__0_0_3;
        let x_0 <- deq_fifoPInput__0_0_3();
        Bit#(4) x_1 = ((x_0).in_msg_from);
        when ((x_1) == ({((Bit#(2))'(2'h2)),((Bit#(2))'(2'h3))}),
        noAction);
        Struct1 x_2 = ((x_0).in_msg);
        when (((x_2).type_) && (((x_2).id) == ((Bit#(6))'(6'h16))),
        noAction);
        let x_3 <- getULReady__0_0_3((x_2).addr);
        let x_4 <- victims___0_0_3__releaseVictim((x_2).addr);
        let x_5 <- releaseMSHR__0_0_3(x_3);
    endrule
    
    rule rule_in_crq__0_0_3;
        let x_0 <- deq_fifoCRqInput__0_0_3();
        Bit#(4) x_1 = ((x_0).in_msg_from);
        when (((x_1)[3:2]) == ((Bit#(2))'(2'h0)), noAction);
        Struct1 x_2 = ((x_0).in_msg);
        when (! ((x_2).type_), noAction);
        let x_3 <- victims___0_0_3__hasVictim();
        when (! (x_3), noAction);
        let x_4 <- getCRqSlot__0_0_3(Struct35 {r_id : unpack(0), r_msg : x_2,
        r_msg_from : x_1});
        when ((x_4).s_has_slot,
        noAction);
        if (! ((x_4).s_conflict)) begin
            let x_5 <- victims___0_0_3__findVictim((x_2).addr);
            Struct38 x_6 = (Struct38 {ir_is_rs_rel : (Bool)'(False), ir_msg :
            (x_0).in_msg, ir_msg_from : x_1, ir_mshr_id : (x_4).s_id,
            ir_by_victim : x_5});
            let x_7 <- enq_fifoN2I__0_0_3(x_6);
        end else begin
            
        end
    endrule
    
    rule rule_ir_cache__0_0_3;
        let x_0 <- deq_fifoN2I__0_0_3();
        when (! (((x_0).ir_by_victim).valid), noAction);
        Struct1 x_1 = ((x_0).ir_msg);
        let x_2 <- cache___0_0_3__infoRq((x_1).addr);
        let x_3 <- enq_fifoI2L__0_0_3(x_0);
    endrule
    
    rule rule_ir_victims__0_0_3;
        let x_0 <- deq_fifoN2I__0_0_3();
        when (((x_0).ir_by_victim).valid, noAction);
        let x_1 <- enq_fifoI2L__0_0_3(x_0);
    endrule
    
    rule rule_lr_cache__0_0_3;
        let x_0 <- deq_fifoI2L__0_0_3();
        when (! (((x_0).ir_by_victim).valid), noAction);
        let x_1 <- cache___0_0_3__infoRsValueRq(((x_0).ir_msg).addr);
        Struct41 x_2 = (Struct41 {lr_ir_pp : x_0, lr_ir : x_1, lr_value :
        unpack(0)});
        let x_3 <- enq_fifoL2E__0_0_3(x_2);
    endrule
    
    rule rule_lr_victims__0_0_3;
        let x_0 <- deq_fifoI2L__0_0_3();
        when (((x_0).ir_by_victim).valid, noAction);
        Bit#(1) x_1 = (((x_0).ir_by_victim).data);
        let x_2 <- victims___0_0_3__getVictim(x_1);
        Struct39 x_3 = (Struct39 {info_index : unpack(0), info_hit :
        unpack(0), info_way : unpack(0), edir_hit : unpack(0), edir_way :
        unpack(0), edir_slot : unpack(0), info : (x_2).victim_info,
        may_victim : unpack(0), reps : unpack(0)});
        Struct41 x_4 = (Struct41 {lr_ir_pp : x_0, lr_ir : x_3, lr_value :
        (x_2).victim_value});
        let x_5 <- enq_fifoL2E__0_0_3(x_4);
    endrule
    
    rule rule_exec__0_0_3__0_0;
        let x_0 <- deq_fifoL2E__0_0_3();
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
        let x_10 <- getMSHR__0_0_3(x_4);
        let x_11 <- getMSHRRq__0_0_3(x_4);
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
            let x_19 <- cache___0_0_3__valueRsLineRq(unpack(0));
            x_20 = x_19;
        end
        Struct18 x_21 = (Struct18 {enq_type : ((((Bit#(4))'(4'h8))[3:2]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : (((((Bit#(4))'(4'h8))[3:2])
        == ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : ((Bit#(4))'(4'h8))[1:0], enq_msg : Struct1 {id :
        (Bit#(6))'(6'h1), type_ : (Bool)'(True), addr : (x_17).addr, value :
        x_20}});
        let x_22 <- makeEnq_parentChildren_0_0_3(x_21);
        let x_23 <- releaseMSHR__0_0_3(x_4);
    endrule
    
    rule rule_exec__0_0_3__0_1;
        let x_0 <- deq_fifoL2E__0_0_3();
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
        let x_10 <- getMSHR__0_0_3(x_4);
        let x_11 <- getMSHRRq__0_0_3(x_4);
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
            let x_19 <- cache___0_0_3__valueRsLineRq(unpack(0));
            x_20 = x_19;
        end
        let x_21 <- registerUL__0_0_3(Struct43 {r_id : x_4, r_ul_rsb :
        (Bool)'(True), r_ul_rsbTo : ((Bit#(4))'(4'h8))[1:0]});
        Struct18 x_22 = (Struct18 {enq_type : ((((Bit#(4))'(4'h3))[3:2]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : (((((Bit#(4))'(4'h3))[3:2])
        == ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : ((Bit#(4))'(4'h3))[1:0], enq_msg : Struct1 {id :
        (Bit#(6))'(6'h2), type_ : (Bool)'(False), addr : (x_17).addr, value :
        unpack(0)}});
        let x_23 <- makeEnq_parentChildren_0_0_3(x_22);
    endrule
    
    rule rule_exec__0_0_3__0_2_0;
        let x_0 <- deq_fifoL2E__0_0_3();
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
        let x_10 <- getMSHR__0_0_3(x_4);
        let x_11 <- getMSHRRq__0_0_3(x_4);
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
            let x_23 <- victims___0_0_3__setVictim(Struct44 {victim_idx :
            (x_8).data, victim_info : (x_22).info, victim_value :
            ((x_22).value_write ? ((x_22).value) : (x_9))});
            x_25 = x_9;
        end else begin
            let x_24 <- cache___0_0_3__valueRsLineRq(x_22);
            x_25 = x_24;
        end
        let x_26 <- releaseMSHR__0_0_3(x_4);
        Struct18 x_27 = (Struct18 {enq_type : (((x_19)[3:2]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : ((((x_19)[3:2]) ==
        ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : (x_19)[1:0], enq_msg : Struct1 {id : (Bit#(6))'(6'h1),
        type_ : (Bool)'(True), addr : (x_17).addr, value :
        (x_17).value}});
        let x_28 <- makeEnq_parentChildren_0_0_3(x_27);
    endrule
    
    rule rule_exec__0_0_3__0_2_1;
        let x_0 <- deq_fifoL2E__0_0_3();
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
        let x_10 <- getMSHR__0_0_3(x_4);
        let x_11 <- getMSHRRq__0_0_3(x_4);
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
            let x_23 <- victims___0_0_3__setVictim(Struct44 {victim_idx :
            (x_8).data, victim_info : (x_22).info, victim_value :
            ((x_22).value_write ? ((x_22).value) : (x_9))});
            x_25 = x_9;
        end else begin
            let x_24 <- cache___0_0_3__valueRsLineRq(x_22);
            x_25 = x_24;
        end
        let x_26 <- releaseMSHR__0_0_3(x_4);
        Struct18 x_27 = (Struct18 {enq_type : (((x_19)[3:2]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : ((((x_19)[3:2]) ==
        ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : (x_19)[1:0], enq_msg : Struct1 {id : (Bit#(6))'(6'h1),
        type_ : (Bool)'(True), addr : (x_17).addr, value :
        (x_17).value}});
        let x_28 <- makeEnq_parentChildren_0_0_3(x_27);
    endrule
    
    rule rule_exec__0_0_3__0_3;
        let x_0 <- deq_fifoL2E__0_0_3();
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
        let x_10 <- getMSHR__0_0_3(x_4);
        let x_11 <- getMSHRRq__0_0_3(x_4);
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
            let x_21 <- victims___0_0_3__setVictim(Struct44 {victim_idx :
            (x_8).data, victim_info : (x_20).info, victim_value :
            ((x_20).value_write ? ((x_20).value) : (x_9))});
            x_23 = x_9;
        end else begin
            let x_22 <- cache___0_0_3__valueRsLineRq(x_20);
            x_23 = x_22;
        end
        Struct18 x_24 = (Struct18 {enq_type : ((((Bit#(4))'(4'h7))[3:2]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : (((((Bit#(4))'(4'h7))[3:2])
        == ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : ((Bit#(4))'(4'h7))[1:0], enq_msg : Struct1 {id :
        (Bit#(6))'(6'h6), type_ : (Bool)'(True), addr : (x_17).addr, value :
        x_23}});
        let x_25 <- makeEnq_parentChildren_0_0_3(x_24);
        let x_26 <- releaseMSHR__0_0_3(x_4);
    endrule
    
    rule rule_exec__0_0_3__1_0_0;
        let x_0 <- deq_fifoL2E__0_0_3();
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
        let x_10 <- getMSHR__0_0_3(x_4);
        let x_11 <- getMSHRRq__0_0_3(x_4);
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
            let x_22 <- victims___0_0_3__setVictim(Struct44 {victim_idx :
            (x_8).data, victim_info : (x_21).info, victim_value :
            ((x_21).value_write ? ((x_21).value) : (x_9))});
            x_24 = x_9;
        end else begin
            let x_23 <- cache___0_0_3__valueRsLineRq(x_21);
            x_24 = x_23;
        end
        Struct18 x_25 = (Struct18 {enq_type : ((((Bit#(4))'(4'h8))[3:2]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : (((((Bit#(4))'(4'h8))[3:2])
        == ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : ((Bit#(4))'(4'h8))[1:0], enq_msg : Struct1 {id :
        (Bit#(6))'(6'h9), type_ : (Bool)'(True), addr : (x_17).addr, value :
        unpack(0)}});
        let x_26 <- makeEnq_parentChildren_0_0_3(x_25);
        let x_27 <- releaseMSHR__0_0_3(x_4);
    endrule
    
    rule rule_exec__0_0_3__1_0_1;
        let x_0 <- deq_fifoL2E__0_0_3();
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
        let x_10 <- getMSHR__0_0_3(x_4);
        let x_11 <- getMSHRRq__0_0_3(x_4);
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
            let x_20 <- victims___0_0_3__setVictim(Struct44 {victim_idx :
            (x_8).data, victim_info : (x_19).info, victim_value :
            ((x_19).value_write ? ((x_19).value) : (x_9))});
            x_22 = x_9;
        end else begin
            let x_21 <- cache___0_0_3__valueRsLineRq(x_19);
            x_22 = x_21;
        end
        Struct18 x_23 = (Struct18 {enq_type : ((((Bit#(4))'(4'h8))[3:2]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : (((((Bit#(4))'(4'h8))[3:2])
        == ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : ((Bit#(4))'(4'h8))[1:0], enq_msg : Struct1 {id :
        (Bit#(6))'(6'h9), type_ : (Bool)'(True), addr : (x_17).addr, value :
        unpack(0)}});
        let x_24 <- makeEnq_parentChildren_0_0_3(x_23);
        let x_25 <- releaseMSHR__0_0_3(x_4);
    endrule
    
    rule rule_exec__0_0_3__1_1;
        let x_0 <- deq_fifoL2E__0_0_3();
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
        let x_10 <- getMSHR__0_0_3(x_4);
        let x_11 <- getMSHRRq__0_0_3(x_4);
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
            let x_19 <- cache___0_0_3__valueRsLineRq(unpack(0));
            x_20 = x_19;
        end
        let x_21 <- registerUL__0_0_3(Struct43 {r_id : x_4, r_ul_rsb :
        (Bool)'(True), r_ul_rsbTo : ((Bit#(4))'(4'h8))[1:0]});
        Struct18 x_22 = (Struct18 {enq_type : ((((Bit#(4))'(4'h3))[3:2]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : (((((Bit#(4))'(4'h3))[3:2])
        == ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : ((Bit#(4))'(4'h3))[1:0], enq_msg : Struct1 {id :
        (Bit#(6))'(6'ha), type_ : (Bool)'(False), addr : (x_17).addr, value :
        unpack(0)}});
        let x_23 <- makeEnq_parentChildren_0_0_3(x_22);
    endrule
    
    rule rule_exec__0_0_3__1_2;
        let x_0 <- deq_fifoL2E__0_0_3();
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
        let x_10 <- getMSHR__0_0_3(x_4);
        let x_11 <- getMSHRRq__0_0_3(x_4);
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
            let x_24 <- victims___0_0_3__setVictim(Struct44 {victim_idx :
            (x_8).data, victim_info : (x_23).info, victim_value :
            ((x_23).value_write ? ((x_23).value) : (x_9))});
            x_26 = x_9;
        end else begin
            let x_25 <- cache___0_0_3__valueRsLineRq(x_23);
            x_26 = x_25;
        end
        let x_27 <- releaseMSHR__0_0_3(x_4);
        Struct18 x_28 = (Struct18 {enq_type : (((x_19)[3:2]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : ((((x_19)[3:2]) ==
        ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : (x_19)[1:0], enq_msg : Struct1 {id : (Bit#(6))'(6'h9),
        type_ : (Bool)'(True), addr : (x_17).addr, value : unpack(0)}});
        let x_29 <- makeEnq_parentChildren_0_0_3(x_28);
    endrule
    
    rule rule_exec__0_0_3__1_3_0;
        let x_0 <- deq_fifoL2E__0_0_3();
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
        let x_10 <- getMSHR__0_0_3(x_4);
        let x_11 <- getMSHRRq__0_0_3(x_4);
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
            let x_21 <- victims___0_0_3__setVictim(Struct44 {victim_idx :
            (x_8).data, victim_info : (x_20).info, victim_value :
            ((x_20).value_write ? ((x_20).value) : (x_9))});
            x_23 = x_9;
        end else begin
            let x_22 <- cache___0_0_3__valueRsLineRq(x_20);
            x_23 = x_22;
        end
        Struct18 x_24 = (Struct18 {enq_type : ((((Bit#(4))'(4'h7))[3:2]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : (((((Bit#(4))'(4'h7))[3:2])
        == ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : ((Bit#(4))'(4'h7))[1:0], enq_msg : Struct1 {id :
        (Bit#(6))'(6'hd), type_ : (Bool)'(True), addr : (x_17).addr, value :
        unpack(0)}});
        let x_25 <- makeEnq_parentChildren_0_0_3(x_24);
        let x_26 <- releaseMSHR__0_0_3(x_4);
    endrule
    
    rule rule_exec__0_0_3__1_3_1;
        let x_0 <- deq_fifoL2E__0_0_3();
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
        let x_10 <- getMSHR__0_0_3(x_4);
        let x_11 <- getMSHRRq__0_0_3(x_4);
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
            let x_21 <- victims___0_0_3__setVictim(Struct44 {victim_idx :
            (x_8).data, victim_info : (x_20).info, victim_value :
            ((x_20).value_write ? ((x_20).value) : (x_9))});
            x_23 = x_9;
        end else begin
            let x_22 <- cache___0_0_3__valueRsLineRq(x_20);
            x_23 = x_22;
        end
        Struct18 x_24 = (Struct18 {enq_type : ((((Bit#(4))'(4'h7))[3:2]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : (((((Bit#(4))'(4'h7))[3:2])
        == ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : ((Bit#(4))'(4'h7))[1:0], enq_msg : Struct1 {id :
        (Bit#(6))'(6'hf), type_ : (Bool)'(True), addr : (x_17).addr, value :
        unpack(0)}});
        let x_25 <- makeEnq_parentChildren_0_0_3(x_24);
        let x_26 <- releaseMSHR__0_0_3(x_4);
    endrule
    
    rule rule_exec__0_0_3__2_0;
        let x_0 <- victims___0_0_3__getFirstVictim();
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
        let x_13 <- makeEnq_parentChildren_0_0_3(x_12);
        let x_14 <- setULImm__0_0_3(x_4);
        let x_15 <- victims___0_0_3__setVictimRq(x_1);
    endrule
    
    rule rule_exec__0_0_3__2_1;
        let x_0 <- victims___0_0_3__getFirstVictim();
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
        let x_13 <- makeEnq_parentChildren_0_0_3(x_12);
        let x_14 <- setULImm__0_0_3(x_4);
        let x_15 <- victims___0_0_3__setVictimRq(x_1);
    endrule
    
    // No methods in this module
endmodule

// The CC interface is defined in the header part (thus in Header.bsv)

module mkCC#(function ActionValue#(Struct1) deq_fifo_0_0_2(),
function Action enq_fifo_0_0_1(Struct1 _),
function Action enq_fifo_0_0_0(Struct1 _)) (CC);
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
    Module107 m107 <- mkModule107 (m94.deq_fifo_0_0_3_0,
    m76.deq_fifo_0_0_2_0, m58.deq_fifo_0_0_1_0, m1.enq_fifoCRqInput__0_0,
    m40.deq_fifo_0_0_0_0);
    Module108 m108 <- mkModule108 (m95.deq_fifo_0_0_3_1,
    m77.deq_fifo_0_0_2_1, m59.deq_fifo_0_0_1_1, m2.enq_fifoCRsInput__0_0,
    m41.deq_fifo_0_0_0_1);
    Module109 m109 <- mkModule109 (m3.enq_fifoPInput__0_0, deq_fifo_0_0_2);
    
    Module110 m110 <- mkModule110 (m42.enq_fifo_0_0_0_2,
    m60.enq_fifo_0_0_1_2, m78.enq_fifo_0_0_2_2, m96.enq_fifo_0_0_3_2,
    enq_fifo_0_0_1, enq_fifo_0_0_0);
    Module111 m111 <- mkModule111 (m33.wrReq_repRam___0_0,
    m33.rdResp_repRam___0_0, m33.rdReq_repRam___0_0);
    Module112 m112 <- mkModule112 (m35.enq_fifoCRqInput__0_0_0,
    m43.deq_fifo_0_0_0_0_0);
    Module113 m113 <- mkModule113 (m36.enq_fifoPInput__0_0_0,
    m42.deq_fifo_0_0_0_2);
    Module114 m114 <- mkModule114 (m44.enq_fifo_0_0_0_0_2,
    m41.enq_fifo_0_0_0_1, m40.enq_fifo_0_0_0_0);
    Module115 m115 <- mkModule115 (m51.wrReq_repRam___0_0_0,
    m51.rdResp_repRam___0_0_0, m51.rdReq_repRam___0_0_0);
    Module116 m116 <- mkModule116 (m53.enq_fifoCRqInput__0_0_1,
    m61.deq_fifo_0_0_1_0_0);
    Module117 m117 <- mkModule117 (m54.enq_fifoPInput__0_0_1,
    m60.deq_fifo_0_0_1_2);
    Module118 m118 <- mkModule118 (m62.enq_fifo_0_0_1_0_2,
    m59.enq_fifo_0_0_1_1, m58.enq_fifo_0_0_1_0);
    Module119 m119 <- mkModule119 (m69.wrReq_repRam___0_0_1,
    m69.rdResp_repRam___0_0_1, m69.rdReq_repRam___0_0_1);
    Module120 m120 <- mkModule120 (m71.enq_fifoCRqInput__0_0_2,
    m79.deq_fifo_0_0_2_0_0);
    Module121 m121 <- mkModule121 (m72.enq_fifoPInput__0_0_2,
    m78.deq_fifo_0_0_2_2);
    Module122 m122 <- mkModule122 (m80.enq_fifo_0_0_2_0_2,
    m77.enq_fifo_0_0_2_1, m76.enq_fifo_0_0_2_0);
    Module123 m123 <- mkModule123 (m87.wrReq_repRam___0_0_2,
    m87.rdResp_repRam___0_0_2, m87.rdReq_repRam___0_0_2);
    Module124 m124 <- mkModule124 (m89.enq_fifoCRqInput__0_0_3,
    m97.deq_fifo_0_0_3_0_0);
    Module125 m125 <- mkModule125 (m90.enq_fifoPInput__0_0_3,
    m96.deq_fifo_0_0_3_2);
    Module126 m126 <- mkModule126 (m98.enq_fifo_0_0_3_0_2,
    m95.enq_fifo_0_0_3_1, m94.enq_fifo_0_0_3_0);
    Module127 m127 <- mkModule127 (m105.wrReq_repRam___0_0_3,
    m105.rdResp_repRam___0_0_3, m105.rdReq_repRam___0_0_3);
    Module128 m128 <- mkModule128 (m32.wrReq_dataRam___0_0,
    m24.wrReq_edirRam___0_0__7, m25.wrReq_edirRam___0_0__6,
    m26.wrReq_edirRam___0_0__5, m27.wrReq_edirRam___0_0__4,
    m28.wrReq_edirRam___0_0__3, m29.wrReq_edirRam___0_0__2,
    m30.wrReq_edirRam___0_0__1, m31.wrReq_edirRam___0_0__0,
    m111.repAccess___0_0, m7.victims___0_0__registerVictim,
    m8.wrReq_infoRam___0_0__15, m9.wrReq_infoRam___0_0__14,
    m10.wrReq_infoRam___0_0__13, m11.wrReq_infoRam___0_0__12,
    m12.wrReq_infoRam___0_0__11, m13.wrReq_infoRam___0_0__10,
    m14.wrReq_infoRam___0_0__9, m15.wrReq_infoRam___0_0__8,
    m16.wrReq_infoRam___0_0__7, m17.wrReq_infoRam___0_0__6,
    m18.wrReq_infoRam___0_0__5, m19.wrReq_infoRam___0_0__4,
    m20.wrReq_infoRam___0_0__3, m21.wrReq_infoRam___0_0__2,
    m22.wrReq_infoRam___0_0__1, m23.wrReq_infoRam___0_0__0,
    m32.rdResp_dataRam___0_0, m32.rdReq_dataRam___0_0, m111.repGetRs___0_0,
    m24.rdResp_edirRam___0_0__7, m25.rdResp_edirRam___0_0__6,
    m26.rdResp_edirRam___0_0__5, m27.rdResp_edirRam___0_0__4,
    m28.rdResp_edirRam___0_0__3, m29.rdResp_edirRam___0_0__2,
    m30.rdResp_edirRam___0_0__1, m31.rdResp_edirRam___0_0__0,
    m8.rdResp_infoRam___0_0__15, m9.rdResp_infoRam___0_0__14,
    m10.rdResp_infoRam___0_0__13, m11.rdResp_infoRam___0_0__12,
    m12.rdResp_infoRam___0_0__11, m13.rdResp_infoRam___0_0__10,
    m14.rdResp_infoRam___0_0__9, m15.rdResp_infoRam___0_0__8,
    m16.rdResp_infoRam___0_0__7, m17.rdResp_infoRam___0_0__6,
    m18.rdResp_infoRam___0_0__5, m19.rdResp_infoRam___0_0__4,
    m20.rdResp_infoRam___0_0__3, m21.rdResp_infoRam___0_0__2,
    m22.rdResp_infoRam___0_0__1, m23.rdResp_infoRam___0_0__0,
    m111.repGetRq___0_0, m24.rdReq_edirRam___0_0__7,
    m25.rdReq_edirRam___0_0__6, m26.rdReq_edirRam___0_0__5,
    m27.rdReq_edirRam___0_0__4, m28.rdReq_edirRam___0_0__3,
    m29.rdReq_edirRam___0_0__2, m30.rdReq_edirRam___0_0__1,
    m31.rdReq_edirRam___0_0__0, m8.rdReq_infoRam___0_0__15,
    m9.rdReq_infoRam___0_0__14, m10.rdReq_infoRam___0_0__13,
    m11.rdReq_infoRam___0_0__12, m12.rdReq_infoRam___0_0__11,
    m13.rdReq_infoRam___0_0__10, m14.rdReq_infoRam___0_0__9,
    m15.rdReq_infoRam___0_0__8, m16.rdReq_infoRam___0_0__7,
    m17.rdReq_infoRam___0_0__6, m18.rdReq_infoRam___0_0__5,
    m19.rdReq_infoRam___0_0__4, m20.rdReq_infoRam___0_0__3,
    m21.rdReq_infoRam___0_0__2, m22.rdReq_infoRam___0_0__1,
    m23.rdReq_infoRam___0_0__0);
    Module129 m129 <- mkModule129 (m50.wrReq_dataRam___0_0_0,
    m115.repAccess___0_0_0, m45.victims___0_0_0__registerVictim,
    m46.wrReq_infoRam___0_0_0__3, m47.wrReq_infoRam___0_0_0__2,
    m48.wrReq_infoRam___0_0_0__1, m49.wrReq_infoRam___0_0_0__0,
    m50.rdResp_dataRam___0_0_0, m50.rdReq_dataRam___0_0_0,
    m115.repGetRs___0_0_0, m46.rdResp_infoRam___0_0_0__3,
    m47.rdResp_infoRam___0_0_0__2, m48.rdResp_infoRam___0_0_0__1,
    m49.rdResp_infoRam___0_0_0__0, m115.repGetRq___0_0_0,
    m46.rdReq_infoRam___0_0_0__3, m47.rdReq_infoRam___0_0_0__2,
    m48.rdReq_infoRam___0_0_0__1, m49.rdReq_infoRam___0_0_0__0);
    Module130 m130 <- mkModule130 (m68.wrReq_dataRam___0_0_1,
    m119.repAccess___0_0_1, m63.victims___0_0_1__registerVictim,
    m64.wrReq_infoRam___0_0_1__3, m65.wrReq_infoRam___0_0_1__2,
    m66.wrReq_infoRam___0_0_1__1, m67.wrReq_infoRam___0_0_1__0,
    m68.rdResp_dataRam___0_0_1, m68.rdReq_dataRam___0_0_1,
    m119.repGetRs___0_0_1, m64.rdResp_infoRam___0_0_1__3,
    m65.rdResp_infoRam___0_0_1__2, m66.rdResp_infoRam___0_0_1__1,
    m67.rdResp_infoRam___0_0_1__0, m119.repGetRq___0_0_1,
    m64.rdReq_infoRam___0_0_1__3, m65.rdReq_infoRam___0_0_1__2,
    m66.rdReq_infoRam___0_0_1__1, m67.rdReq_infoRam___0_0_1__0);
    Module131 m131 <- mkModule131 (m86.wrReq_dataRam___0_0_2,
    m123.repAccess___0_0_2, m81.victims___0_0_2__registerVictim,
    m82.wrReq_infoRam___0_0_2__3, m83.wrReq_infoRam___0_0_2__2,
    m84.wrReq_infoRam___0_0_2__1, m85.wrReq_infoRam___0_0_2__0,
    m86.rdResp_dataRam___0_0_2, m86.rdReq_dataRam___0_0_2,
    m123.repGetRs___0_0_2, m82.rdResp_infoRam___0_0_2__3,
    m83.rdResp_infoRam___0_0_2__2, m84.rdResp_infoRam___0_0_2__1,
    m85.rdResp_infoRam___0_0_2__0, m123.repGetRq___0_0_2,
    m82.rdReq_infoRam___0_0_2__3, m83.rdReq_infoRam___0_0_2__2,
    m84.rdReq_infoRam___0_0_2__1, m85.rdReq_infoRam___0_0_2__0);
    Module132 m132 <- mkModule132 (m104.wrReq_dataRam___0_0_3,
    m127.repAccess___0_0_3, m99.victims___0_0_3__registerVictim,
    m100.wrReq_infoRam___0_0_3__3, m101.wrReq_infoRam___0_0_3__2,
    m102.wrReq_infoRam___0_0_3__1, m103.wrReq_infoRam___0_0_3__0,
    m104.rdResp_dataRam___0_0_3, m104.rdReq_dataRam___0_0_3,
    m127.repGetRs___0_0_3, m100.rdResp_infoRam___0_0_3__3,
    m101.rdResp_infoRam___0_0_3__2, m102.rdResp_infoRam___0_0_3__1,
    m103.rdResp_infoRam___0_0_3__0, m127.repGetRq___0_0_3,
    m100.rdReq_infoRam___0_0_3__3, m101.rdReq_infoRam___0_0_3__2,
    m102.rdReq_infoRam___0_0_3__1, m103.rdReq_infoRam___0_0_3__0);
    Module133 m133 <- mkModule133 (m34.canImm__0_0,
    m7.victims___0_0__setVictimRq, m34.setULImm__0_0,
    m7.victims___0_0__getFirstVictim, m34.transferUpDown__0_0,
    m34.getMSHRFirstRs__0_0, m110.broadcast_parentChildren_0_0,
    m34.registerDL__0_0, m34.registerUL__0_0,
    m110.makeEnq_parentChildren_0_0, m128.cache___0_0__valueRsLineRq,
    m7.victims___0_0__setVictim, m34.getMSHRRq__0_0, m34.getMSHR__0_0,
    m6.deq_fifoL2E__0_0, m7.victims___0_0__getVictim, m6.enq_fifoL2E__0_0,
    m128.cache___0_0__infoRsValueRq, m5.deq_fifoI2L__0_0,
    m5.enq_fifoI2L__0_0, m128.cache___0_0__infoRq, m4.deq_fifoN2I__0_0,
    m34.getDLReady__0_0, m34.addRs__0_0, m2.deq_fifoCRsInput__0_0,
    m34.getCRqSlot__0_0, m7.victims___0_0__hasVictim,
    m1.deq_fifoCRqInput__0_0, m34.releaseMSHR__0_0,
    m7.victims___0_0__releaseVictim, m34.getWait__0_0, m34.startRelease__0_0,
    m34.getULReady__0_0, m4.enq_fifoN2I__0_0, m7.victims___0_0__findVictim,
    m34.getPRqSlot__0_0, m3.deq_fifoPInput__0_0);
    Module134 m134 <- mkModule134 (m45.victims___0_0_0__setVictimRq,
    m52.setULImm__0_0_0, m45.victims___0_0_0__getFirstVictim,
    m45.victims___0_0_0__setVictim, m52.registerUL__0_0_0,
    m114.makeEnq_parentChildren_0_0_0, m129.cache___0_0_0__valueRsLineRq,
    m52.getMSHRRq__0_0_0, m52.getMSHR__0_0_0, m39.deq_fifoL2E__0_0_0,
    m45.victims___0_0_0__getVictim, m39.enq_fifoL2E__0_0_0,
    m129.cache___0_0_0__infoRsValueRq, m38.deq_fifoI2L__0_0_0,
    m38.enq_fifoI2L__0_0_0, m129.cache___0_0_0__infoRq,
    m37.deq_fifoN2I__0_0_0, m52.getCRqSlot__0_0_0,
    m45.victims___0_0_0__hasVictim, m35.deq_fifoCRqInput__0_0_0,
    m52.releaseMSHR__0_0_0, m45.victims___0_0_0__releaseVictim,
    m52.getWait__0_0_0, m52.startRelease__0_0_0, m52.getULReady__0_0_0,
    m37.enq_fifoN2I__0_0_0, m45.victims___0_0_0__findVictim,
    m52.getPRqSlot__0_0_0, m36.deq_fifoPInput__0_0_0);
    Module135 m135 <- mkModule135 (m63.victims___0_0_1__setVictimRq,
    m70.setULImm__0_0_1, m63.victims___0_0_1__getFirstVictim,
    m63.victims___0_0_1__setVictim, m70.registerUL__0_0_1,
    m118.makeEnq_parentChildren_0_0_1, m130.cache___0_0_1__valueRsLineRq,
    m70.getMSHRRq__0_0_1, m70.getMSHR__0_0_1, m57.deq_fifoL2E__0_0_1,
    m63.victims___0_0_1__getVictim, m57.enq_fifoL2E__0_0_1,
    m130.cache___0_0_1__infoRsValueRq, m56.deq_fifoI2L__0_0_1,
    m56.enq_fifoI2L__0_0_1, m130.cache___0_0_1__infoRq,
    m55.deq_fifoN2I__0_0_1, m70.getCRqSlot__0_0_1,
    m63.victims___0_0_1__hasVictim, m53.deq_fifoCRqInput__0_0_1,
    m70.releaseMSHR__0_0_1, m63.victims___0_0_1__releaseVictim,
    m70.getWait__0_0_1, m70.startRelease__0_0_1, m70.getULReady__0_0_1,
    m55.enq_fifoN2I__0_0_1, m63.victims___0_0_1__findVictim,
    m70.getPRqSlot__0_0_1, m54.deq_fifoPInput__0_0_1);
    Module136 m136 <- mkModule136 (m81.victims___0_0_2__setVictimRq,
    m88.setULImm__0_0_2, m81.victims___0_0_2__getFirstVictim,
    m81.victims___0_0_2__setVictim, m88.registerUL__0_0_2,
    m122.makeEnq_parentChildren_0_0_2, m131.cache___0_0_2__valueRsLineRq,
    m88.getMSHRRq__0_0_2, m88.getMSHR__0_0_2, m75.deq_fifoL2E__0_0_2,
    m81.victims___0_0_2__getVictim, m75.enq_fifoL2E__0_0_2,
    m131.cache___0_0_2__infoRsValueRq, m74.deq_fifoI2L__0_0_2,
    m74.enq_fifoI2L__0_0_2, m131.cache___0_0_2__infoRq,
    m73.deq_fifoN2I__0_0_2, m88.getCRqSlot__0_0_2,
    m81.victims___0_0_2__hasVictim, m71.deq_fifoCRqInput__0_0_2,
    m88.releaseMSHR__0_0_2, m81.victims___0_0_2__releaseVictim,
    m88.getWait__0_0_2, m88.startRelease__0_0_2, m88.getULReady__0_0_2,
    m73.enq_fifoN2I__0_0_2, m81.victims___0_0_2__findVictim,
    m88.getPRqSlot__0_0_2, m72.deq_fifoPInput__0_0_2);
    Module137 m137 <- mkModule137 (m99.victims___0_0_3__setVictimRq,
    m106.setULImm__0_0_3, m99.victims___0_0_3__getFirstVictim,
    m99.victims___0_0_3__setVictim, m106.registerUL__0_0_3,
    m126.makeEnq_parentChildren_0_0_3, m132.cache___0_0_3__valueRsLineRq,
    m106.getMSHRRq__0_0_3, m106.getMSHR__0_0_3, m93.deq_fifoL2E__0_0_3,
    m99.victims___0_0_3__getVictim, m93.enq_fifoL2E__0_0_3,
    m132.cache___0_0_3__infoRsValueRq, m92.deq_fifoI2L__0_0_3,
    m92.enq_fifoI2L__0_0_3, m132.cache___0_0_3__infoRq,
    m91.deq_fifoN2I__0_0_3, m106.getCRqSlot__0_0_3,
    m99.victims___0_0_3__hasVictim, m89.deq_fifoCRqInput__0_0_3,
    m106.releaseMSHR__0_0_3, m99.victims___0_0_3__releaseVictim,
    m106.getWait__0_0_3, m106.startRelease__0_0_3, m106.getULReady__0_0_3,
    m91.enq_fifoN2I__0_0_3, m99.victims___0_0_3__findVictim,
    m106.getPRqSlot__0_0_3, m90.deq_fifoPInput__0_0_3);
    //// Interface

    function MemRqRs#(Struct1) getMemRqRs (function Action enq_rq (Struct1 _),
                                           function ActionValue#(Struct1) deq_rs ());
        return interface MemRqRs;
                   method mem_enq_rq = enq_rq;
                   method mem_deq_rs = deq_rs;
               endinterface;
    endfunction

    Vector#(L1Num, MemRqRs#(Struct1)) _l1Ifc = newVector();
    _l1Ifc[0] = getMemRqRs(m43.enq_fifo_0_0_0_0_0, m44.deq_fifo_0_0_0_0_2);
    _l1Ifc[1] = getMemRqRs(m61.enq_fifo_0_0_1_0_0, m62.deq_fifo_0_0_1_0_2);
    _l1Ifc[2] = getMemRqRs(m79.enq_fifo_0_0_2_0_0, m80.deq_fifo_0_0_2_0_2);
    _l1Ifc[3] = getMemRqRs(m97.enq_fifo_0_0_3_0_0, m98.deq_fifo_0_0_3_0_2);
    interface l1Ifc = _l1Ifc;

    interface DMA llDma;
        method dma_rdReq = m32.rdReq_dataRam___0_0;
        method dma_wrReq = m32.wrReq_dataRam___0_0;
        method dma_rdResp = m32.rdResp_dataRam___0_0;
    endinterface

endmodule
