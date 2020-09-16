import Vector::*;
import BuildVector::*;
import FIFO::*;
import FIFOF::*;
import RWBramCore::*;
import SpecialFIFOs::*;
import HCCIfc::*;

interface CC;
    interface Vector#(L1Num, MemRqRs#(Struct1)) l1Ifc;
    interface DMA#(Bit#(12), Struct35, Vector#(4, Bit#(64))) llDma;
endinterface

typedef struct { Bit#(6) id; Bool type_; Bit#(64) addr; Vector#(4, Bit#(64)) value;  } Struct1 deriving(Eq, Bits);
typedef struct { Bit#(9) info_index; Bool info_hit; Bit#(3) info_way; Bool edir_hit; Bit#(2) edir_way; Struct6 edir_slot; Struct11 info; Struct12 may_victim; Vector#(8, Bit#(8)) reps;  } Struct10 deriving(Eq, Bits);
typedef struct { Bool mesi_owned; Bit#(3) mesi_status; Bit#(3) mesi_dir_st; Bit#(2) mesi_dir_sharers;  } Struct11 deriving(Eq, Bits);
typedef struct { Bit#(64) mv_addr; Struct11 mv_info;  } Struct12 deriving(Eq, Bits);
typedef struct { Struct7 lr_ir_pp; Struct10 lr_ir; Vector#(4, Bit#(64)) lr_value;  } Struct13 deriving(Eq, Bits);
typedef struct { Bool victim_valid; Bit#(64) victim_addr; Struct11 victim_info; Vector#(4, Bit#(64)) victim_value; Struct15 victim_req;  } Struct14 deriving(Eq, Bits);
typedef struct { Bool valid; Bit#(4) data;  } Struct15 deriving(Eq, Bits);
typedef struct { Bool valid; Struct4 data;  } Struct16 deriving(Eq, Bits);
typedef struct { Bit#(3) m_status; Struct15 m_next; Bool m_is_ul; Struct1 m_msg; Bit#(3) m_qidx; Bool m_rsb; Bit#(2) m_dl_rss_from; Bit#(2) m_dl_rss_recv; Vector#(2, Struct1) m_dl_rss;  } Struct17 deriving(Eq, Bits);
typedef struct { Bit#(3) dir_st; Bit#(1) dir_excl; Bit#(2) dir_sharers;  } Struct18 deriving(Eq, Bits);
typedef struct { Bit#(64) addr; Bool info_write; Bool info_hit; Bit#(3) info_way; Bool edir_hit; Bit#(2) edir_way; Struct6 edir_slot; Struct11 info; Bool value_write; Vector#(4, Bit#(64)) value; Struct12 may_victim; Vector#(8, Bit#(8)) reps;  } Struct19 deriving(Eq, Bits);
typedef struct { Struct1 in_msg; Bit#(3) in_msg_from;  } Struct2 deriving(Eq, Bits);
typedef struct { Bit#(2) victim_idx; Struct11 victim_info; Vector#(4, Bit#(64)) victim_value;  } Struct20 deriving(Eq, Bits);
typedef struct { Bit#(2) enq_type; Bit#(1) enq_ch_idx; Struct1 enq_msg;  } Struct21 deriving(Eq, Bits);
typedef struct { Bit#(4) r_id; Bool r_ul_rsb; Bit#(1) r_ul_rsbTo;  } Struct22 deriving(Eq, Bits);
typedef struct { Bit#(4) r_id; Bit#(2) r_dl_rss_from; Bool r_dl_rsb; Bit#(3) r_dl_rsbTo;  } Struct23 deriving(Eq, Bits);
typedef struct { Bit#(2) cs_inds; Struct1 cs_msg;  } Struct24 deriving(Eq, Bits);
typedef struct { Bit#(3) cidx; Struct1 msg;  } Struct25 deriving(Eq, Bits);
typedef struct { Bit#(4) r_id; Bit#(2) r_dl_rss_from;  } Struct26 deriving(Eq, Bits);
typedef struct { Bit#(64) victim_addr; Bit#(4) victim_req;  } Struct27 deriving(Eq, Bits);
typedef struct { Bit#(50) tag; Struct11 value;  } Struct28 deriving(Eq, Bits);
typedef struct { Bool tm_hit; Bit#(3) tm_way; Struct11 tm_value;  } Struct29 deriving(Eq, Bits);
typedef struct { Bit#(1) ch_idx; Struct1 ch_msg;  } Struct3 deriving(Eq, Bits);
typedef struct { Bit#(50) tag; Struct31 value;  } Struct30 deriving(Eq, Bits);
typedef struct { Bit#(3) mesi_edir_st; Bit#(2) mesi_edir_sharers;  } Struct31 deriving(Eq, Bits);
typedef struct { Bool tm_hit; Bit#(2) tm_way; Struct31 tm_value;  } Struct32 deriving(Eq, Bits);
typedef struct { Bit#(9) addr; Struct28 datain;  } Struct33 deriving(Eq, Bits);
typedef struct { Bit#(1) acc_type; Vector#(8, Bit#(8)) acc_reps; Bit#(9) acc_index; Bit#(3) acc_way;  } Struct34 deriving(Eq, Bits);
typedef struct { Bit#(12) addr; Vector#(4, Bit#(64)) datain;  } Struct35 deriving(Eq, Bits);
typedef struct { Bit#(9) addr; Struct30 datain;  } Struct36 deriving(Eq, Bits);
typedef struct { Bool valid; Struct14 data;  } Struct37 deriving(Eq, Bits);
typedef struct { Bit#(9) addr; Vector#(8, Bit#(8)) datain;  } Struct38 deriving(Eq, Bits);
typedef struct { Bit#(3) r_id; Struct1 r_msg; Bit#(3) r_msg_from;  } Struct39 deriving(Eq, Bits);
typedef struct { Bit#(4) r_id; Struct1 r_msg; Bit#(3) r_msg_from;  } Struct4 deriving(Eq, Bits);
typedef struct { Bool s_has_slot; Bool s_conflict; Bit#(3) s_id;  } Struct40 deriving(Eq, Bits);
typedef struct { Bool valid; Bit#(1) data;  } Struct41 deriving(Eq, Bits);
typedef struct { Bool ir_is_rs_rel; Bool ir_is_rs_acc; Struct1 ir_msg; Bit#(3) ir_msg_from; Bit#(3) ir_mshr_id; Struct41 ir_by_victim;  } Struct42 deriving(Eq, Bits);
typedef struct { Bit#(3) r_id; Bit#(64) r_addr;  } Struct43 deriving(Eq, Bits);
typedef struct { Bit#(3) r_id; Bit#(1) r_midx; Struct1 r_msg;  } Struct44 deriving(Eq, Bits);
typedef struct { Bit#(8) info_index; Bool info_hit; Bit#(2) info_way; Bool edir_hit; void edir_way; Struct46 edir_slot; Struct11 info; Struct12 may_victim; Vector#(4, Bit#(8)) reps;  } Struct45 deriving(Eq, Bits);
typedef struct { Bool valid; void data;  } Struct46 deriving(Eq, Bits);
typedef struct { Struct42 lr_ir_pp; Struct45 lr_ir; Vector#(4, Bit#(64)) lr_value;  } Struct47 deriving(Eq, Bits);
typedef struct { Bool victim_valid; Bit#(64) victim_addr; Struct11 victim_info; Vector#(4, Bit#(64)) victim_value; Struct49 victim_req;  } Struct48 deriving(Eq, Bits);
typedef struct { Bool valid; Bit#(3) data;  } Struct49 deriving(Eq, Bits);
typedef struct { Bool s_has_slot; Bool s_conflict; Bit#(4) s_id;  } Struct5 deriving(Eq, Bits);
typedef struct { Bool valid; Struct39 data;  } Struct50 deriving(Eq, Bits);
typedef struct { Bit#(3) m_status; Struct49 m_next; Bool m_is_ul; Struct1 m_msg; Bit#(3) m_qidx; Bool m_rsb; Bit#(2) m_dl_rss_from; Bit#(2) m_dl_rss_recv; Vector#(2, Struct1) m_dl_rss;  } Struct51 deriving(Eq, Bits);
typedef struct { Bit#(64) addr; Bool info_write; Bool info_hit; Bit#(2) info_way; Bool edir_hit; void edir_way; Struct46 edir_slot; Struct11 info; Bool value_write; Vector#(4, Bit#(64)) value; Struct12 may_victim; Vector#(4, Bit#(8)) reps;  } Struct52 deriving(Eq, Bits);
typedef struct { Bit#(3) r_id; Bool r_ul_rsb; Bit#(1) r_ul_rsbTo;  } Struct53 deriving(Eq, Bits);
typedef struct { Bit#(1) victim_idx; Struct11 victim_info; Vector#(4, Bit#(64)) victim_value;  } Struct54 deriving(Eq, Bits);
typedef struct { Bit#(64) victim_addr; Bit#(3) victim_req;  } Struct55 deriving(Eq, Bits);
typedef struct { Bit#(51) tag; Struct11 value;  } Struct56 deriving(Eq, Bits);
typedef struct { Bool tm_hit; Bit#(2) tm_way; Struct11 tm_value;  } Struct57 deriving(Eq, Bits);
typedef struct { Bit#(8) addr; Struct56 datain;  } Struct58 deriving(Eq, Bits);
typedef struct { Bit#(1) acc_type; Vector#(4, Bit#(8)) acc_reps; Bit#(8) acc_index; Bit#(2) acc_way;  } Struct59 deriving(Eq, Bits);
typedef struct { Bool valid; Bit#(2) data;  } Struct6 deriving(Eq, Bits);
typedef struct { Bit#(10) addr; Vector#(4, Bit#(64)) datain;  } Struct60 deriving(Eq, Bits);
typedef struct { Bool valid; Struct48 data;  } Struct61 deriving(Eq, Bits);
typedef struct { Bit#(8) addr; Vector#(4, Bit#(8)) datain;  } Struct62 deriving(Eq, Bits);
typedef struct { Bit#(3) r_id; Bit#(2) r_dl_rss_from; Bool r_dl_rsb; Bit#(3) r_dl_rsbTo;  } Struct63 deriving(Eq, Bits);
typedef struct { Bit#(3) r_id; Bit#(2) r_dl_rss_from;  } Struct64 deriving(Eq, Bits);
typedef struct { Bool ir_is_rs_rel; Bool ir_is_rs_acc; Struct1 ir_msg; Bit#(3) ir_msg_from; Bit#(4) ir_mshr_id; Struct6 ir_by_victim;  } Struct7 deriving(Eq, Bits);
typedef struct { Bit#(4) r_id; Bit#(64) r_addr;  } Struct8 deriving(Eq, Bits);
typedef struct { Bit#(4) r_id; Bit#(1) r_midx; Struct1 r_msg;  } Struct9 deriving(Eq, Bits);

interface Module1;
    method Action enq_fifoPInput00 (Struct2 x_0);
    method ActionValue#(Struct2) deq_fifoPInput00 ();
endinterface

module mkModule1
    (Module1);
    Reg#(Struct2) elt_fifoPInput00 <- mkReg(unpack(0));
    Reg#(Bool) full_fifoPInput00 <- mkReg(unpack(0));
    Reg#(Bool) countDone_fifoPInput00 <- mkReg(unpack(0));
    Reg#(Bit#(18)) counter_fifoPInput00 <- mkReg(unpack(0));

    rule count_fifoPInput00;

        let x_0 = (countDone_fifoPInput00);
        when (! (x_0), noAction);
        let x_1 = (counter_fifoPInput00);
        counter_fifoPInput00 <= (x_1) + ((Bit#(18))'(18'h1));
        let x_2 =
        (full_fifoPInput00);
        if (((x_1) == ((Bit#(18))'(18'h3ffff))) && (x_2)) begin
            let x_3 =
            (elt_fifoPInput00);
            $display ("-- INPUT fifoPInput00: %x %x %b %x", (x_3).in_msg_from, ((x_3).in_msg).id, ((x_3).in_msg).type_, ((x_3).in_msg).addr);
            countDone_fifoPInput00 <= (Bool)'(True);
        end else begin

        end
    endrule

    method Action enq_fifoPInput00 (Struct2 x_0);
        let x_1 = (full_fifoPInput00);
        when (! (x_1), noAction);
        elt_fifoPInput00 <= x_0;
        full_fifoPInput00 <= (Bool)'(True);
    endmethod

    method ActionValue#(Struct2) deq_fifoPInput00 ();
        let x_1 = (full_fifoPInput00);
        when (x_1, noAction);
        let x_2 = (elt_fifoPInput00);
        full_fifoPInput00 <= (Bool)'(False);
        return x_2;
    endmethod
endmodule

interface Module2;
    method Action enq_fifoCRqInput_00 (Struct3 x_0);
    method ActionValue#(Struct3) deq_fifoCRqInput_00 ();
endinterface

module mkModule2
    (Module2);
    Reg#(Struct3) elt_fifoCRqInput_00 <- mkReg(unpack(0));
    Reg#(Bool) full_fifoCRqInput_00 <- mkReg(unpack(0));
    Reg#(Bool) countDone_fifoCRqInput_00 <- mkReg(unpack(0));
    Reg#(Bit#(18)) counter_fifoCRqInput_00 <- mkReg(unpack(0));

    rule count_fifoCRqInput_00;

        let x_0 = (countDone_fifoCRqInput_00);
        when (! (x_0), noAction);
        let x_1 = (counter_fifoCRqInput_00);
        counter_fifoCRqInput_00 <= (x_1) + ((Bit#(18))'(18'h1));
        let x_2 =
        (full_fifoCRqInput_00);
        if (((x_1) == ((Bit#(18))'(18'h3ffff))) && (x_2)) begin
            let x_3 =
            (elt_fifoCRqInput_00);
            $display ("-- CINPUT fifoCRqInput_00: %x %x %b %x", (x_3).ch_idx, ((x_3).ch_msg).id, ((x_3).ch_msg).type_, ((x_3).ch_msg).addr);
            countDone_fifoCRqInput_00 <= (Bool)'(True);
        end else begin

        end
    endrule

    method Action enq_fifoCRqInput_00 (Struct3 x_0);
        let x_1 = (full_fifoCRqInput_00);
        when (! (x_1), noAction);
        elt_fifoCRqInput_00 <= x_0;
        full_fifoCRqInput_00 <= (Bool)'(True);
    endmethod

    method ActionValue#(Struct3) deq_fifoCRqInput_00 ();
        let x_1 = (full_fifoCRqInput_00);
        when (x_1, noAction);
        let x_2 = (elt_fifoCRqInput_00);
        full_fifoCRqInput_00 <= (Bool)'(False);
        return x_2;
    endmethod
endmodule

interface Module3;
    method Action enq_fifoCRsInput_00 (Struct3 x_0);
    method ActionValue#(Struct3) deq_fifoCRsInput_00 ();
endinterface

module mkModule3
    (Module3);
    Reg#(Struct3) elt_fifoCRsInput_00 <- mkReg(unpack(0));
    Reg#(Bool) full_fifoCRsInput_00 <- mkReg(unpack(0));
    Reg#(Bool) countDone_fifoCRsInput_00 <- mkReg(unpack(0));
    Reg#(Bit#(18)) counter_fifoCRsInput_00 <- mkReg(unpack(0));

    rule count_fifoCRsInput_00;

        let x_0 = (countDone_fifoCRsInput_00);
        when (! (x_0), noAction);
        let x_1 = (counter_fifoCRsInput_00);
        counter_fifoCRsInput_00 <= (x_1) + ((Bit#(18))'(18'h1));
        let x_2 =
        (full_fifoCRsInput_00);
        if (((x_1) == ((Bit#(18))'(18'h3ffff))) && (x_2)) begin
            let x_3 =
            (elt_fifoCRsInput_00);
            $display ("-- CINPUT fifoCRsInput_00: %x %x %b %x", (x_3).ch_idx, ((x_3).ch_msg).id, ((x_3).ch_msg).type_, ((x_3).ch_msg).addr);
            countDone_fifoCRsInput_00 <= (Bool)'(True);
        end else begin

        end
    endrule

    method Action enq_fifoCRsInput_00 (Struct3 x_0);
        let x_1 = (full_fifoCRsInput_00);
        when (! (x_1), noAction);
        elt_fifoCRsInput_00 <= x_0;
        full_fifoCRsInput_00 <= (Bool)'(True);
    endmethod

    method ActionValue#(Struct3) deq_fifoCRsInput_00 ();
        let x_1 = (full_fifoCRsInput_00);
        when (x_1, noAction);
        let x_2 = (elt_fifoCRsInput_00);
        full_fifoCRsInput_00 <= (Bool)'(False);
        return x_2;
    endmethod
endmodule

interface Module4;
    method Action enq_fifoCInput_00 (Struct2 x_0);
    method ActionValue#(Struct2) deq_fifoCInput_00 ();
endinterface

module mkModule4
    (Module4);
    Reg#(Struct2) elt_fifoCInput_00 <- mkReg(unpack(0));
    Reg#(Bool) full_fifoCInput_00 <- mkReg(unpack(0));
    Reg#(Bool) countDone_fifoCInput_00 <- mkReg(unpack(0));
    Reg#(Bit#(18)) counter_fifoCInput_00 <- mkReg(unpack(0));

    rule count_fifoCInput_00;

        let x_0 = (countDone_fifoCInput_00);
        when (! (x_0), noAction);
        let x_1 = (counter_fifoCInput_00);
        counter_fifoCInput_00 <= (x_1) + ((Bit#(18))'(18'h1));
        let x_2 =
        (full_fifoCInput_00);
        if (((x_1) == ((Bit#(18))'(18'h3ffff))) && (x_2)) begin
            let x_3 =
            (elt_fifoCInput_00);
            $display ("-- INPUT fifoCInput_00: %x %x %b %x", (x_3).in_msg_from, ((x_3).in_msg).id, ((x_3).in_msg).type_, ((x_3).in_msg).addr);
            countDone_fifoCInput_00 <= (Bool)'(True);
        end else begin

        end
    endrule

    method Action enq_fifoCInput_00 (Struct2 x_0);
        let x_1 = (full_fifoCInput_00);
        when (! (x_1), noAction);
        elt_fifoCInput_00 <= x_0;
        full_fifoCInput_00 <= (Bool)'(True);
    endmethod

    method ActionValue#(Struct2) deq_fifoCInput_00 ();
        let x_1 = (full_fifoCInput_00);
        when (x_1, noAction);
        let x_2 = (elt_fifoCInput_00);
        full_fifoCInput_00 <= (Bool)'(False);
        return x_2;
    endmethod
endmodule

interface Module5;
    method Action enq_fifoN2I_parent_00 (Struct7 x_0);
    method ActionValue#(Struct7) deq_fifoN2I_parent_00 ();
endinterface

module mkModule5
    (Module5);
    Reg#(Struct7) elt_fifoN2I_parent_00 <- mkReg(unpack(0));
    Reg#(Bool) full_fifoN2I_parent_00 <- mkReg(unpack(0));
    Reg#(Bool) countDone_fifoN2I_parent_00 <- mkReg(unpack(0));
    Reg#(Bit#(18)) counter_fifoN2I_parent_00 <- mkReg(unpack(0));

    rule count_fifoN2I_parent_00;

        let x_0 = (countDone_fifoN2I_parent_00);
        when (! (x_0), noAction);
        let x_1 = (counter_fifoN2I_parent_00);
        counter_fifoN2I_parent_00 <= (x_1) + ((Bit#(18))'(18'h1));
        let x_2 =
        (full_fifoN2I_parent_00);
        if (((x_1) == ((Bit#(18))'(18'h3ffff))) && (x_2)) begin
            let x_3 =
            (elt_fifoN2I_parent_00);
            $display ("-- IR fifoN2I_parent_00: %b %b %x %b %x %x %x %b %x", (x_3).ir_is_rs_rel, (x_3).ir_is_rs_acc, ((x_3).ir_msg).id, ((x_3).ir_msg).type_, ((x_3).ir_msg).addr, (x_3).ir_msg_from, (x_3).ir_mshr_id, ((x_3).ir_by_victim).valid, ((x_3).ir_by_victim).data);
            countDone_fifoN2I_parent_00 <= (Bool)'(True);
        end else begin

        end
    endrule

    method Action enq_fifoN2I_parent_00 (Struct7 x_0);
        let x_1 = (full_fifoN2I_parent_00);
        when (! (x_1), noAction);
        elt_fifoN2I_parent_00 <= x_0;
        full_fifoN2I_parent_00 <= (Bool)'(True);
    endmethod

    method ActionValue#(Struct7) deq_fifoN2I_parent_00 ();
        let x_1 = (full_fifoN2I_parent_00);
        when (x_1, noAction);
        let x_2 = (elt_fifoN2I_parent_00);
        full_fifoN2I_parent_00 <= (Bool)'(False);
        return x_2;
    endmethod
endmodule

interface Module6;
    method Action enq_fifoI2L_parent_00 (Struct7 x_0);
    method ActionValue#(Struct7) deq_fifoI2L_parent_00 ();
endinterface

module mkModule6
    (Module6);
    Reg#(Struct7) elt_fifoI2L_parent_00 <- mkReg(unpack(0));
    Reg#(Bool) full_fifoI2L_parent_00 <- mkReg(unpack(0));
    Reg#(Bool) countDone_fifoI2L_parent_00 <- mkReg(unpack(0));
    Reg#(Bit#(18)) counter_fifoI2L_parent_00 <- mkReg(unpack(0));

    rule count_fifoI2L_parent_00;

        let x_0 = (countDone_fifoI2L_parent_00);
        when (! (x_0), noAction);
        let x_1 = (counter_fifoI2L_parent_00);
        counter_fifoI2L_parent_00 <= (x_1) + ((Bit#(18))'(18'h1));
        let x_2 =
        (full_fifoI2L_parent_00);
        if (((x_1) == ((Bit#(18))'(18'h3ffff))) && (x_2)) begin
            let x_3 =
            (elt_fifoI2L_parent_00);
            $display ("-- IR fifoI2L_parent_00: %b %b %x %b %x %x %x %b %x", (x_3).ir_is_rs_rel, (x_3).ir_is_rs_acc, ((x_3).ir_msg).id, ((x_3).ir_msg).type_, ((x_3).ir_msg).addr, (x_3).ir_msg_from, (x_3).ir_mshr_id, ((x_3).ir_by_victim).valid, ((x_3).ir_by_victim).data);
            countDone_fifoI2L_parent_00 <= (Bool)'(True);
        end else begin

        end
    endrule

    method Action enq_fifoI2L_parent_00 (Struct7 x_0);
        let x_1 = (full_fifoI2L_parent_00);
        when (! (x_1), noAction);
        elt_fifoI2L_parent_00 <= x_0;
        full_fifoI2L_parent_00 <= (Bool)'(True);
    endmethod

    method ActionValue#(Struct7) deq_fifoI2L_parent_00 ();
        let x_1 = (full_fifoI2L_parent_00);
        when (x_1, noAction);
        let x_2 = (elt_fifoI2L_parent_00);
        full_fifoI2L_parent_00 <= (Bool)'(False);
        return x_2;
    endmethod
endmodule

interface Module7;
    method Action enq_fifoN2I_child_00 (Struct7 x_0);
    method ActionValue#(Struct7) deq_fifoN2I_child_00 ();
endinterface

module mkModule7
    (Module7);
    Reg#(Struct7) elt_fifoN2I_child_00 <- mkReg(unpack(0));
    Reg#(Bool) full_fifoN2I_child_00 <- mkReg(unpack(0));
    Reg#(Bool) countDone_fifoN2I_child_00 <- mkReg(unpack(0));
    Reg#(Bit#(18)) counter_fifoN2I_child_00 <- mkReg(unpack(0));

    rule count_fifoN2I_child_00;

        let x_0 = (countDone_fifoN2I_child_00);
        when (! (x_0), noAction);
        let x_1 = (counter_fifoN2I_child_00);
        counter_fifoN2I_child_00 <= (x_1) + ((Bit#(18))'(18'h1));
        let x_2 =
        (full_fifoN2I_child_00);
        if (((x_1) == ((Bit#(18))'(18'h3ffff))) && (x_2)) begin
            let x_3 =
            (elt_fifoN2I_child_00);
            $display ("-- IR fifoN2I_child_00: %b %b %x %b %x %x %x %b %x", (x_3).ir_is_rs_rel, (x_3).ir_is_rs_acc, ((x_3).ir_msg).id, ((x_3).ir_msg).type_, ((x_3).ir_msg).addr, (x_3).ir_msg_from, (x_3).ir_mshr_id, ((x_3).ir_by_victim).valid, ((x_3).ir_by_victim).data);
            countDone_fifoN2I_child_00 <= (Bool)'(True);
        end else begin

        end
    endrule

    method Action enq_fifoN2I_child_00 (Struct7 x_0);
        let x_1 = (full_fifoN2I_child_00);
        when (! (x_1), noAction);
        elt_fifoN2I_child_00 <= x_0;
        full_fifoN2I_child_00 <= (Bool)'(True);
    endmethod

    method ActionValue#(Struct7) deq_fifoN2I_child_00 ();
        let x_1 = (full_fifoN2I_child_00);
        when (x_1, noAction);
        let x_2 = (elt_fifoN2I_child_00);
        full_fifoN2I_child_00 <= (Bool)'(False);
        return x_2;
    endmethod
endmodule

interface Module8;
    method Action enq_fifoI2L_child_00 (Struct7 x_0);
    method ActionValue#(Struct7) deq_fifoI2L_child_00 ();
endinterface

module mkModule8
    (Module8);
    Reg#(Struct7) elt_fifoI2L_child_00 <- mkReg(unpack(0));
    Reg#(Bool) full_fifoI2L_child_00 <- mkReg(unpack(0));
    Reg#(Bool) countDone_fifoI2L_child_00 <- mkReg(unpack(0));
    Reg#(Bit#(18)) counter_fifoI2L_child_00 <- mkReg(unpack(0));

    rule count_fifoI2L_child_00;

        let x_0 = (countDone_fifoI2L_child_00);
        when (! (x_0), noAction);
        let x_1 = (counter_fifoI2L_child_00);
        counter_fifoI2L_child_00 <= (x_1) + ((Bit#(18))'(18'h1));
        let x_2 =
        (full_fifoI2L_child_00);
        if (((x_1) == ((Bit#(18))'(18'h3ffff))) && (x_2)) begin
            let x_3 =
            (elt_fifoI2L_child_00);
            $display ("-- IR fifoI2L_child_00: %b %b %x %b %x %x %x %b %x", (x_3).ir_is_rs_rel, (x_3).ir_is_rs_acc, ((x_3).ir_msg).id, ((x_3).ir_msg).type_, ((x_3).ir_msg).addr, (x_3).ir_msg_from, (x_3).ir_mshr_id, ((x_3).ir_by_victim).valid, ((x_3).ir_by_victim).data);
            countDone_fifoI2L_child_00 <= (Bool)'(True);
        end else begin

        end
    endrule

    method Action enq_fifoI2L_child_00 (Struct7 x_0);
        let x_1 = (full_fifoI2L_child_00);
        when (! (x_1), noAction);
        elt_fifoI2L_child_00 <= x_0;
        full_fifoI2L_child_00 <= (Bool)'(True);
    endmethod

    method ActionValue#(Struct7) deq_fifoI2L_child_00 ();
        let x_1 = (full_fifoI2L_child_00);
        when (x_1, noAction);
        let x_2 = (elt_fifoI2L_child_00);
        full_fifoI2L_child_00 <= (Bool)'(False);
        return x_2;
    endmethod
endmodule

interface Module9;
    method Action enq_fifoL2E_00 (Struct13 x_0);
    method ActionValue#(Struct13) deq_fifoL2E_00 ();
endinterface

module mkModule9
    (Module9);
    Reg#(Struct13) elt_fifoL2E_00 <- mkReg(unpack(0));
    Reg#(Bool) full_fifoL2E_00 <- mkReg(unpack(0));
    Reg#(Bool) countDone_fifoL2E_00 <- mkReg(unpack(0));
    Reg#(Bit#(18)) counter_fifoL2E_00 <- mkReg(unpack(0));

    rule count_fifoL2E_00;

        let x_0 = (countDone_fifoL2E_00);
        when (! (x_0), noAction);
        let x_1 = (counter_fifoL2E_00);
        counter_fifoL2E_00 <= (x_1) + ((Bit#(18))'(18'h1));
        let x_2 =
        (full_fifoL2E_00);
        if (((x_1) == ((Bit#(18))'(18'h3ffff))) && (x_2)) begin
            let x_3 =
            (elt_fifoL2E_00);
            $display ("-- LR fifoL2E_00: %b %b %x %b %x %x %x %b %x %x %b %x %b %x %b %x", ((x_3).lr_ir_pp).ir_is_rs_rel, ((x_3).lr_ir_pp).ir_is_rs_acc, (((x_3).lr_ir_pp).ir_msg).id, (((x_3).lr_ir_pp).ir_msg).type_, (((x_3).lr_ir_pp).ir_msg).addr, ((x_3).lr_ir_pp).ir_msg_from, ((x_3).lr_ir_pp).ir_mshr_id, (((x_3).lr_ir_pp).ir_by_victim).valid, (((x_3).lr_ir_pp).ir_by_victim).data, ((x_3).lr_ir).info_index, ((x_3).lr_ir).info_hit, ((x_3).lr_ir).info_way, ((x_3).lr_ir).edir_hit, ((x_3).lr_ir).edir_way, (((x_3).lr_ir).edir_slot).valid, (((x_3).lr_ir).edir_slot).data);
            countDone_fifoL2E_00 <= (Bool)'(True);
        end else begin

        end
    endrule

    method Action enq_fifoL2E_00 (Struct13 x_0);
        let x_1 = (full_fifoL2E_00);
        when (! (x_1), noAction);
        elt_fifoL2E_00 <= x_0;
        full_fifoL2E_00 <= (Bool)'(True);
    endmethod

    method ActionValue#(Struct13) deq_fifoL2E_00 ();
        let x_1 = (full_fifoL2E_00);
        when (x_1, noAction);
        let x_2 = (elt_fifoL2E_00);
        full_fifoL2E_00 <= (Bool)'(False);
        return x_2;
    endmethod
endmodule

interface Module10;
    method ActionValue#(Struct6) victims__00findVictim (Bit#(64) x_0);
    method ActionValue#(Struct14) victims__00__getVictim (Bit#(2) x_0);
    method Action victims__00__setVictim (Struct20 x_0);
    method Action victims__00__registerVictim (Struct14 x_0);
    method ActionValue#(Struct14) victims__00__getFirstVictim ();
    method Action victims__00__setVictimRq (Struct27 x_0);
    method ActionValue#(Bit#(4)) victims__00__releaseVictim (Bit#(64) x_0);
endinterface

module mkModule10
    (Module10);
    Reg#(Vector#(8, Struct14)) victimRegs__00 <- mkReg(unpack(0));

    // No rules in this module

    method ActionValue#(Struct6) victims__00findVictim (Bit#(64) x_0);
        let x_1 = (victimRegs__00);
        Struct14 x_2 =
        ((x_1)[(Bit#(2))'(2'h0)]);
        let x_17 = ?;
        if (((x_2).victim_valid) && (((x_2).victim_addr) == (x_0))) begin
            x_17 = Struct6 {valid : (Bool)'(True), data : (Bit#(2))'(2'h0)};
        end else begin
            Struct14 x_3 =
            ((x_1)[(Bit#(2))'(2'h1)]);
            let x_16 = ?;
            if (((x_3).victim_valid) && (((x_3).victim_addr) == (x_0)))
                begin
                x_16 = Struct6 {valid : (Bool)'(True), data :
                (Bit#(2))'(2'h1)};
            end else begin
                Struct14 x_4 =
                ((x_1)[(Bit#(2))'(2'h2)]);
                let x_15 = ?;
                if (((x_4).victim_valid) && (((x_4).victim_addr) == (x_0)))
                    begin
                    x_15 = Struct6 {valid : (Bool)'(True), data :
                    (Bit#(2))'(2'h2)};
                end else begin
                    Struct14 x_5 =
                    ((x_1)[(Bit#(2))'(2'h3)]);
                    let x_14 = ?;
                    if (((x_5).victim_valid) && (((x_5).victim_addr) ==
                        (x_0))) begin
                        x_14 = Struct6 {valid : (Bool)'(True), data :
                        (Bit#(2))'(2'h3)};
                    end else begin
                        Struct14 x_6 =
                        ((x_1)[(Bit#(2))'(2'h0)]);
                        let x_13 = ?;
                        if (((x_6).victim_valid) && (((x_6).victim_addr) ==
                            (x_0))) begin
                            x_13 = Struct6 {valid : (Bool)'(True), data :
                            (Bit#(2))'(2'h0)};
                        end else begin
                            Struct14 x_7 =
                            ((x_1)[(Bit#(2))'(2'h1)]);
                            let x_12 = ?;
                            if (((x_7).victim_valid) && (((x_7).victim_addr)
                                == (x_0))) begin
                                x_12 = Struct6 {valid : (Bool)'(True), data :
                                (Bit#(2))'(2'h1)};
                            end else begin
                                Struct14 x_8 =
                                ((x_1)[(Bit#(2))'(2'h2)]);
                                let x_11 = ?;
                                if (((x_8).victim_valid) &&
                                    (((x_8).victim_addr) == (x_0))) begin
                                    x_11 = Struct6 {valid : (Bool)'(True),
                                    data : (Bit#(2))'(2'h2)};
                                end else begin
                                    Struct14 x_9 =
                                    ((x_1)[(Bit#(2))'(2'h3)]);
                                    let x_10 = ?;
                                    if (((x_9).victim_valid) &&
                                        (((x_9).victim_addr) == (x_0)))
                                        begin
                                        x_10 = Struct6 {valid :
                                        (Bool)'(True), data :
                                        (Bit#(2))'(2'h3)};
                                    end else begin
                                        x_10 = Struct6 {valid :
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

    method ActionValue#(Struct14) victims__00__getVictim (Bit#(2) x_0);
        let x_1 = (victimRegs__00);
        return (x_1)[x_0];
    endmethod

    method Action victims__00__setVictim (Struct20 x_0);
        let x_1 = (victimRegs__00);
        Struct14 x_2 = ((x_1)[(x_0).victim_idx]);
        Struct14 x_3 = (Struct14 {victim_valid : (Bool)'(True), victim_addr :
        (x_2).victim_addr, victim_info : (x_0).victim_info, victim_value :
        (x_0).victim_value, victim_req : (x_2).victim_req});
        victimRegs__00 <= update (x_1, (x_0).victim_idx, x_3);
    endmethod

    method Action victims__00__registerVictim (Struct14 x_0);
        let x_1 = (victimRegs__00);
        Struct6 x_2 = ((((x_1)[(Bit#(2))'(2'h3)]).victim_valid ?
        ((((x_1)[(Bit#(2))'(2'h2)]).victim_valid ?
        ((((x_1)[(Bit#(2))'(2'h1)]).victim_valid ?
        ((((x_1)[(Bit#(2))'(2'h0)]).victim_valid ?
        ((((x_1)[(Bit#(2))'(2'h3)]).victim_valid ?
        ((((x_1)[(Bit#(2))'(2'h2)]).victim_valid ?
        ((((x_1)[(Bit#(2))'(2'h1)]).victim_valid ? (Struct6 {valid :
        (Bool)'(False), data : unpack(0)}) : (Struct6 {valid : (Bool)'(True),
        data : (Bit#(2))'(2'h1)}))) : (Struct6 {valid : (Bool)'(True), data :
        (Bit#(2))'(2'h2)}))) : (Struct6 {valid : (Bool)'(True), data :
        (Bit#(2))'(2'h3)}))) : (Struct6 {valid : (Bool)'(True), data :
        (Bit#(2))'(2'h0)}))) : (Struct6 {valid : (Bool)'(True), data :
        (Bit#(2))'(2'h1)}))) : (Struct6 {valid : (Bool)'(True), data :
        (Bit#(2))'(2'h2)}))) : (Struct6 {valid : (Bool)'(True), data :
        (Bit#(2))'(2'h3)})));
        when ((x_2).valid, noAction);
        Bit#(2) x_3 = ((x_2).data);
        victimRegs__00 <= update (x_1, x_3, x_0);
    endmethod

    method ActionValue#(Struct14) victims__00__getFirstVictim ();
        let x_1 = (victimRegs__00);
        Struct37 x_2 = (((((x_1)[(Bit#(2))'(2'h3)]).victim_valid) && (!
        ((((x_1)[(Bit#(2))'(2'h3)]).victim_req).valid)) ? (Struct37 {valid :
        (Bool)'(True), data : (x_1)[(Bit#(2))'(2'h3)]}) :
        (((((x_1)[(Bit#(2))'(2'h2)]).victim_valid) && (!
        ((((x_1)[(Bit#(2))'(2'h2)]).victim_req).valid)) ? (Struct37 {valid :
        (Bool)'(True), data : (x_1)[(Bit#(2))'(2'h2)]}) :
        (((((x_1)[(Bit#(2))'(2'h1)]).victim_valid) && (!
        ((((x_1)[(Bit#(2))'(2'h1)]).victim_req).valid)) ? (Struct37 {valid :
        (Bool)'(True), data : (x_1)[(Bit#(2))'(2'h1)]}) :
        (((((x_1)[(Bit#(2))'(2'h0)]).victim_valid) && (!
        ((((x_1)[(Bit#(2))'(2'h0)]).victim_req).valid)) ? (Struct37 {valid :
        (Bool)'(True), data : (x_1)[(Bit#(2))'(2'h0)]}) :
        (((((x_1)[(Bit#(2))'(2'h3)]).victim_valid) && (!
        ((((x_1)[(Bit#(2))'(2'h3)]).victim_req).valid)) ? (Struct37 {valid :
        (Bool)'(True), data : (x_1)[(Bit#(2))'(2'h3)]}) :
        (((((x_1)[(Bit#(2))'(2'h2)]).victim_valid) && (!
        ((((x_1)[(Bit#(2))'(2'h2)]).victim_req).valid)) ? (Struct37 {valid :
        (Bool)'(True), data : (x_1)[(Bit#(2))'(2'h2)]}) :
        (((((x_1)[(Bit#(2))'(2'h1)]).victim_valid) && (!
        ((((x_1)[(Bit#(2))'(2'h1)]).victim_req).valid)) ? (Struct37 {valid :
        (Bool)'(True), data : (x_1)[(Bit#(2))'(2'h1)]}) : (Struct37 {valid :
        (Bool)'(False), data : unpack(0)})))))))))))))));
        when ((x_2).valid, noAction);
        return (x_2).data;
    endmethod

    method Action victims__00__setVictimRq (Struct27 x_0);
        Bit#(64) x_1 = ((x_0).victim_addr);
        Bit#(4) x_2 = ((x_0).victim_req);
        let x_3 = (victimRegs__00);
        Struct14 x_4 =
        ((x_3)[(Bit#(2))'(2'h3)]);
        if (((x_4).victim_valid) && (((x_4).victim_addr) == (x_1)))
            begin
            Struct14 x_5 = (Struct14 {victim_valid : (x_4).victim_valid,
            victim_addr : (x_4).victim_addr, victim_info : (x_4).victim_info,
            victim_value : (x_4).victim_value, victim_req : Struct15 {valid :
            (Bool)'(True), data : x_2}});
            victimRegs__00 <= update (x_3, (Bit#(2))'(2'h3), x_5);
        end else begin
            Struct14 x_6 =
            ((x_3)[(Bit#(2))'(2'h2)]);
            if (((x_6).victim_valid) && (((x_6).victim_addr) == (x_1)))
                begin
                Struct14 x_7 = (Struct14 {victim_valid : (x_6).victim_valid,
                victim_addr : (x_6).victim_addr, victim_info :
                (x_6).victim_info, victim_value : (x_6).victim_value,
                victim_req : Struct15 {valid : (Bool)'(True), data :
                x_2}});
                victimRegs__00 <= update (x_3, (Bit#(2))'(2'h2), x_7);
            end else begin
                Struct14 x_8 =
                ((x_3)[(Bit#(2))'(2'h1)]);
                if (((x_8).victim_valid) && (((x_8).victim_addr) == (x_1)))
                    begin
                    Struct14 x_9 = (Struct14 {victim_valid :
                    (x_8).victim_valid, victim_addr : (x_8).victim_addr,
                    victim_info : (x_8).victim_info, victim_value :
                    (x_8).victim_value, victim_req : Struct15 {valid :
                    (Bool)'(True), data : x_2}});
                    victimRegs__00 <= update (x_3, (Bit#(2))'(2'h1), x_9);
                end else begin
                    Struct14 x_10 =
                    ((x_3)[(Bit#(2))'(2'h0)]);
                    if (((x_10).victim_valid) && (((x_10).victim_addr) ==
                        (x_1))) begin
                        Struct14 x_11 = (Struct14 {victim_valid :
                        (x_10).victim_valid, victim_addr :
                        (x_10).victim_addr, victim_info : (x_10).victim_info,
                        victim_value : (x_10).victim_value, victim_req :
                        Struct15 {valid : (Bool)'(True), data :
                        x_2}});
                        victimRegs__00 <= update (x_3, (Bit#(2))'(2'h0),
                        x_11);
                    end else begin
                        Struct14 x_12 =
                        ((x_3)[(Bit#(2))'(2'h3)]);
                        if (((x_12).victim_valid) && (((x_12).victim_addr) ==
                            (x_1))) begin
                            Struct14 x_13 = (Struct14 {victim_valid :
                            (x_12).victim_valid, victim_addr :
                            (x_12).victim_addr, victim_info :
                            (x_12).victim_info, victim_value :
                            (x_12).victim_value, victim_req : Struct15 {valid
                            : (Bool)'(True), data : x_2}});
                            victimRegs__00 <= update (x_3, (Bit#(2))'(2'h3),
                            x_13);
                        end else begin
                            Struct14 x_14 =
                            ((x_3)[(Bit#(2))'(2'h2)]);
                            if (((x_14).victim_valid) &&
                                (((x_14).victim_addr) == (x_1)))
                                begin
                                Struct14 x_15 = (Struct14 {victim_valid :
                                (x_14).victim_valid, victim_addr :
                                (x_14).victim_addr, victim_info :
                                (x_14).victim_info, victim_value :
                                (x_14).victim_value, victim_req : Struct15
                                {valid : (Bool)'(True), data :
                                x_2}});
                                victimRegs__00 <= update (x_3,
                                (Bit#(2))'(2'h2), x_15);
                            end else begin
                                Struct14 x_16 =
                                ((x_3)[(Bit#(2))'(2'h1)]);
                                if (((x_16).victim_valid) &&
                                    (((x_16).victim_addr) == (x_1)))
                                    begin
                                    Struct14 x_17 = (Struct14 {victim_valid :
                                    (x_16).victim_valid, victim_addr :
                                    (x_16).victim_addr, victim_info :
                                    (x_16).victim_info, victim_value :
                                    (x_16).victim_value, victim_req :
                                    Struct15 {valid : (Bool)'(True), data :
                                    x_2}});
                                    victimRegs__00 <= update (x_3,
                                    (Bit#(2))'(2'h1), x_17);
                                end else begin

                                end
                            end
                        end
                    end
                end
            end
        end
    endmethod

    method ActionValue#(Bit#(4)) victims__00__releaseVictim (Bit#(64) x_0);
        let x_1 = (victimRegs__00);
        Struct14 x_2 =
        ((x_1)[(Bit#(2))'(2'h0)]);
        let x_25 = ?;
        if (((x_2).victim_valid) && (((x_2).victim_addr) == (x_0)))
            begin
            victimRegs__00 <= update (x_1, (Bit#(2))'(2'h0),
            unpack(0));
            Bit#(4) x_3 = (((x_2).victim_req).data);
            x_25 = x_3;
        end else begin
            Struct14 x_4 =
            ((x_1)[(Bit#(2))'(2'h1)]);
            let x_24 = ?;
            if (((x_4).victim_valid) && (((x_4).victim_addr) == (x_0)))
                begin
                victimRegs__00 <= update (x_1, (Bit#(2))'(2'h1),
                unpack(0));
                Bit#(4) x_5 = (((x_4).victim_req).data);
                x_24 = x_5;
            end else begin
                Struct14 x_6 =
                ((x_1)[(Bit#(2))'(2'h2)]);
                let x_23 = ?;
                if (((x_6).victim_valid) && (((x_6).victim_addr) == (x_0)))
                    begin
                    victimRegs__00 <= update (x_1, (Bit#(2))'(2'h2),
                    unpack(0));
                    Bit#(4) x_7 = (((x_6).victim_req).data);
                    x_23 = x_7;
                end else begin
                    Struct14 x_8 =
                    ((x_1)[(Bit#(2))'(2'h3)]);
                    let x_22 = ?;
                    if (((x_8).victim_valid) && (((x_8).victim_addr) ==
                        (x_0))) begin
                        victimRegs__00 <= update (x_1, (Bit#(2))'(2'h3),
                        unpack(0));
                        Bit#(4) x_9 = (((x_8).victim_req).data);
                        x_22 = x_9;
                    end else begin
                        Struct14 x_10 =
                        ((x_1)[(Bit#(2))'(2'h0)]);
                        let x_21 = ?;
                        if (((x_10).victim_valid) && (((x_10).victim_addr) ==
                            (x_0))) begin
                            victimRegs__00 <= update (x_1, (Bit#(2))'(2'h0),
                            unpack(0));
                            Bit#(4) x_11 = (((x_10).victim_req).data);
                            x_21 = x_11;
                        end else begin
                            Struct14 x_12 =
                            ((x_1)[(Bit#(2))'(2'h1)]);
                            let x_20 = ?;
                            if (((x_12).victim_valid) &&
                                (((x_12).victim_addr) == (x_0)))
                                begin
                                victimRegs__00 <= update (x_1,
                                (Bit#(2))'(2'h1), unpack(0));
                                Bit#(4) x_13 =
                                (((x_12).victim_req).data);
                                x_20 = x_13;
                            end else begin
                                Struct14 x_14 =
                                ((x_1)[(Bit#(2))'(2'h2)]);
                                let x_19 = ?;
                                if (((x_14).victim_valid) &&
                                    (((x_14).victim_addr) == (x_0)))
                                    begin
                                    victimRegs__00 <= update (x_1,
                                    (Bit#(2))'(2'h2), unpack(0));
                                    Bit#(4) x_15 =
                                    (((x_14).victim_req).data);
                                    x_19 = x_15;
                                end else begin
                                    Struct14 x_16 =
                                    ((x_1)[(Bit#(2))'(2'h3)]);
                                    let x_18 = ?;
                                    if (((x_16).victim_valid) &&
                                        (((x_16).victim_addr) == (x_0)))
                                        begin
                                        victimRegs__00 <= update (x_1,
                                        (Bit#(2))'(2'h3), unpack(0));
                                        Bit#(4) x_17 =
                                        (((x_16).victim_req).data);
                                        x_18 = x_17;
                                    end else begin
                                        x_18 = unpack(0);
                                    end
                                    x_19 = x_18;
                                end
                                x_20 = x_19;
                            end
                            x_21 = x_20;
                        end
                        x_22 = x_21;
                    end
                    x_23 = x_22;
                end
                x_24 = x_23;
            end
            x_25 = x_24;
        end
        return x_25;
    endmethod
endmodule

interface Module11;
    method Action rdReq_infoRam__00__7 (Bit#(9) x_0);
    method Action wrReq_infoRam__00__7 (Struct33 x_0);
    method ActionValue#(Struct28) rdResp_infoRam__00__7 ();
endinterface

module mkModule11 (Module11);
    RWBramCore#(Bit#(9), Struct28) bram <- mkRWBramCore();
    Reg#(Bool) initDone <- mkReg(False);
    Reg#(Bit#(9)) initIdx <- mkReg(0);

    rule init (!initDone);
        let initData = Struct28 {tag: 50'h7, value: Struct11 {mesi_owned: False, mesi_status: 3'h1, mesi_dir_st: 3'h1, mesi_dir_sharers: 2'h0}};
        bram.wrReq(initIdx, initData);
        initIdx <= initIdx + 1;
        initDone <= (initIdx == maxBound);
    endrule

    method Action rdReq_infoRam__00__7 (Bit#(9) x_0) if(initDone);
        bram.rdReq(x_0);
    endmethod

    method Action wrReq_infoRam__00__7 (Struct33 x_0) if(initDone);
        bram.wrReq(x_0.addr, x_0.datain);
    endmethod

    method ActionValue#(Struct28) rdResp_infoRam__00__7 () if(initDone);
        bram.deqRdResp ();
        let data = bram.rdResp ();
        return data;
    endmethod


endmodule

interface Module12;
    method Action rdReq_infoRam__00__6 (Bit#(9) x_0);
    method Action wrReq_infoRam__00__6 (Struct33 x_0);
    method ActionValue#(Struct28) rdResp_infoRam__00__6 ();
endinterface

module mkModule12 (Module12);
    RWBramCore#(Bit#(9), Struct28) bram <- mkRWBramCore();
    Reg#(Bool) initDone <- mkReg(False);
    Reg#(Bit#(9)) initIdx <- mkReg(0);

    rule init (!initDone);
        let initData = Struct28 {tag: 50'h6, value: Struct11 {mesi_owned: False, mesi_status: 3'h1, mesi_dir_st: 3'h1, mesi_dir_sharers: 2'h0}};
        bram.wrReq(initIdx, initData);
        initIdx <= initIdx + 1;
        initDone <= (initIdx == maxBound);
    endrule

    method Action rdReq_infoRam__00__6 (Bit#(9) x_0) if(initDone);
        bram.rdReq(x_0);
    endmethod

    method Action wrReq_infoRam__00__6 (Struct33 x_0) if(initDone);
        bram.wrReq(x_0.addr, x_0.datain);
    endmethod

    method ActionValue#(Struct28) rdResp_infoRam__00__6 () if(initDone);
        bram.deqRdResp ();
        let data = bram.rdResp ();
        return data;
    endmethod


endmodule

interface Module13;
    method Action rdReq_infoRam__00__5 (Bit#(9) x_0);
    method Action wrReq_infoRam__00__5 (Struct33 x_0);
    method ActionValue#(Struct28) rdResp_infoRam__00__5 ();
endinterface

module mkModule13 (Module13);
    RWBramCore#(Bit#(9), Struct28) bram <- mkRWBramCore();
    Reg#(Bool) initDone <- mkReg(False);
    Reg#(Bit#(9)) initIdx <- mkReg(0);

    rule init (!initDone);
        let initData = Struct28 {tag: 50'h5, value: Struct11 {mesi_owned: False, mesi_status: 3'h1, mesi_dir_st: 3'h1, mesi_dir_sharers: 2'h0}};
        bram.wrReq(initIdx, initData);
        initIdx <= initIdx + 1;
        initDone <= (initIdx == maxBound);
    endrule

    method Action rdReq_infoRam__00__5 (Bit#(9) x_0) if(initDone);
        bram.rdReq(x_0);
    endmethod

    method Action wrReq_infoRam__00__5 (Struct33 x_0) if(initDone);
        bram.wrReq(x_0.addr, x_0.datain);
    endmethod

    method ActionValue#(Struct28) rdResp_infoRam__00__5 () if(initDone);
        bram.deqRdResp ();
        let data = bram.rdResp ();
        return data;
    endmethod


endmodule

interface Module14;
    method Action rdReq_infoRam__00__4 (Bit#(9) x_0);
    method Action wrReq_infoRam__00__4 (Struct33 x_0);
    method ActionValue#(Struct28) rdResp_infoRam__00__4 ();
endinterface

module mkModule14 (Module14);
    RWBramCore#(Bit#(9), Struct28) bram <- mkRWBramCore();
    Reg#(Bool) initDone <- mkReg(False);
    Reg#(Bit#(9)) initIdx <- mkReg(0);

    rule init (!initDone);
        let initData = Struct28 {tag: 50'h4, value: Struct11 {mesi_owned: False, mesi_status: 3'h1, mesi_dir_st: 3'h1, mesi_dir_sharers: 2'h0}};
        bram.wrReq(initIdx, initData);
        initIdx <= initIdx + 1;
        initDone <= (initIdx == maxBound);
    endrule

    method Action rdReq_infoRam__00__4 (Bit#(9) x_0) if(initDone);
        bram.rdReq(x_0);
    endmethod

    method Action wrReq_infoRam__00__4 (Struct33 x_0) if(initDone);
        bram.wrReq(x_0.addr, x_0.datain);
    endmethod

    method ActionValue#(Struct28) rdResp_infoRam__00__4 () if(initDone);
        bram.deqRdResp ();
        let data = bram.rdResp ();
        return data;
    endmethod


endmodule

interface Module15;
    method Action rdReq_infoRam__00__3 (Bit#(9) x_0);
    method Action wrReq_infoRam__00__3 (Struct33 x_0);
    method ActionValue#(Struct28) rdResp_infoRam__00__3 ();
endinterface

module mkModule15 (Module15);
    RWBramCore#(Bit#(9), Struct28) bram <- mkRWBramCore();
    Reg#(Bool) initDone <- mkReg(False);
    Reg#(Bit#(9)) initIdx <- mkReg(0);

    rule init (!initDone);
        let initData = Struct28 {tag: 50'h3, value: Struct11 {mesi_owned: False, mesi_status: 3'h1, mesi_dir_st: 3'h1, mesi_dir_sharers: 2'h0}};
        bram.wrReq(initIdx, initData);
        initIdx <= initIdx + 1;
        initDone <= (initIdx == maxBound);
    endrule

    method Action rdReq_infoRam__00__3 (Bit#(9) x_0) if(initDone);
        bram.rdReq(x_0);
    endmethod

    method Action wrReq_infoRam__00__3 (Struct33 x_0) if(initDone);
        bram.wrReq(x_0.addr, x_0.datain);
    endmethod

    method ActionValue#(Struct28) rdResp_infoRam__00__3 () if(initDone);
        bram.deqRdResp ();
        let data = bram.rdResp ();
        return data;
    endmethod


endmodule

interface Module16;
    method Action rdReq_infoRam__00__2 (Bit#(9) x_0);
    method Action wrReq_infoRam__00__2 (Struct33 x_0);
    method ActionValue#(Struct28) rdResp_infoRam__00__2 ();
endinterface

module mkModule16 (Module16);
    RWBramCore#(Bit#(9), Struct28) bram <- mkRWBramCore();
    Reg#(Bool) initDone <- mkReg(False);
    Reg#(Bit#(9)) initIdx <- mkReg(0);

    rule init (!initDone);
        let initData = Struct28 {tag: 50'h2, value: Struct11 {mesi_owned: False, mesi_status: 3'h1, mesi_dir_st: 3'h1, mesi_dir_sharers: 2'h0}};
        bram.wrReq(initIdx, initData);
        initIdx <= initIdx + 1;
        initDone <= (initIdx == maxBound);
    endrule

    method Action rdReq_infoRam__00__2 (Bit#(9) x_0) if(initDone);
        bram.rdReq(x_0);
    endmethod

    method Action wrReq_infoRam__00__2 (Struct33 x_0) if(initDone);
        bram.wrReq(x_0.addr, x_0.datain);
    endmethod

    method ActionValue#(Struct28) rdResp_infoRam__00__2 () if(initDone);
        bram.deqRdResp ();
        let data = bram.rdResp ();
        return data;
    endmethod


endmodule

interface Module17;
    method Action rdReq_infoRam__00__1 (Bit#(9) x_0);
    method Action wrReq_infoRam__00__1 (Struct33 x_0);
    method ActionValue#(Struct28) rdResp_infoRam__00__1 ();
endinterface

module mkModule17 (Module17);
    RWBramCore#(Bit#(9), Struct28) bram <- mkRWBramCore();
    Reg#(Bool) initDone <- mkReg(False);
    Reg#(Bit#(9)) initIdx <- mkReg(0);

    rule init (!initDone);
        let initData = Struct28 {tag: 50'h1, value: Struct11 {mesi_owned: False, mesi_status: 3'h1, mesi_dir_st: 3'h1, mesi_dir_sharers: 2'h0}};
        bram.wrReq(initIdx, initData);
        initIdx <= initIdx + 1;
        initDone <= (initIdx == maxBound);
    endrule

    method Action rdReq_infoRam__00__1 (Bit#(9) x_0) if(initDone);
        bram.rdReq(x_0);
    endmethod

    method Action wrReq_infoRam__00__1 (Struct33 x_0) if(initDone);
        bram.wrReq(x_0.addr, x_0.datain);
    endmethod

    method ActionValue#(Struct28) rdResp_infoRam__00__1 () if(initDone);
        bram.deqRdResp ();
        let data = bram.rdResp ();
        return data;
    endmethod


endmodule

interface Module18;
    method Action rdReq_infoRam__00__0 (Bit#(9) x_0);
    method Action wrReq_infoRam__00__0 (Struct33 x_0);
    method ActionValue#(Struct28) rdResp_infoRam__00__0 ();
endinterface

module mkModule18 (Module18);
    RWBramCore#(Bit#(9), Struct28) bram <- mkRWBramCore();
    Reg#(Bool) initDone <- mkReg(False);
    Reg#(Bit#(9)) initIdx <- mkReg(0);

    rule init (!initDone);
        let initData = Struct28 {tag: 50'h0, value: Struct11 {mesi_owned: False, mesi_status: 3'h1, mesi_dir_st: 3'h1, mesi_dir_sharers: 2'h0}};
        bram.wrReq(initIdx, initData);
        initIdx <= initIdx + 1;
        initDone <= (initIdx == maxBound);
    endrule

    method Action rdReq_infoRam__00__0 (Bit#(9) x_0) if(initDone);
        bram.rdReq(x_0);
    endmethod

    method Action wrReq_infoRam__00__0 (Struct33 x_0) if(initDone);
        bram.wrReq(x_0.addr, x_0.datain);
    endmethod

    method ActionValue#(Struct28) rdResp_infoRam__00__0 () if(initDone);
        bram.deqRdResp ();
        let data = bram.rdResp ();
        return data;
    endmethod


endmodule

interface Module19;
    method Action rdReq_edirRam__00__3 (Bit#(9) x_0);
    method Action wrReq_edirRam__00__3 (Struct36 x_0);
    method ActionValue#(Struct30) rdResp_edirRam__00__3 ();
endinterface

module mkModule19 (Module19);
    RWBramCore#(Bit#(9), Struct30) bram <- mkRWBramCore();
    Reg#(Bool) initDone <- mkReg(False);
    Reg#(Bit#(9)) initIdx <- mkReg(0);

    rule init (!initDone);
        let initData = Struct30 {tag: 50'hb, value: Struct31 {mesi_edir_st: 3'h1, mesi_edir_sharers: 2'h0}};
        bram.wrReq(initIdx, initData);
        initIdx <= initIdx + 1;
        initDone <= (initIdx == maxBound);
    endrule

    method Action rdReq_edirRam__00__3 (Bit#(9) x_0) if(initDone);
        bram.rdReq(x_0);
    endmethod

    method Action wrReq_edirRam__00__3 (Struct36 x_0) if(initDone);
        bram.wrReq(x_0.addr, x_0.datain);
    endmethod

    method ActionValue#(Struct30) rdResp_edirRam__00__3 () if(initDone);
        bram.deqRdResp ();
        let data = bram.rdResp ();
        return data;
    endmethod


endmodule

interface Module20;
    method Action rdReq_edirRam__00__2 (Bit#(9) x_0);
    method Action wrReq_edirRam__00__2 (Struct36 x_0);
    method ActionValue#(Struct30) rdResp_edirRam__00__2 ();
endinterface

module mkModule20 (Module20);
    RWBramCore#(Bit#(9), Struct30) bram <- mkRWBramCore();
    Reg#(Bool) initDone <- mkReg(False);
    Reg#(Bit#(9)) initIdx <- mkReg(0);

    rule init (!initDone);
        let initData = Struct30 {tag: 50'ha, value: Struct31 {mesi_edir_st: 3'h1, mesi_edir_sharers: 2'h0}};
        bram.wrReq(initIdx, initData);
        initIdx <= initIdx + 1;
        initDone <= (initIdx == maxBound);
    endrule

    method Action rdReq_edirRam__00__2 (Bit#(9) x_0) if(initDone);
        bram.rdReq(x_0);
    endmethod

    method Action wrReq_edirRam__00__2 (Struct36 x_0) if(initDone);
        bram.wrReq(x_0.addr, x_0.datain);
    endmethod

    method ActionValue#(Struct30) rdResp_edirRam__00__2 () if(initDone);
        bram.deqRdResp ();
        let data = bram.rdResp ();
        return data;
    endmethod


endmodule

interface Module21;
    method Action rdReq_edirRam__00__1 (Bit#(9) x_0);
    method Action wrReq_edirRam__00__1 (Struct36 x_0);
    method ActionValue#(Struct30) rdResp_edirRam__00__1 ();
endinterface

module mkModule21 (Module21);
    RWBramCore#(Bit#(9), Struct30) bram <- mkRWBramCore();
    Reg#(Bool) initDone <- mkReg(False);
    Reg#(Bit#(9)) initIdx <- mkReg(0);

    rule init (!initDone);
        let initData = Struct30 {tag: 50'h9, value: Struct31 {mesi_edir_st: 3'h1, mesi_edir_sharers: 2'h0}};
        bram.wrReq(initIdx, initData);
        initIdx <= initIdx + 1;
        initDone <= (initIdx == maxBound);
    endrule

    method Action rdReq_edirRam__00__1 (Bit#(9) x_0) if(initDone);
        bram.rdReq(x_0);
    endmethod

    method Action wrReq_edirRam__00__1 (Struct36 x_0) if(initDone);
        bram.wrReq(x_0.addr, x_0.datain);
    endmethod

    method ActionValue#(Struct30) rdResp_edirRam__00__1 () if(initDone);
        bram.deqRdResp ();
        let data = bram.rdResp ();
        return data;
    endmethod


endmodule

interface Module22;
    method Action rdReq_edirRam__00__0 (Bit#(9) x_0);
    method Action wrReq_edirRam__00__0 (Struct36 x_0);
    method ActionValue#(Struct30) rdResp_edirRam__00__0 ();
endinterface

module mkModule22 (Module22);
    RWBramCore#(Bit#(9), Struct30) bram <- mkRWBramCore();
    Reg#(Bool) initDone <- mkReg(False);
    Reg#(Bit#(9)) initIdx <- mkReg(0);

    rule init (!initDone);
        let initData = Struct30 {tag: 50'h8, value: Struct31 {mesi_edir_st: 3'h1, mesi_edir_sharers: 2'h0}};
        bram.wrReq(initIdx, initData);
        initIdx <= initIdx + 1;
        initDone <= (initIdx == maxBound);
    endrule

    method Action rdReq_edirRam__00__0 (Bit#(9) x_0) if(initDone);
        bram.rdReq(x_0);
    endmethod

    method Action wrReq_edirRam__00__0 (Struct36 x_0) if(initDone);
        bram.wrReq(x_0.addr, x_0.datain);
    endmethod

    method ActionValue#(Struct30) rdResp_edirRam__00__0 () if(initDone);
        bram.deqRdResp ();
        let data = bram.rdResp ();
        return data;
    endmethod


endmodule

interface Module23;
    method Action rdReq_dataRam__00 (Bit#(12) x_0);
    method Action wrReq_dataRam__00 (Struct35 x_0);
    method ActionValue#(Vector#(4, Bit#(64))) rdResp_dataRam__00 ();
endinterface

module mkModule23 (Module23);
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

    method Action wrReq_dataRam__00 (Struct35 x_0) if(initDone);
        bram.wrReq(x_0.addr, x_0.datain);
    endmethod

    method ActionValue#(Vector#(4, Bit#(64))) rdResp_dataRam__00 ()
    if(initDone);
        bram.deqRdResp ();
        let data = bram.rdResp ();
        return data;
    endmethod


endmodule

interface Module24;
    method Action rdReq_repRam__00 (Bit#(9) x_0);
    method Action wrReq_repRam__00 (Struct38 x_0);
    method ActionValue#(Vector#(8, Bit#(8))) rdResp_repRam__00 ();
endinterface

module mkModule24 (Module24);
    RWBramCore#(Bit#(9), Vector#(8, Bit#(8))) bram <- mkRWBramCore();
    Reg#(Bool) initDone <- mkReg(False);
    Reg#(Bit#(9)) initIdx <- mkReg(0);

    rule init (!initDone);
        let initData = vec(8'h0, 8'h0, 8'h0, 8'h0, 8'h0, 8'h0, 8'h0, 8'h0);
        bram.wrReq(initIdx, initData);
        initIdx <= initIdx + 1;
        initDone <= (initIdx == maxBound);
    endrule

    method Action rdReq_repRam__00 (Bit#(9) x_0) if(initDone);
        bram.rdReq(x_0);
    endmethod

    method Action wrReq_repRam__00 (Struct38 x_0) if(initDone);
        bram.wrReq(x_0.addr, x_0.datain);
    endmethod

    method ActionValue#(Vector#(8, Bit#(8))) rdResp_repRam__00 ()
    if(initDone);
        bram.deqRdResp ();
        let data = bram.rdResp ();
        return data;
    endmethod


endmodule

interface Module25;
    method ActionValue#(Struct17) getMSHR_00 (Bit#(4) x_0);
    method ActionValue#(Struct5) getPRqSlot_00 (Struct4 x_0);
    method ActionValue#(Struct5) getCRqSlot_00 (Struct4 x_0);
    method ActionValue#(Struct16) getWait_00 ();
    method Action registerUL_00 (Struct22 x_0);
    method Action registerDL_00 (Struct23 x_0);
    method ActionValue#(Bit#(4)) getULImm_00 (Struct1 x_0);
    method Action transferUpDown_00 (Struct26 x_0);
    method ActionValue#(Bit#(4)) findUL_00 (Bit#(64) x_0);
    method ActionValue#(Bit#(4)) findDL_00 (Bit#(64) x_0);
    method Action releaseMSHR_00 (Bit#(4) x_0);
    method Action addRs_00 (Struct9 x_0);
    method ActionValue#(Struct8) getRsReady_00 ();
endinterface

module mkModule25
    (Module25);
    Reg#(Vector#(12, Struct17)) rqs_00 <- mkReg(unpack(0));

    // No rules in this module

    method ActionValue#(Struct17) getMSHR_00 (Bit#(4) x_0);
        let x_1 = (rqs_00);
        return (x_1)[x_0];
    endmethod

    method ActionValue#(Struct5) getPRqSlot_00 (Struct4 x_0);
        let x_1 = (rqs_00);
        Struct15 x_2 = (((((x_1)[(Bit#(4))'(4'h0)]).m_status) ==
        ((Bit#(3))'(3'h0)) ? (Struct15 {valid : (Bool)'(True), data :
        (Bit#(4))'(4'h0)}) : (((((x_1)[(Bit#(4))'(4'h1)]).m_status) ==
        ((Bit#(3))'(3'h0)) ? (Struct15 {valid : (Bool)'(True), data :
        (Bit#(4))'(4'h1)}) : (((((x_1)[(Bit#(4))'(4'h2)]).m_status) ==
        ((Bit#(3))'(3'h0)) ? (Struct15 {valid : (Bool)'(True), data :
        (Bit#(4))'(4'h2)}) : (((((x_1)[(Bit#(4))'(4'h3)]).m_status) ==
        ((Bit#(3))'(3'h0)) ? (Struct15 {valid : (Bool)'(True), data :
        (Bit#(4))'(4'h3)}) : (Struct15 {valid : (Bool)'(False), data :
        unpack(0)})))))))));
        Bool x_3 = ((x_2).valid);
        Bit#(4) x_4 = ((x_2).data);
        Bit#(64) x_5 = (((x_0).r_msg).addr);
        Struct15 x_6 = ((((! ((((x_1)[(Bit#(4))'(4'h0)]).m_status) ==
        ((Bit#(3))'(3'h0)))) && (!
        ((((x_1)[(Bit#(4))'(4'h0)]).m_next).valid))) &&
        (((((x_1)[(Bit#(4))'(4'h0)]).m_msg).addr) == (x_5)) ? (Struct15
        {valid : (Bool)'(True), data : (Bit#(4))'(4'h0)}) : ((((!
        ((((x_1)[(Bit#(4))'(4'h1)]).m_status) == ((Bit#(3))'(3'h0)))) && (!
        ((((x_1)[(Bit#(4))'(4'h1)]).m_next).valid))) &&
        (((((x_1)[(Bit#(4))'(4'h1)]).m_msg).addr) == (x_5)) ? (Struct15
        {valid : (Bool)'(True), data : (Bit#(4))'(4'h1)}) : ((((!
        ((((x_1)[(Bit#(4))'(4'h2)]).m_status) == ((Bit#(3))'(3'h0)))) && (!
        ((((x_1)[(Bit#(4))'(4'h2)]).m_next).valid))) &&
        (((((x_1)[(Bit#(4))'(4'h2)]).m_msg).addr) == (x_5)) ? (Struct15
        {valid : (Bool)'(True), data : (Bit#(4))'(4'h2)}) : ((((!
        ((((x_1)[(Bit#(4))'(4'h3)]).m_status) == ((Bit#(3))'(3'h0)))) && (!
        ((((x_1)[(Bit#(4))'(4'h3)]).m_next).valid))) &&
        (((((x_1)[(Bit#(4))'(4'h3)]).m_msg).addr) == (x_5)) ? (Struct15
        {valid : (Bool)'(True), data : (Bit#(4))'(4'h3)}) : ((((!
        ((((x_1)[(Bit#(4))'(4'h4)]).m_status) == ((Bit#(3))'(3'h0)))) && (!
        ((((x_1)[(Bit#(4))'(4'h4)]).m_next).valid))) &&
        (((((x_1)[(Bit#(4))'(4'h4)]).m_msg).addr) == (x_5)) ? (Struct15
        {valid : (Bool)'(True), data : (Bit#(4))'(4'h4)}) : ((((!
        ((((x_1)[(Bit#(4))'(4'h5)]).m_status) == ((Bit#(3))'(3'h0)))) && (!
        ((((x_1)[(Bit#(4))'(4'h5)]).m_next).valid))) &&
        (((((x_1)[(Bit#(4))'(4'h5)]).m_msg).addr) == (x_5)) ? (Struct15
        {valid : (Bool)'(True), data : (Bit#(4))'(4'h5)}) : ((((!
        ((((x_1)[(Bit#(4))'(4'h6)]).m_status) == ((Bit#(3))'(3'h0)))) && (!
        ((((x_1)[(Bit#(4))'(4'h6)]).m_next).valid))) &&
        (((((x_1)[(Bit#(4))'(4'h6)]).m_msg).addr) == (x_5)) ? (Struct15
        {valid : (Bool)'(True), data : (Bit#(4))'(4'h6)}) : ((((!
        ((((x_1)[(Bit#(4))'(4'h7)]).m_status) == ((Bit#(3))'(3'h0)))) && (!
        ((((x_1)[(Bit#(4))'(4'h7)]).m_next).valid))) &&
        (((((x_1)[(Bit#(4))'(4'h7)]).m_msg).addr) == (x_5)) ? (Struct15
        {valid : (Bool)'(True), data : (Bit#(4))'(4'h7)}) : ((((!
        ((((x_1)[(Bit#(4))'(4'h8)]).m_status) == ((Bit#(3))'(3'h0)))) && (!
        ((((x_1)[(Bit#(4))'(4'h8)]).m_next).valid))) &&
        (((((x_1)[(Bit#(4))'(4'h8)]).m_msg).addr) == (x_5)) ? (Struct15
        {valid : (Bool)'(True), data : (Bit#(4))'(4'h8)}) : ((((!
        ((((x_1)[(Bit#(4))'(4'h9)]).m_status) == ((Bit#(3))'(3'h0)))) && (!
        ((((x_1)[(Bit#(4))'(4'h9)]).m_next).valid))) &&
        (((((x_1)[(Bit#(4))'(4'h9)]).m_msg).addr) == (x_5)) ? (Struct15
        {valid : (Bool)'(True), data : (Bit#(4))'(4'h9)}) : ((((!
        ((((x_1)[(Bit#(4))'(4'ha)]).m_status) == ((Bit#(3))'(3'h0)))) && (!
        ((((x_1)[(Bit#(4))'(4'ha)]).m_next).valid))) &&
        (((((x_1)[(Bit#(4))'(4'ha)]).m_msg).addr) == (x_5)) ? (Struct15
        {valid : (Bool)'(True), data : (Bit#(4))'(4'ha)}) : ((((!
        ((((x_1)[(Bit#(4))'(4'hb)]).m_status) == ((Bit#(3))'(3'h0)))) && (!
        ((((x_1)[(Bit#(4))'(4'hb)]).m_next).valid))) &&
        (((((x_1)[(Bit#(4))'(4'hb)]).m_msg).addr) == (x_5)) ? (Struct15
        {valid : (Bool)'(True), data : (Bit#(4))'(4'hb)}) : (Struct15 {valid
        : (Bool)'(False), data : unpack(0)})))))))))))))))))))))))));
        Bool x_7 = ((x_6).valid);
        Bit#(4) x_8 = ((x_6).data);
        Struct5 x_9 = (Struct5 {s_has_slot : x_3, s_conflict : x_7, s_id :
        x_4});
        if (x_3) begin
            Vector#(12, Struct17) x_10 = (update (x_1, x_4, Struct17
            {m_status : (x_7 ? ((Bit#(3))'(3'h1)) : ((Bit#(3))'(3'h3))),
            m_next : Struct15 {valid : (Bool)'(False), data : unpack(0)},
            m_is_ul : unpack(0), m_msg : (x_0).r_msg, m_qidx :
            (x_0).r_msg_from, m_rsb : unpack(0), m_dl_rss_from : unpack(0),
            m_dl_rss_recv : unpack(0), m_dl_rss :
            unpack(0)}));
            let x_13 = ?;
            if (x_7) begin
                Struct17 x_11 = ((x_1)[x_8]);
                Vector#(12, Struct17) x_12 = (update (x_10, x_8, Struct17
                {m_status : (x_11).m_status, m_next : (x_7 ? (Struct15 {valid
                : (Bool)'(True), data : x_4}) : ((x_11).m_next)), m_is_ul :
                (x_11).m_is_ul, m_msg : (x_11).m_msg, m_qidx : (x_11).m_qidx,
                m_rsb : (x_11).m_rsb, m_dl_rss_from : (x_11).m_dl_rss_from,
                m_dl_rss_recv : (x_11).m_dl_rss_recv, m_dl_rss :
                (x_11).m_dl_rss}));
                x_13 = x_12;
            end else begin
                x_13 = x_10;
            end
            rqs_00 <= x_13;
        end else begin

        end
        return x_9;
    endmethod

    method ActionValue#(Struct5) getCRqSlot_00 (Struct4 x_0);
        let x_1 = (rqs_00);
        Struct15 x_2 = (((((x_1)[(Bit#(4))'(4'h4)]).m_status) ==
        ((Bit#(3))'(3'h0)) ? (Struct15 {valid : (Bool)'(True), data :
        (Bit#(4))'(4'h4)}) : (((((x_1)[(Bit#(4))'(4'h5)]).m_status) ==
        ((Bit#(3))'(3'h0)) ? (Struct15 {valid : (Bool)'(True), data :
        (Bit#(4))'(4'h5)}) : (((((x_1)[(Bit#(4))'(4'h6)]).m_status) ==
        ((Bit#(3))'(3'h0)) ? (Struct15 {valid : (Bool)'(True), data :
        (Bit#(4))'(4'h6)}) : (((((x_1)[(Bit#(4))'(4'h7)]).m_status) ==
        ((Bit#(3))'(3'h0)) ? (Struct15 {valid : (Bool)'(True), data :
        (Bit#(4))'(4'h7)}) : (((((x_1)[(Bit#(4))'(4'h8)]).m_status) ==
        ((Bit#(3))'(3'h0)) ? (Struct15 {valid : (Bool)'(True), data :
        (Bit#(4))'(4'h8)}) : (((((x_1)[(Bit#(4))'(4'h9)]).m_status) ==
        ((Bit#(3))'(3'h0)) ? (Struct15 {valid : (Bool)'(True), data :
        (Bit#(4))'(4'h9)}) : (((((x_1)[(Bit#(4))'(4'ha)]).m_status) ==
        ((Bit#(3))'(3'h0)) ? (Struct15 {valid : (Bool)'(True), data :
        (Bit#(4))'(4'ha)}) : (((((x_1)[(Bit#(4))'(4'hb)]).m_status) ==
        ((Bit#(3))'(3'h0)) ? (Struct15 {valid : (Bool)'(True), data :
        (Bit#(4))'(4'hb)}) : (Struct15 {valid : (Bool)'(False), data :
        unpack(0)})))))))))))))))));
        Bool x_3 = ((x_2).valid);
        Bit#(4) x_4 = ((x_2).data);
        Bit#(64) x_5 = (((x_0).r_msg).addr);
        Struct15 x_6 = ((((! ((((x_1)[(Bit#(4))'(4'h0)]).m_status) ==
        ((Bit#(3))'(3'h0)))) && (!
        ((((x_1)[(Bit#(4))'(4'h0)]).m_next).valid))) &&
        (((((x_1)[(Bit#(4))'(4'h0)]).m_msg).addr) == (x_5)) ? (Struct15
        {valid : (Bool)'(True), data : (Bit#(4))'(4'h0)}) : ((((!
        ((((x_1)[(Bit#(4))'(4'h1)]).m_status) == ((Bit#(3))'(3'h0)))) && (!
        ((((x_1)[(Bit#(4))'(4'h1)]).m_next).valid))) &&
        (((((x_1)[(Bit#(4))'(4'h1)]).m_msg).addr) == (x_5)) ? (Struct15
        {valid : (Bool)'(True), data : (Bit#(4))'(4'h1)}) : ((((!
        ((((x_1)[(Bit#(4))'(4'h2)]).m_status) == ((Bit#(3))'(3'h0)))) && (!
        ((((x_1)[(Bit#(4))'(4'h2)]).m_next).valid))) &&
        (((((x_1)[(Bit#(4))'(4'h2)]).m_msg).addr) == (x_5)) ? (Struct15
        {valid : (Bool)'(True), data : (Bit#(4))'(4'h2)}) : ((((!
        ((((x_1)[(Bit#(4))'(4'h3)]).m_status) == ((Bit#(3))'(3'h0)))) && (!
        ((((x_1)[(Bit#(4))'(4'h3)]).m_next).valid))) &&
        (((((x_1)[(Bit#(4))'(4'h3)]).m_msg).addr) == (x_5)) ? (Struct15
        {valid : (Bool)'(True), data : (Bit#(4))'(4'h3)}) : ((((!
        ((((x_1)[(Bit#(4))'(4'h4)]).m_status) == ((Bit#(3))'(3'h0)))) && (!
        ((((x_1)[(Bit#(4))'(4'h4)]).m_next).valid))) &&
        (((((x_1)[(Bit#(4))'(4'h4)]).m_msg).addr) == (x_5)) ? (Struct15
        {valid : (Bool)'(True), data : (Bit#(4))'(4'h4)}) : ((((!
        ((((x_1)[(Bit#(4))'(4'h5)]).m_status) == ((Bit#(3))'(3'h0)))) && (!
        ((((x_1)[(Bit#(4))'(4'h5)]).m_next).valid))) &&
        (((((x_1)[(Bit#(4))'(4'h5)]).m_msg).addr) == (x_5)) ? (Struct15
        {valid : (Bool)'(True), data : (Bit#(4))'(4'h5)}) : ((((!
        ((((x_1)[(Bit#(4))'(4'h6)]).m_status) == ((Bit#(3))'(3'h0)))) && (!
        ((((x_1)[(Bit#(4))'(4'h6)]).m_next).valid))) &&
        (((((x_1)[(Bit#(4))'(4'h6)]).m_msg).addr) == (x_5)) ? (Struct15
        {valid : (Bool)'(True), data : (Bit#(4))'(4'h6)}) : ((((!
        ((((x_1)[(Bit#(4))'(4'h7)]).m_status) == ((Bit#(3))'(3'h0)))) && (!
        ((((x_1)[(Bit#(4))'(4'h7)]).m_next).valid))) &&
        (((((x_1)[(Bit#(4))'(4'h7)]).m_msg).addr) == (x_5)) ? (Struct15
        {valid : (Bool)'(True), data : (Bit#(4))'(4'h7)}) : ((((!
        ((((x_1)[(Bit#(4))'(4'h8)]).m_status) == ((Bit#(3))'(3'h0)))) && (!
        ((((x_1)[(Bit#(4))'(4'h8)]).m_next).valid))) &&
        (((((x_1)[(Bit#(4))'(4'h8)]).m_msg).addr) == (x_5)) ? (Struct15
        {valid : (Bool)'(True), data : (Bit#(4))'(4'h8)}) : ((((!
        ((((x_1)[(Bit#(4))'(4'h9)]).m_status) == ((Bit#(3))'(3'h0)))) && (!
        ((((x_1)[(Bit#(4))'(4'h9)]).m_next).valid))) &&
        (((((x_1)[(Bit#(4))'(4'h9)]).m_msg).addr) == (x_5)) ? (Struct15
        {valid : (Bool)'(True), data : (Bit#(4))'(4'h9)}) : ((((!
        ((((x_1)[(Bit#(4))'(4'ha)]).m_status) == ((Bit#(3))'(3'h0)))) && (!
        ((((x_1)[(Bit#(4))'(4'ha)]).m_next).valid))) &&
        (((((x_1)[(Bit#(4))'(4'ha)]).m_msg).addr) == (x_5)) ? (Struct15
        {valid : (Bool)'(True), data : (Bit#(4))'(4'ha)}) : ((((!
        ((((x_1)[(Bit#(4))'(4'hb)]).m_status) == ((Bit#(3))'(3'h0)))) && (!
        ((((x_1)[(Bit#(4))'(4'hb)]).m_next).valid))) &&
        (((((x_1)[(Bit#(4))'(4'hb)]).m_msg).addr) == (x_5)) ? (Struct15
        {valid : (Bool)'(True), data : (Bit#(4))'(4'hb)}) : (Struct15 {valid
        : (Bool)'(False), data : unpack(0)})))))))))))))))))))))))));
        Bool x_7 = ((x_6).valid);
        Bit#(4) x_8 = ((x_6).data);
        Struct5 x_9 = (Struct5 {s_has_slot : x_3, s_conflict : x_7, s_id :
        x_4});
        if (x_3) begin
            Vector#(12, Struct17) x_10 = (update (x_1, x_4, Struct17
            {m_status : (x_7 ? ((Bit#(3))'(3'h1)) : ((Bit#(3))'(3'h3))),
            m_next : Struct15 {valid : (Bool)'(False), data : unpack(0)},
            m_is_ul : unpack(0), m_msg : (x_0).r_msg, m_qidx :
            (x_0).r_msg_from, m_rsb : unpack(0), m_dl_rss_from : unpack(0),
            m_dl_rss_recv : unpack(0), m_dl_rss :
            unpack(0)}));
            let x_13 = ?;
            if (x_7) begin
                Struct17 x_11 = ((x_1)[x_8]);
                Vector#(12, Struct17) x_12 = (update (x_10, x_8, Struct17
                {m_status : (x_11).m_status, m_next : (x_7 ? (Struct15 {valid
                : (Bool)'(True), data : x_4}) : ((x_11).m_next)), m_is_ul :
                (x_11).m_is_ul, m_msg : (x_11).m_msg, m_qidx : (x_11).m_qidx,
                m_rsb : (x_11).m_rsb, m_dl_rss_from : (x_11).m_dl_rss_from,
                m_dl_rss_recv : (x_11).m_dl_rss_recv, m_dl_rss :
                (x_11).m_dl_rss}));
                x_13 = x_12;
            end else begin
                x_13 = x_10;
            end
            rqs_00 <= x_13;
        end else begin

        end
        return x_9;
    endmethod

    method ActionValue#(Struct16) getWait_00 ();
        let x_1 = (rqs_00);
        Struct15 x_2 = (((((x_1)[(Bit#(4))'(4'h0)]).m_status) ==
        ((Bit#(3))'(3'h2)) ? (Struct15 {valid : (Bool)'(True), data :
        (Bit#(4))'(4'h0)}) : (((((x_1)[(Bit#(4))'(4'h1)]).m_status) ==
        ((Bit#(3))'(3'h2)) ? (Struct15 {valid : (Bool)'(True), data :
        (Bit#(4))'(4'h1)}) : (((((x_1)[(Bit#(4))'(4'h2)]).m_status) ==
        ((Bit#(3))'(3'h2)) ? (Struct15 {valid : (Bool)'(True), data :
        (Bit#(4))'(4'h2)}) : (((((x_1)[(Bit#(4))'(4'h3)]).m_status) ==
        ((Bit#(3))'(3'h2)) ? (Struct15 {valid : (Bool)'(True), data :
        (Bit#(4))'(4'h3)}) : (((((x_1)[(Bit#(4))'(4'h4)]).m_status) ==
        ((Bit#(3))'(3'h2)) ? (Struct15 {valid : (Bool)'(True), data :
        (Bit#(4))'(4'h4)}) : (((((x_1)[(Bit#(4))'(4'h5)]).m_status) ==
        ((Bit#(3))'(3'h2)) ? (Struct15 {valid : (Bool)'(True), data :
        (Bit#(4))'(4'h5)}) : (((((x_1)[(Bit#(4))'(4'h6)]).m_status) ==
        ((Bit#(3))'(3'h2)) ? (Struct15 {valid : (Bool)'(True), data :
        (Bit#(4))'(4'h6)}) : (((((x_1)[(Bit#(4))'(4'h7)]).m_status) ==
        ((Bit#(3))'(3'h2)) ? (Struct15 {valid : (Bool)'(True), data :
        (Bit#(4))'(4'h7)}) : (((((x_1)[(Bit#(4))'(4'h8)]).m_status) ==
        ((Bit#(3))'(3'h2)) ? (Struct15 {valid : (Bool)'(True), data :
        (Bit#(4))'(4'h8)}) : (((((x_1)[(Bit#(4))'(4'h9)]).m_status) ==
        ((Bit#(3))'(3'h2)) ? (Struct15 {valid : (Bool)'(True), data :
        (Bit#(4))'(4'h9)}) : (((((x_1)[(Bit#(4))'(4'ha)]).m_status) ==
        ((Bit#(3))'(3'h2)) ? (Struct15 {valid : (Bool)'(True), data :
        (Bit#(4))'(4'ha)}) : (((((x_1)[(Bit#(4))'(4'hb)]).m_status) ==
        ((Bit#(3))'(3'h2)) ? (Struct15 {valid : (Bool)'(True), data :
        (Bit#(4))'(4'hb)}) : (Struct15 {valid : (Bool)'(False), data :
        unpack(0)})))))))))))))))))))))))));
        let x_6 = ?;
        if ((x_2).valid) begin
            Bit#(4) x_3 = ((x_2).data);
            Struct17 x_4 = ((x_1)[x_3]);
            rqs_00 <= update (x_1, x_3, Struct17 {m_status :
            (Bit#(3))'(3'h4), m_next : (x_4).m_next, m_is_ul : (x_4).m_is_ul,
            m_msg : (x_4).m_msg, m_qidx : (x_4).m_qidx, m_rsb : (x_4).m_rsb,
            m_dl_rss_from : (x_4).m_dl_rss_from, m_dl_rss_recv :
            (x_4).m_dl_rss_recv, m_dl_rss : (x_4).m_dl_rss});
            Struct4 x_5 = (Struct4 {r_id : x_3, r_msg : (x_4).m_msg,
            r_msg_from : (x_4).m_qidx});
            x_6 = Struct16 {valid : (Bool)'(True), data : x_5};
        end else begin
            x_6 = Struct16 {valid : (Bool)'(False), data : unpack(0)};
        end
        return x_6;
    endmethod

    method Action registerUL_00 (Struct22 x_0);
        let x_1 = (rqs_00);
        Bit#(4) x_2 = ((x_0).r_id);
        Struct17 x_3 = ((x_1)[x_2]);
        Struct17 x_4 = (Struct17 {m_status : (Bit#(3))'(3'h4), m_next :
        (x_3).m_next, m_is_ul : (Bool)'(True), m_msg : (x_3).m_msg, m_qidx :
        zeroExtend((x_0).r_ul_rsbTo), m_rsb : (x_0).r_ul_rsb, m_dl_rss_from :
        unpack(0), m_dl_rss_recv : unpack(0), m_dl_rss : unpack(0)});
        rqs_00 <= update (x_1, x_2, x_4);
    endmethod

    method Action registerDL_00 (Struct23 x_0);
        let x_1 = (rqs_00);
        Bit#(4) x_2 = ((x_0).r_id);
        Struct17 x_3 = ((x_1)[x_2]);
        Struct17 x_4 = (Struct17 {m_status : (Bit#(3))'(3'h4), m_next :
        (x_3).m_next, m_is_ul : (Bool)'(False), m_msg : (x_3).m_msg, m_qidx :
        (x_0).r_dl_rsbTo, m_rsb : (x_0).r_dl_rsb, m_dl_rss_from :
        (x_0).r_dl_rss_from, m_dl_rss_recv : unpack(0), m_dl_rss :
        unpack(0)});
        rqs_00 <= update (x_1, x_2, x_4);
    endmethod

    method ActionValue#(Bit#(4)) getULImm_00 (Struct1 x_0);
        let x_1 = (rqs_00);
        Struct15 x_2 = (((((x_1)[(Bit#(4))'(4'h4)]).m_status) ==
        ((Bit#(3))'(3'h0)) ? (Struct15 {valid : (Bool)'(True), data :
        (Bit#(4))'(4'h8)}) : (((((x_1)[(Bit#(4))'(4'h5)]).m_status) ==
        ((Bit#(3))'(3'h0)) ? (Struct15 {valid : (Bool)'(True), data :
        (Bit#(4))'(4'h9)}) : (((((x_1)[(Bit#(4))'(4'h6)]).m_status) ==
        ((Bit#(3))'(3'h0)) ? (Struct15 {valid : (Bool)'(True), data :
        (Bit#(4))'(4'ha)}) : (((((x_1)[(Bit#(4))'(4'h7)]).m_status) ==
        ((Bit#(3))'(3'h0)) ? (Struct15 {valid : (Bool)'(True), data :
        (Bit#(4))'(4'hb)}) : (((((x_1)[(Bit#(4))'(4'h8)]).m_status) ==
        ((Bit#(3))'(3'h0)) ? (Struct15 {valid : (Bool)'(True), data :
        (Bit#(4))'(4'hc)}) : (((((x_1)[(Bit#(4))'(4'h9)]).m_status) ==
        ((Bit#(3))'(3'h0)) ? (Struct15 {valid : (Bool)'(True), data :
        (Bit#(4))'(4'hd)}) : (((((x_1)[(Bit#(4))'(4'ha)]).m_status) ==
        ((Bit#(3))'(3'h0)) ? (Struct15 {valid : (Bool)'(True), data :
        (Bit#(4))'(4'he)}) : (((((x_1)[(Bit#(4))'(4'hb)]).m_status) ==
        ((Bit#(3))'(3'h0)) ? (Struct15 {valid : (Bool)'(True), data :
        (Bit#(4))'(4'hf)}) : (Struct15 {valid : (Bool)'(False), data :
        unpack(0)})))))))))))))))));
        when ((x_2).valid, noAction);
        Bit#(4) x_3 = ((x_2).data);
        rqs_00 <= update (x_1, x_3, Struct17 {m_status : (Bit#(3))'(3'h4),
        m_next : Struct15 {valid : (Bool)'(False), data : unpack(0)}, m_is_ul
        : (Bool)'(True), m_msg : x_0, m_qidx : unpack(0), m_rsb :
        (Bool)'(False), m_dl_rss_from : unpack(0), m_dl_rss_recv : unpack(0),
        m_dl_rss : unpack(0)});
        return x_3;
    endmethod

    method Action transferUpDown_00 (Struct26 x_0);
        let x_1 = (rqs_00);
        Bit#(4) x_2 = ((x_0).r_id);
        Struct17 x_3 = ((x_1)[x_2]);
        Struct17 x_4 = (Struct17 {m_status : (Bit#(3))'(3'h4), m_next :
        (x_3).m_next, m_is_ul : (Bool)'(False), m_msg : (x_3).m_msg, m_qidx :
        (x_3).m_qidx, m_rsb : (x_3).m_rsb, m_dl_rss_from :
        (x_0).r_dl_rss_from, m_dl_rss_recv : unpack(0), m_dl_rss :
        unpack(0)});
        rqs_00 <= update (x_1, x_2, x_4);
    endmethod

    method ActionValue#(Bit#(4)) findUL_00 (Bit#(64) x_0);
        let x_1 = (rqs_00);
        Bit#(4) x_2 = (((((((x_1)[(Bit#(4))'(4'h4)]).m_status) ==
        ((Bit#(3))'(3'h4))) && (((x_1)[(Bit#(4))'(4'h4)]).m_is_ul)) &&
        (((((x_1)[(Bit#(4))'(4'h4)]).m_msg).addr) == (x_0)) ?
        ((Bit#(4))'(4'h4)) : (((((((x_1)[(Bit#(4))'(4'h5)]).m_status) ==
        ((Bit#(3))'(3'h4))) && (((x_1)[(Bit#(4))'(4'h5)]).m_is_ul)) &&
        (((((x_1)[(Bit#(4))'(4'h5)]).m_msg).addr) == (x_0)) ?
        ((Bit#(4))'(4'h5)) : (((((((x_1)[(Bit#(4))'(4'h6)]).m_status) ==
        ((Bit#(3))'(3'h4))) && (((x_1)[(Bit#(4))'(4'h6)]).m_is_ul)) &&
        (((((x_1)[(Bit#(4))'(4'h6)]).m_msg).addr) == (x_0)) ?
        ((Bit#(4))'(4'h6)) : (((((((x_1)[(Bit#(4))'(4'h7)]).m_status) ==
        ((Bit#(3))'(3'h4))) && (((x_1)[(Bit#(4))'(4'h7)]).m_is_ul)) &&
        (((((x_1)[(Bit#(4))'(4'h7)]).m_msg).addr) == (x_0)) ?
        ((Bit#(4))'(4'h7)) : (((((((x_1)[(Bit#(4))'(4'h8)]).m_status) ==
        ((Bit#(3))'(3'h4))) && (((x_1)[(Bit#(4))'(4'h8)]).m_is_ul)) &&
        (((((x_1)[(Bit#(4))'(4'h8)]).m_msg).addr) == (x_0)) ?
        ((Bit#(4))'(4'h8)) : (((((((x_1)[(Bit#(4))'(4'h9)]).m_status) ==
        ((Bit#(3))'(3'h4))) && (((x_1)[(Bit#(4))'(4'h9)]).m_is_ul)) &&
        (((((x_1)[(Bit#(4))'(4'h9)]).m_msg).addr) == (x_0)) ?
        ((Bit#(4))'(4'h9)) : (((((((x_1)[(Bit#(4))'(4'ha)]).m_status) ==
        ((Bit#(3))'(3'h4))) && (((x_1)[(Bit#(4))'(4'ha)]).m_is_ul)) &&
        (((((x_1)[(Bit#(4))'(4'ha)]).m_msg).addr) == (x_0)) ?
        ((Bit#(4))'(4'ha)) : (((((((x_1)[(Bit#(4))'(4'hb)]).m_status) ==
        ((Bit#(3))'(3'h4))) && (((x_1)[(Bit#(4))'(4'hb)]).m_is_ul)) &&
        (((((x_1)[(Bit#(4))'(4'hb)]).m_msg).addr) == (x_0)) ?
        ((Bit#(4))'(4'hb)) : (unpack(0))))))))))))))))));
        return x_2;
    endmethod

    method ActionValue#(Bit#(4)) findDL_00 (Bit#(64) x_0);
        let x_1 = (rqs_00);
        Bit#(4) x_2 = (((((((x_1)[(Bit#(4))'(4'h0)]).m_status) ==
        ((Bit#(3))'(3'h4))) && (! (((x_1)[(Bit#(4))'(4'h0)]).m_is_ul))) &&
        (((((x_1)[(Bit#(4))'(4'h0)]).m_msg).addr) == (x_0)) ?
        ((Bit#(4))'(4'h0)) : (((((((x_1)[(Bit#(4))'(4'h1)]).m_status) ==
        ((Bit#(3))'(3'h4))) && (! (((x_1)[(Bit#(4))'(4'h1)]).m_is_ul))) &&
        (((((x_1)[(Bit#(4))'(4'h1)]).m_msg).addr) == (x_0)) ?
        ((Bit#(4))'(4'h1)) : (((((((x_1)[(Bit#(4))'(4'h2)]).m_status) ==
        ((Bit#(3))'(3'h4))) && (! (((x_1)[(Bit#(4))'(4'h2)]).m_is_ul))) &&
        (((((x_1)[(Bit#(4))'(4'h2)]).m_msg).addr) == (x_0)) ?
        ((Bit#(4))'(4'h2)) : (((((((x_1)[(Bit#(4))'(4'h3)]).m_status) ==
        ((Bit#(3))'(3'h4))) && (! (((x_1)[(Bit#(4))'(4'h3)]).m_is_ul))) &&
        (((((x_1)[(Bit#(4))'(4'h3)]).m_msg).addr) == (x_0)) ?
        ((Bit#(4))'(4'h3)) : (((((((x_1)[(Bit#(4))'(4'h4)]).m_status) ==
        ((Bit#(3))'(3'h4))) && (! (((x_1)[(Bit#(4))'(4'h4)]).m_is_ul))) &&
        (((((x_1)[(Bit#(4))'(4'h4)]).m_msg).addr) == (x_0)) ?
        ((Bit#(4))'(4'h4)) : (((((((x_1)[(Bit#(4))'(4'h5)]).m_status) ==
        ((Bit#(3))'(3'h4))) && (! (((x_1)[(Bit#(4))'(4'h5)]).m_is_ul))) &&
        (((((x_1)[(Bit#(4))'(4'h5)]).m_msg).addr) == (x_0)) ?
        ((Bit#(4))'(4'h5)) : (((((((x_1)[(Bit#(4))'(4'h6)]).m_status) ==
        ((Bit#(3))'(3'h4))) && (! (((x_1)[(Bit#(4))'(4'h6)]).m_is_ul))) &&
        (((((x_1)[(Bit#(4))'(4'h6)]).m_msg).addr) == (x_0)) ?
        ((Bit#(4))'(4'h6)) : (((((((x_1)[(Bit#(4))'(4'h7)]).m_status) ==
        ((Bit#(3))'(3'h4))) && (! (((x_1)[(Bit#(4))'(4'h7)]).m_is_ul))) &&
        (((((x_1)[(Bit#(4))'(4'h7)]).m_msg).addr) == (x_0)) ?
        ((Bit#(4))'(4'h7)) : (((((((x_1)[(Bit#(4))'(4'h8)]).m_status) ==
        ((Bit#(3))'(3'h4))) && (! (((x_1)[(Bit#(4))'(4'h8)]).m_is_ul))) &&
        (((((x_1)[(Bit#(4))'(4'h8)]).m_msg).addr) == (x_0)) ?
        ((Bit#(4))'(4'h8)) : (((((((x_1)[(Bit#(4))'(4'h9)]).m_status) ==
        ((Bit#(3))'(3'h4))) && (! (((x_1)[(Bit#(4))'(4'h9)]).m_is_ul))) &&
        (((((x_1)[(Bit#(4))'(4'h9)]).m_msg).addr) == (x_0)) ?
        ((Bit#(4))'(4'h9)) : (((((((x_1)[(Bit#(4))'(4'ha)]).m_status) ==
        ((Bit#(3))'(3'h4))) && (! (((x_1)[(Bit#(4))'(4'ha)]).m_is_ul))) &&
        (((((x_1)[(Bit#(4))'(4'ha)]).m_msg).addr) == (x_0)) ?
        ((Bit#(4))'(4'ha)) : (((((((x_1)[(Bit#(4))'(4'hb)]).m_status) ==
        ((Bit#(3))'(3'h4))) && (! (((x_1)[(Bit#(4))'(4'hb)]).m_is_ul))) &&
        (((((x_1)[(Bit#(4))'(4'hb)]).m_msg).addr) == (x_0)) ?
        ((Bit#(4))'(4'hb)) : (unpack(0))))))))))))))))))))))))));
        return x_2;
    endmethod

    method Action releaseMSHR_00 (Bit#(4) x_0);
        let x_1 = (rqs_00);
        Struct17 x_2 = ((x_1)[x_0]);
        Vector#(12, Struct17) x_3 = (update (x_1, x_0,
        unpack(0)));
        let x_7 = ?;
        if (((x_2).m_next).valid) begin
            Bit#(4) x_4 = (((x_2).m_next).data);
            Struct17 x_5 = ((x_1)[x_4]);
            Vector#(12, Struct17) x_6 = (update (x_3, x_4, Struct17 {m_status
            : (Bit#(3))'(3'h2), m_next : (x_5).m_next, m_is_ul :
            (x_5).m_is_ul, m_msg : (x_5).m_msg, m_qidx : (x_5).m_qidx, m_rsb
            : (x_5).m_rsb, m_dl_rss_from : (x_5).m_dl_rss_from, m_dl_rss_recv
            : (x_5).m_dl_rss_recv, m_dl_rss : (x_5).m_dl_rss}));
            x_7 = x_6;
        end else begin
            x_7 = x_3;
        end
        rqs_00 <= x_7;
    endmethod

    method Action addRs_00 (Struct9 x_0);
        let x_1 = (rqs_00);
        Bit#(4) x_2 = ((x_0).r_id);
        Struct17 x_3 = ((x_1)[x_2]);
        Struct17 x_4 = (Struct17 {m_status : (x_3).m_status, m_next :
        (x_3).m_next, m_is_ul : (x_3).m_is_ul, m_msg : (x_3).m_msg, m_qidx :
        (x_3).m_qidx, m_rsb : (x_3).m_rsb, m_dl_rss_from :
        (x_3).m_dl_rss_from, m_dl_rss_recv : ((x_3).m_dl_rss_recv) |
        (((Bit#(2))'(2'h1)) << ((x_0).r_midx)), m_dl_rss : update
        ((x_3).m_dl_rss, (x_0).r_midx, (x_0).r_msg)});
        rqs_00 <= update (x_1, x_2, x_4);
    endmethod

    method ActionValue#(Struct8) getRsReady_00 ();
        let x_1 = (rqs_00);
        Struct15 x_2 = (((((((x_1)[(Bit#(4))'(4'h0)]).m_status) ==
        ((Bit#(3))'(3'h4))) && (! (((x_1)[(Bit#(4))'(4'h0)]).m_is_ul))) &&
        ((((x_1)[(Bit#(4))'(4'h0)]).m_dl_rss_from) ==
        (((x_1)[(Bit#(4))'(4'h0)]).m_dl_rss_recv)) ? (Struct15 {valid :
        (Bool)'(True), data : (Bit#(4))'(4'h0)}) :
        (((((((x_1)[(Bit#(4))'(4'h1)]).m_status) == ((Bit#(3))'(3'h4))) && (!
        (((x_1)[(Bit#(4))'(4'h1)]).m_is_ul))) &&
        ((((x_1)[(Bit#(4))'(4'h1)]).m_dl_rss_from) ==
        (((x_1)[(Bit#(4))'(4'h1)]).m_dl_rss_recv)) ? (Struct15 {valid :
        (Bool)'(True), data : (Bit#(4))'(4'h1)}) :
        (((((((x_1)[(Bit#(4))'(4'h2)]).m_status) == ((Bit#(3))'(3'h4))) && (!
        (((x_1)[(Bit#(4))'(4'h2)]).m_is_ul))) &&
        ((((x_1)[(Bit#(4))'(4'h2)]).m_dl_rss_from) ==
        (((x_1)[(Bit#(4))'(4'h2)]).m_dl_rss_recv)) ? (Struct15 {valid :
        (Bool)'(True), data : (Bit#(4))'(4'h2)}) :
        (((((((x_1)[(Bit#(4))'(4'h3)]).m_status) == ((Bit#(3))'(3'h4))) && (!
        (((x_1)[(Bit#(4))'(4'h3)]).m_is_ul))) &&
        ((((x_1)[(Bit#(4))'(4'h3)]).m_dl_rss_from) ==
        (((x_1)[(Bit#(4))'(4'h3)]).m_dl_rss_recv)) ? (Struct15 {valid :
        (Bool)'(True), data : (Bit#(4))'(4'h3)}) :
        (((((((x_1)[(Bit#(4))'(4'h4)]).m_status) == ((Bit#(3))'(3'h4))) && (!
        (((x_1)[(Bit#(4))'(4'h4)]).m_is_ul))) &&
        ((((x_1)[(Bit#(4))'(4'h4)]).m_dl_rss_from) ==
        (((x_1)[(Bit#(4))'(4'h4)]).m_dl_rss_recv)) ? (Struct15 {valid :
        (Bool)'(True), data : (Bit#(4))'(4'h4)}) :
        (((((((x_1)[(Bit#(4))'(4'h5)]).m_status) == ((Bit#(3))'(3'h4))) && (!
        (((x_1)[(Bit#(4))'(4'h5)]).m_is_ul))) &&
        ((((x_1)[(Bit#(4))'(4'h5)]).m_dl_rss_from) ==
        (((x_1)[(Bit#(4))'(4'h5)]).m_dl_rss_recv)) ? (Struct15 {valid :
        (Bool)'(True), data : (Bit#(4))'(4'h5)}) :
        (((((((x_1)[(Bit#(4))'(4'h6)]).m_status) == ((Bit#(3))'(3'h4))) && (!
        (((x_1)[(Bit#(4))'(4'h6)]).m_is_ul))) &&
        ((((x_1)[(Bit#(4))'(4'h6)]).m_dl_rss_from) ==
        (((x_1)[(Bit#(4))'(4'h6)]).m_dl_rss_recv)) ? (Struct15 {valid :
        (Bool)'(True), data : (Bit#(4))'(4'h6)}) :
        (((((((x_1)[(Bit#(4))'(4'h7)]).m_status) == ((Bit#(3))'(3'h4))) && (!
        (((x_1)[(Bit#(4))'(4'h7)]).m_is_ul))) &&
        ((((x_1)[(Bit#(4))'(4'h7)]).m_dl_rss_from) ==
        (((x_1)[(Bit#(4))'(4'h7)]).m_dl_rss_recv)) ? (Struct15 {valid :
        (Bool)'(True), data : (Bit#(4))'(4'h7)}) :
        (((((((x_1)[(Bit#(4))'(4'h8)]).m_status) == ((Bit#(3))'(3'h4))) && (!
        (((x_1)[(Bit#(4))'(4'h8)]).m_is_ul))) &&
        ((((x_1)[(Bit#(4))'(4'h8)]).m_dl_rss_from) ==
        (((x_1)[(Bit#(4))'(4'h8)]).m_dl_rss_recv)) ? (Struct15 {valid :
        (Bool)'(True), data : (Bit#(4))'(4'h8)}) :
        (((((((x_1)[(Bit#(4))'(4'h9)]).m_status) == ((Bit#(3))'(3'h4))) && (!
        (((x_1)[(Bit#(4))'(4'h9)]).m_is_ul))) &&
        ((((x_1)[(Bit#(4))'(4'h9)]).m_dl_rss_from) ==
        (((x_1)[(Bit#(4))'(4'h9)]).m_dl_rss_recv)) ? (Struct15 {valid :
        (Bool)'(True), data : (Bit#(4))'(4'h9)}) :
        (((((((x_1)[(Bit#(4))'(4'ha)]).m_status) == ((Bit#(3))'(3'h4))) && (!
        (((x_1)[(Bit#(4))'(4'ha)]).m_is_ul))) &&
        ((((x_1)[(Bit#(4))'(4'ha)]).m_dl_rss_from) ==
        (((x_1)[(Bit#(4))'(4'ha)]).m_dl_rss_recv)) ? (Struct15 {valid :
        (Bool)'(True), data : (Bit#(4))'(4'ha)}) :
        (((((((x_1)[(Bit#(4))'(4'hb)]).m_status) == ((Bit#(3))'(3'h4))) && (!
        (((x_1)[(Bit#(4))'(4'hb)]).m_is_ul))) &&
        ((((x_1)[(Bit#(4))'(4'hb)]).m_dl_rss_from) ==
        (((x_1)[(Bit#(4))'(4'hb)]).m_dl_rss_recv)) ? (Struct15 {valid :
        (Bool)'(True), data : (Bit#(4))'(4'hb)}) : (Struct15 {valid :
        (Bool)'(False), data : unpack(0)})))))))))))))))))))))))));
        when ((x_2).valid, noAction);
        Bit#(4) x_3 = ((x_2).data);
        Struct17 x_4 = ((x_1)[x_3]);
        Struct17 x_5 = (Struct17 {m_status : (Bit#(3))'(3'h5), m_next :
        (x_4).m_next, m_is_ul : (x_4).m_is_ul, m_msg : (x_4).m_msg, m_qidx :
        (x_4).m_qidx, m_rsb : (x_4).m_rsb, m_dl_rss_from :
        (x_4).m_dl_rss_from, m_dl_rss_recv : (x_4).m_dl_rss_recv, m_dl_rss :
        (x_4).m_dl_rss});
        rqs_00 <= update (x_1, x_3, x_5);
        Struct8 x_6 = (Struct8 {r_id : x_3, r_addr :
        ((x_4).m_msg).addr});
        return x_6;
    endmethod
endmodule

interface Module26;
    method Action enq_fifoPInput000 (Struct2 x_0);
    method ActionValue#(Struct2) deq_fifoPInput000 ();
endinterface

module mkModule26
    (Module26);
    Reg#(Struct2) elt_fifoPInput000 <- mkReg(unpack(0));
    Reg#(Bool) full_fifoPInput000 <- mkReg(unpack(0));
    Reg#(Bool) countDone_fifoPInput000 <- mkReg(unpack(0));
    Reg#(Bit#(18)) counter_fifoPInput000 <- mkReg(unpack(0));

    rule count_fifoPInput000;

        let x_0 = (countDone_fifoPInput000);
        when (! (x_0), noAction);
        let x_1 = (counter_fifoPInput000);
        counter_fifoPInput000 <= (x_1) + ((Bit#(18))'(18'h1));
        let x_2 =
        (full_fifoPInput000);
        if (((x_1) == ((Bit#(18))'(18'h3ffff))) && (x_2)) begin
            let x_3 =
            (elt_fifoPInput000);
            $display ("-- INPUT fifoPInput000: %x %x %b %x", (x_3).in_msg_from, ((x_3).in_msg).id, ((x_3).in_msg).type_, ((x_3).in_msg).addr);
            countDone_fifoPInput000 <= (Bool)'(True);
        end else begin

        end
    endrule

    method Action enq_fifoPInput000 (Struct2 x_0);
        let x_1 = (full_fifoPInput000);
        when (! (x_1), noAction);
        elt_fifoPInput000 <= x_0;
        full_fifoPInput000 <= (Bool)'(True);
    endmethod

    method ActionValue#(Struct2) deq_fifoPInput000 ();
        let x_1 = (full_fifoPInput000);
        when (x_1, noAction);
        let x_2 = (elt_fifoPInput000);
        full_fifoPInput000 <= (Bool)'(False);
        return x_2;
    endmethod
endmodule

interface Module27;
    method Action enq_fifoCInput_000 (Struct2 x_0);
    method ActionValue#(Struct2) deq_fifoCInput_000 ();
endinterface

module mkModule27
    (Module27);
    Reg#(Struct2) elt_fifoCInput_000 <- mkReg(unpack(0));
    Reg#(Bool) full_fifoCInput_000 <- mkReg(unpack(0));
    Reg#(Bool) countDone_fifoCInput_000 <- mkReg(unpack(0));
    Reg#(Bit#(18)) counter_fifoCInput_000 <- mkReg(unpack(0));

    rule count_fifoCInput_000;

        let x_0 = (countDone_fifoCInput_000);
        when (! (x_0), noAction);
        let x_1 = (counter_fifoCInput_000);
        counter_fifoCInput_000 <= (x_1) + ((Bit#(18))'(18'h1));
        let x_2 =
        (full_fifoCInput_000);
        if (((x_1) == ((Bit#(18))'(18'h3ffff))) && (x_2)) begin
            let x_3 =
            (elt_fifoCInput_000);
            $display ("-- INPUT fifoCInput_000: %x %x %b %x", (x_3).in_msg_from, ((x_3).in_msg).id, ((x_3).in_msg).type_, ((x_3).in_msg).addr);
            countDone_fifoCInput_000 <= (Bool)'(True);
        end else begin

        end
    endrule

    method Action enq_fifoCInput_000 (Struct2 x_0);
        let x_1 = (full_fifoCInput_000);
        when (! (x_1), noAction);
        elt_fifoCInput_000 <= x_0;
        full_fifoCInput_000 <= (Bool)'(True);
    endmethod

    method ActionValue#(Struct2) deq_fifoCInput_000 ();
        let x_1 = (full_fifoCInput_000);
        when (x_1, noAction);
        let x_2 = (elt_fifoCInput_000);
        full_fifoCInput_000 <= (Bool)'(False);
        return x_2;
    endmethod
endmodule

interface Module28;
    method Action enq_fifoN2I_parent_000 (Struct42 x_0);
    method ActionValue#(Struct42) deq_fifoN2I_parent_000 ();
endinterface

module mkModule28
    (Module28);
    Reg#(Struct42) elt_fifoN2I_parent_000 <- mkReg(unpack(0));
    Reg#(Bool) full_fifoN2I_parent_000 <- mkReg(unpack(0));
    Reg#(Bool) countDone_fifoN2I_parent_000 <- mkReg(unpack(0));
    Reg#(Bit#(18)) counter_fifoN2I_parent_000 <- mkReg(unpack(0));

    rule count_fifoN2I_parent_000;

        let x_0 = (countDone_fifoN2I_parent_000);
        when (! (x_0), noAction);
        let x_1 = (counter_fifoN2I_parent_000);
        counter_fifoN2I_parent_000 <= (x_1) + ((Bit#(18))'(18'h1));
        let x_2 =
        (full_fifoN2I_parent_000);
        if (((x_1) == ((Bit#(18))'(18'h3ffff))) && (x_2)) begin
            let x_3 =
            (elt_fifoN2I_parent_000);
            $display ("-- IR fifoN2I_parent_000: %b %b %x %b %x %x %x %b %x", (x_3).ir_is_rs_rel, (x_3).ir_is_rs_acc, ((x_3).ir_msg).id, ((x_3).ir_msg).type_, ((x_3).ir_msg).addr, (x_3).ir_msg_from, (x_3).ir_mshr_id, ((x_3).ir_by_victim).valid, ((x_3).ir_by_victim).data);
            countDone_fifoN2I_parent_000 <= (Bool)'(True);
        end else begin

        end
    endrule

    method Action enq_fifoN2I_parent_000 (Struct42 x_0);
        let x_1 = (full_fifoN2I_parent_000);
        when (! (x_1), noAction);
        elt_fifoN2I_parent_000 <= x_0;
        full_fifoN2I_parent_000 <= (Bool)'(True);
    endmethod

    method ActionValue#(Struct42) deq_fifoN2I_parent_000 ();
        let x_1 = (full_fifoN2I_parent_000);
        when (x_1, noAction);
        let x_2 = (elt_fifoN2I_parent_000);
        full_fifoN2I_parent_000 <= (Bool)'(False);
        return x_2;
    endmethod
endmodule

interface Module29;
    method Action enq_fifoI2L_parent_000 (Struct42 x_0);
    method ActionValue#(Struct42) deq_fifoI2L_parent_000 ();
endinterface

module mkModule29
    (Module29);
    Reg#(Struct42) elt_fifoI2L_parent_000 <- mkReg(unpack(0));
    Reg#(Bool) full_fifoI2L_parent_000 <- mkReg(unpack(0));
    Reg#(Bool) countDone_fifoI2L_parent_000 <- mkReg(unpack(0));
    Reg#(Bit#(18)) counter_fifoI2L_parent_000 <- mkReg(unpack(0));

    rule count_fifoI2L_parent_000;

        let x_0 = (countDone_fifoI2L_parent_000);
        when (! (x_0), noAction);
        let x_1 = (counter_fifoI2L_parent_000);
        counter_fifoI2L_parent_000 <= (x_1) + ((Bit#(18))'(18'h1));
        let x_2 =
        (full_fifoI2L_parent_000);
        if (((x_1) == ((Bit#(18))'(18'h3ffff))) && (x_2)) begin
            let x_3 =
            (elt_fifoI2L_parent_000);
            $display ("-- IR fifoI2L_parent_000: %b %b %x %b %x %x %x %b %x", (x_3).ir_is_rs_rel, (x_3).ir_is_rs_acc, ((x_3).ir_msg).id, ((x_3).ir_msg).type_, ((x_3).ir_msg).addr, (x_3).ir_msg_from, (x_3).ir_mshr_id, ((x_3).ir_by_victim).valid, ((x_3).ir_by_victim).data);
            countDone_fifoI2L_parent_000 <= (Bool)'(True);
        end else begin

        end
    endrule

    method Action enq_fifoI2L_parent_000 (Struct42 x_0);
        let x_1 = (full_fifoI2L_parent_000);
        when (! (x_1), noAction);
        elt_fifoI2L_parent_000 <= x_0;
        full_fifoI2L_parent_000 <= (Bool)'(True);
    endmethod

    method ActionValue#(Struct42) deq_fifoI2L_parent_000 ();
        let x_1 = (full_fifoI2L_parent_000);
        when (x_1, noAction);
        let x_2 = (elt_fifoI2L_parent_000);
        full_fifoI2L_parent_000 <= (Bool)'(False);
        return x_2;
    endmethod
endmodule

interface Module30;
    method Action enq_fifoN2I_child_000 (Struct42 x_0);
    method ActionValue#(Struct42) deq_fifoN2I_child_000 ();
endinterface

module mkModule30
    (Module30);
    Reg#(Struct42) elt_fifoN2I_child_000 <- mkReg(unpack(0));
    Reg#(Bool) full_fifoN2I_child_000 <- mkReg(unpack(0));
    Reg#(Bool) countDone_fifoN2I_child_000 <- mkReg(unpack(0));
    Reg#(Bit#(18)) counter_fifoN2I_child_000 <- mkReg(unpack(0));

    rule count_fifoN2I_child_000;

        let x_0 = (countDone_fifoN2I_child_000);
        when (! (x_0), noAction);
        let x_1 = (counter_fifoN2I_child_000);
        counter_fifoN2I_child_000 <= (x_1) + ((Bit#(18))'(18'h1));
        let x_2 =
        (full_fifoN2I_child_000);
        if (((x_1) == ((Bit#(18))'(18'h3ffff))) && (x_2)) begin
            let x_3 =
            (elt_fifoN2I_child_000);
            $display ("-- IR fifoN2I_child_000: %b %b %x %b %x %x %x %b %x", (x_3).ir_is_rs_rel, (x_3).ir_is_rs_acc, ((x_3).ir_msg).id, ((x_3).ir_msg).type_, ((x_3).ir_msg).addr, (x_3).ir_msg_from, (x_3).ir_mshr_id, ((x_3).ir_by_victim).valid, ((x_3).ir_by_victim).data);
            countDone_fifoN2I_child_000 <= (Bool)'(True);
        end else begin

        end
    endrule

    method Action enq_fifoN2I_child_000 (Struct42 x_0);
        let x_1 = (full_fifoN2I_child_000);
        when (! (x_1), noAction);
        elt_fifoN2I_child_000 <= x_0;
        full_fifoN2I_child_000 <= (Bool)'(True);
    endmethod

    method ActionValue#(Struct42) deq_fifoN2I_child_000 ();
        let x_1 = (full_fifoN2I_child_000);
        when (x_1, noAction);
        let x_2 = (elt_fifoN2I_child_000);
        full_fifoN2I_child_000 <= (Bool)'(False);
        return x_2;
    endmethod
endmodule

interface Module31;
    method Action enq_fifoI2L_child_000 (Struct42 x_0);
    method ActionValue#(Struct42) deq_fifoI2L_child_000 ();
endinterface

module mkModule31
    (Module31);
    Reg#(Struct42) elt_fifoI2L_child_000 <- mkReg(unpack(0));
    Reg#(Bool) full_fifoI2L_child_000 <- mkReg(unpack(0));
    Reg#(Bool) countDone_fifoI2L_child_000 <- mkReg(unpack(0));
    Reg#(Bit#(18)) counter_fifoI2L_child_000 <- mkReg(unpack(0));

    rule count_fifoI2L_child_000;

        let x_0 = (countDone_fifoI2L_child_000);
        when (! (x_0), noAction);
        let x_1 = (counter_fifoI2L_child_000);
        counter_fifoI2L_child_000 <= (x_1) + ((Bit#(18))'(18'h1));
        let x_2 =
        (full_fifoI2L_child_000);
        if (((x_1) == ((Bit#(18))'(18'h3ffff))) && (x_2)) begin
            let x_3 =
            (elt_fifoI2L_child_000);
            $display ("-- IR fifoI2L_child_000: %b %b %x %b %x %x %x %b %x", (x_3).ir_is_rs_rel, (x_3).ir_is_rs_acc, ((x_3).ir_msg).id, ((x_3).ir_msg).type_, ((x_3).ir_msg).addr, (x_3).ir_msg_from, (x_3).ir_mshr_id, ((x_3).ir_by_victim).valid, ((x_3).ir_by_victim).data);
            countDone_fifoI2L_child_000 <= (Bool)'(True);
        end else begin

        end
    endrule

    method Action enq_fifoI2L_child_000 (Struct42 x_0);
        let x_1 = (full_fifoI2L_child_000);
        when (! (x_1), noAction);
        elt_fifoI2L_child_000 <= x_0;
        full_fifoI2L_child_000 <= (Bool)'(True);
    endmethod

    method ActionValue#(Struct42) deq_fifoI2L_child_000 ();
        let x_1 = (full_fifoI2L_child_000);
        when (x_1, noAction);
        let x_2 = (elt_fifoI2L_child_000);
        full_fifoI2L_child_000 <= (Bool)'(False);
        return x_2;
    endmethod
endmodule

interface Module32;
    method Action enq_fifoL2E_000 (Struct47 x_0);
    method ActionValue#(Struct47) deq_fifoL2E_000 ();
endinterface

module mkModule32
    (Module32);
    Reg#(Struct47) elt_fifoL2E_000 <- mkReg(unpack(0));
    Reg#(Bool) full_fifoL2E_000 <- mkReg(unpack(0));
    Reg#(Bool) countDone_fifoL2E_000 <- mkReg(unpack(0));
    Reg#(Bit#(18)) counter_fifoL2E_000 <- mkReg(unpack(0));

    rule count_fifoL2E_000;

        let x_0 = (countDone_fifoL2E_000);
        when (! (x_0), noAction);
        let x_1 = (counter_fifoL2E_000);
        counter_fifoL2E_000 <= (x_1) + ((Bit#(18))'(18'h1));
        let x_2 =
        (full_fifoL2E_000);
        if (((x_1) == ((Bit#(18))'(18'h3ffff))) && (x_2)) begin
            let x_3 =
            (elt_fifoL2E_000);
            $display ("-- LR fifoL2E_000: %b %b %x %b %x %x %x %b %x %x %b %x %b %x %b %x", ((x_3).lr_ir_pp).ir_is_rs_rel, ((x_3).lr_ir_pp).ir_is_rs_acc, (((x_3).lr_ir_pp).ir_msg).id, (((x_3).lr_ir_pp).ir_msg).type_, (((x_3).lr_ir_pp).ir_msg).addr, ((x_3).lr_ir_pp).ir_msg_from, ((x_3).lr_ir_pp).ir_mshr_id, (((x_3).lr_ir_pp).ir_by_victim).valid, (((x_3).lr_ir_pp).ir_by_victim).data, ((x_3).lr_ir).info_index, ((x_3).lr_ir).info_hit, ((x_3).lr_ir).info_way, ((x_3).lr_ir).edir_hit, ((x_3).lr_ir).edir_way, (((x_3).lr_ir).edir_slot).valid, (((x_3).lr_ir).edir_slot).data);
            countDone_fifoL2E_000 <= (Bool)'(True);
        end else begin

        end
    endrule

    method Action enq_fifoL2E_000 (Struct47 x_0);
        let x_1 = (full_fifoL2E_000);
        when (! (x_1), noAction);
        elt_fifoL2E_000 <= x_0;
        full_fifoL2E_000 <= (Bool)'(True);
    endmethod

    method ActionValue#(Struct47) deq_fifoL2E_000 ();
        let x_1 = (full_fifoL2E_000);
        when (x_1, noAction);
        let x_2 = (elt_fifoL2E_000);
        full_fifoL2E_000 <= (Bool)'(False);
        return x_2;
    endmethod
endmodule

interface Module33;
    method Action enq_fifo0000 (Struct1 x_0);
    method ActionValue#(Struct1) deq_fifo0000 ();
endinterface

module mkModule33
    (Module33);
    Reg#(Struct1) elt_fifo0000 <- mkReg(unpack(0));
    Reg#(Bool) full_fifo0000 <- mkReg(unpack(0));
    Reg#(Bool) countDone_fifo0000 <- mkReg(unpack(0));
    Reg#(Bit#(18)) counter_fifo0000 <- mkReg(unpack(0));

    rule count_fifo0000;

        let x_0 = (countDone_fifo0000);
        when (! (x_0), noAction);
        let x_1 = (counter_fifo0000);
        counter_fifo0000 <= (x_1) + ((Bit#(18))'(18'h1));
        let x_2 =
        (full_fifo0000);
        if (((x_1) == ((Bit#(18))'(18'h3ffff))) && (x_2)) begin
            let x_3 =
            (elt_fifo0000);
            $display ("-- MSG fifo0000: %x %b %x", (x_3).id, (x_3).type_, (x_3).addr);
            countDone_fifo0000 <= (Bool)'(True);
        end else begin

        end
    endrule

    method Action enq_fifo0000 (Struct1 x_0);
        let x_1 = (full_fifo0000);
        when (! (x_1), noAction);
        elt_fifo0000 <= x_0;
        full_fifo0000 <= (Bool)'(True);
    endmethod

    method ActionValue#(Struct1) deq_fifo0000 ();
        let x_1 = (full_fifo0000);
        when (x_1, noAction);
        let x_2 = (elt_fifo0000);
        full_fifo0000 <= (Bool)'(False);
        return x_2;
    endmethod
endmodule

interface Module34;
    method Action enq_fifo0001 (Struct1 x_0);
    method ActionValue#(Struct1) deq_fifo0001 ();
endinterface

module mkModule34
    (Module34);
    Reg#(Struct1) elt_fifo0001 <- mkReg(unpack(0));
    Reg#(Bool) full_fifo0001 <- mkReg(unpack(0));
    Reg#(Bool) countDone_fifo0001 <- mkReg(unpack(0));
    Reg#(Bit#(18)) counter_fifo0001 <- mkReg(unpack(0));

    rule count_fifo0001;

        let x_0 = (countDone_fifo0001);
        when (! (x_0), noAction);
        let x_1 = (counter_fifo0001);
        counter_fifo0001 <= (x_1) + ((Bit#(18))'(18'h1));
        let x_2 =
        (full_fifo0001);
        if (((x_1) == ((Bit#(18))'(18'h3ffff))) && (x_2)) begin
            let x_3 =
            (elt_fifo0001);
            $display ("-- MSG fifo0001: %x %b %x", (x_3).id, (x_3).type_, (x_3).addr);
            countDone_fifo0001 <= (Bool)'(True);
        end else begin

        end
    endrule

    method Action enq_fifo0001 (Struct1 x_0);
        let x_1 = (full_fifo0001);
        when (! (x_1), noAction);
        elt_fifo0001 <= x_0;
        full_fifo0001 <= (Bool)'(True);
    endmethod

    method ActionValue#(Struct1) deq_fifo0001 ();
        let x_1 = (full_fifo0001);
        when (x_1, noAction);
        let x_2 = (elt_fifo0001);
        full_fifo0001 <= (Bool)'(False);
        return x_2;
    endmethod
endmodule

interface Module35;
    method Action enq_fifo0002 (Struct1 x_0);
    method ActionValue#(Struct1) deq_fifo0002 ();
endinterface

module mkModule35
    (Module35);
    Reg#(Struct1) elt_fifo0002 <- mkReg(unpack(0));
    Reg#(Bool) full_fifo0002 <- mkReg(unpack(0));
    Reg#(Bool) countDone_fifo0002 <- mkReg(unpack(0));
    Reg#(Bit#(18)) counter_fifo0002 <- mkReg(unpack(0));

    rule count_fifo0002;

        let x_0 = (countDone_fifo0002);
        when (! (x_0), noAction);
        let x_1 = (counter_fifo0002);
        counter_fifo0002 <= (x_1) + ((Bit#(18))'(18'h1));
        let x_2 =
        (full_fifo0002);
        if (((x_1) == ((Bit#(18))'(18'h3ffff))) && (x_2)) begin
            let x_3 =
            (elt_fifo0002);
            $display ("-- MSG fifo0002: %x %b %x", (x_3).id, (x_3).type_, (x_3).addr);
            countDone_fifo0002 <= (Bool)'(True);
        end else begin

        end
    endrule

    method Action enq_fifo0002 (Struct1 x_0);
        let x_1 = (full_fifo0002);
        when (! (x_1), noAction);
        elt_fifo0002 <= x_0;
        full_fifo0002 <= (Bool)'(True);
    endmethod

    method ActionValue#(Struct1) deq_fifo0002 ();
        let x_1 = (full_fifo0002);
        when (x_1, noAction);
        let x_2 = (elt_fifo0002);
        full_fifo0002 <= (Bool)'(False);
        return x_2;
    endmethod
endmodule

interface Module36;
    method Action enq_fifo00000 (Struct1 x_0);
    method ActionValue#(Struct1) deq_fifo00000 ();
endinterface

module mkModule36
    (Module36);
    Reg#(Struct1) elt_fifo00000 <- mkReg(unpack(0));
    Reg#(Bool) full_fifo00000 <- mkReg(unpack(0));
    Reg#(Bool) countDone_fifo00000 <- mkReg(unpack(0));
    Reg#(Bit#(18)) counter_fifo00000 <- mkReg(unpack(0));

    rule count_fifo00000;

        let x_0 = (countDone_fifo00000);
        when (! (x_0), noAction);
        let x_1 = (counter_fifo00000);
        counter_fifo00000 <= (x_1) + ((Bit#(18))'(18'h1));
        let x_2 =
        (full_fifo00000);
        if (((x_1) == ((Bit#(18))'(18'h3ffff))) && (x_2)) begin
            let x_3 =
            (elt_fifo00000);
            $display ("-- MSG fifo00000: %x %b %x", (x_3).id, (x_3).type_, (x_3).addr);
            countDone_fifo00000 <= (Bool)'(True);
        end else begin

        end
    endrule

    method Action enq_fifo00000 (Struct1 x_0);
        let x_1 = (full_fifo00000);
        when (! (x_1), noAction);
        elt_fifo00000 <= x_0;
        full_fifo00000 <= (Bool)'(True);
    endmethod

    method ActionValue#(Struct1) deq_fifo00000 ();
        let x_1 = (full_fifo00000);
        when (x_1, noAction);
        let x_2 = (elt_fifo00000);
        full_fifo00000 <= (Bool)'(False);
        return x_2;
    endmethod
endmodule

interface Module37;
    method Action enq_fifo00002 (Struct1 x_0);
    method ActionValue#(Struct1) deq_fifo00002 ();
endinterface

module mkModule37
    (Module37);
    Reg#(Struct1) elt_fifo00002 <- mkReg(unpack(0));
    Reg#(Bool) full_fifo00002 <- mkReg(unpack(0));
    Reg#(Bool) countDone_fifo00002 <- mkReg(unpack(0));
    Reg#(Bit#(18)) counter_fifo00002 <- mkReg(unpack(0));

    rule count_fifo00002;

        let x_0 = (countDone_fifo00002);
        when (! (x_0), noAction);
        let x_1 = (counter_fifo00002);
        counter_fifo00002 <= (x_1) + ((Bit#(18))'(18'h1));
        let x_2 =
        (full_fifo00002);
        if (((x_1) == ((Bit#(18))'(18'h3ffff))) && (x_2)) begin
            let x_3 =
            (elt_fifo00002);
            $display ("-- MSG fifo00002: %x %b %x", (x_3).id, (x_3).type_, (x_3).addr);
            countDone_fifo00002 <= (Bool)'(True);
        end else begin

        end
    endrule

    method Action enq_fifo00002 (Struct1 x_0);
        let x_1 = (full_fifo00002);
        when (! (x_1), noAction);
        elt_fifo00002 <= x_0;
        full_fifo00002 <= (Bool)'(True);
    endmethod

    method ActionValue#(Struct1) deq_fifo00002 ();
        let x_1 = (full_fifo00002);
        when (x_1, noAction);
        let x_2 = (elt_fifo00002);
        full_fifo00002 <= (Bool)'(False);
        return x_2;
    endmethod
endmodule

interface Module38;
    method ActionValue#(Struct41) victims__000findVictim (Bit#(64) x_0);
    method ActionValue#(Struct48) victims__000__getVictim (Bit#(1) x_0);
    method Action victims__000__setVictim (Struct54 x_0);
    method Action victims__000__registerVictim (Struct48 x_0);
    method ActionValue#(Struct48) victims__000__getFirstVictim ();
    method Action victims__000__setVictimRq (Struct55 x_0);
    method ActionValue#(Bit#(3)) victims__000__releaseVictim (Bit#(64) x_0);
endinterface

module mkModule38
    (Module38);
    Reg#(Vector#(4, Struct48)) victimRegs__000 <- mkReg(unpack(0));

    // No rules in this module

    method ActionValue#(Struct41) victims__000findVictim (Bit#(64) x_0);
        let x_1 = (victimRegs__000);
        Struct48 x_2 =
        ((x_1)[(Bit#(1))'(1'h0)]);
        let x_9 = ?;
        if (((x_2).victim_valid) && (((x_2).victim_addr) == (x_0))) begin
            x_9 = Struct41 {valid : (Bool)'(True), data : (Bit#(1))'(1'h0)};
        end else begin
            Struct48 x_3 =
            ((x_1)[(Bit#(1))'(1'h1)]);
            let x_8 = ?;
            if (((x_3).victim_valid) && (((x_3).victim_addr) == (x_0)))
                begin
                x_8 = Struct41 {valid : (Bool)'(True), data :
                (Bit#(1))'(1'h1)};
            end else begin
                Struct48 x_4 =
                ((x_1)[(Bit#(1))'(1'h0)]);
                let x_7 = ?;
                if (((x_4).victim_valid) && (((x_4).victim_addr) == (x_0)))
                    begin
                    x_7 = Struct41 {valid : (Bool)'(True), data :
                    (Bit#(1))'(1'h0)};
                end else begin
                    Struct48 x_5 =
                    ((x_1)[(Bit#(1))'(1'h1)]);
                    let x_6 = ?;
                    if (((x_5).victim_valid) && (((x_5).victim_addr) ==
                        (x_0))) begin
                        x_6 = Struct41 {valid : (Bool)'(True), data :
                        (Bit#(1))'(1'h1)};
                    end else begin
                        x_6 = Struct41 {valid : (Bool)'(False), data :
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

    method ActionValue#(Struct48) victims__000__getVictim (Bit#(1) x_0);
        let x_1 = (victimRegs__000);
        return (x_1)[x_0];
    endmethod

    method Action victims__000__setVictim (Struct54 x_0);
        let x_1 = (victimRegs__000);
        Struct48 x_2 = ((x_1)[(x_0).victim_idx]);
        Struct48 x_3 = (Struct48 {victim_valid : (Bool)'(True), victim_addr :
        (x_2).victim_addr, victim_info : (x_0).victim_info, victim_value :
        (x_0).victim_value, victim_req : (x_2).victim_req});
        victimRegs__000 <= update (x_1, (x_0).victim_idx, x_3);
    endmethod

    method Action victims__000__registerVictim (Struct48 x_0);
        let x_1 = (victimRegs__000);
        Struct41 x_2 = ((((x_1)[(Bit#(1))'(1'h1)]).victim_valid ?
        ((((x_1)[(Bit#(1))'(1'h0)]).victim_valid ?
        ((((x_1)[(Bit#(1))'(1'h1)]).victim_valid ? (Struct41 {valid :
        (Bool)'(False), data : unpack(0)}) : (Struct41 {valid :
        (Bool)'(True), data : (Bit#(1))'(1'h1)}))) : (Struct41 {valid :
        (Bool)'(True), data : (Bit#(1))'(1'h0)}))) : (Struct41 {valid :
        (Bool)'(True), data : (Bit#(1))'(1'h1)})));
        when ((x_2).valid, noAction);
        Bit#(1) x_3 = ((x_2).data);
        victimRegs__000 <= update (x_1, x_3, x_0);
    endmethod

    method ActionValue#(Struct48) victims__000__getFirstVictim ();
        let x_1 = (victimRegs__000);
        Struct61 x_2 = (((((x_1)[(Bit#(1))'(1'h1)]).victim_valid) && (!
        ((((x_1)[(Bit#(1))'(1'h1)]).victim_req).valid)) ? (Struct61 {valid :
        (Bool)'(True), data : (x_1)[(Bit#(1))'(1'h1)]}) :
        (((((x_1)[(Bit#(1))'(1'h0)]).victim_valid) && (!
        ((((x_1)[(Bit#(1))'(1'h0)]).victim_req).valid)) ? (Struct61 {valid :
        (Bool)'(True), data : (x_1)[(Bit#(1))'(1'h0)]}) :
        (((((x_1)[(Bit#(1))'(1'h1)]).victim_valid) && (!
        ((((x_1)[(Bit#(1))'(1'h1)]).victim_req).valid)) ? (Struct61 {valid :
        (Bool)'(True), data : (x_1)[(Bit#(1))'(1'h1)]}) : (Struct61 {valid :
        (Bool)'(False), data : unpack(0)})))))));
        when ((x_2).valid, noAction);
        return (x_2).data;
    endmethod

    method Action victims__000__setVictimRq (Struct55 x_0);
        Bit#(64) x_1 = ((x_0).victim_addr);
        Bit#(3) x_2 = ((x_0).victim_req);
        let x_3 = (victimRegs__000);
        Struct48 x_4 =
        ((x_3)[(Bit#(1))'(1'h1)]);
        if (((x_4).victim_valid) && (((x_4).victim_addr) == (x_1)))
            begin
            Struct48 x_5 = (Struct48 {victim_valid : (x_4).victim_valid,
            victim_addr : (x_4).victim_addr, victim_info : (x_4).victim_info,
            victim_value : (x_4).victim_value, victim_req : Struct49 {valid :
            (Bool)'(True), data : x_2}});
            victimRegs__000 <= update (x_3, (Bit#(1))'(1'h1), x_5);
        end else begin
            Struct48 x_6 =
            ((x_3)[(Bit#(1))'(1'h0)]);
            if (((x_6).victim_valid) && (((x_6).victim_addr) == (x_1)))
                begin
                Struct48 x_7 = (Struct48 {victim_valid : (x_6).victim_valid,
                victim_addr : (x_6).victim_addr, victim_info :
                (x_6).victim_info, victim_value : (x_6).victim_value,
                victim_req : Struct49 {valid : (Bool)'(True), data :
                x_2}});
                victimRegs__000 <= update (x_3, (Bit#(1))'(1'h0), x_7);
            end else begin
                Struct48 x_8 =
                ((x_3)[(Bit#(1))'(1'h1)]);
                if (((x_8).victim_valid) && (((x_8).victim_addr) == (x_1)))
                    begin
                    Struct48 x_9 = (Struct48 {victim_valid :
                    (x_8).victim_valid, victim_addr : (x_8).victim_addr,
                    victim_info : (x_8).victim_info, victim_value :
                    (x_8).victim_value, victim_req : Struct49 {valid :
                    (Bool)'(True), data : x_2}});
                    victimRegs__000 <= update (x_3, (Bit#(1))'(1'h1), x_9);
                end else begin

                end
            end
        end
    endmethod

    method ActionValue#(Bit#(3)) victims__000__releaseVictim (Bit#(64) x_0);
        let x_1 = (victimRegs__000);
        Struct48 x_2 =
        ((x_1)[(Bit#(1))'(1'h0)]);
        let x_13 = ?;
        if (((x_2).victim_valid) && (((x_2).victim_addr) == (x_0)))
            begin
            victimRegs__000 <= update (x_1, (Bit#(1))'(1'h0),
            unpack(0));
            Bit#(3) x_3 = (((x_2).victim_req).data);
            x_13 = x_3;
        end else begin
            Struct48 x_4 =
            ((x_1)[(Bit#(1))'(1'h1)]);
            let x_12 = ?;
            if (((x_4).victim_valid) && (((x_4).victim_addr) == (x_0)))
                begin
                victimRegs__000 <= update (x_1, (Bit#(1))'(1'h1),
                unpack(0));
                Bit#(3) x_5 = (((x_4).victim_req).data);
                x_12 = x_5;
            end else begin
                Struct48 x_6 =
                ((x_1)[(Bit#(1))'(1'h0)]);
                let x_11 = ?;
                if (((x_6).victim_valid) && (((x_6).victim_addr) == (x_0)))
                    begin
                    victimRegs__000 <= update (x_1, (Bit#(1))'(1'h0),
                    unpack(0));
                    Bit#(3) x_7 = (((x_6).victim_req).data);
                    x_11 = x_7;
                end else begin
                    Struct48 x_8 =
                    ((x_1)[(Bit#(1))'(1'h1)]);
                    let x_10 = ?;
                    if (((x_8).victim_valid) && (((x_8).victim_addr) ==
                        (x_0))) begin
                        victimRegs__000 <= update (x_1, (Bit#(1))'(1'h1),
                        unpack(0));
                        Bit#(3) x_9 = (((x_8).victim_req).data);
                        x_10 = x_9;
                    end else begin
                        x_10 = unpack(0);
                    end
                    x_11 = x_10;
                end
                x_12 = x_11;
            end
            x_13 = x_12;
        end
        return x_13;
    endmethod
endmodule

interface Module39;
    method Action rdReq_infoRam__000__3 (Bit#(8) x_0);
    method Action wrReq_infoRam__000__3 (Struct58 x_0);
    method ActionValue#(Struct56) rdResp_infoRam__000__3 ();
endinterface

module mkModule39 (Module39);
    RWBramCore#(Bit#(8), Struct56) bram <- mkRWBramCore();
    Reg#(Bool) initDone <- mkReg(False);
    Reg#(Bit#(8)) initIdx <- mkReg(0);

    rule init (!initDone);
        let initData = Struct56 {tag: 51'h3, value: Struct11 {mesi_owned: False, mesi_status: 3'h1, mesi_dir_st: 3'h1, mesi_dir_sharers: 2'h0}};
        bram.wrReq(initIdx, initData);
        initIdx <= initIdx + 1;
        initDone <= (initIdx == maxBound);
    endrule

    method Action rdReq_infoRam__000__3 (Bit#(8) x_0) if(initDone);
        bram.rdReq(x_0);
    endmethod

    method Action wrReq_infoRam__000__3 (Struct58 x_0) if(initDone);
        bram.wrReq(x_0.addr, x_0.datain);
    endmethod

    method ActionValue#(Struct56) rdResp_infoRam__000__3 () if(initDone);
        bram.deqRdResp ();
        let data = bram.rdResp ();
        return data;
    endmethod


endmodule

interface Module40;
    method Action rdReq_infoRam__000__2 (Bit#(8) x_0);
    method Action wrReq_infoRam__000__2 (Struct58 x_0);
    method ActionValue#(Struct56) rdResp_infoRam__000__2 ();
endinterface

module mkModule40 (Module40);
    RWBramCore#(Bit#(8), Struct56) bram <- mkRWBramCore();
    Reg#(Bool) initDone <- mkReg(False);
    Reg#(Bit#(8)) initIdx <- mkReg(0);

    rule init (!initDone);
        let initData = Struct56 {tag: 51'h2, value: Struct11 {mesi_owned: False, mesi_status: 3'h1, mesi_dir_st: 3'h1, mesi_dir_sharers: 2'h0}};
        bram.wrReq(initIdx, initData);
        initIdx <= initIdx + 1;
        initDone <= (initIdx == maxBound);
    endrule

    method Action rdReq_infoRam__000__2 (Bit#(8) x_0) if(initDone);
        bram.rdReq(x_0);
    endmethod

    method Action wrReq_infoRam__000__2 (Struct58 x_0) if(initDone);
        bram.wrReq(x_0.addr, x_0.datain);
    endmethod

    method ActionValue#(Struct56) rdResp_infoRam__000__2 () if(initDone);
        bram.deqRdResp ();
        let data = bram.rdResp ();
        return data;
    endmethod


endmodule

interface Module41;
    method Action rdReq_infoRam__000__1 (Bit#(8) x_0);
    method Action wrReq_infoRam__000__1 (Struct58 x_0);
    method ActionValue#(Struct56) rdResp_infoRam__000__1 ();
endinterface

module mkModule41 (Module41);
    RWBramCore#(Bit#(8), Struct56) bram <- mkRWBramCore();
    Reg#(Bool) initDone <- mkReg(False);
    Reg#(Bit#(8)) initIdx <- mkReg(0);

    rule init (!initDone);
        let initData = Struct56 {tag: 51'h1, value: Struct11 {mesi_owned: False, mesi_status: 3'h1, mesi_dir_st: 3'h1, mesi_dir_sharers: 2'h0}};
        bram.wrReq(initIdx, initData);
        initIdx <= initIdx + 1;
        initDone <= (initIdx == maxBound);
    endrule

    method Action rdReq_infoRam__000__1 (Bit#(8) x_0) if(initDone);
        bram.rdReq(x_0);
    endmethod

    method Action wrReq_infoRam__000__1 (Struct58 x_0) if(initDone);
        bram.wrReq(x_0.addr, x_0.datain);
    endmethod

    method ActionValue#(Struct56) rdResp_infoRam__000__1 () if(initDone);
        bram.deqRdResp ();
        let data = bram.rdResp ();
        return data;
    endmethod


endmodule

interface Module42;
    method Action rdReq_infoRam__000__0 (Bit#(8) x_0);
    method Action wrReq_infoRam__000__0 (Struct58 x_0);
    method ActionValue#(Struct56) rdResp_infoRam__000__0 ();
endinterface

module mkModule42 (Module42);
    RWBramCore#(Bit#(8), Struct56) bram <- mkRWBramCore();
    Reg#(Bool) initDone <- mkReg(False);
    Reg#(Bit#(8)) initIdx <- mkReg(0);

    rule init (!initDone);
        let initData = Struct56 {tag: 51'h0, value: Struct11 {mesi_owned: False, mesi_status: 3'h1, mesi_dir_st: 3'h1, mesi_dir_sharers: 2'h0}};
        bram.wrReq(initIdx, initData);
        initIdx <= initIdx + 1;
        initDone <= (initIdx == maxBound);
    endrule

    method Action rdReq_infoRam__000__0 (Bit#(8) x_0) if(initDone);
        bram.rdReq(x_0);
    endmethod

    method Action wrReq_infoRam__000__0 (Struct58 x_0) if(initDone);
        bram.wrReq(x_0.addr, x_0.datain);
    endmethod

    method ActionValue#(Struct56) rdResp_infoRam__000__0 () if(initDone);
        bram.deqRdResp ();
        let data = bram.rdResp ();
        return data;
    endmethod


endmodule

interface Module43;
    method Action rdReq_dataRam__000 (Bit#(10) x_0);
    method Action wrReq_dataRam__000 (Struct60 x_0);
    method ActionValue#(Vector#(4, Bit#(64))) rdResp_dataRam__000 ();
endinterface

module mkModule43 (Module43);
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

    method Action wrReq_dataRam__000 (Struct60 x_0) if(initDone);
        bram.wrReq(x_0.addr, x_0.datain);
    endmethod

    method ActionValue#(Vector#(4, Bit#(64))) rdResp_dataRam__000 ()
    if(initDone);
        bram.deqRdResp ();
        let data = bram.rdResp ();
        return data;
    endmethod


endmodule

interface Module44;
    method Action rdReq_repRam__000 (Bit#(8) x_0);
    method Action wrReq_repRam__000 (Struct62 x_0);
    method ActionValue#(Vector#(4, Bit#(8))) rdResp_repRam__000 ();
endinterface

module mkModule44 (Module44);
    RWBramCore#(Bit#(8), Vector#(4, Bit#(8))) bram <- mkRWBramCore();
    Reg#(Bool) initDone <- mkReg(False);
    Reg#(Bit#(8)) initIdx <- mkReg(0);

    rule init (!initDone);
        let initData = vec(8'h0, 8'h0, 8'h0, 8'h0);
        bram.wrReq(initIdx, initData);
        initIdx <= initIdx + 1;
        initDone <= (initIdx == maxBound);
    endrule

    method Action rdReq_repRam__000 (Bit#(8) x_0) if(initDone);
        bram.rdReq(x_0);
    endmethod

    method Action wrReq_repRam__000 (Struct62 x_0) if(initDone);
        bram.wrReq(x_0.addr, x_0.datain);
    endmethod

    method ActionValue#(Vector#(4, Bit#(8))) rdResp_repRam__000 ()
    if(initDone);
        bram.deqRdResp ();
        let data = bram.rdResp ();
        return data;
    endmethod


endmodule

interface Module45;
    method ActionValue#(Struct51) getMSHR_000 (Bit#(3) x_0);
    method ActionValue#(Struct40) getPRqSlot_000 (Struct39 x_0);
    method ActionValue#(Struct40) getCRqSlot_000 (Struct39 x_0);
    method ActionValue#(Struct50) getWait_000 ();
    method Action registerUL_000 (Struct53 x_0);
    method Action registerDL_000 (Struct63 x_0);
    method ActionValue#(Bit#(3)) getULImm_000 (Struct1 x_0);
    method Action transferUpDown_000 (Struct64 x_0);
    method ActionValue#(Bit#(3)) findUL_000 (Bit#(64) x_0);
    method ActionValue#(Bit#(3)) findDL_000 (Bit#(64) x_0);
    method Action releaseMSHR_000 (Bit#(3) x_0);
    method Action addRs_000 (Struct44 x_0);
    method ActionValue#(Struct43) getRsReady_000 ();
endinterface

module mkModule45
    (Module45);
    Reg#(Vector#(6, Struct51)) rqs_000 <- mkReg(unpack(0));

    // No rules in this module

    method ActionValue#(Struct51) getMSHR_000 (Bit#(3) x_0);
        let x_1 = (rqs_000);
        return (x_1)[x_0];
    endmethod

    method ActionValue#(Struct40) getPRqSlot_000 (Struct39 x_0);
        let x_1 = (rqs_000);
        Struct49 x_2 = (((((x_1)[(Bit#(3))'(3'h0)]).m_status) ==
        ((Bit#(3))'(3'h0)) ? (Struct49 {valid : (Bool)'(True), data :
        (Bit#(3))'(3'h0)}) : (((((x_1)[(Bit#(3))'(3'h1)]).m_status) ==
        ((Bit#(3))'(3'h0)) ? (Struct49 {valid : (Bool)'(True), data :
        (Bit#(3))'(3'h1)}) : (Struct49 {valid : (Bool)'(False), data :
        unpack(0)})))));
        Bool x_3 = ((x_2).valid);
        Bit#(3) x_4 = ((x_2).data);
        Bit#(64) x_5 = (((x_0).r_msg).addr);
        Struct49 x_6 = ((((! ((((x_1)[(Bit#(3))'(3'h0)]).m_status) ==
        ((Bit#(3))'(3'h0)))) && (!
        ((((x_1)[(Bit#(3))'(3'h0)]).m_next).valid))) &&
        (((((x_1)[(Bit#(3))'(3'h0)]).m_msg).addr) == (x_5)) ? (Struct49
        {valid : (Bool)'(True), data : (Bit#(3))'(3'h0)}) : ((((!
        ((((x_1)[(Bit#(3))'(3'h1)]).m_status) == ((Bit#(3))'(3'h0)))) && (!
        ((((x_1)[(Bit#(3))'(3'h1)]).m_next).valid))) &&
        (((((x_1)[(Bit#(3))'(3'h1)]).m_msg).addr) == (x_5)) ? (Struct49
        {valid : (Bool)'(True), data : (Bit#(3))'(3'h1)}) : ((((!
        ((((x_1)[(Bit#(3))'(3'h2)]).m_status) == ((Bit#(3))'(3'h0)))) && (!
        ((((x_1)[(Bit#(3))'(3'h2)]).m_next).valid))) &&
        (((((x_1)[(Bit#(3))'(3'h2)]).m_msg).addr) == (x_5)) ? (Struct49
        {valid : (Bool)'(True), data : (Bit#(3))'(3'h2)}) : ((((!
        ((((x_1)[(Bit#(3))'(3'h3)]).m_status) == ((Bit#(3))'(3'h0)))) && (!
        ((((x_1)[(Bit#(3))'(3'h3)]).m_next).valid))) &&
        (((((x_1)[(Bit#(3))'(3'h3)]).m_msg).addr) == (x_5)) ? (Struct49
        {valid : (Bool)'(True), data : (Bit#(3))'(3'h3)}) : ((((!
        ((((x_1)[(Bit#(3))'(3'h4)]).m_status) == ((Bit#(3))'(3'h0)))) && (!
        ((((x_1)[(Bit#(3))'(3'h4)]).m_next).valid))) &&
        (((((x_1)[(Bit#(3))'(3'h4)]).m_msg).addr) == (x_5)) ? (Struct49
        {valid : (Bool)'(True), data : (Bit#(3))'(3'h4)}) : ((((!
        ((((x_1)[(Bit#(3))'(3'h5)]).m_status) == ((Bit#(3))'(3'h0)))) && (!
        ((((x_1)[(Bit#(3))'(3'h5)]).m_next).valid))) &&
        (((((x_1)[(Bit#(3))'(3'h5)]).m_msg).addr) == (x_5)) ? (Struct49
        {valid : (Bool)'(True), data : (Bit#(3))'(3'h5)}) : (Struct49 {valid
        : (Bool)'(False), data : unpack(0)})))))))))))));
        Bool x_7 = ((x_6).valid);
        Bit#(3) x_8 = ((x_6).data);
        Struct40 x_9 = (Struct40 {s_has_slot : x_3, s_conflict : x_7, s_id :
        x_4});
        if (x_3) begin
            Vector#(6, Struct51) x_10 = (update (x_1, x_4, Struct51 {m_status
            : (x_7 ? ((Bit#(3))'(3'h1)) : ((Bit#(3))'(3'h3))), m_next :
            Struct49 {valid : (Bool)'(False), data : unpack(0)}, m_is_ul :
            unpack(0), m_msg : (x_0).r_msg, m_qidx : (x_0).r_msg_from, m_rsb
            : unpack(0), m_dl_rss_from : unpack(0), m_dl_rss_recv :
            unpack(0), m_dl_rss :
            unpack(0)}));
            let x_13 = ?;
            if (x_7) begin
                Struct51 x_11 = ((x_1)[x_8]);
                Vector#(6, Struct51) x_12 = (update (x_10, x_8, Struct51
                {m_status : (x_11).m_status, m_next : (x_7 ? (Struct49 {valid
                : (Bool)'(True), data : x_4}) : ((x_11).m_next)), m_is_ul :
                (x_11).m_is_ul, m_msg : (x_11).m_msg, m_qidx : (x_11).m_qidx,
                m_rsb : (x_11).m_rsb, m_dl_rss_from : (x_11).m_dl_rss_from,
                m_dl_rss_recv : (x_11).m_dl_rss_recv, m_dl_rss :
                (x_11).m_dl_rss}));
                x_13 = x_12;
            end else begin
                x_13 = x_10;
            end
            rqs_000 <= x_13;
        end else begin

        end
        return x_9;
    endmethod

    method ActionValue#(Struct40) getCRqSlot_000 (Struct39 x_0);
        let x_1 = (rqs_000);
        Struct49 x_2 = (((((x_1)[(Bit#(3))'(3'h2)]).m_status) ==
        ((Bit#(3))'(3'h0)) ? (Struct49 {valid : (Bool)'(True), data :
        (Bit#(3))'(3'h2)}) : (((((x_1)[(Bit#(3))'(3'h3)]).m_status) ==
        ((Bit#(3))'(3'h0)) ? (Struct49 {valid : (Bool)'(True), data :
        (Bit#(3))'(3'h3)}) : (((((x_1)[(Bit#(3))'(3'h4)]).m_status) ==
        ((Bit#(3))'(3'h0)) ? (Struct49 {valid : (Bool)'(True), data :
        (Bit#(3))'(3'h4)}) : (((((x_1)[(Bit#(3))'(3'h5)]).m_status) ==
        ((Bit#(3))'(3'h0)) ? (Struct49 {valid : (Bool)'(True), data :
        (Bit#(3))'(3'h5)}) : (Struct49 {valid : (Bool)'(False), data :
        unpack(0)})))))))));
        Bool x_3 = ((x_2).valid);
        Bit#(3) x_4 = ((x_2).data);
        Bit#(64) x_5 = (((x_0).r_msg).addr);
        Struct49 x_6 = ((((! ((((x_1)[(Bit#(3))'(3'h0)]).m_status) ==
        ((Bit#(3))'(3'h0)))) && (!
        ((((x_1)[(Bit#(3))'(3'h0)]).m_next).valid))) &&
        (((((x_1)[(Bit#(3))'(3'h0)]).m_msg).addr) == (x_5)) ? (Struct49
        {valid : (Bool)'(True), data : (Bit#(3))'(3'h0)}) : ((((!
        ((((x_1)[(Bit#(3))'(3'h1)]).m_status) == ((Bit#(3))'(3'h0)))) && (!
        ((((x_1)[(Bit#(3))'(3'h1)]).m_next).valid))) &&
        (((((x_1)[(Bit#(3))'(3'h1)]).m_msg).addr) == (x_5)) ? (Struct49
        {valid : (Bool)'(True), data : (Bit#(3))'(3'h1)}) : ((((!
        ((((x_1)[(Bit#(3))'(3'h2)]).m_status) == ((Bit#(3))'(3'h0)))) && (!
        ((((x_1)[(Bit#(3))'(3'h2)]).m_next).valid))) &&
        (((((x_1)[(Bit#(3))'(3'h2)]).m_msg).addr) == (x_5)) ? (Struct49
        {valid : (Bool)'(True), data : (Bit#(3))'(3'h2)}) : ((((!
        ((((x_1)[(Bit#(3))'(3'h3)]).m_status) == ((Bit#(3))'(3'h0)))) && (!
        ((((x_1)[(Bit#(3))'(3'h3)]).m_next).valid))) &&
        (((((x_1)[(Bit#(3))'(3'h3)]).m_msg).addr) == (x_5)) ? (Struct49
        {valid : (Bool)'(True), data : (Bit#(3))'(3'h3)}) : ((((!
        ((((x_1)[(Bit#(3))'(3'h4)]).m_status) == ((Bit#(3))'(3'h0)))) && (!
        ((((x_1)[(Bit#(3))'(3'h4)]).m_next).valid))) &&
        (((((x_1)[(Bit#(3))'(3'h4)]).m_msg).addr) == (x_5)) ? (Struct49
        {valid : (Bool)'(True), data : (Bit#(3))'(3'h4)}) : ((((!
        ((((x_1)[(Bit#(3))'(3'h5)]).m_status) == ((Bit#(3))'(3'h0)))) && (!
        ((((x_1)[(Bit#(3))'(3'h5)]).m_next).valid))) &&
        (((((x_1)[(Bit#(3))'(3'h5)]).m_msg).addr) == (x_5)) ? (Struct49
        {valid : (Bool)'(True), data : (Bit#(3))'(3'h5)}) : (Struct49 {valid
        : (Bool)'(False), data : unpack(0)})))))))))))));
        Bool x_7 = ((x_6).valid);
        Bit#(3) x_8 = ((x_6).data);
        Struct40 x_9 = (Struct40 {s_has_slot : x_3, s_conflict : x_7, s_id :
        x_4});
        if (x_3) begin
            Vector#(6, Struct51) x_10 = (update (x_1, x_4, Struct51 {m_status
            : (x_7 ? ((Bit#(3))'(3'h1)) : ((Bit#(3))'(3'h3))), m_next :
            Struct49 {valid : (Bool)'(False), data : unpack(0)}, m_is_ul :
            unpack(0), m_msg : (x_0).r_msg, m_qidx : (x_0).r_msg_from, m_rsb
            : unpack(0), m_dl_rss_from : unpack(0), m_dl_rss_recv :
            unpack(0), m_dl_rss :
            unpack(0)}));
            let x_13 = ?;
            if (x_7) begin
                Struct51 x_11 = ((x_1)[x_8]);
                Vector#(6, Struct51) x_12 = (update (x_10, x_8, Struct51
                {m_status : (x_11).m_status, m_next : (x_7 ? (Struct49 {valid
                : (Bool)'(True), data : x_4}) : ((x_11).m_next)), m_is_ul :
                (x_11).m_is_ul, m_msg : (x_11).m_msg, m_qidx : (x_11).m_qidx,
                m_rsb : (x_11).m_rsb, m_dl_rss_from : (x_11).m_dl_rss_from,
                m_dl_rss_recv : (x_11).m_dl_rss_recv, m_dl_rss :
                (x_11).m_dl_rss}));
                x_13 = x_12;
            end else begin
                x_13 = x_10;
            end
            rqs_000 <= x_13;
        end else begin

        end
        return x_9;
    endmethod

    method ActionValue#(Struct50) getWait_000 ();
        let x_1 = (rqs_000);
        Struct49 x_2 = (((((x_1)[(Bit#(3))'(3'h0)]).m_status) ==
        ((Bit#(3))'(3'h2)) ? (Struct49 {valid : (Bool)'(True), data :
        (Bit#(3))'(3'h0)}) : (((((x_1)[(Bit#(3))'(3'h1)]).m_status) ==
        ((Bit#(3))'(3'h2)) ? (Struct49 {valid : (Bool)'(True), data :
        (Bit#(3))'(3'h1)}) : (((((x_1)[(Bit#(3))'(3'h2)]).m_status) ==
        ((Bit#(3))'(3'h2)) ? (Struct49 {valid : (Bool)'(True), data :
        (Bit#(3))'(3'h2)}) : (((((x_1)[(Bit#(3))'(3'h3)]).m_status) ==
        ((Bit#(3))'(3'h2)) ? (Struct49 {valid : (Bool)'(True), data :
        (Bit#(3))'(3'h3)}) : (((((x_1)[(Bit#(3))'(3'h4)]).m_status) ==
        ((Bit#(3))'(3'h2)) ? (Struct49 {valid : (Bool)'(True), data :
        (Bit#(3))'(3'h4)}) : (((((x_1)[(Bit#(3))'(3'h5)]).m_status) ==
        ((Bit#(3))'(3'h2)) ? (Struct49 {valid : (Bool)'(True), data :
        (Bit#(3))'(3'h5)}) : (Struct49 {valid : (Bool)'(False), data :
        unpack(0)})))))))))))));
        let x_6 = ?;
        if ((x_2).valid) begin
            Bit#(3) x_3 = ((x_2).data);
            Struct51 x_4 = ((x_1)[x_3]);
            rqs_000 <= update (x_1, x_3, Struct51 {m_status :
            (Bit#(3))'(3'h4), m_next : (x_4).m_next, m_is_ul : (x_4).m_is_ul,
            m_msg : (x_4).m_msg, m_qidx : (x_4).m_qidx, m_rsb : (x_4).m_rsb,
            m_dl_rss_from : (x_4).m_dl_rss_from, m_dl_rss_recv :
            (x_4).m_dl_rss_recv, m_dl_rss : (x_4).m_dl_rss});
            Struct39 x_5 = (Struct39 {r_id : x_3, r_msg : (x_4).m_msg,
            r_msg_from : (x_4).m_qidx});
            x_6 = Struct50 {valid : (Bool)'(True), data : x_5};
        end else begin
            x_6 = Struct50 {valid : (Bool)'(False), data : unpack(0)};
        end
        return x_6;
    endmethod

    method Action registerUL_000 (Struct53 x_0);
        let x_1 = (rqs_000);
        Bit#(3) x_2 = ((x_0).r_id);
        Struct51 x_3 = ((x_1)[x_2]);
        Struct51 x_4 = (Struct51 {m_status : (Bit#(3))'(3'h4), m_next :
        (x_3).m_next, m_is_ul : (Bool)'(True), m_msg : (x_3).m_msg, m_qidx :
        zeroExtend((x_0).r_ul_rsbTo), m_rsb : (x_0).r_ul_rsb, m_dl_rss_from :
        unpack(0), m_dl_rss_recv : unpack(0), m_dl_rss : unpack(0)});
        rqs_000 <= update (x_1, x_2, x_4);
    endmethod

    method Action registerDL_000 (Struct63 x_0);
        let x_1 = (rqs_000);
        Bit#(3) x_2 = ((x_0).r_id);
        Struct51 x_3 = ((x_1)[x_2]);
        Struct51 x_4 = (Struct51 {m_status : (Bit#(3))'(3'h4), m_next :
        (x_3).m_next, m_is_ul : (Bool)'(False), m_msg : (x_3).m_msg, m_qidx :
        (x_0).r_dl_rsbTo, m_rsb : (x_0).r_dl_rsb, m_dl_rss_from :
        (x_0).r_dl_rss_from, m_dl_rss_recv : unpack(0), m_dl_rss :
        unpack(0)});
        rqs_000 <= update (x_1, x_2, x_4);
    endmethod

    method ActionValue#(Bit#(3)) getULImm_000 (Struct1 x_0);
        let x_1 = (rqs_000);
        Struct49 x_2 = (((((x_1)[(Bit#(3))'(3'h2)]).m_status) ==
        ((Bit#(3))'(3'h0)) ? (Struct49 {valid : (Bool)'(True), data :
        (Bit#(3))'(3'h4)}) : (((((x_1)[(Bit#(3))'(3'h3)]).m_status) ==
        ((Bit#(3))'(3'h0)) ? (Struct49 {valid : (Bool)'(True), data :
        (Bit#(3))'(3'h5)}) : (((((x_1)[(Bit#(3))'(3'h4)]).m_status) ==
        ((Bit#(3))'(3'h0)) ? (Struct49 {valid : (Bool)'(True), data :
        (Bit#(3))'(3'h6)}) : (((((x_1)[(Bit#(3))'(3'h5)]).m_status) ==
        ((Bit#(3))'(3'h0)) ? (Struct49 {valid : (Bool)'(True), data :
        (Bit#(3))'(3'h7)}) : (Struct49 {valid : (Bool)'(False), data :
        unpack(0)})))))))));
        when ((x_2).valid, noAction);
        Bit#(3) x_3 = ((x_2).data);
        rqs_000 <= update (x_1, x_3, Struct51 {m_status : (Bit#(3))'(3'h4),
        m_next : Struct49 {valid : (Bool)'(False), data : unpack(0)}, m_is_ul
        : (Bool)'(True), m_msg : x_0, m_qidx : unpack(0), m_rsb :
        (Bool)'(False), m_dl_rss_from : unpack(0), m_dl_rss_recv : unpack(0),
        m_dl_rss : unpack(0)});
        return x_3;
    endmethod

    method Action transferUpDown_000 (Struct64 x_0);
        let x_1 = (rqs_000);
        Bit#(3) x_2 = ((x_0).r_id);
        Struct51 x_3 = ((x_1)[x_2]);
        Struct51 x_4 = (Struct51 {m_status : (Bit#(3))'(3'h4), m_next :
        (x_3).m_next, m_is_ul : (Bool)'(False), m_msg : (x_3).m_msg, m_qidx :
        (x_3).m_qidx, m_rsb : (x_3).m_rsb, m_dl_rss_from :
        (x_0).r_dl_rss_from, m_dl_rss_recv : unpack(0), m_dl_rss :
        unpack(0)});
        rqs_000 <= update (x_1, x_2, x_4);
    endmethod

    method ActionValue#(Bit#(3)) findUL_000 (Bit#(64) x_0);
        let x_1 = (rqs_000);
        Bit#(3) x_2 = (((((((x_1)[(Bit#(3))'(3'h2)]).m_status) ==
        ((Bit#(3))'(3'h4))) && (((x_1)[(Bit#(3))'(3'h2)]).m_is_ul)) &&
        (((((x_1)[(Bit#(3))'(3'h2)]).m_msg).addr) == (x_0)) ?
        ((Bit#(3))'(3'h2)) : (((((((x_1)[(Bit#(3))'(3'h3)]).m_status) ==
        ((Bit#(3))'(3'h4))) && (((x_1)[(Bit#(3))'(3'h3)]).m_is_ul)) &&
        (((((x_1)[(Bit#(3))'(3'h3)]).m_msg).addr) == (x_0)) ?
        ((Bit#(3))'(3'h3)) : (((((((x_1)[(Bit#(3))'(3'h4)]).m_status) ==
        ((Bit#(3))'(3'h4))) && (((x_1)[(Bit#(3))'(3'h4)]).m_is_ul)) &&
        (((((x_1)[(Bit#(3))'(3'h4)]).m_msg).addr) == (x_0)) ?
        ((Bit#(3))'(3'h4)) : (((((((x_1)[(Bit#(3))'(3'h5)]).m_status) ==
        ((Bit#(3))'(3'h4))) && (((x_1)[(Bit#(3))'(3'h5)]).m_is_ul)) &&
        (((((x_1)[(Bit#(3))'(3'h5)]).m_msg).addr) == (x_0)) ?
        ((Bit#(3))'(3'h5)) : (unpack(0))))))))));
        return x_2;
    endmethod

    method ActionValue#(Bit#(3)) findDL_000 (Bit#(64) x_0);
        let x_1 = (rqs_000);
        Bit#(3) x_2 = (((((((x_1)[(Bit#(3))'(3'h0)]).m_status) ==
        ((Bit#(3))'(3'h4))) && (! (((x_1)[(Bit#(3))'(3'h0)]).m_is_ul))) &&
        (((((x_1)[(Bit#(3))'(3'h0)]).m_msg).addr) == (x_0)) ?
        ((Bit#(3))'(3'h0)) : (((((((x_1)[(Bit#(3))'(3'h1)]).m_status) ==
        ((Bit#(3))'(3'h4))) && (! (((x_1)[(Bit#(3))'(3'h1)]).m_is_ul))) &&
        (((((x_1)[(Bit#(3))'(3'h1)]).m_msg).addr) == (x_0)) ?
        ((Bit#(3))'(3'h1)) : (((((((x_1)[(Bit#(3))'(3'h2)]).m_status) ==
        ((Bit#(3))'(3'h4))) && (! (((x_1)[(Bit#(3))'(3'h2)]).m_is_ul))) &&
        (((((x_1)[(Bit#(3))'(3'h2)]).m_msg).addr) == (x_0)) ?
        ((Bit#(3))'(3'h2)) : (((((((x_1)[(Bit#(3))'(3'h3)]).m_status) ==
        ((Bit#(3))'(3'h4))) && (! (((x_1)[(Bit#(3))'(3'h3)]).m_is_ul))) &&
        (((((x_1)[(Bit#(3))'(3'h3)]).m_msg).addr) == (x_0)) ?
        ((Bit#(3))'(3'h3)) : (((((((x_1)[(Bit#(3))'(3'h4)]).m_status) ==
        ((Bit#(3))'(3'h4))) && (! (((x_1)[(Bit#(3))'(3'h4)]).m_is_ul))) &&
        (((((x_1)[(Bit#(3))'(3'h4)]).m_msg).addr) == (x_0)) ?
        ((Bit#(3))'(3'h4)) : (((((((x_1)[(Bit#(3))'(3'h5)]).m_status) ==
        ((Bit#(3))'(3'h4))) && (! (((x_1)[(Bit#(3))'(3'h5)]).m_is_ul))) &&
        (((((x_1)[(Bit#(3))'(3'h5)]).m_msg).addr) == (x_0)) ?
        ((Bit#(3))'(3'h5)) : (unpack(0))))))))))))));
        return x_2;
    endmethod

    method Action releaseMSHR_000 (Bit#(3) x_0);
        let x_1 = (rqs_000);
        Struct51 x_2 = ((x_1)[x_0]);
        Vector#(6, Struct51) x_3 = (update (x_1, x_0,
        unpack(0)));
        let x_7 = ?;
        if (((x_2).m_next).valid) begin
            Bit#(3) x_4 = (((x_2).m_next).data);
            Struct51 x_5 = ((x_1)[x_4]);
            Vector#(6, Struct51) x_6 = (update (x_3, x_4, Struct51 {m_status
            : (Bit#(3))'(3'h2), m_next : (x_5).m_next, m_is_ul :
            (x_5).m_is_ul, m_msg : (x_5).m_msg, m_qidx : (x_5).m_qidx, m_rsb
            : (x_5).m_rsb, m_dl_rss_from : (x_5).m_dl_rss_from, m_dl_rss_recv
            : (x_5).m_dl_rss_recv, m_dl_rss : (x_5).m_dl_rss}));
            x_7 = x_6;
        end else begin
            x_7 = x_3;
        end
        rqs_000 <= x_7;
    endmethod

    method Action addRs_000 (Struct44 x_0);
        let x_1 = (rqs_000);
        Bit#(3) x_2 = ((x_0).r_id);
        Struct51 x_3 = ((x_1)[x_2]);
        Struct51 x_4 = (Struct51 {m_status : (x_3).m_status, m_next :
        (x_3).m_next, m_is_ul : (x_3).m_is_ul, m_msg : (x_3).m_msg, m_qidx :
        (x_3).m_qidx, m_rsb : (x_3).m_rsb, m_dl_rss_from :
        (x_3).m_dl_rss_from, m_dl_rss_recv : ((x_3).m_dl_rss_recv) |
        (((Bit#(2))'(2'h1)) << ((x_0).r_midx)), m_dl_rss : update
        ((x_3).m_dl_rss, (x_0).r_midx, (x_0).r_msg)});
        rqs_000 <= update (x_1, x_2, x_4);
    endmethod

    method ActionValue#(Struct43) getRsReady_000 ();
        let x_1 = (rqs_000);
        Struct49 x_2 = (((((((x_1)[(Bit#(3))'(3'h0)]).m_status) ==
        ((Bit#(3))'(3'h4))) && (! (((x_1)[(Bit#(3))'(3'h0)]).m_is_ul))) &&
        ((((x_1)[(Bit#(3))'(3'h0)]).m_dl_rss_from) ==
        (((x_1)[(Bit#(3))'(3'h0)]).m_dl_rss_recv)) ? (Struct49 {valid :
        (Bool)'(True), data : (Bit#(3))'(3'h0)}) :
        (((((((x_1)[(Bit#(3))'(3'h1)]).m_status) == ((Bit#(3))'(3'h4))) && (!
        (((x_1)[(Bit#(3))'(3'h1)]).m_is_ul))) &&
        ((((x_1)[(Bit#(3))'(3'h1)]).m_dl_rss_from) ==
        (((x_1)[(Bit#(3))'(3'h1)]).m_dl_rss_recv)) ? (Struct49 {valid :
        (Bool)'(True), data : (Bit#(3))'(3'h1)}) :
        (((((((x_1)[(Bit#(3))'(3'h2)]).m_status) == ((Bit#(3))'(3'h4))) && (!
        (((x_1)[(Bit#(3))'(3'h2)]).m_is_ul))) &&
        ((((x_1)[(Bit#(3))'(3'h2)]).m_dl_rss_from) ==
        (((x_1)[(Bit#(3))'(3'h2)]).m_dl_rss_recv)) ? (Struct49 {valid :
        (Bool)'(True), data : (Bit#(3))'(3'h2)}) :
        (((((((x_1)[(Bit#(3))'(3'h3)]).m_status) == ((Bit#(3))'(3'h4))) && (!
        (((x_1)[(Bit#(3))'(3'h3)]).m_is_ul))) &&
        ((((x_1)[(Bit#(3))'(3'h3)]).m_dl_rss_from) ==
        (((x_1)[(Bit#(3))'(3'h3)]).m_dl_rss_recv)) ? (Struct49 {valid :
        (Bool)'(True), data : (Bit#(3))'(3'h3)}) :
        (((((((x_1)[(Bit#(3))'(3'h4)]).m_status) == ((Bit#(3))'(3'h4))) && (!
        (((x_1)[(Bit#(3))'(3'h4)]).m_is_ul))) &&
        ((((x_1)[(Bit#(3))'(3'h4)]).m_dl_rss_from) ==
        (((x_1)[(Bit#(3))'(3'h4)]).m_dl_rss_recv)) ? (Struct49 {valid :
        (Bool)'(True), data : (Bit#(3))'(3'h4)}) :
        (((((((x_1)[(Bit#(3))'(3'h5)]).m_status) == ((Bit#(3))'(3'h4))) && (!
        (((x_1)[(Bit#(3))'(3'h5)]).m_is_ul))) &&
        ((((x_1)[(Bit#(3))'(3'h5)]).m_dl_rss_from) ==
        (((x_1)[(Bit#(3))'(3'h5)]).m_dl_rss_recv)) ? (Struct49 {valid :
        (Bool)'(True), data : (Bit#(3))'(3'h5)}) : (Struct49 {valid :
        (Bool)'(False), data : unpack(0)})))))))))))));
        when ((x_2).valid, noAction);
        Bit#(3) x_3 = ((x_2).data);
        Struct51 x_4 = ((x_1)[x_3]);
        Struct51 x_5 = (Struct51 {m_status : (Bit#(3))'(3'h5), m_next :
        (x_4).m_next, m_is_ul : (x_4).m_is_ul, m_msg : (x_4).m_msg, m_qidx :
        (x_4).m_qidx, m_rsb : (x_4).m_rsb, m_dl_rss_from :
        (x_4).m_dl_rss_from, m_dl_rss_recv : (x_4).m_dl_rss_recv, m_dl_rss :
        (x_4).m_dl_rss});
        rqs_000 <= update (x_1, x_3, x_5);
        Struct43 x_6 = (Struct43 {r_id : x_3, r_addr :
        ((x_4).m_msg).addr});
        return x_6;
    endmethod
endmodule

interface Module46;
    method Action enq_fifoPInput001 (Struct2 x_0);
    method ActionValue#(Struct2) deq_fifoPInput001 ();
endinterface

module mkModule46
    (Module46);
    Reg#(Struct2) elt_fifoPInput001 <- mkReg(unpack(0));
    Reg#(Bool) full_fifoPInput001 <- mkReg(unpack(0));
    Reg#(Bool) countDone_fifoPInput001 <- mkReg(unpack(0));
    Reg#(Bit#(18)) counter_fifoPInput001 <- mkReg(unpack(0));

    rule count_fifoPInput001;

        let x_0 = (countDone_fifoPInput001);
        when (! (x_0), noAction);
        let x_1 = (counter_fifoPInput001);
        counter_fifoPInput001 <= (x_1) + ((Bit#(18))'(18'h1));
        let x_2 =
        (full_fifoPInput001);
        if (((x_1) == ((Bit#(18))'(18'h3ffff))) && (x_2)) begin
            let x_3 =
            (elt_fifoPInput001);
            $display ("-- INPUT fifoPInput001: %x %x %b %x", (x_3).in_msg_from, ((x_3).in_msg).id, ((x_3).in_msg).type_, ((x_3).in_msg).addr);
            countDone_fifoPInput001 <= (Bool)'(True);
        end else begin

        end
    endrule

    method Action enq_fifoPInput001 (Struct2 x_0);
        let x_1 = (full_fifoPInput001);
        when (! (x_1), noAction);
        elt_fifoPInput001 <= x_0;
        full_fifoPInput001 <= (Bool)'(True);
    endmethod

    method ActionValue#(Struct2) deq_fifoPInput001 ();
        let x_1 = (full_fifoPInput001);
        when (x_1, noAction);
        let x_2 = (elt_fifoPInput001);
        full_fifoPInput001 <= (Bool)'(False);
        return x_2;
    endmethod
endmodule

interface Module47;
    method Action enq_fifoCInput_001 (Struct2 x_0);
    method ActionValue#(Struct2) deq_fifoCInput_001 ();
endinterface

module mkModule47
    (Module47);
    Reg#(Struct2) elt_fifoCInput_001 <- mkReg(unpack(0));
    Reg#(Bool) full_fifoCInput_001 <- mkReg(unpack(0));
    Reg#(Bool) countDone_fifoCInput_001 <- mkReg(unpack(0));
    Reg#(Bit#(18)) counter_fifoCInput_001 <- mkReg(unpack(0));

    rule count_fifoCInput_001;

        let x_0 = (countDone_fifoCInput_001);
        when (! (x_0), noAction);
        let x_1 = (counter_fifoCInput_001);
        counter_fifoCInput_001 <= (x_1) + ((Bit#(18))'(18'h1));
        let x_2 =
        (full_fifoCInput_001);
        if (((x_1) == ((Bit#(18))'(18'h3ffff))) && (x_2)) begin
            let x_3 =
            (elt_fifoCInput_001);
            $display ("-- INPUT fifoCInput_001: %x %x %b %x", (x_3).in_msg_from, ((x_3).in_msg).id, ((x_3).in_msg).type_, ((x_3).in_msg).addr);
            countDone_fifoCInput_001 <= (Bool)'(True);
        end else begin

        end
    endrule

    method Action enq_fifoCInput_001 (Struct2 x_0);
        let x_1 = (full_fifoCInput_001);
        when (! (x_1), noAction);
        elt_fifoCInput_001 <= x_0;
        full_fifoCInput_001 <= (Bool)'(True);
    endmethod

    method ActionValue#(Struct2) deq_fifoCInput_001 ();
        let x_1 = (full_fifoCInput_001);
        when (x_1, noAction);
        let x_2 = (elt_fifoCInput_001);
        full_fifoCInput_001 <= (Bool)'(False);
        return x_2;
    endmethod
endmodule

interface Module48;
    method Action enq_fifoN2I_parent_001 (Struct42 x_0);
    method ActionValue#(Struct42) deq_fifoN2I_parent_001 ();
endinterface

module mkModule48
    (Module48);
    Reg#(Struct42) elt_fifoN2I_parent_001 <- mkReg(unpack(0));
    Reg#(Bool) full_fifoN2I_parent_001 <- mkReg(unpack(0));
    Reg#(Bool) countDone_fifoN2I_parent_001 <- mkReg(unpack(0));
    Reg#(Bit#(18)) counter_fifoN2I_parent_001 <- mkReg(unpack(0));

    rule count_fifoN2I_parent_001;

        let x_0 = (countDone_fifoN2I_parent_001);
        when (! (x_0), noAction);
        let x_1 = (counter_fifoN2I_parent_001);
        counter_fifoN2I_parent_001 <= (x_1) + ((Bit#(18))'(18'h1));
        let x_2 =
        (full_fifoN2I_parent_001);
        if (((x_1) == ((Bit#(18))'(18'h3ffff))) && (x_2)) begin
            let x_3 =
            (elt_fifoN2I_parent_001);
            $display ("-- IR fifoN2I_parent_001: %b %b %x %b %x %x %x %b %x", (x_3).ir_is_rs_rel, (x_3).ir_is_rs_acc, ((x_3).ir_msg).id, ((x_3).ir_msg).type_, ((x_3).ir_msg).addr, (x_3).ir_msg_from, (x_3).ir_mshr_id, ((x_3).ir_by_victim).valid, ((x_3).ir_by_victim).data);
            countDone_fifoN2I_parent_001 <= (Bool)'(True);
        end else begin

        end
    endrule

    method Action enq_fifoN2I_parent_001 (Struct42 x_0);
        let x_1 = (full_fifoN2I_parent_001);
        when (! (x_1), noAction);
        elt_fifoN2I_parent_001 <= x_0;
        full_fifoN2I_parent_001 <= (Bool)'(True);
    endmethod

    method ActionValue#(Struct42) deq_fifoN2I_parent_001 ();
        let x_1 = (full_fifoN2I_parent_001);
        when (x_1, noAction);
        let x_2 = (elt_fifoN2I_parent_001);
        full_fifoN2I_parent_001 <= (Bool)'(False);
        return x_2;
    endmethod
endmodule

interface Module49;
    method Action enq_fifoI2L_parent_001 (Struct42 x_0);
    method ActionValue#(Struct42) deq_fifoI2L_parent_001 ();
endinterface

module mkModule49
    (Module49);
    Reg#(Struct42) elt_fifoI2L_parent_001 <- mkReg(unpack(0));
    Reg#(Bool) full_fifoI2L_parent_001 <- mkReg(unpack(0));
    Reg#(Bool) countDone_fifoI2L_parent_001 <- mkReg(unpack(0));
    Reg#(Bit#(18)) counter_fifoI2L_parent_001 <- mkReg(unpack(0));

    rule count_fifoI2L_parent_001;

        let x_0 = (countDone_fifoI2L_parent_001);
        when (! (x_0), noAction);
        let x_1 = (counter_fifoI2L_parent_001);
        counter_fifoI2L_parent_001 <= (x_1) + ((Bit#(18))'(18'h1));
        let x_2 =
        (full_fifoI2L_parent_001);
        if (((x_1) == ((Bit#(18))'(18'h3ffff))) && (x_2)) begin
            let x_3 =
            (elt_fifoI2L_parent_001);
            $display ("-- IR fifoI2L_parent_001: %b %b %x %b %x %x %x %b %x", (x_3).ir_is_rs_rel, (x_3).ir_is_rs_acc, ((x_3).ir_msg).id, ((x_3).ir_msg).type_, ((x_3).ir_msg).addr, (x_3).ir_msg_from, (x_3).ir_mshr_id, ((x_3).ir_by_victim).valid, ((x_3).ir_by_victim).data);
            countDone_fifoI2L_parent_001 <= (Bool)'(True);
        end else begin

        end
    endrule

    method Action enq_fifoI2L_parent_001 (Struct42 x_0);
        let x_1 = (full_fifoI2L_parent_001);
        when (! (x_1), noAction);
        elt_fifoI2L_parent_001 <= x_0;
        full_fifoI2L_parent_001 <= (Bool)'(True);
    endmethod

    method ActionValue#(Struct42) deq_fifoI2L_parent_001 ();
        let x_1 = (full_fifoI2L_parent_001);
        when (x_1, noAction);
        let x_2 = (elt_fifoI2L_parent_001);
        full_fifoI2L_parent_001 <= (Bool)'(False);
        return x_2;
    endmethod
endmodule

interface Module50;
    method Action enq_fifoN2I_child_001 (Struct42 x_0);
    method ActionValue#(Struct42) deq_fifoN2I_child_001 ();
endinterface

module mkModule50
    (Module50);
    Reg#(Struct42) elt_fifoN2I_child_001 <- mkReg(unpack(0));
    Reg#(Bool) full_fifoN2I_child_001 <- mkReg(unpack(0));
    Reg#(Bool) countDone_fifoN2I_child_001 <- mkReg(unpack(0));
    Reg#(Bit#(18)) counter_fifoN2I_child_001 <- mkReg(unpack(0));

    rule count_fifoN2I_child_001;

        let x_0 = (countDone_fifoN2I_child_001);
        when (! (x_0), noAction);
        let x_1 = (counter_fifoN2I_child_001);
        counter_fifoN2I_child_001 <= (x_1) + ((Bit#(18))'(18'h1));
        let x_2 =
        (full_fifoN2I_child_001);
        if (((x_1) == ((Bit#(18))'(18'h3ffff))) && (x_2)) begin
            let x_3 =
            (elt_fifoN2I_child_001);
            $display ("-- IR fifoN2I_child_001: %b %b %x %b %x %x %x %b %x", (x_3).ir_is_rs_rel, (x_3).ir_is_rs_acc, ((x_3).ir_msg).id, ((x_3).ir_msg).type_, ((x_3).ir_msg).addr, (x_3).ir_msg_from, (x_3).ir_mshr_id, ((x_3).ir_by_victim).valid, ((x_3).ir_by_victim).data);
            countDone_fifoN2I_child_001 <= (Bool)'(True);
        end else begin

        end
    endrule

    method Action enq_fifoN2I_child_001 (Struct42 x_0);
        let x_1 = (full_fifoN2I_child_001);
        when (! (x_1), noAction);
        elt_fifoN2I_child_001 <= x_0;
        full_fifoN2I_child_001 <= (Bool)'(True);
    endmethod

    method ActionValue#(Struct42) deq_fifoN2I_child_001 ();
        let x_1 = (full_fifoN2I_child_001);
        when (x_1, noAction);
        let x_2 = (elt_fifoN2I_child_001);
        full_fifoN2I_child_001 <= (Bool)'(False);
        return x_2;
    endmethod
endmodule

interface Module51;
    method Action enq_fifoI2L_child_001 (Struct42 x_0);
    method ActionValue#(Struct42) deq_fifoI2L_child_001 ();
endinterface

module mkModule51
    (Module51);
    Reg#(Struct42) elt_fifoI2L_child_001 <- mkReg(unpack(0));
    Reg#(Bool) full_fifoI2L_child_001 <- mkReg(unpack(0));
    Reg#(Bool) countDone_fifoI2L_child_001 <- mkReg(unpack(0));
    Reg#(Bit#(18)) counter_fifoI2L_child_001 <- mkReg(unpack(0));

    rule count_fifoI2L_child_001;

        let x_0 = (countDone_fifoI2L_child_001);
        when (! (x_0), noAction);
        let x_1 = (counter_fifoI2L_child_001);
        counter_fifoI2L_child_001 <= (x_1) + ((Bit#(18))'(18'h1));
        let x_2 =
        (full_fifoI2L_child_001);
        if (((x_1) == ((Bit#(18))'(18'h3ffff))) && (x_2)) begin
            let x_3 =
            (elt_fifoI2L_child_001);
            $display ("-- IR fifoI2L_child_001: %b %b %x %b %x %x %x %b %x", (x_3).ir_is_rs_rel, (x_3).ir_is_rs_acc, ((x_3).ir_msg).id, ((x_3).ir_msg).type_, ((x_3).ir_msg).addr, (x_3).ir_msg_from, (x_3).ir_mshr_id, ((x_3).ir_by_victim).valid, ((x_3).ir_by_victim).data);
            countDone_fifoI2L_child_001 <= (Bool)'(True);
        end else begin

        end
    endrule

    method Action enq_fifoI2L_child_001 (Struct42 x_0);
        let x_1 = (full_fifoI2L_child_001);
        when (! (x_1), noAction);
        elt_fifoI2L_child_001 <= x_0;
        full_fifoI2L_child_001 <= (Bool)'(True);
    endmethod

    method ActionValue#(Struct42) deq_fifoI2L_child_001 ();
        let x_1 = (full_fifoI2L_child_001);
        when (x_1, noAction);
        let x_2 = (elt_fifoI2L_child_001);
        full_fifoI2L_child_001 <= (Bool)'(False);
        return x_2;
    endmethod
endmodule

interface Module52;
    method Action enq_fifoL2E_001 (Struct47 x_0);
    method ActionValue#(Struct47) deq_fifoL2E_001 ();
endinterface

module mkModule52
    (Module52);
    Reg#(Struct47) elt_fifoL2E_001 <- mkReg(unpack(0));
    Reg#(Bool) full_fifoL2E_001 <- mkReg(unpack(0));
    Reg#(Bool) countDone_fifoL2E_001 <- mkReg(unpack(0));
    Reg#(Bit#(18)) counter_fifoL2E_001 <- mkReg(unpack(0));

    rule count_fifoL2E_001;

        let x_0 = (countDone_fifoL2E_001);
        when (! (x_0), noAction);
        let x_1 = (counter_fifoL2E_001);
        counter_fifoL2E_001 <= (x_1) + ((Bit#(18))'(18'h1));
        let x_2 =
        (full_fifoL2E_001);
        if (((x_1) == ((Bit#(18))'(18'h3ffff))) && (x_2)) begin
            let x_3 =
            (elt_fifoL2E_001);
            $display ("-- LR fifoL2E_001: %b %b %x %b %x %x %x %b %x %x %b %x %b %x %b %x", ((x_3).lr_ir_pp).ir_is_rs_rel, ((x_3).lr_ir_pp).ir_is_rs_acc, (((x_3).lr_ir_pp).ir_msg).id, (((x_3).lr_ir_pp).ir_msg).type_, (((x_3).lr_ir_pp).ir_msg).addr, ((x_3).lr_ir_pp).ir_msg_from, ((x_3).lr_ir_pp).ir_mshr_id, (((x_3).lr_ir_pp).ir_by_victim).valid, (((x_3).lr_ir_pp).ir_by_victim).data, ((x_3).lr_ir).info_index, ((x_3).lr_ir).info_hit, ((x_3).lr_ir).info_way, ((x_3).lr_ir).edir_hit, ((x_3).lr_ir).edir_way, (((x_3).lr_ir).edir_slot).valid, (((x_3).lr_ir).edir_slot).data);
            countDone_fifoL2E_001 <= (Bool)'(True);
        end else begin

        end
    endrule

    method Action enq_fifoL2E_001 (Struct47 x_0);
        let x_1 = (full_fifoL2E_001);
        when (! (x_1), noAction);
        elt_fifoL2E_001 <= x_0;
        full_fifoL2E_001 <= (Bool)'(True);
    endmethod

    method ActionValue#(Struct47) deq_fifoL2E_001 ();
        let x_1 = (full_fifoL2E_001);
        when (x_1, noAction);
        let x_2 = (elt_fifoL2E_001);
        full_fifoL2E_001 <= (Bool)'(False);
        return x_2;
    endmethod
endmodule

interface Module53;
    method Action enq_fifo0010 (Struct1 x_0);
    method ActionValue#(Struct1) deq_fifo0010 ();
endinterface

module mkModule53
    (Module53);
    Reg#(Struct1) elt_fifo0010 <- mkReg(unpack(0));
    Reg#(Bool) full_fifo0010 <- mkReg(unpack(0));
    Reg#(Bool) countDone_fifo0010 <- mkReg(unpack(0));
    Reg#(Bit#(18)) counter_fifo0010 <- mkReg(unpack(0));

    rule count_fifo0010;

        let x_0 = (countDone_fifo0010);
        when (! (x_0), noAction);
        let x_1 = (counter_fifo0010);
        counter_fifo0010 <= (x_1) + ((Bit#(18))'(18'h1));
        let x_2 =
        (full_fifo0010);
        if (((x_1) == ((Bit#(18))'(18'h3ffff))) && (x_2)) begin
            let x_3 =
            (elt_fifo0010);
            $display ("-- MSG fifo0010: %x %b %x", (x_3).id, (x_3).type_, (x_3).addr);
            countDone_fifo0010 <= (Bool)'(True);
        end else begin

        end
    endrule

    method Action enq_fifo0010 (Struct1 x_0);
        let x_1 = (full_fifo0010);
        when (! (x_1), noAction);
        elt_fifo0010 <= x_0;
        full_fifo0010 <= (Bool)'(True);
    endmethod

    method ActionValue#(Struct1) deq_fifo0010 ();
        let x_1 = (full_fifo0010);
        when (x_1, noAction);
        let x_2 = (elt_fifo0010);
        full_fifo0010 <= (Bool)'(False);
        return x_2;
    endmethod
endmodule

interface Module54;
    method Action enq_fifo0011 (Struct1 x_0);
    method ActionValue#(Struct1) deq_fifo0011 ();
endinterface

module mkModule54
    (Module54);
    Reg#(Struct1) elt_fifo0011 <- mkReg(unpack(0));
    Reg#(Bool) full_fifo0011 <- mkReg(unpack(0));
    Reg#(Bool) countDone_fifo0011 <- mkReg(unpack(0));
    Reg#(Bit#(18)) counter_fifo0011 <- mkReg(unpack(0));

    rule count_fifo0011;

        let x_0 = (countDone_fifo0011);
        when (! (x_0), noAction);
        let x_1 = (counter_fifo0011);
        counter_fifo0011 <= (x_1) + ((Bit#(18))'(18'h1));
        let x_2 =
        (full_fifo0011);
        if (((x_1) == ((Bit#(18))'(18'h3ffff))) && (x_2)) begin
            let x_3 =
            (elt_fifo0011);
            $display ("-- MSG fifo0011: %x %b %x", (x_3).id, (x_3).type_, (x_3).addr);
            countDone_fifo0011 <= (Bool)'(True);
        end else begin

        end
    endrule

    method Action enq_fifo0011 (Struct1 x_0);
        let x_1 = (full_fifo0011);
        when (! (x_1), noAction);
        elt_fifo0011 <= x_0;
        full_fifo0011 <= (Bool)'(True);
    endmethod

    method ActionValue#(Struct1) deq_fifo0011 ();
        let x_1 = (full_fifo0011);
        when (x_1, noAction);
        let x_2 = (elt_fifo0011);
        full_fifo0011 <= (Bool)'(False);
        return x_2;
    endmethod
endmodule

interface Module55;
    method Action enq_fifo0012 (Struct1 x_0);
    method ActionValue#(Struct1) deq_fifo0012 ();
endinterface

module mkModule55
    (Module55);
    Reg#(Struct1) elt_fifo0012 <- mkReg(unpack(0));
    Reg#(Bool) full_fifo0012 <- mkReg(unpack(0));
    Reg#(Bool) countDone_fifo0012 <- mkReg(unpack(0));
    Reg#(Bit#(18)) counter_fifo0012 <- mkReg(unpack(0));

    rule count_fifo0012;

        let x_0 = (countDone_fifo0012);
        when (! (x_0), noAction);
        let x_1 = (counter_fifo0012);
        counter_fifo0012 <= (x_1) + ((Bit#(18))'(18'h1));
        let x_2 =
        (full_fifo0012);
        if (((x_1) == ((Bit#(18))'(18'h3ffff))) && (x_2)) begin
            let x_3 =
            (elt_fifo0012);
            $display ("-- MSG fifo0012: %x %b %x", (x_3).id, (x_3).type_, (x_3).addr);
            countDone_fifo0012 <= (Bool)'(True);
        end else begin

        end
    endrule

    method Action enq_fifo0012 (Struct1 x_0);
        let x_1 = (full_fifo0012);
        when (! (x_1), noAction);
        elt_fifo0012 <= x_0;
        full_fifo0012 <= (Bool)'(True);
    endmethod

    method ActionValue#(Struct1) deq_fifo0012 ();
        let x_1 = (full_fifo0012);
        when (x_1, noAction);
        let x_2 = (elt_fifo0012);
        full_fifo0012 <= (Bool)'(False);
        return x_2;
    endmethod
endmodule

interface Module56;
    method Action enq_fifo00100 (Struct1 x_0);
    method ActionValue#(Struct1) deq_fifo00100 ();
endinterface

module mkModule56
    (Module56);
    Reg#(Struct1) elt_fifo00100 <- mkReg(unpack(0));
    Reg#(Bool) full_fifo00100 <- mkReg(unpack(0));
    Reg#(Bool) countDone_fifo00100 <- mkReg(unpack(0));
    Reg#(Bit#(18)) counter_fifo00100 <- mkReg(unpack(0));

    rule count_fifo00100;

        let x_0 = (countDone_fifo00100);
        when (! (x_0), noAction);
        let x_1 = (counter_fifo00100);
        counter_fifo00100 <= (x_1) + ((Bit#(18))'(18'h1));
        let x_2 =
        (full_fifo00100);
        if (((x_1) == ((Bit#(18))'(18'h3ffff))) && (x_2)) begin
            let x_3 =
            (elt_fifo00100);
            $display ("-- MSG fifo00100: %x %b %x", (x_3).id, (x_3).type_, (x_3).addr);
            countDone_fifo00100 <= (Bool)'(True);
        end else begin

        end
    endrule

    method Action enq_fifo00100 (Struct1 x_0);
        let x_1 = (full_fifo00100);
        when (! (x_1), noAction);
        elt_fifo00100 <= x_0;
        full_fifo00100 <= (Bool)'(True);
    endmethod

    method ActionValue#(Struct1) deq_fifo00100 ();
        let x_1 = (full_fifo00100);
        when (x_1, noAction);
        let x_2 = (elt_fifo00100);
        full_fifo00100 <= (Bool)'(False);
        return x_2;
    endmethod
endmodule

interface Module57;
    method Action enq_fifo00102 (Struct1 x_0);
    method ActionValue#(Struct1) deq_fifo00102 ();
endinterface

module mkModule57
    (Module57);
    Reg#(Struct1) elt_fifo00102 <- mkReg(unpack(0));
    Reg#(Bool) full_fifo00102 <- mkReg(unpack(0));
    Reg#(Bool) countDone_fifo00102 <- mkReg(unpack(0));
    Reg#(Bit#(18)) counter_fifo00102 <- mkReg(unpack(0));

    rule count_fifo00102;

        let x_0 = (countDone_fifo00102);
        when (! (x_0), noAction);
        let x_1 = (counter_fifo00102);
        counter_fifo00102 <= (x_1) + ((Bit#(18))'(18'h1));
        let x_2 =
        (full_fifo00102);
        if (((x_1) == ((Bit#(18))'(18'h3ffff))) && (x_2)) begin
            let x_3 =
            (elt_fifo00102);
            $display ("-- MSG fifo00102: %x %b %x", (x_3).id, (x_3).type_, (x_3).addr);
            countDone_fifo00102 <= (Bool)'(True);
        end else begin

        end
    endrule

    method Action enq_fifo00102 (Struct1 x_0);
        let x_1 = (full_fifo00102);
        when (! (x_1), noAction);
        elt_fifo00102 <= x_0;
        full_fifo00102 <= (Bool)'(True);
    endmethod

    method ActionValue#(Struct1) deq_fifo00102 ();
        let x_1 = (full_fifo00102);
        when (x_1, noAction);
        let x_2 = (elt_fifo00102);
        full_fifo00102 <= (Bool)'(False);
        return x_2;
    endmethod
endmodule

interface Module58;
    method ActionValue#(Struct41) victims__001findVictim (Bit#(64) x_0);
    method ActionValue#(Struct48) victims__001__getVictim (Bit#(1) x_0);
    method Action victims__001__setVictim (Struct54 x_0);
    method Action victims__001__registerVictim (Struct48 x_0);
    method ActionValue#(Struct48) victims__001__getFirstVictim ();
    method Action victims__001__setVictimRq (Struct55 x_0);
    method ActionValue#(Bit#(3)) victims__001__releaseVictim (Bit#(64) x_0);
endinterface

module mkModule58
    (Module58);
    Reg#(Vector#(4, Struct48)) victimRegs__001 <- mkReg(unpack(0));

    // No rules in this module

    method ActionValue#(Struct41) victims__001findVictim (Bit#(64) x_0);
        let x_1 = (victimRegs__001);
        Struct48 x_2 =
        ((x_1)[(Bit#(1))'(1'h0)]);
        let x_9 = ?;
        if (((x_2).victim_valid) && (((x_2).victim_addr) == (x_0))) begin
            x_9 = Struct41 {valid : (Bool)'(True), data : (Bit#(1))'(1'h0)};
        end else begin
            Struct48 x_3 =
            ((x_1)[(Bit#(1))'(1'h1)]);
            let x_8 = ?;
            if (((x_3).victim_valid) && (((x_3).victim_addr) == (x_0)))
                begin
                x_8 = Struct41 {valid : (Bool)'(True), data :
                (Bit#(1))'(1'h1)};
            end else begin
                Struct48 x_4 =
                ((x_1)[(Bit#(1))'(1'h0)]);
                let x_7 = ?;
                if (((x_4).victim_valid) && (((x_4).victim_addr) == (x_0)))
                    begin
                    x_7 = Struct41 {valid : (Bool)'(True), data :
                    (Bit#(1))'(1'h0)};
                end else begin
                    Struct48 x_5 =
                    ((x_1)[(Bit#(1))'(1'h1)]);
                    let x_6 = ?;
                    if (((x_5).victim_valid) && (((x_5).victim_addr) ==
                        (x_0))) begin
                        x_6 = Struct41 {valid : (Bool)'(True), data :
                        (Bit#(1))'(1'h1)};
                    end else begin
                        x_6 = Struct41 {valid : (Bool)'(False), data :
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

    method ActionValue#(Struct48) victims__001__getVictim (Bit#(1) x_0);
        let x_1 = (victimRegs__001);
        return (x_1)[x_0];
    endmethod

    method Action victims__001__setVictim (Struct54 x_0);
        let x_1 = (victimRegs__001);
        Struct48 x_2 = ((x_1)[(x_0).victim_idx]);
        Struct48 x_3 = (Struct48 {victim_valid : (Bool)'(True), victim_addr :
        (x_2).victim_addr, victim_info : (x_0).victim_info, victim_value :
        (x_0).victim_value, victim_req : (x_2).victim_req});
        victimRegs__001 <= update (x_1, (x_0).victim_idx, x_3);
    endmethod

    method Action victims__001__registerVictim (Struct48 x_0);
        let x_1 = (victimRegs__001);
        Struct41 x_2 = ((((x_1)[(Bit#(1))'(1'h1)]).victim_valid ?
        ((((x_1)[(Bit#(1))'(1'h0)]).victim_valid ?
        ((((x_1)[(Bit#(1))'(1'h1)]).victim_valid ? (Struct41 {valid :
        (Bool)'(False), data : unpack(0)}) : (Struct41 {valid :
        (Bool)'(True), data : (Bit#(1))'(1'h1)}))) : (Struct41 {valid :
        (Bool)'(True), data : (Bit#(1))'(1'h0)}))) : (Struct41 {valid :
        (Bool)'(True), data : (Bit#(1))'(1'h1)})));
        when ((x_2).valid, noAction);
        Bit#(1) x_3 = ((x_2).data);
        victimRegs__001 <= update (x_1, x_3, x_0);
    endmethod

    method ActionValue#(Struct48) victims__001__getFirstVictim ();
        let x_1 = (victimRegs__001);
        Struct61 x_2 = (((((x_1)[(Bit#(1))'(1'h1)]).victim_valid) && (!
        ((((x_1)[(Bit#(1))'(1'h1)]).victim_req).valid)) ? (Struct61 {valid :
        (Bool)'(True), data : (x_1)[(Bit#(1))'(1'h1)]}) :
        (((((x_1)[(Bit#(1))'(1'h0)]).victim_valid) && (!
        ((((x_1)[(Bit#(1))'(1'h0)]).victim_req).valid)) ? (Struct61 {valid :
        (Bool)'(True), data : (x_1)[(Bit#(1))'(1'h0)]}) :
        (((((x_1)[(Bit#(1))'(1'h1)]).victim_valid) && (!
        ((((x_1)[(Bit#(1))'(1'h1)]).victim_req).valid)) ? (Struct61 {valid :
        (Bool)'(True), data : (x_1)[(Bit#(1))'(1'h1)]}) : (Struct61 {valid :
        (Bool)'(False), data : unpack(0)})))))));
        when ((x_2).valid, noAction);
        return (x_2).data;
    endmethod

    method Action victims__001__setVictimRq (Struct55 x_0);
        Bit#(64) x_1 = ((x_0).victim_addr);
        Bit#(3) x_2 = ((x_0).victim_req);
        let x_3 = (victimRegs__001);
        Struct48 x_4 =
        ((x_3)[(Bit#(1))'(1'h1)]);
        if (((x_4).victim_valid) && (((x_4).victim_addr) == (x_1)))
            begin
            Struct48 x_5 = (Struct48 {victim_valid : (x_4).victim_valid,
            victim_addr : (x_4).victim_addr, victim_info : (x_4).victim_info,
            victim_value : (x_4).victim_value, victim_req : Struct49 {valid :
            (Bool)'(True), data : x_2}});
            victimRegs__001 <= update (x_3, (Bit#(1))'(1'h1), x_5);
        end else begin
            Struct48 x_6 =
            ((x_3)[(Bit#(1))'(1'h0)]);
            if (((x_6).victim_valid) && (((x_6).victim_addr) == (x_1)))
                begin
                Struct48 x_7 = (Struct48 {victim_valid : (x_6).victim_valid,
                victim_addr : (x_6).victim_addr, victim_info :
                (x_6).victim_info, victim_value : (x_6).victim_value,
                victim_req : Struct49 {valid : (Bool)'(True), data :
                x_2}});
                victimRegs__001 <= update (x_3, (Bit#(1))'(1'h0), x_7);
            end else begin
                Struct48 x_8 =
                ((x_3)[(Bit#(1))'(1'h1)]);
                if (((x_8).victim_valid) && (((x_8).victim_addr) == (x_1)))
                    begin
                    Struct48 x_9 = (Struct48 {victim_valid :
                    (x_8).victim_valid, victim_addr : (x_8).victim_addr,
                    victim_info : (x_8).victim_info, victim_value :
                    (x_8).victim_value, victim_req : Struct49 {valid :
                    (Bool)'(True), data : x_2}});
                    victimRegs__001 <= update (x_3, (Bit#(1))'(1'h1), x_9);
                end else begin

                end
            end
        end
    endmethod

    method ActionValue#(Bit#(3)) victims__001__releaseVictim (Bit#(64) x_0);
        let x_1 = (victimRegs__001);
        Struct48 x_2 =
        ((x_1)[(Bit#(1))'(1'h0)]);
        let x_13 = ?;
        if (((x_2).victim_valid) && (((x_2).victim_addr) == (x_0)))
            begin
            victimRegs__001 <= update (x_1, (Bit#(1))'(1'h0),
            unpack(0));
            Bit#(3) x_3 = (((x_2).victim_req).data);
            x_13 = x_3;
        end else begin
            Struct48 x_4 =
            ((x_1)[(Bit#(1))'(1'h1)]);
            let x_12 = ?;
            if (((x_4).victim_valid) && (((x_4).victim_addr) == (x_0)))
                begin
                victimRegs__001 <= update (x_1, (Bit#(1))'(1'h1),
                unpack(0));
                Bit#(3) x_5 = (((x_4).victim_req).data);
                x_12 = x_5;
            end else begin
                Struct48 x_6 =
                ((x_1)[(Bit#(1))'(1'h0)]);
                let x_11 = ?;
                if (((x_6).victim_valid) && (((x_6).victim_addr) == (x_0)))
                    begin
                    victimRegs__001 <= update (x_1, (Bit#(1))'(1'h0),
                    unpack(0));
                    Bit#(3) x_7 = (((x_6).victim_req).data);
                    x_11 = x_7;
                end else begin
                    Struct48 x_8 =
                    ((x_1)[(Bit#(1))'(1'h1)]);
                    let x_10 = ?;
                    if (((x_8).victim_valid) && (((x_8).victim_addr) ==
                        (x_0))) begin
                        victimRegs__001 <= update (x_1, (Bit#(1))'(1'h1),
                        unpack(0));
                        Bit#(3) x_9 = (((x_8).victim_req).data);
                        x_10 = x_9;
                    end else begin
                        x_10 = unpack(0);
                    end
                    x_11 = x_10;
                end
                x_12 = x_11;
            end
            x_13 = x_12;
        end
        return x_13;
    endmethod
endmodule

interface Module59;
    method Action rdReq_infoRam__001__3 (Bit#(8) x_0);
    method Action wrReq_infoRam__001__3 (Struct58 x_0);
    method ActionValue#(Struct56) rdResp_infoRam__001__3 ();
endinterface

module mkModule59 (Module59);
    RWBramCore#(Bit#(8), Struct56) bram <- mkRWBramCore();
    Reg#(Bool) initDone <- mkReg(False);
    Reg#(Bit#(8)) initIdx <- mkReg(0);

    rule init (!initDone);
        let initData = Struct56 {tag: 51'h3, value: Struct11 {mesi_owned: False, mesi_status: 3'h1, mesi_dir_st: 3'h1, mesi_dir_sharers: 2'h0}};
        bram.wrReq(initIdx, initData);
        initIdx <= initIdx + 1;
        initDone <= (initIdx == maxBound);
    endrule

    method Action rdReq_infoRam__001__3 (Bit#(8) x_0) if(initDone);
        bram.rdReq(x_0);
    endmethod

    method Action wrReq_infoRam__001__3 (Struct58 x_0) if(initDone);
        bram.wrReq(x_0.addr, x_0.datain);
    endmethod

    method ActionValue#(Struct56) rdResp_infoRam__001__3 () if(initDone);
        bram.deqRdResp ();
        let data = bram.rdResp ();
        return data;
    endmethod


endmodule

interface Module60;
    method Action rdReq_infoRam__001__2 (Bit#(8) x_0);
    method Action wrReq_infoRam__001__2 (Struct58 x_0);
    method ActionValue#(Struct56) rdResp_infoRam__001__2 ();
endinterface

module mkModule60 (Module60);
    RWBramCore#(Bit#(8), Struct56) bram <- mkRWBramCore();
    Reg#(Bool) initDone <- mkReg(False);
    Reg#(Bit#(8)) initIdx <- mkReg(0);

    rule init (!initDone);
        let initData = Struct56 {tag: 51'h2, value: Struct11 {mesi_owned: False, mesi_status: 3'h1, mesi_dir_st: 3'h1, mesi_dir_sharers: 2'h0}};
        bram.wrReq(initIdx, initData);
        initIdx <= initIdx + 1;
        initDone <= (initIdx == maxBound);
    endrule

    method Action rdReq_infoRam__001__2 (Bit#(8) x_0) if(initDone);
        bram.rdReq(x_0);
    endmethod

    method Action wrReq_infoRam__001__2 (Struct58 x_0) if(initDone);
        bram.wrReq(x_0.addr, x_0.datain);
    endmethod

    method ActionValue#(Struct56) rdResp_infoRam__001__2 () if(initDone);
        bram.deqRdResp ();
        let data = bram.rdResp ();
        return data;
    endmethod


endmodule

interface Module61;
    method Action rdReq_infoRam__001__1 (Bit#(8) x_0);
    method Action wrReq_infoRam__001__1 (Struct58 x_0);
    method ActionValue#(Struct56) rdResp_infoRam__001__1 ();
endinterface

module mkModule61 (Module61);
    RWBramCore#(Bit#(8), Struct56) bram <- mkRWBramCore();
    Reg#(Bool) initDone <- mkReg(False);
    Reg#(Bit#(8)) initIdx <- mkReg(0);

    rule init (!initDone);
        let initData = Struct56 {tag: 51'h1, value: Struct11 {mesi_owned: False, mesi_status: 3'h1, mesi_dir_st: 3'h1, mesi_dir_sharers: 2'h0}};
        bram.wrReq(initIdx, initData);
        initIdx <= initIdx + 1;
        initDone <= (initIdx == maxBound);
    endrule

    method Action rdReq_infoRam__001__1 (Bit#(8) x_0) if(initDone);
        bram.rdReq(x_0);
    endmethod

    method Action wrReq_infoRam__001__1 (Struct58 x_0) if(initDone);
        bram.wrReq(x_0.addr, x_0.datain);
    endmethod

    method ActionValue#(Struct56) rdResp_infoRam__001__1 () if(initDone);
        bram.deqRdResp ();
        let data = bram.rdResp ();
        return data;
    endmethod


endmodule

interface Module62;
    method Action rdReq_infoRam__001__0 (Bit#(8) x_0);
    method Action wrReq_infoRam__001__0 (Struct58 x_0);
    method ActionValue#(Struct56) rdResp_infoRam__001__0 ();
endinterface

module mkModule62 (Module62);
    RWBramCore#(Bit#(8), Struct56) bram <- mkRWBramCore();
    Reg#(Bool) initDone <- mkReg(False);
    Reg#(Bit#(8)) initIdx <- mkReg(0);

    rule init (!initDone);
        let initData = Struct56 {tag: 51'h0, value: Struct11 {mesi_owned: False, mesi_status: 3'h1, mesi_dir_st: 3'h1, mesi_dir_sharers: 2'h0}};
        bram.wrReq(initIdx, initData);
        initIdx <= initIdx + 1;
        initDone <= (initIdx == maxBound);
    endrule

    method Action rdReq_infoRam__001__0 (Bit#(8) x_0) if(initDone);
        bram.rdReq(x_0);
    endmethod

    method Action wrReq_infoRam__001__0 (Struct58 x_0) if(initDone);
        bram.wrReq(x_0.addr, x_0.datain);
    endmethod

    method ActionValue#(Struct56) rdResp_infoRam__001__0 () if(initDone);
        bram.deqRdResp ();
        let data = bram.rdResp ();
        return data;
    endmethod


endmodule

interface Module63;
    method Action rdReq_dataRam__001 (Bit#(10) x_0);
    method Action wrReq_dataRam__001 (Struct60 x_0);
    method ActionValue#(Vector#(4, Bit#(64))) rdResp_dataRam__001 ();
endinterface

module mkModule63 (Module63);
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

    method Action wrReq_dataRam__001 (Struct60 x_0) if(initDone);
        bram.wrReq(x_0.addr, x_0.datain);
    endmethod

    method ActionValue#(Vector#(4, Bit#(64))) rdResp_dataRam__001 ()
    if(initDone);
        bram.deqRdResp ();
        let data = bram.rdResp ();
        return data;
    endmethod


endmodule

interface Module64;
    method Action rdReq_repRam__001 (Bit#(8) x_0);
    method Action wrReq_repRam__001 (Struct62 x_0);
    method ActionValue#(Vector#(4, Bit#(8))) rdResp_repRam__001 ();
endinterface

module mkModule64 (Module64);
    RWBramCore#(Bit#(8), Vector#(4, Bit#(8))) bram <- mkRWBramCore();
    Reg#(Bool) initDone <- mkReg(False);
    Reg#(Bit#(8)) initIdx <- mkReg(0);

    rule init (!initDone);
        let initData = vec(8'h0, 8'h0, 8'h0, 8'h0);
        bram.wrReq(initIdx, initData);
        initIdx <= initIdx + 1;
        initDone <= (initIdx == maxBound);
    endrule

    method Action rdReq_repRam__001 (Bit#(8) x_0) if(initDone);
        bram.rdReq(x_0);
    endmethod

    method Action wrReq_repRam__001 (Struct62 x_0) if(initDone);
        bram.wrReq(x_0.addr, x_0.datain);
    endmethod

    method ActionValue#(Vector#(4, Bit#(8))) rdResp_repRam__001 ()
    if(initDone);
        bram.deqRdResp ();
        let data = bram.rdResp ();
        return data;
    endmethod


endmodule

interface Module65;
    method ActionValue#(Struct51) getMSHR_001 (Bit#(3) x_0);
    method ActionValue#(Struct40) getPRqSlot_001 (Struct39 x_0);
    method ActionValue#(Struct40) getCRqSlot_001 (Struct39 x_0);
    method ActionValue#(Struct50) getWait_001 ();
    method Action registerUL_001 (Struct53 x_0);
    method Action registerDL_001 (Struct63 x_0);
    method ActionValue#(Bit#(3)) getULImm_001 (Struct1 x_0);
    method Action transferUpDown_001 (Struct64 x_0);
    method ActionValue#(Bit#(3)) findUL_001 (Bit#(64) x_0);
    method ActionValue#(Bit#(3)) findDL_001 (Bit#(64) x_0);
    method Action releaseMSHR_001 (Bit#(3) x_0);
    method Action addRs_001 (Struct44 x_0);
    method ActionValue#(Struct43) getRsReady_001 ();
endinterface

module mkModule65
    (Module65);
    Reg#(Vector#(6, Struct51)) rqs_001 <- mkReg(unpack(0));

    // No rules in this module

    method ActionValue#(Struct51) getMSHR_001 (Bit#(3) x_0);
        let x_1 = (rqs_001);
        return (x_1)[x_0];
    endmethod

    method ActionValue#(Struct40) getPRqSlot_001 (Struct39 x_0);
        let x_1 = (rqs_001);
        Struct49 x_2 = (((((x_1)[(Bit#(3))'(3'h0)]).m_status) ==
        ((Bit#(3))'(3'h0)) ? (Struct49 {valid : (Bool)'(True), data :
        (Bit#(3))'(3'h0)}) : (((((x_1)[(Bit#(3))'(3'h1)]).m_status) ==
        ((Bit#(3))'(3'h0)) ? (Struct49 {valid : (Bool)'(True), data :
        (Bit#(3))'(3'h1)}) : (Struct49 {valid : (Bool)'(False), data :
        unpack(0)})))));
        Bool x_3 = ((x_2).valid);
        Bit#(3) x_4 = ((x_2).data);
        Bit#(64) x_5 = (((x_0).r_msg).addr);
        Struct49 x_6 = ((((! ((((x_1)[(Bit#(3))'(3'h0)]).m_status) ==
        ((Bit#(3))'(3'h0)))) && (!
        ((((x_1)[(Bit#(3))'(3'h0)]).m_next).valid))) &&
        (((((x_1)[(Bit#(3))'(3'h0)]).m_msg).addr) == (x_5)) ? (Struct49
        {valid : (Bool)'(True), data : (Bit#(3))'(3'h0)}) : ((((!
        ((((x_1)[(Bit#(3))'(3'h1)]).m_status) == ((Bit#(3))'(3'h0)))) && (!
        ((((x_1)[(Bit#(3))'(3'h1)]).m_next).valid))) &&
        (((((x_1)[(Bit#(3))'(3'h1)]).m_msg).addr) == (x_5)) ? (Struct49
        {valid : (Bool)'(True), data : (Bit#(3))'(3'h1)}) : ((((!
        ((((x_1)[(Bit#(3))'(3'h2)]).m_status) == ((Bit#(3))'(3'h0)))) && (!
        ((((x_1)[(Bit#(3))'(3'h2)]).m_next).valid))) &&
        (((((x_1)[(Bit#(3))'(3'h2)]).m_msg).addr) == (x_5)) ? (Struct49
        {valid : (Bool)'(True), data : (Bit#(3))'(3'h2)}) : ((((!
        ((((x_1)[(Bit#(3))'(3'h3)]).m_status) == ((Bit#(3))'(3'h0)))) && (!
        ((((x_1)[(Bit#(3))'(3'h3)]).m_next).valid))) &&
        (((((x_1)[(Bit#(3))'(3'h3)]).m_msg).addr) == (x_5)) ? (Struct49
        {valid : (Bool)'(True), data : (Bit#(3))'(3'h3)}) : ((((!
        ((((x_1)[(Bit#(3))'(3'h4)]).m_status) == ((Bit#(3))'(3'h0)))) && (!
        ((((x_1)[(Bit#(3))'(3'h4)]).m_next).valid))) &&
        (((((x_1)[(Bit#(3))'(3'h4)]).m_msg).addr) == (x_5)) ? (Struct49
        {valid : (Bool)'(True), data : (Bit#(3))'(3'h4)}) : ((((!
        ((((x_1)[(Bit#(3))'(3'h5)]).m_status) == ((Bit#(3))'(3'h0)))) && (!
        ((((x_1)[(Bit#(3))'(3'h5)]).m_next).valid))) &&
        (((((x_1)[(Bit#(3))'(3'h5)]).m_msg).addr) == (x_5)) ? (Struct49
        {valid : (Bool)'(True), data : (Bit#(3))'(3'h5)}) : (Struct49 {valid
        : (Bool)'(False), data : unpack(0)})))))))))))));
        Bool x_7 = ((x_6).valid);
        Bit#(3) x_8 = ((x_6).data);
        Struct40 x_9 = (Struct40 {s_has_slot : x_3, s_conflict : x_7, s_id :
        x_4});
        if (x_3) begin
            Vector#(6, Struct51) x_10 = (update (x_1, x_4, Struct51 {m_status
            : (x_7 ? ((Bit#(3))'(3'h1)) : ((Bit#(3))'(3'h3))), m_next :
            Struct49 {valid : (Bool)'(False), data : unpack(0)}, m_is_ul :
            unpack(0), m_msg : (x_0).r_msg, m_qidx : (x_0).r_msg_from, m_rsb
            : unpack(0), m_dl_rss_from : unpack(0), m_dl_rss_recv :
            unpack(0), m_dl_rss :
            unpack(0)}));
            let x_13 = ?;
            if (x_7) begin
                Struct51 x_11 = ((x_1)[x_8]);
                Vector#(6, Struct51) x_12 = (update (x_10, x_8, Struct51
                {m_status : (x_11).m_status, m_next : (x_7 ? (Struct49 {valid
                : (Bool)'(True), data : x_4}) : ((x_11).m_next)), m_is_ul :
                (x_11).m_is_ul, m_msg : (x_11).m_msg, m_qidx : (x_11).m_qidx,
                m_rsb : (x_11).m_rsb, m_dl_rss_from : (x_11).m_dl_rss_from,
                m_dl_rss_recv : (x_11).m_dl_rss_recv, m_dl_rss :
                (x_11).m_dl_rss}));
                x_13 = x_12;
            end else begin
                x_13 = x_10;
            end
            rqs_001 <= x_13;
        end else begin

        end
        return x_9;
    endmethod

    method ActionValue#(Struct40) getCRqSlot_001 (Struct39 x_0);
        let x_1 = (rqs_001);
        Struct49 x_2 = (((((x_1)[(Bit#(3))'(3'h2)]).m_status) ==
        ((Bit#(3))'(3'h0)) ? (Struct49 {valid : (Bool)'(True), data :
        (Bit#(3))'(3'h2)}) : (((((x_1)[(Bit#(3))'(3'h3)]).m_status) ==
        ((Bit#(3))'(3'h0)) ? (Struct49 {valid : (Bool)'(True), data :
        (Bit#(3))'(3'h3)}) : (((((x_1)[(Bit#(3))'(3'h4)]).m_status) ==
        ((Bit#(3))'(3'h0)) ? (Struct49 {valid : (Bool)'(True), data :
        (Bit#(3))'(3'h4)}) : (((((x_1)[(Bit#(3))'(3'h5)]).m_status) ==
        ((Bit#(3))'(3'h0)) ? (Struct49 {valid : (Bool)'(True), data :
        (Bit#(3))'(3'h5)}) : (Struct49 {valid : (Bool)'(False), data :
        unpack(0)})))))))));
        Bool x_3 = ((x_2).valid);
        Bit#(3) x_4 = ((x_2).data);
        Bit#(64) x_5 = (((x_0).r_msg).addr);
        Struct49 x_6 = ((((! ((((x_1)[(Bit#(3))'(3'h0)]).m_status) ==
        ((Bit#(3))'(3'h0)))) && (!
        ((((x_1)[(Bit#(3))'(3'h0)]).m_next).valid))) &&
        (((((x_1)[(Bit#(3))'(3'h0)]).m_msg).addr) == (x_5)) ? (Struct49
        {valid : (Bool)'(True), data : (Bit#(3))'(3'h0)}) : ((((!
        ((((x_1)[(Bit#(3))'(3'h1)]).m_status) == ((Bit#(3))'(3'h0)))) && (!
        ((((x_1)[(Bit#(3))'(3'h1)]).m_next).valid))) &&
        (((((x_1)[(Bit#(3))'(3'h1)]).m_msg).addr) == (x_5)) ? (Struct49
        {valid : (Bool)'(True), data : (Bit#(3))'(3'h1)}) : ((((!
        ((((x_1)[(Bit#(3))'(3'h2)]).m_status) == ((Bit#(3))'(3'h0)))) && (!
        ((((x_1)[(Bit#(3))'(3'h2)]).m_next).valid))) &&
        (((((x_1)[(Bit#(3))'(3'h2)]).m_msg).addr) == (x_5)) ? (Struct49
        {valid : (Bool)'(True), data : (Bit#(3))'(3'h2)}) : ((((!
        ((((x_1)[(Bit#(3))'(3'h3)]).m_status) == ((Bit#(3))'(3'h0)))) && (!
        ((((x_1)[(Bit#(3))'(3'h3)]).m_next).valid))) &&
        (((((x_1)[(Bit#(3))'(3'h3)]).m_msg).addr) == (x_5)) ? (Struct49
        {valid : (Bool)'(True), data : (Bit#(3))'(3'h3)}) : ((((!
        ((((x_1)[(Bit#(3))'(3'h4)]).m_status) == ((Bit#(3))'(3'h0)))) && (!
        ((((x_1)[(Bit#(3))'(3'h4)]).m_next).valid))) &&
        (((((x_1)[(Bit#(3))'(3'h4)]).m_msg).addr) == (x_5)) ? (Struct49
        {valid : (Bool)'(True), data : (Bit#(3))'(3'h4)}) : ((((!
        ((((x_1)[(Bit#(3))'(3'h5)]).m_status) == ((Bit#(3))'(3'h0)))) && (!
        ((((x_1)[(Bit#(3))'(3'h5)]).m_next).valid))) &&
        (((((x_1)[(Bit#(3))'(3'h5)]).m_msg).addr) == (x_5)) ? (Struct49
        {valid : (Bool)'(True), data : (Bit#(3))'(3'h5)}) : (Struct49 {valid
        : (Bool)'(False), data : unpack(0)})))))))))))));
        Bool x_7 = ((x_6).valid);
        Bit#(3) x_8 = ((x_6).data);
        Struct40 x_9 = (Struct40 {s_has_slot : x_3, s_conflict : x_7, s_id :
        x_4});
        if (x_3) begin
            Vector#(6, Struct51) x_10 = (update (x_1, x_4, Struct51 {m_status
            : (x_7 ? ((Bit#(3))'(3'h1)) : ((Bit#(3))'(3'h3))), m_next :
            Struct49 {valid : (Bool)'(False), data : unpack(0)}, m_is_ul :
            unpack(0), m_msg : (x_0).r_msg, m_qidx : (x_0).r_msg_from, m_rsb
            : unpack(0), m_dl_rss_from : unpack(0), m_dl_rss_recv :
            unpack(0), m_dl_rss :
            unpack(0)}));
            let x_13 = ?;
            if (x_7) begin
                Struct51 x_11 = ((x_1)[x_8]);
                Vector#(6, Struct51) x_12 = (update (x_10, x_8, Struct51
                {m_status : (x_11).m_status, m_next : (x_7 ? (Struct49 {valid
                : (Bool)'(True), data : x_4}) : ((x_11).m_next)), m_is_ul :
                (x_11).m_is_ul, m_msg : (x_11).m_msg, m_qidx : (x_11).m_qidx,
                m_rsb : (x_11).m_rsb, m_dl_rss_from : (x_11).m_dl_rss_from,
                m_dl_rss_recv : (x_11).m_dl_rss_recv, m_dl_rss :
                (x_11).m_dl_rss}));
                x_13 = x_12;
            end else begin
                x_13 = x_10;
            end
            rqs_001 <= x_13;
        end else begin

        end
        return x_9;
    endmethod

    method ActionValue#(Struct50) getWait_001 ();
        let x_1 = (rqs_001);
        Struct49 x_2 = (((((x_1)[(Bit#(3))'(3'h0)]).m_status) ==
        ((Bit#(3))'(3'h2)) ? (Struct49 {valid : (Bool)'(True), data :
        (Bit#(3))'(3'h0)}) : (((((x_1)[(Bit#(3))'(3'h1)]).m_status) ==
        ((Bit#(3))'(3'h2)) ? (Struct49 {valid : (Bool)'(True), data :
        (Bit#(3))'(3'h1)}) : (((((x_1)[(Bit#(3))'(3'h2)]).m_status) ==
        ((Bit#(3))'(3'h2)) ? (Struct49 {valid : (Bool)'(True), data :
        (Bit#(3))'(3'h2)}) : (((((x_1)[(Bit#(3))'(3'h3)]).m_status) ==
        ((Bit#(3))'(3'h2)) ? (Struct49 {valid : (Bool)'(True), data :
        (Bit#(3))'(3'h3)}) : (((((x_1)[(Bit#(3))'(3'h4)]).m_status) ==
        ((Bit#(3))'(3'h2)) ? (Struct49 {valid : (Bool)'(True), data :
        (Bit#(3))'(3'h4)}) : (((((x_1)[(Bit#(3))'(3'h5)]).m_status) ==
        ((Bit#(3))'(3'h2)) ? (Struct49 {valid : (Bool)'(True), data :
        (Bit#(3))'(3'h5)}) : (Struct49 {valid : (Bool)'(False), data :
        unpack(0)})))))))))))));
        let x_6 = ?;
        if ((x_2).valid) begin
            Bit#(3) x_3 = ((x_2).data);
            Struct51 x_4 = ((x_1)[x_3]);
            rqs_001 <= update (x_1, x_3, Struct51 {m_status :
            (Bit#(3))'(3'h4), m_next : (x_4).m_next, m_is_ul : (x_4).m_is_ul,
            m_msg : (x_4).m_msg, m_qidx : (x_4).m_qidx, m_rsb : (x_4).m_rsb,
            m_dl_rss_from : (x_4).m_dl_rss_from, m_dl_rss_recv :
            (x_4).m_dl_rss_recv, m_dl_rss : (x_4).m_dl_rss});
            Struct39 x_5 = (Struct39 {r_id : x_3, r_msg : (x_4).m_msg,
            r_msg_from : (x_4).m_qidx});
            x_6 = Struct50 {valid : (Bool)'(True), data : x_5};
        end else begin
            x_6 = Struct50 {valid : (Bool)'(False), data : unpack(0)};
        end
        return x_6;
    endmethod

    method Action registerUL_001 (Struct53 x_0);
        let x_1 = (rqs_001);
        Bit#(3) x_2 = ((x_0).r_id);
        Struct51 x_3 = ((x_1)[x_2]);
        Struct51 x_4 = (Struct51 {m_status : (Bit#(3))'(3'h4), m_next :
        (x_3).m_next, m_is_ul : (Bool)'(True), m_msg : (x_3).m_msg, m_qidx :
        zeroExtend((x_0).r_ul_rsbTo), m_rsb : (x_0).r_ul_rsb, m_dl_rss_from :
        unpack(0), m_dl_rss_recv : unpack(0), m_dl_rss : unpack(0)});
        rqs_001 <= update (x_1, x_2, x_4);
    endmethod

    method Action registerDL_001 (Struct63 x_0);
        let x_1 = (rqs_001);
        Bit#(3) x_2 = ((x_0).r_id);
        Struct51 x_3 = ((x_1)[x_2]);
        Struct51 x_4 = (Struct51 {m_status : (Bit#(3))'(3'h4), m_next :
        (x_3).m_next, m_is_ul : (Bool)'(False), m_msg : (x_3).m_msg, m_qidx :
        (x_0).r_dl_rsbTo, m_rsb : (x_0).r_dl_rsb, m_dl_rss_from :
        (x_0).r_dl_rss_from, m_dl_rss_recv : unpack(0), m_dl_rss :
        unpack(0)});
        rqs_001 <= update (x_1, x_2, x_4);
    endmethod

    method ActionValue#(Bit#(3)) getULImm_001 (Struct1 x_0);
        let x_1 = (rqs_001);
        Struct49 x_2 = (((((x_1)[(Bit#(3))'(3'h2)]).m_status) ==
        ((Bit#(3))'(3'h0)) ? (Struct49 {valid : (Bool)'(True), data :
        (Bit#(3))'(3'h4)}) : (((((x_1)[(Bit#(3))'(3'h3)]).m_status) ==
        ((Bit#(3))'(3'h0)) ? (Struct49 {valid : (Bool)'(True), data :
        (Bit#(3))'(3'h5)}) : (((((x_1)[(Bit#(3))'(3'h4)]).m_status) ==
        ((Bit#(3))'(3'h0)) ? (Struct49 {valid : (Bool)'(True), data :
        (Bit#(3))'(3'h6)}) : (((((x_1)[(Bit#(3))'(3'h5)]).m_status) ==
        ((Bit#(3))'(3'h0)) ? (Struct49 {valid : (Bool)'(True), data :
        (Bit#(3))'(3'h7)}) : (Struct49 {valid : (Bool)'(False), data :
        unpack(0)})))))))));
        when ((x_2).valid, noAction);
        Bit#(3) x_3 = ((x_2).data);
        rqs_001 <= update (x_1, x_3, Struct51 {m_status : (Bit#(3))'(3'h4),
        m_next : Struct49 {valid : (Bool)'(False), data : unpack(0)}, m_is_ul
        : (Bool)'(True), m_msg : x_0, m_qidx : unpack(0), m_rsb :
        (Bool)'(False), m_dl_rss_from : unpack(0), m_dl_rss_recv : unpack(0),
        m_dl_rss : unpack(0)});
        return x_3;
    endmethod

    method Action transferUpDown_001 (Struct64 x_0);
        let x_1 = (rqs_001);
        Bit#(3) x_2 = ((x_0).r_id);
        Struct51 x_3 = ((x_1)[x_2]);
        Struct51 x_4 = (Struct51 {m_status : (Bit#(3))'(3'h4), m_next :
        (x_3).m_next, m_is_ul : (Bool)'(False), m_msg : (x_3).m_msg, m_qidx :
        (x_3).m_qidx, m_rsb : (x_3).m_rsb, m_dl_rss_from :
        (x_0).r_dl_rss_from, m_dl_rss_recv : unpack(0), m_dl_rss :
        unpack(0)});
        rqs_001 <= update (x_1, x_2, x_4);
    endmethod

    method ActionValue#(Bit#(3)) findUL_001 (Bit#(64) x_0);
        let x_1 = (rqs_001);
        Bit#(3) x_2 = (((((((x_1)[(Bit#(3))'(3'h2)]).m_status) ==
        ((Bit#(3))'(3'h4))) && (((x_1)[(Bit#(3))'(3'h2)]).m_is_ul)) &&
        (((((x_1)[(Bit#(3))'(3'h2)]).m_msg).addr) == (x_0)) ?
        ((Bit#(3))'(3'h2)) : (((((((x_1)[(Bit#(3))'(3'h3)]).m_status) ==
        ((Bit#(3))'(3'h4))) && (((x_1)[(Bit#(3))'(3'h3)]).m_is_ul)) &&
        (((((x_1)[(Bit#(3))'(3'h3)]).m_msg).addr) == (x_0)) ?
        ((Bit#(3))'(3'h3)) : (((((((x_1)[(Bit#(3))'(3'h4)]).m_status) ==
        ((Bit#(3))'(3'h4))) && (((x_1)[(Bit#(3))'(3'h4)]).m_is_ul)) &&
        (((((x_1)[(Bit#(3))'(3'h4)]).m_msg).addr) == (x_0)) ?
        ((Bit#(3))'(3'h4)) : (((((((x_1)[(Bit#(3))'(3'h5)]).m_status) ==
        ((Bit#(3))'(3'h4))) && (((x_1)[(Bit#(3))'(3'h5)]).m_is_ul)) &&
        (((((x_1)[(Bit#(3))'(3'h5)]).m_msg).addr) == (x_0)) ?
        ((Bit#(3))'(3'h5)) : (unpack(0))))))))));
        return x_2;
    endmethod

    method ActionValue#(Bit#(3)) findDL_001 (Bit#(64) x_0);
        let x_1 = (rqs_001);
        Bit#(3) x_2 = (((((((x_1)[(Bit#(3))'(3'h0)]).m_status) ==
        ((Bit#(3))'(3'h4))) && (! (((x_1)[(Bit#(3))'(3'h0)]).m_is_ul))) &&
        (((((x_1)[(Bit#(3))'(3'h0)]).m_msg).addr) == (x_0)) ?
        ((Bit#(3))'(3'h0)) : (((((((x_1)[(Bit#(3))'(3'h1)]).m_status) ==
        ((Bit#(3))'(3'h4))) && (! (((x_1)[(Bit#(3))'(3'h1)]).m_is_ul))) &&
        (((((x_1)[(Bit#(3))'(3'h1)]).m_msg).addr) == (x_0)) ?
        ((Bit#(3))'(3'h1)) : (((((((x_1)[(Bit#(3))'(3'h2)]).m_status) ==
        ((Bit#(3))'(3'h4))) && (! (((x_1)[(Bit#(3))'(3'h2)]).m_is_ul))) &&
        (((((x_1)[(Bit#(3))'(3'h2)]).m_msg).addr) == (x_0)) ?
        ((Bit#(3))'(3'h2)) : (((((((x_1)[(Bit#(3))'(3'h3)]).m_status) ==
        ((Bit#(3))'(3'h4))) && (! (((x_1)[(Bit#(3))'(3'h3)]).m_is_ul))) &&
        (((((x_1)[(Bit#(3))'(3'h3)]).m_msg).addr) == (x_0)) ?
        ((Bit#(3))'(3'h3)) : (((((((x_1)[(Bit#(3))'(3'h4)]).m_status) ==
        ((Bit#(3))'(3'h4))) && (! (((x_1)[(Bit#(3))'(3'h4)]).m_is_ul))) &&
        (((((x_1)[(Bit#(3))'(3'h4)]).m_msg).addr) == (x_0)) ?
        ((Bit#(3))'(3'h4)) : (((((((x_1)[(Bit#(3))'(3'h5)]).m_status) ==
        ((Bit#(3))'(3'h4))) && (! (((x_1)[(Bit#(3))'(3'h5)]).m_is_ul))) &&
        (((((x_1)[(Bit#(3))'(3'h5)]).m_msg).addr) == (x_0)) ?
        ((Bit#(3))'(3'h5)) : (unpack(0))))))))))))));
        return x_2;
    endmethod

    method Action releaseMSHR_001 (Bit#(3) x_0);
        let x_1 = (rqs_001);
        Struct51 x_2 = ((x_1)[x_0]);
        Vector#(6, Struct51) x_3 = (update (x_1, x_0,
        unpack(0)));
        let x_7 = ?;
        if (((x_2).m_next).valid) begin
            Bit#(3) x_4 = (((x_2).m_next).data);
            Struct51 x_5 = ((x_1)[x_4]);
            Vector#(6, Struct51) x_6 = (update (x_3, x_4, Struct51 {m_status
            : (Bit#(3))'(3'h2), m_next : (x_5).m_next, m_is_ul :
            (x_5).m_is_ul, m_msg : (x_5).m_msg, m_qidx : (x_5).m_qidx, m_rsb
            : (x_5).m_rsb, m_dl_rss_from : (x_5).m_dl_rss_from, m_dl_rss_recv
            : (x_5).m_dl_rss_recv, m_dl_rss : (x_5).m_dl_rss}));
            x_7 = x_6;
        end else begin
            x_7 = x_3;
        end
        rqs_001 <= x_7;
    endmethod

    method Action addRs_001 (Struct44 x_0);
        let x_1 = (rqs_001);
        Bit#(3) x_2 = ((x_0).r_id);
        Struct51 x_3 = ((x_1)[x_2]);
        Struct51 x_4 = (Struct51 {m_status : (x_3).m_status, m_next :
        (x_3).m_next, m_is_ul : (x_3).m_is_ul, m_msg : (x_3).m_msg, m_qidx :
        (x_3).m_qidx, m_rsb : (x_3).m_rsb, m_dl_rss_from :
        (x_3).m_dl_rss_from, m_dl_rss_recv : ((x_3).m_dl_rss_recv) |
        (((Bit#(2))'(2'h1)) << ((x_0).r_midx)), m_dl_rss : update
        ((x_3).m_dl_rss, (x_0).r_midx, (x_0).r_msg)});
        rqs_001 <= update (x_1, x_2, x_4);
    endmethod

    method ActionValue#(Struct43) getRsReady_001 ();
        let x_1 = (rqs_001);
        Struct49 x_2 = (((((((x_1)[(Bit#(3))'(3'h0)]).m_status) ==
        ((Bit#(3))'(3'h4))) && (! (((x_1)[(Bit#(3))'(3'h0)]).m_is_ul))) &&
        ((((x_1)[(Bit#(3))'(3'h0)]).m_dl_rss_from) ==
        (((x_1)[(Bit#(3))'(3'h0)]).m_dl_rss_recv)) ? (Struct49 {valid :
        (Bool)'(True), data : (Bit#(3))'(3'h0)}) :
        (((((((x_1)[(Bit#(3))'(3'h1)]).m_status) == ((Bit#(3))'(3'h4))) && (!
        (((x_1)[(Bit#(3))'(3'h1)]).m_is_ul))) &&
        ((((x_1)[(Bit#(3))'(3'h1)]).m_dl_rss_from) ==
        (((x_1)[(Bit#(3))'(3'h1)]).m_dl_rss_recv)) ? (Struct49 {valid :
        (Bool)'(True), data : (Bit#(3))'(3'h1)}) :
        (((((((x_1)[(Bit#(3))'(3'h2)]).m_status) == ((Bit#(3))'(3'h4))) && (!
        (((x_1)[(Bit#(3))'(3'h2)]).m_is_ul))) &&
        ((((x_1)[(Bit#(3))'(3'h2)]).m_dl_rss_from) ==
        (((x_1)[(Bit#(3))'(3'h2)]).m_dl_rss_recv)) ? (Struct49 {valid :
        (Bool)'(True), data : (Bit#(3))'(3'h2)}) :
        (((((((x_1)[(Bit#(3))'(3'h3)]).m_status) == ((Bit#(3))'(3'h4))) && (!
        (((x_1)[(Bit#(3))'(3'h3)]).m_is_ul))) &&
        ((((x_1)[(Bit#(3))'(3'h3)]).m_dl_rss_from) ==
        (((x_1)[(Bit#(3))'(3'h3)]).m_dl_rss_recv)) ? (Struct49 {valid :
        (Bool)'(True), data : (Bit#(3))'(3'h3)}) :
        (((((((x_1)[(Bit#(3))'(3'h4)]).m_status) == ((Bit#(3))'(3'h4))) && (!
        (((x_1)[(Bit#(3))'(3'h4)]).m_is_ul))) &&
        ((((x_1)[(Bit#(3))'(3'h4)]).m_dl_rss_from) ==
        (((x_1)[(Bit#(3))'(3'h4)]).m_dl_rss_recv)) ? (Struct49 {valid :
        (Bool)'(True), data : (Bit#(3))'(3'h4)}) :
        (((((((x_1)[(Bit#(3))'(3'h5)]).m_status) == ((Bit#(3))'(3'h4))) && (!
        (((x_1)[(Bit#(3))'(3'h5)]).m_is_ul))) &&
        ((((x_1)[(Bit#(3))'(3'h5)]).m_dl_rss_from) ==
        (((x_1)[(Bit#(3))'(3'h5)]).m_dl_rss_recv)) ? (Struct49 {valid :
        (Bool)'(True), data : (Bit#(3))'(3'h5)}) : (Struct49 {valid :
        (Bool)'(False), data : unpack(0)})))))))))))));
        when ((x_2).valid, noAction);
        Bit#(3) x_3 = ((x_2).data);
        Struct51 x_4 = ((x_1)[x_3]);
        Struct51 x_5 = (Struct51 {m_status : (Bit#(3))'(3'h5), m_next :
        (x_4).m_next, m_is_ul : (x_4).m_is_ul, m_msg : (x_4).m_msg, m_qidx :
        (x_4).m_qidx, m_rsb : (x_4).m_rsb, m_dl_rss_from :
        (x_4).m_dl_rss_from, m_dl_rss_recv : (x_4).m_dl_rss_recv, m_dl_rss :
        (x_4).m_dl_rss});
        rqs_001 <= update (x_1, x_3, x_5);
        Struct43 x_6 = (Struct43 {r_id : x_3, r_addr :
        ((x_4).m_msg).addr});
        return x_6;
    endmethod
endmodule

interface Module66;

endinterface

module mkModule66#(function Action enq_fifoPInput00(Struct2 _),
    function ActionValue#(Struct1) deq_fifo002())
    (Module66);

    rule parent_convert_00;
        $display ("Rule fired: parent_convert_00 at %t", $time);
        let x_0 <- deq_fifo002();
        Struct2 x_1 = (Struct2 {in_msg : x_0, in_msg_from :
        {((Bit#(2))'(2'h2)),((Bit#(1))'(1'h0))}});
        let x_2 <- enq_fifoPInput00(x_1);
    endrule

    // No methods in this module
endmodule

interface Module67;

endinterface

module mkModule67#(function ActionValue#(Struct1) deq_fifo0010(),
    function Action enq_fifoCRqInput_00(Struct3 _),
    function ActionValue#(Struct1) deq_fifo0000())
    (Module67);
    Reg#(Bit#(1)) rr_cRq2_00 <- mkReg(unpack(0));

    rule inc_rr_cRq2_00;
        let x_0 = (rr_cRq2_00);
        rr_cRq2_00 <= (x_0) + ((Bit#(1))'(1'h1));
    endrule

    rule accept0_cRq2_00;
        $display ("Rule fired: accept0_cRq2_00 at %t", $time);
        let x_0 = (rr_cRq2_00);
        when ((x_0) == ((Bit#(1))'(1'h0)), noAction);
        let x_1 <- deq_fifo0000();
        Struct3 x_2 = (Struct3 {ch_idx : (Bit#(1))'(1'h0), ch_msg : x_1});
        let x_3 <- enq_fifoCRqInput_00(x_2);
    endrule

    rule accept1_cRq2_00;
        $display ("Rule fired: accept1_cRq2_00 at %t", $time);
        let x_0 = (rr_cRq2_00);
        when ((x_0) == ((Bit#(1))'(1'h1)), noAction);
        let x_1 <- deq_fifo0010();
        Struct3 x_2 = (Struct3 {ch_idx : (Bit#(1))'(1'h1), ch_msg : x_1});
        let x_3 <- enq_fifoCRqInput_00(x_2);
    endrule

    // No methods in this module
endmodule

interface Module68;

endinterface

module mkModule68#(function ActionValue#(Struct1) deq_fifo0011(),
    function Action enq_fifoCRsInput_00(Struct3 _),
    function ActionValue#(Struct1) deq_fifo0001())
    (Module68);
    Reg#(Bit#(1)) rr_cRs2_00 <- mkReg(unpack(0));

    rule inc_rr_cRs2_00;
        let x_0 = (rr_cRs2_00);
        rr_cRs2_00 <= (x_0) + ((Bit#(1))'(1'h1));
    endrule

    rule accept0_cRs2_00;
        $display ("Rule fired: accept0_cRs2_00 at %t", $time);
        let x_0 = (rr_cRs2_00);
        when ((x_0) == ((Bit#(1))'(1'h0)), noAction);
        let x_1 <- deq_fifo0001();
        Struct3 x_2 = (Struct3 {ch_idx : (Bit#(1))'(1'h0), ch_msg : x_1});
        let x_3 <- enq_fifoCRsInput_00(x_2);
    endrule

    rule accept1_cRs2_00;
        $display ("Rule fired: accept1_cRs2_00 at %t", $time);
        let x_0 = (rr_cRs2_00);
        when ((x_0) == ((Bit#(1))'(1'h1)), noAction);
        let x_1 <- deq_fifo0011();
        Struct3 x_2 = (Struct3 {ch_idx : (Bit#(1))'(1'h1), ch_msg : x_1});
        let x_3 <- enq_fifoCRsInput_00(x_2);
    endrule

    // No methods in this module
endmodule

interface Module69;

endinterface

module mkModule69#(function ActionValue#(Struct3) deq_fifoCRsInput_00(),
    function Action enq_fifoCInput_00(Struct2 _),
    function ActionValue#(Struct3) deq_fifoCRqInput_00())
    (Module69);
    Reg#(Bit#(1)) rr_child_inputs_00 <- mkReg(unpack(0));

    rule inc_rr_child_inputs_00;
        let x_0 = (rr_child_inputs_00);
        rr_child_inputs_00 <= (x_0) + ((Bit#(1))'(1'h1));
    endrule

    rule accept0_child_inputs_00;
        $display ("Rule fired: accept0_child_inputs_00 at %t", $time);
        let x_0 = (rr_child_inputs_00);
        when ((x_0) == ((Bit#(1))'(1'h0)), noAction);
        let x_1 <- deq_fifoCRqInput_00();
        Struct2 x_2 = (Struct2 {in_msg : (x_1).ch_msg, in_msg_from :
        {((Bit#(2))'(2'h0)),((x_1).ch_idx)}});
        let x_3 <- enq_fifoCInput_00(x_2);
    endrule

    rule accept1_child_inputs_00;
        $display ("Rule fired: accept1_child_inputs_00 at %t", $time);
        let x_0 = (rr_child_inputs_00);
        when ((x_0) == ((Bit#(1))'(1'h1)), noAction);
        let x_1 <- deq_fifoCRsInput_00();
        Struct2 x_2 = (Struct2 {in_msg : (x_1).ch_msg, in_msg_from :
        {((Bit#(2))'(2'h1)),((x_1).ch_idx)}});
        let x_3 <- enq_fifoCInput_00(x_2);
    endrule

    // No methods in this module
endmodule

interface Module70;
    method Action makeEnq_parentChildren00 (Struct21 x_0);
    method Action broadcast_parentChildren00 (Struct24 x_0);
endinterface

module mkModule70#(function Action enq_fifo0002(Struct1 _),
    function Action enq_fifo0012(Struct1 _),
    function Action enq_fifo001(Struct1 _),
    function Action enq_fifo000(Struct1 _))
    (Module70);

    // No rules in this module

    method Action makeEnq_parentChildren00 (Struct21 x_0);
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

    method Action broadcast_parentChildren00 (Struct24 x_0);
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

interface Module71;
    method Action repGetRq__00 (Bit#(9) x_0);
    method ActionValue#(Vector#(8, Bit#(8))) repGetRs__00 ();
    method Action repAccess__00 (Struct34 x_0);
endinterface

module mkModule71#(function Action wrReq_repRam__00(Struct38 _),
    function ActionValue#(Vector#(8, Bit#(8))) rdResp_repRam__00(),
    function Action rdReq_repRam__00(Bit#(9) _))
    (Module71);

    // No rules in this module

    method Action repGetRq__00 (Bit#(9) x_0);
        let x_1 <- rdReq_repRam__00(x_0);
    endmethod

    method ActionValue#(Vector#(8, Bit#(8))) repGetRs__00 ();
        let x_1 <- rdResp_repRam__00();
        return x_1;
    endmethod

    method Action repAccess__00 (Struct34 x_0);
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
            (Bit#(8))'(8'hff)));
            x_20 = x_19;
        end
        Struct38 x_21 = (Struct38 {addr : (x_0).acc_index, datain :
        x_20});
        let x_22 <- wrReq_repRam__00(x_21);
    endmethod
endmodule

interface Module72;

endinterface

module mkModule72#(function Action enq_fifoPInput000(Struct2 _),
    function ActionValue#(Struct1) deq_fifo0002())
    (Module72);

    rule parent_convert_000;
        $display ("Rule fired: parent_convert_000 at %t", $time);
        let x_0 <- deq_fifo0002();
        Struct2 x_1 = (Struct2 {in_msg : x_0, in_msg_from :
        {((Bit#(2))'(2'h2)),((Bit#(1))'(1'h0))}});
        let x_2 <- enq_fifoPInput000(x_1);
    endrule

    // No methods in this module
endmodule

interface Module73;

endinterface

module mkModule73#(function Action enq_fifoCInput_000(Struct2 _),
    function ActionValue#(Struct1) deq_fifo00000())
    (Module73);

    rule child_convert_000;
        $display ("Rule fired: child_convert_000 at %t", $time);
        let x_0 <- deq_fifo00000();
        Struct2 x_1 = (Struct2 {in_msg : x_0, in_msg_from :
        {((Bit#(2))'(2'h0)),((Bit#(1))'(1'h0))}});
        let x_2 <- enq_fifoCInput_000(x_1);
    endrule

    // No methods in this module
endmodule

interface Module74;
    method Action makeEnq_parentChildren000 (Struct21 x_0);
endinterface

module mkModule74#(function Action enq_fifo00002(Struct1 _),
    function Action enq_fifo0001(Struct1 _),
    function Action enq_fifo0000(Struct1 _))
    (Module74);

    // No rules in this module

    method Action makeEnq_parentChildren000 (Struct21 x_0);
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

interface Module75;
    method Action repGetRq__000 (Bit#(8) x_0);
    method ActionValue#(Vector#(4, Bit#(8))) repGetRs__000 ();
    method Action repAccess__000 (Struct59 x_0);
endinterface

module mkModule75#(function Action wrReq_repRam__000(Struct62 _),
    function ActionValue#(Vector#(4, Bit#(8))) rdResp_repRam__000(),
    function Action rdReq_repRam__000(Bit#(8) _))
    (Module75);

    // No rules in this module

    method Action repGetRq__000 (Bit#(8) x_0);
        let x_1 <- rdReq_repRam__000(x_0);
    endmethod

    method ActionValue#(Vector#(4, Bit#(8))) repGetRs__000 ();
        let x_1 <- rdResp_repRam__000();
        return x_1;
    endmethod

    method Action repAccess__000 (Struct59 x_0);
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
            (Bit#(8))'(8'hff)));
            x_12 = x_11;
        end
        Struct62 x_13 = (Struct62 {addr : (x_0).acc_index, datain :
        x_12});
        let x_14 <- wrReq_repRam__000(x_13);
    endmethod
endmodule

interface Module76;

endinterface

module mkModule76#(function Action enq_fifoPInput001(Struct2 _),
    function ActionValue#(Struct1) deq_fifo0012())
    (Module76);

    rule parent_convert_001;
        $display ("Rule fired: parent_convert_001 at %t", $time);
        let x_0 <- deq_fifo0012();
        Struct2 x_1 = (Struct2 {in_msg : x_0, in_msg_from :
        {((Bit#(2))'(2'h2)),((Bit#(1))'(1'h1))}});
        let x_2 <- enq_fifoPInput001(x_1);
    endrule

    // No methods in this module
endmodule

interface Module77;

endinterface

module mkModule77#(function Action enq_fifoCInput_001(Struct2 _),
    function ActionValue#(Struct1) deq_fifo00100())
    (Module77);

    rule child_convert_001;
        $display ("Rule fired: child_convert_001 at %t", $time);
        let x_0 <- deq_fifo00100();
        Struct2 x_1 = (Struct2 {in_msg : x_0, in_msg_from :
        {((Bit#(2))'(2'h0)),((Bit#(1))'(1'h0))}});
        let x_2 <- enq_fifoCInput_001(x_1);
    endrule

    // No methods in this module
endmodule

interface Module78;
    method Action makeEnq_parentChildren001 (Struct21 x_0);
endinterface

module mkModule78#(function Action enq_fifo00102(Struct1 _),
    function Action enq_fifo0011(Struct1 _),
    function Action enq_fifo0010(Struct1 _))
    (Module78);

    // No rules in this module

    method Action makeEnq_parentChildren001 (Struct21 x_0);
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

interface Module79;
    method Action repGetRq__001 (Bit#(8) x_0);
    method ActionValue#(Vector#(4, Bit#(8))) repGetRs__001 ();
    method Action repAccess__001 (Struct59 x_0);
endinterface

module mkModule79#(function Action wrReq_repRam__001(Struct62 _),
    function ActionValue#(Vector#(4, Bit#(8))) rdResp_repRam__001(),
    function Action rdReq_repRam__001(Bit#(8) _))
    (Module79);

    // No rules in this module

    method Action repGetRq__001 (Bit#(8) x_0);
        let x_1 <- rdReq_repRam__001(x_0);
    endmethod

    method ActionValue#(Vector#(4, Bit#(8))) repGetRs__001 ();
        let x_1 <- rdResp_repRam__001();
        return x_1;
    endmethod

    method Action repAccess__001 (Struct59 x_0);
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
            (Bit#(8))'(8'hff)));
            x_12 = x_11;
        end
        Struct62 x_13 = (Struct62 {addr : (x_0).acc_index, datain :
        x_12});
        let x_14 <- wrReq_repRam__001(x_13);
    endmethod
endmodule

interface Module80;
    method Action cache__00__infoRq (Bit#(64) x_0);
    method ActionValue#(Struct10) cache__00__infoRsValueRq (Bit#(64) x_0);
    method ActionValue#(Vector#(4, Bit#(64))) cache__00__valueRsLineRq
    (Struct19 x_0);
endinterface

module mkModule80#(function Action wrReq_edirRam__00__3(Struct36 _),
    function Action wrReq_edirRam__00__2(Struct36 _),
    function Action wrReq_edirRam__00__1(Struct36 _),
    function Action wrReq_edirRam__00__0(Struct36 _),
    function Action wrReq_dataRam__00(Struct35 _),
    function Action repAccess__00(Struct34 _),
    function Action victims__00__registerVictim(Struct14 _),
    function Action wrReq_infoRam__00__7(Struct33 _),
    function Action wrReq_infoRam__00__6(Struct33 _),
    function Action wrReq_infoRam__00__5(Struct33 _),
    function Action wrReq_infoRam__00__4(Struct33 _),
    function Action wrReq_infoRam__00__3(Struct33 _),
    function Action wrReq_infoRam__00__2(Struct33 _),
    function Action wrReq_infoRam__00__1(Struct33 _),
    function Action wrReq_infoRam__00__0(Struct33 _),
    function ActionValue#(Vector#(4, Bit#(64))) rdResp_dataRam__00(),
    function Action rdReq_dataRam__00(Bit#(12) _),
    function ActionValue#(Vector#(8, Bit#(8))) repGetRs__00(),
    function ActionValue#(Struct30) rdResp_edirRam__00__3(),
    function ActionValue#(Struct30) rdResp_edirRam__00__2(),
    function ActionValue#(Struct30) rdResp_edirRam__00__1(),
    function ActionValue#(Struct30) rdResp_edirRam__00__0(),
    function ActionValue#(Struct28) rdResp_infoRam__00__7(),
    function ActionValue#(Struct28) rdResp_infoRam__00__6(),
    function ActionValue#(Struct28) rdResp_infoRam__00__5(),
    function ActionValue#(Struct28) rdResp_infoRam__00__4(),
    function ActionValue#(Struct28) rdResp_infoRam__00__3(),
    function ActionValue#(Struct28) rdResp_infoRam__00__2(),
    function ActionValue#(Struct28) rdResp_infoRam__00__1(),
    function ActionValue#(Struct28) rdResp_infoRam__00__0(),
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
    (Module80);

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

    method ActionValue#(Struct10) cache__00__infoRsValueRq (Bit#(64) x_0);
        Bit#(50) x_1 = ((x_0)[63:14]);
        Bit#(9) x_2 = ((x_0)[13:5]);
        Vector#(8, Struct28) x_3 = (unpack(0));
        let x_4 <- rdResp_infoRam__00__0();
        Vector#(8, Struct28) x_5 = (update (x_3, (Bit#(3))'(3'h0), x_4));
        let x_6 <- rdResp_infoRam__00__1();
        Vector#(8, Struct28) x_7 = (update (x_5, (Bit#(3))'(3'h1), x_6));
        let x_8 <- rdResp_infoRam__00__2();
        Vector#(8, Struct28) x_9 = (update (x_7, (Bit#(3))'(3'h2), x_8));
        let x_10 <- rdResp_infoRam__00__3();
        Vector#(8, Struct28) x_11 = (update (x_9, (Bit#(3))'(3'h3),
        x_10));
        let x_12 <- rdResp_infoRam__00__4();
        Vector#(8, Struct28) x_13 = (update (x_11, (Bit#(3))'(3'h4),
        x_12));
        let x_14 <- rdResp_infoRam__00__5();
        Vector#(8, Struct28) x_15 = (update (x_13, (Bit#(3))'(3'h5),
        x_14));
        let x_16 <- rdResp_infoRam__00__6();
        Vector#(8, Struct28) x_17 = (update (x_15, (Bit#(3))'(3'h6),
        x_16));
        let x_18 <- rdResp_infoRam__00__7();
        Vector#(8, Struct28) x_19 = (update (x_17, (Bit#(3))'(3'h7),
        x_18));
        Struct29 x_20 = (((((x_19)[(Bit#(3))'(3'h0)]).tag) == (x_1) ?
        (Struct29 {tm_hit : (Bool)'(True), tm_way : (Bit#(3))'(3'h0),
        tm_value : ((x_19)[(Bit#(3))'(3'h0)]).value}) :
        (((((x_19)[(Bit#(3))'(3'h1)]).tag) == (x_1) ? (Struct29 {tm_hit :
        (Bool)'(True), tm_way : (Bit#(3))'(3'h1), tm_value :
        ((x_19)[(Bit#(3))'(3'h1)]).value}) :
        (((((x_19)[(Bit#(3))'(3'h2)]).tag) == (x_1) ? (Struct29 {tm_hit :
        (Bool)'(True), tm_way : (Bit#(3))'(3'h2), tm_value :
        ((x_19)[(Bit#(3))'(3'h2)]).value}) :
        (((((x_19)[(Bit#(3))'(3'h3)]).tag) == (x_1) ? (Struct29 {tm_hit :
        (Bool)'(True), tm_way : (Bit#(3))'(3'h3), tm_value :
        ((x_19)[(Bit#(3))'(3'h3)]).value}) :
        (((((x_19)[(Bit#(3))'(3'h4)]).tag) == (x_1) ? (Struct29 {tm_hit :
        (Bool)'(True), tm_way : (Bit#(3))'(3'h4), tm_value :
        ((x_19)[(Bit#(3))'(3'h4)]).value}) :
        (((((x_19)[(Bit#(3))'(3'h5)]).tag) == (x_1) ? (Struct29 {tm_hit :
        (Bool)'(True), tm_way : (Bit#(3))'(3'h5), tm_value :
        ((x_19)[(Bit#(3))'(3'h5)]).value}) :
        (((((x_19)[(Bit#(3))'(3'h6)]).tag) == (x_1) ? (Struct29 {tm_hit :
        (Bool)'(True), tm_way : (Bit#(3))'(3'h6), tm_value :
        ((x_19)[(Bit#(3))'(3'h6)]).value}) :
        (((((x_19)[(Bit#(3))'(3'h7)]).tag) == (x_1) ? (Struct29 {tm_hit :
        (Bool)'(True), tm_way : (Bit#(3))'(3'h7), tm_value :
        ((x_19)[(Bit#(3))'(3'h7)]).value}) :
        (unpack(0))))))))))))))))));
        Vector#(4, Struct30) x_21 = (unpack(0));
        let x_22 <- rdResp_edirRam__00__0();
        Vector#(4, Struct30) x_23 = (update (x_21, (Bit#(2))'(2'h0),
        x_22));
        let x_24 <- rdResp_edirRam__00__1();
        Vector#(4, Struct30) x_25 = (update (x_23, (Bit#(2))'(2'h1),
        x_24));
        let x_26 <- rdResp_edirRam__00__2();
        Vector#(4, Struct30) x_27 = (update (x_25, (Bit#(2))'(2'h2),
        x_26));
        let x_28 <- rdResp_edirRam__00__3();
        Vector#(4, Struct30) x_29 = (update (x_27, (Bit#(2))'(2'h3),
        x_28));
        Struct32 x_30 = (((((x_29)[(Bit#(2))'(2'h0)]).tag) == (x_1) ?
        (Struct32 {tm_hit : (Bool)'(True), tm_way : (Bit#(2))'(2'h0),
        tm_value : ((x_29)[(Bit#(2))'(2'h0)]).value}) :
        (((((x_29)[(Bit#(2))'(2'h1)]).tag) == (x_1) ? (Struct32 {tm_hit :
        (Bool)'(True), tm_way : (Bit#(2))'(2'h1), tm_value :
        ((x_29)[(Bit#(2))'(2'h1)]).value}) :
        (((((x_29)[(Bit#(2))'(2'h2)]).tag) == (x_1) ? (Struct32 {tm_hit :
        (Bool)'(True), tm_way : (Bit#(2))'(2'h2), tm_value :
        ((x_29)[(Bit#(2))'(2'h2)]).value}) :
        (((((x_29)[(Bit#(2))'(2'h3)]).tag) == (x_1) ? (Struct32 {tm_hit :
        (Bool)'(True), tm_way : (Bit#(2))'(2'h3), tm_value :
        ((x_29)[(Bit#(2))'(2'h3)]).value}) : (unpack(0))))))))));
        Struct31 x_31 = ((x_30).tm_value);
        Struct6 x_32 = (((((((x_29)[(Bit#(2))'(2'h0)]).value).mesi_edir_st)
        == ((Bit#(3))'(3'h0))) ||
        (((((x_29)[(Bit#(2))'(2'h0)]).value).mesi_edir_st) ==
        ((Bit#(3))'(3'h1))) ? (Struct6 {valid : (Bool)'(True), data :
        (Bit#(2))'(2'h0)}) :
        (((((((x_29)[(Bit#(2))'(2'h1)]).value).mesi_edir_st) ==
        ((Bit#(3))'(3'h0))) ||
        (((((x_29)[(Bit#(2))'(2'h1)]).value).mesi_edir_st) ==
        ((Bit#(3))'(3'h1))) ? (Struct6 {valid : (Bool)'(True), data :
        (Bit#(2))'(2'h1)}) :
        (((((((x_29)[(Bit#(2))'(2'h2)]).value).mesi_edir_st) ==
        ((Bit#(3))'(3'h0))) ||
        (((((x_29)[(Bit#(2))'(2'h2)]).value).mesi_edir_st) ==
        ((Bit#(3))'(3'h1))) ? (Struct6 {valid : (Bool)'(True), data :
        (Bit#(2))'(2'h2)}) :
        (((((((x_29)[(Bit#(2))'(2'h3)]).value).mesi_edir_st) ==
        ((Bit#(3))'(3'h0))) ||
        (((((x_29)[(Bit#(2))'(2'h3)]).value).mesi_edir_st) ==
        ((Bit#(3))'(3'h1))) ? (Struct6 {valid : (Bool)'(True), data :
        (Bit#(2))'(2'h3)}) : (Struct6 {valid : (Bool)'(False), data :
        unpack(0)})))))))));
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
        Struct28 x_52 = ((x_19)[x_50]);
        Bit#(50) x_53 = ((x_52).tag);
        Struct11 x_54 = ((x_52).value);
        Struct10 x_55 = (Struct10 {info_index : x_2, info_hit :
        (x_20).tm_hit, info_way : (x_20).tm_way, edir_hit : (x_30).tm_hit,
        edir_way : (x_30).tm_way, edir_slot : x_32, info : ((x_20).tm_hit ?
        ((x_20).tm_value) : (Struct11 {mesi_owned : (Bool)'(False),
        mesi_status : (Bit#(3))'(3'h1), mesi_dir_st : (x_31).mesi_edir_st,
        mesi_dir_sharers : (x_31).mesi_edir_sharers})), may_victim : Struct12
        {mv_addr : {(x_53),({(x_2),((Bit#(5))'(5'h0))})}, mv_info : x_54},
        reps : x_33});
        let x_56 <- rdReq_dataRam__00({(((x_20).tm_hit ? ((x_20).tm_way) :
        (x_50))),(x_2)});
        return x_55;
    endmethod

    method ActionValue#(Vector#(4, Bit#(64))) cache__00__valueRsLineRq
    (Struct19 x_0);
        let x_1 <- rdResp_dataRam__00();
        Bit#(64) x_2 = ((x_0).addr);
        Bit#(9) x_3 = ((x_2)[13:5]);
        Bit#(3) x_4 = ((x_0).info_way);
        Struct11 x_5 = ((x_0).info);
        Bool x_6 = ((! ((x_5).mesi_owned)) && (((x_5).mesi_status) ==
        ((Bit#(3))'(3'h1))));
        Struct6 x_7 = ((x_0).edir_slot);
        Bool x_8 = ((x_7).valid);
        Bit#(2) x_9 =
        ((x_7).data);
        if ((x_0).info_write)
            begin
            if ((((x_0).info_hit) || (! (x_6))) || (((! ((x_0).edir_hit)) &&
                (x_6)) && (! (x_8)))) begin
                Struct33 x_10 = (Struct33 {addr : x_3, datain : Struct28 {tag
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
                    (x_27).mv_info, victim_value : x_1, victim_req : Struct15
                    {valid : (Bool)'(False), data : unpack(0)}});
                    let x_29 <- victims__00__registerVictim(x_28);
                end else begin

                end
                let x_31 <- repAccess__00(Struct34 {acc_type :
                ((((x_5).mesi_dir_st) == ((Bit#(3))'(3'h0))) ||
                (((x_5).mesi_dir_st) == ((Bit#(3))'(3'h1))) ?
                ((Bit#(1))'(1'h1)) : ((Bit#(1))'(1'h0))), acc_reps :
                (x_0).reps, acc_index : x_3, acc_way :
                x_4});
                if ((x_0).value_write) begin
                    Struct35 x_32 = (Struct35 {addr : {(x_4),((x_2)[13:5])},
                    datain : (x_0).value});
                    let x_33 <- wrReq_dataRam__00(x_32);
                end else begin

                end
            end else begin

            end
            if (((! ((x_0).info_hit)) && (x_6)) && (((x_0).edir_hit) ||
                (x_8))) begin
                Bit#(2) x_36 = (((x_0).edir_hit ? ((x_0).edir_way) :
                (x_9)));
                Struct36 x_37 = (Struct36 {addr : (x_2)[13:5], datain :
                Struct30 {tag : (x_2)[63:14], value : Struct31 {mesi_edir_st
                : (x_5).mesi_dir_st, mesi_edir_sharers :
                (x_5).mesi_dir_sharers}}});
                if ((x_36) == ((Bit#(2))'(2'h0))) begin
                    let x_38 <- wrReq_edirRam__00__0(x_37);
                end else begin

                end
                if ((x_36) == ((Bit#(2))'(2'h1))) begin
                    let x_40 <- wrReq_edirRam__00__1(x_37);
                end else begin

                end
                if ((x_36) == ((Bit#(2))'(2'h2))) begin
                    let x_42 <- wrReq_edirRam__00__2(x_37);
                end else begin

                end
                if ((x_36) == ((Bit#(2))'(2'h3))) begin
                    let x_44 <- wrReq_edirRam__00__3(x_37);
                end else begin

                end
            end else
                begin
                if ((x_0).edir_hit) begin
                    Bit#(2) x_46 = ((x_0).edir_way);
                    Struct36 x_47 = (Struct36 {addr : (x_2)[13:5], datain :
                    Struct30 {tag : (x_2)[63:14], value : Struct31
                    {mesi_edir_st : (x_5).mesi_dir_st, mesi_edir_sharers :
                    (x_5).mesi_dir_sharers}}});
                    if ((x_46) == ((Bit#(2))'(2'h0))) begin
                        let x_48 <- wrReq_edirRam__00__0(x_47);
                    end else begin

                    end
                    if ((x_46) == ((Bit#(2))'(2'h1))) begin
                        let x_50 <- wrReq_edirRam__00__1(x_47);
                    end else begin

                    end
                    if ((x_46) == ((Bit#(2))'(2'h2))) begin
                        let x_52 <- wrReq_edirRam__00__2(x_47);
                    end else begin

                    end
                    if ((x_46) == ((Bit#(2))'(2'h3))) begin
                        let x_54 <- wrReq_edirRam__00__3(x_47);
                    end else begin

                    end
                end else begin

                end
            end
        end else begin

        end
        return x_1;
    endmethod
endmodule

interface Module81;
    method Action cache__000__infoRq (Bit#(64) x_0);
    method ActionValue#(Struct45) cache__000__infoRsValueRq (Bit#(64) x_0);
    method ActionValue#(Vector#(4, Bit#(64))) cache__000__valueRsLineRq
    (Struct52 x_0);
endinterface

module mkModule81#(function Action wrReq_dataRam__000(Struct60 _),
    function Action repAccess__000(Struct59 _),
    function Action victims__000__registerVictim(Struct48 _),
    function Action wrReq_infoRam__000__3(Struct58 _),
    function Action wrReq_infoRam__000__2(Struct58 _),
    function Action wrReq_infoRam__000__1(Struct58 _),
    function Action wrReq_infoRam__000__0(Struct58 _),
    function ActionValue#(Vector#(4, Bit#(64))) rdResp_dataRam__000(),
    function Action rdReq_dataRam__000(Bit#(10) _),
    function ActionValue#(Vector#(4, Bit#(8))) repGetRs__000(),
    function ActionValue#(Struct56) rdResp_infoRam__000__3(),
    function ActionValue#(Struct56) rdResp_infoRam__000__2(),
    function ActionValue#(Struct56) rdResp_infoRam__000__1(),
    function ActionValue#(Struct56) rdResp_infoRam__000__0(),
    function Action repGetRq__000(Bit#(8) _),
    function Action rdReq_infoRam__000__3(Bit#(8) _),
    function Action rdReq_infoRam__000__2(Bit#(8) _),
    function Action rdReq_infoRam__000__1(Bit#(8) _),
    function Action rdReq_infoRam__000__0(Bit#(8) _))
    (Module81);

    // No rules in this module

    method Action cache__000__infoRq (Bit#(64) x_0);
        Bit#(8) x_1 = ((x_0)[12:5]);
        let x_2 <- rdReq_infoRam__000__0(x_1);
        let x_3 <- rdReq_infoRam__000__1(x_1);
        let x_4 <- rdReq_infoRam__000__2(x_1);
        let x_5 <- rdReq_infoRam__000__3(x_1);
        let x_6 <- repGetRq__000(x_1);
    endmethod

    method ActionValue#(Struct45) cache__000__infoRsValueRq (Bit#(64) x_0);
        Bit#(51) x_1 = ((x_0)[63:13]);
        Bit#(8) x_2 = ((x_0)[12:5]);
        Vector#(4, Struct56) x_3 = (unpack(0));
        let x_4 <- rdResp_infoRam__000__0();
        Vector#(4, Struct56) x_5 = (update (x_3, (Bit#(2))'(2'h0), x_4));
        let x_6 <- rdResp_infoRam__000__1();
        Vector#(4, Struct56) x_7 = (update (x_5, (Bit#(2))'(2'h1), x_6));
        let x_8 <- rdResp_infoRam__000__2();
        Vector#(4, Struct56) x_9 = (update (x_7, (Bit#(2))'(2'h2), x_8));
        let x_10 <- rdResp_infoRam__000__3();
        Vector#(4, Struct56) x_11 = (update (x_9, (Bit#(2))'(2'h3),
        x_10));
        Struct57 x_12 = (((((x_11)[(Bit#(2))'(2'h0)]).tag) == (x_1) ?
        (Struct57 {tm_hit : (Bool)'(True), tm_way : (Bit#(2))'(2'h0),
        tm_value : ((x_11)[(Bit#(2))'(2'h0)]).value}) :
        (((((x_11)[(Bit#(2))'(2'h1)]).tag) == (x_1) ? (Struct57 {tm_hit :
        (Bool)'(True), tm_way : (Bit#(2))'(2'h1), tm_value :
        ((x_11)[(Bit#(2))'(2'h1)]).value}) :
        (((((x_11)[(Bit#(2))'(2'h2)]).tag) == (x_1) ? (Struct57 {tm_hit :
        (Bool)'(True), tm_way : (Bit#(2))'(2'h2), tm_value :
        ((x_11)[(Bit#(2))'(2'h2)]).value}) :
        (((((x_11)[(Bit#(2))'(2'h3)]).tag) == (x_1) ? (Struct57 {tm_hit :
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
        Struct56 x_24 = ((x_11)[x_22]);
        Bit#(51) x_25 = ((x_24).tag);
        Struct11 x_26 = ((x_24).value);
        Struct45 x_27 = (Struct45 {info_index : x_2, info_hit :
        (x_12).tm_hit, info_way : (x_12).tm_way, edir_hit : unpack(0),
        edir_way : unpack(0), edir_slot : unpack(0), info : (x_12).tm_value,
        may_victim : Struct12 {mv_addr :
        {(x_25),({(x_2),((Bit#(5))'(5'h0))})}, mv_info : x_26}, reps :
        x_13});
        let x_28 <- rdReq_dataRam__000({(((x_12).tm_hit ? ((x_12).tm_way) :
        (x_22))),(x_2)});
        return x_27;
    endmethod

    method ActionValue#(Vector#(4, Bit#(64))) cache__000__valueRsLineRq
    (Struct52 x_0);
        let x_1 <- rdResp_dataRam__000();
        Bit#(64) x_2 = ((x_0).addr);
        Bit#(8) x_3 = ((x_2)[12:5]);
        Bit#(2) x_4 = ((x_0).info_way);
        Struct11 x_5 =
        ((x_0).info);
        if ((x_0).info_write) begin
            Struct58 x_6 = (Struct58 {addr : x_3, datain : Struct56 {tag :
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
                Struct48 x_16 = (Struct48 {victim_valid : (Bool)'(True),
                victim_addr : (x_15).mv_addr, victim_info : (x_15).mv_info,
                victim_value : x_1, victim_req : Struct49 {valid :
                (Bool)'(False), data : unpack(0)}});
                let x_17 <- victims__000__registerVictim(x_16);
            end else begin

            end
            let x_19 <- repAccess__000(Struct59 {acc_type :
            ((((x_5).mesi_dir_st) == ((Bit#(3))'(3'h0))) ||
            (((x_5).mesi_dir_st) == ((Bit#(3))'(3'h1))) ? ((Bit#(1))'(1'h1))
            : ((Bit#(1))'(1'h0))), acc_reps : (x_0).reps, acc_index : x_3,
            acc_way :
            x_4});
            if ((x_0).value_write) begin
                Struct60 x_20 = (Struct60 {addr : {(x_4),((x_2)[12:5])},
                datain : (x_0).value});
                let x_21 <- wrReq_dataRam__000(x_20);
            end else begin

            end
        end else begin

        end
        return x_1;
    endmethod
endmodule

interface Module82;
    method Action cache__001__infoRq (Bit#(64) x_0);
    method ActionValue#(Struct45) cache__001__infoRsValueRq (Bit#(64) x_0);
    method ActionValue#(Vector#(4, Bit#(64))) cache__001__valueRsLineRq
    (Struct52 x_0);
endinterface

module mkModule82#(function Action wrReq_dataRam__001(Struct60 _),
    function Action repAccess__001(Struct59 _),
    function Action victims__001__registerVictim(Struct48 _),
    function Action wrReq_infoRam__001__3(Struct58 _),
    function Action wrReq_infoRam__001__2(Struct58 _),
    function Action wrReq_infoRam__001__1(Struct58 _),
    function Action wrReq_infoRam__001__0(Struct58 _),
    function ActionValue#(Vector#(4, Bit#(64))) rdResp_dataRam__001(),
    function Action rdReq_dataRam__001(Bit#(10) _),
    function ActionValue#(Vector#(4, Bit#(8))) repGetRs__001(),
    function ActionValue#(Struct56) rdResp_infoRam__001__3(),
    function ActionValue#(Struct56) rdResp_infoRam__001__2(),
    function ActionValue#(Struct56) rdResp_infoRam__001__1(),
    function ActionValue#(Struct56) rdResp_infoRam__001__0(),
    function Action repGetRq__001(Bit#(8) _),
    function Action rdReq_infoRam__001__3(Bit#(8) _),
    function Action rdReq_infoRam__001__2(Bit#(8) _),
    function Action rdReq_infoRam__001__1(Bit#(8) _),
    function Action rdReq_infoRam__001__0(Bit#(8) _))
    (Module82);

    // No rules in this module

    method Action cache__001__infoRq (Bit#(64) x_0);
        Bit#(8) x_1 = ((x_0)[12:5]);
        let x_2 <- rdReq_infoRam__001__0(x_1);
        let x_3 <- rdReq_infoRam__001__1(x_1);
        let x_4 <- rdReq_infoRam__001__2(x_1);
        let x_5 <- rdReq_infoRam__001__3(x_1);
        let x_6 <- repGetRq__001(x_1);
    endmethod

    method ActionValue#(Struct45) cache__001__infoRsValueRq (Bit#(64) x_0);
        Bit#(51) x_1 = ((x_0)[63:13]);
        Bit#(8) x_2 = ((x_0)[12:5]);
        Vector#(4, Struct56) x_3 = (unpack(0));
        let x_4 <- rdResp_infoRam__001__0();
        Vector#(4, Struct56) x_5 = (update (x_3, (Bit#(2))'(2'h0), x_4));
        let x_6 <- rdResp_infoRam__001__1();
        Vector#(4, Struct56) x_7 = (update (x_5, (Bit#(2))'(2'h1), x_6));
        let x_8 <- rdResp_infoRam__001__2();
        Vector#(4, Struct56) x_9 = (update (x_7, (Bit#(2))'(2'h2), x_8));
        let x_10 <- rdResp_infoRam__001__3();
        Vector#(4, Struct56) x_11 = (update (x_9, (Bit#(2))'(2'h3),
        x_10));
        Struct57 x_12 = (((((x_11)[(Bit#(2))'(2'h0)]).tag) == (x_1) ?
        (Struct57 {tm_hit : (Bool)'(True), tm_way : (Bit#(2))'(2'h0),
        tm_value : ((x_11)[(Bit#(2))'(2'h0)]).value}) :
        (((((x_11)[(Bit#(2))'(2'h1)]).tag) == (x_1) ? (Struct57 {tm_hit :
        (Bool)'(True), tm_way : (Bit#(2))'(2'h1), tm_value :
        ((x_11)[(Bit#(2))'(2'h1)]).value}) :
        (((((x_11)[(Bit#(2))'(2'h2)]).tag) == (x_1) ? (Struct57 {tm_hit :
        (Bool)'(True), tm_way : (Bit#(2))'(2'h2), tm_value :
        ((x_11)[(Bit#(2))'(2'h2)]).value}) :
        (((((x_11)[(Bit#(2))'(2'h3)]).tag) == (x_1) ? (Struct57 {tm_hit :
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
        Struct56 x_24 = ((x_11)[x_22]);
        Bit#(51) x_25 = ((x_24).tag);
        Struct11 x_26 = ((x_24).value);
        Struct45 x_27 = (Struct45 {info_index : x_2, info_hit :
        (x_12).tm_hit, info_way : (x_12).tm_way, edir_hit : unpack(0),
        edir_way : unpack(0), edir_slot : unpack(0), info : (x_12).tm_value,
        may_victim : Struct12 {mv_addr :
        {(x_25),({(x_2),((Bit#(5))'(5'h0))})}, mv_info : x_26}, reps :
        x_13});
        let x_28 <- rdReq_dataRam__001({(((x_12).tm_hit ? ((x_12).tm_way) :
        (x_22))),(x_2)});
        return x_27;
    endmethod

    method ActionValue#(Vector#(4, Bit#(64))) cache__001__valueRsLineRq
    (Struct52 x_0);
        let x_1 <- rdResp_dataRam__001();
        Bit#(64) x_2 = ((x_0).addr);
        Bit#(8) x_3 = ((x_2)[12:5]);
        Bit#(2) x_4 = ((x_0).info_way);
        Struct11 x_5 =
        ((x_0).info);
        if ((x_0).info_write) begin
            Struct58 x_6 = (Struct58 {addr : x_3, datain : Struct56 {tag :
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
                Struct48 x_16 = (Struct48 {victim_valid : (Bool)'(True),
                victim_addr : (x_15).mv_addr, victim_info : (x_15).mv_info,
                victim_value : x_1, victim_req : Struct49 {valid :
                (Bool)'(False), data : unpack(0)}});
                let x_17 <- victims__001__registerVictim(x_16);
            end else begin

            end
            let x_19 <- repAccess__001(Struct59 {acc_type :
            ((((x_5).mesi_dir_st) == ((Bit#(3))'(3'h0))) ||
            (((x_5).mesi_dir_st) == ((Bit#(3))'(3'h1))) ? ((Bit#(1))'(1'h1))
            : ((Bit#(1))'(1'h0))), acc_reps : (x_0).reps, acc_index : x_3,
            acc_way :
            x_4});
            if ((x_0).value_write) begin
                Struct60 x_20 = (Struct60 {addr : {(x_4),((x_2)[12:5])},
                datain : (x_0).value});
                let x_21 <- wrReq_dataRam__001(x_20);
            end else begin

            end
        end else begin

        end
        return x_1;
    endmethod
endmodule

interface Module83;

endinterface

module mkModule83#(function Action victims__00__setVictimRq(Struct27 _),
    function ActionValue#(Bit#(4)) getULImm_00(Struct1 _),
    function ActionValue#(Struct14) victims__00__getFirstVictim(),
    function Action transferUpDown_00(Struct26 _),
    function Action broadcast_parentChildren00(Struct24 _),
    function Action registerDL_00(Struct23 _),
    function Action registerUL_00(Struct22 _),
    function Action makeEnq_parentChildren00(Struct21 _),
    function ActionValue#(Vector#(4, Bit#(64))) cache__00__valueRsLineRq(Struct19 _),
    function Action victims__00__setVictim(Struct20 _),
    function ActionValue#(Struct17) getMSHR_00(Bit#(4) _),
    function ActionValue#(Struct13) deq_fifoL2E_00(),
    function ActionValue#(Struct7) deq_fifoI2L_child_00(),
    function Action enq_fifoI2L_child_00(Struct7 _),
    function ActionValue#(Struct7) deq_fifoN2I_child_00(),
    function ActionValue#(Struct16) getWait_00(),
    function ActionValue#(Bit#(4)) findDL_00(Bit#(64) _),
    function Action enq_fifoN2I_child_00(Struct7 _),
    function ActionValue#(Struct5) getCRqSlot_00(Struct4 _),
    function ActionValue#(Struct2) deq_fifoCInput_00(),
    function ActionValue#(Struct14) victims__00__getVictim(Bit#(2) _),
    function Action enq_fifoL2E_00(Struct13 _),
    function ActionValue#(Struct10) cache__00__infoRsValueRq(Bit#(64) _),
    function ActionValue#(Struct7) deq_fifoI2L_parent_00(),
    function Action addRs_00(Struct9 _),
    function Action enq_fifoI2L_parent_00(Struct7 _),
    function Action cache__00__infoRq(Bit#(64) _),
    function ActionValue#(Struct7) deq_fifoN2I_parent_00(),
    function ActionValue#(Struct8) getRsReady_00(),
    function Action releaseMSHR_00(Bit#(4) _),
    function ActionValue#(Bit#(4)) victims__00__releaseVictim(Bit#(64) _),
    function ActionValue#(Bit#(4)) findUL_00(Bit#(64) _),
    function Action enq_fifoN2I_parent_00(Struct7 _),
    function ActionValue#(Struct6) victims__00findVictim(Bit#(64) _),
    function ActionValue#(Struct5) getPRqSlot_00(Struct4 _),
    function ActionValue#(Struct2) deq_fifoPInput00())
    (Module83);

    rule rule_in_prq_parent_00;
        $display ("Rule fired: rule_in_prq_parent_00 at %t", $time);
        let x_0 <- deq_fifoPInput00();
        Bit#(3) x_1 = ((x_0).in_msg_from);
        when ((x_1) == ({((Bit#(2))'(2'h2)),((Bit#(1))'(1'h0))}),
        noAction);
        Struct1 x_2 = ((x_0).in_msg);
        when (! ((x_2).type_), noAction);
        let x_3 <- getPRqSlot_00(Struct4 {r_id : unpack(0), r_msg : x_2,
        r_msg_from : (x_0).in_msg_from});
        when ((x_3).s_has_slot,
        noAction);
        if (! ((x_3).s_conflict)) begin
            let x_4 <- victims__00findVictim((x_2).addr);
            Struct7 x_5 = (Struct7 {ir_is_rs_rel : (Bool)'(False),
            ir_is_rs_acc : (Bool)'(False), ir_msg : (x_0).in_msg, ir_msg_from
            : x_1, ir_mshr_id : (x_3).s_id, ir_by_victim : x_4});
            let x_6 <- enq_fifoN2I_parent_00(x_5);
        end else begin

        end
    endrule

    rule rule_in_prs_parent_00;
        $display ("Rule fired: rule_in_prs_parent_00 at %t", $time);
        let x_0 <- deq_fifoPInput00();
        Bit#(3) x_1 = ((x_0).in_msg_from);
        when ((x_1) == ({((Bit#(2))'(2'h2)),((Bit#(1))'(1'h0))}),
        noAction);
        Struct1 x_2 = ((x_0).in_msg);
        when (((x_2).type_) && (! (((x_2).id) == ((Bit#(6))'(6'h16)))),
        noAction);
        let x_3 <- findUL_00((x_2).addr);
        let x_4 <- victims__00findVictim((x_2).addr);
        Struct7 x_5 = (Struct7 {ir_is_rs_rel : (Bool)'(False), ir_is_rs_acc :
        (Bool)'(False), ir_msg : (x_0).in_msg, ir_msg_from : x_1, ir_mshr_id
        : x_3, ir_by_victim : x_4});
        let x_6 <- enq_fifoN2I_parent_00(x_5);
    endrule

    rule rule_in_invrs_parent_00;
        $display ("Rule fired: rule_in_invrs_parent_00 at %t", $time);
        let x_0 <- deq_fifoPInput00();
        Bit#(3) x_1 = ((x_0).in_msg_from);
        when ((x_1) == ({((Bit#(2))'(2'h2)),((Bit#(1))'(1'h0))}),
        noAction);
        Struct1 x_2 = ((x_0).in_msg);
        when (((x_2).type_) && (((x_2).id) == ((Bit#(6))'(6'h16))),
        noAction);
        let x_3 <- victims__00__releaseVictim((x_2).addr);
        let x_4 <- releaseMSHR_00(x_3);
    endrule

    rule rule_in_rsrel_parent_00;
        $display ("Rule fired: rule_in_rsrel_parent_00 at %t", $time);
        let x_0 <- getRsReady_00();
        Struct1 x_1 = (Struct1 {id : unpack(0), type_ : unpack(0), addr :
        (x_0).r_addr, value : unpack(0)});
        Struct7 x_2 = (Struct7 {ir_is_rs_rel : (Bool)'(True), ir_is_rs_acc :
        (Bool)'(False), ir_msg : x_1, ir_msg_from : unpack(0), ir_mshr_id :
        (x_0).r_id, ir_by_victim : Struct6 {valid : (Bool)'(False), data :
        unpack(0)}});
        let x_3 <- enq_fifoN2I_parent_00(x_2);
    endrule

    rule rule_ir_cache_parent_00;
        $display ("Rule fired: rule_ir_cache_parent_00 at %t", $time);
        let x_0 <- deq_fifoN2I_parent_00();
        when (! ((x_0).ir_is_rs_acc), noAction);
        when (! (((x_0).ir_by_victim).valid), noAction);
        Struct1 x_1 = ((x_0).ir_msg);
        let x_2 <- cache__00__infoRq((x_1).addr);
        let x_3 <- enq_fifoI2L_parent_00(x_0);
    endrule

    rule rule_ir_victims_parent_00;
        $display ("Rule fired: rule_ir_victims_parent_00 at %t", $time);
        let x_0 <- deq_fifoN2I_parent_00();
        when (! ((x_0).ir_is_rs_acc), noAction);
        when (((x_0).ir_by_victim).valid, noAction);
        let x_1 <- enq_fifoI2L_parent_00(x_0);
    endrule

    rule rule_ir_rs_acc_parent_00;
        $display ("Rule fired: rule_ir_rs_acc_parent_00 at %t", $time);
        let x_0 <- deq_fifoN2I_parent_00();
        when ((x_0).ir_is_rs_acc, noAction);
        let x_1 <- addRs_00(Struct9 {r_id : (x_0).ir_mshr_id, r_midx :
        ((x_0).ir_msg_from)[0:0], r_msg : (x_0).ir_msg});
    endrule

    rule rule_lr_cache_parent_00;
        $display ("Rule fired: rule_lr_cache_parent_00 at %t", $time);
        let x_0 <- deq_fifoI2L_parent_00();
        when (! (((x_0).ir_by_victim).valid), noAction);
        let x_1 <- cache__00__infoRsValueRq(((x_0).ir_msg).addr);
        Struct13 x_2 = (Struct13 {lr_ir_pp : x_0, lr_ir : x_1, lr_value :
        unpack(0)});
        let x_3 <- enq_fifoL2E_00(x_2);
    endrule

    rule rule_lr_victims_parent_00;
        $display ("Rule fired: rule_lr_victims_parent_00 at %t", $time);
        let x_0 <- deq_fifoI2L_parent_00();
        when (((x_0).ir_by_victim).valid, noAction);
        let x_1 <- victims__00__getVictim((Bit#(2))'(2'h0));
        Struct10 x_2 = (Struct10 {info_index : unpack(0), info_hit :
        unpack(0), info_way : unpack(0), edir_hit : unpack(0), edir_way :
        unpack(0), edir_slot : unpack(0), info : (x_1).victim_info,
        may_victim : unpack(0), reps : unpack(0)});
        Struct13 x_3 = (Struct13 {lr_ir_pp : x_0, lr_ir : x_2, lr_value :
        (x_1).victim_value});
        let x_4 <- enq_fifoL2E_00(x_3);
    endrule

    rule rule_in_crq_child_00;
        $display ("Rule fired: rule_in_crq_child_00 at %t", $time);
        let x_0 <- deq_fifoCInput_00();
        Bit#(3) x_1 = ((x_0).in_msg_from);
        when (((x_1)[2:1]) == ((Bit#(2))'(2'h0)), noAction);
        Struct1 x_2 = ((x_0).in_msg);
        when (! ((x_2).type_), noAction);
        let x_3 <- getCRqSlot_00(Struct4 {r_id : unpack(0), r_msg : x_2,
        r_msg_from : x_1});
        when ((x_3).s_has_slot,
        noAction);
        if (! ((x_3).s_conflict)) begin
            let x_4 <- victims__00findVictim((x_2).addr);
            Struct7 x_5 = (Struct7 {ir_is_rs_rel : (Bool)'(False),
            ir_is_rs_acc : (Bool)'(False), ir_msg : (x_0).in_msg, ir_msg_from
            : x_1, ir_mshr_id : (x_3).s_id, ir_by_victim : x_4});
            let x_6 <- enq_fifoN2I_child_00(x_5);
        end else begin

        end
    endrule

    rule rule_in_crs_child_00;
        $display ("Rule fired: rule_in_crs_child_00 at %t", $time);
        let x_0 <- deq_fifoCInput_00();
        Bit#(3) x_1 = ((x_0).in_msg_from);
        when (((x_1)[2:1]) == ((Bit#(2))'(2'h1)), noAction);
        Struct1 x_2 = ((x_0).in_msg);
        when ((x_2).type_, noAction);
        let x_3 <- findDL_00((x_2).addr);
        let x_4 <- victims__00findVictim((x_2).addr);
        Struct7 x_5 = (Struct7 {ir_is_rs_rel : (Bool)'(False), ir_is_rs_acc :
        (Bool)'(True), ir_msg : x_2, ir_msg_from : x_1, ir_mshr_id : x_3,
        ir_by_victim : x_4});
        let x_6 <- enq_fifoN2I_child_00(x_5);
    endrule

    rule rule_in_retry_child_00;
        $display ("Rule fired: rule_in_retry_child_00 at %t", $time);
        let x_0 <- getWait_00();
        when ((x_0).valid, noAction);
        Struct4 x_1 = ((x_0).data);
        Struct1 x_2 = ((x_1).r_msg);
        let x_3 <- victims__00findVictim((x_2).addr);
        Struct7 x_4 = (Struct7 {ir_is_rs_rel : (Bool)'(False), ir_is_rs_acc :
        (Bool)'(False), ir_msg : x_2, ir_msg_from : (x_1).r_msg_from,
        ir_mshr_id : (x_1).r_id, ir_by_victim : x_3});
        let x_5 <- enq_fifoN2I_child_00(x_4);
    endrule

    rule rule_ir_cache_child_00;
        $display ("Rule fired: rule_ir_cache_child_00 at %t", $time);
        let x_0 <- deq_fifoN2I_child_00();
        when (! ((x_0).ir_is_rs_acc), noAction);
        when (! (((x_0).ir_by_victim).valid), noAction);
        Struct1 x_1 = ((x_0).ir_msg);
        let x_2 <- cache__00__infoRq((x_1).addr);
        let x_3 <- enq_fifoI2L_child_00(x_0);
    endrule

    rule rule_ir_victims_child_00;
        $display ("Rule fired: rule_ir_victims_child_00 at %t", $time);
        let x_0 <- deq_fifoN2I_child_00();
        when (! ((x_0).ir_is_rs_acc), noAction);
        when (((x_0).ir_by_victim).valid, noAction);
        let x_1 <- enq_fifoI2L_child_00(x_0);
    endrule

    rule rule_ir_rs_acc_child_00;
        $display ("Rule fired: rule_ir_rs_acc_child_00 at %t", $time);
        let x_0 <- deq_fifoN2I_child_00();
        when ((x_0).ir_is_rs_acc, noAction);
        let x_1 <- addRs_00(Struct9 {r_id : (x_0).ir_mshr_id, r_midx :
        ((x_0).ir_msg_from)[0:0], r_msg : (x_0).ir_msg});
    endrule

    rule rule_lr_cache_child_00;
        $display ("Rule fired: rule_lr_cache_child_00 at %t", $time);
        let x_0 <- deq_fifoI2L_child_00();
        when (! (((x_0).ir_by_victim).valid), noAction);
        let x_1 <- cache__00__infoRsValueRq(((x_0).ir_msg).addr);
        Struct13 x_2 = (Struct13 {lr_ir_pp : x_0, lr_ir : x_1, lr_value :
        unpack(0)});
        let x_3 <- enq_fifoL2E_00(x_2);
    endrule

    rule rule_lr_victims_child_00;
        $display ("Rule fired: rule_lr_victims_child_00 at %t", $time);
        let x_0 <- deq_fifoI2L_child_00();
        when (((x_0).ir_by_victim).valid, noAction);
        let x_1 <- victims__00__getVictim((Bit#(2))'(2'h0));
        Struct10 x_2 = (Struct10 {info_index : unpack(0), info_hit :
        unpack(0), info_way : unpack(0), edir_hit : unpack(0), edir_way :
        unpack(0), edir_slot : unpack(0), info : (x_1).victim_info,
        may_victim : unpack(0), reps : unpack(0)});
        Struct13 x_3 = (Struct13 {lr_ir_pp : x_0, lr_ir : x_2, lr_value :
        (x_1).victim_value});
        let x_4 <- enq_fifoL2E_00(x_3);
    endrule

    rule rule_exec_00_000000;
        $display ("Rule fired: rule_exec_00_000000 at %t", $time);
        let x_0 <- deq_fifoL2E_00();
        Struct7 x_1 = ((x_0).lr_ir_pp);
        Bit#(3) x_2 = ((x_1).ir_msg_from);
        Struct1 x_3 = ((x_1).ir_msg);
        Bit#(4) x_4 = ((x_1).ir_mshr_id);
        Bool x_5 = ((x_1).ir_is_rs_rel);
        when (! (x_5), noAction);
        Struct10 x_6 = ((x_0).lr_ir);
        Struct11 x_7 = ((x_6).info);
        Struct6 x_8 = ((x_1).ir_by_victim);
        Vector#(4, Bit#(64)) x_9 = ((x_0).lr_value);
        let x_10 <- getMSHR_00(x_4);
        Vector#(4, Bit#(64)) x_11 = (unpack(0));
        Bool x_12 = ((x_7).mesi_owned);
        Bit#(3) x_13 = ((x_7).mesi_status);
        Struct18 x_14 = (Struct18 {dir_st : (x_7).mesi_dir_st, dir_excl :
        ((((x_7).mesi_dir_sharers)[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(1))'(1'h0)) : (((Bit#(1))'(1'h1)) +
        ((((((x_7).mesi_dir_sharers)[1:1])[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(1))'(1'h0)) : (((Bit#(1))'(1'h1)) + (unpack(0))))))),
        dir_sharers : (x_7).mesi_dir_sharers});
        when ((x_2) == ((Bit#(3))'(3'h0)), noAction);
        when (((x_3).id) == ((Bit#(6))'(6'h2)), noAction);
        when (! ((x_3).type_), noAction);
        when ((! (((Bit#(3))'(3'h2)) < ((x_14).dir_st))) && ((x_13) ==
        ((Bit#(3))'(3'h2))), noAction);
        Struct1 x_15 = (x_3);
        Struct19 x_16 = (Struct19 {addr : (x_3).addr, info_write :
        (Bool)'(False), info_hit : (x_6).info_hit, info_way : (x_6).info_way,
        edir_hit : (x_6).edir_hit, edir_way : (x_6).edir_way, edir_slot :
        (x_6).edir_slot, info : (x_6).info, value_write : (Bool)'(False),
        value : unpack(0), may_victim : (x_6).may_victim, reps :
        (x_6).reps});
        Struct19 x_17 = (Struct19 {addr : (x_16).addr, info_write :
        (Bool)'(True), info_hit : (x_16).info_hit, info_way :
        (x_16).info_way, edir_hit : (x_16).edir_hit, edir_way :
        (x_16).edir_way, edir_slot : (x_16).edir_slot, info : Struct11
        {mesi_owned : ((x_16).info).mesi_owned, mesi_status :
        ((x_16).info).mesi_status, mesi_dir_st : (Struct18 {dir_st :
        (Bit#(3))'(3'h2), dir_excl : (x_14).dir_excl, dir_sharers :
        (((x_14).dir_st) == ((Bit#(3))'(3'h2)) ? (((x_14).dir_sharers) |
        (((Bit#(2))'(2'h1)) << ((Bit#(1))'(1'h0)))) : (((Bit#(2))'(2'h1)) <<
        ((Bit#(1))'(1'h0))))}).dir_st, mesi_dir_sharers : (((Struct18 {dir_st
        : (Bit#(3))'(3'h2), dir_excl : (x_14).dir_excl, dir_sharers :
        (((x_14).dir_st) == ((Bit#(3))'(3'h2)) ? (((x_14).dir_sharers) |
        (((Bit#(2))'(2'h1)) << ((Bit#(1))'(1'h0)))) : (((Bit#(2))'(2'h1)) <<
        ((Bit#(1))'(1'h0))))}).dir_st) == ((Bit#(3))'(3'h2)) ? ((Struct18
        {dir_st : (Bit#(3))'(3'h2), dir_excl : (x_14).dir_excl, dir_sharers :
        (((x_14).dir_st) == ((Bit#(3))'(3'h2)) ? (((x_14).dir_sharers) |
        (((Bit#(2))'(2'h1)) << ((Bit#(1))'(1'h0)))) : (((Bit#(2))'(2'h1)) <<
        ((Bit#(1))'(1'h0))))}).dir_sharers) : (((Bit#(2))'(2'h1)) <<
        ((Struct18 {dir_st : (Bit#(3))'(3'h2), dir_excl : (x_14).dir_excl,
        dir_sharers : (((x_14).dir_st) == ((Bit#(3))'(3'h2)) ?
        (((x_14).dir_sharers) | (((Bit#(2))'(2'h1)) << ((Bit#(1))'(1'h0)))) :
        (((Bit#(2))'(2'h1)) << ((Bit#(1))'(1'h0))))}).dir_excl)))},
        value_write : (x_16).value_write, value : (x_16).value, may_victim :
        (x_16).may_victim, reps :
        (x_16).reps});
        let x_20 = ?;
        if ((x_8).valid) begin
            let x_18 <- victims__00__setVictim(Struct20 {victim_idx :
            (x_8).data, victim_info : (x_17).info, victim_value :
            (x_17).value});
            x_20 = x_9;
        end else begin
            let x_19 <- cache__00__valueRsLineRq(x_17);
            x_20 = x_19;
        end
        Struct21 x_21 = (Struct21 {enq_type : ((((Bit#(3))'(3'h4))[2:1]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : (((((Bit#(3))'(3'h4))[2:1])
        == ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : ((Bit#(3))'(3'h4))[0:0], enq_msg : Struct1 {id :
        (Bit#(6))'(6'h3), type_ : (Bool)'(True), addr : (x_15).addr, value :
        x_20}});
        let x_22 <- makeEnq_parentChildren00(x_21);
    endrule

    rule rule_exec_00_001000;
        $display ("Rule fired: rule_exec_00_001000 at %t", $time);
        let x_0 <- deq_fifoL2E_00();
        Struct7 x_1 = ((x_0).lr_ir_pp);
        Bit#(3) x_2 = ((x_1).ir_msg_from);
        Struct1 x_3 = ((x_1).ir_msg);
        Bit#(4) x_4 = ((x_1).ir_mshr_id);
        Bool x_5 = ((x_1).ir_is_rs_rel);
        when (! (x_5), noAction);
        Struct10 x_6 = ((x_0).lr_ir);
        Struct11 x_7 = ((x_6).info);
        Struct6 x_8 = ((x_1).ir_by_victim);
        Vector#(4, Bit#(64)) x_9 = ((x_0).lr_value);
        let x_10 <- getMSHR_00(x_4);
        Vector#(4, Bit#(64)) x_11 = (unpack(0));
        Bool x_12 = ((x_7).mesi_owned);
        Bit#(3) x_13 = ((x_7).mesi_status);
        Struct18 x_14 = (Struct18 {dir_st : (x_7).mesi_dir_st, dir_excl :
        ((((x_7).mesi_dir_sharers)[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(1))'(1'h0)) : (((Bit#(1))'(1'h1)) +
        ((((((x_7).mesi_dir_sharers)[1:1])[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(1))'(1'h0)) : (((Bit#(1))'(1'h1)) + (unpack(0))))))),
        dir_sharers : (x_7).mesi_dir_sharers});
        when ((x_2) == ((Bit#(3))'(3'h0)), noAction);
        when (((x_3).id) == ((Bit#(6))'(6'h2)), noAction);
        when (! ((x_3).type_), noAction);
        when ((! ((x_13) < ((Bit#(3))'(3'h3)))) && (((x_14).dir_st) ==
        ((Bit#(3))'(3'h1))), noAction);
        Struct1 x_15 = (x_3);
        Struct19 x_16 = (Struct19 {addr : (x_3).addr, info_write :
        (Bool)'(False), info_hit : (x_6).info_hit, info_way : (x_6).info_way,
        edir_hit : (x_6).edir_hit, edir_way : (x_6).edir_way, edir_slot :
        (x_6).edir_slot, info : (x_6).info, value_write : (Bool)'(False),
        value : unpack(0), may_victim : (x_6).may_victim, reps :
        (x_6).reps});
        Struct19 x_17 = (Struct19 {addr : (x_16).addr, info_write :
        (Bool)'(True), info_hit : (x_16).info_hit, info_way :
        (x_16).info_way, edir_hit : (x_16).edir_hit, edir_way :
        (x_16).edir_way, edir_slot : (x_16).edir_slot, info : Struct11
        {mesi_owned : ((x_16).info).mesi_owned, mesi_status :
        ((x_16).info).mesi_status, mesi_dir_st : (Struct18 {dir_st :
        (Bit#(3))'(3'h3), dir_excl : (Bit#(1))'(1'h0), dir_sharers :
        unpack(0)}).dir_st, mesi_dir_sharers : (((Struct18 {dir_st :
        (Bit#(3))'(3'h3), dir_excl : (Bit#(1))'(1'h0), dir_sharers :
        unpack(0)}).dir_st) == ((Bit#(3))'(3'h2)) ? ((Struct18 {dir_st :
        (Bit#(3))'(3'h3), dir_excl : (Bit#(1))'(1'h0), dir_sharers :
        unpack(0)}).dir_sharers) : (((Bit#(2))'(2'h1)) << ((Struct18 {dir_st
        : (Bit#(3))'(3'h3), dir_excl : (Bit#(1))'(1'h0), dir_sharers :
        unpack(0)}).dir_excl)))}, value_write : (x_16).value_write, value :
        (x_16).value, may_victim : (x_16).may_victim, reps :
        (x_16).reps});
        Struct19 x_18 = (Struct19 {addr : (x_17).addr, info_write :
        (Bool)'(True), info_hit : (x_17).info_hit, info_way :
        (x_17).info_way, edir_hit : (x_17).edir_hit, edir_way :
        (x_17).edir_way, edir_slot : (x_17).edir_slot, info : Struct11
        {mesi_owned : ((x_17).info).mesi_owned, mesi_status :
        (Bit#(3))'(3'h1), mesi_dir_st : ((x_17).info).mesi_dir_st,
        mesi_dir_sharers : ((x_17).info).mesi_dir_sharers}, value_write :
        (x_17).value_write, value : (x_17).value, may_victim :
        (x_17).may_victim, reps :
        (x_17).reps});
        let x_21 = ?;
        if ((x_8).valid) begin
            let x_19 <- victims__00__setVictim(Struct20 {victim_idx :
            (x_8).data, victim_info : (x_18).info, victim_value :
            (x_18).value});
            x_21 = x_9;
        end else begin
            let x_20 <- cache__00__valueRsLineRq(x_18);
            x_21 = x_20;
        end
        Struct21 x_22 = (Struct21 {enq_type : ((((Bit#(3))'(3'h4))[2:1]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : (((((Bit#(3))'(3'h4))[2:1])
        == ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : ((Bit#(3))'(3'h4))[0:0], enq_msg : Struct1 {id :
        (Bit#(6))'(6'h4), type_ : (Bool)'(True), addr : (x_15).addr, value :
        x_21}});
        let x_23 <- makeEnq_parentChildren00(x_22);
    endrule

    rule rule_exec_00_01000;
        $display ("Rule fired: rule_exec_00_01000 at %t", $time);
        let x_0 <- deq_fifoL2E_00();
        Struct7 x_1 = ((x_0).lr_ir_pp);
        Bit#(3) x_2 = ((x_1).ir_msg_from);
        Struct1 x_3 = ((x_1).ir_msg);
        Bit#(4) x_4 = ((x_1).ir_mshr_id);
        Bool x_5 = ((x_1).ir_is_rs_rel);
        when (! (x_5), noAction);
        Struct10 x_6 = ((x_0).lr_ir);
        Struct11 x_7 = ((x_6).info);
        Struct6 x_8 = ((x_1).ir_by_victim);
        Vector#(4, Bit#(64)) x_9 = ((x_0).lr_value);
        let x_10 <- getMSHR_00(x_4);
        Vector#(4, Bit#(64)) x_11 = (unpack(0));
        Bool x_12 = ((x_7).mesi_owned);
        Bit#(3) x_13 = ((x_7).mesi_status);
        Struct18 x_14 = (Struct18 {dir_st : (x_7).mesi_dir_st, dir_excl :
        ((((x_7).mesi_dir_sharers)[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(1))'(1'h0)) : (((Bit#(1))'(1'h1)) +
        ((((((x_7).mesi_dir_sharers)[1:1])[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(1))'(1'h0)) : (((Bit#(1))'(1'h1)) + (unpack(0))))))),
        dir_sharers : (x_7).mesi_dir_sharers});
        when ((x_2) == ((Bit#(3))'(3'h0)), noAction);
        when (((x_3).id) == ((Bit#(6))'(6'h2)), noAction);
        when (! ((x_3).type_), noAction);
        when (((x_12) == ((Bool)'(False))) && ((! (((Bit#(3))'(3'h1)) <
        (x_13))) && (! (((Bit#(3))'(3'h2)) < ((x_14).dir_st)))),
        noAction);
        Struct1 x_15 = (x_3);
        Struct19 x_16 = (Struct19 {addr : (x_3).addr, info_write :
        (Bool)'(False), info_hit : (x_6).info_hit, info_way : (x_6).info_way,
        edir_hit : (x_6).edir_hit, edir_way : (x_6).edir_way, edir_slot :
        (x_6).edir_slot, info : (x_6).info, value_write : (Bool)'(False),
        value : unpack(0), may_victim : (x_6).may_victim, reps :
        (x_6).reps});
        let x_18 = ?;
        if ((x_8).valid) begin
            x_18 = x_9;
        end else begin
            let x_17 <- cache__00__valueRsLineRq(unpack(0));
            x_18 = x_17;
        end
        let x_19 <- registerUL_00(Struct22 {r_id : x_4, r_ul_rsb :
        (Bool)'(True), r_ul_rsbTo : ((Bit#(3))'(3'h4))[0:0]});
        Struct21 x_20 = (Struct21 {enq_type : ((((Bit#(3))'(3'h0))[2:1]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : (((((Bit#(3))'(3'h0))[2:1])
        == ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : ((Bit#(3))'(3'h0))[0:0], enq_msg : Struct1 {id :
        (Bit#(6))'(6'h2), type_ : (Bool)'(False), addr : (x_15).addr, value :
        unpack(0)}});
        let x_21 <- makeEnq_parentChildren00(x_20);
    endrule

    rule rule_exec_00_03000;
        $display ("Rule fired: rule_exec_00_03000 at %t", $time);
        let x_0 <- deq_fifoL2E_00();
        Struct7 x_1 = ((x_0).lr_ir_pp);
        Bit#(3) x_2 = ((x_1).ir_msg_from);
        Struct1 x_3 = ((x_1).ir_msg);
        Bit#(4) x_4 = ((x_1).ir_mshr_id);
        Bool x_5 = ((x_1).ir_is_rs_rel);
        when (! (x_5), noAction);
        Struct10 x_6 = ((x_0).lr_ir);
        Struct11 x_7 = ((x_6).info);
        Struct6 x_8 = ((x_1).ir_by_victim);
        Vector#(4, Bit#(64)) x_9 = ((x_0).lr_value);
        let x_10 <- getMSHR_00(x_4);
        Vector#(4, Bit#(64)) x_11 = (unpack(0));
        Bool x_12 = ((x_7).mesi_owned);
        Bit#(3) x_13 = ((x_7).mesi_status);
        Struct18 x_14 = (Struct18 {dir_st : (x_7).mesi_dir_st, dir_excl :
        ((((x_7).mesi_dir_sharers)[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(1))'(1'h0)) : (((Bit#(1))'(1'h1)) +
        ((((((x_7).mesi_dir_sharers)[1:1])[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(1))'(1'h0)) : (((Bit#(1))'(1'h1)) + (unpack(0))))))),
        dir_sharers : (x_7).mesi_dir_sharers});
        when ((x_2) == ((Bit#(3))'(3'h0)), noAction);
        when (((x_3).id) == ((Bit#(6))'(6'h2)), noAction);
        when (! ((x_3).type_), noAction);
        when (((Bool)'(True)) && (((Bool)'(True)) && ((! (((Bit#(3))'(3'h1))
        < (x_13))) && ((! (((x_14).dir_st) < ((Bit#(3))'(3'h3)))) && (!
        (((Bit#(3))'(3'h4)) < ((x_14).dir_st)))))), noAction);
        Struct1 x_15 = (x_3);
        Struct19 x_16 = (Struct19 {addr : (x_3).addr, info_write :
        (Bool)'(False), info_hit : (x_6).info_hit, info_way : (x_6).info_way,
        edir_hit : (x_6).edir_hit, edir_way : (x_6).edir_way, edir_slot :
        (x_6).edir_slot, info : (x_6).info, value_write : (Bool)'(False),
        value : unpack(0), may_victim : (x_6).may_victim, reps :
        (x_6).reps});
        let x_18 = ?;
        if ((x_8).valid) begin
            x_18 = x_9;
        end else begin
            let x_17 <- cache__00__valueRsLineRq(unpack(0));
            x_18 = x_17;
        end
        let x_19 <- registerDL_00(Struct23 {r_id : x_4, r_dl_rss_from :
        (unpack(0)) | (((Bit#(2))'(2'h1)) <<
        (({((Bit#(2))'(2'h1)),((x_14).dir_excl)})[0:0])), r_dl_rsb :
        (Bool)'(True), r_dl_rsbTo : (Bit#(3))'(3'h4)});
        Struct21 x_20 = (Struct21 {enq_type :
        ((({((Bit#(2))'(2'h2)),((x_14).dir_excl)})[2:1]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) :
        (((({((Bit#(2))'(2'h2)),((x_14).dir_excl)})[2:1]) ==
        ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : ({((Bit#(2))'(2'h2)),((x_14).dir_excl)})[0:0], enq_msg :
        Struct1 {id : (Bit#(6))'(6'h5), type_ : (Bool)'(False), addr :
        (x_15).addr, value : unpack(0)}});
        let x_21 <- makeEnq_parentChildren00(x_20);
    endrule

    rule rule_exec_00_10000;
        $display ("Rule fired: rule_exec_00_10000 at %t", $time);
        let x_0 <- deq_fifoL2E_00();
        Struct7 x_1 = ((x_0).lr_ir_pp);
        Bit#(3) x_2 = ((x_1).ir_msg_from);
        Struct1 x_3 = ((x_1).ir_msg);
        Bit#(4) x_4 = ((x_1).ir_mshr_id);
        Bool x_5 = ((x_1).ir_is_rs_rel);
        when (! (x_5), noAction);
        Struct10 x_6 = ((x_0).lr_ir);
        Struct11 x_7 = ((x_6).info);
        Struct6 x_8 = ((x_1).ir_by_victim);
        Vector#(4, Bit#(64)) x_9 = ((x_0).lr_value);
        let x_10 <- getMSHR_00(x_4);
        Vector#(4, Bit#(64)) x_11 = (unpack(0));
        Bool x_12 = ((x_7).mesi_owned);
        Bit#(3) x_13 = ((x_7).mesi_status);
        Struct18 x_14 = (Struct18 {dir_st : (x_7).mesi_dir_st, dir_excl :
        ((((x_7).mesi_dir_sharers)[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(1))'(1'h0)) : (((Bit#(1))'(1'h1)) +
        ((((((x_7).mesi_dir_sharers)[1:1])[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(1))'(1'h0)) : (((Bit#(1))'(1'h1)) + (unpack(0))))))),
        dir_sharers : (x_7).mesi_dir_sharers});
        when ((x_2) == ((Bit#(3))'(3'h0)), noAction);
        when (((x_3).id) == ((Bit#(6))'(6'ha)), noAction);
        when (! ((x_3).type_), noAction);
        when ((! ((x_13) < ((Bit#(3))'(3'h3)))) || (((x_13) ==
        ((Bit#(3))'(3'h2))) && (((x_12) == ((Bool)'(True))) &&
        ((((x_14).dir_st) == ((Bit#(3))'(3'h2))) && (((x_14).dir_sharers) ==
        (((Bit#(2))'(2'h1)) << ((Bit#(1))'(1'h0))))))), noAction);
        Struct1 x_15 = (x_3);
        Struct19 x_16 = (Struct19 {addr : (x_3).addr, info_write :
        (Bool)'(False), info_hit : (x_6).info_hit, info_way : (x_6).info_way,
        edir_hit : (x_6).edir_hit, edir_way : (x_6).edir_way, edir_slot :
        (x_6).edir_slot, info : (x_6).info, value_write : (Bool)'(False),
        value : unpack(0), may_victim : (x_6).may_victim, reps :
        (x_6).reps});
        Struct19 x_17 = (Struct19 {addr : (x_16).addr, info_write :
        (Bool)'(True), info_hit : (x_16).info_hit, info_way :
        (x_16).info_way, edir_hit : (x_16).edir_hit, edir_way :
        (x_16).edir_way, edir_slot : (x_16).edir_slot, info : Struct11
        {mesi_owned : ((x_16).info).mesi_owned, mesi_status :
        ((x_16).info).mesi_status, mesi_dir_st : (Struct18 {dir_st :
        (Bit#(3))'(3'h4), dir_excl : (Bit#(1))'(1'h0), dir_sharers :
        unpack(0)}).dir_st, mesi_dir_sharers : (((Struct18 {dir_st :
        (Bit#(3))'(3'h4), dir_excl : (Bit#(1))'(1'h0), dir_sharers :
        unpack(0)}).dir_st) == ((Bit#(3))'(3'h2)) ? ((Struct18 {dir_st :
        (Bit#(3))'(3'h4), dir_excl : (Bit#(1))'(1'h0), dir_sharers :
        unpack(0)}).dir_sharers) : (((Bit#(2))'(2'h1)) << ((Struct18 {dir_st
        : (Bit#(3))'(3'h4), dir_excl : (Bit#(1))'(1'h0), dir_sharers :
        unpack(0)}).dir_excl)))}, value_write : (x_16).value_write, value :
        (x_16).value, may_victim : (x_16).may_victim, reps :
        (x_16).reps});
        Struct19 x_18 = (Struct19 {addr : (x_17).addr, info_write :
        (Bool)'(True), info_hit : (x_17).info_hit, info_way :
        (x_17).info_way, edir_hit : (x_17).edir_hit, edir_way :
        (x_17).edir_way, edir_slot : (x_17).edir_slot, info : Struct11
        {mesi_owned : ((x_17).info).mesi_owned, mesi_status :
        (Bit#(3))'(3'h1), mesi_dir_st : ((x_17).info).mesi_dir_st,
        mesi_dir_sharers : ((x_17).info).mesi_dir_sharers}, value_write :
        (x_17).value_write, value : (x_17).value, may_victim :
        (x_17).may_victim, reps : (x_17).reps});
        Struct19 x_19 = (Struct19 {addr : (x_18).addr, info_write :
        (Bool)'(True), info_hit : (x_18).info_hit, info_way :
        (x_18).info_way, edir_hit : (x_18).edir_hit, edir_way :
        (x_18).edir_way, edir_slot : (x_18).edir_slot, info : Struct11
        {mesi_owned : (Bool)'(False), mesi_status :
        ((x_18).info).mesi_status, mesi_dir_st : ((x_18).info).mesi_dir_st,
        mesi_dir_sharers : ((x_18).info).mesi_dir_sharers}, value_write :
        (x_18).value_write, value : (x_18).value, may_victim :
        (x_18).may_victim, reps :
        (x_18).reps});
        let x_22 = ?;
        if ((x_8).valid) begin
            let x_20 <- victims__00__setVictim(Struct20 {victim_idx :
            (x_8).data, victim_info : (x_19).info, victim_value :
            (x_19).value});
            x_22 = x_9;
        end else begin
            let x_21 <- cache__00__valueRsLineRq(x_19);
            x_22 = x_21;
        end
        Struct21 x_23 = (Struct21 {enq_type : ((((Bit#(3))'(3'h4))[2:1]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : (((((Bit#(3))'(3'h4))[2:1])
        == ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : ((Bit#(3))'(3'h4))[0:0], enq_msg : Struct1 {id :
        (Bit#(6))'(6'hb), type_ : (Bool)'(True), addr : (x_15).addr, value :
        unpack(0)}});
        let x_24 <- makeEnq_parentChildren00(x_23);
    endrule

    rule rule_exec_00_11000;
        $display ("Rule fired: rule_exec_00_11000 at %t", $time);
        let x_0 <- deq_fifoL2E_00();
        Struct7 x_1 = ((x_0).lr_ir_pp);
        Bit#(3) x_2 = ((x_1).ir_msg_from);
        Struct1 x_3 = ((x_1).ir_msg);
        Bit#(4) x_4 = ((x_1).ir_mshr_id);
        Bool x_5 = ((x_1).ir_is_rs_rel);
        when (! (x_5), noAction);
        Struct10 x_6 = ((x_0).lr_ir);
        Struct11 x_7 = ((x_6).info);
        Struct6 x_8 = ((x_1).ir_by_victim);
        Vector#(4, Bit#(64)) x_9 = ((x_0).lr_value);
        let x_10 <- getMSHR_00(x_4);
        Vector#(4, Bit#(64)) x_11 = (unpack(0));
        Bool x_12 = ((x_7).mesi_owned);
        Bit#(3) x_13 = ((x_7).mesi_status);
        Struct18 x_14 = (Struct18 {dir_st : (x_7).mesi_dir_st, dir_excl :
        ((((x_7).mesi_dir_sharers)[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(1))'(1'h0)) : (((Bit#(1))'(1'h1)) +
        ((((((x_7).mesi_dir_sharers)[1:1])[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(1))'(1'h0)) : (((Bit#(1))'(1'h1)) + (unpack(0))))))),
        dir_sharers : (x_7).mesi_dir_sharers});
        when ((x_2) == ((Bit#(3))'(3'h0)), noAction);
        when (((x_3).id) == ((Bit#(6))'(6'ha)), noAction);
        when (! ((x_3).type_), noAction);
        when (((x_12) == ((Bool)'(False))) && ((! (((Bit#(3))'(3'h2)) <
        (x_13))) && (! (((Bit#(3))'(3'h2)) < ((x_14).dir_st)))),
        noAction);
        Struct1 x_15 = (x_3);
        Struct19 x_16 = (Struct19 {addr : (x_3).addr, info_write :
        (Bool)'(False), info_hit : (x_6).info_hit, info_way : (x_6).info_way,
        edir_hit : (x_6).edir_hit, edir_way : (x_6).edir_way, edir_slot :
        (x_6).edir_slot, info : (x_6).info, value_write : (Bool)'(False),
        value : unpack(0), may_victim : (x_6).may_victim, reps :
        (x_6).reps});
        let x_18 = ?;
        if ((x_8).valid) begin
            x_18 = x_9;
        end else begin
            let x_17 <- cache__00__valueRsLineRq(unpack(0));
            x_18 = x_17;
        end
        let x_19 <- registerUL_00(Struct22 {r_id : x_4, r_ul_rsb :
        (Bool)'(True), r_ul_rsbTo : ((Bit#(3))'(3'h4))[0:0]});
        Struct21 x_20 = (Struct21 {enq_type : ((((Bit#(3))'(3'h0))[2:1]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : (((((Bit#(3))'(3'h0))[2:1])
        == ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : ((Bit#(3))'(3'h0))[0:0], enq_msg : Struct1 {id :
        (Bit#(6))'(6'ha), type_ : (Bool)'(False), addr : (x_15).addr, value :
        unpack(0)}});
        let x_21 <- makeEnq_parentChildren00(x_20);
    endrule

    rule rule_exec_00_14000;
        $display ("Rule fired: rule_exec_00_14000 at %t", $time);
        let x_0 <- deq_fifoL2E_00();
        Struct7 x_1 = ((x_0).lr_ir_pp);
        Bit#(3) x_2 = ((x_1).ir_msg_from);
        Struct1 x_3 = ((x_1).ir_msg);
        Bit#(4) x_4 = ((x_1).ir_mshr_id);
        Bool x_5 = ((x_1).ir_is_rs_rel);
        when (! (x_5), noAction);
        Struct10 x_6 = ((x_0).lr_ir);
        Struct11 x_7 = ((x_6).info);
        Struct6 x_8 = ((x_1).ir_by_victim);
        Vector#(4, Bit#(64)) x_9 = ((x_0).lr_value);
        let x_10 <- getMSHR_00(x_4);
        Vector#(4, Bit#(64)) x_11 = (unpack(0));
        Bool x_12 = ((x_7).mesi_owned);
        Bit#(3) x_13 = ((x_7).mesi_status);
        Struct18 x_14 = (Struct18 {dir_st : (x_7).mesi_dir_st, dir_excl :
        ((((x_7).mesi_dir_sharers)[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(1))'(1'h0)) : (((Bit#(1))'(1'h1)) +
        ((((((x_7).mesi_dir_sharers)[1:1])[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(1))'(1'h0)) : (((Bit#(1))'(1'h1)) + (unpack(0))))))),
        dir_sharers : (x_7).mesi_dir_sharers});
        when ((x_2) == ((Bit#(3))'(3'h0)), noAction);
        when (((x_3).id) == ((Bit#(6))'(6'ha)), noAction);
        when (! ((x_3).type_), noAction);
        when (((Bool)'(True)) && (((Bool)'(True)) && ((! (((Bit#(3))'(3'h1))
        < (x_13))) && ((! (((x_14).dir_st) < ((Bit#(3))'(3'h3)))) && (!
        (((Bit#(3))'(3'h4)) < ((x_14).dir_st)))))), noAction);
        Struct1 x_15 = (x_3);
        Struct19 x_16 = (Struct19 {addr : (x_3).addr, info_write :
        (Bool)'(False), info_hit : (x_6).info_hit, info_way : (x_6).info_way,
        edir_hit : (x_6).edir_hit, edir_way : (x_6).edir_way, edir_slot :
        (x_6).edir_slot, info : (x_6).info, value_write : (Bool)'(False),
        value : unpack(0), may_victim : (x_6).may_victim, reps :
        (x_6).reps});
        let x_18 = ?;
        if ((x_8).valid) begin
            x_18 = x_9;
        end else begin
            let x_17 <- cache__00__valueRsLineRq(unpack(0));
            x_18 = x_17;
        end
        let x_19 <- registerDL_00(Struct23 {r_id : x_4, r_dl_rss_from :
        (unpack(0)) | (((Bit#(2))'(2'h1)) <<
        (({((Bit#(2))'(2'h1)),((x_14).dir_excl)})[0:0])), r_dl_rsb :
        (Bool)'(True), r_dl_rsbTo : (Bit#(3))'(3'h4)});
        Struct21 x_20 = (Struct21 {enq_type :
        ((({((Bit#(2))'(2'h2)),((x_14).dir_excl)})[2:1]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) :
        (((({((Bit#(2))'(2'h2)),((x_14).dir_excl)})[2:1]) ==
        ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : ({((Bit#(2))'(2'h2)),((x_14).dir_excl)})[0:0], enq_msg :
        Struct1 {id : (Bit#(6))'(6'he), type_ : (Bool)'(False), addr :
        (x_15).addr, value : unpack(0)}});
        let x_21 <- makeEnq_parentChildren00(x_20);
    endrule

    rule rule_exec_00_15000;
        $display ("Rule fired: rule_exec_00_15000 at %t", $time);
        let x_0 <- deq_fifoL2E_00();
        Struct7 x_1 = ((x_0).lr_ir_pp);
        Bit#(3) x_2 = ((x_1).ir_msg_from);
        Struct1 x_3 = ((x_1).ir_msg);
        Bit#(4) x_4 = ((x_1).ir_mshr_id);
        Bool x_5 = ((x_1).ir_is_rs_rel);
        when (! (x_5), noAction);
        Struct10 x_6 = ((x_0).lr_ir);
        Struct11 x_7 = ((x_6).info);
        Struct6 x_8 = ((x_1).ir_by_victim);
        Vector#(4, Bit#(64)) x_9 = ((x_0).lr_value);
        let x_10 <- getMSHR_00(x_4);
        Vector#(4, Bit#(64)) x_11 = (unpack(0));
        Bool x_12 = ((x_7).mesi_owned);
        Bit#(3) x_13 = ((x_7).mesi_status);
        Struct18 x_14 = (Struct18 {dir_st : (x_7).mesi_dir_st, dir_excl :
        ((((x_7).mesi_dir_sharers)[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(1))'(1'h0)) : (((Bit#(1))'(1'h1)) +
        ((((((x_7).mesi_dir_sharers)[1:1])[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(1))'(1'h0)) : (((Bit#(1))'(1'h1)) + (unpack(0))))))),
        dir_sharers : (x_7).mesi_dir_sharers});
        when ((x_2) == ((Bit#(3))'(3'h0)), noAction);
        when (((x_3).id) == ((Bit#(6))'(6'ha)), noAction);
        when (! ((x_3).type_), noAction);
        when (((Bool)'(True)) && (((Bool)'(True)) && ((!
        ((((x_14).dir_sharers) & (~(((Bit#(2))'(2'h1)) <<
        ((Bit#(1))'(1'h0))))) == ((Bit#(2))'(2'h0)))) && (((x_12) ==
        ((Bool)'(True))) && ((! (((Bit#(3))'(3'h2)) < (x_13))) &&
        (((x_14).dir_st) == ((Bit#(3))'(3'h2))))))), noAction);
        Struct1 x_15 = (x_3);
        Struct19 x_16 = (Struct19 {addr : (x_3).addr, info_write :
        (Bool)'(False), info_hit : (x_6).info_hit, info_way : (x_6).info_way,
        edir_hit : (x_6).edir_hit, edir_way : (x_6).edir_way, edir_slot :
        (x_6).edir_slot, info : (x_6).info, value_write : (Bool)'(False),
        value : unpack(0), may_victim : (x_6).may_victim, reps :
        (x_6).reps});
        let x_18 = ?;
        if ((x_8).valid) begin
            x_18 = x_9;
        end else begin
            let x_17 <- cache__00__valueRsLineRq(unpack(0));
            x_18 = x_17;
        end
        let x_19 <- registerDL_00(Struct23 {r_id : x_4, r_dl_rss_from :
        ((x_14).dir_sharers) & (~(((Bit#(2))'(2'h1)) << ((Bit#(1))'(1'h0)))),
        r_dl_rsb : (Bool)'(True), r_dl_rsbTo : (Bit#(3))'(3'h4)});
        let x_20 <- broadcast_parentChildren00(Struct24 {cs_inds :
        ((x_14).dir_sharers) & (~(((Bit#(2))'(2'h1)) << ((Bit#(1))'(1'h0)))),
        cs_msg : Struct1 {id : (Bit#(6))'(6'hc), type_ : (Bool)'(False), addr
        : (x_15).addr, value : unpack(0)}});
    endrule

    rule rule_exec_00_25000;
        $display ("Rule fired: rule_exec_00_25000 at %t", $time);
        let x_0 <- deq_fifoL2E_00();
        Struct7 x_1 = ((x_0).lr_ir_pp);
        Bit#(3) x_2 = ((x_1).ir_msg_from);
        Struct1 x_3 = ((x_1).ir_msg);
        Bit#(4) x_4 = ((x_1).ir_mshr_id);
        Bool x_5 = ((x_1).ir_is_rs_rel);
        when (! (x_5), noAction);
        Struct10 x_6 = ((x_0).lr_ir);
        Struct11 x_7 = ((x_6).info);
        Struct6 x_8 = ((x_1).ir_by_victim);
        Vector#(4, Bit#(64)) x_9 = ((x_0).lr_value);
        let x_10 <- getMSHR_00(x_4);
        Vector#(4, Bit#(64)) x_11 = (unpack(0));
        Bool x_12 = ((x_7).mesi_owned);
        Bit#(3) x_13 = ((x_7).mesi_status);
        Struct18 x_14 = (Struct18 {dir_st : (x_7).mesi_dir_st, dir_excl :
        ((((x_7).mesi_dir_sharers)[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(1))'(1'h0)) : (((Bit#(1))'(1'h1)) +
        ((((((x_7).mesi_dir_sharers)[1:1])[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(1))'(1'h0)) : (((Bit#(1))'(1'h1)) + (unpack(0))))))),
        dir_sharers : (x_7).mesi_dir_sharers});
        when ((x_2) == ((Bit#(3))'(3'h0)), noAction);
        when (((x_3).id) == ((Bit#(6))'(6'h14)), noAction);
        when (! ((x_3).type_), noAction);
        when ((((((x_14).dir_st) == ((Bit#(3))'(3'h4))) && (((x_14).dir_excl)
        == ((Bit#(1))'(1'h0))) ? ((Bit#(3))'(3'h4)) : (((((x_14).dir_st) ==
        ((Bit#(3))'(3'h3))) && (((x_14).dir_excl) == ((Bit#(1))'(1'h0))) ?
        ((Bit#(3))'(3'h3)) : (((((x_14).dir_st) == ((Bit#(3))'(3'h2))) &&
        ((((x_14).dir_sharers) | (((Bit#(2))'(2'h1)) << ((Bit#(1))'(1'h0))))
        == ((x_14).dir_sharers)) ? ((Bit#(3))'(3'h2)) :
        ((Bit#(3))'(3'h1)))))))) == ((Bit#(3))'(3'h1)), noAction);
        Struct1 x_15 = (x_3);
        Struct19 x_16 = (Struct19 {addr : (x_3).addr, info_write :
        (Bool)'(False), info_hit : (x_6).info_hit, info_way : (x_6).info_way,
        edir_hit : (x_6).edir_hit, edir_way : (x_6).edir_way, edir_slot :
        (x_6).edir_slot, info : (x_6).info, value_write : (Bool)'(False),
        value : unpack(0), may_victim : (x_6).may_victim, reps :
        (x_6).reps});
        let x_18 = ?;
        if ((x_8).valid) begin
            x_18 = x_9;
        end else begin
            let x_17 <- cache__00__valueRsLineRq(unpack(0));
            x_18 = x_17;
        end
        Struct21 x_19 = (Struct21 {enq_type : ((((Bit#(3))'(3'h4))[2:1]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : (((((Bit#(3))'(3'h4))[2:1])
        == ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : ((Bit#(3))'(3'h4))[0:0], enq_msg : Struct1 {id :
        (Bit#(6))'(6'h16), type_ : (Bool)'(True), addr : (x_15).addr, value :
        unpack(0)}});
        let x_20 <- makeEnq_parentChildren00(x_19);
    endrule

    rule rule_exec_00_2600000;
        $display ("Rule fired: rule_exec_00_2600000 at %t", $time);
        let x_0 <- deq_fifoL2E_00();
        Struct7 x_1 = ((x_0).lr_ir_pp);
        Bit#(3) x_2 = ((x_1).ir_msg_from);
        Struct1 x_3 = ((x_1).ir_msg);
        Bit#(4) x_4 = ((x_1).ir_mshr_id);
        Bool x_5 = ((x_1).ir_is_rs_rel);
        when (! (x_5), noAction);
        Struct10 x_6 = ((x_0).lr_ir);
        Struct11 x_7 = ((x_6).info);
        Struct6 x_8 = ((x_1).ir_by_victim);
        Vector#(4, Bit#(64)) x_9 = ((x_0).lr_value);
        let x_10 <- getMSHR_00(x_4);
        Vector#(4, Bit#(64)) x_11 = (unpack(0));
        Bool x_12 = ((x_7).mesi_owned);
        Bit#(3) x_13 = ((x_7).mesi_status);
        Struct18 x_14 = (Struct18 {dir_st : (x_7).mesi_dir_st, dir_excl :
        ((((x_7).mesi_dir_sharers)[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(1))'(1'h0)) : (((Bit#(1))'(1'h1)) +
        ((((((x_7).mesi_dir_sharers)[1:1])[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(1))'(1'h0)) : (((Bit#(1))'(1'h1)) + (unpack(0))))))),
        dir_sharers : (x_7).mesi_dir_sharers});
        when ((x_2) == ((Bit#(3))'(3'h0)), noAction);
        when (((x_3).id) == ((Bit#(6))'(6'h14)), noAction);
        when (! ((x_3).type_), noAction);
        when (((x_12) == ((Bool)'(False))) && (((((((x_14).dir_st) ==
        ((Bit#(3))'(3'h4))) && (((x_14).dir_excl) == ((Bit#(1))'(1'h0))) ?
        ((Bit#(3))'(3'h4)) : (((((x_14).dir_st) == ((Bit#(3))'(3'h3))) &&
        (((x_14).dir_excl) == ((Bit#(1))'(1'h0))) ? ((Bit#(3))'(3'h3)) :
        (((((x_14).dir_st) == ((Bit#(3))'(3'h2))) && ((((x_14).dir_sharers) |
        (((Bit#(2))'(2'h1)) << ((Bit#(1))'(1'h0)))) == ((x_14).dir_sharers))
        ? ((Bit#(3))'(3'h2)) : ((Bit#(3))'(3'h1)))))))) ==
        ((Bit#(3))'(3'h2))) && (((x_14).dir_sharers) == (((Bit#(2))'(2'h1))
        << ((Bit#(1))'(1'h0))))), noAction);
        Struct1 x_15 = (x_3);
        Struct19 x_16 = (Struct19 {addr : (x_3).addr, info_write :
        (Bool)'(False), info_hit : (x_6).info_hit, info_way : (x_6).info_way,
        edir_hit : (x_6).edir_hit, edir_way : (x_6).edir_way, edir_slot :
        (x_6).edir_slot, info : (x_6).info, value_write : (Bool)'(False),
        value : unpack(0), may_victim : (x_6).may_victim, reps :
        (x_6).reps});
        Struct19 x_17 = (Struct19 {addr : (x_16).addr, info_write :
        (Bool)'(True), info_hit : (x_16).info_hit, info_way :
        (x_16).info_way, edir_hit : (x_16).edir_hit, edir_way :
        (x_16).edir_way, edir_slot : (x_16).edir_slot, info : Struct11
        {mesi_owned : ((x_16).info).mesi_owned, mesi_status :
        ((x_16).info).mesi_status, mesi_dir_st : (Struct18 {dir_st :
        (Bit#(3))'(3'h1), dir_excl : unpack(0), dir_sharers :
        unpack(0)}).dir_st, mesi_dir_sharers : (((Struct18 {dir_st :
        (Bit#(3))'(3'h1), dir_excl : unpack(0), dir_sharers :
        unpack(0)}).dir_st) == ((Bit#(3))'(3'h2)) ? ((Struct18 {dir_st :
        (Bit#(3))'(3'h1), dir_excl : unpack(0), dir_sharers :
        unpack(0)}).dir_sharers) : (((Bit#(2))'(2'h1)) << ((Struct18 {dir_st
        : (Bit#(3))'(3'h1), dir_excl : unpack(0), dir_sharers :
        unpack(0)}).dir_excl)))}, value_write : (x_16).value_write, value :
        (x_16).value, may_victim : (x_16).may_victim, reps :
        (x_16).reps});
        let x_20 = ?;
        if ((x_8).valid) begin
            let x_18 <- victims__00__setVictim(Struct20 {victim_idx :
            (x_8).data, victim_info : (x_17).info, victim_value :
            (x_17).value});
            x_20 = x_9;
        end else begin
            let x_19 <- cache__00__valueRsLineRq(x_17);
            x_20 = x_19;
        end
        Struct21 x_21 = (Struct21 {enq_type : ((((Bit#(3))'(3'h4))[2:1]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : (((((Bit#(3))'(3'h4))[2:1])
        == ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : ((Bit#(3))'(3'h4))[0:0], enq_msg : Struct1 {id :
        (Bit#(6))'(6'h16), type_ : (Bool)'(True), addr : (x_15).addr, value :
        unpack(0)}});
        let x_22 <- makeEnq_parentChildren00(x_21);
    endrule

    rule rule_exec_00_2601000;
        $display ("Rule fired: rule_exec_00_2601000 at %t", $time);
        let x_0 <- deq_fifoL2E_00();
        Struct7 x_1 = ((x_0).lr_ir_pp);
        Bit#(3) x_2 = ((x_1).ir_msg_from);
        Struct1 x_3 = ((x_1).ir_msg);
        Bit#(4) x_4 = ((x_1).ir_mshr_id);
        Bool x_5 = ((x_1).ir_is_rs_rel);
        when (! (x_5), noAction);
        Struct10 x_6 = ((x_0).lr_ir);
        Struct11 x_7 = ((x_6).info);
        Struct6 x_8 = ((x_1).ir_by_victim);
        Vector#(4, Bit#(64)) x_9 = ((x_0).lr_value);
        let x_10 <- getMSHR_00(x_4);
        Vector#(4, Bit#(64)) x_11 = (unpack(0));
        Bool x_12 = ((x_7).mesi_owned);
        Bit#(3) x_13 = ((x_7).mesi_status);
        Struct18 x_14 = (Struct18 {dir_st : (x_7).mesi_dir_st, dir_excl :
        ((((x_7).mesi_dir_sharers)[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(1))'(1'h0)) : (((Bit#(1))'(1'h1)) +
        ((((((x_7).mesi_dir_sharers)[1:1])[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(1))'(1'h0)) : (((Bit#(1))'(1'h1)) + (unpack(0))))))),
        dir_sharers : (x_7).mesi_dir_sharers});
        when ((x_2) == ((Bit#(3))'(3'h0)), noAction);
        when (((x_3).id) == ((Bit#(6))'(6'h14)), noAction);
        when (! ((x_3).type_), noAction);
        when (((x_12) == ((Bool)'(True))) && (((x_13) == ((Bit#(3))'(3'h2)))
        && (((((((x_14).dir_st) == ((Bit#(3))'(3'h4))) && (((x_14).dir_excl)
        == ((Bit#(1))'(1'h0))) ? ((Bit#(3))'(3'h4)) : (((((x_14).dir_st) ==
        ((Bit#(3))'(3'h3))) && (((x_14).dir_excl) == ((Bit#(1))'(1'h0))) ?
        ((Bit#(3))'(3'h3)) : (((((x_14).dir_st) == ((Bit#(3))'(3'h2))) &&
        ((((x_14).dir_sharers) | (((Bit#(2))'(2'h1)) << ((Bit#(1))'(1'h0))))
        == ((x_14).dir_sharers)) ? ((Bit#(3))'(3'h2)) :
        ((Bit#(3))'(3'h1)))))))) == ((Bit#(3))'(3'h2))) &&
        (((x_14).dir_sharers) == (((Bit#(2))'(2'h1)) <<
        ((Bit#(1))'(1'h0)))))), noAction);
        Struct1 x_15 = (x_3);
        Struct19 x_16 = (Struct19 {addr : (x_3).addr, info_write :
        (Bool)'(False), info_hit : (x_6).info_hit, info_way : (x_6).info_way,
        edir_hit : (x_6).edir_hit, edir_way : (x_6).edir_way, edir_slot :
        (x_6).edir_slot, info : (x_6).info, value_write : (Bool)'(False),
        value : unpack(0), may_victim : (x_6).may_victim, reps :
        (x_6).reps});
        Struct19 x_17 = (Struct19 {addr : (x_16).addr, info_write :
        (Bool)'(True), info_hit : (x_16).info_hit, info_way :
        (x_16).info_way, edir_hit : (x_16).edir_hit, edir_way :
        (x_16).edir_way, edir_slot : (x_16).edir_slot, info : Struct11
        {mesi_owned : ((x_16).info).mesi_owned, mesi_status :
        ((x_16).info).mesi_status, mesi_dir_st : (Struct18 {dir_st :
        (Bit#(3))'(3'h1), dir_excl : unpack(0), dir_sharers :
        unpack(0)}).dir_st, mesi_dir_sharers : (((Struct18 {dir_st :
        (Bit#(3))'(3'h1), dir_excl : unpack(0), dir_sharers :
        unpack(0)}).dir_st) == ((Bit#(3))'(3'h2)) ? ((Struct18 {dir_st :
        (Bit#(3))'(3'h1), dir_excl : unpack(0), dir_sharers :
        unpack(0)}).dir_sharers) : (((Bit#(2))'(2'h1)) << ((Struct18 {dir_st
        : (Bit#(3))'(3'h1), dir_excl : unpack(0), dir_sharers :
        unpack(0)}).dir_excl)))}, value_write : (x_16).value_write, value :
        (x_16).value, may_victim : (x_16).may_victim, reps :
        (x_16).reps});
        Struct19 x_18 = (Struct19 {addr : (x_17).addr, info_write :
        (Bool)'(True), info_hit : (x_17).info_hit, info_way :
        (x_17).info_way, edir_hit : (x_17).edir_hit, edir_way :
        (x_17).edir_way, edir_slot : (x_17).edir_slot, info : Struct11
        {mesi_owned : ((x_17).info).mesi_owned, mesi_status :
        (Bit#(3))'(3'h4), mesi_dir_st : ((x_17).info).mesi_dir_st,
        mesi_dir_sharers : ((x_17).info).mesi_dir_sharers}, value_write :
        (x_17).value_write, value : (x_17).value, may_victim :
        (x_17).may_victim, reps :
        (x_17).reps});
        let x_21 = ?;
        if ((x_8).valid) begin
            let x_19 <- victims__00__setVictim(Struct20 {victim_idx :
            (x_8).data, victim_info : (x_18).info, victim_value :
            (x_18).value});
            x_21 = x_9;
        end else begin
            let x_20 <- cache__00__valueRsLineRq(x_18);
            x_21 = x_20;
        end
        Struct21 x_22 = (Struct21 {enq_type : ((((Bit#(3))'(3'h4))[2:1]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : (((((Bit#(3))'(3'h4))[2:1])
        == ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : ((Bit#(3))'(3'h4))[0:0], enq_msg : Struct1 {id :
        (Bit#(6))'(6'h16), type_ : (Bool)'(True), addr : (x_15).addr, value :
        unpack(0)}});
        let x_23 <- makeEnq_parentChildren00(x_22);
    endrule

    rule rule_exec_00_261000;
        $display ("Rule fired: rule_exec_00_261000 at %t", $time);
        let x_0 <- deq_fifoL2E_00();
        Struct7 x_1 = ((x_0).lr_ir_pp);
        Bit#(3) x_2 = ((x_1).ir_msg_from);
        Struct1 x_3 = ((x_1).ir_msg);
        Bit#(4) x_4 = ((x_1).ir_mshr_id);
        Bool x_5 = ((x_1).ir_is_rs_rel);
        when (! (x_5), noAction);
        Struct10 x_6 = ((x_0).lr_ir);
        Struct11 x_7 = ((x_6).info);
        Struct6 x_8 = ((x_1).ir_by_victim);
        Vector#(4, Bit#(64)) x_9 = ((x_0).lr_value);
        let x_10 <- getMSHR_00(x_4);
        Vector#(4, Bit#(64)) x_11 = (unpack(0));
        Bool x_12 = ((x_7).mesi_owned);
        Bit#(3) x_13 = ((x_7).mesi_status);
        Struct18 x_14 = (Struct18 {dir_st : (x_7).mesi_dir_st, dir_excl :
        ((((x_7).mesi_dir_sharers)[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(1))'(1'h0)) : (((Bit#(1))'(1'h1)) +
        ((((((x_7).mesi_dir_sharers)[1:1])[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(1))'(1'h0)) : (((Bit#(1))'(1'h1)) + (unpack(0))))))),
        dir_sharers : (x_7).mesi_dir_sharers});
        when ((x_2) == ((Bit#(3))'(3'h0)), noAction);
        when (((x_3).id) == ((Bit#(6))'(6'h14)), noAction);
        when (! ((x_3).type_), noAction);
        when (((((((x_14).dir_st) == ((Bit#(3))'(3'h4))) &&
        (((x_14).dir_excl) == ((Bit#(1))'(1'h0))) ? ((Bit#(3))'(3'h4)) :
        (((((x_14).dir_st) == ((Bit#(3))'(3'h3))) && (((x_14).dir_excl) ==
        ((Bit#(1))'(1'h0))) ? ((Bit#(3))'(3'h3)) : (((((x_14).dir_st) ==
        ((Bit#(3))'(3'h2))) && ((((x_14).dir_sharers) | (((Bit#(2))'(2'h1))
        << ((Bit#(1))'(1'h0)))) == ((x_14).dir_sharers)) ? ((Bit#(3))'(3'h2))
        : ((Bit#(3))'(3'h1)))))))) == ((Bit#(3))'(3'h2))) &&
        (((Bit#(2))'(2'h1)) < ((((((x_14).dir_sharers)[0:0]) ==
        ((Bit#(1))'(1'h1)) ? ((Bit#(2))'(2'h1)) : ((Bit#(2))'(2'h0)))) +
        (((((((x_14).dir_sharers)[1:1])[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(2))'(2'h1)) : ((Bit#(2))'(2'h0)))) + (unpack(0))))),
        noAction);
        Struct1 x_15 = (x_3);
        Struct19 x_16 = (Struct19 {addr : (x_3).addr, info_write :
        (Bool)'(False), info_hit : (x_6).info_hit, info_way : (x_6).info_way,
        edir_hit : (x_6).edir_hit, edir_way : (x_6).edir_way, edir_slot :
        (x_6).edir_slot, info : (x_6).info, value_write : (Bool)'(False),
        value : unpack(0), may_victim : (x_6).may_victim, reps :
        (x_6).reps});
        Struct19 x_17 = (Struct19 {addr : (x_16).addr, info_write :
        (Bool)'(True), info_hit : (x_16).info_hit, info_way :
        (x_16).info_way, edir_hit : (x_16).edir_hit, edir_way :
        (x_16).edir_way, edir_slot : (x_16).edir_slot, info : Struct11
        {mesi_owned : ((x_16).info).mesi_owned, mesi_status :
        ((x_16).info).mesi_status, mesi_dir_st : (Struct18 {dir_st :
        (Bit#(3))'(3'h2), dir_excl : (x_14).dir_excl, dir_sharers :
        ((x_14).dir_sharers) & (~(((Bit#(2))'(2'h1)) <<
        ((Bit#(1))'(1'h0))))}).dir_st, mesi_dir_sharers : (((Struct18 {dir_st
        : (Bit#(3))'(3'h2), dir_excl : (x_14).dir_excl, dir_sharers :
        ((x_14).dir_sharers) & (~(((Bit#(2))'(2'h1)) <<
        ((Bit#(1))'(1'h0))))}).dir_st) == ((Bit#(3))'(3'h2)) ? ((Struct18
        {dir_st : (Bit#(3))'(3'h2), dir_excl : (x_14).dir_excl, dir_sharers :
        ((x_14).dir_sharers) & (~(((Bit#(2))'(2'h1)) <<
        ((Bit#(1))'(1'h0))))}).dir_sharers) : (((Bit#(2))'(2'h1)) <<
        ((Struct18 {dir_st : (Bit#(3))'(3'h2), dir_excl : (x_14).dir_excl,
        dir_sharers : ((x_14).dir_sharers) & (~(((Bit#(2))'(2'h1)) <<
        ((Bit#(1))'(1'h0))))}).dir_excl)))}, value_write :
        (x_16).value_write, value : (x_16).value, may_victim :
        (x_16).may_victim, reps :
        (x_16).reps});
        let x_20 = ?;
        if ((x_8).valid) begin
            let x_18 <- victims__00__setVictim(Struct20 {victim_idx :
            (x_8).data, victim_info : (x_17).info, victim_value :
            (x_17).value});
            x_20 = x_9;
        end else begin
            let x_19 <- cache__00__valueRsLineRq(x_17);
            x_20 = x_19;
        end
        Struct21 x_21 = (Struct21 {enq_type : ((((Bit#(3))'(3'h4))[2:1]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : (((((Bit#(3))'(3'h4))[2:1])
        == ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : ((Bit#(3))'(3'h4))[0:0], enq_msg : Struct1 {id :
        (Bit#(6))'(6'h16), type_ : (Bool)'(True), addr : (x_15).addr, value :
        unpack(0)}});
        let x_22 <- makeEnq_parentChildren00(x_21);
    endrule

    rule rule_exec_00_27000;
        $display ("Rule fired: rule_exec_00_27000 at %t", $time);
        let x_0 <- deq_fifoL2E_00();
        Struct7 x_1 = ((x_0).lr_ir_pp);
        Bit#(3) x_2 = ((x_1).ir_msg_from);
        Struct1 x_3 = ((x_1).ir_msg);
        Bit#(4) x_4 = ((x_1).ir_mshr_id);
        Bool x_5 = ((x_1).ir_is_rs_rel);
        when (! (x_5), noAction);
        Struct10 x_6 = ((x_0).lr_ir);
        Struct11 x_7 = ((x_6).info);
        Struct6 x_8 = ((x_1).ir_by_victim);
        Vector#(4, Bit#(64)) x_9 = ((x_0).lr_value);
        let x_10 <- getMSHR_00(x_4);
        Vector#(4, Bit#(64)) x_11 = (unpack(0));
        Bool x_12 = ((x_7).mesi_owned);
        Bit#(3) x_13 = ((x_7).mesi_status);
        Struct18 x_14 = (Struct18 {dir_st : (x_7).mesi_dir_st, dir_excl :
        ((((x_7).mesi_dir_sharers)[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(1))'(1'h0)) : (((Bit#(1))'(1'h1)) +
        ((((((x_7).mesi_dir_sharers)[1:1])[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(1))'(1'h0)) : (((Bit#(1))'(1'h1)) + (unpack(0))))))),
        dir_sharers : (x_7).mesi_dir_sharers});
        when ((x_2) == ((Bit#(3))'(3'h0)), noAction);
        when (((x_3).id) == ((Bit#(6))'(6'h14)), noAction);
        when (! ((x_3).type_), noAction);
        when ((((((x_14).dir_st) == ((Bit#(3))'(3'h4))) && (((x_14).dir_excl)
        == ((Bit#(1))'(1'h0))) ? ((Bit#(3))'(3'h4)) : (((((x_14).dir_st) ==
        ((Bit#(3))'(3'h3))) && (((x_14).dir_excl) == ((Bit#(1))'(1'h0))) ?
        ((Bit#(3))'(3'h3)) : (((((x_14).dir_st) == ((Bit#(3))'(3'h2))) &&
        ((((x_14).dir_sharers) | (((Bit#(2))'(2'h1)) << ((Bit#(1))'(1'h0))))
        == ((x_14).dir_sharers)) ? ((Bit#(3))'(3'h2)) :
        ((Bit#(3))'(3'h1)))))))) == ((Bit#(3))'(3'h3)), noAction);
        Struct1 x_15 = (x_3);
        Struct19 x_16 = (Struct19 {addr : (x_3).addr, info_write :
        (Bool)'(False), info_hit : (x_6).info_hit, info_way : (x_6).info_way,
        edir_hit : (x_6).edir_hit, edir_way : (x_6).edir_way, edir_slot :
        (x_6).edir_slot, info : (x_6).info, value_write : (Bool)'(False),
        value : unpack(0), may_victim : (x_6).may_victim, reps :
        (x_6).reps});
        Struct19 x_17 = (Struct19 {addr : (x_16).addr, info_write :
        (Bool)'(True), info_hit : (x_16).info_hit, info_way :
        (x_16).info_way, edir_hit : (x_16).edir_hit, edir_way :
        (x_16).edir_way, edir_slot : (x_16).edir_slot, info : Struct11
        {mesi_owned : ((x_16).info).mesi_owned, mesi_status :
        ((x_16).info).mesi_status, mesi_dir_st : (Struct18 {dir_st :
        (Bit#(3))'(3'h1), dir_excl : unpack(0), dir_sharers :
        unpack(0)}).dir_st, mesi_dir_sharers : (((Struct18 {dir_st :
        (Bit#(3))'(3'h1), dir_excl : unpack(0), dir_sharers :
        unpack(0)}).dir_st) == ((Bit#(3))'(3'h2)) ? ((Struct18 {dir_st :
        (Bit#(3))'(3'h1), dir_excl : unpack(0), dir_sharers :
        unpack(0)}).dir_sharers) : (((Bit#(2))'(2'h1)) << ((Struct18 {dir_st
        : (Bit#(3))'(3'h1), dir_excl : unpack(0), dir_sharers :
        unpack(0)}).dir_excl)))}, value_write : (x_16).value_write, value :
        (x_16).value, may_victim : (x_16).may_victim, reps :
        (x_16).reps});
        Struct19 x_18 = (Struct19 {addr : (x_17).addr, info_write :
        (Bool)'(True), info_hit : (x_17).info_hit, info_way :
        (x_17).info_way, edir_hit : (x_17).edir_hit, edir_way :
        (x_17).edir_way, edir_slot : (x_17).edir_slot, info : Struct11
        {mesi_owned : ((x_17).info).mesi_owned, mesi_status :
        (Bit#(3))'(3'h3), mesi_dir_st : ((x_17).info).mesi_dir_st,
        mesi_dir_sharers : ((x_17).info).mesi_dir_sharers}, value_write :
        (x_17).value_write, value : (x_17).value, may_victim :
        (x_17).may_victim, reps :
        (x_17).reps});
        let x_21 = ?;
        if ((x_8).valid) begin
            let x_19 <- victims__00__setVictim(Struct20 {victim_idx :
            (x_8).data, victim_info : (x_18).info, victim_value :
            (x_18).value});
            x_21 = x_9;
        end else begin
            let x_20 <- cache__00__valueRsLineRq(x_18);
            x_21 = x_20;
        end
        Struct21 x_22 = (Struct21 {enq_type : ((((Bit#(3))'(3'h4))[2:1]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : (((((Bit#(3))'(3'h4))[2:1])
        == ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : ((Bit#(3))'(3'h4))[0:0], enq_msg : Struct1 {id :
        (Bit#(6))'(6'h16), type_ : (Bool)'(True), addr : (x_15).addr, value :
        unpack(0)}});
        let x_23 <- makeEnq_parentChildren00(x_22);
    endrule

    rule rule_exec_00_28000;
        $display ("Rule fired: rule_exec_00_28000 at %t", $time);
        let x_0 <- deq_fifoL2E_00();
        Struct7 x_1 = ((x_0).lr_ir_pp);
        Bit#(3) x_2 = ((x_1).ir_msg_from);
        Struct1 x_3 = ((x_1).ir_msg);
        Bit#(4) x_4 = ((x_1).ir_mshr_id);
        Bool x_5 = ((x_1).ir_is_rs_rel);
        when (! (x_5), noAction);
        Struct10 x_6 = ((x_0).lr_ir);
        Struct11 x_7 = ((x_6).info);
        Struct6 x_8 = ((x_1).ir_by_victim);
        Vector#(4, Bit#(64)) x_9 = ((x_0).lr_value);
        let x_10 <- getMSHR_00(x_4);
        Vector#(4, Bit#(64)) x_11 = (unpack(0));
        Bool x_12 = ((x_7).mesi_owned);
        Bit#(3) x_13 = ((x_7).mesi_status);
        Struct18 x_14 = (Struct18 {dir_st : (x_7).mesi_dir_st, dir_excl :
        ((((x_7).mesi_dir_sharers)[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(1))'(1'h0)) : (((Bit#(1))'(1'h1)) +
        ((((((x_7).mesi_dir_sharers)[1:1])[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(1))'(1'h0)) : (((Bit#(1))'(1'h1)) + (unpack(0))))))),
        dir_sharers : (x_7).mesi_dir_sharers});
        when ((x_2) == ((Bit#(3))'(3'h0)), noAction);
        when (((x_3).id) == ((Bit#(6))'(6'h15)), noAction);
        when (! ((x_3).type_), noAction);
        when ((((((x_14).dir_st) == ((Bit#(3))'(3'h4))) && (((x_14).dir_excl)
        == ((Bit#(1))'(1'h0))) ? ((Bit#(3))'(3'h4)) : (((((x_14).dir_st) ==
        ((Bit#(3))'(3'h3))) && (((x_14).dir_excl) == ((Bit#(1))'(1'h0))) ?
        ((Bit#(3))'(3'h3)) : (((((x_14).dir_st) == ((Bit#(3))'(3'h2))) &&
        ((((x_14).dir_sharers) | (((Bit#(2))'(2'h1)) << ((Bit#(1))'(1'h0))))
        == ((x_14).dir_sharers)) ? ((Bit#(3))'(3'h2)) :
        ((Bit#(3))'(3'h1)))))))) == ((Bit#(3))'(3'h1)), noAction);
        Struct1 x_15 = (x_3);
        Struct19 x_16 = (Struct19 {addr : (x_3).addr, info_write :
        (Bool)'(False), info_hit : (x_6).info_hit, info_way : (x_6).info_way,
        edir_hit : (x_6).edir_hit, edir_way : (x_6).edir_way, edir_slot :
        (x_6).edir_slot, info : (x_6).info, value_write : (Bool)'(False),
        value : unpack(0), may_victim : (x_6).may_victim, reps :
        (x_6).reps});
        let x_18 = ?;
        if ((x_8).valid) begin
            x_18 = x_9;
        end else begin
            let x_17 <- cache__00__valueRsLineRq(unpack(0));
            x_18 = x_17;
        end
        Struct21 x_19 = (Struct21 {enq_type : ((((Bit#(3))'(3'h4))[2:1]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : (((((Bit#(3))'(3'h4))[2:1])
        == ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : ((Bit#(3))'(3'h4))[0:0], enq_msg : Struct1 {id :
        (Bit#(6))'(6'h16), type_ : (Bool)'(True), addr : (x_15).addr, value :
        unpack(0)}});
        let x_20 <- makeEnq_parentChildren00(x_19);
    endrule

    rule rule_exec_00_290000;
        $display ("Rule fired: rule_exec_00_290000 at %t", $time);
        let x_0 <- deq_fifoL2E_00();
        Struct7 x_1 = ((x_0).lr_ir_pp);
        Bit#(3) x_2 = ((x_1).ir_msg_from);
        Struct1 x_3 = ((x_1).ir_msg);
        Bit#(4) x_4 = ((x_1).ir_mshr_id);
        Bool x_5 = ((x_1).ir_is_rs_rel);
        when (! (x_5), noAction);
        Struct10 x_6 = ((x_0).lr_ir);
        Struct11 x_7 = ((x_6).info);
        Struct6 x_8 = ((x_1).ir_by_victim);
        Vector#(4, Bit#(64)) x_9 = ((x_0).lr_value);
        let x_10 <- getMSHR_00(x_4);
        Vector#(4, Bit#(64)) x_11 = (unpack(0));
        Bool x_12 = ((x_7).mesi_owned);
        Bit#(3) x_13 = ((x_7).mesi_status);
        Struct18 x_14 = (Struct18 {dir_st : (x_7).mesi_dir_st, dir_excl :
        ((((x_7).mesi_dir_sharers)[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(1))'(1'h0)) : (((Bit#(1))'(1'h1)) +
        ((((((x_7).mesi_dir_sharers)[1:1])[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(1))'(1'h0)) : (((Bit#(1))'(1'h1)) + (unpack(0))))))),
        dir_sharers : (x_7).mesi_dir_sharers});
        when ((x_2) == ((Bit#(3))'(3'h0)), noAction);
        when (((x_3).id) == ((Bit#(6))'(6'h15)), noAction);
        when (! ((x_3).type_), noAction);
        when (((x_12) == ((Bool)'(False))) && (((((((x_14).dir_st) ==
        ((Bit#(3))'(3'h4))) && (((x_14).dir_excl) == ((Bit#(1))'(1'h0))) ?
        ((Bit#(3))'(3'h4)) : (((((x_14).dir_st) == ((Bit#(3))'(3'h3))) &&
        (((x_14).dir_excl) == ((Bit#(1))'(1'h0))) ? ((Bit#(3))'(3'h3)) :
        (((((x_14).dir_st) == ((Bit#(3))'(3'h2))) && ((((x_14).dir_sharers) |
        (((Bit#(2))'(2'h1)) << ((Bit#(1))'(1'h0)))) == ((x_14).dir_sharers))
        ? ((Bit#(3))'(3'h2)) : ((Bit#(3))'(3'h1)))))))) ==
        ((Bit#(3))'(3'h2))) && (((x_14).dir_sharers) == (((Bit#(2))'(2'h1))
        << ((Bit#(1))'(1'h0))))), noAction);
        Struct1 x_15 = (x_3);
        Struct19 x_16 = (Struct19 {addr : (x_3).addr, info_write :
        (Bool)'(False), info_hit : (x_6).info_hit, info_way : (x_6).info_way,
        edir_hit : (x_6).edir_hit, edir_way : (x_6).edir_way, edir_slot :
        (x_6).edir_slot, info : (x_6).info, value_write : (Bool)'(False),
        value : unpack(0), may_victim : (x_6).may_victim, reps :
        (x_6).reps});
        Struct19 x_17 = (Struct19 {addr : (x_16).addr, info_write :
        (Bool)'(True), info_hit : (x_16).info_hit, info_way :
        (x_16).info_way, edir_hit : (x_16).edir_hit, edir_way :
        (x_16).edir_way, edir_slot : (x_16).edir_slot, info : Struct11
        {mesi_owned : ((x_16).info).mesi_owned, mesi_status :
        ((x_16).info).mesi_status, mesi_dir_st : (Struct18 {dir_st :
        (Bit#(3))'(3'h1), dir_excl : unpack(0), dir_sharers :
        unpack(0)}).dir_st, mesi_dir_sharers : (((Struct18 {dir_st :
        (Bit#(3))'(3'h1), dir_excl : unpack(0), dir_sharers :
        unpack(0)}).dir_st) == ((Bit#(3))'(3'h2)) ? ((Struct18 {dir_st :
        (Bit#(3))'(3'h1), dir_excl : unpack(0), dir_sharers :
        unpack(0)}).dir_sharers) : (((Bit#(2))'(2'h1)) << ((Struct18 {dir_st
        : (Bit#(3))'(3'h1), dir_excl : unpack(0), dir_sharers :
        unpack(0)}).dir_excl)))}, value_write : (x_16).value_write, value :
        (x_16).value, may_victim : (x_16).may_victim, reps :
        (x_16).reps});
        let x_20 = ?;
        if ((x_8).valid) begin
            let x_18 <- victims__00__setVictim(Struct20 {victim_idx :
            (x_8).data, victim_info : (x_17).info, victim_value :
            (x_17).value});
            x_20 = x_9;
        end else begin
            let x_19 <- cache__00__valueRsLineRq(x_17);
            x_20 = x_19;
        end
        Struct21 x_21 = (Struct21 {enq_type : ((((Bit#(3))'(3'h4))[2:1]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : (((((Bit#(3))'(3'h4))[2:1])
        == ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : ((Bit#(3))'(3'h4))[0:0], enq_msg : Struct1 {id :
        (Bit#(6))'(6'h16), type_ : (Bool)'(True), addr : (x_15).addr, value :
        unpack(0)}});
        let x_22 <- makeEnq_parentChildren00(x_21);
    endrule

    rule rule_exec_00_291000;
        $display ("Rule fired: rule_exec_00_291000 at %t", $time);
        let x_0 <- deq_fifoL2E_00();
        Struct7 x_1 = ((x_0).lr_ir_pp);
        Bit#(3) x_2 = ((x_1).ir_msg_from);
        Struct1 x_3 = ((x_1).ir_msg);
        Bit#(4) x_4 = ((x_1).ir_mshr_id);
        Bool x_5 = ((x_1).ir_is_rs_rel);
        when (! (x_5), noAction);
        Struct10 x_6 = ((x_0).lr_ir);
        Struct11 x_7 = ((x_6).info);
        Struct6 x_8 = ((x_1).ir_by_victim);
        Vector#(4, Bit#(64)) x_9 = ((x_0).lr_value);
        let x_10 <- getMSHR_00(x_4);
        Vector#(4, Bit#(64)) x_11 = (unpack(0));
        Bool x_12 = ((x_7).mesi_owned);
        Bit#(3) x_13 = ((x_7).mesi_status);
        Struct18 x_14 = (Struct18 {dir_st : (x_7).mesi_dir_st, dir_excl :
        ((((x_7).mesi_dir_sharers)[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(1))'(1'h0)) : (((Bit#(1))'(1'h1)) +
        ((((((x_7).mesi_dir_sharers)[1:1])[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(1))'(1'h0)) : (((Bit#(1))'(1'h1)) + (unpack(0))))))),
        dir_sharers : (x_7).mesi_dir_sharers});
        when ((x_2) == ((Bit#(3))'(3'h0)), noAction);
        when (((x_3).id) == ((Bit#(6))'(6'h15)), noAction);
        when (! ((x_3).type_), noAction);
        when (((((((x_14).dir_st) == ((Bit#(3))'(3'h4))) &&
        (((x_14).dir_excl) == ((Bit#(1))'(1'h0))) ? ((Bit#(3))'(3'h4)) :
        (((((x_14).dir_st) == ((Bit#(3))'(3'h3))) && (((x_14).dir_excl) ==
        ((Bit#(1))'(1'h0))) ? ((Bit#(3))'(3'h3)) : (((((x_14).dir_st) ==
        ((Bit#(3))'(3'h2))) && ((((x_14).dir_sharers) | (((Bit#(2))'(2'h1))
        << ((Bit#(1))'(1'h0)))) == ((x_14).dir_sharers)) ? ((Bit#(3))'(3'h2))
        : ((Bit#(3))'(3'h1)))))))) == ((Bit#(3))'(3'h2))) &&
        (((Bit#(2))'(2'h1)) < ((((((x_14).dir_sharers)[0:0]) ==
        ((Bit#(1))'(1'h1)) ? ((Bit#(2))'(2'h1)) : ((Bit#(2))'(2'h0)))) +
        (((((((x_14).dir_sharers)[1:1])[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(2))'(2'h1)) : ((Bit#(2))'(2'h0)))) + (unpack(0))))),
        noAction);
        Struct1 x_15 = (x_3);
        Struct19 x_16 = (Struct19 {addr : (x_3).addr, info_write :
        (Bool)'(False), info_hit : (x_6).info_hit, info_way : (x_6).info_way,
        edir_hit : (x_6).edir_hit, edir_way : (x_6).edir_way, edir_slot :
        (x_6).edir_slot, info : (x_6).info, value_write : (Bool)'(False),
        value : unpack(0), may_victim : (x_6).may_victim, reps :
        (x_6).reps});
        Struct19 x_17 = (Struct19 {addr : (x_16).addr, info_write :
        (Bool)'(True), info_hit : (x_16).info_hit, info_way :
        (x_16).info_way, edir_hit : (x_16).edir_hit, edir_way :
        (x_16).edir_way, edir_slot : (x_16).edir_slot, info : Struct11
        {mesi_owned : ((x_16).info).mesi_owned, mesi_status :
        ((x_16).info).mesi_status, mesi_dir_st : (Struct18 {dir_st :
        (Bit#(3))'(3'h2), dir_excl : (x_14).dir_excl, dir_sharers :
        ((x_14).dir_sharers) & (~(((Bit#(2))'(2'h1)) <<
        ((Bit#(1))'(1'h0))))}).dir_st, mesi_dir_sharers : (((Struct18 {dir_st
        : (Bit#(3))'(3'h2), dir_excl : (x_14).dir_excl, dir_sharers :
        ((x_14).dir_sharers) & (~(((Bit#(2))'(2'h1)) <<
        ((Bit#(1))'(1'h0))))}).dir_st) == ((Bit#(3))'(3'h2)) ? ((Struct18
        {dir_st : (Bit#(3))'(3'h2), dir_excl : (x_14).dir_excl, dir_sharers :
        ((x_14).dir_sharers) & (~(((Bit#(2))'(2'h1)) <<
        ((Bit#(1))'(1'h0))))}).dir_sharers) : (((Bit#(2))'(2'h1)) <<
        ((Struct18 {dir_st : (Bit#(3))'(3'h2), dir_excl : (x_14).dir_excl,
        dir_sharers : ((x_14).dir_sharers) & (~(((Bit#(2))'(2'h1)) <<
        ((Bit#(1))'(1'h0))))}).dir_excl)))}, value_write :
        (x_16).value_write, value : (x_16).value, may_victim :
        (x_16).may_victim, reps :
        (x_16).reps});
        let x_20 = ?;
        if ((x_8).valid) begin
            let x_18 <- victims__00__setVictim(Struct20 {victim_idx :
            (x_8).data, victim_info : (x_17).info, victim_value :
            (x_17).value});
            x_20 = x_9;
        end else begin
            let x_19 <- cache__00__valueRsLineRq(x_17);
            x_20 = x_19;
        end
        Struct21 x_21 = (Struct21 {enq_type : ((((Bit#(3))'(3'h4))[2:1]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : (((((Bit#(3))'(3'h4))[2:1])
        == ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : ((Bit#(3))'(3'h4))[0:0], enq_msg : Struct1 {id :
        (Bit#(6))'(6'h16), type_ : (Bool)'(True), addr : (x_15).addr, value :
        unpack(0)}});
        let x_22 <- makeEnq_parentChildren00(x_21);
    endrule

    rule rule_exec_00_210000;
        $display ("Rule fired: rule_exec_00_210000 at %t", $time);
        let x_0 <- deq_fifoL2E_00();
        Struct7 x_1 = ((x_0).lr_ir_pp);
        Bit#(3) x_2 = ((x_1).ir_msg_from);
        Struct1 x_3 = ((x_1).ir_msg);
        Bit#(4) x_4 = ((x_1).ir_mshr_id);
        Bool x_5 = ((x_1).ir_is_rs_rel);
        when (! (x_5), noAction);
        Struct10 x_6 = ((x_0).lr_ir);
        Struct11 x_7 = ((x_6).info);
        Struct6 x_8 = ((x_1).ir_by_victim);
        Vector#(4, Bit#(64)) x_9 = ((x_0).lr_value);
        let x_10 <- getMSHR_00(x_4);
        Vector#(4, Bit#(64)) x_11 = (unpack(0));
        Bool x_12 = ((x_7).mesi_owned);
        Bit#(3) x_13 = ((x_7).mesi_status);
        Struct18 x_14 = (Struct18 {dir_st : (x_7).mesi_dir_st, dir_excl :
        ((((x_7).mesi_dir_sharers)[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(1))'(1'h0)) : (((Bit#(1))'(1'h1)) +
        ((((((x_7).mesi_dir_sharers)[1:1])[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(1))'(1'h0)) : (((Bit#(1))'(1'h1)) + (unpack(0))))))),
        dir_sharers : (x_7).mesi_dir_sharers});
        when ((x_2) == ((Bit#(3))'(3'h0)), noAction);
        when (((x_3).id) == ((Bit#(6))'(6'h15)), noAction);
        when (! ((x_3).type_), noAction);
        when (((x_12) == ((Bool)'(True))) && (((x_13) == ((Bit#(3))'(3'h2)))
        && (((((((x_14).dir_st) == ((Bit#(3))'(3'h4))) && (((x_14).dir_excl)
        == ((Bit#(1))'(1'h0))) ? ((Bit#(3))'(3'h4)) : (((((x_14).dir_st) ==
        ((Bit#(3))'(3'h3))) && (((x_14).dir_excl) == ((Bit#(1))'(1'h0))) ?
        ((Bit#(3))'(3'h3)) : (((((x_14).dir_st) == ((Bit#(3))'(3'h2))) &&
        ((((x_14).dir_sharers) | (((Bit#(2))'(2'h1)) << ((Bit#(1))'(1'h0))))
        == ((x_14).dir_sharers)) ? ((Bit#(3))'(3'h2)) :
        ((Bit#(3))'(3'h1)))))))) == ((Bit#(3))'(3'h2))) &&
        (((x_14).dir_sharers) == (((Bit#(2))'(2'h1)) <<
        ((Bit#(1))'(1'h0)))))), noAction);
        Struct1 x_15 = (x_3);
        Struct19 x_16 = (Struct19 {addr : (x_3).addr, info_write :
        (Bool)'(False), info_hit : (x_6).info_hit, info_way : (x_6).info_way,
        edir_hit : (x_6).edir_hit, edir_way : (x_6).edir_way, edir_slot :
        (x_6).edir_slot, info : (x_6).info, value_write : (Bool)'(False),
        value : unpack(0), may_victim : (x_6).may_victim, reps :
        (x_6).reps});
        Struct19 x_17 = (Struct19 {addr : (x_16).addr, info_write :
        (Bool)'(True), info_hit : (x_16).info_hit, info_way :
        (x_16).info_way, edir_hit : (x_16).edir_hit, edir_way :
        (x_16).edir_way, edir_slot : (x_16).edir_slot, info : Struct11
        {mesi_owned : ((x_16).info).mesi_owned, mesi_status :
        ((x_16).info).mesi_status, mesi_dir_st : (Struct18 {dir_st :
        (Bit#(3))'(3'h1), dir_excl : unpack(0), dir_sharers :
        unpack(0)}).dir_st, mesi_dir_sharers : (((Struct18 {dir_st :
        (Bit#(3))'(3'h1), dir_excl : unpack(0), dir_sharers :
        unpack(0)}).dir_st) == ((Bit#(3))'(3'h2)) ? ((Struct18 {dir_st :
        (Bit#(3))'(3'h1), dir_excl : unpack(0), dir_sharers :
        unpack(0)}).dir_sharers) : (((Bit#(2))'(2'h1)) << ((Struct18 {dir_st
        : (Bit#(3))'(3'h1), dir_excl : unpack(0), dir_sharers :
        unpack(0)}).dir_excl)))}, value_write : (x_16).value_write, value :
        (x_16).value, may_victim : (x_16).may_victim, reps :
        (x_16).reps});
        Struct19 x_18 = (Struct19 {addr : (x_17).addr, info_write :
        (Bool)'(True), info_hit : (x_17).info_hit, info_way :
        (x_17).info_way, edir_hit : (x_17).edir_hit, edir_way :
        (x_17).edir_way, edir_slot : (x_17).edir_slot, info : Struct11
        {mesi_owned : ((x_17).info).mesi_owned, mesi_status :
        (Bit#(3))'(3'h4), mesi_dir_st : ((x_17).info).mesi_dir_st,
        mesi_dir_sharers : ((x_17).info).mesi_dir_sharers}, value_write :
        (x_17).value_write, value : (x_17).value, may_victim :
        (x_17).may_victim, reps :
        (x_17).reps});
        let x_21 = ?;
        if ((x_8).valid) begin
            let x_19 <- victims__00__setVictim(Struct20 {victim_idx :
            (x_8).data, victim_info : (x_18).info, victim_value :
            (x_18).value});
            x_21 = x_9;
        end else begin
            let x_20 <- cache__00__valueRsLineRq(x_18);
            x_21 = x_20;
        end
        Struct21 x_22 = (Struct21 {enq_type : ((((Bit#(3))'(3'h4))[2:1]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : (((((Bit#(3))'(3'h4))[2:1])
        == ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : ((Bit#(3))'(3'h4))[0:0], enq_msg : Struct1 {id :
        (Bit#(6))'(6'h16), type_ : (Bool)'(True), addr : (x_15).addr, value :
        unpack(0)}});
        let x_23 <- makeEnq_parentChildren00(x_22);
    endrule

    rule rule_exec_00_211000;
        $display ("Rule fired: rule_exec_00_211000 at %t", $time);
        let x_0 <- deq_fifoL2E_00();
        Struct7 x_1 = ((x_0).lr_ir_pp);
        Bit#(3) x_2 = ((x_1).ir_msg_from);
        Struct1 x_3 = ((x_1).ir_msg);
        Bit#(4) x_4 = ((x_1).ir_mshr_id);
        Bool x_5 = ((x_1).ir_is_rs_rel);
        when (! (x_5), noAction);
        Struct10 x_6 = ((x_0).lr_ir);
        Struct11 x_7 = ((x_6).info);
        Struct6 x_8 = ((x_1).ir_by_victim);
        Vector#(4, Bit#(64)) x_9 = ((x_0).lr_value);
        let x_10 <- getMSHR_00(x_4);
        Vector#(4, Bit#(64)) x_11 = (unpack(0));
        Bool x_12 = ((x_7).mesi_owned);
        Bit#(3) x_13 = ((x_7).mesi_status);
        Struct18 x_14 = (Struct18 {dir_st : (x_7).mesi_dir_st, dir_excl :
        ((((x_7).mesi_dir_sharers)[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(1))'(1'h0)) : (((Bit#(1))'(1'h1)) +
        ((((((x_7).mesi_dir_sharers)[1:1])[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(1))'(1'h0)) : (((Bit#(1))'(1'h1)) + (unpack(0))))))),
        dir_sharers : (x_7).mesi_dir_sharers});
        when ((x_2) == ((Bit#(3))'(3'h0)), noAction);
        when (((x_3).id) == ((Bit#(6))'(6'h15)), noAction);
        when (! ((x_3).type_), noAction);
        when (! ((((((x_14).dir_st) == ((Bit#(3))'(3'h4))) &&
        (((x_14).dir_excl) == ((Bit#(1))'(1'h0))) ? ((Bit#(3))'(3'h4)) :
        (((((x_14).dir_st) == ((Bit#(3))'(3'h3))) && (((x_14).dir_excl) ==
        ((Bit#(1))'(1'h0))) ? ((Bit#(3))'(3'h3)) : (((((x_14).dir_st) ==
        ((Bit#(3))'(3'h2))) && ((((x_14).dir_sharers) | (((Bit#(2))'(2'h1))
        << ((Bit#(1))'(1'h0)))) == ((x_14).dir_sharers)) ? ((Bit#(3))'(3'h2))
        : ((Bit#(3))'(3'h1)))))))) < ((Bit#(3))'(3'h3))), noAction);
        Struct1 x_15 = (x_3);
        Struct19 x_16 = (Struct19 {addr : (x_3).addr, info_write :
        (Bool)'(False), info_hit : (x_6).info_hit, info_way : (x_6).info_way,
        edir_hit : (x_6).edir_hit, edir_way : (x_6).edir_way, edir_slot :
        (x_6).edir_slot, info : (x_6).info, value_write : (Bool)'(False),
        value : unpack(0), may_victim : (x_6).may_victim, reps :
        (x_6).reps});
        Struct19 x_17 = (Struct19 {addr : (x_16).addr, info_write :
        (x_16).info_write, info_hit : (x_16).info_hit, info_way :
        (x_16).info_way, edir_hit : (x_16).edir_hit, edir_way :
        (x_16).edir_way, edir_slot : (x_16).edir_slot, info : (x_16).info,
        value_write : (Bool)'(True), value : (x_15).value, may_victim :
        (x_16).may_victim, reps : (x_16).reps});
        Struct19 x_18 = (Struct19 {addr : (x_17).addr, info_write :
        (Bool)'(True), info_hit : (x_17).info_hit, info_way :
        (x_17).info_way, edir_hit : (x_17).edir_hit, edir_way :
        (x_17).edir_way, edir_slot : (x_17).edir_slot, info : Struct11
        {mesi_owned : ((x_17).info).mesi_owned, mesi_status :
        (Bit#(3))'(3'h4), mesi_dir_st : ((x_17).info).mesi_dir_st,
        mesi_dir_sharers : ((x_17).info).mesi_dir_sharers}, value_write :
        (x_17).value_write, value : (x_17).value, may_victim :
        (x_17).may_victim, reps : (x_17).reps});
        Struct19 x_19 = (Struct19 {addr : (x_18).addr, info_write :
        (Bool)'(True), info_hit : (x_18).info_hit, info_way :
        (x_18).info_way, edir_hit : (x_18).edir_hit, edir_way :
        (x_18).edir_way, edir_slot : (x_18).edir_slot, info : Struct11
        {mesi_owned : (Bool)'(True), mesi_status : ((x_18).info).mesi_status,
        mesi_dir_st : ((x_18).info).mesi_dir_st, mesi_dir_sharers :
        ((x_18).info).mesi_dir_sharers}, value_write : (x_18).value_write,
        value : (x_18).value, may_victim : (x_18).may_victim, reps :
        (x_18).reps});
        Struct19 x_20 = (Struct19 {addr : (x_19).addr, info_write :
        (Bool)'(True), info_hit : (x_19).info_hit, info_way :
        (x_19).info_way, edir_hit : (x_19).edir_hit, edir_way :
        (x_19).edir_way, edir_slot : (x_19).edir_slot, info : Struct11
        {mesi_owned : ((x_19).info).mesi_owned, mesi_status :
        ((x_19).info).mesi_status, mesi_dir_st : (Struct18 {dir_st :
        (Bit#(3))'(3'h1), dir_excl : unpack(0), dir_sharers :
        unpack(0)}).dir_st, mesi_dir_sharers : (((Struct18 {dir_st :
        (Bit#(3))'(3'h1), dir_excl : unpack(0), dir_sharers :
        unpack(0)}).dir_st) == ((Bit#(3))'(3'h2)) ? ((Struct18 {dir_st :
        (Bit#(3))'(3'h1), dir_excl : unpack(0), dir_sharers :
        unpack(0)}).dir_sharers) : (((Bit#(2))'(2'h1)) << ((Struct18 {dir_st
        : (Bit#(3))'(3'h1), dir_excl : unpack(0), dir_sharers :
        unpack(0)}).dir_excl)))}, value_write : (x_19).value_write, value :
        (x_19).value, may_victim : (x_19).may_victim, reps :
        (x_19).reps});
        let x_23 = ?;
        if ((x_8).valid) begin
            let x_21 <- victims__00__setVictim(Struct20 {victim_idx :
            (x_8).data, victim_info : (x_20).info, victim_value :
            (x_20).value});
            x_23 = x_9;
        end else begin
            let x_22 <- cache__00__valueRsLineRq(x_20);
            x_23 = x_22;
        end
        Struct21 x_24 = (Struct21 {enq_type : ((((Bit#(3))'(3'h4))[2:1]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : (((((Bit#(3))'(3'h4))[2:1])
        == ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : ((Bit#(3))'(3'h4))[0:0], enq_msg : Struct1 {id :
        (Bit#(6))'(6'h16), type_ : (Bool)'(True), addr : (x_15).addr, value :
        unpack(0)}});
        let x_25 <- makeEnq_parentChildren00(x_24);
    endrule

    rule rule_exec_00_000001;
        $display ("Rule fired: rule_exec_00_000001 at %t", $time);
        let x_0 <- deq_fifoL2E_00();
        Struct7 x_1 = ((x_0).lr_ir_pp);
        Bit#(3) x_2 = ((x_1).ir_msg_from);
        Struct1 x_3 = ((x_1).ir_msg);
        Bit#(4) x_4 = ((x_1).ir_mshr_id);
        Bool x_5 = ((x_1).ir_is_rs_rel);
        when (! (x_5), noAction);
        Struct10 x_6 = ((x_0).lr_ir);
        Struct11 x_7 = ((x_6).info);
        Struct6 x_8 = ((x_1).ir_by_victim);
        Vector#(4, Bit#(64)) x_9 = ((x_0).lr_value);
        let x_10 <- getMSHR_00(x_4);
        Vector#(4, Bit#(64)) x_11 = (unpack(0));
        Bool x_12 = ((x_7).mesi_owned);
        Bit#(3) x_13 = ((x_7).mesi_status);
        Struct18 x_14 = (Struct18 {dir_st : (x_7).mesi_dir_st, dir_excl :
        ((((x_7).mesi_dir_sharers)[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(1))'(1'h0)) : (((Bit#(1))'(1'h1)) +
        ((((((x_7).mesi_dir_sharers)[1:1])[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(1))'(1'h0)) : (((Bit#(1))'(1'h1)) + (unpack(0))))))),
        dir_sharers : (x_7).mesi_dir_sharers});
        when ((x_2) == ((Bit#(3))'(3'h1)), noAction);
        when (((x_3).id) == ((Bit#(6))'(6'h2)), noAction);
        when (! ((x_3).type_), noAction);
        when ((! (((Bit#(3))'(3'h2)) < ((x_14).dir_st))) && ((x_13) ==
        ((Bit#(3))'(3'h2))), noAction);
        Struct1 x_15 = (x_3);
        Struct19 x_16 = (Struct19 {addr : (x_3).addr, info_write :
        (Bool)'(False), info_hit : (x_6).info_hit, info_way : (x_6).info_way,
        edir_hit : (x_6).edir_hit, edir_way : (x_6).edir_way, edir_slot :
        (x_6).edir_slot, info : (x_6).info, value_write : (Bool)'(False),
        value : unpack(0), may_victim : (x_6).may_victim, reps :
        (x_6).reps});
        Struct19 x_17 = (Struct19 {addr : (x_16).addr, info_write :
        (Bool)'(True), info_hit : (x_16).info_hit, info_way :
        (x_16).info_way, edir_hit : (x_16).edir_hit, edir_way :
        (x_16).edir_way, edir_slot : (x_16).edir_slot, info : Struct11
        {mesi_owned : ((x_16).info).mesi_owned, mesi_status :
        ((x_16).info).mesi_status, mesi_dir_st : (Struct18 {dir_st :
        (Bit#(3))'(3'h2), dir_excl : (x_14).dir_excl, dir_sharers :
        (((x_14).dir_st) == ((Bit#(3))'(3'h2)) ? (((x_14).dir_sharers) |
        (((Bit#(2))'(2'h1)) << ((Bit#(1))'(1'h1)))) : (((Bit#(2))'(2'h1)) <<
        ((Bit#(1))'(1'h1))))}).dir_st, mesi_dir_sharers : (((Struct18 {dir_st
        : (Bit#(3))'(3'h2), dir_excl : (x_14).dir_excl, dir_sharers :
        (((x_14).dir_st) == ((Bit#(3))'(3'h2)) ? (((x_14).dir_sharers) |
        (((Bit#(2))'(2'h1)) << ((Bit#(1))'(1'h1)))) : (((Bit#(2))'(2'h1)) <<
        ((Bit#(1))'(1'h1))))}).dir_st) == ((Bit#(3))'(3'h2)) ? ((Struct18
        {dir_st : (Bit#(3))'(3'h2), dir_excl : (x_14).dir_excl, dir_sharers :
        (((x_14).dir_st) == ((Bit#(3))'(3'h2)) ? (((x_14).dir_sharers) |
        (((Bit#(2))'(2'h1)) << ((Bit#(1))'(1'h1)))) : (((Bit#(2))'(2'h1)) <<
        ((Bit#(1))'(1'h1))))}).dir_sharers) : (((Bit#(2))'(2'h1)) <<
        ((Struct18 {dir_st : (Bit#(3))'(3'h2), dir_excl : (x_14).dir_excl,
        dir_sharers : (((x_14).dir_st) == ((Bit#(3))'(3'h2)) ?
        (((x_14).dir_sharers) | (((Bit#(2))'(2'h1)) << ((Bit#(1))'(1'h1)))) :
        (((Bit#(2))'(2'h1)) << ((Bit#(1))'(1'h1))))}).dir_excl)))},
        value_write : (x_16).value_write, value : (x_16).value, may_victim :
        (x_16).may_victim, reps :
        (x_16).reps});
        let x_20 = ?;
        if ((x_8).valid) begin
            let x_18 <- victims__00__setVictim(Struct20 {victim_idx :
            (x_8).data, victim_info : (x_17).info, victim_value :
            (x_17).value});
            x_20 = x_9;
        end else begin
            let x_19 <- cache__00__valueRsLineRq(x_17);
            x_20 = x_19;
        end
        Struct21 x_21 = (Struct21 {enq_type : ((((Bit#(3))'(3'h5))[2:1]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : (((((Bit#(3))'(3'h5))[2:1])
        == ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : ((Bit#(3))'(3'h5))[0:0], enq_msg : Struct1 {id :
        (Bit#(6))'(6'h3), type_ : (Bool)'(True), addr : (x_15).addr, value :
        x_20}});
        let x_22 <- makeEnq_parentChildren00(x_21);
    endrule

    rule rule_exec_00_001001;
        $display ("Rule fired: rule_exec_00_001001 at %t", $time);
        let x_0 <- deq_fifoL2E_00();
        Struct7 x_1 = ((x_0).lr_ir_pp);
        Bit#(3) x_2 = ((x_1).ir_msg_from);
        Struct1 x_3 = ((x_1).ir_msg);
        Bit#(4) x_4 = ((x_1).ir_mshr_id);
        Bool x_5 = ((x_1).ir_is_rs_rel);
        when (! (x_5), noAction);
        Struct10 x_6 = ((x_0).lr_ir);
        Struct11 x_7 = ((x_6).info);
        Struct6 x_8 = ((x_1).ir_by_victim);
        Vector#(4, Bit#(64)) x_9 = ((x_0).lr_value);
        let x_10 <- getMSHR_00(x_4);
        Vector#(4, Bit#(64)) x_11 = (unpack(0));
        Bool x_12 = ((x_7).mesi_owned);
        Bit#(3) x_13 = ((x_7).mesi_status);
        Struct18 x_14 = (Struct18 {dir_st : (x_7).mesi_dir_st, dir_excl :
        ((((x_7).mesi_dir_sharers)[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(1))'(1'h0)) : (((Bit#(1))'(1'h1)) +
        ((((((x_7).mesi_dir_sharers)[1:1])[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(1))'(1'h0)) : (((Bit#(1))'(1'h1)) + (unpack(0))))))),
        dir_sharers : (x_7).mesi_dir_sharers});
        when ((x_2) == ((Bit#(3))'(3'h1)), noAction);
        when (((x_3).id) == ((Bit#(6))'(6'h2)), noAction);
        when (! ((x_3).type_), noAction);
        when ((! ((x_13) < ((Bit#(3))'(3'h3)))) && (((x_14).dir_st) ==
        ((Bit#(3))'(3'h1))), noAction);
        Struct1 x_15 = (x_3);
        Struct19 x_16 = (Struct19 {addr : (x_3).addr, info_write :
        (Bool)'(False), info_hit : (x_6).info_hit, info_way : (x_6).info_way,
        edir_hit : (x_6).edir_hit, edir_way : (x_6).edir_way, edir_slot :
        (x_6).edir_slot, info : (x_6).info, value_write : (Bool)'(False),
        value : unpack(0), may_victim : (x_6).may_victim, reps :
        (x_6).reps});
        Struct19 x_17 = (Struct19 {addr : (x_16).addr, info_write :
        (Bool)'(True), info_hit : (x_16).info_hit, info_way :
        (x_16).info_way, edir_hit : (x_16).edir_hit, edir_way :
        (x_16).edir_way, edir_slot : (x_16).edir_slot, info : Struct11
        {mesi_owned : ((x_16).info).mesi_owned, mesi_status :
        ((x_16).info).mesi_status, mesi_dir_st : (Struct18 {dir_st :
        (Bit#(3))'(3'h3), dir_excl : (Bit#(1))'(1'h1), dir_sharers :
        unpack(0)}).dir_st, mesi_dir_sharers : (((Struct18 {dir_st :
        (Bit#(3))'(3'h3), dir_excl : (Bit#(1))'(1'h1), dir_sharers :
        unpack(0)}).dir_st) == ((Bit#(3))'(3'h2)) ? ((Struct18 {dir_st :
        (Bit#(3))'(3'h3), dir_excl : (Bit#(1))'(1'h1), dir_sharers :
        unpack(0)}).dir_sharers) : (((Bit#(2))'(2'h1)) << ((Struct18 {dir_st
        : (Bit#(3))'(3'h3), dir_excl : (Bit#(1))'(1'h1), dir_sharers :
        unpack(0)}).dir_excl)))}, value_write : (x_16).value_write, value :
        (x_16).value, may_victim : (x_16).may_victim, reps :
        (x_16).reps});
        Struct19 x_18 = (Struct19 {addr : (x_17).addr, info_write :
        (Bool)'(True), info_hit : (x_17).info_hit, info_way :
        (x_17).info_way, edir_hit : (x_17).edir_hit, edir_way :
        (x_17).edir_way, edir_slot : (x_17).edir_slot, info : Struct11
        {mesi_owned : ((x_17).info).mesi_owned, mesi_status :
        (Bit#(3))'(3'h1), mesi_dir_st : ((x_17).info).mesi_dir_st,
        mesi_dir_sharers : ((x_17).info).mesi_dir_sharers}, value_write :
        (x_17).value_write, value : (x_17).value, may_victim :
        (x_17).may_victim, reps :
        (x_17).reps});
        let x_21 = ?;
        if ((x_8).valid) begin
            let x_19 <- victims__00__setVictim(Struct20 {victim_idx :
            (x_8).data, victim_info : (x_18).info, victim_value :
            (x_18).value});
            x_21 = x_9;
        end else begin
            let x_20 <- cache__00__valueRsLineRq(x_18);
            x_21 = x_20;
        end
        Struct21 x_22 = (Struct21 {enq_type : ((((Bit#(3))'(3'h5))[2:1]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : (((((Bit#(3))'(3'h5))[2:1])
        == ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : ((Bit#(3))'(3'h5))[0:0], enq_msg : Struct1 {id :
        (Bit#(6))'(6'h4), type_ : (Bool)'(True), addr : (x_15).addr, value :
        x_21}});
        let x_23 <- makeEnq_parentChildren00(x_22);
    endrule

    rule rule_exec_00_01001;
        $display ("Rule fired: rule_exec_00_01001 at %t", $time);
        let x_0 <- deq_fifoL2E_00();
        Struct7 x_1 = ((x_0).lr_ir_pp);
        Bit#(3) x_2 = ((x_1).ir_msg_from);
        Struct1 x_3 = ((x_1).ir_msg);
        Bit#(4) x_4 = ((x_1).ir_mshr_id);
        Bool x_5 = ((x_1).ir_is_rs_rel);
        when (! (x_5), noAction);
        Struct10 x_6 = ((x_0).lr_ir);
        Struct11 x_7 = ((x_6).info);
        Struct6 x_8 = ((x_1).ir_by_victim);
        Vector#(4, Bit#(64)) x_9 = ((x_0).lr_value);
        let x_10 <- getMSHR_00(x_4);
        Vector#(4, Bit#(64)) x_11 = (unpack(0));
        Bool x_12 = ((x_7).mesi_owned);
        Bit#(3) x_13 = ((x_7).mesi_status);
        Struct18 x_14 = (Struct18 {dir_st : (x_7).mesi_dir_st, dir_excl :
        ((((x_7).mesi_dir_sharers)[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(1))'(1'h0)) : (((Bit#(1))'(1'h1)) +
        ((((((x_7).mesi_dir_sharers)[1:1])[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(1))'(1'h0)) : (((Bit#(1))'(1'h1)) + (unpack(0))))))),
        dir_sharers : (x_7).mesi_dir_sharers});
        when ((x_2) == ((Bit#(3))'(3'h1)), noAction);
        when (((x_3).id) == ((Bit#(6))'(6'h2)), noAction);
        when (! ((x_3).type_), noAction);
        when (((x_12) == ((Bool)'(False))) && ((! (((Bit#(3))'(3'h1)) <
        (x_13))) && (! (((Bit#(3))'(3'h2)) < ((x_14).dir_st)))),
        noAction);
        Struct1 x_15 = (x_3);
        Struct19 x_16 = (Struct19 {addr : (x_3).addr, info_write :
        (Bool)'(False), info_hit : (x_6).info_hit, info_way : (x_6).info_way,
        edir_hit : (x_6).edir_hit, edir_way : (x_6).edir_way, edir_slot :
        (x_6).edir_slot, info : (x_6).info, value_write : (Bool)'(False),
        value : unpack(0), may_victim : (x_6).may_victim, reps :
        (x_6).reps});
        let x_18 = ?;
        if ((x_8).valid) begin
            x_18 = x_9;
        end else begin
            let x_17 <- cache__00__valueRsLineRq(unpack(0));
            x_18 = x_17;
        end
        let x_19 <- registerUL_00(Struct22 {r_id : x_4, r_ul_rsb :
        (Bool)'(True), r_ul_rsbTo : ((Bit#(3))'(3'h5))[0:0]});
        Struct21 x_20 = (Struct21 {enq_type : ((((Bit#(3))'(3'h0))[2:1]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : (((((Bit#(3))'(3'h0))[2:1])
        == ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : ((Bit#(3))'(3'h0))[0:0], enq_msg : Struct1 {id :
        (Bit#(6))'(6'h2), type_ : (Bool)'(False), addr : (x_15).addr, value :
        unpack(0)}});
        let x_21 <- makeEnq_parentChildren00(x_20);
    endrule

    rule rule_exec_00_03001;
        $display ("Rule fired: rule_exec_00_03001 at %t", $time);
        let x_0 <- deq_fifoL2E_00();
        Struct7 x_1 = ((x_0).lr_ir_pp);
        Bit#(3) x_2 = ((x_1).ir_msg_from);
        Struct1 x_3 = ((x_1).ir_msg);
        Bit#(4) x_4 = ((x_1).ir_mshr_id);
        Bool x_5 = ((x_1).ir_is_rs_rel);
        when (! (x_5), noAction);
        Struct10 x_6 = ((x_0).lr_ir);
        Struct11 x_7 = ((x_6).info);
        Struct6 x_8 = ((x_1).ir_by_victim);
        Vector#(4, Bit#(64)) x_9 = ((x_0).lr_value);
        let x_10 <- getMSHR_00(x_4);
        Vector#(4, Bit#(64)) x_11 = (unpack(0));
        Bool x_12 = ((x_7).mesi_owned);
        Bit#(3) x_13 = ((x_7).mesi_status);
        Struct18 x_14 = (Struct18 {dir_st : (x_7).mesi_dir_st, dir_excl :
        ((((x_7).mesi_dir_sharers)[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(1))'(1'h0)) : (((Bit#(1))'(1'h1)) +
        ((((((x_7).mesi_dir_sharers)[1:1])[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(1))'(1'h0)) : (((Bit#(1))'(1'h1)) + (unpack(0))))))),
        dir_sharers : (x_7).mesi_dir_sharers});
        when ((x_2) == ((Bit#(3))'(3'h1)), noAction);
        when (((x_3).id) == ((Bit#(6))'(6'h2)), noAction);
        when (! ((x_3).type_), noAction);
        when (((Bool)'(True)) && (((Bool)'(True)) && ((! (((Bit#(3))'(3'h1))
        < (x_13))) && ((! (((x_14).dir_st) < ((Bit#(3))'(3'h3)))) && (!
        (((Bit#(3))'(3'h4)) < ((x_14).dir_st)))))), noAction);
        Struct1 x_15 = (x_3);
        Struct19 x_16 = (Struct19 {addr : (x_3).addr, info_write :
        (Bool)'(False), info_hit : (x_6).info_hit, info_way : (x_6).info_way,
        edir_hit : (x_6).edir_hit, edir_way : (x_6).edir_way, edir_slot :
        (x_6).edir_slot, info : (x_6).info, value_write : (Bool)'(False),
        value : unpack(0), may_victim : (x_6).may_victim, reps :
        (x_6).reps});
        let x_18 = ?;
        if ((x_8).valid) begin
            x_18 = x_9;
        end else begin
            let x_17 <- cache__00__valueRsLineRq(unpack(0));
            x_18 = x_17;
        end
        let x_19 <- registerDL_00(Struct23 {r_id : x_4, r_dl_rss_from :
        (unpack(0)) | (((Bit#(2))'(2'h1)) <<
        (({((Bit#(2))'(2'h1)),((x_14).dir_excl)})[0:0])), r_dl_rsb :
        (Bool)'(True), r_dl_rsbTo : (Bit#(3))'(3'h5)});
        Struct21 x_20 = (Struct21 {enq_type :
        ((({((Bit#(2))'(2'h2)),((x_14).dir_excl)})[2:1]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) :
        (((({((Bit#(2))'(2'h2)),((x_14).dir_excl)})[2:1]) ==
        ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : ({((Bit#(2))'(2'h2)),((x_14).dir_excl)})[0:0], enq_msg :
        Struct1 {id : (Bit#(6))'(6'h5), type_ : (Bool)'(False), addr :
        (x_15).addr, value : unpack(0)}});
        let x_21 <- makeEnq_parentChildren00(x_20);
    endrule

    rule rule_exec_00_10001;
        $display ("Rule fired: rule_exec_00_10001 at %t", $time);
        let x_0 <- deq_fifoL2E_00();
        Struct7 x_1 = ((x_0).lr_ir_pp);
        Bit#(3) x_2 = ((x_1).ir_msg_from);
        Struct1 x_3 = ((x_1).ir_msg);
        Bit#(4) x_4 = ((x_1).ir_mshr_id);
        Bool x_5 = ((x_1).ir_is_rs_rel);
        when (! (x_5), noAction);
        Struct10 x_6 = ((x_0).lr_ir);
        Struct11 x_7 = ((x_6).info);
        Struct6 x_8 = ((x_1).ir_by_victim);
        Vector#(4, Bit#(64)) x_9 = ((x_0).lr_value);
        let x_10 <- getMSHR_00(x_4);
        Vector#(4, Bit#(64)) x_11 = (unpack(0));
        Bool x_12 = ((x_7).mesi_owned);
        Bit#(3) x_13 = ((x_7).mesi_status);
        Struct18 x_14 = (Struct18 {dir_st : (x_7).mesi_dir_st, dir_excl :
        ((((x_7).mesi_dir_sharers)[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(1))'(1'h0)) : (((Bit#(1))'(1'h1)) +
        ((((((x_7).mesi_dir_sharers)[1:1])[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(1))'(1'h0)) : (((Bit#(1))'(1'h1)) + (unpack(0))))))),
        dir_sharers : (x_7).mesi_dir_sharers});
        when ((x_2) == ((Bit#(3))'(3'h1)), noAction);
        when (((x_3).id) == ((Bit#(6))'(6'ha)), noAction);
        when (! ((x_3).type_), noAction);
        when ((! ((x_13) < ((Bit#(3))'(3'h3)))) || (((x_13) ==
        ((Bit#(3))'(3'h2))) && (((x_12) == ((Bool)'(True))) &&
        ((((x_14).dir_st) == ((Bit#(3))'(3'h2))) && (((x_14).dir_sharers) ==
        (((Bit#(2))'(2'h1)) << ((Bit#(1))'(1'h1))))))), noAction);
        Struct1 x_15 = (x_3);
        Struct19 x_16 = (Struct19 {addr : (x_3).addr, info_write :
        (Bool)'(False), info_hit : (x_6).info_hit, info_way : (x_6).info_way,
        edir_hit : (x_6).edir_hit, edir_way : (x_6).edir_way, edir_slot :
        (x_6).edir_slot, info : (x_6).info, value_write : (Bool)'(False),
        value : unpack(0), may_victim : (x_6).may_victim, reps :
        (x_6).reps});
        Struct19 x_17 = (Struct19 {addr : (x_16).addr, info_write :
        (Bool)'(True), info_hit : (x_16).info_hit, info_way :
        (x_16).info_way, edir_hit : (x_16).edir_hit, edir_way :
        (x_16).edir_way, edir_slot : (x_16).edir_slot, info : Struct11
        {mesi_owned : ((x_16).info).mesi_owned, mesi_status :
        ((x_16).info).mesi_status, mesi_dir_st : (Struct18 {dir_st :
        (Bit#(3))'(3'h4), dir_excl : (Bit#(1))'(1'h1), dir_sharers :
        unpack(0)}).dir_st, mesi_dir_sharers : (((Struct18 {dir_st :
        (Bit#(3))'(3'h4), dir_excl : (Bit#(1))'(1'h1), dir_sharers :
        unpack(0)}).dir_st) == ((Bit#(3))'(3'h2)) ? ((Struct18 {dir_st :
        (Bit#(3))'(3'h4), dir_excl : (Bit#(1))'(1'h1), dir_sharers :
        unpack(0)}).dir_sharers) : (((Bit#(2))'(2'h1)) << ((Struct18 {dir_st
        : (Bit#(3))'(3'h4), dir_excl : (Bit#(1))'(1'h1), dir_sharers :
        unpack(0)}).dir_excl)))}, value_write : (x_16).value_write, value :
        (x_16).value, may_victim : (x_16).may_victim, reps :
        (x_16).reps});
        Struct19 x_18 = (Struct19 {addr : (x_17).addr, info_write :
        (Bool)'(True), info_hit : (x_17).info_hit, info_way :
        (x_17).info_way, edir_hit : (x_17).edir_hit, edir_way :
        (x_17).edir_way, edir_slot : (x_17).edir_slot, info : Struct11
        {mesi_owned : ((x_17).info).mesi_owned, mesi_status :
        (Bit#(3))'(3'h1), mesi_dir_st : ((x_17).info).mesi_dir_st,
        mesi_dir_sharers : ((x_17).info).mesi_dir_sharers}, value_write :
        (x_17).value_write, value : (x_17).value, may_victim :
        (x_17).may_victim, reps : (x_17).reps});
        Struct19 x_19 = (Struct19 {addr : (x_18).addr, info_write :
        (Bool)'(True), info_hit : (x_18).info_hit, info_way :
        (x_18).info_way, edir_hit : (x_18).edir_hit, edir_way :
        (x_18).edir_way, edir_slot : (x_18).edir_slot, info : Struct11
        {mesi_owned : (Bool)'(False), mesi_status :
        ((x_18).info).mesi_status, mesi_dir_st : ((x_18).info).mesi_dir_st,
        mesi_dir_sharers : ((x_18).info).mesi_dir_sharers}, value_write :
        (x_18).value_write, value : (x_18).value, may_victim :
        (x_18).may_victim, reps :
        (x_18).reps});
        let x_22 = ?;
        if ((x_8).valid) begin
            let x_20 <- victims__00__setVictim(Struct20 {victim_idx :
            (x_8).data, victim_info : (x_19).info, victim_value :
            (x_19).value});
            x_22 = x_9;
        end else begin
            let x_21 <- cache__00__valueRsLineRq(x_19);
            x_22 = x_21;
        end
        Struct21 x_23 = (Struct21 {enq_type : ((((Bit#(3))'(3'h5))[2:1]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : (((((Bit#(3))'(3'h5))[2:1])
        == ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : ((Bit#(3))'(3'h5))[0:0], enq_msg : Struct1 {id :
        (Bit#(6))'(6'hb), type_ : (Bool)'(True), addr : (x_15).addr, value :
        unpack(0)}});
        let x_24 <- makeEnq_parentChildren00(x_23);
    endrule

    rule rule_exec_00_11001;
        $display ("Rule fired: rule_exec_00_11001 at %t", $time);
        let x_0 <- deq_fifoL2E_00();
        Struct7 x_1 = ((x_0).lr_ir_pp);
        Bit#(3) x_2 = ((x_1).ir_msg_from);
        Struct1 x_3 = ((x_1).ir_msg);
        Bit#(4) x_4 = ((x_1).ir_mshr_id);
        Bool x_5 = ((x_1).ir_is_rs_rel);
        when (! (x_5), noAction);
        Struct10 x_6 = ((x_0).lr_ir);
        Struct11 x_7 = ((x_6).info);
        Struct6 x_8 = ((x_1).ir_by_victim);
        Vector#(4, Bit#(64)) x_9 = ((x_0).lr_value);
        let x_10 <- getMSHR_00(x_4);
        Vector#(4, Bit#(64)) x_11 = (unpack(0));
        Bool x_12 = ((x_7).mesi_owned);
        Bit#(3) x_13 = ((x_7).mesi_status);
        Struct18 x_14 = (Struct18 {dir_st : (x_7).mesi_dir_st, dir_excl :
        ((((x_7).mesi_dir_sharers)[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(1))'(1'h0)) : (((Bit#(1))'(1'h1)) +
        ((((((x_7).mesi_dir_sharers)[1:1])[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(1))'(1'h0)) : (((Bit#(1))'(1'h1)) + (unpack(0))))))),
        dir_sharers : (x_7).mesi_dir_sharers});
        when ((x_2) == ((Bit#(3))'(3'h1)), noAction);
        when (((x_3).id) == ((Bit#(6))'(6'ha)), noAction);
        when (! ((x_3).type_), noAction);
        when (((x_12) == ((Bool)'(False))) && ((! (((Bit#(3))'(3'h2)) <
        (x_13))) && (! (((Bit#(3))'(3'h2)) < ((x_14).dir_st)))),
        noAction);
        Struct1 x_15 = (x_3);
        Struct19 x_16 = (Struct19 {addr : (x_3).addr, info_write :
        (Bool)'(False), info_hit : (x_6).info_hit, info_way : (x_6).info_way,
        edir_hit : (x_6).edir_hit, edir_way : (x_6).edir_way, edir_slot :
        (x_6).edir_slot, info : (x_6).info, value_write : (Bool)'(False),
        value : unpack(0), may_victim : (x_6).may_victim, reps :
        (x_6).reps});
        let x_18 = ?;
        if ((x_8).valid) begin
            x_18 = x_9;
        end else begin
            let x_17 <- cache__00__valueRsLineRq(unpack(0));
            x_18 = x_17;
        end
        let x_19 <- registerUL_00(Struct22 {r_id : x_4, r_ul_rsb :
        (Bool)'(True), r_ul_rsbTo : ((Bit#(3))'(3'h5))[0:0]});
        Struct21 x_20 = (Struct21 {enq_type : ((((Bit#(3))'(3'h0))[2:1]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : (((((Bit#(3))'(3'h0))[2:1])
        == ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : ((Bit#(3))'(3'h0))[0:0], enq_msg : Struct1 {id :
        (Bit#(6))'(6'ha), type_ : (Bool)'(False), addr : (x_15).addr, value :
        unpack(0)}});
        let x_21 <- makeEnq_parentChildren00(x_20);
    endrule

    rule rule_exec_00_14001;
        $display ("Rule fired: rule_exec_00_14001 at %t", $time);
        let x_0 <- deq_fifoL2E_00();
        Struct7 x_1 = ((x_0).lr_ir_pp);
        Bit#(3) x_2 = ((x_1).ir_msg_from);
        Struct1 x_3 = ((x_1).ir_msg);
        Bit#(4) x_4 = ((x_1).ir_mshr_id);
        Bool x_5 = ((x_1).ir_is_rs_rel);
        when (! (x_5), noAction);
        Struct10 x_6 = ((x_0).lr_ir);
        Struct11 x_7 = ((x_6).info);
        Struct6 x_8 = ((x_1).ir_by_victim);
        Vector#(4, Bit#(64)) x_9 = ((x_0).lr_value);
        let x_10 <- getMSHR_00(x_4);
        Vector#(4, Bit#(64)) x_11 = (unpack(0));
        Bool x_12 = ((x_7).mesi_owned);
        Bit#(3) x_13 = ((x_7).mesi_status);
        Struct18 x_14 = (Struct18 {dir_st : (x_7).mesi_dir_st, dir_excl :
        ((((x_7).mesi_dir_sharers)[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(1))'(1'h0)) : (((Bit#(1))'(1'h1)) +
        ((((((x_7).mesi_dir_sharers)[1:1])[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(1))'(1'h0)) : (((Bit#(1))'(1'h1)) + (unpack(0))))))),
        dir_sharers : (x_7).mesi_dir_sharers});
        when ((x_2) == ((Bit#(3))'(3'h1)), noAction);
        when (((x_3).id) == ((Bit#(6))'(6'ha)), noAction);
        when (! ((x_3).type_), noAction);
        when (((Bool)'(True)) && (((Bool)'(True)) && ((! (((Bit#(3))'(3'h1))
        < (x_13))) && ((! (((x_14).dir_st) < ((Bit#(3))'(3'h3)))) && (!
        (((Bit#(3))'(3'h4)) < ((x_14).dir_st)))))), noAction);
        Struct1 x_15 = (x_3);
        Struct19 x_16 = (Struct19 {addr : (x_3).addr, info_write :
        (Bool)'(False), info_hit : (x_6).info_hit, info_way : (x_6).info_way,
        edir_hit : (x_6).edir_hit, edir_way : (x_6).edir_way, edir_slot :
        (x_6).edir_slot, info : (x_6).info, value_write : (Bool)'(False),
        value : unpack(0), may_victim : (x_6).may_victim, reps :
        (x_6).reps});
        let x_18 = ?;
        if ((x_8).valid) begin
            x_18 = x_9;
        end else begin
            let x_17 <- cache__00__valueRsLineRq(unpack(0));
            x_18 = x_17;
        end
        let x_19 <- registerDL_00(Struct23 {r_id : x_4, r_dl_rss_from :
        (unpack(0)) | (((Bit#(2))'(2'h1)) <<
        (({((Bit#(2))'(2'h1)),((x_14).dir_excl)})[0:0])), r_dl_rsb :
        (Bool)'(True), r_dl_rsbTo : (Bit#(3))'(3'h5)});
        Struct21 x_20 = (Struct21 {enq_type :
        ((({((Bit#(2))'(2'h2)),((x_14).dir_excl)})[2:1]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) :
        (((({((Bit#(2))'(2'h2)),((x_14).dir_excl)})[2:1]) ==
        ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : ({((Bit#(2))'(2'h2)),((x_14).dir_excl)})[0:0], enq_msg :
        Struct1 {id : (Bit#(6))'(6'he), type_ : (Bool)'(False), addr :
        (x_15).addr, value : unpack(0)}});
        let x_21 <- makeEnq_parentChildren00(x_20);
    endrule

    rule rule_exec_00_15001;
        $display ("Rule fired: rule_exec_00_15001 at %t", $time);
        let x_0 <- deq_fifoL2E_00();
        Struct7 x_1 = ((x_0).lr_ir_pp);
        Bit#(3) x_2 = ((x_1).ir_msg_from);
        Struct1 x_3 = ((x_1).ir_msg);
        Bit#(4) x_4 = ((x_1).ir_mshr_id);
        Bool x_5 = ((x_1).ir_is_rs_rel);
        when (! (x_5), noAction);
        Struct10 x_6 = ((x_0).lr_ir);
        Struct11 x_7 = ((x_6).info);
        Struct6 x_8 = ((x_1).ir_by_victim);
        Vector#(4, Bit#(64)) x_9 = ((x_0).lr_value);
        let x_10 <- getMSHR_00(x_4);
        Vector#(4, Bit#(64)) x_11 = (unpack(0));
        Bool x_12 = ((x_7).mesi_owned);
        Bit#(3) x_13 = ((x_7).mesi_status);
        Struct18 x_14 = (Struct18 {dir_st : (x_7).mesi_dir_st, dir_excl :
        ((((x_7).mesi_dir_sharers)[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(1))'(1'h0)) : (((Bit#(1))'(1'h1)) +
        ((((((x_7).mesi_dir_sharers)[1:1])[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(1))'(1'h0)) : (((Bit#(1))'(1'h1)) + (unpack(0))))))),
        dir_sharers : (x_7).mesi_dir_sharers});
        when ((x_2) == ((Bit#(3))'(3'h1)), noAction);
        when (((x_3).id) == ((Bit#(6))'(6'ha)), noAction);
        when (! ((x_3).type_), noAction);
        when (((Bool)'(True)) && (((Bool)'(True)) && ((!
        ((((x_14).dir_sharers) & (~(((Bit#(2))'(2'h1)) <<
        ((Bit#(1))'(1'h1))))) == ((Bit#(2))'(2'h0)))) && (((x_12) ==
        ((Bool)'(True))) && ((! (((Bit#(3))'(3'h2)) < (x_13))) &&
        (((x_14).dir_st) == ((Bit#(3))'(3'h2))))))), noAction);
        Struct1 x_15 = (x_3);
        Struct19 x_16 = (Struct19 {addr : (x_3).addr, info_write :
        (Bool)'(False), info_hit : (x_6).info_hit, info_way : (x_6).info_way,
        edir_hit : (x_6).edir_hit, edir_way : (x_6).edir_way, edir_slot :
        (x_6).edir_slot, info : (x_6).info, value_write : (Bool)'(False),
        value : unpack(0), may_victim : (x_6).may_victim, reps :
        (x_6).reps});
        let x_18 = ?;
        if ((x_8).valid) begin
            x_18 = x_9;
        end else begin
            let x_17 <- cache__00__valueRsLineRq(unpack(0));
            x_18 = x_17;
        end
        let x_19 <- registerDL_00(Struct23 {r_id : x_4, r_dl_rss_from :
        ((x_14).dir_sharers) & (~(((Bit#(2))'(2'h1)) << ((Bit#(1))'(1'h1)))),
        r_dl_rsb : (Bool)'(True), r_dl_rsbTo : (Bit#(3))'(3'h5)});
        let x_20 <- broadcast_parentChildren00(Struct24 {cs_inds :
        ((x_14).dir_sharers) & (~(((Bit#(2))'(2'h1)) << ((Bit#(1))'(1'h1)))),
        cs_msg : Struct1 {id : (Bit#(6))'(6'hc), type_ : (Bool)'(False), addr
        : (x_15).addr, value : unpack(0)}});
    endrule

    rule rule_exec_00_25001;
        $display ("Rule fired: rule_exec_00_25001 at %t", $time);
        let x_0 <- deq_fifoL2E_00();
        Struct7 x_1 = ((x_0).lr_ir_pp);
        Bit#(3) x_2 = ((x_1).ir_msg_from);
        Struct1 x_3 = ((x_1).ir_msg);
        Bit#(4) x_4 = ((x_1).ir_mshr_id);
        Bool x_5 = ((x_1).ir_is_rs_rel);
        when (! (x_5), noAction);
        Struct10 x_6 = ((x_0).lr_ir);
        Struct11 x_7 = ((x_6).info);
        Struct6 x_8 = ((x_1).ir_by_victim);
        Vector#(4, Bit#(64)) x_9 = ((x_0).lr_value);
        let x_10 <- getMSHR_00(x_4);
        Vector#(4, Bit#(64)) x_11 = (unpack(0));
        Bool x_12 = ((x_7).mesi_owned);
        Bit#(3) x_13 = ((x_7).mesi_status);
        Struct18 x_14 = (Struct18 {dir_st : (x_7).mesi_dir_st, dir_excl :
        ((((x_7).mesi_dir_sharers)[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(1))'(1'h0)) : (((Bit#(1))'(1'h1)) +
        ((((((x_7).mesi_dir_sharers)[1:1])[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(1))'(1'h0)) : (((Bit#(1))'(1'h1)) + (unpack(0))))))),
        dir_sharers : (x_7).mesi_dir_sharers});
        when ((x_2) == ((Bit#(3))'(3'h1)), noAction);
        when (((x_3).id) == ((Bit#(6))'(6'h14)), noAction);
        when (! ((x_3).type_), noAction);
        when ((((((x_14).dir_st) == ((Bit#(3))'(3'h4))) && (((x_14).dir_excl)
        == ((Bit#(1))'(1'h1))) ? ((Bit#(3))'(3'h4)) : (((((x_14).dir_st) ==
        ((Bit#(3))'(3'h3))) && (((x_14).dir_excl) == ((Bit#(1))'(1'h1))) ?
        ((Bit#(3))'(3'h3)) : (((((x_14).dir_st) == ((Bit#(3))'(3'h2))) &&
        ((((x_14).dir_sharers) | (((Bit#(2))'(2'h1)) << ((Bit#(1))'(1'h1))))
        == ((x_14).dir_sharers)) ? ((Bit#(3))'(3'h2)) :
        ((Bit#(3))'(3'h1)))))))) == ((Bit#(3))'(3'h1)), noAction);
        Struct1 x_15 = (x_3);
        Struct19 x_16 = (Struct19 {addr : (x_3).addr, info_write :
        (Bool)'(False), info_hit : (x_6).info_hit, info_way : (x_6).info_way,
        edir_hit : (x_6).edir_hit, edir_way : (x_6).edir_way, edir_slot :
        (x_6).edir_slot, info : (x_6).info, value_write : (Bool)'(False),
        value : unpack(0), may_victim : (x_6).may_victim, reps :
        (x_6).reps});
        let x_18 = ?;
        if ((x_8).valid) begin
            x_18 = x_9;
        end else begin
            let x_17 <- cache__00__valueRsLineRq(unpack(0));
            x_18 = x_17;
        end
        Struct21 x_19 = (Struct21 {enq_type : ((((Bit#(3))'(3'h5))[2:1]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : (((((Bit#(3))'(3'h5))[2:1])
        == ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : ((Bit#(3))'(3'h5))[0:0], enq_msg : Struct1 {id :
        (Bit#(6))'(6'h16), type_ : (Bool)'(True), addr : (x_15).addr, value :
        unpack(0)}});
        let x_20 <- makeEnq_parentChildren00(x_19);
    endrule

    rule rule_exec_00_2600001;
        $display ("Rule fired: rule_exec_00_2600001 at %t", $time);
        let x_0 <- deq_fifoL2E_00();
        Struct7 x_1 = ((x_0).lr_ir_pp);
        Bit#(3) x_2 = ((x_1).ir_msg_from);
        Struct1 x_3 = ((x_1).ir_msg);
        Bit#(4) x_4 = ((x_1).ir_mshr_id);
        Bool x_5 = ((x_1).ir_is_rs_rel);
        when (! (x_5), noAction);
        Struct10 x_6 = ((x_0).lr_ir);
        Struct11 x_7 = ((x_6).info);
        Struct6 x_8 = ((x_1).ir_by_victim);
        Vector#(4, Bit#(64)) x_9 = ((x_0).lr_value);
        let x_10 <- getMSHR_00(x_4);
        Vector#(4, Bit#(64)) x_11 = (unpack(0));
        Bool x_12 = ((x_7).mesi_owned);
        Bit#(3) x_13 = ((x_7).mesi_status);
        Struct18 x_14 = (Struct18 {dir_st : (x_7).mesi_dir_st, dir_excl :
        ((((x_7).mesi_dir_sharers)[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(1))'(1'h0)) : (((Bit#(1))'(1'h1)) +
        ((((((x_7).mesi_dir_sharers)[1:1])[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(1))'(1'h0)) : (((Bit#(1))'(1'h1)) + (unpack(0))))))),
        dir_sharers : (x_7).mesi_dir_sharers});
        when ((x_2) == ((Bit#(3))'(3'h1)), noAction);
        when (((x_3).id) == ((Bit#(6))'(6'h14)), noAction);
        when (! ((x_3).type_), noAction);
        when (((x_12) == ((Bool)'(False))) && (((((((x_14).dir_st) ==
        ((Bit#(3))'(3'h4))) && (((x_14).dir_excl) == ((Bit#(1))'(1'h1))) ?
        ((Bit#(3))'(3'h4)) : (((((x_14).dir_st) == ((Bit#(3))'(3'h3))) &&
        (((x_14).dir_excl) == ((Bit#(1))'(1'h1))) ? ((Bit#(3))'(3'h3)) :
        (((((x_14).dir_st) == ((Bit#(3))'(3'h2))) && ((((x_14).dir_sharers) |
        (((Bit#(2))'(2'h1)) << ((Bit#(1))'(1'h1)))) == ((x_14).dir_sharers))
        ? ((Bit#(3))'(3'h2)) : ((Bit#(3))'(3'h1)))))))) ==
        ((Bit#(3))'(3'h2))) && (((x_14).dir_sharers) == (((Bit#(2))'(2'h1))
        << ((Bit#(1))'(1'h1))))), noAction);
        Struct1 x_15 = (x_3);
        Struct19 x_16 = (Struct19 {addr : (x_3).addr, info_write :
        (Bool)'(False), info_hit : (x_6).info_hit, info_way : (x_6).info_way,
        edir_hit : (x_6).edir_hit, edir_way : (x_6).edir_way, edir_slot :
        (x_6).edir_slot, info : (x_6).info, value_write : (Bool)'(False),
        value : unpack(0), may_victim : (x_6).may_victim, reps :
        (x_6).reps});
        Struct19 x_17 = (Struct19 {addr : (x_16).addr, info_write :
        (Bool)'(True), info_hit : (x_16).info_hit, info_way :
        (x_16).info_way, edir_hit : (x_16).edir_hit, edir_way :
        (x_16).edir_way, edir_slot : (x_16).edir_slot, info : Struct11
        {mesi_owned : ((x_16).info).mesi_owned, mesi_status :
        ((x_16).info).mesi_status, mesi_dir_st : (Struct18 {dir_st :
        (Bit#(3))'(3'h1), dir_excl : unpack(0), dir_sharers :
        unpack(0)}).dir_st, mesi_dir_sharers : (((Struct18 {dir_st :
        (Bit#(3))'(3'h1), dir_excl : unpack(0), dir_sharers :
        unpack(0)}).dir_st) == ((Bit#(3))'(3'h2)) ? ((Struct18 {dir_st :
        (Bit#(3))'(3'h1), dir_excl : unpack(0), dir_sharers :
        unpack(0)}).dir_sharers) : (((Bit#(2))'(2'h1)) << ((Struct18 {dir_st
        : (Bit#(3))'(3'h1), dir_excl : unpack(0), dir_sharers :
        unpack(0)}).dir_excl)))}, value_write : (x_16).value_write, value :
        (x_16).value, may_victim : (x_16).may_victim, reps :
        (x_16).reps});
        let x_20 = ?;
        if ((x_8).valid) begin
            let x_18 <- victims__00__setVictim(Struct20 {victim_idx :
            (x_8).data, victim_info : (x_17).info, victim_value :
            (x_17).value});
            x_20 = x_9;
        end else begin
            let x_19 <- cache__00__valueRsLineRq(x_17);
            x_20 = x_19;
        end
        Struct21 x_21 = (Struct21 {enq_type : ((((Bit#(3))'(3'h5))[2:1]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : (((((Bit#(3))'(3'h5))[2:1])
        == ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : ((Bit#(3))'(3'h5))[0:0], enq_msg : Struct1 {id :
        (Bit#(6))'(6'h16), type_ : (Bool)'(True), addr : (x_15).addr, value :
        unpack(0)}});
        let x_22 <- makeEnq_parentChildren00(x_21);
    endrule

    rule rule_exec_00_2601001;
        $display ("Rule fired: rule_exec_00_2601001 at %t", $time);
        let x_0 <- deq_fifoL2E_00();
        Struct7 x_1 = ((x_0).lr_ir_pp);
        Bit#(3) x_2 = ((x_1).ir_msg_from);
        Struct1 x_3 = ((x_1).ir_msg);
        Bit#(4) x_4 = ((x_1).ir_mshr_id);
        Bool x_5 = ((x_1).ir_is_rs_rel);
        when (! (x_5), noAction);
        Struct10 x_6 = ((x_0).lr_ir);
        Struct11 x_7 = ((x_6).info);
        Struct6 x_8 = ((x_1).ir_by_victim);
        Vector#(4, Bit#(64)) x_9 = ((x_0).lr_value);
        let x_10 <- getMSHR_00(x_4);
        Vector#(4, Bit#(64)) x_11 = (unpack(0));
        Bool x_12 = ((x_7).mesi_owned);
        Bit#(3) x_13 = ((x_7).mesi_status);
        Struct18 x_14 = (Struct18 {dir_st : (x_7).mesi_dir_st, dir_excl :
        ((((x_7).mesi_dir_sharers)[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(1))'(1'h0)) : (((Bit#(1))'(1'h1)) +
        ((((((x_7).mesi_dir_sharers)[1:1])[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(1))'(1'h0)) : (((Bit#(1))'(1'h1)) + (unpack(0))))))),
        dir_sharers : (x_7).mesi_dir_sharers});
        when ((x_2) == ((Bit#(3))'(3'h1)), noAction);
        when (((x_3).id) == ((Bit#(6))'(6'h14)), noAction);
        when (! ((x_3).type_), noAction);
        when (((x_12) == ((Bool)'(True))) && (((x_13) == ((Bit#(3))'(3'h2)))
        && (((((((x_14).dir_st) == ((Bit#(3))'(3'h4))) && (((x_14).dir_excl)
        == ((Bit#(1))'(1'h1))) ? ((Bit#(3))'(3'h4)) : (((((x_14).dir_st) ==
        ((Bit#(3))'(3'h3))) && (((x_14).dir_excl) == ((Bit#(1))'(1'h1))) ?
        ((Bit#(3))'(3'h3)) : (((((x_14).dir_st) == ((Bit#(3))'(3'h2))) &&
        ((((x_14).dir_sharers) | (((Bit#(2))'(2'h1)) << ((Bit#(1))'(1'h1))))
        == ((x_14).dir_sharers)) ? ((Bit#(3))'(3'h2)) :
        ((Bit#(3))'(3'h1)))))))) == ((Bit#(3))'(3'h2))) &&
        (((x_14).dir_sharers) == (((Bit#(2))'(2'h1)) <<
        ((Bit#(1))'(1'h1)))))), noAction);
        Struct1 x_15 = (x_3);
        Struct19 x_16 = (Struct19 {addr : (x_3).addr, info_write :
        (Bool)'(False), info_hit : (x_6).info_hit, info_way : (x_6).info_way,
        edir_hit : (x_6).edir_hit, edir_way : (x_6).edir_way, edir_slot :
        (x_6).edir_slot, info : (x_6).info, value_write : (Bool)'(False),
        value : unpack(0), may_victim : (x_6).may_victim, reps :
        (x_6).reps});
        Struct19 x_17 = (Struct19 {addr : (x_16).addr, info_write :
        (Bool)'(True), info_hit : (x_16).info_hit, info_way :
        (x_16).info_way, edir_hit : (x_16).edir_hit, edir_way :
        (x_16).edir_way, edir_slot : (x_16).edir_slot, info : Struct11
        {mesi_owned : ((x_16).info).mesi_owned, mesi_status :
        ((x_16).info).mesi_status, mesi_dir_st : (Struct18 {dir_st :
        (Bit#(3))'(3'h1), dir_excl : unpack(0), dir_sharers :
        unpack(0)}).dir_st, mesi_dir_sharers : (((Struct18 {dir_st :
        (Bit#(3))'(3'h1), dir_excl : unpack(0), dir_sharers :
        unpack(0)}).dir_st) == ((Bit#(3))'(3'h2)) ? ((Struct18 {dir_st :
        (Bit#(3))'(3'h1), dir_excl : unpack(0), dir_sharers :
        unpack(0)}).dir_sharers) : (((Bit#(2))'(2'h1)) << ((Struct18 {dir_st
        : (Bit#(3))'(3'h1), dir_excl : unpack(0), dir_sharers :
        unpack(0)}).dir_excl)))}, value_write : (x_16).value_write, value :
        (x_16).value, may_victim : (x_16).may_victim, reps :
        (x_16).reps});
        Struct19 x_18 = (Struct19 {addr : (x_17).addr, info_write :
        (Bool)'(True), info_hit : (x_17).info_hit, info_way :
        (x_17).info_way, edir_hit : (x_17).edir_hit, edir_way :
        (x_17).edir_way, edir_slot : (x_17).edir_slot, info : Struct11
        {mesi_owned : ((x_17).info).mesi_owned, mesi_status :
        (Bit#(3))'(3'h4), mesi_dir_st : ((x_17).info).mesi_dir_st,
        mesi_dir_sharers : ((x_17).info).mesi_dir_sharers}, value_write :
        (x_17).value_write, value : (x_17).value, may_victim :
        (x_17).may_victim, reps :
        (x_17).reps});
        let x_21 = ?;
        if ((x_8).valid) begin
            let x_19 <- victims__00__setVictim(Struct20 {victim_idx :
            (x_8).data, victim_info : (x_18).info, victim_value :
            (x_18).value});
            x_21 = x_9;
        end else begin
            let x_20 <- cache__00__valueRsLineRq(x_18);
            x_21 = x_20;
        end
        Struct21 x_22 = (Struct21 {enq_type : ((((Bit#(3))'(3'h5))[2:1]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : (((((Bit#(3))'(3'h5))[2:1])
        == ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : ((Bit#(3))'(3'h5))[0:0], enq_msg : Struct1 {id :
        (Bit#(6))'(6'h16), type_ : (Bool)'(True), addr : (x_15).addr, value :
        unpack(0)}});
        let x_23 <- makeEnq_parentChildren00(x_22);
    endrule

    rule rule_exec_00_261001;
        $display ("Rule fired: rule_exec_00_261001 at %t", $time);
        let x_0 <- deq_fifoL2E_00();
        Struct7 x_1 = ((x_0).lr_ir_pp);
        Bit#(3) x_2 = ((x_1).ir_msg_from);
        Struct1 x_3 = ((x_1).ir_msg);
        Bit#(4) x_4 = ((x_1).ir_mshr_id);
        Bool x_5 = ((x_1).ir_is_rs_rel);
        when (! (x_5), noAction);
        Struct10 x_6 = ((x_0).lr_ir);
        Struct11 x_7 = ((x_6).info);
        Struct6 x_8 = ((x_1).ir_by_victim);
        Vector#(4, Bit#(64)) x_9 = ((x_0).lr_value);
        let x_10 <- getMSHR_00(x_4);
        Vector#(4, Bit#(64)) x_11 = (unpack(0));
        Bool x_12 = ((x_7).mesi_owned);
        Bit#(3) x_13 = ((x_7).mesi_status);
        Struct18 x_14 = (Struct18 {dir_st : (x_7).mesi_dir_st, dir_excl :
        ((((x_7).mesi_dir_sharers)[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(1))'(1'h0)) : (((Bit#(1))'(1'h1)) +
        ((((((x_7).mesi_dir_sharers)[1:1])[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(1))'(1'h0)) : (((Bit#(1))'(1'h1)) + (unpack(0))))))),
        dir_sharers : (x_7).mesi_dir_sharers});
        when ((x_2) == ((Bit#(3))'(3'h1)), noAction);
        when (((x_3).id) == ((Bit#(6))'(6'h14)), noAction);
        when (! ((x_3).type_), noAction);
        when (((((((x_14).dir_st) == ((Bit#(3))'(3'h4))) &&
        (((x_14).dir_excl) == ((Bit#(1))'(1'h1))) ? ((Bit#(3))'(3'h4)) :
        (((((x_14).dir_st) == ((Bit#(3))'(3'h3))) && (((x_14).dir_excl) ==
        ((Bit#(1))'(1'h1))) ? ((Bit#(3))'(3'h3)) : (((((x_14).dir_st) ==
        ((Bit#(3))'(3'h2))) && ((((x_14).dir_sharers) | (((Bit#(2))'(2'h1))
        << ((Bit#(1))'(1'h1)))) == ((x_14).dir_sharers)) ? ((Bit#(3))'(3'h2))
        : ((Bit#(3))'(3'h1)))))))) == ((Bit#(3))'(3'h2))) &&
        (((Bit#(2))'(2'h1)) < ((((((x_14).dir_sharers)[0:0]) ==
        ((Bit#(1))'(1'h1)) ? ((Bit#(2))'(2'h1)) : ((Bit#(2))'(2'h0)))) +
        (((((((x_14).dir_sharers)[1:1])[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(2))'(2'h1)) : ((Bit#(2))'(2'h0)))) + (unpack(0))))),
        noAction);
        Struct1 x_15 = (x_3);
        Struct19 x_16 = (Struct19 {addr : (x_3).addr, info_write :
        (Bool)'(False), info_hit : (x_6).info_hit, info_way : (x_6).info_way,
        edir_hit : (x_6).edir_hit, edir_way : (x_6).edir_way, edir_slot :
        (x_6).edir_slot, info : (x_6).info, value_write : (Bool)'(False),
        value : unpack(0), may_victim : (x_6).may_victim, reps :
        (x_6).reps});
        Struct19 x_17 = (Struct19 {addr : (x_16).addr, info_write :
        (Bool)'(True), info_hit : (x_16).info_hit, info_way :
        (x_16).info_way, edir_hit : (x_16).edir_hit, edir_way :
        (x_16).edir_way, edir_slot : (x_16).edir_slot, info : Struct11
        {mesi_owned : ((x_16).info).mesi_owned, mesi_status :
        ((x_16).info).mesi_status, mesi_dir_st : (Struct18 {dir_st :
        (Bit#(3))'(3'h2), dir_excl : (x_14).dir_excl, dir_sharers :
        ((x_14).dir_sharers) & (~(((Bit#(2))'(2'h1)) <<
        ((Bit#(1))'(1'h1))))}).dir_st, mesi_dir_sharers : (((Struct18 {dir_st
        : (Bit#(3))'(3'h2), dir_excl : (x_14).dir_excl, dir_sharers :
        ((x_14).dir_sharers) & (~(((Bit#(2))'(2'h1)) <<
        ((Bit#(1))'(1'h1))))}).dir_st) == ((Bit#(3))'(3'h2)) ? ((Struct18
        {dir_st : (Bit#(3))'(3'h2), dir_excl : (x_14).dir_excl, dir_sharers :
        ((x_14).dir_sharers) & (~(((Bit#(2))'(2'h1)) <<
        ((Bit#(1))'(1'h1))))}).dir_sharers) : (((Bit#(2))'(2'h1)) <<
        ((Struct18 {dir_st : (Bit#(3))'(3'h2), dir_excl : (x_14).dir_excl,
        dir_sharers : ((x_14).dir_sharers) & (~(((Bit#(2))'(2'h1)) <<
        ((Bit#(1))'(1'h1))))}).dir_excl)))}, value_write :
        (x_16).value_write, value : (x_16).value, may_victim :
        (x_16).may_victim, reps :
        (x_16).reps});
        let x_20 = ?;
        if ((x_8).valid) begin
            let x_18 <- victims__00__setVictim(Struct20 {victim_idx :
            (x_8).data, victim_info : (x_17).info, victim_value :
            (x_17).value});
            x_20 = x_9;
        end else begin
            let x_19 <- cache__00__valueRsLineRq(x_17);
            x_20 = x_19;
        end
        Struct21 x_21 = (Struct21 {enq_type : ((((Bit#(3))'(3'h5))[2:1]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : (((((Bit#(3))'(3'h5))[2:1])
        == ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : ((Bit#(3))'(3'h5))[0:0], enq_msg : Struct1 {id :
        (Bit#(6))'(6'h16), type_ : (Bool)'(True), addr : (x_15).addr, value :
        unpack(0)}});
        let x_22 <- makeEnq_parentChildren00(x_21);
    endrule

    rule rule_exec_00_27001;
        $display ("Rule fired: rule_exec_00_27001 at %t", $time);
        let x_0 <- deq_fifoL2E_00();
        Struct7 x_1 = ((x_0).lr_ir_pp);
        Bit#(3) x_2 = ((x_1).ir_msg_from);
        Struct1 x_3 = ((x_1).ir_msg);
        Bit#(4) x_4 = ((x_1).ir_mshr_id);
        Bool x_5 = ((x_1).ir_is_rs_rel);
        when (! (x_5), noAction);
        Struct10 x_6 = ((x_0).lr_ir);
        Struct11 x_7 = ((x_6).info);
        Struct6 x_8 = ((x_1).ir_by_victim);
        Vector#(4, Bit#(64)) x_9 = ((x_0).lr_value);
        let x_10 <- getMSHR_00(x_4);
        Vector#(4, Bit#(64)) x_11 = (unpack(0));
        Bool x_12 = ((x_7).mesi_owned);
        Bit#(3) x_13 = ((x_7).mesi_status);
        Struct18 x_14 = (Struct18 {dir_st : (x_7).mesi_dir_st, dir_excl :
        ((((x_7).mesi_dir_sharers)[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(1))'(1'h0)) : (((Bit#(1))'(1'h1)) +
        ((((((x_7).mesi_dir_sharers)[1:1])[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(1))'(1'h0)) : (((Bit#(1))'(1'h1)) + (unpack(0))))))),
        dir_sharers : (x_7).mesi_dir_sharers});
        when ((x_2) == ((Bit#(3))'(3'h1)), noAction);
        when (((x_3).id) == ((Bit#(6))'(6'h14)), noAction);
        when (! ((x_3).type_), noAction);
        when ((((((x_14).dir_st) == ((Bit#(3))'(3'h4))) && (((x_14).dir_excl)
        == ((Bit#(1))'(1'h1))) ? ((Bit#(3))'(3'h4)) : (((((x_14).dir_st) ==
        ((Bit#(3))'(3'h3))) && (((x_14).dir_excl) == ((Bit#(1))'(1'h1))) ?
        ((Bit#(3))'(3'h3)) : (((((x_14).dir_st) == ((Bit#(3))'(3'h2))) &&
        ((((x_14).dir_sharers) | (((Bit#(2))'(2'h1)) << ((Bit#(1))'(1'h1))))
        == ((x_14).dir_sharers)) ? ((Bit#(3))'(3'h2)) :
        ((Bit#(3))'(3'h1)))))))) == ((Bit#(3))'(3'h3)), noAction);
        Struct1 x_15 = (x_3);
        Struct19 x_16 = (Struct19 {addr : (x_3).addr, info_write :
        (Bool)'(False), info_hit : (x_6).info_hit, info_way : (x_6).info_way,
        edir_hit : (x_6).edir_hit, edir_way : (x_6).edir_way, edir_slot :
        (x_6).edir_slot, info : (x_6).info, value_write : (Bool)'(False),
        value : unpack(0), may_victim : (x_6).may_victim, reps :
        (x_6).reps});
        Struct19 x_17 = (Struct19 {addr : (x_16).addr, info_write :
        (Bool)'(True), info_hit : (x_16).info_hit, info_way :
        (x_16).info_way, edir_hit : (x_16).edir_hit, edir_way :
        (x_16).edir_way, edir_slot : (x_16).edir_slot, info : Struct11
        {mesi_owned : ((x_16).info).mesi_owned, mesi_status :
        ((x_16).info).mesi_status, mesi_dir_st : (Struct18 {dir_st :
        (Bit#(3))'(3'h1), dir_excl : unpack(0), dir_sharers :
        unpack(0)}).dir_st, mesi_dir_sharers : (((Struct18 {dir_st :
        (Bit#(3))'(3'h1), dir_excl : unpack(0), dir_sharers :
        unpack(0)}).dir_st) == ((Bit#(3))'(3'h2)) ? ((Struct18 {dir_st :
        (Bit#(3))'(3'h1), dir_excl : unpack(0), dir_sharers :
        unpack(0)}).dir_sharers) : (((Bit#(2))'(2'h1)) << ((Struct18 {dir_st
        : (Bit#(3))'(3'h1), dir_excl : unpack(0), dir_sharers :
        unpack(0)}).dir_excl)))}, value_write : (x_16).value_write, value :
        (x_16).value, may_victim : (x_16).may_victim, reps :
        (x_16).reps});
        Struct19 x_18 = (Struct19 {addr : (x_17).addr, info_write :
        (Bool)'(True), info_hit : (x_17).info_hit, info_way :
        (x_17).info_way, edir_hit : (x_17).edir_hit, edir_way :
        (x_17).edir_way, edir_slot : (x_17).edir_slot, info : Struct11
        {mesi_owned : ((x_17).info).mesi_owned, mesi_status :
        (Bit#(3))'(3'h3), mesi_dir_st : ((x_17).info).mesi_dir_st,
        mesi_dir_sharers : ((x_17).info).mesi_dir_sharers}, value_write :
        (x_17).value_write, value : (x_17).value, may_victim :
        (x_17).may_victim, reps :
        (x_17).reps});
        let x_21 = ?;
        if ((x_8).valid) begin
            let x_19 <- victims__00__setVictim(Struct20 {victim_idx :
            (x_8).data, victim_info : (x_18).info, victim_value :
            (x_18).value});
            x_21 = x_9;
        end else begin
            let x_20 <- cache__00__valueRsLineRq(x_18);
            x_21 = x_20;
        end
        Struct21 x_22 = (Struct21 {enq_type : ((((Bit#(3))'(3'h5))[2:1]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : (((((Bit#(3))'(3'h5))[2:1])
        == ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : ((Bit#(3))'(3'h5))[0:0], enq_msg : Struct1 {id :
        (Bit#(6))'(6'h16), type_ : (Bool)'(True), addr : (x_15).addr, value :
        unpack(0)}});
        let x_23 <- makeEnq_parentChildren00(x_22);
    endrule

    rule rule_exec_00_28001;
        $display ("Rule fired: rule_exec_00_28001 at %t", $time);
        let x_0 <- deq_fifoL2E_00();
        Struct7 x_1 = ((x_0).lr_ir_pp);
        Bit#(3) x_2 = ((x_1).ir_msg_from);
        Struct1 x_3 = ((x_1).ir_msg);
        Bit#(4) x_4 = ((x_1).ir_mshr_id);
        Bool x_5 = ((x_1).ir_is_rs_rel);
        when (! (x_5), noAction);
        Struct10 x_6 = ((x_0).lr_ir);
        Struct11 x_7 = ((x_6).info);
        Struct6 x_8 = ((x_1).ir_by_victim);
        Vector#(4, Bit#(64)) x_9 = ((x_0).lr_value);
        let x_10 <- getMSHR_00(x_4);
        Vector#(4, Bit#(64)) x_11 = (unpack(0));
        Bool x_12 = ((x_7).mesi_owned);
        Bit#(3) x_13 = ((x_7).mesi_status);
        Struct18 x_14 = (Struct18 {dir_st : (x_7).mesi_dir_st, dir_excl :
        ((((x_7).mesi_dir_sharers)[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(1))'(1'h0)) : (((Bit#(1))'(1'h1)) +
        ((((((x_7).mesi_dir_sharers)[1:1])[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(1))'(1'h0)) : (((Bit#(1))'(1'h1)) + (unpack(0))))))),
        dir_sharers : (x_7).mesi_dir_sharers});
        when ((x_2) == ((Bit#(3))'(3'h1)), noAction);
        when (((x_3).id) == ((Bit#(6))'(6'h15)), noAction);
        when (! ((x_3).type_), noAction);
        when ((((((x_14).dir_st) == ((Bit#(3))'(3'h4))) && (((x_14).dir_excl)
        == ((Bit#(1))'(1'h1))) ? ((Bit#(3))'(3'h4)) : (((((x_14).dir_st) ==
        ((Bit#(3))'(3'h3))) && (((x_14).dir_excl) == ((Bit#(1))'(1'h1))) ?
        ((Bit#(3))'(3'h3)) : (((((x_14).dir_st) == ((Bit#(3))'(3'h2))) &&
        ((((x_14).dir_sharers) | (((Bit#(2))'(2'h1)) << ((Bit#(1))'(1'h1))))
        == ((x_14).dir_sharers)) ? ((Bit#(3))'(3'h2)) :
        ((Bit#(3))'(3'h1)))))))) == ((Bit#(3))'(3'h1)), noAction);
        Struct1 x_15 = (x_3);
        Struct19 x_16 = (Struct19 {addr : (x_3).addr, info_write :
        (Bool)'(False), info_hit : (x_6).info_hit, info_way : (x_6).info_way,
        edir_hit : (x_6).edir_hit, edir_way : (x_6).edir_way, edir_slot :
        (x_6).edir_slot, info : (x_6).info, value_write : (Bool)'(False),
        value : unpack(0), may_victim : (x_6).may_victim, reps :
        (x_6).reps});
        let x_18 = ?;
        if ((x_8).valid) begin
            x_18 = x_9;
        end else begin
            let x_17 <- cache__00__valueRsLineRq(unpack(0));
            x_18 = x_17;
        end
        Struct21 x_19 = (Struct21 {enq_type : ((((Bit#(3))'(3'h5))[2:1]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : (((((Bit#(3))'(3'h5))[2:1])
        == ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : ((Bit#(3))'(3'h5))[0:0], enq_msg : Struct1 {id :
        (Bit#(6))'(6'h16), type_ : (Bool)'(True), addr : (x_15).addr, value :
        unpack(0)}});
        let x_20 <- makeEnq_parentChildren00(x_19);
    endrule

    rule rule_exec_00_290001;
        $display ("Rule fired: rule_exec_00_290001 at %t", $time);
        let x_0 <- deq_fifoL2E_00();
        Struct7 x_1 = ((x_0).lr_ir_pp);
        Bit#(3) x_2 = ((x_1).ir_msg_from);
        Struct1 x_3 = ((x_1).ir_msg);
        Bit#(4) x_4 = ((x_1).ir_mshr_id);
        Bool x_5 = ((x_1).ir_is_rs_rel);
        when (! (x_5), noAction);
        Struct10 x_6 = ((x_0).lr_ir);
        Struct11 x_7 = ((x_6).info);
        Struct6 x_8 = ((x_1).ir_by_victim);
        Vector#(4, Bit#(64)) x_9 = ((x_0).lr_value);
        let x_10 <- getMSHR_00(x_4);
        Vector#(4, Bit#(64)) x_11 = (unpack(0));
        Bool x_12 = ((x_7).mesi_owned);
        Bit#(3) x_13 = ((x_7).mesi_status);
        Struct18 x_14 = (Struct18 {dir_st : (x_7).mesi_dir_st, dir_excl :
        ((((x_7).mesi_dir_sharers)[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(1))'(1'h0)) : (((Bit#(1))'(1'h1)) +
        ((((((x_7).mesi_dir_sharers)[1:1])[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(1))'(1'h0)) : (((Bit#(1))'(1'h1)) + (unpack(0))))))),
        dir_sharers : (x_7).mesi_dir_sharers});
        when ((x_2) == ((Bit#(3))'(3'h1)), noAction);
        when (((x_3).id) == ((Bit#(6))'(6'h15)), noAction);
        when (! ((x_3).type_), noAction);
        when (((x_12) == ((Bool)'(False))) && (((((((x_14).dir_st) ==
        ((Bit#(3))'(3'h4))) && (((x_14).dir_excl) == ((Bit#(1))'(1'h1))) ?
        ((Bit#(3))'(3'h4)) : (((((x_14).dir_st) == ((Bit#(3))'(3'h3))) &&
        (((x_14).dir_excl) == ((Bit#(1))'(1'h1))) ? ((Bit#(3))'(3'h3)) :
        (((((x_14).dir_st) == ((Bit#(3))'(3'h2))) && ((((x_14).dir_sharers) |
        (((Bit#(2))'(2'h1)) << ((Bit#(1))'(1'h1)))) == ((x_14).dir_sharers))
        ? ((Bit#(3))'(3'h2)) : ((Bit#(3))'(3'h1)))))))) ==
        ((Bit#(3))'(3'h2))) && (((x_14).dir_sharers) == (((Bit#(2))'(2'h1))
        << ((Bit#(1))'(1'h1))))), noAction);
        Struct1 x_15 = (x_3);
        Struct19 x_16 = (Struct19 {addr : (x_3).addr, info_write :
        (Bool)'(False), info_hit : (x_6).info_hit, info_way : (x_6).info_way,
        edir_hit : (x_6).edir_hit, edir_way : (x_6).edir_way, edir_slot :
        (x_6).edir_slot, info : (x_6).info, value_write : (Bool)'(False),
        value : unpack(0), may_victim : (x_6).may_victim, reps :
        (x_6).reps});
        Struct19 x_17 = (Struct19 {addr : (x_16).addr, info_write :
        (Bool)'(True), info_hit : (x_16).info_hit, info_way :
        (x_16).info_way, edir_hit : (x_16).edir_hit, edir_way :
        (x_16).edir_way, edir_slot : (x_16).edir_slot, info : Struct11
        {mesi_owned : ((x_16).info).mesi_owned, mesi_status :
        ((x_16).info).mesi_status, mesi_dir_st : (Struct18 {dir_st :
        (Bit#(3))'(3'h1), dir_excl : unpack(0), dir_sharers :
        unpack(0)}).dir_st, mesi_dir_sharers : (((Struct18 {dir_st :
        (Bit#(3))'(3'h1), dir_excl : unpack(0), dir_sharers :
        unpack(0)}).dir_st) == ((Bit#(3))'(3'h2)) ? ((Struct18 {dir_st :
        (Bit#(3))'(3'h1), dir_excl : unpack(0), dir_sharers :
        unpack(0)}).dir_sharers) : (((Bit#(2))'(2'h1)) << ((Struct18 {dir_st
        : (Bit#(3))'(3'h1), dir_excl : unpack(0), dir_sharers :
        unpack(0)}).dir_excl)))}, value_write : (x_16).value_write, value :
        (x_16).value, may_victim : (x_16).may_victim, reps :
        (x_16).reps});
        let x_20 = ?;
        if ((x_8).valid) begin
            let x_18 <- victims__00__setVictim(Struct20 {victim_idx :
            (x_8).data, victim_info : (x_17).info, victim_value :
            (x_17).value});
            x_20 = x_9;
        end else begin
            let x_19 <- cache__00__valueRsLineRq(x_17);
            x_20 = x_19;
        end
        Struct21 x_21 = (Struct21 {enq_type : ((((Bit#(3))'(3'h5))[2:1]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : (((((Bit#(3))'(3'h5))[2:1])
        == ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : ((Bit#(3))'(3'h5))[0:0], enq_msg : Struct1 {id :
        (Bit#(6))'(6'h16), type_ : (Bool)'(True), addr : (x_15).addr, value :
        unpack(0)}});
        let x_22 <- makeEnq_parentChildren00(x_21);
    endrule

    rule rule_exec_00_291001;
        $display ("Rule fired: rule_exec_00_291001 at %t", $time);
        let x_0 <- deq_fifoL2E_00();
        Struct7 x_1 = ((x_0).lr_ir_pp);
        Bit#(3) x_2 = ((x_1).ir_msg_from);
        Struct1 x_3 = ((x_1).ir_msg);
        Bit#(4) x_4 = ((x_1).ir_mshr_id);
        Bool x_5 = ((x_1).ir_is_rs_rel);
        when (! (x_5), noAction);
        Struct10 x_6 = ((x_0).lr_ir);
        Struct11 x_7 = ((x_6).info);
        Struct6 x_8 = ((x_1).ir_by_victim);
        Vector#(4, Bit#(64)) x_9 = ((x_0).lr_value);
        let x_10 <- getMSHR_00(x_4);
        Vector#(4, Bit#(64)) x_11 = (unpack(0));
        Bool x_12 = ((x_7).mesi_owned);
        Bit#(3) x_13 = ((x_7).mesi_status);
        Struct18 x_14 = (Struct18 {dir_st : (x_7).mesi_dir_st, dir_excl :
        ((((x_7).mesi_dir_sharers)[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(1))'(1'h0)) : (((Bit#(1))'(1'h1)) +
        ((((((x_7).mesi_dir_sharers)[1:1])[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(1))'(1'h0)) : (((Bit#(1))'(1'h1)) + (unpack(0))))))),
        dir_sharers : (x_7).mesi_dir_sharers});
        when ((x_2) == ((Bit#(3))'(3'h1)), noAction);
        when (((x_3).id) == ((Bit#(6))'(6'h15)), noAction);
        when (! ((x_3).type_), noAction);
        when (((((((x_14).dir_st) == ((Bit#(3))'(3'h4))) &&
        (((x_14).dir_excl) == ((Bit#(1))'(1'h1))) ? ((Bit#(3))'(3'h4)) :
        (((((x_14).dir_st) == ((Bit#(3))'(3'h3))) && (((x_14).dir_excl) ==
        ((Bit#(1))'(1'h1))) ? ((Bit#(3))'(3'h3)) : (((((x_14).dir_st) ==
        ((Bit#(3))'(3'h2))) && ((((x_14).dir_sharers) | (((Bit#(2))'(2'h1))
        << ((Bit#(1))'(1'h1)))) == ((x_14).dir_sharers)) ? ((Bit#(3))'(3'h2))
        : ((Bit#(3))'(3'h1)))))))) == ((Bit#(3))'(3'h2))) &&
        (((Bit#(2))'(2'h1)) < ((((((x_14).dir_sharers)[0:0]) ==
        ((Bit#(1))'(1'h1)) ? ((Bit#(2))'(2'h1)) : ((Bit#(2))'(2'h0)))) +
        (((((((x_14).dir_sharers)[1:1])[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(2))'(2'h1)) : ((Bit#(2))'(2'h0)))) + (unpack(0))))),
        noAction);
        Struct1 x_15 = (x_3);
        Struct19 x_16 = (Struct19 {addr : (x_3).addr, info_write :
        (Bool)'(False), info_hit : (x_6).info_hit, info_way : (x_6).info_way,
        edir_hit : (x_6).edir_hit, edir_way : (x_6).edir_way, edir_slot :
        (x_6).edir_slot, info : (x_6).info, value_write : (Bool)'(False),
        value : unpack(0), may_victim : (x_6).may_victim, reps :
        (x_6).reps});
        Struct19 x_17 = (Struct19 {addr : (x_16).addr, info_write :
        (Bool)'(True), info_hit : (x_16).info_hit, info_way :
        (x_16).info_way, edir_hit : (x_16).edir_hit, edir_way :
        (x_16).edir_way, edir_slot : (x_16).edir_slot, info : Struct11
        {mesi_owned : ((x_16).info).mesi_owned, mesi_status :
        ((x_16).info).mesi_status, mesi_dir_st : (Struct18 {dir_st :
        (Bit#(3))'(3'h2), dir_excl : (x_14).dir_excl, dir_sharers :
        ((x_14).dir_sharers) & (~(((Bit#(2))'(2'h1)) <<
        ((Bit#(1))'(1'h1))))}).dir_st, mesi_dir_sharers : (((Struct18 {dir_st
        : (Bit#(3))'(3'h2), dir_excl : (x_14).dir_excl, dir_sharers :
        ((x_14).dir_sharers) & (~(((Bit#(2))'(2'h1)) <<
        ((Bit#(1))'(1'h1))))}).dir_st) == ((Bit#(3))'(3'h2)) ? ((Struct18
        {dir_st : (Bit#(3))'(3'h2), dir_excl : (x_14).dir_excl, dir_sharers :
        ((x_14).dir_sharers) & (~(((Bit#(2))'(2'h1)) <<
        ((Bit#(1))'(1'h1))))}).dir_sharers) : (((Bit#(2))'(2'h1)) <<
        ((Struct18 {dir_st : (Bit#(3))'(3'h2), dir_excl : (x_14).dir_excl,
        dir_sharers : ((x_14).dir_sharers) & (~(((Bit#(2))'(2'h1)) <<
        ((Bit#(1))'(1'h1))))}).dir_excl)))}, value_write :
        (x_16).value_write, value : (x_16).value, may_victim :
        (x_16).may_victim, reps :
        (x_16).reps});
        let x_20 = ?;
        if ((x_8).valid) begin
            let x_18 <- victims__00__setVictim(Struct20 {victim_idx :
            (x_8).data, victim_info : (x_17).info, victim_value :
            (x_17).value});
            x_20 = x_9;
        end else begin
            let x_19 <- cache__00__valueRsLineRq(x_17);
            x_20 = x_19;
        end
        Struct21 x_21 = (Struct21 {enq_type : ((((Bit#(3))'(3'h5))[2:1]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : (((((Bit#(3))'(3'h5))[2:1])
        == ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : ((Bit#(3))'(3'h5))[0:0], enq_msg : Struct1 {id :
        (Bit#(6))'(6'h16), type_ : (Bool)'(True), addr : (x_15).addr, value :
        unpack(0)}});
        let x_22 <- makeEnq_parentChildren00(x_21);
    endrule

    rule rule_exec_00_210001;
        $display ("Rule fired: rule_exec_00_210001 at %t", $time);
        let x_0 <- deq_fifoL2E_00();
        Struct7 x_1 = ((x_0).lr_ir_pp);
        Bit#(3) x_2 = ((x_1).ir_msg_from);
        Struct1 x_3 = ((x_1).ir_msg);
        Bit#(4) x_4 = ((x_1).ir_mshr_id);
        Bool x_5 = ((x_1).ir_is_rs_rel);
        when (! (x_5), noAction);
        Struct10 x_6 = ((x_0).lr_ir);
        Struct11 x_7 = ((x_6).info);
        Struct6 x_8 = ((x_1).ir_by_victim);
        Vector#(4, Bit#(64)) x_9 = ((x_0).lr_value);
        let x_10 <- getMSHR_00(x_4);
        Vector#(4, Bit#(64)) x_11 = (unpack(0));
        Bool x_12 = ((x_7).mesi_owned);
        Bit#(3) x_13 = ((x_7).mesi_status);
        Struct18 x_14 = (Struct18 {dir_st : (x_7).mesi_dir_st, dir_excl :
        ((((x_7).mesi_dir_sharers)[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(1))'(1'h0)) : (((Bit#(1))'(1'h1)) +
        ((((((x_7).mesi_dir_sharers)[1:1])[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(1))'(1'h0)) : (((Bit#(1))'(1'h1)) + (unpack(0))))))),
        dir_sharers : (x_7).mesi_dir_sharers});
        when ((x_2) == ((Bit#(3))'(3'h1)), noAction);
        when (((x_3).id) == ((Bit#(6))'(6'h15)), noAction);
        when (! ((x_3).type_), noAction);
        when (((x_12) == ((Bool)'(True))) && (((x_13) == ((Bit#(3))'(3'h2)))
        && (((((((x_14).dir_st) == ((Bit#(3))'(3'h4))) && (((x_14).dir_excl)
        == ((Bit#(1))'(1'h1))) ? ((Bit#(3))'(3'h4)) : (((((x_14).dir_st) ==
        ((Bit#(3))'(3'h3))) && (((x_14).dir_excl) == ((Bit#(1))'(1'h1))) ?
        ((Bit#(3))'(3'h3)) : (((((x_14).dir_st) == ((Bit#(3))'(3'h2))) &&
        ((((x_14).dir_sharers) | (((Bit#(2))'(2'h1)) << ((Bit#(1))'(1'h1))))
        == ((x_14).dir_sharers)) ? ((Bit#(3))'(3'h2)) :
        ((Bit#(3))'(3'h1)))))))) == ((Bit#(3))'(3'h2))) &&
        (((x_14).dir_sharers) == (((Bit#(2))'(2'h1)) <<
        ((Bit#(1))'(1'h1)))))), noAction);
        Struct1 x_15 = (x_3);
        Struct19 x_16 = (Struct19 {addr : (x_3).addr, info_write :
        (Bool)'(False), info_hit : (x_6).info_hit, info_way : (x_6).info_way,
        edir_hit : (x_6).edir_hit, edir_way : (x_6).edir_way, edir_slot :
        (x_6).edir_slot, info : (x_6).info, value_write : (Bool)'(False),
        value : unpack(0), may_victim : (x_6).may_victim, reps :
        (x_6).reps});
        Struct19 x_17 = (Struct19 {addr : (x_16).addr, info_write :
        (Bool)'(True), info_hit : (x_16).info_hit, info_way :
        (x_16).info_way, edir_hit : (x_16).edir_hit, edir_way :
        (x_16).edir_way, edir_slot : (x_16).edir_slot, info : Struct11
        {mesi_owned : ((x_16).info).mesi_owned, mesi_status :
        ((x_16).info).mesi_status, mesi_dir_st : (Struct18 {dir_st :
        (Bit#(3))'(3'h1), dir_excl : unpack(0), dir_sharers :
        unpack(0)}).dir_st, mesi_dir_sharers : (((Struct18 {dir_st :
        (Bit#(3))'(3'h1), dir_excl : unpack(0), dir_sharers :
        unpack(0)}).dir_st) == ((Bit#(3))'(3'h2)) ? ((Struct18 {dir_st :
        (Bit#(3))'(3'h1), dir_excl : unpack(0), dir_sharers :
        unpack(0)}).dir_sharers) : (((Bit#(2))'(2'h1)) << ((Struct18 {dir_st
        : (Bit#(3))'(3'h1), dir_excl : unpack(0), dir_sharers :
        unpack(0)}).dir_excl)))}, value_write : (x_16).value_write, value :
        (x_16).value, may_victim : (x_16).may_victim, reps :
        (x_16).reps});
        Struct19 x_18 = (Struct19 {addr : (x_17).addr, info_write :
        (Bool)'(True), info_hit : (x_17).info_hit, info_way :
        (x_17).info_way, edir_hit : (x_17).edir_hit, edir_way :
        (x_17).edir_way, edir_slot : (x_17).edir_slot, info : Struct11
        {mesi_owned : ((x_17).info).mesi_owned, mesi_status :
        (Bit#(3))'(3'h4), mesi_dir_st : ((x_17).info).mesi_dir_st,
        mesi_dir_sharers : ((x_17).info).mesi_dir_sharers}, value_write :
        (x_17).value_write, value : (x_17).value, may_victim :
        (x_17).may_victim, reps :
        (x_17).reps});
        let x_21 = ?;
        if ((x_8).valid) begin
            let x_19 <- victims__00__setVictim(Struct20 {victim_idx :
            (x_8).data, victim_info : (x_18).info, victim_value :
            (x_18).value});
            x_21 = x_9;
        end else begin
            let x_20 <- cache__00__valueRsLineRq(x_18);
            x_21 = x_20;
        end
        Struct21 x_22 = (Struct21 {enq_type : ((((Bit#(3))'(3'h5))[2:1]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : (((((Bit#(3))'(3'h5))[2:1])
        == ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : ((Bit#(3))'(3'h5))[0:0], enq_msg : Struct1 {id :
        (Bit#(6))'(6'h16), type_ : (Bool)'(True), addr : (x_15).addr, value :
        unpack(0)}});
        let x_23 <- makeEnq_parentChildren00(x_22);
    endrule

    rule rule_exec_00_211001;
        $display ("Rule fired: rule_exec_00_211001 at %t", $time);
        let x_0 <- deq_fifoL2E_00();
        Struct7 x_1 = ((x_0).lr_ir_pp);
        Bit#(3) x_2 = ((x_1).ir_msg_from);
        Struct1 x_3 = ((x_1).ir_msg);
        Bit#(4) x_4 = ((x_1).ir_mshr_id);
        Bool x_5 = ((x_1).ir_is_rs_rel);
        when (! (x_5), noAction);
        Struct10 x_6 = ((x_0).lr_ir);
        Struct11 x_7 = ((x_6).info);
        Struct6 x_8 = ((x_1).ir_by_victim);
        Vector#(4, Bit#(64)) x_9 = ((x_0).lr_value);
        let x_10 <- getMSHR_00(x_4);
        Vector#(4, Bit#(64)) x_11 = (unpack(0));
        Bool x_12 = ((x_7).mesi_owned);
        Bit#(3) x_13 = ((x_7).mesi_status);
        Struct18 x_14 = (Struct18 {dir_st : (x_7).mesi_dir_st, dir_excl :
        ((((x_7).mesi_dir_sharers)[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(1))'(1'h0)) : (((Bit#(1))'(1'h1)) +
        ((((((x_7).mesi_dir_sharers)[1:1])[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(1))'(1'h0)) : (((Bit#(1))'(1'h1)) + (unpack(0))))))),
        dir_sharers : (x_7).mesi_dir_sharers});
        when ((x_2) == ((Bit#(3))'(3'h1)), noAction);
        when (((x_3).id) == ((Bit#(6))'(6'h15)), noAction);
        when (! ((x_3).type_), noAction);
        when (! ((((((x_14).dir_st) == ((Bit#(3))'(3'h4))) &&
        (((x_14).dir_excl) == ((Bit#(1))'(1'h1))) ? ((Bit#(3))'(3'h4)) :
        (((((x_14).dir_st) == ((Bit#(3))'(3'h3))) && (((x_14).dir_excl) ==
        ((Bit#(1))'(1'h1))) ? ((Bit#(3))'(3'h3)) : (((((x_14).dir_st) ==
        ((Bit#(3))'(3'h2))) && ((((x_14).dir_sharers) | (((Bit#(2))'(2'h1))
        << ((Bit#(1))'(1'h1)))) == ((x_14).dir_sharers)) ? ((Bit#(3))'(3'h2))
        : ((Bit#(3))'(3'h1)))))))) < ((Bit#(3))'(3'h3))), noAction);
        Struct1 x_15 = (x_3);
        Struct19 x_16 = (Struct19 {addr : (x_3).addr, info_write :
        (Bool)'(False), info_hit : (x_6).info_hit, info_way : (x_6).info_way,
        edir_hit : (x_6).edir_hit, edir_way : (x_6).edir_way, edir_slot :
        (x_6).edir_slot, info : (x_6).info, value_write : (Bool)'(False),
        value : unpack(0), may_victim : (x_6).may_victim, reps :
        (x_6).reps});
        Struct19 x_17 = (Struct19 {addr : (x_16).addr, info_write :
        (x_16).info_write, info_hit : (x_16).info_hit, info_way :
        (x_16).info_way, edir_hit : (x_16).edir_hit, edir_way :
        (x_16).edir_way, edir_slot : (x_16).edir_slot, info : (x_16).info,
        value_write : (Bool)'(True), value : (x_15).value, may_victim :
        (x_16).may_victim, reps : (x_16).reps});
        Struct19 x_18 = (Struct19 {addr : (x_17).addr, info_write :
        (Bool)'(True), info_hit : (x_17).info_hit, info_way :
        (x_17).info_way, edir_hit : (x_17).edir_hit, edir_way :
        (x_17).edir_way, edir_slot : (x_17).edir_slot, info : Struct11
        {mesi_owned : ((x_17).info).mesi_owned, mesi_status :
        (Bit#(3))'(3'h4), mesi_dir_st : ((x_17).info).mesi_dir_st,
        mesi_dir_sharers : ((x_17).info).mesi_dir_sharers}, value_write :
        (x_17).value_write, value : (x_17).value, may_victim :
        (x_17).may_victim, reps : (x_17).reps});
        Struct19 x_19 = (Struct19 {addr : (x_18).addr, info_write :
        (Bool)'(True), info_hit : (x_18).info_hit, info_way :
        (x_18).info_way, edir_hit : (x_18).edir_hit, edir_way :
        (x_18).edir_way, edir_slot : (x_18).edir_slot, info : Struct11
        {mesi_owned : (Bool)'(True), mesi_status : ((x_18).info).mesi_status,
        mesi_dir_st : ((x_18).info).mesi_dir_st, mesi_dir_sharers :
        ((x_18).info).mesi_dir_sharers}, value_write : (x_18).value_write,
        value : (x_18).value, may_victim : (x_18).may_victim, reps :
        (x_18).reps});
        Struct19 x_20 = (Struct19 {addr : (x_19).addr, info_write :
        (Bool)'(True), info_hit : (x_19).info_hit, info_way :
        (x_19).info_way, edir_hit : (x_19).edir_hit, edir_way :
        (x_19).edir_way, edir_slot : (x_19).edir_slot, info : Struct11
        {mesi_owned : ((x_19).info).mesi_owned, mesi_status :
        ((x_19).info).mesi_status, mesi_dir_st : (Struct18 {dir_st :
        (Bit#(3))'(3'h1), dir_excl : unpack(0), dir_sharers :
        unpack(0)}).dir_st, mesi_dir_sharers : (((Struct18 {dir_st :
        (Bit#(3))'(3'h1), dir_excl : unpack(0), dir_sharers :
        unpack(0)}).dir_st) == ((Bit#(3))'(3'h2)) ? ((Struct18 {dir_st :
        (Bit#(3))'(3'h1), dir_excl : unpack(0), dir_sharers :
        unpack(0)}).dir_sharers) : (((Bit#(2))'(2'h1)) << ((Struct18 {dir_st
        : (Bit#(3))'(3'h1), dir_excl : unpack(0), dir_sharers :
        unpack(0)}).dir_excl)))}, value_write : (x_19).value_write, value :
        (x_19).value, may_victim : (x_19).may_victim, reps :
        (x_19).reps});
        let x_23 = ?;
        if ((x_8).valid) begin
            let x_21 <- victims__00__setVictim(Struct20 {victim_idx :
            (x_8).data, victim_info : (x_20).info, victim_value :
            (x_20).value});
            x_23 = x_9;
        end else begin
            let x_22 <- cache__00__valueRsLineRq(x_20);
            x_23 = x_22;
        end
        Struct21 x_24 = (Struct21 {enq_type : ((((Bit#(3))'(3'h5))[2:1]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : (((((Bit#(3))'(3'h5))[2:1])
        == ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : ((Bit#(3))'(3'h5))[0:0], enq_msg : Struct1 {id :
        (Bit#(6))'(6'h16), type_ : (Bool)'(True), addr : (x_15).addr, value :
        unpack(0)}});
        let x_25 <- makeEnq_parentChildren00(x_24);
    endrule

    rule rule_exec_00_020;
        $display ("Rule fired: rule_exec_00_020 at %t", $time);
        let x_0 <- deq_fifoL2E_00();
        Struct7 x_1 = ((x_0).lr_ir_pp);
        Bit#(3) x_2 = ((x_1).ir_msg_from);
        Struct1 x_3 = ((x_1).ir_msg);
        Bit#(4) x_4 = ((x_1).ir_mshr_id);
        Bool x_5 = ((x_1).ir_is_rs_rel);
        when (! (x_5), noAction);
        Struct10 x_6 = ((x_0).lr_ir);
        Struct11 x_7 = ((x_6).info);
        Struct6 x_8 = ((x_1).ir_by_victim);
        Vector#(4, Bit#(64)) x_9 = ((x_0).lr_value);
        let x_10 <- getMSHR_00(x_4);
        Vector#(4, Bit#(64)) x_11 = (unpack(0));
        Bool x_12 = ((x_7).mesi_owned);
        Bit#(3) x_13 = ((x_7).mesi_status);
        Struct18 x_14 = (Struct18 {dir_st : (x_7).mesi_dir_st, dir_excl :
        ((((x_7).mesi_dir_sharers)[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(1))'(1'h0)) : (((Bit#(1))'(1'h1)) +
        ((((((x_7).mesi_dir_sharers)[1:1])[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(1))'(1'h0)) : (((Bit#(1))'(1'h1)) + (unpack(0))))))),
        dir_sharers : (x_7).mesi_dir_sharers});
        when ((x_2) == ({((Bit#(2))'(2'h2)),((Bit#(1))'(1'h0))}),
        noAction);
        when (((x_3).id) == ((Bit#(6))'(6'h3)), noAction);
        when (((x_10).m_status) == ((Bit#(3))'(3'h4)), noAction);
        when ((x_10).m_rsb, noAction);
        when ((((x_10).m_msg).type_) == ((Bool)'(False)), noAction);
        when ((((x_10).m_msg).id) == ((Bit#(6))'(6'h2)), noAction);
        when (((x_10).m_status) == ((Bit#(3))'(3'h4)), noAction);
        when ((x_10).m_rsb, noAction);
        when ((x_3).type_, noAction);
        when ((Bool)'(True), noAction);
        Struct1 x_15 = (x_3);
        Struct1 x_16 = ((x_10).m_msg);
        Bit#(3) x_17 = ({((Bit#(2))'(2'h2)),(((x_10).m_qidx)[0:0])});
        Struct19 x_18 = (Struct19 {addr : (x_3).addr, info_write :
        (Bool)'(False), info_hit : (x_6).info_hit, info_way : (x_6).info_way,
        edir_hit : (x_6).edir_hit, edir_way : (x_6).edir_way, edir_slot :
        (x_6).edir_slot, info : (x_6).info, value_write : (Bool)'(False),
        value : unpack(0), may_victim : (x_6).may_victim, reps :
        (x_6).reps});
        Struct19 x_19 = (Struct19 {addr : (x_18).addr, info_write :
        (Bool)'(True), info_hit : (x_18).info_hit, info_way :
        (x_18).info_way, edir_hit : (x_18).edir_hit, edir_way :
        (x_18).edir_way, edir_slot : (x_18).edir_slot, info : Struct11
        {mesi_owned : ((x_18).info).mesi_owned, mesi_status :
        ((x_18).info).mesi_status, mesi_dir_st : (Struct18 {dir_st :
        (Bit#(3))'(3'h2), dir_excl : (x_14).dir_excl, dir_sharers :
        (((x_14).dir_st) == ((Bit#(3))'(3'h2)) ? (((x_14).dir_sharers) |
        (((Bit#(2))'(2'h1)) << ((x_17)[0:0]))) : (((Bit#(2))'(2'h1)) <<
        ((x_17)[0:0])))}).dir_st, mesi_dir_sharers : (((Struct18 {dir_st :
        (Bit#(3))'(3'h2), dir_excl : (x_14).dir_excl, dir_sharers :
        (((x_14).dir_st) == ((Bit#(3))'(3'h2)) ? (((x_14).dir_sharers) |
        (((Bit#(2))'(2'h1)) << ((x_17)[0:0]))) : (((Bit#(2))'(2'h1)) <<
        ((x_17)[0:0])))}).dir_st) == ((Bit#(3))'(3'h2)) ? ((Struct18 {dir_st
        : (Bit#(3))'(3'h2), dir_excl : (x_14).dir_excl, dir_sharers :
        (((x_14).dir_st) == ((Bit#(3))'(3'h2)) ? (((x_14).dir_sharers) |
        (((Bit#(2))'(2'h1)) << ((x_17)[0:0]))) : (((Bit#(2))'(2'h1)) <<
        ((x_17)[0:0])))}).dir_sharers) : (((Bit#(2))'(2'h1)) << ((Struct18
        {dir_st : (Bit#(3))'(3'h2), dir_excl : (x_14).dir_excl, dir_sharers :
        (((x_14).dir_st) == ((Bit#(3))'(3'h2)) ? (((x_14).dir_sharers) |
        (((Bit#(2))'(2'h1)) << ((x_17)[0:0]))) : (((Bit#(2))'(2'h1)) <<
        ((x_17)[0:0])))}).dir_excl)))}, value_write : (x_18).value_write,
        value : (x_18).value, may_victim : (x_18).may_victim, reps :
        (x_18).reps});
        Struct19 x_20 = (Struct19 {addr : (x_19).addr, info_write :
        (Bool)'(True), info_hit : (x_19).info_hit, info_way :
        (x_19).info_way, edir_hit : (x_19).edir_hit, edir_way :
        (x_19).edir_way, edir_slot : (x_19).edir_slot, info : Struct11
        {mesi_owned : ((x_19).info).mesi_owned, mesi_status :
        (Bit#(3))'(3'h2), mesi_dir_st : ((x_19).info).mesi_dir_st,
        mesi_dir_sharers : ((x_19).info).mesi_dir_sharers}, value_write :
        (x_19).value_write, value : (x_19).value, may_victim :
        (x_19).may_victim, reps : (x_19).reps});
        Struct19 x_21 = (Struct19 {addr : (x_20).addr, info_write :
        (Bool)'(True), info_hit : (x_20).info_hit, info_way :
        (x_20).info_way, edir_hit : (x_20).edir_hit, edir_way :
        (x_20).edir_way, edir_slot : (x_20).edir_slot, info : Struct11
        {mesi_owned : (Bool)'(False), mesi_status :
        ((x_20).info).mesi_status, mesi_dir_st : ((x_20).info).mesi_dir_st,
        mesi_dir_sharers : ((x_20).info).mesi_dir_sharers}, value_write :
        (x_20).value_write, value : (x_20).value, may_victim :
        (x_20).may_victim, reps : (x_20).reps});
        Struct19 x_22 = (Struct19 {addr : (x_21).addr, info_write :
        (x_21).info_write, info_hit : (x_21).info_hit, info_way :
        (x_21).info_way, edir_hit : (x_21).edir_hit, edir_way :
        (x_21).edir_way, edir_slot : (x_21).edir_slot, info : (x_21).info,
        value_write : (Bool)'(True), value : (x_15).value, may_victim :
        (x_21).may_victim, reps :
        (x_21).reps});
        let x_25 = ?;
        if ((x_8).valid) begin
            let x_23 <- victims__00__setVictim(Struct20 {victim_idx :
            (x_8).data, victim_info : (x_22).info, victim_value :
            (x_22).value});
            x_25 = x_9;
        end else begin
            let x_24 <- cache__00__valueRsLineRq(x_22);
            x_25 = x_24;
        end
        let x_26 <- releaseMSHR_00(x_4);
        Struct21 x_27 = (Struct21 {enq_type : (((x_17)[2:1]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : ((((x_17)[2:1]) ==
        ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : (x_17)[0:0], enq_msg : Struct1 {id : (Bit#(6))'(6'h3),
        type_ : (Bool)'(True), addr : (x_15).addr, value :
        (x_15).value}});
        let x_28 <- makeEnq_parentChildren00(x_27);
    endrule

    rule rule_exec_00_021;
        $display ("Rule fired: rule_exec_00_021 at %t", $time);
        let x_0 <- deq_fifoL2E_00();
        Struct7 x_1 = ((x_0).lr_ir_pp);
        Bit#(3) x_2 = ((x_1).ir_msg_from);
        Struct1 x_3 = ((x_1).ir_msg);
        Bit#(4) x_4 = ((x_1).ir_mshr_id);
        Bool x_5 = ((x_1).ir_is_rs_rel);
        when (! (x_5), noAction);
        Struct10 x_6 = ((x_0).lr_ir);
        Struct11 x_7 = ((x_6).info);
        Struct6 x_8 = ((x_1).ir_by_victim);
        Vector#(4, Bit#(64)) x_9 = ((x_0).lr_value);
        let x_10 <- getMSHR_00(x_4);
        Vector#(4, Bit#(64)) x_11 = (unpack(0));
        Bool x_12 = ((x_7).mesi_owned);
        Bit#(3) x_13 = ((x_7).mesi_status);
        Struct18 x_14 = (Struct18 {dir_st : (x_7).mesi_dir_st, dir_excl :
        ((((x_7).mesi_dir_sharers)[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(1))'(1'h0)) : (((Bit#(1))'(1'h1)) +
        ((((((x_7).mesi_dir_sharers)[1:1])[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(1))'(1'h0)) : (((Bit#(1))'(1'h1)) + (unpack(0))))))),
        dir_sharers : (x_7).mesi_dir_sharers});
        when ((x_2) == ({((Bit#(2))'(2'h2)),((Bit#(1))'(1'h0))}),
        noAction);
        when (((x_3).id) == ((Bit#(6))'(6'h4)), noAction);
        when (((x_10).m_status) == ((Bit#(3))'(3'h4)), noAction);
        when ((x_10).m_rsb, noAction);
        when ((((x_10).m_msg).type_) == ((Bool)'(False)), noAction);
        when ((((x_10).m_msg).id) == ((Bit#(6))'(6'h2)), noAction);
        when (((x_10).m_status) == ((Bit#(3))'(3'h4)), noAction);
        when ((x_10).m_rsb, noAction);
        when ((x_3).type_, noAction);
        when ((Bool)'(True), noAction);
        Struct1 x_15 = (x_3);
        Struct1 x_16 = ((x_10).m_msg);
        Bit#(3) x_17 = ({((Bit#(2))'(2'h2)),(((x_10).m_qidx)[0:0])});
        Struct19 x_18 = (Struct19 {addr : (x_3).addr, info_write :
        (Bool)'(False), info_hit : (x_6).info_hit, info_way : (x_6).info_way,
        edir_hit : (x_6).edir_hit, edir_way : (x_6).edir_way, edir_slot :
        (x_6).edir_slot, info : (x_6).info, value_write : (Bool)'(False),
        value : unpack(0), may_victim : (x_6).may_victim, reps :
        (x_6).reps});
        Struct19 x_19 = (Struct19 {addr : (x_18).addr, info_write :
        (Bool)'(True), info_hit : (x_18).info_hit, info_way :
        (x_18).info_way, edir_hit : (x_18).edir_hit, edir_way :
        (x_18).edir_way, edir_slot : (x_18).edir_slot, info : Struct11
        {mesi_owned : ((x_18).info).mesi_owned, mesi_status :
        ((x_18).info).mesi_status, mesi_dir_st : (Struct18 {dir_st :
        (Bit#(3))'(3'h3), dir_excl : (x_17)[0:0], dir_sharers :
        unpack(0)}).dir_st, mesi_dir_sharers : (((Struct18 {dir_st :
        (Bit#(3))'(3'h3), dir_excl : (x_17)[0:0], dir_sharers :
        unpack(0)}).dir_st) == ((Bit#(3))'(3'h2)) ? ((Struct18 {dir_st :
        (Bit#(3))'(3'h3), dir_excl : (x_17)[0:0], dir_sharers :
        unpack(0)}).dir_sharers) : (((Bit#(2))'(2'h1)) << ((Struct18 {dir_st
        : (Bit#(3))'(3'h3), dir_excl : (x_17)[0:0], dir_sharers :
        unpack(0)}).dir_excl)))}, value_write : (x_18).value_write, value :
        (x_18).value, may_victim : (x_18).may_victim, reps :
        (x_18).reps});
        Struct19 x_20 = (Struct19 {addr : (x_19).addr, info_write :
        (Bool)'(True), info_hit : (x_19).info_hit, info_way :
        (x_19).info_way, edir_hit : (x_19).edir_hit, edir_way :
        (x_19).edir_way, edir_slot : (x_19).edir_slot, info : Struct11
        {mesi_owned : ((x_19).info).mesi_owned, mesi_status :
        (Bit#(3))'(3'h1), mesi_dir_st : ((x_19).info).mesi_dir_st,
        mesi_dir_sharers : ((x_19).info).mesi_dir_sharers}, value_write :
        (x_19).value_write, value : (x_19).value, may_victim :
        (x_19).may_victim, reps : (x_19).reps});
        Struct19 x_21 = (Struct19 {addr : (x_20).addr, info_write :
        (Bool)'(True), info_hit : (x_20).info_hit, info_way :
        (x_20).info_way, edir_hit : (x_20).edir_hit, edir_way :
        (x_20).edir_way, edir_slot : (x_20).edir_slot, info : Struct11
        {mesi_owned : (Bool)'(False), mesi_status :
        ((x_20).info).mesi_status, mesi_dir_st : ((x_20).info).mesi_dir_st,
        mesi_dir_sharers : ((x_20).info).mesi_dir_sharers}, value_write :
        (x_20).value_write, value : (x_20).value, may_victim :
        (x_20).may_victim, reps : (x_20).reps});
        Struct19 x_22 = (Struct19 {addr : (x_21).addr, info_write :
        (x_21).info_write, info_hit : (x_21).info_hit, info_way :
        (x_21).info_way, edir_hit : (x_21).edir_hit, edir_way :
        (x_21).edir_way, edir_slot : (x_21).edir_slot, info : (x_21).info,
        value_write : (Bool)'(True), value : (x_15).value, may_victim :
        (x_21).may_victim, reps :
        (x_21).reps});
        let x_25 = ?;
        if ((x_8).valid) begin
            let x_23 <- victims__00__setVictim(Struct20 {victim_idx :
            (x_8).data, victim_info : (x_22).info, victim_value :
            (x_22).value});
            x_25 = x_9;
        end else begin
            let x_24 <- cache__00__valueRsLineRq(x_22);
            x_25 = x_24;
        end
        let x_26 <- releaseMSHR_00(x_4);
        Struct21 x_27 = (Struct21 {enq_type : (((x_17)[2:1]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : ((((x_17)[2:1]) ==
        ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : (x_17)[0:0], enq_msg : Struct1 {id : (Bit#(6))'(6'h4),
        type_ : (Bool)'(True), addr : (x_15).addr, value :
        (x_15).value}});
        let x_28 <- makeEnq_parentChildren00(x_27);
    endrule

    rule rule_exec_00_041;
        $display ("Rule fired: rule_exec_00_041 at %t", $time);
        let x_0 <- deq_fifoL2E_00();
        Struct7 x_1 = ((x_0).lr_ir_pp);
        Bit#(3) x_2 = ((x_1).ir_msg_from);
        Struct1 x_3 = ((x_1).ir_msg);
        Bit#(4) x_4 = ((x_1).ir_mshr_id);
        Bool x_5 = ((x_1).ir_is_rs_rel);
        when (x_5, noAction);
        Struct10 x_6 = ((x_0).lr_ir);
        Struct11 x_7 = ((x_6).info);
        Struct6 x_8 = ((x_1).ir_by_victim);
        Vector#(4, Bit#(64)) x_9 = ((x_0).lr_value);
        let x_10 <- getMSHR_00(x_4);
        Vector#(4, Bit#(64)) x_11 = (unpack(0));
        Bool x_12 = ((x_7).mesi_owned);
        Bit#(3) x_13 = ((x_7).mesi_status);
        Struct18 x_14 = (Struct18 {dir_st : (x_7).mesi_dir_st, dir_excl :
        ((((x_7).mesi_dir_sharers)[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(1))'(1'h0)) : (((Bit#(1))'(1'h1)) +
        ((((((x_7).mesi_dir_sharers)[1:1])[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(1))'(1'h0)) : (((Bit#(1))'(1'h1)) + (unpack(0))))))),
        dir_sharers : (x_7).mesi_dir_sharers});
        when (((x_10).m_status) == ((Bit#(3))'(3'h4)), noAction);
        when ((x_10).m_rsb, noAction);
        when ((((x_10).m_msg).type_) == ((Bool)'(False)), noAction);
        when ((((x_10).m_msg).id) == ((Bit#(6))'(6'h2)), noAction);
        when (((x_10).m_dl_rss) == ((x_10).m_dl_rss), noAction);
        when ((Bool)'(True), noAction);
        Struct25 x_15 = (Struct25 {cidx :
        {((Bit#(2))'(2'h1)),(((((x_10).m_dl_rss_from)[0:0]) ==
        ((Bit#(1))'(1'h1)) ? ((Bit#(1))'(1'h0)) : (((Bit#(1))'(1'h1)) +
        ((((((x_10).m_dl_rss_from)[1:1])[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(1))'(1'h0)) : (((Bit#(1))'(1'h1)) + (unpack(0))))))))}, msg :
        ((x_10).m_dl_rss)[((((x_10).m_dl_rss_from)[0:0]) ==
        ((Bit#(1))'(1'h1)) ? ((Bit#(1))'(1'h0)) : (((Bit#(1))'(1'h1)) +
        ((((((x_10).m_dl_rss_from)[1:1])[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(1))'(1'h0)) : (((Bit#(1))'(1'h1)) +
        (unpack(0)))))))]});
        Struct1 x_16 = ((x_10).m_msg);
        Bit#(3) x_17 = ((x_10).m_qidx);
        Struct19 x_18 = (Struct19 {addr : (x_3).addr, info_write :
        (Bool)'(False), info_hit : (x_6).info_hit, info_way : (x_6).info_way,
        edir_hit : (x_6).edir_hit, edir_way : (x_6).edir_way, edir_slot :
        (x_6).edir_slot, info : (x_6).info, value_write : (Bool)'(False),
        value : unpack(0), may_victim : (x_6).may_victim, reps :
        (x_6).reps});
        Struct19 x_19 = (Struct19 {addr : (x_18).addr, info_write :
        (Bool)'(True), info_hit : (x_18).info_hit, info_way :
        (x_18).info_way, edir_hit : (x_18).edir_hit, edir_way :
        (x_18).edir_way, edir_slot : (x_18).edir_slot, info : Struct11
        {mesi_owned : ((x_18).info).mesi_owned, mesi_status :
        ((x_18).info).mesi_status, mesi_dir_st : (Struct18 {dir_st :
        (Bit#(3))'(3'h2), dir_excl : unpack(0), dir_sharers : ((unpack(0)) |
        (((Bit#(2))'(2'h1)) << ((x_17)[0:0]))) | (((Bit#(2))'(2'h1)) <<
        (((x_15).cidx)[0:0]))}).dir_st, mesi_dir_sharers : (((Struct18
        {dir_st : (Bit#(3))'(3'h2), dir_excl : unpack(0), dir_sharers :
        ((unpack(0)) | (((Bit#(2))'(2'h1)) << ((x_17)[0:0]))) |
        (((Bit#(2))'(2'h1)) << (((x_15).cidx)[0:0]))}).dir_st) ==
        ((Bit#(3))'(3'h2)) ? ((Struct18 {dir_st : (Bit#(3))'(3'h2), dir_excl
        : unpack(0), dir_sharers : ((unpack(0)) | (((Bit#(2))'(2'h1)) <<
        ((x_17)[0:0]))) | (((Bit#(2))'(2'h1)) <<
        (((x_15).cidx)[0:0]))}).dir_sharers) : (((Bit#(2))'(2'h1)) <<
        ((Struct18 {dir_st : (Bit#(3))'(3'h2), dir_excl : unpack(0),
        dir_sharers : ((unpack(0)) | (((Bit#(2))'(2'h1)) << ((x_17)[0:0]))) |
        (((Bit#(2))'(2'h1)) << (((x_15).cidx)[0:0]))}).dir_excl)))},
        value_write : (x_18).value_write, value : (x_18).value, may_victim :
        (x_18).may_victim, reps : (x_18).reps});
        Struct19 x_20 = (Struct19 {addr : (x_19).addr, info_write :
        (Bool)'(True), info_hit : (x_19).info_hit, info_way :
        (x_19).info_way, edir_hit : (x_19).edir_hit, edir_way :
        (x_19).edir_way, edir_slot : (x_19).edir_slot, info : Struct11
        {mesi_owned : ((x_19).info).mesi_owned, mesi_status :
        (Bit#(3))'(3'h2), mesi_dir_st : ((x_19).info).mesi_dir_st,
        mesi_dir_sharers : ((x_19).info).mesi_dir_sharers}, value_write :
        (x_19).value_write, value : (x_19).value, may_victim :
        (x_19).may_victim, reps : (x_19).reps});
        Struct19 x_21 = (Struct19 {addr : (x_20).addr, info_write :
        (x_20).info_write, info_hit : (x_20).info_hit, info_way :
        (x_20).info_way, edir_hit : (x_20).edir_hit, edir_way :
        (x_20).edir_way, edir_slot : (x_20).edir_slot, info : (x_20).info,
        value_write : (Bool)'(True), value : ((x_15).msg).value, may_victim :
        (x_20).may_victim, reps : (x_20).reps});
        Struct19 x_22 = (Struct19 {addr : (x_21).addr, info_write :
        (Bool)'(True), info_hit : (x_21).info_hit, info_way :
        (x_21).info_way, edir_hit : (x_21).edir_hit, edir_way :
        (x_21).edir_way, edir_slot : (x_21).edir_slot, info : Struct11
        {mesi_owned : (Bool)'(True), mesi_status : ((x_21).info).mesi_status,
        mesi_dir_st : ((x_21).info).mesi_dir_st, mesi_dir_sharers :
        ((x_21).info).mesi_dir_sharers}, value_write : (x_21).value_write,
        value : (x_21).value, may_victim : (x_21).may_victim, reps :
        (x_21).reps});
        let x_25 = ?;
        if ((x_8).valid) begin
            let x_23 <- victims__00__setVictim(Struct20 {victim_idx :
            (x_8).data, victim_info : (x_22).info, victim_value :
            (x_22).value});
            x_25 = x_9;
        end else begin
            let x_24 <- cache__00__valueRsLineRq(x_22);
            x_25 = x_24;
        end
        let x_26 <- releaseMSHR_00(x_4);
        Struct21 x_27 = (Struct21 {enq_type : (((x_17)[2:1]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : ((((x_17)[2:1]) ==
        ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : (x_17)[0:0], enq_msg : Struct1 {id : (Bit#(6))'(6'h3),
        type_ : (Bool)'(True), addr : (x_16).addr, value :
        ((x_15).msg).value}});
        let x_28 <- makeEnq_parentChildren00(x_27);
    endrule

    rule rule_exec_00_05;
        $display ("Rule fired: rule_exec_00_05 at %t", $time);
        let x_0 <- deq_fifoL2E_00();
        Struct7 x_1 = ((x_0).lr_ir_pp);
        Bit#(3) x_2 = ((x_1).ir_msg_from);
        Struct1 x_3 = ((x_1).ir_msg);
        Bit#(4) x_4 = ((x_1).ir_mshr_id);
        Bool x_5 = ((x_1).ir_is_rs_rel);
        when (! (x_5), noAction);
        Struct10 x_6 = ((x_0).lr_ir);
        Struct11 x_7 = ((x_6).info);
        Struct6 x_8 = ((x_1).ir_by_victim);
        Vector#(4, Bit#(64)) x_9 = ((x_0).lr_value);
        let x_10 <- getMSHR_00(x_4);
        Vector#(4, Bit#(64)) x_11 = (unpack(0));
        Bool x_12 = ((x_7).mesi_owned);
        Bit#(3) x_13 = ((x_7).mesi_status);
        Struct18 x_14 = (Struct18 {dir_st : (x_7).mesi_dir_st, dir_excl :
        ((((x_7).mesi_dir_sharers)[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(1))'(1'h0)) : (((Bit#(1))'(1'h1)) +
        ((((((x_7).mesi_dir_sharers)[1:1])[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(1))'(1'h0)) : (((Bit#(1))'(1'h1)) + (unpack(0))))))),
        dir_sharers : (x_7).mesi_dir_sharers});
        when ((x_2) == ((Bit#(3))'(3'h4)), noAction);
        when (((x_3).id) == ((Bit#(6))'(6'h5)), noAction);
        when (! ((x_3).type_), noAction);
        when ((! ((x_13) < ((Bit#(3))'(3'h2)))) && (! (((Bit#(3))'(3'h2)) <
        ((x_14).dir_st))), noAction);
        Struct1 x_15 = (x_3);
        Struct19 x_16 = (Struct19 {addr : (x_3).addr, info_write :
        (Bool)'(False), info_hit : (x_6).info_hit, info_way : (x_6).info_way,
        edir_hit : (x_6).edir_hit, edir_way : (x_6).edir_way, edir_slot :
        (x_6).edir_slot, info : (x_6).info, value_write : (Bool)'(False),
        value : unpack(0), may_victim : (x_6).may_victim, reps :
        (x_6).reps});
        Struct19 x_17 = (Struct19 {addr : (x_16).addr, info_write :
        (Bool)'(True), info_hit : (x_16).info_hit, info_way :
        (x_16).info_way, edir_hit : (x_16).edir_hit, edir_way :
        (x_16).edir_way, edir_slot : (x_16).edir_slot, info : Struct11
        {mesi_owned : ((x_16).info).mesi_owned, mesi_status :
        (Bit#(3))'(3'h2), mesi_dir_st : ((x_16).info).mesi_dir_st,
        mesi_dir_sharers : ((x_16).info).mesi_dir_sharers}, value_write :
        (x_16).value_write, value : (x_16).value, may_victim :
        (x_16).may_victim, reps : (x_16).reps});
        Struct19 x_18 = (Struct19 {addr : (x_17).addr, info_write :
        (Bool)'(True), info_hit : (x_17).info_hit, info_way :
        (x_17).info_way, edir_hit : (x_17).edir_hit, edir_way :
        (x_17).edir_way, edir_slot : (x_17).edir_slot, info : Struct11
        {mesi_owned : (Bool)'(False), mesi_status :
        ((x_17).info).mesi_status, mesi_dir_st : ((x_17).info).mesi_dir_st,
        mesi_dir_sharers : ((x_17).info).mesi_dir_sharers}, value_write :
        (x_17).value_write, value : (x_17).value, may_victim :
        (x_17).may_victim, reps :
        (x_17).reps});
        let x_21 = ?;
        if ((x_8).valid) begin
            let x_19 <- victims__00__setVictim(Struct20 {victim_idx :
            (x_8).data, victim_info : (x_18).info, victim_value :
            (x_18).value});
            x_21 = x_9;
        end else begin
            let x_20 <- cache__00__valueRsLineRq(x_18);
            x_21 = x_20;
        end
        Struct21 x_22 = (Struct21 {enq_type : ((((Bit#(3))'(3'h2))[2:1]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : (((((Bit#(3))'(3'h2))[2:1])
        == ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : ((Bit#(3))'(3'h2))[0:0], enq_msg : Struct1 {id :
        (Bit#(6))'(6'h6), type_ : (Bool)'(True), addr : (x_15).addr, value :
        x_21}});
        let x_23 <- makeEnq_parentChildren00(x_22);
    endrule

    rule rule_exec_00_06;
        $display ("Rule fired: rule_exec_00_06 at %t", $time);
        let x_0 <- deq_fifoL2E_00();
        Struct7 x_1 = ((x_0).lr_ir_pp);
        Bit#(3) x_2 = ((x_1).ir_msg_from);
        Struct1 x_3 = ((x_1).ir_msg);
        Bit#(4) x_4 = ((x_1).ir_mshr_id);
        Bool x_5 = ((x_1).ir_is_rs_rel);
        when (! (x_5), noAction);
        Struct10 x_6 = ((x_0).lr_ir);
        Struct11 x_7 = ((x_6).info);
        Struct6 x_8 = ((x_1).ir_by_victim);
        Vector#(4, Bit#(64)) x_9 = ((x_0).lr_value);
        let x_10 <- getMSHR_00(x_4);
        Vector#(4, Bit#(64)) x_11 = (unpack(0));
        Bool x_12 = ((x_7).mesi_owned);
        Bit#(3) x_13 = ((x_7).mesi_status);
        Struct18 x_14 = (Struct18 {dir_st : (x_7).mesi_dir_st, dir_excl :
        ((((x_7).mesi_dir_sharers)[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(1))'(1'h0)) : (((Bit#(1))'(1'h1)) +
        ((((((x_7).mesi_dir_sharers)[1:1])[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(1))'(1'h0)) : (((Bit#(1))'(1'h1)) + (unpack(0))))))),
        dir_sharers : (x_7).mesi_dir_sharers});
        when ((x_2) == ((Bit#(3))'(3'h4)), noAction);
        when (((x_3).id) == ((Bit#(6))'(6'h5)), noAction);
        when (! ((x_3).type_), noAction);
        when (((Bool)'(True)) && ((! (((Bit#(3))'(3'h1)) < (x_13))) && ((!
        (((x_14).dir_st) < ((Bit#(3))'(3'h3)))) && (! (((Bit#(3))'(3'h4)) <
        ((x_14).dir_st))))), noAction);
        Struct1 x_15 = (x_3);
        Struct19 x_16 = (Struct19 {addr : (x_3).addr, info_write :
        (Bool)'(False), info_hit : (x_6).info_hit, info_way : (x_6).info_way,
        edir_hit : (x_6).edir_hit, edir_way : (x_6).edir_way, edir_slot :
        (x_6).edir_slot, info : (x_6).info, value_write : (Bool)'(False),
        value : unpack(0), may_victim : (x_6).may_victim, reps :
        (x_6).reps});
        let x_18 = ?;
        if ((x_8).valid) begin
            x_18 = x_9;
        end else begin
            let x_17 <- cache__00__valueRsLineRq(unpack(0));
            x_18 = x_17;
        end
        let x_19 <- registerDL_00(Struct23 {r_id : x_4, r_dl_rss_from :
        (unpack(0)) | (((Bit#(2))'(2'h1)) <<
        (({((Bit#(2))'(2'h1)),((x_14).dir_excl)})[0:0])), r_dl_rsb :
        (Bool)'(True), r_dl_rsbTo : (Bit#(3))'(3'h2)});
        Struct21 x_20 = (Struct21 {enq_type :
        ((({((Bit#(2))'(2'h2)),((x_14).dir_excl)})[2:1]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) :
        (((({((Bit#(2))'(2'h2)),((x_14).dir_excl)})[2:1]) ==
        ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : ({((Bit#(2))'(2'h2)),((x_14).dir_excl)})[0:0], enq_msg :
        Struct1 {id : (Bit#(6))'(6'h5), type_ : (Bool)'(False), addr :
        (x_15).addr, value : unpack(0)}});
        let x_21 <- makeEnq_parentChildren00(x_20);
    endrule

    rule rule_exec_00_071;
        $display ("Rule fired: rule_exec_00_071 at %t", $time);
        let x_0 <- deq_fifoL2E_00();
        Struct7 x_1 = ((x_0).lr_ir_pp);
        Bit#(3) x_2 = ((x_1).ir_msg_from);
        Struct1 x_3 = ((x_1).ir_msg);
        Bit#(4) x_4 = ((x_1).ir_mshr_id);
        Bool x_5 = ((x_1).ir_is_rs_rel);
        when (x_5, noAction);
        Struct10 x_6 = ((x_0).lr_ir);
        Struct11 x_7 = ((x_6).info);
        Struct6 x_8 = ((x_1).ir_by_victim);
        Vector#(4, Bit#(64)) x_9 = ((x_0).lr_value);
        let x_10 <- getMSHR_00(x_4);
        Vector#(4, Bit#(64)) x_11 = (unpack(0));
        Bool x_12 = ((x_7).mesi_owned);
        Bit#(3) x_13 = ((x_7).mesi_status);
        Struct18 x_14 = (Struct18 {dir_st : (x_7).mesi_dir_st, dir_excl :
        ((((x_7).mesi_dir_sharers)[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(1))'(1'h0)) : (((Bit#(1))'(1'h1)) +
        ((((((x_7).mesi_dir_sharers)[1:1])[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(1))'(1'h0)) : (((Bit#(1))'(1'h1)) + (unpack(0))))))),
        dir_sharers : (x_7).mesi_dir_sharers});
        when (((x_10).m_status) == ((Bit#(3))'(3'h4)), noAction);
        when ((x_10).m_rsb, noAction);
        when ((((x_10).m_msg).type_) == ((Bool)'(False)), noAction);
        when ((((x_10).m_msg).id) == ((Bit#(6))'(6'h5)), noAction);
        when (((x_10).m_dl_rss) == ((x_10).m_dl_rss), noAction);
        when ((Bool)'(True), noAction);
        Struct25 x_15 = (Struct25 {cidx :
        {((Bit#(2))'(2'h1)),(((((x_10).m_dl_rss_from)[0:0]) ==
        ((Bit#(1))'(1'h1)) ? ((Bit#(1))'(1'h0)) : (((Bit#(1))'(1'h1)) +
        ((((((x_10).m_dl_rss_from)[1:1])[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(1))'(1'h0)) : (((Bit#(1))'(1'h1)) + (unpack(0))))))))}, msg :
        ((x_10).m_dl_rss)[((((x_10).m_dl_rss_from)[0:0]) ==
        ((Bit#(1))'(1'h1)) ? ((Bit#(1))'(1'h0)) : (((Bit#(1))'(1'h1)) +
        ((((((x_10).m_dl_rss_from)[1:1])[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(1))'(1'h0)) : (((Bit#(1))'(1'h1)) +
        (unpack(0)))))))]});
        Struct1 x_16 = ((x_10).m_msg);
        Bit#(3) x_17 = ((x_10).m_qidx);
        Struct19 x_18 = (Struct19 {addr : (x_3).addr, info_write :
        (Bool)'(False), info_hit : (x_6).info_hit, info_way : (x_6).info_way,
        edir_hit : (x_6).edir_hit, edir_way : (x_6).edir_way, edir_slot :
        (x_6).edir_slot, info : (x_6).info, value_write : (Bool)'(False),
        value : unpack(0), may_victim : (x_6).may_victim, reps :
        (x_6).reps});
        Struct19 x_19 = (Struct19 {addr : (x_18).addr, info_write :
        (Bool)'(True), info_hit : (x_18).info_hit, info_way :
        (x_18).info_way, edir_hit : (x_18).edir_hit, edir_way :
        (x_18).edir_way, edir_slot : (x_18).edir_slot, info : Struct11
        {mesi_owned : ((x_18).info).mesi_owned, mesi_status :
        ((x_18).info).mesi_status, mesi_dir_st : (Struct18 {dir_st :
        (Bit#(3))'(3'h2), dir_excl : unpack(0), dir_sharers : (unpack(0)) |
        (((Bit#(2))'(2'h1)) << (((x_15).cidx)[0:0]))}).dir_st,
        mesi_dir_sharers : (((Struct18 {dir_st : (Bit#(3))'(3'h2), dir_excl :
        unpack(0), dir_sharers : (unpack(0)) | (((Bit#(2))'(2'h1)) <<
        (((x_15).cidx)[0:0]))}).dir_st) == ((Bit#(3))'(3'h2)) ? ((Struct18
        {dir_st : (Bit#(3))'(3'h2), dir_excl : unpack(0), dir_sharers :
        (unpack(0)) | (((Bit#(2))'(2'h1)) <<
        (((x_15).cidx)[0:0]))}).dir_sharers) : (((Bit#(2))'(2'h1)) <<
        ((Struct18 {dir_st : (Bit#(3))'(3'h2), dir_excl : unpack(0),
        dir_sharers : (unpack(0)) | (((Bit#(2))'(2'h1)) <<
        (((x_15).cidx)[0:0]))}).dir_excl)))}, value_write :
        (x_18).value_write, value : (x_18).value, may_victim :
        (x_18).may_victim, reps : (x_18).reps});
        Struct19 x_20 = (Struct19 {addr : (x_19).addr, info_write :
        (Bool)'(True), info_hit : (x_19).info_hit, info_way :
        (x_19).info_way, edir_hit : (x_19).edir_hit, edir_way :
        (x_19).edir_way, edir_slot : (x_19).edir_slot, info : Struct11
        {mesi_owned : ((x_19).info).mesi_owned, mesi_status :
        (Bit#(3))'(3'h2), mesi_dir_st : ((x_19).info).mesi_dir_st,
        mesi_dir_sharers : ((x_19).info).mesi_dir_sharers}, value_write :
        (x_19).value_write, value : (x_19).value, may_victim :
        (x_19).may_victim, reps : (x_19).reps});
        Struct19 x_21 = (Struct19 {addr : (x_20).addr, info_write :
        (Bool)'(True), info_hit : (x_20).info_hit, info_way :
        (x_20).info_way, edir_hit : (x_20).edir_hit, edir_way :
        (x_20).edir_way, edir_slot : (x_20).edir_slot, info : Struct11
        {mesi_owned : (Bool)'(False), mesi_status :
        ((x_20).info).mesi_status, mesi_dir_st : ((x_20).info).mesi_dir_st,
        mesi_dir_sharers : ((x_20).info).mesi_dir_sharers}, value_write :
        (x_20).value_write, value : (x_20).value, may_victim :
        (x_20).may_victim, reps : (x_20).reps});
        Struct19 x_22 = (Struct19 {addr : (x_21).addr, info_write :
        (x_21).info_write, info_hit : (x_21).info_hit, info_way :
        (x_21).info_way, edir_hit : (x_21).edir_hit, edir_way :
        (x_21).edir_way, edir_slot : (x_21).edir_slot, info : (x_21).info,
        value_write : (Bool)'(True), value : ((x_15).msg).value, may_victim :
        (x_21).may_victim, reps :
        (x_21).reps});
        let x_25 = ?;
        if ((x_8).valid) begin
            let x_23 <- victims__00__setVictim(Struct20 {victim_idx :
            (x_8).data, victim_info : (x_22).info, victim_value :
            (x_22).value});
            x_25 = x_9;
        end else begin
            let x_24 <- cache__00__valueRsLineRq(x_22);
            x_25 = x_24;
        end
        let x_26 <- releaseMSHR_00(x_4);
        Struct21 x_27 = (Struct21 {enq_type : (((x_17)[2:1]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : ((((x_17)[2:1]) ==
        ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : (x_17)[0:0], enq_msg : Struct1 {id : (Bit#(6))'(6'h6),
        type_ : (Bool)'(True), addr : (x_16).addr, value :
        ((x_15).msg).value}});
        let x_28 <- makeEnq_parentChildren00(x_27);
    endrule

    rule rule_exec_00_12;
        $display ("Rule fired: rule_exec_00_12 at %t", $time);
        let x_0 <- deq_fifoL2E_00();
        Struct7 x_1 = ((x_0).lr_ir_pp);
        Bit#(3) x_2 = ((x_1).ir_msg_from);
        Struct1 x_3 = ((x_1).ir_msg);
        Bit#(4) x_4 = ((x_1).ir_mshr_id);
        Bool x_5 = ((x_1).ir_is_rs_rel);
        when (! (x_5), noAction);
        Struct10 x_6 = ((x_0).lr_ir);
        Struct11 x_7 = ((x_6).info);
        Struct6 x_8 = ((x_1).ir_by_victim);
        Vector#(4, Bit#(64)) x_9 = ((x_0).lr_value);
        let x_10 <- getMSHR_00(x_4);
        Vector#(4, Bit#(64)) x_11 = (unpack(0));
        Bool x_12 = ((x_7).mesi_owned);
        Bit#(3) x_13 = ((x_7).mesi_status);
        Struct18 x_14 = (Struct18 {dir_st : (x_7).mesi_dir_st, dir_excl :
        ((((x_7).mesi_dir_sharers)[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(1))'(1'h0)) : (((Bit#(1))'(1'h1)) +
        ((((((x_7).mesi_dir_sharers)[1:1])[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(1))'(1'h0)) : (((Bit#(1))'(1'h1)) + (unpack(0))))))),
        dir_sharers : (x_7).mesi_dir_sharers});
        when ((x_2) == ({((Bit#(2))'(2'h2)),((Bit#(1))'(1'h0))}),
        noAction);
        when (((x_3).id) == ((Bit#(6))'(6'hb)), noAction);
        when (((x_10).m_status) == ((Bit#(3))'(3'h4)), noAction);
        when ((x_10).m_rsb, noAction);
        when ((((x_10).m_msg).type_) == ((Bool)'(False)), noAction);
        when ((((x_10).m_msg).id) == ((Bit#(6))'(6'ha)), noAction);
        when (((x_10).m_status) == ((Bit#(3))'(3'h4)), noAction);
        when ((x_10).m_rsb, noAction);
        when ((x_3).type_, noAction);
        when ((((x_14).dir_st) == ((Bit#(3))'(3'h1))) || ((((x_14).dir_st) ==
        ((Bit#(3))'(3'h2))) && (((x_14).dir_sharers) == (((Bit#(2))'(2'h1))
        << (({((Bit#(2))'(2'h2)),(((x_10).m_qidx)[0:0])})[0:0])))),
        noAction);
        Struct1 x_15 = (x_3);
        Struct1 x_16 = ((x_10).m_msg);
        Bit#(3) x_17 = ({((Bit#(2))'(2'h2)),(((x_10).m_qidx)[0:0])});
        Struct19 x_18 = (Struct19 {addr : (x_3).addr, info_write :
        (Bool)'(False), info_hit : (x_6).info_hit, info_way : (x_6).info_way,
        edir_hit : (x_6).edir_hit, edir_way : (x_6).edir_way, edir_slot :
        (x_6).edir_slot, info : (x_6).info, value_write : (Bool)'(False),
        value : unpack(0), may_victim : (x_6).may_victim, reps :
        (x_6).reps});
        Struct19 x_19 = (Struct19 {addr : (x_18).addr, info_write :
        (Bool)'(True), info_hit : (x_18).info_hit, info_way :
        (x_18).info_way, edir_hit : (x_18).edir_hit, edir_way :
        (x_18).edir_way, edir_slot : (x_18).edir_slot, info : Struct11
        {mesi_owned : ((x_18).info).mesi_owned, mesi_status :
        ((x_18).info).mesi_status, mesi_dir_st : (Struct18 {dir_st :
        (Bit#(3))'(3'h4), dir_excl : (x_17)[0:0], dir_sharers :
        unpack(0)}).dir_st, mesi_dir_sharers : (((Struct18 {dir_st :
        (Bit#(3))'(3'h4), dir_excl : (x_17)[0:0], dir_sharers :
        unpack(0)}).dir_st) == ((Bit#(3))'(3'h2)) ? ((Struct18 {dir_st :
        (Bit#(3))'(3'h4), dir_excl : (x_17)[0:0], dir_sharers :
        unpack(0)}).dir_sharers) : (((Bit#(2))'(2'h1)) << ((Struct18 {dir_st
        : (Bit#(3))'(3'h4), dir_excl : (x_17)[0:0], dir_sharers :
        unpack(0)}).dir_excl)))}, value_write : (x_18).value_write, value :
        (x_18).value, may_victim : (x_18).may_victim, reps :
        (x_18).reps});
        Struct19 x_20 = (Struct19 {addr : (x_19).addr, info_write :
        (Bool)'(True), info_hit : (x_19).info_hit, info_way :
        (x_19).info_way, edir_hit : (x_19).edir_hit, edir_way :
        (x_19).edir_way, edir_slot : (x_19).edir_slot, info : Struct11
        {mesi_owned : ((x_19).info).mesi_owned, mesi_status :
        (Bit#(3))'(3'h1), mesi_dir_st : ((x_19).info).mesi_dir_st,
        mesi_dir_sharers : ((x_19).info).mesi_dir_sharers}, value_write :
        (x_19).value_write, value : (x_19).value, may_victim :
        (x_19).may_victim, reps : (x_19).reps});
        Struct19 x_21 = (Struct19 {addr : (x_20).addr, info_write :
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
            let x_22 <- victims__00__setVictim(Struct20 {victim_idx :
            (x_8).data, victim_info : (x_21).info, victim_value :
            (x_21).value});
            x_24 = x_9;
        end else begin
            let x_23 <- cache__00__valueRsLineRq(x_21);
            x_24 = x_23;
        end
        let x_25 <- releaseMSHR_00(x_4);
        Struct21 x_26 = (Struct21 {enq_type : (((x_17)[2:1]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : ((((x_17)[2:1]) ==
        ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : (x_17)[0:0], enq_msg : Struct1 {id : (Bit#(6))'(6'hb),
        type_ : (Bool)'(True), addr : (x_15).addr, value : unpack(0)}});
        let x_27 <- makeEnq_parentChildren00(x_26);
    endrule

    rule rule_exec_00_13;
        $display ("Rule fired: rule_exec_00_13 at %t", $time);
        let x_0 <- deq_fifoL2E_00();
        Struct7 x_1 = ((x_0).lr_ir_pp);
        Bit#(3) x_2 = ((x_1).ir_msg_from);
        Struct1 x_3 = ((x_1).ir_msg);
        Bit#(4) x_4 = ((x_1).ir_mshr_id);
        Bool x_5 = ((x_1).ir_is_rs_rel);
        when (! (x_5), noAction);
        Struct10 x_6 = ((x_0).lr_ir);
        Struct11 x_7 = ((x_6).info);
        Struct6 x_8 = ((x_1).ir_by_victim);
        Vector#(4, Bit#(64)) x_9 = ((x_0).lr_value);
        let x_10 <- getMSHR_00(x_4);
        Vector#(4, Bit#(64)) x_11 = (unpack(0));
        Bool x_12 = ((x_7).mesi_owned);
        Bit#(3) x_13 = ((x_7).mesi_status);
        Struct18 x_14 = (Struct18 {dir_st : (x_7).mesi_dir_st, dir_excl :
        ((((x_7).mesi_dir_sharers)[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(1))'(1'h0)) : (((Bit#(1))'(1'h1)) +
        ((((((x_7).mesi_dir_sharers)[1:1])[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(1))'(1'h0)) : (((Bit#(1))'(1'h1)) + (unpack(0))))))),
        dir_sharers : (x_7).mesi_dir_sharers});
        when ((x_2) == ({((Bit#(2))'(2'h2)),((Bit#(1))'(1'h0))}),
        noAction);
        when (((x_3).id) == ((Bit#(6))'(6'hb)), noAction);
        when (((x_10).m_status) == ((Bit#(3))'(3'h4)), noAction);
        when ((x_10).m_rsb, noAction);
        when ((((x_10).m_msg).type_) == ((Bool)'(False)), noAction);
        when ((((x_10).m_msg).id) == ((Bit#(6))'(6'ha)), noAction);
        when (((x_10).m_status) == ((Bit#(3))'(3'h4)), noAction);
        when ((x_10).m_rsb, noAction);
        when ((x_3).type_, noAction);
        when (((Bool)'(True)) && (((Bool)'(True)) && (((Bool)'(True)) && ((!
        ((((x_14).dir_sharers) & (~(((Bit#(2))'(2'h1)) <<
        (({((Bit#(2))'(2'h2)),(((x_10).m_qidx)[0:0])})[0:0])))) ==
        ((Bit#(2))'(2'h0)))) && (((x_14).dir_st) == ((Bit#(3))'(3'h2)))))),
        noAction);
        Struct1 x_15 = ((x_10).m_msg);
        Bit#(3) x_16 = ({((Bit#(2))'(2'h2)),(((x_10).m_qidx)[0:0])});
        Struct19 x_17 = (Struct19 {addr : (x_3).addr, info_write :
        (Bool)'(False), info_hit : (x_6).info_hit, info_way : (x_6).info_way,
        edir_hit : (x_6).edir_hit, edir_way : (x_6).edir_way, edir_slot :
        (x_6).edir_slot, info : (x_6).info, value_write : (Bool)'(False),
        value : unpack(0), may_victim : (x_6).may_victim, reps :
        (x_6).reps});
        Struct19 x_18 = (Struct19 {addr : (x_17).addr, info_write :
        (Bool)'(True), info_hit : (x_17).info_hit, info_way :
        (x_17).info_way, edir_hit : (x_17).edir_hit, edir_way :
        (x_17).edir_way, edir_slot : (x_17).edir_slot, info : Struct11
        {mesi_owned : (Bool)'(True), mesi_status : ((x_17).info).mesi_status,
        mesi_dir_st : ((x_17).info).mesi_dir_st, mesi_dir_sharers :
        ((x_17).info).mesi_dir_sharers}, value_write : (x_17).value_write,
        value : (x_17).value, may_victim : (x_17).may_victim, reps :
        (x_17).reps});
        let x_21 = ?;
        if ((x_8).valid) begin
            let x_19 <- victims__00__setVictim(Struct20 {victim_idx :
            (x_8).data, victim_info : (x_18).info, victim_value :
            (x_18).value});
            x_21 = x_9;
        end else begin
            let x_20 <- cache__00__valueRsLineRq(x_18);
            x_21 = x_20;
        end
        let x_22 <- transferUpDown_00(Struct26 {r_id : x_4, r_dl_rss_from :
        ((x_14).dir_sharers) & (~(((Bit#(2))'(2'h1)) << ((x_16)[0:0])))});
        let x_23 <- broadcast_parentChildren00(Struct24 {cs_inds :
        ((x_14).dir_sharers) & (~(((Bit#(2))'(2'h1)) << ((x_16)[0:0]))),
        cs_msg : Struct1 {id : (Bit#(6))'(6'hc), type_ : (Bool)'(False), addr
        : (x_15).addr, value : unpack(0)}});
    endrule

    rule rule_exec_00_161;
        $display ("Rule fired: rule_exec_00_161 at %t", $time);
        let x_0 <- deq_fifoL2E_00();
        Struct7 x_1 = ((x_0).lr_ir_pp);
        Bit#(3) x_2 = ((x_1).ir_msg_from);
        Struct1 x_3 = ((x_1).ir_msg);
        Bit#(4) x_4 = ((x_1).ir_mshr_id);
        Bool x_5 = ((x_1).ir_is_rs_rel);
        when (x_5, noAction);
        Struct10 x_6 = ((x_0).lr_ir);
        Struct11 x_7 = ((x_6).info);
        Struct6 x_8 = ((x_1).ir_by_victim);
        Vector#(4, Bit#(64)) x_9 = ((x_0).lr_value);
        let x_10 <- getMSHR_00(x_4);
        Vector#(4, Bit#(64)) x_11 = (unpack(0));
        Bool x_12 = ((x_7).mesi_owned);
        Bit#(3) x_13 = ((x_7).mesi_status);
        Struct18 x_14 = (Struct18 {dir_st : (x_7).mesi_dir_st, dir_excl :
        ((((x_7).mesi_dir_sharers)[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(1))'(1'h0)) : (((Bit#(1))'(1'h1)) +
        ((((((x_7).mesi_dir_sharers)[1:1])[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(1))'(1'h0)) : (((Bit#(1))'(1'h1)) + (unpack(0))))))),
        dir_sharers : (x_7).mesi_dir_sharers});
        when (((x_10).m_status) == ((Bit#(3))'(3'h4)), noAction);
        when ((x_10).m_rsb, noAction);
        when ((((x_10).m_msg).type_) == ((Bool)'(False)), noAction);
        when ((((x_10).m_msg).id) == ((Bit#(6))'(6'ha)), noAction);
        when (((x_10).m_dl_rss) == ((x_10).m_dl_rss), noAction);
        when ((Bool)'(True), noAction);
        Struct1 x_15 = ((x_10).m_msg);
        Bit#(3) x_16 = ((x_10).m_qidx);
        Struct19 x_17 = (Struct19 {addr : (x_3).addr, info_write :
        (Bool)'(False), info_hit : (x_6).info_hit, info_way : (x_6).info_way,
        edir_hit : (x_6).edir_hit, edir_way : (x_6).edir_way, edir_slot :
        (x_6).edir_slot, info : (x_6).info, value_write : (Bool)'(False),
        value : unpack(0), may_victim : (x_6).may_victim, reps :
        (x_6).reps});
        Struct19 x_18 = (Struct19 {addr : (x_17).addr, info_write :
        (Bool)'(True), info_hit : (x_17).info_hit, info_way :
        (x_17).info_way, edir_hit : (x_17).edir_hit, edir_way :
        (x_17).edir_way, edir_slot : (x_17).edir_slot, info : Struct11
        {mesi_owned : ((x_17).info).mesi_owned, mesi_status :
        ((x_17).info).mesi_status, mesi_dir_st : (Struct18 {dir_st :
        (Bit#(3))'(3'h4), dir_excl : (x_16)[0:0], dir_sharers :
        unpack(0)}).dir_st, mesi_dir_sharers : (((Struct18 {dir_st :
        (Bit#(3))'(3'h4), dir_excl : (x_16)[0:0], dir_sharers :
        unpack(0)}).dir_st) == ((Bit#(3))'(3'h2)) ? ((Struct18 {dir_st :
        (Bit#(3))'(3'h4), dir_excl : (x_16)[0:0], dir_sharers :
        unpack(0)}).dir_sharers) : (((Bit#(2))'(2'h1)) << ((Struct18 {dir_st
        : (Bit#(3))'(3'h4), dir_excl : (x_16)[0:0], dir_sharers :
        unpack(0)}).dir_excl)))}, value_write : (x_17).value_write, value :
        (x_17).value, may_victim : (x_17).may_victim, reps :
        (x_17).reps});
        Struct19 x_19 = (Struct19 {addr : (x_18).addr, info_write :
        (Bool)'(True), info_hit : (x_18).info_hit, info_way :
        (x_18).info_way, edir_hit : (x_18).edir_hit, edir_way :
        (x_18).edir_way, edir_slot : (x_18).edir_slot, info : Struct11
        {mesi_owned : ((x_18).info).mesi_owned, mesi_status :
        (Bit#(3))'(3'h1), mesi_dir_st : ((x_18).info).mesi_dir_st,
        mesi_dir_sharers : ((x_18).info).mesi_dir_sharers}, value_write :
        (x_18).value_write, value : (x_18).value, may_victim :
        (x_18).may_victim, reps : (x_18).reps});
        Struct19 x_20 = (Struct19 {addr : (x_19).addr, info_write :
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
            let x_21 <- victims__00__setVictim(Struct20 {victim_idx :
            (x_8).data, victim_info : (x_20).info, victim_value :
            (x_20).value});
            x_23 = x_9;
        end else begin
            let x_22 <- cache__00__valueRsLineRq(x_20);
            x_23 = x_22;
        end
        let x_24 <- releaseMSHR_00(x_4);
        Struct21 x_25 = (Struct21 {enq_type : (((x_16)[2:1]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : ((((x_16)[2:1]) ==
        ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : (x_16)[0:0], enq_msg : Struct1 {id : (Bit#(6))'(6'hb),
        type_ : (Bool)'(True), addr : (x_15).addr, value : unpack(0)}});
        let x_26 <- makeEnq_parentChildren00(x_25);
    endrule

    rule rule_exec_00_170;
        $display ("Rule fired: rule_exec_00_170 at %t", $time);
        let x_0 <- deq_fifoL2E_00();
        Struct7 x_1 = ((x_0).lr_ir_pp);
        Bit#(3) x_2 = ((x_1).ir_msg_from);
        Struct1 x_3 = ((x_1).ir_msg);
        Bit#(4) x_4 = ((x_1).ir_mshr_id);
        Bool x_5 = ((x_1).ir_is_rs_rel);
        when (! (x_5), noAction);
        Struct10 x_6 = ((x_0).lr_ir);
        Struct11 x_7 = ((x_6).info);
        Struct6 x_8 = ((x_1).ir_by_victim);
        Vector#(4, Bit#(64)) x_9 = ((x_0).lr_value);
        let x_10 <- getMSHR_00(x_4);
        Vector#(4, Bit#(64)) x_11 = (unpack(0));
        Bool x_12 = ((x_7).mesi_owned);
        Bit#(3) x_13 = ((x_7).mesi_status);
        Struct18 x_14 = (Struct18 {dir_st : (x_7).mesi_dir_st, dir_excl :
        ((((x_7).mesi_dir_sharers)[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(1))'(1'h0)) : (((Bit#(1))'(1'h1)) +
        ((((((x_7).mesi_dir_sharers)[1:1])[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(1))'(1'h0)) : (((Bit#(1))'(1'h1)) + (unpack(0))))))),
        dir_sharers : (x_7).mesi_dir_sharers});
        when ((x_2) == ((Bit#(3))'(3'h4)), noAction);
        when (((x_3).id) == ((Bit#(6))'(6'hc)), noAction);
        when (! ((x_3).type_), noAction);
        when (((x_14).dir_st) == ((Bit#(3))'(3'h1)), noAction);
        Struct1 x_15 = (x_3);
        Struct19 x_16 = (Struct19 {addr : (x_3).addr, info_write :
        (Bool)'(False), info_hit : (x_6).info_hit, info_way : (x_6).info_way,
        edir_hit : (x_6).edir_hit, edir_way : (x_6).edir_way, edir_slot :
        (x_6).edir_slot, info : (x_6).info, value_write : (Bool)'(False),
        value : unpack(0), may_victim : (x_6).may_victim, reps :
        (x_6).reps});
        Struct19 x_17 = (Struct19 {addr : (x_16).addr, info_write :
        (Bool)'(True), info_hit : (x_16).info_hit, info_way :
        (x_16).info_way, edir_hit : (x_16).edir_hit, edir_way :
        (x_16).edir_way, edir_slot : (x_16).edir_slot, info : Struct11
        {mesi_owned : ((x_16).info).mesi_owned, mesi_status :
        (Bit#(3))'(3'h1), mesi_dir_st : ((x_16).info).mesi_dir_st,
        mesi_dir_sharers : ((x_16).info).mesi_dir_sharers}, value_write :
        (x_16).value_write, value : (x_16).value, may_victim :
        (x_16).may_victim, reps : (x_16).reps});
        Struct19 x_18 = (Struct19 {addr : (x_17).addr, info_write :
        (Bool)'(True), info_hit : (x_17).info_hit, info_way :
        (x_17).info_way, edir_hit : (x_17).edir_hit, edir_way :
        (x_17).edir_way, edir_slot : (x_17).edir_slot, info : Struct11
        {mesi_owned : (Bool)'(False), mesi_status :
        ((x_17).info).mesi_status, mesi_dir_st : ((x_17).info).mesi_dir_st,
        mesi_dir_sharers : ((x_17).info).mesi_dir_sharers}, value_write :
        (x_17).value_write, value : (x_17).value, may_victim :
        (x_17).may_victim, reps :
        (x_17).reps});
        let x_21 = ?;
        if ((x_8).valid) begin
            let x_19 <- victims__00__setVictim(Struct20 {victim_idx :
            (x_8).data, victim_info : (x_18).info, victim_value :
            (x_18).value});
            x_21 = x_9;
        end else begin
            let x_20 <- cache__00__valueRsLineRq(x_18);
            x_21 = x_20;
        end
        Struct21 x_22 = (Struct21 {enq_type : ((((Bit#(3))'(3'h2))[2:1]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : (((((Bit#(3))'(3'h2))[2:1])
        == ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : ((Bit#(3))'(3'h2))[0:0], enq_msg : Struct1 {id :
        (Bit#(6))'(6'hd), type_ : (Bool)'(True), addr : (x_15).addr, value :
        unpack(0)}});
        let x_23 <- makeEnq_parentChildren00(x_22);
    endrule

    rule rule_exec_00_171;
        $display ("Rule fired: rule_exec_00_171 at %t", $time);
        let x_0 <- deq_fifoL2E_00();
        Struct7 x_1 = ((x_0).lr_ir_pp);
        Bit#(3) x_2 = ((x_1).ir_msg_from);
        Struct1 x_3 = ((x_1).ir_msg);
        Bit#(4) x_4 = ((x_1).ir_mshr_id);
        Bool x_5 = ((x_1).ir_is_rs_rel);
        when (! (x_5), noAction);
        Struct10 x_6 = ((x_0).lr_ir);
        Struct11 x_7 = ((x_6).info);
        Struct6 x_8 = ((x_1).ir_by_victim);
        Vector#(4, Bit#(64)) x_9 = ((x_0).lr_value);
        let x_10 <- getMSHR_00(x_4);
        Vector#(4, Bit#(64)) x_11 = (unpack(0));
        Bool x_12 = ((x_7).mesi_owned);
        Bit#(3) x_13 = ((x_7).mesi_status);
        Struct18 x_14 = (Struct18 {dir_st : (x_7).mesi_dir_st, dir_excl :
        ((((x_7).mesi_dir_sharers)[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(1))'(1'h0)) : (((Bit#(1))'(1'h1)) +
        ((((((x_7).mesi_dir_sharers)[1:1])[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(1))'(1'h0)) : (((Bit#(1))'(1'h1)) + (unpack(0))))))),
        dir_sharers : (x_7).mesi_dir_sharers});
        when ((x_2) == ((Bit#(3))'(3'h4)), noAction);
        when (((x_3).id) == ((Bit#(6))'(6'he)), noAction);
        when (! ((x_3).type_), noAction);
        when ((! ((x_13) < ((Bit#(3))'(3'h3)))) && (((x_14).dir_st) ==
        ((Bit#(3))'(3'h1))), noAction);
        Struct1 x_15 = (x_3);
        Struct19 x_16 = (Struct19 {addr : (x_3).addr, info_write :
        (Bool)'(False), info_hit : (x_6).info_hit, info_way : (x_6).info_way,
        edir_hit : (x_6).edir_hit, edir_way : (x_6).edir_way, edir_slot :
        (x_6).edir_slot, info : (x_6).info, value_write : (Bool)'(False),
        value : unpack(0), may_victim : (x_6).may_victim, reps :
        (x_6).reps});
        Struct19 x_17 = (Struct19 {addr : (x_16).addr, info_write :
        (Bool)'(True), info_hit : (x_16).info_hit, info_way :
        (x_16).info_way, edir_hit : (x_16).edir_hit, edir_way :
        (x_16).edir_way, edir_slot : (x_16).edir_slot, info : Struct11
        {mesi_owned : ((x_16).info).mesi_owned, mesi_status :
        (Bit#(3))'(3'h1), mesi_dir_st : ((x_16).info).mesi_dir_st,
        mesi_dir_sharers : ((x_16).info).mesi_dir_sharers}, value_write :
        (x_16).value_write, value : (x_16).value, may_victim :
        (x_16).may_victim, reps : (x_16).reps});
        Struct19 x_18 = (Struct19 {addr : (x_17).addr, info_write :
        (Bool)'(True), info_hit : (x_17).info_hit, info_way :
        (x_17).info_way, edir_hit : (x_17).edir_hit, edir_way :
        (x_17).edir_way, edir_slot : (x_17).edir_slot, info : Struct11
        {mesi_owned : (Bool)'(False), mesi_status :
        ((x_17).info).mesi_status, mesi_dir_st : ((x_17).info).mesi_dir_st,
        mesi_dir_sharers : ((x_17).info).mesi_dir_sharers}, value_write :
        (x_17).value_write, value : (x_17).value, may_victim :
        (x_17).may_victim, reps :
        (x_17).reps});
        let x_21 = ?;
        if ((x_8).valid) begin
            let x_19 <- victims__00__setVictim(Struct20 {victim_idx :
            (x_8).data, victim_info : (x_18).info, victim_value :
            (x_18).value});
            x_21 = x_9;
        end else begin
            let x_20 <- cache__00__valueRsLineRq(x_18);
            x_21 = x_20;
        end
        Struct21 x_22 = (Struct21 {enq_type : ((((Bit#(3))'(3'h2))[2:1]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : (((((Bit#(3))'(3'h2))[2:1])
        == ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : ((Bit#(3))'(3'h2))[0:0], enq_msg : Struct1 {id :
        (Bit#(6))'(6'hf), type_ : (Bool)'(True), addr : (x_15).addr, value :
        unpack(0)}});
        let x_23 <- makeEnq_parentChildren00(x_22);
    endrule

    rule rule_exec_00_190;
        $display ("Rule fired: rule_exec_00_190 at %t", $time);
        let x_0 <- deq_fifoL2E_00();
        Struct7 x_1 = ((x_0).lr_ir_pp);
        Bit#(3) x_2 = ((x_1).ir_msg_from);
        Struct1 x_3 = ((x_1).ir_msg);
        Bit#(4) x_4 = ((x_1).ir_mshr_id);
        Bool x_5 = ((x_1).ir_is_rs_rel);
        when (! (x_5), noAction);
        Struct10 x_6 = ((x_0).lr_ir);
        Struct11 x_7 = ((x_6).info);
        Struct6 x_8 = ((x_1).ir_by_victim);
        Vector#(4, Bit#(64)) x_9 = ((x_0).lr_value);
        let x_10 <- getMSHR_00(x_4);
        Vector#(4, Bit#(64)) x_11 = (unpack(0));
        Bool x_12 = ((x_7).mesi_owned);
        Bit#(3) x_13 = ((x_7).mesi_status);
        Struct18 x_14 = (Struct18 {dir_st : (x_7).mesi_dir_st, dir_excl :
        ((((x_7).mesi_dir_sharers)[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(1))'(1'h0)) : (((Bit#(1))'(1'h1)) +
        ((((((x_7).mesi_dir_sharers)[1:1])[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(1))'(1'h0)) : (((Bit#(1))'(1'h1)) + (unpack(0))))))),
        dir_sharers : (x_7).mesi_dir_sharers});
        when ((x_2) == ((Bit#(3))'(3'h4)), noAction);
        when (((x_3).id) == ((Bit#(6))'(6'hc)), noAction);
        when (! ((x_3).type_), noAction);
        when (((Bool)'(True)) && (((Bool)'(True)) && (((x_14).dir_st) ==
        ((Bit#(3))'(3'h2)))), noAction);
        Struct1 x_15 = (x_3);
        Struct19 x_16 = (Struct19 {addr : (x_3).addr, info_write :
        (Bool)'(False), info_hit : (x_6).info_hit, info_way : (x_6).info_way,
        edir_hit : (x_6).edir_hit, edir_way : (x_6).edir_way, edir_slot :
        (x_6).edir_slot, info : (x_6).info, value_write : (Bool)'(False),
        value : unpack(0), may_victim : (x_6).may_victim, reps :
        (x_6).reps});
        let x_18 = ?;
        if ((x_8).valid) begin
            x_18 = x_9;
        end else begin
            let x_17 <- cache__00__valueRsLineRq(unpack(0));
            x_18 = x_17;
        end
        let x_19 <- registerDL_00(Struct23 {r_id : x_4, r_dl_rss_from :
        (x_14).dir_sharers, r_dl_rsb : (Bool)'(True), r_dl_rsbTo :
        (Bit#(3))'(3'h2)});
        let x_20 <- broadcast_parentChildren00(Struct24 {cs_inds :
        (x_14).dir_sharers, cs_msg : Struct1 {id : (Bit#(6))'(6'hc), type_ :
        (Bool)'(False), addr : (x_15).addr, value : unpack(0)}});
    endrule

    rule rule_exec_00_191;
        $display ("Rule fired: rule_exec_00_191 at %t", $time);
        let x_0 <- deq_fifoL2E_00();
        Struct7 x_1 = ((x_0).lr_ir_pp);
        Bit#(3) x_2 = ((x_1).ir_msg_from);
        Struct1 x_3 = ((x_1).ir_msg);
        Bit#(4) x_4 = ((x_1).ir_mshr_id);
        Bool x_5 = ((x_1).ir_is_rs_rel);
        when (! (x_5), noAction);
        Struct10 x_6 = ((x_0).lr_ir);
        Struct11 x_7 = ((x_6).info);
        Struct6 x_8 = ((x_1).ir_by_victim);
        Vector#(4, Bit#(64)) x_9 = ((x_0).lr_value);
        let x_10 <- getMSHR_00(x_4);
        Vector#(4, Bit#(64)) x_11 = (unpack(0));
        Bool x_12 = ((x_7).mesi_owned);
        Bit#(3) x_13 = ((x_7).mesi_status);
        Struct18 x_14 = (Struct18 {dir_st : (x_7).mesi_dir_st, dir_excl :
        ((((x_7).mesi_dir_sharers)[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(1))'(1'h0)) : (((Bit#(1))'(1'h1)) +
        ((((((x_7).mesi_dir_sharers)[1:1])[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(1))'(1'h0)) : (((Bit#(1))'(1'h1)) + (unpack(0))))))),
        dir_sharers : (x_7).mesi_dir_sharers});
        when ((x_2) == ((Bit#(3))'(3'h4)), noAction);
        when (((x_3).id) == ((Bit#(6))'(6'he)), noAction);
        when (! ((x_3).type_), noAction);
        when (((Bool)'(True)) && ((! (((x_14).dir_st) < ((Bit#(3))'(3'h3))))
        && (! (((Bit#(3))'(3'h4)) < ((x_14).dir_st)))), noAction);
        Struct1 x_15 = (x_3);
        Struct19 x_16 = (Struct19 {addr : (x_3).addr, info_write :
        (Bool)'(False), info_hit : (x_6).info_hit, info_way : (x_6).info_way,
        edir_hit : (x_6).edir_hit, edir_way : (x_6).edir_way, edir_slot :
        (x_6).edir_slot, info : (x_6).info, value_write : (Bool)'(False),
        value : unpack(0), may_victim : (x_6).may_victim, reps :
        (x_6).reps});
        let x_18 = ?;
        if ((x_8).valid) begin
            x_18 = x_9;
        end else begin
            let x_17 <- cache__00__valueRsLineRq(unpack(0));
            x_18 = x_17;
        end
        let x_19 <- registerDL_00(Struct23 {r_id : x_4, r_dl_rss_from :
        (unpack(0)) | (((Bit#(2))'(2'h1)) <<
        (({((Bit#(2))'(2'h1)),((x_14).dir_excl)})[0:0])), r_dl_rsb :
        (Bool)'(True), r_dl_rsbTo : (Bit#(3))'(3'h2)});
        Struct21 x_20 = (Struct21 {enq_type :
        ((({((Bit#(2))'(2'h2)),((x_14).dir_excl)})[2:1]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) :
        (((({((Bit#(2))'(2'h2)),((x_14).dir_excl)})[2:1]) ==
        ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : ({((Bit#(2))'(2'h2)),((x_14).dir_excl)})[0:0], enq_msg :
        Struct1 {id : (Bit#(6))'(6'he), type_ : (Bool)'(False), addr :
        (x_15).addr, value : unpack(0)}});
        let x_21 <- makeEnq_parentChildren00(x_20);
    endrule

    rule rule_exec_00_192;
        $display ("Rule fired: rule_exec_00_192 at %t", $time);
        let x_0 <- deq_fifoL2E_00();
        Struct7 x_1 = ((x_0).lr_ir_pp);
        Bit#(3) x_2 = ((x_1).ir_msg_from);
        Struct1 x_3 = ((x_1).ir_msg);
        Bit#(4) x_4 = ((x_1).ir_mshr_id);
        Bool x_5 = ((x_1).ir_is_rs_rel);
        when (! (x_5), noAction);
        Struct10 x_6 = ((x_0).lr_ir);
        Struct11 x_7 = ((x_6).info);
        Struct6 x_8 = ((x_1).ir_by_victim);
        Vector#(4, Bit#(64)) x_9 = ((x_0).lr_value);
        let x_10 <- getMSHR_00(x_4);
        Vector#(4, Bit#(64)) x_11 = (unpack(0));
        Bool x_12 = ((x_7).mesi_owned);
        Bit#(3) x_13 = ((x_7).mesi_status);
        Struct18 x_14 = (Struct18 {dir_st : (x_7).mesi_dir_st, dir_excl :
        ((((x_7).mesi_dir_sharers)[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(1))'(1'h0)) : (((Bit#(1))'(1'h1)) +
        ((((((x_7).mesi_dir_sharers)[1:1])[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(1))'(1'h0)) : (((Bit#(1))'(1'h1)) + (unpack(0))))))),
        dir_sharers : (x_7).mesi_dir_sharers});
        when ((x_2) == ((Bit#(3))'(3'h4)), noAction);
        when (((x_3).id) == ((Bit#(6))'(6'he)), noAction);
        when (! ((x_3).type_), noAction);
        when (((Bool)'(True)) && (((Bool)'(True)) && (((x_14).dir_st) ==
        ((Bit#(3))'(3'h2)))), noAction);
        Struct1 x_15 = (x_3);
        Struct19 x_16 = (Struct19 {addr : (x_3).addr, info_write :
        (Bool)'(False), info_hit : (x_6).info_hit, info_way : (x_6).info_way,
        edir_hit : (x_6).edir_hit, edir_way : (x_6).edir_way, edir_slot :
        (x_6).edir_slot, info : (x_6).info, value_write : (Bool)'(False),
        value : unpack(0), may_victim : (x_6).may_victim, reps :
        (x_6).reps});
        let x_18 = ?;
        if ((x_8).valid) begin
            x_18 = x_9;
        end else begin
            let x_17 <- cache__00__valueRsLineRq(unpack(0));
            x_18 = x_17;
        end
        let x_19 <- registerDL_00(Struct23 {r_id : x_4, r_dl_rss_from :
        (x_14).dir_sharers, r_dl_rsb : (Bool)'(True), r_dl_rsbTo :
        (Bit#(3))'(3'h2)});
        let x_20 <- broadcast_parentChildren00(Struct24 {cs_inds :
        (x_14).dir_sharers, cs_msg : Struct1 {id : (Bit#(6))'(6'hc), type_ :
        (Bool)'(False), addr : (x_15).addr, value : unpack(0)}});
    endrule

    rule rule_exec_00_11010;
        $display ("Rule fired: rule_exec_00_11010 at %t", $time);
        let x_0 <- deq_fifoL2E_00();
        Struct7 x_1 = ((x_0).lr_ir_pp);
        Bit#(3) x_2 = ((x_1).ir_msg_from);
        Struct1 x_3 = ((x_1).ir_msg);
        Bit#(4) x_4 = ((x_1).ir_mshr_id);
        Bool x_5 = ((x_1).ir_is_rs_rel);
        when (x_5, noAction);
        Struct10 x_6 = ((x_0).lr_ir);
        Struct11 x_7 = ((x_6).info);
        Struct6 x_8 = ((x_1).ir_by_victim);
        Vector#(4, Bit#(64)) x_9 = ((x_0).lr_value);
        let x_10 <- getMSHR_00(x_4);
        Vector#(4, Bit#(64)) x_11 = (unpack(0));
        Bool x_12 = ((x_7).mesi_owned);
        Bit#(3) x_13 = ((x_7).mesi_status);
        Struct18 x_14 = (Struct18 {dir_st : (x_7).mesi_dir_st, dir_excl :
        ((((x_7).mesi_dir_sharers)[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(1))'(1'h0)) : (((Bit#(1))'(1'h1)) +
        ((((((x_7).mesi_dir_sharers)[1:1])[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(1))'(1'h0)) : (((Bit#(1))'(1'h1)) + (unpack(0))))))),
        dir_sharers : (x_7).mesi_dir_sharers});
        when (((x_10).m_status) == ((Bit#(3))'(3'h4)), noAction);
        when ((x_10).m_rsb, noAction);
        when ((((x_10).m_msg).type_) == ((Bool)'(False)), noAction);
        when ((((x_10).m_msg).id) == ((Bit#(6))'(6'hc)), noAction);
        when (((x_10).m_dl_rss) == ((x_10).m_dl_rss), noAction);
        when ((Bool)'(True), noAction);
        Struct1 x_15 = ((x_10).m_msg);
        Bit#(3) x_16 = ((x_10).m_qidx);
        Struct19 x_17 = (Struct19 {addr : (x_3).addr, info_write :
        (Bool)'(False), info_hit : (x_6).info_hit, info_way : (x_6).info_way,
        edir_hit : (x_6).edir_hit, edir_way : (x_6).edir_way, edir_slot :
        (x_6).edir_slot, info : (x_6).info, value_write : (Bool)'(False),
        value : unpack(0), may_victim : (x_6).may_victim, reps :
        (x_6).reps});
        Struct19 x_18 = (Struct19 {addr : (x_17).addr, info_write :
        (Bool)'(True), info_hit : (x_17).info_hit, info_way :
        (x_17).info_way, edir_hit : (x_17).edir_hit, edir_way :
        (x_17).edir_way, edir_slot : (x_17).edir_slot, info : Struct11
        {mesi_owned : ((x_17).info).mesi_owned, mesi_status :
        ((x_17).info).mesi_status, mesi_dir_st : (Struct18 {dir_st :
        (Bit#(3))'(3'h1), dir_excl : unpack(0), dir_sharers :
        unpack(0)}).dir_st, mesi_dir_sharers : (((Struct18 {dir_st :
        (Bit#(3))'(3'h1), dir_excl : unpack(0), dir_sharers :
        unpack(0)}).dir_st) == ((Bit#(3))'(3'h2)) ? ((Struct18 {dir_st :
        (Bit#(3))'(3'h1), dir_excl : unpack(0), dir_sharers :
        unpack(0)}).dir_sharers) : (((Bit#(2))'(2'h1)) << ((Struct18 {dir_st
        : (Bit#(3))'(3'h1), dir_excl : unpack(0), dir_sharers :
        unpack(0)}).dir_excl)))}, value_write : (x_17).value_write, value :
        (x_17).value, may_victim : (x_17).may_victim, reps :
        (x_17).reps});
        Struct19 x_19 = (Struct19 {addr : (x_18).addr, info_write :
        (Bool)'(True), info_hit : (x_18).info_hit, info_way :
        (x_18).info_way, edir_hit : (x_18).edir_hit, edir_way :
        (x_18).edir_way, edir_slot : (x_18).edir_slot, info : Struct11
        {mesi_owned : ((x_18).info).mesi_owned, mesi_status :
        (Bit#(3))'(3'h1), mesi_dir_st : ((x_18).info).mesi_dir_st,
        mesi_dir_sharers : ((x_18).info).mesi_dir_sharers}, value_write :
        (x_18).value_write, value : (x_18).value, may_victim :
        (x_18).may_victim, reps : (x_18).reps});
        Struct19 x_20 = (Struct19 {addr : (x_19).addr, info_write :
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
            let x_21 <- victims__00__setVictim(Struct20 {victim_idx :
            (x_8).data, victim_info : (x_20).info, victim_value :
            (x_20).value});
            x_23 = x_9;
        end else begin
            let x_22 <- cache__00__valueRsLineRq(x_20);
            x_23 = x_22;
        end
        let x_24 <- releaseMSHR_00(x_4);
        Struct21 x_25 = (Struct21 {enq_type : (((x_16)[2:1]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : ((((x_16)[2:1]) ==
        ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : (x_16)[0:0], enq_msg : Struct1 {id : (Bit#(6))'(6'hd),
        type_ : (Bool)'(True), addr : (x_15).addr, value : unpack(0)}});
        let x_26 <- makeEnq_parentChildren00(x_25);
    endrule

    rule rule_exec_00_11011;
        $display ("Rule fired: rule_exec_00_11011 at %t", $time);
        let x_0 <- deq_fifoL2E_00();
        Struct7 x_1 = ((x_0).lr_ir_pp);
        Bit#(3) x_2 = ((x_1).ir_msg_from);
        Struct1 x_3 = ((x_1).ir_msg);
        Bit#(4) x_4 = ((x_1).ir_mshr_id);
        Bool x_5 = ((x_1).ir_is_rs_rel);
        when (x_5, noAction);
        Struct10 x_6 = ((x_0).lr_ir);
        Struct11 x_7 = ((x_6).info);
        Struct6 x_8 = ((x_1).ir_by_victim);
        Vector#(4, Bit#(64)) x_9 = ((x_0).lr_value);
        let x_10 <- getMSHR_00(x_4);
        Vector#(4, Bit#(64)) x_11 = (unpack(0));
        Bool x_12 = ((x_7).mesi_owned);
        Bit#(3) x_13 = ((x_7).mesi_status);
        Struct18 x_14 = (Struct18 {dir_st : (x_7).mesi_dir_st, dir_excl :
        ((((x_7).mesi_dir_sharers)[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(1))'(1'h0)) : (((Bit#(1))'(1'h1)) +
        ((((((x_7).mesi_dir_sharers)[1:1])[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(1))'(1'h0)) : (((Bit#(1))'(1'h1)) + (unpack(0))))))),
        dir_sharers : (x_7).mesi_dir_sharers});
        when (((x_10).m_status) == ((Bit#(3))'(3'h4)), noAction);
        when ((x_10).m_rsb, noAction);
        when ((((x_10).m_msg).type_) == ((Bool)'(False)), noAction);
        when ((((x_10).m_msg).id) == ((Bit#(6))'(6'he)), noAction);
        when (((x_10).m_dl_rss) == ((x_10).m_dl_rss), noAction);
        when ((Bool)'(True), noAction);
        Struct1 x_15 = ((x_10).m_msg);
        Bit#(3) x_16 = ((x_10).m_qidx);
        Struct19 x_17 = (Struct19 {addr : (x_3).addr, info_write :
        (Bool)'(False), info_hit : (x_6).info_hit, info_way : (x_6).info_way,
        edir_hit : (x_6).edir_hit, edir_way : (x_6).edir_way, edir_slot :
        (x_6).edir_slot, info : (x_6).info, value_write : (Bool)'(False),
        value : unpack(0), may_victim : (x_6).may_victim, reps :
        (x_6).reps});
        Struct19 x_18 = (Struct19 {addr : (x_17).addr, info_write :
        (Bool)'(True), info_hit : (x_17).info_hit, info_way :
        (x_17).info_way, edir_hit : (x_17).edir_hit, edir_way :
        (x_17).edir_way, edir_slot : (x_17).edir_slot, info : Struct11
        {mesi_owned : ((x_17).info).mesi_owned, mesi_status :
        ((x_17).info).mesi_status, mesi_dir_st : (Struct18 {dir_st :
        (Bit#(3))'(3'h1), dir_excl : unpack(0), dir_sharers :
        unpack(0)}).dir_st, mesi_dir_sharers : (((Struct18 {dir_st :
        (Bit#(3))'(3'h1), dir_excl : unpack(0), dir_sharers :
        unpack(0)}).dir_st) == ((Bit#(3))'(3'h2)) ? ((Struct18 {dir_st :
        (Bit#(3))'(3'h1), dir_excl : unpack(0), dir_sharers :
        unpack(0)}).dir_sharers) : (((Bit#(2))'(2'h1)) << ((Struct18 {dir_st
        : (Bit#(3))'(3'h1), dir_excl : unpack(0), dir_sharers :
        unpack(0)}).dir_excl)))}, value_write : (x_17).value_write, value :
        (x_17).value, may_victim : (x_17).may_victim, reps :
        (x_17).reps});
        Struct19 x_19 = (Struct19 {addr : (x_18).addr, info_write :
        (Bool)'(True), info_hit : (x_18).info_hit, info_way :
        (x_18).info_way, edir_hit : (x_18).edir_hit, edir_way :
        (x_18).edir_way, edir_slot : (x_18).edir_slot, info : Struct11
        {mesi_owned : ((x_18).info).mesi_owned, mesi_status :
        (Bit#(3))'(3'h1), mesi_dir_st : ((x_18).info).mesi_dir_st,
        mesi_dir_sharers : ((x_18).info).mesi_dir_sharers}, value_write :
        (x_18).value_write, value : (x_18).value, may_victim :
        (x_18).may_victim, reps : (x_18).reps});
        Struct19 x_20 = (Struct19 {addr : (x_19).addr, info_write :
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
            let x_21 <- victims__00__setVictim(Struct20 {victim_idx :
            (x_8).data, victim_info : (x_20).info, victim_value :
            (x_20).value});
            x_23 = x_9;
        end else begin
            let x_22 <- cache__00__valueRsLineRq(x_20);
            x_23 = x_22;
        end
        let x_24 <- releaseMSHR_00(x_4);
        Struct21 x_25 = (Struct21 {enq_type : (((x_16)[2:1]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : ((((x_16)[2:1]) ==
        ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : (x_16)[0:0], enq_msg : Struct1 {id : (Bit#(6))'(6'hf),
        type_ : (Bool)'(True), addr : (x_15).addr, value : unpack(0)}});
        let x_26 <- makeEnq_parentChildren00(x_25);
    endrule

    rule rule_exec_00_20;
        $display ("Rule fired: rule_exec_00_20 at %t", $time);
        let x_0 <- victims__00__getFirstVictim();
        Bit#(64) x_1 = ((x_0).victim_addr);
        Struct11 x_2 = ((x_0).victim_info);
        Vector#(4, Bit#(64)) x_3 = ((x_0).victim_value);
        Struct1 x_4 = (Struct1 {id : unpack(0), type_ : (Bool)'(False), addr
        : x_1, value : unpack(0)});
        let x_5 <- getULImm_00(x_4);
        let x_6 <- victims__00__setVictimRq(Struct27 {victim_addr : x_1,
        victim_req : x_5});
        Struct17 x_7 = (Struct17 {m_status : (Bit#(3))'(3'h4), m_next :
        unpack(0), m_is_ul : (Bool)'(True), m_msg : x_4, m_qidx : unpack(0),
        m_rsb : (Bool)'(False), m_dl_rss_from : unpack(0), m_dl_rss_recv :
        unpack(0), m_dl_rss : unpack(0)});
        Vector#(4, Bit#(64)) x_8 = (unpack(0));
        Bool x_9 = ((x_2).mesi_owned);
        Bit#(3) x_10 = ((x_2).mesi_status);
        Struct18 x_11 = (Struct18 {dir_st : (x_2).mesi_dir_st, dir_excl :
        ((((x_2).mesi_dir_sharers)[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(1))'(1'h0)) : (((Bit#(1))'(1'h1)) +
        ((((((x_2).mesi_dir_sharers)[1:1])[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(1))'(1'h0)) : (((Bit#(1))'(1'h1)) + (unpack(0))))))),
        dir_sharers : (x_2).mesi_dir_sharers});
        when (! ((x_4).type_), noAction);
        when (((x_9) == ((Bool)'(False))) && (((((Bit#(3))'(3'h0)) < (x_10))
        && ((x_10) < ((Bit#(3))'(3'h4)))) && (((x_11).dir_st) ==
        ((Bit#(3))'(3'h1)))), noAction);
        Struct21 x_12 = (Struct21 {enq_type : ((((Bit#(3))'(3'h0))[2:1]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : (((((Bit#(3))'(3'h0))[2:1])
        == ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : ((Bit#(3))'(3'h0))[0:0], enq_msg : Struct1 {id :
        (Bit#(6))'(6'h14), type_ : (Bool)'(False), addr : (x_4).addr, value :
        unpack(0)}});
        let x_13 <- makeEnq_parentChildren00(x_12);
    endrule

    rule rule_exec_00_21;
        $display ("Rule fired: rule_exec_00_21 at %t", $time);
        let x_0 <- victims__00__getFirstVictim();
        Bit#(64) x_1 = ((x_0).victim_addr);
        Struct11 x_2 = ((x_0).victim_info);
        Vector#(4, Bit#(64)) x_3 = ((x_0).victim_value);
        Struct1 x_4 = (Struct1 {id : unpack(0), type_ : (Bool)'(False), addr
        : x_1, value : unpack(0)});
        let x_5 <- getULImm_00(x_4);
        let x_6 <- victims__00__setVictimRq(Struct27 {victim_addr : x_1,
        victim_req : x_5});
        Struct17 x_7 = (Struct17 {m_status : (Bit#(3))'(3'h4), m_next :
        unpack(0), m_is_ul : (Bool)'(True), m_msg : x_4, m_qidx : unpack(0),
        m_rsb : (Bool)'(False), m_dl_rss_from : unpack(0), m_dl_rss_recv :
        unpack(0), m_dl_rss : unpack(0)});
        Vector#(4, Bit#(64)) x_8 = (unpack(0));
        Bool x_9 = ((x_2).mesi_owned);
        Bit#(3) x_10 = ((x_2).mesi_status);
        Struct18 x_11 = (Struct18 {dir_st : (x_2).mesi_dir_st, dir_excl :
        ((((x_2).mesi_dir_sharers)[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(1))'(1'h0)) : (((Bit#(1))'(1'h1)) +
        ((((((x_2).mesi_dir_sharers)[1:1])[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(1))'(1'h0)) : (((Bit#(1))'(1'h1)) + (unpack(0))))))),
        dir_sharers : (x_2).mesi_dir_sharers});
        when (! ((x_4).type_), noAction);
        when ((((x_11).dir_st) == ((Bit#(3))'(3'h1))) && ((((x_9) ==
        ((Bool)'(True))) && (((Bit#(3))'(3'h1)) < (x_10))) || (((x_9) ==
        ((Bool)'(False))) && ((((Bit#(3))'(3'h0)) < (x_10)) && ((x_10) <
        ((Bit#(3))'(3'h3)))))), noAction);
        Struct21 x_12 = (Struct21 {enq_type : ((((Bit#(3))'(3'h0))[2:1]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : (((((Bit#(3))'(3'h0))[2:1])
        == ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : ((Bit#(3))'(3'h0))[0:0], enq_msg : Struct1 {id :
        (Bit#(6))'(6'h15), type_ : (Bool)'(False), addr : (x_4).addr, value :
        x_3}});
        let x_13 <- makeEnq_parentChildren00(x_12);
    endrule

    rule rule_exec_00_22;
        $display ("Rule fired: rule_exec_00_22 at %t", $time);
        let x_0 <- deq_fifoL2E_00();
        Struct7 x_1 = ((x_0).lr_ir_pp);
        Bit#(3) x_2 = ((x_1).ir_msg_from);
        Struct1 x_3 = ((x_1).ir_msg);
        Bit#(4) x_4 = ((x_1).ir_mshr_id);
        Bool x_5 = ((x_1).ir_is_rs_rel);
        when (! (x_5), noAction);
        Struct10 x_6 = ((x_0).lr_ir);
        Struct11 x_7 = ((x_6).info);
        Struct6 x_8 = ((x_1).ir_by_victim);
        Vector#(4, Bit#(64)) x_9 = ((x_0).lr_value);
        let x_10 <- getMSHR_00(x_4);
        Vector#(4, Bit#(64)) x_11 = (unpack(0));
        Bool x_12 = ((x_7).mesi_owned);
        Bit#(3) x_13 = ((x_7).mesi_status);
        Struct18 x_14 = (Struct18 {dir_st : (x_7).mesi_dir_st, dir_excl :
        ((((x_7).mesi_dir_sharers)[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(1))'(1'h0)) : (((Bit#(1))'(1'h1)) +
        ((((((x_7).mesi_dir_sharers)[1:1])[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(1))'(1'h0)) : (((Bit#(1))'(1'h1)) + (unpack(0))))))),
        dir_sharers : (x_7).mesi_dir_sharers});
        when ((x_2) == ({((Bit#(2))'(2'h2)),((Bit#(1))'(1'h0))}),
        noAction);
        when (((x_3).id) == ((Bit#(6))'(6'h16)), noAction);
        when (((x_10).m_status) == ((Bit#(3))'(3'h4)), noAction);
        when (! ((x_10).m_rsb), noAction);
        when ((x_3).type_, noAction);
        when ((Bool)'(True), noAction);
        Struct1 x_15 = (x_3);
        Struct19 x_16 = (Struct19 {addr : (x_3).addr, info_write :
        (Bool)'(False), info_hit : (x_6).info_hit, info_way : (x_6).info_way,
        edir_hit : (x_6).edir_hit, edir_way : (x_6).edir_way, edir_slot :
        (x_6).edir_slot, info : (x_6).info, value_write : (Bool)'(False),
        value : unpack(0), may_victim : (x_6).may_victim, reps :
        (x_6).reps});
        Struct19 x_17 = (Struct19 {addr : (x_16).addr, info_write :
        (Bool)'(True), info_hit : (x_16).info_hit, info_way :
        (x_16).info_way, edir_hit : (x_16).edir_hit, edir_way :
        (x_16).edir_way, edir_slot : (x_16).edir_slot, info : Struct11
        {mesi_owned : ((x_16).info).mesi_owned, mesi_status :
        (Bit#(3))'(3'h0), mesi_dir_st : ((x_16).info).mesi_dir_st,
        mesi_dir_sharers : ((x_16).info).mesi_dir_sharers}, value_write :
        (x_16).value_write, value : (x_16).value, may_victim :
        (x_16).may_victim, reps : (x_16).reps});
        Struct19 x_18 = (Struct19 {addr : (x_17).addr, info_write :
        (Bool)'(True), info_hit : (x_17).info_hit, info_way :
        (x_17).info_way, edir_hit : (x_17).edir_hit, edir_way :
        (x_17).edir_way, edir_slot : (x_17).edir_slot, info : Struct11
        {mesi_owned : (Bool)'(False), mesi_status :
        ((x_17).info).mesi_status, mesi_dir_st : ((x_17).info).mesi_dir_st,
        mesi_dir_sharers : ((x_17).info).mesi_dir_sharers}, value_write :
        (x_17).value_write, value : (x_17).value, may_victim :
        (x_17).may_victim, reps :
        (x_17).reps});
        let x_21 = ?;
        if ((x_8).valid) begin
            let x_19 <- victims__00__setVictim(Struct20 {victim_idx :
            (x_8).data, victim_info : (x_18).info, victim_value :
            (x_18).value});
            x_21 = x_9;
        end else begin
            let x_20 <- cache__00__valueRsLineRq(x_18);
            x_21 = x_20;
        end
        let x_22 <- releaseMSHR_00(x_4);
    endrule

    rule rule_exec_00_23;
        $display ("Rule fired: rule_exec_00_23 at %t", $time);
        let x_0 <- deq_fifoL2E_00();
        Struct7 x_1 = ((x_0).lr_ir_pp);
        Bit#(3) x_2 = ((x_1).ir_msg_from);
        Struct1 x_3 = ((x_1).ir_msg);
        Bit#(4) x_4 = ((x_1).ir_mshr_id);
        Bool x_5 = ((x_1).ir_is_rs_rel);
        when (x_5, noAction);
        Struct10 x_6 = ((x_0).lr_ir);
        Struct11 x_7 = ((x_6).info);
        Struct6 x_8 = ((x_1).ir_by_victim);
        Vector#(4, Bit#(64)) x_9 = ((x_0).lr_value);
        let x_10 <- getMSHR_00(x_4);
        Vector#(4, Bit#(64)) x_11 = (unpack(0));
        Bool x_12 = ((x_7).mesi_owned);
        Bit#(3) x_13 = ((x_7).mesi_status);
        Struct18 x_14 = (Struct18 {dir_st : (x_7).mesi_dir_st, dir_excl :
        ((((x_7).mesi_dir_sharers)[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(1))'(1'h0)) : (((Bit#(1))'(1'h1)) +
        ((((((x_7).mesi_dir_sharers)[1:1])[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(1))'(1'h0)) : (((Bit#(1))'(1'h1)) + (unpack(0))))))),
        dir_sharers : (x_7).mesi_dir_sharers});
        when ((((x_13) == ((Bit#(3))'(3'h1))) && (! (((x_14).dir_st) ==
        ((Bit#(3))'(3'h3))))) || (((x_13) == ((Bit#(3))'(3'h2))) && ((x_12)
        == ((Bool)'(False)))), noAction);
        Struct19 x_15 = (Struct19 {addr : (x_3).addr, info_write :
        (Bool)'(False), info_hit : (x_6).info_hit, info_way : (x_6).info_way,
        edir_hit : (x_6).edir_hit, edir_way : (x_6).edir_way, edir_slot :
        (x_6).edir_slot, info : (x_6).info, value_write : (Bool)'(False),
        value : unpack(0), may_victim : (x_6).may_victim, reps :
        (x_6).reps});
        Struct19 x_16 = (Struct19 {addr : (x_15).addr, info_write :
        (Bool)'(True), info_hit : (x_15).info_hit, info_way :
        (x_15).info_way, edir_hit : (x_15).edir_hit, edir_way :
        (x_15).edir_way, edir_slot : (x_15).edir_slot, info : Struct11
        {mesi_owned : ((x_15).info).mesi_owned, mesi_status :
        (Bit#(3))'(3'h0), mesi_dir_st : ((x_15).info).mesi_dir_st,
        mesi_dir_sharers : ((x_15).info).mesi_dir_sharers}, value_write :
        (x_15).value_write, value : (x_15).value, may_victim :
        (x_15).may_victim, reps :
        (x_15).reps});
        let x_19 = ?;
        if ((x_8).valid) begin
            let x_17 <- victims__00__setVictim(Struct20 {victim_idx :
            (x_8).data, victim_info : (x_16).info, victim_value :
            (x_16).value});
            x_19 = x_9;
        end else begin
            let x_18 <- cache__00__valueRsLineRq(x_16);
            x_19 = x_18;
        end
    endrule

    // No methods in this module
endmodule

interface Module84;

endinterface

module mkModule84#(function Action victims__000__setVictimRq(Struct55 _),
    function ActionValue#(Bit#(3)) getULImm_000(Struct1 _),
    function ActionValue#(Struct48) victims__000__getFirstVictim(),
    function Action victims__000__setVictim(Struct54 _),
    function Action registerUL_000(Struct53 _),
    function Action makeEnq_parentChildren000(Struct21 _),
    function ActionValue#(Vector#(4, Bit#(64))) cache__000__valueRsLineRq(Struct52 _),
    function ActionValue#(Struct51) getMSHR_000(Bit#(3) _),
    function ActionValue#(Struct47) deq_fifoL2E_000(),
    function ActionValue#(Struct42) deq_fifoI2L_child_000(),
    function Action enq_fifoI2L_child_000(Struct42 _),
    function ActionValue#(Struct42) deq_fifoN2I_child_000(),
    function ActionValue#(Struct50) getWait_000(),
    function ActionValue#(Bit#(3)) findDL_000(Bit#(64) _),
    function Action enq_fifoN2I_child_000(Struct42 _),
    function ActionValue#(Struct40) getCRqSlot_000(Struct39 _),
    function ActionValue#(Struct2) deq_fifoCInput_000(),
    function ActionValue#(Struct48) victims__000__getVictim(Bit#(1) _),
    function Action enq_fifoL2E_000(Struct47 _),
    function ActionValue#(Struct45) cache__000__infoRsValueRq(Bit#(64) _),
    function ActionValue#(Struct42) deq_fifoI2L_parent_000(),
    function Action addRs_000(Struct44 _),
    function Action enq_fifoI2L_parent_000(Struct42 _),
    function Action cache__000__infoRq(Bit#(64) _),
    function ActionValue#(Struct42) deq_fifoN2I_parent_000(),
    function ActionValue#(Struct43) getRsReady_000(),
    function Action releaseMSHR_000(Bit#(3) _),
    function ActionValue#(Bit#(3)) victims__000__releaseVictim(Bit#(64) _),
    function ActionValue#(Bit#(3)) findUL_000(Bit#(64) _),
    function Action enq_fifoN2I_parent_000(Struct42 _),
    function ActionValue#(Struct41) victims__000findVictim(Bit#(64) _),
    function ActionValue#(Struct40) getPRqSlot_000(Struct39 _),
    function ActionValue#(Struct2) deq_fifoPInput000())
    (Module84);

    rule rule_in_prq_parent_000;
        $display ("Rule fired: rule_in_prq_parent_000 at %t", $time);
        let x_0 <- deq_fifoPInput000();
        Bit#(3) x_1 = ((x_0).in_msg_from);
        when ((x_1) == ({((Bit#(2))'(2'h2)),((Bit#(1))'(1'h0))}),
        noAction);
        Struct1 x_2 = ((x_0).in_msg);
        when (! ((x_2).type_), noAction);
        let x_3 <- getPRqSlot_000(Struct39 {r_id : unpack(0), r_msg : x_2,
        r_msg_from : (x_0).in_msg_from});
        when ((x_3).s_has_slot,
        noAction);
        if (! ((x_3).s_conflict)) begin
            let x_4 <- victims__000findVictim((x_2).addr);
            Struct42 x_5 = (Struct42 {ir_is_rs_rel : (Bool)'(False),
            ir_is_rs_acc : (Bool)'(False), ir_msg : (x_0).in_msg, ir_msg_from
            : x_1, ir_mshr_id : (x_3).s_id, ir_by_victim : x_4});
            let x_6 <- enq_fifoN2I_parent_000(x_5);
        end else begin

        end
    endrule

    rule rule_in_prs_parent_000;
        $display ("Rule fired: rule_in_prs_parent_000 at %t", $time);
        let x_0 <- deq_fifoPInput000();
        Bit#(3) x_1 = ((x_0).in_msg_from);
        when ((x_1) == ({((Bit#(2))'(2'h2)),((Bit#(1))'(1'h0))}),
        noAction);
        Struct1 x_2 = ((x_0).in_msg);
        when (((x_2).type_) && (! (((x_2).id) == ((Bit#(6))'(6'h16)))),
        noAction);
        let x_3 <- findUL_000((x_2).addr);
        let x_4 <- victims__000findVictim((x_2).addr);
        Struct42 x_5 = (Struct42 {ir_is_rs_rel : (Bool)'(False), ir_is_rs_acc
        : (Bool)'(False), ir_msg : (x_0).in_msg, ir_msg_from : x_1,
        ir_mshr_id : x_3, ir_by_victim : x_4});
        let x_6 <- enq_fifoN2I_parent_000(x_5);
    endrule

    rule rule_in_invrs_parent_000;
        $display ("Rule fired: rule_in_invrs_parent_000 at %t", $time);
        let x_0 <- deq_fifoPInput000();
        Bit#(3) x_1 = ((x_0).in_msg_from);
        when ((x_1) == ({((Bit#(2))'(2'h2)),((Bit#(1))'(1'h0))}),
        noAction);
        Struct1 x_2 = ((x_0).in_msg);
        when (((x_2).type_) && (((x_2).id) == ((Bit#(6))'(6'h16))),
        noAction);
        let x_3 <- victims__000__releaseVictim((x_2).addr);
        let x_4 <- releaseMSHR_000(x_3);
    endrule

    rule rule_in_rsrel_parent_000;
        $display ("Rule fired: rule_in_rsrel_parent_000 at %t", $time);
        let x_0 <- getRsReady_000();
        Struct1 x_1 = (Struct1 {id : unpack(0), type_ : unpack(0), addr :
        (x_0).r_addr, value : unpack(0)});
        Struct42 x_2 = (Struct42 {ir_is_rs_rel : (Bool)'(True), ir_is_rs_acc
        : (Bool)'(False), ir_msg : x_1, ir_msg_from : unpack(0), ir_mshr_id :
        (x_0).r_id, ir_by_victim : Struct41 {valid : (Bool)'(False), data :
        unpack(0)}});
        let x_3 <- enq_fifoN2I_parent_000(x_2);
    endrule

    rule rule_ir_cache_parent_000;
        $display ("Rule fired: rule_ir_cache_parent_000 at %t", $time);
        let x_0 <- deq_fifoN2I_parent_000();
        when (! ((x_0).ir_is_rs_acc), noAction);
        when (! (((x_0).ir_by_victim).valid), noAction);
        Struct1 x_1 = ((x_0).ir_msg);
        let x_2 <- cache__000__infoRq((x_1).addr);
        let x_3 <- enq_fifoI2L_parent_000(x_0);
    endrule

    rule rule_ir_victims_parent_000;
        $display ("Rule fired: rule_ir_victims_parent_000 at %t", $time);
        let x_0 <- deq_fifoN2I_parent_000();
        when (! ((x_0).ir_is_rs_acc), noAction);
        when (((x_0).ir_by_victim).valid, noAction);
        let x_1 <- enq_fifoI2L_parent_000(x_0);
    endrule

    rule rule_ir_rs_acc_parent_000;
        $display ("Rule fired: rule_ir_rs_acc_parent_000 at %t", $time);
        let x_0 <- deq_fifoN2I_parent_000();
        when ((x_0).ir_is_rs_acc, noAction);
        let x_1 <- addRs_000(Struct44 {r_id : (x_0).ir_mshr_id, r_midx :
        ((x_0).ir_msg_from)[0:0], r_msg : (x_0).ir_msg});
    endrule

    rule rule_lr_cache_parent_000;
        $display ("Rule fired: rule_lr_cache_parent_000 at %t", $time);
        let x_0 <- deq_fifoI2L_parent_000();
        when (! (((x_0).ir_by_victim).valid), noAction);
        let x_1 <- cache__000__infoRsValueRq(((x_0).ir_msg).addr);
        Struct47 x_2 = (Struct47 {lr_ir_pp : x_0, lr_ir : x_1, lr_value :
        unpack(0)});
        let x_3 <- enq_fifoL2E_000(x_2);
    endrule

    rule rule_lr_victims_parent_000;
        $display ("Rule fired: rule_lr_victims_parent_000 at %t", $time);
        let x_0 <- deq_fifoI2L_parent_000();
        when (((x_0).ir_by_victim).valid, noAction);
        let x_1 <- victims__000__getVictim((Bit#(1))'(1'h0));
        Struct45 x_2 = (Struct45 {info_index : unpack(0), info_hit :
        unpack(0), info_way : unpack(0), edir_hit : unpack(0), edir_way :
        unpack(0), edir_slot : unpack(0), info : (x_1).victim_info,
        may_victim : unpack(0), reps : unpack(0)});
        Struct47 x_3 = (Struct47 {lr_ir_pp : x_0, lr_ir : x_2, lr_value :
        (x_1).victim_value});
        let x_4 <- enq_fifoL2E_000(x_3);
    endrule

    rule rule_in_crq_child_000;
        $display ("Rule fired: rule_in_crq_child_000 at %t", $time);
        let x_0 <- deq_fifoCInput_000();
        Bit#(3) x_1 = ((x_0).in_msg_from);
        when (((x_1)[2:1]) == ((Bit#(2))'(2'h0)), noAction);
        Struct1 x_2 = ((x_0).in_msg);
        when (! ((x_2).type_), noAction);
        let x_3 <- getCRqSlot_000(Struct39 {r_id : unpack(0), r_msg : x_2,
        r_msg_from : x_1});
        when ((x_3).s_has_slot,
        noAction);
        if (! ((x_3).s_conflict)) begin
            let x_4 <- victims__000findVictim((x_2).addr);
            Struct42 x_5 = (Struct42 {ir_is_rs_rel : (Bool)'(False),
            ir_is_rs_acc : (Bool)'(False), ir_msg : (x_0).in_msg, ir_msg_from
            : x_1, ir_mshr_id : (x_3).s_id, ir_by_victim : x_4});
            let x_6 <- enq_fifoN2I_child_000(x_5);
        end else begin

        end
    endrule

    rule rule_in_crs_child_000;
        $display ("Rule fired: rule_in_crs_child_000 at %t", $time);
        let x_0 <- deq_fifoCInput_000();
        Bit#(3) x_1 = ((x_0).in_msg_from);
        when (((x_1)[2:1]) == ((Bit#(2))'(2'h1)), noAction);
        Struct1 x_2 = ((x_0).in_msg);
        when ((x_2).type_, noAction);
        let x_3 <- findDL_000((x_2).addr);
        let x_4 <- victims__000findVictim((x_2).addr);
        Struct42 x_5 = (Struct42 {ir_is_rs_rel : (Bool)'(False), ir_is_rs_acc
        : (Bool)'(True), ir_msg : x_2, ir_msg_from : x_1, ir_mshr_id : x_3,
        ir_by_victim : x_4});
        let x_6 <- enq_fifoN2I_child_000(x_5);
    endrule

    rule rule_in_retry_child_000;
        $display ("Rule fired: rule_in_retry_child_000 at %t", $time);
        let x_0 <- getWait_000();
        when ((x_0).valid, noAction);
        Struct39 x_1 = ((x_0).data);
        Struct1 x_2 = ((x_1).r_msg);
        let x_3 <- victims__000findVictim((x_2).addr);
        Struct42 x_4 = (Struct42 {ir_is_rs_rel : (Bool)'(False), ir_is_rs_acc
        : (Bool)'(False), ir_msg : x_2, ir_msg_from : (x_1).r_msg_from,
        ir_mshr_id : (x_1).r_id, ir_by_victim : x_3});
        let x_5 <- enq_fifoN2I_child_000(x_4);
    endrule

    rule rule_ir_cache_child_000;
        $display ("Rule fired: rule_ir_cache_child_000 at %t", $time);
        let x_0 <- deq_fifoN2I_child_000();
        when (! ((x_0).ir_is_rs_acc), noAction);
        when (! (((x_0).ir_by_victim).valid), noAction);
        Struct1 x_1 = ((x_0).ir_msg);
        let x_2 <- cache__000__infoRq((x_1).addr);
        let x_3 <- enq_fifoI2L_child_000(x_0);
    endrule

    rule rule_ir_victims_child_000;
        $display ("Rule fired: rule_ir_victims_child_000 at %t", $time);
        let x_0 <- deq_fifoN2I_child_000();
        when (! ((x_0).ir_is_rs_acc), noAction);
        when (((x_0).ir_by_victim).valid, noAction);
        let x_1 <- enq_fifoI2L_child_000(x_0);
    endrule

    rule rule_ir_rs_acc_child_000;
        $display ("Rule fired: rule_ir_rs_acc_child_000 at %t", $time);
        let x_0 <- deq_fifoN2I_child_000();
        when ((x_0).ir_is_rs_acc, noAction);
        let x_1 <- addRs_000(Struct44 {r_id : (x_0).ir_mshr_id, r_midx :
        ((x_0).ir_msg_from)[0:0], r_msg : (x_0).ir_msg});
    endrule

    rule rule_lr_cache_child_000;
        $display ("Rule fired: rule_lr_cache_child_000 at %t", $time);
        let x_0 <- deq_fifoI2L_child_000();
        when (! (((x_0).ir_by_victim).valid), noAction);
        let x_1 <- cache__000__infoRsValueRq(((x_0).ir_msg).addr);
        Struct47 x_2 = (Struct47 {lr_ir_pp : x_0, lr_ir : x_1, lr_value :
        unpack(0)});
        let x_3 <- enq_fifoL2E_000(x_2);
    endrule

    rule rule_lr_victims_child_000;
        $display ("Rule fired: rule_lr_victims_child_000 at %t", $time);
        let x_0 <- deq_fifoI2L_child_000();
        when (((x_0).ir_by_victim).valid, noAction);
        let x_1 <- victims__000__getVictim((Bit#(1))'(1'h0));
        Struct45 x_2 = (Struct45 {info_index : unpack(0), info_hit :
        unpack(0), info_way : unpack(0), edir_hit : unpack(0), edir_way :
        unpack(0), edir_slot : unpack(0), info : (x_1).victim_info,
        may_victim : unpack(0), reps : unpack(0)});
        Struct47 x_3 = (Struct47 {lr_ir_pp : x_0, lr_ir : x_2, lr_value :
        (x_1).victim_value});
        let x_4 <- enq_fifoL2E_000(x_3);
    endrule

    rule rule_exec_000_00;
        $display ("Rule fired: rule_exec_000_00 at %t", $time);
        let x_0 <- deq_fifoL2E_000();
        Struct42 x_1 = ((x_0).lr_ir_pp);
        Bit#(3) x_2 = ((x_1).ir_msg_from);
        Struct1 x_3 = ((x_1).ir_msg);
        Bit#(3) x_4 = ((x_1).ir_mshr_id);
        Bool x_5 = ((x_1).ir_is_rs_rel);
        when (! (x_5), noAction);
        Struct45 x_6 = ((x_0).lr_ir);
        Struct11 x_7 = ((x_6).info);
        Struct41 x_8 = ((x_1).ir_by_victim);
        Vector#(4, Bit#(64)) x_9 = ((x_0).lr_value);
        let x_10 <- getMSHR_000(x_4);
        Vector#(4, Bit#(64)) x_11 = (unpack(0));
        Bool x_12 = ((x_7).mesi_owned);
        Bit#(3) x_13 = ((x_7).mesi_status);
        Struct18 x_14 = (Struct18 {dir_st : (x_7).mesi_dir_st, dir_excl :
        ((((x_7).mesi_dir_sharers)[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(1))'(1'h0)) : (((Bit#(1))'(1'h1)) +
        ((((((x_7).mesi_dir_sharers)[1:1])[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(1))'(1'h0)) : (((Bit#(1))'(1'h1)) + (unpack(0))))))),
        dir_sharers : (x_7).mesi_dir_sharers});
        when ((x_2) == ((Bit#(3))'(3'h0)), noAction);
        when (((x_3).id) == ((Bit#(6))'(6'h0)), noAction);
        when (! ((x_3).type_), noAction);
        when (! ((x_13) < ((Bit#(3))'(3'h2))), noAction);
        Struct1 x_15 = (x_3);
        Struct52 x_16 = (Struct52 {addr : (x_3).addr, info_write :
        (Bool)'(False), info_hit : (x_6).info_hit, info_way : (x_6).info_way,
        edir_hit : (x_6).edir_hit, edir_way : (x_6).edir_way, edir_slot :
        (x_6).edir_slot, info : (x_6).info, value_write : (Bool)'(False),
        value : unpack(0), may_victim : (x_6).may_victim, reps :
        (x_6).reps});
        let x_18 = ?;
        if ((x_8).valid) begin
            x_18 = x_9;
        end else begin
            let x_17 <- cache__000__valueRsLineRq(unpack(0));
            x_18 = x_17;
        end
        Struct21 x_19 = (Struct21 {enq_type : ((((Bit#(3))'(3'h4))[2:1]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : (((((Bit#(3))'(3'h4))[2:1])
        == ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : ((Bit#(3))'(3'h4))[0:0], enq_msg : Struct1 {id :
        (Bit#(6))'(6'h1), type_ : (Bool)'(True), addr : (x_15).addr, value :
        x_18}});
        let x_20 <- makeEnq_parentChildren000(x_19);
    endrule

    rule rule_exec_000_01;
        $display ("Rule fired: rule_exec_000_01 at %t", $time);
        let x_0 <- deq_fifoL2E_000();
        Struct42 x_1 = ((x_0).lr_ir_pp);
        Bit#(3) x_2 = ((x_1).ir_msg_from);
        Struct1 x_3 = ((x_1).ir_msg);
        Bit#(3) x_4 = ((x_1).ir_mshr_id);
        Bool x_5 = ((x_1).ir_is_rs_rel);
        when (! (x_5), noAction);
        Struct45 x_6 = ((x_0).lr_ir);
        Struct11 x_7 = ((x_6).info);
        Struct41 x_8 = ((x_1).ir_by_victim);
        Vector#(4, Bit#(64)) x_9 = ((x_0).lr_value);
        let x_10 <- getMSHR_000(x_4);
        Vector#(4, Bit#(64)) x_11 = (unpack(0));
        Bool x_12 = ((x_7).mesi_owned);
        Bit#(3) x_13 = ((x_7).mesi_status);
        Struct18 x_14 = (Struct18 {dir_st : (x_7).mesi_dir_st, dir_excl :
        ((((x_7).mesi_dir_sharers)[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(1))'(1'h0)) : (((Bit#(1))'(1'h1)) +
        ((((((x_7).mesi_dir_sharers)[1:1])[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(1))'(1'h0)) : (((Bit#(1))'(1'h1)) + (unpack(0))))))),
        dir_sharers : (x_7).mesi_dir_sharers});
        when ((x_2) == ((Bit#(3))'(3'h0)), noAction);
        when (((x_3).id) == ((Bit#(6))'(6'h0)), noAction);
        when (! ((x_3).type_), noAction);
        when (! (((Bit#(3))'(3'h1)) < (x_13)), noAction);
        Struct1 x_15 = (x_3);
        Struct52 x_16 = (Struct52 {addr : (x_3).addr, info_write :
        (Bool)'(False), info_hit : (x_6).info_hit, info_way : (x_6).info_way,
        edir_hit : (x_6).edir_hit, edir_way : (x_6).edir_way, edir_slot :
        (x_6).edir_slot, info : (x_6).info, value_write : (Bool)'(False),
        value : unpack(0), may_victim : (x_6).may_victim, reps :
        (x_6).reps});
        let x_18 = ?;
        if ((x_8).valid) begin
            x_18 = x_9;
        end else begin
            let x_17 <- cache__000__valueRsLineRq(unpack(0));
            x_18 = x_17;
        end
        let x_19 <- registerUL_000(Struct53 {r_id : x_4, r_ul_rsb :
        (Bool)'(True), r_ul_rsbTo : ((Bit#(3))'(3'h4))[0:0]});
        Struct21 x_20 = (Struct21 {enq_type : ((((Bit#(3))'(3'h0))[2:1]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : (((((Bit#(3))'(3'h0))[2:1])
        == ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : ((Bit#(3))'(3'h0))[0:0], enq_msg : Struct1 {id :
        (Bit#(6))'(6'h2), type_ : (Bool)'(False), addr : (x_15).addr, value :
        unpack(0)}});
        let x_21 <- makeEnq_parentChildren000(x_20);
    endrule

    rule rule_exec_000_020;
        $display ("Rule fired: rule_exec_000_020 at %t", $time);
        let x_0 <- deq_fifoL2E_000();
        Struct42 x_1 = ((x_0).lr_ir_pp);
        Bit#(3) x_2 = ((x_1).ir_msg_from);
        Struct1 x_3 = ((x_1).ir_msg);
        Bit#(3) x_4 = ((x_1).ir_mshr_id);
        Bool x_5 = ((x_1).ir_is_rs_rel);
        when (! (x_5), noAction);
        Struct45 x_6 = ((x_0).lr_ir);
        Struct11 x_7 = ((x_6).info);
        Struct41 x_8 = ((x_1).ir_by_victim);
        Vector#(4, Bit#(64)) x_9 = ((x_0).lr_value);
        let x_10 <- getMSHR_000(x_4);
        Vector#(4, Bit#(64)) x_11 = (unpack(0));
        Bool x_12 = ((x_7).mesi_owned);
        Bit#(3) x_13 = ((x_7).mesi_status);
        Struct18 x_14 = (Struct18 {dir_st : (x_7).mesi_dir_st, dir_excl :
        ((((x_7).mesi_dir_sharers)[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(1))'(1'h0)) : (((Bit#(1))'(1'h1)) +
        ((((((x_7).mesi_dir_sharers)[1:1])[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(1))'(1'h0)) : (((Bit#(1))'(1'h1)) + (unpack(0))))))),
        dir_sharers : (x_7).mesi_dir_sharers});
        when ((x_2) == ({((Bit#(2))'(2'h2)),((Bit#(1))'(1'h0))}),
        noAction);
        when (((x_3).id) == ((Bit#(6))'(6'h3)), noAction);
        when (((x_10).m_status) == ((Bit#(3))'(3'h4)), noAction);
        when ((x_10).m_rsb, noAction);
        when ((((x_10).m_msg).type_) == ((Bool)'(False)), noAction);
        when ((((x_10).m_msg).id) == ((Bit#(6))'(6'h0)), noAction);
        when (((x_10).m_status) == ((Bit#(3))'(3'h4)), noAction);
        when ((x_10).m_rsb, noAction);
        when ((x_3).type_, noAction);
        when ((Bool)'(True), noAction);
        Struct1 x_15 = (x_3);
        Struct1 x_16 = ((x_10).m_msg);
        Bit#(3) x_17 = ({((Bit#(2))'(2'h2)),(((x_10).m_qidx)[0:0])});
        Struct52 x_18 = (Struct52 {addr : (x_3).addr, info_write :
        (Bool)'(False), info_hit : (x_6).info_hit, info_way : (x_6).info_way,
        edir_hit : (x_6).edir_hit, edir_way : (x_6).edir_way, edir_slot :
        (x_6).edir_slot, info : (x_6).info, value_write : (Bool)'(False),
        value : unpack(0), may_victim : (x_6).may_victim, reps :
        (x_6).reps});
        Struct52 x_19 = (Struct52 {addr : (x_18).addr, info_write :
        (Bool)'(True), info_hit : (x_18).info_hit, info_way :
        (x_18).info_way, edir_hit : (x_18).edir_hit, edir_way :
        (x_18).edir_way, edir_slot : (x_18).edir_slot, info : Struct11
        {mesi_owned : ((x_18).info).mesi_owned, mesi_status :
        (Bit#(3))'(3'h2), mesi_dir_st : ((x_18).info).mesi_dir_st,
        mesi_dir_sharers : ((x_18).info).mesi_dir_sharers}, value_write :
        (x_18).value_write, value : (x_18).value, may_victim :
        (x_18).may_victim, reps : (x_18).reps});
        Struct52 x_20 = (Struct52 {addr : (x_19).addr, info_write :
        (x_19).info_write, info_hit : (x_19).info_hit, info_way :
        (x_19).info_way, edir_hit : (x_19).edir_hit, edir_way :
        (x_19).edir_way, edir_slot : (x_19).edir_slot, info : (x_19).info,
        value_write : (Bool)'(True), value : (x_15).value, may_victim :
        (x_19).may_victim, reps :
        (x_19).reps});
        let x_23 = ?;
        if ((x_8).valid) begin
            let x_21 <- victims__000__setVictim(Struct54 {victim_idx :
            (x_8).data, victim_info : (x_20).info, victim_value :
            (x_20).value});
            x_23 = x_9;
        end else begin
            let x_22 <- cache__000__valueRsLineRq(x_20);
            x_23 = x_22;
        end
        let x_24 <- releaseMSHR_000(x_4);
        Struct21 x_25 = (Struct21 {enq_type : (((x_17)[2:1]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : ((((x_17)[2:1]) ==
        ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : (x_17)[0:0], enq_msg : Struct1 {id : (Bit#(6))'(6'h1),
        type_ : (Bool)'(True), addr : (x_15).addr, value :
        (x_15).value}});
        let x_26 <- makeEnq_parentChildren000(x_25);
    endrule

    rule rule_exec_000_021;
        $display ("Rule fired: rule_exec_000_021 at %t", $time);
        let x_0 <- deq_fifoL2E_000();
        Struct42 x_1 = ((x_0).lr_ir_pp);
        Bit#(3) x_2 = ((x_1).ir_msg_from);
        Struct1 x_3 = ((x_1).ir_msg);
        Bit#(3) x_4 = ((x_1).ir_mshr_id);
        Bool x_5 = ((x_1).ir_is_rs_rel);
        when (! (x_5), noAction);
        Struct45 x_6 = ((x_0).lr_ir);
        Struct11 x_7 = ((x_6).info);
        Struct41 x_8 = ((x_1).ir_by_victim);
        Vector#(4, Bit#(64)) x_9 = ((x_0).lr_value);
        let x_10 <- getMSHR_000(x_4);
        Vector#(4, Bit#(64)) x_11 = (unpack(0));
        Bool x_12 = ((x_7).mesi_owned);
        Bit#(3) x_13 = ((x_7).mesi_status);
        Struct18 x_14 = (Struct18 {dir_st : (x_7).mesi_dir_st, dir_excl :
        ((((x_7).mesi_dir_sharers)[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(1))'(1'h0)) : (((Bit#(1))'(1'h1)) +
        ((((((x_7).mesi_dir_sharers)[1:1])[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(1))'(1'h0)) : (((Bit#(1))'(1'h1)) + (unpack(0))))))),
        dir_sharers : (x_7).mesi_dir_sharers});
        when ((x_2) == ({((Bit#(2))'(2'h2)),((Bit#(1))'(1'h0))}),
        noAction);
        when (((x_3).id) == ((Bit#(6))'(6'h4)), noAction);
        when (((x_10).m_status) == ((Bit#(3))'(3'h4)), noAction);
        when ((x_10).m_rsb, noAction);
        when ((((x_10).m_msg).type_) == ((Bool)'(False)), noAction);
        when ((((x_10).m_msg).id) == ((Bit#(6))'(6'h0)), noAction);
        when (((x_10).m_status) == ((Bit#(3))'(3'h4)), noAction);
        when ((x_10).m_rsb, noAction);
        when ((x_3).type_, noAction);
        when ((Bool)'(True), noAction);
        Struct1 x_15 = (x_3);
        Struct1 x_16 = ((x_10).m_msg);
        Bit#(3) x_17 = ({((Bit#(2))'(2'h2)),(((x_10).m_qidx)[0:0])});
        Struct52 x_18 = (Struct52 {addr : (x_3).addr, info_write :
        (Bool)'(False), info_hit : (x_6).info_hit, info_way : (x_6).info_way,
        edir_hit : (x_6).edir_hit, edir_way : (x_6).edir_way, edir_slot :
        (x_6).edir_slot, info : (x_6).info, value_write : (Bool)'(False),
        value : unpack(0), may_victim : (x_6).may_victim, reps :
        (x_6).reps});
        Struct52 x_19 = (Struct52 {addr : (x_18).addr, info_write :
        (Bool)'(True), info_hit : (x_18).info_hit, info_way :
        (x_18).info_way, edir_hit : (x_18).edir_hit, edir_way :
        (x_18).edir_way, edir_slot : (x_18).edir_slot, info : Struct11
        {mesi_owned : ((x_18).info).mesi_owned, mesi_status :
        (Bit#(3))'(3'h3), mesi_dir_st : ((x_18).info).mesi_dir_st,
        mesi_dir_sharers : ((x_18).info).mesi_dir_sharers}, value_write :
        (x_18).value_write, value : (x_18).value, may_victim :
        (x_18).may_victim, reps : (x_18).reps});
        Struct52 x_20 = (Struct52 {addr : (x_19).addr, info_write :
        (x_19).info_write, info_hit : (x_19).info_hit, info_way :
        (x_19).info_way, edir_hit : (x_19).edir_hit, edir_way :
        (x_19).edir_way, edir_slot : (x_19).edir_slot, info : (x_19).info,
        value_write : (Bool)'(True), value : (x_15).value, may_victim :
        (x_19).may_victim, reps :
        (x_19).reps});
        let x_23 = ?;
        if ((x_8).valid) begin
            let x_21 <- victims__000__setVictim(Struct54 {victim_idx :
            (x_8).data, victim_info : (x_20).info, victim_value :
            (x_20).value});
            x_23 = x_9;
        end else begin
            let x_22 <- cache__000__valueRsLineRq(x_20);
            x_23 = x_22;
        end
        let x_24 <- releaseMSHR_000(x_4);
        Struct21 x_25 = (Struct21 {enq_type : (((x_17)[2:1]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : ((((x_17)[2:1]) ==
        ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : (x_17)[0:0], enq_msg : Struct1 {id : (Bit#(6))'(6'h1),
        type_ : (Bool)'(True), addr : (x_15).addr, value :
        (x_15).value}});
        let x_26 <- makeEnq_parentChildren000(x_25);
    endrule

    rule rule_exec_000_03;
        $display ("Rule fired: rule_exec_000_03 at %t", $time);
        let x_0 <- deq_fifoL2E_000();
        Struct42 x_1 = ((x_0).lr_ir_pp);
        Bit#(3) x_2 = ((x_1).ir_msg_from);
        Struct1 x_3 = ((x_1).ir_msg);
        Bit#(3) x_4 = ((x_1).ir_mshr_id);
        Bool x_5 = ((x_1).ir_is_rs_rel);
        when (! (x_5), noAction);
        Struct45 x_6 = ((x_0).lr_ir);
        Struct11 x_7 = ((x_6).info);
        Struct41 x_8 = ((x_1).ir_by_victim);
        Vector#(4, Bit#(64)) x_9 = ((x_0).lr_value);
        let x_10 <- getMSHR_000(x_4);
        Vector#(4, Bit#(64)) x_11 = (unpack(0));
        Bool x_12 = ((x_7).mesi_owned);
        Bit#(3) x_13 = ((x_7).mesi_status);
        Struct18 x_14 = (Struct18 {dir_st : (x_7).mesi_dir_st, dir_excl :
        ((((x_7).mesi_dir_sharers)[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(1))'(1'h0)) : (((Bit#(1))'(1'h1)) +
        ((((((x_7).mesi_dir_sharers)[1:1])[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(1))'(1'h0)) : (((Bit#(1))'(1'h1)) + (unpack(0))))))),
        dir_sharers : (x_7).mesi_dir_sharers});
        when ((x_2) == ((Bit#(3))'(3'h4)), noAction);
        when (((x_3).id) == ((Bit#(6))'(6'h5)), noAction);
        when (! ((x_3).type_), noAction);
        when (! ((x_13) < ((Bit#(3))'(3'h2))), noAction);
        Struct1 x_15 = (x_3);
        Struct52 x_16 = (Struct52 {addr : (x_3).addr, info_write :
        (Bool)'(False), info_hit : (x_6).info_hit, info_way : (x_6).info_way,
        edir_hit : (x_6).edir_hit, edir_way : (x_6).edir_way, edir_slot :
        (x_6).edir_slot, info : (x_6).info, value_write : (Bool)'(False),
        value : unpack(0), may_victim : (x_6).may_victim, reps :
        (x_6).reps});
        Struct52 x_17 = (Struct52 {addr : (x_16).addr, info_write :
        (Bool)'(True), info_hit : (x_16).info_hit, info_way :
        (x_16).info_way, edir_hit : (x_16).edir_hit, edir_way :
        (x_16).edir_way, edir_slot : (x_16).edir_slot, info : Struct11
        {mesi_owned : ((x_16).info).mesi_owned, mesi_status :
        (Bit#(3))'(3'h2), mesi_dir_st : ((x_16).info).mesi_dir_st,
        mesi_dir_sharers : ((x_16).info).mesi_dir_sharers}, value_write :
        (x_16).value_write, value : (x_16).value, may_victim :
        (x_16).may_victim, reps : (x_16).reps});
        Struct52 x_18 = (Struct52 {addr : (x_17).addr, info_write :
        (Bool)'(True), info_hit : (x_17).info_hit, info_way :
        (x_17).info_way, edir_hit : (x_17).edir_hit, edir_way :
        (x_17).edir_way, edir_slot : (x_17).edir_slot, info : Struct11
        {mesi_owned : (Bool)'(False), mesi_status :
        ((x_17).info).mesi_status, mesi_dir_st : ((x_17).info).mesi_dir_st,
        mesi_dir_sharers : ((x_17).info).mesi_dir_sharers}, value_write :
        (x_17).value_write, value : (x_17).value, may_victim :
        (x_17).may_victim, reps :
        (x_17).reps});
        let x_21 = ?;
        if ((x_8).valid) begin
            let x_19 <- victims__000__setVictim(Struct54 {victim_idx :
            (x_8).data, victim_info : (x_18).info, victim_value :
            (x_18).value});
            x_21 = x_9;
        end else begin
            let x_20 <- cache__000__valueRsLineRq(x_18);
            x_21 = x_20;
        end
        Struct21 x_22 = (Struct21 {enq_type : ((((Bit#(3))'(3'h2))[2:1]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : (((((Bit#(3))'(3'h2))[2:1])
        == ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : ((Bit#(3))'(3'h2))[0:0], enq_msg : Struct1 {id :
        (Bit#(6))'(6'h6), type_ : (Bool)'(True), addr : (x_15).addr, value :
        x_21}});
        let x_23 <- makeEnq_parentChildren000(x_22);
    endrule

    rule rule_exec_000_100;
        $display ("Rule fired: rule_exec_000_100 at %t", $time);
        let x_0 <- deq_fifoL2E_000();
        Struct42 x_1 = ((x_0).lr_ir_pp);
        Bit#(3) x_2 = ((x_1).ir_msg_from);
        Struct1 x_3 = ((x_1).ir_msg);
        Bit#(3) x_4 = ((x_1).ir_mshr_id);
        Bool x_5 = ((x_1).ir_is_rs_rel);
        when (! (x_5), noAction);
        Struct45 x_6 = ((x_0).lr_ir);
        Struct11 x_7 = ((x_6).info);
        Struct41 x_8 = ((x_1).ir_by_victim);
        Vector#(4, Bit#(64)) x_9 = ((x_0).lr_value);
        let x_10 <- getMSHR_000(x_4);
        Vector#(4, Bit#(64)) x_11 = (unpack(0));
        Bool x_12 = ((x_7).mesi_owned);
        Bit#(3) x_13 = ((x_7).mesi_status);
        Struct18 x_14 = (Struct18 {dir_st : (x_7).mesi_dir_st, dir_excl :
        ((((x_7).mesi_dir_sharers)[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(1))'(1'h0)) : (((Bit#(1))'(1'h1)) +
        ((((((x_7).mesi_dir_sharers)[1:1])[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(1))'(1'h0)) : (((Bit#(1))'(1'h1)) + (unpack(0))))))),
        dir_sharers : (x_7).mesi_dir_sharers});
        when ((x_2) == ((Bit#(3))'(3'h0)), noAction);
        when (((x_3).id) == ((Bit#(6))'(6'h8)), noAction);
        when (! ((x_3).type_), noAction);
        when ((x_13) == ((Bit#(3))'(3'h3)), noAction);
        Struct1 x_15 = (x_3);
        Struct52 x_16 = (Struct52 {addr : (x_3).addr, info_write :
        (Bool)'(False), info_hit : (x_6).info_hit, info_way : (x_6).info_way,
        edir_hit : (x_6).edir_hit, edir_way : (x_6).edir_way, edir_slot :
        (x_6).edir_slot, info : (x_6).info, value_write : (Bool)'(False),
        value : unpack(0), may_victim : (x_6).may_victim, reps :
        (x_6).reps});
        Struct52 x_17 = (Struct52 {addr : (x_16).addr, info_write :
        (x_16).info_write, info_hit : (x_16).info_hit, info_way :
        (x_16).info_way, edir_hit : (x_16).edir_hit, edir_way :
        (x_16).edir_way, edir_slot : (x_16).edir_slot, info : (x_16).info,
        value_write : (Bool)'(True), value : (x_15).value, may_victim :
        (x_16).may_victim, reps : (x_16).reps});
        Struct52 x_18 = (Struct52 {addr : (x_17).addr, info_write :
        (Bool)'(True), info_hit : (x_17).info_hit, info_way :
        (x_17).info_way, edir_hit : (x_17).edir_hit, edir_way :
        (x_17).edir_way, edir_slot : (x_17).edir_slot, info : Struct11
        {mesi_owned : ((x_17).info).mesi_owned, mesi_status :
        (Bit#(3))'(3'h4), mesi_dir_st : ((x_17).info).mesi_dir_st,
        mesi_dir_sharers : ((x_17).info).mesi_dir_sharers}, value_write :
        (x_17).value_write, value : (x_17).value, may_victim :
        (x_17).may_victim, reps : (x_17).reps});
        Struct52 x_19 = (Struct52 {addr : (x_18).addr, info_write :
        (Bool)'(True), info_hit : (x_18).info_hit, info_way :
        (x_18).info_way, edir_hit : (x_18).edir_hit, edir_way :
        (x_18).edir_way, edir_slot : (x_18).edir_slot, info : Struct11
        {mesi_owned : (Bool)'(True), mesi_status : ((x_18).info).mesi_status,
        mesi_dir_st : ((x_18).info).mesi_dir_st, mesi_dir_sharers :
        ((x_18).info).mesi_dir_sharers}, value_write : (x_18).value_write,
        value : (x_18).value, may_victim : (x_18).may_victim, reps :
        (x_18).reps});
        let x_22 = ?;
        if ((x_8).valid) begin
            let x_20 <- victims__000__setVictim(Struct54 {victim_idx :
            (x_8).data, victim_info : (x_19).info, victim_value :
            (x_19).value});
            x_22 = x_9;
        end else begin
            let x_21 <- cache__000__valueRsLineRq(x_19);
            x_22 = x_21;
        end
        Struct21 x_23 = (Struct21 {enq_type : ((((Bit#(3))'(3'h4))[2:1]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : (((((Bit#(3))'(3'h4))[2:1])
        == ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : ((Bit#(3))'(3'h4))[0:0], enq_msg : Struct1 {id :
        (Bit#(6))'(6'h9), type_ : (Bool)'(True), addr : (x_15).addr, value :
        unpack(0)}});
        let x_24 <- makeEnq_parentChildren000(x_23);
    endrule

    rule rule_exec_000_101;
        $display ("Rule fired: rule_exec_000_101 at %t", $time);
        let x_0 <- deq_fifoL2E_000();
        Struct42 x_1 = ((x_0).lr_ir_pp);
        Bit#(3) x_2 = ((x_1).ir_msg_from);
        Struct1 x_3 = ((x_1).ir_msg);
        Bit#(3) x_4 = ((x_1).ir_mshr_id);
        Bool x_5 = ((x_1).ir_is_rs_rel);
        when (! (x_5), noAction);
        Struct45 x_6 = ((x_0).lr_ir);
        Struct11 x_7 = ((x_6).info);
        Struct41 x_8 = ((x_1).ir_by_victim);
        Vector#(4, Bit#(64)) x_9 = ((x_0).lr_value);
        let x_10 <- getMSHR_000(x_4);
        Vector#(4, Bit#(64)) x_11 = (unpack(0));
        Bool x_12 = ((x_7).mesi_owned);
        Bit#(3) x_13 = ((x_7).mesi_status);
        Struct18 x_14 = (Struct18 {dir_st : (x_7).mesi_dir_st, dir_excl :
        ((((x_7).mesi_dir_sharers)[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(1))'(1'h0)) : (((Bit#(1))'(1'h1)) +
        ((((((x_7).mesi_dir_sharers)[1:1])[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(1))'(1'h0)) : (((Bit#(1))'(1'h1)) + (unpack(0))))))),
        dir_sharers : (x_7).mesi_dir_sharers});
        when ((x_2) == ((Bit#(3))'(3'h0)), noAction);
        when (((x_3).id) == ((Bit#(6))'(6'h8)), noAction);
        when (! ((x_3).type_), noAction);
        when (((x_12) == ((Bool)'(True))) && ((x_13) == ((Bit#(3))'(3'h4))),
        noAction);
        Struct1 x_15 = (x_3);
        Struct52 x_16 = (Struct52 {addr : (x_3).addr, info_write :
        (Bool)'(False), info_hit : (x_6).info_hit, info_way : (x_6).info_way,
        edir_hit : (x_6).edir_hit, edir_way : (x_6).edir_way, edir_slot :
        (x_6).edir_slot, info : (x_6).info, value_write : (Bool)'(False),
        value : unpack(0), may_victim : (x_6).may_victim, reps :
        (x_6).reps});
        Struct52 x_17 = (Struct52 {addr : (x_16).addr, info_write :
        (x_16).info_write, info_hit : (x_16).info_hit, info_way :
        (x_16).info_way, edir_hit : (x_16).edir_hit, edir_way :
        (x_16).edir_way, edir_slot : (x_16).edir_slot, info : (x_16).info,
        value_write : (Bool)'(True), value : (x_15).value, may_victim :
        (x_16).may_victim, reps :
        (x_16).reps});
        let x_20 = ?;
        if ((x_8).valid) begin
            let x_18 <- victims__000__setVictim(Struct54 {victim_idx :
            (x_8).data, victim_info : (x_17).info, victim_value :
            (x_17).value});
            x_20 = x_9;
        end else begin
            let x_19 <- cache__000__valueRsLineRq(x_17);
            x_20 = x_19;
        end
        Struct21 x_21 = (Struct21 {enq_type : ((((Bit#(3))'(3'h4))[2:1]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : (((((Bit#(3))'(3'h4))[2:1])
        == ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : ((Bit#(3))'(3'h4))[0:0], enq_msg : Struct1 {id :
        (Bit#(6))'(6'h9), type_ : (Bool)'(True), addr : (x_15).addr, value :
        unpack(0)}});
        let x_22 <- makeEnq_parentChildren000(x_21);
    endrule

    rule rule_exec_000_11;
        $display ("Rule fired: rule_exec_000_11 at %t", $time);
        let x_0 <- deq_fifoL2E_000();
        Struct42 x_1 = ((x_0).lr_ir_pp);
        Bit#(3) x_2 = ((x_1).ir_msg_from);
        Struct1 x_3 = ((x_1).ir_msg);
        Bit#(3) x_4 = ((x_1).ir_mshr_id);
        Bool x_5 = ((x_1).ir_is_rs_rel);
        when (! (x_5), noAction);
        Struct45 x_6 = ((x_0).lr_ir);
        Struct11 x_7 = ((x_6).info);
        Struct41 x_8 = ((x_1).ir_by_victim);
        Vector#(4, Bit#(64)) x_9 = ((x_0).lr_value);
        let x_10 <- getMSHR_000(x_4);
        Vector#(4, Bit#(64)) x_11 = (unpack(0));
        Bool x_12 = ((x_7).mesi_owned);
        Bit#(3) x_13 = ((x_7).mesi_status);
        Struct18 x_14 = (Struct18 {dir_st : (x_7).mesi_dir_st, dir_excl :
        ((((x_7).mesi_dir_sharers)[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(1))'(1'h0)) : (((Bit#(1))'(1'h1)) +
        ((((((x_7).mesi_dir_sharers)[1:1])[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(1))'(1'h0)) : (((Bit#(1))'(1'h1)) + (unpack(0))))))),
        dir_sharers : (x_7).mesi_dir_sharers});
        when ((x_2) == ((Bit#(3))'(3'h0)), noAction);
        when (((x_3).id) == ((Bit#(6))'(6'h8)), noAction);
        when (! ((x_3).type_), noAction);
        when (! (((Bit#(3))'(3'h2)) < (x_13)), noAction);
        Struct1 x_15 = (x_3);
        Struct52 x_16 = (Struct52 {addr : (x_3).addr, info_write :
        (Bool)'(False), info_hit : (x_6).info_hit, info_way : (x_6).info_way,
        edir_hit : (x_6).edir_hit, edir_way : (x_6).edir_way, edir_slot :
        (x_6).edir_slot, info : (x_6).info, value_write : (Bool)'(False),
        value : unpack(0), may_victim : (x_6).may_victim, reps :
        (x_6).reps});
        let x_18 = ?;
        if ((x_8).valid) begin
            x_18 = x_9;
        end else begin
            let x_17 <- cache__000__valueRsLineRq(unpack(0));
            x_18 = x_17;
        end
        let x_19 <- registerUL_000(Struct53 {r_id : x_4, r_ul_rsb :
        (Bool)'(True), r_ul_rsbTo : ((Bit#(3))'(3'h4))[0:0]});
        Struct21 x_20 = (Struct21 {enq_type : ((((Bit#(3))'(3'h0))[2:1]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : (((((Bit#(3))'(3'h0))[2:1])
        == ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : ((Bit#(3))'(3'h0))[0:0], enq_msg : Struct1 {id :
        (Bit#(6))'(6'ha), type_ : (Bool)'(False), addr : (x_15).addr, value :
        unpack(0)}});
        let x_21 <- makeEnq_parentChildren000(x_20);
    endrule

    rule rule_exec_000_12;
        $display ("Rule fired: rule_exec_000_12 at %t", $time);
        let x_0 <- deq_fifoL2E_000();
        Struct42 x_1 = ((x_0).lr_ir_pp);
        Bit#(3) x_2 = ((x_1).ir_msg_from);
        Struct1 x_3 = ((x_1).ir_msg);
        Bit#(3) x_4 = ((x_1).ir_mshr_id);
        Bool x_5 = ((x_1).ir_is_rs_rel);
        when (! (x_5), noAction);
        Struct45 x_6 = ((x_0).lr_ir);
        Struct11 x_7 = ((x_6).info);
        Struct41 x_8 = ((x_1).ir_by_victim);
        Vector#(4, Bit#(64)) x_9 = ((x_0).lr_value);
        let x_10 <- getMSHR_000(x_4);
        Vector#(4, Bit#(64)) x_11 = (unpack(0));
        Bool x_12 = ((x_7).mesi_owned);
        Bit#(3) x_13 = ((x_7).mesi_status);
        Struct18 x_14 = (Struct18 {dir_st : (x_7).mesi_dir_st, dir_excl :
        ((((x_7).mesi_dir_sharers)[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(1))'(1'h0)) : (((Bit#(1))'(1'h1)) +
        ((((((x_7).mesi_dir_sharers)[1:1])[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(1))'(1'h0)) : (((Bit#(1))'(1'h1)) + (unpack(0))))))),
        dir_sharers : (x_7).mesi_dir_sharers});
        when ((x_2) == ({((Bit#(2))'(2'h2)),((Bit#(1))'(1'h0))}),
        noAction);
        when (((x_3).id) == ((Bit#(6))'(6'hb)), noAction);
        when (((x_10).m_status) == ((Bit#(3))'(3'h4)), noAction);
        when ((x_10).m_rsb, noAction);
        when ((((x_10).m_msg).type_) == ((Bool)'(False)), noAction);
        when ((((x_10).m_msg).id) == ((Bit#(6))'(6'h8)), noAction);
        when (((x_10).m_status) == ((Bit#(3))'(3'h4)), noAction);
        when ((x_10).m_rsb, noAction);
        when ((x_3).type_, noAction);
        when ((Bool)'(True), noAction);
        Struct1 x_15 = (x_3);
        Struct1 x_16 = ((x_10).m_msg);
        Bit#(3) x_17 = ({((Bit#(2))'(2'h2)),(((x_10).m_qidx)[0:0])});
        Struct52 x_18 = (Struct52 {addr : (x_3).addr, info_write :
        (Bool)'(False), info_hit : (x_6).info_hit, info_way : (x_6).info_way,
        edir_hit : (x_6).edir_hit, edir_way : (x_6).edir_way, edir_slot :
        (x_6).edir_slot, info : (x_6).info, value_write : (Bool)'(False),
        value : unpack(0), may_victim : (x_6).may_victim, reps :
        (x_6).reps});
        Struct52 x_19 = (Struct52 {addr : (x_18).addr, info_write :
        (x_18).info_write, info_hit : (x_18).info_hit, info_way :
        (x_18).info_way, edir_hit : (x_18).edir_hit, edir_way :
        (x_18).edir_way, edir_slot : (x_18).edir_slot, info : (x_18).info,
        value_write : (Bool)'(True), value : (x_16).value, may_victim :
        (x_18).may_victim, reps : (x_18).reps});
        Struct52 x_20 = (Struct52 {addr : (x_19).addr, info_write :
        (Bool)'(True), info_hit : (x_19).info_hit, info_way :
        (x_19).info_way, edir_hit : (x_19).edir_hit, edir_way :
        (x_19).edir_way, edir_slot : (x_19).edir_slot, info : Struct11
        {mesi_owned : (Bool)'(True), mesi_status : ((x_19).info).mesi_status,
        mesi_dir_st : ((x_19).info).mesi_dir_st, mesi_dir_sharers :
        ((x_19).info).mesi_dir_sharers}, value_write : (x_19).value_write,
        value : (x_19).value, may_victim : (x_19).may_victim, reps :
        (x_19).reps});
        Struct52 x_21 = (Struct52 {addr : (x_20).addr, info_write :
        (Bool)'(True), info_hit : (x_20).info_hit, info_way :
        (x_20).info_way, edir_hit : (x_20).edir_hit, edir_way :
        (x_20).edir_way, edir_slot : (x_20).edir_slot, info : Struct11
        {mesi_owned : ((x_20).info).mesi_owned, mesi_status :
        (Bit#(3))'(3'h4), mesi_dir_st : ((x_20).info).mesi_dir_st,
        mesi_dir_sharers : ((x_20).info).mesi_dir_sharers}, value_write :
        (x_20).value_write, value : (x_20).value, may_victim :
        (x_20).may_victim, reps :
        (x_20).reps});
        let x_24 = ?;
        if ((x_8).valid) begin
            let x_22 <- victims__000__setVictim(Struct54 {victim_idx :
            (x_8).data, victim_info : (x_21).info, victim_value :
            (x_21).value});
            x_24 = x_9;
        end else begin
            let x_23 <- cache__000__valueRsLineRq(x_21);
            x_24 = x_23;
        end
        let x_25 <- releaseMSHR_000(x_4);
        Struct21 x_26 = (Struct21 {enq_type : (((x_17)[2:1]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : ((((x_17)[2:1]) ==
        ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : (x_17)[0:0], enq_msg : Struct1 {id : (Bit#(6))'(6'h9),
        type_ : (Bool)'(True), addr : (x_15).addr, value : unpack(0)}});
        let x_27 <- makeEnq_parentChildren000(x_26);
    endrule

    rule rule_exec_000_130;
        $display ("Rule fired: rule_exec_000_130 at %t", $time);
        let x_0 <- deq_fifoL2E_000();
        Struct42 x_1 = ((x_0).lr_ir_pp);
        Bit#(3) x_2 = ((x_1).ir_msg_from);
        Struct1 x_3 = ((x_1).ir_msg);
        Bit#(3) x_4 = ((x_1).ir_mshr_id);
        Bool x_5 = ((x_1).ir_is_rs_rel);
        when (! (x_5), noAction);
        Struct45 x_6 = ((x_0).lr_ir);
        Struct11 x_7 = ((x_6).info);
        Struct41 x_8 = ((x_1).ir_by_victim);
        Vector#(4, Bit#(64)) x_9 = ((x_0).lr_value);
        let x_10 <- getMSHR_000(x_4);
        Vector#(4, Bit#(64)) x_11 = (unpack(0));
        Bool x_12 = ((x_7).mesi_owned);
        Bit#(3) x_13 = ((x_7).mesi_status);
        Struct18 x_14 = (Struct18 {dir_st : (x_7).mesi_dir_st, dir_excl :
        ((((x_7).mesi_dir_sharers)[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(1))'(1'h0)) : (((Bit#(1))'(1'h1)) +
        ((((((x_7).mesi_dir_sharers)[1:1])[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(1))'(1'h0)) : (((Bit#(1))'(1'h1)) + (unpack(0))))))),
        dir_sharers : (x_7).mesi_dir_sharers});
        when ((x_2) == ((Bit#(3))'(3'h4)), noAction);
        when (((x_3).id) == ((Bit#(6))'(6'hc)), noAction);
        when (! ((x_3).type_), noAction);
        when ((Bool)'(True), noAction);
        Struct1 x_15 = (x_3);
        Struct52 x_16 = (Struct52 {addr : (x_3).addr, info_write :
        (Bool)'(False), info_hit : (x_6).info_hit, info_way : (x_6).info_way,
        edir_hit : (x_6).edir_hit, edir_way : (x_6).edir_way, edir_slot :
        (x_6).edir_slot, info : (x_6).info, value_write : (Bool)'(False),
        value : unpack(0), may_victim : (x_6).may_victim, reps :
        (x_6).reps});
        Struct52 x_17 = (Struct52 {addr : (x_16).addr, info_write :
        (Bool)'(True), info_hit : (x_16).info_hit, info_way :
        (x_16).info_way, edir_hit : (x_16).edir_hit, edir_way :
        (x_16).edir_way, edir_slot : (x_16).edir_slot, info : Struct11
        {mesi_owned : ((x_16).info).mesi_owned, mesi_status :
        (Bit#(3))'(3'h1), mesi_dir_st : ((x_16).info).mesi_dir_st,
        mesi_dir_sharers : ((x_16).info).mesi_dir_sharers}, value_write :
        (x_16).value_write, value : (x_16).value, may_victim :
        (x_16).may_victim, reps : (x_16).reps});
        Struct52 x_18 = (Struct52 {addr : (x_17).addr, info_write :
        (Bool)'(True), info_hit : (x_17).info_hit, info_way :
        (x_17).info_way, edir_hit : (x_17).edir_hit, edir_way :
        (x_17).edir_way, edir_slot : (x_17).edir_slot, info : Struct11
        {mesi_owned : (Bool)'(False), mesi_status :
        ((x_17).info).mesi_status, mesi_dir_st : ((x_17).info).mesi_dir_st,
        mesi_dir_sharers : ((x_17).info).mesi_dir_sharers}, value_write :
        (x_17).value_write, value : (x_17).value, may_victim :
        (x_17).may_victim, reps :
        (x_17).reps});
        let x_21 = ?;
        if ((x_8).valid) begin
            let x_19 <- victims__000__setVictim(Struct54 {victim_idx :
            (x_8).data, victim_info : (x_18).info, victim_value :
            (x_18).value});
            x_21 = x_9;
        end else begin
            let x_20 <- cache__000__valueRsLineRq(x_18);
            x_21 = x_20;
        end
        Struct21 x_22 = (Struct21 {enq_type : ((((Bit#(3))'(3'h2))[2:1]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : (((((Bit#(3))'(3'h2))[2:1])
        == ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : ((Bit#(3))'(3'h2))[0:0], enq_msg : Struct1 {id :
        (Bit#(6))'(6'hd), type_ : (Bool)'(True), addr : (x_15).addr, value :
        unpack(0)}});
        let x_23 <- makeEnq_parentChildren000(x_22);
    endrule

    rule rule_exec_000_131;
        $display ("Rule fired: rule_exec_000_131 at %t", $time);
        let x_0 <- deq_fifoL2E_000();
        Struct42 x_1 = ((x_0).lr_ir_pp);
        Bit#(3) x_2 = ((x_1).ir_msg_from);
        Struct1 x_3 = ((x_1).ir_msg);
        Bit#(3) x_4 = ((x_1).ir_mshr_id);
        Bool x_5 = ((x_1).ir_is_rs_rel);
        when (! (x_5), noAction);
        Struct45 x_6 = ((x_0).lr_ir);
        Struct11 x_7 = ((x_6).info);
        Struct41 x_8 = ((x_1).ir_by_victim);
        Vector#(4, Bit#(64)) x_9 = ((x_0).lr_value);
        let x_10 <- getMSHR_000(x_4);
        Vector#(4, Bit#(64)) x_11 = (unpack(0));
        Bool x_12 = ((x_7).mesi_owned);
        Bit#(3) x_13 = ((x_7).mesi_status);
        Struct18 x_14 = (Struct18 {dir_st : (x_7).mesi_dir_st, dir_excl :
        ((((x_7).mesi_dir_sharers)[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(1))'(1'h0)) : (((Bit#(1))'(1'h1)) +
        ((((((x_7).mesi_dir_sharers)[1:1])[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(1))'(1'h0)) : (((Bit#(1))'(1'h1)) + (unpack(0))))))),
        dir_sharers : (x_7).mesi_dir_sharers});
        when ((x_2) == ((Bit#(3))'(3'h4)), noAction);
        when (((x_3).id) == ((Bit#(6))'(6'he)), noAction);
        when (! ((x_3).type_), noAction);
        when (! ((x_13) < ((Bit#(3))'(3'h3))), noAction);
        Struct1 x_15 = (x_3);
        Struct52 x_16 = (Struct52 {addr : (x_3).addr, info_write :
        (Bool)'(False), info_hit : (x_6).info_hit, info_way : (x_6).info_way,
        edir_hit : (x_6).edir_hit, edir_way : (x_6).edir_way, edir_slot :
        (x_6).edir_slot, info : (x_6).info, value_write : (Bool)'(False),
        value : unpack(0), may_victim : (x_6).may_victim, reps :
        (x_6).reps});
        Struct52 x_17 = (Struct52 {addr : (x_16).addr, info_write :
        (Bool)'(True), info_hit : (x_16).info_hit, info_way :
        (x_16).info_way, edir_hit : (x_16).edir_hit, edir_way :
        (x_16).edir_way, edir_slot : (x_16).edir_slot, info : Struct11
        {mesi_owned : ((x_16).info).mesi_owned, mesi_status :
        (Bit#(3))'(3'h1), mesi_dir_st : ((x_16).info).mesi_dir_st,
        mesi_dir_sharers : ((x_16).info).mesi_dir_sharers}, value_write :
        (x_16).value_write, value : (x_16).value, may_victim :
        (x_16).may_victim, reps : (x_16).reps});
        Struct52 x_18 = (Struct52 {addr : (x_17).addr, info_write :
        (Bool)'(True), info_hit : (x_17).info_hit, info_way :
        (x_17).info_way, edir_hit : (x_17).edir_hit, edir_way :
        (x_17).edir_way, edir_slot : (x_17).edir_slot, info : Struct11
        {mesi_owned : (Bool)'(False), mesi_status :
        ((x_17).info).mesi_status, mesi_dir_st : ((x_17).info).mesi_dir_st,
        mesi_dir_sharers : ((x_17).info).mesi_dir_sharers}, value_write :
        (x_17).value_write, value : (x_17).value, may_victim :
        (x_17).may_victim, reps :
        (x_17).reps});
        let x_21 = ?;
        if ((x_8).valid) begin
            let x_19 <- victims__000__setVictim(Struct54 {victim_idx :
            (x_8).data, victim_info : (x_18).info, victim_value :
            (x_18).value});
            x_21 = x_9;
        end else begin
            let x_20 <- cache__000__valueRsLineRq(x_18);
            x_21 = x_20;
        end
        Struct21 x_22 = (Struct21 {enq_type : ((((Bit#(3))'(3'h2))[2:1]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : (((((Bit#(3))'(3'h2))[2:1])
        == ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : ((Bit#(3))'(3'h2))[0:0], enq_msg : Struct1 {id :
        (Bit#(6))'(6'hf), type_ : (Bool)'(True), addr : (x_15).addr, value :
        unpack(0)}});
        let x_23 <- makeEnq_parentChildren000(x_22);
    endrule

    rule rule_exec_000_20;
        $display ("Rule fired: rule_exec_000_20 at %t", $time);
        let x_0 <- victims__000__getFirstVictim();
        Bit#(64) x_1 = ((x_0).victim_addr);
        Struct11 x_2 = ((x_0).victim_info);
        Vector#(4, Bit#(64)) x_3 = ((x_0).victim_value);
        Struct1 x_4 = (Struct1 {id : unpack(0), type_ : (Bool)'(False), addr
        : x_1, value : unpack(0)});
        let x_5 <- getULImm_000(x_4);
        let x_6 <- victims__000__setVictimRq(Struct55 {victim_addr : x_1,
        victim_req : x_5});
        Struct51 x_7 = (Struct51 {m_status : (Bit#(3))'(3'h4), m_next :
        unpack(0), m_is_ul : (Bool)'(True), m_msg : x_4, m_qidx : unpack(0),
        m_rsb : (Bool)'(False), m_dl_rss_from : unpack(0), m_dl_rss_recv :
        unpack(0), m_dl_rss : unpack(0)});
        Vector#(4, Bit#(64)) x_8 = (unpack(0));
        Bool x_9 = ((x_2).mesi_owned);
        Bit#(3) x_10 = ((x_2).mesi_status);
        Struct18 x_11 = (Struct18 {dir_st : (x_2).mesi_dir_st, dir_excl :
        ((((x_2).mesi_dir_sharers)[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(1))'(1'h0)) : (((Bit#(1))'(1'h1)) +
        ((((((x_2).mesi_dir_sharers)[1:1])[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(1))'(1'h0)) : (((Bit#(1))'(1'h1)) + (unpack(0))))))),
        dir_sharers : (x_2).mesi_dir_sharers});
        when (! ((x_4).type_), noAction);
        when (((x_9) == ((Bool)'(False))) && ((((Bit#(3))'(3'h0)) < (x_10))
        && ((x_10) < ((Bit#(3))'(3'h4)))), noAction);
        Struct21 x_12 = (Struct21 {enq_type : ((((Bit#(3))'(3'h0))[2:1]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : (((((Bit#(3))'(3'h0))[2:1])
        == ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : ((Bit#(3))'(3'h0))[0:0], enq_msg : Struct1 {id :
        (Bit#(6))'(6'h14), type_ : (Bool)'(False), addr : (x_4).addr, value :
        unpack(0)}});
        let x_13 <- makeEnq_parentChildren000(x_12);
    endrule

    rule rule_exec_000_21;
        $display ("Rule fired: rule_exec_000_21 at %t", $time);
        let x_0 <- victims__000__getFirstVictim();
        Bit#(64) x_1 = ((x_0).victim_addr);
        Struct11 x_2 = ((x_0).victim_info);
        Vector#(4, Bit#(64)) x_3 = ((x_0).victim_value);
        Struct1 x_4 = (Struct1 {id : unpack(0), type_ : (Bool)'(False), addr
        : x_1, value : unpack(0)});
        let x_5 <- getULImm_000(x_4);
        let x_6 <- victims__000__setVictimRq(Struct55 {victim_addr : x_1,
        victim_req : x_5});
        Struct51 x_7 = (Struct51 {m_status : (Bit#(3))'(3'h4), m_next :
        unpack(0), m_is_ul : (Bool)'(True), m_msg : x_4, m_qidx : unpack(0),
        m_rsb : (Bool)'(False), m_dl_rss_from : unpack(0), m_dl_rss_recv :
        unpack(0), m_dl_rss : unpack(0)});
        Vector#(4, Bit#(64)) x_8 = (unpack(0));
        Bool x_9 = ((x_2).mesi_owned);
        Bit#(3) x_10 = ((x_2).mesi_status);
        Struct18 x_11 = (Struct18 {dir_st : (x_2).mesi_dir_st, dir_excl :
        ((((x_2).mesi_dir_sharers)[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(1))'(1'h0)) : (((Bit#(1))'(1'h1)) +
        ((((((x_2).mesi_dir_sharers)[1:1])[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(1))'(1'h0)) : (((Bit#(1))'(1'h1)) + (unpack(0))))))),
        dir_sharers : (x_2).mesi_dir_sharers});
        when (! ((x_4).type_), noAction);
        when (((Bit#(3))'(3'h0)) < (x_10), noAction);
        Struct21 x_12 = (Struct21 {enq_type : ((((Bit#(3))'(3'h0))[2:1]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : (((((Bit#(3))'(3'h0))[2:1])
        == ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : ((Bit#(3))'(3'h0))[0:0], enq_msg : Struct1 {id :
        (Bit#(6))'(6'h15), type_ : (Bool)'(False), addr : (x_4).addr, value :
        x_3}});
        let x_13 <- makeEnq_parentChildren000(x_12);
    endrule

    rule rule_exec_000_22;
        $display ("Rule fired: rule_exec_000_22 at %t", $time);
        let x_0 <- deq_fifoL2E_000();
        Struct42 x_1 = ((x_0).lr_ir_pp);
        Bit#(3) x_2 = ((x_1).ir_msg_from);
        Struct1 x_3 = ((x_1).ir_msg);
        Bit#(3) x_4 = ((x_1).ir_mshr_id);
        Bool x_5 = ((x_1).ir_is_rs_rel);
        when (! (x_5), noAction);
        Struct45 x_6 = ((x_0).lr_ir);
        Struct11 x_7 = ((x_6).info);
        Struct41 x_8 = ((x_1).ir_by_victim);
        Vector#(4, Bit#(64)) x_9 = ((x_0).lr_value);
        let x_10 <- getMSHR_000(x_4);
        Vector#(4, Bit#(64)) x_11 = (unpack(0));
        Bool x_12 = ((x_7).mesi_owned);
        Bit#(3) x_13 = ((x_7).mesi_status);
        Struct18 x_14 = (Struct18 {dir_st : (x_7).mesi_dir_st, dir_excl :
        ((((x_7).mesi_dir_sharers)[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(1))'(1'h0)) : (((Bit#(1))'(1'h1)) +
        ((((((x_7).mesi_dir_sharers)[1:1])[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(1))'(1'h0)) : (((Bit#(1))'(1'h1)) + (unpack(0))))))),
        dir_sharers : (x_7).mesi_dir_sharers});
        when ((x_2) == ({((Bit#(2))'(2'h2)),((Bit#(1))'(1'h0))}),
        noAction);
        when (((x_3).id) == ((Bit#(6))'(6'h16)), noAction);
        when (((x_10).m_status) == ((Bit#(3))'(3'h4)), noAction);
        when (! ((x_10).m_rsb), noAction);
        when ((x_3).type_, noAction);
        when ((Bool)'(True), noAction);
        Struct1 x_15 = (x_3);
        Struct52 x_16 = (Struct52 {addr : (x_3).addr, info_write :
        (Bool)'(False), info_hit : (x_6).info_hit, info_way : (x_6).info_way,
        edir_hit : (x_6).edir_hit, edir_way : (x_6).edir_way, edir_slot :
        (x_6).edir_slot, info : (x_6).info, value_write : (Bool)'(False),
        value : unpack(0), may_victim : (x_6).may_victim, reps :
        (x_6).reps});
        Struct52 x_17 = (Struct52 {addr : (x_16).addr, info_write :
        (Bool)'(True), info_hit : (x_16).info_hit, info_way :
        (x_16).info_way, edir_hit : (x_16).edir_hit, edir_way :
        (x_16).edir_way, edir_slot : (x_16).edir_slot, info : Struct11
        {mesi_owned : ((x_16).info).mesi_owned, mesi_status :
        (Bit#(3))'(3'h0), mesi_dir_st : ((x_16).info).mesi_dir_st,
        mesi_dir_sharers : ((x_16).info).mesi_dir_sharers}, value_write :
        (x_16).value_write, value : (x_16).value, may_victim :
        (x_16).may_victim, reps : (x_16).reps});
        Struct52 x_18 = (Struct52 {addr : (x_17).addr, info_write :
        (Bool)'(True), info_hit : (x_17).info_hit, info_way :
        (x_17).info_way, edir_hit : (x_17).edir_hit, edir_way :
        (x_17).edir_way, edir_slot : (x_17).edir_slot, info : Struct11
        {mesi_owned : (Bool)'(False), mesi_status :
        ((x_17).info).mesi_status, mesi_dir_st : ((x_17).info).mesi_dir_st,
        mesi_dir_sharers : ((x_17).info).mesi_dir_sharers}, value_write :
        (x_17).value_write, value : (x_17).value, may_victim :
        (x_17).may_victim, reps :
        (x_17).reps});
        let x_21 = ?;
        if ((x_8).valid) begin
            let x_19 <- victims__000__setVictim(Struct54 {victim_idx :
            (x_8).data, victim_info : (x_18).info, victim_value :
            (x_18).value});
            x_21 = x_9;
        end else begin
            let x_20 <- cache__000__valueRsLineRq(x_18);
            x_21 = x_20;
        end
        let x_22 <- releaseMSHR_000(x_4);
    endrule

    // No methods in this module
endmodule

interface Module85;

endinterface

module mkModule85#(function Action victims__001__setVictimRq(Struct55 _),
    function ActionValue#(Bit#(3)) getULImm_001(Struct1 _),
    function ActionValue#(Struct48) victims__001__getFirstVictim(),
    function Action victims__001__setVictim(Struct54 _),
    function Action registerUL_001(Struct53 _),
    function Action makeEnq_parentChildren001(Struct21 _),
    function ActionValue#(Vector#(4, Bit#(64))) cache__001__valueRsLineRq(Struct52 _),
    function ActionValue#(Struct51) getMSHR_001(Bit#(3) _),
    function ActionValue#(Struct47) deq_fifoL2E_001(),
    function ActionValue#(Struct42) deq_fifoI2L_child_001(),
    function Action enq_fifoI2L_child_001(Struct42 _),
    function ActionValue#(Struct42) deq_fifoN2I_child_001(),
    function ActionValue#(Struct50) getWait_001(),
    function ActionValue#(Bit#(3)) findDL_001(Bit#(64) _),
    function Action enq_fifoN2I_child_001(Struct42 _),
    function ActionValue#(Struct40) getCRqSlot_001(Struct39 _),
    function ActionValue#(Struct2) deq_fifoCInput_001(),
    function ActionValue#(Struct48) victims__001__getVictim(Bit#(1) _),
    function Action enq_fifoL2E_001(Struct47 _),
    function ActionValue#(Struct45) cache__001__infoRsValueRq(Bit#(64) _),
    function ActionValue#(Struct42) deq_fifoI2L_parent_001(),
    function Action addRs_001(Struct44 _),
    function Action enq_fifoI2L_parent_001(Struct42 _),
    function Action cache__001__infoRq(Bit#(64) _),
    function ActionValue#(Struct42) deq_fifoN2I_parent_001(),
    function ActionValue#(Struct43) getRsReady_001(),
    function Action releaseMSHR_001(Bit#(3) _),
    function ActionValue#(Bit#(3)) victims__001__releaseVictim(Bit#(64) _),
    function ActionValue#(Bit#(3)) findUL_001(Bit#(64) _),
    function Action enq_fifoN2I_parent_001(Struct42 _),
    function ActionValue#(Struct41) victims__001findVictim(Bit#(64) _),
    function ActionValue#(Struct40) getPRqSlot_001(Struct39 _),
    function ActionValue#(Struct2) deq_fifoPInput001())
    (Module85);

    rule rule_in_prq_parent_001;
        $display ("Rule fired: rule_in_prq_parent_001 at %t", $time);
        let x_0 <- deq_fifoPInput001();
        Bit#(3) x_1 = ((x_0).in_msg_from);
        when ((x_1) == ({((Bit#(2))'(2'h2)),((Bit#(1))'(1'h1))}),
        noAction);
        Struct1 x_2 = ((x_0).in_msg);
        when (! ((x_2).type_), noAction);
        let x_3 <- getPRqSlot_001(Struct39 {r_id : unpack(0), r_msg : x_2,
        r_msg_from : (x_0).in_msg_from});
        when ((x_3).s_has_slot,
        noAction);
        if (! ((x_3).s_conflict)) begin
            let x_4 <- victims__001findVictim((x_2).addr);
            Struct42 x_5 = (Struct42 {ir_is_rs_rel : (Bool)'(False),
            ir_is_rs_acc : (Bool)'(False), ir_msg : (x_0).in_msg, ir_msg_from
            : x_1, ir_mshr_id : (x_3).s_id, ir_by_victim : x_4});
            let x_6 <- enq_fifoN2I_parent_001(x_5);
        end else begin

        end
    endrule

    rule rule_in_prs_parent_001;
        $display ("Rule fired: rule_in_prs_parent_001 at %t", $time);
        let x_0 <- deq_fifoPInput001();
        Bit#(3) x_1 = ((x_0).in_msg_from);
        when ((x_1) == ({((Bit#(2))'(2'h2)),((Bit#(1))'(1'h1))}),
        noAction);
        Struct1 x_2 = ((x_0).in_msg);
        when (((x_2).type_) && (! (((x_2).id) == ((Bit#(6))'(6'h16)))),
        noAction);
        let x_3 <- findUL_001((x_2).addr);
        let x_4 <- victims__001findVictim((x_2).addr);
        Struct42 x_5 = (Struct42 {ir_is_rs_rel : (Bool)'(False), ir_is_rs_acc
        : (Bool)'(False), ir_msg : (x_0).in_msg, ir_msg_from : x_1,
        ir_mshr_id : x_3, ir_by_victim : x_4});
        let x_6 <- enq_fifoN2I_parent_001(x_5);
    endrule

    rule rule_in_invrs_parent_001;
        $display ("Rule fired: rule_in_invrs_parent_001 at %t", $time);
        let x_0 <- deq_fifoPInput001();
        Bit#(3) x_1 = ((x_0).in_msg_from);
        when ((x_1) == ({((Bit#(2))'(2'h2)),((Bit#(1))'(1'h1))}),
        noAction);
        Struct1 x_2 = ((x_0).in_msg);
        when (((x_2).type_) && (((x_2).id) == ((Bit#(6))'(6'h16))),
        noAction);
        let x_3 <- victims__001__releaseVictim((x_2).addr);
        let x_4 <- releaseMSHR_001(x_3);
    endrule

    rule rule_in_rsrel_parent_001;
        $display ("Rule fired: rule_in_rsrel_parent_001 at %t", $time);
        let x_0 <- getRsReady_001();
        Struct1 x_1 = (Struct1 {id : unpack(0), type_ : unpack(0), addr :
        (x_0).r_addr, value : unpack(0)});
        Struct42 x_2 = (Struct42 {ir_is_rs_rel : (Bool)'(True), ir_is_rs_acc
        : (Bool)'(False), ir_msg : x_1, ir_msg_from : unpack(0), ir_mshr_id :
        (x_0).r_id, ir_by_victim : Struct41 {valid : (Bool)'(False), data :
        unpack(0)}});
        let x_3 <- enq_fifoN2I_parent_001(x_2);
    endrule

    rule rule_ir_cache_parent_001;
        $display ("Rule fired: rule_ir_cache_parent_001 at %t", $time);
        let x_0 <- deq_fifoN2I_parent_001();
        when (! ((x_0).ir_is_rs_acc), noAction);
        when (! (((x_0).ir_by_victim).valid), noAction);
        Struct1 x_1 = ((x_0).ir_msg);
        let x_2 <- cache__001__infoRq((x_1).addr);
        let x_3 <- enq_fifoI2L_parent_001(x_0);
    endrule

    rule rule_ir_victims_parent_001;
        $display ("Rule fired: rule_ir_victims_parent_001 at %t", $time);
        let x_0 <- deq_fifoN2I_parent_001();
        when (! ((x_0).ir_is_rs_acc), noAction);
        when (((x_0).ir_by_victim).valid, noAction);
        let x_1 <- enq_fifoI2L_parent_001(x_0);
    endrule

    rule rule_ir_rs_acc_parent_001;
        $display ("Rule fired: rule_ir_rs_acc_parent_001 at %t", $time);
        let x_0 <- deq_fifoN2I_parent_001();
        when ((x_0).ir_is_rs_acc, noAction);
        let x_1 <- addRs_001(Struct44 {r_id : (x_0).ir_mshr_id, r_midx :
        ((x_0).ir_msg_from)[0:0], r_msg : (x_0).ir_msg});
    endrule

    rule rule_lr_cache_parent_001;
        $display ("Rule fired: rule_lr_cache_parent_001 at %t", $time);
        let x_0 <- deq_fifoI2L_parent_001();
        when (! (((x_0).ir_by_victim).valid), noAction);
        let x_1 <- cache__001__infoRsValueRq(((x_0).ir_msg).addr);
        Struct47 x_2 = (Struct47 {lr_ir_pp : x_0, lr_ir : x_1, lr_value :
        unpack(0)});
        let x_3 <- enq_fifoL2E_001(x_2);
    endrule

    rule rule_lr_victims_parent_001;
        $display ("Rule fired: rule_lr_victims_parent_001 at %t", $time);
        let x_0 <- deq_fifoI2L_parent_001();
        when (((x_0).ir_by_victim).valid, noAction);
        let x_1 <- victims__001__getVictim((Bit#(1))'(1'h0));
        Struct45 x_2 = (Struct45 {info_index : unpack(0), info_hit :
        unpack(0), info_way : unpack(0), edir_hit : unpack(0), edir_way :
        unpack(0), edir_slot : unpack(0), info : (x_1).victim_info,
        may_victim : unpack(0), reps : unpack(0)});
        Struct47 x_3 = (Struct47 {lr_ir_pp : x_0, lr_ir : x_2, lr_value :
        (x_1).victim_value});
        let x_4 <- enq_fifoL2E_001(x_3);
    endrule

    rule rule_in_crq_child_001;
        $display ("Rule fired: rule_in_crq_child_001 at %t", $time);
        let x_0 <- deq_fifoCInput_001();
        Bit#(3) x_1 = ((x_0).in_msg_from);
        when (((x_1)[2:1]) == ((Bit#(2))'(2'h0)), noAction);
        Struct1 x_2 = ((x_0).in_msg);
        when (! ((x_2).type_), noAction);
        let x_3 <- getCRqSlot_001(Struct39 {r_id : unpack(0), r_msg : x_2,
        r_msg_from : x_1});
        when ((x_3).s_has_slot,
        noAction);
        if (! ((x_3).s_conflict)) begin
            let x_4 <- victims__001findVictim((x_2).addr);
            Struct42 x_5 = (Struct42 {ir_is_rs_rel : (Bool)'(False),
            ir_is_rs_acc : (Bool)'(False), ir_msg : (x_0).in_msg, ir_msg_from
            : x_1, ir_mshr_id : (x_3).s_id, ir_by_victim : x_4});
            let x_6 <- enq_fifoN2I_child_001(x_5);
        end else begin

        end
    endrule

    rule rule_in_crs_child_001;
        $display ("Rule fired: rule_in_crs_child_001 at %t", $time);
        let x_0 <- deq_fifoCInput_001();
        Bit#(3) x_1 = ((x_0).in_msg_from);
        when (((x_1)[2:1]) == ((Bit#(2))'(2'h1)), noAction);
        Struct1 x_2 = ((x_0).in_msg);
        when ((x_2).type_, noAction);
        let x_3 <- findDL_001((x_2).addr);
        let x_4 <- victims__001findVictim((x_2).addr);
        Struct42 x_5 = (Struct42 {ir_is_rs_rel : (Bool)'(False), ir_is_rs_acc
        : (Bool)'(True), ir_msg : x_2, ir_msg_from : x_1, ir_mshr_id : x_3,
        ir_by_victim : x_4});
        let x_6 <- enq_fifoN2I_child_001(x_5);
    endrule

    rule rule_in_retry_child_001;
        $display ("Rule fired: rule_in_retry_child_001 at %t", $time);
        let x_0 <- getWait_001();
        when ((x_0).valid, noAction);
        Struct39 x_1 = ((x_0).data);
        Struct1 x_2 = ((x_1).r_msg);
        let x_3 <- victims__001findVictim((x_2).addr);
        Struct42 x_4 = (Struct42 {ir_is_rs_rel : (Bool)'(False), ir_is_rs_acc
        : (Bool)'(False), ir_msg : x_2, ir_msg_from : (x_1).r_msg_from,
        ir_mshr_id : (x_1).r_id, ir_by_victim : x_3});
        let x_5 <- enq_fifoN2I_child_001(x_4);
    endrule

    rule rule_ir_cache_child_001;
        $display ("Rule fired: rule_ir_cache_child_001 at %t", $time);
        let x_0 <- deq_fifoN2I_child_001();
        when (! ((x_0).ir_is_rs_acc), noAction);
        when (! (((x_0).ir_by_victim).valid), noAction);
        Struct1 x_1 = ((x_0).ir_msg);
        let x_2 <- cache__001__infoRq((x_1).addr);
        let x_3 <- enq_fifoI2L_child_001(x_0);
    endrule

    rule rule_ir_victims_child_001;
        $display ("Rule fired: rule_ir_victims_child_001 at %t", $time);
        let x_0 <- deq_fifoN2I_child_001();
        when (! ((x_0).ir_is_rs_acc), noAction);
        when (((x_0).ir_by_victim).valid, noAction);
        let x_1 <- enq_fifoI2L_child_001(x_0);
    endrule

    rule rule_ir_rs_acc_child_001;
        $display ("Rule fired: rule_ir_rs_acc_child_001 at %t", $time);
        let x_0 <- deq_fifoN2I_child_001();
        when ((x_0).ir_is_rs_acc, noAction);
        let x_1 <- addRs_001(Struct44 {r_id : (x_0).ir_mshr_id, r_midx :
        ((x_0).ir_msg_from)[0:0], r_msg : (x_0).ir_msg});
    endrule

    rule rule_lr_cache_child_001;
        $display ("Rule fired: rule_lr_cache_child_001 at %t", $time);
        let x_0 <- deq_fifoI2L_child_001();
        when (! (((x_0).ir_by_victim).valid), noAction);
        let x_1 <- cache__001__infoRsValueRq(((x_0).ir_msg).addr);
        Struct47 x_2 = (Struct47 {lr_ir_pp : x_0, lr_ir : x_1, lr_value :
        unpack(0)});
        let x_3 <- enq_fifoL2E_001(x_2);
    endrule

    rule rule_lr_victims_child_001;
        $display ("Rule fired: rule_lr_victims_child_001 at %t", $time);
        let x_0 <- deq_fifoI2L_child_001();
        when (((x_0).ir_by_victim).valid, noAction);
        let x_1 <- victims__001__getVictim((Bit#(1))'(1'h0));
        Struct45 x_2 = (Struct45 {info_index : unpack(0), info_hit :
        unpack(0), info_way : unpack(0), edir_hit : unpack(0), edir_way :
        unpack(0), edir_slot : unpack(0), info : (x_1).victim_info,
        may_victim : unpack(0), reps : unpack(0)});
        Struct47 x_3 = (Struct47 {lr_ir_pp : x_0, lr_ir : x_2, lr_value :
        (x_1).victim_value});
        let x_4 <- enq_fifoL2E_001(x_3);
    endrule

    rule rule_exec_001_00;
        $display ("Rule fired: rule_exec_001_00 at %t", $time);
        let x_0 <- deq_fifoL2E_001();
        Struct42 x_1 = ((x_0).lr_ir_pp);
        Bit#(3) x_2 = ((x_1).ir_msg_from);
        Struct1 x_3 = ((x_1).ir_msg);
        Bit#(3) x_4 = ((x_1).ir_mshr_id);
        Bool x_5 = ((x_1).ir_is_rs_rel);
        when (! (x_5), noAction);
        Struct45 x_6 = ((x_0).lr_ir);
        Struct11 x_7 = ((x_6).info);
        Struct41 x_8 = ((x_1).ir_by_victim);
        Vector#(4, Bit#(64)) x_9 = ((x_0).lr_value);
        let x_10 <- getMSHR_001(x_4);
        Vector#(4, Bit#(64)) x_11 = (unpack(0));
        Bool x_12 = ((x_7).mesi_owned);
        Bit#(3) x_13 = ((x_7).mesi_status);
        Struct18 x_14 = (Struct18 {dir_st : (x_7).mesi_dir_st, dir_excl :
        ((((x_7).mesi_dir_sharers)[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(1))'(1'h0)) : (((Bit#(1))'(1'h1)) +
        ((((((x_7).mesi_dir_sharers)[1:1])[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(1))'(1'h0)) : (((Bit#(1))'(1'h1)) + (unpack(0))))))),
        dir_sharers : (x_7).mesi_dir_sharers});
        when ((x_2) == ((Bit#(3))'(3'h0)), noAction);
        when (((x_3).id) == ((Bit#(6))'(6'h0)), noAction);
        when (! ((x_3).type_), noAction);
        when (! ((x_13) < ((Bit#(3))'(3'h2))), noAction);
        Struct1 x_15 = (x_3);
        Struct52 x_16 = (Struct52 {addr : (x_3).addr, info_write :
        (Bool)'(False), info_hit : (x_6).info_hit, info_way : (x_6).info_way,
        edir_hit : (x_6).edir_hit, edir_way : (x_6).edir_way, edir_slot :
        (x_6).edir_slot, info : (x_6).info, value_write : (Bool)'(False),
        value : unpack(0), may_victim : (x_6).may_victim, reps :
        (x_6).reps});
        let x_18 = ?;
        if ((x_8).valid) begin
            x_18 = x_9;
        end else begin
            let x_17 <- cache__001__valueRsLineRq(unpack(0));
            x_18 = x_17;
        end
        Struct21 x_19 = (Struct21 {enq_type : ((((Bit#(3))'(3'h4))[2:1]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : (((((Bit#(3))'(3'h4))[2:1])
        == ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : ((Bit#(3))'(3'h4))[0:0], enq_msg : Struct1 {id :
        (Bit#(6))'(6'h1), type_ : (Bool)'(True), addr : (x_15).addr, value :
        x_18}});
        let x_20 <- makeEnq_parentChildren001(x_19);
    endrule

    rule rule_exec_001_01;
        $display ("Rule fired: rule_exec_001_01 at %t", $time);
        let x_0 <- deq_fifoL2E_001();
        Struct42 x_1 = ((x_0).lr_ir_pp);
        Bit#(3) x_2 = ((x_1).ir_msg_from);
        Struct1 x_3 = ((x_1).ir_msg);
        Bit#(3) x_4 = ((x_1).ir_mshr_id);
        Bool x_5 = ((x_1).ir_is_rs_rel);
        when (! (x_5), noAction);
        Struct45 x_6 = ((x_0).lr_ir);
        Struct11 x_7 = ((x_6).info);
        Struct41 x_8 = ((x_1).ir_by_victim);
        Vector#(4, Bit#(64)) x_9 = ((x_0).lr_value);
        let x_10 <- getMSHR_001(x_4);
        Vector#(4, Bit#(64)) x_11 = (unpack(0));
        Bool x_12 = ((x_7).mesi_owned);
        Bit#(3) x_13 = ((x_7).mesi_status);
        Struct18 x_14 = (Struct18 {dir_st : (x_7).mesi_dir_st, dir_excl :
        ((((x_7).mesi_dir_sharers)[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(1))'(1'h0)) : (((Bit#(1))'(1'h1)) +
        ((((((x_7).mesi_dir_sharers)[1:1])[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(1))'(1'h0)) : (((Bit#(1))'(1'h1)) + (unpack(0))))))),
        dir_sharers : (x_7).mesi_dir_sharers});
        when ((x_2) == ((Bit#(3))'(3'h0)), noAction);
        when (((x_3).id) == ((Bit#(6))'(6'h0)), noAction);
        when (! ((x_3).type_), noAction);
        when (! (((Bit#(3))'(3'h1)) < (x_13)), noAction);
        Struct1 x_15 = (x_3);
        Struct52 x_16 = (Struct52 {addr : (x_3).addr, info_write :
        (Bool)'(False), info_hit : (x_6).info_hit, info_way : (x_6).info_way,
        edir_hit : (x_6).edir_hit, edir_way : (x_6).edir_way, edir_slot :
        (x_6).edir_slot, info : (x_6).info, value_write : (Bool)'(False),
        value : unpack(0), may_victim : (x_6).may_victim, reps :
        (x_6).reps});
        let x_18 = ?;
        if ((x_8).valid) begin
            x_18 = x_9;
        end else begin
            let x_17 <- cache__001__valueRsLineRq(unpack(0));
            x_18 = x_17;
        end
        let x_19 <- registerUL_001(Struct53 {r_id : x_4, r_ul_rsb :
        (Bool)'(True), r_ul_rsbTo : ((Bit#(3))'(3'h4))[0:0]});
        Struct21 x_20 = (Struct21 {enq_type : ((((Bit#(3))'(3'h1))[2:1]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : (((((Bit#(3))'(3'h1))[2:1])
        == ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : ((Bit#(3))'(3'h1))[0:0], enq_msg : Struct1 {id :
        (Bit#(6))'(6'h2), type_ : (Bool)'(False), addr : (x_15).addr, value :
        unpack(0)}});
        let x_21 <- makeEnq_parentChildren001(x_20);
    endrule

    rule rule_exec_001_020;
        $display ("Rule fired: rule_exec_001_020 at %t", $time);
        let x_0 <- deq_fifoL2E_001();
        Struct42 x_1 = ((x_0).lr_ir_pp);
        Bit#(3) x_2 = ((x_1).ir_msg_from);
        Struct1 x_3 = ((x_1).ir_msg);
        Bit#(3) x_4 = ((x_1).ir_mshr_id);
        Bool x_5 = ((x_1).ir_is_rs_rel);
        when (! (x_5), noAction);
        Struct45 x_6 = ((x_0).lr_ir);
        Struct11 x_7 = ((x_6).info);
        Struct41 x_8 = ((x_1).ir_by_victim);
        Vector#(4, Bit#(64)) x_9 = ((x_0).lr_value);
        let x_10 <- getMSHR_001(x_4);
        Vector#(4, Bit#(64)) x_11 = (unpack(0));
        Bool x_12 = ((x_7).mesi_owned);
        Bit#(3) x_13 = ((x_7).mesi_status);
        Struct18 x_14 = (Struct18 {dir_st : (x_7).mesi_dir_st, dir_excl :
        ((((x_7).mesi_dir_sharers)[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(1))'(1'h0)) : (((Bit#(1))'(1'h1)) +
        ((((((x_7).mesi_dir_sharers)[1:1])[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(1))'(1'h0)) : (((Bit#(1))'(1'h1)) + (unpack(0))))))),
        dir_sharers : (x_7).mesi_dir_sharers});
        when ((x_2) == ({((Bit#(2))'(2'h2)),((Bit#(1))'(1'h1))}),
        noAction);
        when (((x_3).id) == ((Bit#(6))'(6'h3)), noAction);
        when (((x_10).m_status) == ((Bit#(3))'(3'h4)), noAction);
        when ((x_10).m_rsb, noAction);
        when ((((x_10).m_msg).type_) == ((Bool)'(False)), noAction);
        when ((((x_10).m_msg).id) == ((Bit#(6))'(6'h0)), noAction);
        when (((x_10).m_status) == ((Bit#(3))'(3'h4)), noAction);
        when ((x_10).m_rsb, noAction);
        when ((x_3).type_, noAction);
        when ((Bool)'(True), noAction);
        Struct1 x_15 = (x_3);
        Struct1 x_16 = ((x_10).m_msg);
        Bit#(3) x_17 = ({((Bit#(2))'(2'h2)),(((x_10).m_qidx)[0:0])});
        Struct52 x_18 = (Struct52 {addr : (x_3).addr, info_write :
        (Bool)'(False), info_hit : (x_6).info_hit, info_way : (x_6).info_way,
        edir_hit : (x_6).edir_hit, edir_way : (x_6).edir_way, edir_slot :
        (x_6).edir_slot, info : (x_6).info, value_write : (Bool)'(False),
        value : unpack(0), may_victim : (x_6).may_victim, reps :
        (x_6).reps});
        Struct52 x_19 = (Struct52 {addr : (x_18).addr, info_write :
        (Bool)'(True), info_hit : (x_18).info_hit, info_way :
        (x_18).info_way, edir_hit : (x_18).edir_hit, edir_way :
        (x_18).edir_way, edir_slot : (x_18).edir_slot, info : Struct11
        {mesi_owned : ((x_18).info).mesi_owned, mesi_status :
        (Bit#(3))'(3'h2), mesi_dir_st : ((x_18).info).mesi_dir_st,
        mesi_dir_sharers : ((x_18).info).mesi_dir_sharers}, value_write :
        (x_18).value_write, value : (x_18).value, may_victim :
        (x_18).may_victim, reps : (x_18).reps});
        Struct52 x_20 = (Struct52 {addr : (x_19).addr, info_write :
        (x_19).info_write, info_hit : (x_19).info_hit, info_way :
        (x_19).info_way, edir_hit : (x_19).edir_hit, edir_way :
        (x_19).edir_way, edir_slot : (x_19).edir_slot, info : (x_19).info,
        value_write : (Bool)'(True), value : (x_15).value, may_victim :
        (x_19).may_victim, reps :
        (x_19).reps});
        let x_23 = ?;
        if ((x_8).valid) begin
            let x_21 <- victims__001__setVictim(Struct54 {victim_idx :
            (x_8).data, victim_info : (x_20).info, victim_value :
            (x_20).value});
            x_23 = x_9;
        end else begin
            let x_22 <- cache__001__valueRsLineRq(x_20);
            x_23 = x_22;
        end
        let x_24 <- releaseMSHR_001(x_4);
        Struct21 x_25 = (Struct21 {enq_type : (((x_17)[2:1]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : ((((x_17)[2:1]) ==
        ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : (x_17)[0:0], enq_msg : Struct1 {id : (Bit#(6))'(6'h1),
        type_ : (Bool)'(True), addr : (x_15).addr, value :
        (x_15).value}});
        let x_26 <- makeEnq_parentChildren001(x_25);
    endrule

    rule rule_exec_001_021;
        $display ("Rule fired: rule_exec_001_021 at %t", $time);
        let x_0 <- deq_fifoL2E_001();
        Struct42 x_1 = ((x_0).lr_ir_pp);
        Bit#(3) x_2 = ((x_1).ir_msg_from);
        Struct1 x_3 = ((x_1).ir_msg);
        Bit#(3) x_4 = ((x_1).ir_mshr_id);
        Bool x_5 = ((x_1).ir_is_rs_rel);
        when (! (x_5), noAction);
        Struct45 x_6 = ((x_0).lr_ir);
        Struct11 x_7 = ((x_6).info);
        Struct41 x_8 = ((x_1).ir_by_victim);
        Vector#(4, Bit#(64)) x_9 = ((x_0).lr_value);
        let x_10 <- getMSHR_001(x_4);
        Vector#(4, Bit#(64)) x_11 = (unpack(0));
        Bool x_12 = ((x_7).mesi_owned);
        Bit#(3) x_13 = ((x_7).mesi_status);
        Struct18 x_14 = (Struct18 {dir_st : (x_7).mesi_dir_st, dir_excl :
        ((((x_7).mesi_dir_sharers)[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(1))'(1'h0)) : (((Bit#(1))'(1'h1)) +
        ((((((x_7).mesi_dir_sharers)[1:1])[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(1))'(1'h0)) : (((Bit#(1))'(1'h1)) + (unpack(0))))))),
        dir_sharers : (x_7).mesi_dir_sharers});
        when ((x_2) == ({((Bit#(2))'(2'h2)),((Bit#(1))'(1'h1))}),
        noAction);
        when (((x_3).id) == ((Bit#(6))'(6'h4)), noAction);
        when (((x_10).m_status) == ((Bit#(3))'(3'h4)), noAction);
        when ((x_10).m_rsb, noAction);
        when ((((x_10).m_msg).type_) == ((Bool)'(False)), noAction);
        when ((((x_10).m_msg).id) == ((Bit#(6))'(6'h0)), noAction);
        when (((x_10).m_status) == ((Bit#(3))'(3'h4)), noAction);
        when ((x_10).m_rsb, noAction);
        when ((x_3).type_, noAction);
        when ((Bool)'(True), noAction);
        Struct1 x_15 = (x_3);
        Struct1 x_16 = ((x_10).m_msg);
        Bit#(3) x_17 = ({((Bit#(2))'(2'h2)),(((x_10).m_qidx)[0:0])});
        Struct52 x_18 = (Struct52 {addr : (x_3).addr, info_write :
        (Bool)'(False), info_hit : (x_6).info_hit, info_way : (x_6).info_way,
        edir_hit : (x_6).edir_hit, edir_way : (x_6).edir_way, edir_slot :
        (x_6).edir_slot, info : (x_6).info, value_write : (Bool)'(False),
        value : unpack(0), may_victim : (x_6).may_victim, reps :
        (x_6).reps});
        Struct52 x_19 = (Struct52 {addr : (x_18).addr, info_write :
        (Bool)'(True), info_hit : (x_18).info_hit, info_way :
        (x_18).info_way, edir_hit : (x_18).edir_hit, edir_way :
        (x_18).edir_way, edir_slot : (x_18).edir_slot, info : Struct11
        {mesi_owned : ((x_18).info).mesi_owned, mesi_status :
        (Bit#(3))'(3'h3), mesi_dir_st : ((x_18).info).mesi_dir_st,
        mesi_dir_sharers : ((x_18).info).mesi_dir_sharers}, value_write :
        (x_18).value_write, value : (x_18).value, may_victim :
        (x_18).may_victim, reps : (x_18).reps});
        Struct52 x_20 = (Struct52 {addr : (x_19).addr, info_write :
        (x_19).info_write, info_hit : (x_19).info_hit, info_way :
        (x_19).info_way, edir_hit : (x_19).edir_hit, edir_way :
        (x_19).edir_way, edir_slot : (x_19).edir_slot, info : (x_19).info,
        value_write : (Bool)'(True), value : (x_15).value, may_victim :
        (x_19).may_victim, reps :
        (x_19).reps});
        let x_23 = ?;
        if ((x_8).valid) begin
            let x_21 <- victims__001__setVictim(Struct54 {victim_idx :
            (x_8).data, victim_info : (x_20).info, victim_value :
            (x_20).value});
            x_23 = x_9;
        end else begin
            let x_22 <- cache__001__valueRsLineRq(x_20);
            x_23 = x_22;
        end
        let x_24 <- releaseMSHR_001(x_4);
        Struct21 x_25 = (Struct21 {enq_type : (((x_17)[2:1]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : ((((x_17)[2:1]) ==
        ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : (x_17)[0:0], enq_msg : Struct1 {id : (Bit#(6))'(6'h1),
        type_ : (Bool)'(True), addr : (x_15).addr, value :
        (x_15).value}});
        let x_26 <- makeEnq_parentChildren001(x_25);
    endrule

    rule rule_exec_001_03;
        $display ("Rule fired: rule_exec_001_03 at %t", $time);
        let x_0 <- deq_fifoL2E_001();
        Struct42 x_1 = ((x_0).lr_ir_pp);
        Bit#(3) x_2 = ((x_1).ir_msg_from);
        Struct1 x_3 = ((x_1).ir_msg);
        Bit#(3) x_4 = ((x_1).ir_mshr_id);
        Bool x_5 = ((x_1).ir_is_rs_rel);
        when (! (x_5), noAction);
        Struct45 x_6 = ((x_0).lr_ir);
        Struct11 x_7 = ((x_6).info);
        Struct41 x_8 = ((x_1).ir_by_victim);
        Vector#(4, Bit#(64)) x_9 = ((x_0).lr_value);
        let x_10 <- getMSHR_001(x_4);
        Vector#(4, Bit#(64)) x_11 = (unpack(0));
        Bool x_12 = ((x_7).mesi_owned);
        Bit#(3) x_13 = ((x_7).mesi_status);
        Struct18 x_14 = (Struct18 {dir_st : (x_7).mesi_dir_st, dir_excl :
        ((((x_7).mesi_dir_sharers)[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(1))'(1'h0)) : (((Bit#(1))'(1'h1)) +
        ((((((x_7).mesi_dir_sharers)[1:1])[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(1))'(1'h0)) : (((Bit#(1))'(1'h1)) + (unpack(0))))))),
        dir_sharers : (x_7).mesi_dir_sharers});
        when ((x_2) == ((Bit#(3))'(3'h5)), noAction);
        when (((x_3).id) == ((Bit#(6))'(6'h5)), noAction);
        when (! ((x_3).type_), noAction);
        when (! ((x_13) < ((Bit#(3))'(3'h2))), noAction);
        Struct1 x_15 = (x_3);
        Struct52 x_16 = (Struct52 {addr : (x_3).addr, info_write :
        (Bool)'(False), info_hit : (x_6).info_hit, info_way : (x_6).info_way,
        edir_hit : (x_6).edir_hit, edir_way : (x_6).edir_way, edir_slot :
        (x_6).edir_slot, info : (x_6).info, value_write : (Bool)'(False),
        value : unpack(0), may_victim : (x_6).may_victim, reps :
        (x_6).reps});
        Struct52 x_17 = (Struct52 {addr : (x_16).addr, info_write :
        (Bool)'(True), info_hit : (x_16).info_hit, info_way :
        (x_16).info_way, edir_hit : (x_16).edir_hit, edir_way :
        (x_16).edir_way, edir_slot : (x_16).edir_slot, info : Struct11
        {mesi_owned : ((x_16).info).mesi_owned, mesi_status :
        (Bit#(3))'(3'h2), mesi_dir_st : ((x_16).info).mesi_dir_st,
        mesi_dir_sharers : ((x_16).info).mesi_dir_sharers}, value_write :
        (x_16).value_write, value : (x_16).value, may_victim :
        (x_16).may_victim, reps : (x_16).reps});
        Struct52 x_18 = (Struct52 {addr : (x_17).addr, info_write :
        (Bool)'(True), info_hit : (x_17).info_hit, info_way :
        (x_17).info_way, edir_hit : (x_17).edir_hit, edir_way :
        (x_17).edir_way, edir_slot : (x_17).edir_slot, info : Struct11
        {mesi_owned : (Bool)'(False), mesi_status :
        ((x_17).info).mesi_status, mesi_dir_st : ((x_17).info).mesi_dir_st,
        mesi_dir_sharers : ((x_17).info).mesi_dir_sharers}, value_write :
        (x_17).value_write, value : (x_17).value, may_victim :
        (x_17).may_victim, reps :
        (x_17).reps});
        let x_21 = ?;
        if ((x_8).valid) begin
            let x_19 <- victims__001__setVictim(Struct54 {victim_idx :
            (x_8).data, victim_info : (x_18).info, victim_value :
            (x_18).value});
            x_21 = x_9;
        end else begin
            let x_20 <- cache__001__valueRsLineRq(x_18);
            x_21 = x_20;
        end
        Struct21 x_22 = (Struct21 {enq_type : ((((Bit#(3))'(3'h3))[2:1]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : (((((Bit#(3))'(3'h3))[2:1])
        == ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : ((Bit#(3))'(3'h3))[0:0], enq_msg : Struct1 {id :
        (Bit#(6))'(6'h6), type_ : (Bool)'(True), addr : (x_15).addr, value :
        x_21}});
        let x_23 <- makeEnq_parentChildren001(x_22);
    endrule

    rule rule_exec_001_100;
        $display ("Rule fired: rule_exec_001_100 at %t", $time);
        let x_0 <- deq_fifoL2E_001();
        Struct42 x_1 = ((x_0).lr_ir_pp);
        Bit#(3) x_2 = ((x_1).ir_msg_from);
        Struct1 x_3 = ((x_1).ir_msg);
        Bit#(3) x_4 = ((x_1).ir_mshr_id);
        Bool x_5 = ((x_1).ir_is_rs_rel);
        when (! (x_5), noAction);
        Struct45 x_6 = ((x_0).lr_ir);
        Struct11 x_7 = ((x_6).info);
        Struct41 x_8 = ((x_1).ir_by_victim);
        Vector#(4, Bit#(64)) x_9 = ((x_0).lr_value);
        let x_10 <- getMSHR_001(x_4);
        Vector#(4, Bit#(64)) x_11 = (unpack(0));
        Bool x_12 = ((x_7).mesi_owned);
        Bit#(3) x_13 = ((x_7).mesi_status);
        Struct18 x_14 = (Struct18 {dir_st : (x_7).mesi_dir_st, dir_excl :
        ((((x_7).mesi_dir_sharers)[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(1))'(1'h0)) : (((Bit#(1))'(1'h1)) +
        ((((((x_7).mesi_dir_sharers)[1:1])[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(1))'(1'h0)) : (((Bit#(1))'(1'h1)) + (unpack(0))))))),
        dir_sharers : (x_7).mesi_dir_sharers});
        when ((x_2) == ((Bit#(3))'(3'h0)), noAction);
        when (((x_3).id) == ((Bit#(6))'(6'h8)), noAction);
        when (! ((x_3).type_), noAction);
        when ((x_13) == ((Bit#(3))'(3'h3)), noAction);
        Struct1 x_15 = (x_3);
        Struct52 x_16 = (Struct52 {addr : (x_3).addr, info_write :
        (Bool)'(False), info_hit : (x_6).info_hit, info_way : (x_6).info_way,
        edir_hit : (x_6).edir_hit, edir_way : (x_6).edir_way, edir_slot :
        (x_6).edir_slot, info : (x_6).info, value_write : (Bool)'(False),
        value : unpack(0), may_victim : (x_6).may_victim, reps :
        (x_6).reps});
        Struct52 x_17 = (Struct52 {addr : (x_16).addr, info_write :
        (x_16).info_write, info_hit : (x_16).info_hit, info_way :
        (x_16).info_way, edir_hit : (x_16).edir_hit, edir_way :
        (x_16).edir_way, edir_slot : (x_16).edir_slot, info : (x_16).info,
        value_write : (Bool)'(True), value : (x_15).value, may_victim :
        (x_16).may_victim, reps : (x_16).reps});
        Struct52 x_18 = (Struct52 {addr : (x_17).addr, info_write :
        (Bool)'(True), info_hit : (x_17).info_hit, info_way :
        (x_17).info_way, edir_hit : (x_17).edir_hit, edir_way :
        (x_17).edir_way, edir_slot : (x_17).edir_slot, info : Struct11
        {mesi_owned : ((x_17).info).mesi_owned, mesi_status :
        (Bit#(3))'(3'h4), mesi_dir_st : ((x_17).info).mesi_dir_st,
        mesi_dir_sharers : ((x_17).info).mesi_dir_sharers}, value_write :
        (x_17).value_write, value : (x_17).value, may_victim :
        (x_17).may_victim, reps : (x_17).reps});
        Struct52 x_19 = (Struct52 {addr : (x_18).addr, info_write :
        (Bool)'(True), info_hit : (x_18).info_hit, info_way :
        (x_18).info_way, edir_hit : (x_18).edir_hit, edir_way :
        (x_18).edir_way, edir_slot : (x_18).edir_slot, info : Struct11
        {mesi_owned : (Bool)'(True), mesi_status : ((x_18).info).mesi_status,
        mesi_dir_st : ((x_18).info).mesi_dir_st, mesi_dir_sharers :
        ((x_18).info).mesi_dir_sharers}, value_write : (x_18).value_write,
        value : (x_18).value, may_victim : (x_18).may_victim, reps :
        (x_18).reps});
        let x_22 = ?;
        if ((x_8).valid) begin
            let x_20 <- victims__001__setVictim(Struct54 {victim_idx :
            (x_8).data, victim_info : (x_19).info, victim_value :
            (x_19).value});
            x_22 = x_9;
        end else begin
            let x_21 <- cache__001__valueRsLineRq(x_19);
            x_22 = x_21;
        end
        Struct21 x_23 = (Struct21 {enq_type : ((((Bit#(3))'(3'h4))[2:1]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : (((((Bit#(3))'(3'h4))[2:1])
        == ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : ((Bit#(3))'(3'h4))[0:0], enq_msg : Struct1 {id :
        (Bit#(6))'(6'h9), type_ : (Bool)'(True), addr : (x_15).addr, value :
        unpack(0)}});
        let x_24 <- makeEnq_parentChildren001(x_23);
    endrule

    rule rule_exec_001_101;
        $display ("Rule fired: rule_exec_001_101 at %t", $time);
        let x_0 <- deq_fifoL2E_001();
        Struct42 x_1 = ((x_0).lr_ir_pp);
        Bit#(3) x_2 = ((x_1).ir_msg_from);
        Struct1 x_3 = ((x_1).ir_msg);
        Bit#(3) x_4 = ((x_1).ir_mshr_id);
        Bool x_5 = ((x_1).ir_is_rs_rel);
        when (! (x_5), noAction);
        Struct45 x_6 = ((x_0).lr_ir);
        Struct11 x_7 = ((x_6).info);
        Struct41 x_8 = ((x_1).ir_by_victim);
        Vector#(4, Bit#(64)) x_9 = ((x_0).lr_value);
        let x_10 <- getMSHR_001(x_4);
        Vector#(4, Bit#(64)) x_11 = (unpack(0));
        Bool x_12 = ((x_7).mesi_owned);
        Bit#(3) x_13 = ((x_7).mesi_status);
        Struct18 x_14 = (Struct18 {dir_st : (x_7).mesi_dir_st, dir_excl :
        ((((x_7).mesi_dir_sharers)[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(1))'(1'h0)) : (((Bit#(1))'(1'h1)) +
        ((((((x_7).mesi_dir_sharers)[1:1])[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(1))'(1'h0)) : (((Bit#(1))'(1'h1)) + (unpack(0))))))),
        dir_sharers : (x_7).mesi_dir_sharers});
        when ((x_2) == ((Bit#(3))'(3'h0)), noAction);
        when (((x_3).id) == ((Bit#(6))'(6'h8)), noAction);
        when (! ((x_3).type_), noAction);
        when (((x_12) == ((Bool)'(True))) && ((x_13) == ((Bit#(3))'(3'h4))),
        noAction);
        Struct1 x_15 = (x_3);
        Struct52 x_16 = (Struct52 {addr : (x_3).addr, info_write :
        (Bool)'(False), info_hit : (x_6).info_hit, info_way : (x_6).info_way,
        edir_hit : (x_6).edir_hit, edir_way : (x_6).edir_way, edir_slot :
        (x_6).edir_slot, info : (x_6).info, value_write : (Bool)'(False),
        value : unpack(0), may_victim : (x_6).may_victim, reps :
        (x_6).reps});
        Struct52 x_17 = (Struct52 {addr : (x_16).addr, info_write :
        (x_16).info_write, info_hit : (x_16).info_hit, info_way :
        (x_16).info_way, edir_hit : (x_16).edir_hit, edir_way :
        (x_16).edir_way, edir_slot : (x_16).edir_slot, info : (x_16).info,
        value_write : (Bool)'(True), value : (x_15).value, may_victim :
        (x_16).may_victim, reps :
        (x_16).reps});
        let x_20 = ?;
        if ((x_8).valid) begin
            let x_18 <- victims__001__setVictim(Struct54 {victim_idx :
            (x_8).data, victim_info : (x_17).info, victim_value :
            (x_17).value});
            x_20 = x_9;
        end else begin
            let x_19 <- cache__001__valueRsLineRq(x_17);
            x_20 = x_19;
        end
        Struct21 x_21 = (Struct21 {enq_type : ((((Bit#(3))'(3'h4))[2:1]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : (((((Bit#(3))'(3'h4))[2:1])
        == ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : ((Bit#(3))'(3'h4))[0:0], enq_msg : Struct1 {id :
        (Bit#(6))'(6'h9), type_ : (Bool)'(True), addr : (x_15).addr, value :
        unpack(0)}});
        let x_22 <- makeEnq_parentChildren001(x_21);
    endrule

    rule rule_exec_001_11;
        $display ("Rule fired: rule_exec_001_11 at %t", $time);
        let x_0 <- deq_fifoL2E_001();
        Struct42 x_1 = ((x_0).lr_ir_pp);
        Bit#(3) x_2 = ((x_1).ir_msg_from);
        Struct1 x_3 = ((x_1).ir_msg);
        Bit#(3) x_4 = ((x_1).ir_mshr_id);
        Bool x_5 = ((x_1).ir_is_rs_rel);
        when (! (x_5), noAction);
        Struct45 x_6 = ((x_0).lr_ir);
        Struct11 x_7 = ((x_6).info);
        Struct41 x_8 = ((x_1).ir_by_victim);
        Vector#(4, Bit#(64)) x_9 = ((x_0).lr_value);
        let x_10 <- getMSHR_001(x_4);
        Vector#(4, Bit#(64)) x_11 = (unpack(0));
        Bool x_12 = ((x_7).mesi_owned);
        Bit#(3) x_13 = ((x_7).mesi_status);
        Struct18 x_14 = (Struct18 {dir_st : (x_7).mesi_dir_st, dir_excl :
        ((((x_7).mesi_dir_sharers)[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(1))'(1'h0)) : (((Bit#(1))'(1'h1)) +
        ((((((x_7).mesi_dir_sharers)[1:1])[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(1))'(1'h0)) : (((Bit#(1))'(1'h1)) + (unpack(0))))))),
        dir_sharers : (x_7).mesi_dir_sharers});
        when ((x_2) == ((Bit#(3))'(3'h0)), noAction);
        when (((x_3).id) == ((Bit#(6))'(6'h8)), noAction);
        when (! ((x_3).type_), noAction);
        when (! (((Bit#(3))'(3'h2)) < (x_13)), noAction);
        Struct1 x_15 = (x_3);
        Struct52 x_16 = (Struct52 {addr : (x_3).addr, info_write :
        (Bool)'(False), info_hit : (x_6).info_hit, info_way : (x_6).info_way,
        edir_hit : (x_6).edir_hit, edir_way : (x_6).edir_way, edir_slot :
        (x_6).edir_slot, info : (x_6).info, value_write : (Bool)'(False),
        value : unpack(0), may_victim : (x_6).may_victim, reps :
        (x_6).reps});
        let x_18 = ?;
        if ((x_8).valid) begin
            x_18 = x_9;
        end else begin
            let x_17 <- cache__001__valueRsLineRq(unpack(0));
            x_18 = x_17;
        end
        let x_19 <- registerUL_001(Struct53 {r_id : x_4, r_ul_rsb :
        (Bool)'(True), r_ul_rsbTo : ((Bit#(3))'(3'h4))[0:0]});
        Struct21 x_20 = (Struct21 {enq_type : ((((Bit#(3))'(3'h1))[2:1]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : (((((Bit#(3))'(3'h1))[2:1])
        == ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : ((Bit#(3))'(3'h1))[0:0], enq_msg : Struct1 {id :
        (Bit#(6))'(6'ha), type_ : (Bool)'(False), addr : (x_15).addr, value :
        unpack(0)}});
        let x_21 <- makeEnq_parentChildren001(x_20);
    endrule

    rule rule_exec_001_12;
        $display ("Rule fired: rule_exec_001_12 at %t", $time);
        let x_0 <- deq_fifoL2E_001();
        Struct42 x_1 = ((x_0).lr_ir_pp);
        Bit#(3) x_2 = ((x_1).ir_msg_from);
        Struct1 x_3 = ((x_1).ir_msg);
        Bit#(3) x_4 = ((x_1).ir_mshr_id);
        Bool x_5 = ((x_1).ir_is_rs_rel);
        when (! (x_5), noAction);
        Struct45 x_6 = ((x_0).lr_ir);
        Struct11 x_7 = ((x_6).info);
        Struct41 x_8 = ((x_1).ir_by_victim);
        Vector#(4, Bit#(64)) x_9 = ((x_0).lr_value);
        let x_10 <- getMSHR_001(x_4);
        Vector#(4, Bit#(64)) x_11 = (unpack(0));
        Bool x_12 = ((x_7).mesi_owned);
        Bit#(3) x_13 = ((x_7).mesi_status);
        Struct18 x_14 = (Struct18 {dir_st : (x_7).mesi_dir_st, dir_excl :
        ((((x_7).mesi_dir_sharers)[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(1))'(1'h0)) : (((Bit#(1))'(1'h1)) +
        ((((((x_7).mesi_dir_sharers)[1:1])[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(1))'(1'h0)) : (((Bit#(1))'(1'h1)) + (unpack(0))))))),
        dir_sharers : (x_7).mesi_dir_sharers});
        when ((x_2) == ({((Bit#(2))'(2'h2)),((Bit#(1))'(1'h1))}),
        noAction);
        when (((x_3).id) == ((Bit#(6))'(6'hb)), noAction);
        when (((x_10).m_status) == ((Bit#(3))'(3'h4)), noAction);
        when ((x_10).m_rsb, noAction);
        when ((((x_10).m_msg).type_) == ((Bool)'(False)), noAction);
        when ((((x_10).m_msg).id) == ((Bit#(6))'(6'h8)), noAction);
        when (((x_10).m_status) == ((Bit#(3))'(3'h4)), noAction);
        when ((x_10).m_rsb, noAction);
        when ((x_3).type_, noAction);
        when ((Bool)'(True), noAction);
        Struct1 x_15 = (x_3);
        Struct1 x_16 = ((x_10).m_msg);
        Bit#(3) x_17 = ({((Bit#(2))'(2'h2)),(((x_10).m_qidx)[0:0])});
        Struct52 x_18 = (Struct52 {addr : (x_3).addr, info_write :
        (Bool)'(False), info_hit : (x_6).info_hit, info_way : (x_6).info_way,
        edir_hit : (x_6).edir_hit, edir_way : (x_6).edir_way, edir_slot :
        (x_6).edir_slot, info : (x_6).info, value_write : (Bool)'(False),
        value : unpack(0), may_victim : (x_6).may_victim, reps :
        (x_6).reps});
        Struct52 x_19 = (Struct52 {addr : (x_18).addr, info_write :
        (x_18).info_write, info_hit : (x_18).info_hit, info_way :
        (x_18).info_way, edir_hit : (x_18).edir_hit, edir_way :
        (x_18).edir_way, edir_slot : (x_18).edir_slot, info : (x_18).info,
        value_write : (Bool)'(True), value : (x_16).value, may_victim :
        (x_18).may_victim, reps : (x_18).reps});
        Struct52 x_20 = (Struct52 {addr : (x_19).addr, info_write :
        (Bool)'(True), info_hit : (x_19).info_hit, info_way :
        (x_19).info_way, edir_hit : (x_19).edir_hit, edir_way :
        (x_19).edir_way, edir_slot : (x_19).edir_slot, info : Struct11
        {mesi_owned : (Bool)'(True), mesi_status : ((x_19).info).mesi_status,
        mesi_dir_st : ((x_19).info).mesi_dir_st, mesi_dir_sharers :
        ((x_19).info).mesi_dir_sharers}, value_write : (x_19).value_write,
        value : (x_19).value, may_victim : (x_19).may_victim, reps :
        (x_19).reps});
        Struct52 x_21 = (Struct52 {addr : (x_20).addr, info_write :
        (Bool)'(True), info_hit : (x_20).info_hit, info_way :
        (x_20).info_way, edir_hit : (x_20).edir_hit, edir_way :
        (x_20).edir_way, edir_slot : (x_20).edir_slot, info : Struct11
        {mesi_owned : ((x_20).info).mesi_owned, mesi_status :
        (Bit#(3))'(3'h4), mesi_dir_st : ((x_20).info).mesi_dir_st,
        mesi_dir_sharers : ((x_20).info).mesi_dir_sharers}, value_write :
        (x_20).value_write, value : (x_20).value, may_victim :
        (x_20).may_victim, reps :
        (x_20).reps});
        let x_24 = ?;
        if ((x_8).valid) begin
            let x_22 <- victims__001__setVictim(Struct54 {victim_idx :
            (x_8).data, victim_info : (x_21).info, victim_value :
            (x_21).value});
            x_24 = x_9;
        end else begin
            let x_23 <- cache__001__valueRsLineRq(x_21);
            x_24 = x_23;
        end
        let x_25 <- releaseMSHR_001(x_4);
        Struct21 x_26 = (Struct21 {enq_type : (((x_17)[2:1]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : ((((x_17)[2:1]) ==
        ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : (x_17)[0:0], enq_msg : Struct1 {id : (Bit#(6))'(6'h9),
        type_ : (Bool)'(True), addr : (x_15).addr, value : unpack(0)}});
        let x_27 <- makeEnq_parentChildren001(x_26);
    endrule

    rule rule_exec_001_130;
        $display ("Rule fired: rule_exec_001_130 at %t", $time);
        let x_0 <- deq_fifoL2E_001();
        Struct42 x_1 = ((x_0).lr_ir_pp);
        Bit#(3) x_2 = ((x_1).ir_msg_from);
        Struct1 x_3 = ((x_1).ir_msg);
        Bit#(3) x_4 = ((x_1).ir_mshr_id);
        Bool x_5 = ((x_1).ir_is_rs_rel);
        when (! (x_5), noAction);
        Struct45 x_6 = ((x_0).lr_ir);
        Struct11 x_7 = ((x_6).info);
        Struct41 x_8 = ((x_1).ir_by_victim);
        Vector#(4, Bit#(64)) x_9 = ((x_0).lr_value);
        let x_10 <- getMSHR_001(x_4);
        Vector#(4, Bit#(64)) x_11 = (unpack(0));
        Bool x_12 = ((x_7).mesi_owned);
        Bit#(3) x_13 = ((x_7).mesi_status);
        Struct18 x_14 = (Struct18 {dir_st : (x_7).mesi_dir_st, dir_excl :
        ((((x_7).mesi_dir_sharers)[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(1))'(1'h0)) : (((Bit#(1))'(1'h1)) +
        ((((((x_7).mesi_dir_sharers)[1:1])[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(1))'(1'h0)) : (((Bit#(1))'(1'h1)) + (unpack(0))))))),
        dir_sharers : (x_7).mesi_dir_sharers});
        when ((x_2) == ((Bit#(3))'(3'h5)), noAction);
        when (((x_3).id) == ((Bit#(6))'(6'hc)), noAction);
        when (! ((x_3).type_), noAction);
        when ((Bool)'(True), noAction);
        Struct1 x_15 = (x_3);
        Struct52 x_16 = (Struct52 {addr : (x_3).addr, info_write :
        (Bool)'(False), info_hit : (x_6).info_hit, info_way : (x_6).info_way,
        edir_hit : (x_6).edir_hit, edir_way : (x_6).edir_way, edir_slot :
        (x_6).edir_slot, info : (x_6).info, value_write : (Bool)'(False),
        value : unpack(0), may_victim : (x_6).may_victim, reps :
        (x_6).reps});
        Struct52 x_17 = (Struct52 {addr : (x_16).addr, info_write :
        (Bool)'(True), info_hit : (x_16).info_hit, info_way :
        (x_16).info_way, edir_hit : (x_16).edir_hit, edir_way :
        (x_16).edir_way, edir_slot : (x_16).edir_slot, info : Struct11
        {mesi_owned : ((x_16).info).mesi_owned, mesi_status :
        (Bit#(3))'(3'h1), mesi_dir_st : ((x_16).info).mesi_dir_st,
        mesi_dir_sharers : ((x_16).info).mesi_dir_sharers}, value_write :
        (x_16).value_write, value : (x_16).value, may_victim :
        (x_16).may_victim, reps : (x_16).reps});
        Struct52 x_18 = (Struct52 {addr : (x_17).addr, info_write :
        (Bool)'(True), info_hit : (x_17).info_hit, info_way :
        (x_17).info_way, edir_hit : (x_17).edir_hit, edir_way :
        (x_17).edir_way, edir_slot : (x_17).edir_slot, info : Struct11
        {mesi_owned : (Bool)'(False), mesi_status :
        ((x_17).info).mesi_status, mesi_dir_st : ((x_17).info).mesi_dir_st,
        mesi_dir_sharers : ((x_17).info).mesi_dir_sharers}, value_write :
        (x_17).value_write, value : (x_17).value, may_victim :
        (x_17).may_victim, reps :
        (x_17).reps});
        let x_21 = ?;
        if ((x_8).valid) begin
            let x_19 <- victims__001__setVictim(Struct54 {victim_idx :
            (x_8).data, victim_info : (x_18).info, victim_value :
            (x_18).value});
            x_21 = x_9;
        end else begin
            let x_20 <- cache__001__valueRsLineRq(x_18);
            x_21 = x_20;
        end
        Struct21 x_22 = (Struct21 {enq_type : ((((Bit#(3))'(3'h3))[2:1]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : (((((Bit#(3))'(3'h3))[2:1])
        == ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : ((Bit#(3))'(3'h3))[0:0], enq_msg : Struct1 {id :
        (Bit#(6))'(6'hd), type_ : (Bool)'(True), addr : (x_15).addr, value :
        unpack(0)}});
        let x_23 <- makeEnq_parentChildren001(x_22);
    endrule

    rule rule_exec_001_131;
        $display ("Rule fired: rule_exec_001_131 at %t", $time);
        let x_0 <- deq_fifoL2E_001();
        Struct42 x_1 = ((x_0).lr_ir_pp);
        Bit#(3) x_2 = ((x_1).ir_msg_from);
        Struct1 x_3 = ((x_1).ir_msg);
        Bit#(3) x_4 = ((x_1).ir_mshr_id);
        Bool x_5 = ((x_1).ir_is_rs_rel);
        when (! (x_5), noAction);
        Struct45 x_6 = ((x_0).lr_ir);
        Struct11 x_7 = ((x_6).info);
        Struct41 x_8 = ((x_1).ir_by_victim);
        Vector#(4, Bit#(64)) x_9 = ((x_0).lr_value);
        let x_10 <- getMSHR_001(x_4);
        Vector#(4, Bit#(64)) x_11 = (unpack(0));
        Bool x_12 = ((x_7).mesi_owned);
        Bit#(3) x_13 = ((x_7).mesi_status);
        Struct18 x_14 = (Struct18 {dir_st : (x_7).mesi_dir_st, dir_excl :
        ((((x_7).mesi_dir_sharers)[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(1))'(1'h0)) : (((Bit#(1))'(1'h1)) +
        ((((((x_7).mesi_dir_sharers)[1:1])[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(1))'(1'h0)) : (((Bit#(1))'(1'h1)) + (unpack(0))))))),
        dir_sharers : (x_7).mesi_dir_sharers});
        when ((x_2) == ((Bit#(3))'(3'h5)), noAction);
        when (((x_3).id) == ((Bit#(6))'(6'he)), noAction);
        when (! ((x_3).type_), noAction);
        when (! ((x_13) < ((Bit#(3))'(3'h3))), noAction);
        Struct1 x_15 = (x_3);
        Struct52 x_16 = (Struct52 {addr : (x_3).addr, info_write :
        (Bool)'(False), info_hit : (x_6).info_hit, info_way : (x_6).info_way,
        edir_hit : (x_6).edir_hit, edir_way : (x_6).edir_way, edir_slot :
        (x_6).edir_slot, info : (x_6).info, value_write : (Bool)'(False),
        value : unpack(0), may_victim : (x_6).may_victim, reps :
        (x_6).reps});
        Struct52 x_17 = (Struct52 {addr : (x_16).addr, info_write :
        (Bool)'(True), info_hit : (x_16).info_hit, info_way :
        (x_16).info_way, edir_hit : (x_16).edir_hit, edir_way :
        (x_16).edir_way, edir_slot : (x_16).edir_slot, info : Struct11
        {mesi_owned : ((x_16).info).mesi_owned, mesi_status :
        (Bit#(3))'(3'h1), mesi_dir_st : ((x_16).info).mesi_dir_st,
        mesi_dir_sharers : ((x_16).info).mesi_dir_sharers}, value_write :
        (x_16).value_write, value : (x_16).value, may_victim :
        (x_16).may_victim, reps : (x_16).reps});
        Struct52 x_18 = (Struct52 {addr : (x_17).addr, info_write :
        (Bool)'(True), info_hit : (x_17).info_hit, info_way :
        (x_17).info_way, edir_hit : (x_17).edir_hit, edir_way :
        (x_17).edir_way, edir_slot : (x_17).edir_slot, info : Struct11
        {mesi_owned : (Bool)'(False), mesi_status :
        ((x_17).info).mesi_status, mesi_dir_st : ((x_17).info).mesi_dir_st,
        mesi_dir_sharers : ((x_17).info).mesi_dir_sharers}, value_write :
        (x_17).value_write, value : (x_17).value, may_victim :
        (x_17).may_victim, reps :
        (x_17).reps});
        let x_21 = ?;
        if ((x_8).valid) begin
            let x_19 <- victims__001__setVictim(Struct54 {victim_idx :
            (x_8).data, victim_info : (x_18).info, victim_value :
            (x_18).value});
            x_21 = x_9;
        end else begin
            let x_20 <- cache__001__valueRsLineRq(x_18);
            x_21 = x_20;
        end
        Struct21 x_22 = (Struct21 {enq_type : ((((Bit#(3))'(3'h3))[2:1]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : (((((Bit#(3))'(3'h3))[2:1])
        == ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : ((Bit#(3))'(3'h3))[0:0], enq_msg : Struct1 {id :
        (Bit#(6))'(6'hf), type_ : (Bool)'(True), addr : (x_15).addr, value :
        unpack(0)}});
        let x_23 <- makeEnq_parentChildren001(x_22);
    endrule

    rule rule_exec_001_20;
        $display ("Rule fired: rule_exec_001_20 at %t", $time);
        let x_0 <- victims__001__getFirstVictim();
        Bit#(64) x_1 = ((x_0).victim_addr);
        Struct11 x_2 = ((x_0).victim_info);
        Vector#(4, Bit#(64)) x_3 = ((x_0).victim_value);
        Struct1 x_4 = (Struct1 {id : unpack(0), type_ : (Bool)'(False), addr
        : x_1, value : unpack(0)});
        let x_5 <- getULImm_001(x_4);
        let x_6 <- victims__001__setVictimRq(Struct55 {victim_addr : x_1,
        victim_req : x_5});
        Struct51 x_7 = (Struct51 {m_status : (Bit#(3))'(3'h4), m_next :
        unpack(0), m_is_ul : (Bool)'(True), m_msg : x_4, m_qidx : unpack(0),
        m_rsb : (Bool)'(False), m_dl_rss_from : unpack(0), m_dl_rss_recv :
        unpack(0), m_dl_rss : unpack(0)});
        Vector#(4, Bit#(64)) x_8 = (unpack(0));
        Bool x_9 = ((x_2).mesi_owned);
        Bit#(3) x_10 = ((x_2).mesi_status);
        Struct18 x_11 = (Struct18 {dir_st : (x_2).mesi_dir_st, dir_excl :
        ((((x_2).mesi_dir_sharers)[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(1))'(1'h0)) : (((Bit#(1))'(1'h1)) +
        ((((((x_2).mesi_dir_sharers)[1:1])[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(1))'(1'h0)) : (((Bit#(1))'(1'h1)) + (unpack(0))))))),
        dir_sharers : (x_2).mesi_dir_sharers});
        when (! ((x_4).type_), noAction);
        when (((x_9) == ((Bool)'(False))) && ((((Bit#(3))'(3'h0)) < (x_10))
        && ((x_10) < ((Bit#(3))'(3'h4)))), noAction);
        Struct21 x_12 = (Struct21 {enq_type : ((((Bit#(3))'(3'h1))[2:1]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : (((((Bit#(3))'(3'h1))[2:1])
        == ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : ((Bit#(3))'(3'h1))[0:0], enq_msg : Struct1 {id :
        (Bit#(6))'(6'h14), type_ : (Bool)'(False), addr : (x_4).addr, value :
        unpack(0)}});
        let x_13 <- makeEnq_parentChildren001(x_12);
    endrule

    rule rule_exec_001_21;
        $display ("Rule fired: rule_exec_001_21 at %t", $time);
        let x_0 <- victims__001__getFirstVictim();
        Bit#(64) x_1 = ((x_0).victim_addr);
        Struct11 x_2 = ((x_0).victim_info);
        Vector#(4, Bit#(64)) x_3 = ((x_0).victim_value);
        Struct1 x_4 = (Struct1 {id : unpack(0), type_ : (Bool)'(False), addr
        : x_1, value : unpack(0)});
        let x_5 <- getULImm_001(x_4);
        let x_6 <- victims__001__setVictimRq(Struct55 {victim_addr : x_1,
        victim_req : x_5});
        Struct51 x_7 = (Struct51 {m_status : (Bit#(3))'(3'h4), m_next :
        unpack(0), m_is_ul : (Bool)'(True), m_msg : x_4, m_qidx : unpack(0),
        m_rsb : (Bool)'(False), m_dl_rss_from : unpack(0), m_dl_rss_recv :
        unpack(0), m_dl_rss : unpack(0)});
        Vector#(4, Bit#(64)) x_8 = (unpack(0));
        Bool x_9 = ((x_2).mesi_owned);
        Bit#(3) x_10 = ((x_2).mesi_status);
        Struct18 x_11 = (Struct18 {dir_st : (x_2).mesi_dir_st, dir_excl :
        ((((x_2).mesi_dir_sharers)[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(1))'(1'h0)) : (((Bit#(1))'(1'h1)) +
        ((((((x_2).mesi_dir_sharers)[1:1])[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(1))'(1'h0)) : (((Bit#(1))'(1'h1)) + (unpack(0))))))),
        dir_sharers : (x_2).mesi_dir_sharers});
        when (! ((x_4).type_), noAction);
        when (((Bit#(3))'(3'h0)) < (x_10), noAction);
        Struct21 x_12 = (Struct21 {enq_type : ((((Bit#(3))'(3'h1))[2:1]) ==
        ((Bit#(2))'(2'h2)) ? ((Bit#(2))'(2'h2)) : (((((Bit#(3))'(3'h1))[2:1])
        == ((Bit#(2))'(2'h0)) ? ((Bit#(2))'(2'h0)) : ((Bit#(2))'(2'h1))))),
        enq_ch_idx : ((Bit#(3))'(3'h1))[0:0], enq_msg : Struct1 {id :
        (Bit#(6))'(6'h15), type_ : (Bool)'(False), addr : (x_4).addr, value :
        x_3}});
        let x_13 <- makeEnq_parentChildren001(x_12);
    endrule

    rule rule_exec_001_22;
        $display ("Rule fired: rule_exec_001_22 at %t", $time);
        let x_0 <- deq_fifoL2E_001();
        Struct42 x_1 = ((x_0).lr_ir_pp);
        Bit#(3) x_2 = ((x_1).ir_msg_from);
        Struct1 x_3 = ((x_1).ir_msg);
        Bit#(3) x_4 = ((x_1).ir_mshr_id);
        Bool x_5 = ((x_1).ir_is_rs_rel);
        when (! (x_5), noAction);
        Struct45 x_6 = ((x_0).lr_ir);
        Struct11 x_7 = ((x_6).info);
        Struct41 x_8 = ((x_1).ir_by_victim);
        Vector#(4, Bit#(64)) x_9 = ((x_0).lr_value);
        let x_10 <- getMSHR_001(x_4);
        Vector#(4, Bit#(64)) x_11 = (unpack(0));
        Bool x_12 = ((x_7).mesi_owned);
        Bit#(3) x_13 = ((x_7).mesi_status);
        Struct18 x_14 = (Struct18 {dir_st : (x_7).mesi_dir_st, dir_excl :
        ((((x_7).mesi_dir_sharers)[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(1))'(1'h0)) : (((Bit#(1))'(1'h1)) +
        ((((((x_7).mesi_dir_sharers)[1:1])[0:0]) == ((Bit#(1))'(1'h1)) ?
        ((Bit#(1))'(1'h0)) : (((Bit#(1))'(1'h1)) + (unpack(0))))))),
        dir_sharers : (x_7).mesi_dir_sharers});
        when ((x_2) == ({((Bit#(2))'(2'h2)),((Bit#(1))'(1'h1))}),
        noAction);
        when (((x_3).id) == ((Bit#(6))'(6'h16)), noAction);
        when (((x_10).m_status) == ((Bit#(3))'(3'h4)), noAction);
        when (! ((x_10).m_rsb), noAction);
        when ((x_3).type_, noAction);
        when ((Bool)'(True), noAction);
        Struct1 x_15 = (x_3);
        Struct52 x_16 = (Struct52 {addr : (x_3).addr, info_write :
        (Bool)'(False), info_hit : (x_6).info_hit, info_way : (x_6).info_way,
        edir_hit : (x_6).edir_hit, edir_way : (x_6).edir_way, edir_slot :
        (x_6).edir_slot, info : (x_6).info, value_write : (Bool)'(False),
        value : unpack(0), may_victim : (x_6).may_victim, reps :
        (x_6).reps});
        Struct52 x_17 = (Struct52 {addr : (x_16).addr, info_write :
        (Bool)'(True), info_hit : (x_16).info_hit, info_way :
        (x_16).info_way, edir_hit : (x_16).edir_hit, edir_way :
        (x_16).edir_way, edir_slot : (x_16).edir_slot, info : Struct11
        {mesi_owned : ((x_16).info).mesi_owned, mesi_status :
        (Bit#(3))'(3'h0), mesi_dir_st : ((x_16).info).mesi_dir_st,
        mesi_dir_sharers : ((x_16).info).mesi_dir_sharers}, value_write :
        (x_16).value_write, value : (x_16).value, may_victim :
        (x_16).may_victim, reps : (x_16).reps});
        Struct52 x_18 = (Struct52 {addr : (x_17).addr, info_write :
        (Bool)'(True), info_hit : (x_17).info_hit, info_way :
        (x_17).info_way, edir_hit : (x_17).edir_hit, edir_way :
        (x_17).edir_way, edir_slot : (x_17).edir_slot, info : Struct11
        {mesi_owned : (Bool)'(False), mesi_status :
        ((x_17).info).mesi_status, mesi_dir_st : ((x_17).info).mesi_dir_st,
        mesi_dir_sharers : ((x_17).info).mesi_dir_sharers}, value_write :
        (x_17).value_write, value : (x_17).value, may_victim :
        (x_17).may_victim, reps :
        (x_17).reps});
        let x_21 = ?;
        if ((x_8).valid) begin
            let x_19 <- victims__001__setVictim(Struct54 {victim_idx :
            (x_8).data, victim_info : (x_18).info, victim_value :
            (x_18).value});
            x_21 = x_9;
        end else begin
            let x_20 <- cache__001__valueRsLineRq(x_18);
            x_21 = x_20;
        end
        let x_22 <- releaseMSHR_001(x_4);
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
    Module66 m66 <- mkModule66 (m1.enq_fifoPInput00, deq_fifo002);
    Module67 m67 <- mkModule67 (m53.deq_fifo0010, m2.enq_fifoCRqInput_00,
    m33.deq_fifo0000);
    Module68 m68 <- mkModule68 (m54.deq_fifo0011, m3.enq_fifoCRsInput_00,
    m34.deq_fifo0001);
    Module69 m69 <- mkModule69 (m3.deq_fifoCRsInput_00, m4.enq_fifoCInput_00,
    m2.deq_fifoCRqInput_00);
    Module70 m70 <- mkModule70 (m35.enq_fifo0002, m55.enq_fifo0012,
    enq_fifo001, enq_fifo000);
    Module71 m71 <- mkModule71 (m24.wrReq_repRam__00, m24.rdResp_repRam__00,
    m24.rdReq_repRam__00);
    Module72 m72 <- mkModule72 (m26.enq_fifoPInput000, m35.deq_fifo0002);

    Module73 m73 <- mkModule73 (m27.enq_fifoCInput_000, m36.deq_fifo00000);

    Module74 m74 <- mkModule74 (m37.enq_fifo00002, m34.enq_fifo0001,
    m33.enq_fifo0000);
    Module75 m75 <- mkModule75 (m44.wrReq_repRam__000,
    m44.rdResp_repRam__000, m44.rdReq_repRam__000);
    Module76 m76 <- mkModule76 (m46.enq_fifoPInput001, m55.deq_fifo0012);

    Module77 m77 <- mkModule77 (m47.enq_fifoCInput_001, m56.deq_fifo00100);

    Module78 m78 <- mkModule78 (m57.enq_fifo00102, m54.enq_fifo0011,
    m53.enq_fifo0010);
    Module79 m79 <- mkModule79 (m64.wrReq_repRam__001,
    m64.rdResp_repRam__001, m64.rdReq_repRam__001);
    Module80 m80 <- mkModule80 (m19.wrReq_edirRam__00__3,
    m20.wrReq_edirRam__00__2, m21.wrReq_edirRam__00__1,
    m22.wrReq_edirRam__00__0, m23.wrReq_dataRam__00, m71.repAccess__00,
    m10.victims__00__registerVictim, m11.wrReq_infoRam__00__7,
    m12.wrReq_infoRam__00__6, m13.wrReq_infoRam__00__5,
    m14.wrReq_infoRam__00__4, m15.wrReq_infoRam__00__3,
    m16.wrReq_infoRam__00__2, m17.wrReq_infoRam__00__1,
    m18.wrReq_infoRam__00__0, m23.rdResp_dataRam__00, m23.rdReq_dataRam__00,
    m71.repGetRs__00, m19.rdResp_edirRam__00__3, m20.rdResp_edirRam__00__2,
    m21.rdResp_edirRam__00__1, m22.rdResp_edirRam__00__0,
    m11.rdResp_infoRam__00__7, m12.rdResp_infoRam__00__6,
    m13.rdResp_infoRam__00__5, m14.rdResp_infoRam__00__4,
    m15.rdResp_infoRam__00__3, m16.rdResp_infoRam__00__2,
    m17.rdResp_infoRam__00__1, m18.rdResp_infoRam__00__0, m71.repGetRq__00,
    m19.rdReq_edirRam__00__3, m20.rdReq_edirRam__00__2,
    m21.rdReq_edirRam__00__1, m22.rdReq_edirRam__00__0,
    m11.rdReq_infoRam__00__7, m12.rdReq_infoRam__00__6,
    m13.rdReq_infoRam__00__5, m14.rdReq_infoRam__00__4,
    m15.rdReq_infoRam__00__3, m16.rdReq_infoRam__00__2,
    m17.rdReq_infoRam__00__1, m18.rdReq_infoRam__00__0);
    Module81 m81 <- mkModule81 (m43.wrReq_dataRam__000, m75.repAccess__000,
    m38.victims__000__registerVictim, m39.wrReq_infoRam__000__3,
    m40.wrReq_infoRam__000__2, m41.wrReq_infoRam__000__1,
    m42.wrReq_infoRam__000__0, m43.rdResp_dataRam__000,
    m43.rdReq_dataRam__000, m75.repGetRs__000, m39.rdResp_infoRam__000__3,
    m40.rdResp_infoRam__000__2, m41.rdResp_infoRam__000__1,
    m42.rdResp_infoRam__000__0, m75.repGetRq__000, m39.rdReq_infoRam__000__3,
    m40.rdReq_infoRam__000__2, m41.rdReq_infoRam__000__1,
    m42.rdReq_infoRam__000__0);
    Module82 m82 <- mkModule82 (m63.wrReq_dataRam__001, m79.repAccess__001,
    m58.victims__001__registerVictim, m59.wrReq_infoRam__001__3,
    m60.wrReq_infoRam__001__2, m61.wrReq_infoRam__001__1,
    m62.wrReq_infoRam__001__0, m63.rdResp_dataRam__001,
    m63.rdReq_dataRam__001, m79.repGetRs__001, m59.rdResp_infoRam__001__3,
    m60.rdResp_infoRam__001__2, m61.rdResp_infoRam__001__1,
    m62.rdResp_infoRam__001__0, m79.repGetRq__001, m59.rdReq_infoRam__001__3,
    m60.rdReq_infoRam__001__2, m61.rdReq_infoRam__001__1,
    m62.rdReq_infoRam__001__0);
    Module83 m83 <- mkModule83 (m10.victims__00__setVictimRq,
    m25.getULImm_00, m10.victims__00__getFirstVictim, m25.transferUpDown_00,
    m70.broadcast_parentChildren00, m25.registerDL_00, m25.registerUL_00,
    m70.makeEnq_parentChildren00, m80.cache__00__valueRsLineRq,
    m10.victims__00__setVictim, m25.getMSHR_00, m9.deq_fifoL2E_00,
    m8.deq_fifoI2L_child_00, m8.enq_fifoI2L_child_00,
    m7.deq_fifoN2I_child_00, m25.getWait_00, m25.findDL_00,
    m7.enq_fifoN2I_child_00, m25.getCRqSlot_00, m4.deq_fifoCInput_00,
    m10.victims__00__getVictim, m9.enq_fifoL2E_00,
    m80.cache__00__infoRsValueRq, m6.deq_fifoI2L_parent_00, m25.addRs_00,
    m6.enq_fifoI2L_parent_00, m80.cache__00__infoRq,
    m5.deq_fifoN2I_parent_00, m25.getRsReady_00, m25.releaseMSHR_00,
    m10.victims__00__releaseVictim, m25.findUL_00, m5.enq_fifoN2I_parent_00,
    m10.victims__00findVictim, m25.getPRqSlot_00, m1.deq_fifoPInput00);

    Module84 m84 <- mkModule84 (m38.victims__000__setVictimRq,
    m45.getULImm_000, m38.victims__000__getFirstVictim,
    m38.victims__000__setVictim, m45.registerUL_000,
    m74.makeEnq_parentChildren000, m81.cache__000__valueRsLineRq,
    m45.getMSHR_000, m32.deq_fifoL2E_000, m31.deq_fifoI2L_child_000,
    m31.enq_fifoI2L_child_000, m30.deq_fifoN2I_child_000, m45.getWait_000,
    m45.findDL_000, m30.enq_fifoN2I_child_000, m45.getCRqSlot_000,
    m27.deq_fifoCInput_000, m38.victims__000__getVictim, m32.enq_fifoL2E_000,
    m81.cache__000__infoRsValueRq, m29.deq_fifoI2L_parent_000, m45.addRs_000,
    m29.enq_fifoI2L_parent_000, m81.cache__000__infoRq,
    m28.deq_fifoN2I_parent_000, m45.getRsReady_000, m45.releaseMSHR_000,
    m38.victims__000__releaseVictim, m45.findUL_000,
    m28.enq_fifoN2I_parent_000, m38.victims__000findVictim,
    m45.getPRqSlot_000, m26.deq_fifoPInput000);
    Module85 m85 <- mkModule85 (m58.victims__001__setVictimRq,
    m65.getULImm_001, m58.victims__001__getFirstVictim,
    m58.victims__001__setVictim, m65.registerUL_001,
    m78.makeEnq_parentChildren001, m82.cache__001__valueRsLineRq,
    m65.getMSHR_001, m52.deq_fifoL2E_001, m51.deq_fifoI2L_child_001,
    m51.enq_fifoI2L_child_001, m50.deq_fifoN2I_child_001, m65.getWait_001,
    m65.findDL_001, m50.enq_fifoN2I_child_001, m65.getCRqSlot_001,
    m47.deq_fifoCInput_001, m58.victims__001__getVictim, m52.enq_fifoL2E_001,
    m82.cache__001__infoRsValueRq, m49.deq_fifoI2L_parent_001, m65.addRs_001,
    m49.enq_fifoI2L_parent_001, m82.cache__001__infoRq,
    m48.deq_fifoN2I_parent_001, m65.getRsReady_001, m65.releaseMSHR_001,
    m58.victims__001__releaseVictim, m65.findUL_001,
    m48.enq_fifoN2I_parent_001, m58.victims__001findVictim,
    m65.getPRqSlot_001, m46.deq_fifoPInput001);
    //// Interface

    function MemRqRs#(Struct1) getMemRqRs (function Action enq_rq (Struct1 _),
                                           function ActionValue#(Struct1) deq_rs ());
        return interface MemRqRs;
                   method mem_enq_rq = enq_rq;
                   method mem_deq_rs = deq_rs;
               endinterface;
    endfunction

    Vector#(L1Num, MemRqRs#(Struct1)) _l1Ifc = newVector();
    _l1Ifc[0] = getMemRqRs(m36.enq_fifo00000, m37.deq_fifo00002);
    _l1Ifc[1] = getMemRqRs(m56.enq_fifo00100, m57.deq_fifo00102);
    interface l1Ifc = _l1Ifc;

    interface DMA llDma;
        method dma_rdReq = m23.rdReq_dataRam__00;
        method dma_wrReq = m23.wrReq_dataRam__00;
        method dma_rdResp = m23.rdResp_dataRam__00;
    endinterface

endmodule
