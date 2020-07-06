import Vector::*;
import BuildVector::*;
import FIFO::*;
import FIFOF::*;

import HCC::*;
import HCCTypes::*;
import HMemBank::*;

interface IgnoreEnq#(type elt_t);
    method Action ignore_enq (elt_t v);
endinterface

module mkIgnoreEnq(IgnoreEnq#(CCMsg));
    method Action ignore_enq (CCMsg v) = noAction;
endmodule

interface IgnoreDeq#(type elt_t);
    method ActionValue#(elt_t) ignore_deq ();
endinterface

module mkIgnoreDeq(IgnoreDeq#(CCMsg));
    method ActionValue#(CCMsg) ignore_deq () if (False);
        return unpack(0);
    endmethod
endmodule

interface CCMem;
    interface CC cc;
    interface DMA memDma;
endinterface

// CC + BRAM memory
(* synthesize *)
module mkCCBramMem(CCMem);
    MemBank mb <- mkMemBankBram();
    IgnoreEnq#(CCMsg) ige <- mkIgnoreEnq();
    IgnoreDeq#(CCMsg) igd <- mkIgnoreDeq();
    CC mem <- mkCC(mb.getMemRs, ige.ignore_enq, mb.putMemRq);
    interface cc = mem;
    interface memDma = mb.memDma;
endmodule
