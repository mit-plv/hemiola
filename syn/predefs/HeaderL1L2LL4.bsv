import Vector::*;
import BuildVector::*;
import FIFO::*;
import FIFOF::*;
import RWBramCore::*;
import SpecialFIFOs::*;

typedef 4 L1Num;

interface MemRqRs;
    method Action mem_enq_rq (Struct1 rq);
    method ActionValue#(Struct1) mem_deq_rs ();
endinterface

interface DMA;
    method Action dma_rdReq (Bit#(14) addr);
    method Action dma_wrReq (Struct36 rq);
    method ActionValue#(Vector#(4, Bit#(64))) dma_rdResp ();
endinterface

interface CC;
    interface Vector#(L1Num, MemRqRs) l1Ifc;
    interface DMA llDma;
endinterface

