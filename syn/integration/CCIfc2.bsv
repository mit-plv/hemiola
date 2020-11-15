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

