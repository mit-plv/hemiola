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
