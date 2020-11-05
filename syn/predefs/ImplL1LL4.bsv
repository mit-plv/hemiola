//// Interface

    function MemRqRs#(Struct1) getMemRqRs (function Action enq_rq (Struct1 _),
                                           function ActionValue#(Struct1) deq_rs ());
        return interface MemRqRs;
                   method mem_enq_rq = enq_rq;
                   method mem_deq_rs = deq_rs;
               endinterface;
    endfunction

    Vector#(L1Num, MemRqRs#(Struct1)) _l1Ifc = newVector();
    _l1Ifc[0] = getMemRqRs(m44.enq_fifo00000, m45.deq_fifo00002);
    _l1Ifc[1] = getMemRqRs(m62.enq_fifo00100, m63.deq_fifo00102);
    _l1Ifc[2] = getMemRqRs(m80.enq_fifo00200, m81.deq_fifo00202);
    _l1Ifc[3] = getMemRqRs(m98.enq_fifo00300, m99.deq_fifo00302);
    interface l1Ifc = _l1Ifc;

    interface DMA llDma;
        method dma_rdReq = m33.rdReq_dataRam__00;
        method dma_wrReq = m33.wrReq_dataRam__00;
        method dma_rdResp = m33.rdResp_dataRam__00;
    endinterface
