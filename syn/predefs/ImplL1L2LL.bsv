//// Interface

    function MemRqRs#(Struct1) getMemRqRs (function Action enq_rq (Struct1 _),
                                           function ActionValue#(Struct1) deq_rs ());
        return interface MemRqRs;
                   method mem_enq_rq = enq_rq;
                   method mem_deq_rs = deq_rs;
               endinterface;
    endfunction

    Vector#(L1Num, MemRqRs#(Struct1)) _l1Ifc = newVector();
    _l1Ifc[0] = getMemRqRs(m71.enq_fifo000000, m72.deq_fifo000002);
    _l1Ifc[1] = getMemRqRs(m90.enq_fifo000100, m91.deq_fifo000102);
    _l1Ifc[2] = getMemRqRs(m136.enq_fifo001000, m137.deq_fifo001002);
    _l1Ifc[3] = getMemRqRs(m155.enq_fifo001100, m156.deq_fifo001102);
    interface l1Ifc = _l1Ifc;

    interface DMA llDma;
        method dma_rdReq = m34.rdReq_dataRam__00;
        method dma_wrReq = m34.wrReq_dataRam__00;
        method dma_rdResp = m34.rdResp_dataRam__00;
    endinterface
