//// Interface

    function MemRqRs#(Struct1) getMemRqRs (function Action enq_rq (Struct1 _),
                                           function ActionValue#(Struct1) deq_rs ());
        return interface MemRqRs;
                   method mem_enq_rq = enq_rq;
                   method mem_deq_rs = deq_rs;
               endinterface;
    endfunction

    Vector#(L1Num, MemRqRs#(Struct1)) _l1Ifc = newVector();
    _l1Ifc[0] = getMemRqRs(m68.enq_fifo000000, m69.deq_fifo000002);
    _l1Ifc[1] = getMemRqRs(m86.enq_fifo000100, m87.deq_fifo000102);
    _l1Ifc[2] = getMemRqRs(m129.enq_fifo001000, m130.deq_fifo001002);
    _l1Ifc[3] = getMemRqRs(m147.enq_fifo001100, m148.deq_fifo001102);
    interface l1Ifc = _l1Ifc;

    interface DMA llDma;
        method dma_rdReq = m32.rdReq_dataRam__00;
        method dma_wrReq = m32.wrReq_dataRam__00;
        method dma_rdResp = m32.rdResp_dataRam__00;
    endinterface
