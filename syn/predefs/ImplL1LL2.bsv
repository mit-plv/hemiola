//// Interface

    function MemRqRs#(Struct1) getMemRqRs (function Action enq_rq (Struct1 _),
                                           function ActionValue#(Struct1) deq_rs ());
        return interface MemRqRs;
                   method mem_enq_rq = enq_rq;
                   method mem_deq_rs = deq_rs;
               endinterface;
    endfunction

    Vector#(L1Num, MemRqRs#(Struct1)) _l1Ifc = newVector();
    _l1Ifc[0] = getMemRqRs(m31.enq_fifo_0_0_0_0_0, m32.deq_fifo_0_0_0_0_2);
    _l1Ifc[1] = getMemRqRs(m49.enq_fifo_0_0_1_0_0, m50.deq_fifo_0_0_1_0_2);
    interface l1Ifc = _l1Ifc;

    interface DMA llDma;
        method dma_rdReq = m20.rdReq_dataRam___0_0;
        method dma_wrReq = m20.wrReq_dataRam___0_0;
        method dma_rdResp = m20.rdResp_dataRam___0_0;
    endinterface
