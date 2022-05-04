//// Interface

    function MemRqRs#(Struct1) getMemRqRs (function Action enq_rq (Struct1 _),
                                           function ActionValue#(Struct1) deq_rs ());
        return interface MemRqRs;
                   method mem_enq_rq = enq_rq;
                   method mem_deq_rs = deq_rs;
               endinterface;
    endfunction

    Vector#(L_1Num, MemRqRs#(Struct_1)) _l_1Ifc = newVector();
    _l1Ifc[0] = getMemRqRs(m43.enq_fifo_0_0_0_0_0, m44.deq_fifo_0_0_0_0_2);
    _l1Ifc[1] = getMemRqRs(m61.enq_fifo_0_0_1_0_0, m62.deq_fifo_0_0_1_0_2);
    _l1Ifc[2] = getMemRqRs(m79.enq_fifo_0_0_2_0_0, m80.deq_fifo_0_0_2_0_2);
    _l1Ifc[3] = getMemRqRs(m97.enq_fifo_0_0_3_0_0, m98.deq_fifo_0_0_3_0_2);
    interface l_1Ifc = _l_1Ifc;

    interface DMA llDma;
        method dma_rdReq = m32.rdReq_dataRam___0_0;
        method dma_wrReq = m32.wrReq_dataRam___0_0;
        method dma_rdResp = m32.rdResp_dataRam___0_0;
    endinterface
