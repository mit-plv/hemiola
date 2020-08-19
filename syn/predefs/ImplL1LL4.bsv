    //// Interface

    function MemRqRs getMemRqRs (function Action enq_rq (Struct2 _),
                                 function ActionValue#(Struct2) deq_rs ());
        return interface MemRqRs;
                   method mem_enq_rq = enq_rq;
                   method mem_deq_rs = deq_rs;
               endinterface;
    endfunction

    Vector#(L1Num, MemRqRs) _l1Ifc = newVector();
    _l1Ifc[0] = getMemRqRs(m28.enq_fifo00000, m29.deq_fifo00002);
    _l1Ifc[1] = getMemRqRs(m39.enq_fifo00100, m40.deq_fifo00102);
    _l1Ifc[2] = getMemRqRs(m50.enq_fifo00200, m51.deq_fifo00202);
    _l1Ifc[3] = getMemRqRs(m61.enq_fifo00300, m62.deq_fifo00302);
    interface l1Ifc = _l1Ifc;

    interface DMA llDma;
        method dma_putRq = m17.putRq_dataRam_00;
        method dma_getRs = m17.getRs_dataRam_00;
    endinterface
