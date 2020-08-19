    //// Interface

    function MemRqRs getMemRqRs (function Action enq_rq (Struct2 _),
                                 function ActionValue#(Struct2) deq_rs ());
        return interface MemRqRs;
                   method mem_enq_rq = enq_rq;
                   method mem_deq_rs = deq_rs;
               endinterface;
    endfunction

    Vector#(L1Num, MemRqRs) _l1Ifc = newVector();
    _l1Ifc[0] = getMemRqRs(m41.enq_fifo000000, m42.deq_fifo000002);
    _l1Ifc[1] = getMemRqRs(m52.enq_fifo000100, m53.deq_fifo000102);
    _l1Ifc[2] = getMemRqRs(m76.enq_fifo001000, m77.deq_fifo001002);
    _l1Ifc[3] = getMemRqRs(m87.enq_fifo001100, m88.deq_fifo001102);
    interface l1Ifc = _l1Ifc;

    interface DMA llDma;
        method dma_putRq = m17.putRq_dataRam_00;
        method dma_getRs = m17.getRs_dataRam_00;
    endinterface
