import Vector::*;
import BuildVector::*;
import RWire::*;
import FIFO::*;
import FIFOF::*;

import HCC::*;
import HCCIfc::*;
import HCCTypes::*;
import HCCWrapper::*;
import HCCTest::*;
import HMemBank::*;

////////// Connectal interfaces

interface HostIndication;
    method Action finish(Bit#(64) numResps, Bit#(64) mark);
    method Action dma_rdResp_ll(Bit#(64) val);
    method Action dma_rdResp_mem(Bit#(64) val);
endinterface

interface HostRequest;
    method Action start(Bit#(64) maxCycle);

    method Action dma_rdReq_ll(Bit#(64) faddr);
    method Action dma_wrReq_ll(Bit#(64) faddr,
       Bit#(64) val0, Bit#(64) val1, Bit#(64) val2, Bit#(64) val3);
    method Action dma_rdResp_ll_rq(Bit#(2) lineIdx);

    method Action dma_rdReq_mem(Bit#(64) faddr);
    method Action dma_wrReq_mem(Bit#(64) faddr,
       Bit#(64) val0, Bit#(64) val1, Bit#(64) val2, Bit#(64) val3);
    method Action dma_rdResp_mem_rq(Bit#(2) lineIdx);
endinterface

////////// Connectal interfaces end

interface Host;
    interface HostRequest request;
endinterface

module mkHost#(HostIndication indication) (Host);
    CCMem mem <- mkCCBramMem();
    CCTest tester <- mkCCTestCheck(mem.cc);

    Reg#(Bool) started <- mkReg(False);
    Reg#(Bool) ended <- mkReg(False);

    rule check_end (started && tester.isEnd && !ended);
        let n = tester.getThroughput;
        let m = tester.getMark;
        indication.finish(n, m);
        ended <= True;
    endrule

    interface HostRequest request;
        method Action start(Bit#(64) maxCycle);
	    tester.start(maxCycle);
	    started <= True;
	endmethod

        method Action dma_rdReq_ll(Bit#(64) faddr);
            let baddr = truncate(faddr >> valueOf(AddrOffset));
            mem.cc.llDma.dma_rdReq(baddr);
        endmethod
        method Action dma_wrReq_ll(Bit#(64) faddr,
           Bit#(64) val0, Bit#(64) val1, Bit#(64) val2, Bit#(64) val3);
            Vector#(4, Bit#(64)) val = newVector();
            val[0] = val0; val[1] = val1; val[2] = val2; val[3] = val3;
            mem.cc.llDma.dma_wrReq(
               LLDmaRq { addr: truncate(faddr >> valueOf(AddrOffset)), datain: val});
        endmethod
        method Action dma_rdResp_ll_rq(Bit#(2) lineIdx);
            let line <- mem.cc.llDma.dma_rdResp();
            indication.dma_rdResp_ll(line[lineIdx]);
        endmethod

        method Action dma_rdReq_mem(Bit#(64) faddr);
            let baddr = truncate(faddr >> valueOf(AddrOffset));
            mem.memDma.dma_rdReq(baddr);
        endmethod
        method Action dma_wrReq_mem(Bit#(64) faddr,
           Bit#(64) val0, Bit#(64) val1, Bit#(64) val2, Bit#(64) val3);
            Vector#(4, Bit#(64)) val = newVector();
            val[0] = val0; val[1] = val1; val[2] = val2; val[3] = val3;
            mem.memDma.dma_wrReq(
               MemDmaRq { addr: truncate(faddr >> valueOf(AddrOffset)), datain: val});
        endmethod
        method Action dma_rdResp_mem_rq(Bit#(2) lineIdx);
            let line <- mem.memDma.dma_rdResp();
            indication.dma_rdResp_mem(line[lineIdx]);
        endmethod
    endinterface
endmodule
