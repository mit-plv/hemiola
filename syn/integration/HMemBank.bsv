import Vector::*;
import FIFO::*;
import FIFOF::*;
import RWBramCore::*;
import Assert::*;
import RegFile::*;
import SpecialFIFOs::*;

import HCC::*;
import HCCIfc::*;
import HCCTypes::*;

typedef 14 MemAddrSz;
typedef Bit#(MemAddrSz) MemAddr;
typedef struct { MemAddr addr; CCValue datain; } MemDmaRq deriving (Bits, Eq);

interface MemBank;
    method Action putMemRq(CCMsg _);
    method ActionValue#(CCMsg) getMemRs();
    interface DMA#(MemAddr, MemDmaRq, CCValue) memDma;
endinterface

typedef 30 MemLatency; // #cycles to delay
module mkDelayedBram(RWBramCore#(addrT, dataT)) provisos(
    Bits#(addrT, addrSz), Bits#(dataT, dataSz)
);
    RWBramCore#(addrT, dataT) mem <- mkRWBramCore();
    Reg#(Bit#(8)) delay <- mkReg(0);

    Reg#(Bool) hasRq <- mkReg(False);
    Reg#(Bool) rqWrite <- mkReg(False);
    Reg#(addrT) rqAddr <- mkRegU;
    Reg#(dataT) rqData <- mkRegU;

    rule dec_delay (hasRq);
        delay <= delay - 1;
        if (delay == 0) begin
            hasRq <= False;
            if (rqWrite) mem.wrReq(rqAddr, rqData);
            else mem.rdReq(rqAddr);
        end
    endrule

    method Action wrReq(addrT a, dataT d) if (!hasRq);
        hasRq <= True;
        delay <= fromInteger(valueOf(MemLatency));
        rqWrite <= True;
        rqAddr <= a;
        rqData <= d;
    endmethod
    method Action rdReq(addrT a) if (!hasRq);
        hasRq <= True;
        delay <= fromInteger(valueOf(MemLatency));
        rqWrite <= False;
        rqAddr <= a;
    endmethod

    method rdResp = mem.rdResp;
    method rdRespValid = mem.rdRespValid;
    method deqRdResp = mem.deqRdResp;
endmodule

// Below implements a simple BRAM-based memory
module mkMemBankBramA#(FIFOF#(CCMsg) rqs, FIFOF#(CCMsg) rss)(MemBank);
    RWBramCore#(MemAddr, CCValue) bram <- mkRWBramCore();
    // RWBramCore#(MemAddr, CCValue) bram <- mkDelayedBram();
    Reg#(CCAddr) rdAddr <- mkReg(0);

    CCMsgId readRqId = 6'h2; // [mesiRqS] in Hemiola
    CCMsgId readRsId = 6'h4; // [mesiRsE] in Hemiola
    CCMsgId writeRqId = 6'ha; // [mesiRqM] in Hemiola
    CCMsgId writeRsId = 6'hb; // [mesiRsM] in Hemiola
    CCMsgId invRqId = 6'h14; // [mesiInvRq] in Hemiola
    CCMsgId invWRqId = 6'h15; // [mesiInvWRq] in Hemiola
    CCMsgId invRsId = 6'h16; // [mesiInvRs] in Hemiola

    // Corresponds to [liGetSImmME] in Hemiola
    rule mem_read_rq (rqs.notEmpty && rqs.first.id == readRqId);
        rqs.deq();
        let raddr = rqs.first.addr;
        dynamicAssert(raddr >> (valueOf(MemAddrSz) + valueOf(AddrOffset)) == 0,
                      "Address out-of-bound exception in [mem_read_rq]");
        rdAddr <= raddr;
        MemAddr baddr = truncate (raddr >> valueOf(AddrOffset));
        bram.rdReq(baddr);
    endrule

    rule mem_read_rs;
        bram.deqRdResp();
        let bval = bram.rdResp;
        CCMsg rs = CCMsg {id: readRsId, type_: True, addr: rdAddr, value: bval};
        rss.enq(rs);
    endrule

    // Corresponds to [liGetMImm] in Hemiola
    rule mem_write (rqs.notEmpty && rqs.first.id == writeRqId);
        // no need to touch memory, just return the response
        rqs.deq();
        let raddr = rqs.first.addr;
        dynamicAssert(raddr >> (valueOf(MemAddrSz) + valueOf(AddrOffset)) == 0,
                      "Address out-of-bound exception in [mem_write]");
        CCMsg rs = CCMsg {id: writeRsId, type_: True, addr: raddr, value: unpack(0)};
        rss.enq(rs);
    endrule

    // Corresponds to [liInvImmE] in Hemiola
    rule mem_inv (rqs.notEmpty && rqs.first.id == invRqId);
        // no need to touch memory, just return the response
        rqs.deq();
        let raddr = rqs.first.addr;
        dynamicAssert(raddr >> (valueOf(MemAddrSz) + valueOf(AddrOffset)) == 0,
                      "Address out-of-bound exception in [mem_inv]");
        CCMsg rs = CCMsg {id: invRsId, type_: True, addr: raddr, value: unpack(0)};
        rss.enq(rs);
    endrule

    // Corresponds to [liInvImmWBME] in Hemiola
    rule mem_wb (rqs.notEmpty && rqs.first.id == invWRqId);
        rqs.deq();
        let raddr = rqs.first.addr;
        dynamicAssert(raddr >> (valueOf(MemAddrSz) + valueOf(AddrOffset)) == 0,
                      "Address out-of-bound exception in [mem_wb]");
        MemAddr baddr = truncate (raddr >> valueOf(AddrOffset));
        CCValue bval = rqs.first.value;
        bram.wrReq(baddr, bval);
        CCMsg rs = CCMsg {id: invRsId, type_: True, addr: raddr, value: unpack(0)};
        rss.enq(rs);
    endrule

    method putMemRq = rqs.enq;
    method ActionValue#(CCMsg) getMemRs;
        rss.deq();
        return rss.first;
    endmethod

    interface DMA memDma;
        method dma_rdReq = bram.rdReq;
        method Action dma_wrReq (MemDmaRq rq);
            bram.wrReq(rq.addr, rq.datain);
        endmethod
        method ActionValue#(CCValue) dma_rdResp ();
            bram.deqRdResp();
            return bram.rdResp;
        endmethod
    endinterface
endmodule

(* synthesize *)
module mkMemBankBram(MemBank);
    FIFOF#(CCMsg) rqs <- mkFIFOF();
    FIFOF#(CCMsg) rss <- mkFIFOF();
    MemBank mb <- mkMemBankBramA(rqs, rss);
    return mb;
endmodule

module mkMemBankRegFileA#(FIFOF#(CCMsg) rqs, FIFOF#(CCMsg) rss)(MemBank);
    RegFile#(MemAddr, CCValue) bram <- mkRegFileFull;
    FIFOF#(CCAddr) rdAddr <- mkPipelineFIFOF();
    Reg#(MemAddr) dmaRdAddr <- mkReg(0);

    CCMsgId readRqId = 6'h2; // [mesiRqS] in Hemiola
    CCMsgId readRsId = 6'h4; // [mesiRsE] in Hemiola
    CCMsgId writeRqId = 6'ha; // [mesiRqM] in Hemiola
    CCMsgId writeRsId = 6'hb; // [mesiRsM] in Hemiola
    CCMsgId invRqId = 6'h14; // [mesiInvRq] in Hemiola
    CCMsgId invWRqId = 6'h15; // [mesiInvWRq] in Hemiola
    CCMsgId invRsId = 6'h16; // [mesiInvRs] in Hemiola

    // Corresponds to [liGetSImmME] in Hemiola
    rule mem_read_rq (rqs.notEmpty && rqs.first.id == readRqId);
        rqs.deq();
        let raddr = rqs.first.addr;
        dynamicAssert(raddr >> (valueOf(MemAddrSz) + valueOf(AddrOffset)) == 0,
                      "Address out-of-bound exception in [mem_read_rq]");
        rdAddr.enq(raddr);
    endrule

    rule mem_read_rs if (rdAddr.notEmpty);
        let raddr = rdAddr.first;
        MemAddr baddr = truncate (raddr >> valueOf(AddrOffset));
        let bval = bram.sub(baddr);
        CCMsg rs = CCMsg {id: readRsId, type_: True, addr: raddr, value: bval};
        rdAddr.deq;
        rss.enq(rs);
    endrule

    // Corresponds to [liGetMImm] in Hemiola
    rule mem_write (rqs.notEmpty && rqs.first.id == writeRqId);
        // no need to touch memory, just return the response
        rqs.deq();
        let raddr = rqs.first.addr;
        dynamicAssert(raddr >> (valueOf(MemAddrSz) + valueOf(AddrOffset)) == 0,
                      "Address out-of-bound exception in [mem_write]");
        CCMsg rs = CCMsg {id: writeRsId, type_: True, addr: raddr, value: unpack(0)};
        rss.enq(rs);
    endrule

    // Corresponds to [liInvImmE] in Hemiola
    rule mem_inv (rqs.notEmpty && rqs.first.id == invRqId);
        // no need to touch memory, just return the response
        rqs.deq();
        let raddr = rqs.first.addr;
        dynamicAssert(raddr >> (valueOf(MemAddrSz) + valueOf(AddrOffset)) == 0,
                      "Address out-of-bound exception in [mem_inv]");
        CCMsg rs = CCMsg {id: invRsId, type_: True, addr: raddr, value: unpack(0)};
        rss.enq(rs);
    endrule

    // Corresponds to [liInvImmWBME] in Hemiola
    rule mem_wb (rqs.notEmpty && rqs.first.id == invWRqId);
        rqs.deq();
        let raddr = rqs.first.addr;
        dynamicAssert(raddr >> (valueOf(MemAddrSz) + valueOf(AddrOffset)) == 0,
                      "Address out-of-bound exception in [mem_wb]");
        MemAddr baddr = truncate (raddr >> valueOf(AddrOffset));
        CCValue bval = rqs.first.value;
        bram.upd(baddr, bval);
        CCMsg rs = CCMsg {id: invRsId, type_: True, addr: raddr, value: unpack(0)};
        rss.enq(rs);
    endrule

    method putMemRq = rqs.enq;
    method ActionValue#(CCMsg) getMemRs;
        rss.deq();
        return rss.first;
    endmethod

    interface DMA memDma;
        method Action dma_rdReq (MemAddr addr);
            dmaRdAddr <= addr;
        endmethod
        method Action dma_wrReq (MemDmaRq rq);
            bram.upd(rq.addr, rq.datain);
        endmethod
        method ActionValue#(CCValue) dma_rdResp ();
            let bval = bram.sub(dmaRdAddr);
            return bval;
        endmethod
    endinterface
endmodule

(* synthesize *)
module mkMemBankRegFile(MemBank);
    FIFOF#(CCMsg) rqs <- mkFIFOF();
    FIFOF#(CCMsg) rss <- mkFIFOF();
    MemBank mb <- mkMemBankRegFileA(rqs, rss);
    return mb;
endmodule
