import Vector::*;
import BuildVector::*;
import FIFO::*;
import FIFOF::*;
// import Randomizable::*;
import LFSR::*;

import HCC::*;
import HCCTypes::*;
import HMemBank::*;

typedef MemBramAddrSz BAddrSz;

typedef Bit#(32) CycleCnt;
interface CCTest;
    method Action start(CycleCnt maxCycle);
    method Bool isEnd();
    method Bit#(32) getThroughput();
endinterface

typedef 10000 DeadlockDetectCnt;
typedef `RQ_TYPE_SEED RqTypeSeed;
typedef `RQ_BADDR_SEED RqBAddrSeed;

module mkCCTestRandom#(CC mem)(CCTest);
    Reg#(Bool) memInit <- mkReg(False);
    Reg#(Bool) onTest <- mkReg(False);
    Reg#(CycleCnt) maxCycle <- mkReg(0);
    Reg#(CycleCnt) curCycle <- mkReg(0);
    Reg#(Bit#(32)) numResps <- mkReg(0);
    Reg#(Bit#(16)) deadlockDetector <- mkReg(0);

    Vector#(L1Num, LFSR#(Bit#(4))) rq_type_rand <- replicateM(mkLFSR_4);
    LFSR#(Bit#(16)) rq_baddr_rand <- mkLFSR_16;
    Vector#(L1Num, Reg#(Bool)) rq_type_seed <- replicateM(mkReg(False));
    Reg#(Bit#(64)) rq_addr <- mkReg(0);
    Reg#(CCValue) rq_data <- mkReg(replicate(0));

    function Bit#(64) getAddr (Bit#(BAddrSz) baddr);
        Bit#(AddrOffset) pad = 0;
        Bit#(64) addr = zeroExtend({baddr, pad});
        return addr;
    endfunction

    rule mem_init_done (!memInit && mem.isInit);
        memInit <= True;
    endrule

    rule inc_cycle (memInit && onTest);
        curCycle <= curCycle + 1;
        if (curCycle == maxCycle) onTest <= False;
    endrule

    rule detect_deadlock (onTest);
        deadlockDetector <= deadlockDetector + 1;
        if (deadlockDetector == fromInteger(valueOf(DeadlockDetectCnt)))
            $display ("Deadlock detected!");
    endrule

    rule rq_type_seed_toggle (onTest);
        for (Integer i = 0; i < valueOf(L1Num); i = i+1) begin
            let t = rq_type_rand[i].value;
            rq_type_rand[i].next();
            rq_type_seed[i] <= (t[0] == 1 ? True : False);
        end
    endrule
    rule rq_addr_toggle;
        Bit#(BAddrSz) baddr = truncate(rq_baddr_rand.value);
        rq_baddr_rand.next();
        let addr = getAddr(baddr);
        rq_addr <= addr;
    endrule
    rule rq_data_inc;
        rq_data <= update(rq_data, 0, rq_data[0] + 1);
    endrule

    let getRqId = 6'b000000;
    let setRqId = 6'b001000;
    let getRsId = 6'b000001;
    let setRsId = 6'b001001;

    let ldReq = Struct2 { id : getRqId, type_ : False, addr : rq_addr, value : unpack(0) };
    let stReq = Struct2 { id : setRqId, type_ : False, addr : rq_addr, value : rq_data };

    function Action addResp();
        action
            numResps <= numResps + 1;
            deadlockDetector <= 0;
        endaction
    endfunction

    for (Integer i = 0; i < valueOf(L1Num); i = i+1) begin
        rule request_load if (memInit && onTest && rq_type_seed[i]);
            mem.l1Ifc[i].mem_enq_rq(ldReq);
        endrule
    end
    for (Integer i = 0; i < valueOf(L1Num); i = i+1) begin
        rule request_store if (memInit && onTest && !rq_type_seed[i]);
            mem.l1Ifc[i].mem_enq_rq(stReq);
        endrule
    end
    for (Integer i = 0; i < valueOf(L1Num); i = i+1) begin
        rule response;
            let rs <- mem.l1Ifc[i].mem_deq_rs ();
            addResp();
        endrule
    end

    method Action start(CycleCnt _maxCycle) if (!onTest);
        maxCycle <= _maxCycle;
        onTest <= True;
        for (Integer i = 0; i < valueOf(L1Num); i = i+1) begin
            rq_type_rand[i].seed(fromInteger(valueOf(RqTypeSeed)));
        end
        rq_baddr_rand.seed(fromInteger(valueOf(RqBAddrSeed)));
    endmethod

    method Bool isEnd();
        return !onTest;
    endmethod

    method Bit#(32) getThroughput();
        return numResps;
    endmethod
endmodule
