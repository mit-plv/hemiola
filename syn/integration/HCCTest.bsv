import Vector::*;
import BuildVector::*;
import FIFO::*;
import FIFOF::*;
// import Randomizable::*;
import LFSR::*;

import HCC::*;
import HMemBank::*;

typedef 8 L1Num;
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
    Reg#(Bit#(64)) rq_data <- mkReg(0);

    function Bit#(64) getAddr (Bit#(BAddrSz) baddr);
        Bit#(64) addr = zeroExtend({baddr, 3'b000});
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
        rq_data <= rq_data + 1;
    endrule

    let getRqId = 6'b000000;
    let setRqId = 6'b001000;
    let getRsId = 6'b000001;
    let setRsId = 6'b001001;

    let ldReq = Struct2 { id : getRqId, type_ : False, addr : rq_addr, value : 0 };
    let stReq = Struct2 { id : setRqId, type_ : False, addr : rq_addr, value : rq_data };

    function Action addResp();
        action
            numResps <= numResps + 1;
            deadlockDetector <= 0;
        endaction
    endfunction

    rule request_load_0 if (memInit && onTest && rq_type_seed[0]);
        mem.mem_enq_rq_0(ldReq);
    endrule
    rule request_store_0 if (memInit && onTest && !rq_type_seed[0]);
        mem.mem_enq_rq_0(stReq);
    endrule
    rule response_0;
        let rs <- mem.mem_deq_rs_0 ();
        addResp();
    endrule

    rule request_load_1 if (memInit && onTest && rq_type_seed[1]);
        mem.mem_enq_rq_1(ldReq);
    endrule
    rule request_store_1 if (memInit && onTest && !rq_type_seed[1]);
        mem.mem_enq_rq_1(stReq);
    endrule
    rule response_1;
        let rs <- mem.mem_deq_rs_1 ();
        addResp();
    endrule

    rule request_load_2 if (memInit && onTest && rq_type_seed[2]);
        mem.mem_enq_rq_2(ldReq);
    endrule
    rule request_store_2 if (memInit && onTest && !rq_type_seed[2]);
        mem.mem_enq_rq_2(stReq);
    endrule
    rule response_2;
        let rs <- mem.mem_deq_rs_2 ();
        addResp();
    endrule

    rule request_load_3 if (memInit && onTest && rq_type_seed[3]);
        mem.mem_enq_rq_3(ldReq);
    endrule
    rule request_store_3 if (memInit && onTest && !rq_type_seed[3]);
        mem.mem_enq_rq_3(stReq);
    endrule
    rule response_3;
        let rs <- mem.mem_deq_rs_3 ();
        addResp();
    endrule

    rule request_load_4 if (memInit && onTest && rq_type_seed[4]);
        mem.mem_enq_rq_4(ldReq);
    endrule
    rule request_store_4 if (memInit && onTest && !rq_type_seed[4]);
        mem.mem_enq_rq_4(stReq);
    endrule
    rule response_4;
        let rs <- mem.mem_deq_rs_4 ();
        addResp();
    endrule

    rule request_load_5 if (memInit && onTest && rq_type_seed[5]);
        mem.mem_enq_rq_5(ldReq);
    endrule
    rule request_store_5 if (memInit && onTest && !rq_type_seed[5]);
        mem.mem_enq_rq_5(stReq);
    endrule
    rule response_5;
        let rs <- mem.mem_deq_rs_5 ();
        addResp();
    endrule

    rule request_load_6 if (memInit && onTest && rq_type_seed[6]);
        mem.mem_enq_rq_6(ldReq);
    endrule
    rule request_store_6 if (memInit && onTest && !rq_type_seed[6]);
        mem.mem_enq_rq_6(stReq);
    endrule
    rule response_6;
        let rs <- mem.mem_deq_rs_6 ();
        addResp();
    endrule

    rule request_load_7 if (memInit && onTest && rq_type_seed[7]);
        mem.mem_enq_rq_7(ldReq);
    endrule
    rule request_store_7 if (memInit && onTest && !rq_type_seed[7]);
        mem.mem_enq_rq_7(stReq);
    endrule
    rule response_7;
        let rs <- mem.mem_deq_rs_7 ();
        addResp();
    endrule

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
