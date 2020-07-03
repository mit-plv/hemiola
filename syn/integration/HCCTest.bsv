import Vector::*;
import BuildVector::*;
import FIFO::*;
import FIFOF::*;
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

`ifdef RQ_TYPE_SEED
typedef `RQ_TYPE_SEED RqTypeSeed;
`else
typedef 3 RqTypeSeed;
`endif

`ifdef RQ_BADDR_SEED
typedef `RQ_BADDR_SEED RqBAddrSeed;
`else
typedef 79 RqBAddrSeed;
`endif

`ifdef RQ_EX_SH_SEED
typedef `RQ_EX_SH_SEED RqExShSeed;
`else
typedef 2 RqExShSeed;
`endif

module mkCCTestRandom#(CC mem)(CCTest);
    Reg#(Bool) memInit <- mkReg(False);
    Reg#(Bool) onTest <- mkReg(False);
    Reg#(CycleCnt) maxCycle <- mkReg(0);
    Reg#(CycleCnt) curCycle <- mkReg(0);
    Vector#(L1Num, Reg#(Bit#(32))) numResps <- replicateM(mkReg(0));
    Reg#(Bit#(16)) deadlockDetector <- mkReg(0);

    Vector#(L1Num, LFSR#(Bit#(4))) rq_type_rand <- replicateM(mkLFSR_4);
    Vector#(L1Num, LFSR#(Bit#(16))) rq_baddr_rand <- replicateM(mkLFSR_16);
    Vector#(L1Num, Reg#(Bool)) rq_type <- replicateM(mkReg(False));
    Vector#(L1Num, Reg#(Bit#(64))) rq_addr <- replicateM(mkReg(0));
    Vector#(L1Num, Reg#(Bit#(64))) recentLines <- replicateM(mkReg(0));
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

    rule rq_type_upd (onTest);
        for (Integer i = 0; i < valueOf(L1Num); i = i+1) begin
            let t = rq_type_rand[i].value;
            rq_type_rand[i].next();
            rq_type[i] <= (t[0] == 1 ? True : False);
        end
    endrule
    for (Integer i = 0; i < valueOf(L1IdxSz); i=i+1) begin
        rule rq_addr_upd;
            Bit#(BAddrSz) baddr = truncate(rq_baddr_rand[i].value);
            rq_baddr_rand[i].next();
            let addr = getAddr(baddr);
            rq_addr[i] <= addr;
        endrule
    end
    rule rq_data_inc;
        rq_data <= update(rq_data, 0, rq_data[0] + 1);
    endrule

    let getRqId = 6'b000000;
    let setRqId = 6'b001000;
    let getRsId = 6'b000001;
    let setRsId = 6'b001001;

    function Struct2 ldReq(Integer i);
        return Struct2 { id : getRqId, type_ : False, addr : rq_addr[i], value : unpack(0) };
    endfunction
    function Struct2 stReq(Integer i);
        return Struct2 { id : setRqId, type_ : False, addr : rq_addr[i], value : rq_data };
    endfunction

    function Action addResp(Integer i);
        action
            numResps[i] <= numResps[i] + 1;
            if (i == 0) deadlockDetector <= 0;
        endaction
    endfunction

    for (Integer i = 0; i < valueOf(L1Num); i = i+1) begin
        rule request_load if (memInit && onTest && rq_type[i]);
            mem.l1Ifc[i].mem_enq_rq(ldReq(i));
        endrule
    end
    for (Integer i = 0; i < valueOf(L1Num); i = i+1) begin
        rule request_store if (memInit && onTest && !rq_type[i]);
            mem.l1Ifc[i].mem_enq_rq(stReq(i));
        endrule
    end
    for (Integer i = 0; i < valueOf(L1Num); i = i+1) begin
        rule response;
            let rs <- mem.l1Ifc[i].mem_deq_rs ();
            recentLines[i] <= rs.value[0];
            addResp(i);
        endrule
    end

    method Action start(CycleCnt _maxCycle) if (!onTest);
        maxCycle <= _maxCycle;
        onTest <= True;
        for (Integer i = 0; i < valueOf(L1Num); i = i+1) begin
            rq_type_rand[i].seed(fromInteger(valueOf(RqTypeSeed) + i));
            rq_baddr_rand[i].seed(fromInteger(valueOf(RqBAddrSeed) + i));
        end
    endmethod

    method Bool isEnd();
        return !onTest;
    endmethod

    method Bit#(32) getThroughput();
        Bit#(32) sum = 0;
        for (Integer i = 0; i < valueOf(L1Num); i = i+1) begin
            sum = sum + numResps[i];
        end
        return sum;
    endmethod
endmodule

module mkCCTestRandomSame#(CC mem)(CCTest);
    Reg#(Bool) memInit <- mkReg(False);
    Reg#(Bool) onTest <- mkReg(False);
    Reg#(CycleCnt) maxCycle <- mkReg(0);
    Reg#(CycleCnt) curCycle <- mkReg(0);
    Vector#(L1Num, Reg#(Bit#(32))) numResps <- replicateM(mkReg(0));
    Reg#(Bit#(16)) deadlockDetector <- mkReg(0);

    Vector#(L1Num, LFSR#(Bit#(4))) rq_type_rand <- replicateM(mkLFSR_4);
    LFSR#(Bit#(16)) rq_baddr_rand <- mkLFSR_16;
    Vector#(L1Num, Reg#(Bool)) rq_type <- replicateM(mkReg(False));
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

    rule rq_type_upd (onTest);
        for (Integer i = 0; i < valueOf(L1Num); i = i+1) begin
            let t = rq_type_rand[i].value;
            rq_type_rand[i].next();
            rq_type[i] <= (t[0] == 1 ? True : False);
        end
    endrule
    rule rq_addr_upd;
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

    function Action addResp(Integer i);
        action
            numResps[i] <= numResps[i] + 1;
            if (i == 0) deadlockDetector <= 0;
        endaction
    endfunction

    for (Integer i = 0; i < valueOf(L1Num); i = i+1) begin
        rule request_load if (memInit && onTest && rq_type[i]);
            mem.l1Ifc[i].mem_enq_rq(ldReq);
        endrule
    end
    for (Integer i = 0; i < valueOf(L1Num); i = i+1) begin
        rule request_store if (memInit && onTest && !rq_type[i]);
            mem.l1Ifc[i].mem_enq_rq(stReq);
        endrule
    end
    for (Integer i = 0; i < valueOf(L1Num); i = i+1) begin
        rule response;
            let rs <- mem.l1Ifc[i].mem_deq_rs ();
            addResp(i);
        endrule
    end

    method Action start(CycleCnt _maxCycle) if (!onTest);
        maxCycle <= _maxCycle;
        onTest <= True;
        for (Integer i = 0; i < valueOf(L1Num); i = i+1) begin
            rq_type_rand[i].seed(fromInteger(valueOf(RqTypeSeed)));
        end
        // Since all requests to the L1 caches are using the same sequence of
        // addresses this test case is random but quite heavy in requiring lots
        // of invalidation cases.
        rq_baddr_rand.seed(fromInteger(valueOf(RqBAddrSeed)));
    endmethod

    method Bool isEnd();
        return !onTest;
    endmethod

    method Bit#(32) getThroughput();
        Bit#(32) sum = 0;
        for (Integer i = 0; i < valueOf(L1Num); i = i+1) begin
            sum = sum + numResps[i];
        end
        return sum;
    endmethod
endmodule

typedef TLog#(L1Num) L1IdxSz;
typedef 9 L1Range;

module mkCCBenchLocality#(CC mem)(CCTest);
    Reg#(Bool) memInit <- mkReg(False);
    Reg#(Bool) onTest <- mkReg(False);
    Reg#(CycleCnt) maxCycle <- mkReg(0);
    Reg#(CycleCnt) curCycle <- mkReg(0);
    Vector#(L1Num, Reg#(Bit#(32))) numResps <- replicateM(mkReg(0));
    Reg#(Bit#(16)) deadlockDetector <- mkReg(0);

    Vector#(L1Num, LFSR#(Bit#(4))) rq_type_rand <- replicateM(mkLFSR_4);
    Vector#(L1Num, LFSR#(Bit#(16))) rq_baddr_rand <- replicateM(mkLFSR_16);
    Vector#(L1Num, Reg#(Bool)) rq_type <- replicateM(mkReg(False));
    Vector#(L1Num, Reg#(Bit#(64))) rq_addr <- replicateM(mkReg(0));
    Reg#(CCValue) rq_data <- mkReg(replicate(0));

    function Bit#(64) getAddr (Bit#(L1IdxSz) idx, Bit#(L1Range) l1Addr);
        Bit#(AddrOffset) pad = 0;
        Bit#(64) addr = zeroExtend({idx, l1Addr, pad});
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

    rule rq_type_upd (onTest);
        for (Integer i = 0; i < valueOf(L1Num); i = i+1) begin
            let t = rq_type_rand[i].value;
            rq_type_rand[i].next();
            rq_type[i] <= (t[0] == 1 ? True : False);
        end
    endrule

    for (Integer i = 0; i < valueOf(L1IdxSz); i=i+1) begin
        rule rq_addr_upd;
            Bit#(L1Range) l1Addr = truncate(rq_baddr_rand[i].value);
            rq_baddr_rand[i].next();
            let addr = getAddr(fromInteger(i), l1Addr);
            rq_addr[i] <= addr;
        endrule
    end
    rule rq_data_inc;
        rq_data <= update(rq_data, 0, rq_data[0] + 1);
    endrule

    let getRqId = 6'b000000;
    let setRqId = 6'b001000;
    let getRsId = 6'b000001;
    let setRsId = 6'b001001;

    function Struct2 ldReq(Integer i);
        return Struct2 { id : getRqId, type_ : False, addr : rq_addr[i], value : unpack(0) };
    endfunction
    function Struct2 stReq(Integer i);
        return Struct2 { id : setRqId, type_ : False, addr : rq_addr[i], value : rq_data };
    endfunction

    function Action addResp(Integer i);
        action
            numResps[i] <= numResps[i] + 1;
            if (i == 0) deadlockDetector <= 0;
        endaction
    endfunction

    for (Integer i = 0; i < valueOf(L1Num); i = i+1) begin
        rule request_load if (memInit && onTest && rq_type[i]);
            mem.l1Ifc[i].mem_enq_rq(ldReq(i));
        endrule
    end
    for (Integer i = 0; i < valueOf(L1Num); i = i+1) begin
        rule request_store if (memInit && onTest && !rq_type[i]);
            mem.l1Ifc[i].mem_enq_rq(stReq(i));
        endrule
    end
    for (Integer i = 0; i < valueOf(L1Num); i = i+1) begin
        rule response;
            let rs <- mem.l1Ifc[i].mem_deq_rs ();
            addResp(i);
        endrule
    end

    method Action start(CycleCnt _maxCycle) if (!onTest);
        maxCycle <= _maxCycle;
        onTest <= True;
        for (Integer i = 0; i < valueOf(L1Num); i = i+1) begin
            rq_type_rand[i].seed(fromInteger(valueOf(RqTypeSeed) + i));
            rq_baddr_rand[i].seed(fromInteger(valueOf(RqBAddrSeed) + i));
        end
    endmethod

    method Bool isEnd();
        return !onTest;
    endmethod

    method Bit#(32) getThroughput();
        Bit#(32) sum = 0;
        for (Integer i = 0; i < valueOf(L1Num); i = i+1) begin
            sum = sum + numResps[i];
        end
        return sum;
    endmethod
endmodule

// Force the address ranges for exclusive and shared parts.
// - Exclusive: [0..0][0][L1Idx][----rand(L1Range)----]
// - Shared   : [0..0][1][0...0][0..0][rand(LgShRange)]
typedef TAdd#(L1IdxSz, 1) ExShIdxSz;
typedef L1Num ShIdx;
typedef 4 LgShRange;

module mkCCTestShared#(CC mem)(CCTest);
    Reg#(Bool) memInit <- mkReg(False);
    Reg#(Bool) onTest <- mkReg(False);
    Reg#(CycleCnt) maxCycle <- mkReg(0);
    Reg#(CycleCnt) curCycle <- mkReg(0);
    Vector#(L1Num, Reg#(Bit#(32))) numResps <- replicateM(mkReg(0));
    Reg#(Bit#(16)) deadlockDetector <- mkReg(0);

    Vector#(L1Num, LFSR#(Bit#(4))) rq_type_rand <- replicateM(mkLFSR_4);
    Vector#(L1Num, LFSR#(Bit#(16))) rq_baddr_rand <- replicateM(mkLFSR_16);
    Vector#(L1Num, LFSR#(Bit#(4))) rq_ex_sh_rand <- replicateM(mkLFSR_4);

    Vector#(L1Num, Reg#(Bool)) rq_type <- replicateM(mkReg(False));
    Vector#(L1Num, Reg#(Bit#(64))) rq_addr <- replicateM(mkReg(0));
    Vector#(L1Num, Reg#(Bool)) rq_ex_sh <- replicateM(mkReg(False));
    Reg#(CCValue) rq_data <- mkReg(replicate(0));

    function Bit#(64) getAddr (Bit#(ExShIdxSz) idx, Bit#(L1Range) l1Addr);
        Bit#(AddrOffset) pad = 0;
        Bit#(64) addr = zeroExtend({idx, l1Addr, pad});
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

    rule rq_type_upd (onTest);
        for (Integer i = 0; i < valueOf(L1Num); i = i+1) begin
            let t = rq_type_rand[i].value;
            rq_type_rand[i].next();
            rq_type[i] <= (t[0] == 1 ? True : False);
        end
    endrule

    for (Integer i = 0; i < valueOf(L1IdxSz); i=i+1) begin
        rule rq_addr_upd;
            Bit#(L1Range) l1Addr = truncate(rq_baddr_rand[i].value);
            rq_baddr_rand[i].next();
            if (rq_ex_sh[i]) begin
                // TODO: use [LgShRange] instead of [3:0]
                Bit#(L1Range) saddr = zeroExtend(l1Addr[3:0]);
                let shAddr = getAddr(fromInteger(valueOf(ShIdx)), saddr);
                rq_addr[i] <= shAddr;
            end
            else begin
                let addr = getAddr(fromInteger(i), l1Addr);
                rq_addr[i] <= addr;
            end
        endrule
    end
    for (Integer i = 0; i < valueOf(L1IdxSz); i=i+1) begin
        rule rq_ex_sh_upd;
            let t = rq_ex_sh_rand[i].value;
            rq_ex_sh_rand[i].next();
            rq_ex_sh[i] <= (t[0] == 1 ? True : False); // 1/2 for sh
        endrule
    end

    rule rq_data_inc;
        rq_data <= update(rq_data, 0, rq_data[0] + 1);
    endrule

    let getRqId = 6'b000000;
    let setRqId = 6'b001000;
    let getRsId = 6'b000001;
    let setRsId = 6'b001001;

    function Struct2 ldReq(Integer i);
        return Struct2 { id : getRqId, type_ : False, addr : rq_addr[i], value : unpack(0) };
    endfunction
    function Struct2 stReq(Integer i);
        return Struct2 { id : setRqId, type_ : False, addr : rq_addr[i], value : rq_data };
    endfunction

    function Action addResp(Integer i);
        action
            numResps[i] <= numResps[i] + 1;
            if (i == 0) deadlockDetector <= 0;
        endaction
    endfunction

    for (Integer i = 0; i < valueOf(L1Num); i = i+1) begin
        rule request_load if (memInit && onTest && rq_type[i]);
            mem.l1Ifc[i].mem_enq_rq(ldReq(i));
        endrule
    end
    for (Integer i = 0; i < valueOf(L1Num); i = i+1) begin
        rule request_store if (memInit && onTest && !rq_type[i]);
            mem.l1Ifc[i].mem_enq_rq(stReq(i));
        endrule
    end
    for (Integer i = 0; i < valueOf(L1Num); i = i+1) begin
        rule response;
            let rs <- mem.l1Ifc[i].mem_deq_rs ();
            addResp(i);
        endrule
    end

    method Action start(CycleCnt _maxCycle) if (!onTest);
        maxCycle <= _maxCycle;
        onTest <= True;
        for (Integer i = 0; i < valueOf(L1Num); i = i+1) begin
            rq_type_rand[i].seed(fromInteger(valueOf(RqTypeSeed) + i));
            rq_baddr_rand[i].seed(fromInteger(valueOf(RqBAddrSeed) + i));
            rq_ex_sh_rand[i].seed(fromInteger(valueOf(RqExShSeed) + i));
        end
    endmethod

    method Bool isEnd();
        return !onTest;
    endmethod

    method Bit#(32) getThroughput();
        Bit#(32) sum = 0;
        for (Integer i = 0; i < valueOf(L1Num); i = i+1) begin
            sum = sum + numResps[i];
        end
        return sum;
    endmethod
endmodule
