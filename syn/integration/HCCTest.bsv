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

    method Action force_rq(Bool wr, Bit#(64) faddr, Vector#(8, Bit#(64)) val);
    method Bit#(64) getMark();
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

`ifdef RQ_VALUE_SEED
typedef `RQ_VALUE_SEED RqValueSeed;
`else
typedef 42 RqValueSeed;
`endif

`ifdef RQ_EX_SH_SEED
typedef `RQ_EX_SH_SEED RqExShSeed;
`else
typedef 2 RqExShSeed;
`endif

// Access ratio between read and write, used throughout all testers
typedef 2 LgRWRatio; // 1/4 (=1/2^2) accesses of writes

module mkCCTestRandom#(CC mem)(CCTest);
    Reg#(Bool) memInit <- mkReg(False);
    Reg#(Bool) onTest <- mkReg(False);
    Reg#(CycleCnt) maxCycle <- mkReg(0);
    Reg#(CycleCnt) curCycle <- mkReg(0);
    Vector#(L1Num, Reg#(Bit#(32))) numResps <- replicateM(mkReg(0));
    Reg#(Bit#(16)) deadlockDetector <- mkReg(0);

    Vector#(L1Num, LFSR#(Bit#(4))) rq_type_rand <- replicateM(mkLFSR_4);
    Vector#(L1Num, LFSR#(Bit#(16))) rq_baddr_rand <- replicateM(mkLFSR_16);
    LFSR#(Bit#(32)) rq_value_rand_high <- mkLFSR_32;
    LFSR#(Bit#(32)) rq_value_rand_low <- mkLFSR_32;

    Vector#(L1Num, Reg#(Bool)) rq_type <- replicateM(mkReg(False));
    Vector#(L1Num, Reg#(Bit#(64))) rq_addr <- replicateM(mkReg(0));
    Vector#(L1Num, Reg#(Bit#(64))) marks <- replicateM(mkReg(0));
    Reg#(CCValue) rq_value <- mkReg(replicate(0));
    Reg#(Bit#(3)) rq_value_idx <- mkReg(0);

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

    for (Integer i = 0; i < valueOf(L1Num); i = i+1) begin
        rule rq_type_upd (onTest);
            let t = rq_type_rand[i].value;
            rq_type_rand[i].next();
            Bit#(LgRWRatio) rz = 0;
            rq_type[i] <= (truncate(t) == rz ? True : False);
        endrule
    end
    for (Integer i = 0; i < valueOf(L1Num); i=i+1) begin
        rule rq_addr_upd;
            Bit#(BAddrSz) baddr = truncate(rq_baddr_rand[i].value);
            rq_baddr_rand[i].next();
            let addr = getAddr(baddr);
            rq_addr[i] <= addr;
        endrule
    end
    rule rq_value_upd;
        rq_value[rq_value_idx] <= {rq_value_rand_high.value, rq_value_rand_low.value};
        rq_value_rand_high.next();
        rq_value_rand_low.next();
        rq_value_idx <= rq_value_idx + 1;
    endrule

    let getRqId = 6'b000000;
    let setRqId = 6'b001000;
    let getRsId = 6'b000001;
    let setRsId = 6'b001001;

    function Struct2 ldReq(Integer i);
        return Struct2 { id : getRqId, type_ : False, addr : rq_addr[i], value : unpack(0) };
    endfunction
    function Struct2 stReq(Integer i);
        return Struct2 { id : setRqId, type_ : False, addr : rq_addr[i], value : rq_value };
    endfunction

    function Action addResp(Integer i);
        action
            numResps[i] <= numResps[i] + 1;
            if (i == 0) deadlockDetector <= 0;
        endaction
    endfunction

    for (Integer i = 0; i < valueOf(L1Num); i = i+1) begin
        rule request_load if (memInit && onTest && !rq_type[i]);
            mem.l1Ifc[i].mem_enq_rq(ldReq(i));
        endrule
    end
    for (Integer i = 0; i < valueOf(L1Num); i = i+1) begin
        rule request_store if (memInit && onTest && rq_type[i]);
            mem.l1Ifc[i].mem_enq_rq(stReq(i));
        endrule
    end
    for (Integer i = 0; i < valueOf(L1Num); i = i+1) begin
        rule response;
            let rs <- mem.l1Ifc[i].mem_deq_rs ();
            marks[i] <= marks[i]
            + rs.value[0] + rs.value[1] + rs.value[2] + rs.value[3]
            + rs.value[4] + rs.value[5] + rs.value[6] + rs.value[7];
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
        rq_value_rand_high.seed(fromInteger(valueOf(RqValueSeed)));
        rq_value_rand_low.seed(fromInteger(valueOf(RqValueSeed) + 1));
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

    method Action force_rq(Bool wr, Bit#(64) faddr, Vector#(8, Bit#(64)) val);
        Struct2 frq = Struct2 {id: (wr ? setRqId : getRqId),
                               type_: False,
                               addr: faddr,
                               value: val};
        mem.l1Ifc[0].mem_enq_rq(frq);
    endmethod

    method Bit#(64) getMark();
        Bit#(64) sum = 0;
        for (Integer i = 0; i < valueOf(L1Num); i = i+1) begin
            sum = sum + marks[i];
        end
        return sum;
    endmethod
endmodule

typedef TLog#(L1Num) LgL1Num;
typedef 9 LgL1DSz;

module mkCCTestIsolated#(CC mem)(CCTest);
    Reg#(Bool) memInit <- mkReg(False);
    Reg#(Bool) onTest <- mkReg(False);
    Reg#(CycleCnt) maxCycle <- mkReg(0);
    Reg#(CycleCnt) curCycle <- mkReg(0);
    Vector#(L1Num, Reg#(Bit#(32))) numResps <- replicateM(mkReg(0));
    Reg#(Bit#(16)) deadlockDetector <- mkReg(0);

    Vector#(L1Num, LFSR#(Bit#(4))) rq_type_rand <- replicateM(mkLFSR_4);
    Vector#(L1Num, LFSR#(Bit#(16))) rq_baddr_rand <- replicateM(mkLFSR_16);
    LFSR#(Bit#(32)) rq_value_rand_high <- mkLFSR_32;
    LFSR#(Bit#(32)) rq_value_rand_low <- mkLFSR_32;

    Vector#(L1Num, Reg#(Bool)) rq_type <- replicateM(mkReg(False));
    Vector#(L1Num, Reg#(Bit#(64))) rq_addr <- replicateM(mkReg(0));
    Reg#(CCValue) rq_value <- mkReg(replicate(0));
    Reg#(Bit#(3)) rq_value_idx <- mkReg(0);

    function Bit#(64) getAddr (Bit#(LgL1Num) idx, Bit#(LgL1DSz) l1Addr);
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

    for (Integer i = 0; i < valueOf(L1Num); i = i+1) begin
        rule rq_type_upd (onTest);
            let t = rq_type_rand[i].value;
            rq_type_rand[i].next();
            Bit#(LgRWRatio) rz = 0;
            rq_type[i] <= (truncate(t) == rz ? True : False);
        endrule
    end

    for (Integer i = 0; i < valueOf(L1Num); i=i+1) begin
        rule rq_addr_upd;
            Bit#(LgL1DSz) l1Addr = truncate(rq_baddr_rand[i].value);
            rq_baddr_rand[i].next();
            let addr = getAddr(fromInteger(i), l1Addr);
            rq_addr[i] <= addr;
        endrule
    end
    rule rq_value_upd;
        rq_value[rq_value_idx] <= {rq_value_rand_high.value, rq_value_rand_low.value};
        rq_value_rand_high.next();
        rq_value_rand_low.next();
        rq_value_idx <= rq_value_idx + 1;
    endrule

    let getRqId = 6'b000000;
    let setRqId = 6'b001000;
    let getRsId = 6'b000001;
    let setRsId = 6'b001001;

    function Struct2 ldReq(Integer i);
        return Struct2 { id : getRqId, type_ : False, addr : rq_addr[i], value : unpack(0) };
    endfunction
    function Struct2 stReq(Integer i);
        return Struct2 { id : setRqId, type_ : False, addr : rq_addr[i], value : rq_value };
    endfunction

    function Action addResp(Integer i);
        action
            numResps[i] <= numResps[i] + 1;
            if (i == 0) deadlockDetector <= 0;
        endaction
    endfunction

    for (Integer i = 0; i < valueOf(L1Num); i = i+1) begin
        rule request_load if (memInit && onTest && !rq_type[i]);
            mem.l1Ifc[i].mem_enq_rq(ldReq(i));
        endrule
    end
    for (Integer i = 0; i < valueOf(L1Num); i = i+1) begin
        rule request_store if (memInit && onTest && rq_type[i]);
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
        rq_value_rand_high.seed(fromInteger(valueOf(RqValueSeed)));
        rq_value_rand_low.seed(fromInteger(valueOf(RqValueSeed) + 1));
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

    method Action force_rq(Bool wr, Bit#(64) faddr, Vector#(8, Bit#(64)) val);
    endmethod
    method Bit#(64) getMark();
        return 0;
    endmethod
endmodule

// There are two additional parameters used in `mkCCTestShared`:
// - Size of shared lines (LgShRange)
// - Access ratio between exclusive and shared lines (LgExShRatio)
// NOTE:
// Exclusive: [0..0][0][L1Idx][----rand(LgL1DSz)----]
// Shared   : [0..0][1][0...0][0..0][rand(LgShRange)]
typedef TAdd#(LgL1Num, 1) ExShIdxSz;
typedef L1Num ShIdx;
typedef 4 LgShRange;
typedef 2 LgExShRatio; // 1/4 (=1/2^2) accesses of shared lines

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
    Reg#(CCValue) rq_value <- mkReg(replicate(0));

    function Bit#(64) getAddr (Bit#(ExShIdxSz) idx, Bit#(LgL1DSz) l1Addr);
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

    for (Integer i = 0; i < valueOf(L1Num); i = i+1) begin
        rule rq_type_upd (onTest);
            let t = rq_type_rand[i].value;
            rq_type_rand[i].next();
            Bit#(LgRWRatio) rz = 0;
            rq_type[i] <= (truncate(t) == rz ? True : False);
        endrule
    end

    for (Integer i = 0; i < valueOf(L1Num); i=i+1) begin
        rule rq_addr_upd;
            Bit#(LgL1DSz) l1Addr = truncate(rq_baddr_rand[i].value);
            rq_baddr_rand[i].next();
            if (rq_ex_sh[i]) begin
                Bit#(LgShRange) saddrTrunc = truncate(l1Addr);
                Bit#(LgL1DSz) saddr = zeroExtend(saddrTrunc);
                let shAddr = getAddr(fromInteger(valueOf(ShIdx)), saddr);
                rq_addr[i] <= shAddr;
            end
            else begin
                let addr = getAddr(fromInteger(i), l1Addr);
                rq_addr[i] <= addr;
            end
        endrule
    end
    for (Integer i = 0; i < valueOf(L1Num); i=i+1) begin
        rule rq_ex_sh_upd;
            let t = rq_ex_sh_rand[i].value;
            rq_ex_sh_rand[i].next();
            Bit#(LgExShRatio) rz = 0;
            rq_ex_sh[i] <= (truncate(t) == rz? True : False);
        endrule
    end

    rule rq_value_inc;
        rq_value <= update(rq_value, 0, rq_value[0] + 1);
    endrule

    let getRqId = 6'b000000;
    let setRqId = 6'b001000;
    let getRsId = 6'b000001;
    let setRsId = 6'b001001;

    function Struct2 ldReq(Integer i);
        return Struct2 { id : getRqId, type_ : False, addr : rq_addr[i], value : unpack(0) };
    endfunction
    function Struct2 stReq(Integer i);
        return Struct2 { id : setRqId, type_ : False, addr : rq_addr[i], value : rq_value };
    endfunction

    function Action addResp(Integer i);
        action
            numResps[i] <= numResps[i] + 1;
            if (i == 0) deadlockDetector <= 0;
        endaction
    endfunction

    for (Integer i = 0; i < valueOf(L1Num); i = i+1) begin
        rule request_load if (memInit && onTest && !rq_type[i]);
            mem.l1Ifc[i].mem_enq_rq(ldReq(i));
        endrule
    end
    for (Integer i = 0; i < valueOf(L1Num); i = i+1) begin
        rule request_store if (memInit && onTest && rq_type[i]);
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

    method Action force_rq(Bool wr, Bit#(64) faddr, Vector#(8, Bit#(64)) val);
    endmethod
    method Bit#(64) getMark();
        return 0;
    endmethod
endmodule
