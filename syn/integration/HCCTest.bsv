import Vector::*;
import RegFile::*;
import BuildVector::*;
import FIFO::*;
import FIFOF::*;
import LFSR::*;

import HCC::*;
import HCCIfc::*;
import HCCWrapper::*;
import HCCTypes::*;
import HMemBank::*;

typedef Bit#(64) CycleCnt;
interface CCTest;
    method Action start(CycleCnt maxCycle);
    method Bool isEnd();
    method Bit#(64) getThroughput();
    method Bit#(64) getMark();
endinterface

typedef 20000 DeadlockDetectCnt;

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

typedef 11 ChkAddrSz;

interface StoreBuffer;
    method Action set(Bit#(ChkAddrSz) caddr, CCValue value);
    method ActionValue#(Maybe#(CCValue)) get(Bit#(ChkAddrSz) caddr);
endinterface

typedef struct { Bool sb_valid;
                Bit#(ChkAddrSz) sb_caddr;
                CCValue sb_value; } SBSlot deriving(Eq, Bits);
typedef 8 SBSize;
module mkStoreBuffer(StoreBuffer);
    Vector#(SBSize, Reg#(SBSlot)) slots <- replicateM(mkReg(unpack(0)));

    method Action set(Bit#(ChkAddrSz) caddr, CCValue value);
        Bool alreadySet = False;
        for (Integer i = 0; i < valueOf(SBSize); i = i+1) begin
            alreadySet = alreadySet || (slots[i].sb_valid && slots[i].sb_caddr == caddr);
        end
        when (!alreadySet, noAction);
        Bool hasSlot = False;
        for (Integer i = 0; i < valueOf(SBSize); i = i+1) begin
            hasSlot = hasSlot || !slots[i].sb_valid;
        end
        when (hasSlot, noAction);
        Bool added = False;
        for (Integer i = 0; i < valueOf(SBSize); i = i+1) begin
            if (!added && !slots[i].sb_valid) begin
                slots[i] <= SBSlot { sb_valid: True, sb_caddr: caddr, sb_value: value };
                added = True;
            end
        end
    endmethod

    method ActionValue#(Maybe#(CCValue)) get(Bit#(ChkAddrSz) caddr);
        Maybe#(CCValue) ret = Invalid;
        for (Integer i = 0; i < valueOf(SBSize); i = i+1) begin
            if (slots[i].sb_valid && slots[i].sb_caddr == caddr) begin
                ret = Valid (slots[i].sb_value);
                slots[i] <= SBSlot { sb_valid: False, sb_caddr: ?, sb_value: ? };
            end
        end
        return ret;
    endmethod
endmodule

typedef 9 IndexSz;
typedef TAdd#(AddrOffset, IndexSz) IEAddrOffset;
module mkCCTestCheckIdxEquiv#(CC mem)(CCTest);
    Reg#(Bool) memInit <- mkReg(False);
    Reg#(Bit#(LLCacheSz)) memInitCount <- mkReg(0);
    Reg#(Bool) onTest <- mkReg(False);
    Reg#(CycleCnt) maxCycle <- mkReg(0);
    Reg#(CycleCnt) curCycle <- mkReg(0);
    Vector#(L1Num, Reg#(Bit#(64))) numResps <- replicateM(mkReg(0));

    Vector#(L1Num, StoreBuffer) sb <- replicateM(mkStoreBuffer);
    RegFile#(Bit#(ChkAddrSz), CCValue) refMem <- mkRegFileFull;

    Vector#(L1Num, LFSR#(Bit#(4))) rq_type_rand <- replicateM(mkLFSR_4);
    Vector#(L1Num, LFSR#(Bit#(16))) rq_baddr_rand <- replicateM(mkLFSR_16);
    LFSR#(Bit#(32)) rq_value_rand_high <- mkLFSR_32;
    LFSR#(Bit#(32)) rq_value_rand_low <- mkLFSR_32;

    Vector#(L1Num, Reg#(Bool)) rq_type <- replicateM(mkReg(False));
    Vector#(L1Num, Reg#(Bit#(64))) rq_addr <- replicateM(mkReg(0));
    Reg#(CCValue) rq_value <- mkReg(replicate(0));
    Reg#(Bit#(3)) rq_value_idx <- mkReg(0);

    Reg#(Bool) check_succeed <- mkReg(True);

    function Bit#(64) getAddr (Bit#(ChkAddrSz) baddr);
        Bit#(IEAddrOffset) pad = 0;
        Bit#(64) addr = zeroExtend({baddr >> valueOf(IndexSz), pad});
        return addr;
    endfunction

    function Bit#(ChkAddrSz) getChkAddr (Bit#(64) addr);
        return truncate(addr >> valueOf(AddrOffset));
    endfunction

    rule mem_init_count (!memInit);
        memInitCount <= memInitCount + 1;
        memInit <= (memInitCount == maxBound);
    endrule

    rule inc_cycle (memInit && onTest);
        curCycle <= curCycle + 1;
        if (curCycle == maxCycle) onTest <= False;
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
            Bit#(ChkAddrSz) baddr = truncate(rq_baddr_rand[i].value);
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

    function CCMsg ldReq(Integer i);
        return CCMsg { id : getRqId, type_ : False, addr : rq_addr[i], value : unpack(0) };
    endfunction
    function CCMsg stReq(Integer i);
        return CCMsg { id : setRqId, type_ : False, addr : rq_addr[i], value : rq_value };
    endfunction

    for (Integer i = 0; i < valueOf(L1Num); i = i+1) begin
        rule request_load if (memInit && onTest && !rq_type[i]);
            // $display ("-- %d: load requested (%x)", i, rq_addr[i]);
            mem.l1Ifc[i].mem_enq_rq(ldReq(i));
        endrule
    end
    for (Integer i = 0; i < valueOf(L1Num); i = i+1) begin
        rule request_store if (memInit && onTest && rq_type[i]);
            // $display ("-- %d: store requested (%x : %x)", i, rq_addr[i], rq_value);
            mem.l1Ifc[i].mem_enq_rq(stReq(i));
            sb[i].set(getChkAddr(rq_addr[i]), rq_value);
        endrule
    end

    for (Integer i = 0; i < valueOf(L1Num); i = i+1) begin
        rule response;
            numResps[i] <= numResps[i] + 1;
            let rs <- mem.l1Ifc[i].mem_deq_rs ();
            if (rs.id == 6'b000001) begin
                let caddr = getChkAddr(rs.addr);
                let rvalue = refMem.sub(caddr);
                if (rvalue != rs.value) begin
                    $display ("-- Verification failed at %t: value mismatch", $time);
                    $display ("---- core index: %d", i);
                    $display ("---- address: %x", rs.addr);
                    $display ("---- response value: %x", rs.value);
                    $display ("---- reference value: %x", rvalue);
                    check_succeed <= False;
                end
            end
            else if (rs.id == 6'b001001) begin
                let caddr = getChkAddr(rs.addr);
                let sval <- sb[i].get(caddr);
                if (sval matches tagged Valid .val) refMem.upd(caddr, val);
                else begin
                    $display ("Verification failed (%d): cannot find a previous store: %x",
                       i, caddr);
                    check_succeed <= False;
                end
            end
            else begin
                $display (stderr, "Verification failed (%d): a wrong response ID: %b", i, rs.id);
                check_succeed <= False;
            end
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

    method Bit#(64) getThroughput();
        Bit#(64) sum = 0;
        for (Integer i = 0; i < valueOf(L1Num); i = i+1) begin
            sum = sum + numResps[i];
        end
        return sum;
    endmethod
    method Bit#(64) getMark();
        return (check_succeed ? 1 : 0);
    endmethod
endmodule

module mkCCTestCheck#(CC mem)(CCTest);
    Reg#(Bool) memInit <- mkReg(False);
    Reg#(Bit#(LLCacheSz)) memInitCount <- mkReg(0);
    Reg#(Bool) onTest <- mkReg(False);
    Reg#(CycleCnt) maxCycle <- mkReg(0);
    Reg#(CycleCnt) curCycle <- mkReg(0);
    Vector#(L1Num, Reg#(Bit#(64))) numResps <- replicateM(mkReg(0));

    Vector#(L1Num, StoreBuffer) sb <- replicateM(mkStoreBuffer);
    RegFile#(Bit#(ChkAddrSz), CCValue) refMem <- mkRegFileFull;

    Vector#(L1Num, LFSR#(Bit#(4))) rq_type_rand <- replicateM(mkLFSR_4);
    Vector#(L1Num, LFSR#(Bit#(16))) rq_baddr_rand <- replicateM(mkLFSR_16);
    LFSR#(Bit#(32)) rq_value_rand_high <- mkLFSR_32;
    LFSR#(Bit#(32)) rq_value_rand_low <- mkLFSR_32;

    Vector#(L1Num, Reg#(Bool)) rq_type <- replicateM(mkReg(False));
    Vector#(L1Num, Reg#(Bit#(64))) rq_addr <- replicateM(mkReg(0));
    Reg#(CCValue) rq_value <- mkReg(replicate(0));
    Reg#(Bit#(3)) rq_value_idx <- mkReg(0);

    Reg#(Bool) check_succeed <- mkReg(True);

    function Bit#(64) getAddr (Bit#(ChkAddrSz) baddr);
        Bit#(AddrOffset) pad = 0;
        Bit#(64) addr = zeroExtend({baddr, pad});
        return addr;
    endfunction

    function Bit#(ChkAddrSz) getChkAddr (Bit#(64) addr);
        return truncate(addr >> valueOf(AddrOffset));
    endfunction

    rule mem_init_count (!memInit);
        memInitCount <= memInitCount + 1;
        memInit <= (memInitCount == maxBound);
    endrule

    rule inc_cycle (memInit && onTest);
        curCycle <= curCycle + 1;
        if (curCycle == maxCycle) onTest <= False;
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
            Bit#(ChkAddrSz) baddr = truncate(rq_baddr_rand[i].value);
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

    function CCMsg ldReq(Integer i);
        return CCMsg { id : getRqId, type_ : False, addr : rq_addr[i], value : unpack(0) };
    endfunction
    function CCMsg stReq(Integer i);
        return CCMsg { id : setRqId, type_ : False, addr : rq_addr[i], value : rq_value };
    endfunction

    for (Integer i = 0; i < valueOf(L1Num); i = i+1) begin
        rule request_load if (memInit && onTest && !rq_type[i]);
            // $display ("-- %d: load requested (%x)", i, rq_addr[i]);
            mem.l1Ifc[i].mem_enq_rq(ldReq(i));
        endrule
    end
    for (Integer i = 0; i < valueOf(L1Num); i = i+1) begin
        rule request_store if (memInit && onTest && rq_type[i]);
            // $display ("-- %d: store requested (%x : %x)", i, rq_addr[i], rq_value);
            mem.l1Ifc[i].mem_enq_rq(stReq(i));
            sb[i].set(getChkAddr(rq_addr[i]), rq_value);
        endrule
    end

    for (Integer i = 0; i < valueOf(L1Num); i = i+1) begin
        rule response;
            numResps[i] <= numResps[i] + 1;
            let rs <- mem.l1Ifc[i].mem_deq_rs ();
            if (rs.id == 6'b000001) begin
                let caddr = getChkAddr(rs.addr);
                let rvalue = refMem.sub(caddr);
                if (rvalue != rs.value) begin
                    $display ("-- Verification failed at %t: value mismatch", $time);
                    $display ("---- core index: %d", i);
                    $display ("---- address: %x", rs.addr);
                    $display ("---- response value: %x", rs.value);
                    $display ("---- reference value: %x", rvalue);
                    check_succeed <= False;
                end
            end
            else if (rs.id == 6'b001001) begin
                let caddr = getChkAddr(rs.addr);
                let sval <- sb[i].get(caddr);
                if (sval matches tagged Valid .val) refMem.upd(caddr, val);
                else begin
                    $display ("Verification failed (%d): cannot find a previous store: %x",
                       i, caddr);
                    check_succeed <= False;
                end
            end
            else begin
                $display (stderr, "Verification failed (%d): a wrong response ID: %b", i, rs.id);
                check_succeed <= False;
            end
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

    method Bit#(64) getThroughput();
        Bit#(64) sum = 0;
        for (Integer i = 0; i < valueOf(L1Num); i = i+1) begin
            sum = sum + numResps[i];
        end
        return sum;
    endmethod
    method Bit#(64) getMark();
        return (check_succeed ? 1 : 0);
    endmethod
endmodule

typedef 11 RandAddrSz;
// Access ratio between read and write, used throughout all testers
typedef 2 LgRWRatio; // 1/4 (=1/2^2) accesses of writes

module mkCCTestRandom#(CC mem)(CCTest);
    Reg#(Bool) memInit <- mkReg(False);
    Reg#(Bit#(LLCacheSz)) memInitCount <- mkReg(0);
    Reg#(Bool) onTest <- mkReg(False);
    Reg#(CycleCnt) maxCycle <- mkReg(0);
    Reg#(CycleCnt) curCycle <- mkReg(0);
    Vector#(L1Num, Reg#(Bit#(64))) numResps <- replicateM(mkReg(0));
    Reg#(Bit#(16)) deadlockDetector <- mkReg(0);

    Vector#(L1Num, LFSR#(Bit#(4))) rq_type_rand <- replicateM(mkLFSR_4);
    Vector#(L1Num, LFSR#(Bit#(16))) rq_baddr_rand <- replicateM(mkLFSR_16);
    LFSR#(Bit#(32)) rq_value_rand_high <- mkLFSR_32;
    LFSR#(Bit#(32)) rq_value_rand_low <- mkLFSR_32;

    Vector#(L1Num, Reg#(Bool)) rq_type <- replicateM(mkReg(False));
    Vector#(L1Num, Reg#(Bit#(64))) rq_addr <- replicateM(mkReg(0));
    Reg#(CCValue) rq_value <- mkReg(replicate(0));
    Reg#(Bit#(3)) rq_value_idx <- mkReg(0);

    Vector#(L1Num, Reg#(Bit#(64))) marks <- replicateM(mkReg(0));

    function Bit#(64) getAddr (Bit#(RandAddrSz) baddr);
        Bit#(AddrOffset) pad = 0;
        Bit#(64) addr = zeroExtend({baddr, pad});
        return addr;
    endfunction

    rule mem_init_count (!memInit);
        memInitCount <= memInitCount + 1;
        memInit <= (memInitCount == maxBound);
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
            Bit#(RandAddrSz) baddr = truncate(rq_baddr_rand[i].value);
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

    function CCMsg ldReq(Integer i);
        return CCMsg { id : getRqId, type_ : False, addr : rq_addr[i], value : unpack(0) };
    endfunction
    function CCMsg stReq(Integer i);
        return CCMsg { id : setRqId, type_ : False, addr : rq_addr[i], value : rq_value };
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
            marks[i] <= marks[i] + rs.value[0] + rs.value[1] + rs.value[2] + rs.value[3];
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

    method Bit#(64) getThroughput();
        Bit#(64) sum = 0;
        for (Integer i = 0; i < valueOf(L1Num); i = i+1) begin
            sum = sum + numResps[i];
        end
        return sum;
    endmethod
    method Bit#(64) getMark();
        Bit#(64) ret = 0;
        for (Integer i = 0; i < valueOf(L1Num); i = i+1) begin
            ret = ret + marks[i];
        end
        return ret;
    endmethod
endmodule

typedef TLog#(L1Num) LgL1Num;
typedef 10 LgL1DSz;

module mkCCTestIsolated#(CC mem)(CCTest);
    Reg#(Bool) memInit <- mkReg(False);
    Reg#(Bit#(LLCacheSz)) memInitCount <- mkReg(0);
    Reg#(Bool) onTest <- mkReg(False);
    Reg#(CycleCnt) maxCycle <- mkReg(0);
    Reg#(CycleCnt) curCycle <- mkReg(0);
    Vector#(L1Num, Reg#(Bit#(64))) numResps <- replicateM(mkReg(0));
    Reg#(Bit#(16)) deadlockDetector <- mkReg(0);

    Vector#(L1Num, LFSR#(Bit#(4))) rq_type_rand <- replicateM(mkLFSR_4);
    Vector#(L1Num, LFSR#(Bit#(16))) rq_baddr_rand <- replicateM(mkLFSR_16);
    LFSR#(Bit#(32)) rq_value_rand_high <- mkLFSR_32;
    LFSR#(Bit#(32)) rq_value_rand_low <- mkLFSR_32;

    Vector#(L1Num, Reg#(Bool)) rq_type <- replicateM(mkReg(False));
    Vector#(L1Num, Reg#(Bit#(64))) rq_addr <- replicateM(mkReg(0));
    Reg#(CCValue) rq_value <- mkReg(replicate(0));
    Reg#(Bit#(3)) rq_value_idx <- mkReg(0);

    Vector#(L1Num, Reg#(Bit#(64))) marks <- replicateM(mkReg(0));

    function Bit#(64) getAddr (Bit#(LgL1Num) idx, Bit#(LgL1DSz) l1Addr);
        Bit#(AddrOffset) pad = 0;
        Bit#(64) addr = zeroExtend({idx, l1Addr, pad});
        return addr;
    endfunction

    rule mem_init_count (!memInit);
        memInitCount <= memInitCount + 1;
        memInit <= (memInitCount == maxBound);
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

    function CCMsg ldReq(Integer i);
        return CCMsg { id : getRqId, type_ : False, addr : rq_addr[i], value : unpack(0) };
    endfunction
    function CCMsg stReq(Integer i);
        return CCMsg { id : setRqId, type_ : False, addr : rq_addr[i], value : rq_value };
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
            marks[i] <= marks[i] + rs.value[0] + rs.value[1] + rs.value[2] + rs.value[3];
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

    method Bit#(64) getThroughput();
        Bit#(64) sum = 0;
        for (Integer i = 0; i < valueOf(L1Num); i = i+1) begin
            sum = sum + numResps[i];
        end
        return sum;
    endmethod
    method Bit#(64) getMark();
        Bit#(64) ret = 0;
        for (Integer i = 0; i < valueOf(L1Num); i = i+1) begin
            ret = ret + marks[i];
        end
        return ret;
    endmethod
endmodule

// NOTE:
// Exclusive: [0..0][0][L1Idx][----rand(LgL1DSz)----]
// Shared   : [0..0][--ShIdx-][0..0][rand(LgShRange)]
typedef TAdd#(LgL1Num, 1) ExShIdxSz; // FIXED
typedef L1Num ShIdx; // FIXED

// There are two additional parameters used in `mkCCTestShared`:
// - LgShRange: the size of shared lines.
// - LgExShRatio: access ratio between exclusive and shared lines.
typedef 5 LgShRange;
typedef 1 LgExShRatio;
typedef 32 NumTlCycles;

module mkCCTestShared#(CC mem)(CCTest);
    Reg#(Bool) memInit <- mkReg(False);
    Reg#(Bit#(LLCacheSz)) memInitCount <- mkReg(0);
    Reg#(Bool) onTest <- mkReg(False);
    Reg#(CycleCnt) maxCycle <- mkReg(0);
    Reg#(CycleCnt) curCycle <- mkReg(0);
    Vector#(L1Num, Reg#(Bit#(64))) numResps <- replicateM(mkReg(0));
    Reg#(Bit#(16)) deadlockDetector <- mkReg(0);

    Vector#(L1Num, LFSR#(Bit#(4))) rq_type_rand <- replicateM(mkLFSR_4);
    Vector#(L1Num, LFSR#(Bit#(16))) rq_baddr_rand <- replicateM(mkLFSR_16);
    Vector#(L1Num, LFSR#(Bit#(8))) rq_ex_sh_rand <- replicateM(mkLFSR_8);
    LFSR#(Bit#(32)) rq_value_rand_high <- mkLFSR_32;
    LFSR#(Bit#(32)) rq_value_rand_low <- mkLFSR_32;

    Vector#(L1Num, Reg#(Bool)) rq_type <- replicateM(mkReg(False));
    Vector#(L1Num, Reg#(Bit#(64))) rq_addr <- replicateM(mkReg(0));
    Vector#(L1Num, Reg#(Bool)) rq_ex_sh <- replicateM(mkReg(False));
    // For temporal locality
    Vector#(L1Num, Reg#(Bit#(8))) rq_tl_cycles <- replicateM(mkReg(0));
    Reg#(CCValue) rq_value <- mkReg(replicate(0));
    Reg#(Bit#(3)) rq_value_idx <- mkReg(0);

    Vector#(L1Num, Reg#(Bit#(64))) marks <- replicateM(mkReg(0));

    function Bit#(64) getAddr (Bit#(ExShIdxSz) idx, Bit#(LgL1DSz) l1Addr);
        Bit#(AddrOffset) pad = 0;
        Bit#(64) addr = zeroExtend({idx, l1Addr, pad});
        return addr;
    endfunction

    rule mem_init_count (!memInit);
        memInitCount <= memInitCount + 1;
        memInit <= (memInitCount == maxBound);
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
        rule rq_ex_sh_upd (rq_tl_cycles[i] >= fromInteger(valueOf(NumTlCycles)));
            let t = rq_ex_sh_rand[i].value;
            rq_ex_sh_rand[i].next();
            Bit#(LgExShRatio) rz = 0;
            rq_ex_sh[i] <= (truncate(t) == rz? True : False);
            rq_tl_cycles[i] <= 0; // fill the fuel
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

    function CCMsg ldReq(Integer i);
        return CCMsg { id : getRqId, type_ : False, addr : rq_addr[i], value : unpack(0) };
    endfunction
    function CCMsg stReq(Integer i);
        return CCMsg { id : setRqId, type_ : False, addr : rq_addr[i], value : rq_value };
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
            rq_tl_cycles[i] <= rq_tl_cycles[i] + 1;
        endrule
    end
    for (Integer i = 0; i < valueOf(L1Num); i = i+1) begin
        rule request_store if (memInit && onTest && rq_type[i]);
            mem.l1Ifc[i].mem_enq_rq(stReq(i));
            rq_tl_cycles[i] <= rq_tl_cycles[i] + 1;
        endrule
    end
    for (Integer i = 0; i < valueOf(L1Num); i = i+1) begin
        rule response;
            let rs <- mem.l1Ifc[i].mem_deq_rs ();
            addResp(i);
            marks[i] <= marks[i] + rs.value[0] + rs.value[1] + rs.value[2] + rs.value[3];
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
        rq_value_rand_high.seed(fromInteger(valueOf(RqValueSeed)));
        rq_value_rand_low.seed(fromInteger(valueOf(RqValueSeed) + 1));
    endmethod

    method Bool isEnd();
        return !onTest;
    endmethod

    method Bit#(64) getThroughput();
        Bit#(64) sum = 0;
        for (Integer i = 0; i < valueOf(L1Num); i = i+1) begin
            sum = sum + numResps[i];
        end
        return sum;
    endmethod
    method Bit#(64) getMark();
        Bit#(64) ret = 0;
        for (Integer i = 0; i < valueOf(L1Num); i = i+1) begin
            ret = ret + marks[i];
        end
        return ret;
    endmethod
endmodule

// A workload that adjacent two L1 caches share some memory address
// Exclusive: [0..0][0][------L1Idx-----][----rand(LgL1DSz)----]
// Shared   : [0..0][1][(L1CacheIndex)/2][0..0][rand(LgShRange)]
module mkCCTestSharedPair#(CC mem)(CCTest);
    Reg#(Bool) memInit <- mkReg(False);
    Reg#(Bit#(LLCacheSz)) memInitCount <- mkReg(0);
    Reg#(Bool) onTest <- mkReg(False);
    Reg#(CycleCnt) maxCycle <- mkReg(0);
    Reg#(CycleCnt) curCycle <- mkReg(0);
    Vector#(L1Num, Reg#(Bit#(64))) numResps <- replicateM(mkReg(0));
    Reg#(Bit#(16)) deadlockDetector <- mkReg(0);

    Vector#(L1Num, LFSR#(Bit#(4))) rq_type_rand <- replicateM(mkLFSR_4);
    Vector#(L1Num, LFSR#(Bit#(16))) rq_baddr_rand <- replicateM(mkLFSR_16);
    Vector#(L1Num, LFSR#(Bit#(8))) rq_ex_sh_rand <- replicateM(mkLFSR_8);
    LFSR#(Bit#(32)) rq_value_rand_high <- mkLFSR_32;
    LFSR#(Bit#(32)) rq_value_rand_low <- mkLFSR_32;

    Vector#(L1Num, Reg#(Bool)) rq_type <- replicateM(mkReg(False));
    Vector#(L1Num, Reg#(Bit#(64))) rq_addr <- replicateM(mkReg(0));
    Vector#(L1Num, Reg#(Bool)) rq_ex_sh <- replicateM(mkReg(False));
    // For temporal locality
    Vector#(L1Num, Reg#(Bit#(8))) rq_tl_cycles <- replicateM(mkReg(0));
    Reg#(CCValue) rq_value <- mkReg(replicate(0));
    Reg#(Bit#(3)) rq_value_idx <- mkReg(0);

    Vector#(L1Num, Reg#(Bit#(64))) marks <- replicateM(mkReg(0));

    function Bit#(64) getAddr (Bit#(ExShIdxSz) idx, Bit#(LgL1DSz) l1Addr);
        Bit#(AddrOffset) pad = 0;
        Bit#(64) addr = zeroExtend({idx, l1Addr, pad});
        return addr;
    endfunction

    rule mem_init_count (!memInit);
        memInitCount <= memInitCount + 1;
        memInit <= (memInitCount == maxBound);
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
                // Here the trick is to set the sharing index based on (i / 2);
                // (2n)-th and (2n+1)-th L1 caches will have the same shared region.
                Bit#(ExShIdxSz) shIdx = fromInteger(valueOf(ShIdx) + i / 2);
                let shAddr = getAddr(shIdx, saddr);
                rq_addr[i] <= shAddr;
            end
            else begin
                let addr = getAddr(fromInteger(i), l1Addr);
                rq_addr[i] <= addr;
            end
        endrule
    end
    for (Integer i = 0; i < valueOf(L1Num); i=i+1) begin
        rule rq_ex_sh_upd (rq_tl_cycles[i] >= fromInteger(valueOf(NumTlCycles)));
            let t = rq_ex_sh_rand[i].value;
            rq_ex_sh_rand[i].next();
            Bit#(LgExShRatio) rz = 0;
            rq_ex_sh[i] <= (truncate(t) == rz? True : False);
            rq_tl_cycles[i] <= 0; // fill the fuel
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

    function CCMsg ldReq(Integer i);
        return CCMsg { id : getRqId, type_ : False, addr : rq_addr[i], value : unpack(0) };
    endfunction
    function CCMsg stReq(Integer i);
        return CCMsg { id : setRqId, type_ : False, addr : rq_addr[i], value : rq_value };
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
            rq_tl_cycles[i] <= rq_tl_cycles[i] + 1;
        endrule
    end
    for (Integer i = 0; i < valueOf(L1Num); i = i+1) begin
        rule request_store if (memInit && onTest && rq_type[i]);
            mem.l1Ifc[i].mem_enq_rq(stReq(i));
            rq_tl_cycles[i] <= rq_tl_cycles[i] + 1;
        endrule
    end
    for (Integer i = 0; i < valueOf(L1Num); i = i+1) begin
        rule response;
            let rs <- mem.l1Ifc[i].mem_deq_rs ();
            addResp(i);
            marks[i] <= marks[i] + rs.value[0] + rs.value[1] + rs.value[2] + rs.value[3];
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
        rq_value_rand_high.seed(fromInteger(valueOf(RqValueSeed)));
        rq_value_rand_low.seed(fromInteger(valueOf(RqValueSeed) + 1));
    endmethod

    method Bool isEnd();
        return !onTest;
    endmethod

    method Bit#(64) getThroughput();
        Bit#(64) sum = 0;
        for (Integer i = 0; i < valueOf(L1Num); i = i+1) begin
            sum = sum + numResps[i];
        end
        return sum;
    endmethod
    method Bit#(64) getMark();
        Bit#(64) ret = 0;
        for (Integer i = 0; i < valueOf(L1Num); i = i+1) begin
            ret = ret + marks[i];
        end
        return ret;
    endmethod
endmodule
