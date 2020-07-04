import Vector::*;
import BuildVector::*;
import RWire::*;
import FIFO::*;
import FIFOF::*;

import HCC::*;
import HCCWrapper::*;
import HCCTest::*;

////////// Connectal interfaces

interface HostIndication;
    method Action finish(Bit#(32) numResps, Bit#(64) mark);
endinterface

interface HostRequest;
    method Action start(Bit#(32) maxCycle);
    method Action force_rq(Bool wr, Bit#(64) faddr,
       Bit#(64) val0, Bit#(64) val1, Bit#(64) val2, Bit#(64) val3,
       Bit#(64) val4, Bit#(64) val5, Bit#(64) val6, Bit#(64) val7);
endinterface

////////// Connectal interfaces end

interface Host;
    interface HostRequest request;
endinterface

module mkHost#(HostIndication indication) (Host);
    // CC mem <- mkCCRegFileMem();
    CC mem <- mkCCBramMem();

    // CCTest tester <- mkCCTestIsolated(mem);
    // CCTest tester <- mkCCTestShared(mem);
    CCTest tester <- mkCCTestRandom(mem);

    Reg#(Bool) started <- mkReg(False);
    Reg#(Bool) ended <- mkReg(False);

    rule check_end (started && tester.isEnd && !ended);
        let n = tester.getThroughput;
        let m = tester.getMark;
        indication.finish(n, m);
        ended <= True;
    endrule

    interface HostRequest request;
        method Action start(Bit#(32) maxCycle);
	    tester.start(maxCycle);
	    started <= True;
	endmethod
        method Action force_rq(Bool wr, Bit#(64) faddr,
           Bit#(64) val0, Bit#(64) val1, Bit#(64) val2, Bit#(64) val3,
           Bit#(64) val4, Bit#(64) val5, Bit#(64) val6, Bit#(64) val7);
            Vector#(8, Bit#(64)) val = newVector();
            val[0] = val0; val[1] = val1; val[2] = val2; val[3] = val3;
            val[4] = val4; val[5] = val5; val[6] = val6; val[7] = val7;
            tester.force_rq(wr, faddr, val);
        endmethod
    endinterface
endmodule
