import Vector::*;
import BuildVector::*;
import RWire::*;
import FIFO::*;
import FIFOF::*;

import CC::*;
import CCWrapper::*;
import CCTest::*;

////////// Connectal interfaces

typedef Bit#(64) Addr;
typedef Bit#(64) Value;

interface HostIndication;
    method Action finish(Bit#(32) numResps);
endinterface

interface HostRequest;
    method Action start(CycleCnt maxCycle);
endinterface

////////// Connectal interfaces end

interface Host;
    interface HostRequest request;
endinterface

module mkHost#(HostIndication indication) (Host);
    CC mem <- mkCCWrapper();
    CCTest tester <- mkCCTestRandom(mem);
    Reg#(Bool) ended <- mkReg(False)

    rule check_end (tester.isEnd && !ended);
        let n = tester.getThroughput;
        indication.finish(n);
        ended <= True;
    endrule

    interface HostRequest request;
        method start = tester.start;
        method getThroughput = tester.getThroughput;
    endinterface
endmodule
