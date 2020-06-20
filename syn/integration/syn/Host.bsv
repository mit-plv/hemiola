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
    method Action start(Bit#(32) maxCycle);
endinterface

////////// Connectal interfaces end

interface Host;
    interface HostRequest request;
endinterface

module mkHost#(HostIndication indication) (Host);
    CC mem <- mkCCBramMem();
    CCTest tester <- mkCCTestRandom(mem);
    Reg#(Bool) started <- mkReg(False);
    Reg#(Bool) ended <- mkReg(False);

    rule check_end (started && tester.isEnd && !ended);
        let n = tester.getThroughput;
        indication.finish(n);
        ended <= True;
    endrule

    interface HostRequest request;
        method Action start(Bit#(32) maxCycle);
	    tester.start(maxCycle);
	    started <= True;
	endmethod
    endinterface
endmodule
