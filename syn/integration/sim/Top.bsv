import Vector::*;
import BuildVector::*;
import FIFO::*;
import FIFOF::*;
import Randomizable::*;

import CC::*;
import CCWrapper::*;
import CCTest::*;

typedef 1000000 TestCycleCnt;

(* synthesize *)
module mkTop(Empty);
    CC mem <- mkCCBramMem();
    CCTest tester <- mkCCTestRandom(mem);
    Reg#(Bool) started <- mkReg(False);
    Reg#(Bool) ended <- mkReg(False);

    rule start (!started);
        started <= True;
        tester.start(fromInteger(valueOf(TestCycleCnt)));
    endrule

    rule check_end (started && tester.isEnd && !ended);
        let n = tester.getThroughput();
        $display ("Test done, throughput: %d / %d",
           n, fromInteger(valueOf(TestCycleCnt)));
        ended <= True;
    endrule

endmodule
