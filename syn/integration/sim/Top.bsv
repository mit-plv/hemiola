import Vector::*;
import BuildVector::*;
import FIFO::*;
import FIFOF::*;
import Randomizable::*;

import HCC::*;
import HCCWrapper::*;
import HCCTest::*;

typedef `TEST_CYCLE_CNT TestCycleCnt;

(* synthesize *)
module mkTop(Empty);
    // CC mem <- mkCCRegFileMem();
    CC mem <- mkCCBramMem();

    // CCTest tester <- mkCCTestIsolated(mem);
    // CCTest tester <- mkCCTestShared(mem);
    // CCTest tester <- mkCCTestRandom(mem);
    // CCTest tester <- mkCCTestCheck(mem);
    CCTest tester <- mkCCTestCheckIdxEquiv(mem);

    Reg#(Bool) started <- mkReg(False);
    Reg#(Bool) ended <- mkReg(False);

    rule start (!started);
        started <= True;
        tester.start(fromInteger(valueOf(TestCycleCnt)));
    endrule

    rule check_end (started && tester.isEnd && !ended);
        let n = tester.getThroughput();
        let m = tester.getMark();
        $display ("Test done, throughput: %d / %d", n, fromInteger(valueOf(TestCycleCnt)));
        $display ("Mark: %x", m);
        ended <= True;
    endrule

endmodule
