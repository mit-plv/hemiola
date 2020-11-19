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
    CCMem mem <- mkCCBramMem();

    // CCTest tester <- mkCCTestCheck(mem.cc);
    // CCTest tester <- mkCCTestRandom(mem.cc);
    CCTest tester <- mkCCTestShared(mem.cc);

    Reg#(Bool) started <- mkReg(False);
    Reg#(Bool) ended <- mkReg(False);

    rule start (!started);
        started <= True;
        tester.start(fromInteger(valueOf(TestCycleCnt)));
    endrule

    rule check_end (started && tester.isEnd && !ended);
        let n = tester.getThroughput();
        let m = tester.getMark();
        $fwrite (stderr, "Test done, throughput: %d / %d", n, fromInteger(valueOf(TestCycleCnt)));
        $fwrite (stderr, "Mark: %x", m);
        ended <= True;
    endrule

endmodule
