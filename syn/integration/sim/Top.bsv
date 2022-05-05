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
    CCMem mem <- mkCCBramMem();

`ifdef TB_ALL_SHARED
    CCTest tester <- mkCCTestRandom(mem.cc);
`elsif TB_PAIR_SHARED
    CCTest tester <- mkCCTestSharedPair(mem.cc);
`elsif TB_EX_SH
    CCTest tester <- mkCCTestShared(mem.cc);
`endif

    Reg#(Bool) started <- mkReg(False);
    Reg#(Bool) ended <- mkReg(False);

    rule start (!started);
        started <= True;
        tester.start(fromInteger(valueOf(TestCycleCnt)));
    endrule

    rule check_end (started && tester.isEnd && !ended);
        let n = tester.getThroughput();
        let m = tester.getMark();
        $fwrite (stderr, "Test done, #trs/cycle: %d / %d\n", n, fromInteger(valueOf(TestCycleCnt)));
        ended <= True;
    endrule

endmodule
