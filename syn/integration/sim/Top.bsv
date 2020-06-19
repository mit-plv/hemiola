import Vector::*;
import BuildVector::*;
import FIFO::*;
import FIFOF::*;
import Randomizable::*;

import CC::*;
import CCWrapper::*;
import MemBank::*;

typedef 8 L1Num;
typedef MemBramAddrSz BAddrSz;

(* synthesize *)
module mkTop(Empty);
    CC mem <- mkCCWrapper ();
    Reg#(Bool) memInit <- mkReg(False);
    Vector#(L1Num, Randomize#(int)) rq_type_rand <- replicateM(mkConstrainedRandomizer(0, 1));
    Randomize#(Bit#(BAddrSz)) rq_baddr_rand <- mkGenericRandomizer;
    Vector#(L1Num, Reg#(Bool)) rq_type_seed <- replicateM(mkReg(False));
    Reg#(Bit#(64)) rq_addr <- mkReg(0);
    Reg#(Bit#(64)) rq_data <- mkReg(0);

    function Bit#(64) getAddr (Bit#(BAddrSz) baddr);
        Bit#(64) addr = zeroExtend({baddr, 3'b000});
        return addr;
    endfunction

    rule mem_init_done (!memInit && mem.isInit);
        memInit <= True;
    endrule

    rule rq_type_rand_init;
        for (Integer i = 0; i < valueOf(L1Num); i = i+1) begin
            rq_type_rand[i].cntrl.init();
        end
        rq_baddr_rand.cntrl.init();
    endrule
    rule rq_type_seed_toggle;
        for (Integer i = 0; i < valueOf(L1Num); i = i+1) begin
            let t <- rq_type_rand[i].next();
            rq_type_seed[i] <= (t == 1 ? True : False);
        end
    endrule
    rule rq_addr_toggle;
        let baddr <- rq_baddr_rand.next();
        let addr = getAddr(baddr);
        rq_addr <= addr;
    endrule
    rule rq_data_inc;
        rq_data <= rq_data + 1;
    endrule

    let getRqId = 6'b000000;
    let setRqId = 6'b001000;
    let getRsId = 6'b000001;
    let setRsId = 6'b001001;

    let ldReq = Struct2 { id : getRqId, type_ : False, addr : rq_addr, value : 0 };
    let stReq = Struct2 { id : setRqId, type_ : False, addr : rq_addr, value : rq_data };

    rule request_load_0 if (memInit && rq_type_seed[0]);
        mem.mem_enq_rq_0(ldReq);
        $display ("0: LdReq: %x", rq_addr);
    endrule
    rule request_store_0 if (memInit && !rq_type_seed[0]);
        mem.mem_enq_rq_0(stReq);
        $display ("0: StReq: %x %x", rq_addr, rq_data);
    endrule
    rule response_0;
        let rs <- mem.mem_deq_rs_0 ();
        if (rs.id == getRsId) $display ("0: LdResp: %x", rs.value);
        else if (rs.id == setRsId) $display ("0: StResp");
        else $display ("0: Unknown response: %x", rs.id);
    endrule

    rule request_load_1 if (memInit && rq_type_seed[1]);
        mem.mem_enq_rq_1(ldReq);
        $display ("1: LdReq: %x", rq_addr);
    endrule
    rule request_store_1 if (memInit && !rq_type_seed[1]);
        mem.mem_enq_rq_1(stReq);
        $display ("1: StReq: %x %x", rq_addr, rq_data);
    endrule
    rule response_1;
        let rs <- mem.mem_deq_rs_1 ();
        if (rs.id == getRsId) $display ("1: LdResp: %x", rs.value);
        else if (rs.id == setRsId) $display ("1: StResp");
        else $display ("1: Unknown response: %x", rs.id);
    endrule

    rule request_load_2 if (memInit && rq_type_seed[2]);
        mem.mem_enq_rq_2(ldReq);
        $display ("2: LdReq: %x", rq_addr);
    endrule
    rule request_store_2 if (memInit && !rq_type_seed[2]);
        mem.mem_enq_rq_2(stReq);
        $display ("2: StReq: %x %x", rq_addr, rq_data);
    endrule
    rule response_2;
        let rs <- mem.mem_deq_rs_2 ();
        if (rs.id == getRsId) $display ("2: LdResp: %x", rs.value);
        else if (rs.id == setRsId) $display ("2: StResp");
        else $display ("2: Unknown response: %x", rs.id);
    endrule

    rule request_load_3 if (memInit && rq_type_seed[3]);
        mem.mem_enq_rq_3(ldReq);
        $display ("3: LdReq: %x", rq_addr);
    endrule
    rule request_store_3 if (memInit && !rq_type_seed[3]);
        mem.mem_enq_rq_3(stReq);
        $display ("3: StReq: %x %x", rq_addr, rq_data);
    endrule
    rule response_3;
        let rs <- mem.mem_deq_rs_3 ();
        if (rs.id == getRsId) $display ("3: LdResp: %x", rs.value);
        else if (rs.id == setRsId) $display ("3: StResp");
        else $display ("3: Unknown response: %x", rs.id);
    endrule

    rule request_load_4 if (memInit && rq_type_seed[4]);
        mem.mem_enq_rq_4(ldReq);
        $display ("4: LdReq: %x", rq_addr);
    endrule
    rule request_store_4 if (memInit && !rq_type_seed[4]);
        mem.mem_enq_rq_4(stReq);
        $display ("4: StReq: %x %x", rq_addr, rq_data);
    endrule
    rule response_4;
        let rs <- mem.mem_deq_rs_4 ();
        if (rs.id == getRsId) $display ("4: LdResp: %x", rs.value);
        else if (rs.id == setRsId) $display ("4: StResp");
        else $display ("4: Unknown response: %x", rs.id);
    endrule

    rule request_load_5 if (memInit && rq_type_seed[5]);
        mem.mem_enq_rq_5(ldReq);
        $display ("5: LdReq: %x", rq_addr);
    endrule
    rule request_store_5 if (memInit && !rq_type_seed[5]);
        mem.mem_enq_rq_5(stReq);
        $display ("5: StReq: %x %x", rq_addr, rq_data);
    endrule
    rule response_5;
        let rs <- mem.mem_deq_rs_5 ();
        if (rs.id == getRsId) $display ("5: LdResp: %x", rs.value);
        else if (rs.id == setRsId) $display ("5: StResp");
        else $display ("5: Unknown response: %x", rs.id);
    endrule

    rule request_load_6 if (memInit && rq_type_seed[6]);
        mem.mem_enq_rq_6(ldReq);
        $display ("6: LdReq: %x", rq_addr);
    endrule
    rule request_store_6 if (memInit && !rq_type_seed[6]);
        mem.mem_enq_rq_6(stReq);
        $display ("6: StReq: %x %x", rq_addr, rq_data);
    endrule
    rule response_6;
        let rs <- mem.mem_deq_rs_6 ();
        if (rs.id == getRsId) $display ("6: LdResp: %x", rs.value);
        else if (rs.id == setRsId) $display ("6: StResp");
        else $display ("6: Unknown response: %x", rs.id);
    endrule

    rule request_load_7 if (memInit && rq_type_seed[7]);
        mem.mem_enq_rq_7(ldReq);
        $display ("7: LdReq: %x", rq_addr);
    endrule
    rule request_store_7 if (memInit && !rq_type_seed[7]);
        mem.mem_enq_rq_7(stReq);
        $display ("7: StReq: %x %x", rq_addr, rq_data);
    endrule
    rule response_7;
        let rs <- mem.mem_deq_rs_7 ();
        if (rs.id == getRsId) $display ("7: LdResp: %x", rs.value);
        else if (rs.id == setRsId) $display ("7: StResp");
        else $display ("7: Unknown response: %x", rs.id);
    endrule

endmodule
