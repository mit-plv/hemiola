import Vector::*;
import BuildVector::*;
import RWire::*;
import FIFO::*;
import FIFOF::*;

import CC::*;
import CCWrapper::*;

////////// Connectal interfaces

typedef Bit#(64) Addr;
typedef Bit#(64) Value;

interface HostIndication;
    method Action getRs0(Bool write, Addr a, Value v);
    method Action getRs1(Bool write, Addr a, Value v);
    method Action getRs2(Bool write, Addr a, Value v);
    method Action getRs3(Bool write, Addr a, Value v);
    method Action getRs4(Bool write, Addr a, Value v);
    method Action getRs5(Bool write, Addr a, Value v);
    method Action getRs6(Bool write, Addr a, Value v);
    method Action getRs7(Bool write, Addr a, Value v);
endinterface

interface HostRequest;
    method Action start();
    method Action putRq0(Bool write, Addr a, Value v);
    method Action putRq1(Bool write, Addr a, Value v);
    method Action putRq2(Bool write, Addr a, Value v);
    method Action putRq3(Bool write, Addr a, Value v);
    method Action putRq4(Bool write, Addr a, Value v);
    method Action putRq5(Bool write, Addr a, Value v);
    method Action putRq6(Bool write, Addr a, Value v);
    method Action putRq7(Bool write, Addr a, Value v);
endinterface

////////// Connectal interfaces end

interface Host;
    interface HostRequest request;
endinterface

module mkHost#(HostIndication indication) (Host);
    CC mem <- mkCCWrapper();
    Reg#(Bool) init <- mkReg(False);

    let getRqId = 6'b000000;
    let setRqId = 6'b001000;
    let getRsId = 6'b000001;
    let setRsId = 6'b001001;

    function Struct2 ldReq(Addr a);
        return Struct2 { id : getRqId, type_ : False, addr : a, value : 0 };
    endfunction

    function Struct2 stReq(Addr a, Value v);
        return Struct2 { id : setRqId, type_ : False, addr : a, value : v };
    endfunction

    (* fire_when_enabled *)
    rule mem_init_done (!init && mem.isInit);
        init <= True;
    endrule

    (* fire_when_enabled *)
    rule get_rs_0 if (init);
        let rs <- mem.mem_deq_rs_0 ();
        if (rs.id == getRsId) indication.getRs0(False, rs.addr, rs.value);
        else if (rs.id == setRsId) indication.getRs0(True, rs.addr, rs.value);
    endrule
    rule get_rs_1 if (init);
        let rs <- mem.mem_deq_rs_1 ();
        if (rs.id == getRsId) indication.getRs1(False, rs.addr, rs.value);
        else if (rs.id == setRsId) indication.getRs1(True, rs.addr, rs.value);
    endrule
    rule get_rs_2 if (init);
        let rs <- mem.mem_deq_rs_2 ();
        if (rs.id == getRsId) indication.getRs2(False, rs.addr, rs.value);
        else if (rs.id == setRsId) indication.getRs2(True, rs.addr, rs.value);
    endrule
    rule get_rs_3 if (init);
        let rs <- mem.mem_deq_rs_3 ();
        if (rs.id == getRsId) indication.getRs3(False, rs.addr, rs.value);
        else if (rs.id == setRsId) indication.getRs3(True, rs.addr, rs.value);
    endrule
    rule get_rs_4 if (init);
        let rs <- mem.mem_deq_rs_4 ();
        if (rs.id == getRsId) indication.getRs4(False, rs.addr, rs.value);
        else if (rs.id == setRsId) indication.getRs4(True, rs.addr, rs.value);
    endrule
    rule get_rs_5 if (init);
        let rs <- mem.mem_deq_rs_5 ();
        if (rs.id == getRsId) indication.getRs5(False, rs.addr, rs.value);
        else if (rs.id == setRsId) indication.getRs5(True, rs.addr, rs.value);
    endrule
    rule get_rs_6 if (init);
        let rs <- mem.mem_deq_rs_6 ();
        if (rs.id == getRsId) indication.getRs6(False, rs.addr, rs.value);
        else if (rs.id == setRsId) indication.getRs6(True, rs.addr, rs.value);
    endrule
    rule get_rs_7 if (init);
        let rs <- mem.mem_deq_rs_7 ();
        if (rs.id == getRsId) indication.getRs7(False, rs.addr, rs.value);
        else if (rs.id == setRsId) indication.getRs7(True, rs.addr, rs.value);
    endrule

    interface HostRequest request;
        method Action start ();
        endmethod

        method Action putRq0(Bool write, Addr a, Value v) if (init);
            if (write) mem.mem_enq_rq_0(stReq(a, v));
            else mem.mem_enq_rq_0(ldReq(a));
        endmethod
        method Action putRq1(Bool write, Addr a, Value v) if (init);
            if (write) mem.mem_enq_rq_1(stReq(a, v));
            else mem.mem_enq_rq_1(ldReq(a));
        endmethod
        method Action putRq2(Bool write, Addr a, Value v) if (init);
            if (write) mem.mem_enq_rq_2(stReq(a, v));
            else mem.mem_enq_rq_2(ldReq(a));
        endmethod
        method Action putRq3(Bool write, Addr a, Value v) if (init);
            if (write) mem.mem_enq_rq_3(stReq(a, v));
            else mem.mem_enq_rq_3(ldReq(a));
        endmethod
        method Action putRq4(Bool write, Addr a, Value v) if (init);
            if (write) mem.mem_enq_rq_4(stReq(a, v));
            else mem.mem_enq_rq_4(ldReq(a));
        endmethod
        method Action putRq5(Bool write, Addr a, Value v) if (init);
            if (write) mem.mem_enq_rq_5(stReq(a, v));
            else mem.mem_enq_rq_5(ldReq(a));
        endmethod
        method Action putRq6(Bool write, Addr a, Value v) if (init);
            if (write) mem.mem_enq_rq_6(stReq(a, v));
            else mem.mem_enq_rq_6(ldReq(a));
        endmethod
        method Action putRq7(Bool write, Addr a, Value v) if (init);
            if (write) mem.mem_enq_rq_7(stReq(a, v));
            else mem.mem_enq_rq_7(ldReq(a));
        endmethod
    endinterface
endmodule
