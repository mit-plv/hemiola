import Vector::*;
import BuildVector::*;
import FIFO::*;
import FIFOF::*;
import RWBramCore::*;
import SpecialFIFOs::*;
import HCCIfc::*;

interface CC;
    interface Vector#(L1Num, MemRqRs#(Struct1)) l1Ifc;
    interface DMA#(Bit#(14), Struct32, Vector#(4, Bit#(64))) llDma;
endinterface

