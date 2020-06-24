import Vector::*;
import BuildVector::*;
import FIFO::*;
import FIFOF::*;

import HCC::*;

typedef Struct2 CCMsg;
typedef Bit#(6) CCMsgId;
typedef Bit#(64) CCAddr;

typedef 8 BitsPerByte;
typedef 8 ValueByte;
typedef TMul#(ValueByte, BitsPerByte) ValueSz; // 64
typedef Bit#(ValueSz) CCVal; // Bit#(64)

typedef 8 LineSz;
typedef Vector#(LineSz, CCVal) CCValue;

typedef TLog#(ValueByte) ValueOffset; // 3
typedef TLog#(LineSz) LineOffset; // 3
typedef TAdd#(LineOffset, ValueOffset) AddrOffset; // 6
