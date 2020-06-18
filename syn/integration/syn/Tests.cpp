#include <stdio.h>
#include <stdlib.h>
#include "HostRequest.h"
#include "Tests.h"

ReadAfterWriteTest::ReadAfterWriteTest(HostRequestProxy* _rqIfc)
  : rqIfc(_rqIfc)
{ }

void ReadAfterWriteTest::init() {
  rqIfc->putRq0(false, 0x0, 0x0);
  rqIfc->putRq1(false, 0x0, 0x0);
  rqIfc->putRq2(false, 0x0, 0x0);
  rqIfc->putRq3(false, 0x0, 0x0);
  rqIfc->putRq4(false, 0x0, 0x0);
  rqIfc->putRq5(false, 0x0, 0x0);
  rqIfc->putRq6(false, 0x0, 0x0);
  rqIfc->putRq7(false, 0x0, 0x0);
  rqIfc->putRq0(true, 0x0, 0xdeadbeef0badbeef);
}

void ReadAfterWriteTest::loop() {
  rqIfc->putRq0(false, 0x0, 0x0);
  rqIfc->putRq1(false, 0x0, 0x0);
  rqIfc->putRq2(false, 0x0, 0x0);
  rqIfc->putRq3(false, 0x0, 0x0);
  rqIfc->putRq4(false, 0x0, 0x0);
  rqIfc->putRq5(false, 0x0, 0x0);
  rqIfc->putRq6(false, 0x0, 0x0);
  rqIfc->putRq7(false, 0x0, 0x0);
}

RandomAddrRWTest::RandomAddrRWTest(HostRequestProxy* _rqIfc, const uint64_t& _addrRange)
  : rqIfc(_rqIfc), addrRange(_addrRange) {
  srand(0);
}

void RandomAddrRWTest::init() {
}

void RandomAddrRWTest::loop() {
  int turn = rand() % 8;
  bool rw = rand() % 2;
  uint64_t addr = rand() % addrRange;
  uint64_t val = rand();
  addr = addr << 3;

  switch (turn) {
  case 0:
    printf("req 0 %d %lx\n", rw, addr);
    rqIfc->putRq0(rw, addr, val);
    break;
  case 1:
    printf("req 1 %d %lx\n", rw, addr);
    rqIfc->putRq1(rw, addr, val);
    break;
  case 2:
    printf("req 2 %d %lx\n", rw, addr);
    rqIfc->putRq2(rw, addr, val);
    break;
  case 3:
    printf("req 3 %d %lx\n", rw, addr);
    rqIfc->putRq3(rw, addr, val);
    break;
  case 4:
    printf("req 4 %d %lx\n", rw, addr);
    rqIfc->putRq4(rw, addr, val);
    break;
  case 5:
    printf("req 5 %d %lx\n", rw, addr);
    rqIfc->putRq5(rw, addr, val);
    break;
  case 6:
    printf("req 6 %d %lx\n", rw, addr);
    rqIfc->putRq6(rw, addr, val);
    break;
  case 7:
    printf("req 7 %d %lx\n", rw, addr);
    rqIfc->putRq7(rw, addr, val);
    break;
  default: break;
  }
}
