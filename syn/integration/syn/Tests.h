#include <stdio.h>
#include "HostRequest.h"

class CCTest {
public:
  virtual void init() = 0;
  virtual void loop() = 0;
};

class ReadAfterWriteTest : public CCTest {
public:
  virtual void init();
  virtual void loop();
  ReadAfterWriteTest(HostRequestProxy* _rqIfc);

private:
  HostRequestProxy* rqIfc;
};

class RandomAddrRWTest : public CCTest {
public:
  virtual void init();
  virtual void loop();
  RandomAddrRWTest(HostRequestProxy* _rqIfc, const uint64_t& _addrRange);

private:
  HostRequestProxy* rqIfc;
  const uint64_t& addrRange; // without offset
};
