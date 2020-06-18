#include <errno.h>
#include <stdio.h>
#include <unistd.h>
#include "HostIndication.h"
#include "HostRequest.h"
#include "GeneratedTypes.h"

#include "Tests.h"

class HostIndication : public HostIndicationWrapper
{
public:
  virtual void getRs0(int write, uint64_t a, uint64_t v) {
    printf("resp 0 %d %lx %lx\n", write, a, v);
  }
  virtual void getRs1(int write, uint64_t a, uint64_t v) {
    printf("resp 1 %d %lx %lx\n", write, a, v);
  }
  virtual void getRs2(int write, uint64_t a, uint64_t v) {
    printf("resp 2 %d %lx %lx\n", write, a, v);
  }
  virtual void getRs3(int write, uint64_t a, uint64_t v) {
    printf("resp 3 %d %lx %lx\n", write, a, v);
  }
  virtual void getRs4(int write, uint64_t a, uint64_t v) {
    printf("resp 4 %d %lx %lx\n", write, a, v);
  }
  virtual void getRs5(int write, uint64_t a, uint64_t v) {
    printf("resp 5 %d %lx %lx\n", write, a, v);
  }
  virtual void getRs6(int write, uint64_t a, uint64_t v) {
    printf("resp 6 %d %lx %lx\n", write, a, v);
  }
  virtual void getRs7(int write, uint64_t a, uint64_t v) {
    printf("resp 7 %d %lx %lx\n", write, a, v);
  }

  HostIndication(unsigned int id) : HostIndicationWrapper(id) {}
};

int main(int argc, const char **argv) {

  HostIndication toHostIndication(IfcNames_HostIndicationH2S);
  HostRequestProxy* hostRequestProxy = new HostRequestProxy(IfcNames_HostRequestS2H);

  // Wait for some seconds from connectal to be ready
  usleep(3 * 1000);
  hostRequestProxy->start();

  CCTest* test = new RandomAddrRWTest(hostRequestProxy, 0x1000);
  test->init();
  while (1) test->loop();

  return 0;
}
