#include <errno.h>
#include <stdio.h>
#include <unistd.h>
#include "HostIndication.h"
#include "HostRequest.h"
#include "GeneratedTypes.h"

class HostIndication : public HostIndicationWrapper
{
public:
  virtual void getRs0(int write, uint64_t a, uint64_t v) {
    printf("resp: %d %lx %lx\n", write, a, v);
  }
  virtual void getRs1(int write, uint64_t a, uint64_t v) {
    printf("resp: %d %lx %lx\n", write, a, v);
  }
  virtual void getRs2(int write, uint64_t a, uint64_t v) {
    printf("resp: %d %lx %lx\n", write, a, v);
  }
  virtual void getRs3(int write, uint64_t a, uint64_t v) {
    printf("resp: %d %lx %lx\n", write, a, v);
  }
  virtual void getRs4(int write, uint64_t a, uint64_t v) {
    printf("resp: %d %lx %lx\n", write, a, v);
  }
  virtual void getRs5(int write, uint64_t a, uint64_t v) {
    printf("resp: %d %lx %lx\n", write, a, v);
  }
  virtual void getRs6(int write, uint64_t a, uint64_t v) {
    printf("resp: %d %lx %lx\n", write, a, v);
  }
  virtual void getRs7(int write, uint64_t a, uint64_t v) {
    printf("resp: %d %lx %lx\n", write, a, v);
  }

  HostIndication(unsigned int id) : HostIndicationWrapper(id) {}
};

int main(int argc, const char **argv) {

  HostIndication toHostIndication(IfcNames_HostIndicationH2S);
  HostRequestProxy* hostRequestProxy = new HostRequestProxy(IfcNames_HostRequestS2H);

  // Wait for some seconds from connectal to be ready
  usleep(3 * 1000);

  hostRequestProxy->start();

  // Wait for some seconds from connectal to be ready
  usleep(3 * 1000);

  // Let's just try a simple case
  hostRequestProxy->putRq0(false, 0x0, 0x0);
  hostRequestProxy->putRq1(false, 0x0, 0x0);
  hostRequestProxy->putRq2(false, 0x0, 0x0);
  hostRequestProxy->putRq3(false, 0x0, 0x0);
  hostRequestProxy->putRq4(false, 0x0, 0x0);
  hostRequestProxy->putRq5(false, 0x0, 0x0);
  hostRequestProxy->putRq6(false, 0x0, 0x0);
  hostRequestProxy->putRq7(false, 0x0, 0x0);

  hostRequestProxy->putRq0(true, 0x0, 0xdeadbeef0badbeef);

  // busy-waiting
  while (1) {
    hostRequestProxy->putRq0(false, 0x0, 0x0);
    hostRequestProxy->putRq1(false, 0x0, 0x0);
    hostRequestProxy->putRq2(false, 0x0, 0x0);
    hostRequestProxy->putRq3(false, 0x0, 0x0);
    hostRequestProxy->putRq4(false, 0x0, 0x0);
    hostRequestProxy->putRq5(false, 0x0, 0x0);
    hostRequestProxy->putRq6(false, 0x0, 0x0);
    hostRequestProxy->putRq7(false, 0x0, 0x0);
  }

  return 0;
}
