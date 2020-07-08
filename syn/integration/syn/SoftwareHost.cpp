#include <errno.h>
#include <stdio.h>
#include <unistd.h>
#include "HostIndication.h"
#include "HostRequest.h"
#include "GeneratedTypes.h"

class HostIndication : public HostIndicationWrapper
{
public:
  virtual void finish(uint32_t numResps, uint64_t mark) {
    printf("Test done, #responses: %d\n", numResps);
    printf("Mark: %lx\n", mark);
    done = true;
  }

  virtual void dma_getRs_ll(uint64_t val) {
    printf("DMA LL: %lx\n", val);
  }
  virtual void dma_getRs_mem(uint64_t val) {
    printf("DMA MEM: %lx\n", val);
  }

  bool isDone() {
    return done;
  }

  HostIndication(unsigned int id)
    : HostIndicationWrapper(id), done(false) {}

private:
  bool done;
};

int main(int argc, const char **argv) {

  HostIndication toHostIndication(IfcNames_HostIndicationH2S);
  HostRequestProxy* hostRequestProxy = new HostRequestProxy(IfcNames_HostRequestS2H);

  // Wait for some seconds from connectal to be ready
  uint32_t maxCycle;
  printf ("Set the number of cycles: ");
  int s = scanf ("%u",&maxCycle); // to avoid [-Werror=unused-result]
  (void)s; // to avoid [-Werror=unused-variable]
  hostRequestProxy->start(maxCycle);

  while (!toHostIndication.isDone()) { }

  return 0;
}
