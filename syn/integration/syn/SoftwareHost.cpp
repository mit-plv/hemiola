#include <errno.h>
#include <stdio.h>
#include <unistd.h>
#include "HostIndication.h"
#include "HostRequest.h"
#include "GeneratedTypes.h"

class HostIndication : public HostIndicationWrapper
{
public:
  virtual void finish(uint32_t numResps) {
    printf("Test done, #responses: %d\n", numResps);
    done = true;
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
  usleep(3 * 1000);
  hostRequestProxy->start();

  while (!toHostIndication.isDone()) { }

  return 0;
}
