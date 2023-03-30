#include <cassert>

#include "Transduction.h"

int main(int argc, char **argv) {
  aigman aig(argv[1]);
  Transduction tra(aig, 0, 0);
  assert(tra.BuildDebug());
  tra.Cspf(true);
  assert(tra.CspfDebug());
  tra.Mspf(true);
  assert(tra.MspfDebug());
  tra.Cspf(true);
  assert(tra.CspfDebug());
  tra.Mspf(true);
  assert(tra.MspfDebug());
  tra.GenerateAig(aig);
  aig.write("tmp.aig");
  return 0;
}
