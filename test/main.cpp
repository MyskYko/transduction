#include "Transduction.h"

int main(int argc, char **argv) {
  aigman aig(argv[1]);
  Transduction tra(aig, 0, 0);
  tra.Cspf(true);
  tra.GenerateAig(aig);
  aig.write("tmp.aig");
  return 0;
}
