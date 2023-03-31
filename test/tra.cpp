#include <iostream>
#include <cassert>

#include "Transduction.h"

int main(int argc, char **argv) {
  aigman aig(argv[1]);
  Transduction tra(aig, 0, 0, 0);
  tra.Optimize(false, false, false, false, false);
  tra.GenerateAig(aig);
  aig.write("tmp.aig");
  return 0;
}
