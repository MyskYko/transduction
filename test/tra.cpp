#include <iostream>
#include <cassert>

#include <NextBdd.h>
#include "ttman.h"
using namespace Ttman;

#include "Transduction.h"

int main(int argc, char **argv) {
  aigman aig(argv[1]);
  Transduction<Man, Param, lit, 0xffffffff> tra(aig, 4, 1, 0);
  tra.Optimize(false, false, true, false, false);
  tra.GenerateAig(aig);
  aig.write("tmp.aig");
  return 0;
}
