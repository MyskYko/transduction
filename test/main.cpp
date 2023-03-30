#include "Transduction.h"

int main(int argc, char **argv) {
  aigman aig(argv[1]);
  Transduction tra(aig, 7);
  tra.GenerateAig(aig);
  aig.write("tmp.aig");
  return 0;
}
