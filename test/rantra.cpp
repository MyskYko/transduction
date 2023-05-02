#include <iostream>
#include <chrono>
#include <random>
#include <ctime>
#include <cassert>

#include <NextBdd.h>
#include "ttman.h"
using namespace Ttman;

#include "Transduction.h"

using namespace std;

template <class Tra>
void Print(Tra const & t, chrono::steady_clock::time_point const & start, int n) {
  auto end = chrono::steady_clock::now();
  chrono::duration<double> elapsed_seconds = end - start;
  cout << "Test " << n << ": time = " << right << setw(10) << elapsed_seconds.count() << "s, ";
  t.PrintStats();
}

int main(int argc, char ** argv) {
  bool fMspf = true;
  bool fLevel = true;
  int N = 100;
  int M = 6;
  srand(time(NULL));
  int nSortType = rand() % 4;
  int nPiShuffle = rand();
  vector<int> Tests;
  for(int i = 0; i < N; i++)
    Tests.push_back(rand() % M);
  cout << "nSortType = " << nSortType << "; nPiShuffle = " << nPiShuffle << ";" << endl;
  cout << "Tests = {";
  string delim;
  for(unsigned i = 0; i < Tests.size(); i++) {
    cout << delim << Tests[i];
    delim = ", ";
  }
  cout << "};" << endl;
  aigman aig(argv[1]);
  Transduction<Man, Param, lit, 0xffffffff> t(aig, 0, nSortType, nPiShuffle, fLevel);
  int count = t.CountWires();
  int level = fLevel? t.CountLevels(): 0;
  auto start = chrono::steady_clock::now();
  for(unsigned i = 0; i < Tests.size(); i++) {
    switch(Tests[i]) {
    case 0:
      if(fLevel)
        break;
      count -= t.TrivialMerge();
      if(t.State() == PfState::cspf)
        assert(t.CspfDebug());
      else if(t.State() == PfState::mspf)
        assert(t.MspfDebug());
      break;
    case 1:
      if(fLevel)
        break;
      count -= t.TrivialDecompose();
      if(t.State() == PfState::cspf)
        assert(t.CspfDebug());
      else if(t.State() == PfState::mspf)
        assert(t.MspfDebug());
      break;
    case 2:
      count -= fMspf? t.Mspf(): t.Cspf();
      assert(fMspf? t.MspfDebug(): t.CspfDebug());
      break;
    case 3:
      count -= t.Resub(fMspf);
      assert(fMspf? t.MspfDebug(): t.CspfDebug());
      break;
    case 4:
      count -= t.ResubMono(fMspf);
      assert(fMspf? t.MspfDebug(): t.CspfDebug());
      break;
    case 5:
      if(fLevel)
        break;
      count -= t.ResubShared(fMspf);
      count -= fMspf? t.Mspf(): t.Cspf();
      assert(fMspf? t.MspfDebug(): t.CspfDebug());
      break;
    default:
      cout << "Wrong test pattern!" << endl;
      return 1;
    }
    Print(t, start, Tests[i]);
    if(!t.Verify()) {
      cout << "Circuits are not equivalent!" << endl;
      return 1;
    }
    if(count != t.CountWires()) {
      cout << "Wrong wire count!" << endl;
      return 1;
    }
    if(fLevel && level < t.CountLevels()) {
      cout << "Increased level!" << endl;
      return 1;
    }
    t.GenerateAig(aig);
    aig.write("tmp.aig");
  }
  return 0;
}
