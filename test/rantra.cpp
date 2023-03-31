#include <iostream>
#include <chrono>
#include <random>
#include <ctime>
#include <cassert>

#include "Transduction.h"

using namespace std;

void Print(Transduction const & t, chrono::steady_clock::time_point const & start, string name) {
  auto end = chrono::steady_clock::now();
  chrono::duration<double> elapsed_seconds = end - start;
  cout << left << setw(20) << name << " : " << right << setw(10) << elapsed_seconds.count() << "s ";
  t.PrintStats();
}

int main(int argc, char ** argv) {
  bool fMspf = false;
  int N = 100;
  int M = 6;
  if(fMspf) {
    N = 10;
    M = 7;
  }
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
  Transduction t(aig, 0, nSortType, nPiShuffle);
  int nodes = aig.nGates;
  int count = t.CountWires();
  auto start = chrono::steady_clock::now();
  for(unsigned i = 0; i < Tests.size(); i++) {
    switch(Tests[i]) {
    case 0:
      count -= t.TrivialMerge();
      if(t.State() == PfState::cspf)
        assert(t.CspfDebug());
      else if(t.State() == PfState::mspf)
        assert(t.MspfDebug());
      break;
    case 1:
      count -= t.TrivialDecompose();
      if(t.State() == PfState::cspf)
        assert(t.CspfDebug());
      else if(t.State() == PfState::mspf)
        assert(t.MspfDebug());
      break;
    case 2:
      count -= t.Cspf(true);
      assert(t.CspfDebug());
      break;
    case 3:
      count -= t.Resub(false);
      assert(t.CspfDebug());
      break;
    case 4:
      count -= t.ResubMono(false);
      assert(t.CspfDebug());
      break;
    case 5:
      count -= t.ResubShared(false);
      count -= t.Cspf(true);
      assert(t.CspfDebug());
      break;
    default:
      cout << "Wrong test pattern!" << endl;
      return 1;
    }
    Print(t, start, "Test " + to_string(Tests[i]));
    if(!t.Verify()) {
      cout << "Circuits are not equivalent!" << endl;
      return 1;
    }
    if(count != t.CountWires()) {
      cout << "Wrong wire count!" << endl;
      return 1;
    }
    if(t.CountNodes() < nodes) {
      nodes = t.CountNodes();
      t.GenerateAig(aig);
    }
  }
  cout << nodes << endl;
  aig.write("tmp.aig");
  return 0;
}
