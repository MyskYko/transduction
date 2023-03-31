#include <iostream>
#include <cassert>

#include "Transduction.h"

using namespace std;

int Transduction::RemoveRedundantFis(int i, int block_i0, unsigned j) {
  int count = 0;
  for(; j < vvFis[i].size(); j++) {
    if(block_i0 == (vvFis[i][j] >> 1))
      continue;
    lit x = man->Const1();
    IncRef(x);
    for(unsigned jj = 0; jj < vvFis[i].size(); jj++)
      if(j != jj)
        Update(x, man->And(x, LitFi(i, jj)));
    Update(x, man->Or(man->LitNot(x), vGs[i]));
    Update(x, man->Or(x, LitFi(i, j)));
    DecRef(x);
    if(man->IsConst1(x)) {
      int i0 = vvFis[i][j] >> 1;
      if(nVerbose > 4)
        cout << "\t\t\t\tRRF remove wire " << i0 << "(" << (vvFis[i][j] & 1) << ")" << " -> " << i << endl;
      Disconnect(i, i0, j--);
      count++;
    }
  }
  return count;
}

void Transduction::CalcG(int i) {
  Update(vGs[i], man->Const1());
  for(unsigned j = 0; j < vvFos[i].size(); j++) {
    int k = vvFos[i][j];
    int l = FindFi(k, i);
    assert(l >= 0);
    Update(vGs[i], man->And(vGs[i], vvCs[k][l]));
  }
}

int Transduction::CalcC(int i) {
  int count = 0;
  for(unsigned j = 0; j < vvFis[i].size(); j++) {
    lit x = man->Const1();
    IncRef(x);
    for(unsigned jj = j + 1; jj < vvFis[i].size(); jj++)
      Update(x, man->And(x, LitFi(i, jj)));
    Update(x, man->Or(man->LitNot(x), vGs[i]));
    int i0 = vvFis[i][j] >> 1;
    if(man->IsConst1(man->Or(x, LitFi(i, j)))) {
      if(nVerbose > 4)
        cout << "\t\t\t\tCspf remove wire " << i0 << "(" << (vvFis[i][j] & 1) << ")" << " -> " << i << endl;
      Disconnect(i, i0, j--);
      count++;
    } else if(vvCs[i][j] != x) {
      Update(vvCs[i][j], x);
      vPfUpdates[i0] = true;
    }
    DecRef(x);
  }
  return count;
}

int Transduction::Cspf(bool fSortRemove, int block, int block_i0) {
  if(nVerbose > 2) {
    cout << "\t\tCspf";
    if(block_i0 != -1)
      cout << " (block " << block_i0 << " -> " << block << ")";
    else if(block != -1)
      cout << " (block " << block << ")";
    cout << endl;
  }
  if(state != PfState::cspf)
    for(list<int>::iterator it = vObjs.begin(); it != vObjs.end(); it++)
      vPfUpdates[*it] = true;
  state = PfState::cspf;
  int count = 0;
  for(list<int>::reverse_iterator it = vObjs.rbegin(); it != vObjs.rend();) {
    if(vvFos[*it].empty()) {
      if(nVerbose > 3)
        cout << "\t\t\tRemove unused " << *it << endl;
      count += Remove(*it);
      it = list<int>::reverse_iterator(vObjs.erase(--(it.base())));
      continue;
    }
    if(!vPfUpdates[*it]) {
      it++;
      continue;
    }
    if(nVerbose > 3)
      cout << "\t\t\tCspf " << *it << endl;
    CalcG(*it);
    if(fSortRemove) {
      if(*it != block)
        SortFis(*it), count += RemoveRedundantFis(*it);
      else if(block_i0 != -1)
        count += RemoveRedundantFis(*it, block_i0);
    }
    count += CalcC(*it);
    vPfUpdates[*it] = false;
    assert(!vvFis[*it].empty());
    if(vvFis[*it].size() == 1) {
      count += Replace(*it, vvFis[*it][0]);
      it = list<int>::reverse_iterator(vObjs.erase(--(it.base())));
      continue;
    }
    it++;
  }
  Build(false);
  assert(AllFalse(vPfUpdates));
  return count;
}

bool Transduction::CspfDebug() {
  vector<lit> vGsOld;
  CopyVec(vGsOld, vGs);
  vector<vector<lit> > vvCsOld;
  CopyVec(vvCsOld, vvCs);
  state = PfState::none;
  Cspf();
  bool r = vGsOld == vGs && vvCsOld == vvCs;
  DelVec(vGsOld);
  DelVec(vvCsOld);
  return r;
}
