#include <iostream>
#include <algorithm>
#include <cassert>

#include "Transduction.h"

using namespace std;

Transduction::Transduction(aigman const &aig, int nVerbose, int nSortType): nVerbose(nVerbose), nSortType(nSortType) {
  ImportAig(aig);
  Param p;
  p.nGbc = 1;
  p.nReo = 4000;
  man = new Man(aig.nPis, p);
  for(unsigned i = 0; i < vPis.size(); i++)
    vFs[i + 1] = man->IthVar(i);
  Build(false);
  man->Reorder();
  man->TurnOffReo();
  RemoveConstOutputs();
  vPoFs.resize(vPos.size());
  for(unsigned i = 0; i < vPos.size(); i++)
    vPoFs[i] = LitFi(vPos[i], 0);
  state = PfState::none;
}
Transduction::~Transduction() {
  DelVec(vFs);
  DelVec(vGs);
  for(int i = 0; i < nObjsAlloc; i++)
    DelVec(vvCs[i]);
  assert(man->CountNodes() == (int)vPis.size() + 1);
  delete man;
}

void Transduction::Build(int i, vector<lit>& vFs_) const {
  if(nVerbose > 4)
    cout << "\t\t\t\tBuild " << i << endl;
  Update(vFs_[i], man->Const1());
  for(unsigned j = 0; j < vvFis[i].size(); j++)
    Update(vFs_[i], man->And(vFs_[i], LitFi(i, j)));
}
void Transduction::Build(bool fPfUpdate) {
  if(nVerbose > 3)
    cout << "\t\t\tBuild" << endl;
  for(list<int>::iterator it = vObjs.begin(); it != vObjs.end(); it++) {
    if(vUpdates[*it]) {
      lit x = vFs[*it];
      man->IncRef(x);
      Build(*it, vFs);
      if(x != vFs[*it])
        for(unsigned j = 0; j < vvFos[*it].size(); j++)
          vUpdates[vvFos[*it][j]] = true;
      man->DecRef(x);
    }
  }
  if(fPfUpdate)
    for(list<int>::iterator it = vObjs.begin(); it != vObjs.end(); it++)
      vPfUpdates[*it] = vPfUpdates[*it] || vUpdates[*it];
  for(list<int>::iterator it = vObjs.begin(); it != vObjs.end(); it++)
    vUpdates[*it] = false;
  assert(AllFalse(vUpdates));
}
bool Transduction::BuildDebug() {
  for(list<int>::iterator it = vObjs.begin(); it != vObjs.end(); it++)
    vUpdates[*it] = true;
  vector<lit> vFsOld;
  CopyVec(vFsOld, vFs);
  Build(false);
  bool r = vFsOld == vFs;
  DelVec(vFsOld);
  return r;
}

void Transduction::RemoveConstOutputs() {
  bool fRemoved = false;
  for(unsigned i = 0; i < vPos.size(); i++) {
    int i0 = vvFis[vPos[i]][0] >> 1;
    if(i0) {
      if(man->IsConst1(man->Or(LitFi(vPos[i], 0), vvCs[vPos[i]][0]))) {
        if(nVerbose > 3)
          cout << "\t\t\tConst 1 output : po " << i << endl;
        Disconnect(vPos[i], i0, 0, false, false);
        Connect(vPos[i], 1, false, false);
        fRemoved |= vvFos[i0].empty();
    } else if(man->IsConst1(man->Or(man->LitNot(LitFi(vPos[i], 0)), vvCs[vPos[i]][0]))) {
        if(nVerbose > 3)
          cout << "\t\t\tConst 0 output : po " << i << endl;
        Disconnect(vPos[i], i0, 0, false, false);
        Connect(vPos[i], 0, false, false);
        fRemoved |= vvFos[i0].empty();
      }
    }
  }
  if(fRemoved) {
    if(nVerbose > 3)
      cout << "\t\t\tRemove unused" << endl;
    for(list<int>::reverse_iterator it = vObjs.rbegin(); it != vObjs.rend();) {
      if(vvFos[*it].empty()) {
        Remove(*it, false);
        it = list<int>::reverse_iterator(vObjs.erase(--(it.base())));
        continue;
      }
      it++;
    }
  }
}

// cost(a) > cost(b)
bool Transduction::CostCompare(int a, int b) const {
  int a0 = a >> 1;
  int b0 = b >> 1;
  if(vvFis[a0].empty() && vvFis[b0].empty())
    return find(find(vPis.begin(), vPis.end(), a0), vPis.end(), b0) != vPis.end();
  if(vvFis[a0].empty() && !vvFis[b0].empty())
    return false;
  if(!vvFis[a0].empty() && vvFis[b0].empty())
    return true;
  if(vvFos[a0].size() > vvFos[b0].size())
    return false;
  if(vvFos[a0].size() < vvFos[b0].size())
    return true;
  bool ac = a & 1;
  bool bc = b & 1;
  switch(nSortType) {
  case 0:
    return find(find(vObjs.begin(), vObjs.end(), a0), vObjs.end(), b0) == vObjs.end();
  case 1:
    return man->OneCount(man->LitNotCond(vFs[a0], ac)) < man->OneCount(man->LitNotCond(vFs[b0], bc));
  case 2:
    return man->OneCount(vFs[a0]) < man->OneCount(vFs[b0]);
  case 3:
    return man->OneCount(man->LitNot(vFs[a0])) < man->OneCount(vFs[b0]);
  default:
    return false;
  }
}
bool Transduction::SortFis(int i) {
  if(nVerbose > 4)
    cout << "\t\t\t\tSort fanins " << i << endl;
  bool fSort = false;
  for(int p = 1; p < (int)vvFis[i].size(); p++) {
    int f = vvFis[i][p];
    lit c = vvCs[i][p];
    int q = p - 1;
    for(; q >= 0 && CostCompare(f, vvFis[i][q]); q--) {
      vvFis[i][q + 1] = vvFis[i][q];
      vvCs[i][q + 1] = vvCs[i][q];
    }
    if(q + 1 != p) {
      fSort = true;
      vvFis[i][q + 1] = f;
      vvCs[i][q + 1] = c;
    }
  }
  if(nVerbose > 5)
    for(unsigned j = 0; j < vvFis[i].size(); j++)
      cout << "\t\t\t\t\tFanin " << j << " : " << (vvFis[i][j] >> 1) << "(" << (vvFis[i][j] & 1) << ")" << endl;
  return fSort;
}
