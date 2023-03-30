#include <iostream>
#include <cassert>

#include "Transduction.h"

using namespace std;

Transduction::Transduction(aigman const &aig, int nVerbose): nVerbose(nVerbose) {
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
    vPoFs[i] = LitFanin(vPos[i], 0);
}
Transduction::~Transduction() {
  delete man;
}

void Transduction::Build(int i, vector<lit>& vFs_) const {
  if(nVerbose > 4)
    cout << "\t\t\t\tBuild " << i << endl;
  Update(vFs_[i], man->Const1());
  for(unsigned j = 0; j < vvFis[i].size(); j++)
    Update(vFs_[i], man->And(vFs_[i], LitFanin(i, j)));
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
      if(man->IsConst1(man->Or(LitFanin(vPos[i], 0), vvCs[vPos[i]][0]))) {
        if(nVerbose > 3)
          cout << "\t\t\tConst 1 output : po " << i << endl;
        Disconnect(vPos[i], i0, 0, false, false);
        Connect(vPos[i], 1, false, false);
        fRemoved |= vvFos[i0].empty();
    } else if(man->IsConst1(man->Or(man->LitNot(LitFanin(vPos[i], 0)), vvCs[vPos[i]][0]))) {
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
