#include <iostream>
#include <cassert>

#include "Transduction.h"

using namespace std;

void Transduction::BuildFoConeCompl(int i, vector<lit> &vPoFsCompl) const {
  if(nVerbose > 3)
    cout << "\t\t\tBuild with complemented " << i << endl;
  vector<lit> vFsCompl;
  CopyVec(vFsCompl, vFs);
  vFsCompl[i] = man->LitNot(vFs[i]);
  vector<bool> vUpdatesCompl(nObjsAlloc);
  for(unsigned j = 0; j < vvFos[i].size(); j++)
    vUpdatesCompl[vvFos[i][j]] = true;
  for(list<int>::const_iterator it = vObjs.begin(); it != vObjs.end(); it++)
    if(vUpdatesCompl[*it]) {
      Build(*it, vFsCompl);
      if(vFsCompl[*it] != vFs[*it])
        for(unsigned j = 0; j < vvFos[*it].size(); j++)
          vUpdatesCompl[vvFos[*it][j]] = true;
    }
  for(unsigned j = 0; j < vPos.size(); j++)
    Update(vPoFsCompl[j], LitFi(vPos[j], 0, vFsCompl));
  DelVec(vFsCompl);
}
bool Transduction::MspfCalcG(int i) {
  lit g = vGs[i];
  IncRef(g);
  vector<lit> vPoFsCompl(vPos.size(), LitMax());
  BuildFoConeCompl(i, vPoFsCompl);
  Update(vGs[i], man->Const1());
  for(unsigned j = 0; j < vPos.size(); j++) {
    lit x = man->LitNot(Xor(vPoFs[j], vPoFsCompl[j]));
    IncRef(x);
    Update(x, man->Or(x, vvCs[vPos[j]][0]));
    Update(vGs[i], man->And(vGs[i], x));
    DecRef(x);
  }
  DelVec(vPoFsCompl);
  DecRef(g);
  return vGs[i] != g;
}

int Transduction::MspfCalcC(int i, int block_i0) {
  for(unsigned j = 0; j < vvFis[i].size(); j++) {
    lit x = man->Const1();
    IncRef(x);
    for(unsigned jj = 0; jj < vvFis[i].size(); jj++)
      if(j != jj)
        Update(x, man->And(x, LitFi(i, jj)));
    Update(x, man->Or(man->LitNot(x), vGs[i]));
    int i0 = vvFis[i][j] >> 1;
    if(i0 != block_i0 && man->IsConst1(man->Or(x, LitFi(i, j)))) {
      if(nVerbose > 4)
        cout << "\t\t\t\tMspf remove wire " << i0 << "(" << (vvFis[i][j] & 1) << ")" << " -> " << i << endl;
      Disconnect(i, i0, j);
      DecRef(x);
      return RemoveRedundantFis(i, block_i0, j) + 1;
    } else if(vvCs[i][j] != x) {
      Update(vvCs[i][j], x);
      vPfUpdates[i0] = true;
    }
    DecRef(x);
  }
  return 0;
}

int Transduction::Mspf(bool fSort, int block, int block_i0) {
  if(nVerbose > 2) {
    cout << "\t\tMspf";
    if(block_i0 != -1)
      cout << " (block " << block_i0 << " -> " << block << ")";
    else if(block != -1)
      cout << " (block " << block << ")";
    cout << endl;
  }
  assert(AllFalse(vUpdates));
  vFoConeShared.resize(nObjsAlloc);
  if(state != PfState::mspf)
    for(list<int>::iterator it = vObjs.begin(); it != vObjs.end(); it++)
      vPfUpdates[*it] = true;
  state = PfState::mspf;
  int count = 0;
  for(list<int>::reverse_iterator it = vObjs.rbegin(); it != vObjs.rend();) {
    if(vvFos[*it].empty()) {
      if(nVerbose > 3)
        cout << "\t\t\tRemove unused " << *it << endl;
      count += Remove(*it);
      it = list<int>::reverse_iterator(vObjs.erase(--(it.base())));
      continue;
    }
    if(!vFoConeShared[*it] && !vPfUpdates[*it] && (vvFos[*it].size() == 1 || !IsFoConeShared(*it))) {
      it++;
      continue;
    }
    if(nVerbose > 3)
      cout << "\t\t\tMspf " << *it << endl;
    if(vvFos[*it].size() == 1 || !IsFoConeShared(*it)) {
      if(vFoConeShared[*it]) {
        vFoConeShared[*it] = false;
        lit g = vGs[*it];
        IncRef(g);
        CalcG(*it);
        DecRef(g);
        if(g == vGs[*it] && !vPfUpdates[*it]) {
          it++;
          continue;
        }
      } else
        CalcG(*it);
    } else {
      vFoConeShared[*it] = true;
      if(!MspfCalcG(*it) && !vPfUpdates[*it]) {
        it++;
        continue;
      }
      bool IsConst1 = man->IsConst1(man->Or(vGs[*it], vFs[*it]));
      bool IsConst0 = IsConst1? false: man->IsConst1(man->Or(vGs[*it], man->LitNot(vFs[*it])));
      if(IsConst1 || IsConst0) {
        count += ReplaceByConst(*it, (int)IsConst1);
        vObjs.erase(--(it.base()));
        Build();
        it = vObjs.rbegin();
        continue;
      }
    }
    if(fSort && block != *it)
      SortFis(*it);
    if(int diff = (block == *it)? MspfCalcC(*it, block_i0): MspfCalcC(*it)) {
      count += diff;
      assert(!vvFis[*it].empty());
      if(vvFis[*it].size() == 1) {
        count += Replace(*it, vvFis[*it][0]);
        vObjs.erase(--(it.base()));
      }
      Build();
      it = vObjs.rbegin();
      continue;
    }
    vPfUpdates[*it] = false;
    it++;
  }
  assert(AllFalse(vUpdates));
  assert(AllFalse(vPfUpdates));
  if(fLevel)
    ComputeLevel();
  return count;
}

bool Transduction::MspfDebug() {
  vector<lit> vGsOld;
  CopyVec(vGsOld, vGs);
  vector<vector<lit> > vvCsOld;
  CopyVec(vvCsOld, vvCs);
  state = PfState::none;
  Mspf();
  bool r = vGsOld == vGs && vvCsOld == vvCs;
  DelVec(vGsOld);
  DelVec(vvCsOld);
  return r;
}
