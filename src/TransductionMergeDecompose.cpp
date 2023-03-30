#include <iostream>
#include <algorithm>
#include <cassert>

#include "Transduction.h"

using namespace std;

int Transduction::TrivialMergeOne(int i) {
  if(nVerbose > 3)
    cout << "\t\t\tTrivial merge " << i << endl;
  int count = 0;
  vector<int> vFisOld = vvFis[i];
  vector<lit> vCsOld = vvCs[i];
  vvFis[i].clear();
  vvCs[i].clear();
  for(unsigned j = 0; j < vFisOld.size(); j++) {
    int i0 = vFisOld[j] >> 1;
    int c0 = vFisOld[j] & 1;
    if(vvFis[i0].empty() || vvFos[i0].size() > 1 || c0) {
      if(nVerbose > 5)
        cout << "\t\t\t\t\tFanin " << j << " : " << i0 << "(" << c0 << ")" << endl;
      vvFis[i].push_back(vFisOld[j]);
      vvCs[i].push_back(vCsOld[j]);
      continue;
    }
    vPfUpdates[i] = vPfUpdates[i] | vPfUpdates[i0];
    vvFos[i0].erase(find(vvFos[i0].begin(), vvFos[i0].end(), i));
    count++;
    vector<int>::iterator itfi = vFisOld.begin() + j;
    vector<lit>::iterator itc = vCsOld.begin() + j;
    for(unsigned jj = 0; jj < vvFis[i0].size(); jj++) {
      int f = vvFis[i0][jj];
      vector<int>::iterator it = find(vvFis[i].begin(), vvFis[i].end(), f);
      if(it == vvFis[i].end()) {
        vvFos[f >> 1].push_back(i);
        itfi = vFisOld.insert(itfi, f);
        itc = vCsOld.insert(itc, vvCs[i0][jj]);
        man->IncRef(*itc);
        itfi++;
        itc++;
        count--;
      } else {
        assert(state == PfState::none);
      }
    }
    count += Remove(i0, false);
    vObjs.erase(find(vObjs.begin(), vObjs.end(), i0));
    vFisOld.erase(itfi);
    man->DecRef(*itc);
    vCsOld.erase(itc);
    j--;
  }
  return count;
}
int Transduction::TrivialMerge() {
  if(nVerbose > 2)
    cout << "\t\tTrivial merge" << endl;
  int count = 0;
  for(list<int>::reverse_iterator it = vObjs.rbegin(); it != vObjs.rend();) {
    count += TrivialMergeOne(*it);
    it++;
  }
  return count;
}

int Transduction::TrivialDecomposeOne(list<int>::iterator const &it, int &pos) {
  if(nVerbose > 3)
    cout << "\t\t\tTrivial decompose " << *it << endl;
  assert(vvFis[*it].size() > 2);
  int count = 2 - vvFis[*it].size();
  while(vvFis[*it].size() > 2) {
    int f0 = vvFis[*it].back();
    lit c0 = vvCs[*it].back();
    Disconnect(*it, f0 >> 1, vvFis[*it].size() - 1, false, false);
    int f1 = vvFis[*it].back();
    lit c1 = vvCs[*it].back();
    Disconnect(*it, f1 >> 1, vvFis[*it].size() - 1, false, false);
    NewGate(pos);
    Connect(pos, f1, false, false, c1);
    Connect(pos, f0, false, false, c0);
    if(!vPfUpdates[*it]) {
      if(state == PfState::cspf)
        Update(vGs[pos], vGs[*it]);
      else if(state == PfState::mspf) {
        lit x = man->Const1();
        for(unsigned j = 0; j < vvFis[*it].size(); j++)
          Update(x, man->And(x, LitFi(*it, j)));
        Update(vGs[pos], man->Or(man->LitNot(x), vGs[*it]));
        man->DecRef(x);
      }
    }
    Connect(*it, pos << 1, false, false, vGs[pos]);
    vObjs.insert(it, pos);
    Build(pos, vFs);
  }
  return count;
}
int Transduction::TrivialDecompose() {
  if(nVerbose > 2)
    cout << "\t\tTrivial decompose" << endl;
  int count = 0;
  int pos = vPis.size() + 1;
  for(list<int>::iterator it = vObjs.begin(); it != vObjs.end(); it++)
    if(vvFis[*it].size() > 2)
      count += TrivialDecomposeOne(it, pos);
  return count;
}
