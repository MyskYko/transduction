#include <iostream>
#include <algorithm>
#include <cassert>

#include "Transduction.h"

using namespace std;

void Transduction::SortObjs_rec(list<int>::iterator const &it) {
  for(unsigned j = 0; j < vvFis[*it].size(); j++) {
    int i0 = vvFis[*it][j] >> 1;
    if(!vvFis[i0].empty()) {
      list<int>::iterator it_i0 = find(it, vObjs.end(), i0);
      if(it_i0 != vObjs.end()) {
        if(nVerbose > 6)
          cout << "\t\t\t\t\t\tMove " << i0 << " before " << *it << endl;
        vObjs.erase(it_i0);
        it_i0 = vObjs.insert(it, i0);
        SortObjs_rec(it_i0);
      }
    }
  }
}

void Transduction::Connect(int i, int f, bool fSort, bool fUpdate, lit c) {
  int i0 = f >> 1;
  if(nVerbose > 5)
    cout << "\t\t\t\t\tConnect " << i0 << "(" << (f & 1) << ")" << " to " << i << endl;
  assert(find(vvFis[i].begin(), vvFis[i].end(), f) == vvFis[i].end());
  vvFis[i].push_back(f);
  vvFos[i0].push_back(i);
  if(fUpdate)
    vUpdates[i] = true;
  vvCs[i].push_back(c);
  if(fSort && !vvFos[i].empty() && !vvFis[i0].empty()) {
    list<int>::iterator it = find(vObjs.begin(), vObjs.end(), i);
    list<int>::iterator it_i0 = find(it, vObjs.end(), i0);
    if(it_i0 != vObjs.end()) {
      if(nVerbose > 6)
        cout << "\t\t\t\t\t\tMove " << i0 << " before " << *it << endl;
      vObjs.erase(it_i0);
      it_i0 = vObjs.insert(it, i0);
      SortObjs_rec(it_i0);
    }
  }
}

void Transduction::Disconnect(int i, int i0, unsigned j, bool fUpdate, bool fPfUpdate) {
  if(nVerbose > 5)
    cout << "\t\t\t\t\tDisconnect " << i0 << "(" << (vvFis[i][j] & 1) << ")" << " from " << i << endl;
  vvFos[i0].erase(find(vvFos[i0].begin(), vvFos[i0].end(), i));
  vvFis[i].erase(vvFis[i].begin() + j);
  man->DecRef(vvCs[i][j]);
  vvCs[i].erase(vvCs[i].begin() + j);
  if(fUpdate)
    vUpdates[i] = true;
  if(fPfUpdate)
    vPfUpdates[i0] = true;
}

int Transduction::Remove(int i, bool fPfUpdate) {
  if(nVerbose > 4)
    cout << "\t\t\t\tRemove " << i << endl;
  assert(vvFos[i].empty());
  for(unsigned j = 0; j < vvFis[i].size(); j++) {
    int i0 = vvFis[i][j] >> 1;
    vvFos[i0].erase(find(vvFos[i0].begin(), vvFos[i0].end(), i));
    if(fPfUpdate)
      vPfUpdates[i0] = true;
  }
  int count = vvFis[i].size();
  vvFis[i].clear();
  man->DecRef(vFs[i]);
  man->DecRef(vGs[i]);
  vFs[i] = vGs[i] = Z;
  DelVec(vvCs[i]);
  vUpdates[i] = vPfUpdates[i] = false;
  return count;
}

unsigned Transduction::FindFi(int i, int i0) const {
  for(unsigned j = 0; j < vvFis[i].size(); j++)
    if((vvFis[i][j] >> 1) == i0)
      return j;
  abort();
}
int Transduction::Replace(int i, int f, bool fUpdate) {
  if(nVerbose > 4)
    cout << "\t\t\t\tReplace " << i << " by " << (f >> 1) << "(" << (f & 1) << ")" << endl;
  assert(i != (f >> 1));
  int count = 0;
  for(unsigned j = 0; j < vvFos[i].size(); j++) {
    int k = vvFos[i][j];
    unsigned l = FindFi(k, i);
    int fc = f ^ (vvFis[k][l] & 1);
    if(find(vvFis[k].begin(), vvFis[k].end(), fc) != vvFis[k].end()) {
      vvCs[k].erase(vvCs[k].begin() + l);
      vvFis[k].erase(vvFis[k].begin() + l);
      count++;
    } else {
      vvFis[k][l] = f ^ (vvFis[k][l] & 1);
      vvFos[f >> 1].push_back(k);
    }
    if(fUpdate)
      vUpdates[k] = true;
  }
  vvFos[i].clear();
  vPfUpdates[f >> 1] = true;
  return count + Remove(i);
}

void Transduction::ImportAig(aigman const &aig) {
  if(nVerbose > 2)
    cout << "\t\tImport aig" << endl;
  nObjsAlloc = aig.nObjs + aig.nPos;
  vvFis.resize(nObjsAlloc);
  vvFos.resize(nObjsAlloc);
  vFs.resize(nObjsAlloc, Z);
  vGs.resize(nObjsAlloc, Z);
  vvCs.resize(nObjsAlloc);
  vUpdates.resize(nObjsAlloc);
  vPfUpdates.resize(nObjsAlloc);
  vector<int> v(aig.nObjs, -1);
  v[0] = 0;
  for(int i = 0; i < aig.nPis; i++) {
    vPis.push_back(i + 1);
    v[i + 1] = (i + 1) << 1;
  }
  for(int i = aig.nPis + 1; i < aig.nObjs; i++) {
    if(nVerbose > 3)
      cout << "\t\t\tImport node " << i << endl;
    if(aig.vObjs[i + i] == aig.vObjs[i + i + 1])
      v[i] = v[aig.vObjs[i + i] >> 1] ^ (aig.vObjs[i + i] & 1);
    else {
      for(int ii = i + i;  ii <= i + i + 1; ii++)
        Connect(i, v[aig.vObjs[ii] >> 1] ^ (aig.vObjs[ii] & 1));
      vObjs.push_back(i);
      v[i] = i << 1;
    }
  }
  for(int i = 0; i < aig.nPos; i++) {
    if(nVerbose > 3)
      cout << "\t\t\tImport po " << i << endl;
    vPos.push_back(i + aig.nObjs);
    Connect(vPos[i], v[aig.vPos[i] >> 1] ^ (aig.vPos[i] & 1));
  }
}

void Transduction::GenerateAig(aigman &aig) const {
  aig.clear();
  aig.nPis = vPis.size();
  aig.nObjs = aig.nPis + 1;
  aig.vObjs.resize(aig.nObjs * 2);
  vector<int> values(nObjsAlloc);
  for(int i = 0; i < aig.nPis; i++)
    values[i + 1] = (i + 1) << 1;
  for(list<int>::const_iterator it = vObjs.begin(); it != vObjs.end(); it++) {
    assert(vvFis[*it].size() > 1);
    int i0 = vvFis[*it][0] >> 1;
    int i1 = vvFis[*it][1] >> 1;
    int c0 = vvFis[*it][0] & 1;
    int c1 = vvFis[*it][1] & 1;
    int r = aig.newgate(values[i0] ^ c0, values[i1] ^ c1) << 1;
    for(unsigned i = 2; i < vvFis[*it].size(); i++) {
      int ii = vvFis[*it][i] >> 1;
      int ci = vvFis[*it][i] & 1;
      r = aig.newgate(r, values[ii] ^ ci) << 1;
    }
    values[*it] = r;
  }
  for(unsigned i = 0; i < vPos.size(); i++) {
    int i0 = vvFis[vPos[i]][0] >> 1;
    int c0 = vvFis[vPos[i]][0] & 1;
    aig.vPos.push_back(values[i0] ^ c0);
    aig.nPos++;
  }
}
