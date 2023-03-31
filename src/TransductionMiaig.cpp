#include <iostream>
#include <algorithm>
#include <cassert>

#include "Transduction.h"

using namespace std;

int Transduction::CountGates() const {
  return vObjs.size();
}
int Transduction::CountWires() const {
  int count = 0;
  for(std::list<int>::const_iterator it = vObjs.begin(); it != vObjs.end(); it++)
    count += vvFis[*it].size();
  return count;
}
int Transduction::CountNodes() const {
  return CountWires() - CountGates();
}

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
  IncRef(c);
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
  DecRef(vvCs[i][j]);
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
  DecRef(vFs[i]);
  DecRef(vGs[i]);
  vFs[i] = vGs[i] = LitMax();
  DelVec(vvCs[i]);
  vUpdates[i] = vPfUpdates[i] = false;
  return count;
}

int Transduction::FindFi(int i, int i0) const {
  for(unsigned j = 0; j < vvFis[i].size(); j++)
    if((vvFis[i][j] >> 1) == i0)
      return j;
  return -1;
}
int Transduction::Replace(int i, int f, bool fUpdate) {
  if(nVerbose > 4)
    cout << "\t\t\t\tReplace " << i << " by " << (f >> 1) << "(" << (f & 1) << ")" << endl;
  assert(i != (f >> 1));
  int count = 0;
  for(unsigned j = 0; j < vvFos[i].size(); j++) {
    int k = vvFos[i][j];
    int l = FindFi(k, i);
    assert(l >= 0);
    int fc = f ^ (vvFis[k][l] & 1);
    if(find(vvFis[k].begin(), vvFis[k].end(), fc) != vvFis[k].end()) {
      DecRef(vvCs[k][l]);
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
int Transduction::ReplaceByConst(int i, bool c) {
  if(nVerbose > 4)
    std::cout << "\t\t\t\tReplace " << i << " by " << c << std::endl;
  int count = 0;
  for(unsigned j = 0; j < vvFos[i].size(); j++) {
    int k = vvFos[i][j];
    int l = FindFi(k, i);
    assert(l >= 0);
    bool fc = c ^ (vvFis[k][l] & 1);
    DecRef(vvCs[k][l]);
    vvCs[k].erase(vvCs[k].begin() + l);
    vvFis[k].erase(vvFis[k].begin() + l);
    if(fc) {
      if(vvFis[k].size() == 1)
        count += Replace(k, vvFis[k][0]);
      else
        vUpdates[k] = true;
    } else
      count += ReplaceByConst(k, 0);
  }
  count += vvFos[i].size();
  vvFos[i].clear();
  return count + Remove(i);
}

void Transduction::NewGate(int &pos) {
  while(pos != nObjsAlloc && (!vvFis[pos].empty() || !vvFos[pos].empty()))
    pos++;
  if(nVerbose > 4)
    std::cout << "\t\t\t\tCreate " << pos << std::endl;
  if(pos == nObjsAlloc) {
    nObjsAlloc++;
    vvFis.resize(nObjsAlloc);
    vvFos.resize(nObjsAlloc);
    vFs.resize(nObjsAlloc, LitMax());
    vGs.resize(nObjsAlloc, LitMax());
    vvCs.resize(nObjsAlloc);
    vUpdates.resize(nObjsAlloc);
    vPfUpdates.resize(nObjsAlloc);
  }
}

void Transduction::MarkFiCone_rec(vector<bool> &vMarks, int i) const {
  if(vMarks[i])
    return;
  vMarks[i] = true;
  for(unsigned j = 0; j < vvFis[i].size(); j++)
    MarkFiCone_rec(vMarks, vvFis[i][j] >> 1);
}
void Transduction::MarkFoCone_rec(vector<bool> &vMarks, int i) const {
  if(vMarks[i])
    return;
  vMarks[i] = true;
  for(unsigned j = 0; j < vvFos[i].size(); j++)
    MarkFoCone_rec(vMarks, vvFos[i][j]);
}

bool Transduction::IsFoConeShared_rec(vector<int> &vVisits, int i, int visitor) const {
  if(vVisits[i] == visitor)
    return false;
  if(vVisits[i])
    return true;
  vVisits[i] = visitor;
  for(unsigned j = 0; j < vvFos[i].size(); j++)
    if(IsFoConeShared_rec(vVisits, vvFos[i][j], visitor))
      return true;
  return false;
}
bool Transduction::IsFoConeShared(int i) const {
  vector<int> vVisits(nObjsAlloc);
  for(unsigned j = 0; j < vvFos[i].size(); j++)
    if(IsFoConeShared_rec(vVisits, vvFos[i][j], j + 1))
      return true;
  return false;
}

void Transduction::ImportAig(aigman const &aig) {
  if(nVerbose > 2)
    cout << "\t\tImport aig" << endl;
  nObjsAlloc = aig.nObjs + aig.nPos;
  vvFis.resize(nObjsAlloc);
  vvFos.resize(nObjsAlloc);
  vFs.resize(nObjsAlloc, LitMax());
  vGs.resize(nObjsAlloc, LitMax());
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
