#ifndef TRANSDUCTION_H
#define TRANSDUCTION_H

#include <list>
#include <set>
#include <algorithm>

#include <cassert>

#include <aig.hpp>
// #include <NextBdd.h>
// using namespace NextBdd;
#include "ttman.h"
using namespace Ttman;

enum class PfState {none, cspf, mspf};

class ManUtil {
protected:
  Man *man;
  inline void IncRef(lit x) const {
    if(x != LitMax())
      man->IncRef(x);
  }
  inline void DecRef(lit x) const {
    if(x != LitMax())
      man->DecRef(x);
  }
  inline void Update(lit &x, lit y) const {
    DecRef(x);
    x = y;
    IncRef(x);
  }
  inline void DelVec(std::vector<lit> &v) const {
    for(unsigned i = 0; i < v.size(); i++)
      DecRef(v[i]);
    v.clear();
  }
  inline void DelVec(std::vector<std::vector<lit> > &v) const {
    for(unsigned i = 0; i < v.size(); i++)
      DelVec(v[i]);
    v.clear();
  }
  inline void CopyVec(std::vector<lit> &v, std::vector<lit> const &u) const {
    DelVec(v);
    v = u;
    for(unsigned i = 0; i < v.size(); i++)
      IncRef(v[i]);
  }
  inline void CopyVec(std::vector<std::vector<lit> > &v, std::vector<std::vector<lit> > const &u) const {
    for(unsigned i = u.size(); i < v.size(); i++)
      DelVec(v[i]);
    v.resize(u.size());
    for(unsigned i = 0; i < v.size(); i++)
      CopyVec(v[i], u[i]);
  }
  inline bool LitVecIsEq(std::vector<lit> const &v, std::vector<lit> const &u) const {
    if(v.size() != u.size())
      return false;
    for(unsigned i = 0; i < v.size(); i++)
      if(!man->LitIsEq(v[i], u[i]))
        return false;
    return true;
  }
  inline bool LitVecIsEq(std::vector<std::vector<lit> > const &v, std::vector<std::vector<lit> > const &u) const {
    if(v.size() != u.size())
      return false;
    for(unsigned i = 0; i < v.size(); i++)
      if(!LitVecIsEq(v[i], u[i]))
        return false;
    return true;
  }
  inline lit Xor(lit x, lit y) const {
    lit f = man->And(x, man->LitNot(y));
    man->IncRef(f);
    lit g = man->And(man->LitNot(x), y);
    man->IncRef(g);
    lit r = man->Or(f, g);
    man->DecRef(f);
    man->DecRef(g);
    return r;
  }
};

class TransductionBackup: ManUtil {
private:
  int nObjsAlloc;
  PfState state;
  std::list<int> vObjs;
  std::vector<std::vector<int> > vvFis;
  std::vector<std::vector<int> > vvFos;
  std::vector<int> vLevels;
  std::vector<int> vSlacks;
  std::vector<std::vector<int> > vvFiSlacks;
  std::vector<lit> vFs;
  std::vector<lit> vGs;
  std::vector<std::vector<lit> > vvCs;
  std::vector<bool> vUpdates;
  std::vector<bool> vPfUpdates;
  std::vector<bool> vFoConeShared;
  friend class Transduction;

public:
  ~TransductionBackup() {
    if(man) {
      DelVec(vFs);
      DelVec(vGs);
      DelVec(vvCs);
    }
  }
};

class Transduction: ManUtil {
private:
  int  nVerbose;
  int  nSortType;
  bool fLevel;
  int  nObjsAlloc;
  int  nMaxLevels;
  PfState state;
  std::vector<int> vPis;
  std::vector<int> vPos;
  std::list<int> vObjs;
  std::vector<std::vector<int> > vvFis;
  std::vector<std::vector<int> > vvFos;
  std::vector<int> vLevels;
  std::vector<int> vSlacks;
  std::vector<std::vector<int> > vvFiSlacks;
  std::vector<lit> vFs;
  std::vector<lit> vGs;
  std::vector<std::vector<lit> > vvCs;
  std::vector<bool> vUpdates;
  std::vector<bool> vPfUpdates;
  std::vector<bool> vFoConeShared;
  std::vector<lit> vPoFs;

private: // Helper functions
  inline bool AllFalse(std::vector<bool> const &v) const {
    for(std::list<int>::const_iterator it = vObjs.begin(); it != vObjs.end(); it++)
      if(v[*it])
        return false;
    return true;
  }

public: // Counting
  inline int CountGates() const {
    return vObjs.size();
  }
  inline int CountWires() const {
    int count = 0;
    for(std::list<int>::const_iterator it = vObjs.begin(); it != vObjs.end(); it++)
      count += vvFis[*it].size();
    return count;
  }
  inline int CountNodes() const {
    return CountWires() - CountGates();
  }
  inline int CountLevels() const {
    int count = 0;
    for(unsigned i = 0; i < vPos.size(); i++)
      count = std::max(count, vLevels[vvFis[vPos[i]][0] >> 1]);
    return count;
  }

private: // MIAIG
  void SortObjs_rec(std::list<int>::iterator const &it) {
    for(unsigned j = 0; j < vvFis[*it].size(); j++) {
      int i0 = vvFis[*it][j] >> 1;
      if(!vvFis[i0].empty()) {
        std::list<int>::iterator it_i0 = std::find(it, vObjs.end(), i0);
        if(it_i0 != vObjs.end()) {
          if(nVerbose > 6)
            std::cout << "\t\t\t\t\t\tMove " << i0 << " before " << *it << std::endl;
          vObjs.erase(it_i0);
          it_i0 = vObjs.insert(it, i0);
          SortObjs_rec(it_i0);
        }
      }
    }
  }
  inline void Connect(int i, int f, bool fSort = false, bool fUpdate = true, lit c = LitMax()) {
    int i0 = f >> 1;
    if(nVerbose > 5)
      std::cout << "\t\t\t\t\tConnect " << i0 << "(" << (f & 1) << ")" << " to " << i << std::endl;
    assert(std::find(vvFis[i].begin(), vvFis[i].end(), f) == vvFis[i].end());
    vvFis[i].push_back(f);
    vvFos[i0].push_back(i);
    if(fUpdate)
      vUpdates[i] = true;
    IncRef(c);
    vvCs[i].push_back(c);
    if(fSort && !vvFos[i].empty() && !vvFis[i0].empty()) {
      std::list<int>::iterator it = find(vObjs.begin(), vObjs.end(), i);
      std::list<int>::iterator it_i0 = find(it, vObjs.end(), i0);
      if(it_i0 != vObjs.end()) {
        if(nVerbose > 6)
          std::cout << "\t\t\t\t\t\tMove " << i0 << " before " << *it << std::endl;
        vObjs.erase(it_i0);
        it_i0 = vObjs.insert(it, i0);
        SortObjs_rec(it_i0);
      }
    }
  }
  inline void Disconnect(int i, int i0, unsigned j, bool fUpdate = true, bool fPfUpdate = true) {
    if(nVerbose > 5)
      std::cout << "\t\t\t\t\tDisconnect " << i0 << "(" << (vvFis[i][j] & 1) << ")" << " from " << i << std::endl;
    vvFos[i0].erase(std::find(vvFos[i0].begin(), vvFos[i0].end(), i));
    vvFis[i].erase(vvFis[i].begin() + j);
    DecRef(vvCs[i][j]);
    vvCs[i].erase(vvCs[i].begin() + j);
    if(fUpdate)
      vUpdates[i] = true;
    if(fPfUpdate)
      vPfUpdates[i0] = true;
  }
  inline int Remove(int i, bool fPfUpdate = true) {
    if(nVerbose > 4)
      std::cout << "\t\t\t\tRemove " << i << std::endl;
    assert(vvFos[i].empty());
    for(unsigned j = 0; j < vvFis[i].size(); j++) {
      int i0 = vvFis[i][j] >> 1;
      vvFos[i0].erase(std::find(vvFos[i0].begin(), vvFos[i0].end(), i));
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
  inline int FindFi(int i, int i0) const {
    for(unsigned j = 0; j < vvFis[i].size(); j++)
      if((vvFis[i][j] >> 1) == i0)
        return j;
    return -1;
  }
  inline int Replace(int i, int f, bool fUpdate = true) {
    if(nVerbose > 4)
      std::cout << "\t\t\t\tReplace " << i << " by " << (f >> 1) << "(" << (f & 1) << ")" << std::endl;
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
  int ReplaceByConst(int i, bool c) {
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
  inline void NewGate(int &pos) {
    while(pos != nObjsAlloc && (!vvFis[pos].empty() || !vvFos[pos].empty()))
      pos++;
    if(nVerbose > 4)
      std::cout << "\t\t\t\tCreate " << pos << std::endl;
    if(pos == nObjsAlloc) {
      nObjsAlloc++;
      vvFis.resize(nObjsAlloc);
      vvFos.resize(nObjsAlloc);
      if(fLevel) {
        vLevels.resize(nObjsAlloc);
        vSlacks.resize(nObjsAlloc);
        vvFiSlacks.resize(nObjsAlloc);
      }
      vFs.resize(nObjsAlloc, LitMax());
      vGs.resize(nObjsAlloc, LitMax());
      vvCs.resize(nObjsAlloc);
      vUpdates.resize(nObjsAlloc);
      vPfUpdates.resize(nObjsAlloc);
    }
  }
  void MarkFiCone_rec(std::vector<bool> &vMarks, int i) const {
    if(vMarks[i])
      return;
    vMarks[i] = true;
    for(unsigned j = 0; j < vvFis[i].size(); j++)
      MarkFiCone_rec(vMarks, vvFis[i][j] >> 1);
  }
  void MarkFoCone_rec(std::vector<bool> &vMarks, int i) const {
    if(vMarks[i])
      return;
    vMarks[i] = true;
    for(unsigned j = 0; j < vvFos[i].size(); j++)
      MarkFoCone_rec(vMarks, vvFos[i][j]);
  }
  bool IsFoConeShared_rec(std::vector<int> &vVisits, int i, int visitor) const {
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
  inline bool IsFoConeShared(int i) const {
    std::vector<int> vVisits(nObjsAlloc);
    for(unsigned j = 0; j < vvFos[i].size(); j++)
      if(IsFoConeShared_rec(vVisits, vvFos[i][j], j + 1))
        return true;
    return false;
  }

private: // Level calculation
  inline void add(std::vector<bool> &a, unsigned i) {
    if(a.size() <= i) {
      a.resize(i + 1);
      a[i] = true;
      return;
    }
    for(; i < a.size() && a[i]; i++)
      a[i] = false;
    if(i == a.size())
      a.resize(i + 1);
    a[i] = true;
  }
  inline bool balanced(std::vector<bool> const &a) {
    for(unsigned i = 0; i < a.size() - 1; i++)
      if(a[i])
        return false;
    return true;
  }
  inline bool noexcess(std::vector<bool> const &a, unsigned i) {
    if(a.size() <= i)
      return false;
    for(unsigned j = i; j < a.size(); j++)
      if(!a[j])
        return true;
    for(unsigned j = 0; j < i; j++)
      if(a[j])
        return false;
    return true;
  }
  inline void ComputeLevel() {
    for(std::list<int>::iterator it = vObjs.begin(); it != vObjs.end(); it++) {
      if(vvFis[*it].size() == 2)
        vLevels[*it] = std::max(vLevels[vvFis[*it][0] >> 1], vLevels[vvFis[*it][1] >> 1]) + 1;
      else {
        std::vector<bool> lev;
        for(unsigned j = 0; j < vvFis[*it].size(); j++)
          add(lev, vLevels[vvFis[*it][j] >> 1]);
        if(balanced(lev))
          vLevels[*it] = (int)lev.size() - 1;
        else
          vLevels[*it] = (int)lev.size();
      }
    }
    if(nMaxLevels == -1)
      nMaxLevels = CountLevels();
    for(unsigned i = 0; i < vPos.size(); i++) {
      vvFiSlacks[vPos[i]].resize(1);
      vvFiSlacks[vPos[i]][0] = nMaxLevels - vLevels[vvFis[vPos[i]][0] >> 1];
    }
    for(std::list<int>::reverse_iterator it = vObjs.rbegin(); it != vObjs.rend(); it++) {
      vSlacks[*it] = nMaxLevels;
      for(unsigned j = 0; j < vvFos[*it].size(); j++) {
        int k = vvFos[*it][j];
        int l = FindFi(k, *it);
        assert(l >= 0);
        vSlacks[*it] = std::min(vSlacks[*it], vvFiSlacks[k][l]);
      }
      vvFiSlacks[*it].resize(vvFis[*it].size());
      for(unsigned j = 0; j < vvFis[*it].size(); j++)
        vvFiSlacks[*it][j] = vSlacks[*it] + vLevels[*it] - 1 - vLevels[vvFis[*it][j] >> 1];
    }
  }

private: // Cost function
  inline void ShufflePis(int seed) {
    srand(seed);
    for(int i = (int)vPis.size() - 1; i > 0; i--)
      std::swap(vPis[i], vPis[rand() % (i + 1)]);
  }
  inline bool CostCompare(int a, int b) const { // return (cost(a) > cost(b))
    int a0 = a >> 1;
    int b0 = b >> 1;
    if(vvFis[a0].empty() && vvFis[b0].empty())
      return std::find(find(vPis.begin(), vPis.end(), a0), vPis.end(), b0) != vPis.end();
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
      return std::find(find(vObjs.begin(), vObjs.end(), a0), vObjs.end(), b0) == vObjs.end();
    case 1:
      return man->OneCount(man->LitNotCond(vFs[a0], ac)) < man->OneCount(man->LitNotCond(vFs[b0], bc));
    case 2:
      return man->OneCount(vFs[a0]) < man->OneCount(vFs[b0]);
    case 3:
      return man->OneCount(man->LitNot(vFs[a0])) < man->OneCount(vFs[b0]); // pseudo random
    default:
      return false; // no sorting
    }
  }
  inline bool SortFis(int i) {
    if(nVerbose > 4)
      std::cout << "\t\t\t\tSort fanins " << i << std::endl;
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
        std::cout << "\t\t\t\t\tFanin " << j << " : " << (vvFis[i][j] >> 1) << "(" << (vvFis[i][j] & 1) << ")" << std::endl;
    return fSort;
  }

private: // Symbolic simulation
  inline lit LitFi(int i, int j) const {
    int i0 = vvFis[i][j] >> 1;
    bool c0 = vvFis[i][j] & 1;
    return man->LitNotCond(vFs[i0], c0);
  }
  inline lit LitFi(int i, int j, std::vector<lit> const &vFs_) const {
    int i0 = vvFis[i][j] >> 1;
    bool c0 = vvFis[i][j] & 1;
    return man->LitNotCond(vFs_[i0], c0);
  }
  inline void Build(int i, std::vector<lit> &vFs_) const {
    if(nVerbose > 4)
      std::cout << "\t\t\t\tBuild " << i << std::endl;
    Update(vFs_[i], man->Const1());
    for(unsigned j = 0; j < vvFis[i].size(); j++)
      Update(vFs_[i], man->And(vFs_[i], LitFi(i, j, vFs_)));
  }
  inline void Build(bool fPfUpdate = true) {
    if(nVerbose > 3)
      std::cout << "\t\t\tBuild" << std::endl;
    for(std::list<int>::iterator it = vObjs.begin(); it != vObjs.end(); it++)
      if(vUpdates[*it]) {
        lit x = vFs[*it];
        IncRef(x);
        Build(*it, vFs);
        DecRef(x);
        if(!man->LitIsEq(x, vFs[*it]))
          for(unsigned j = 0; j < vvFos[*it].size(); j++)
            vUpdates[vvFos[*it][j]] = true;
      }
    if(fPfUpdate)
      for(std::list<int>::iterator it = vObjs.begin(); it != vObjs.end(); it++)
        vPfUpdates[*it] = vPfUpdates[*it] || vUpdates[*it];
    for(std::list<int>::iterator it = vObjs.begin(); it != vObjs.end(); it++)
      vUpdates[*it] = false;
    assert(AllFalse(vUpdates));
  }
  void BuildFoConeCompl(int i, std::vector<lit> &vPoFsCompl) const {
    if(nVerbose > 3)
      std::cout << "\t\t\tBuild with complemented " << i << std::endl;
    std::vector<lit> vFsCompl;
    CopyVec(vFsCompl, vFs);
    vFsCompl[i] = man->LitNot(vFs[i]);
    std::vector<bool> vUpdatesCompl(nObjsAlloc);
    for(unsigned j = 0; j < vvFos[i].size(); j++)
      vUpdatesCompl[vvFos[i][j]] = true;
    for(std::list<int>::const_iterator it = vObjs.begin(); it != vObjs.end(); it++)
      if(vUpdatesCompl[*it]) {
        Build(*it, vFsCompl);
        if(!man->LitIsEq(vFsCompl[*it], vFs[*it]))
          for(unsigned j = 0; j < vvFos[*it].size(); j++)
            vUpdatesCompl[vvFos[*it][j]] = true;
      }
    for(unsigned j = 0; j < vPos.size(); j++)
      Update(vPoFsCompl[j], LitFi(vPos[j], 0, vFsCompl));
    DelVec(vFsCompl);
  }

private: // CSPF
  inline int RemoveRedundantFis(int i, int block_i0 = -1, unsigned j = 0) {
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
          std::cout << "\t\t\t\tRRF remove wire " << i0 << "(" << (vvFis[i][j] & 1) << ")" << " -> " << i << std::endl;
        Disconnect(i, i0, j--);
        count++;
      }
    }
    return count;
  }
  inline void CalcG(int i) {
    Update(vGs[i], man->Const1());
    for(unsigned j = 0; j < vvFos[i].size(); j++) {
      int k = vvFos[i][j];
      int l = FindFi(k, i);
      assert(l >= 0);
      Update(vGs[i], man->And(vGs[i], vvCs[k][l]));
    }
  }
  inline int CalcC(int i) {
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
          std::cout << "\t\t\t\tCspf remove wire " << i0 << "(" << (vvFis[i][j] & 1) << ")" << " -> " << i << std::endl;
        Disconnect(i, i0, j--);
        count++;
      } else if(!man->LitIsEq(vvCs[i][j], x)) {
        Update(vvCs[i][j], x);
        vPfUpdates[i0] = true;
      }
      DecRef(x);
    }
    return count;
  }
  int Cspf(bool fSortRemove, int block = -1, int block_i0 = -1) {
    if(nVerbose > 2) {
      std::cout << "\t\tCspf";
      if(block_i0 != -1)
        std::cout << " (block " << block_i0 << " -> " << block << ")";
      else if(block != -1)
        std::cout << " (block " << block << ")";
      std::cout << std::endl;
    }
    if(state != PfState::cspf)
      for(std::list<int>::iterator it = vObjs.begin(); it != vObjs.end(); it++)
        vPfUpdates[*it] = true;
    state = PfState::cspf;
    int count = 0;
    for(std::list<int>::reverse_iterator it = vObjs.rbegin(); it != vObjs.rend();) {
      if(vvFos[*it].empty()) {
        if(nVerbose > 3)
          std::cout << "\t\t\tRemove unused " << *it << std::endl;
        count += Remove(*it);
        it = std::list<int>::reverse_iterator(vObjs.erase(--(it.base())));
        continue;
      }
      if(!vPfUpdates[*it]) {
        it++;
        continue;
      }
      if(nVerbose > 3)
        std::cout << "\t\t\tCspf " << *it << std::endl;
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
        it = std::list<int>::reverse_iterator(vObjs.erase(--(it.base())));
        continue;
      }
      it++;
    }
    Build(false);
    assert(AllFalse(vPfUpdates));
    if(fLevel)
      ComputeLevel();
    return count;
  }

private: // MSPF
  inline bool MspfCalcG(int i) {
    lit g = vGs[i];
    IncRef(g);
    std::vector<lit> vPoFsCompl(vPos.size(), LitMax());
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
    return !man->LitIsEq(vGs[i], g);
  }
  inline int MspfCalcC(int i, int block_i0 = -1) {
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
          std::cout << "\t\t\t\tMspf remove wire " << i0 << "(" << (vvFis[i][j] & 1) << ")" << " -> " << i << std::endl;
        Disconnect(i, i0, j);
        DecRef(x);
        return RemoveRedundantFis(i, block_i0, j) + 1;
      } else if(!man->LitIsEq(vvCs[i][j], x)) {
        Update(vvCs[i][j], x);
        vPfUpdates[i0] = true;
      }
      DecRef(x);
    }
    return 0;
  }
  int Mspf(bool fSort, int block = -1, int block_i0 = -1) {
    if(nVerbose > 2) {
      std::cout << "\t\tMspf";
      if(block_i0 != -1)
        std::cout << " (block " << block_i0 << " -> " << block << ")";
      else if(block != -1)
        std::cout << " (block " << block << ")";
      std::cout << std::endl;
    }
    assert(AllFalse(vUpdates));
    vFoConeShared.resize(nObjsAlloc);
    if(state != PfState::mspf)
      for(std::list<int>::iterator it = vObjs.begin(); it != vObjs.end(); it++)
        vPfUpdates[*it] = true;
    state = PfState::mspf;
    int count = 0;
    for(std::list<int>::reverse_iterator it = vObjs.rbegin(); it != vObjs.rend();) {
      if(vvFos[*it].empty()) {
        if(nVerbose > 3)
          std::cout << "\t\t\tRemove unused " << *it << std::endl;
        count += Remove(*it);
        it = std::list<int>::reverse_iterator(vObjs.erase(--(it.base())));
        continue;
      }
      if(!vFoConeShared[*it] && !vPfUpdates[*it] && (vvFos[*it].size() == 1 || !IsFoConeShared(*it))) {
        it++;
        continue;
      }
      if(nVerbose > 3)
        std::cout << "\t\t\tMspf " << *it << std::endl;
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

private: // Merge/decompose one
  inline int TrivialMergeOne(int i) {
    if(nVerbose > 3)
      std::cout << "\t\t\tTrivial merge " << i << std::endl;
    int count = 0;
    std::vector<int> vFisOld = vvFis[i];
    std::vector<lit> vCsOld = vvCs[i];
    vvFis[i].clear();
    vvCs[i].clear();
    for(unsigned j = 0; j < vFisOld.size(); j++) {
      int i0 = vFisOld[j] >> 1;
      int c0 = vFisOld[j] & 1;
      if(vvFis[i0].empty() || vvFos[i0].size() > 1 || c0) {
        if(nVerbose > 5)
          std::cout << "\t\t\t\t\tFanin " << j << " : " << i0 << "(" << c0 << ")" << std::endl;
        vvFis[i].push_back(vFisOld[j]);
        vvCs[i].push_back(vCsOld[j]);
        continue;
      }
      vPfUpdates[i] = vPfUpdates[i] | vPfUpdates[i0];
      vvFos[i0].erase(find(vvFos[i0].begin(), vvFos[i0].end(), i));
      count++;
      std::vector<int>::iterator itfi = vFisOld.begin() + j;
      std::vector<lit>::iterator itc = vCsOld.begin() + j;
      for(unsigned jj = 0; jj < vvFis[i0].size(); jj++) {
        int f = vvFis[i0][jj];
        std::vector<int>::iterator it = find(vvFis[i].begin(), vvFis[i].end(), f);
        if(it == vvFis[i].end()) {
          vvFos[f >> 1].push_back(i);
          itfi = vFisOld.insert(itfi, f);
          itc = vCsOld.insert(itc, vvCs[i0][jj]);
          IncRef(*itc);
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
      DecRef(*itc);
      vCsOld.erase(itc);
      j--;
    }
    return count;
  }
  inline int TrivialDecomposeOne(std::list<int>::iterator const &it, int &pos) {
    if(nVerbose > 3)
      std::cout << "\t\t\tTrivial decompose " << *it << std::endl;
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
          IncRef(x);
          for(unsigned j = 0; j < vvFis[*it].size(); j++)
            Update(x, man->And(x, LitFi(*it, j)));
          Update(vGs[pos], man->Or(man->LitNot(x), vGs[*it]));
          DecRef(x);
        }
      }
      Connect(*it, pos << 1, false, false, vGs[pos]);
      vObjs.insert(it, pos);
      Build(pos, vFs);
    }
    return count;
  }
  inline int BalancedDecomposeOne(std::list<int>::iterator const &it, int &pos) {
    if(nVerbose > 3)
      std::cout << "\t\t\tBalanced decompose " << *it << std::endl;
    assert(fLevel);
    assert(vvFis[*it].size() > 2);
    for(int p = 1; p < (int)vvFis[*it].size(); p++) {
      int f = vvFis[*it][p];
      lit c = vvCs[*it][p];
      int q = p - 1;
      for(; q >= 0 && vLevels[f >> 1] > vLevels[vvFis[*it][q] >> 1]; q--) {
        vvFis[*it][q + 1] = vvFis[*it][q];
        vvCs[*it][q + 1] = vvCs[*it][q];
      }
      if(q + 1 != p) {
        vvFis[*it][q + 1] = f;
        vvCs[*it][q + 1] = c;
      }
    }
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
      Connect(*it, pos << 1, false, false);
      Build(pos, vFs);
      vLevels[pos] = std::max(vLevels[f0 >> 1], vLevels[f1 >> 1]) + 1;
      vObjs.insert(it, pos);
      int f = vvFis[*it].back();
      lit c = vvCs[*it].back();
      int q = (int)vvFis[*it].size() - 2;
      for(; q >= 0 && vLevels[f >> 1] > vLevels[vvFis[*it][q] >> 1]; q--) {
        vvFis[*it][q + 1] = vvFis[*it][q];
        vvCs[*it][q + 1] = vvCs[*it][q];
      }
      if(q + 1 != (int)vvFis[*it].size() - 1) {
        vvFis[*it][q + 1] = f;
        vvCs[*it][q + 1] = c;
      }
    }
    vPfUpdates[*it] = true;
    return count;
  }

public: // Merge/decompose
  int TrivialMerge() {
    if(nVerbose > 2)
      std::cout << "\t\tTrivial merge" << std::endl;
    int count = 0;
    for(std::list<int>::reverse_iterator it = vObjs.rbegin(); it != vObjs.rend();) {
      count += TrivialMergeOne(*it);
      it++;
    }
    return count;
  }
  int TrivialDecompose() {
    if(nVerbose > 2)
      std::cout << "\t\tTrivial decompose" << std::endl;
    int count = 0;
    int pos = vPis.size() + 1;
    for(std::list<int>::iterator it = vObjs.begin(); it != vObjs.end(); it++)
      if(vvFis[*it].size() > 2)
        count += TrivialDecomposeOne(it, pos);
    return count;
  }
  int Decompose() {
    if(nVerbose)
      std::cout << "Decompose" << std::endl;
    int count = 0;
    int pos = vPis.size() + 1;
    for(std::list<int>::iterator it = vObjs.begin(); it != vObjs.end(); it++) {
      std::set<int> s1(vvFis[*it].begin(), vvFis[*it].end());
      assert(s1.size() == vvFis[*it].size());
      std::list<int>::iterator it2 = it;
      for(it2++; it2 != vObjs.end(); it2++) {
        std::set<int> s2(vvFis[*it2].begin(), vvFis[*it2].end());
        std::set<int> s;
        std::set_intersection(s1.begin(), s1.end(), s2.begin(), s2.end(), inserter(s, s.begin()));
        if(s.size() > 1) {
          if(s == s1) {
            if(s == s2) {
              if(nVerbose > 1)
                std::cout << "\tReplace " << *it2 << " by " << *it << std::endl;
              count += Replace(*it2, *it << 1, false);
              it2 = vObjs.erase(it2);
              it2--;
            } else {
              if(nVerbose > 1)
                std::cout << "\tDecompose " << *it2 << " by " << *it << std::endl;
              for(std::set<int>::iterator it3 = s.begin(); it3 != s.end(); it3++) {
                unsigned j = find(vvFis[*it2].begin(), vvFis[*it2].end(), *it3) - vvFis[*it2].begin();
                Disconnect(*it2, *it3 >> 1, j, false);
              }
              count += s.size();
              if(std::find(vvFis[*it2].begin(), vvFis[*it2].end(), *it << 1) == vvFis[*it2].end()) {
                Connect(*it2, *it << 1, false, false);
                count--;
              }
              vPfUpdates[*it2] = true;
            }
            continue;
          }
          if(s == s2) {
            it = vObjs.insert(it, *it2);
            vObjs.erase(it2);
          } else {
            NewGate(pos);
            if(nVerbose > 1)
              std::cout << "\tCreate " << pos << " for intersection of " << *it << " and " << *it2  << std::endl;
            if(nVerbose > 2) {
              std::cout << "\t\tIntersection :";
              for(std::set<int>::iterator it3 = s.begin(); it3 != s.end(); it3++)
                std::cout << " " << (*it3 >> 1) << "(" << (*it3 & 1) << ")";
              std::cout << std::endl;
            }
            for(std::set<int>::iterator it3 = s.begin(); it3 != s.end(); it3++)
              Connect(pos, *it3, false, false);
            count -= s.size();
            it = vObjs.insert(it, pos);
            Build(pos, vFs);
            vPfUpdates[*it] = true;
          }
          s1 = s;
          it2 = it;
        }
      }
      if(vvFis[*it].size() > 2) {
        if(nVerbose > 1)
          std::cout << "\tTrivial decompose " << *it << std::endl;
        count += TrivialDecomposeOne(it, pos);
      }
    }
    return count;
  }

private: // Save/load
  inline void Save(TransductionBackup &b) const {
    b.man = man;
    b.nObjsAlloc = nObjsAlloc;
    b.state = state;
    b.vObjs = vObjs;
    b.vvFis = vvFis;
    b.vvFos = vvFos;
    b.vLevels = vLevels;
    b.vSlacks = vSlacks;
    b.vvFiSlacks = vvFiSlacks;
    CopyVec(b.vFs, vFs);
    CopyVec(b.vGs, vGs);
    CopyVec(b.vvCs, vvCs);
    b.vUpdates = vUpdates;
    b.vPfUpdates = vPfUpdates;
    b.vFoConeShared = vFoConeShared;
  }
  inline void Load(TransductionBackup const &b) {
    nObjsAlloc = b.nObjsAlloc;
    state = b.state;
    vObjs = b.vObjs;
    vvFis = b.vvFis;
    vvFos = b.vvFos;
    vLevels = b.vLevels;
    vSlacks = b.vSlacks;
    vvFiSlacks = b.vvFiSlacks;
    CopyVec(vFs, b.vFs);
    CopyVec(vGs, b.vGs);
    CopyVec(vvCs, b.vvCs);
    vUpdates = b.vUpdates;
    vPfUpdates = b.vPfUpdates;
    vFoConeShared = b.vFoConeShared;
  }

private: // Connectable condition
  inline bool TryConnect(int i, int i0, bool c0) {
    int f = (i0 << 1) ^ (int)c0;
    if(find(vvFis[i].begin(), vvFis[i].end(), f) == vvFis[i].end()) {
      lit x = man->Or(man->LitNot(vFs[i]), vGs[i]);
      IncRef(x);
      if(man->IsConst1(man->Or(x, man->LitNotCond(vFs[i0], c0)))) {
        DecRef(x);
        if(nVerbose > 3)
          std::cout << "\t\t\tConnect " << i0 << "(" << c0 << ")" << std::endl;
        Connect(i, f, true);
        return true;
      }
      DecRef(x);
    }
    return false;
  }

public: // Resubs
  int Resub(bool fMspf) {
    if(nVerbose)
      std::cout << "Resubstitution" << std::endl;
    int count = fMspf? Mspf(true): Cspf(true);
    int nodes = CountNodes();
    TransductionBackup b;
    Save(b);
    int count_ = count;
    std::list<int> targets = vObjs;
    for(std::list<int>::reverse_iterator it = targets.rbegin(); it != targets.rend(); it++) {
      if(nVerbose > 1)
        std::cout << "\tResubstitute " << *it << std::endl;
      if(vvFos[*it].empty())
        continue;
      count += TrivialMergeOne(*it);
      std::vector<bool> lev;
      if(fLevel) {
        for(unsigned j = 0; j < vvFis[*it].size(); j++)
          add(lev, vLevels[vvFis[*it][j] >> 1]);
        if((int)lev.size() > vLevels[*it] + vSlacks[*it]) {
          Load(b);
          count = count_;
          continue;
        }
        lev.resize(vLevels[*it] + vSlacks[*it]);
      }
      bool fConnect = false;
      std::vector<bool> vMarks(nObjsAlloc);
      MarkFoCone_rec(vMarks, *it);
      std::list<int> targets2 = vObjs;
      for(std::list<int>::iterator it2 = targets2.begin(); it2 != targets2.end(); it2++) {
        if(fLevel && (int)lev.size() > vLevels[*it] + vSlacks[*it])
          break;
        if(!vMarks[*it2] && !vvFos[*it2].empty())
          if(!fLevel || noexcess(lev, vLevels[*it2]))
            if(TryConnect(*it, *it2, false) || TryConnect(*it, *it2, true)) {
              fConnect = true;
              count--;
              if(fLevel)
                add(lev, vLevels[*it2]);
            }
      }
      if(fConnect) {
        if(fMspf) {
          Build();
          count += Mspf(true, *it);
        } else {
          vPfUpdates[*it] = true;
          count += Cspf(true, *it);
        }
        if(!vvFos[*it].empty()) {
          vPfUpdates[*it] = true;
          count += fMspf? Mspf(true): Cspf(true);
        }
      }
      if(nodes < CountNodes()) {
        Load(b);
        count = count_;
        continue;
      }
      if(!vvFos[*it].empty() && vvFis[*it].size() > 2) {
        std::list<int>::iterator it2 = find(vObjs.begin(), vObjs.end(), *it);
        int pos = nObjsAlloc;
        if(fLevel)
          count += BalancedDecomposeOne(it2, pos) + (fMspf? Mspf(true): Cspf(true));
        else
          count += TrivialDecomposeOne(it2, pos);
      }
      nodes = CountNodes();
      Save(b);
      count_ = count;
    }
    return count;
  }
  int ResubMono(bool fMspf) {
    if(nVerbose)
      std::cout << "Resubstitution mono" << std::endl;
    int count = fMspf? Mspf(true): Cspf(true);
    std::list<int> targets = vObjs;
    for(std::list<int>::reverse_iterator it = targets.rbegin(); it != targets.rend(); it++) {
      if(nVerbose > 1)
        std::cout << "\tResubstitute mono " << *it << std::endl;
      if(vvFos[*it].empty())
        continue;
      count += TrivialMergeOne(*it);
      TransductionBackup b;
      Save(b);
      int count_ = count;
      for(unsigned i = 0; i < vPis.size(); i++) {
        if(vvFos[*it].empty())
          break;
        if(TryConnect(*it, vPis[i], false) || TryConnect(*it, vPis[i], true)) {
          count--;
          int diff;
          if(fMspf) {
            Build();
            diff = Mspf(true, *it, vPis[i]);
          } else {
            vPfUpdates[*it] = true;
            diff = Cspf(true, *it, vPis[i]);
          }
          if(diff) {
            count += diff;
            if(!vvFos[*it].empty()) {
              vPfUpdates[*it] = true;
              count += fMspf? Mspf(true): Cspf(true);
            }
            if(fLevel && CountLevels() > nMaxLevels) {
              Load(b);
              count = count_;
            } else {
              Save(b);
              count_ = count;
            }
          } else {
            Load(b);
            count = count_;
          }
        }
      }
      if(vvFos[*it].empty())
        continue;
      std::vector<bool> vMarks(nObjsAlloc);
      MarkFoCone_rec(vMarks, *it);
      std::list<int> targets2 = vObjs;
      for(std::list<int>::iterator it2 = targets2.begin(); it2 != targets2.end(); it2++) {
        if(vvFos[*it].empty())
          break;
        if(!vMarks[*it2] && !vvFos[*it2].empty())
          if(TryConnect(*it, *it2, false) || TryConnect(*it, *it2, true)) {
            count--;
            int diff;
            if(fMspf) {
              Build();
              diff = Mspf(true, *it, *it2);
            } else {
              vPfUpdates[*it] = true;
              diff = Cspf(true, *it, *it2);
            }
            if(diff) {
              count += diff;
              if(!vvFos[*it].empty()) {
                vPfUpdates[*it] = true;
                count += fMspf? Mspf(true): Cspf(true);
              }
              if(fLevel && CountLevels() > nMaxLevels) {
                Load(b);
                count = count_;
              } else {
                Save(b);
                count_ = count;
              }
            } else {
              Load(b);
              count = count_;
            }
          }
      }
      if(vvFos[*it].empty())
        continue;
      if(vvFis[*it].size() > 2) {
        std::list<int>::iterator it2 = find(vObjs.begin(), vObjs.end(), *it);
        int pos = nObjsAlloc;
        if(fLevel)
          count += BalancedDecomposeOne(it2, pos) + (fMspf? Mspf(true): Cspf(true));
        else
          count += TrivialDecomposeOne(it2, pos);
      }
    }
    return count;
  }
  int ResubShared(bool fMspf) {
    if(nVerbose)
      std::cout << "Merge" << std::endl;
    int count = fMspf? Mspf(true): Cspf(true);
    std::list<int> targets = vObjs;
    for(std::list<int>::reverse_iterator it = targets.rbegin(); it != targets.rend(); it++) {
      if(nVerbose > 1)
        std::cout << "\tMerge " << *it << std::endl;
      if(vvFos[*it].empty())
        continue;
      count += TrivialMergeOne(*it);
      bool fConnect = false;
      for(unsigned i = 0; i < vPis.size(); i++)
        if(TryConnect(*it, vPis[i], false) || TryConnect(*it, vPis[i], true)) {
          fConnect |= true;
          count--;
        }
      std::vector<bool> vMarks(nObjsAlloc);
      MarkFoCone_rec(vMarks, *it);
      for(std::list<int>::iterator it2 = targets.begin(); it2 != targets.end(); it2++)
        if(!vMarks[*it2] && !vvFos[*it2].empty())
          if(TryConnect(*it, *it2, false) || TryConnect(*it, *it2, true)) {
            fConnect |= true;
            count--;
          }
      if(fConnect) {
        if(fMspf) {
          Build();
          count += Mspf(true, *it);
        } else {
          vPfUpdates[*it] = true;
          count += Cspf(true, *it);
        }
        if(!vvFos[*it].empty()) {
          vPfUpdates[*it] = true;
          count += fMspf? Mspf(true): Cspf(true);
        }
      }
    }
    return count + Decompose();
  }

public: // Optimization scripts
  int RepeatResub(bool fMono, bool fMspf) {
    int count = 0;
    while(int diff = fMono? ResubMono(fMspf): Resub(fMspf))
      count += diff;
    return count;
  }
  int RepeatResubInner(bool fMspf, bool fInner) {
    int count = 0;
    while(int diff = RepeatResub(true, fMspf) + RepeatResub(false, fMspf)) {
      count += diff;
      if(!fInner)
        break;
    }
    return count;
  }
  int RepeatResubOuter(bool fMspf, bool fInner, bool fOuter) {
    int count = 0;
    while(int diff = fMspf? RepeatResubInner(false, fInner) + RepeatResubInner(true, fInner): RepeatResubInner(false, fInner)) {
      count += diff;
      if(!fOuter)
        break;
    }
    return count;
  }
  int Optimize(bool fFirstMerge, bool fMspfMerge, bool fMspfResub, bool fInner, bool fOuter) {
    TransductionBackup b;
    Save(b);
    int count = 0;
    int diff = 0;
    if(fFirstMerge)
      diff = ResubShared(fMspfMerge);
    diff += RepeatResubOuter(fMspfResub, fInner, fOuter);
    if(diff > 0) {
      count = diff;
      Save(b);
      diff = 0;
    }
    while(true) {
      diff += ResubShared(fMspfMerge) + RepeatResubOuter(fMspfResub, fInner, fOuter);
      if(diff > 0) {
        count += diff;
        Save(b);
        diff = 0;
      } else {
        Load(b);
        break;
      }
    }
    return count;
  }

public: // Cspf/mspf
  int Cspf() {
    return Cspf(true);
  }
  int Mspf() {
    return Mspf(true);
  }

private: // Setup
  void ImportAig(aigman const &aig) {
    if(nVerbose > 2)
      std::cout << "\t\tImport aig" << std::endl;
    nObjsAlloc = aig.nObjs + aig.nPos;
    vvFis.resize(nObjsAlloc);
    vvFos.resize(nObjsAlloc);
    if(fLevel) {
      vLevels.resize(nObjsAlloc);
      vSlacks.resize(nObjsAlloc);
      vvFiSlacks.resize(nObjsAlloc);
    }
    vFs.resize(nObjsAlloc, LitMax());
    vGs.resize(nObjsAlloc, LitMax());
    vvCs.resize(nObjsAlloc);
    vUpdates.resize(nObjsAlloc);
    vPfUpdates.resize(nObjsAlloc);
    std::vector<int> v(aig.nObjs, -1);
    v[0] = 0;
    for(int i = 0; i < aig.nPis; i++) {
      vPis.push_back(i + 1);
      v[i + 1] = (i + 1) << 1;
    }
    for(int i = aig.nPis + 1; i < aig.nObjs; i++) {
      if(nVerbose > 3)
        std::cout << "\t\t\tImport node " << i << std::endl;
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
        std::cout << "\t\t\tImport po " << i << std::endl;
      vPos.push_back(i + aig.nObjs);
      Connect(vPos[i], v[aig.vPos[i] >> 1] ^ (aig.vPos[i] & 1));
    }
  }
  void RemoveConstOutputs() {
    bool fRemoved = false;
    for(unsigned i = 0; i < vPos.size(); i++) {
      int i0 = vvFis[vPos[i]][0] >> 1;
      lit c = vvCs[vPos[i]][0];
      if(i0) {
        if(man->IsConst1(man->Or(LitFi(vPos[i], 0), c))) {
          if(nVerbose > 3)
            std::cout << "\t\t\tConst 1 output : po " << i << std::endl;
          Disconnect(vPos[i], i0, 0, false, false);
          Connect(vPos[i], 1, false, false, c);
          fRemoved |= vvFos[i0].empty();
        } else if(man->IsConst1(man->Or(man->LitNot(LitFi(vPos[i], 0)), c))) {
          if(nVerbose > 3)
            std::cout << "\t\t\tConst 0 output : po " << i << std::endl;
          Disconnect(vPos[i], i0, 0, false, false);
          Connect(vPos[i], 0, false, false, c);
          fRemoved |= vvFos[i0].empty();
        }
      }
    }
    if(fRemoved) {
      if(nVerbose > 3)
        std::cout << "\t\t\tRemove unused" << std::endl;
      for(std::list<int>::reverse_iterator it = vObjs.rbegin(); it != vObjs.rend();) {
        if(vvFos[*it].empty()) {
          Remove(*it, false);
          it = std::list<int>::reverse_iterator(vObjs.erase(--(it.base())));
          continue;
        }
        it++;
      }
    }
  }

public: // Constructor
  Transduction(aigman const &aig, int nVerbose, int nSortType = 0, int nPiShuffle = 0, bool fLevel = false): nVerbose(nVerbose), nSortType(nSortType), fLevel(fLevel) {
    Param p;
    p.nGbc = 1;
    p.nReo = 4000;
    if(nSortType)
      p.fCountOnes = true;
    man = new Man(aig.nPis, p);
    ImportAig(aig);
    Update(vFs[0], man->Const0());
    for(unsigned i = 0; i < vPis.size(); i++)
      Update(vFs[i + 1], man->IthVar(i));
    nMaxLevels = -1;
    Build(false);
    man->Reorder();
    man->TurnOffReo();
    for(unsigned i = 0; i < vPos.size(); i++)
      Update(vvCs[vPos[i]][0], man->Const0());
    RemoveConstOutputs();
    vPoFs.resize(vPos.size(), LitMax());
    for(unsigned i = 0; i < vPos.size(); i++)
      Update(vPoFs[i], LitFi(vPos[i], 0));
    state = PfState::none;
    if(nPiShuffle)
      ShufflePis(nPiShuffle);
    if(fLevel)
      ComputeLevel();
  }
  ~Transduction() {
    DelVec(vFs);
    DelVec(vGs);
    DelVec(vvCs);
    DelVec(vPoFs);
    //assert(man->CountNodes() == (int)vPis.size() + 1);
    //assert(!man->Ref(man->Const0()));
    delete man;
  }

public:  // Output
  void GenerateAig(aigman &aig) const {
    aig.clear();
    aig.nPis = vPis.size();
    aig.nObjs = aig.nPis + 1;
    aig.vObjs.resize(aig.nObjs * 2);
    std::vector<int> values(nObjsAlloc);
    for(int i = 0; i < aig.nPis; i++)
      values[i + 1] = (i + 1) << 1;
    for(std::list<int>::const_iterator it = vObjs.begin(); it != vObjs.end(); it++) {
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

public: // Debug and print
  PfState State() const {
    return state;
  }
  bool BuildDebug() {
    for(std::list<int>::iterator it = vObjs.begin(); it != vObjs.end(); it++)
      vUpdates[*it] = true;
    std::vector<lit> vFsOld;
    CopyVec(vFsOld, vFs);
    Build(false);
    bool r = LitVecIsEq(vFsOld, vFs);
    DelVec(vFsOld);
    return r;
  }
  bool CspfDebug() {
    std::vector<lit> vGsOld;
    CopyVec(vGsOld, vGs);
    std::vector<std::vector<lit> > vvCsOld;
    CopyVec(vvCsOld, vvCs);
    state = PfState::none;
    Cspf(false);
    bool r = LitVecIsEq(vGsOld, vGs) && LitVecIsEq(vvCsOld, vvCs);
    DelVec(vGsOld);
    DelVec(vvCsOld);
    return r;
  }
  bool MspfDebug() {
    std::vector<lit> vGsOld;
    CopyVec(vGsOld, vGs);
    std::vector<std::vector<lit> > vvCsOld;
    CopyVec(vvCsOld, vvCs);
    state = PfState::none;
    Mspf(false);
    bool r = LitVecIsEq(vGsOld, vGs) && LitVecIsEq(vvCsOld, vvCs);
    DelVec(vGsOld);
    DelVec(vvCsOld);
    return r;
  }
  bool Verify() const {
    for(unsigned j = 0; j < vPos.size(); j++) {
      lit x = Xor(LitFi(vPos[j], 0), vPoFs[j]);
      IncRef(x);
      Update(x, man->And(x, man->LitNot(vvCs[vPos[j]][0])));
      DecRef(x);
      if(!man->IsConst0(x))
        return false;
    }
    return true;
  }
  void PrintStats() const {
    int gates = CountGates();
    int wires = CountWires();
    int nodes = wires - gates;
    std::cout << "nodes = " << std::setw(5) << nodes << ", "
              << "gates = " << std::setw(5) << gates << ", "
              << "wires = " << std::setw(5) << wires;
    if(fLevel)
      std::cout << ", level = " << std::setw(5) << CountLevels();
    std::cout << std::endl;
  }
  void PrintObjs() const {
    for(std::list<int>::const_iterator it = vObjs.begin(); it != vObjs.end(); it++) {
      std::cout << "Gate " << *it << ":";
      if(fLevel)
        std::cout << " Level = " << vLevels[*it] << ", Slack = " << vSlacks[*it];
      std::cout << std::endl;
      std::string delim = "";
      std::cout << "\tFis: ";
      for(unsigned j = 0; j < vvFis[*it].size(); j++) {
        std::cout << delim << (vvFis[*it][j] >> 1) << "(" << (vvFis[*it][j] & 1) << ")";
        delim = ", ";
      }
      std::cout << std::endl;
      delim = "";
      std::cout << "\tFos: ";
      for(unsigned j = 0; j < vvFos[*it].size(); j++) {
        std::cout << delim << vvFos[*it][j];
        delim = ", ";
      }
      std::cout << std::endl;
    }
  }
};

#endif
