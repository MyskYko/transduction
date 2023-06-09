#ifndef TRANSDUCTION_H
#define TRANSDUCTION_H

#include <list>

#include <aig.hpp>
#include <NextBdd.h>

using namespace NextBdd;

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
public:
  ~TransductionBackup() {
    if(man) {
      DelVec(vFs);
      DelVec(vGs);
      DelVec(vvCs);
    }
  }

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
};

class Transduction: ManUtil {
public:
  int  CountGates() const;
  int  CountWires() const;
  int  CountNodes() const;
  int  CountLevels() const;
  void GenerateAig(aigman &aig) const;

  Transduction(aigman const &aig, int nVerbose, int nSortType = 0, int nPiShuffle = 0, bool fLevel = false);
  ~Transduction();
  bool BuildDebug();

  int  Cspf(bool fSortRemove = false, int block = -1, int block_i0 = -1);
  bool CspfDebug();

  int  Mspf(bool fSort = false, int block = -1, int block_i0 = -1);
  bool MspfDebug();

  int TrivialMerge();
  int TrivialDecompose();
  int Decompose();

  int Resub(bool fMspf);
  int ResubMono(bool fMspf);
  int ResubShared(bool fMspf);

  int RepeatResub(bool fMono, bool fMspf);
  int RepeatResubInner(bool fMspf, bool fInner);
  int RepeatResubOuter(bool fMspf, bool fInner, bool fOuter);
  int Optimize(bool fFirstMerge, bool fMspfMerge, bool fMspfResub, bool fInner, bool fOuter);

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

  void SortObjs_rec(std::list<int>::iterator const &it);
  void Connect(int i, int f, bool fSort = false, bool fUpdate = true, lit c = LitMax());
  void Disconnect(int i, int i0, unsigned j, bool fUpdate = true, bool fPfUpdate = true);
  int  Remove(int i, bool fPfUpdate = true);
  int  FindFi(int i, int i0) const;
  int  Replace(int i, int f, bool fUpdate = true);
  int  ReplaceByConst(int i, bool c);
  void NewGate(int &pos);
  void MarkFiCone_rec(std::vector<bool> &vMarks, int i) const;
  void MarkFoCone_rec(std::vector<bool> &vMarks, int i) const;
  bool IsFoConeShared_rec(std::vector<int> &vVisits, int i, int visitor) const;
  bool IsFoConeShared(int i) const;
  void ImportAig(aigman const &aig);
  void ComputeLevel();

  void ShufflePis(int seed);
  void Build(int i, std::vector<lit> &vFs_) const;
  void Build(bool fPfUpdate = true);
  void RemoveConstOutputs();
  bool CostCompare(int a, int b) const;
  bool SortFis(int i);

  int  RemoveRedundantFis(int i, int block_i0 = -1, unsigned j = 0);
  void CalcG(int i);
  int  CalcC(int i);

  void BuildFoConeCompl(int i, std::vector<lit> &vPoFsCompl) const;
  bool MspfCalcG(int i);
  int  MspfCalcC(int i, int block_i0 = -1);

  int  TrivialMergeOne(int i);
  int  TrivialDecomposeOne(std::list<int>::iterator const &it, int &pos);
  int  BalancedDecomposeOne(std::list<int>::iterator const &it, int &pos);

  bool TryConnect(int i, int i0, bool c0);

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
  inline bool AllFalse(std::vector<bool> const &v) const {
    for(std::list<int>::const_iterator it = vObjs.begin(); it != vObjs.end(); it++)
      if(v[*it])
        return false;
    return true;
  }
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

public:
  inline PfState State() const {
    return state;
  }
  inline void PrintStats() const {
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
  inline bool Verify() const {
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
  inline void PrintObjs() const {
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
