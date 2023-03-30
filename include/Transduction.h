#ifndef TRANSDUCTION_H
#define TRANSDUCTION_H

#include <list>

#include <aig.hpp>
#include <NextBdd.h>

using namespace NextBdd;

#define Z 0 // TODO: fix this

enum class PfState {none, cspf, mspf};

class Transduction {
 public:
  void GenerateAig(aigman &aig) const;

  Transduction(aigman const &aig, int nVerbose, int nSortType);
  ~Transduction();
  bool BuildDebug();

  int  Cspf(bool fSortRemove = false, int block = -1, int block_i0 = -1);
  bool CspfDebug();

  int  Mspf(bool fSort = false, int block = -1, int block_i0 = -1);
  bool MspfDebug();

 private:
  int nVerbose;
  int nSortType;
  int nObjsAlloc;
  PfState state;
  std::vector<int> vPis;
  std::vector<int> vPos;
  std::list<int> vObjs;
  std::vector<std::vector<int> > vvFis;
  std::vector<std::vector<int> > vvFos;
  std::vector<lit> vFs;
  std::vector<lit> vGs;
  std::vector<std::vector<lit> > vvCs;
  std::vector<bool> vUpdates;
  std::vector<bool> vPfUpdates;
  std::vector<bool> vFoConeShared;
  std::vector<lit> vPoFs;
  Man * man;

  void SortObjs_rec(std::list<int>::iterator const &it);
  void Connect(int i, int f, bool fSort = false, bool fUpdate = true, lit c = Z);
  void Disconnect(int i, int i0, unsigned j, bool fUpdate = true, bool fPfUpdate = true);
  int  Remove(int i, bool fPfUpdate = true);
  unsigned FindFi(int i, int i0) const;
  int  Replace(int i, int f, bool fUpdate = true);
  int  ReplaceByConst(int i, bool c);
  void ImportAig(aigman const &aig);

  void Build(int i, std::vector<lit> &vFs_) const;
  void Build(bool fPfUpdate = true);
  void RemoveConstOutputs();
  bool CostCompare(int a, int b) const;
  bool SortFis(int i);

  int  RemoveRedundantFis(int i, int block_i0 = -1, unsigned j = 0);
  void CalcG(int i);
  int  CalcC(int i);

  bool IsFoConeShared_rec(std::vector<int> &vVisits, int i, int visitor) const;
  bool IsFoConeShared(int i) const;
  void BuildFoConeCompl(int i, std::vector<lit> &vPoFsCompl) const;
  bool MspfCalcG(int i);
  int  MspfCalcC(int i, int block_i0 = -1);

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
  inline void Update(lit &x, lit y) const {
    man->DecRef(x);
    x = y;
    man->IncRef(x);
  }
  inline void DelVec(std::vector<lit> &x) const {
    for(unsigned i = 0; i < x.size(); i++)
      man->DecRef(x[i]);
    x.clear();
  }
  inline void CopyVec(std::vector<lit> &x, std::vector<lit> const &y) const {
    DelVec(x);
    x = y;
    for(unsigned i = 0; i < x.size(); i++)
      man->IncRef(x[i]);
  }
  inline bool AllFalse(std::vector<bool> const &v) const {
    for(std::list<int>::const_iterator it = vObjs.begin(); it != vObjs.end(); it++)
      if(v[*it])
        return false;
    return true;
  }
  inline bool Verify() const {
    for(unsigned j = 0; j < vPos.size(); j++) {
      lit x = Xor(LitFi(vPos[j], 0), vPoFs[j]);
      man->IncRef(x);
      Update(x, man->And(x, man->LitNot(vvCs[vPos[j]][0])));
      man->DecRef(x);
      if(!man->IsConst0(x))
        return false;
    }
    return true;
  }
};

#endif
