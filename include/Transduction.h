#ifndef TRANSDUCTION_H
#define TRANSDUCTION_H

#include <list>

#include <aig.hpp>
#include <NextBdd.h>

using namespace NextBdd;

#define Z 0 // TODO: fix this

class Transduction {
 public:
  void GenerateAig(aigman &aig) const;

  Transduction(aigman const &aig, int nVerbose);
  ~Transduction();

 private:
  int nVerbose;
  int nObjsAlloc;
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
  std::vector<lit> vPoFs;
  Man * man;

  void SortObjs_rec(std::list<int>::iterator const &it);
  void Connect(int i, int f, bool fSort = false, bool fUpdate = true, lit c = Z);
  void Disconnect(int i, int i0, unsigned j, bool fUpdate = true, bool fPfUpdate = true);
  int  Remove(int i, bool fPfUpdate = true);
  void ImportAig(aigman const &aig);

  void Build(int i, std::vector<lit> &vFs_) const;
  void Build(bool fPfUpdate = true);
  bool BuildDebug();
  void RemoveConstOutputs();

  inline lit LitFanin(int i, int j) const {
    int i0 = vvFis[i][j] >> 1;
    bool c0 = vvFis[i][j] & 1;
    return man->LitNotCond(vFs[i0], c0);
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
};

#endif
