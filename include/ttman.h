#ifndef TTMAN_H
#define TTMAN_H

#include <limits>
#include <iomanip>
#include <iostream>
#include <vector>
#include <bitset>

namespace Ttman {

  typedef int                bvar;
  typedef unsigned           lit;
  typedef unsigned short     ref;
  typedef unsigned long long size;
  
  static inline bvar BvarMax() { return std::numeric_limits<bvar>::max(); }
  static inline lit  LitMax()  { return std::numeric_limits<lit>::max();  }
  static inline ref  RefMax()  { return std::numeric_limits<ref>::max();  }
  static inline size SizeMax() { return std::numeric_limits<size>::max(); }

  struct Param {
    int  nObjsAllocLog      = 15;
    int  nObjsMaxLog        = 20;
    int  nVerbose           = 0;
    bool fCountOnes         = 0;

    int  nGbc;
    int  nReo;
  };

  class Man {
  private:
    typedef unsigned long long word;
    const int ww = 64; // word width
    const int lww = 6; // log word width
    const word one = 0xffffffffffffffffull;
    static const word vars[];
    
    int  nVars;
    bvar nObjs;
    bvar nObjsAlloc;
    bvar nObjsMax;
    size nSize;
    size nTotalSize;
    std::vector<word> vVals;
    std::vector<bvar> vDeads;
    std::vector<ref>  vRefs;
    std::vector<size> vOneCounts;
    int nVerbose;

  public:
    Man(int nVars, Param p);
    lit  And(lit x, lit y);
    bool Resize();
    bool Gbc();
    void PrintNode(lit x) const;

    lit  Const0()                  const { return 0;                  }
    lit  Const1()                  const { return 1;                  }
    bool IsConst0(lit x)           const {
      bvar a = x >> 1;
      word c = x & 1? one: 0;
      for(size j = 0; j < nSize; j++)
        if(vVals[nSize * a + j] ^ c)
          return false;
      return true;
    }
    bool IsConst1(lit x)           const {
      bvar a = x >> 1;
      word c = x & 1? one: 0;
      for(size j = 0; j < nSize; j++)
        if(~(vVals[nSize * a + j] ^ c))
          return false;
      return true;
    }
    lit  IthVar(int v)             const { return (v + 1) << 1;       }
    lit  LitNot(lit x)             const { return x ^ 1;              }
    lit  LitNotCond(lit x, bool c) const { return x ^ (lit)c;         }
    bool LitIsCompl(lit x)         const { return x & 1;              }
    lit  Bvar2Lit(bvar a)          const { return a << 1;             }
    bvar Lit2Bvar(lit x)           const { return x >> 1;             }
    ref  Ref(lit x)                const { return vRefs[Lit2Bvar(x)]; }
    void IncRef(lit x) { if(Ref(x) != RefMax()) vRefs[Lit2Bvar(x)]++; }
    void DecRef(lit x) { if(Ref(x) != RefMax()) vRefs[Lit2Bvar(x)]--; }
    lit  Or(lit x, lit y) { return LitNot(And(LitNot(x), LitNot(y))); }
    size OneCount(lit x) const {
      if(LitIsCompl(x)) {
        return ((size)1 << std::max(nVars, 6)) - vOneCounts[Lit2Bvar(x)];
      } else {
        return vOneCounts[Lit2Bvar(x)];
      }
    }
    bool LitIsEq(lit x, lit y) {
      if(x == y)
        return true;
      if(x == LitMax() || y == LitMax())
        return false;
      bvar xvar = Lit2Bvar(x);
      bvar yvar = Lit2Bvar(y);
      word c = LitIsCompl(x) ^ LitIsCompl(y)? one: 0;
      for(size j = 0; j < nSize; j++)
        if(vVals[nSize * xvar + j] ^ vVals[nSize * yvar + j] ^ c)
          return false;
      return true;
    }

    void Reorder() {};
    void TurnOffReo() {};
  };
  
  inline Man::Man(int nVars, Param p): nVars(nVars) {
    if(p.nObjsMaxLog < p.nObjsAllocLog)
      throw std::invalid_argument("nObjsMax must not be smaller than nObjsAlloc");
    if(nVars >= lww)
      nSize = 1 << (nVars - lww);
    else
      nSize = 1;
    if(!nSize)
      throw std::length_error("Memout (nVars) in init");
    if(!(nSize << p.nObjsMaxLog))
      throw std::length_error("Memout (nObjsMax) in init");
    lit nObjsMaxLit = (lit)1 << p.nObjsMaxLog;
    if(!nObjsMaxLit)
      throw std::length_error("Memout (nObjsMax) in init");
    if(nObjsMaxLit > (lit)BvarMax())
      nObjsMax = BvarMax();
    else
      nObjsMax = (bvar)nObjsMaxLit;
    lit nObjsAllocLit = (lit)1 << p.nObjsAllocLog;
    if(!nObjsAllocLit)
      throw std::length_error("Memout (nObjsAlloc) in init");
    if(nObjsAllocLit > (lit)BvarMax())
      nObjsAlloc = BvarMax();
    else
      nObjsAlloc = (bvar)nObjsAllocLit;
    if(nObjsAlloc <= (bvar)nVars)
      throw std::invalid_argument("nObjsAlloc must be larger than nVars");
    nTotalSize = nSize << p.nObjsAllocLog;
    vVals.resize(nTotalSize);
    vRefs.resize(nObjsAlloc);
    vOneCounts.resize(nObjsAlloc);
    nObjs = 1;
    for(int i = 0; i < 6 && i < nVars; i++) {
      for(size j = 0; j < nSize; j++)
        vVals[nSize * nObjs + j] = vars[i];
      nObjs++;
    }
    for(int i = 0; i < nVars - 6; i++) {
      for(size j = 0; j < nSize; j += (2ull << i))
        for(size k = 0; k < (1ull << i); k++)
        vVals[nSize * nObjs + j + k] = one;
      nObjs++;
    }
    for(bvar a = 0; a <= nVars; a++)
      vRefs[a] = RefMax();
    nVerbose = p.nVerbose;
  }

  inline lit Man::And(lit x, lit y) {
    bvar xvar = Lit2Bvar(x);
    bvar yvar = Lit2Bvar(y);
    word xcompl = LitIsCompl(x)? one: 0;
    word ycompl = LitIsCompl(y)? one: 0;
    unsigned j;
    if(nObjs >= nObjsAlloc && vDeads.empty())
      if(!Resize() && !Gbc())
        throw "memout";
    bvar zvar;
    if(nObjs < nObjsAlloc)
      zvar = nObjs++;
    else
      zvar = vDeads.back(), vDeads.resize(vDeads.size() - 1);
    for(j = 0; j < nSize; j++)
      vVals[nSize * zvar + j] = (vVals[nSize * xvar + j] ^ xcompl) & (vVals[nSize * yvar + j] ^ ycompl);
    return zvar << 1;
  }

  inline bool Man::Resize() {
    if(nObjsAlloc == nObjsMax)
      return false;
    lit nObjsAllocLit = (lit)nObjsAlloc << 1;
    if(nObjsAllocLit > (lit)BvarMax())
      nObjsAlloc = BvarMax();
    else
      nObjsAlloc = (bvar)nObjsAllocLit;
    nTotalSize = nTotalSize << 1;
    if(nVerbose >= 2)
      std::cout << "Reallocating " << nObjsAlloc << " nodes" << std::endl;
    vVals.resize(nTotalSize);
    vRefs.resize(nObjsAlloc);
    vOneCounts.resize(nObjsAlloc);
    return true;
  }
  
  inline bool Man::Gbc() {
    if(nVerbose >= 2)
      std::cout << "Garbage collect" << std::endl;
    for(bvar a = nVars + 1; a < nObjs; a++)
      if(!vRefs[a])
        vDeads.push_back(a);
    return vDeads.size();
  }
  
  inline void Man::PrintNode(lit x) const {
    bvar a = Lit2Bvar(x);
    word c = LitIsCompl(x)? one: 0;
    for(size j = 0; j < nSize; j++)
      std::cout << std::bitset<64>(vVals[nSize * a + j] ^ c);
    std::cout << std::endl;
  }

}

#endif
