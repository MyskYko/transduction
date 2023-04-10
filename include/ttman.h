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
  typedef unsigned           uniq;
  typedef unsigned long long size;
  typedef unsigned           cac;
  
  static inline bvar BvarMax() { return std::numeric_limits<bvar>::max(); }
  static inline lit  LitMax()  { return std::numeric_limits<lit>::max();  }
  static inline ref  RefMax()  { return std::numeric_limits<ref>::max();  }
  static inline uniq UniqMax() { return std::numeric_limits<uniq>::max(); }
  static inline size SizeMax() { return std::numeric_limits<size>::max(); }
  static inline cac  CacHash(lit Arg0, lit Arg1)  { return Arg0 + 4256249 * Arg1; }

  class Cache {
  public:
    Cache(int nCacheSizeLog, int nCacheMaxLog, int nVerbose);
    ~Cache();
    inline lit  Lookup(lit x, lit y);
    inline void Insert(lit x, lit y, lit z);
    inline void Clear();
    inline void Resize();

  private:
    cac    nSize;
    cac    nMax;
    cac    Mask;
    size_t nLookups;
    size_t nHits;
    size_t nThold;
    double HitRate;
    int    nVerbose;
    std::vector<lit> vCache;
  };
  
  inline Cache::Cache(int nCacheSizeLog, int nCacheMaxLog, int nVerbose): nVerbose(nVerbose) {
    if(nCacheMaxLog < nCacheSizeLog)
      throw std::invalid_argument("nCacheMax must not be smaller than nCacheSize");
    nMax = (cac)1 << nCacheMaxLog;
    if(!(nMax << 1))
      throw std::length_error("Memout (nCacheMax) in init");
    nSize = (cac)1 << nCacheSizeLog;
    if(nVerbose)
      std::cout << "Allocating " << nSize << " cache entries" << std::endl;
    vCache.resize(nSize * 3);
    Mask = nSize - 1;
    nLookups = 0;
    nHits = 0;
    nThold = (nSize == nMax)? 0: nSize;
    HitRate = 1;
  }
  inline Cache::~Cache() {
    if(nVerbose)
      std::cout << "Free " << nSize << " cache entries" << std::endl;
  }
  inline lit Cache::Lookup(lit x, lit y) {
    nLookups++;
    if(nThold && nLookups > nThold) {
      double NewHitRate = (double)nHits / nLookups;
      if(nVerbose >= 2)
        std::cout << "Cache Hits: " << std::setw(10) << nHits << ", "
                  << "Lookups: " << std::setw(10) << nLookups << ", "
                  << "Rate: " << std::setw(10) << NewHitRate
                  << std::endl;
      if(NewHitRate > HitRate)
        Resize();
      if(nSize == nMax)
        nThold = SizeMax();
      else
        nThold <<= 1;
      HitRate = NewHitRate;
    }
    cac i = (CacHash(x, y) & Mask) * 3;
    if(vCache[i] == x && vCache[i + 1] == y) {
      if(nVerbose >= 3)
        std::cout << "Cache hit: "
                  << "x = " << std::setw(10) << x << ", "
                  << "y = " << std::setw(10) << y << ", "
                  << "z = " << std::setw(10) << vCache[i + 2] << ", "
                  << "hash = " << std::hex << (CacHash(x, y) & Mask) << std::dec
                  << std::endl;
      nHits++;
      return vCache[i + 2];
    }
    return LitMax();
  }
  inline void Cache::Insert(lit x, lit y, lit z) {
    cac i = (CacHash(x, y) & Mask) * 3;
    vCache[i] = x;
    vCache[i + 1] = y;
    vCache[i + 2] = z;
    if(nVerbose >= 3)
      std::cout << "Cache ent: "
                << "x = " << std::setw(10) << x << ", "
                << "y = " << std::setw(10) << y << ", "
                << "z = " << std::setw(10) << z << ", "
                << "hash = " << std::hex << (CacHash(x, y) & Mask) << std::dec
                << std::endl;
  }
  inline void Cache::Clear() {
    std::fill(vCache.begin(), vCache.end(), 0);
  }
  inline void Cache::Resize() {
    cac nSizeOld = nSize;
    nSize <<= 1;
    if(nVerbose >= 2)
      std::cout << "Reallocating " << nSize << " cache entries" << std::endl;
    vCache.resize(nSize * 3);
    Mask = nSize - 1;
    for(cac j = 0; j < nSizeOld; j++) {
      cac i = j * 3;
      if(vCache[i] || vCache[i + 1]) {
        cac hash = (CacHash(vCache[i], vCache[i + 1]) & Mask) * 3;
        vCache[hash] = vCache[i];
        vCache[hash + 1] = vCache[i + 1];
        vCache[hash + 2] = vCache[i + 2];
        if(nVerbose >= 3)
          std::cout << "Cache mov: "
                    << "x = " << std::setw(10) << vCache[i] << ", "
                    << "y = " << std::setw(10) << vCache[i + 1] << ", "
                    << "z = " << std::setw(10) << vCache[i + 2] << ", "
                    << "hash = " << std::hex << (CacHash(vCache[i], vCache[i + 1]) & Mask) << std::dec
                    << std::endl;
      }
    }
  }

  struct Param {
    int  nObjsAllocLog      = 15;
    int  nObjsMaxLog        = 20;
    int  nUniqueDensityLog  = 1;
    int  nCacheSizeLog      = 15;
    int  nCacheMaxLog       = 20;
    int  nCacheVerbose      = 0;
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
    uniq nUniqueMask;
    bvar RemovedHead;
    size nSize;
    size nTotalSize;
    std::vector<word> vVals;
    std::vector<word> vTmp;
    std::vector<bvar> vUnique;
    std::vector<bvar> vNexts;
    std::vector<ref>  vRefs;
    std::vector<size> vOneCounts;
    Cache *cache;
    int nVerbose;

  public:
    Man(int nVars, Param p);
    ~Man();
    uniq UniqHash(std::vector<word>::iterator p) const;
    lit  UniqueCreateInt();
    lit  UniqueCreate();
    lit  And(lit x, lit y);
    bool Resize();
    bool Gbc();
    void PrintNode(lit x) const;

    lit  Const0()                  const { return 0;                  }
    lit  Const1()                  const { return 1;                  }
    bool IsConst0(lit x)           const { return x == 0;             }
    bool IsConst1(lit x)           const { return x == 1;             }
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

    void Reorder() {};
    void TurnOffReo() {};
  };
  
  inline uniq Man::UniqHash(std::vector<word>::iterator p) const {
    word h = 0;
    for(size j = 0; j < nSize; j++) {
      h ^= *p;
      p++;
    }
    h ^= h >> 32;
    return h & nUniqueMask;
  }
  inline lit Man::UniqueCreateInt() {
    size j;
    std::vector<bvar>::iterator p, q;
    p = q = vUnique.begin() + UniqHash(vTmp.begin());
    if(vUnique.begin() == p) {
      for(j = 0; j < nSize; j++)
        if(vTmp[j])
          break;
      if(j == nSize)
        return 0;
    }
    for(; *q; q = vNexts.begin() + *q) {
      for(j = 0; j < nSize; j++)
        if(vVals[nSize * *q + j] != vTmp[j])
          break;
      if(j == nSize)
        return *q << 1;
    }
    bvar next = *p;
    if(nObjs < nObjsAlloc)
      *p = nObjs++;
    else if(RemovedHead)
      *p = RemovedHead,  RemovedHead = vNexts[*p];
    else
      return LitMax();
    for(j = 0; j < nSize; j++)
      vVals[nSize * *p + j] = vTmp[j];
    vOneCounts[*p] = 0;
    for(j = 0; j < nSize; j++)
      vOneCounts[*p] += std::bitset<64>(vTmp[j]).count();
    vNexts[*p] = next;
    return *p << 1;
  }
  inline lit Man::UniqueCreate() {
    bool fCompl = vTmp[nSize - 1] & 1;
    if(fCompl)
      for(size j = 0; j < nSize; j++)
        vTmp[j] ^= one;
    lit x = UniqueCreateInt();
    if(x == LitMax()) {
      if(!Resize() &&
         !Gbc())
        throw std::length_error("Memout (node)");
      x = UniqueCreateInt();
    }
    return x ^ (lit)fCompl;
  }
  
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
    vTmp.resize(nSize);
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
    vNexts.resize(nObjsAlloc);
    vRefs.resize(nObjsAlloc);
    vOneCounts.resize(nObjsAlloc);
    uniq nUniqueSize;
    if(p.nUniqueDensityLog >= 0)
      nUniqueSize = (uniq)nObjsAlloc << p.nUniqueDensityLog;
    else
      nUniqueSize = (uniq)nObjsAlloc >> -p.nUniqueDensityLog;
    if(!nUniqueSize)
      throw std::length_error("Memout (nUniqueSize) in init");
    vUnique.resize(nUniqueSize);
    nUniqueMask = nUniqueSize - 1;
    cache = new Cache(p.nCacheSizeLog, p.nCacheMaxLog, p.nCacheVerbose);
    nObjs = 1;
    for(int i = 0; i < 6 && i < nVars; i++) {
      for(size j = 0; j < nSize; j++)
        vTmp[j] = vars[i];
      UniqueCreate();
    }
    for(int i = 0; i < nVars - 6; i++) {
      for(size j = 0; j < nSize; j += (2ull << i)) {
        for(size k = 0; k < (1ull << i); k++)
          vTmp[j + k] = one;
        for(size k = (1ull << i); k < (2ull << i); k++)
          vTmp[j + k] = 0;
      }
      UniqueCreate();
    }
    for(bvar a = 0; a <= nVars; a++)
      vRefs[a] = RefMax();
    RemovedHead = 0;
    nVerbose = p.nVerbose;
  }
  inline Man::~Man() {
    delete cache;
  }

  inline lit Man::And(lit x, lit y) {
    if(x == 0 || y == 1)
      return x;
    if(x == 1 || y == 0)
      return y;
    if(Lit2Bvar(x) == Lit2Bvar(y))
      return (x == y)? x: 0;
    if(x > y)
      std::swap(x, y);
    lit z = cache->Lookup(x, y);
    if(z != LitMax())
      return z;
    bvar xvar = Lit2Bvar(x);
    bvar yvar = Lit2Bvar(y);
    word xcompl = LitIsCompl(x)? one: 0;
    word ycompl = LitIsCompl(y)? one: 0;
    unsigned j;
    for(j = 0; j < nSize; j++)
      vTmp[j] = (vVals[nSize * xvar + j] ^ xcompl) & (vVals[nSize * yvar + j] ^ ycompl);
    z = UniqueCreate();
    cache->Insert(x, y, z);
    return z;
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
    vNexts.resize(nObjsAlloc);
    vRefs.resize(nObjsAlloc);
    vOneCounts.resize(nObjsAlloc);
    uniq nUniqueSize, nUniqueSizeOld;
    nUniqueSize = nUniqueSizeOld = vUnique.size();
    nUniqueSize <<= 1;
    if(nUniqueSize) {
      if(nVerbose >= 2)
        std::cout << "Reallocating " << nUniqueSize << " unique table entries" << std::endl;
      vUnique.resize(nUniqueSize);
      nUniqueMask = nUniqueSize - 1;
      for(uniq i = 0; i < nUniqueSizeOld; i++) {
        std::vector<bvar>::iterator q, tail, tail1, tail2;
        q = tail1 = vUnique.begin() + i;
        tail2 = q + nUniqueSizeOld;
        while(*q) {
          uniq hash = UniqHash(vVals.begin() + *q);
          if(hash == i)
            tail = tail1;
          else
            tail = tail2;
          if(tail != q)
            *tail = *q, *q = 0;
          q = vNexts.begin() + *tail;
          if(tail == tail1)
            tail1 = q;
          else
            tail2 = q;
        }
      }
    }
    return true;
  }
  
  inline bool Man::Gbc() {
    if(nVerbose >= 2)
      std::cout << "Garbage collect" << std::endl;
    for(std::vector<bvar>::iterator p = vUnique.begin(); p != vUnique.end(); p++)
      for(std::vector<bvar>::iterator q = p; *q;) {
        if(!vRefs[*q]) {
          bvar next = vNexts[*q];
          vNexts[*q] = RemovedHead;
          RemovedHead = *q;
          *q = next;
        } else
          q = vNexts.begin() + *q;
      }
    cache->Clear();
    return RemovedHead;
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
