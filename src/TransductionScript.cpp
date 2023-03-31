#include "Transduction.h"

int Transduction::RepeatResub(bool fMono, bool fMspf) {
  int count = 0;
  while(int diff = fMono? ResubMono(fMspf): Resub(fMspf))
    count += diff;
  return count;
}

int Transduction::RepeatResubInner(bool fMspf, bool fInner) {
  int count = 0;
  while(int diff = RepeatResub(true, fMspf) + RepeatResub(false, fMspf)) {
    count += diff;
    if(!fInner)
      break;
  }
  return count;
}

int Transduction::RepeatResubOuter(bool fMspf, bool fInner, bool fOuter) {
  int count = 0;
  while(int diff = fMspf? RepeatResubInner(false, fInner) + RepeatResubInner(true, fInner): RepeatResubInner(false, fInner)) {
    count += diff;
    if(!fOuter)
      break;
  }
  return count;
}

int Transduction::Optimize(bool fFirstMerge, bool fMspfMerge, bool fMspfResub, bool fInner, bool fOuter) {
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
