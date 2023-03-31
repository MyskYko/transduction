#include <iostream>
#include <algorithm>

#include "Transduction.h"

using namespace std;

bool Transduction::TryConnect(int i, int i0, bool c0) {
  int f = (i0 << 1) ^ (int)c0;
  if(find(vvFis[i].begin(), vvFis[i].end(), f) == vvFis[i].end()) {
    lit x = man->Or(man->LitNot(vFs[i]), vGs[i]);
    IncRef(x);
    if(man->IsConst1(man->Or(x, man->LitNotCond(vFs[i0], c0)))) {
      DecRef(x);
      if(nVerbose > 3)
        cout << "\t\t\tConnect " << i0 << "(" << c0 << ")" << std::endl;
      Connect(i, f, true);
      return true;
    }
    DecRef(x);
  }
  return false;
}

int Transduction::Resub(bool fMspf) {
  if(nVerbose)
    cout << "Resubstitution" << endl;
  int count = fMspf? Mspf(true): Cspf(true);
  int nodes = CountNodes();
  TransductionBackup b;
  Save(b);
  list<int> targets = vObjs;
  for(list<int>::reverse_iterator it = targets.rbegin(); it != targets.rend(); it++) {
    if(nVerbose > 1)
      cout << "\tResubstitute " << *it << endl;
    if(vvFos[*it].empty())
      continue;
    int count_ = count;
    count += TrivialMergeOne(*it);
    bool fConnect = false;
    vector<bool> vMarks(nObjsAlloc);
    MarkFoCone_rec(vMarks, *it);
    list<int> targets2 = vObjs;
    for(list<int>::iterator it2 = targets2.begin(); it2 != targets2.end(); it2++)
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
    if(nodes < CountNodes()) {
      Load(b);
      count = count_;
      continue;
    }
    if(!vvFos[*it].empty() && vvFis[*it].size() > 2) {
      list<int>::iterator it2 = find(vObjs.begin(), vObjs.end(), *it);
      int pos = nObjsAlloc;
      count += TrivialDecomposeOne(it2, pos);
    }
    nodes = CountNodes();
    Save(b);
  }
  return count;
}

int Transduction::ResubMono(bool fMspf) {
  if(nVerbose)
    cout << "Resubstitution mono" << endl;
  int count = fMspf? Mspf(true): Cspf(true);
  list<int> targets = vObjs;
  for(list<int>::reverse_iterator it = targets.rbegin(); it != targets.rend(); it++) {
    if(nVerbose > 1)
      cout << "\tResubstitute mono " << *it << endl;
    if(vvFos[*it].empty())
      continue;
    count += TrivialMergeOne(*it);
    TransductionBackup b;
    Save(b);
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
          Save(b);
        } else {
          Load(b);
          count++;
        }
      }
    }
    if(vvFos[*it].empty())
      continue;
    vector<bool> vMarks(nObjsAlloc);
    MarkFoCone_rec(vMarks, *it);
    list<int> targets2 = vObjs;
    for(list<int>::iterator it2 = targets2.begin(); it2 != targets2.end(); it2++) {
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
            Save(b);
          } else {
            Load(b);
            count++;
          }
        }
    }
    if(vvFos[*it].empty())
      continue;
    if(vvFis[*it].size() > 2) {
      list<int>::iterator it2 = find(vObjs.begin(), vObjs.end(), *it);
      int pos = nObjsAlloc;
      count += TrivialDecomposeOne(it2, pos);
    }
  }
  return count;
}

int Transduction::ResubShared(bool fMspf) {
  if(nVerbose)
    cout << "Merge" << endl;
  int count = fMspf? Mspf(true): Cspf(true);
  list<int> targets = vObjs;
  for(list<int>::reverse_iterator it = targets.rbegin(); it != targets.rend(); it++) {
    if(nVerbose > 1)
      cout << "\tMerge " << *it << endl;
    if(vvFos[*it].empty())
      continue;
    count += TrivialMergeOne(*it);
    bool fConnect = false;
    for(unsigned i = 0; i < vPis.size(); i++)
      if(TryConnect(*it, vPis[i], false) || TryConnect(*it, vPis[i], true)) {
        fConnect |= true;
        count--;
      }
    vector<bool> vMarks(nObjsAlloc);
    MarkFoCone_rec(vMarks, *it);
    for(list<int>::iterator it2 = targets.begin(); it2 != targets.end(); it2++)
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
