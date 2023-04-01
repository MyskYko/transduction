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
  int count_ = count;
  list<int> targets = vObjs;
  for(list<int>::reverse_iterator it = targets.rbegin(); it != targets.rend(); it++) {
    if(nVerbose > 1)
      cout << "\tResubstitute " << *it << endl;
    if(vvFos[*it].empty())
      continue;
    count += TrivialMergeOne(*it);
    vector<bool> lev;
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
    vector<bool> vMarks(nObjsAlloc);
    MarkFoCone_rec(vMarks, *it);
    list<int> targets2 = vObjs;
    for(list<int>::iterator it2 = targets2.begin(); it2 != targets2.end(); it2++) {
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
      list<int>::iterator it2 = find(vObjs.begin(), vObjs.end(), *it);
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
      list<int>::iterator it2 = find(vObjs.begin(), vObjs.end(), *it);
      int pos = nObjsAlloc;
      if(fLevel)
        count += BalancedDecomposeOne(it2, pos) + (fMspf? Mspf(true): Cspf(true));
      else
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
