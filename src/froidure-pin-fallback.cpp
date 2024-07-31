//
// Semigroups package for GAP
// Copyright (C) 2016-2022 James D. Mitchell
//
// This program is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.
//
// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.
//
// You should have received a copy of the GNU General Public License
// along with this program.  If not, see <https://www.gnu.org/licenses/>.
//

#include "froidure-pin-fallback.hpp"

#include <string.h>  // for size_t, memcpy

#include <algorithm>  // for max
#include <iostream>   // for operator<<, cout, ostream
#include <string>     // for string

// GAP headers
#include "compiled.h"  // for RNamName etc

// Semigroups package for GAP headers
#include "pkg.hpp"               // for HTAdd, HTValue, IsSemigroup, SEMIGROUPS
#include "semigroups-debug.hpp"  // for SEMIGROUPS_ASSERT

// libsemigroups headers
#include "libsemigroups/detail/report.hpp"  // for REPORTER, Reporter
#include "libsemigroups/detail/timer.hpp"   // for Timer

using libsemigroups::detail::Timer;

// Macros for the GAP version of the algorithm

#define INT_PLIST(plist, i) INT_INTOBJ(ELM_PLIST(plist, i))
#define INT_PLIST2(plist, i, j) INT_INTOBJ(ELM_PLIST2(plist, i, j))
#define ELM_PLIST2(plist, i, j) ELM_PLIST(ELM_PLIST(plist, i), j)

static Int RNam_batch_size        = 0;
static Int RNam_DefaultOptionsRec = 0;
static Int RNam_opts              = 0;

static inline void initRNams() {
  if (!RNam_batch_size) {
    RNam_batch_size        = RNamName("batch_size");
    RNam_DefaultOptionsRec = RNamName("DefaultOptionsRec");
    RNam_opts              = RNamName("opts");
  }
}

inline void SET_ELM_PLIST2(Obj plist, UInt i, UInt j, Obj val) {
  Obj inner = ELM_PLIST(plist, i);
  SET_ELM_PLIST(inner, j, val);
  SET_LEN_PLIST(inner, j);
  CHANGED_BAG(inner);
}

// Semigroups

static Obj get_default_value(Int rnam) {
  initRNams();
  Obj opts = ElmPRec(SEMIGROUPS, RNam_DefaultOptionsRec);
  return ElmPRec(opts, rnam);
}

static inline size_t get_batch_size(Obj so) {
  initRNams();
  UInt i;
  if (FindPRec(so, RNam_opts, &i, 1)) {
    Obj opts = GET_ELM_PREC(so, i);
    if (FindPRec(opts, RNam_batch_size, &i, 1)) {
      return INT_INTOBJ(GET_ELM_PREC(opts, i));
    }
  }
  return INT_INTOBJ(get_default_value(RNam_batch_size));
}

// GAP kernel version of the algorithm for other types of semigroups.
//
// Assumes the length of data!.elts is at most 2 ^ 28.

Obj RUN_FROIDURE_PIN(Obj self, Obj obj, Obj limit, Obj report) {
  Obj found, elts, gens, genslookup, right, left, first, final, prefix, suffix,
      reduced, words, ht, rules, lenindex, newElt, newword, objval, newrule,
      empty, oldword, x, data, parent, stopper;
  UInt i, nr, len, stopper_int, nrrules, b, s, r, p, j, k, int_limit, nrgens,
      intval, stop, one;

  if (!IS_PREC(obj)) {
    ErrorQuit("expected a plain record as 1st argument, found %s",
              (Int) TNAM_OBJ(obj),
              0L);
  }  // TODO(later) other checks

  initRNams();

  parent = ElmPRec(obj, RNamName("parent"));
  SEMIGROUPS_ASSERT(CALL_1ARGS(IsSemigroup, parent) == True);
  data              = obj;
  size_t batch_size = get_batch_size(parent);

  i  = INT_INTOBJ(ElmPRec(data, RNamName("pos")));
  nr = INT_INTOBJ(ElmPRec(data, RNamName("nr")));

  if (i > nr || static_cast<size_t>(INT_INTOBJ(limit)) <= nr) {
    CHANGED_BAG(parent);
    return data;
  }
  int_limit = std::max(static_cast<UInt>(INT_INTOBJ(limit)), nr + batch_size);
  if (report == True) {
    std::cout << "#I  limit = " << int_limit << std::endl;
  }

  Timer timer;

  // get everything out of <data>

  // lists of integers, objects
  elts = ElmPRec(data, RNamName("elts"));
  // the so far enumerated elements
  gens = ElmPRec(data, RNamName("gens"));
  // the generators
  genslookup = ElmPRec(data, RNamName("genslookup"));
  // genslookup[i]=Position(elts, gens[i],
  // this is not always <i+1>!
  lenindex = ElmPRec(data, RNamName("lenindex"));
  // lenindex[len]=position in <words> and
  // <elts> of first element of length <len>
  first = ElmPRec(data, RNamName("first"));
  // elts[i]=gens[first[i]]*elts[suffix[i]],
  // first letter
  final = ElmPRec(data, RNamName("final"));
  // elts[i]=elts[prefix[i]]*gens[final[i]]
  prefix = ElmPRec(data, RNamName("prefix"));
  // see final, 0 if prefix is empty i.e.
  // elts[i] is a gen
  suffix = ElmPRec(data, RNamName("suffix"));
  // see first, 0 if suffix is empty i.e.
  // elts[i] is a gen

  // lists of lists
  right = ElmPRec(data, RNamName("right"));
  // elts[right[i][j]]=elts[i]*gens[j],
  // right Cayley graph
  left = ElmPRec(data, RNamName("left"));
  // elts[left[i][j]]=gens[j]*elts[i], left
  // Cayley graph
  reduced = ElmPRec(data, RNamName("reduced"));
  // words[right[i][j]] is reduced if
  // reduced[i][j]=true
  words = ElmPRec(data, RNamName("words"));
  // words[i] is a word in the gens equal to
  // elts[i]
  rules = ElmPRec(data, RNamName("rules"));
  if (TNUM_OBJ(rules) == T_PLIST_EMPTY) {
    RetypeBag(rules, T_PLIST_CYC);
  }

  // hash table
  ht = ElmPRec(data, RNamName("ht"));

  // current word length
  len = INT_INTOBJ(ElmPRec(data, RNamName("len")));

  // <elts[one]> is the mult. neutral
  // element
  if (IS_INTOBJ(ElmPRec(data, RNamName("one")))) {
    one = INT_INTOBJ(ElmPRec(data, RNamName("one")));
  } else {
    one = 0;
  }

  // stop when we have applied generators to
  // elts[stopper_int]
  stopper = ElmPRec(data, RNamName("stopper"));
  if (!IS_INTOBJ(stopper)) {
    stopper_int = -1;
  } else {
    stopper_int = INT_INTOBJ(stopper);
  }

  nrrules = INT_INTOBJ(ElmPRec(data, RNamName("nrrules")));

  nrgens = LEN_PLIST(gens);
  stop   = 0;
  found  = False;

  while (i <= nr && !stop) {
    while (i <= nr && (UInt) LEN_PLIST(ELM_PLIST(words, i)) == len && !stop) {
      b = INT_INTOBJ(ELM_PLIST(first, i));
      s = INT_INTOBJ(ELM_PLIST(suffix, i));
      RetypeBag(ELM_PLIST(right, i),
                T_PLIST_CYC);  // from T_PLIST_EMPTY
      for (j = 1; j <= nrgens; j++) {
        if (s != 0 && ELM_PLIST2(reduced, s, j) == False) {
          r = INT_PLIST2(right, s, j);
          if (INT_PLIST(prefix, r) != 0) {
            intval = INT_PLIST2(left, INT_PLIST(prefix, r), b);
            SET_ELM_PLIST2(
                right, i, j, ELM_PLIST2(right, intval, INT_PLIST(final, r)));
            SET_ELM_PLIST2(reduced, i, j, False);
          } else if (r == one) {
            SET_ELM_PLIST2(right, i, j, ELM_PLIST(genslookup, b));
            SET_ELM_PLIST2(reduced, i, j, False);
          } else {
            SET_ELM_PLIST2(right,
                           i,
                           j,
                           ELM_PLIST2(right,
                                      INT_PLIST(genslookup, b),
                                      INT_PLIST(final, r)));
            SET_ELM_PLIST2(reduced, i, j, False);
          }
        } else {
          newElt  = PROD(ELM_PLIST(elts, i), ELM_PLIST(gens, j));
          oldword = ELM_PLIST(words, i);
          len     = LEN_PLIST(oldword);
          newword = NEW_PLIST(T_PLIST_CYC, len + 1);

          memcpy(ADDR_OBJ(newword) + 1,
                 CONST_ADDR_OBJ(oldword) + 1,
                 static_cast<size_t>(len * sizeof(Obj)));
          SET_ELM_PLIST(newword, len + 1, INTOBJ_INT(j));
          SET_LEN_PLIST(newword, len + 1);

          objval = CALL_2ARGS(HTValue, ht, newElt);
          if (objval != Fail) {
            newrule = NEW_PLIST(T_PLIST, 2);
            SET_ELM_PLIST(newrule, 1, newword);
            SET_ELM_PLIST(newrule, 2, ELM_PLIST(words, INT_INTOBJ(objval)));
            SET_LEN_PLIST(newrule, 2);
            CHANGED_BAG(newrule);
            nrrules++;
            AssPlist(rules, nrrules, newrule);
            SET_ELM_PLIST2(right, i, j, objval);
          } else {
            nr++;

            CALL_3ARGS(HTAdd, ht, newElt, INTOBJ_INT(nr));

            if (one == 0) {
              one = nr;
              for (k = 1; k <= nrgens; k++) {
                x = ELM_PLIST(gens, k);
                if (!EQ(PROD(newElt, x), x)) {
                  one = 0;
                  break;
                }
                if (!EQ(PROD(x, newElt), x)) {
                  one = 0;
                  break;
                }
              }
            }

            if (s != 0) {
              AssPlist(suffix, nr, ELM_PLIST2(right, s, j));
            } else {
              AssPlist(suffix, nr, ELM_PLIST(genslookup, j));
            }

            AssPlist(elts, nr, newElt);
            AssPlist(words, nr, newword);
            AssPlist(first, nr, INTOBJ_INT(b));
            AssPlist(final, nr, INTOBJ_INT(j));
            AssPlist(prefix, nr, INTOBJ_INT(i));

            empty = NEW_PLIST(T_PLIST_EMPTY, nrgens);
            SET_LEN_PLIST(empty, 0);
            AssPlist(right, nr, empty);

            empty = NEW_PLIST(T_PLIST_EMPTY, nrgens);
            SET_LEN_PLIST(empty, 0);
            AssPlist(left, nr, empty);

            empty = NEW_PLIST(T_PLIST_CYC, nrgens);
            for (k = 1; k <= nrgens; k++) {
              SET_ELM_PLIST(empty, k, False);
            }
            SET_LEN_PLIST(empty, nrgens);
            AssPlist(reduced, nr, empty);

            SET_ELM_PLIST2(reduced, i, j, True);
            SET_ELM_PLIST2(right, i, j, INTOBJ_INT(nr));
            stop = (nr >= int_limit);
          }
        }
      }  // finished applying gens to
         // <elts[i]>
      stop = (stop || i == stopper_int);
      i++;
    }  // finished words of length <len> or
       // <stop>
    if (i > nr || (UInt) LEN_PLIST(ELM_PLIST(words, i)) != len) {
      if (len > 1) {
        for (j = INT_INTOBJ(ELM_PLIST(lenindex, len)); j <= i - 1; j++) {
          RetypeBag(ELM_PLIST(left, j),
                    T_PLIST_CYC);  // from
                                   // T_PLIST_EMPTY
          p = INT_INTOBJ(ELM_PLIST(prefix, j));
          b = INT_INTOBJ(ELM_PLIST(final, j));
          for (k = 1; k <= nrgens; k++) {
            SET_ELM_PLIST2(
                left, j, k, ELM_PLIST2(right, INT_PLIST2(left, p, k), b));
          }
        }
      } else if (len == 1) {
        for (j = INT_INTOBJ(ELM_PLIST(lenindex, len)); j <= i - 1; j++) {
          RetypeBag(ELM_PLIST(left, j),
                    T_PLIST_CYC);  // from
                                   // T_PLIST_EMPTY
          b = INT_INTOBJ(ELM_PLIST(final, j));
          for (k = 1; k <= nrgens; k++) {
            SET_ELM_PLIST2(
                left, j, k, ELM_PLIST2(right, INT_PLIST(genslookup, k), b));
          }
        }
      }
      len++;
      AssPlist(lenindex, len, INTOBJ_INT(i));
    }
    if (report == True) {
      std::cout << "#I  found " << nr << " elements, " << nrrules
                << " rules, max word length " << len - 1 << ", ";
      if (i <= nr) {
        std::cout << "so far";
      } else {
        std::cout << "finished!";
      }
      std::cout << std::endl;
    }
  }

  if (report == True) {
    std::cout << "#I  elapsed time: " << timer << std::endl;
  }
  AssPRec(data, RNamName("nr"), INTOBJ_INT(nr));
  AssPRec(data, RNamName("nrrules"), INTOBJ_INT(nrrules));
  AssPRec(data, RNamName("one"), ((one != 0) ? INTOBJ_INT(one) : False));
  AssPRec(data, RNamName("pos"), INTOBJ_INT(i));
  AssPRec(data, RNamName("len"), INTOBJ_INT(len));

  CHANGED_BAG(parent);

  return data;
}

// Using the output of DigraphStronglyConnectedComponents on the right and left
// Cayley graphs of a semigroup, the following function calculates the strongly
// connected components of the union of these two graphs.

Obj SCC_UNION_LEFT_RIGHT_CAYLEY_GRAPHS(Obj self, Obj scc1, Obj scc2) {
  UInt* ptr;
  Int   i, n, len, nr, j, k, l;
  Obj   comps1, id2, comps2, id, comps, seen, comp1, comp2, new_comp, x, out;

  n = LEN_PLIST(ElmPRec(scc1, RNamName("id")));

  if (n == 0) {
    out = NEW_PREC(2);
    AssPRec(out, RNamName("id"), NEW_PLIST_IMM(T_PLIST_EMPTY, 0));
    AssPRec(out, RNamName("comps"), NEW_PLIST_IMM(T_PLIST_EMPTY, 0));
    return out;
  }

  comps1 = ElmPRec(scc1, RNamName("comps"));
  comps2 = ElmPRec(scc2, RNamName("comps"));
  id2    = ElmPRec(scc2, RNamName("id"));

  id = NEW_PLIST_IMM(T_PLIST_CYC, n);
  SET_LEN_PLIST(id, n);
  // init id
  for (i = 1; i <= n; i++) {
    SET_ELM_PLIST(id, i, INTOBJ_INT(0));
  }

  seen = NewBag(T_DATOBJ, (LEN_PLIST(comps2) + 1) * sizeof(UInt));
  ptr  = reinterpret_cast<UInt*>(ADDR_OBJ(seen));
  for (i = 0; i < LEN_PLIST(comps2) + 1; i++) {
    ptr[i] = 0;
  }

  comps = NEW_PLIST_IMM(T_PLIST_TAB, LEN_PLIST(comps1));
  SET_LEN_PLIST(comps, 0);

  nr = 0;

  for (i = 1; i <= LEN_PLIST(comps1); i++) {
    comp1 = ELM_PLIST(comps1, i);
    if (INT_INTOBJ(ELM_PLIST(id, INT_INTOBJ(ELM_PLIST(comp1, 1)))) == 0) {
      nr++;
      new_comp = NEW_PLIST_IMM(T_PLIST_CYC, LEN_PLIST(comp1));
      SET_LEN_PLIST(new_comp, 0);
      for (j = 1; j <= LEN_PLIST(comp1); j++) {
        k = INT_INTOBJ(ELM_PLIST(id2, INT_INTOBJ(ELM_PLIST(comp1, j))));
        if (reinterpret_cast<UInt*>(ADDR_OBJ(seen))[k] == 0) {
          reinterpret_cast<UInt*>(ADDR_OBJ(seen))[k] = 1;
          comp2                                      = ELM_PLIST(comps2, k);
          for (l = 1; l <= LEN_PLIST(comp2); l++) {
            x = ELM_PLIST(comp2, l);
            SET_ELM_PLIST(id, INT_INTOBJ(x), INTOBJ_INT(nr));
            len = LEN_PLIST(new_comp);
            AssPlist(new_comp, len + 1, x);
            SET_LEN_PLIST(new_comp, len + 1);
          }
        }
      }
      SHRINK_PLIST(new_comp, LEN_PLIST(new_comp));
      len = LEN_PLIST(comps) + 1;
      SET_ELM_PLIST(comps, len, new_comp);
      SET_LEN_PLIST(comps, len);
      CHANGED_BAG(comps);
    }
  }

  out = NEW_PREC(2);
  SHRINK_PLIST(comps, LEN_PLIST(comps));
  AssPRec(out, RNamName("id"), id);
  AssPRec(out, RNamName("comps"), comps);
  return out;
}

// <right> and <left> should be scc data structures for the right and left
// Cayley graphs of a semigroup, as produced by
// DigraphStronglyConnectedComponents. This function find the H-classes of the
// semigroup from <right> and <left>. The method used is that described in:
// https://www.irif.fr/~jep//PDF/Exposes/StAndrews.pdf

Obj FIND_HCLASSES(Obj self, Obj right, Obj left) {
  UInt *nextpos, *sorted, *lookup, init;
  Int   n, nrcomps, i, hindex, rindex, j, k, len;
  Obj   rightid, leftid, comps, buf, id, out, comp;

  rightid = ElmPRec(right, RNamName("id"));
  leftid  = ElmPRec(left, RNamName("id"));
  n       = LEN_PLIST(rightid);

  if (n == 0) {
    out = NEW_PREC(2);
    AssPRec(out, RNamName("id"), NEW_PLIST_IMM(T_PLIST_EMPTY, 0));
    AssPRec(out, RNamName("comps"), NEW_PLIST_IMM(T_PLIST_EMPTY, 0));
    return out;
  }
  comps   = ElmPRec(right, RNamName("comps"));
  nrcomps = LEN_PLIST(comps);

  buf     = NewBag(T_DATOBJ, (2 * n + nrcomps + 1) * sizeof(UInt));
  nextpos = reinterpret_cast<UInt*>(ADDR_OBJ(buf));

  nextpos[1] = 1;
  for (i = 2; i <= nrcomps; i++) {
    nextpos[i] = nextpos[i - 1] + LEN_PLIST(ELM_PLIST(comps, i - 1));
  }

  sorted = reinterpret_cast<UInt*>(ADDR_OBJ(buf)) + nrcomps;
  lookup = reinterpret_cast<UInt*>(ADDR_OBJ(buf)) + nrcomps + n;
  for (i = 1; i <= n; i++) {
    j                  = INT_INTOBJ(ELM_PLIST(rightid, i));
    sorted[nextpos[j]] = i;
    nextpos[j]++;
    lookup[i] = 0;
  }

  id = NEW_PLIST_IMM(T_PLIST_CYC, n);
  SET_LEN_PLIST(id, n);
  comps = NEW_PLIST_IMM(T_PLIST_TAB, n);
  SET_LEN_PLIST(comps, 0);

  hindex = 0;
  rindex = 0;
  init   = 0;

  for (i = 1; i <= n; i++) {
    sorted = reinterpret_cast<UInt*>(ADDR_OBJ(buf)) + nrcomps;
    lookup = reinterpret_cast<UInt*>(ADDR_OBJ(buf)) + nrcomps + n;
    j      = sorted[i];
    k      = INT_INTOBJ(ELM_PLIST(rightid, j));
    if (k > rindex) {
      rindex = k;
      init   = hindex;
    }
    k = INT_INTOBJ(ELM_PLIST(leftid, j));
    if (lookup[k] <= init) {
      hindex++;
      lookup[k] = hindex;

      comp = NEW_PLIST_IMM(T_PLIST_CYC, 1);
      SET_LEN_PLIST(comp, 0);
      SET_ELM_PLIST(comps, hindex, comp);
      SET_LEN_PLIST(comps, hindex);
      CHANGED_BAG(comps);

      sorted = reinterpret_cast<UInt*>(ADDR_OBJ(buf)) + nrcomps;
      lookup = reinterpret_cast<UInt*>(ADDR_OBJ(buf)) + nrcomps + n;
    }
    k    = lookup[k];
    comp = ELM_PLIST(comps, k);
    len  = LEN_PLIST(comp) + 1;
    AssPlist(comp, len, INTOBJ_INT(j));
    SET_LEN_PLIST(comp, len);

    SET_ELM_PLIST(id, j, INTOBJ_INT(k));
  }

  SHRINK_PLIST(comps, LEN_PLIST(comps));
  for (i = 1; i <= LEN_PLIST(comps); i++) {
    comp = ELM_PLIST(comps, i);
    SHRINK_PLIST(comp, LEN_PLIST(comp));
  }

  out = NEW_PREC(2);
  AssPRec(out, RNamName("id"), id);
  AssPRec(out, RNamName("comps"), comps);

  return out;
}
