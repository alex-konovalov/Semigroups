//
// Semigroups package for GAP
// Copyright (C) 2016 James D. Mitchell
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

// TODO(later) 1) if we use clear before resize maybe don't need fill
//             2) in-place product

#include "bipart.hpp"

#include <algorithm>    // for fill, min, max, all_of, max_element
#include <cstddef>      // for size_t, NULL
#include <cstdint>      // for uint32_t
#include <string>       // for string
#include <thread>       // for thread
#include <type_traits>  // for conditional<>::type
#include <utility>      // for pair, make_pair
#include <vector>       // for vector

// GAP headers
#include "compiled.h"

// libsemigroups headers
#include "libsemigroups/bipart.hpp"  // for Blocks, Bipartition, validate
#include "libsemigroups/detail/report.hpp"  // for Reporter, etc
#include "libsemigroups/detail/timer.hpp"   // for Timer
#include "semigroups-config.hpp"     // for SEMIGROUPS_KERNEL_DEBUG

#include "gapbind14/gapbind14.hpp"  // for GAPBIND14_TRY

using libsemigroups::Bipartition;
using libsemigroups::Blocks;
using libsemigroups::detail::Timer;

// Global variables

static std::vector<size_t> _BUFFER_size_t;
static std::vector<bool>   _BUFFER_bool;

// A T_BIPART Obj in GAP is of the form:
//
//   [pointer to C++ bipartition, left blocks Obj, right blocks Obj]

// Create a new GAP bipartition Obj from a C++ Bipartition pointer.

Obj bipart_new_obj(Bipartition* x) {
  size_t deg = x->degree() + 1;
  if (deg > static_cast<size_t>(LEN_PLIST(TYPES_BIPART))
      || ELM_PLIST(TYPES_BIPART, deg) == 0) {
    CALL_1ARGS(TYPE_BIPART, INTOBJ_INT(deg - 1));
  }

  Obj o          = NewBag(T_BIPART, 3 * sizeof(Obj));
  ADDR_OBJ(o)[0] = reinterpret_cast<Obj>(x);
  return o;
}

// A T_BLOCKS Obj in GAP is of the form:
//
//   [pointer to C++ blocks]

// Returns the pointer to the C++ blocks object from the GAP bipartition
// object.

// Create a new GAP blocks Obj from a C++ Blocks pointer.

inline Obj blocks_new_obj(Blocks* x) {
  Obj o          = NewBag(T_BLOCKS, 1 * sizeof(Obj));
  ADDR_OBJ(o)[0] = reinterpret_cast<Obj>(x);
  return o;
}

////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
// Bipartitions
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////////////
// GAP level functions
////////////////////////////////////////////////////////////////////////////////

// Create a bipartition from the list gap_blocks. The argument gap_blocks must
// be a list which either represents:
//
//    * the internal rep of a bipartition (list of positive integers such that
//      gap_blocks[i] is the index of the class containing i); or
//
//    * the external rep of a bipartition (a list of lists of ints that
//    partition [-n ... -1] union [1 .. n].
//
// BIPART_NC does only minimal checks, and doesn't fully check if its argument
// is valid.

Obj BIPART_NC(Obj self, Obj gap_blocks) {
  SEMIGROUPS_ASSERT(IS_LIST(gap_blocks));
  std::vector<uint32_t> blocks;

  size_t degree         = 0;
  size_t nr_left_blocks = 0;
  size_t nr_blocks      = 0;

  if (LEN_LIST(gap_blocks) != 0) {
    if (IS_LIST(ELM_LIST(gap_blocks, 1))) {  // gap_blocks is a list of lists
      nr_blocks = LEN_LIST(gap_blocks);
      for (size_t i = 1; i <= nr_blocks; i++) {
        SEMIGROUPS_ASSERT(IS_LIST(ELM_LIST(gap_blocks, i)));
        degree += LEN_LIST(ELM_LIST(gap_blocks, i));
      }
      blocks.resize(degree);

      degree /= 2;

      for (size_t i = 1; i <= nr_blocks; i++) {
        Obj block = ELM_LIST(gap_blocks, i);
        for (size_t j = 1; j <= static_cast<size_t>(LEN_LIST(block)); j++) {
          SEMIGROUPS_ASSERT(IS_INTOBJ(ELM_LIST(block, j)));
          int jj = INT_INTOBJ(ELM_LIST(block, j));
          if (jj < 0) {
            blocks[-jj + degree - 1] = i - 1;
          } else {
            nr_left_blocks = i;
            blocks[jj - 1] = i - 1;
          }
        }
      }
    } else {  // gap_blocks is the internal rep of a bipartition
      blocks.reserve(LEN_LIST(gap_blocks));
      for (size_t i = 1; i <= static_cast<size_t>(LEN_LIST(gap_blocks)) / 2;
           i++) {
        SEMIGROUPS_ASSERT(IS_INTOBJ(ELM_LIST(gap_blocks, i))
                          && INT_INTOBJ(ELM_LIST(gap_blocks, i)) > 0);
        uint32_t index = INT_INTOBJ(ELM_LIST(gap_blocks, i)) - 1;
        blocks.push_back(index);
        nr_blocks = (index > nr_blocks ? index : nr_blocks);
      }
      nr_left_blocks = nr_blocks + 1;
      for (size_t i = (static_cast<size_t>(LEN_LIST(gap_blocks)) / 2) + 1;
           i <= static_cast<size_t>(LEN_LIST(gap_blocks));
           i++) {
        SEMIGROUPS_ASSERT(IS_INTOBJ(ELM_LIST(gap_blocks, i))
                          && INT_INTOBJ(ELM_LIST(gap_blocks, i)) > 0);
        uint32_t index = INT_INTOBJ(ELM_LIST(gap_blocks, i)) - 1;
        blocks.push_back(index);
        nr_blocks = (index > nr_blocks ? index : nr_blocks);
      }
      nr_blocks++;
    }
  }

  // construct C++ object
  Bipartition* x;
  // We could use Bipartition::make in the next line, but then we are repeating
  // the checks in the Semigroups package, which give more meaningful error
  // messages.
  GAPBIND14_TRY(x = new Bipartition(Bipartition(blocks));)
  x->set_number_of_left_blocks(nr_left_blocks);
  x->set_number_of_blocks(nr_blocks);

  return bipart_new_obj(x);
}

// Returns the external rep of a GAP bipartition, see description before
// BIPART_NC for more details.

Obj BIPART_EXT_REP(Obj self, Obj x) {
  SEMIGROUPS_ASSERT(TNUM_OBJ(x) == T_BIPART);

  Bipartition* xx = bipart_get_cpp(x);
  size_t       n  = xx->degree();

  Obj ext_rep
      = NEW_PLIST(n == 0 ? T_PLIST_EMPTY : T_PLIST_TAB, xx->number_of_blocks());
  SET_LEN_PLIST(ext_rep, (Int) xx->number_of_blocks());

  for (size_t i = 0; i < 2 * n; i++) {
    Obj entry = INTOBJ_INT((i < n ? i + 1 : -(i - n) - 1));
    if (ELM_PLIST(ext_rep, xx->at(i) + 1) == 0) {
      Obj block = NEW_PLIST(T_PLIST_CYC, 1);
      SET_LEN_PLIST(block, 1);
      SET_ELM_PLIST(block, 1, entry);
      SET_ELM_PLIST(ext_rep, xx->at(i) + 1, block);
      CHANGED_BAG(ext_rep);
    } else {
      Obj block = ELM_PLIST(ext_rep, xx->at(i) + 1);
      AssPlist(block, LEN_PLIST(block) + 1, entry);
    }
  }
  MakeImmutable(ext_rep);
  return ext_rep;
}

// Returns the internal rep of a GAP bipartition, see description before
// BIPART_NC for more details.

Obj BIPART_INT_REP(Obj self, Obj x) {
  SEMIGROUPS_ASSERT(TNUM_OBJ(x) == T_BIPART);

  Bipartition* xx = bipart_get_cpp(x);  // get C++ bipartition pointer
  size_t       n  = xx->degree();

  Obj int_rep = NEW_PLIST_IMM(n == 0 ? T_PLIST_EMPTY : T_PLIST_CYC, 2 * n);
  SET_LEN_PLIST(int_rep, (Int) 2 * n);

  for (size_t i = 0; i < 2 * n; i++) {
    SET_ELM_PLIST(int_rep, i + 1, INTOBJ_INT(xx->at(i) + 1));
  }
  return int_rep;
}

// Returns the hash value for a GAP bipartition from the C++ object.

Obj BIPART_HASH(Obj self, Obj x, Obj data) {
  SEMIGROUPS_ASSERT(TNUM_OBJ(x) == T_BIPART);
  SEMIGROUPS_ASSERT(IS_INTOBJ(data));

  return INTOBJ_INT((bipart_get_cpp(x)->hash_value() % INT_INTOBJ(data)) + 1);
}

// Returns the degree of a GAP bipartition from the C++ object. A bipartition
// is of degree n if it is defined on [-n .. -1] union [1 .. n].

Obj BIPART_DEGREE(Obj self, Obj x) {
  SEMIGROUPS_ASSERT(TNUM_OBJ(x) == T_BIPART);

  return INTOBJ_INT(bipart_get_cpp(x)->degree());
}

// Returns the number of blocks in the bipartition from the C++ object.

Obj BIPART_NR_BLOCKS(Obj self, Obj x) {
  SEMIGROUPS_ASSERT(TNUM_OBJ(x) == T_BIPART);

  return INTOBJ_INT(bipart_get_cpp(x)->number_of_blocks());
}

// Returns the number of blocks containing positive integers in the GAP
// bipartition from the C++ object.

Obj BIPART_NR_LEFT_BLOCKS(Obj self, Obj x) {
  SEMIGROUPS_ASSERT(TNUM_OBJ(x) == T_BIPART);

  return INTOBJ_INT(bipart_get_cpp(x)->number_of_left_blocks());
}

// Returns the number of blocks both positive and negative integers in the GAP
// bipartition from the C++ object.

Obj BIPART_RANK(Obj self, Obj x, Obj dummy) {
  SEMIGROUPS_ASSERT(TNUM_OBJ(x) == T_BIPART);

  return INTOBJ_INT(bipart_get_cpp(x)->rank());
}

// Returns the product of the GAP bipartitions x and y as a new GAP
// bipartition.

Obj BIPART_PROD(Obj x, Obj y) {
  SEMIGROUPS_ASSERT(TNUM_OBJ(x) == T_BIPART);
  SEMIGROUPS_ASSERT(TNUM_OBJ(y) == T_BIPART);

  Bipartition* xx = bipart_get_cpp(x);
  Bipartition* yy = bipart_get_cpp(y);

  Bipartition* z = new Bipartition(xx->degree());
  z->product_inplace(*xx, *yy);

  return bipart_new_obj(static_cast<Bipartition*>(z));
}

// Check if the GAP bipartitions x and y are equal.

Int BIPART_EQ(Obj x, Obj y) {
  return (*bipart_get_cpp(x) == *bipart_get_cpp(y) ? 1L : 0L);
}

// Check if x < y for the GAP bipartitions x and y.

Int BIPART_LT(Obj x, Obj y) {
  return (*bipart_get_cpp(x) < *bipart_get_cpp(y) ? 1L : 0L);
}

// Returns the permutation of the indices of the transverse blocks of (x ^ * y)
// induced by (x ^ * y). Assumes that the left and right blocks of x and y are
// equal.

Obj BIPART_PERM_LEFT_QUO(Obj self, Obj x, Obj y) {
  SEMIGROUPS_ASSERT(TNUM_OBJ(x) == T_BIPART);
  SEMIGROUPS_ASSERT(TNUM_OBJ(y) == T_BIPART);

// The following is done to avoid leaking memory
#ifdef SEMIGROUPS_KERNEL_DEBUG
  Blocks* xb = bipart_get_cpp(x)->left_blocks();
  Blocks* yb = bipart_get_cpp(y)->left_blocks();
  SEMIGROUPS_ASSERT(*xb == *yb);
  delete xb;
  delete yb;
  xb = bipart_get_cpp(x)->right_blocks();
  yb = bipart_get_cpp(y)->right_blocks();
  SEMIGROUPS_ASSERT(*xb == *yb);
  delete xb;
  delete yb;
#endif

  size_t deg  = bipart_get_cpp(x)->degree();
  Obj    p    = NEW_PERM4(deg);
  UInt4* ptrp = ADDR_PERM4(p);

  Bipartition* xx = bipart_get_cpp(x);
  Bipartition* yy = bipart_get_cpp(y);

  SEMIGROUPS_ASSERT(xx->degree() == yy->degree());

  // find indices of right blocks of <x>
  size_t index = 0;
  _BUFFER_size_t.clear();
  _BUFFER_size_t.resize(2 * deg, -1);

  for (size_t i = deg; i < 2 * deg; i++) {
    if (_BUFFER_size_t[xx->at(i)] == static_cast<size_t>(-1)) {
      _BUFFER_size_t[xx->at(i)] = index;
      index++;
    }
    ptrp[i - deg] = i - deg;
  }

  for (size_t i = deg; i < 2 * deg; i++) {
    if (yy->at(i) < xx->number_of_left_blocks()) {
      ptrp[_BUFFER_size_t[yy->at(i)]] = _BUFFER_size_t[xx->at(i)];
    }
  }
  return p;
}

// Returns the GAP bipartition xx ^ *.

Obj BIPART_LEFT_PROJ(Obj self, Obj x) {
  SEMIGROUPS_ASSERT(TNUM_OBJ(x) == T_BIPART);

  Bipartition* xx = bipart_get_cpp(x);

  size_t deg  = xx->degree();
  size_t next = xx->number_of_left_blocks();

  std::fill(_BUFFER_size_t.begin(),
            std::min(_BUFFER_size_t.end(), _BUFFER_size_t.begin() + 2 * deg),
            -1);
  _BUFFER_size_t.resize(2 * deg, -1);

  std::vector<uint32_t> blocks(2 * deg, -1);

  for (size_t i = 0; i < deg; i++) {
    blocks[i] = xx->at(i);
    if (xx->is_transverse_block(xx->at(i))) {
      blocks[i + deg] = xx->at(i);
    } else if (_BUFFER_size_t[xx->at(i)] != static_cast<size_t>(-1)) {
      blocks[i + deg] = _BUFFER_size_t[xx->at(i)];
    } else {
      _BUFFER_size_t[xx->at(i)] = next;
      blocks[i + deg]           = next;
      next++;
    }
  }

  Bipartition* out = new Bipartition(blocks);
  out->set_number_of_blocks(next);
  return bipart_new_obj(out);
}

// Returns the GAP bipartition x ^ *x.

Obj BIPART_RIGHT_PROJ(Obj self, Obj x) {
  SEMIGROUPS_ASSERT(TNUM_OBJ(x) == T_BIPART);

  Bipartition* xx = bipart_get_cpp(x);

  size_t deg     = xx->degree();
  size_t l_block = 0;
  size_t r_block = xx->number_of_right_blocks();

  _BUFFER_size_t.clear();
  _BUFFER_size_t.resize(4 * deg, -1);
  auto buf1 = _BUFFER_size_t.begin();
  auto buf2 = _BUFFER_size_t.begin() + 2 * deg;

  std::vector<uint32_t> blocks(2 * deg, -1);

  for (size_t i = deg; i < 2 * deg; i++) {
    if (buf2[xx->at(i)] == static_cast<size_t>(-1)) {
      if (xx->is_transverse_block(xx->at(i))) {
        buf2[xx->at(i)] = buf1[xx->at(i)] = l_block++;
      } else {
        buf2[xx->at(i)] = r_block++;
        buf1[xx->at(i)] = l_block++;
      }
    }
    blocks[i - deg] = buf1[xx->at(i)];
    blocks[i]       = buf2[xx->at(i)];
  }

  Bipartition* out = new Bipartition(blocks);
  out->set_number_of_blocks(r_block);
  return bipart_new_obj(out);
}

// Returns the GAP bipartition x ^ *.

Obj BIPART_STAR(Obj self, Obj x) {
  SEMIGROUPS_ASSERT(TNUM_OBJ(x) == T_BIPART);

  Bipartition* xx  = bipart_get_cpp(x);
  size_t       deg = xx->degree();

  std::fill(_BUFFER_size_t.begin(),
            std::min(_BUFFER_size_t.end(), _BUFFER_size_t.begin() + 2 * deg),
            -1);
  _BUFFER_size_t.resize(2 * deg, -1);

  std::vector<uint32_t> blocks(2 * deg, -1);

  size_t next = 0;

  for (size_t i = 0; i < deg; i++) {
    if (_BUFFER_size_t[xx->at(i + deg)] != static_cast<size_t>(-1)) {
      blocks[i] = _BUFFER_size_t[xx->at(i + deg)];
    } else {
      _BUFFER_size_t[xx->at(i + deg)] = next;
      blocks[i]                       = next;
      next++;
    }
  }

  size_t nr_left = next;

  for (size_t i = 0; i < deg; i++) {
    if (_BUFFER_size_t[xx->at(i)] != static_cast<size_t>(-1)) {
      blocks[i + deg] = _BUFFER_size_t[xx->at(i)];
    } else {
      _BUFFER_size_t[xx->at(i)] = next;
      blocks[i + deg]           = next;
      next++;
    }
  }

  Bipartition* out = new Bipartition(blocks);
  out->set_number_of_blocks(next);
  out->set_number_of_left_blocks(nr_left);

  return bipart_new_obj(out);
}

// Returns a permutation mapping the indices of the right transverse blocks of
// x and to the right transverse blocks of y. Assumes that x and y have equal
// left blocks.

Obj BIPART_LAMBDA_CONJ(Obj self, Obj x, Obj y) {
  SEMIGROUPS_ASSERT(TNUM_OBJ(x) == T_BIPART);
  SEMIGROUPS_ASSERT(TNUM_OBJ(y) == T_BIPART);

  Bipartition* xx = bipart_get_cpp(x);
  Bipartition* yy = bipart_get_cpp(y);

#ifdef SEMIGROUPS_KERNEL_DEBUG
  Blocks* xb = xx->left_blocks();
  Blocks* yb = yy->left_blocks();
  SEMIGROUPS_ASSERT(*xb == *yb);
  delete xb;
  delete yb;
#endif

  size_t deg            = xx->degree();
  size_t nr_left_blocks = xx->number_of_left_blocks();
  size_t nr_blocks = std::max(xx->number_of_blocks(), yy->number_of_blocks());

  _BUFFER_bool.clear();
  _BUFFER_bool.resize(3 * nr_blocks);
  auto seen = _BUFFER_bool.begin();
  auto src  = seen + nr_blocks;
  auto dst  = src + nr_blocks;

  _BUFFER_size_t.clear();
  _BUFFER_size_t.resize(nr_left_blocks);
  auto   lookup = _BUFFER_size_t.begin();
  size_t next   = 0;

  for (size_t i = deg; i < 2 * deg; i++) {
    if (!seen[yy->at(i)]) {
      seen[yy->at(i)] = true;
      if (yy->at(i) < nr_left_blocks) {  // connected block
        lookup[yy->at(i)] = next;
      }
      next++;
    }
  }

  std::fill(_BUFFER_bool.begin(), _BUFFER_bool.begin() + nr_blocks, false);

  Obj    p    = NEW_PERM4(nr_blocks);
  UInt4* ptrp = ADDR_PERM4(p);
  next        = 0;

  for (size_t i = deg; i < 2 * deg; i++) {
    if (!seen[xx->at(i)]) {
      seen[xx->at(i)] = true;
      if (xx->at(i) < nr_left_blocks) {  // connected block
        ptrp[next]             = lookup[xx->at(i)];
        src[next]              = true;
        dst[lookup[xx->at(i)]] = true;
      }
      next++;
    }
  }

  size_t j = 0;
  for (size_t i = 0; i < nr_blocks; i++) {
    if (!src[i]) {
      while (dst[j]) {
        j++;
      }
      ptrp[i] = j;
      j++;
    }
  }
  return p;
}

// Returns a GAP bipartition y such that the right blocks of y are the right
// blocks of x permuted by p.

Obj BIPART_STAB_ACTION(Obj self, Obj x, Obj p) {
  SEMIGROUPS_ASSERT(TNUM_OBJ(x) == T_BIPART);

  // find the largest moved point of the permutation p
  size_t pdeg;

  if (TNUM_OBJ(p) == T_PERM2) {
    UInt2* ptr = ADDR_PERM2(p);
    for (pdeg = DEG_PERM2(p); 1 <= pdeg; pdeg--) {
      if (ptr[pdeg - 1] != pdeg - 1) {
        break;
      }
    }
  } else if (TNUM_OBJ(p) == T_PERM4) {
    UInt4* ptr = ADDR_PERM4(p);
    for (pdeg = DEG_PERM4(p); 1 <= pdeg; pdeg--) {
      if (ptr[pdeg - 1] != pdeg - 1) {
        break;
      }
    }
  } else {
    ErrorQuit("usage: <p> must be a perm (not a %s)", (Int) TNAM_OBJ(p), 0L);
    return 0L;  // to keep the compiler happy
  }

  if (pdeg == 0) {
    return x;
  }
  Bipartition* xx = bipart_get_cpp(x);

  size_t deg       = xx->degree();
  size_t nr_blocks = xx->number_of_blocks();

  std::vector<uint32_t> blocks(2 * deg);

  _BUFFER_size_t.clear();
  _BUFFER_size_t.resize(2 * nr_blocks + std::max(deg, pdeg), -1);

  auto tab1 = _BUFFER_size_t.begin();
  auto tab2 = _BUFFER_size_t.begin() + nr_blocks;
  auto q    = tab2 + nr_blocks;  // the inverse of p

  if (TNUM_OBJ(p) == T_PERM2) {
    UInt2* ptr = ADDR_PERM2(p);
    UInt2  i;
    for (i = 0; i < pdeg; i++) {
      q[ptr[i]] = static_cast<size_t>(i);
    }
    for (; i < deg; i++) {
      q[i] = static_cast<size_t>(i);
    }
  } else if (TNUM_OBJ(p) == T_PERM4) {
    UInt4* ptr = ADDR_PERM4(p);
    UInt4  i;
    for (i = 0; i < pdeg; i++) {
      q[ptr[i]] = static_cast<size_t>(i);
    }
    for (; i < deg; i++) {
      q[i] = static_cast<size_t>(i);
    }
  }

  size_t next = 0;

  for (size_t i = deg; i < 2 * deg; i++) {
    if (tab1[xx->at(i)] == static_cast<size_t>(-1)) {
      tab1[xx->at(i)] = q[next];
      tab2[next]      = xx->at(i);
      next++;
    }
  }

  for (size_t i = 0; i < deg; i++) {
    blocks[i]       = xx->at(i);
    blocks[i + deg] = tab2[tab1[xx->at(i + deg)]];
  }

  return bipart_new_obj(new Bipartition(blocks));
}

// Returns the GAP Obj left block of the bipartition x. The left blocks are
// simply the subpartition of [1 .. n] induced by x.

Obj BIPART_LEFT_BLOCKS(Obj self, Obj x) {
  SEMIGROUPS_ASSERT(TNUM_OBJ(x) == T_BIPART);
  if (ADDR_OBJ(x)[1] == NULL) {
    Obj o          = blocks_new_obj(bipart_get_cpp(x)->left_blocks());
    ADDR_OBJ(x)[1] = o;
    CHANGED_BAG(x);
  }
  SEMIGROUPS_ASSERT(ADDR_OBJ(x)[1] != NULL);
  SEMIGROUPS_ASSERT(TNUM_OBJ(ADDR_OBJ(x)[1]) == T_BLOCKS);
  return ADDR_OBJ(x)[1];
}

// Returns the GAP Obj right block of the bipartition x. The right blocks are
// simply the subpartition of [-n .. -1] induced by x.

Obj BIPART_RIGHT_BLOCKS(Obj self, Obj x) {
  SEMIGROUPS_ASSERT(TNUM_OBJ(x) == T_BIPART);
  if (ADDR_OBJ(x)[2] == NULL) {
    Obj o          = blocks_new_obj(bipart_get_cpp(x)->right_blocks());
    ADDR_OBJ(x)[2] = o;
    CHANGED_BAG(x);
  }
  SEMIGROUPS_ASSERT(ADDR_OBJ(x)[2] != NULL);
  SEMIGROUPS_ASSERT(TNUM_OBJ(ADDR_OBJ(x)[2]) == T_BLOCKS);
  return ADDR_OBJ(x)[2];
}

////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
// Blocks
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////

// Forward declarations, see below for the definition of these functions.

static inline size_t fuse_it(size_t);

static void fuse(uint32_t,
                 typename std::vector<uint32_t>::const_iterator,
                 uint32_t,
                 typename std::vector<uint32_t>::const_iterator,
                 uint32_t,
                 bool);

////////////////////////////////////////////////////////////////////////////////
// GAP-level functions
////////////////////////////////////////////////////////////////////////////////

// Create a GAP blocks object from the list gap_blocks. The argument gap_blocks
// must be a list which is the external rep of a GAP blocks object (a list of
// lists of integers such that the absolute values of these lists partition
// [1 .. n], transverse blocks are indicated by positive integers and
// non-transverse by negative integers).
//
// BLOCKS_NC does only minimal checks, and doesn't fully check if its argument
// is valid.

Obj BLOCKS_NC(Obj self, Obj gap_blocks) {
  SEMIGROUPS_ASSERT(IS_LIST(gap_blocks));

  if (LEN_LIST(gap_blocks) == 0) {
    return blocks_new_obj(new Blocks());
  }

  SEMIGROUPS_ASSERT(IS_LIST(ELM_LIST(gap_blocks, 1)));

  size_t degree    = 0;
  size_t nr_blocks = LEN_LIST(gap_blocks);

  for (size_t i = 1; i <= nr_blocks; i++) {
    SEMIGROUPS_ASSERT(IS_LIST(ELM_LIST(gap_blocks, i)));
    degree += LEN_LIST(ELM_LIST(gap_blocks, i));
  }

  Blocks* blocks = new Blocks(degree);

  for (size_t i = 1; i <= nr_blocks; i++) {
    Obj block = ELM_LIST(gap_blocks, i);
    for (size_t j = 1; j <= static_cast<size_t>(LEN_LIST(block)); j++) {
      SEMIGROUPS_ASSERT(IS_INTOBJ(ELM_LIST(block, j)));
      int jj = INT_INTOBJ(ELM_LIST(block, j));
      if (jj < 0) {
        blocks->set_block(-jj - 1, i - 1);
        blocks->set_is_transverse_block(i - 1, false);
      } else {
        blocks->set_block(jj - 1, i - 1);
        blocks->set_is_transverse_block(i - 1, true);
      }
    }
  }
#ifdef SEMIGROUPS_KERNEL_DEBUG
  libsemigroups::validate(*blocks);
#endif
  return blocks_new_obj(blocks);
}

// Returns the external representation of a GAP blocks Obj, see the description
// before BLOCKS_NC for more details.

Obj BLOCKS_EXT_REP(Obj self, Obj x) {
  SEMIGROUPS_ASSERT(TNUM_OBJ(x) == T_BLOCKS);

  Blocks* xx = blocks_get_cpp(x);
  size_t  n  = xx->degree();

  Obj ext_rep
      = NEW_PLIST(n == 0 ? T_PLIST_EMPTY : T_PLIST_TAB, xx->number_of_blocks());
  SET_LEN_PLIST(ext_rep, (Int) xx->number_of_blocks());

  for (size_t i = 0; i < n; i++) {
    Obj block;
    Obj entry = (xx->is_transverse_block((*xx)[i]) ? INTOBJ_INT(i + 1)
                                                   : INTOBJ_INT(-i - 1));
    if (ELM_PLIST(ext_rep, (*xx)[i] + 1) == 0) {
      block = NEW_PLIST(T_PLIST_CYC, 1);
      SET_LEN_PLIST(block, 1);
      SET_ELM_PLIST(block, 1, entry);
      SET_ELM_PLIST(ext_rep, (*xx)[i] + 1, block);
      CHANGED_BAG(ext_rep);
    } else {
      block = ELM_PLIST(ext_rep, (*xx)[i] + 1);
      AssPlist(block, LEN_PLIST(block) + 1, entry);
    }
  }
  MakeImmutable(ext_rep);
  return ext_rep;
}

// Returns the hash value for a GAP bipartition from the C++ object.

Obj BLOCKS_HASH(Obj self, Obj x, Obj data) {
  SEMIGROUPS_ASSERT(TNUM_OBJ(x) == T_BLOCKS);

  return INTOBJ_INT((blocks_get_cpp(x)->hash_value() % INT_INTOBJ(data)) + 1);
}

// Returns the degree of a GAP blocks from the C++ object. A blocks object
// is of degree n if the union of the sets of absolute values of its blocks is
// [1 .. n].

Obj BLOCKS_DEGREE(Obj self, Obj x) {
  SEMIGROUPS_ASSERT(TNUM_OBJ(x) == T_BLOCKS);

  return INTOBJ_INT(blocks_get_cpp(x)->degree());
}

// Returns the rank of a GAP blocks from the C++ object. The rank of a blocks
// object is the number of transverse blocks (equivalently the number of blocks
// consisting of positive integers).

Obj BLOCKS_RANK(Obj self, Obj x) {
  SEMIGROUPS_ASSERT(TNUM_OBJ(x) == T_BLOCKS);

  return INTOBJ_INT(blocks_get_cpp(x)->rank());
}

// Returns the number of blocks in the partition represented by the GAP blocks
// object.

Obj BLOCKS_NR_BLOCKS(Obj self, Obj x) {
  SEMIGROUPS_ASSERT(TNUM_OBJ(x) == T_BLOCKS);

  return INTOBJ_INT(blocks_get_cpp(x)->number_of_blocks());
}

// Returns an idempotent GAP bipartition whose left and right blocks equal the
// GAP blocks object x.

Obj BLOCKS_PROJ(Obj self, Obj x) {
  SEMIGROUPS_ASSERT(TNUM_OBJ(x) == T_BLOCKS);

  Blocks& blocks = *blocks_get_cpp(x);

  _BUFFER_size_t.clear();
  _BUFFER_size_t.resize(blocks.number_of_blocks(), -1);

  std::vector<uint32_t> out(2 * blocks.degree());
  uint32_t              nr_blocks = blocks.number_of_blocks();

  for (uint32_t i = 0; i < blocks.degree(); i++) {
    uint32_t index = blocks[i];
    out[i]         = index;
    if (blocks.is_transverse_block(index)) {
      out[i + blocks.degree()] = index;
    } else {
      if (_BUFFER_size_t[index] == static_cast<size_t>(-1)) {
        _BUFFER_size_t[index] = nr_blocks;
        nr_blocks++;
      }
      out[i + blocks.degree()] = _BUFFER_size_t[index];
    }
  }
  return bipart_new_obj(new Bipartition(out));
}

// Check if two GAP blocks objects are equal.

Int BLOCKS_EQ(Obj x, Obj y) {
  SEMIGROUPS_ASSERT(TNUM_OBJ(x) == T_BLOCKS);
  SEMIGROUPS_ASSERT(TNUM_OBJ(y) == T_BLOCKS);

  return (*blocks_get_cpp(x) == *blocks_get_cpp(y) ? 1L : 0L);
}

// Check if x < y, when x and y are GAP blocks objects.

Int BLOCKS_LT(Obj x, Obj y) {
  SEMIGROUPS_ASSERT(TNUM_OBJ(x) == T_BLOCKS);
  SEMIGROUPS_ASSERT(TNUM_OBJ(y) == T_BLOCKS);

  return (*blocks_get_cpp(x) < *blocks_get_cpp(y) ? 1L : 0L);
}

// Returns True if there is an idempotent bipartition with left blocks equal to
// left_gap and right blocks equal to right_gap.

Obj BLOCKS_E_TESTER(Obj self, Obj left_gap, Obj right_gap) {
  SEMIGROUPS_ASSERT(TNUM_OBJ(left_gap) == T_BLOCKS);
  SEMIGROUPS_ASSERT(TNUM_OBJ(right_gap) == T_BLOCKS);

  Blocks* left  = blocks_get_cpp(left_gap);
  Blocks* right = blocks_get_cpp(right_gap);

  if (left->rank() != right->rank()) {
    return False;
  } else if (left->rank() == 0) {
    return True;
  }

  // prepare the _BUFFER_bool for detecting transverse fused blocks
  _BUFFER_bool.clear();
  _BUFFER_bool.resize(right->number_of_blocks() + 2 * left->number_of_blocks());
  std::copy(right->cbegin_lookup(),
            right->cend_lookup(),
            _BUFFER_bool.begin() + left->number_of_blocks());
  auto seen = _BUFFER_bool.begin() + right->number_of_blocks()
              + left->number_of_blocks();

  // after the following line:
  //
  // 1) [_BUFFER_size_t.begin() .. _BUFFER_size_t.begin() + left_nr_blocks +
  //    right_nr_blocks - 1] is the fuse table for left and right
  //
  // 2) _BUFFER_bool is a lookup for the transverse blocks of the fused left
  //     and right

  fuse(left->degree(),
       left->cbegin(),
       left->number_of_blocks(),
       right->cbegin(),
       right->number_of_blocks(),
       true);

  // check we are injective on transverse blocks of <left> and that the fused
  // blocks are also transverse.

  for (uint32_t i = 0; i < left->number_of_blocks(); i++) {
    if (left->is_transverse_block(i)) {
      size_t j = fuse_it(i);
      if (!_BUFFER_bool[j] || seen[j]) {
        return False;
      }
      seen[j] = true;
    }
  }
  return True;
}

// Returns the idempotent bipartition with left blocks equal to
// left_gap and right blocks equal to right_gap, assuming that this exists.

Obj BLOCKS_E_CREATOR(Obj self, Obj left_gap, Obj right_gap) {
  SEMIGROUPS_ASSERT(TNUM_OBJ(left_gap) == T_BLOCKS);
  SEMIGROUPS_ASSERT(TNUM_OBJ(right_gap) == T_BLOCKS);
  SEMIGROUPS_ASSERT(BLOCKS_E_TESTER(self, left_gap, right_gap) == True);

  Blocks* left  = blocks_get_cpp(left_gap);
  Blocks* right = blocks_get_cpp(right_gap);

  fuse(left->degree(),
       left->cbegin(),
       left->number_of_blocks(),
       right->cbegin(),
       right->number_of_blocks(),
       false);

  _BUFFER_size_t.resize(
      3 * (left->number_of_blocks() + right->number_of_blocks()), 0);
  std::fill(_BUFFER_size_t.begin()
                + 2 * (left->number_of_blocks() + right->number_of_blocks()),
            _BUFFER_size_t.begin()
                + 3 * (left->number_of_blocks() + right->number_of_blocks()),
            -1);

  auto tab1 = _BUFFER_size_t.begin() + left->number_of_blocks()
              + right->number_of_blocks();
  auto tab2 = _BUFFER_size_t.begin()
              + 2 * (left->number_of_blocks() + right->number_of_blocks());

  // find new names for the signed blocks of right
  for (size_t i = 0; i < right->number_of_blocks(); i++) {
    if (right->is_transverse_block(i)) {
      tab1[fuse_it(i + left->number_of_blocks())] = i;
    }
  }

  std::vector<uint32_t> blocks(2 * left->degree());

  size_t next = right->number_of_blocks();

  for (size_t i = 0; i < left->degree(); i++) {
    blocks[i] = (*right)[i];
    size_t j  = (*left)[i];
    if (left->is_transverse_block(j)) {
      blocks[i + left->degree()] = tab1[fuse_it(j)];
    } else {
      if (tab2[j] == static_cast<size_t>(-1)) {
        tab2[j] = next;
        next++;
      }
      blocks[i + left->degree()] = tab2[j];
    }
  }

  Bipartition* out = new Bipartition(blocks);
  out->set_number_of_blocks(next);
  out->set_number_of_left_blocks(right->number_of_blocks());

  return bipart_new_obj(out);
}

// Returns the left blocks of BLOCKS_PROJ(blocks_gap) * x_gap where the latter
// is a GAP bipartition.

Obj BLOCKS_LEFT_ACT(Obj self, Obj blocks_gap, Obj x_gap) {
  SEMIGROUPS_ASSERT(TNUM_OBJ(x_gap) == T_BIPART);
  SEMIGROUPS_ASSERT(TNUM_OBJ(blocks_gap) == T_BLOCKS);

  Bipartition* x      = bipart_get_cpp(x_gap);
  Blocks*      blocks = blocks_get_cpp(blocks_gap);

  if (blocks->degree() != x->degree()) {
    // hack to allow Lambda/RhoOrbSeed
    return blocks_new_obj(x->left_blocks());
  } else if (blocks->degree() == 0) {
    return blocks_gap;
  }

  // prepare the _BUFFER_bool for detecting transverse fused blocks
  _BUFFER_bool.clear();
  _BUFFER_bool.resize(x->number_of_blocks() + blocks->number_of_blocks());
  std::copy(blocks->cbegin_lookup(),
            blocks->cend_lookup(),
            _BUFFER_bool.begin() + x->number_of_blocks());

  fuse(x->degree(),
       x->cbegin() + x->degree(),
       x->number_of_blocks(),
       blocks->cbegin(),
       blocks->number_of_blocks(),
       true);

  _BUFFER_size_t.resize(
      2 * (x->number_of_blocks() + blocks->number_of_blocks()), -1);
  auto tab = _BUFFER_size_t.begin() + x->number_of_blocks()
             + blocks->number_of_blocks();

  Blocks* out_blocks = new Blocks(x->degree());

  uint32_t next = 0;
  for (uint32_t i = 0; i < x->degree(); i++) {
    uint32_t j = fuse_it(x->at(i));
    if (tab[j] == static_cast<size_t>(-1)) {
      tab[j] = next;
      next++;
    }
    out_blocks->set_block(i, tab[j]);
    out_blocks->set_is_transverse_block(tab[j], _BUFFER_bool[j]);
  }

#ifdef SEMIGROUPS_KERNEL_DEBUG
  libsemigroups::validate(*out_blocks);
#endif

  return blocks_new_obj(out_blocks);
}

// Returns the right blocks of x_gap * BLOCKS_PROJ(blocks_gap) where the former
// is a GAP bipartition.

Obj BLOCKS_RIGHT_ACT(Obj self, Obj blocks_gap, Obj x_gap) {
  SEMIGROUPS_ASSERT(TNUM_OBJ(x_gap) == T_BIPART);
  SEMIGROUPS_ASSERT(TNUM_OBJ(blocks_gap) == T_BLOCKS);

  Bipartition* x      = bipart_get_cpp(x_gap);
  Blocks*      blocks = blocks_get_cpp(blocks_gap);

  if (blocks->degree() != x->degree()) {
    // hack to allow Lambda/RhoOrbSeed
    return blocks_new_obj(x->right_blocks());
  } else if (blocks->degree() == 0) {
    return blocks_gap;
  }

  // prepare the _BUFFER_bool for detecting transverse fused blocks
  _BUFFER_bool.clear();
  _BUFFER_bool.resize(x->number_of_blocks() + blocks->number_of_blocks());
  std::copy(
      blocks->cbegin_lookup(), blocks->cend_lookup(), _BUFFER_bool.begin());

  fuse(x->degree(),
       blocks->cbegin(),
       blocks->number_of_blocks(),
       x->cbegin(),
       x->number_of_blocks(),
       true);

  _BUFFER_size_t.resize(
      2 * (x->number_of_blocks() + blocks->number_of_blocks()), -1);
  auto tab = _BUFFER_size_t.begin() + x->number_of_blocks()
             + blocks->number_of_blocks();

  Blocks*        out_blocks = new Blocks(x->degree());
  uint32_t       next       = 0;
  uint32_t const n          = x->degree();
  for (uint32_t i = n; i < 2 * n; i++) {
    uint32_t j = fuse_it(x->at(i) + blocks->number_of_blocks());
    if (tab[j] == static_cast<size_t>(-1)) {
      tab[j] = next;
      next++;
    }
    out_blocks->set_block(i - n, tab[j]);
    out_blocks->set_is_transverse_block(tab[j], _BUFFER_bool[j]);
  }
#ifdef SEMIGROUPS_KERNEL_DEBUG
  libsemigroups::validate(*out_blocks);
#endif
  return blocks_new_obj(out_blocks);
}

// Returns a GAP bipartition y such that if BLOCKS_LEFT_ACT(blocks_gap, x_gap)
// = Y, then BLOCKS_LEFT_ACT(Y, y) = blocks_gap, and y acts on Y as the inverse
// of x_gap on Y.

Obj BLOCKS_INV_LEFT(Obj self, Obj blocks_gap, Obj x_gap) {
  SEMIGROUPS_ASSERT(TNUM_OBJ(blocks_gap) == T_BLOCKS);
  SEMIGROUPS_ASSERT(TNUM_OBJ(x_gap) == T_BIPART);
  Blocks*      blocks = blocks_get_cpp(blocks_gap);
  Bipartition* x      = bipart_get_cpp(x_gap);
  SEMIGROUPS_ASSERT(x->degree() == blocks->degree());

  fuse(x->degree(),
       blocks->cbegin(),
       blocks->number_of_blocks(),
       x->cbegin() + x->degree(),
       x->number_of_blocks(),
       false);
  SEMIGROUPS_ASSERT(_BUFFER_size_t.size()
                    == blocks->number_of_blocks() + x->number_of_blocks());

  std::vector<uint32_t> out_blocks(2 * x->degree());

  _BUFFER_size_t.resize(2 * blocks->number_of_blocks() + x->number_of_blocks(),
                        -1);
  SEMIGROUPS_ASSERT(_BUFFER_size_t.size()
                    == 2 * blocks->number_of_blocks() + x->number_of_blocks());
  SEMIGROUPS_ASSERT(std::all_of(
      _BUFFER_size_t.cbegin() + blocks->number_of_blocks()
          + x->number_of_blocks(),
      _BUFFER_size_t.cend(),
      [](size_t i) -> bool { return i == static_cast<size_t>(-1); }));
  auto tab = _BUFFER_size_t.begin() + blocks->number_of_blocks()
             + x->number_of_blocks();
  SEMIGROUPS_ASSERT(_BUFFER_size_t.end() - tab == blocks->number_of_blocks());

  for (uint32_t i = 0; i < blocks->number_of_blocks(); i++) {
    if (blocks->is_transverse_block(i)) {
      SEMIGROUPS_ASSERT(fuse_it(i) < blocks->number_of_blocks());
      SEMIGROUPS_ASSERT(tab + fuse_it(i) < _BUFFER_size_t.end());
      tab[fuse_it(i)] = i;
    }
  }

  // find the left blocks of the output
  for (uint32_t i = 0; i < blocks->degree(); i++) {
    out_blocks[i] = (*blocks)[i];
    uint32_t j    = fuse_it(x->at(i) + blocks->number_of_blocks());
    if (j >= blocks->number_of_blocks() || tab[j] == static_cast<size_t>(-1)) {
      out_blocks[i + x->degree()] = blocks->number_of_blocks();  // junk
    } else {
      out_blocks[i + x->degree()] = tab[j];
    }
  }

  Bipartition* out = new Bipartition(out_blocks);
  out->set_number_of_left_blocks(blocks->number_of_blocks());

  return bipart_new_obj(out);
}

// Returns a GAP bipartition y such that if BLOCKS_RIGHT_ACT(blocks_gap, x_gap)
// = Y, then BLOCKS_RIGHT_ACT(Y, y) = blocks_gap, and y acts on Y as the inverse
// of x_gap on Y.
//
// We fuse <blocks_gap> with the left blocks of <x_gap> keeping track of
// the signs of the fused classes.
//
// The left blocks of the output are then:
//
// 1) disconnected right blocks of <x_gap> (before fusing)
//
// 2) disconnected right blocks of <x_gap> (after fusing)
//
// 3) connected right blocks of <x_gap> (after fusing)
//
// both types 1+2 of the disconnected blocks are unioned into one left block of
// the output with index <junk>. The connected blocks 3 of <x_gap> are given the
// next
// available index, if they have not been seen before. The table <tab1> keeps
// track of which connected right blocks of <x_gap> have been seen before and
// the
// corresponding index in the output, i.e. <tab1[x]> is the index in <out> of
// the
// fused block with index <x>.
//
// The right blocks of the output are:
//
// 1) disconnected blocks of <blocks_gap>; or
//
// 2) connected blocks of <blocks_gap>.
//
// The disconnected blocks 1 are given the next available index, if they have
// not
// been seen before. The table <tab2> keeps track of which disconnected blocks
// of
// <blocks_gap> have been seen before and the corresponding index in the output,
// i.e.
// <tab2[x]> is the index in <out> of the disconnected block of <blocks_gap>
// with
// index <x>. The connected blocks 2 of <blocks_gap> is given the index
// <tab1[x]>
// where <x> is the fused index of the block.

Obj BLOCKS_INV_RIGHT(Obj self, Obj blocks_gap, Obj x_gap) {
  Blocks*      blocks = blocks_get_cpp(blocks_gap);
  Bipartition* x      = bipart_get_cpp(x_gap);

  // prepare _BUFFER_bool for fusing

  _BUFFER_bool.clear();
  _BUFFER_bool.resize(blocks->number_of_blocks() + x->number_of_blocks());
  std::copy(
      blocks->cbegin_lookup(), blocks->cend_lookup(), _BUFFER_bool.begin());

  fuse(x->degree(),
       blocks->cbegin(),
       blocks->number_of_blocks(),
       x->cbegin(),
       x->number_of_blocks(),
       true);

  uint32_t junk = -1;
  uint32_t next = 0;

  std::vector<uint32_t> out_blocks(2 * x->degree());

  _BUFFER_size_t.resize(
      3 * blocks->number_of_blocks() + 2 * x->number_of_blocks(), -1);
  auto tab1 = _BUFFER_size_t.begin() + blocks->number_of_blocks()
              + x->number_of_blocks();
  auto tab2 = _BUFFER_size_t.begin()
              + 2 * (blocks->number_of_blocks() + x->number_of_blocks());

  // find the left blocks of the output
  for (uint32_t i = 0; i < blocks->degree(); i++) {
    if (x->at(i + x->degree()) < x->number_of_left_blocks()) {
      uint32_t j = fuse_it(x->at(i + x->degree()) + blocks->number_of_blocks());
      if (_BUFFER_bool[j]) {
        if (tab1[j] == static_cast<size_t>(-1)) {
          tab1[j] = next;
          next++;
        }
        out_blocks[i] = tab1[j];
        continue;
      }
    }
    if (junk == (uint32_t) -1) {
      junk = next;
      next++;
    }
    out_blocks[i] = junk;
  }

  uint32_t out_nr_left_blocks = next;

  // find the right blocks of the output

  for (uint32_t i = blocks->degree(); i < 2 * blocks->degree(); i++) {
    uint32_t j = (*blocks)[i - blocks->degree()];
    if (blocks->is_transverse_block(j)) {
      out_blocks[i] = tab1[fuse_it(j)];
    } else {
      if (tab2[j] == static_cast<size_t>(-1)) {
        tab2[j] = next;
        next++;
      }
      out_blocks[i] = tab2[j];
    }
  }

  Bipartition* out = new Bipartition(out_blocks);
  out->set_number_of_left_blocks(out_nr_left_blocks);
  out->set_number_of_blocks(next);
  return bipart_new_obj(out);
}

////////////////////////////////////////////////////////////////////////////////
// Non-GAP functions
////////////////////////////////////////////////////////////////////////////////

// The functions below do the Union-Find algorithm for finding the least
// equivalence relation containing two other equivalence relations. These are
// used by many of the functions above for blocks.

// Returns the class containing the number i (i.e. this is the Find part of
// Union-Find). This strongly relies on everything being set up correctly.

static inline size_t fuse_it(size_t i) {
  while (_BUFFER_size_t[i] < i) {
    i = _BUFFER_size_t[i];
  }
  return i;
}

// This function performs Union-Find to find the least equivalence relation
// containing the equivalence relations starting at left_begin, and
// right_begin (named left and right below).
//
// If it = left_begin or right_begin, then it must be an iterator such that:
//
//   * it.end() >= it.begin() + deg
//
//   * *(it.begin() + i) is the index of the block containing i in the
//   equivalence relation represented by it
//
//   * left_nr_blocks/right_nr_blocks is the number of blocks in the
//   equivalence relation represented by left_begin/right_begin.
//
//   * if we want to keep track of transverse blocks, then sign should be true,
//   otherwise it is false.
//
// After running fuse:
//
// 1) [_BUFFER_size_t.begin() .. _BUFFER_size_t.begin() + left_nr_blocks +
//    right_nr_blocks - 1] is the fuse table for left and right
//
// 2) If sign == true, then _BUFFER_bool is a lookup for the transverse blocks
//    of the fused left and right
//
// Note that _BUFFER_bool has to be pre-assigned with the correct values, i.e.
// it must be at least initialized (and have the appropriate length).

static void fuse(uint32_t                                       deg,
                 typename std::vector<uint32_t>::const_iterator left_begin,
                 uint32_t                                       left_nr_blocks,
                 typename std::vector<uint32_t>::const_iterator right_begin,
                 uint32_t                                       right_nr_blocks,
                 bool                                           sign) {
  _BUFFER_size_t.clear();
  _BUFFER_size_t.reserve(left_nr_blocks + right_nr_blocks);

  for (size_t i = 0; i < left_nr_blocks + right_nr_blocks; i++) {
    _BUFFER_size_t.push_back(i);
  }

  for (auto left_it = left_begin, right_it = right_begin;
       left_it < left_begin + deg;
       left_it++, right_it++) {
    size_t j = fuse_it(*left_it);
    size_t k = fuse_it(*right_it + left_nr_blocks);

    if (j != k) {
      if (j < k) {
        _BUFFER_size_t[k] = j;
        if (sign && _BUFFER_bool[k]) {
          _BUFFER_bool[j] = true;
        }
      } else {
        _BUFFER_size_t[j] = k;
        if (sign && _BUFFER_bool[j]) {
          _BUFFER_bool[k] = true;
        }
      }
    }
  }
}

////////////////////////////////////////////////////////////////////////////////
// Counting idempotents in regular *-semigroups of bipartitions
////////////////////////////////////////////////////////////////////////////////

// The class and functions below implement a parallel idempotent counting
// method for regular *-semigroups of bipartitions.

// IdempotentCounter is a class for containing the data required for the
// search for idempotents.

class IdempotentCounter {
  typedef std::vector<std::vector<size_t>> thrds_size_t;
  typedef std::vector<std::vector<bool>>   thrds_bool_t;
  typedef std::pair<size_t, size_t>        unpr_t;
  typedef std::vector<std::vector<unpr_t>> thrds_unpr_t;

 public:
  IdempotentCounter(Obj orbit, Obj scc, Obj lookup, unsigned int nr_threads)
      : _nr_threads(std::min(nr_threads, std::thread::hardware_concurrency())),
        _fuse_tab(thrds_size_t(_nr_threads, std::vector<size_t>())),
        _lookup(thrds_bool_t(_nr_threads, std::vector<bool>())),
        _min_scc(),
        _orbit(),
        _scc(),
        _scc_pos(std::vector<size_t>(LEN_LIST(orbit), 0)),
        _seen(thrds_bool_t(_nr_threads, std::vector<bool>())),
        _threads(),
        _unprocessed(thrds_unpr_t(_nr_threads, std::vector<unpr_t>())),
        _vals(thrds_size_t(_nr_threads,
                           std::vector<size_t>(LEN_PLIST(scc) - 1, 0))) {
    // copy the GAP blocks from the orbit into _orbit
    _orbit.reserve(LEN_LIST(orbit));
    for (Int i = 2; i <= LEN_LIST(orbit); i++) {
      _orbit.push_back(blocks_get_cpp(ELM_LIST(orbit, i)));
    }

    size_t total_load = 0;
    size_t min_rank   = -1;
    // copy the scc from GAP to C++
    for (Int i = 2; i <= LEN_PLIST(scc); i++) {
      Obj comp = ELM_PLIST(scc, i);

      _scc.push_back(std::vector<size_t>());
      _scc.back().reserve(LEN_PLIST(comp));

      for (Int j = 1; j <= LEN_PLIST(comp); j++) {
        _scc.back().push_back(INT_INTOBJ(ELM_PLIST(comp, j)) - 2);
        _scc_pos[INT_INTOBJ(ELM_PLIST(comp, j)) - 2] = j - 1;
      }
      _ranks.push_back(_orbit[_scc.back()[0]]->rank());
      if (_ranks.back() < min_rank) {
        min_rank = _ranks.back();
        _min_scc = i - 2;
      }
      total_load += _scc.back().size() * (_scc.back().size() - 1) / 2;
    }

    total_load -= (_scc[_min_scc].size() * (_scc[_min_scc].size() - 1) / 2);

    // queue pairs for each thread
    size_t mean_load   = total_load / _nr_threads;
    size_t thread_id   = 0;
    size_t thread_load = 0;

    for (size_t i = 0; i < _orbit.size(); i++) {
      size_t comp = INT_INTOBJ(ELM_PLIST(lookup, i + 2)) - 2;
      if (comp != _min_scc) {
        _unprocessed[thread_id].push_back(std::make_pair(i, comp));
        thread_load += _scc[comp].size() - _scc_pos[i];
        if (thread_load >= mean_load && thread_id != _nr_threads - 1) {
          thread_id++;
          thread_load = 0;
        }
      }
    }
  }

  std::vector<size_t> count() {
    libsemigroups::detail::reset_thread_ids();
    libsemigroups::report_default("using {} / {} additional threads",
                   _nr_threads,
                   std::thread::hardware_concurrency());
    Timer timer;

    for (size_t i = 0; i < _nr_threads; i++) {
      _threads.push_back(
          std::thread(&IdempotentCounter::thread_counter, this, i));
    }

    for (size_t i = 0; i < _nr_threads; i++) {
      _threads[i].join();
    }

        libsemigroups::report_elapsed_time("", timer);

    size_t              max = *max_element(_ranks.begin(), _ranks.end()) + 1;
    std::vector<size_t> out = std::vector<size_t>(max, 0);

    for (size_t j = 0; j < _scc.size(); j++) {
      size_t rank = _ranks[j];
      if (j != _min_scc) {
        for (size_t i = 0; i < _nr_threads; i++) {
          out[rank] += _vals[i][j];
        }

      } else {
        out[rank] += _scc[_min_scc].size() * _scc[_min_scc].size();
      }
    }

    return out;
  }

 private:
  void thread_counter(size_t thread_id) {
    Timer timer;

    for (unpr_t index : _unprocessed[thread_id]) {
      if (tester(thread_id, index.first, index.first)) {
        _vals[thread_id][index.second]++;
      }
      std::vector<size_t> comp  = _scc[index.second];
      auto                begin = comp.begin() + _scc_pos[index.first] + 1;
      for (auto it = begin; it < comp.end(); it++) {
        if (tester(thread_id, index.first, *it)) {
          _vals[thread_id][index.second] += 2;
        }
      }
    }
        libsemigroups::report_default("finished in {}", timer);
  }

  // This is basically the same as BLOCKS_E_TESTER, but is required because we
  // must have different temporary storage for every thread.
  bool tester(size_t thread_id, size_t i, size_t j) {
    Blocks* left  = _orbit[i];
    Blocks* right = _orbit[j];

    // prepare the _lookup for detecting transverse fused blocks
    _lookup[thread_id].clear();
    _lookup[thread_id].resize(right->number_of_blocks()
                              + left->number_of_blocks());
    std::copy(right->cbegin_lookup(),
              right->cend_lookup(),
              _lookup[thread_id].begin() + left->number_of_blocks());

    _seen[thread_id].clear();
    _seen[thread_id].resize(left->number_of_blocks());

    // prepare the _fuse_tab
    _fuse_tab[thread_id].clear();
    _fuse_tab[thread_id].reserve(left->number_of_blocks()
                                 + right->number_of_blocks());

    for (size_t k = 0; k < left->number_of_blocks() + right->number_of_blocks();
         k++) {
      _fuse_tab[thread_id].push_back(k);
    }

    for (auto left_it = left->cbegin(), right_it = right->cbegin();
         left_it < left->cbegin() + left->degree();
         left_it++, right_it++) {
      size_t k = fuse_it(thread_id, *left_it);
      size_t l = fuse_it(thread_id, *right_it + left->number_of_blocks());

      if (k != l) {
        if (k < l) {
          _fuse_tab[thread_id][l] = k;
          if (_lookup[thread_id][l]) {
            _lookup[thread_id][k] = true;
          }
        } else {
          _fuse_tab[thread_id][k] = l;
          if (_lookup[thread_id][k]) {
            _lookup[thread_id][l] = true;
          }
        }
      }
    }

    for (uint32_t k = 0; k < left->number_of_blocks(); k++) {
      if (left->is_transverse_block(k)) {
        size_t l = fuse_it(thread_id, k);
        if (!_lookup[thread_id][l] || _seen[thread_id][l]) {
          return false;
        }
        _seen[thread_id][l] = true;
      }
    }
    return true;
  }

  inline size_t fuse_it(size_t thread_id, size_t i) {
    while (_fuse_tab[thread_id][i] < i) {
      i = _fuse_tab[thread_id][i];
    }
    return i;
  }

  size_t               _nr_threads;
  thrds_size_t         _fuse_tab;
  thrds_bool_t         _lookup;
  size_t               _min_scc;
  std::vector<Blocks*> _orbit;
  std::vector<size_t>  _ranks;
  thrds_size_t         _scc;
  std::vector<size_t>  _scc_pos;
  // _scc_pos[i] is the position of _orbit[i] in its scc
  thrds_bool_t             _seen;
  std::vector<std::thread> _threads;
  thrds_unpr_t             _unprocessed;
  thrds_size_t             _vals;
  // map from the scc indices to the rank of elements in that scc
};

// GAP-level function

Obj BIPART_NR_IDEMPOTENTS(Obj self,
                          Obj o,
                          Obj scc,
                          Obj lookup,
                          Obj nr_threads) {
  IdempotentCounter   finder(o, scc, lookup, INT_INTOBJ(nr_threads));
  std::vector<size_t> vals = finder.count();

  Obj out = NEW_PLIST(T_PLIST_CYC, vals.size());
  SET_LEN_PLIST(out, vals.size());

  for (size_t i = 1; i <= vals.size(); i++) {
    SET_ELM_PLIST(out, i, INTOBJ_INT(vals[i - 1]));
  }

  return out;
}
