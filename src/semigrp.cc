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
// along with this program.  If not, see <http://www.gnu.org/licenses/>.
//

#include "semigrp.h"

#include <utility>

#include "bipart.h"
#include "converter.h"
#include "fropin.h"
#include "gap.h"
#include "src/compiled.h"

#define DEBUG

#ifdef DEBUG
#define SEMI_OBJ_CHECK_ARG(so)                                                 \
  if (CALL_1ARGS(IsSemigroup, so) != True) {                                   \
    ErrorQuit(                                                                 \
        "the argument must be a semigroup not a %s,", (Int) TNAM_OBJ(so), 0L); \
  }
#define PLIST_CHECK_ARG(obj)                                                \
  if (!IS_PLIST(obj)) {                                                     \
    ErrorQuit(                                                              \
        "the argument must be a plist not a %s,", (Int) TNAM_OBJ(obj), 0L); \
  }
#define INTOBJ_CHECK_ARG(obj)                                      \
  if (!IS_INTOBJ(obj) || INT_INTOBJ(obj) < 0) {                    \
    ErrorQuit("the argument must be a positive integer not a %s,", \
              (Int) TNAM_OBJ(obj),                                 \
              0L);                                                 \
  }
#define EN_SEMI_CHECK_ARG(es)                                \
  if (TNUM_OBJ(es) != T_SEMI                                 \
      || SUBTYPE_OF_T_SEMI(es) != T_SEMI_SUBTYPE_ENSEMI) {   \
    ErrorQuit("the argument must be a T_SEMI Obj of subtype" \
              " T_SEMI_SUBTYPE_ENSEMI not a %s,",            \
              (Int) TNAM_OBJ(es),                            \
              0L);                                           \
  }
#else
#define SEMI_OBJ_CHECK_ARG(so)
#define PLIST_CHECK_ARG(obj)
#define INTOBJ_CHECK_ARG(obj)
#define EN_SEMI_CHECK_ARG(es)
#endif

// RNams
static Int RNam_GeneratorsOfMagma = RNamName("GeneratorsOfMagma");
static Int RNam_Representative    = RNamName("Representative");

// static Int RNam_batch_size        = RNamName("batch_size");
static Int RNam_ht      = RNamName("ht");
static Int RNam_nr      = RNamName("nr");
static Int RNam_nrrules = RNamName("nrrules");
static Int RNam_opts    = RNamName("opts");
static Int RNam_parent  = RNamName("parent");
// static Int RNam_report            = RNamName("report");

static Int RNam_en_semi_cpp = RNamName("__en_semi_cpp_data");
static Int RNam_en_semi_frp = RNamName("__en_semi_frp_data");

// TODO initRnams function

std::vector<Element*>*
plist_to_vec(Converter* converter, gap_plist_t elements, size_t degree) {

  assert(IS_PLIST(elements));

  auto out = new std::vector<Element*>();

  for (size_t i = 0; i < (size_t) LEN_PLIST(elements); i++) {
    out->push_back(converter->convert(ELM_LIST(elements, i + 1), degree));
  }
  return out;
}

template <typename T>
static inline gap_plist_t vec_to_plist(Converter* converter, T* cont) {
  gap_plist_t out = NEW_PLIST(T_PLIST, cont->size());
  SET_LEN_PLIST(out, cont->size());
  size_t i = 1;
  for (auto x : *cont) {
    SET_ELM_PLIST(out, i++, converter->unconvert(x));
    CHANGED_BAG(out);
  }
  return out;
}

gap_plist_t word_t_to_plist(word_t const& word) {
  gap_plist_t out = NEW_PLIST(T_PLIST_CYC, word.size());
  SET_LEN_PLIST(out, word.size());

  for (size_t i = 0; i < word.size(); i++) {
    SET_ELM_PLIST(out, i + 1, INTOBJ_INT(word[i] + 1));
  }
  CHANGED_BAG(out);
  return out;
}

gap_plist_t cayley_graph_t_to_plist(cayley_graph_t* graph) {

  assert(graph->size() != 0);
  gap_plist_t out = NEW_PLIST(T_PLIST, graph->nr_rows());
  SET_LEN_PLIST(out, graph->nr_rows());

  for (size_t i = 0; i < graph->nr_rows(); i++) {
    gap_plist_t next = NEW_PLIST(T_PLIST_CYC, graph->nr_cols());
    SET_LEN_PLIST(next, graph->nr_cols());
    typename std::vector<size_t>::const_iterator end = graph->row_cend(i);
    size_t                                       j   = 1;
    for (auto it = graph->row_cbegin(i); it != end; ++it) {
      SET_ELM_PLIST(next, j++, INTOBJ_INT(*it + 1));
    }
    SET_ELM_PLIST(out, i + 1, next);
    CHANGED_BAG(out);
  }
  return out;
}

// TODO this should go elsewhere
template <typename T> static inline void really_delete_cont(T* cont) {

  for (Element* x : *cont) {
    x->really_delete();
  }
  delete cont;
}

// Semigroups

gap_plist_t semi_obj_get_gens(gap_semigroup_t so) {
  SEMI_OBJ_CHECK_ARG(so);
  initRNams();
  UInt i;
  if (FindPRec(so, RNam_GeneratorsOfMagma, &i, 1)) {
    Obj gens = GET_ELM_PREC(so, i);
    PLAIN_LIST(gens);
    CHANGED_BAG(so);
    return gens;
  } else {
    CALL_1ARGS(GeneratorsOfMagma, so);
    if (FindPRec(so, RNam_GeneratorsOfMagma, &i, 1)) {
      Obj gens = GET_ELM_PREC(so, i);
      PLAIN_LIST(gens);
      CHANGED_BAG(so);
      return gens;
    }
    ErrorQuit("cannot find generators of the semigroup,", 0L, 0L);
    return 0L;
  }
}

Obj semi_obj_get_rep(gap_semigroup_t so) {
  SEMI_OBJ_CHECK_ARG(so);
  initRNams();
  UInt i;
  if (FindPRec(so, RNam_Representative, &i, 1)) {
    return GET_ELM_PREC(so, i);
  } else {
    gap_plist_t gens = semi_obj_get_gens(so);
    if (LEN_PLIST(gens) > 0) {
      return ELM_PLIST(gens, 1);
    } else {
      ErrorQuit("cannot find a representative of the semigroup,", 0L, 0L);
      return 0L;
    }
  }
}

size_t semi_obj_get_batch_size(gap_semigroup_t so) {
  SEMI_OBJ_CHECK_ARG(so);
  initRNams();
  UInt i;
  if (FindPRec(so, RNam_opts, &i, 1)) {
    gap_prec_t opts = GET_ELM_PREC(so, i);
    if (FindPRec(opts, RNam_batch_size, &i, 1)) {
      return INT_INTOBJ(GET_ELM_PREC(opts, i));
    }
  }
#ifdef DEBUG
  Pr("Using default value of 8192 for reporting!\n", 0L, 0L);
#endif
  return 8192;
}

static inline bool semi_obj_get_report(gap_semigroup_t so) {
  SEMI_OBJ_CHECK_ARG(so);

  initRNams();
  UInt i;
  if (FindPRec(so, RNam_opts, &i, 1)) {
    Obj opts = GET_ELM_PREC(so, i);
    if (FindPRec(opts, RNam_report, &i, 1)) {
      return (GET_ELM_PREC(opts, i) == True ? true : false);
    }
  }
#ifdef DEBUG
  Pr("Using default value of <false> for reporting!\n", 0L, 0L);
#endif
  return false;
}

static inline size_t semi_obj_get_nr_threads(gap_semigroup_t so) {
  SEMI_OBJ_CHECK_ARG(so);
  initRNams();
  UInt i;
  if (FindPRec(so, RNam_opts, &i, 1)) {
    Obj opts = GET_ELM_PREC(so, i);
    if (FindPRec(opts, RNam_nr_threads, &i, 1)) {
      return INT_INTOBJ(GET_ELM_PREC(opts, i));
    }
  }
#ifdef DEBUG
  Pr("Using default value of 1 for number of threads!\n", 0L, 0L);
#endif
  return 1;
}

static inline size_t semi_obj_get_threshold(gap_semigroup_t so) {
  SEMI_OBJ_CHECK_ARG(so);
  initRNams();
  Obj x = semi_obj_get_rep(so);
  assert(TNUM_OBJ(x) == T_POSOBJ);
  assert(CALL_1ARGS(IsTropicalMatrix, x) || CALL_1ARGS(IsNTPMatrix, x));
  assert(ELM_PLIST(x, 1) != 0);
  assert(IS_PLIST(ELM_PLIST(x, 1)));
  assert(ELM_PLIST(x, LEN_PLIST(ELM_PLIST(x, 1)) + 1) != 0);

  return INT_INTOBJ(ELM_PLIST(x, LEN_PLIST(ELM_PLIST(x, 1)) + 1));
}

static inline size_t semi_obj_get_period(gap_semigroup_t so) {
  SEMI_OBJ_CHECK_ARG(so);
  initRNams();
  Obj x = semi_obj_get_rep(so);
  assert(TNUM_OBJ(x) == T_POSOBJ);
  assert(CALL_1ARGS(IsNTPMatrix, x));
  assert(ELM_PLIST(x, 1) != 0);
  assert(IS_PLIST(ELM_PLIST(x, 1)));
  assert(ELM_PLIST(x, LEN_PLIST(ELM_PLIST(x, 1)) + 2) != 0);

  return INT_INTOBJ(ELM_PLIST(x, LEN_PLIST(ELM_PLIST(x, 1)) + 2));
}

// Enumerable semigroups

/*enum en_semi_t {
  UNKNOWN,
  TRANS2,
  TRANS4,
  PPERM2,
  PPERM4,
  BOOL_MAT,
  BIPART,
  MAX_PLUS_MAT,
  MIN_PLUS_MAT,
  TROP_MAX_PLUS_MAT,
  TROP_MIN_PLUS_MAT,
  PROJ_MAX_PLUS_MAT,
  NTP_MAT,
  INT_MAT,
  MAT_OVER_PF,
  PBR_TYPE
};*/

// Initialise the en_semi of the GAP semigroup Obj <so>, the optional 2nd and
// 3rd args are for use with closure semigroup.

Obj semi_obj_init_en_semi(gap_semigroup_t so,
                          gap_semigroup_t old_so = 0,
                          gap_plist_t     plist  = 0) {
  SEMI_OBJ_CHECK_ARG(so);
  size_t     deg;
  en_semi_t  type = UNKNOWN;
  Converter* converter;

  gap_element_t x = semi_obj_get_rep(so);

  if (IS_TRANS(x)) {
    deg = (old_so == 0 ? 0 : semi_obj_get_semi_cpp(old_so)->degree());
    gap_plist_t gens = semi_obj_get_gens(so);
    for (size_t i = 1; i <= (size_t) LEN_PLIST(gens); i++) {
      size_t n = DEG_TRANS(ELM_PLIST(gens, i));
      if (n > deg) {
        deg = n;
      }
    }
    if (deg < 65536) {
      type      = TRANS2;
      converter = new TransConverter<u_int16_t>();
    } else {
      type      = TRANS4;
      converter = new TransConverter<u_int32_t>();
    }
  } else if (IS_PPERM(x)) {
    deg = (old_so == 0 ? 0 : semi_obj_get_semi_cpp(old_so)->degree());
    gap_plist_t gens = semi_obj_get_gens(so);
    for (size_t i = 1; i <= (size_t) LEN_PLIST(gens); i++) {
      size_t n = std::max(DEG_PPERM(ELM_PLIST(gens, i)),
                          CODEG_PPERM(ELM_PLIST(gens, i)));
      if (n > deg) {
        deg = n;
      }
    }
    if (deg < 65535) {
      type      = PPERM2;
      converter = new PPermConverter<u_int16_t>();
    } else {
      type      = PPERM4;
      converter = new PPermConverter<u_int32_t>();
    }
  } else if (TNUM_OBJ(x) == T_BIPART) {
    type      = BIPART;
    deg       = INT_INTOBJ(BIPART_DEGREE(0L, x));
    converter = new BipartConverter();
  } else if (CALL_1ARGS(IsBooleanMat, x) == True) {
    type      = BOOL_MAT;
    deg       = INT_INTOBJ(CALL_1ARGS(DimensionOfMatrixOverSemiring, x));
    converter = new BoolMatConverter();
  } else if (CALL_1ARGS(IsMaxPlusMatrix, x) == True) {
    type      = MAX_PLUS_MAT;
    deg       = INT_INTOBJ(CALL_1ARGS(DimensionOfMatrixOverSemiring, x));
    converter = new MatrixOverSemiringConverter(
        new semiring::MaxPlusSemiring(), Ninfinity, MaxPlusMatrixType);
  } else if (CALL_1ARGS(IsMinPlusMatrix, x) == True) {
    type      = MIN_PLUS_MAT;
    deg       = INT_INTOBJ(CALL_1ARGS(DimensionOfMatrixOverSemiring, x));
    converter = new MatrixOverSemiringConverter(
        new semiring::MinPlusSemiring(), infinity, MinPlusMatrixType);
  } else if (CALL_1ARGS(IsTropicalMaxPlusMatrix, x) == True) {
    type      = TROP_MAX_PLUS_MAT;
    deg       = INT_INTOBJ(CALL_1ARGS(DimensionOfMatrixOverSemiring, x));
    converter = new MatrixOverSemiringConverter(
        new semiring::TropicalMaxPlusSemiring(semi_obj_get_threshold(so)),
        Ninfinity,
        TropicalMaxPlusMatrixType);
  } else if (CALL_1ARGS(IsTropicalMinPlusMatrix, x) == True) {
    type      = TROP_MIN_PLUS_MAT;
    deg       = INT_INTOBJ(CALL_1ARGS(DimensionOfMatrixOverSemiring, x));
    converter = new MatrixOverSemiringConverter(
        new semiring::TropicalMinPlusSemiring(semi_obj_get_threshold(so)),
        infinity,
        TropicalMinPlusMatrixType);
  } else if (CALL_1ARGS(IsProjectiveMaxPlusMatrix, x) == True) {
    type = PROJ_MAX_PLUS_MAT;
    deg  = INT_INTOBJ(CALL_1ARGS(DimensionOfMatrixOverSemiring, x));
    converter =
        new ProjectiveMaxPlusMatrixConverter(new semiring::MaxPlusSemiring(),
                                             Ninfinity,
                                             ProjectiveMaxPlusMatrixType);
  } else if (CALL_1ARGS(IsNTPMatrix, x) == True) {
    type      = NTP_MAT;
    deg       = INT_INTOBJ(CALL_1ARGS(DimensionOfMatrixOverSemiring, x));
    converter = new MatrixOverSemiringConverter(
        new semiring::NaturalSemiring(semi_obj_get_threshold(so),
                                      semi_obj_get_period(so)),
        INTOBJ_INT(0),
        NTPMatrixType);
  } else if (CALL_1ARGS(IsIntegerMatrix, x) == True) {
    type      = INT_MAT;
    deg       = INT_INTOBJ(CALL_1ARGS(DimensionOfMatrixOverSemiring, x));
    converter = new MatrixOverSemiringConverter(
        new semiring::Integers(), INTOBJ_INT(0), IntegerMatrixType);
  } else if (CALL_1ARGS(IsPBR, x) == True) {
    type      = PBR_TYPE;
    deg       = INT_INTOBJ(CALL_1ARGS(DegreeOfPBR, x));
    converter = new PBRConverter();
  }

  if (type != UNKNOWN) {
    Semigroup* semi_cpp;
    if (old_so == 0) {
      assert(plist == 0);
      gap_plist_t            plist = semi_obj_get_gens(so);
      std::vector<Element*>* gens  = plist_to_vec(converter, plist, deg);
      semi_cpp                     = new Semigroup(gens);
      really_delete_cont(gens);
    } else {
      assert(plist != 0);
      Semigroup*             old_semi_cpp = semi_obj_get_semi_cpp(old_so);
      std::vector<Element*>* coll         = plist_to_vec(converter, plist, deg);
      semi_cpp = new Semigroup(*old_semi_cpp, coll, semi_obj_get_report(so));
      really_delete_cont(coll);
    }
    semi_cpp->set_batch_size(semi_obj_get_batch_size(so));

    Obj o          = NewBag(T_SEMI, 5 * sizeof(Obj));
    ADDR_OBJ(o)[0] = reinterpret_cast<Obj>(T_SEMI_SUBTYPE_ENSEMI);
    ADDR_OBJ(o)[1] = reinterpret_cast<Obj>(type);
    ADDR_OBJ(o)[2] = reinterpret_cast<Obj>(semi_cpp);
    ADDR_OBJ(o)[3] = reinterpret_cast<Obj>(converter);
    ADDR_OBJ(o)[4] = reinterpret_cast<Obj>(deg);
    CHANGED_BAG(o);
    AssPRec(so, RNam_en_semi_cpp, o);
    CHANGED_BAG(so);
    return o;
  } else {
    Obj o          = NewBag(T_SEMI, 2 * sizeof(Obj));
    ADDR_OBJ(o)[0] = reinterpret_cast<Obj>(T_SEMI_SUBTYPE_ENSEMI);
    ADDR_OBJ(o)[1] = reinterpret_cast<Obj>(type);
    CHANGED_BAG(o);
    AssPRec(so, RNam_en_semi_cpp, o);
    CHANGED_BAG(so);
    return o;
  }
}

Obj semi_obj_get_en_semi(gap_semigroup_t so) {
  SEMI_OBJ_CHECK_ARG(so);
  UInt i;
  if (FindPRec(so, RNam_en_semi_cpp, &i, 1)) {
    return GET_ELM_PREC(so, i);
  }
  return semi_obj_init_en_semi(so);
}

// FIXME should be inline
Semigroup* semi_obj_get_semi_cpp(gap_semigroup_t so) {
  SEMI_OBJ_CHECK_ARG(so);
  return en_semi_get_cpp(semi_obj_get_en_semi(so));
}

gap_prec_t semi_obj_get_fropin(gap_semigroup_t so) {
  SEMI_OBJ_CHECK_ARG(so);
  UInt i;
  if (FindPRec(so, RNam_en_semi_frp, &i, 1)) {
    return GET_ELM_PREC(so, i);
  } else {
    if (semi_obj_get_type(so) != UNKNOWN) {  // only initialise a record
      gap_prec_t fp = NEW_PREC(0);
      SET_LEN_PREC(fp, 0);
      AssPRec(so, RNam_en_semi_frp, fp);
      CHANGED_BAG(so);
      return fp;
    } else {
      CALL_1ARGS(INIT_FROPIN, so);
      if (FindPRec(so, RNam_en_semi_frp, &i, 1)) {
        return GET_ELM_PREC(so, i);
      }
      ErrorQuit("unknown error in INIT_FROPIN,", 0L, 0L);
      return 0L;
    }
  }
}

// FIXME should be inline
en_semi_t semi_obj_get_type(gap_semigroup_t so) {
  SEMI_OBJ_CHECK_ARG(so);
  return en_semi_get_type(semi_obj_get_en_semi(so));
}

static inline size_t en_semi_get_degree(Obj es) {
  EN_SEMI_CHECK_ARG(es);
  assert(en_semi_get_type(es) != UNKNOWN);
  return CLASS_OBJ<size_t>(es, 4);
}

// GAP level functions

// Add generators to the GAP semigroup Obj <so>. Note that this only works if
// the degree of every element in plist is less than or equal to the degree of
// the elements in <so>. If this is not the case, then this should not be
// called but ClosureSemigroup should be instead, on the GAP level.

gap_semigroup_t
EN_SEMI_ADD_GENERATORS(Obj self, gap_semigroup_t so, gap_plist_t plist) {
  SEMI_OBJ_CHECK_ARG(so);
  PLIST_CHECK_ARG(plist);

  en_semi_obj_t es = semi_obj_get_en_semi(so);

  if (en_semi_get_type(es) == UNKNOWN) {
    return Fail;
  }

  assert(IS_PLIST(plist));
  assert(LEN_PLIST(plist) > 0);

  Semigroup*   semi_cpp  = en_semi_get_cpp(es);
  size_t const deg       = semi_cpp->degree();
  Converter*   converter = en_semi_get_converter(es);

  std::unordered_set<Element*>* coll = new std::unordered_set<Element*>();

  for (size_t i = 1; i <= (size_t) LEN_PLIST(plist); i++) {
    coll->insert(converter->convert(ELM_PLIST(plist, i), deg));
  }

  semi_cpp->add_generators(coll, semi_obj_get_report(so));
  really_delete_cont(coll);

  gap_plist_t gens = ElmPRec(so, RNam_GeneratorsOfMagma);

  for (size_t i = 0; i < semi_cpp->nrgens(); i++) {
    AssPlist(gens, i + 1, converter->unconvert((*semi_cpp->gens())[i]));
  }

  // Reset the fropin data since none of it is valid any longer
  gap_prec_t fp = NEW_PREC(0);
  SET_LEN_PREC(fp, 0);
  AssPRec(so, RNam_en_semi_frp, fp);
  CHANGED_BAG(so);

  return so;
}

gap_plist_t EN_SEMI_AS_LIST(Obj self, gap_plist_t so) {
  SEMI_OBJ_CHECK_ARG(so);
  en_semi_obj_t es = semi_obj_get_en_semi(so);

  if (en_semi_get_type(es) != UNKNOWN) {
    std::vector<Element*>* elements =
        en_semi_get_cpp(es)->elements(semi_obj_get_report(so));
    Converter* converter = en_semi_get_converter(es);
    return vec_to_plist(converter, elements);
  } else {
    gap_prec_t fp = fropin(so, INTOBJ_INT(-1), 0, False);
    return ElmPRec(fp, RNam_elts);
  }
}

gap_plist_t EN_SEMI_AS_SET(Obj self, gap_semigroup_t so) {
  SEMI_OBJ_CHECK_ARG(so);
  en_semi_obj_t es = semi_obj_get_en_semi(so);

  if (en_semi_get_type(es) != UNKNOWN) {
    std::vector<std::pair<Element*, size_t>>* pairs =
        en_semi_get_cpp(es)->sorted_elements(semi_obj_get_report(so));
    Converter* converter = en_semi_get_converter(es);

    gap_plist_t out = NEW_PLIST(T_PLIST_HOM_SSORT + IMMUTABLE, pairs->size());
    SET_LEN_PLIST(out, pairs->size());
    size_t i = 1;
    for (auto x : *pairs) {
      SET_ELM_PLIST(out, i++, converter->unconvert(x.first));
      CHANGED_BAG(out);
    }
    return out;
  } else {
    gap_prec_t  fp  = fropin(so, INTOBJ_INT(-1), 0, False);
    gap_plist_t out = SHALLOW_COPY_OBJ(ElmPRec(fp, RNam_elts));
    SortDensePlist(out);
    CHANGED_BAG(out);
    return out;
  }
}

gap_plist_t EN_SEMI_CAYLEY_TABLE(Obj self, gap_semigroup_t so) {
  SEMI_OBJ_CHECK_ARG(so);
  en_semi_obj_t es = semi_obj_get_en_semi(so);
  if (en_semi_get_type(es) != UNKNOWN) {
    Semigroup*  semigroup = en_semi_get_cpp(es);
    bool        report    = semi_obj_get_report(so);
    size_t      n         = semigroup->size(report);
    gap_plist_t out       = NEW_PLIST(T_PLIST_HOM, n);
    SET_LEN_PLIST(out, n);

    for (size_t i = 0; i < n; i++) {
      gap_plist_t next = NEW_PLIST(T_PLIST_CYC, n);
      SET_LEN_PLIST(next, n);
      for (size_t j = 0; j < n; j++) {
        SET_ELM_PLIST(
            next, j + 1, INTOBJ_INT(semigroup->fast_product(i, j) + 1));
      }
      SET_ELM_PLIST(out, i + 1, next);
      CHANGED_BAG(out);
    }
    return out;
  }  // TODO non-cpp method, requires fast_product for non-cpp
}

// This takes a newly constructed semigroup <new_so> which is generated by
// <old_so> and <coll>, and it transfers any information known about the
// <old_so>s cpp semigroup to <new_so>.

gap_semigroup_t EN_SEMI_CLOSURE(Obj             self,
                                gap_semigroup_t new_so,
                                gap_semigroup_t old_so,
                                gap_plist_t     plist) {
  SEMI_OBJ_CHECK_ARG(new_so);
  SEMI_OBJ_CHECK_ARG(old_so);
  PLIST_CHECK_ARG(plist);

  en_semi_obj_t es = semi_obj_get_en_semi(old_so);

  if (en_semi_get_type(es) == UNKNOWN) {
    return new_so;
  }
  semi_obj_init_en_semi(new_so, old_so, plist);
  return new_so;
}

gap_int_t EN_SEMI_CURRENT_MAX_WORD_LENGTH(Obj self, gap_semigroup_t so) {
  SEMI_OBJ_CHECK_ARG(so);
  en_semi_obj_t es = semi_obj_get_en_semi(so);
  if (en_semi_get_type(es) != UNKNOWN) {
    return INTOBJ_INT(en_semi_get_cpp(es)->current_max_word_length());
  } else {
    initRNams();
    gap_prec_t fp = semi_obj_get_en_semi(so);
    if (IsbPRec(fp, RNam_words) && LEN_PLIST(ElmPRec(fp, RNam_words)) > 0) {
      gap_plist_t words = ElmPRec(fp, RNam_words);
      return INTOBJ_INT(LEN_PLIST(ELM_PLIST(words, LEN_PLIST(words))));
    } else {
      return INTOBJ_INT(0);
    }
  }
}

gap_int_t EN_SEMI_CURRENT_NR_RULES(Obj self, gap_semigroup_t so) {
  SEMI_OBJ_CHECK_ARG(so);
  en_semi_obj_t es = semi_obj_get_en_semi(so);
  if (en_semi_get_type(es) != UNKNOWN) {
    return INTOBJ_INT(en_semi_get_cpp(es)->current_nrrules());
  } else {
    initRNams();
    gap_prec_t fp = semi_obj_get_en_semi(so);
    if (IsbPRec(fp, RNam_nrrules)) {
      return ElmPRec(fp, RNam_nrrules);
    } else {
      return INTOBJ_INT(0);
    }
  }
}

gap_int_t EN_SEMI_CURRENT_SIZE(Obj self, gap_semigroup_t so) {
  SEMI_OBJ_CHECK_ARG(so);
  en_semi_obj_t es = semi_obj_get_en_semi(so);
  if (en_semi_get_type(es) != UNKNOWN) {
    return INTOBJ_INT(en_semi_get_cpp(es)->current_max_word_length());
  } else {
    initRNams();
    gap_prec_t fp = semi_obj_get_en_semi(so);
    if (IsbPRec(fp, RNam_elts)) {
      return INTOBJ_INT(LEN_PLIST(ElmPRec(fp, RNam_elts)));
    } else {
      return INTOBJ_INT(0);
    }
  }
}

// Get the <pos> element of <S> this is not cached anywhere for cpp semigroups

gap_element_t
EN_SEMI_ELEMENT_NUMBER(Obj self, gap_semigroup_t so, gap_int_t pos) {
  SEMI_OBJ_CHECK_ARG(so);
  INTOBJ_CHECK_ARG(pos);

  Obj    es = semi_obj_get_en_semi(so);
  size_t nr = INT_INTOBJ(pos);

  if (en_semi_get_type(es) != UNKNOWN) {
    nr--;
    Semigroup* semi_cpp = en_semi_get_cpp(es);
    Element*   x        = semi_cpp->at(nr, semi_obj_get_report(so));
    return (x == nullptr ? Fail : en_semi_get_converter(es)->unconvert(x));
  } else {
    initRNams();
    Obj fp = semi_obj_get_fropin(so);
    if (IsbPRec(fp, RNam_elts)) {
      // use the element cached in the data record if known
      gap_plist_t elts = ElmPRec(fp, RNam_elts);
      if (nr <= (size_t) LEN_PLIST(elts) && ELM_PLIST(elts, nr) != 0) {
        return ELM_PLIST(elts, nr);
      }
    }
    fp               = fropin(so, pos, 0, False);
    gap_plist_t elts = ElmPRec(fp, RNam_elts);
    if (nr <= (size_t) LEN_PLIST(elts) && ELM_PLIST(elts, nr) != 0) {
      return ELM_PLIST(elts, nr);
    } else {
      return Fail;
    }
  }
}

gap_element_t
EN_SEMI_ELEMENT_NUMBER_SORTED(Obj self, gap_semigroup_t so, gap_int_t pos) {
  SEMI_OBJ_CHECK_ARG(so);
  INTOBJ_CHECK_ARG(pos);

  en_semi_obj_t es = semi_obj_get_en_semi(so);

  if (en_semi_get_type(es) != UNKNOWN) {
    size_t     nr       = INT_INTOBJ(pos) - 1;
    Semigroup* semi_cpp = en_semi_get_cpp(es);
    Element*   x        = semi_cpp->sorted_at(nr, semi_obj_get_report(so));
    return (x == nullptr ? Fail : en_semi_get_converter(es)->unconvert(x));
  } else {
    ErrorQuit("EN_SEMI_ELEMENT_NUMBER_SORTED: this shouldn't happen!", 0L, 0L);
    return 0L;
  }
}

gap_semigroup_t
EN_SEMI_ENUMERATE(Obj self, gap_semigroup_t so, gap_int_t limit) {
  SEMI_OBJ_CHECK_ARG(so);
  INTOBJ_CHECK_ARG(limit);  // FIXME limit can be -1, remove this

  en_semi_obj_t es = semi_obj_get_en_semi(so);
  if (en_semi_get_type(es) != UNKNOWN) {
    en_semi_get_cpp(es)->enumerate(INT_INTOBJ(limit), semi_obj_get_report(so));
  } else {
    fropin(so, limit, 0, False);
  }
  return so;
}

gap_plist_t EN_SEMI_FACTORIZATION(Obj self, gap_semigroup_t so, gap_int_t pos) {
  SEMI_OBJ_CHECK_ARG(so);
  INTOBJ_CHECK_ARG(pos);

  Obj    es    = semi_obj_get_en_semi(so);
  size_t pos_c = INT_INTOBJ(pos);

  if (en_semi_get_type(es) != UNKNOWN) {
    gap_plist_t words;
    Semigroup*  semi_cpp = en_semi_get_cpp(es);

    if (pos_c > semi_cpp->current_size()) {
      ErrorQuit("the 2nd argument must be at most %d not %d",
                semi_cpp->current_size(),
                pos_c);
    }

    gap_prec_t fp = semi_obj_get_fropin(so);
    if (!IsbPRec(fp, RNam_words)) {
      // TODO Use FindPRec instead
      word_t w;  // changed in place by the next line
      semi_cpp->factorisation(w, pos_c - 1, semi_obj_get_report(so));
      words = NEW_PLIST(T_PLIST, pos_c);
      SET_LEN_PLIST(words, pos_c);
      SET_ELM_PLIST(words, pos_c, word_t_to_plist(w));
      CHANGED_BAG(words);
      AssPRec(fp, RNam_words, words);
    } else {
      words = ElmPRec(fp, RNam_words);
      if (pos_c > (size_t) LEN_PLIST(words) || ELM_PLIST(words, pos_c) == 0) {
        // avoid retracing the Schreier tree if possible
        size_t prefix = semi_cpp->prefix(pos_c - 1) + 1;
        size_t suffix = semi_cpp->suffix(pos_c - 1) + 1;
        if (prefix != 0 && prefix <= (size_t) LEN_PLIST(words)
            && ELM_PLIST(words, prefix) != 0) {
          Obj old_word = ELM_PLIST(words, prefix);
          Obj new_word = NEW_PLIST(T_PLIST_CYC, LEN_PLIST(old_word) + 1);
          memcpy((void*) ((char*) (ADDR_OBJ(new_word)) + sizeof(Obj)),
                 (void*) ((char*) (ADDR_OBJ(old_word)) + sizeof(Obj)),
                 (size_t)(LEN_PLIST(old_word) * sizeof(Obj)));
          SET_ELM_PLIST(new_word,
                        LEN_PLIST(old_word) + 1,
                        INTOBJ_INT(semi_cpp->final_letter(pos_c - 1) + 1));
          SET_LEN_PLIST(new_word, LEN_PLIST(old_word) + 1);
          AssPlist(words, pos_c, new_word);
        } else if (suffix != 0 && suffix <= (size_t) LEN_PLIST(words)
                   && ELM_PLIST(words, suffix) != 0) {
          Obj old_word = ELM_PLIST(words, suffix);
          Obj new_word = NEW_PLIST(T_PLIST_CYC, LEN_PLIST(old_word) + 1);
          memcpy((void*) ((char*) (ADDR_OBJ(new_word)) + 2 * sizeof(Obj)),
                 (void*) ((char*) (ADDR_OBJ(old_word)) + sizeof(Obj)),
                 (size_t)(LEN_PLIST(old_word) * sizeof(Obj)));
          SET_ELM_PLIST(
              new_word, 1, INTOBJ_INT(semi_cpp->first_letter(pos_c - 1) + 1));
          SET_LEN_PLIST(new_word, LEN_PLIST(old_word) + 1);
          AssPlist(words, pos_c, new_word);
        } else {
          word_t w;  // changed in place by the next line
          semi_cpp->factorisation(w, pos_c - 1, semi_obj_get_report(so));
          AssPlist(words, pos_c, word_t_to_plist(w));
        }
      }
    }
    CHANGED_BAG(fp);
    assert(IsbPRec(fp, RNam_words));
    assert(IS_PLIST(ElmPRec(fp, RNam_words)));
    assert(pos_c <= (size_t) LEN_PLIST(ElmPRec(fp, RNam_words)));
    return ELM_PLIST(ElmPRec(fp, RNam_words), pos_c);
  } else {
    gap_prec_t fp = fropin(so, INTOBJ_INT(pos), 0, False);
    return ELM_PLIST(ElmPRec(fp, RNam_words), pos_c);
  }
}

gap_plist_t EN_SEMI_LEFT_CAYLEY_GRAPH(Obj self, gap_semigroup_t so) {
  SEMI_OBJ_CHECK_ARG(so);
  en_semi_obj_t es = semi_obj_get_en_semi(so);
  if (en_semi_get_type(es) != UNKNOWN) {
    Semigroup* semi_cpp = en_semi_get_cpp(es);
    bool       report   = semi_obj_get_report(so);
    return cayley_graph_t_to_plist(semi_cpp->left_cayley_graph(report));
  } else {
    return ElmPRec(fropin(so, INTOBJ_INT(-1), 0, False), RNam_left);
  }
}

gap_int_t EN_SEMI_LENGTH_ELEMENT(Obj self, gap_semigroup_t so, gap_int_t pos) {
  SEMI_OBJ_CHECK_ARG(so);
  INTOBJ_CHECK_ARG(pos);
  en_semi_obj_t es = semi_obj_get_en_semi(so);
  if (en_semi_get_type(es) != UNKNOWN) {
    return INTOBJ_INT(en_semi_get_cpp(es)->length_non_const(
        INT_INTOBJ(pos) - 1, semi_obj_get_report(so)));
  } else {
    return INTOBJ_INT(LEN_PLIST(EN_SEMI_FACTORIZATION(self, so, pos)));
  }
}

gap_bool_t EN_SEMI_IS_DONE(Obj self, gap_semigroup_t so) {
  SEMI_OBJ_CHECK_ARG(so);
  en_semi_obj_t es = semi_obj_get_en_semi(so);

  if (en_semi_get_type(es) != UNKNOWN) {
    return (en_semi_get_cpp(es)->is_done() ? True : False);
  }

  gap_prec_t fp = semi_obj_get_fropin(so);

  size_t pos = INT_INTOBJ(ElmPRec(fp, RNam_pos));
  size_t nr  = INT_INTOBJ(ElmPRec(fp, RNam_nr));
  return (pos > nr ? True : False);
}

gap_int_t EN_SEMI_NR_IDEMPOTENTS(Obj self, gap_semigroup_t so) {
  SEMI_OBJ_CHECK_ARG(so);
  en_semi_obj_t es = semi_obj_get_en_semi(so);
  if (en_semi_get_type(es) != UNKNOWN) {
    return INTOBJ_INT(en_semi_get_cpp(es)->nr_idempotents(
        semi_obj_get_report(so), semi_obj_get_nr_threads(so)));
  } else {
    gap_prec_t  fp     = fropin(so, INTOBJ_INT(-1), 0, False);
    gap_plist_t left   = ElmPRec(fp, RNamName("left"));
    gap_plist_t last   = ElmPRec(fp, RNamName("final"));
    gap_plist_t prefix = ElmPRec(fp, RNamName("prefix"));
    size_t      size   = LEN_PLIST(left);
    size_t      nr     = 0;
    for (size_t pos = 1; pos <= size; pos++) {
      size_t i = pos, j = pos;
      while (i != 0) {
        j = INT_INTOBJ(
            ELM_PLIST(ELM_PLIST(left, j), INT_INTOBJ(ELM_PLIST(last, i))));
        i = INT_INTOBJ(ELM_PLIST(prefix, i));
      }
      if (j == pos) {
        nr++;
      }
    }
    return INTOBJ_INT(nr);
  }
}

Obj EN_SEMI_POSITION(Obj self, gap_semigroup_t so, gap_element_t x) {
  SEMI_OBJ_CHECK_ARG(so);
  en_semi_obj_t es = semi_obj_get_en_semi(so);

  if (en_semi_get_type(es) != UNKNOWN) {
    size_t   deg = en_semi_get_degree(es);
    Element* xx  = en_semi_get_converter(es)->convert(x, deg);
    size_t   pos = en_semi_get_cpp(es)->position(xx, semi_obj_get_report(so));
    delete xx;
    return (pos == Semigroup::UNDEFINED ? Fail : INTOBJ_INT(pos + 1));
  } else {
    Obj    data = semi_obj_get_fropin(so);
    Obj    ht   = ElmPRec(data, RNam_ht);
    size_t pos, nr;

    do {
      Obj val = CALL_2ARGS(HTValue, ht, x);
      if (val != Fail) {
        return val;
      }
      Obj limit = SumInt(ElmPRec(data, RNam_nr), INTOBJ_INT(1));
      fropin(data, limit, 0, False);
      pos = INT_INTOBJ(ElmPRec(data, RNam_pos));
      nr  = INT_INTOBJ(ElmPRec(data, RNam_nr));
    } while (pos <= nr);
    return CALL_2ARGS(HTValue, ht, x);
  }
}

// Get the position of <x> with out any further enumeration

Obj EN_SEMI_POSITION_CURRENT(Obj self, gap_semigroup_t so, gap_element_t x) {
  SEMI_OBJ_CHECK_ARG(so);

  en_semi_obj_t es = semi_obj_get_en_semi(so);

  if (en_semi_get_type(es) != UNKNOWN) {
    size_t   deg = en_semi_get_degree(es);
    Element* xx  = en_semi_get_converter(es)->convert(x, deg);
    size_t   pos = en_semi_get_cpp(es)->position_current(xx);
    delete xx;
    return (pos == Semigroup::UNDEFINED ? Fail : INTOBJ_INT(pos + 1));
  } else {
    return CALL_2ARGS(HTValue, ElmPRec(semi_obj_get_fropin(so), RNam_ht), x);
  }
}

gap_int_t
EN_SEMI_POSITION_SORTED(Obj self, gap_semigroup_t so, gap_element_t x) {
  SEMI_OBJ_CHECK_ARG(so);

  en_semi_obj_t es = semi_obj_get_en_semi(so);

  if (en_semi_get_type(es) == UNKNOWN) {
    ErrorQuit("EN_SEMI_POSITION_SORTED: this shouldn't happen!", 0L, 0L);
    return 0L;
  } else {
    size_t     deg      = en_semi_get_degree(es);
    Semigroup* semi_cpp = en_semi_get_cpp(es);
    Element*   xx       = en_semi_get_converter(es)->convert(x, deg);
    size_t     pos = semi_cpp->position_sorted(xx, semi_obj_get_report(so));
    delete xx;
    return (pos == Semigroup::UNDEFINED ? Fail : INTOBJ_INT(pos + 1));
  }
}

gap_plist_t EN_SEMI_RELATIONS(Obj self, gap_semigroup_t so) {
  SEMI_OBJ_CHECK_ARG(so);
  initRNams();
  gap_plist_t es = semi_obj_get_en_semi(so);
  gap_prec_t  fp = semi_obj_get_fropin(so);

  if (en_semi_get_type(es) != UNKNOWN) {
    if (!IsbPRec(fp, RNam_rules) || LEN_PLIST(ElmPRec(fp, RNam_rules)) == 0) {
      Semigroup*  semigroup = en_semi_get_cpp(es);
      bool        report    = semi_obj_get_report(so);
      gap_plist_t rules     = NEW_PLIST(T_PLIST, semigroup->nrrules(report));
      SET_LEN_PLIST(rules, semigroup->nrrules(report));
      size_t nr = 0;

      semigroup->reset_next_relation();
      std::vector<size_t> relation;
      semigroup->next_relation(relation, report);

      while (relation.size() == 2) {
        gap_plist_t next = NEW_PLIST(T_PLIST, 2);
        SET_LEN_PLIST(next, 2);
        for (size_t i = 0; i < 2; i++) {
          gap_plist_t w = NEW_PLIST(T_PLIST_CYC, 1);
          SET_LEN_PLIST(w, 1);
          SET_ELM_PLIST(w, 1, INTOBJ_INT(relation[i] + 1));
          SET_ELM_PLIST(next, i + 1, w);
          CHANGED_BAG(next);
        }
        nr++;
        SET_ELM_PLIST(rules, nr, next);
        CHANGED_BAG(rules);
        semigroup->next_relation(relation, report);
      }

      while (!relation.empty()) {
        gap_plist_t old_word =
            EN_SEMI_FACTORIZATION(self, so, INTOBJ_INT(relation[0] + 1));
        gap_plist_t new_word = NEW_PLIST(T_PLIST_CYC, LEN_PLIST(old_word) + 1);
        memcpy((void*) ((char*) (ADDR_OBJ(new_word)) + sizeof(Obj)),
               (void*) ((char*) (ADDR_OBJ(old_word)) + sizeof(Obj)),
               (size_t)(LEN_PLIST(old_word) * sizeof(Obj)));
        SET_ELM_PLIST(
            new_word, LEN_PLIST(old_word) + 1, INTOBJ_INT(relation[1] + 1));
        SET_LEN_PLIST(new_word, LEN_PLIST(old_word) + 1);

        gap_plist_t next = NEW_PLIST(T_PLIST, 2);
        SET_LEN_PLIST(next, 2);
        SET_ELM_PLIST(next, 1, new_word);
        CHANGED_BAG(next);
        SET_ELM_PLIST(
            next,
            2,
            EN_SEMI_FACTORIZATION(self, so, INTOBJ_INT(relation[2] + 1)));
        CHANGED_BAG(next);
        nr++;
        SET_ELM_PLIST(rules, nr, next);
        CHANGED_BAG(rules);
        semigroup->next_relation(relation, report);
      }
      AssPRec(fp, RNam_rules, rules);
      CHANGED_BAG(fp);
      CHANGED_BAG(so);
    }
  } else {
    fropin(so, INTOBJ_INT(-1), 0, False);
  }
  return ElmPRec(fp, RNam_rules);
}

gap_plist_t EN_SEMI_RIGHT_CAYLEY_GRAPH(Obj self, gap_semigroup_t so) {
  SEMI_OBJ_CHECK_ARG(so);
  en_semi_obj_t es = semi_obj_get_en_semi(so);

  if (en_semi_get_type(es) != UNKNOWN) {
    Semigroup* semi_cpp = en_semi_get_cpp(es);
    bool       report   = semi_obj_get_report(so);
    return cayley_graph_t_to_plist(semi_cpp->right_cayley_graph(report));
  } else {
    return ElmPRec(fropin(so, INTOBJ_INT(-1), 0, False), RNam_right);
  }
}

gap_int_t EN_SEMI_SIZE(Obj self, gap_semigroup_t so) {
  SEMI_OBJ_CHECK_ARG(so);
  initRNams();
  en_semi_obj_t es = semi_obj_get_en_semi(so);

  if (en_semi_get_type(es) != UNKNOWN) {
    bool report = semi_obj_get_report(so);
    return INTOBJ_INT(en_semi_get_cpp(es)->size(report));
  } else {
    Obj fp = fropin(so, INTOBJ_INT(-1), 0, False);
    return INTOBJ_INT(LEN_PLIST(ElmPRec(fp, RNam_elts)));
  }
}

// Iterators
// TODO rename these

gap_bool_t EN_SEMI_IS_DONE_ITERATOR(Obj self, gap_prec_t iter) {
  initRNams();
  Int size = INT_INTOBJ(EN_SEMI_SIZE(self, ElmPRec(iter, RNam_parent)));
  return (INT_INTOBJ(ElmPRec(iter, RNam_pos)) == size ? True : False);
}

gap_element_t EN_SEMI_NEXT_ITERATOR(Obj self, gap_prec_t iter) {
  initRNams();
  gap_int_t pos = INTOBJ_INT(INT_INTOBJ(ElmPRec(iter, RNam_pos)) + 1);
  AssPRec(iter, RNam_pos, pos);
  return EN_SEMI_ELEMENT_NUMBER(self, ElmPRec(iter, RNam_parent), pos);
}

gap_element_t EN_SEMI_NEXT_ITERATOR_SORTED(Obj self, gap_prec_t iter) {
  initRNams();
  gap_int_t pos = INTOBJ_INT(INT_INTOBJ(ElmPRec(iter, RNam_pos)) + 1);
  AssPRec(iter, RNam_pos, pos);
  return EN_SEMI_ELEMENT_NUMBER_SORTED(self, ElmPRec(iter, RNam_parent), pos);
}
