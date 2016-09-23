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

#include <assert.h>

#include <string>
#include <utility>

#include "src/compiled.h"

#include "converter.h"
#include "data.h"
#include "fropin.h"
#include "gap.h"
#include "interface.h"
#include "semigrp.h"

#include "semigroupsplusplus/semigroups.h"

// Helper functions

template <typename T>
static inline void really_delete_cont(T* cont) {
  for (Element* x : *cont) {
    x->really_delete();
  }
  delete cont;
}

/*******************************************************************************
 * ConvertElements:
 ******************************************************************************/

std::vector<Element*>*
ConvertElements(Converter* converter, Obj elements, size_t degree) {
  assert(IS_LIST(elements));

  auto out = new std::vector<Element*>();

  for (size_t i = 0; i < (size_t) LEN_LIST(elements); i++) {
    out->push_back(converter->convert(ELM_LIST(elements, i + 1), degree));
  }
  return out;
}

Obj UnconvertElements(Converter* converter, std::vector<Element*>* elements) {

  if (elements->empty()) {
    Obj out = NEW_PLIST(T_PLIST_EMPTY, 0);
    SET_LEN_PLIST(out, 0);
    return out;
  }

  Obj out = NEW_PLIST(T_PLIST, elements->size());
  SET_LEN_PLIST(out, elements->size());

  for (size_t i = 0; i < elements->size(); i++) {
    SET_ELM_PLIST(out, i + 1, converter->unconvert(elements->at(i)));
    CHANGED_BAG(out);
  }
  return out;
}

/*******************************************************************************
 * ConvertFromCayleyGraph: helper function to convert a cayley_graph_t to a GAP
 * plist of GAP plists
 ******************************************************************************/

Obj ConvertFromCayleyGraph(cayley_graph_t* graph) {
  assert(graph->size() != 0);
  Obj out = NEW_PLIST(T_PLIST, graph->nr_rows());
  SET_LEN_PLIST(out, graph->nr_rows());

  for (size_t i = 0; i < graph->nr_rows(); i++) {
    Obj next = NEW_PLIST(T_PLIST_CYC, graph->nr_cols());
    SET_LEN_PLIST(next, graph->nr_cols());
    for (size_t j = 0; j < graph->nr_cols(); j++) { // TODO reinstate this
      SET_ELM_PLIST(next, j + 1, INTOBJ_INT(graph->get(i, j) + 1));
    }
    SET_ELM_PLIST(out, i + 1, next);
    CHANGED_BAG(out);
  }
  return out;
}

// GAP level functions

/*******************************************************************************
 * SEMIGROUP_ADD_GENERATORS:
 ******************************************************************************/

Obj SEMIGROUP_ADD_GENERATORS(Obj self, Obj data, Obj coll_gap) {
  if (data_type(data) == UNKNOWN) {
    ErrorQuit("SEMIGROUP_ADD_GENERATORS: this shouldn't happen!", 0L, 0L);
  }

  assert(IS_PLIST(coll_gap));
  assert(LEN_PLIST(coll_gap) > 0);

  Semigroup*                    semigroup = data_semigroup(data);
  Converter*                    converter = data_converter(data);
  std::unordered_set<Element*>* coll = new std::unordered_set<Element*>();

  for (size_t i = 1; i <= (size_t) LEN_PLIST(coll_gap); i++) {
    coll->insert(
        converter->convert(ELM_PLIST(coll_gap, i), semigroup->degree()));
  }
  semigroup->add_generators(coll, rec_get_report(data));
  really_delete_cont(coll);

  Obj gens = ElmPRec(data, RNam_gens); // TODO make this safe

  for (size_t i = 0; i < semigroup->nrgens(); i++) {
    AssPlist(gens, i + 1, converter->unconvert(semigroup->gens()->at(i)));
  }

  if (IsbPRec(data, RNam_left)) {
    UnbPRec(data, RNam_left);
  }
  if (IsbPRec(data, RNam_right)) {
    UnbPRec(data, RNam_right);
  }
  if (IsbPRec(data, RNam_rules)) {
    UnbPRec(data, RNam_rules);
  }
  if (IsbPRec(data, RNam_words)) {
    UnbPRec(data, RNam_words);
  }

  return data;
}

/*******************************************************************************
 * SEMIGROUP_CAYLEY_TABLE: TODO for non-C++
 ******************************************************************************/

Obj SEMIGROUP_CAYLEY_TABLE(Obj self, Obj data) {
  if (data_type(data) != UNKNOWN) {
    Semigroup* semigroup = data_semigroup(data);
    bool       report    = rec_get_report(data);
    Obj        out       = NEW_PLIST(T_PLIST_HOM, semigroup->size(report));
    SET_LEN_PLIST(out, semigroup->size(report));

    for (size_t i = 0; i < semigroup->size(report); i++) {
      Obj next = NEW_PLIST(T_PLIST_CYC, semigroup->size(report));
      SET_LEN_PLIST(next, semigroup->size(report));
      for (size_t j = 0; j < semigroup->size(report); j++) {
        SET_ELM_PLIST(
            next, j + 1, INTOBJ_INT(semigroup->fast_product(i, j) + 1));
      }
      SET_ELM_PLIST(out, i + 1, next);
      CHANGED_BAG(out);
    }
    return out;
  }
}

/*******************************************************************************
 * SEMIGROUP_CLOSURE:
 ******************************************************************************/

Obj SEMIGROUP_CLOSURE(Obj self, Obj old_data, Obj coll_gap, Obj degree) {

  assert(IS_LIST(coll_gap) && LEN_LIST(coll_gap) > 0);
  assert(data_type(old_data) != UNKNOWN);

  Semigroup* old_semigroup = data_semigroup(old_data);
  Converter* converter     = data_converter(old_data);

  std::vector<Element*>* coll(
      ConvertElements(converter, coll_gap, INT_INTOBJ(degree)));

  Semigroup* new_semigroup(
      new Semigroup(*old_semigroup, coll, rec_get_report(old_data)));
  new_semigroup->set_batch_size(data_batch_size(old_data));

  really_delete_cont(coll);

  Obj new_data = NEW_PREC(6);

  AssPRec(
      new_data, RNam_gens, UnconvertElements(converter, new_semigroup->gens()));
  AssPRec(new_data, RNam_degree, INTOBJ_INT(new_semigroup->degree()));
  AssPRec(new_data, RNam_report, ElmPRec(old_data, RNam_report));
  AssPRec(new_data, RNam_batch_size, ElmPRec(old_data, RNam_batch_size));

  data_init_semigroup(new_data, new_semigroup);

  return new_data;
}

/*******************************************************************************
 * SEMIGROUP_CURRENT_MAX_WORD_LENGTH:
 ******************************************************************************/

Obj SEMIGROUP_CURRENT_MAX_WORD_LENGTH(Obj self, Obj data) {
  if (data_type(data) != UNKNOWN) {
    return INTOBJ_INT(data_semigroup(data)->current_max_word_length());
  } else {
    initRNams();
    if (IsbPRec(data, RNam_words) && LEN_PLIST(ElmPRec(data, RNam_words)) > 0) {
      Obj words = ElmPRec(data, RNam_words);
      return INTOBJ_INT(LEN_PLIST(ELM_PLIST(words, LEN_PLIST(words))));
    } else {
      return INTOBJ_INT(1);
    }
  }
}

/*******************************************************************************
 * SEMIGROUP_CURRENT_NR_RULES:
 ******************************************************************************/

Obj SEMIGROUP_CURRENT_NR_RULES(Obj self, Obj data) {
  if (data_type(data) != UNKNOWN) {
    return INTOBJ_INT(data_semigroup(data)->current_nrrules());
  }
  return INTOBJ_INT(ElmPRec(data, RNamName("nrrules")));
}

/*******************************************************************************
 * SEMIGROUP_CURRENT_SIZE:
 ******************************************************************************/

Obj SEMIGROUP_CURRENT_SIZE(Obj self, Obj data) {
  if (data_type(data) != UNKNOWN) {
    return INTOBJ_INT(data_semigroup(data)->current_size());
  }

  initRNams();
  return INTOBJ_INT(LEN_PLIST(ElmPRec(data, RNam_elts)));
}

/*******************************************************************************
 * SEMIGROUP_AS_LIST: get the elements of the C++ semigroup, store them in
 * data.
 ******************************************************************************/

Obj SEMIGROUP_AS_LIST(Obj self, Obj data) {
  initRNams();

  if (data_type(data) != UNKNOWN) {
    std::vector<Element*>* elements =
        data_semigroup(data)->elements(rec_get_report(data));
    Converter* converter = data_converter(data);

    if (!IsbPRec(data, RNam_elts)) {
      Obj out = NEW_PLIST(T_PLIST, elements->size());
      SET_LEN_PLIST(out, elements->size());
      for (size_t i = 0; i < elements->size(); i++) {
        SET_ELM_PLIST(out, i + 1, converter->unconvert(elements->at(i)));
        CHANGED_BAG(out);
      }
      AssPRec(data, RNam_elts, out);
    } else {
      Obj out = ElmPRec(data, RNam_elts);
      for (size_t i = LEN_PLIST(out); i < elements->size(); i++) {
        AssPlist(out, i + 1, converter->unconvert(elements->at(i)));
      }
    }
    CHANGED_BAG(data);
  } else {
    fropin(data, INTOBJ_INT(-1), 0, False);
  }
  return ElmPRec(data, RNam_elts);
}

/*******************************************************************************
 * SEMIGROUP_ELEMENT_NUMBER: get the <pos> element of <S>, do not store them in
 * the data record.
 ******************************************************************************/

Obj SEMIGROUP_ELEMENT_NUMBER(Obj self, Obj data, Obj pos) {

  size_t nr = INT_INTOBJ(pos);

  initRNams();

  // use the element cached in the data record if known
  if (IsbPRec(data, RNam_elts)) {
    Obj elts = ElmPRec(data, RNam_elts);
    if (nr <= (size_t) LEN_PLIST(elts) && ELM_PLIST(elts, nr) != 0) {
      return ELM_PLIST(elts, nr);
    }
  }

  if (data_type(data) == UNKNOWN) {
    fropin(data, pos, 0, False);
    Obj elts = ElmPRec(data, RNam_elts);
    if (nr <= (size_t) LEN_PLIST(elts) && ELM_PLIST(elts, nr) != 0) {
      return ELM_PLIST(elts, nr);
    } else {
      return Fail;
    }
  } else {
    nr--;
    Semigroup* semigroup = data_semigroup(data);
    Element*   x         = semigroup->at(nr, rec_get_report(data));
    return (x == nullptr ? Fail : data_converter(data)->unconvert(x));
  }
}

Obj SEMIGROUP_ELEMENT_NUMBER_SORTED(Obj self, Obj data, Obj pos) {

  if (data_type(data) == UNKNOWN) {
    ErrorQuit(
        "SEMIGROUP_ELEMENT_NUMBER_SORTED: this shouldn't happen!", 0L, 0L);
    return 0L;
  } else {
    size_t     nr        = INT_INTOBJ(pos) - 1;
    Semigroup* semigroup = data_semigroup(data);
    Element*   x         = semigroup->sorted_at(nr, rec_get_report(data));
    return (x == nullptr ? Fail : data_converter(data)->unconvert(x));
  }
}

Obj SEMIGROUP_AS_SET(Obj self, Obj data) {
  // TODO make this faster by running through _pos_sorted so that we run through
  // semigroup->_elements in order, and fill in out (below) out of order
  if (data_type(data) == UNKNOWN) {
    ErrorQuit("SEMIGROUP_AS_SET: this shouldn't happen!", 0L, 0L);
    return 0L;
  }

  std::vector<std::pair<Element*, size_t>>* pairs =
      data_semigroup(data)->sorted_elements(rec_get_report(data));
  Converter* converter = data_converter(data);

  Obj out = NEW_PLIST(T_PLIST, pairs->size());
  SET_LEN_PLIST(out, pairs->size());

  size_t i = 1;
  for (auto x : *pairs) {
    SET_ELM_PLIST(out, i++, converter->unconvert(x.first));
    CHANGED_BAG(out);
  }
  return out;
}

Obj SEMIGROUP_POSITION_SORTED(Obj self, Obj data, Obj x) {

  // use the element cached in the data record if known
  if (data_type(data) == UNKNOWN) {
    ErrorQuit("SEMIGROUP_POSITION_SORTED: this shouldn't happen!", 0L, 0L);
    return 0L;
  } else {
    size_t     deg       = data_degree(data);
    Semigroup* semigroup = data_semigroup(data);
    Converter* converter = data_converter(data);
    Element* xx(converter->convert(x, deg));
    size_t     pos = semigroup->position_sorted(xx, rec_get_report(data));
    delete xx;
    return (pos == Semigroup::UNDEFINED ? Fail : INTOBJ_INT(pos + 1));
  }
}

/*******************************************************************************
 * SEMIGROUP_ENUMERATE:
 ******************************************************************************/

Obj SEMIGROUP_ENUMERATE(Obj self, Obj data, Obj limit) {
  if (data_type(data) != UNKNOWN) {
    data_semigroup(data)->enumerate(INT_INTOBJ(limit), rec_get_report(data));
  } else {
    fropin(data, limit, 0, False);
  }
  return data;
}

/*******************************************************************************
 * SEMIGROUP_IS_DONE:
 ******************************************************************************/

Obj SEMIGROUP_IS_DONE(Obj self, Obj data) {
  if (data_type(data) != UNKNOWN) {
    return (data_semigroup(data)->is_done() ? True : False);
  }

  size_t pos = INT_INTOBJ(ElmPRec(data, RNamName("pos")));
  size_t nr  = INT_INTOBJ(ElmPRec(data, RNamName("nr")));
  return (pos > nr ? True : False);
}

Obj SEMIGROUP_NEXT_ITERATOR(Obj self, Obj iter) {
  initRNams();
  Obj pos = INTOBJ_INT(INT_INTOBJ(ElmPRec(iter, RNam_pos)) + 1);
  AssPRec(iter, RNam_pos, pos);
  return SEMIGROUP_ELEMENT_NUMBER(self, ElmPRec(iter, RNam_data), pos);
}

Obj SEMIGROUP_NEXT_ITERATOR_SORTED(Obj self, Obj iter) {
  initRNams();
  Obj pos = INTOBJ_INT(INT_INTOBJ(ElmPRec(iter, RNam_pos)) + 1);
  AssPRec(iter, RNam_pos, pos);
  return SEMIGROUP_ELEMENT_NUMBER_SORTED(self, ElmPRec(iter, RNam_data), pos);
}

Obj SEMIGROUP_IS_DONE_ITERATOR_CC(Obj self, Obj iter) {
  initRNams();
  Obj data = ElmPRec(iter, RNam_data);
  Int size = data_semigroup(data)->size(rec_get_report(data));
  return (INT_INTOBJ(ElmPRec(iter, RNam_pos)) == size ? True : False);
}
