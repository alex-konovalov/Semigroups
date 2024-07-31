//
// Semigroups package for GAP
// Copyright (C) 2022 James D. Mitchell
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

// Semigroups GAP package headers
#include "to_cpp.hpp"  // for to_cpp
#include "to_gap.hpp"  // for to_gap

// libsemigroups headers
#include "libsemigroups/froidure-pin-base.hpp"  // for FroidurePin

// Forward decl
namespace gapbind14 {
  class Module;
}

void init_froidure_pin_base(gapbind14::Module& m) {
  //   using FroidurePin_ = std::shared_ptr<libsemigroups::FroidurePinBase>;
  //   gapbind14::class_<FroidurePin_>("FroidurePinBase")
  //       .def("enumerate",
  //            [](FroidurePin_ S, size_t limit) { S->enumerate(limit); })
  //       .def("left_cayley_graph",
  //            [](FroidurePin_ S)
  //                -> libsemigroups::FroidurePinBase::cayley_graph_type const&
  //                {
  //              return S->left_cayley_graph();
  //            })
  //       .def("right_cayley_graph",
  //            [](FroidurePin_ S)
  //                -> libsemigroups::FroidurePinBase::cayley_graph_type const&
  //                {
  //              return S->right_cayley_graph();
  //            })
  //       .def("factorisation",
  //            [](FroidurePin_ S, size_t i) { return S->factorisation(i); })
  //       .def("minimal_factorisation",
  //            [](FroidurePin_ S, size_t i) { return
  //            S->minimal_factorisation(i); })
  //       .def("product_by_reduction",
  //            [](FroidurePin_ S, size_t i, size_t j) {
  //              return S->product_by_reduction(i, j);
  //            })
  //       .def("current_position",
  //            [](FroidurePin_ S, libsemigroups::word_type const& w) {
  //              return S->current_position(w);
  //            })
  //       .def("current_size", [](FroidurePin_ S) { return S->current_size();
  //       }) .def("size", [](FroidurePin_ S) { return S->size(); })
  //       .def("finished", [](FroidurePin_ S) { return S->finished(); })
  //       .def("rules",
  //            [](FroidurePin_& S) {
  //              return gapbind14::make_iterator(S->cbegin_rules(),
  //                                              S->cend_rules());
  //            })
  //       .def("first_letter",
  //            [](FroidurePin_ S, size_t i) { return S->first_letter(i); })
  //       .def("final_letter",
  //            [](FroidurePin_ S, size_t i) { return S->final_letter(i); })
  //       .def("prefix", [](FroidurePin_ S, size_t i) { return S->prefix(i); })
  //       .def("suffix", [](FroidurePin_ S, size_t i) { return S->suffix(i);
  //       });
}
