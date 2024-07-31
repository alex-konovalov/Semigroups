//
// Semigroups package for GAP
// Copyright (C) 2021 James D. Mitchell
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

#include "cong.hpp"

#include <exception>    // for exception
#include <memory>       // for shared_ptr
#include <type_traits>  // for true_type
#include <vector>       // for vector

// Semigroups GAP package headers
#include "froidure-pin.hpp"  // for to_cpp<FroidurePin<Bipartition>
#include "pkg.hpp"           // for IsGapBind14Type
#include "to_cpp.hpp"        // for to_cpp
#include "to_gap.hpp"        // for to_gap

// GAP headers
#include "compiled.h"  // for UInt2, UInt4

// GapBind14 headers
#include "gapbind14/gapbind14.hpp"  // for class_ etc

// libsemigroups headers
#include "libsemigroups/bipart.hpp"        // for Bipartition
#include "libsemigroups/cong-intf.hpp"     // for congruence_kind
#include "libsemigroups/cong.hpp"          // for Congruence
#include "libsemigroups/constants.hpp"     // for UNDEFINED etc
#include "libsemigroups/froidure-pin.hpp"  // for FroidurePin
#include "libsemigroups/matrix.hpp"        // for BMat etc
#include "libsemigroups/todd-coxeter.hpp"  // for ToddCoxeter
#include "libsemigroups/transf.hpp"        // for PPerm etc
#include "libsemigroups/types.hpp"         // for word_type

// Forward decls
namespace libsemigroups {
  class FpSemigroup;
  class PBR;
}  // namespace libsemigroups

namespace gapbind14 {
  template <>
  struct IsGapBind14Type<libsemigroups::Congruence> : std::true_type {
    static constexpr std::string_view name = "Congruence";
  };

}  // namespace gapbind14

////////////////////////////////////////////////////////////////////////
// Congruence
////////////////////////////////////////////////////////////////////////

using gapbind14::overload_cast;

void init_cong(gapbind14::Module& m) {
  using libsemigroups::Congruence;
  using libsemigroups::congruence_kind;
  using libsemigroups::FpSemigroup;
  using libsemigroups::FroidurePin;
  using libsemigroups::FroidurePinBase;
  using libsemigroups::word_type;

  using libsemigroups::Bipartition;
  using libsemigroups::BMat;
  using libsemigroups::IntMat;
  using libsemigroups::LeastPPerm;
  using libsemigroups::LeastTransf;
  using libsemigroups::MaxPlusMat;
  using libsemigroups::MaxPlusTruncMat;
  using libsemigroups::MinPlusMat;
  using libsemigroups::MinPlusTruncMat;
  using libsemigroups::NTPMat;
  using libsemigroups::PBR;
  using libsemigroups::PPerm;
  using libsemigroups::ProjMaxPlusMat;
  using libsemigroups::Transf;

  // Cannot use FroidurePinBase rather than the specialisations because there's
  // no constructor for a Congruence from a FroidurePinBase&.
  //  gapbind14::class_<Congruence>("Congruence")
  //      .def(gapbind14::init<congruence_kind, FroidurePin<Bipartition>
  //      const&>{},
  //           "make_from_froidurepin_bipartition")
  //      .def(gapbind14::init<congruence_kind, FroidurePin<BMat<>> const&>{},
  //           "make_from_froidurepin_bmat")
  //      .def(gapbind14::init<congruence_kind, FroidurePin<WBMat8> const&>{},
  //           "make_from_froidurepin_bmat8")
  //      .def(gapbind14::init<congruence_kind, FroidurePin<PBR> const&>{},
  //           "make_from_froidurepin_pbr")
  // #ifdef LIBSEMIGROUPS_HPCOMBI_ENABLED
  //      .def(gapbind14::init<congruence_kind,
  //                           FroidurePin<LeastPPerm<16>> const&>{},
  //           "make_from_froidurepin_leastpperm")
  //      .def(gapbind14::init<congruence_kind,
  //                           FroidurePin<LeastTransf<16>> const&>{},
  //           "make_from_froidurepin_leasttransf")
  // #endif
  //      .def(gapbind14::init<congruence_kind,
  //                           FroidurePin<Transf<0, UInt2>> const&>{},
  //           "make_from_froidurepin_transfUInt2")
  //      .def(gapbind14::init<congruence_kind,
  //                           FroidurePin<Transf<0, UInt4>> const&>{},
  //           "make_from_froidurepin_transfUInt4")
  //      .def(gapbind14::init<congruence_kind,
  //                           FroidurePin<PPerm<0, UInt2>> const&>{},
  //           "make_from_froidurepin_ppermUInt2")
  //      .def(gapbind14::init<congruence_kind,
  //                           FroidurePin<PPerm<0, UInt4>> const&>{},
  //           "make_from_froidurepin_ppermUInt4")
  //      .def(gapbind14::init<congruence_kind, FpSemigroup&>{},
  //           "make_from_fpsemigroup")
  //      .def(gapbind14::init<congruence_kind,
  //      std::shared_ptr<FroidurePinBase>>{},
  //           "make_from_froidurepinbase")
  //      .def(gapbind14::init<congruence_kind>{},
  //           "make_from_table")
  //      .def("set_number_of_generators",
  //      &Congruence::set_number_of_generators) .def("number_of_pairs",
  //      &Congruence::number_of_generating_pairs) .def("add_pair",
  //           overload_cast<word_type const&, word_type const&>(
  //               &Congruence::add_pair))
  //      .def("number_of_classes", &Congruence::number_of_classes)
  //      .def("word_to_class_index", &Congruence::word_to_class_index)
  //      .def("class_index_to_word", &Congruence::class_index_to_word)
  //      .def("contains", &Congruence::contains)
  //      .def("less", &Congruence::less)
  //      .def("add_runner",
  //           &Congruence::add_runner<libsemigroups::congruence::ToddCoxeter>)
  //      .def("is_quotient_obviously_infinite",
  //           &Congruence::is_quotient_obviously_infinite)
  //      .def("ntc",
  //           [](Congruence& C) {
  //             return gapbind14::make_iterator(C.cbegin_ntc(), C.cend_ntc());
  //           })
  //      .def("quotient_froidure_pin", &Congruence::quotient_froidure_pin);
}
