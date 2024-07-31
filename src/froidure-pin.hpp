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

#ifndef SEMIGROUPS_SRC_FROIDURE_PIN_HPP_
#define SEMIGROUPS_SRC_FROIDURE_PIN_HPP_

#include <cstddef>      // for size_t
#include <string>       // for string
#include <type_traits>  // for true_type
#include <utility>      // for pair
#include <vector>       // for vector

// GapBind14 headers
#include "gapbind14/gapbind14.hpp"  // for Module etc

// libsemigroups headers
#include "libsemigroups/bmat8.hpp"         // for BMat8
#include "libsemigroups/froidure-pin.hpp"  // for FroidurePin

namespace gapbind14 {

  template <typename T>
  struct IsGapBind14Type<libsemigroups::FroidurePin<T>> : std::true_type {
    // TODO have to do this properly! By probably having one of these structs
    // per type T
    static constexpr std::string_view name = "FroidurePinT";
  };

  template <>
  struct IsGapBind14Type<libsemigroups::FroidurePinBase> : std::true_type {
    static constexpr std::string_view name = "FroidurePinBase";
  };

}  // namespace gapbind14

void init_froidure_pin_bipart(gapbind14::Module&);
void init_froidure_pin_bmat(gapbind14::Module&);
void init_froidure_pin_matrix(gapbind14::Module&);
void init_froidure_pin_max_plus_mat(gapbind14::Module&);
void init_froidure_pin_min_plus_mat(gapbind14::Module&);
void init_froidure_pin_pbr(gapbind14::Module&);
void init_froidure_pin_pperm(gapbind14::Module&);
void init_froidure_pin_transf(gapbind14::Module&);

void init_froidure_pin_base(gapbind14::Module& m);

template <typename element_type>
void bind_froidure_pin(gapbind14::Module& m, std::string name) {
  //  using libsemigroups::FroidurePin;
  //  using FroidurePin_    = FroidurePin<element_type>;
  //  using const_reference = typename
  //  FroidurePin<element_type>::const_reference; using element_index_type =
  //      typename FroidurePin<element_type>::element_index_type;
  //  gapbind14::class_<FroidurePin_>(name)
  //      .def(gapbind14::init<>{}, "make")
  //      .def(gapbind14::init<FroidurePin_ const&>{}, "copy")
  //      .def("add_generator", &FroidurePin_::add_generator)
  //      .def("generator", &FroidurePin_::generator)
  //      .def("closure",
  //           &FroidurePin_::template closure<std::vector<element_type>>)
  //      .def("number_of_generators", &FroidurePin_::number_of_generators)
  //      .def("size", &FroidurePin_::size)
  //      .def("at", &FroidurePin_::at)
  //      .def("sorted_at", &FroidurePin_::sorted_at)
  //      .def("current_position",
  //           gapbind14::overload_cast<const_reference>(
  //               &FroidurePin_::current_position))
  //      .def("sorted_position", &FroidurePin_::sorted_position)
  //      .def("number_of_idempotents", &FroidurePin_::number_of_idempotents)
  //      .def("enumerate", &FroidurePin_::enumerate)
  //      .def("left_cayley_graph", &FroidurePin_::left_cayley_graph)
  //      .def("right_cayley_graph", &FroidurePin_::right_cayley_graph)
  //      .def("factorisation",
  //           gapbind14::overload_cast<element_index_type>(
  //               &FroidurePin_::factorisation))
  //      .def("position_to_sorted_position",
  //           &FroidurePin_::position_to_sorted_position)
  //      .def("fast_product", &FroidurePin_::fast_product)
  //      .def("is_idempotent", &FroidurePin_::is_idempotent)
  //      .def("finished", &FroidurePin_::finished)
  //      .def("position", &FroidurePin_::position)
  //      .def("rules",
  //           [](FroidurePin_& S) {
  //             return gapbind14::make_iterator(S.cbegin_rules(),
  //             S.cend_rules());
  //           })
  //      .def("idempotents",
  //           [](FroidurePin_& S) {
  //             return gapbind14::make_iterator(S.cbegin_idempotents(),
  //                                             S.cend_idempotents());
  //           })
  //      .def("first_letter", &FroidurePin_::first_letter)
  //      .def("final_letter", &FroidurePin_::final_letter)
  //      .def("prefix", &FroidurePin_::prefix)
  //      .def("suffix", &FroidurePin_::suffix);
}

namespace semigroups {
  using WBMat8 = std::pair<libsemigroups::BMat8, uint8_t>;
}

namespace libsemigroups {
  using semigroups::WBMat8;

  template <>
  struct Complexity<WBMat8> {
    constexpr inline size_t operator()(WBMat8 const& x) const noexcept {
      return Complexity<BMat8>()(x.first);
    }
  };

  template <>
  struct Degree<WBMat8> {
    size_t operator()(WBMat8 const& x) const noexcept {
      return x.second;
    }
  };

  template <>
  struct One<WBMat8> {
    WBMat8 operator()(WBMat8 const& x) const noexcept {
      return std::make_pair(One<BMat8>()(x.first), x.second);
    }
  };

  template <>
  struct Product<WBMat8> {
    void operator()(WBMat8&       xy,
                    WBMat8 const& x,
                    WBMat8 const& y,
                    size_t = 0) const noexcept {
      return Product<BMat8>()(xy.first, x.first, y.first);
    }
  };

  template <>
  struct Hash<WBMat8> {
    size_t operator()(WBMat8 const& x) {
      return Hash<BMat8>()(x.first);
    }
  };

  template <>
  struct IncreaseDegree<WBMat8> {
    inline void operator()(WBMat8 const&) const noexcept {}
  };

}  // namespace libsemigroups

#endif  // SEMIGROUPS_SRC_FROIDURE_PIN_HPP_
