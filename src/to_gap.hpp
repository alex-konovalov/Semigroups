//
// Semigroups package for GAP
// Copyright (C) 2020-2022 James D. Mitchell
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

// This file contains specialisations of gapbind14::to_gap for various types
// defined in the GAP package Semigroups and the corresponding types in
// libsemigroups.

#ifndef SEMIGROUPS_SRC_TO_GAP_HPP_
#define SEMIGROUPS_SRC_TO_GAP_HPP_

// Standard library
#include <algorithm>    // for sort
#include <cstddef>      // for size_t
#include <cstdint>      // for uint32_t
#include <limits>       // for numeric_limits
#include <type_traits>  // for enable_if_t, decay_t, is_same
#include <vector>       // for vector

// GAP headers
#include "compiled.h"  // for Obj etc

// Semigroups package headers
#include "bipart.hpp"            // for bipart_new_obj
#include "froidure-pin.hpp"      // for WBMat8
#include "pkg.hpp"               // for TYPES_PBR etc
#include "semigroups-debug.hpp"  // for SEMIGROUPS_ASSERT

// gapbind14 headers
#include "gapbind14/to_gap.hpp"  // for gapbind14

// libsemigroups headers
#include "libsemigroups/adapters.hpp"    // for Degree
#include "libsemigroups/bipart.hpp"      // for Bipartition, IsBipartition
#include "libsemigroups/bmat8.hpp"       // for BMat8
#include "libsemigroups/config.hpp"      // for LIBSEMIGROUPS_HPCOMBI_ENABLED
#include "libsemigroups/constants.hpp"   // for NEGATIVE_INFINITY etc
#include "libsemigroups/matrix.hpp"      // for matrix_threshold etc
#include "libsemigroups/pbr.hpp"         // for PBR
#include "libsemigroups/transf.hpp"      // for IsPPerm, IsTransf
#include "libsemigroups/word-graph.hpp"  // for WordGraph

using libsemigroups::IsBMat;
using libsemigroups::IsIntMat;
using libsemigroups::IsMatrix;
using libsemigroups::IsMaxPlusMat;
using libsemigroups::IsMaxPlusTruncMat;
using libsemigroups::IsMinPlusMat;
using libsemigroups::IsMinPlusTruncMat;
using libsemigroups::IsNTPMat;
using libsemigroups::IsProjMaxPlusMat;

using libsemigroups::Bipartition;
using libsemigroups::MaxPlusTruncSemiring;
using libsemigroups::MinPlusTruncSemiring;
using libsemigroups::NTPSemiring;

using libsemigroups::IsBipartition;
using libsemigroups::IsPPerm;
using libsemigroups::IsTransf;

using libsemigroups::NEGATIVE_INFINITY;
using libsemigroups::NegativeInfinity;
using libsemigroups::POSITIVE_INFINITY;
using libsemigroups::PositiveInfinity;
using libsemigroups::UNDEFINED;

namespace gapbind14 {

  namespace detail {
    template <typename T, typename F = to_gap<typename T::scalar_type>>
    Obj
    make_matrix(T const& x, Obj gap_t, size_t extra_capacity, F&& func = F()) {
      size_t n      = x.number_of_rows();
      Obj    result = NEW_PLIST(T_PLIST, n + extra_capacity);
      SET_LEN_PLIST(result, n + extra_capacity);

      for (size_t i = 0; i < n; i++) {
        Obj row = NEW_PLIST_IMM(T_PLIST_CYC, n);
        SET_LEN_PLIST(row, n);
        for (size_t j = 0; j < n; j++) {
          AssPlist(row, j + 1, func(x(i, j)));
        }
        AssPlist(result, i + 1, row);
      }
      SEMIGROUPS_ASSERT(LEN_PLIST(result) == n + extra_capacity);
      if (gap_t != nullptr) {
        RetypeBag(result, T_POSOBJ);
        SET_TYPE_POSOBJ(result, gap_t);
        CHANGED_BAG(result);
      }
      return result;
    }
  }  // namespace detail

  ////////////////////////////////////////////////////////////////////////
  // Constants
  ////////////////////////////////////////////////////////////////////////

  template <>
  struct to_gap<PositiveInfinity> {
    template <typename T>
    Obj operator()(T const& x) {
      return Pinfinity;
    }
  };

  template <>
  struct to_gap<NegativeInfinity> {
    template <typename T>
    Obj operator()(T const& x) {
      return Ninfinity;
    }
  };

  ////////////////////////////////////////////////////////////////////////
  // BMat<> -> IsBooleanMat
  ////////////////////////////////////////////////////////////////////////

  template <>
  struct to_gap<libsemigroups::BMat<>> {
    Obj operator()(libsemigroups::BMat<> const& x) {
      size_t n = x.number_of_rows();
      Obj    o = NEW_PLIST(T_PLIST_TAB_RECT, n);
      SET_LEN_PLIST(o, n);

      for (size_t i = 0; i < n; i++) {
        Obj blist = NewBag(T_BLIST, SIZE_PLEN_BLIST(n));
        SET_LEN_BLIST(blist, n);
        for (size_t j = 0; j < n; j++) {
          if (x(i, j)) {
            SET_BIT_BLIST(blist, j + 1);
          }
        }
        MakeImmutable(blist);
        SET_ELM_PLIST(o, i + 1, blist);
        CHANGED_BAG(o);
      }

      SET_TYPE_POSOBJ(o, BooleanMatType);
      RetypeBag(o, T_POSOBJ);
      CHANGED_BAG(o);
      return o;
    }
  };

  template <>
  struct to_gap<semigroups::WBMat8> {
    Obj operator()(semigroups::WBMat8 const& x) {
      size_t n = x.second;
      Obj    o = NEW_PLIST(T_PLIST_TAB_RECT, n);
      SET_LEN_PLIST(o, n);

      for (size_t i = 0; i < n; i++) {
        Obj blist = NewBag(T_BLIST, SIZE_PLEN_BLIST(n));
        SET_LEN_BLIST(blist, n);
        for (size_t j = 0; j < n; j++) {
          if (x.first.get(i, j)) {
            SET_BIT_BLIST(blist, j + 1);
          }
        }
        MakeImmutable(blist);
        SET_ELM_PLIST(o, i + 1, blist);
        CHANGED_BAG(o);
      }

      SET_TYPE_POSOBJ(o, BooleanMatType);
      RetypeBag(o, T_POSOBJ);
      CHANGED_BAG(o);
      return o;
    }
  };

  ////////////////////////////////////////////////////////////////////////
  // MaxPlusMat<> -> MaxPlusMatrix
  ////////////////////////////////////////////////////////////////////////

  template <>
  struct to_gap<libsemigroups::MaxPlusMat<>> {
    using MaxPlusMat_ = libsemigroups::MaxPlusMat<>;
    Obj operator()(MaxPlusMat_ const& x) {
      using scalar_type = typename MaxPlusMat_::scalar_type;

      return detail::make_matrix(
          x, MaxPlusMatrixType, 0, [](scalar_type const& y) {
            return (y == NEGATIVE_INFINITY ? to_gap<NegativeInfinity>()(y)
                                           : to_gap<scalar_type>()(y));
          });
    }
  };

  ////////////////////////////////////////////////////////////////////////
  // MinPlusMat<> -> MinPlusMatrix
  ////////////////////////////////////////////////////////////////////////

  template <>
  struct to_gap<libsemigroups::MinPlusMat<>> {
    using MinPlusMat_ = libsemigroups::MinPlusMat<>;
    Obj operator()(MinPlusMat_ const& x) {
      using scalar_type = typename MinPlusMat_::scalar_type;

      return detail::make_matrix(
          x, MinPlusMatrixType, 0, [](scalar_type const& y) {
            return (y == POSITIVE_INFINITY ? to_gap<PositiveInfinity>()(y)
                                           : to_gap<scalar_type>()(y));
          });
    }
  };

  ////////////////////////////////////////////////////////////////////////
  // IntMat<> -> IntegerMatrix
  ////////////////////////////////////////////////////////////////////////

  template <>
  struct to_gap<libsemigroups::IntMat<>> {
    using IntMat_ = libsemigroups::IntMat<>;
    Obj operator()(IntMat_ const& x) {
      return CALL_2ARGS(Matrix, Integers, detail::make_matrix(x, nullptr, 0));
    }
  };

  ////////////////////////////////////////////////////////////////////////
  // MaxPlusTruncMat<> -> TropicalMaxPlusMatrix
  ////////////////////////////////////////////////////////////////////////

  template <>
  struct to_gap<libsemigroups::MaxPlusTruncMat<>> {
    using MaxPlusTruncMat_ = libsemigroups::MaxPlusTruncMat<>;
    Obj operator()(MaxPlusTruncMat_ const& x) {
      using libsemigroups::matrix_threshold;
      using scalar_type = typename MaxPlusTruncMat_::scalar_type;

      auto result = detail::make_matrix(
          x, TropicalMaxPlusMatrixType, 1, [](scalar_type const& y) {
            return (y == NEGATIVE_INFINITY ? to_gap<NegativeInfinity>()(y)
                                           : to_gap<scalar_type>()(y));
          });
      SET_ELM_PLIST(result,
                    x.number_of_rows() + 1,
                    to_gap<scalar_type>()(matrix_threshold(x)));
      return result;
    }
  };

  ////////////////////////////////////////////////////////////////////////
  // MinPlusTruncMat<> -> TropicalMinPlusMatrix
  ////////////////////////////////////////////////////////////////////////

  template <>
  struct to_gap<libsemigroups::MinPlusTruncMat<>> {
    using MinPlusTruncMat_ = libsemigroups::MinPlusTruncMat<>;

    Obj operator()(MinPlusTruncMat_ const& x) {
      using libsemigroups::matrix_threshold;
      using scalar_type = typename MinPlusTruncMat_::scalar_type;

      auto result = detail::make_matrix(
          x, TropicalMinPlusMatrixType, 1, [](scalar_type const& y) {
            return (y == POSITIVE_INFINITY ? to_gap<PositiveInfinity>()(y)
                                           : to_gap<scalar_type>()(y));
          });
      SET_ELM_PLIST(result,
                    x.number_of_rows() + 1,
                    to_gap<scalar_type>()(matrix_threshold(x)));
      return result;
    }
  };

  ////////////////////////////////////////////////////////////////////////
  // ProjectiveMaxPlusMat<> -> ProjectiveMaxPlusMatrix
  ////////////////////////////////////////////////////////////////////////

  template <>
  struct to_gap<libsemigroups::ProjMaxPlusMat<>> {
    using ProjMaxPlusMat_ = libsemigroups::ProjMaxPlusMat<>;

    Obj operator()(ProjMaxPlusMat_ const& x) {
      using scalar_type = typename ProjMaxPlusMat_::scalar_type;

      return detail::make_matrix(
          x, ProjectiveMaxPlusMatrixType, 0, [](scalar_type const& y) {
            return (y == NEGATIVE_INFINITY ? to_gap<NegativeInfinity>()(y)
                                           : to_gap<scalar_type>()(y));
          });
    }
  };

  ////////////////////////////////////////////////////////////////////////
  // NTPMat<> -> NTPMatrix
  ////////////////////////////////////////////////////////////////////////

  template <>
  struct to_gap<libsemigroups::NTPMat<>> {
    using NTPMat_ = libsemigroups::NTPMat<>;

    Obj operator()(NTPMat_ const& x) {
      using scalar_type = typename NTPMat_::scalar_type;
      using libsemigroups::matrix_period;
      using libsemigroups::matrix_threshold;

      auto result = detail::make_matrix(x, NTPMatrixType, 2);
      SET_ELM_PLIST(result,
                    x.number_of_rows() + 1,
                    to_gap<scalar_type>()(matrix_threshold(x)));
      SET_ELM_PLIST(result,
                    x.number_of_rows() + 2,
                    to_gap<scalar_type>()(matrix_period(x)));
      return result;
    }
  };

  ////////////////////////////////////////////////////////////////////////
  // Transformations
  ////////////////////////////////////////////////////////////////////////

  namespace detail {
    template <typename S, typename T>
    Obj make_transf(T const& x) {
      static_assert(
          std::is_same<S, UInt2>::value || std::is_same<S, UInt4>::value,
          "the template parameter S must be the same as UInt2 or UInt4");
      static_assert(
          IsTransf<T>
#ifdef LIBSEMIGROUPS_HPCOMBI_ENABLED
              || std::is_same<T, HPCombi::Transf16>::value
#endif
          ,
          "the template parameter T must be the same as Transf<> or Transf16");

      auto const N      = libsemigroups::Degree<T>()(x);
      Obj        result = NEW_TRANS(N);
      S* ptr = reinterpret_cast<S*>(static_cast<Obj*>(ADDR_OBJ(result) + 3));
      for (S i = 0; i < N; ++i) {
        ptr[i] = x[i];
      }
      return result;
    }
  }  // namespace detail

  template <>
  struct to_gap<libsemigroups::Transf<0, UInt2>> {
    Obj operator()(libsemigroups::Transf<0, UInt2> const& x) {
      return detail::make_transf<UInt2>(x);
    }
  };

  template <>
  struct to_gap<libsemigroups::Transf<0, UInt4>> {
    Obj operator()(libsemigroups::Transf<0, UInt4> const& x) {
      return detail::make_transf<UInt4>(x);
    }
  };

#ifdef LIBSEMIGROUPS_HPCOMBI_ENABLED
  template <>
  struct to_gap<HPCombi::Transf16> {
    Obj operator()(HPCombi::Transf16 const& x) {
      return detail::make_transf<UInt2>(x);
    }
  };
#endif

  ////////////////////////////////////////////////////////////////////////
  // Partial perms
  ////////////////////////////////////////////////////////////////////////

  namespace detail {
    inline Obj NEW_PPERM(UInt2 N) {
      return NEW_PPERM2(N);
    }

    inline Obj NEW_PPERM(UInt4 N) {
      return NEW_PPERM4(N);
    }

    template <typename S, typename T>
    Obj make_pperm(T const& x, S undef) {
      static_assert(
          std::is_same<S, UInt2>::value || std::is_same<S, UInt4>::value,
          "the template parameter T must be the same as UInt2 or UInt4");
      static_assert(
          IsPPerm<T>
#ifdef LIBSEMIGROUPS_HPCOMBI_ENABLED
              || std::is_same<T, HPCombi::PPerm16>::value
#endif
          ,
          "the template parameter T must be the same as PPerm<> or PPerm16");

      S N = libsemigroups::Degree<T>()(x);
      // remove trailing 0s
      while (N > 0 && x[N - 1] == undef) {
        N--;
      }

      Obj result = NEW_PPERM(N);
      S*  ptr
          = reinterpret_cast<S*>(static_cast<Obj*>(ADDR_OBJ(result)) + 2) + 1;
      for (S i = 0; i < N; i++) {
        if (x[i] == undef) {
          ptr[i] = 0;
        } else {
          ptr[i] = x[i] + 1;
        }
      }
      return result;
    }
  }  // namespace detail

  template <>
  struct to_gap<libsemigroups::PPerm<0, UInt2>> {
    Obj operator()(libsemigroups::PPerm<0, UInt2> const& x) {
      return detail::make_pperm<UInt2>(x, UNDEFINED);
    }
  };

  template <>
  struct to_gap<libsemigroups::PPerm<0, UInt4>> {
    Obj operator()(libsemigroups::PPerm<0, UInt4> const& x) {
      return detail::make_pperm<UInt4>(x, UNDEFINED);
    }
  };

#ifdef LIBSEMIGROUPS_HPCOMBI_ENABLED
  template <>
  struct to_gap<HPCombi::PPerm16> {
    Obj operator()(HPCombi::PPerm16 const& x) {
      return detail::make_pperm<UInt2>(x, 0xFF);
    }
  };
#endif

  ////////////////////////////////////////////////////////////////////////
  // Bipartition
  ////////////////////////////////////////////////////////////////////////

  template <>
  struct to_gap<Bipartition> {
    Obj operator()(Bipartition const& x) const {
      return bipart_new_obj(new Bipartition(x));
    }
  };

  ////////////////////////////////////////////////////////////////////////
  // PBR
  ////////////////////////////////////////////////////////////////////////

  template <>
  struct to_gap<libsemigroups::PBR> {
    Obj operator()(libsemigroups::PBR x) const {
      Obj result = NEW_PLIST(T_PLIST, 2 * x.degree() + 1);
      // can't use T_PLIST_TAB/HOM here because some of the subplists might be
      // empty
      SET_LEN_PLIST(result, 2 * x.degree() + 1);
      SET_ELM_PLIST(result, 1, INTOBJ_INT(x.degree()));
      for (uint32_t i = 0; i < 2 * x.degree(); i++) {
        Obj next = SUM(to_gap<std::vector<uint32_t>>()(x[i]), INTOBJ_INT(1));
        SET_ELM_PLIST(result, i + 2, next);
        CHANGED_BAG(result);
      }
      SET_TYPE_POSOBJ(result, get_gap_type(x.degree()));
      RetypeBag(result, T_POSOBJ);
      CHANGED_BAG(result);
      return result;
    }

    static Obj get_gap_type(size_t N) {
      N++;
      if (N > static_cast<size_t>(LEN_PLIST(TYPES_PBR))
          || ELM_PLIST(TYPES_PBR, N) == 0) {
        CALL_1ARGS(TYPE_PBR, INTOBJ_INT(N - 1));
      }
      return ELM_PLIST(TYPES_PBR, N);
    }
  };

  ////////////////////////////////////////////////////////////////////////
  // DynamicArray2
  ////////////////////////////////////////////////////////////////////////

  template <typename T>
  struct to_gap<libsemigroups::detail::DynamicArray2<T>> {
    using DynamicArray2_ = libsemigroups::detail::DynamicArray2<T>;
    Obj operator()(DynamicArray2_ const& da) {
      using value_type = typename DynamicArray2_::value_type;
      Obj result       = NEW_PLIST(T_PLIST_TAB_RECT, da.number_of_rows());
      // this is intentionally not IMMUTABLE
      SET_LEN_PLIST(result, da.number_of_rows());

      for (size_t i = 0; i < da.number_of_rows(); ++i) {
        Obj next = NEW_PLIST(T_PLIST_CYC, da.number_of_cols());
        // this is intentionally not IMMUTABLE
        SET_LEN_PLIST(next, da.number_of_cols());
        for (size_t j = 0; j < da.number_of_cols(); ++j) {
          SET_ELM_PLIST(next, j + 1, to_gap<value_type>()(da.get(i, j)));
        }
        SET_ELM_PLIST(result, i + 1, next);
        CHANGED_BAG(result);
      }
      return result;
    }
  };

  ////////////////////////////////////////////////////////////////////////
  // WordGraph
  ////////////////////////////////////////////////////////////////////////

  template <typename T>
  struct to_gap<libsemigroups::WordGraph<T>> {
    using WordGraph_ = libsemigroups::WordGraph<T>;
    Obj operator()(WordGraph_ const& ad) const noexcept {
      using node_type = typename WordGraph_::node_type;
      Obj result      = NEW_PLIST(T_PLIST, ad.number_of_nodes());
      // this is intentionally not IMMUTABLE
      // TODO(WordGraph) handle case of zero nodes?
      SET_LEN_PLIST(result, ad.number_of_nodes());

      for (size_t i = 0; i < ad.number_of_nodes(); ++i) {
        Obj next = NEW_PLIST(T_PLIST, 0);
        SET_LEN_PLIST(next, 0);
        for (size_t j = 0; j < ad.out_degree(); ++j) {
          auto val = ad.target_no_checks(i, j);
          if (val != UNDEFINED) {
            AssPlist(next, j + 1, to_gap<node_type>()(val + 1));
          }
        }
        SET_ELM_PLIST(result, i + 1, next);
        CHANGED_BAG(result);
      }
      return result;
    }
  };

  // TODO could use magic_enum and make this generic
  template <>
  struct to_gap<libsemigroups::Order> {
    Obj operator()(libsemigroups::Order const& val) const noexcept {
      using order = libsemigroups::Order;
      switch (val) {
        case order::shortlex:
          return to_gap<std::string>()("shortlex");
        case order::lex:
          return to_gap<std::string>()("lex");
        case order::none:
          return to_gap<std::string>()("none");
        case order::recursive:
          return to_gap<std::string>()("recursive");
      }
    }
  };

}  // namespace gapbind14
#endif  // SEMIGROUPS_SRC_TO_GAP_HPP_
