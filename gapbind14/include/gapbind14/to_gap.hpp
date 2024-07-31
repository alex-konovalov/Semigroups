//
// gapbind14
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

#ifndef INCLUDE_GAPBIND14_TO_GAP_HPP_
#define INCLUDE_GAPBIND14_TO_GAP_HPP_

#include <cstddef>      // for size_t
#include <string>       // for string
#include <type_traits>  // for enable_if_t, is_integral, is_same
#include <utility>      // for pair
#include <vector>       // for vector

#include "gap_include.hpp"  // for Obj, UInt

namespace gapbind14 {

  template <typename T>
  struct IsGapBind14Type;

  using gap_tnum_type = UInt;

  template <typename T, typename = void>
  struct to_gap;

  template <typename T>
  struct to_gap<
      T&,
      std::enable_if_t<!IsGapBind14Type<T>::value && !std::is_const<T>::value>>
      : to_gap<T> {};

  template <typename T>
  struct to_gap<T const&, std::enable_if_t<!IsGapBind14Type<T>::value>>
      : to_gap<T> {};

  template <typename T>
  struct to_gap<T&&, std::enable_if_t<!IsGapBind14Type<T>::value>> : to_gap<T> {
  };

  ////////////////////////////////////////////////////////////////////////
  // Obj
  ////////////////////////////////////////////////////////////////////////

  template <>
  struct to_gap<Obj> {
    using cpp_type = Obj;
    Obj operator()(Obj x) const noexcept {
      return x;
    }
  };

  ////////////////////////////////////////////////////////////////////////
  // Strings
  ////////////////////////////////////////////////////////////////////////

  template <>
  struct to_gap<std::string> {
    using cpp_type                          = std::string;
    static gap_tnum_type constexpr gap_type = T_STRING;

    Obj operator()(std::string_view str) const {
      Obj ret;
      C_NEW_STRING(ret, str.size(), str.begin());
      return ret;
    }
  };

  ////////////////////////////////////////////////////////////////////////
  // Integers
  ////////////////////////////////////////////////////////////////////////

  template <typename T>
  struct to_gap<T,
                std::enable_if_t<std::is_integral<T>::value
                                 && !std::is_same<T, bool>::value>> {
    using cpp_type                          = T;
    static gap_tnum_type constexpr gap_type = T_INT;

    Obj operator()(T&& i) const {
      return INTOBJ_INT(i);
    }

    Obj operator()(T const& i) const {
      return INTOBJ_INT(i);
    }
  };

  ////////////////////////////////////////////////////////////////////////
  // Bools
  ////////////////////////////////////////////////////////////////////////

  template <>
  struct to_gap<bool> {
    using cpp_type                          = bool;
    static gap_tnum_type constexpr gap_type = T_BOOL;

    Obj operator()(bool&& val) const noexcept {
      return (val ? True : False);
    }

    Obj operator()(bool const& val) const noexcept {
      return (val ? True : False);
    }
  };

  ////////////////////////////////////////////////////////////////////////
  // Vectors
  ////////////////////////////////////////////////////////////////////////

  template <typename T>
  struct to_gap<std::vector<T>> {
    using cpp_type                          = std::vector<T>;
    static gap_tnum_type constexpr gap_type = T_PLIST_HOM;

    Obj operator()(std::vector<T> const& v) const {
      Obj result = NEW_PLIST(T_PLIST, v.size());
      SET_LEN_PLIST(result, v.size());
      using value_type = typename std::vector<T>::value_type;
      size_t index     = 1;
      for (auto const& item : v) {
        AssPlist(result, index++, to_gap<value_type>()(item));
      }
      return result;
    }
  };

  ////////////////////////////////////////////////////////////////////////
  // Pairs
  ////////////////////////////////////////////////////////////////////////

  template <typename S, typename T>
  struct to_gap<std::pair<S, T>> {
    using cpp_type                          = std::pair<S, T>;
    static gap_tnum_type constexpr gap_type = T_PLIST;

    Obj operator()(std::pair<S, T> const& p) const {
      Obj result = NEW_PLIST(T_PLIST, 2);
      SET_LEN_PLIST(result, 2);
      AssPlist(result, 1, to_gap<S>()(p.first));
      AssPlist(result, 2, to_gap<T>()(p.second));
      return result;
    }
  };

}  // namespace gapbind14
#endif  // INCLUDE_GAPBIND14_TO_GAP_HPP_
