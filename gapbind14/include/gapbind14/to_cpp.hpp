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

#ifndef INCLUDE_GAPBIND14_TO_CPP_HPP_
#define INCLUDE_GAPBIND14_TO_CPP_HPP_

#include <cstddef>      // for size_t
#include <string>       // for string
#include <string_view>  // for string_view
#include <type_traits>  // for enable_if_t, is_const, is_integral, is_same
#include <vector>       // for vector

#include "gap_include.hpp"

namespace gapbind14 {

  template <typename T>
  struct IsGapBind14Type;

  using gap_tnum_type = UInt;

  // For Obj -> T
  template <typename T, typename = void>
  struct to_cpp;

  template <typename T>
  struct to_cpp<
      T &,
      std::enable_if_t<!IsGapBind14Type<T>::value && !std::is_const<T>::value>>
      : to_cpp<T> {};

  template <typename T>
  struct to_cpp<T const &, std::enable_if_t<!IsGapBind14Type<T>::value>>
      : to_cpp<T> {};

  template <typename T>
  struct to_cpp<T &&, std::enable_if_t<!IsGapBind14Type<T>::value>>
      : to_cpp<T> {};

  ////////////////////////////////////////////////////////////////////////
  // void
  ////////////////////////////////////////////////////////////////////////

  template <>
  struct to_cpp<void> {
    using cpp_type                          = void;
    static gap_tnum_type constexpr gap_type = 0;

    void operator()() const noexcept {}
  };

  ////////////////////////////////////////////////////////////////////////
  // Obj
  ////////////////////////////////////////////////////////////////////////

  template <>
  struct to_cpp<Obj> {
    using cpp_type = Obj;

    Obj operator()(Obj o) const noexcept {
      return o;
    }
  };

  ////////////////////////////////////////////////////////////////////////
  // Strings
  ////////////////////////////////////////////////////////////////////////

  template <>
  struct to_cpp<std::string> {
    using cpp_type                          = std::string;
    static gap_tnum_type constexpr gap_type = T_STRING;

    std::string operator()(Obj o) const {
      if (TNUM_OBJ(o) != T_STRING) {
        throw std::runtime_error(std::string("expected string, found ")
                                 + TNAM_OBJ(o));
      }
      return std::string(CSTR_STRING(o), GET_LEN_STRING(o));
    }
  };

  template <>
  struct to_cpp<char const *> {
    using cpp_type                          = char const *;
    static gap_tnum_type constexpr gap_type = T_STRING;

    char const *operator()(Obj o) const {
      if (TNUM_OBJ(o) != T_STRING) {
        throw std::runtime_error(std::string("expected string, found ")
                                 + TNAM_OBJ(o));
      }
      return CSTR_STRING(o);
    }
  };

  template <>
  struct to_cpp<std::string_view> {
    using cpp_type                          = char const *;
    static gap_tnum_type constexpr gap_type = T_STRING;

    std::string_view operator()(Obj o) const {
      return to_cpp<char const *>()(o);
    }
  };

  ////////////////////////////////////////////////////////////////////////
  // Integers
  ////////////////////////////////////////////////////////////////////////

  template <typename T>
  struct to_cpp<T,
                std::enable_if_t<std::is_integral<T>::value
                                 && !std::is_same<T, bool>::value>> {
    using cpp_type                          = T;
    static gap_tnum_type constexpr gap_type = T_INT;

    Int operator()(Obj o) const {
      if (TNUM_OBJ(o) != T_INT) {
        throw std::runtime_error(std::string("expected int, found ")
                                 + TNAM_OBJ(o));
      }
      return INT_INTOBJ(o);
    }
  };

  ////////////////////////////////////////////////////////////////////////
  // Bools
  ////////////////////////////////////////////////////////////////////////

  template <>
  struct to_cpp<bool> {
    using cpp_type                          = bool;
    static gap_tnum_type constexpr gap_type = T_BOOL;

    bool operator()(Obj o) const {
      if (TNUM_OBJ(o) != T_BOOL) {
        throw std::runtime_error(std::string("expected bool, found ")
                                 + TNAM_OBJ(o));
      }
      return o == True ? true : false;
    }
  };

  ////////////////////////////////////////////////////////////////////////
  // Vectors
  ////////////////////////////////////////////////////////////////////////

  template <typename T>
  struct to_cpp<std::vector<T>> {
    using cpp_type                          = std::vector<T>;
    static gap_tnum_type constexpr gap_type = T_PLIST_HOM;

    std::vector<T> operator()(Obj o) const {
      if (!IS_LIST(o)) {
        throw std::runtime_error(std::string("expected list, found ")
                                 + TNAM_OBJ(o));
      }

      size_t const N   = LEN_LIST(o);
      using value_type = typename std::vector<T>::value_type;
      std::vector<T> result;
      result.reserve(N);
      for (size_t i = 0; i < N; ++i) {
        result.push_back(to_cpp<value_type>()(ELM_LIST(o, i + 1)));
      }
      return result;
    }
  };

}  // namespace gapbind14
#endif  // INCLUDE_GAPBIND14_TO_CPP_HPP_
