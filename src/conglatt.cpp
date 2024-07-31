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

// This file contains a function LATTICE_OF_CONGRUENCES for finding the lattice
// of congruences when there are too many generating congruences for
// Froidure-Pin to handle.

#include "conglatt.hpp"

#include <algorithm>      // for equal, max
#include <chrono>         // for time_point
#include <cmath>          // for log2
#include <cstddef>        // for size_t
#include <cstdint>        // for uint16_t, uint32_t
#include <iostream>       // for cout
#include <memory>         // for unique_ptr
#include <numeric>        // for iota
#include <unordered_map>  // for unordered_map
#include <utility>        // for swap, pair
#include <vector>         // for vector

// GAP headers
#include "compiled.h"

// Semigroups package for GAP headers
#include "semigroups-debug.hpp"  // for SEMIGROUPS_ASSERT

// libsemigroups headers
#include "libsemigroups/adapters.hpp"  // for Hash
#include "libsemigroups/detail/report.hpp"    // for should_report
#include "libsemigroups/detail/string.hpp"    // for group_digits
                                       //

namespace semigroups {
  namespace {
    // This class is minimally adapted from libsemigroups::detail::UF, but
    // specialised for the problem at hand.
    template <typename T>
    class UF {
      std::vector<T> _data;
      size_t         _log2_data_size;

     public:
      ////////////////////////////////////////////////////////////////////////
      // Aliases - public
      ////////////////////////////////////////////////////////////////////////
      using size_type      = size_t;
      using node_type      = T;
      using container_type = std::vector<T>;
      using index_type     = T;

      // not noexcept because the constructors of std::vector and std::array
      // aren't
      explicit UF(size_type size)
          : _data(size, 0),
            _log2_data_size(
                std::max(static_cast<size_t>(std::log2(_data.size())),
                         static_cast<size_t>(1))) {
        SEMIGROUPS_ASSERT(size != 0);
        std::iota(_data.begin(), _data.end(), 0);
      }

      // not noexcept because the constructors of std::vector and std::array
      // aren't
      UF(UF const&)            = default;
      UF& operator=(UF const&) = default;
      UF(UF&&)                 = default;
      UF& operator=(UF&&)      = default;
      ~UF()                    = default;

      // not noexcept because std::vector::operator[] isn't
      index_type find(index_type x) const {
        SEMIGROUPS_ASSERT(x < _data.size());
        auto y = _data[x];
        while (y != _data[y]) {
          y = _data[y];
        }
        return y;
      }

      // not noexcept because UF::find isn't
      void unite(index_type x, index_type y) {
        SEMIGROUPS_ASSERT(x < _data.size());
        SEMIGROUPS_ASSERT(y < _data.size());
        x = find(x);
        y = find(y);
        if (x < y) {
          _data[y] = x;
        } else {
          _data[x] = y;
        }
      }

      // Not noexcept because std::equal isn't
      bool operator==(UF const& that) const {
        return std::equal(that._data.cbegin(),
                          that._data.cend(),
                          _data.cbegin(),
                          _data.cend());
      }

      void normalize() {
        for (index_type i = 0; i < _data.size(); ++i) {
          _data[i] = find(_data[i]);
        }
      }

      void join(UF const& x, UF const& y) {
        SEMIGROUPS_ASSERT(size() == x.size());
        SEMIGROUPS_ASSERT(size() == y.size());
        for (index_type i = 0; i < _data.size(); ++i) {
          _data[i] = x._data[i];
          unite(x._data[i], y._data[i]);
        }
        normalize();
      }

      size_t hash() const {
        size_t val = 0;
        for (auto it = _data.cbegin(); it < _data.cend();
             it += _log2_data_size) {
          val ^= *it + 0x9e3779b97f4a7c16 + (val << 6);
        }
        return val;
      }

      size_t size() const noexcept {
        return _data.size();
      }
    };
  }  // namespace
}  // namespace semigroups

namespace libsemigroups {
  template <typename T>
  struct Hash<semigroups::UF<T>*> {
    size_t operator()(semigroups::UF<T>* x) const {
      return x->hash();
    }
  };

  template <typename T>
  struct Hash<semigroups::UF<T>> {
    size_t operator()(semigroups::UF<T> const& x) const {
      return x.hash();
    }
  };

  template <typename T>
  struct EqualTo<semigroups::UF<T>*> {
    size_t operator()(semigroups::UF<T>* x, semigroups::UF<T>* y) const {
      return *x == *y;
    }
  };
}  // namespace libsemigroups

namespace semigroups {
  namespace {
    // should be to_cpp<UF>
    auto to_uf(Obj lookup) {
      using UF = UF<uint16_t>;
      SEMIGROUPS_ASSERT(IS_LIST(lookup));
      size_t const n = LEN_LIST(lookup);
      SEMIGROUPS_ASSERT(n < 65536);
      UF uf(n);
      for (uint16_t i = 0; i < n; ++i) {
        SEMIGROUPS_ASSERT(IS_INTOBJ(ELM_LIST(lookup, i)));
        SEMIGROUPS_ASSERT(INT_INTOBJ(ELM_LIST(lookup, i)) >= 1);
        SEMIGROUPS_ASSERT(INT_INTOBJ(ELM_LIST(lookup, i)) <= n);
        uf.unite(i, INT_INTOBJ(ELM_LIST(lookup, i + 1)) - 1);
      }
      return uf;
    }
  }  // namespace

  Obj LATTICE_OF_CONGRUENCES(Obj list) {
    using UF = UF<uint16_t>;

    using libsemigroups::EqualTo;
    using libsemigroups::Hash;
    using libsemigroups::detail::group_digits;

    using std::chrono::duration_cast;
    using std::chrono::nanoseconds;
    using std::chrono::seconds;

    if (LEN_LIST(list) == 0) {
      ErrorQuit(
          "the argument must be a list of length at least 1, found 0", 0L, 0L);
    }
    size_t const n = LEN_LIST(ELM_LIST(list, 1));
    if (n > 65535) {
      // Then the values in the lookup won't fit into uint16_t
      ErrorQuit("the lists in the argument must have length at most 65535, "
                "found %d",
                (Int) LEN_LIST(list),
                0L);
    }

    auto     start_time  = std::chrono::high_resolution_clock::now();
    auto     last_report = start_time;
    uint32_t last_count  = 1;
    bool     report      = libsemigroups::reporting_enabled();

    std::vector<UF> gens;
    gens.reserve(LEN_LIST(list));

    for (size_t i = 1; i <= LEN_LIST(list); ++i) {
      gens.push_back(to_uf(ELM_LIST(list, i)));
    }

    std::unordered_map<UF*, uint32_t, Hash<UF*>, EqualTo<UF*>> res;
    Obj latt = NEW_PLIST(T_PLIST_TAB_RECT, 1);
    AssPlist(latt, 1, NEW_PLIST(T_PLIST_CYC, gens.size()));

    auto one = std::make_unique<UF>(n);
    auto tmp = std::make_unique<UF>(n);

    std::vector<std::unique_ptr<UF>> todo;
    res.emplace(one.get(), 0);
    todo.push_back(std::move(one));

    for (size_t i = 0; i < todo.size(); ++i) {
      size_t const old_todo_size = todo.size();

      for (size_t j = 0; j < gens.size(); ++j) {
        auto const& g = gens[j];
        tmp->join(*todo[i], g);
        auto it = res.find(tmp.get());
        if (it == res.end()) {
          auto cpy = std::make_unique<UF>(*tmp);
          res.emplace(cpy.get(), todo.size());
          AssPlist(ELM_PLIST(latt, i + 1), j + 1, INTOBJ_INT(todo.size() + 1));
          todo.push_back(std::move(cpy));
        } else {
          AssPlist(ELM_PLIST(latt, i + 1), j + 1, INTOBJ_INT(it->second + 1));
        }
      }
      for (size_t k = old_todo_size; k < todo.size(); ++k) {
        PushPlist(latt, NEW_PLIST(T_PLIST_CYC, gens.size()));
      }

      if (report) {
        auto now = std::chrono::high_resolution_clock::now();
        if (now - last_report > std::chrono::seconds(1)) {
          auto total_time = duration_cast<seconds>(now - start_time);
          auto diff_time  = duration_cast<seconds>(now - last_report);
          std::cout << "#I  Found " << group_digits(res.size())
                    << " congruences in " << total_time.count() << "s ("
                    << group_digits((todo.size() - last_count)
                                    / diff_time.count())
                    << "/s)!\n";
          std::swap(now, last_report);
          last_count = todo.size();
        }
      }
    }
    return latt;
  }
}  // namespace semigroups
