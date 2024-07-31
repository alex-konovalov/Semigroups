//
// gapbind14
// Copyright (C) 2021-2022 James D. Mitchell
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

// TODO:
// * Allow return Fail instead of ErrorQuit in GAPBIND14_TRY
// * Allow custom printing
// * Support enums
// * Support operators
// * tests for gapbind14/demo
// * update gapbind14/README.md
// * gapbind: iwyu in all files
// * gapbind: const/noexcept in all files
// * gapbind: use string_views where possible

#ifndef INCLUDE_GAPBIND14_GAPBIND14_HPP_
#define INCLUDE_GAPBIND14_GAPBIND14_HPP_

#include <cstddef>        // for size_t
#include <iostream>       // for ostringstream
#include <iterator>       // for distance, iterator_traits
#include <memory>         // for shared_ptr
#include <sstream>        // for ostringstream
#include <stdexcept>      // for runtime_error
#include <string>         // for string
#include <type_traits>    // for enable_if_t
#include <typeinfo>       // for typeid
#include <unordered_map>  // for unordered_map
#include <utility>        // for make_pair
#include <vector>         // for vector

#include "gap_include.hpp"   // for Obj etc
#include "tame_free_fn.hpp"  // for tame free functions
#include "tame_mem_fn.hpp"   // for tame member functions
#include "to_gap.hpp"        // for to_gap

////////////////////////////////////////////////////////////////////////
// Assertions
////////////////////////////////////////////////////////////////////////

#ifdef GAPBIND14_DEBUG
#define GAPBIND14_ASSERT(x) assert(x)
#else
#define GAPBIND14_ASSERT(x)
#endif

////////////////////////////////////////////////////////////////////////
// Macros
////////////////////////////////////////////////////////////////////////

#define GAPBIND14_MODULE(name)                                                 \
  static void gapbind14_init_##name();                                         \
  int         gapbind14_dummy_var_##name                                       \
      = ::gapbind14::detail::emplace_init_func(#name, &gapbind14_init_##name); \
  void gapbind14_init_##name()

#define GAPBIND14_TYPE(gap_name, cpp_type)             \
  template <>                                          \
  struct IsGapBind14Type<cpp_type> : std::true_type {  \
    static constexpr std::string_view name = gap_name; \
  };

namespace gapbind14 {

  ////////////////////////////////////////////////////////////////////////
  // Helpers for interacting with GAP
  ////////////////////////////////////////////////////////////////////////

  // Provides a mechanism for defining and accessing GAP library variables in
  // the kernel module.
  class LibraryGVar_ {
    std::vector<Obj>                        _GAP_LibraryGVars;
    std::unordered_map<std::string, size_t> _map;
    bool                                    _imported;

   public:
    LibraryGVar_() : _GAP_LibraryGVars(), _map(), _imported(false) {}

    Obj operator()(std::string_view name);

    void operator()(std::initializer_list<std::string_view> names) {
      for (auto const& name : names) {
        operator()(name);
      }
    }

    void import_all();
  };

  class TNums_ {
    std::vector<UInt>                       _GAP_TNums;
    std::unordered_map<std::string, size_t> _map;

   public:
    TNums_() : _GAP_TNums(), _map() {}

    UInt& operator()(std::string_view name);
  };

  extern LibraryGVar_ LibraryGVar;
  extern TNums_       TNums;

  ////////////////////////////////////////////////////////////////////////
  // Aliases
  ////////////////////////////////////////////////////////////////////////
  // TODO remove
  using gapbind14_subtype = size_t;

  ////////////////////////////////////////////////////////////////////////
  // Constants
  ////////////////////////////////////////////////////////////////////////

  // TODO remove
  extern UInt T_GAPBIND14_OBJ;

  template <typename T>
  struct IsGapBind14Type : std::false_type {};

  template <typename T>
  struct IsGapBind14Type<T&> : IsGapBind14Type<T> {};

  template <typename T>
  struct IsGapBind14Type<T&&> : IsGapBind14Type<T> {};

  template <typename T>
  struct IsGapBind14Type<T const&> : IsGapBind14Type<T> {};

  template <typename T>
  struct IsGapBind14Type<std::shared_ptr<T>> : IsGapBind14Type<T> {};

  void init_library(char const*);
  void init_kernel(char const*);

  class Module;  // Forward decl
  Module& module();

  ////////////////////////////////////////////////////////////////////////
  // Helper functions
  ////////////////////////////////////////////////////////////////////////

  namespace detail {

    // TODO move into Module
    int emplace_init_func(char const* module_name, void (*func)());

    // Convert object to string
    // TODO remove? Just use std::to_string?
    template <typename T>
    std::string to_string(T const& n) {
      std::ostringstream stm;
      stm << n;
      return stm.str();
    }

    void require_gapbind14_obj(Obj o);

    // Get the gapbind14 subtype of the object o.
    gapbind14_subtype obj_subtype(Obj o);

    template <typename T>
    T* obj_cpp_ptr(Obj o) {
      // Couldn't add static_assert that IsGapBind14Type<T>::value is true
      // because sometimes we call this function when T is a base class of a
      // class where IsGapBind14Type<T>::value is true.
      // require_gapbind14_obj(o);
      // Also cannot check that subtype of o corresponds to T for the same
      // reason as above T might be a base class of a GapBind14Type.
      return reinterpret_cast<T*>(ADDR_OBJ(o)[1]);
    }

    char const* copy_c_str(std::string const& str);
    char const* copy_c_str(std::string_view sv);

    char const* params_c_str(size_t nr);

    ////////////////////////////////////////////////////////////////////////
    // SubtypeBase class - for polymorphism
    ////////////////////////////////////////////////////////////////////////

    class SubtypeBase {
     private:
      std::string       _name;
      gapbind14_subtype _subtype;

     public:
      SubtypeBase(std::string nm, gapbind14_subtype sbtyp);

      virtual ~SubtypeBase() {}

      std::string const& name() const {
        return _name;
      }

      gapbind14_subtype subtype() const noexcept {
        return _subtype;
      }

      virtual void free(Obj o) = 0;
    };

    ////////////////////////////////////////////////////////////////////////
    // Subtype class
    ////////////////////////////////////////////////////////////////////////

    template <typename T>
    class Subtype : public SubtypeBase {
     public:
      using class_type = T;

      Subtype(std::string nm, gapbind14_subtype sbtyp)
          : SubtypeBase(nm, sbtyp) {}

      void free(Obj o) override {
        static_assert(IsGapBind14Type<T>::value,
                      "template parameter T must satisfy IsGapbind14Type<T>");
        GAPBIND14_ASSERT(obj_subtype(o) == module().subtype<T>());
        delete detail::obj_cpp_ptr<T>(o);
      }
    };
  }  // namespace detail

  ////////////////////////////////////////////////////////////////////////
  // Module class
  ////////////////////////////////////////////////////////////////////////

  class Module {
   public:
    struct MethodToInstall {
      std::string                   name;
      std::string                   info_string;
      std::vector<std::string_view> filt_list;
      StructGVarFunc                func;
    };

    struct CategoryToDeclare {
      std::string name;
      std::string parent;
    };

    struct OperationToDeclare {
      std::string                   name;
      std::vector<std::string_view> filt_list;
    };

    struct AttributeToDeclare {
      AttributeToDeclare(std::string_view name_, std::string_view filt_)
          : filt(filt_), name(name_) {}
      std::string_view filt;
      std::string_view name;
    };

    struct TNUMToRegister {
      TNUMToRegister(std::string_view name_) : name(name_) {}
      std::string name;
    };

   private:
    // TODO use StructGVarOper?

    std::vector<AttributeToDeclare> _attributes_to_declare;
    std::vector<CategoryToDeclare>  _categories_to_declare;
    std::vector<StructGVarFunc>     _funcs;
    std::vector<StructGVarFilt>     _filts;
    std::vector<MethodToInstall>    _methods_to_install;
    std::vector<OperationToDeclare> _operations_to_declare;
    std::vector<AttributeToDeclare> _properties_to_declare;
    std::vector<TNUMToRegister>     _tnums_to_register;

    // TODO remove
    std::vector<std::vector<StructGVarFunc>>           _mem_funcs;
    std::unordered_map<std::string, gapbind14_subtype> _subtype_names;
    std::vector<detail::SubtypeBase*>                  _subtypes;
    std::unordered_map<size_t, gapbind14_subtype>      _type_to_subtype;

    // TODO remove
    static size_t _next_subtype;

    typedef Obj (*GVarFunc)(/*arguments*/);

   public:
    // TODO to cpp
    Module()
        : _funcs(),
          _mem_funcs(),
          _subtype_names(),  // TODO init everything
          _subtypes(),
          _type_to_subtype() {}

    Module(Module const&)            = delete;
    Module(Module&&)                 = delete;
    Module& operator=(Module const&) = delete;
    Module& operator=(Module&&)      = delete;

    ~Module();

    void clear();

    // TODO remove
    gapbind14_subtype subtype(std::string const& subtype_name) const;

    // TODO remove
    template <typename T>
    gapbind14_subtype subtype() const {
      auto it = _type_to_subtype.find(typeid(T).hash_code());
      if (it == _type_to_subtype.end()) {
        throw std::runtime_error(std::string("No subtype for ")
                                 + typeid(T).name());
      }
      return it->second;
    }

    // TODO remove
    const char* subtype_name(Obj o) const {
      return _subtypes.at(detail::obj_subtype(o))->name().c_str();
    }

    // TODO remove
    void print(Obj o) {
      Pr("<class %s at %s>",
         (Int) subtype_name(o),
         (Int) detail::to_string(o).c_str());
    }

    // TODO remove
    void save(Obj o) {
      SaveUInt(detail::obj_subtype(o));
    }

    // TODO remove
    void load(Obj o) const;

    // TODO remove
    void free(Obj o) const {
      _subtypes.at(detail::obj_subtype(o))->free(o);
    }

    StructGVarFunc const* funcs() const {
      return &_funcs[0];
    }

    StructGVarFunc const* mem_funcs(std::string const& nm) const {
      return &_mem_funcs[subtype(nm)][0];
    }

    StructGVarFilt const* filters() const {
      return &_filts[0];
    }

    // TODO move elsewhere
    static void toupper(std::string& s) {
      std::transform(s.begin(), s.end(), s.begin(), [](auto c) {
        return std::toupper(c);
      });
    }

    // TODO remove
    template <typename T>
    gapbind14_subtype add_subtype(std::string&& nm) {
      bool inserted
          = _subtype_names.insert(std::make_pair(nm, _subtypes.size())).second;
      if (!inserted) {
        throw std::runtime_error("Subtype named " + nm + " already registered");
      }

      _type_to_subtype.emplace(typeid(T).hash_code(), _subtypes.size());
      _subtypes.push_back(new detail::Subtype<T>(nm, _subtypes.size()));
      // TODO delete next
      _mem_funcs.push_back(std::vector<StructGVarFunc>());
      _tnums_to_register.push_back({nm});
      return _subtypes.back()->subtype();
    }

    template <typename... Args>
    void add_func(std::string        fnm,
                  std::string const& nm,
                  Obj (*func)(Args...)) {
      static_assert(sizeof...(Args) > 0,
                    "there must be at least 1 parameter: Obj self");
      static_assert(sizeof...(Args) <= 7, "Args must be at most 7");

      _funcs.push_back({detail::copy_c_str(nm),
                        sizeof...(Args) - 1,
                        detail::params_c_str(sizeof...(Args) - 1),
                        (GVarFunc) func,
                        detail::copy_c_str(fnm + ":Func" + nm)});
    }

    // TODO remove
    template <typename... Args>
    void add_mem_func(std::string const& sbtyp,
                      std::string        flnm,
                      std::string const& nm,
                      Obj (*func)(Args...)) {
      static_assert(sizeof...(Args) <= 7, "Args must be at most 7");
      _mem_funcs.at(subtype(sbtyp))
          .push_back({detail::copy_c_str(nm),
                      sizeof...(Args) - 1,
                      detail::params_c_str(sizeof...(Args) - 1),
                      (GVarFunc) func,
                      detail::copy_c_str(flnm + ":Func" + sbtyp + "::" + nm)});
    }

    template <typename... Args>
    void add_method_to_install(std::string_view                     flnm,
                               std::string_view                     nm,
                               std::string_view                     info_string,
                               std::vector<std::string_view> const& filt_list,
                               Obj (*func)(Args...)) {
      static_assert(sizeof...(Args) <= 7, "length of Args must be at most 7");
      if (filt_list.size() + 1 != sizeof...(Args)) {
        std::cout << "Something wrong expected " << filt_list.size() + 1
                  << " arguments, found " << sizeof...(Args) << std::endl;
      }

      MethodToInstall mti;
      mti.name        = nm;
      mti.info_string = info_string;
      mti.filt_list   = filt_list;

      std::string cookie_name = std::string(flnm) + ":Func";
      cookie_name += nm;
      mti.func = {detail::copy_c_str(nm),
                  sizeof...(Args) - 1,
                  detail::params_c_str(sizeof...(Args) - 1),
                  (GVarFunc) func,
                  detail::copy_c_str(cookie_name)};
      _methods_to_install.push_back(std::move(mti));
    }

    // TODO to cpp file
    void add_category_to_declare(std::string_view name,
                                 std::string_view parent) {
      CategoryToDeclare ctd;
      ctd.name   = name;
      ctd.parent = parent;
      _categories_to_declare.push_back(std::move(ctd));
    }

    // TODO to cpp file
    void add_operation_to_declare(std::string_view              name,
                                  std::vector<std::string_view> filt_list) {
      OperationToDeclare otd;
      otd.name      = name;
      otd.filt_list = filt_list;
      _operations_to_declare.push_back(std::move(otd));
    }

    // TODO to cpp file
    void add_attribute_to_declare(std::string_view name,
                                  std::string_view filt) {
      _attributes_to_declare.emplace_back(name, filt);
    }

    void add_property_to_declare(std::string_view name, std::string_view filt) {
      _properties_to_declare.emplace_back(name, filt);
    }

    auto const& categories_to_declare() const {
      return _categories_to_declare;
    }

    auto const& operations_to_declare() const {
      return _operations_to_declare;
    }

    auto const& attributes_to_declare() const {
      return _attributes_to_declare;
    }

    auto const& properties_to_declare() const {
      return _properties_to_declare;
    }

    auto const& tnums_to_register() const {
      return _tnums_to_register;
    }

    auto const& methods_to_install() const {
      return _methods_to_install;
    }

    void finalize();

    // TODO remove
    std::vector<detail::SubtypeBase*>::const_iterator begin() const noexcept {
      return _subtypes.cbegin();
    }

    // TODO remove
    std::vector<detail::SubtypeBase*>::const_iterator end() const noexcept {
      return _subtypes.cend();
    }
  };

  ////////////////////////////////////////////////////////////////////////
  // to_cpp/gap - for gapbind14 gap objects
  ////////////////////////////////////////////////////////////////////////

  // Forward decl
  template <typename T, typename>
  struct to_cpp;

  template <typename T>
  struct to_cpp<T, std::enable_if_t<IsGapBind14Type<T>::value>> {
    using cpp_type = std::decay_t<T>;

    std::decay_t<T>& operator()(Obj o) const {
      // detail::require_gapbind14_obj(o);
      return *detail::obj_cpp_ptr<std::decay_t<T>>(o);
    }
  };

  template <typename T>
  struct to_gap<T, std::enable_if_t<IsGapBind14Type<T>::value>> {
    using cpp_type = T;

    Obj operator()(T const& obj) const {
      return to_gap<T*>()(new T(obj));
    }
  };

  template <typename T>
  struct to_gap<T*, std::enable_if_t<IsGapBind14Type<T>::value>> {
    using cpp_type = T;

    Obj operator()(T* ptr) const {
      Obj o          = NewBag(TNums(IsGapBind14Type<T>::name), 2 * sizeof(Obj));
      ADDR_OBJ(o)[0] = reinterpret_cast<Obj>(module().subtype<T>());
      ADDR_OBJ(o)[1] = reinterpret_cast<Obj>(ptr);
      CHANGED_BAG(o);
      return o;
    }
  };

  ////////////////////////////////////////////////////////////////////////
  // DeclareOperation etc
  ////////////////////////////////////////////////////////////////////////

  template <typename... Args>
  struct init {};

  namespace detail {
    template <typename T, typename... Args>
    T* make(Args... params) {
      return new T(std::forward<Args>(params)...);
    }

  }  // namespace detail

  template <typename Wild>
  static void InstallGlobalFunction(char const* name, Wild f) {
    size_t const n = detail::all_wilds<Wild>().size();
    detail::all_wilds<Wild>().push_back(f);
    module().add_func(
        __FILE__,
        name,
        detail::get_tame<decltype(&detail::tame<0, Wild>), Wild>(n));
  }

  void DeclareCategory(std::string_view name, std::string_view parent_category);

  void
  DeclareOperation(std::string_view                               name,
                   std::initializer_list<std::string_view> const& filt_list);

  void DeclareProperty(std::string_view name, std::string_view filt);

  template <typename Wild, typename... Args>
  static inline auto
  InstallMethod(std::string_view                               name,
                std::string_view                               info_string,
                std::initializer_list<std::string_view> const& filt_list,
                Wild                                           f)
      -> std::enable_if_t<std::is_member_function_pointer<Wild>::value> {
    LibraryGVar(name);
    LibraryGVar(filt_list);
    size_t const n = detail::all_wild_mem_fns<Wild>().size();
    detail::all_wild_mem_fns<Wild>().push_back(f);
    module().add_method_to_install(
        __FILE__,
        name,
        info_string,
        filt_list,
        detail::get_tame_mem_fn<decltype(&detail::tame_mem_fn<0, Wild>), Wild>(
            n));
  }

  template <typename Wild, typename... Args>
  static inline auto
  InstallMethod(std::string_view                               name,
                std::string_view                               info_string,
                std::initializer_list<std::string_view> const& filt_list,
                Wild                                           f)
      -> std::enable_if_t<!std::is_member_function_pointer<Wild>::value> {
    LibraryGVar(name);
    LibraryGVar(filt_list);

    size_t const n = detail::all_wilds<Wild>().size();
    detail::all_wilds<Wild>().push_back(f);
    module().add_method_to_install(
        __FILE__,
        name,
        info_string,
        filt_list,
        detail::get_tame<decltype(&detail::tame<0, Wild>), Wild>(n));
  }

  template <typename Thing, typename... Args>
  static inline void
  InstallMethod(std::string_view                               name,
                std::string_view                               info_string,
                std::initializer_list<std::string_view> const& filt_list,
                init<Thing, Args...>) {
    return InstallMethod(
        name, info_string, filt_list, &detail::make<Thing, Args...>);
  }

  ////////////////////////////////////////////////////////////////////////
  //
  ////////////////////////////////////////////////////////////////////////

  // TODO this should be a function
  template <typename T>
  void class_(std::string_view name) {
    module().add_subtype<T>(std::string(name));
  }

  template <typename T>
  Obj make_iterator(T first, T last) {
    size_t N      = std::distance(first, last);
    Obj    result = NEW_PLIST((N == 0 ? T_PLIST_EMPTY : T_PLIST_HOM), N);
    SET_LEN_PLIST(result, N);
    size_t i = 1;
    for (auto it = first; it != last; ++it) {
      AssPlist(result,
               i++,
               to_gap<typename std::iterator_traits<T>::value_type>()(*it));
    }
    return result;
  }

}  // namespace gapbind14

#endif  // INCLUDE_GAPBIND14_GAPBIND14_HPP_
