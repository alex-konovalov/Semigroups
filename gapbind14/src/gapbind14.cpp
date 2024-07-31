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

#include "gapbind14/gapbind14.hpp"

#include <initializer_list>
#include <stdio.h>   // for fprintf, stderr
#include <string.h>  // for memcpy, strchr, strrchr

#include <iostream>

#include <unordered_set>  // for unordered_set, unordered_set<>::iterator

#include "gapbind14/gap_include.hpp"  // for Obj etc

#define GVAR_ENTRY(srcfile, name, nparam, params) \
  { #name, nparam, params, (GVarFunc) name, srcfile ":Func" #name }

typedef Obj (*GVarFunc)(/*arguments*/);

namespace gapbind14 {
  ////////////////////////////////////////////////////////////////////////
  // Helpers for interacting with GAP
  ////////////////////////////////////////////////////////////////////////

  Obj LibraryGVar_::operator()(std::string_view name) {
    auto [it, inserted] = _map.emplace(name, _GAP_LibraryGVars.size());
    if (inserted) {
      if (_imported) {
        std::string msg = "LibraryGVar: trying to access \"";
        msg += name;
        msg += "\" after GVars imported";
        throw std::runtime_error(msg);
      }
      _GAP_LibraryGVars.emplace_back();
      return _GAP_LibraryGVars.back();
    } else {
      return _GAP_LibraryGVars[it->second];
    }
  }

  void LibraryGVar_::import_all() {
    for (auto const &var : _map) {
      std::cout << "Importing GAP GVar " << var.first << " from library"
                << std::endl;
      ImportGVarFromLibrary(var.first.c_str(), &_GAP_LibraryGVars[var.second]);
    }
    _imported = true;
  }

  UInt &TNums_::operator()(std::string_view name) {
    auto [it, inserted] = _map.emplace(name, _GAP_TNums.size());
    if (inserted) {
      _GAP_TNums.emplace_back();
      return _GAP_TNums.back();
    } else {
      return _GAP_TNums[it->second];
    }
  }

  LibraryGVar_ LibraryGVar;
  TNums_       TNums;

  UInt T_GAPBIND14_OBJ = 0;

  namespace {

    std::unordered_map<std::string, void (*)()> &init_funcs() {
      static std::unordered_map<std::string, void (*)()> inits;
      return inits;
    }
  }  // namespace

  namespace detail {
    int emplace_init_func(char const *module_name, void (*func)()) {
      bool inserted = init_funcs().emplace(module_name, func).second;
      if (!inserted) {
        throw std::runtime_error(std::string("init function for module ")
                                 + module_name + " already inserted!");
      }
      return 0;
    }

    void require_gapbind14_obj(Obj o) {
      if (TNUM_OBJ(o) != T_GAPBIND14_OBJ) {
        ErrorQuit(
            "expected gapbind14 object but got %s!", (Int) TNAM_OBJ(o), 0L);
      }
      GAPBIND14_ASSERT(SIZE_OBJ(o) == 2);
    }

    gapbind14_subtype obj_subtype(Obj o) {
      // require_gapbind14_obj(o);
      return reinterpret_cast<gapbind14_subtype>(ADDR_OBJ(o)[0]);
    }

    char const *copy_c_str(std::string const &str) {
      char *out = new char[str.size() + 1];  // we need extra char for NUL
      memcpy(out, str.c_str(), str.size() + 1);
      return out;
    }

    char const *copy_c_str(std::string_view sv) {
      char *out = new char[sv.size() + 1];  // we need extra char for NUL
      memcpy(out, sv.begin(), sv.size() + 1);
      return out;
    }

    char const *params_c_str(size_t nr) {
      GAPBIND14_ASSERT(nr <= 6);
      if (nr == 0) {
        return "";
      }
      static std::string params = "arg1, arg2, arg3, arg4, arg5, arg6";
      std::string source(params.cbegin(), params.cbegin() + (nr - 1) * 6);
      source += std::string(params.cbegin() + (nr - 1) * 6,
                            params.cbegin() + (nr - 1) * 6 + 4);
      return copy_c_str(source);
    }

    // SubtypeBase implementations

    SubtypeBase::SubtypeBase(std::string nm, gapbind14_subtype sbtyp)
        : _name(nm), _subtype(sbtyp) {
      static std::unordered_set<gapbind14_subtype> defined;
      if (defined.find(sbtyp) != defined.end()) {
        throw std::runtime_error("SubtypeBase " + to_string(sbtyp)
                                 + " already registered!");
      } else {
        defined.insert(sbtyp);
      }
    }
  }  // namespace detail

  // Module implementations

  Module::~Module() {
    clear();
    for (auto *subtype : _subtypes) {
      delete subtype;
    }
  }

  void Module::clear() {
    for (auto &func : _funcs) {
      delete func.name;
      if (func.nargs != 0) {
        delete func.args;
      }
      delete func.cookie;
    }
    _funcs.clear();

    for (auto &vec : _mem_funcs) {
      for (auto &func : vec) {
        delete func.name;
        if (func.nargs != 0) {
          delete func.args;
        }
        delete func.cookie;
      }
      vec.clear();
    }
  }

  gapbind14_subtype Module::subtype(std::string const &subtype_name) const {
    auto it = _subtype_names.find(subtype_name);
    if (it == _subtype_names.end()) {
      throw std::runtime_error("No subtype named " + subtype_name);
    }
    return it->second;
  }
  void Module::load(Obj o) const {
    gapbind14_subtype sbtyp = LoadUInt();
    ADDR_OBJ(o)[0]          = reinterpret_cast<Obj>(sbtyp);
    ADDR_OBJ(o)[1]          = static_cast<Obj>(nullptr);
  }

  void Module::finalize() {
    for (auto &x : _mem_funcs) {
      x.push_back(StructGVarFunc({0, 0, 0, 0, 0}));
    }
    _funcs.push_back(StructGVarFunc({0, 0, 0, 0, 0}));
    _filts.push_back(StructGVarFilt({0, 0, 0, 0, 0}));
  }

  ////////////////////////////////////////////////////////////////////////
  // Declare user facing
  ////////////////////////////////////////////////////////////////////////

  void DeclareCategory(std::string_view name,
                       std::string_view parent_category) {
    module().add_category_to_declare(name, parent_category);
    LibraryGVar(name);
    LibraryGVar(parent_category);
  }

  void DeclareOperation(
      std::string_view                               name,
      std::initializer_list<std::string_view> const &filt_list) {
    LibraryGVar(name);
    LibraryGVar(filt_list);
    module().add_operation_to_declare(name, filt_list);
  }

  void DeclareProperty(std::string_view name, std::string_view filt) {
    LibraryGVar(name);
    LibraryGVar(filt);
    module().add_property_to_declare(name, filt);
  }

  namespace {

    Obj TheTypeTGapBind14Obj;

    ////////////////////////////////////////////////////////////////////////
    // Required kernel functions
    ////////////////////////////////////////////////////////////////////////

    Obj TGapBind14ObjTypeFunc(Obj o) {
      return TheTypeTGapBind14Obj;
    }

    void TGapBind14ObjPrintFunc(Obj o) {
      module().print(o);
    }

    void TGapBind14ObjSaveFunc(Obj o) {
      module().save(o);
    }

    void TGapBind14ObjLoadFunc(Obj o) {
      module().load(o);
    }

    Obj TGapBind14ObjCopyFunc(Obj o, Int mut) {
      return o;
    }

    void TGapBind14ObjCleanFunc(Obj o) {}

    void TGapBind14ObjFreeFunc(Obj o) {
      module().free(o);
    }

    ////////////////////////////////////////////////////////////////////////
    // Copied from gap/src/modules.c, should be exposed in header TODO(later)
    ////////////////////////////////////////////////////////////////////////

    static Obj ValidatedArgList(const char *name,
                                int         nargs,
                                const char *argStr) {
      Obj args = ArgStringToList(argStr);
      int len  = LEN_PLIST(args);
      if (nargs >= 0 && len != nargs)
        fprintf(stderr,
                "#W %s takes %d arguments, but argument string is '%s'"
                " which implies %d arguments\n",
                name,
                nargs,
                argStr,
                len);
      return args;
    }

    static void SetupFuncInfo(Obj func, const Char *cookie) {
      // The string <cookie> usually has the form "PATH/TO/FILE.c:FUNCNAME".
      // We check if that is the case, and if so, split it into the parts before
      // and after the colon. In addition, the file path is cut to only contain
      // the last two '/'-separated components.
      const Char *pos = strchr(cookie, ':');
      if (pos) {
        Obj location = MakeImmString(pos + 1);

        Obj  filename;
        char buffer[512];
        Int  len = 511 < (pos - cookie) ? 511 : pos - cookie;
        memcpy(buffer, cookie, len);
        buffer[len] = 0;

        Char *start = strrchr(buffer, '/');
        if (start) {
          while (start > buffer && *(start - 1) != '/')
            start--;
        } else {
          start = buffer;
        }
        filename = MakeImmString(start);

        Obj body_bag = NewBag(T_BODY, sizeof(BodyHeader));
        SET_FILENAME_BODY(body_bag, filename);
        SET_LOCATION_BODY(body_bag, location);
        SET_BODY_FUNC(func, body_bag);
        CHANGED_BAG(body_bag);
        CHANGED_BAG(func);
      }
    }

    // TODO renovate this
    Obj IsValidGapbind14Object(Obj self, Obj arg1) {
      // detail::require_gapbind14_obj(arg1);
      return (ADDR_OBJ(arg1)[1] != nullptr ? True : False);
    }

    // TODO(later) remove, use InstallGlobalFunction instead
    StructGVarFunc GVarFuncs[]
        = {GVAR_ENTRY("gapbind14.cpp", IsValidGapbind14Object, 1, "arg1"),
           {0, 0, 0, 0, 0}};
  }  // namespace

  Module &module() {
    static Module MODULE;
    return MODULE;
  }

  void init_kernel(char const *name) {
    // Things we want from the GAP library
    LibraryGVar("DeclareCategory");
    LibraryGVar("DeclareOperation");
    LibraryGVar("DeclareProperty");
    LibraryGVar("InstallMethod");
    LibraryGVar("InstallEarlyMethod");
    LibraryGVar("IsObject");

    static bool first_call = true;
    if (first_call) {
      first_call = false;
      InitHdlrFuncsFromTable(GVarFuncs);
      UInt &PKG_TNUM = T_GAPBIND14_OBJ;
      PKG_TNUM       = RegisterPackageTNUM("TGapBind14", TGapBind14ObjTypeFunc);

      PrintObjFuncs[PKG_TNUM] = TGapBind14ObjPrintFunc;
      SaveObjFuncs[PKG_TNUM]  = TGapBind14ObjSaveFunc;
      LoadObjFuncs[PKG_TNUM]  = TGapBind14ObjLoadFunc;

      CopyObjFuncs[PKG_TNUM]      = &TGapBind14ObjCopyFunc;
      CleanObjFuncs[PKG_TNUM]     = &TGapBind14ObjCleanFunc;
      IsMutableObjFuncs[PKG_TNUM] = &AlwaysNo;

      InitMarkFuncBags(PKG_TNUM, MarkNoSubBags);
      InitFreeFuncBag(PKG_TNUM, TGapBind14ObjFreeFunc);

      InitCopyGVar("TheTypeTGapBind14Obj", &TheTypeTGapBind14Obj);
    }

    auto it = init_funcs().find(std::string(name));
    if (it == init_funcs().end()) {
      throw std::runtime_error(std::string("No init function for module ")
                               + name + " found");
    }
    it->second();  // installs all functions in the current module.
    module().finalize();

    for (auto const &tntr : module().tnums_to_register()) {
      auto GAP_type_name = "The" + tntr.name + "Type";
      auto GAP_type      = LibraryGVar(GAP_type_name);
      std::cout << "Copying GVar " << GAP_type_name << std::endl;
      InitCopyGVar(GAP_type_name.c_str(), &GAP_type);
      UInt &GAP_tnum      = TNums(tntr.name);
      auto  GAP_tnum_name = "T_" + tntr.name + "_OBJ";
      Module::toupper(GAP_tnum_name);
      std::cout << "Registering TNUM " << GAP_tnum_name << std::endl;

      auto type_func = [GAP_type_name]() { return LibraryGVar(GAP_type_name); };
      using Wild     = decltype(type_func);
      size_t const n = detail::all_wilds<Wild>().size();
      detail::all_wilds<Wild>().push_back(type_func);
      GAP_tnum = RegisterPackageTNUM(
          detail::copy_c_str(GAP_tnum_name),
          detail::get_tame<decltype(&detail::tame<0, Wild>), Wild>(n));
      // TODO copy the other functions from above
      // TODO only install PrintObjFuncs if PrintObj is not one of the methods
      // installed for objects of this type.
      PrintObjFuncs[GAP_tnum] = TGapBind14ObjPrintFunc;
    }

    InitHdlrFuncsFromTable(module().funcs());
    InitHdlrFiltsFromTable(module().filters());

    for (auto ptr : module()) {
      InitHdlrFuncsFromTable(module().mem_funcs(ptr->name()));
    }
    LibraryGVar.import_all();
  }

  // TODO move and rename this
  std::vector<Obj> filter_list(std::vector<std::string_view> const &svs) {
    std::vector<Obj> filt_list;
    for (auto const &filt : svs) {
      filt_list.push_back(LibraryGVar(filt));
    }
    return filt_list;
  }

  void init_library(char const *name) {
    static bool first_call = true;
    if (first_call) {
      first_call = false;
      InitGVarFuncsFromTable(GVarFuncs);
    }

    InitGVarFuncsFromTable(module().funcs());
    InitGVarFiltsFromTable(module().filters());

    for (auto const &ctd : module().categories_to_declare()) {
      std::cout << "Declared category " << ctd.name << std::endl;
      CALL_2ARGS(LibraryGVar("DeclareCategory"),
                 to_gap<std::string>()(ctd.name),
                 LibraryGVar(ctd.parent));
    }

    for (auto const &otd : module().operations_to_declare()) {
      CALL_2ARGS(LibraryGVar("DeclareOperation"),
                 to_gap<std::string>()(otd.name),
                 to_gap<std::vector<Obj>>()(filter_list(otd.filt_list)));
      std::cout << "Declared operation " << otd.name << std::endl;
    }

    for (auto const &atd : module().properties_to_declare()) {
      CALL_2ARGS(LibraryGVar("DeclareProperty"),
                 to_gap<std::string>()(atd.name),
                 LibraryGVar(atd.filt));
      std::cout << "Declared property " << atd.name << std::endl;
    }

    size_t index = 0;
    for (auto const &mti : module().methods_to_install()) {
      Obj  GAP_op    = LibraryGVar(mti.name);
      auto filt_list = filter_list(mti.filt_list);
      // TODO must be an easier way of doing this, i.e. just add the global
      // function as elsewhere to GAP and then call install method using that
      UInt gvar = GVarName(mti.func.name);
      Obj  name = NameGVar(gvar);
      Obj args = ValidatedArgList(mti.func.name, mti.func.nargs, mti.func.args);
      Obj func = NewFunction(name, mti.func.nargs, args, mti.func.handler);
      SetupFuncInfo(func, mti.func.cookie);
      assert(mt.func.nargs == filt_list.size());

      CALL_4ARGS(LibraryGVar("InstallMethod"),
                 GAP_op,
                 // TODO deduction guides so that the template params aren't
                 // required
                 to_gap<std::string>()(mti.info_string),
                 to_gap<std::vector<Obj>>()(filt_list),
                 func);
      std::cout << "Installed method for " << mti.name << " with "
                << filt_list.size() << " args" << std::endl;
      index++;
    }
  }
}  // namespace gapbind14
