//
// Semigroups package for GAP
// Copyright (C) 2016-2023 James D. Mitchell
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

// This file contains everything in the kernel module for the Semigroups
// package that involves GAP directly, i.e. importing functions/variables from
// GAP and declaring functions for GAP etc.

#include "pkg.hpp"

#include <cstddef>  // for size_t
#include <vector>   // for vector

// GAP headers
#include "compiled.h"

// Semigroups package for GAP headers
#include "bipart.hpp"  // for Blocks, Bipartition
#include "cong.hpp"    // for init_cong
#include "conglatt.hpp"
#include "froidure-pin-fallback.hpp"  // for RUN_FROIDURE_PIN
#include "froidure-pin.hpp"           // for init_froidure_pin
#include "semigroups-debug.hpp"       // for SEMIGROUPS_ASSERT
#include "to_cpp.hpp"                 // for to_cpp
#include "to_gap.hpp"                 // for to_gap
#include "words.hpp"                  // for init_words

// Gapbind14 headers
#include "gapbind14/cpp_fn.hpp"     // for overload_cast
#include "gapbind14/gapbind14.hpp"  // for class_, InstallGlobalFunction

// libsemigroups headers
#include "libsemigroups/bipart.hpp"    // for Blocks, Bipartition
#include "libsemigroups/freeband.hpp"  // for freeband_equal_to
#include "libsemigroups/todd-coxeter.hpp"  // for ToddCoxeter, ToddCoxeter::table_type
#include "libsemigroups/types.hpp"         // for word_type, letter_type

#include "libsemigroups/detail/report.hpp"  // for REPORTER, Reporter

using libsemigroups::Bipartition;
using libsemigroups::Blocks;

// using libsemigroups::Hash;
// using libsemigroups::detail::Duf;

namespace {
  void LIBSEMIGROUPS_REPORTING_ENABLED(bool const val) {
    static std::unique_ptr<libsemigroups::ReportGuard> rg;
    if (val) {
      if (rg != nullptr) {
        rg = std::make_unique<libsemigroups::ReportGuard>(val);
      }
    } else {
      rg = nullptr;
    }
  }
}  // namespace

namespace gapbind14 {
  //   template <>
  //   struct
  //   IsGapBind14Type<libsemigroups::Presentation<libsemigroups::word_type>>
  //       : std::true_type {};
  //
  //   template <>
  //   struct IsGapBind14Type<libsemigroups::Sims1> : std::true_type {};
  //
  //   template <>
  //   struct IsGapBind14Type<typename libsemigroups::Sims1::iterator>
  //       : std::true_type {};
  //
  //   template <>
  //   struct IsGapBind14Type<libsemigroups::RepOrc> : std::true_type {};
}

GAPBIND14_MODULE(libsemigroups) {
  gapbind14::DeclareCategory("IsRangeObj", "IsObject");
  ////////////////////////////////////////////////////////////////////////
  // Free functions
  ////////////////////////////////////////////////////////////////////////

  gapbind14::InstallGlobalFunction("LIBSEMIGROUPS_REPORTING_ENABLED",
                                   &LIBSEMIGROUPS_REPORTING_ENABLED);

  gapbind14::InstallGlobalFunction("should_report",
                                   &libsemigroups::reporting_enabled);
  gapbind14::InstallGlobalFunction("hardware_concurrency",
                                   &std::thread::hardware_concurrency);
  gapbind14::InstallGlobalFunction(
      "freeband_equal_to",
      gapbind14::overload_cast<libsemigroups::word_type,
                               libsemigroups::word_type>(
          &libsemigroups::freeband_equal_to<libsemigroups::word_type>));

  gapbind14::InstallGlobalFunction("LATTICE_OF_CONGRUENCES",
                                   &semigroups::LATTICE_OF_CONGRUENCES);

  ////////////////////////////////////////////////////////////////////////
  // Initialise from other cpp files
  ////////////////////////////////////////////////////////////////////////

  init_froidure_pin_base(gapbind14::module());
  init_froidure_pin_bipart(gapbind14::module());
  init_froidure_pin_bmat(gapbind14::module());
  init_froidure_pin_matrix(gapbind14::module());
  init_froidure_pin_max_plus_mat(gapbind14::module());
  init_froidure_pin_min_plus_mat(gapbind14::module());
  init_froidure_pin_pperm(gapbind14::module());
  init_froidure_pin_pbr(gapbind14::module());
  init_froidure_pin_transf(gapbind14::module());
  init_cong(gapbind14::module());

  init_words(gapbind14::module());

  ////////////////////////////////////////////////////////////////////////
  // ToddCoxeter
  ////////////////////////////////////////////////////////////////////////

  using libsemigroups::congruence_kind;
  using libsemigroups::ToddCoxeter;
  using libsemigroups::word_type;
  /*using table_type = libsemigroups::congruence::ToddCoxeter::table_type;

  gapbind14::class_<ToddCoxeter>("ToddCoxeter")
      .def(gapbind14::init<congruence_kind>{})
      .def("set_number_of_generators", &ToddCoxeter::set_number_of_generators)
      .def("number_of_generators", &ToddCoxeter::number_of_generators)
      .def("prefill",
           gapbind14::overload_cast<table_type
  const&>(&ToddCoxeter::prefill));
*/
  // using libsemigroups::Presentation;

  // gapbind14::class_<Presentation<word_type>>("Presentation")
  //     .def(gapbind14::init<>{}, "make")
  //     .def("alphabet",
  //          gapbind14::overload_cast<>(&Presentation<word_type>::alphabet))
  //     .def("set_alphabet",
  //          [](Presentation<word_type>& thing, word_type val) -> void {
  //            thing.alphabet(val);
  //          })
  //     .def("alphabet_from_rules",
  //          [](Presentation<word_type>& thing) -> void {
  //            thing.alphabet_from_rules();
  //          })
  //     .def("contains_empty_word",
  //          [](Presentation<word_type>& thing, bool val) -> void {
  //            thing.contains_empty_word(val);
  //          })
  //     .def("validate", &Presentation<word_type>::validate)
  //     .def("number_of_rules",
  //          [](Presentation<word_type> const& thing) -> size_t {
  //            return thing.rules.size();
  //          });

  // gapbind14::InstallGlobalFunction(
  //     "presentation_add_rule",
  //     gapbind14::overload_cast<Presentation<word_type>&,
  //                              word_type const&,
  //                              word_type const&>(
  //         &libsemigroups::presentation::add_rule<word_type>));

  /*  using libsemigroups::Sims1;

    gapbind14::class_<Sims1::iterator>("Sims1Iterator")
        .def("increment", [](Sims1::iterator& it) { ++it; })
        .def("deref", [](Sims1::iterator const& it) { return *it; });

    gapbind14::class_<Sims1>("Sims1")
        .def(gapbind14::init<congruence_kind>{}, "make")
        .def("short_rules",
             [](Sims1& s, Presentation<word_type> const& p) {
  s.short_rules(p);
  }) .def("extra",
             [](Sims1& s, Presentation<word_type> const& p) { s.extra(p); })
        .def("number_of_threads",
             [](Sims1& s, size_t val) { s.number_of_threads(val); })
        .def("number_of_congruences", &Sims1::number_of_congruences)
        .def("cbegin", &Sims1::cbegin);

    using libsemigroups::RepOrc;

    gapbind14::class_<RepOrc>("RepOrc")
        .def(gapbind14::init<>{}, "make")
        .def("short_rules",
             [](RepOrc& ro, Presentation<word_type> const& p) {
               ro.short_rules(p);
             })
        .def("number_of_threads",
             [](RepOrc& ro, size_t val) { ro.number_of_threads(val); })
        .def("max_nodes", [](RepOrc& ro, size_t val) { ro.max_nodes(val); })
        .def("min_nodes", [](RepOrc& ro, size_t val) { ro.min_nodes(val); })
        .def("target_size", [](RepOrc& ro, size_t val) { ro.target_size(val);
  }) .def("get_target_size", [](RepOrc& ro) { return ro.target_size(); })
        .def("digraph", &RepOrc::digraph<uint32_t>);
        */
}

////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////

Obj SEMIGROUPS;

Obj TheTypeTBlocksObj;

Obj TYPE_BIPART;   // function
Obj TYPES_BIPART;  // plist

UInt T_BIPART = 0;
UInt T_BLOCKS = 0;

Obj TBipartObjCopyFunc(Obj o, Int mut) {
  // Bipartition objects are mathematically immutable, so
  // we don't need to do anything,
  return o;
}

Obj TBlocksObjCopyFunc(Obj o, Int mut) {
  // Blocks objects are mathematically immutable, so we don't need to do
  // anything,
  return o;
}

void TBipartObjCleanFunc(Obj o) {}

void TBlocksObjCleanFunc(Obj o) {}

void TBipartObjFreeFunc(Obj o) {
  SEMIGROUPS_ASSERT(TNUM_OBJ(o) == T_BIPART);
  delete bipart_get_cpp(o);
}

void TBlocksObjFreeFunc(Obj o) {
  SEMIGROUPS_ASSERT(TNUM_OBJ(o) == T_BLOCKS);
  delete blocks_get_cpp(o);
}

Obj TBipartObjTypeFunc(Obj o) {
  return ELM_PLIST(TYPES_BIPART, bipart_get_cpp(o)->degree() + 1);
}

Obj TBlocksObjTypeFunc(Obj o) {
  return TheTypeTBlocksObj;
}

void TBipartObjSaveFunc(Obj o) {
  Bipartition* b = bipart_get_cpp(o);
  SaveUInt4(b->degree());
  for (auto it = b->cbegin(); it < b->cend(); it++) {
    SaveUInt4(*it);
  }
}

void TBipartObjLoadFunc(Obj o) {
  UInt4                 deg = LoadUInt4();
  std::vector<uint32_t> blocks;
  blocks.reserve(2 * deg);

  for (size_t i = 0; i < 2 * deg; i++) {
    blocks.push_back(LoadUInt4());
  }
  ADDR_OBJ(o)[0] = reinterpret_cast<Obj>(new Bipartition(blocks));
  SEMIGROUPS_ASSERT(ADDR_OBJ(o)[1] == NULL && ADDR_OBJ(o)[2] == NULL);
}

void TBlocksObjSaveFunc(Obj o) {
  Blocks* b = blocks_get_cpp(o);
  SaveUInt4(b->degree());
  if (b->degree() != 0) {
    SaveUInt4(b->number_of_blocks());
    for (auto it = b->cbegin(); it < b->cend(); it++) {
      SaveUInt4(*it);
    }
    for (auto it = b->cbegin_lookup(); it < b->cend_lookup(); it++) {
      SaveUInt1(static_cast<UInt1>(*it));
    }
  }
}

void TBlocksObjLoadFunc(Obj o) {
  UInt4 deg = LoadUInt4();
  if (deg == 0) {
    ADDR_OBJ(o)[0] = reinterpret_cast<Obj>(new Blocks());
    return;
  }
  UInt4 nr_blocks = LoadUInt4();

  Blocks* blocks = new Blocks(deg);

  for (size_t i = 0; i < deg; i++) {
    blocks->set_block(i, LoadUInt4());
  }
  for (size_t i = 0; i < nr_blocks; i++) {
    blocks->set_is_transverse_block(i, static_cast<bool>(LoadUInt1()));
  }
#ifdef SEMIGROUPS_KERNEL_DEBUG
  libsemigroups::validate(*blocks);
#endif
  ADDR_OBJ(o)[0] = reinterpret_cast<Obj>(blocks);
}

// Filters for IS_BIPART, IS_BLOCKS

Obj IsBipartFilt;

Obj IsBipartHandler(Obj self, Obj val) {
  if (TNUM_OBJ(val) == T_BIPART) {
    return True;
  } else if (TNUM_OBJ(val) < FIRST_EXTERNAL_TNUM) {
    return False;
  } else {
    return DoFilter(self, val);
  }
}

Obj IsBlocksFilt;

Obj IsBlocksHandler(Obj self, Obj val) {
  if (TNUM_OBJ(val) == T_BLOCKS) {
    return True;
  } else if (TNUM_OBJ(val) < FIRST_EXTERNAL_TNUM) {
    return False;
  } else {
    return DoFilter(self, val);
  }
}

// Imported types and functions from the library, defined below

Obj HTValue;
Obj HTAdd;
Obj Pinfinity;
Obj Ninfinity;
Obj IsInfinity;
Obj IsNegInfinity;
Obj IsBooleanMat;
Obj BooleanMatType;
Obj IsMaxPlusMatrix;
Obj MaxPlusMatrixType;
Obj IsMinPlusMatrix;
Obj MinPlusMatrixType;
Obj IsTropicalMinPlusMatrix;
Obj TropicalMinPlusMatrixType;
Obj IsTropicalMaxPlusMatrix;
Obj TropicalMaxPlusMatrixType;
Obj IsProjectiveMaxPlusMatrix;
Obj ProjectiveMaxPlusMatrixType;
Obj IsNTPMatrix;
Obj NTPMatrixType;
Obj IntegerMatrixType;
Obj IsPBR;
Obj TYPES_PBR;
Obj TYPE_PBR;
Obj DegreeOfPBR;
Obj LARGEST_MOVED_PT_TRANS;

Obj IsSemigroup;
Obj IsMatrixObj;
Obj BaseDomain;
Obj Matrix;
Obj Integers;
Obj NrRows;

/*****************************************************************************
 *V  GVarFilts . . . . . . . . . . . . . . . . . . . list of filters to export
 */

#if defined(GAP_KERNEL_MAJOR_VERSION) && (GAP_KERNEL_MAJOR_VERSION >= 2)
typedef Obj (*GVarFilt)(Obj, Obj);
#else
typedef Obj (*GVarFilt)(/*arguments*/);
#endif

static StructGVarFilt GVarFilts[] = {
    {"IS_BIPART",
     "obj",
     &IsBipartFilt,
     (GVarFilt) IsBipartHandler,
     "pkg.cpp:IS_BIPART"},

    {"IS_BLOCKS",
     "obj",
     &IsBlocksFilt,
     (GVarFilt) IsBlocksHandler,
     "pkg.cpp:IS_BLOCKS"},

    {0, 0, 0, 0, 0} /* Finish with an empty entry */
};

/*****************************************************************************/

typedef Obj (*GVarFunc)(/*arguments*/);

#define GVAR_ENTRY(srcfile, name, nparam, params) \
  { #name, nparam, params, (GVarFunc) name, srcfile ":Func" #name }

// Table of functions to export

static StructGVarFunc GVarFuncs[] = {
    GVAR_ENTRY("froidure-pin-fallback.cpp",
               SCC_UNION_LEFT_RIGHT_CAYLEY_GRAPHS,
               2,
               "scc1, scc2"),
    GVAR_ENTRY("froidure-pin-fallback.cpp", FIND_HCLASSES, 2, "left, right"),
    GVAR_ENTRY("froidure-pin-fallback.cpp",
               RUN_FROIDURE_PIN,
               3,
               "obj, limit, report"),

    GVAR_ENTRY("bipart.cpp", BIPART_NC, 1, "list"),
    GVAR_ENTRY("bipart.cpp", BIPART_EXT_REP, 1, "x"),
    GVAR_ENTRY("bipart.cpp", BIPART_INT_REP, 1, "x"),
    GVAR_ENTRY("bipart.cpp", BIPART_HASH, 2, "x, data"),
    GVAR_ENTRY("bipart.cpp", BIPART_DEGREE, 1, "x"),
    GVAR_ENTRY("bipart.cpp", BIPART_RANK, 2, "x, nothing"),
    GVAR_ENTRY("bipart.cpp", BIPART_NR_BLOCKS, 1, "x"),
    GVAR_ENTRY("bipart.cpp", BIPART_NR_LEFT_BLOCKS, 1, "x"),
    GVAR_ENTRY("bipart.cpp", BIPART_PERM_LEFT_QUO, 2, "x, y"),
    GVAR_ENTRY("bipart.cpp", BIPART_LEFT_PROJ, 1, "x"),
    GVAR_ENTRY("bipart.cpp", BIPART_RIGHT_PROJ, 1, "x"),
    GVAR_ENTRY("bipart.cpp", BIPART_STAR, 1, "x"),
    GVAR_ENTRY("bipart.cpp", BIPART_LAMBDA_CONJ, 2, "x, y"),
    GVAR_ENTRY("bipart.cpp", BIPART_STAB_ACTION, 2, "x, p"),
    GVAR_ENTRY("bipart.cpp", BIPART_LEFT_BLOCKS, 1, "x"),
    GVAR_ENTRY("bipart.cpp", BIPART_RIGHT_BLOCKS, 1, "x"),
    GVAR_ENTRY("bipart.cpp", BLOCKS_NC, 1, "blocks"),
    GVAR_ENTRY("bipart.cpp", BLOCKS_EXT_REP, 1, "blocks"),
    GVAR_ENTRY("bipart.cpp", BLOCKS_DEGREE, 1, "blocks"),
    GVAR_ENTRY("bipart.cpp", BLOCKS_RANK, 1, "blocks"),
    GVAR_ENTRY("bipart.cpp", BLOCKS_NR_BLOCKS, 1, "blocks"),
    GVAR_ENTRY("bipart.cpp", BLOCKS_HASH, 2, "blocks, data"),
    GVAR_ENTRY("bipart.cpp", BLOCKS_PROJ, 1, "blocks"),
    GVAR_ENTRY("bipart.cpp", BLOCKS_EQ, 2, "blocks1, blocks2"),
    GVAR_ENTRY("bipart.cpp", BLOCKS_LT, 2, "blocks1, blocks2"),
    GVAR_ENTRY("bipart.cpp", BLOCKS_E_TESTER, 2, "left, right"),
    GVAR_ENTRY("bipart.cpp", BLOCKS_E_CREATOR, 2, "left, right"),
    GVAR_ENTRY("bipart.cpp", BLOCKS_LEFT_ACT, 2, "blocks, x"),
    GVAR_ENTRY("bipart.cpp", BLOCKS_RIGHT_ACT, 2, "blocks, x"),
    GVAR_ENTRY("bipart.cpp", BLOCKS_INV_LEFT, 2, "blocks, x"),
    GVAR_ENTRY("bipart.cpp", BLOCKS_INV_RIGHT, 2, "blocks, x"),
    GVAR_ENTRY("bipart.cpp",
               BIPART_NR_IDEMPOTENTS,
               4,
               "o, scc, lookup, nr_threads"),

    {0, 0, 0, 0, 0} /* Finish with an empty entry */
};

/******************************************************************************
 *F  InitKernel( <module> )  . . . . . . . . initialise kernel data structures
 */
static Int InitKernel(StructInitInfo* module) {
  gapbind14::init_kernel("libsemigroups");

  /* init filters and functions */
  InitHdlrFiltsFromTable(GVarFilts);
  InitHdlrFuncsFromTable(GVarFuncs);

  ImportGVarFromLibrary("SEMIGROUPS", &SEMIGROUPS);

  // T_BIPART
  T_BIPART = RegisterPackageTNUM("bipartition", TBipartObjTypeFunc);

  CopyObjFuncs[T_BIPART]      = &TBipartObjCopyFunc;
  CleanObjFuncs[T_BIPART]     = &TBipartObjCleanFunc;
  IsMutableObjFuncs[T_BIPART] = &AlwaysNo;

  SaveObjFuncs[T_BIPART] = TBipartObjSaveFunc;
  LoadObjFuncs[T_BIPART] = TBipartObjLoadFunc;

  InitMarkFuncBags(T_BIPART, &MarkAllButFirstSubBags);
  InitFreeFuncBag(T_BIPART, &TBipartObjFreeFunc);

  ProdFuncs[T_BIPART][T_BIPART] = BIPART_PROD;
  EqFuncs[T_BIPART][T_BIPART]   = BIPART_EQ;
  LtFuncs[T_BIPART][T_BIPART]   = BIPART_LT;

  ImportGVarFromLibrary("TYPE_BIPART", &TYPE_BIPART);
  ImportGVarFromLibrary("TYPES_BIPART", &TYPES_BIPART);

  // T_BLOCKS
  T_BLOCKS = RegisterPackageTNUM("blocks", TBlocksObjTypeFunc);

  CopyObjFuncs[T_BLOCKS]      = &TBlocksObjCopyFunc;
  CleanObjFuncs[T_BLOCKS]     = &TBlocksObjCleanFunc;
  IsMutableObjFuncs[T_BLOCKS] = &AlwaysNo;

  SaveObjFuncs[T_BLOCKS] = TBlocksObjSaveFunc;
  LoadObjFuncs[T_BLOCKS] = TBlocksObjLoadFunc;

  InitMarkFuncBags(T_BLOCKS, &MarkNoSubBags);
  InitFreeFuncBag(T_BLOCKS, &TBlocksObjFreeFunc);

  EqFuncs[T_BLOCKS][T_BLOCKS] = BLOCKS_EQ;
  LtFuncs[T_BLOCKS][T_BLOCKS] = BLOCKS_LT;

  InitCopyGVar("TheTypeTBlocksObj", &TheTypeTBlocksObj);

  // Import things from the library

  ImportGVarFromLibrary("HTValue", &HTValue);
  ImportGVarFromLibrary("HTAdd", &HTAdd);

  ImportGVarFromLibrary("infinity", &Pinfinity);
  ImportGVarFromLibrary("Ninfinity", &Ninfinity);

  ImportGVarFromLibrary("IsInfinity", &IsInfinity);
  ImportGVarFromLibrary("IsNegInfinity", &IsNegInfinity);

  ImportGVarFromLibrary("TYPES_PBR", &TYPES_PBR);
  ImportGVarFromLibrary("TYPE_PBR", &TYPE_PBR);

  ImportGVarFromLibrary("IsPBR", &IsPBR);
  ImportGVarFromLibrary("DegreeOfPBR", &DegreeOfPBR);

  ImportGVarFromLibrary("IsBooleanMat", &IsBooleanMat);
  ImportGVarFromLibrary("BooleanMatType", &BooleanMatType);

  ImportGVarFromLibrary("IsMaxPlusMatrix", &IsMaxPlusMatrix);
  ImportGVarFromLibrary("MaxPlusMatrixType", &MaxPlusMatrixType);

  ImportGVarFromLibrary("IsMinPlusMatrix", &IsMinPlusMatrix);
  ImportGVarFromLibrary("MinPlusMatrixType", &MinPlusMatrixType);

  ImportGVarFromLibrary("IsTropicalMaxPlusMatrix", &IsTropicalMaxPlusMatrix);
  ImportGVarFromLibrary("TropicalMaxPlusMatrixType",
                        &TropicalMaxPlusMatrixType);

  ImportGVarFromLibrary("IsTropicalMinPlusMatrix", &IsTropicalMinPlusMatrix);
  ImportGVarFromLibrary("TropicalMinPlusMatrixType",
                        &TropicalMinPlusMatrixType);

  ImportGVarFromLibrary("IsProjectiveMaxPlusMatrix",
                        &IsProjectiveMaxPlusMatrix);
  ImportGVarFromLibrary("ProjectiveMaxPlusMatrixType",
                        &ProjectiveMaxPlusMatrixType);

  ImportGVarFromLibrary("IsNTPMatrix", &IsNTPMatrix);
  ImportGVarFromLibrary("NTPMatrixType", &NTPMatrixType);

  ImportGVarFromLibrary("IntegerMatrixType", &IntegerMatrixType);

  ImportGVarFromLibrary("LARGEST_MOVED_PT_TRANS", &LARGEST_MOVED_PT_TRANS);

  ImportGVarFromLibrary("IsSemigroup", &IsSemigroup);
  ImportGVarFromLibrary("IsMatrixObj", &IsMatrixObj);
  ImportGVarFromLibrary("BaseDomain", &BaseDomain);
  ImportGVarFromLibrary("Integers", &Integers);
  ImportGVarFromLibrary("NrRows", &NrRows);
  ImportGVarFromLibrary("Matrix", &Matrix);

  return 0;
}

static Int PostRestore(StructInitInfo* module) {
  LIBSEMIGROUPS_REPORTING_ENABLED(false);
  return 0;
}

static Int InitLibrary(StructInitInfo* module) {
  gapbind14::init_library("libsemigroups");
  InitGVarFiltsFromTable(GVarFilts);
  InitGVarFuncsFromTable(GVarFuncs);
#ifdef LIBSEMIGROUPS_HPCOMBI_ENABLED
  ExportAsConstantGVar(LIBSEMIGROUPS_HPCOMBI_ENABLED);
#endif
  return PostRestore(module);
}

/******************************************************************************
 *F  InitInfopl()  . . . . . . . . . . . . . . . . . table of init functions
 */
static StructInitInfo module = {/* type        = */ MODULE_DYNAMIC,
                                /* name        = */ "semigroups",
                                /* revision_c  = */ 0,
                                /* revision_h  = */ 0,
                                /* version     = */ 0,
                                /* crc         = */ 0,
                                /* initKernel  = */ InitKernel,
                                /* initLibrary = */ InitLibrary,
                                /* checkInit   = */ 0,
                                /* preSave     = */ 0,
                                /* postSave    = */ 0,
                                /* postRestore = */ PostRestore};

extern "C" StructInitInfo* Init__Dynamic(void) {
  return &module;
}
