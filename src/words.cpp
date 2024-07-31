//
// Semigroups package for GAP
// Copyright (C) 2023 James D. Mitchell
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

// This file contains everything in the kernel module related to the file
// libsemigroups/include/words.hpp.

#include "words.hpp"

#include "to_cpp.hpp"
#include "to_gap.hpp"

#include "gapbind14/gapbind14.hpp"
#include "gapbind14/to_gap.hpp"

#include "libsemigroups/words.hpp"

namespace gapbind14 {
  using Words     = libsemigroups::Words;
  using Strings   = libsemigroups::Strings;
  using word_type = libsemigroups::word_type;
  using ToWord    = libsemigroups::ToWord;

  GAPBIND14_TYPE("Words", Words);
  GAPBIND14_TYPE("Strings", Strings);
  GAPBIND14_TYPE("ToWord", ToWord);

  void init_words(Module& m) {
    ////////////////////////////////////////////////////////////////////////
    // Global functions
    ////////////////////////////////////////////////////////////////////////

    InstallGlobalFunction("NumberOfWords", &libsemigroups::number_of_words);
    // There is already a RandomWord function in Semigroups
    // InstallGlobalFunction("RandomWord", &libsemigroups::random_word);
    InstallGlobalFunction(
        "ParseString",
        overload_cast<char const*>(&libsemigroups::literals::operator""_p));

    InstallGlobalFunction(
        "ToWordFunc", overload_cast<std::string_view>(&libsemigroups::to_word));

    InstallGlobalFunction(
        "ToStringFunc", [](std::string_view alphabet, word_type const& input) {
          return libsemigroups::to_string(alphabet, input);
        });

    ////////////////////////////////////////////////////////////////////////
    // Declarations for Words
    ////////////////////////////////////////////////////////////////////////

    class_<Words>("Words");

    DeclareCategory("IsWords", "IsRangeObj");

    // TODO maybe DeclareOperationKernel in some places?
    DeclareOperation("Words", {});
    DeclareOperation("Words", {"IsWords"});
    DeclareOperation("Init", {"IsWords"});
    DeclareOperation("Count", {"IsWords"});
    DeclareOperation("FirstWord", {"IsWords"});
    DeclareOperation("FirstWord", {"IsWords", "IsObject"});
    DeclareOperation("LastWord", {"IsWords"});
    DeclareOperation("LastWord", {"IsWords", "IsObject"});
    DeclareOperation("Get", {"IsWords"});
    DeclareOperation("Next", {"IsWords"});
    DeclareOperation("AtEnd", {"IsWords"});
    DeclareOperation("ReductionOrdering", {"IsWords"});
    DeclareOperation("ReductionOrdering", {"IsWords", "IsString"});
    DeclareOperation("UpperBound", {"IsWords"});
    DeclareOperation("UpperBound", {"IsWords", "IsInt"});
    DeclareOperation("MinimumWordLength", {"IsWords", "IsInt"});
    DeclareOperation("MaximumWordLength", {"IsWords", "IsInt"});

    DeclareOperation("NumberOfLetters", {"IsWords", "IsObject"});
    DeclareOperation("NumberOfLetters", {"IsWords"});

    ////////////////////////////////////////////////////////////////////////
    // Install methods for IsWords
    ////////////////////////////////////////////////////////////////////////

    InstallMethod("Words", "for no arguments", {}, init<Words>());
    InstallMethod("Words",
                  "for an IsWords object",
                  {"IsWords"},
                  init<Words, Words const&>());
    InstallMethod("Init", "for an IsWords object", {"IsWords"}, [](Words& w) {
      w.init();
    });

    InstallMethod("Count", "for an IsWords object", {"IsWords"}, &Words::count);

    InstallMethod("FirstWord",
                  "for an IsWords object",
                  {"IsWords"},
                  overload_cast<>(&Words::first));

    InstallMethod("FirstWord",
                  "for an IsWords object and word",
                  {"IsWords", "IsObject"},
                  // gapbind14 currently doesn't handle the reference returned
                  // by words.first(w) properly so we wrap it in a lambda
                  [](Words& words, word_type const& w) { words.first(w); });

    InstallMethod("LastWord",
                  "for an IsWords object",
                  {"IsWords"},
                  overload_cast<>(&Words::last));

    InstallMethod("LastWord",
                  "for an IsWords object and word",
                  {"IsWords", "IsObject"},
                  // gapbind14 currently doesn't handle the reference returned
                  // by words.first(w) properly so we wrap it in a lambda
                  [](Words& words, word_type const& w) { words.last(w); });

    InstallMethod("NumberOfLetters",
                  "for an IsWords object and a pos. int.",
                  {"IsWords", "IsObject"},
                  // gapbind14 currently doesn't handle the reference returned
                  // by words.first(w) properly so we wrap it in a lambda
                  [](Words& words, size_t n) { words.number_of_letters(n); });

    InstallMethod("Get", "for an IsWords object", {"IsWords"}, &Words::get);

    InstallMethod("Next", "for an IsWords object", {"IsWords"}, &Words::next);

    InstallMethod(
        "AtEnd", "for an IsWords object", {"IsWords"}, &Words::at_end);

    InstallMethod("ReductionOrdering",
                  "for an IsWords object",
                  {"IsWords"},
                  overload_cast<>(&Words::order));

    InstallMethod(
        "ReductionOrdering",
        "for an IsWords object and a string",
        {"IsWords", "IsString"},
        // gapbind14 currently doesn't handle the reference returned
        // by words.first(w) properly so we wrap it in a lambda
        [](Words& words, libsemigroups::Order val) { words.order(val); });

    InstallMethod(
        "ReductionOrdering",
        "for an IsWords object and a string",
        {"IsWords", "IsString"},
        // gapbind14 currently doesn't handle the reference returned
        // by words.first(w) properly so we wrap it in a lambda
        [](Words& words, libsemigroups::Order val) { words.order(val); });

    InstallMethod("UpperBound",
                  "for an IsWords object",
                  {"IsWords"},
                  overload_cast<>(&Words::upper_bound));

    InstallMethod("UpperBound",
                  "for an IsWords object and an int",
                  {"IsWords", "IsInt"},
                  // gapbind14 currently doesn't handle the reference returned
                  // by words.first(w) properly so we wrap it in a lambda
                  [](Words& words, size_t val) { words.upper_bound(val); });

    InstallMethod("MinimumWordLength",
                  "for an IsWords object and an int",
                  {"IsWords", "IsInt"},
                  // gapbind14 currently doesn't handle the reference returned
                  // by words.first(w) properly so we wrap it in a lambda
                  [](Words& words, size_t val) { words.min(val); });

    InstallMethod("MaximumWordLength",
                  "for an IsWords object and an int",
                  {"IsWords", "IsInt"},
                  // gapbind14 currently doesn't handle the reference returned
                  // by words.first(w) properly so we wrap it in a lambda
                  [](Words& words, size_t val) { words.max(val); });

    // Only works if PrintObjFuncs isn't installed later in
    // init_kernel InstallMethod("PrintObj",
    //                          "for an IsWords object XXX",
    //                          {"IsWords"},
    //                          [](Obj o) { Pr("bananas", 0L, 0L);
    //                          });

    ////////////////////////////////////////////////////////////////////////
    // Declarations for Strings
    ////////////////////////////////////////////////////////////////////////

    class_<Strings>("Strings");

    DeclareCategory("IsStrings", "IsRangeObj");

    DeclareOperation("Strings", {});
    DeclareOperation("Strings", {"IsStrings"});
    DeclareOperation("Init", {"IsStrings"});
    DeclareOperation("Count", {"IsStrings"});
    DeclareOperation("FirstWord", {"IsStrings"});
    DeclareOperation("FirstWord", {"IsStrings", "IsString"});
    DeclareOperation("LastWord", {"IsStrings"});
    DeclareOperation("LastWord", {"IsStrings", "IsString"});
    DeclareOperation("Get", {"IsStrings"});
    DeclareOperation("Next", {"IsStrings"});
    DeclareOperation("AtEnd", {"IsStrings"});
    DeclareOperation("ReductionOrdering", {"IsStrings"});
    DeclareOperation("ReductionOrdering", {"IsStrings", "IsString"});
    DeclareOperation("UpperBound", {"IsStrings"});
    DeclareOperation("UpperBound", {"IsStrings", "IsInt"});
    DeclareOperation("MinimumWordLength", {"IsStrings", "IsInt"});
    DeclareOperation("MaximumWordLength", {"IsStrings", "IsInt"});

    DeclareOperation("Alphabet", {"IsStrings", "IsString"});
    DeclareOperation("Alphabet", {"IsStrings"});

    ////////////////////////////////////////////////////////////////////////
    // Install methods for Strings
    ////////////////////////////////////////////////////////////////////////

    InstallMethod("Strings", "for no arguments", {}, init<Strings>());
    InstallMethod("Strings",
                  "for an IsStrings object",
                  {"IsStrings"},
                  init<Strings, Strings const&>());
    InstallMethod("Init",
                  "for an IsStrings object",
                  {"IsStrings"},
                  [](Strings& w) { w.init(); });

    InstallMethod(
        "Count", "for an IsStrings object", {"IsStrings"}, &Strings::count);

    InstallMethod("FirstWord",
                  "for an IsStrings object",
                  {"IsStrings"},
                  overload_cast<>(&Strings::first));

    InstallMethod(
        "FirstWord",
        "for an IsStrings object and word",
        {"IsStrings", "IsString"},
        // gapbind14 currently doesn't handle the reference returned
        // by strings.first(w) properly so we wrap it in a lambda
        [](Strings& strings, std::string const& w) { strings.first(w); });

    InstallMethod("LastWord",
                  "for an IsStrings object",
                  {"IsStrings"},
                  overload_cast<>(&Strings::last));

    InstallMethod(
        "LastWord",
        "for an IsStrings object and a string",
        {"IsStrings", "IsString"},
        // gapbind14 currently doesn't handle the reference returned
        // by strings.first(w) properly so we wrap it in a lambda
        [](Strings& strings, std::string const& w) { strings.last(w); });

    InstallMethod(
        "Get", "for an IsStrings object", {"IsStrings"}, &Strings::get);

    InstallMethod(
        "Next", "for an IsStrings object", {"IsStrings"}, &Strings::next);

    InstallMethod(
        "AtEnd", "for an IsStrings object", {"IsStrings"}, &Strings::at_end);

    InstallMethod("ReductionOrdering",
                  "for an IsStrings object",
                  {"IsStrings"},
                  overload_cast<>(&Strings::order));

    InstallMethod(
        "ReductionOrdering",
        "for an IsStrings object and a string",
        {"IsStrings", "IsString"},
        // gapbind14 currently doesn't handle the reference returned
        // by strings.first(w) properly so we wrap it in a lambda
        [](Strings& strings, libsemigroups::Order val) { strings.order(val); });

    InstallMethod(
        "ReductionOrdering",
        "for an IsStrings object and a string",
        {"IsStrings", "IsString"},
        // gapbind14 currently doesn't handle the reference returned
        // by strings.first(w) properly so we wrap it in a lambda
        [](Strings& strings, libsemigroups::Order val) { strings.order(val); });

    InstallMethod("UpperBound",
                  "for an IsStrings object",
                  {"IsStrings"},
                  overload_cast<>(&Strings::upper_bound));

    InstallMethod(
        "UpperBound",
        "for an IsStrings object and an int",
        {"IsStrings", "IsInt"},
        // gapbind14 currently doesn't handle the reference returned
        // by strings.first(w) properly so we wrap it in a lambda
        [](Strings& strings, size_t val) { strings.upper_bound(val); });

    InstallMethod("MinimumWordLength",
                  "for an IsStrings object and an int",
                  {"IsStrings", "IsInt"},
                  // gapbind14 currently doesn't handle the reference returned
                  // by strings.first(w) properly so we wrap it in a lambda
                  [](Strings& strings, size_t val) { strings.min(val); });

    InstallMethod("MaximumWordLength",
                  "for an IsStrings object and an int",
                  {"IsStrings", "IsInt"},
                  // gapbind14 currently doesn't handle the reference returned
                  // by strings.first(w) properly so we wrap it in a lambda
                  [](Strings& strings, size_t val) { strings.max(val); });

    InstallMethod(
        "Alphabet",
        "for an IsStrings object and a string",
        {"IsStrings", "IsString"},
        // gapbind14 currently doesn't handle the reference returned
        // by thing.first(w) properly so we wrap it in a lambda
        [](Strings& strings, std::string const& s) { strings.alphabet(s); });

    InstallMethod("Alphabet",
                  "for an IsStrings object",
                  {"IsStrings"},
                  // gapbind14 currently doesn't handle the reference returned
                  // by thing.first(w) properly so we wrap it in a lambda
                  overload_cast<>(&Strings::alphabet));

    ////////////////////////////////////////////////////////////////////////
    // ToWord declarations
    ////////////////////////////////////////////////////////////////////////

    class_<ToWord>("ToWord");

    DeclareCategory("IsToWord", "IsObject");

    DeclareOperation("ToWord", {});
    DeclareOperation("ToWord", {"IsToWord"});
    DeclareOperation("ToWord", {"IsString"});
    DeclareOperation("Init", {"IsToWord"});
    DeclareOperation("Init", {"IsToWord", "IsString"});
    DeclareOperation("[]", {"IsToWord", "IsList"});

    DeclareProperty("IsEmpty", "IsToWord");

    ////////////////////////////////////////////////////////////////////////
    // ToWord implementations
    ////////////////////////////////////////////////////////////////////////

    InstallMethod("ToWord", "for no arguments", {}, init<ToWord>());
    InstallMethod("ToWord",
                  "for a ToWord object",
                  {"IsToWord"},
                  init<ToWord, ToWord const&>());
    InstallMethod("ToWord",
                  "for a string",
                  {"IsString"},
                  init<ToWord, std::string const&>());

    InstallMethod("Init", "for a ToWord object", {"IsToWord"}, [](ToWord& tw) {
      tw.init();
    });
    InstallMethod("Init",
                  "for a ToWord object and string",
                  {"IsToWord", "IsString"},
                  [](ToWord& tw, std::string const& s) { tw.init(s); });

    InstallMethod("[]",
                  "for a ToWord object and string",
                  {"IsToWord", "IsString"},
                  overload_cast<std::string const&>(&ToWord::operator()));

    InstallMethod(
        "IsEmpty", "for a ToWord object", {"IsToWord"}, &ToWord::empty);
  }
}  // namespace gapbind14
