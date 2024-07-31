#############################################################################
##
##  tools/utils.gi
##  Copyright (C) 2013-2022                              James D. Mitchell
##
##  Licensing information can be found in the README file of this package.
##
#############################################################################
##
## This file contains utilities for use with the Semigroups package.

# No attempt has been made to get good test coverage for this file, since it
# will hopefully be binned in the near future.

# The file is organised as follows:
#
# 1. Tests - functions relating to testing Semigroups
#
# 2. Documentation - functions relating to compiling and verifying the
#    documentation.

InstallGlobalFunction(ToBeat,
function(list, arg...)
  local rank, rank_to_beat;
  Assert(1, IsList(list));

  rank         := Sum(list, RankFilter);
  rank_to_beat := Maximum(List(arg, x -> Sum(x, RankFilter)));

  if rank > rank_to_beat then
    return 0;
  else
    return rank_to_beat - rank + 1;
  fi;
end);

#############################################################################
# 1. Tests - internal stuff . . .
#############################################################################

SEMIGROUPS.TestRec := rec();

SEMIGROUPS.TestRec.reportDiff := function(inp, expout, found, fnam, line, _)
  Print("######## > Diff in:\n");
  if IsStream(fnam)  then
    Print("test stream, line ", line, "\n");
  else
    Print(fnam, ":", line, "\n");
  fi;
  Print("# Input is:\n", inp);
  Print("# Expected output:\n\033[30;42m", Chomp(expout), "\033[0m\n");
  Print("# But found:\n\033[30;41m", Chomp(found), "\033[0m\n");
  Print("########\n");
  return;
end;

SEMIGROUPS.StartTest := function()
  local record;

  record := SEMIGROUPS.TestRec;

  # store current info levels
  record.InfoLevelInfoWarning := InfoLevel(InfoWarning);
  record.InfoLevelInfoSemigroups := InfoLevel(InfoSemigroups);
  record.InfoLevelInfoOrb := InfoLevel(InfoOrb);
  record.InfoLevelInfoGenSS := InfoLevel(InfoGenSS);
  record.InfoLevelInfoPackageLoading := InfoLevel(InfoPackageLoading);

  # store current user preferences
  record.PartialPermDisplayLimit :=
    UserPreference("PartialPermDisplayLimit");
  record.TransformationDisplayLimit :=
    UserPreference("TransformationDisplayLimit");
  record.NotationForPartialPerms :=
    UserPreference("NotationForPartialPerms");
  record.NotationForTransformations :=
    UserPreference("NotationForTransformations");
  record.FreeInverseSemigroupElementDisplay :=
    UserPreference("semigroups", "FreeInverseSemigroupElementDisplay");
  record.ViewObj :=
    UserPreference("semigroups", "ViewObj");

  # store current default options
  record.SEMIGROUPS_DefaultOptionsRec :=
    ShallowCopy(SEMIGROUPS.DefaultOptionsRec);

  # set info levels
  SetInfoLevel(InfoWarning, 0);
  SetInfoLevel(InfoSemigroups, 0);
  SetInfoLevel(InfoOrb, 0);
  SetInfoLevel(InfoGenSS, 0);
  SetInfoLevel(InfoPackageLoading, 0);

  # set user preferences
  SetUserPreference("PartialPermDisplayLimit",
                    100);
  SetUserPreference("TransformationDisplayLimit",
                    100);
  SetUserPreference("NotationForPartialPerms",
                    "component");
  SetUserPreference("NotationForTransformations",
                    "input");
  SetUserPreference("semigroups",
                    "FreeInverseSemigroupElementDisplay",
                    "minimal");
  SetUserPreference("semigroups",
                    "ViewObj",
                    "semigroups-pkg");

  # set default options
  LIBSEMIGROUPS_REPORTING_ENABLED(false);
  return;
end;

SEMIGROUPS.StopTest := function()
  local record;

  record := SEMIGROUPS.TestRec;

  # restore info levels
  SetInfoLevel(InfoWarning, record.InfoLevelInfoWarning);
  SetInfoLevel(InfoSemigroups, record.InfoLevelInfoSemigroups);
  SetInfoLevel(InfoOrb, record.InfoLevelInfoOrb);
  SetInfoLevel(InfoGenSS, record.InfoLevelInfoGenSS);
  SetInfoLevel(InfoSemigroups, record.InfoLevelInfoPackageLoading);

  # restore user preferences
  SetUserPreference("PartialPermDisplayLimit",
                    record.PartialPermDisplayLimit);
  SetUserPreference("TransformationDisplayLimit",
                    record.TransformationDisplayLimit);
  SetUserPreference("NotationForPartialPerms",
                    record.NotationForPartialPerms);
  SetUserPreference("NotationForTransformations",
                    record.NotationForTransformations);
  SetUserPreference("semigroups",
                    "FreeInverseSemigroupElementDisplay",
                    record.FreeInverseSemigroupElementDisplay);
  SetUserPreference("semigroups",
                    "ViewObj",
                    record.ViewObj);

  # restore default options
  SEMIGROUPS.DefaultOptionsRec := record.SEMIGROUPS_DefaultOptionsRec;
  GASMAN("collect");
  return;
end;

SEMIGROUPS.RunTest := function(func)
  local acting, passed;
  if not (IsFunction(func) and NumberArgumentsFunction(func) = 0) then
    ErrorNoReturn("the argument must be a 0-parameter function");
  fi;

  # Store global option
  acting := SEMIGROUPS.DefaultOptionsRec.acting;

  # Run tests with acting := true
  Print("\033[1m");
  Info(InfoWarning, 1, "Running tests with acting methods enabled");
  Print("\033[0m");
  SEMIGROUPS.DefaultOptionsRec.acting := true;
  passed := func();

  if not (IsBool(passed) and passed in [true, false]) then
    ErrorNoReturn("the argument must be a function returning 'true'",
                  " or 'false'");
  elif not passed then
    SEMIGROUPS.DefaultOptionsRec.acting := acting;
    return passed;
  fi;

  # Run tests with acting := false
  Print("\033[1m");
  Info(InfoWarning, 1, "Running tests with acting methods disabled");
  Print("\033[0m");
  SEMIGROUPS.DefaultOptionsRec.acting := false;
  passed := func();

  # Reset global options
  SEMIGROUPS.DefaultOptionsRec.acting := acting;
  return passed;
end;

SEMIGROUPS.TestDir := function(dir, arg)
  local opts, name;

  opts := rec(earlyStop   := false,
              testOptions := ShallowCopy(SEMIGROUPS.TestRec));
  opts.testOptions.showProgress := false;
  if Length(arg) = 1 and IsRecord(arg[1]) then
    # Override default options with input ones.
    for name in RecNames(arg[1]) do
      opts.testOptions.(name) := arg[1].(name);
    od;
    # To allow the option from tst/teststandard.g to be processed
    if "suppressStatusMessage" in RecNames(arg[1]) then
      opts.suppressStatusMessage := arg[1].suppressStatusMessage;
    fi;
  elif Length(arg) <> 0 then
    ErrorNoReturn("there must be no arguments, or the argument ",
                  "must be a record");
  fi;
  return SEMIGROUPS.RunTest({} -> TestDirectory(dir, opts));
end;

#############################################################################
# 1. Tests - user/global functions
#############################################################################

InstallGlobalFunction(SemigroupsTestInstall,
function(arg...)
  local opts, name;
  opts := ShallowCopy(SEMIGROUPS.TestRec);
  if Length(arg) = 1 and IsRecord(arg[1]) then
    # Override default options with input ones.
    for name in RecNames(arg[1]) do
      opts.(name) := arg[1].(name);
    od;
  elif Length(arg) <> 0 then
    ErrorNoReturn("there must be no arguments, or the argument ",
                  "must be a record");
  fi;
  return SEMIGROUPS.RunTest(function()
      return Test(Filename(DirectoriesPackageLibrary("semigroups",
                                                     "tst"),
                           "testinstall.tst"), opts);
    end);
end);

InstallGlobalFunction(SemigroupsTestStandard,
function(arg...)
  return SEMIGROUPS.TestDir(DirectoriesPackageLibrary("semigroups",
                                                      "tst/standard/")[1]![1],
                            arg);
end);

InstallGlobalFunction(SemigroupsTestExtreme,
function(arg...)
  if IsEmpty(arg) then
    arg := [rec(showProgress := "some")];
  elif IsRecord(arg[1]) and not IsBound(arg[1].showProgress) then
    arg[1].showProgress := "some";
  fi;
  return SEMIGROUPS.TestDir(DirectoriesPackageLibrary("semigroups",
                                                      "tst/extreme/"),
                            arg);
end);

InstallGlobalFunction(SemigroupsTestAll,
function(arg...)
  SemigroupsMakeDoc();
  if not CallFuncList(SemigroupsTestInstall, arg) then
    Print("Abort: SemigroupsTestInstall failed . . . \n");
    return false;
  elif not CallFuncList(SemigroupsTestStandard, arg) then
    Print("Abort: SemigroupsTestStandard failed . . . \n");
    return false;
  fi;

  return SEMIGROUPS.TestManualExamples();
end);

################################################################################
# 2. Documentation - internal stuff
################################################################################

BindGlobal("SEMIGROUPS_DocXMLFiles",
function()
  local dir;
  dir := DirectoriesPackageLibrary("Semigroups", "doc")[1];
  return Filtered(DirectoryContents(dir),
                  x -> (not StartsWith(x, "."))
                        and (not StartsWith(x, "z-"))
                        and EndsWith(x, ".xml"));
end);

InstallGlobalFunction(SemigroupsMakeDoc,
function()
  local fname;
  fname := Filename(DirectoriesPackageLibrary("Semigroups", ""), "makedoc.g");
  Read(fname);
end);

SEMIGROUPS.ManualExamples := function()
  if Filename(DirectoriesPackageLibrary("semigroups", "doc"),
              "main.xml") = fail then
    # The file main.xml only exists if AutoDoc has been run.
    SemigroupsMakeDoc();
  fi;
  return ExtractExamples(DirectoriesPackageLibrary("semigroups", "doc"),
                         "main.xml",
                         SEMIGROUPS_DocXMLFiles(),
                         "Single");
end;

SEMIGROUPS.RunExamples := function(exlists, nums, excluded)
  local oldscr, pad, total, fails, num, HighlightWS, l, sp, bad, s, start_time,
  test, end_time, elapsed, pex, j, ex, i;

  oldscr := SizeScreen();
  SizeScreen([72, oldscr[2]]);
  pad := function(nr)
    nr := Length(String(Maximum(nums))) - Length(String(nr)) + 1;
    return List([1 .. nr], x -> ' ');
  end;
  total := 0;
  fails := [];
  num   := 0;

  HighlightWS := function(str)
    str := Chomp(str);
    return ReplacedString(str, " \n", "~\n");
  end;

  for j in [1 .. Length(exlists)] do
    if j in excluded then
      Print("\033[44m# Skipping example ",
            j,
            pad(j),
            " . . .\033[0m\n");
    else
      l := exlists[j];
      Print("# Running example ", nums[j], pad(nums[j]), " . . .");
      START_TEST("");
      num := num + 1;
      for ex in l do
        sp := SplitString(ex[1], "\n", "");
        bad := Filtered([1 .. Length(sp)], i -> Length(sp[i]) > 72);
        s := InputTextString(ex[1]);

        start_time := IO_gettimeofday();
        test := Test(s, rec(compareFunction := "uptowhitespace",
                            ignoreComments := false,
                            width := 72,
                            EQ := \=,
                            reportDiff := Ignore,
                            showProgress := false));
        end_time := IO_gettimeofday();
        CloseStream(s);
        elapsed := (end_time.tv_sec - start_time.tv_sec) * 1000
                   + Int((end_time.tv_usec - start_time.tv_usec) / 1000);
        total := total + elapsed;
        pex := TEST.lastTestData;

        Print(" msecs: ", elapsed, "\n");

        if Length(bad) > 0 then
          Print("\033[31m# WARNING: Overlong lines ",
                bad,
                " in ",
                ex[2]{[1 .. 3]},
                "\033[0m\n");
          AddSet(fails, nums[j]);
        fi;

        if test = false then
          for i in [1 .. Length(pex[1])] do
            if pex[2][i] <> pex[4][i] then
              Print("########> Diff in:\n",
                    "# ", ex[2][1], ":", ex[2][2],
                    "\n# Input is:\n");
              PrintFormattedString(pex[1][i]);
              Print("# Expected output:\n\033[30;42m");
              PrintFormattedString(HighlightWS(pex[2][i]));
              Print("\033[0m\n# But found:\n\033[30;41m");
              PrintFormattedString(HighlightWS(pex[4][i]));
              Print("\033[0m\n########\n");
              AddSet(fails, nums[j]);
            fi;
          od;
        fi;
      od;
    fi;
  od;
  SizeScreen(oldscr);
  if Length(exlists) > 1 then
    PrintFormatted("# {} failures in {} examples . . . msecs: {}\n",
                   Length(fails),
                   Sum(exlists, Length),
                   total);
  fi;
  if not IsEmpty(fails) then
    Print("# Failed manual examples are:\n");
    return fails;
  fi;
  return true;
end;

SEMIGROUPS.TestManualExamples := function(arg...)
  local ex, nums, doc, tree, mansect, tester, actual, omit, acting, passed,
  str;

  ex := SEMIGROUPS.ManualExamples();
  if IsEmpty(arg) then
    nums := [1 .. Length(ex)];
  elif Length(arg) = 1 then
    if IsPosInt(arg[1]) and arg[1] <= Length(ex) then
      ex := [ex[arg[1]]];
      nums := [arg[1]];
    elif IsHomogeneousList(arg[1])
        and ForAll(arg[1], x -> IsPosInt(x) and x <= Length(ex)) then
      ex := SEMIGROUPS.ManualExamples(){arg[1]};
      nums := arg[1];
    elif IsString(arg[1]) then
      doc := ComposedXMLString(Concatenation(SEMIGROUPS.PackageDir, "/doc"),
                               "main.xml",
                               SEMIGROUPS_DocXMLFiles(),
                               true);
      tree := ParseTreeXMLString(doc[1]);
      CheckAndCleanGapDocTree(tree);
      mansect := XMLElements(tree, "ManSection");
      tester := function(record)
        return IsBound(record.content[1].attributes.Name)
            and record.content[1].attributes.Name = arg[1];
      end;
      mansect := First(mansect, tester);
      if mansect = fail then
        ErrorNoReturn("did not find a man section named ", arg[1]);
      fi;
      actual := ExtractExamplesXMLTree(mansect, "Single");
      nums := [PositionProperty(ex, x -> x[1][1] = actual[1][1][1])];
      ex := actual;
    else
      ErrorNoReturn("the argument must be a pos int or list of pos ints");
    fi;
  elif Length(arg) > 1 then
    ErrorNoReturn("there should be 0 or 1 arguments");
  fi;

  omit := SEMIGROUPS.OmitFromTests;
  if Length(omit) > 0 then
    Print("# not testing examples containing the strings");
    for str in omit do
      ex := Filtered(ex, x -> PositionSublist(x[1][1], str) = fail);
      Print(", \"", str, "\"");
    od;
    Print(" . . .\n");
  fi;

  acting := SEMIGROUPS.DefaultOptionsRec.acting;
  Apply(ex, function(x)
    x[1][1] := StripBeginEnd(x[1][1], "\n");
    return x;
  end);

  SEMIGROUPS.DefaultOptionsRec.acting := true;
  SEMIGROUPS.StartTest();
  passed := SEMIGROUPS.RunExamples(ex, nums, []);
  SEMIGROUPS.StopTest();

  SEMIGROUPS.DefaultOptionsRec.acting := acting;
  return passed;
end;

# The following is based on doc/ref/testconsistency.g

# Detect which ManSection should be used to document obj. Returns one of
# "Func", "Oper", "Meth", "Filt", "Prop", "Attr", "Var", "Fam", "InfoClass"
#
# See PRINT_OPERATION where some of the code below is borrowed

SEMIGROUPS.ManSectionType := function(op)
  local   class, flags, types, catok, repok, propok, seenprop, t;
  if IsInfoClass(op) then
    return "InfoClass";
  elif IsFamily(op) then
    return "Fam";
  elif not IsFunction(op) then
    return "Var";
  elif IsFunction(op) and not IsOperation(op) then
    return "Func";
  elif IsOperation(op) then
    class := "Oper";
    if IS_IDENTICAL_OBJ(op, IS_OBJECT) then
      class := "Filt";
    elif IS_CONSTRUCTOR(op) then
      class := "Constructor";
      # seem to never get one
    elif IsFilter(op) then
      class := "Filt";
      flags := TRUES_FLAGS(FLAGS_FILTER(op));
      types := INFO_FILTERS{flags};
      catok := true;
      repok := true;
      propok := true;
      seenprop := false;
      for t in types do
        if not t in FNUM_REPS then
          repok := false;
        fi;
        if not t in FNUM_CATS then
          catok := false;
        fi;
        if not t in FNUM_PROS and not t in FNUM_TPRS then
          propok := false;
        fi;
        if t in FNUM_PROS then
          seenprop := true;
        fi;
      od;
      if seenprop and propok then
        class := "Prop";
      elif catok then
        class := "Filt";
        # in PRINT_OPERATION - "Category";
      elif repok then
        class := "Filt";
        # in PRINT_OPERATION - "Representation";
      fi;
    elif Tester(op) <> false  then
      # op is an attribute
      class := "Attr";
    fi;
    return class;
  else
    return fail;
  fi;
end;

# Checks whether ManSections are using the right kind of elements

SEMIGROUPS.CheckManSectionTypes := function(doc, verbose...)
  local display_warnings, types, r, x, errcount, name, pos, obj, man, y, yint,
  referrcount, warncount, type, matches, match, matches2, stats,
  elt, t, s;

  if IsEmpty(verbose) then
    display_warnings := false;
  else
    display_warnings := verbose[1];
  fi;
  types := ["Func", "Oper", "Meth", "Filt", "Prop", "Attr", "Var", "Fam",
            "InfoClass"];
  r := ParseTreeXMLString(doc[1]);
  CheckAndCleanGapDocTree(r);
  x := XMLElements(r, types);
  errcount := 0;
  Print("****************************************************************\n");
  Print("*** Checking types in ManSections \n");
  Print("****************************************************************\n");
  for elt in x do
    name := elt.attributes.Name;
    if not name in ["IsBound", "Unbind", "Info", "Assert", "TryNextMethod",
                    "QUIT", "-infinity"] then
      if not IsBoundGlobal(name) then
        pos := OriginalPositionDocument(doc[2], elt.start);
        Print(pos[1], ":", pos[2], " : ", name, " is unbound \n");
        errcount := errcount + 1;
      else
        obj := ValueGlobal(name);
        man := SEMIGROUPS.ManSectionType(obj);
        # we allow to use "Meth" for "Oper" but probably should issue a warning
        # if there is no at least one "Oper" for any "Meth"
        if (man <> elt.name) and
            not (man in ["Attr", "Prop", "Oper"] and elt.name = "Meth") then
          pos := OriginalPositionDocument(doc[2], elt.start);
          Print(pos[1], ":", pos[2], " : ", name, " uses ", elt.name,
                " instead of ", man, "\n");
          errcount := errcount + 1;
        fi;
      fi;
    fi;
  od;

  Print("****************************************************************\n");
  Print("*** Checking types in cross-references \n");
  Print("****************************************************************\n");
  y := XMLElements(r, ["Ref"]);
  Print("Found ", Length(y), " Ref elements ");
  yint := Filtered(y, elt -> not IsBound(elt.attributes.BookName)
                             or (IsBound(elt.attributes.BookName)
                                 and elt.attributes.BookName = "ref"));
  Print("including ", Length(yint), " within the Reference manual\n");
  y := Filtered(yint, elt -> ForAny(types, t -> IsBound(elt.attributes.(t))));

  referrcount := 0;
  warncount := 0;
  for elt in y do
    type := First(types, t -> IsBound(elt.attributes.(t)));
    if type <> fail then
      matches := Filtered(x, t -> t.attributes.Name = elt.attributes.(type));
      if IsEmpty(matches) then
        pos := OriginalPositionDocument(doc[2], elt.start);
        Print(pos[1], ":", pos[2], " : no match for ", type, " := ",
              elt.attributes.(type), "\n");
        referrcount := referrcount + 1;
        continue;
      elif Length(matches) = 1 then
        match := matches[1];
      elif IsBound(elt.attributes.Label) then
        matches := Filtered(matches, t -> IsBound(t.attributes.Label));
        matches := Filtered(matches, t -> t.attributes.Label =
                                          elt.attributes.Label);
        if Length(matches) > 1 then
          ErrorNoReturn("Multiple labels - this should not happen!");
        fi;
        match := matches[1];
      else
        matches2 := Filtered(matches, t -> not IsBound(t.attributes.Label));
        if IsEmpty(matches2) then
          pos := OriginalPositionDocument(doc[2], elt.start);
          Print(pos[1], ":", pos[2],
                " : no match (wrong type or missing label?) for ", type, " := ",
                elt.attributes.(type), "\n");
          Print("  Suggestions: \n");
          matches := Filtered(matches, t -> IsBound(t.attributes.Label));
          for t in matches do
            Print("Use ", t.name, " with Label := \"", t.attributes.Label,
                  "\" (for Arg := \"", t.attributes.Arg, "\")\n");
          od;

          referrcount := referrcount + 1;
          continue;
        elif Length(matches2) > 1 then
          ErrorNoReturn("Multiple labels - this should not happen!");
        else
          match := matches[1];
        fi;
      fi;
      if match.name <> type then
        pos := OriginalPositionDocument(doc[2], elt.start);
        if display_warnings then
          Print(pos[1], ":", pos[2], " : Ref to ", elt.attributes.(type),
                " uses ", type, " instead of ", match.name, "\n");
        fi;
        warncount := warncount + 1;
      fi;
    fi;
  od;

  Print("****************************************************************\n");
  stats := Collected(List(x, elt -> elt.name));
  Print("Selected ", Length(x), " ManSections of the following types:\n");
  for s in stats do
    Print(s[1], " - ", s[2], "\n");
  od;
  Print("Found ", errcount, " errors in ManSection types \n");

  Print("Selected ", Length(y), " Ref elements referring to ManSections \n");
  Print("Found ", referrcount, " errors and ", warncount,
        " warnings in Ref elements \n");

  if display_warnings then
    Print("To suppress warnings, use SEMIGROUPS.CheckManSectionTypes",
          "(doc,false) or with one argument\n");
  else
    Print("To show warnings, use SEMIGROUPS.CheckManSectionTypes(doc,true);",
          "\n");
  fi;
  Print("****************************************************************\n");
  return errcount = 0;
end;

SEMIGROUPS.CheckDocCoverage := function(doc)
  local r, x, with, without, mansect, pos, y;
  r := ParseTreeXMLString(doc[1]);
  CheckAndCleanGapDocTree(r);
  x := XMLElements(r, ["ManSection"]);
  with := 0;
  without := 0;
  Print("****************************************************************\n");
  Print("*** Looking for ManSections having no examples \n");
  Print("****************************************************************\n");
  for mansect in x do
    pos := OriginalPositionDocument(doc[2], mansect.start);
    y := XMLElements(mansect, ["Example"]);
    if IsEmpty(y) then
      if IsBound(mansect.content[1].attributes) and
          IsBound(mansect.content[1].attributes.Name) then
        Print(pos[1], ":", pos[2], " : ", mansect.content[1].attributes.Name);
      elif IsBound(mansect.content[2].attributes) and
          IsBound(mansect.content[2].attributes.Name) then
        Print(pos[1], ":", pos[2], " : ", mansect.content[2].attributes.Name);
      else
        Print(pos[1], ":", pos[2], " : ",
              mansect.content[1].content[1].content);
      fi;
      without := without + 1;
      Print("\n");
    else
      with := with + 1;
    fi;
  od;
  Print("****************************************************************\n");
  Print("*** Doc coverage report \n");
  Print("****************************************************************\n");
  Print(Length(x), " mansections \n");
  Print(with, " with examples \n");
  Print(without, " without examples \n");
end;

SEMIGROUPS.CheckManualConsistency := function()
  local doc;

  doc := ComposedXMLString(Concatenation(SEMIGROUPS.PackageDir, "/doc"),
                           "main.xml",
                           SEMIGROUPS_DocXMLFiles(),
                           true);
  SEMIGROUPS.CheckDocCoverage(doc);
  return SEMIGROUPS.CheckManSectionTypes(doc, true);
end;

SEMIGROUPS.DocumentedPackageVariables := function()
  local doc, r, x, out, mansect, record;
  doc := ComposedXMLString(Concatenation(SEMIGROUPS.PackageDir, "/doc"),
                           "main.xml",
                           SEMIGROUPS_DocXMLFiles(),
                           true);
  r := ParseTreeXMLString(doc[1]);
  CheckAndCleanGapDocTree(r);
  x := XMLElements(r, ["ManSection"]);
  out := [];
  for mansect in x do
    for record in mansect.content do
      if IsBound(record.attributes) and IsBound(record.attributes.Name) then
        AddSet(out, record.attributes.Name);
      fi;
    od;
  od;
  return out;
end;

# info := PackageVariablesInfo("semigroups", "3.0.0");;
# which must be run before loading Semigroups
SEMIGROUPS.UndocumentedPackageVariables := function(info)
  local out, suppressions, obsoletes, documented, name, part, entry;

  out := [];
  suppressions := ["*", ".", "/", "<", "=", "[]", "^", "in", "{}",
                   "HTAdd_TreeHash_C", "HTValue_TreeHash_C"];

  obsoletes := [];
  documented := SEMIGROUPS.DocumentedPackageVariables();

  for part in info do
    if (part[1]{[1 .. 3]} = "new" or part[1]{[1 .. 9]} = "other new") and not
        part[1] = "new methods" then
      for entry in part[2] do
        name := entry[1][1];
        if not name in suppressions
            and not name in obsoletes
            and not name in documented
            and not ForAll(name, x -> IsUpperAlphaChar(x) or x = '_')
            and not (Length(name) >= 3 and name{[1 .. 3]} = "Has")
            and not (Length(name) >= 3 and name{[1 .. 3]} = "Set")
            and not (Length(name) >= 11 and name{[1 .. 11]} = "SEMIGROUPS_")
            and not (Length(name) >= 2
                     and name{[Length(name) - 1, Length(name)]} = "NC") then
          AddSet(out, [name, JoinStringsWithSeparator(entry[2], ":")]);
        fi;
      od;
    fi;
  od;
  return out;
end;
