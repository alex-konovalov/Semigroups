#############################################################################
##
##  semigroups/semifp.gi
##  Copyright (C) 2015-2022                              James D. Mitchell
##
##  Licensing information can be found in the README file of this package.
##
#############################################################################
##

# Many of the methods in this file should probably have the filter
# HasRelationsOfFpMonoid/Semigroup added to their requirements, but for some
# reason fp semigroups and monoids don't known their relations at creation.

# All methods for fp semigroups and monoids go via the underlying congruence on
# the free semigroup and free monoid.

# TODO methods for submonoids of fp monoids and subsemigroups of fp semigroups
InstallImmediateMethod(CanUseGapFroidurePin,
IsSubsemigroupOfFpMonoid and HasGeneratorsOfSemigroup, 0,
function(T)
  local x;
  x := Representative(GeneratorsOfSemigroup(T));
  return CanUseFroidurePin(FpMonoidOfElementOfFpMonoid(x));
end);

InstallMethod(UnderlyingCongruence, "for an fp semigroup",
[IsFpSemigroup],
function(S)
  local F, R;
  F := FreeSemigroupOfFpSemigroup(S);
  R := RelationsOfFpSemigroup(S);
  return SemigroupCongruenceByGeneratingPairs(F, R);
end);

InstallMethod(UnderlyingCongruence, "for an fp monoid",
[IsFpMonoid],
function(S)
  local F, R;
  F := FreeMonoidOfFpMonoid(S);
  R := RelationsOfFpMonoid(S);
  return SemigroupCongruenceByGeneratingPairs(F, R);
end);

InstallMethod(ElementOfFpSemigroup,
"for an fp semigroup and an associative word",
[IsFpSemigroup, IsAssocWord],
{S, w} -> ElementOfFpSemigroup(FamilyObj(Representative(S)), w));

InstallMethod(ElementOfFpMonoid,
"for an fp monoid and an associative word",
[IsFpMonoid, IsAssocWord],
{M, w} -> ElementOfFpMonoid(FamilyObj(Representative(M)), w));

InstallMethod(Size, "for an fp semigroup", [IsFpSemigroup],
S -> NrEquivalenceClasses(UnderlyingCongruence(S)));

# TODO(later) more of these

InstallMethod(Size, "for an fp semigroup with nice monomorphism",
[IsFpSemigroup and HasNiceMonomorphism],
S -> Size(Range(NiceMonomorphism(S))));

InstallMethod(AsList, "for an fp semigroup with nice monomorphism",
[IsFpSemigroup and HasNiceMonomorphism],
function(S)
  local map;
  map := InverseGeneralMapping(NiceMonomorphism(S));
  return List(Enumerator(Source(map)), x -> x ^ map);
end);

InstallMethod(Enumerator, "for an fp semigroup with nice monomorphism",
[IsFpSemigroup and HasNiceMonomorphism], 100,
function(S)
  local enum;
  enum := rec();

  enum.map := NiceMonomorphism(S);

  enum.NumberElement := function(enum, x)
    return PositionCanonical(Range(enum!.map), x ^ enum!.map);
  end;

  enum.ElementNumber := function(enum, nr)
    return EnumeratorCanonical(Range(enum!.map))[nr]
      ^ InverseGeneralMapping(enum!.map);
  end;

  enum.Length := enum -> Size(S);

  enum.Membership := function(x, enum)
    return x ^ enum!.map in Range(enum!.map);
  end;

  # TODO store S in enum and use this below
  enum.IsBound\[\] := function(_, nr)
    return nr <= Size(S);
  end;

  return EnumeratorByFunctions(S, enum);
end);

# TODO(later) EnumeratorSorted

InstallMethod(AsSSortedList, "for an fp semigroup with nice monomorphism",
[IsFpSemigroup and HasNiceMonomorphism],
22,
function(S)
  local map;
  map := InverseGeneralMapping(NiceMonomorphism(S));
  # EnumeratorCanonical returns the elements of the Range(NiceMonomorphism(S))
  # in short-lex order, which is sorted.
  return List(EnumeratorCanonical(Source(map)), x -> x ^ map);
end);

InstallMethod(Size, "for an fp monoid", [IsFpMonoid],
S -> NrEquivalenceClasses(UnderlyingCongruence(S)));

InstallMethod(\=, "for elements of an f.p. semigroup",
IsIdenticalObj, [IsElementOfFpSemigroup, IsElementOfFpSemigroup],
function(x, y)
  local C;
  C := UnderlyingCongruence(FpSemigroupOfElementOfFpSemigroup(x));
  return CongruenceTestMembershipNC(C,
                                    UnderlyingElement(x),
                                    UnderlyingElement(y));
end);

InstallMethod(\=, "for two elements of an f.p. monoid",
IsIdenticalObj, [IsElementOfFpMonoid, IsElementOfFpMonoid],
function(x, y)
  local C;
  C := UnderlyingCongruence(FpMonoidOfElementOfFpMonoid(x));
  return CongruenceTestMembershipNC(C,
                                    UnderlyingElement(x),
                                    UnderlyingElement(y));
end);

InstallMethod(\<, "for elements of an f.p. semigroup",
IsIdenticalObj, [IsElementOfFpSemigroup, IsElementOfFpSemigroup],
function(x, y)
  local S, map, C;
  S := FpSemigroupOfElementOfFpSemigroup(x);
  if HasNiceMonomorphism(S) then
    map := NiceMonomorphism(S);
    return PositionCanonical(Range(map), x ^ map)
      < PositionCanonical(Range(map), y ^ map);
  fi;
  C := UnderlyingCongruence(S);
  return CongruenceLessNC(C, UnderlyingElement(x), UnderlyingElement(y));
end);

InstallMethod(\<, "for two elements of an f.p. monoid",
IsIdenticalObj, [IsElementOfFpMonoid, IsElementOfFpMonoid],
function(x, y)
  local C;
  C := UnderlyingCongruence(FpMonoidOfElementOfFpMonoid(x));
  return CongruenceLessNC(C, UnderlyingElement(x), UnderlyingElement(y));
end);

#############################################################################
# Methods not using the underlying congruence directly
#############################################################################

InstallMethod(ExtRepOfObj, "for an element of an fp semigroup",
[IsElementOfFpSemigroup], x -> ExtRepOfObj(UnderlyingElement(x)));

InstallMethod(ExtRepOfObj, "for an element of an fp monoid",
[IsElementOfFpMonoid], x -> ExtRepOfObj(UnderlyingElement(x)));

# TODO(later) AsSSortedList, RightCayleyDigraph, any more?
# - for both IsFpSemigroup/Monoid and IsFpSemigroup/Monoid +
# HasNiceMonomorphism

#############################################################################
# Viewing and printing - elements
#############################################################################

InstallMethod(ViewString, "for an f.p. semigroup element",
[IsElementOfFpSemigroup], String);

InstallMethod(ViewString, "for an f.p. monoid element",
[IsElementOfFpMonoid], String);

#############################################################################
# Viewing and printing - free monoids and semigroups
#############################################################################

InstallMethod(String, "for a free monoid with known generators",
[IsFreeMonoid and HasGeneratorsOfMonoid],
function(M)

  if UserPreference("semigroups", "ViewObj") <> "semigroups-pkg" then
    TryNextMethod();
  fi;

  return StringFormatted("FreeMonoidAndAssignGeneratorVars({})",
                         List(GeneratorsOfMonoid(M), String));
end);

InstallMethod(PrintString, "for a free monoid with known generators",
[IsFreeMonoid and HasGeneratorsOfMonoid], String);

InstallMethod(PrintObj, "for a free monoid with known generators",
[IsFreeMonoid and HasGeneratorsOfMonoid],
function(M)

  if UserPreference("semigroups", "ViewObj") <> "semigroups-pkg" then
    TryNextMethod();
  fi;

  Print(PrintString(M));
  return;
end);

InstallMethod(String, "for a free semigroup with known generators",
[IsFreeSemigroup and HasGeneratorsOfSemigroup],
function(M)

  if UserPreference("semigroups", "ViewObj") <> "semigroups-pkg" then
    TryNextMethod();
  fi;

  return StringFormatted("FreeSemigroupAndAssignGeneratorVars({})",
                         List(GeneratorsOfSemigroup(M), String));
end);

InstallMethod(PrintString, "for a free semigroup with known generators",
[IsFreeSemigroup and HasGeneratorsOfSemigroup], String);

InstallMethod(PrintObj, "for a free semigroup with known generators",
[IsFreeSemigroup and HasGeneratorsOfSemigroup],
function(M)

  if UserPreference("semigroups", "ViewObj") <> "semigroups-pkg" then
    TryNextMethod();
  fi;

  Print(PrintString(M));
  return;
end);

#############################################################################
# Viewing and printing - free monoids and semigroups
#############################################################################

InstallMethod(String, "for an f.p. monoid with known generators",
[IsFpMonoid and HasGeneratorsOfMonoid],
function(M)
  local result, fam, id;

  if UserPreference("semigroups", "ViewObj") <> "semigroups-pkg" then
    TryNextMethod();
  fi;

  result := PRINT_STRINGIFY(FreeMonoidOfFpMonoid(M),
                            " / ",
                            RelationsOfFpMonoid(M));

  fam := ElementsFamily(FamilyObj(FreeMonoidOfFpMonoid(M)));

  if IsEmpty(fam!.names) then
    return result;
  fi;
  id := StringFormatted("One({})", fam!.names[1]);
  return ReplacedString(result, "<identity ...>", id);
end);

InstallMethod(PrintString, "for an f.p. monoid with known generators",
[IsFpMonoid and HasGeneratorsOfMonoid],
function(M)

  if UserPreference("semigroups", "ViewObj") <> "semigroups-pkg" then
    TryNextMethod();
  fi;

  return String(M);
end);

InstallMethod(PrintObj, "for an f.p. monoid with known generators",
[IsFpMonoid and HasGeneratorsOfMonoid],
4,  # to beat the library method
function(M)

  if UserPreference("semigroups", "ViewObj") <> "semigroups-pkg" then
    TryNextMethod();
  fi;

  Print(PrintString(M));
  return;
end);

InstallMethod(ViewString, "for an f.p. monoid with known generators",
[IsFpMonoid and HasGeneratorsOfMonoid],
function(M)

  if UserPreference("semigroups", "ViewObj") <> "semigroups-pkg" then
    TryNextMethod();
  fi;

  return PRINT_STRINGIFY(
    StringFormatted("\>\><fp monoid with {} and {} of length {}>\<\<",
                    Pluralize(Length(GeneratorsOfMonoid(M)), "generator"),
                    Pluralize(Length(RelationsOfFpMonoid(M)), "relation"),
                    Length(M)));
end);

InstallMethod(ViewObj, "for an f.p. monoid with known generators",
[IsFpMonoid and HasGeneratorsOfMonoid],
4,  # to beat the library method
function(M)
  if UserPreference("semigroups", "ViewObj") <> "semigroups-pkg" then
    TryNextMethod();
  fi;
  Print(ViewString(M));
end);

InstallMethod(String, "for an f.p. semigroup with known generators",
[IsFpSemigroup and HasGeneratorsOfSemigroup],
function(M)

  if UserPreference("semigroups", "ViewObj") <> "semigroups-pkg" then
    TryNextMethod();
  fi;

  return PRINT_STRINGIFY(FreeSemigroupOfFpSemigroup(M),
                        " / ",
                         RelationsOfFpSemigroup(M));
end);

InstallMethod(PrintString, "for an f.p. semigroup with known generators",
[IsFpSemigroup and HasGeneratorsOfSemigroup],
function(M)

  if UserPreference("semigroups", "ViewObj") <> "semigroups-pkg" then
    TryNextMethod();
  fi;

  return String(M);
end);

InstallMethod(PrintObj, "for an f.p. semigroup with known generators",
[IsFpSemigroup and HasGeneratorsOfSemigroup],
4,  # to beat the library method
function(M)

  if UserPreference("semigroups", "ViewObj") <> "semigroups-pkg" then
    TryNextMethod();
  fi;

  Print(PrintString(M));
  return;
end);

InstallMethod(ViewString, "for an f.p. semigroup with known generators",
[IsFpSemigroup and HasGeneratorsOfSemigroup],
function(S)
  if UserPreference("semigroups", "ViewObj") <> "semigroups-pkg" then
    TryNextMethod();
  fi;

  return PRINT_STRINGIFY(
    StringFormatted("\>\><fp semigroup with {} and {} of length {}>\<\<",
                    Pluralize(Length(GeneratorsOfSemigroup(S)), "generator"),
                    Pluralize(Length(RelationsOfFpSemigroup(S)), "relation"),
                    Length(S)));
end);

InstallMethod(ViewObj,
"for an f.p. semigroup with known generators",
[IsFpSemigroup and HasGeneratorsOfSemigroup],
4,  # to beat the library method
function(S)
  if UserPreference("semigroups", "ViewObj") <> "semigroups-pkg" then
    TryNextMethod();
  fi;
  Print(ViewString(S));
end);

InstallGlobalFunction(FreeMonoidAndAssignGeneratorVars,
function(arg...)
  local F;
  F := CallFuncList(FreeMonoid, arg);
  AssignGeneratorVariables(F);
  return F;
end);

InstallGlobalFunction(FreeSemigroupAndAssignGeneratorVars,
function(arg...)
  local F;
  F := CallFuncList(FreeSemigroup, arg);
  AssignGeneratorVariables(F);
  return F;
end);

########################################################################
# Random
########################################################################

InstallMethod(SEMIGROUPS_ProcessRandomArgsCons,
[IsFpSemigroup, IsList],
function(_, params)
  if Length(params) < 1 then  # nr gens
    params[1] := Random(1, 20);
    params[2] := Random(1, 8);
  elif Length(params) < 2 then  # degree
    params[2] := Random(1, 8);
  fi;
  if not ForAll(params, IsPosInt) then
    ErrorNoReturn("the arguments must be positive integers");
  fi;
  return params;
end);

InstallMethod(SEMIGROUPS_ProcessRandomArgsCons,
[IsFpMonoid, IsList],
{_, params} -> SEMIGROUPS_ProcessRandomArgsCons(IsFpSemigroup, params));

# this doesn't work very well

InstallMethod(RandomSemigroupCons, "for IsFpSemigroup and a list",
[IsFpSemigroup, IsList],
function(_, params)
  return AsSemigroup(IsFpSemigroup,
                     CallFuncList(RandomSemigroup,
                                  Concatenation([IsTransformationSemigroup],
                                                 params)));
end);

# this doesn't work very well

InstallMethod(RandomMonoidCons, "for IsFpMonoid and a list",
[IsFpMonoid, IsList],
function(_, params)
  return AsMonoid(IsFpMonoid,
                  CallFuncList(RandomMonoid,
                               Concatenation([IsTransformationMonoid],
                                              params)));
end);

# this doesn't work very well

InstallMethod(RandomInverseSemigroupCons, "for IsFpSemigroup and a list",
[IsFpSemigroup, IsList],
function(_, params)
  return AsSemigroup(IsFpSemigroup,
                     CallFuncList(RandomInverseSemigroup,
                                  Concatenation([IsPartialPermSemigroup],
                                                params)));
end);

# this doesn't work very well

InstallMethod(RandomInverseMonoidCons, "for IsFpMonoid and a list",
[IsFpMonoid, IsList],
function(_, params)
  return AsMonoid(IsFpMonoid,
                  CallFuncList(RandomInverseMonoid,
                               Concatenation([IsPartialPermMonoid],
                                              params)));
end);

InstallMethod(IsomorphismSemigroup, "for IsFpSemigroup and a semigroup",
[IsFpSemigroup, IsSemigroup], {_, S} -> IsomorphismFpSemigroup(S));

InstallMethod(AsMonoid, "for an fp semigroup",
[IsFpSemigroup],
function(S)
  if MultiplicativeNeutralElement(S) = fail then
    return fail;  # so that we do the same as the GAP/ref manual says
  fi;
  return Range(IsomorphismMonoid(IsFpMonoid, S));
end);

InstallMethod(IsomorphismMonoid, "for IsFpMonoid and a semigroup",
[IsFpMonoid, IsSemigroup], {_, S} -> IsomorphismFpMonoid(S));

# same method for ideals

InstallMethod(IsomorphismFpSemigroup,
"for a semigroup with CanUseFroidurePin",
[CanUseFroidurePin],
function(S)
  local rules, F, A, rels, Q, B, map, inv, result;

  if not IsFinite(S) or not CanUseFroidurePin(S) then
    TryNextMethod();
  fi;

  rules := RulesOfSemigroup(S);

  F := FreeSemigroup(Length(GeneratorsOfSemigroup(S)));
  A := GeneratorsOfSemigroup(F);
  rels := List(rules, x -> [EvaluateWord(A, x[1]), EvaluateWord(A, x[2])]);

  Q := F / rels;
  B := GeneratorsOfSemigroup(Q);

  map := x -> EvaluateWord(B, Factorization(S, x));
  inv := x -> MappedWord(UnderlyingElement(x), A, GeneratorsOfSemigroup(S));
  result := SemigroupIsomorphismByFunctionNC(S, Q, map, inv);
  if IsTransformationSemigroup(S) or IsPartialPermSemigroup(S)
      or IsBipartitionSemigroup(S) then
    SetNiceMonomorphism(Q, InverseGeneralMapping(result));
  fi;
  if IsTransformationSemigroup(S) then
    SetIsomorphismTransformationSemigroup(Q, InverseGeneralMapping(result));
  elif IsPartialPermSemigroup(S) then
    SetIsomorphismPartialPermSemigroup(Q, InverseGeneralMapping(result));
  fi;
  return result;
end);

# same method for ideals

InstallMethod(IsomorphismFpMonoid, "for a semigroup with CanUseFroidurePin",
[CanUseFroidurePin],
function(S)
  local sgens, mgens, F, A, start, lookup, spos, mpos, pos, rules, rels,
  convert, word, is_redundant, Q, map, inv, i, rule;

  if not IsMonoidAsSemigroup(S) then
    ErrorNoReturn("the 1st argument (a semigroup) must ",
                  "satisfy `IsMonoidAsSemigroup`");
  elif not IsFinite(S) then
    TryNextMethod();
  fi;

  sgens := GeneratorsOfSemigroup(S);
  mgens := Filtered(sgens,
                    x -> x <> MultiplicativeNeutralElement(S));

  F := FreeMonoid(Length(mgens));
  A := GeneratorsOfMonoid(F);
  start := [1 .. Length(sgens)] * 0;
  lookup := [];
  # make sure we map duplicate generators to the correct values
  for i in [1 .. Length(sgens)] do
    spos := Position(sgens, sgens[i]);
    mpos := Position(mgens, sgens[i], start[spos]);
    lookup[i] := mpos;
    if mpos <> fail then
      start[spos] := mpos;
    fi;
  od;

  pos := Position(lookup, fail);

  rules := RulesOfSemigroup(S);
  rels := [];

  # convert a word in GeneratorsOfSemigroup to a word in GeneratorsOfMonoid
  convert := function(word)
    local out, i;
    out := One(F);
    for i in word do
      if lookup[i] <> fail then
        out := out * A[lookup[i]];
      fi;
    od;
    return out;
  end;

  if mgens = sgens then
    # the identity is not a generator, so to avoid adjoining an additional
    # identity in the output, we must add a relation equating the identity with
    # a word in the generators.
    word := Factorization(S, MultiplicativeNeutralElement(S));
    Add(rels, [convert(word), One(F)]);
    # Note that the previously line depends on Factorization always giving a
    # factorization in the GeneratorsOfSemigroup(S), and not in
    # GeneratorsOfMonoid(S) if S happens to be a monoid.
  fi;

  # check if a rule is a consequence of the relation (word = one)
  is_redundant := function(rule)
    local prefix, suffix, i;
    if not IsBound(word) or Length(rule[1]) < Length(word) then
      return false;
    fi;

    # check if <word> is a prefix
    prefix := true;
    for i in [1 .. Length(word)] do
      if word[i] <> rule[1][i] then
        prefix := false;
        break;
      fi;
    od;
    if prefix then
      return rule[1]{[Length(word) + 1 .. Length(rule[1])]} = rule[2];
    fi;

    # check if <word> is a suffix
    suffix := true;
    for i in [1 .. Length(word)] do
      if word[i] <> rule[1][i] then
        suffix := false;
        break;
      fi;
    od;
    if suffix then
      return rule[1]{[1 .. Length(rule[1]) - Length(word)]} = rule[2];
    fi;
    return false;
  end;

  for rule in rules do
    # only include non-redundant rules
    if (Length(rule[1]) <> 2
        or (rule[1][1] <> pos and rule[1][Length(rule[1])] <> pos))
        and (not is_redundant(rule)) then
      Add(rels, [convert(rule[1]), convert(rule[2])]);
    fi;
  od;

  Q := F / rels;

  if sgens = mgens then
    map := x -> EvaluateWord(GeneratorsOfMonoid(Q),
                             Factorization(S, x));
  else
    map := x -> EvaluateWord(GeneratorsOfSemigroup(Q),
                             Factorization(S, x));
  fi;

  inv := function(x)
    if not IsOne(UnderlyingElement(x)) then
      return MappedWord(UnderlyingElement(x), A, mgens);
    fi;
    return MultiplicativeNeutralElement(S);
  end;

  return SemigroupIsomorphismByFunctionNC(S, Q, map, inv);
end);

InstallMethod(AssignGeneratorVariables, "for a free semigroup",
[IsFreeSemigroup],
function(S)
  DoAssignGenVars(GeneratorsOfSemigroup(S));
end);

InstallMethod(AssignGeneratorVariables, "for an free monoid",
[IsFreeMonoid],
function(S)
  DoAssignGenVars(GeneratorsOfMonoid(S));
end);

InstallMethod(AssignGeneratorVariables, "for an fp semigroup",
[IsFpSemigroup],
function(S)
  DoAssignGenVars(GeneratorsOfSemigroup(S));
end);

InstallMethod(AssignGeneratorVariables, "for an fp monoid",
[IsFpMonoid],
function(S)
  DoAssignGenVars(GeneratorsOfMonoid(S));
end);

InstallMethod(IsomorphismFpSemigroup, "for a group",
[IsGroup],
function(G)
  local iso1, inv1, iso2, inv2;
  # The next clause shouldn't be required, but for some reason in GAP 4.10 the
  # rank of the method for IsomorphismFpMonoid for IsFpGroup is lower than this
  # methods rank.
  if IsFpGroup(G) then
    TryNextMethod();
  fi;

  iso1 := IsomorphismFpGroup(G);
  inv1 := InverseGeneralMapping(iso1);
  # TODO(later) the method for IsomorphismFpSemigroup uses the generators of G
  # and their inverses, since we know that G is finite this could be avoided.
  iso2 := IsomorphismFpSemigroup(Range(iso1));
  inv2 := InverseGeneralMapping(iso2);

  return SemigroupIsomorphismByFunctionNC(G,
                                          Range(iso2),
                                          x -> (x ^ iso1) ^ iso2,
                                          x -> (x ^ inv2) ^ inv1);
end);

InstallMethod(IsomorphismFpSemigroup, "for a free semigroup",
[IsFreeSemigroup],
function(S)
  local T;
  T := S / [];
  return SemigroupIsomorphismByImagesNC(S,
                                        T,
                                        GeneratorsOfSemigroup(S),
                                        GeneratorsOfSemigroup(T));
end);

InstallMethod(IsomorphismFpMonoid, "for a free monoid",
[IsFreeMonoid],
function(S)
  local T;
  T := S / [];
  return SemigroupIsomorphismByImagesNC(S,
                                        T,
                                        GeneratorsOfMonoid(S),
                                        GeneratorsOfMonoid(T));
end);

InstallMethod(IsomorphismFpSemigroup, "for a free monoid",
[IsFreeMonoid],
function(S)
  local map1, map2;
  map1 := IsomorphismFpMonoid(S);
  map2 := IsomorphismFpSemigroup(Range(map1));
  return CompositionMapping(map2, map1);
end);

InstallMethod(IsomorphismFpSemigroup, "for an fp semigroup",
[IsFpSemigroup],
function(S)
  return SemigroupIsomorphismByImagesNC(S,
                                        S,
                                        GeneratorsOfSemigroup(S),
                                        GeneratorsOfSemigroup(S));
end);

InstallMethod(IsomorphismFpMonoid, "for an fp monoid",
[IsFpMonoid],
function(S)
  return SemigroupIsomorphismByImagesNC(S,
                                        S,
                                        GeneratorsOfSemigroup(S),
                                        GeneratorsOfSemigroup(S));
end);

# The next method is copied directly from the GAP library the only change is
# the return value which uses SemigroupIsomorphismByFunctionNC here but
# MagmaIsomorphismByFunctionsNC in the GAP library; comments are also removed
# and other superficial changes to adhere to Semigroups package conventions.

InstallMethod(IsomorphismFpSemigroup, "for an fp group", [IsFpGroup],
function(G)
  local freegp, gensfreegp, freesmg, gensfreesmg, idgen, newrels, rels, smgrel,
  semi, gens, isomfun, id, invfun, i, rel;

  freegp := FreeGroupOfFpGroup(G);

  gensfreegp := List(GeneratorsOfSemigroup(freegp), String);
  freesmg := FreeSemigroup(gensfreegp{[1 .. Length(gensfreegp)]});

  gensfreesmg := GeneratorsOfSemigroup(freesmg);
  idgen := gensfreesmg[1];

  newrels := [[idgen * idgen, idgen]];
  for i in [2 .. Length(gensfreesmg)] do
    Add(newrels, [idgen * gensfreesmg[i], gensfreesmg[i]]);
    Add(newrels, [gensfreesmg[i] * idgen, gensfreesmg[i]]);
  od;

  # then relations gens * gens ^ -1 = idgen (and the other way around)
  for i in [2 .. Length(gensfreesmg)] do
    if IsOddInt(i) then
      Add(newrels, [gensfreesmg[i] * gensfreesmg[i - 1], idgen]);
    else
      Add(newrels, [gensfreesmg[i] * gensfreesmg[i + 1], idgen]);
    fi;
  od;

  rels := RelatorsOfFpGroup(G);
  for rel in rels do
     smgrel := [Gpword2MSword(idgen, rel, 1), idgen];
     Add(newrels, smgrel);
  od;

  # finally create the fp semigroup
  semi := FactorFreeSemigroupByRelations(freesmg, newrels);
  gens := GeneratorsOfSemigroup(semi);

  isomfun := x -> ElementOfFpSemigroup(FamilyObj(gens[1]),
                  Gpword2MSword(idgen, UnderlyingElement(x), 1));

  id := One(freegp);
  invfun := x -> ElementOfFpGroup(FamilyObj(One(G)),
              MSword2gpword(id, UnderlyingElement(x), 1));

  return SemigroupIsomorphismByFunctionNC(G, semi, isomfun, invfun);
end);

# The next method is copied directly from the GAP library the only change is
# the return value which uses SemigroupIsomorphismByFunctionNC here but
# MagmaIsomorphismByFunctionsNC in the GAP library; comments are also removed
# and other superficial changes to adhere to Semigroups package conventions.

InstallMethod(IsomorphismFpMonoid, "for an fp group", [IsFpGroup],
function(G)
  local freegp, gens, mongens, s, t, p, freemon, gensmon, id, newrels, rels, w,
  monrel, mon, monfam, isomfun, idg, invfun, hom, i, j, rel;

  freegp := FreeGroupOfFpGroup(G);
  gens := GeneratorsOfGroup(G);

  mongens := [];
  for i in gens do
    s := String(i);
    Add(mongens, s);
    if ForAll(s, x -> x in CHARS_UALPHA or x in CHARS_LALPHA) then
      # inverse: change casification
      t := "";
      for j in [1 .. Length(s)] do
        p := Position(CHARS_LALPHA, s[j]);
        if p <> fail then
          Add(t, CHARS_UALPHA[p]);
        else
          p := Position(CHARS_UALPHA, s[j]);
          Add(t, CHARS_LALPHA[p]);
        fi;
      od;
      s := t;
    else
      s := Concatenation(s, "^-1");
    fi;
    Add(mongens, s);
  od;

  freemon := FreeMonoid(mongens);
  gensmon := GeneratorsOfMonoid(freemon);
  id := Identity(freemon);
  newrels := [];
  # inverse relators
  for i in [1 .. Length(gens)] do
    Add(newrels, [gensmon[2 * i - 1] * gensmon[2 * i], id]);
    Add(newrels, [gensmon[2 * i] * gensmon[2 * i - 1], id]);
  od;

  rels := ValueOption("relations");
  if rels = fail then
    rels := RelatorsOfFpGroup(G);
    for rel in rels do
      w := rel;
      w := GroupwordToMonword(id, w);
      monrel := [w, id];
      Add(newrels, monrel);
    od;
  else
    if not ForAll(Flat(rels), x -> x in FreeGroupOfFpGroup(G)) then
      Info(InfoFpGroup, 1, "Converting relation words into free group");
      rels := List(rels, i -> List(i, UnderlyingElement));
    fi;
    for rel in rels do
      Add(newrels, List(rel, x -> GroupwordToMonword(id, x)));
    od;
  fi;

  mon := FactorFreeMonoidByRelations(freemon, newrels);
  gens := GeneratorsOfMonoid(mon);
  monfam := FamilyObj(Representative(mon));

  isomfun := x -> ElementOfFpMonoid(monfam,
                  GroupwordToMonword(id, UnderlyingElement(x)));

  idg := One(freegp);
  invfun := x -> ElementOfFpGroup(FamilyObj(One(G)),
     MonwordToGroupword(idg, UnderlyingElement(x)));
  hom := SemigroupIsomorphismByFunctionNC(G, mon, isomfun, invfun);
  hom!.type := 1;
  if not HasIsomorphismFpMonoid(G) then
    SetIsomorphismFpMonoid(G, hom);
  fi;
  return hom;
end);

# The next method is copied directly from the GAP library the only change is
# the return value which uses SemigroupIsomorphismByFunctionNC here but
# MagmaIsomorphismByFunctionsNC in the GAP library; comments are also removed
# and other superficial changes to adhere to Semigroups package conventions.

InstallMethod(IsomorphismFpSemigroup, "for an fp monoid", [IsFpMonoid],
function(M)
  local AddToExtRep, FMtoFS, FStoFM, FM, FS, id, rels, next, S, map, inv, x,
  rel;

  AddToExtRep := function(w, id, val)
    local wlist, i;

    wlist := ExtRepOfObj(w);
    wlist := ShallowCopy(wlist);
    for i in [1 .. 1 / 2 * (Length(wlist))] do
      wlist[2 * i - 1] := wlist[2 * i - 1] + val;
    od;

    return ObjByExtRep(FamilyObj(id), wlist);
  end;

  FMtoFS := function(id, w)
    if IsOne(w) then
      return id;
    fi;
    return AddToExtRep(w, id, 1);
  end;

  FStoFM := function(id, w)
    if ExtRepOfObj(w) = [1, 1] then
      return id;
    fi;
    return AddToExtRep(w, id, -1);
  end;

  FM := FreeMonoidOfFpMonoid(M);
  FS := FreeSemigroup(List(GeneratorsOfSemigroup(FM), String));

  id := FS.(Position(GeneratorsOfSemigroup(FM), One(FM)));

  rels := [[id * id, id]];
  for x in GeneratorsOfSemigroup(FS) do
    if x <> id then
      Add(rels, [id * x, x]);
      Add(rels, [x * id, x]);
    fi;
  od;

  for rel in RelationsOfFpMonoid(M) do
    next := [FMtoFS(id, rel[1]), FMtoFS(id, rel[2])];
    Add(rels, next);
  od;

  S := FS / rels;

  map := x -> ElementOfFpSemigroup(FamilyObj(S.1),
                                   FMtoFS(id, UnderlyingElement(x)));

  inv := x -> Image(NaturalHomomorphismByGenerators(FM, M),
                    FStoFM(One(FM), UnderlyingElement(x)));

  return SemigroupIsomorphismByFunctionNC(M, S, map, inv);
end);

InstallMethod(IsomorphismFpMonoid, "for a group", [IsGroup],
function(G)
  local iso1, inv1, iso2, inv2;
  # The next clause shouldn't be required, but for some reason in GAP 4.10 the
  # rank of the method for IsomorphismFpMonoid for IsFpGroup is lower than this
  # methods rank.
  if IsFpGroup(G) then
    TryNextMethod();
  fi;
  iso1 := IsomorphismFpGroup(G);
  inv1 := InverseGeneralMapping(iso1);
  # TODO(later) the method for IsomorphismFpMonoid uses the generators of G and
  # their inverses, since we know that G is finite this could be avoided.
  iso2 := IsomorphismFpMonoid(Range(iso1));
  inv2 := InverseGeneralMapping(iso2);

  return SemigroupIsomorphismByFunctionNC(G,
                                          Range(iso2),
                                          x -> (x ^ iso1) ^ iso2,
                                          x -> (x ^ inv2) ^ inv1);
end);

SEMIGROUPS.ExtRepObjToWord := function(ext_rep_obj)
  local n, word, val, pow, i;
  n    := Length(ext_rep_obj);
  word := [];
  for i in [1, 3 .. n - 1] do
    val := ext_rep_obj[i];
    pow := ext_rep_obj[i + 1];
    while pow > 0 do
      Add(word, val);
      pow := pow - 1;
    od;
  od;
  return word;
end;

SEMIGROUPS.WordToExtRepObj := function(word)
  local ext_rep_obj, i, j;
  ext_rep_obj := [];
  i           := 1;
  j           := 1;

  while i <= Length(word) do
    Add(ext_rep_obj, word[i]);
    Add(ext_rep_obj, 1);
    i := i + 1;
    while i <= Length(word) and word[i] = ext_rep_obj[j] do
      ext_rep_obj[j + 1] := ext_rep_obj[j + 1] + 1;
      i := i + 1;
    od;
    j := j + 2;
  od;
  return ext_rep_obj;
end;

SEMIGROUPS.ExtRepObjToString := function(ext_rep_obj)
  local alphabet, out, i;
  alphabet := "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ";
  out := "";
  for i in [1, 3 .. Length(ext_rep_obj) - 1] do
    if ext_rep_obj[i] > Length(alphabet) then
      ErrorNoReturn("the maximum value in an odd position of the ",
                    "argument must be at most ", Length(alphabet));
    fi;
    Add(out, alphabet[ext_rep_obj[i]]);
    if ext_rep_obj[i + 1] > 1 then
      Append(out, " ^ ");
      Append(out, String(ext_rep_obj[i + 1]));
    fi;
  od;
  return out;
end;

SEMIGROUPS.WordToString := function(word)
  local alphabet, out, letter;
  alphabet := "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ";
  out := "";
  for letter in word do
    if letter > Length(alphabet) then
      ErrorNoReturn("the argument be at most ", Length(alphabet));
    fi;
    Add(out, alphabet[letter]);
  od;
  return out;
end;

# This method is based on the following paper
# Presentations of Factorizable Inverse Monoids
# David Easdown, James East, and D. G. FitzGerald
# July 19, 2004
InstallMethod(IsomorphismFpSemigroup,
"for an inverse partial perm semigroup",
[IsPartialPermSemigroup and IsInverseActingSemigroupRep],
function(M)
  local add_to_odd_positions, S, SS, G, GG, s, g, F, rels, fam, alpha,
  beta, lhs, rhs, map, H, o, comp, U, rhs_list, conj, MF, T, inv, rel, x, y, m,
  i;

  if not IsFactorisableInverseMonoid(M) then
    TryNextMethod();
  fi;

  add_to_odd_positions := function(list, s)
    list{[1, 3 .. Length(list) - 1]} := list{[1, 3 .. Length(list) - 1]} + s;
    return list;
  end;

  S := Semigroup(IdempotentGeneratedSubsemigroup(M));
  SS := GeneratorsOfSemigroup(S);
  G := GroupOfUnits(M);
  GG := GeneratorsOfSemigroup(G);
  s := Length(GeneratorsOfSemigroup(S));
  g := Length(GeneratorsOfSemigroup(G));

  F := FreeSemigroup(s + g);
  rels := [];
  fam := ElementsFamily(FamilyObj(F));

  # R_S - semigroup relations for the idempotent generated subsemigroup
  alpha := IsomorphismFpSemigroup(S);
  for rel in RelationsOfFpSemigroup(Image(alpha)) do
    Add(rels, [ObjByExtRep(fam, ExtRepOfObj(rel[1])),
               ObjByExtRep(fam, ExtRepOfObj(rel[2]))]);
  od;

  # R_G - semigroup relations for the group of units
  beta  := IsomorphismFpSemigroup(G);
  for rel in RelationsOfFpSemigroup(Image(beta)) do
    lhs := add_to_odd_positions(ShallowCopy(ExtRepOfObj(rel[1])), s);
    rhs := add_to_odd_positions(ShallowCopy(ExtRepOfObj(rel[2])), s);
    Add(rels, [ObjByExtRep(fam, lhs), ObjByExtRep(fam, rhs)]);
  od;

  # R_product - see page 4 of the paper
  for x in [1 .. s] do
    for y in [1 .. g] do
      rhs := Factorization(S, SS[x] ^ (GG[y] ^ -1));
      Add(rels, [F.(s + y) * F.(x),
                 EvaluateWord(GeneratorsOfSemigroup(F), rhs) * F.(s + y)]);
    od;
  od;

  map := InverseGeneralMapping(IsomorphismPermGroup(G));
  H   := Source(map);
  o   := Enumerate(LambdaOrb(M));
  # R_tilde - see page 4 of the paper
  for m in [2 .. Length(OrbSCC(o))] do
    comp := OrbSCC(o)[m];
    U := SmallGeneratingSet(Stabilizer(H,
                                       PartialPerm(o[comp[1]], o[comp[1]]),
                                       OnRight));

    for i in comp do
      rhs_list := Factorization(S, PartialPerm(o[i], o[i]));
      rhs := EvaluateWord(GeneratorsOfSemigroup(F), rhs_list);
      conj := MappingPermListList(o[comp[1]], o[i]);
      for x in List(U, x -> x ^ conj) do
        lhs := ShallowCopy(rhs_list);
        Append(lhs, Factorization(G, x ^ map) + s);
        Add(rels, [EvaluateWord(GeneratorsOfSemigroup(F), lhs), rhs]);
      od;
    od;
  od;

  # Relation to identify One(G) and One(S)
  Add(rels, [EvaluateWord(GeneratorsOfSemigroup(F),
                          Factorization(G, One(G)) + s),
             EvaluateWord(GeneratorsOfSemigroup(F),
                          Factorization(S, One(S)))]);

  MF := F / rels;  # FpSemigroup which is isomorphic to M, with different gens.
  fam := ElementsFamily(FamilyObj(MF));
  T := Semigroup(Concatenation(SS, GG));  # M with isomorphic generators to MF
  map := x -> ElementOfFpSemigroup(fam, EvaluateWord(GeneratorsOfSemigroup(F),
                                                     Factorization(T, x)));
  inv := x -> EvaluateWord(GeneratorsOfSemigroup(T),
                           SEMIGROUPS.ExtRepObjToWord(ExtRepOfObj(x)));

  return SemigroupIsomorphismByFunctionNC(M, MF, map, inv);
end);

InstallMethod(ParseRelations,
"for a list of free generators and a string",
[IsDenseList, IsString],
function(gens, inputstring)
    local newinputstring, g, chartoel, RemoveBrackets, ParseRelation, output,
    chars;

    for g in gens do
      g := String(g);
      if Size(g) <> 1 or not IsAlphaChar(g[1]) then
        ErrorNoReturn(
        "expected the 1st argument to be a list of a free semigroup or monoid ",
        "generators represented by a single alphabet letter but found ",
        String(g));
      fi;
    od;

    newinputstring := Filtered(inputstring, x -> x <> ' ');
    chars := List(gens, x -> String(x)[1]);
    if PositionSublist(newinputstring, "=1") <> fail then
      Add(chars, '1');
    fi;

    for g in chars do
      newinputstring := ReplacedString(newinputstring,
                                       [g, '^'],
                                       ['(', g, ')', '^']);
      newinputstring := ReplacedString(newinputstring,
                                       Concatenation(['(', g, ')'], "^1="),
                                       ['(', g, ')', '=']);
      newinputstring := ReplacedString(newinputstring,
                                       Concatenation(['(', g, ')'], "^1)"),
                                       ['(', g, ')', ')']);
      newinputstring := ReplacedString(newinputstring,
                                       Concatenation(['(', g, ')'], "^1("),
                                       ['(', g, ')', '(']);

    od;

    RemoveBrackets := function(word)
        local i, product, lbracket, rbracket, nestcount, index, p, chartoel;
        if word = "" then
            ErrorNoReturn("expected the 2nd argument to be",
                          " a string listing the relations of a semigroup",
                          " but found an = symbol which isn't pairing two",
                          " words");
        fi;

        # if the number of left brackets is different from the number of right
        # brackets they can't possibly pair up
        if Number(word, x -> x = '(') <> Number(word, x -> x = ')') then
            ErrorNoReturn("expected the number of open brackets",
                          " to match the number of closed brackets");
        fi;

        # if the ^ is at the end of the string there is no exponent.
        # if the ^ is at the start of the string there is no base.
        if word[1] = '^' then
            ErrorNoReturn("expected ^ to be preceded by a ) or",
                          " a generator but found beginning of string");
        elif word[Size(word)] = '^' then
            ErrorNoReturn("expected ^ to be followed by a ",
                          "positive integer but found end of string");
        fi;
        # checks that all ^s have an exponent.
        for index in [1 .. Size(word)] do
            if word[index] = '^' then
                if not word[index + 1] in "0123456789" then
                  ErrorNoReturn("expected ^ to be followed by",
                  " a positive integer but found ", [word[index + 1]]);
                fi;
                if word[index - 1] in "0123456789^(" then
                  ErrorNoReturn(
                  "expected ^ to be preceded by a ) or a generator",
                  " but found ", [word[index - 1]]);
                fi;
            fi;
        od;

        # converts a character to the element it represents
        chartoel := function(char)
            local i;
            for i in [1 .. Size(gens)] do
                if char = String(gens[i])[1] then
                    return gens[i];
                fi;
            od;
            if char = '1' and IsAssocWordWithOne(gens[1]) then
              return One(gens);
            fi;
            ErrorNoReturn("expected a free semigroup generator",
                          " but found ", [char]);
        end;

        # i acts as a pointer to positions in the string.
        product := "";
        i := 1;
        while i <= Size(word) do
            # if there are no brackets the character is left as it is.
            if not word[i] = '(' then
                if product = "" then
                  product := chartoel(word[i]);
                else
                  product := product * chartoel(word[i]);
                fi;
            else
                lbracket := i;
                rbracket := -1;
                # tracks how 'deep' the position of i is in terms of nested
                # brackets
                nestcount := 0;
                i := i + 1;
                while i <= Size(word) do
                    if word[i] = '(' then
                        nestcount := nestcount + 1;
                    elif word[i] = ')' then
                        if nestcount = 0 then
                            rbracket := i;
                            break;
                        else
                            nestcount := nestcount - 1;
                        fi;
                    fi;
                    i := i + 1;
                od;
                # if rbracket is not followed by ^ then the value inside the
                # bracket is appended (recursion is used to remove any brackets
                # in this value)
                if rbracket = Size(word) or (not word[rbracket + 1] = '^') then
                    if product = "" then
                      product := RemoveBrackets(
                                 word{[lbracket + 1 .. rbracket - 1]});
                    else
                      product := product *
                                 RemoveBrackets(
                                 word{[lbracket + 1 .. rbracket - 1]});
                    fi;
                # if rbracket is followed by ^ then the value inside the
                # bracket is appended the given number of time
                else
                    i := i + 2;
                    while i <= Size(word) do
                        if word[i] in "0123456789" then
                            i := i + 1;
                        else
                            break;
                        fi;
                    od;

                    p := Int(word{[rbracket + 2 .. i - 1]});
                    if p = 0 then
                      ErrorNoReturn("expected ^ to be followed",
                                    " by a positive integer but found 0");
                    fi;
                    if product = "" then
                       product := RemoveBrackets(word{[lbracket + 1 ..
                                                       rbracket - 1]}) ^ p;
                    else
                       product := product *
                                  RemoveBrackets(word{[lbracket + 1 ..
                                                       rbracket - 1]}) ^ p;
                    fi;
                    i := i - 1;
                fi;
            fi;
            i := i + 1;
        od;
        return product;
    end;

    ParseRelation := x -> List(SplitString(x, "="), RemoveBrackets);
    output := List(SplitString(newinputstring, ","), ParseRelation);
    if ForAny(output, x -> Size(x) = 1) then
      ErrorNoReturn("expected the 2nd argument to be",
                    " a string listing the relations of a semigroup",
                    " but found an = symbol which isn't pairing two",
                    " words");
    fi;
    output := Filtered(output, x -> Size(x) >= 2);
    output := List(output,
                   x -> List([1 .. Size(x) - 1], y -> [x[y], x[y + 1]]));
    return Concatenation(output);
end);

InstallMethod(Factorization, "for an fp semigroup and element",
IsCollsElms, [IsFpSemigroup, IsElementOfFpSemigroup],
{S, x} -> SEMIGROUPS.ExtRepObjToWord(ExtRepOfObj(x)));

# Returns a factorization of the semigroup generators of S, not the monoid
# generators !!!
InstallMethod(Factorization, "for an fp monoid and element",
IsCollsElms, [IsFpMonoid, IsElementOfFpMonoid],
function(_, x)
  local y;
  y := ExtRepOfObj(x);
  if IsEmpty(y) then
    return [1];
  else
    return SEMIGROUPS.ExtRepObjToWord(y) + 1;
  fi;
end);

InstallMethod(Factorization, "for a free semigroup and word",
[IsFreeSemigroup, IsWord],
{S, x} -> SEMIGROUPS.ExtRepObjToWord(ExtRepOfObj(x)));

InstallMethod(MinimalFactorization, "for a free semigroup and word",
[IsFreeSemigroup, IsWord], Factorization);

# Returns a factorization of the semigroup generators of S, not the monoid
# generators !!!
InstallMethod(Factorization, "for a free monoid and word",
[IsFreeMonoid, IsWord],
function(_, x)
  if IsOne(x) then
    return [1];
  else
    return SEMIGROUPS.ExtRepObjToWord(ExtRepOfObj(x)) + 1;
  fi;
end);

InstallMethod(MinimalFactorization, "for a free monoid and word",
[IsFreeMonoid, IsWord], Factorization);

InstallMethod(Length, "for an fp semigroup", [IsFpSemigroup],
function(S)
  return Length(GeneratorsOfSemigroup(S))
    + Sum(RelationsOfFpSemigroup(S), x -> Length(x[1]) + Length(x[2]));
end);

InstallMethod(Length, "for an fp monoid", [IsFpMonoid],
function(S)
  return Length(GeneratorsOfMonoid(S))
    + Sum(RelationsOfFpMonoid(S), x -> Length(x[1]) + Length(x[2]));
end);

InstallMethod(ReversedOp, "for an element of an fp semigroup",
[IsElementOfFpSemigroup],
function(word)
  local rev;
  rev := Reversed(UnderlyingElement(word));
  return ElementOfFpSemigroup(FamilyObj(word), rev);
end);

InstallMethod(ReversedOp, "for an element of an fp monoid",
[IsElementOfFpMonoid],
function(word)
  local rev;
  rev := Reversed(UnderlyingElement(word));
  return ElementOfFpMonoid(FamilyObj(word), rev);
end);

InstallMethod(EmbeddingFpMonoid, "for an fp semigroup",
[IsFpSemigroup],
function(S)
  local F, R, map, T, hom, rel;

  if HasIsMonoidAsSemigroup(S) and IsMonoidAsSemigroup(S) then
    return IsomorphismFpMonoid(S);
  fi;

  F := FreeSemigroupOfFpSemigroup(S);
  F := FreeMonoid(List(GeneratorsOfSemigroup(F), String));
  R := [];

  map := x -> ObjByExtRep(ElementsFamily(FamilyObj(F)), ExtRepOfObj(x));

  for rel in RelationsOfFpSemigroup(S) do
    Add(R, [map(rel[1]), map(rel[2])]);
  od;

  T := F / R;
  hom := SemigroupHomomorphismByImages_NC(S,
                                          T,
                                          GeneratorsOfSemigroup(S),
                                          GeneratorsOfMonoid(T));
  SetIsInjective(hom, true);
  return hom;
end);
