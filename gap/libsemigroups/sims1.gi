###########################################################################
##
##  libsemigroups/sims1.gi
##  Copyright (C) 2022                                   James D. Mitchell
##
##  Licensing information can be found in the README file of this package.
##
#############################################################################
##

DeclareOperation("LibsemigroupsSims1",
                 [IsSemigroup, IsPosInt, IsList, IsString]);

InstallMethod(LibsemigroupsSims1,
[IsSemigroup, IsPosInt, IsList, IsString],
function(S, n, extra, kind)
  local P, rules, sims1, Q, pair, r;

  Assert(1,
         CanUseFroidurePin(S)
         or IsFpSemigroup(S)
         or IsFpMonoid(S)
         or (HasIsFreeSemigroup(S) and IsFreeSemigroup(S))
         or (HasIsFreeMonoid(S) and IsFreeMonoid(S)));

  Assert(1, IsEmpty(extra) or IsMultiplicativeElementCollColl(extra));

  Assert(1, kind in ["left", "right"]);

  if IsFpSemigroup(S) then
    rules := List(RelationsOfFpSemigroup(S),
                  r -> List(r,
                            x -> SEMIGROUPS.ExtRepObjToWord(ExtRepOfObj(x))));
  elif IsFpMonoid(S) then
    rules := List(RelationsOfFpMonoid(S),
                  r -> List(r,
                            x -> SEMIGROUPS.ExtRepObjToWord(ExtRepOfObj(x))));
  elif (HasIsFreeSemigroup(S) and IsFreeSemigroup(S))
      or (HasIsFreeMonoid(S) and IsFreeMonoid(S)) then
    rules := [];
  else
    Assert(1, CanUseFroidurePin(S));
    rules := RulesOfSemigroup(S);
  fi;

  P := libsemigroups.Presentation.make();
  for r in rules do
    libsemigroups.presentation_add_rule(P, r[1] - 1, r[2] - 1);
  od;

  if not IsEmpty(rules) then
    libsemigroups.Presentation.alphabet_from_rules(P);
  elif (HasIsFreeMonoid(S) and IsFreeMonoid(S)) or IsFpMonoid(S) then
    libsemigroups.Presentation.set_alphabet(
      P, [0 .. Size(GeneratorsOfMonoid(S)) - 1]);
  elif (HasIsFreeSemigroup(S) and IsFreeSemigroup(S)) or IsFpSemigroup(S) then
    libsemigroups.Presentation.set_alphabet(
      P, [0 .. Size(GeneratorsOfSemigroup(S)) - 1]);
  fi;
  libsemigroups.Presentation.validate(P);
  # RulesOfSemigroup always returns the rules of an isomorphic fp semigroup
  libsemigroups.Presentation.contains_empty_word(
    P, IsFpMonoid(S) or (HasIsFreeMonoid(S) and IsFreeMonoid(S)));

  sims1 := libsemigroups.Sims1.make(kind);
  libsemigroups.Sims1.short_rules(sims1, P);

  if not IsEmpty(extra) then
    Q := libsemigroups.Presentation.make();
    libsemigroups.Presentation.contains_empty_word(Q, IsMonoid(S));
    libsemigroups.Presentation.set_alphabet(Q,
      libsemigroups.Presentation.alphabet(P));

    for pair in extra do
      libsemigroups.presentation_add_rule(
        Q,
        MinimalFactorization(S, pair[1]) - 1,
        MinimalFactorization(S, pair[2]) - 1);
    od;
    libsemigroups.Presentation.validate(Q);
    libsemigroups.Sims1.extra(sims1, Q);
  fi;
  if n > 64 and libsemigroups.hardware_concurrency() > 2 then
    libsemigroups.Sims1.number_of_threads(
      sims1, libsemigroups.hardware_concurrency() - 2);
  fi;
  return sims1;
end);

BindGlobal("_CheckExtraPairs", function(S, extra)
  local pair;
  for pair in extra do
    if not (IsList(pair) and Length(pair) = 2) then
      ErrorNoReturn("the 3rd argument (a list) must consist of ",
                    "lists of length 2");
    elif not pair[1] in S or not pair[2] in S then
      ErrorNoReturn("the 3rd argument (a list of length 2) must consist ",
                    "of pairs of elements of the 1st argument (a semigroup)");
    fi;
  od;
end);

InstallMethod(NumberOfRightCongruences, "for a semigroup", [IsSemigroup],
S -> NumberOfRightCongruences(S, Size(S), []));

InstallMethod(NumberOfLeftCongruences, "for a semigroup", [IsSemigroup],
S -> NumberOfLeftCongruences(S, Size(S), []));

InstallMethod(NumberOfRightCongruences,
"for a semigroup and positive integer",
[IsSemigroup, IsPosInt],
{S, n} -> NumberOfRightCongruences(S, n, []));

InstallMethod(NumberOfLeftCongruences,
"for a semigroup and positive integer",
[IsSemigroup, IsPosInt],
{S, n} -> NumberOfLeftCongruences(S, n, []));

InstallMethod(NumberOfRightCongruences,
"for a semigroup, pos. int., and list ",
[IsSemigroup, IsPosInt, IsList],
function(S, n, extra)
  local sims1;
  _CheckExtraPairs(S, extra);
  if HasRightCongruencesOfSemigroup(S) then
    return Number(RightCongruencesOfSemigroup(S),
                  x -> NrEquivalenceClasses(x) <= n
                       and ForAll(extra, y -> y in x));
  elif not (CanUseFroidurePin(S) or IsFpSemigroup(S) or IsFpMonoid(S)
      or (HasIsFreeSemigroup(S) and IsFreeSemigroup(S))
      or (HasIsFreeMonoid(S) and IsFreeMonoid(S))) then
    TryNextMethod();
  fi;
  sims1 := LibsemigroupsSims1(S, n, extra, "right");
  return libsemigroups.Sims1.number_of_congruences(sims1, n);
end);

InstallMethod(NumberOfLeftCongruences,
"for a semigroup, pos. int., and list",
[IsSemigroup, IsPosInt, IsList],
function(S, n, extra)
  local sims1;
  _CheckExtraPairs(S, extra);
  if HasLeftCongruencesOfSemigroup(S) then
    return Number(LeftCongruencesOfSemigroup(S),
                  x -> NrEquivalenceClasses(x) <= n
                       and ForAll(extra, y -> y in x));
  elif not (CanUseFroidurePin(S) or IsFpSemigroup(S) or IsFpMonoid(S)
      or (HasIsFreeSemigroup(S) and IsFreeSemigroup(S))
      or (HasIsFreeMonoid(S) and IsFreeMonoid(S))) then
    TryNextMethod();
  fi;

  sims1 := LibsemigroupsSims1(S, n, extra, "left");
  return libsemigroups.Sims1.number_of_congruences(sims1, n);
end);

InstallMethod(SmallerDegreeTransformationRepresentation,
"for semigroup with CanUseFroidurePin",
[IsSemigroup and CanUseFroidurePin],
function(S)
  local map1, map2;
  map1 := IsomorphismFpSemigroup(S);
  map2 := SmallerDegreeTransformationRepresentation(Range(map1));
  return CompositionMapping(map2, map1);
end);

InstallMethod(SmallerDegreeTransformationRepresentation,
"for an fp semigroup", [IsFpSemigroup],
function(S)
  local P, ro, map, max, D, deg, imgs, pts, r, j, i;

  if not IsFinite(S) then
    ErrorNoReturn("the argument (an fp semigroup) must be finite");
  fi;

  P := libsemigroups.Presentation.make();
  for r in RelationsOfFpSemigroup(S) do
    r := List(r, x -> SEMIGROUPS.ExtRepObjToWord(ExtRepOfObj(x)));
    libsemigroups.presentation_add_rule(P, r[1] - 1, r[2] - 1);
  od;

  libsemigroups.Presentation.alphabet_from_rules(P);
  # FIXME libsemigroups.Presentation.contains_empty_word(P, true);
  libsemigroups.Presentation.validate(P);

  ro := libsemigroups.RepOrc.make();
  libsemigroups.RepOrc.short_rules(ro, P);
  libsemigroups.RepOrc.min_nodes(ro, 1);
  if HasIsomorphismTransformationSemigroup(S)
      or IsTransformationSemigroup(S) then
    map := IsomorphismTransformationSemigroup(S);
    max := DegreeOfTransformationSemigroup(Range(map)) - 1;
  else
    max := Size(S);
  fi;

  libsemigroups.RepOrc.max_nodes(ro, max);
  libsemigroups.RepOrc.target_size(ro, Size(S));
  if Size(S) > 64 and libsemigroups.hardware_concurrency() > 2 then
    libsemigroups.RepOrc.number_of_threads(
      ro, libsemigroups.hardware_concurrency() - 2);
  fi;

  D := libsemigroups.RepOrc.digraph(ro);
  deg := Length(D);

  if deg = 0 then
    # Should only occur if HasIsomorphismTransformationSemigroup since
    # otherwise we'll always find the right regular representation eventually.
    return IsomorphismTransformationSemigroup(S);
  fi;

  imgs := [];
  for j in [1 .. Length(GeneratorsOfSemigroup(S))] do
    pts := [1 .. deg];
    for i in pts do
      pts[i] := D[i][j];
    od;
    Add(imgs, TransformationNC(pts));
  od;
  return SemigroupIsomorphismByImagesNC(S,
                                        Semigroup(imgs),
                                        GeneratorsOfSemigroup(S),
                                        imgs);
end);

BindGlobal("NextIterator_Sims1", function(iter)
  local result;
  result := libsemigroups.Sims1Iterator.deref(iter!.it);
  libsemigroups.Sims1Iterator.increment(iter!.it);
  if IsEmpty(result) then
    return fail;
  fi;
  result := Filtered(result, x -> not IsEmpty(x));
  result := DigraphNC(result);
  SetFilterObj(result, IsWordGraph);
  return iter!.construct(result);
end);

InstallMethod(IteratorOfRightCongruences,
"for a semigroup, pos. int., list or coll.",
[IsSemigroup, IsPosInt, IsListOrCollection],
function(S, n, extra)
  local sims1, iter;
  _CheckExtraPairs(S, extra);
  if HasRightCongruencesOfSemigroup(S) then
    return IteratorFiniteList(Filtered(RightCongruencesOfSemigroup(S),
                    x -> NrEquivalenceClasses(x) <= n
                    and ForAll(extra, y -> y in x)));
  elif not (CanUseFroidurePin(S) or IsFpSemigroup(S) or IsFpMonoid(S)
      or (HasIsFreeSemigroup(S) and IsFreeSemigroup(S))
      or (HasIsFreeMonoid(S) and IsFreeMonoid(S))) then
    TryNextMethod();
  fi;
  sims1 := LibsemigroupsSims1(S, n, extra, "right");

  iter := rec(it := libsemigroups.Sims1.cbegin(sims1, n),
              construct := x -> RightCongruenceByWordGraphNC(S, x));

  iter.NextIterator := NextIterator_Sims1;
  iter.ShallowCopy := x -> rec(it := libsemigroups.Sims1.cbegin(sims1, n),
                               construct :=
                                 x -> RightCongruenceByWordGraphNC(S, x));
  return IteratorByNextIterator(iter);
end);

InstallMethod(IteratorOfLeftCongruences,
"for CanUseFroidurePin, pos. int., list or coll.",
[IsSemigroup and CanUseFroidurePin, IsPosInt, IsListOrCollection],
function(S, n, extra)
  local sims1, iter;
  _CheckExtraPairs(S, extra);
  if HasLeftCongruencesOfSemigroup(S) then
    return IteratorFiniteList(Filtered(LeftCongruencesOfSemigroup(S),
                    x -> NrEquivalenceClasses(x) <= n
                    and ForAll(extra, y -> y in x)));
  elif not (CanUseFroidurePin(S) or IsFpSemigroup(S) or IsFpMonoid(S)
      or (HasIsFreeSemigroup(S) and IsFreeSemigroup(S))
      or (HasIsFreeMonoid(S) and IsFreeMonoid(S))) then
  fi;

  sims1 := LibsemigroupsSims1(S, n, extra, "left");

  iter := rec(it := libsemigroups.Sims1.cbegin(sims1, n),
              construct := x -> LeftCongruenceByWordGraphNC(S, x));
  iter.NextIterator := NextIterator_Sims1;
  iter.ShallowCopy := x -> rec(it := libsemigroups.Sims1.cbegin(sims1, n),
                               construct :=
                                 x -> LeftCongruenceByWordGraphNC(S, x));
  return IteratorByNextIterator(iter);
end);

InstallMethod(IteratorOfRightCongruences,
"for a semigroup and pos. int.",
[IsSemigroup, IsPosInt],
{S, n} -> IteratorOfRightCongruences(S, n, []));

InstallMethod(IteratorOfLeftCongruences,
"for a semigroup and pos. int.",
[IsSemigroup, IsPosInt],
{S, n} -> IteratorOfLeftCongruences(S, n, []));

InstallMethod(IteratorOfRightCongruences, "for a semigroup",
[IsSemigroup], S -> IteratorOfRightCongruences(S, Size(S), []));

InstallMethod(IteratorOfLeftCongruences, "for a semigroup",
[IsSemigroup], S -> IteratorOfLeftCongruences(S, Size(S), []));
