############################################################################
##
##  congruences/conglatt.gi
##  Copyright (C) 2016-2022                               Michael C. Young
##
##  Licensing information can be found in the README file of this package.
##
#############################################################################
##
## This file contains functions for a poset of congruences.
##
## When the congruences of a semigroup are computed, they form a lattice with
## respect to containment.  The information about the congruences' positions in
## this lattice may be stored in an IsCongruencePoset object (a component object
## based on a record) and can be retrieved from this object using the methods in
## this file.
##
## The list of congruences in the poset is stored as an attribute
## CongruencesOfPoset.  The partial order of the poset is stored as a digraph,
## where an edge (i,j) is present if and only if congruence i is a subrelation
## of congruence j.  When a congruence poset is displayed, it appears to the
## user as the list of out-neighbours of that digraph.
##

#############################################################################
## Helper function for creating CongruencePosets
#############################################################################

SEMIGROUPS.MakeCongruencePoset := function(poset, congs)
  if congs <> fail then
    SetCongruencesOfPoset(poset, congs);
    SetDigraphVertexLabels(poset, congs);
    if not IsEmpty(congs) then
      SetUnderlyingSemigroupOfCongruencePoset(poset, Range(congs[1]));
    fi;
  fi;
  SetFilterObj(poset, IsCongruencePoset);
  return poset;
end;

#############################################################################
## The main three functions
#############################################################################

SEMIGROUPS.PrincipalXCongruencesNC :=
  function(S, pairs, SemigroupXCongruence)
    local total, words, congs, congs_discrim, nrcongs, last_collected, nr,
    keep, newcong, m, newcongdiscrim, i, old_pair, new_pair;

  Assert(1, IsListOrCollection(pairs));
  total := Size(pairs);

  Info(InfoSemigroups, 1, "Finding principal congruences . . .");
  words := List([1 .. Int(Log2(Float(Size(S))))], x -> Random(S));
  words := List(words, x -> MinimalFactorization(S, x));

  congs := [];      # List of all congs found so far, partitioned by nr classes
  congs_discrim := [];

  nrcongs := 0;     # Number of congs found so far
  last_collected := 0;
  nr := 0;
  for new_pair in pairs do
    nr := nr + 1;
    if new_pair[1] = new_pair[2] then
      continue;
    fi;
    keep := true;
    newcong := SemigroupXCongruence(S, [new_pair]);
    m := NrEquivalenceClasses(newcong);
    newcongdiscrim := List(words, w -> CongruenceWordToClassIndex(newcong, w));
    if not IsBound(congs[m]) then
      congs[m] := [newcong];
      congs_discrim[m] := [newcongdiscrim];
      nrcongs := nrcongs + 1;
      continue;
    fi;
    i := PositionSorted(congs_discrim[m], newcongdiscrim);
    while i <= Length(congs_discrim[m])
         and congs_discrim[m][i] = newcongdiscrim do
      old_pair := GeneratingPairsOfLeftRightOrTwoSidedCongruence(congs[m][i]);
      if not IsEmpty(old_pair) then
        old_pair := old_pair[1];
        if CongruenceTestMembershipNC(congs[m][i], new_pair[1], new_pair[2])
            and CongruenceTestMembershipNC(newcong, old_pair[1], old_pair[2])
            then
          keep := false;
          break;
        fi;
      fi;
      i := i + 1;
    od;

    if nr > last_collected + 1999 then
      Info(InfoSemigroups,
           1,
           StringFormatted("Pair {} of {}: {} congruences so far",
                           nr,
                           total,
                           nrcongs));
      last_collected := nr;
      GASMAN("collect");
    fi;
    if keep then
      nrcongs := nrcongs + 1;
      InsertElmList(congs[m], i, newcong);
      InsertElmList(congs_discrim[m], i, newcongdiscrim);
    fi;
  od;
  Info(InfoSemigroups,
       1,
       StringFormatted("Found {} principal congruences in total!",
                       nrcongs));

  return Flat(congs);
end;

########################################################################
########################################################################

# We declare the following for the sole purpose of being able to use the
# Froidure-Pin (GAP implementation) algorithm for computing the join
# semilattice of congruences. We could not just implement multiplication of
# left, right, 2-sided congruences (which would have been less code) for family
# reasons (i.e. if we declare DeclareCategoryCollections for
# IsLeftMagmaCongruence, it turns out that [LeftSemigroupCongruence(*)] does
# not belong to IsLeftMagmaCongruenceCollection, because the family of these
# objects is GeneralMappingsFamily, and it is not the case that
# IsLeftMagmaCongruence is true for every elements of the
# GeneralMappingsFamily. This is a requirement according to the GAP reference
# manual entry for CategoryCollections.
DeclareCategory("IsWrappedLeftRightOrTwoSidedCongruence",
                IsAssociativeElement and IsMultiplicativeElementWithOne);
DeclareCategory("IsWrappedRightCongruence",
                IsWrappedLeftRightOrTwoSidedCongruence);
DeclareCategory("IsWrappedLeftCongruence",
                IsWrappedLeftRightOrTwoSidedCongruence);
DeclareCategory("IsWrappedTwoSidedCongruence",
                IsWrappedLeftRightOrTwoSidedCongruence);

DeclareCategoryCollections("IsWrappedLeftRightOrTwoSidedCongruence");

InstallTrueMethod(CanUseGapFroidurePin,
                  IsWrappedLeftRightOrTwoSidedCongruenceCollection and
                  IsSemigroup);

InstallTrueMethod(IsFinite,
                  IsWrappedLeftRightOrTwoSidedCongruenceCollection and
                  IsSemigroup);

BindGlobal("WrappedLeftCongruenceFamily",
           NewFamily("WrappedLeftCongruenceFamily",
                     IsWrappedLeftCongruence));
BindGlobal("WrappedRightCongruenceFamily",
           NewFamily("WrappedRightCongruenceFamily",
                     IsWrappedRightCongruence));
BindGlobal("WrappedTwoSidedCongruenceFamily",
           NewFamily("WrappedTwoSidedCongruenceFamily",
                     IsWrappedTwoSidedCongruence));

BindGlobal("WrappedLeftCongruenceType",
           NewType(WrappedLeftCongruenceFamily,
                   IsWrappedLeftCongruence and IsPositionalObjectRep));
BindGlobal("WrappedRightCongruenceType",
           NewType(WrappedRightCongruenceFamily,
                   IsWrappedRightCongruence and IsPositionalObjectRep));
BindGlobal("WrappedTwoSidedCongruenceType",
           NewType(WrappedTwoSidedCongruenceFamily,
                   IsWrappedTwoSidedCongruence and IsPositionalObjectRep));

BindGlobal("WrappedLeftCongruence",
x -> Objectify(WrappedLeftCongruenceType, [x]);

BindGlobal("WrappedRightCongruence",
x -> Objectify(WrappedRightCongruenceType, [x]);

InstallGlobalFunction(WrappedTwoSidedCongruence,
x -> Objectify(WrappedTwoSidedCongruence, [x]);

InstallMethod(\=, "for wrapped left, right, or 2-sided congruences",
[IsWrappedLeftRightOrTwoSidedCongruence,
 IsWrappedLeftRightOrTwoSidedCongruence],
{x, y} -> x![1] = y![1]);

InstallMethod(\<, "for wrapped left, right, or 2-sided congruences",
[IsWrappedLeftRightOrTwoSidedCongruence,
 IsWrappedLeftRightOrTwoSidedCongruence],
function(x, y)
  return EquivalenceRelationCanonicalLookup(x![1])
  < EquivalenceRelationCanonicalLookup(y![1]);
end);

InstallMethod(ChooseHashFunction,
"for a wrapped left, right, or 2-sided congruence and integer",
[IsLeftRightOrTwoSidedCongruence, IsInt],
function(cong, data)
  local HashFunc;
  HashFunc := function(cong, data)
    local x;
    x := EquivalenceRelationCanonicalLookup(cong![1]);
    return ORB_HashFunctionForPlainFlatList(x, data);
  end;
  return rec(func := HashFunc, data := data);
end);

InstallMethod(\*, "for wrapped left semigroup congruences",
[IsWrappedLeftCongruence, IsWrappedLeftCongruence],
{x, y} -> WrappedLeftCongruence(JoinLeftSemigroupCongruences(x![1], y![1])));

InstallMethod(\*, "for wrapped right semigroup congruences",
[IsWrappedRightCongruence, IsWrappedRightCongruence],
{x, y} -> WrappedRightCongruence(JoinRightSemigroupCongruences(x![1], y![1])));

InstallMethod(\*, "for wrapped 2-sided semigroup congruences",
[IsWrappedTwoSidedCongruence, IsWrappedTwoSidedCongruence],
{x, y} -> WrappedTwoSidedCongruence(JoinSemigroupCongruences(x![1], y![1])));

InstallMethod(One, "for wrapped left semigroup congruence",
[IsWrappedLeftCongruence],
x -> WrappedLeftCongruence(TrivialCongruence(Source(x![1]))));

InstallMethod(One, "for wrapped right semigroup congruence",
[IsWrappedRightCongruence],
x -> WrappedRightCongruence(TrivialCongruence(Source(x![1]))));

InstallMethod(One, "for wrapped 2-sided semigroup congruence",
[IsWrappedTwoSidedCongruence],
x -> WrappedTwoSidedCongruence(TrivialCongruence(Source(x![1]))));

InstallGlobalFunction(_ClosureLattice,
function(S, gen_congs, WrappedXCongruence)
  local gens, poset, all_congs, old_value, U;

  # Trivial case
  if Length(gen_congs) = 0 then
    return SEMIGROUPS.MakeCongruencePoset(Digraph([[1]]),
                                          [TrivialCongruence(S)]);
  fi;

  if ValueOption("FroidurePin") <> fail then
    gens := List(gen_congs, WrappedXCongruence);
    S := Monoid(gens);
    poset := RightCayleyDigraph(S);
    all_congs := List(AsListCanonical(S), x -> x![1]);
  else  # The default
    S := List(gen_congs, EquivalenceRelationLookup);
    old_value := libsemigroups.should_report();
    if InfoLevel(InfoSemigroups) = 4 then
        LIBSEMIGROUPS_REPORTING_ENABLED(true);
    fi;
    poset := DigraphNC(libsemigroups.LATTICE_OF_CONGRUENCES(S));
    LIBSEMIGROUPS_REPORTING_ENABLED(old_value);
    all_congs := fail;
  fi;
  Info(InfoSemigroups, 1, StringFormatted("Found {} congruences in total!",
       DigraphNrVertices(poset)));

  U := Source(Representative(gen_congs));

  poset := SEMIGROUPS.MakeCongruencePoset(poset, all_congs);
  SetUnderlyingSemigroupOfCongruencePoset(poset, U);
  SetPosetOfPrincipalCongruences(poset,
    Filtered(gen_congs,
     x -> Size(GeneratingPairsOfLeftRightOrTwoSidedCongruence(x)) = 1));
  SetGeneratingCongruencesOfJoinSemilattice(poset, gen_congs);
  SetFilterObj(poset, IsCayleyDigraphOfCongruences);
  return poset;
end);

BindGlobal("_CheckCongruenceLatticeArgs",
function(S, obj)
  if not (IsFinite(S) and CanUseFroidurePin(S)) then
    ErrorNoReturn("the 1st argument (a semigroup) must be finite and have ",
                  "CanUseFroidurePin");
  elif IsIterator(obj) then
    return;
  elif not (IsEmpty(obj) or IsMultiplicativeElementCollColl(obj)) then
    ErrorNoReturn("the 2nd argument (a list or collection) must be ",
                  "empty or a mult. elt. coll. coll.");
  elif not ForAll(obj, x -> Size(x) = 2)
      or not ForAll(obj, x -> x[1] in S and x[2] in S)  then
    ErrorNoReturn("the 2nd argument (a list) must consist of ",
                  "pairs of the 1st argument (a semigroup)");
  fi;
end);

# Creates a poset object from a list of congruences, without generating any
# congruences.

InstallMethod(PosetOfCongruences, "for a list or collection",
[IsListOrCollection],
function(coll)
  local congs, nrcongs, children, parents, i, ignore, j, poset;
  congs := AsList(coll);
  nrcongs := Length(congs);

  # Setup children and parents lists
  children := [];
  parents := [];
  for i in [1 .. nrcongs] do
    children[i] := Set([i]);
    parents[i] := Set([i]);
  od;

  # Find children of each cong in turn
  for i in [1 .. nrcongs] do
    # Ignore known parents
    ignore := BlistList([1 .. nrcongs], [parents[i]]);
    for j in [1 .. nrcongs] do
      if not ignore[j] and IsSubrelation(congs[i], congs[j]) then
        AddSet(children[i], j);
        AddSet(parents[j], i);
      fi;
    od;
  od;

  # We are done: make the object and return
  poset := Digraph(parents);
  SetInNeighbours(poset, children);
  return SEMIGROUPS.MakeCongruencePoset(poset, congs);
end);

InstallMethod(JoinSemilatticeOfCongruences, "for a congruence poset",
[IsCongruencePoset],
function(C)
  local S;
  if IsEmpty(CongruencesOfPoset(C)) then
    if not HasUnderlyingSemigroupOfCongruencePoset(C) then
      ErrorNoReturn("cannot form the join semilattice of an empty congruence ",
                    "poset without the underlying semigroup being set");
    fi;

    S := UnderlyingSemigroupOfCongruencePoset(C);
    return SEMIGROUPS.MakeCongruencePoset(Digraph([[1]]),
                                          [TrivialCongruence(S)]);
  fi;
  return JoinSemilatticeOfCongruences(CongruencesOfPoset(C));
end);

InstallMethod(JoinSemilatticeOfCongruences, "for a congruence poset",
[IsListOrCollection],
function(gen_congs)
  local S, D, all_congs, trivial;
  # TODO(FasterJoins) arg checks
  if IsEmpty(gen_congs) then
    ErrorNoReturn("the argument must not be empty");
  fi;
  S := Source(gen_congs[1]);
  if ForAll(gen_congs, IsMagmaCongruence) then
    D := _ClosureLattice(S, gen_congs, WrappedTwoSidedCongruence);
  elif ForAll(gen_congs, IsLeftMagmaCongruence) then
    D := _ClosureLattice(S, gen_congs, WrappedLeftCongruence);
  else
    Assert(1, ForAll(gen_congs, IsRightMagmaCongruence));
    D := _ClosureLattice(S, gen_congs, WrappedRightCongruence);
  fi;
  all_congs := CongruencesOfPoset(D);
  D := DigraphMutableCopy(D);
  DigraphRemoveAllMultipleEdges(D);
  if not TrivialCongruence(S) in gen_congs then
    all_congs := ShallowCopy(all_congs);
    DigraphRemoveLoops(D);
    trivial := DigraphSources(D)[1];
    DigraphRemoveVertex(D, trivial);
    Remove(all_congs, trivial);
  fi;
  DigraphReflexiveTransitiveClosure(D);
  MakeImmutable(D);
  return SEMIGROUPS.MakeCongruencePoset(D, all_congs);
end);

# This method exists because when we use the "Simple" option with
# LatticeOfCongruences etc the congruences themselves are not present (only the
# CayleyDigraphOfCongruences), so we use this method to reconstruct the
# congruences themselves.
InstallMethod(CongruencesOfPoset, "for a congruence poset",
[IsCayleyDigraphOfCongruences],
function(D)
  local S, result, gen_congs, Q, q, genstoapply, seen, Join, current, n, i;

  S := UnderlyingSemigroupOfCongruencePoset(D);
  result := [TrivialCongruence(S)];
  gen_congs := GeneratingCongruencesOfJoinSemilattice(D);
  if IsEmpty(gen_congs) then
    return result;
  fi;
  Append(result, gen_congs);

  # TODO(later): replace this with a Queue from the datastructures
  # We do a simple BFS from the bottom of the lattice.
  Q := [1];
  q := 1;
  # We prepended the TrivialCongruence and this is not one of the generators
  genstoapply := [1 .. Length(result) - 1];
  seen := BlistList([1 .. DigraphNrVertices(D)], []);

  if IsMagmaCongruence(gen_congs[1]) then
    Join := JoinSemigroupCongruences;
  elif IsRightMagmaCongruence(gen_congs[1]) then
    Join := JoinRightSemigroupCongruences;
  else
    Assert(1, IsLeftMagmaCongruence(gen_congs[1]));
    Join := JoinLeftSemigroupCongruences;
  fi;

  while q <= Size(Q) do
    current := Q[q];
    for i in genstoapply do
      n := OutNeighbours(D)[current][i];
      if not seen[n] then
        seen[n] := true;
        result[n] := Join(result[current], result[i + 1]);
        if n <> 1 then
          Add(Q, n);
        fi;
      fi;
    od;
    q := q + 1;
  od;
  SetDigraphVertexLabels(D, result);
  return result;
end);

########################################################################
# GeneratingPairsOfPrincipalCongruences
########################################################################

InstallMethod(GeneratingPairsOfPrincipalCongruences, "for a semigroup",
[IsSemigroup],
function(S)
  if not (IsFinite(S) and CanUseFroidurePin(S)) then
    ErrorNoReturn("the argument (a semigroup) must be finite and have ",
                  "CanUseFroidurePin");
  fi;
  return Combinations(AsList(S), 2);
  # It'd be better to return an iterator here, but given that
  # GeneratingPairsOfPrincipalCongruences is an attribute, the iterator can't
  # be used when it's returned.
  # return IteratorOfCombinations(AsList(S), 2);
end);

# Use the method just above
InstallMethod(GeneratingPairsOfPrincipalLeftCongruences,
"for a semigroup", [IsSemigroup], GeneratingPairsOfPrincipalCongruences);

# Use the method just above
InstallMethod(GeneratingPairsOfPrincipalRightCongruences,
"for a semigroup", [IsSemigroup], GeneratingPairsOfPrincipalCongruences);

InstallMethod(GeneratingPairsOfPrincipalCongruences, "for an acting semigroup",
[IsActingSemigroup],
function(S)
  local M, MxM, map1, map2, Delta, pairs;
  if not (IsFinite(S) and CanUseFroidurePin(S)) then
    ErrorNoReturn("the argument (a semigroup) must be finite and have ",
                  "CanUseFroidurePin");
  elif not IsMonoid(S) and not IsMonoidAsSemigroup(S) then
    M := Monoid(S, rec(acting := true));
  else
    M := S;
  fi;

  MxM   := DirectProduct(M, M);
  SetFilterObj(MxM, IsActingSemigroup);
  map1  := Embedding(MxM, 1);
  map2  := Embedding(MxM, 2);

  Delta := Set(GeneratorsOfSemigroup(S), x -> x ^ map1 * x ^ map2);
  pairs := RelativeDClassReps(MxM, Semigroup(Delta, rec(acting := true)));
  map1  := Projection(MxM, 1);
  map2  := Projection(MxM, 2);
  pairs := Set(pairs, x -> AsSortedList([x ^ map1, x ^ map2]));
  return Filtered(pairs, x -> x[1] in S and x[2] in S);
end);

InstallMethod(GeneratingPairsOfPrincipalRightCongruences,
"for an acting semigroup",
[IsActingSemigroup],
function(S)
  local M, MxM, map1, map2, Delta, pairs;

  if not (IsFinite(S) and CanUseFroidurePin(S)) then
    ErrorNoReturn("the argument (a semigroup) must be finite and have ",
                  "CanUseFroidurePin");
  elif not IsMonoid(S) and not IsMonoidAsSemigroup(S) then
    M := Monoid(S);
  else
    M := S;
  fi;

  MxM   := DirectProduct(M, M);
  SetFilterObj(MxM, IsActingSemigroup);
  map1  := Embedding(MxM, 1);
  map2  := Embedding(MxM, 2);

  Delta := Set(GeneratorsOfSemigroup(S), x -> x ^ map1 * x ^ map2);
  pairs := RelativeRClassReps(MxM, Semigroup(Delta, rec(acting := true)));
  map1  := Projection(MxM, 1);
  map2  := Projection(MxM, 2);
  pairs := Set(pairs, x -> AsSortedList([x ^ map1, x ^ map2]));
  return Filtered(pairs, x -> x[1] in S and x[2] in S);
end);

InstallMethod(GeneratingPairsOfPrincipalLeftCongruences,
"for an acting semigroup", [IsActingSemigroup],
function(S)
  local map, T;
  map := AntiIsomorphismTransformationSemigroup(S);
  T := Range(map);
  map := InverseGeneralMapping(map);
  return List(GeneratingPairsOfPrincipalRightCongruences(T),
              x -> List(x, y -> y ^ map));
end);

#############################################################################
## CayleyDigraphOfCongruences
#############################################################################

InstallMethod(CayleyDigraphOfCongruences,
"for a semigroup and a list or collection",
[IsSemigroup, IsListOrCollection],
function(S, pairs)
  # pairs are checked in PrincipalCongruencesOfSemigroup
  return _ClosureLattice(S,
                         PrincipalCongruencesOfSemigroup(S, pairs),
                         WrappedTwoSidedCongruence);
end);

InstallMethod(CayleyDigraphOfCongruences, "for a semigroup", [IsSemigroup],
function(S)
  return _ClosureLattice(S,
                         PrincipalCongruencesOfSemigroup(S),
                         WrappedTwoSidedCongruence);
end);

InstallMethod(CayleyDigraphOfRightCongruences,
"for a semigroup and a list or collection",
[IsSemigroup, IsListOrCollection],
function(S, pairs)
  # pairs are checked in PrincipalCongruencesOfSemigroup
  return _ClosureLattice(S,
                         PrincipalRightCongruencesOfSemigroup(S, pairs),
                         WrappedRightCongruence);
end);

InstallMethod(CayleyDigraphOfRightCongruences, "for a semigroup",
[IsSemigroup],
function(S)
  return _ClosureLattice(S,
                         PrincipalRightCongruencesOfSemigroup(S),
                         WrappedRightCongruence);
end);

InstallMethod(CayleyDigraphOfLeftCongruences,
"for a semigroup and a list or collection",
[IsSemigroup, IsListOrCollection],
function(S, pairs)
  # pairs are checked in PrincipalCongruencesOfSemigroup
  return _ClosureLattice(S,
                         PrincipalLeftCongruencesOfSemigroup(S, pairs),
                         WrappedLeftCongruence);
end);

InstallMethod(CayleyDigraphOfLeftCongruences, "for a semigroup", [IsSemigroup],
function(S)
  return _ClosureLattice(S,
                         PrincipalLeftCongruencesOfSemigroup(S),
                         WrappedLeftCongruence);
end);

#############################################################################
## LatticeOfCongruences
#############################################################################

SEMIGROUPS.MakeLattice := function(C)
  local D;
  D := DigraphMutableCopy(C);
  DigraphRemoveAllMultipleEdges(D);
  DigraphReflexiveTransitiveClosure(D);
  MakeImmutable(D);
  return SEMIGROUPS.MakeCongruencePoset(D, CongruencesOfPoset(C));
end;

InstallMethod(LatticeOfCongruences,
"for a semigroup and a list or collection",
[IsSemigroup, IsListOrCollection],
{S, pairs} -> SEMIGROUPS.MakeLattice(CayleyDigraphOfCongruences(S, pairs)));

InstallMethod(LatticeOfCongruences, "for a semigroup", [IsSemigroup],
S -> SEMIGROUPS.MakeLattice(CayleyDigraphOfCongruences(S)));

InstallMethod(LatticeOfRightCongruences,
"for a semigroup and a list or collection",
[IsSemigroup, IsListOrCollection],
{S, pairs} -> SEMIGROUPS.MakeLattice(CayleyDigraphOfRightCongruences(S, pairs)));

InstallMethod(LatticeOfRightCongruences, "for a semigroup", [IsSemigroup],
S -> SEMIGROUPS.MakeLattice(CayleyDigraphOfRightCongruences(S)));

InstallMethod(LatticeOfLeftCongruences,
"for a semigroup and a list or collection",
[IsSemigroup, IsListOrCollection],
{S, pairs} -> SEMIGROUPS.MakeLattice(CayleyDigraphOfLeftCongruences(S, pairs)));

InstallMethod(LatticeOfLeftCongruences, "for a semigroup", [IsSemigroup],
S -> SEMIGROUPS.MakeLattice(CayleyDigraphOfLeftCongruences(S)));

########################################################################
# Left/Right/CongruencesOfSemigroup
########################################################################

InstallMethod(LeftCongruencesOfSemigroup,
"for a semigroup", [IsSemigroup],
S -> CongruencesOfPoset(CayleyDigraphOfLeftCongruences(S)));

InstallMethod(RightCongruencesOfSemigroup,
"for a semigroup", [IsSemigroup],
S -> CongruencesOfPoset(CayleyDigraphOfRightCongruences(S)));

InstallMethod(CongruencesOfSemigroup,
"for a semigroup", [IsSemigroup],
S -> CongruencesOfPoset(CayleyDigraphOfCongruences(S)));

########################################################################
# Principal congruences
########################################################################

InstallMethod(PrincipalLeftCongruencesOfSemigroup, "for a semigroup",
[IsSemigroup],
function(S)
  local pairs;
  pairs := GeneratingPairsOfPrincipalLeftCongruences(S);
  return SEMIGROUPS.PrincipalXCongruencesNC(S,
                                            pairs,
                                            LeftSemigroupCongruence);
end);

InstallMethod(PrincipalRightCongruencesOfSemigroup, "for a semigroup",
[IsSemigroup],
function(S)
  local pairs;
  pairs := GeneratingPairsOfPrincipalRightCongruences(S);
  return SEMIGROUPS.PrincipalXCongruencesNC(S,
                                            pairs,
                                            RightSemigroupCongruence);
end);

InstallMethod(PrincipalCongruencesOfSemigroup, "for a semigroup",
[IsSemigroup],
function(S)
  local pairs;
  pairs := GeneratingPairsOfPrincipalCongruences(S);
  return SEMIGROUPS.PrincipalXCongruencesNC(S,
                                            pairs,
                                            SemigroupCongruence);
end);

InstallMethod(PrincipalLeftCongruencesOfSemigroup,
"for a semigroup and a list or collection",
[IsSemigroup, IsListOrCollection],
function(S, pairs)
  _CheckCongruenceLatticeArgs(S, pairs);
  return SEMIGROUPS.PrincipalXCongruencesNC(S,
                                            pairs,
                                            LeftSemigroupCongruence);
end);

InstallMethod(PrincipalRightCongruencesOfSemigroup,
"for a semigroup and a list or collection",
[IsSemigroup, IsListOrCollection],
function(S, pairs)
  _CheckCongruenceLatticeArgs(S, pairs);
  return SEMIGROUPS.PrincipalXCongruencesNC(S,
                                            pairs,
                                            RightSemigroupCongruence);
end);

InstallMethod(PrincipalCongruencesOfSemigroup,
"for a semigroup and a list or collection",
[IsSemigroup, IsListOrCollection],
function(S, pairs)
  _CheckCongruenceLatticeArgs(S, pairs);
  return SEMIGROUPS.PrincipalXCongruencesNC(S,
                                            pairs,
                                            SemigroupCongruence);
end);

########################################################################
## MinimalCongruences
########################################################################

InstallMethod(MinimalCongruences, "for a congruence poset",
[IsCongruencePoset],
poset -> CongruencesOfPoset(poset){Positions(InDegrees(poset), 1)});

InstallMethod(MinimalCongruencesOfSemigroup, "for a semigroup", [IsSemigroup],
function(S)
  if HasLatticeOfCongruences(S) then
    return MinimalCongruences(LatticeOfCongruences(S));
  fi;
  return MinimalCongruences(PosetOfPrincipalCongruences(S));
end);

InstallMethod(MinimalLeftCongruencesOfSemigroup, "for a semigroup",
[IsSemigroup],
function(S)
  if HasLatticeOfLeftCongruences(S) then
    return MinimalCongruences(LatticeOfLeftCongruences(S));
  fi;
  return MinimalCongruences(PosetOfPrincipalLeftCongruences(S));
end);

InstallMethod(MinimalRightCongruencesOfSemigroup, "for a semigroup",
[IsSemigroup],
function(S)
  if HasLatticeOfRightCongruences(S) then
    return MinimalCongruences(LatticeOfRightCongruences(S));
  fi;
  return MinimalCongruences(PosetOfPrincipalRightCongruences(S));
end);

InstallMethod(MinimalCongruencesOfSemigroup,
"for a semigroup and list or collection",
[IsSemigroup, IsListOrCollection],
{S, pairs} -> MinimalCongruences(PosetOfPrincipalCongruences(S, pairs)));

InstallMethod(MinimalRightCongruencesOfSemigroup,
"for a semigroup and list or collection",
[IsSemigroup, IsListOrCollection],
{S, pairs} -> MinimalCongruences(PosetOfPrincipalRightCongruences(S, pairs)));

InstallMethod(MinimalLeftCongruencesOfSemigroup,
"for a semigroup and list or collection",
[IsSemigroup, IsListOrCollection],
{S, pairs} -> MinimalCongruences(PosetOfPrincipalLeftCongruences(S, pairs)));

########################################################################
# PosetOfPrincipalRight/LeftCongruences
########################################################################

InstallMethod(PosetOfPrincipalCongruences, "for a semigroup", [IsSemigroup],
function(S)
  if HasLatticeOfCongruences(S) then
    return PosetOfPrincipalCongruences(LatticeOfCongruences(S));
  fi;
  return PosetOfCongruences(PrincipalCongruencesOfSemigroup(S));
end);

InstallMethod(PosetOfPrincipalRightCongruences, "for a semigroup",
[IsSemigroup],
function(S)
  if HasLatticeOfRightCongruences(S) then
    return PosetOfPrincipalRightCongruences(LatticeOfRightCongruences(S));
  fi;
  return PosetOfCongruences(PrincipalRightCongruencesOfSemigroup(S));
end);

InstallMethod(PosetOfPrincipalLeftCongruences, "for a semigroup",
[IsSemigroup],
function(S)
  if HasLatticeOfLeftCongruences(S) then
    return PosetOfPrincipalLeftCongruences(LatticeOfLeftCongruences(S));
  fi;
  return PosetOfCongruences(PrincipalLeftCongruencesOfSemigroup(S));
end);

InstallMethod(PosetOfPrincipalCongruences,
"for a semigroup and list or collection",
[IsSemigroup, IsListOrCollection],
{S, pairs} -> PosetOfCongruences(PrincipalCongruencesOfSemigroup(S, pairs)));

InstallMethod(PosetOfPrincipalRightCongruences,
"for a semigroup and list or collection",
[IsSemigroup, IsListOrCollection],
{S, pairs} -> PosetOfCongruences(PrincipalRightCongruencesOfSemigroup(S,
                                                                      pairs)));

InstallMethod(PosetOfPrincipalLeftCongruences,
"for a semigroup and list or collection",
[IsSemigroup, IsListOrCollection],
{S, pairs} -> PosetOfCongruences(PrincipalLeftCongruencesOfSemigroup(S, pairs)));

########################################################################
# Printing, viewing, dot strings etc
########################################################################

InstallMethod(ViewObj, "for a congruence poset", [IsCongruencePoset],
function(poset)
  local prefix, S, C, hand;
  if DigraphNrVertices(poset) = 0 then
    Print("<empty congruence poset>");
  else
    if not IsMultiDigraph(poset) and IsLatticeDigraph(poset) then
      prefix := "lattice";
    else
      prefix := "poset";
    fi;
    S := UnderlyingSemigroupOfCongruencePoset(poset);
    # Find a non-trivial non-universal congruence if it exists
    C := First(CongruencesOfPoset(poset),
               x -> not NrEquivalenceClasses(x) in [1, Size(S)]);
    if C = fail or IsMagmaCongruence(C) then
      hand := "two-sided";
    else
      hand := ShallowCopy(CongruenceHandednessString(C));
    fi;
    Append(hand, " congruence");
    PrintFormatted("<\>{} of {} over \<",
                   prefix,
                   Pluralize(DigraphNrVertices(poset), hand));
    ViewObj(S);
    Print(">");
  fi;
end);

InstallMethod(PrintObj, "for a congruence poset", [IsCongruencePoset],
function(poset)
  Print("PosetOfCongruences( ", CongruencesOfPoset(poset), " )");
end);

InstallMethod(DotString,
"for a congruence poset",
[IsCongruencePoset],
function(poset)
  # Call the below function, with default options
  return DotString(poset, rec());
end);

InstallMethod(DotString,
"for a congruence poset and a record",
[IsCongruencePoset, IsRecord],
function(poset, opts)
  local nrcongs, congs, S, symbols, i, nr, in_nbs, rel, str, j, k;
  nrcongs := DigraphNrVertices(poset);
  # Setup unbound options
  if not IsBound(opts.info) then
    opts.info := false;
  fi;
  if not IsBound(opts.numbers) then
    opts.numbers := (nrcongs < 40);
  fi;
  # If the user wants info, then change the node labels
  if opts.info = true then
    # The congruences are stored inside the poset object
    congs := CongruencesOfPoset(poset);
    S := Range(congs[1]);
    symbols := EmptyPlist(nrcongs);
    for i in [1 .. nrcongs] do
      nr := NrEquivalenceClasses(congs[i]);
      if nr = 1 then
        symbols[i] := "U";
      elif nr = Size(S) then
        symbols[i] := "T";
      elif IsReesCongruence(congs[i]) then
        symbols[i] := Concatenation("R", String(i));
      else
        symbols[i] := String(i);
      fi;
    od;
  else
    symbols := List([1 .. nrcongs], String);
  fi;

  in_nbs := InNeighbours(poset);
  rel := List([1 .. nrcongs], x -> Filtered(in_nbs[x], y -> x <> y));
  str := "";

  if opts.numbers then
    Append(str, "//dot\ngraph graphname {\n     node [shape=circle]\n");
  else
    Append(str, "//dot\ngraph graphname {\n     node [shape=point]\n");
  fi;

  for i in [1 .. Length(rel)] do
    j := Difference(rel[i], Union(rel{rel[i]}));
    i := symbols[i];
    for k in j do
      k := symbols[k];
      Append(str, Concatenation(i, " -- ", k, "\n"));
    od;
  od;

  Append(str, " }");

  return str;
end);
