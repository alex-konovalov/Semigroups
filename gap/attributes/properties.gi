###############################################################################
##
##  properties.gi
##  Copyright (C) 2013-15                                James D. Mitchell
##
##  Licensing information can be found in the README file of this package.
##
#############################################################################
##

# This file contains methods for determining properties of arbitrary
# semigroups. There are not very many specialised methods for acting semigroups
# and so we only have a single file.

# Ecom (commuting idempotents), LI (locally trivial),
# LG (locally group), B1 (dot-depth one), DA (regular D-classes are idempotent)
# R v L (???), IsNilpotentSemigroup, inverses, local submonoid, right ideal,
# left ideal, kernel!?

# IsLeftCancellative,
# IsRightCancellative, IsRightGroup, IsLeftGroup, IsUnitarySemigroup,
# IsRightUnitarySemigp, IsLeftUnitarySemigp, IsCongruenceFree,
# PrimitiveIdempotents, IdempotentOrder,
# IsLeftNormalBand, IsRightNormalBand, IsNormalBand, IsEUnitarySemigroup
# IsRectangularGroup, IsBandOfGroups, IsFreeBand, IsFreeSemilattice,
# IsFreeNormalBand, , IsFundamentalInverseSemigp,
# IsFullSubsemigroup (of an inverse semigroup), IsFactorizableInverseMonoid,
# IsFInverseSemigroup, IsSemigroupWithCentralIdempotents, IsLeftUnipotent,
# IsRightUnipotent, IsSemigroupWithClosedIdempotents, .

# same method for ideals, works for finite and infinite

InstallMethod(IsBand, "for a semigroup",
[IsSemigroup],
function(S)
  if HasParent(S) and HasIsBand(Parent(S)) and IsBand(Parent(S)) then
    return true;
  fi;
  return IsCompletelyRegularSemigroup(S) and IsHTrivial(S);
end);

# same method for ideals, works for finite and infinite

InstallMethod(IsBand, "for an inverse semigroup", [IsInverseSemigroup],
IsSemilattice);

# same method for ideals

InstallMethod(IsBlockGroup, "for a semigroup",
[IsSemigroup],
function(S)
  local D;

  if HasParent(S) and HasIsBlockGroup(Parent(S))
      and IsBlockGroup(Parent(S)) then
    return true;
  elif (HasIsRegularSemigroup(S) and IsRegularSemigroup(S))
      and (HasIsInverseSemigroup(S) and not IsInverseSemigroup(S)) then
    Info(InfoSemigroups, 2, "regular but non-inverse semigroup");
    return false;
  elif not IsFinite(S) then
    TryNextMethod();
  fi;

  for D in DClasses(S) do
    if IsRegularDClass(D)
        and (ForAny(RClasses(D), x -> NrIdempotents(x) > 1)
             or NrRClasses(D) <> NrLClasses(D)) then
      return false;
    fi;
  od;
  return true;
end);

InstallMethod(IsSemigroupWithCommutingIdempotents, "for a semigroup",
[IsSemigroup],
function(S)
  local ids, n, i, j;
  ids := Idempotents(S);
  n := Length(ids);
  for i in [1 .. n - 1] do
    for j in [i + 1 .. n] do
      if ids[i] * ids[j] <> ids[j] * ids[i] then
        return false;
      fi;
    od;
  od;
  return true;
end);

InstallMethod(IsSemigroupWithCommutingIdempotents,
"for a semigroup with idempotent generated subsemigroup",
[IsSemigroup and HasIdempotentGeneratedSubsemigroup],
S -> IsCommutativeSemigroup(IdempotentGeneratedSubsemigroup(S)));

# same method for ideals

InstallMethod(IsBrandtSemigroup, "for a semigroup",
[IsSemigroup],
function(S)
  if not IsFinite(S) then
    return false;
  fi;
  return IsZeroSimpleSemigroup(S) and IsInverseSemigroup(S);
end);

# same method for ideals

InstallMethod(IsCongruenceFreeSemigroup, "for a semigroup",
[IsSemigroup],
function(S)
  local rowsDiff, T, P;

  if not IsFinite(S) then
    TryNextMethod();
  fi;

  rowsDiff := function(p)
    local i, j;
    for i in [1 .. Size(p) - 1] do
      for j in [i + 1 .. Size(p)] do
        if p[i] = p[j] then
          return false;
        fi;
      od;
    od;
    return true;
  end;

  if Size(S) <= 2 then
    return true;
  fi;

  if MultiplicativeZero(S) <> fail then
    # CASE 1: S has zero
    if IsZeroSimpleSemigroup(S) then
      # Find an isomorphic RZMS
      T := Range(IsomorphismReesZeroMatrixSemigroup(S));
      if IsTrivial(UnderlyingSemigroup(T)) then
        # Check that no two rows or columns are identical
        P := Matrix(T);
        if rowsDiff(P) and rowsDiff(TransposedMat(P)) then
          return true;
        fi;
      fi;
    fi;
    return false;
  fi;

  # CASE 2: S has no zero
  return (IsGroup(S) and IsSimpleGroup(S))
    or (IsGroupAsSemigroup(S)
        and IsSimpleGroup(Range(IsomorphismPermGroup(S))));
end);

# same method for regular ideals, or non-regular without a generating set

InstallMethod(IsCliffordSemigroup, "for a semigroup",
[IsSemigroup],
function(S)
  if HasParent(S) and HasIsCliffordSemigroup(Parent(S))
      and IsCliffordSemigroup(Parent(S)) then
    return true;
  elif not IsFinite(S) then
    TryNextMethod();
  fi;

  return IsRegularSemigroup(S) and NrHClasses(S) = NrDClasses(S);
end);

# same method for non-regular ideals

InstallMethod(IsCliffordSemigroup,
"for a semigroup with generators",
[IsSemigroup and HasGeneratorsOfSemigroup],
function(S)
  local gens, idem, f, g;

  if HasParent(S) and HasIsCliffordSemigroup(Parent(S))
      and IsCliffordSemigroup(Parent(S)) then
    return true;
  elif HasIsInverseSemigroup(S) and not IsInverseSemigroup(S) then
    Info(InfoSemigroups, 2, "the semigroup is not inverse");
    return false;
  elif HasIsCompletelyRegularSemigroup(S)
      and not IsCompletelyRegularSemigroup(S) then
    Info(InfoSemigroups, 2, "the semigroup is not completely regular");
    return false;
  elif not IsFinite(S) then
    TryNextMethod();
  elif IsGroupAsSemigroup(S) then
    Info(InfoSemigroups, 2, "the semigroup is a group");
    return true;
  elif not IsRegularSemigroup(S) then
    Info(InfoSemigroups, 2, "the semigroup is not regular");
    return false;
  fi;

  gens := GeneratorsOfSemigroup(S);
  idem := List(gens, x -> One(GreensHClassOfElementNC(S, x)));

  for f in gens do
    for g in idem do
      if not f * g = g * f then
        Info(InfoSemigroups, 2, "the idempotents are not central:");
        Info(InfoSemigroups, 2, "  ", f, "\n#I  and\n#I    ", g,
             "\n#I  do not commute,");
        return false;
      fi;
    od;
  od;

  return true;
end);

# same method for inverse ideals

InstallMethod(IsCliffordSemigroup, "for an inverse acting semigroup",
[IsInverseSemigroup and IsActingSemigroup],
S -> ForAll(OrbSCC(LambdaOrb(S)), x -> Length(x) = 1));

# different method for ideals

InstallMethod(IsCommutativeSemigroup, "for a semigroup with generators",
[IsSemigroup and HasGeneratorsOfSemigroup],
function(S)
  local gens, n, i, j;

  if not IsFinite(S) then
    TryNextMethod();
  fi;

  gens := GeneratorsOfSemigroup(S);
  n := Length(gens);

  for i in [1 .. n - 1] do
    for j in [i + 1 .. n] do
      if not gens[i] * gens[j] = gens[j] * gens[i] then
        Info(InfoSemigroups, 2, "generators ", i, " and ", j,
             " do not commute");
        return false;
      fi;
    od;
  od;

  return true;
end);

# same method for non-regular ideals with generators

InstallMethod(IsCompletelyRegularSemigroup,
"for an acting semigroup with generators",
[IsActingSemigroup and HasGeneratorsOfSemigroup],
function(S)
  local record, o, pos, f;

  if HasParent(S) and HasIsCompletelyRegularSemigroup(Parent(S))
      and IsCompletelyRegularSemigroup(Parent(S)) then
    return true;
  elif HasIsRegularSemigroup(S) and not IsRegularSemigroup(S) then
    Info(InfoSemigroups, 2, "semigroup is not regular");
    return false;
  fi;

  record := ShallowCopy(LambdaOrbOpts(S));
  record.treehashsize := SEMIGROUPS.OptionsRec(S).hashlen;

  for f in GeneratorsOfSemigroup(S) do
    o := Orb(S, LambdaFunc(S)(f), LambdaAct(S), record);
    pos := LookForInOrb(o,
                        function(o, x)
                          return LambdaRank(S)(LambdaAct(S)(x, f))
                                  <> LambdaRank(S)(x);
                        end,
                        1);
    # for transformations we could use IsInjectiveListTrans instead
    # and the performance would be better!

    if pos <> false then
      Info(InfoSemigroups, 2, "at least one H-class is not a subgroup");
      return false;
    fi;
  od;

  return true;
end);

# same method for regular ideals, or non-regular without a generating set

InstallMethod(IsCompletelyRegularSemigroup, "for a semigroup",
[IsSemigroup],
function(S)
  if HasParent(S) and HasIsCompletelyRegularSemigroup(Parent(S))
      and IsCompletelyRegularSemigroup(Parent(S)) then
    return true;
  elif HasIsRegularSemigroup(S) and not IsRegularSemigroup(S) then
    Info(InfoSemigroups, 2, "semigroup is not regular");
    return false;
  elif not IsFinite(S) then
    TryNextMethod();
  fi;

  return NrHClasses(S) = NrIdempotents(S);
end);

# same method for inverse ideals

InstallMethod(IsCompletelyRegularSemigroup, "for an inverse semigroup",
[IsInverseSemigroup], IsCliffordSemigroup);

# Notes: this test required to avoid conflict with Smallsemi,
# DeclareSynonymAttr causes problems.

# same method for ideals

InstallMethod(IsCompletelySimpleSemigroup, "for a semigroup",
[IsSemigroup],
function(S)
  if not IsFinite(S) then
    TryNextMethod();
  fi;
  return IsSimpleSemigroup(S);
end);

# same method for ideals

InstallMethod(IsEUnitaryInverseSemigroup,
"for an inverse semigroup with inverse op",
[IsInverseSemigroup and IsGeneratorsOfInverseSemigroup],
function(S)
  if not IsFinite(S) then
    TryNextMethod();
  fi;
  return IsMajorantlyClosed(S, IdempotentGeneratedSubsemigroup(S));
end);

InstallMethod(IsEUnitaryInverseSemigroup, "for a semigroup",
[IsSemigroup],
function(S)
  if not IsFinite(S) then
    TryNextMethod();
  elif not IsInverseSemigroup(S) then
    return false;
  fi;
  return IsEUnitaryInverseSemigroup(AsSemigroup(IsPartialPermSemigroup, S));
end);

# different method for ideals TODO or same?

InstallMethod(IsFactorisableInverseMonoid,
"for an inverse semigroup with generators",
[IsInverseSemigroup and HasGeneratorsOfSemigroup],
function(S)
  local G, iso, enum, func, x;

  if not IsFinite(S) then
    TryNextMethod();
  fi;

  G := GroupOfUnits(S);

  if G = fail then
    return false;
  elif IsTrivial(G) then
    return IsSemilattice(S);
  fi;

  iso := InverseGeneralMapping(IsomorphismPermGroup(G));
  enum := Enumerator(Source(iso));
  func := NaturalLeqInverseSemigroup(S);

  for x in Generators(S) do
    if not x in G then
      if not ForAny(enum, y -> func(x, y ^ iso)) then
        return false;
      fi;
    fi;
  od;
  return true;
end);

# same method for ideals

InstallMethod(IsHTrivial, "for an acting semigroup",
[IsActingSemigroup],
function(S)
  local iter, x;

  if HasParent(S) and HasIsHTrivial(Parent(S)) and IsHTrivial(Parent(S)) then
    return true;
  fi;

  if IsTransformationSemigroup(S) and HasGeneratorsOfSemigroup(S) then
    for x in GeneratorsOfSemigroup(S) do
      if IndexPeriodOfTransformation(x)[2] <> 1 then
        return false;
      fi;
    od;
  elif IsPartialPermSemigroup(S) and HasGeneratorsOfSemigroup(S) then
    for x in GeneratorsOfSemigroup(S) do
      if IndexPeriodOfPartialPerm(x)[2] <> 1 then
        return false;
      fi;
    od;
  fi;

  iter := IteratorOfDClasses(S);

  for x in iter do
    if not IsTrivial(SchutzenbergerGroup(x)) then
      return false;
    fi;
  od;
  return true;
end);

InstallMethod(IsHTrivial, "for a semigroup", [IsSemigroup],
function(S)
  if HasParent(S) and HasIsHTrivial(Parent(S)) and IsHTrivial(Parent(S)) then
    return true;
  elif not IsFinite(S) then
    TryNextMethod();
  fi;

  return NrHClasses(S) = Size(S);
end);

# same method for non-inverse ideals

InstallMethod(IsLTrivial, "for an acting semigroup",
[IsActingSemigroup],
function(S)
  local iter, D;

  if HasParent(S) and HasIsLTrivial(Parent(S)) and IsLTrivial(Parent(S)) then
    return true;
  fi;

  iter := IteratorOfDClasses(S);

  for D in iter do
    if not IsTrivial(SchutzenbergerGroup(D)) or Length(RhoOrbSCC(D)) <> 1 then
      return false;
    fi;
  od;

  return true;
end);

# same method for inverse ideals

InstallMethod(IsLTrivial, "for an inverse acting semigroup",
[IsInverseActingSemigroupRep],
function(S)
  if HasParent(S) and HasIsLTrivial(Parent(S)) and IsLTrivial(Parent(S)) then
    return true;
  fi;
  return ForAll(OrbSCC(LambdaOrb(S)), x -> Length(x) = 1);
end);

# same method for ideals

InstallMethod(IsLTrivial, "for a semigroup",
[IsSemigroup],
function(S)
  if HasParent(S) and HasIsLTrivial(Parent(S)) and IsLTrivial(Parent(S)) then
    return true;
    elif not IsFinite(S) then
    TryNextMethod();
  fi;

  return NrLClasses(S) = Size(S);
end);

# same method for ideals

InstallMethod(IsRTrivial, "for an inverse semigroup",
[IsInverseSemigroup], IsLTrivial);

# different method for ideals

InstallMethod(IsRTrivial, "for a transformation semigroup with generators",
[IsTransformationSemigroup and HasGeneratorsOfSemigroup],
2,  # to beat the method for acting semigroups
function(S)
  return IsAcyclicDigraph(DigraphRemoveLoops(DigraphOfActionOnPoints(S)));
end);

# different method for ideals

InstallMethod(IsRTrivial, "for a partial perm semigroup with generators",
[IsPartialPermSemigroup and HasGeneratorsOfSemigroup],
function(S)
  if ForAny(GeneratorsOfSemigroup(S),
            x -> ForAny(CyclesOfPartialPerm(x), y -> Length(y) > 1)) then
    return false;
  fi;
  return ForAll(CyclesOfPartialPermSemigroup(S), x -> Length(x) = 1);
end);

# same method for non-inverse ideals

InstallMethod(IsRTrivial, "for an acting semigroup",
[IsActingSemigroup],
function(S)
  local iter, x;

  if HasParent(S) and HasIsRTrivial(Parent(S)) and IsRTrivial(Parent(S)) then
    return true;
  fi;

  if IsClosedData(SemigroupData(S)) and IsClosedOrbit(RhoOrb(S)) then
    for x in GreensDClasses(S) do
      if (not IsTrivial(SchutzenbergerGroup(x)))
          or Length(LambdaOrbSCC(x)) > 1 then
        return false;
      fi;
    od;
    return true;
  fi;

  iter := IteratorOfRClasses(S);

  for x in iter do
    if (not IsTrivial(SchutzenbergerGroup(x)))
        or Length(LambdaOrbSCC(x)) > 1 then
      return false;
    fi;
  od;

  return true;
end);

InstallMethod(IsRTrivial, "for a semigroup", [IsSemigroup],
function(S)
  if HasParent(S) and HasIsRTrivial(Parent(S)) and IsRTrivial(Parent(S)) then
    return true;
  elif not IsFinite(S) then
    TryNextMethod();
  fi;

  return Size(S) = NrRClasses(S);
end);

InstallMethod(IsGroupAsSemigroup, "for a semigroup",
[IsSemigroup],
function(S)
  if HasParent(S) and HasIsGroupAsSemigroup(Parent(S))
      and IsGroupAsSemigroup(Parent(S)) then
    return true;
  elif not IsFinite(S) then
    TryNextMethod();
  fi;
  return NrRClasses(S) = 1 and NrLClasses(S) = 1;
end);

# same method for non-regular ideals

InstallMethod(IsGroupAsSemigroup, "for an acting semigroup",
[IsActingSemigroup],
function(S)
  local gens, lambdafunc, lambda, rhofunc, rho, tester, lambda_f, rho_f, f;

  if HasParent(S) and HasIsGroupAsSemigroup(Parent(S))
      and IsGroupAsSemigroup(Parent(S)) then
    return true;
  fi;

  gens := GeneratorsOfSemigroup(S);  # not GeneratorsOfMonoid!

  if IsActingSemigroupWithFixedDegreeMultiplication(S)
      and ForAll(gens, x -> ActionRank(S)(x) = ActionDegree(x)) then
    return true;
  fi;

  lambdafunc := LambdaFunc(S);
  lambda := lambdafunc(gens[1]);
  rhofunc := RhoFunc(S);
  rho := rhofunc(gens[1]);
  tester := IdempotentTester(S);

  for f in gens do
    lambda_f := lambdafunc(f);
    rho_f := rhofunc(f);
    if lambda_f <> lambda or rho_f <> rho or not tester(lambda_f, rho_f) then
      return false;
    fi;
  od;

  return true;
end);

# same method for ideals

InstallMethod(IsIdempotentGenerated, "for a semigroup",
[IsSemigroup],
function(S)
  local gens, T, ranks, min, new, max, i;

  if not IsFinite(S) then
    TryNextMethod();
  fi;

  if HasIsMonoidAsSemigroup(S) and IsMonoidAsSemigroup(S)
      and not IsTrivial(GroupOfUnits(S)) then
    return false;
  fi;

  gens := GeneratorsOfSemigroup(S);

  if ForAll(gens, IsIdempotent) then
    Info(InfoSemigroups, 2, "all the generators are idempotents");
    return true;
  fi;

  if HasIdempotentGeneratedSubsemigroup(S) or not IsActingSemigroup(S) then
    T := IdempotentGeneratedSubsemigroup(S);
  else
    ranks := List(gens, x -> ActionRank(S)(x));
    min := MinimumList(ranks);
    if HasIdempotents(S) then
      new := Filtered(Idempotents(S), x -> ActionRank(S)(x) >= min);
    else
      max := MaximumList(ranks);
      new := [];
      for i in [min .. max] do
        Append(new, Idempotents(S, i));
      od;
    fi;
    if new = [] then
      return false;
    fi;
    T := Semigroup(new, rec(acting := true));
  fi;

  # T is not always the idempotent generated subsemigroup!
  return ForAll(gens, x -> x in T);
end);

# same method for inverse ideals

InstallMethod(IsIdempotentGenerated, "for an inverse semigroup",
[IsInverseSemigroup], IsSemilattice);

# same method for ideals

InstallMethod(IsInverseSemigroup, "for a semigroup",
[IsSemigroup],
1,  # to beat sgpviz
function(S)
  local lambda, rho, iter, x;

  if HasIsRegularSemigroup(S) and not IsRegularSemigroup(S) then
    Info(InfoSemigroups, 2, "the semigroup is not regular");
    return false;
  elif not IsFinite(S) then
    TryNextMethod();
  fi;

  if HasGeneratorsOfSemigroup(S) and
      IsGeneratorsOfInverseSemigroup(GeneratorsOfSemigroup(S)) and
      ForAll(GeneratorsOfSemigroup(S), x -> x ^ -1 in S) then
    return true;
  fi;

  if IsCompletelyRegularSemigroup(S) then
    Info(InfoSemigroups, 2, "the semigroup is completely regular");
    return IsCliffordSemigroup(S);
  elif IsActingSemigroup(S) then
    lambda := LambdaOrb(S);
    Enumerate(lambda);
    rho := RhoOrb(S);
    Enumerate(rho, Length(lambda) + 1);
    if not (IsClosedOrbit(rho) and Length(rho) = Length(lambda)) then
      Info(InfoSemigroups, 2,
           "the numbers of lambda and rho values are not equal");
      return false;
    fi;
  fi;

  if HasGreensDClasses(S) then
    iter := GreensDClasses(S);
    for x in iter do
      if not IsRegularGreensClass(x)
          or NrRClasses(x) <> NrLClasses(x)
          or NrIdempotents(x) <> NrRClasses(x) then
        return false;
      fi;
    od;
    return true;
  fi;

  return NrLClasses(S) = NrRClasses(S) and IsRegularSemigroup(S)
    and NrIdempotents(S) = NrRClasses(S);
end);

# same method for ideals

InstallMethod(IsLeftSimple, "for a semigroup", [IsSemigroup],
function(S)
  local iter;

  if HasIsRegularSemigroup(S) and not IsRegularSemigroup(S) then
    return false;
  elif not IsFinite(S) then
    TryNextMethod();
  elif HasNrLClasses(S) or HasGreensLClasses(S) then
    return NrLClasses(S) = 1;
  fi;

  if IsActingSemigroup(S) then
    iter := IteratorOfLClassReps(S);
    NextIterator(iter);
    return IsDoneIterator(iter);
  fi;

  return NrLClasses(S) = 1;
end);

# same method for ideals

InstallMethod(IsLeftSimple, "for an inverse semigroup",
[IsInverseSemigroup], IsGroupAsSemigroup);

# different method for ideals without generators

InstallMethod(IsLeftZeroSemigroup,
"for an acting semigroup with generators",
[IsActingSemigroup and HasGeneratorsOfSemigroup],
function(S)
  local gens, lambda, val, x;

  if HasParent(S) and HasIsLeftZeroSemigroup(Parent(S))
      and IsLeftZeroSemigroup(Parent(S)) then
    return true;
  fi;

  gens := GeneratorsOfSemigroup(S);
  lambda := LambdaFunc(S);
  val := lambda(gens[1]);

  for x in gens do
    if not lambda(x) = val then
      return false;
    fi;
  od;

  return ForAll(gens, IsIdempotent);
end);

# works for finite and infinite

InstallMethod(IsLeftZeroSemigroup, "for a semigroup", [IsSemigroup],
function(S)
  if HasParent(S) and HasIsLeftZeroSemigroup(Parent(S))
      and IsLeftZeroSemigroup(Parent(S)) then
    return true;
  elif not IsFinite(S) then
    TryNextMethod();
  fi;
  return IsLeftSimple(S) and IsRTrivial(S);
end);

# same method for ideals

InstallMethod(IsLeftZeroSemigroup, "for an inverse semigroup",
[IsInverseSemigroup], IsTrivial);

# not applicable for ideals

InstallImmediateMethod(IsMonogenicSemigroup,
IsSemigroup and IsFinite and HasGeneratorsOfSemigroup,
0,
function(S)
  local gens;

  gens := GeneratorsOfSemigroup(S);
  if Length(gens) <= 1 then
    SetMinimalSemigroupGeneratingSet(S, gens);
    return Length(gens) = 1;
  elif CanEasilyCompareElements(gens)
      and ForAll([2 .. Length(gens)], i -> gens[1] = gens[i]) then
    SetMinimalSemigroupGeneratingSet(S, [gens[1]]);
    return true;
  fi;
  TryNextMethod();
end);

InstallImmediateMethod(IsMonogenicMonoid,
IsMonoid and IsFinite and HasGeneratorsOfMonoid,
0,
function(S)
  local gens;

  gens := GeneratorsOfMonoid(S);
  if Length(gens) <= 1 then
    SetMinimalMonoidGeneratingSet(S, gens);
    return true;
  elif CanEasilyCompareElements(gens)
      and ForAll([2 .. Length(gens)], i -> gens[1] = gens[i]) then
    SetMinimalMonoidGeneratingSet(S, [gens[1]]);
    return true;
  fi;
  TryNextMethod();
end);

# same method for ideals

InstallMethod(IsMonogenicSemigroup, "for a semigroup",
[IsSemigroup],
function(S)
  local I, gens, y, i;

  if HasGeneratorsOfSemigroup(S) then
    gens := GeneratorsOfSemigroup(S);

    if not IsDuplicateFreeList(gens) then
      gens := ShallowCopy(DuplicateFreeList(gens));
      Info(InfoSemigroups, 2, "there are repeated generators");
    fi;

    if Length(gens) = 1 then
      Info(InfoSemigroups, 2, "the semigroup only has one generator");
      SetMinimalSemigroupGeneratingSet(S, gens);
      return true;
    fi;
  fi;

  if not IsFinite(S) then
    TryNextMethod();
  fi;

  I := MinimalIdeal(S);

  if not (IsGroup(I) or IsGroupAsSemigroup(I)) then
    Info(InfoSemigroups, 2, "the minimal ideal is not a group.");
    return false;
  elif not IsCyclic(Range(IsomorphismPermGroup(I))) then
    Info(InfoSemigroups, 2, "the minimal ideal is a non-cyclic group.");
    return false;
  fi;

  if HasGreensDClasses(S) then
    i := NrDClasses(S);
    if not IsTrivial(I) then
      i := i - 1;
    fi;
    if i <> Number(GreensDClasses(S), IsTrivial) then
      return false;
    fi;
  fi;

  gens := GeneratorsOfSemigroup(S);

  for i in [1 .. Length(gens)] do
    y := gens[i];
    if ForAll(gens, x -> x in Semigroup(y)) then
      Info(InfoSemigroups, 2, "the semigroup is generated by generator ", i);
      SetMinimalSemigroupGeneratingSet(S, [y]);
      return true;
    fi;
  od;
  Info(InfoSemigroups, 2, "at least one generator does not belong to the",
       " semigroup generated by any ");
  Info(InfoSemigroups, 2, "other generator.");
  return false;
end);

# same method for ideals

InstallMethod(IsMonogenicInverseSemigroup, "for a semigroup",
[IsSemigroup],
function(S)
  if not IsInverseSemigroup(S) then
    return false;
  elif not IsFinite(S) then
    TryNextMethod();
  fi;
  return IsMonogenicInverseSemigroup(AsSemigroup(IsPartialPermSemigroup, S));
end);

# same method for ideals

InstallMethod(IsMonogenicInverseSemigroup,
"for an inverse semigroup with inverse op",
[IsInverseSemigroup and IsGeneratorsOfInverseSemigroup],
function(S)
  local gens, I, y, i;

  if HasGeneratorsOfInverseSemigroup(S) then
    gens := GeneratorsOfInverseSemigroup(S);

    if not IsDuplicateFreeList(gens) then
      gens := ShallowCopy(DuplicateFreeList(gens));
      Info(InfoSemigroups, 2, "there are repeated generators");
    fi;

    if Length(gens) = 1 then
      Info(InfoSemigroups, 2, "the inverse semigroup only has one generator");
      SetMinimalInverseSemigroupGeneratingSet(S, gens);
      return true;
    fi;
  fi;

  if not IsFinite(S) then
    TryNextMethod();
  fi;

  I := MinimalIdeal(S);

  if not IsCyclic(Range(IsomorphismPermGroup(I))) then
    Info(InfoSemigroups, 2, "the minimal ideal is a non-cyclic group.");
    return false;
  fi;

  gens := GeneratorsOfInverseSemigroup(S);

  for i in [1 .. Length(gens)] do
    y := gens[i];
    if ForAll(gens, x -> x in InverseSemigroup(y)) then
      Info(InfoSemigroups, 2, "the inverse semigroup is generated by ",
                              "generator ", i);
      SetMinimalInverseSemigroupGeneratingSet(S, [y]);
      return true;
    fi;
  od;

  Info(InfoSemigroups, 2, "at least one generator does not belong to the",
       " inverse semigroup generated by any ");
  Info(InfoSemigroups, 2, "other generator.");
  return false;
end);

InstallMethod(IsMonogenicMonoid, "for a monoid",
[IsMonoid],
function(S)
  local I, gens, y, i;

  if HasGeneratorsOfMonoid(S) then
    gens := GeneratorsOfMonoid(S);

    if not IsDuplicateFreeList(gens) then
      gens := ShallowCopy(DuplicateFreeList(gens));
      Info(InfoSemigroups, 2, "there are repeated generators");
    fi;

    if Length(gens) = 1 then
      Info(InfoSemigroups, 2, "the monoid only has one generator");
      SetMinimalMonoidGeneratingSet(S, gens);
      return true;
    fi;
  fi;

  if not IsFinite(S) then
    TryNextMethod();
  fi;

  I := MinimalIdeal(S);

  if not (IsGroup(I) or IsGroupAsSemigroup(I)) then
    Info(InfoSemigroups, 2, "the minimal ideal is not a group.");
    return false;
  elif not IsCyclic(Range(IsomorphismPermGroup(I))) then
    Info(InfoSemigroups, 2, "the minimal ideal is a non-cyclic group.");
    return false;
  fi;

  if HasGreensDClasses(S) then
    i := NrDClasses(S);
    if not IsTrivial(I) then
      i := i - 1;
    fi;
    if i <> Number(GreensDClasses(S), IsTrivial) then
      return false;
    fi;
  fi;

  gens := GeneratorsOfMonoid(S);

  for i in [1 .. Length(gens)] do
    y := gens[i];
    if ForAll(gens, x -> x in Monoid(y)) then
      Info(InfoSemigroups, 2, "the monoid is generated by generator ", i);
      SetMinimalMonoidGeneratingSet(S, [y]);
      return true;
    fi;
  od;
  Info(InfoSemigroups, 2, "at least one generator does not belong to the",
       " monoid generated by any ");
  Info(InfoSemigroups, 2, "other generator.");
  return false;
end);

InstallMethod(IsMonogenicInverseMonoid, "for a monoid",
[IsMonoid],
function(S)
  if not IsInverseMonoid(S) then
    return false;
  elif not IsFinite(S) then
    TryNextMethod();
  fi;
  return IsMonogenicInverseMonoid(AsMonoid(IsPartialPermMonoid, S));
end);

InstallMethod(IsMonogenicInverseMonoid,
"for an inverse monoid with inverse op",
[IsInverseMonoid and IsGeneratorsOfInverseSemigroup],
function(S)
  local gens, I, y, i;

  if HasGeneratorsOfInverseMonoid(S) then
    gens := GeneratorsOfInverseMonoid(S);

    if not IsDuplicateFreeList(gens) then
      gens := ShallowCopy(DuplicateFreeList(gens));
      Info(InfoSemigroups, 2, "there are repeated generators");
    fi;

    if Length(gens) = 1 then
      Info(InfoSemigroups, 2, "the inverse monoid only has one generator");
      SetMinimalInverseMonoidGeneratingSet(S, gens);
      return true;
    fi;
  fi;

  if not IsFinite(S) then
    # WW I can not find an example of an example of an infinite inverse monoid
    # with InverseOp - FreeGroup(1) should work, but it is not in the category
    TryNextMethod();
  fi;

  I := MinimalIdeal(S);

  if not IsCyclic(Range(IsomorphismPermGroup(I))) then
    Info(InfoSemigroups, 2, "the minimal ideal is a non-cyclic group.");
    return false;
  fi;

  gens := GeneratorsOfInverseMonoid(S);

  for i in [1 .. Length(gens)] do
    y := gens[i];
    if ForAll(gens, x -> x in InverseMonoid(y)) then
      Info(InfoSemigroups, 2, "the inverse monoid is generated by generator ",
                              i);
      SetMinimalInverseMonoidGeneratingSet(S, [y]);
      return true;
    fi;
  od;

  Info(InfoSemigroups, 2, "at least one generator does not belong to the",
       " inverse monoid generated by any ");
  Info(InfoSemigroups, 2, "other generator.");
  return false;
end);

# same method for ideals

InstallMethod(IsMonoidAsSemigroup, "for a semigroup",
[IsSemigroup],
function(S)
  return MultiplicativeNeutralElement(S) <> fail;
end);

# is there a better method? JDM
# same method for ideals

InstallMethod(IsOrthodoxSemigroup, "for a semigroup",
[IsSemigroup], SUM_FLAGS,  # to beat the Smallsemi method
function(S)
  if not IsFinite(S) then
    # WW we can not test the following line, since the error message we
    # eventually get depends on whether or not Smallsemi is loaded
    TryNextMethod();
  elif not IsRegularSemigroup(S) then
    Info(InfoSemigroups, 2, "the semigroup is not regular");
    return false;
  fi;
  Info(InfoSemigroups, 2, "the idempotents do not form a subsemigroup");
  return IsSemigroupWithClosedIdempotents(S);
end);

InstallMethod(IsSemigroupWithClosedIdempotents, "for a semigroup",
[IsSemigroup],
function(S)
  local e, m, i, j;

  if not IsFinite(S) then
    TryNextMethod();
  fi;

  e := Idempotents(S);
  m := NrIdempotents(S);

  for i in [1 .. m] do
    for j in [i + 1 .. m] do
      if not IsIdempotent(e[i] * e[j]) or not IsIdempotent(e[j] * e[i]) then
        Info(InfoSemigroups, 2, "the product of idempotents ", i, " and ", j,
             " (in some order) is not idempotent");
        return false;
      fi;
    od;
  od;
  return true;
end);

InstallTrueMethod(IsSemigroupWithClosedIdempotents,
                  IsSemigroupWithCommutingIdempotents);

# same method for ideals, works for finite and infinite

InstallMethod(IsRectangularBand, "for a semigroup",
[IsSemigroup],
function(S)

  if HasParent(S) and HasIsRectangularBand(Parent(S))
      and IsRectangularBand(Parent(S)) then
    return true;
  elif not IsFinite(S) then
    TryNextMethod();
  fi;

  # the following is not true for infinite semigroups:
  # the bicyclic monoid is a simple h-trivial semigroup which is not a band

  if not IsSimpleSemigroup(S) then
    Info(InfoSemigroups, 2, "the semigroup is not simple");
    return false;
  elif HasIsBand(S) then
    return IsBand(S);
  fi;

  return IsHTrivial(S);
end);

# same method for ideals

InstallMethod(IsRectangularBand, "for an inverse semigroup",
[IsInverseSemigroup], IsTrivial);

# different method for ideals (ideals know at their point of creation if they
# are regular or not)

InstallMethod(IsRegularSemigroup, "for an acting semigroup with generators",
[IsActingSemigroup and HasGeneratorsOfSemigroup],
function(S)
  local tester, rhofunc, lookfunc, data, i;

  if IsSimpleSemigroup(S) then
    Info(InfoSemigroups, 2, "the semigroup is simple");
    return true;
  elif HasIsCompletelyRegularSemigroup(S)
      and IsCompletelyRegularSemigroup(S) then
    Info(InfoSemigroups, 2, "the semigroup is completely regular");
    return true;
  elif HasGreensDClasses(S) then
    return ForAll(GreensDClasses(S), IsRegularDClass);
  fi;

  tester := IdempotentTester(S);
  rhofunc := RhoFunc(S);

  # look for <S> not being regular
  lookfunc := function(data, x)
    local rho, scc, i;
    if data!.repslens[x[2]][data!.orblookup1[x[6]]] > 1 then
      return true;
    fi;

    # data corresponds to the group of units...
    if IsActingSemigroupWithFixedDegreeMultiplication(S)
        and ActionRank(S)(x[4]) = ActionDegree(x[4]) then
      return false;
    fi;

    rho := rhofunc(x[4]);
    scc := OrbSCC(x[3])[x[2]];
    for i in scc do
      if tester(x[3][i], rho) then
        return false;
      fi;
    od;
    return true;
  end;

  data := SemigroupData(S);

  for i in [2 .. Length(data)] do
    if lookfunc(data, data[i]) then
      return false;
    fi;
  od;

  if IsClosedData(data) then
    return true;
  fi;

  data := Enumerate(data, infinity, lookfunc);
  return data!.found = false;
end);

# InstallMethod(IsRegularSemigroup,
# "for an acting star semigroup with generators",
# [IsActingSemigroup and IsStarSemigroup and HasGeneratorsOfSemigroup],
# function(S)
#   local lookfunc, data, i;
#
#   if IsSimpleSemigroup(S) then
#     Info(InfoSemigroups, 2, "the semigroup is simple");
#     return true;
#   elif HasIsCompletelyRegularSemigroup(S)
#       and IsCompletelyRegularSemigroup(S) then
#     Info(InfoSemigroups, 2, "the semigroup is completely regular");
#     return true;
#   elif HasGreensDClasses(S) then
#     return ForAll(GreensDClasses(S), IsRegularDClass);
#   fi;
#
#   # look for <S> not being regular
#   lookfunc := function(data, x)
#     local l;
#     if data!.repslens[x[2]][data!.orblookup1[x[6]]] > 1 then
#       return true;
#     fi;
#
#     # data corresponds to the group of units...
#     if IsActingSemigroupWithFixedDegreeMultiplication(S)
#         and ActionRank(S)(x[4]) = ActionDegree(x[4]) then
#       return false;
#     fi;
#     #check that the rho value of <x> is in the same scc as the lambda value of
#     #<x>
#     l := Position(x[3], RhoFunc(S)(x[4]));
#     return l = fail or OrbSCCLookup(x[3])[l] <> x[2];
#   end;
#
#   data := SemigroupData(S);
#
#   for i in [2 .. Length(data)] do
#     if lookfunc(data, data[i]) then
#       return false;
#     fi;
#   od;
#
#   if IsClosedData(data) then
#     return true;
#   fi;
#
#   data := Enumerate(data, infinity, lookfunc);
#   return data!.found = false;
# end);

# same method for ideals

InstallMethod(IsRegularSemigroupElement,
"for an acting semigroup and multiplicative element",
[IsActingSemigroup, IsMultiplicativeElement],
function(S, x)
  local o, scc, rho, tester, i;

  if not x in S then
    Info(InfoSemigroups, 2, "the element does not belong to the semigroup,");
    return false;
  fi;

  if HasIsRegularSemigroup(S) and IsRegularSemigroup(S) then
    Info(InfoSemigroups, 2, "the semigroup is regular,");
    return true;
  fi;

  o := LambdaOrb(S);
  scc := OrbSCC(o)[OrbSCCLookup(o)[Position(o, LambdaFunc(S)(x))]];
  rho := RhoFunc(S)(x);
  tester := IdempotentTester(S);

  for i in scc do
    if tester(o[i], rho) then
      return true;
    fi;
  od;
  return false;
end);

# InstallMethod(IsRegularSemigroupElement,
# "for an acting star semigroup and associative element with star",
# [IsActingSemigroup and IsStarSemigroup, IsAssociativeElementWithStar],
# function(S, x)
#   local o, k, l;
#
#   if not x in S then
#     Info(InfoSemigroups, 2, "the element does not belong to the semigroup,");
#     return false;
#   fi;
#
#   if HasIsRegularSemigroup(S) and IsRegularSemigroup(S) then
#     Info(InfoSemigroups, 2, "the semigroup is regular,");
#     return true;
#   fi;
#
#   o := LambdaOrb(S);
#   k := Position(o, LambdaFunc(S)(x));
#   l := Position(o, RhoFunc(S)(x));
#
#   return l <> fail and OrbSCCLookup(o)[k] = OrbSCCLookup(o)[l];
# end);

# same method for ideals

InstallMethod(IsRegularSemigroupElementNC,
"for an acting semigroup and multiplicative element",
[IsActingSemigroup, IsMultiplicativeElement],
function(S, x)
  local o, l, scc, rho, tester, i;

   if IsClosedOrbit(LambdaOrb(S)) then
    o := LambdaOrb(S);
    l := Position(o, LambdaFunc(S)(x));
    if l = fail then
      return false;
    fi;
  else
    # this has to be false, since we're not sure if <x> in <S>
    o := GradedLambdaOrb(S, x, false);
    l := 1;
  fi;

  scc := OrbSCC(o)[OrbSCCLookup(o)[l]];
  rho := RhoFunc(S)(x);
  tester := IdempotentTester(S);

  for i in scc do
    if tester(o[i], rho) then
      return true;
    fi;
  od;
  return false;
end);

# InstallMethod(IsRegularSemigroupElementNC,
# "for an acting semigroup with star and associative element with star",
# [IsActingSemigroup and IsStarSemigroup, IsAssociativeElementWithStar],
# function(S, x)
#   local o, k, l;
#
#    if IsClosedOrbit(LambdaOrb(S)) then
#     o := LambdaOrb(S);
#     k := Position(o, LambdaFunc(S)(x));
#     if k = fail then
#       return false;
#     fi;
#   else
#     # this has to be false, since we're not sure if <x> in <S>
#     o := GradedLambdaOrb(S, x, false);
#     k := 1;
#   fi;
#   l := EnumeratePosition(o, RhoFunc(S)(x));
#   return l <> fail and OrbSCCLookup(o)[k] = OrbSCCLookup(o)[l];
# end);

InstallMethod(IsRegularSemigroupElementNC,
[IsSemigroup, IsMultiplicativeElement], IsRegularSemigroupElement);

InstallMethod(IsRegularSemigroupElement, "for semigroup", IsCollsElms,
[IsSemigroup, IsMultiplicativeElement],
function(S, x)
  return x in S and IsRegularGreensClass(RClass(S, x));
end);

# same method for ideals

InstallMethod(IsRightSimple, "for a semigroup", [IsSemigroup],
function(S)
  local iter;

  if HasIsRegularSemigroup(S) and not IsRegularSemigroup(S) then
    return false;
  elif not IsFinite(S) then
    TryNextMethod();
  elif IsActingSemigroup(S) and not HasNrRClasses(S) then
    iter := IteratorOfRClassData(S);
    NextIterator(iter);
    return IsDoneIterator(iter);
  fi;
  return NrRClasses(S) = 1;
end);

# same method for ideals

InstallMethod(IsRightSimple, "for an inverse semigroup",
[IsInverseSemigroup], IsGroupAsSemigroup);

# different method for ideals

InstallMethod(IsRightZeroSemigroup,
"for an acting semigroup with generators",
[IsActingSemigroup and HasGeneratorsOfSemigroup],
function(S)
  local gens, rho, val, x;

  if HasParent(S) and HasIsRightZeroSemigroup(Parent(S))
      and IsRightZeroSemigroup(Parent(S)) then
    return true;
  fi;

  gens := GeneratorsOfSemigroup(S);
  rho := RhoFunc(S);
  val := rho(gens[1]);
  for x in gens do
    if rho(x) <> val or not IsIdempotent(x) then
      return false;
    fi;
  od;

  return true;
end);

InstallMethod(IsRightZeroSemigroup, "for a semigroup",
[IsSemigroup],
function(S)
  if HasParent(S) and HasIsRightZeroSemigroup(Parent(S))
      and IsRightZeroSemigroup(Parent(S)) then
    return true;
  elif not IsFinite(S) then
    TryNextMethod();
  fi;
  return NrRClasses(S) = 1 and Size(S) = NrLClasses(S);
end);

# same method for ideals

InstallMethod(IsRightZeroSemigroup, "for an inverse semigroup",
[IsInverseSemigroup], IsTrivial);

# same method for ideals, FIXME make this a synonym?

InstallMethod(IsSemiband, "for a semigroup", [IsSemigroup],
IsIdempotentGenerated);

# same method for ideals

InstallMethod(IsSemilattice, "for a semigroup", [IsSemigroup],
function(S)
  # Do not have to check if HasParent(S) and HasIsSemilattice(Parent(S)) and
  # IsSemilattice(Parent(S)) since if this is true, then S is an inverse
  # semigroup and the method after the next is used in preference to this one
  return IsCommutativeSemigroup(S) and IsBand(S);
end);

# not applicable to ideals

InstallMethod(IsSemilattice,
"for an inverse semigroup with generators",
[IsInverseSemigroup and HasGeneratorsOfSemigroup],
function(S)
  if not IsFinite(S) then
    TryNextMethod();
  elif HasParent(S) and HasIsSemilattice(Parent(S))
      and IsSemilattice(Parent(S)) then
    return true;
  fi;
  return ForAll(GeneratorsOfSemigroup(S), IsIdempotent);
end);

# same method for ideals

InstallMethod(IsSemilattice, "for an inverse semigroup",
[IsInverseSemigroup],
function(S)
  if HasParent(S) and HasIsSemilattice(Parent(S))
      and IsSemilattice(Parent(S)) then
    return true;
  elif not IsFinite(S) then
    TryNextMethod();
  fi;
  return IsDTrivial(S);
end);

InstallMethod(IsSimpleSemigroup, "for a finite semigroup",
[IsSemigroup and IsFinite], S -> NrDClasses(S) = 1);

# same method for ideals

InstallMethod(IsSimpleSemigroup, "for an acting semigroup",
[IsActingSemigroup],
function(S)
  local gens, lambdafunc, lambdarank, rank, opts, o, pos, iter, name, f;

  if HasIsRegularSemigroup(S) and not IsRegularSemigroup(S) then
    Info(InfoSemigroups, 2, "the semigroup is not regular");
    return false;
  elif HasIsCompletelyRegularSemigroup(S)
      and not IsCompletelyRegularSemigroup(S) then
    Info(InfoSemigroups, 2, "the semigroup is not completely regular");
    return false;
  elif HasNrDClasses(S) then
    return NrDClasses(S) = 1;
  elif HasGeneratorsOfSemigroup(S) then
    gens := GeneratorsOfSemigroup(S);  # not GeneratorsOfMonoid!
    lambdafunc := LambdaFunc(S);
    lambdarank := LambdaRank(S);
    rank := lambdarank(lambdafunc(gens[1]));

    if not ForAll([2 .. Length(gens)],
                  i -> lambdarank(lambdafunc(gens[i])) = rank) then
      return false;
    fi;

    opts := rec(treehashsize := SEMIGROUPS.OptionsRec(S).hashlen);

    for name in RecNames(LambdaOrbOpts(S)) do
      opts.(name) := LambdaOrbOpts(S).(name);
    od;

    for f in gens do
      o := Orb(S, LambdaFunc(S)(f), LambdaAct(S), opts);
      pos := LookForInOrb(o, function(o, x)
                               return LambdaRank(S)(x) < rank;
                             end, 1);
      if pos <> false then
        return false;
      fi;
    od;

    return true;
  fi;

  # regular ideal case
  iter := IteratorOfDClasses(S);
  NextIterator(iter);
  return IsDoneIterator(iter);
end);

# same method for ideals

InstallMethod(IsSimpleSemigroup, "for a finite inverse semigroup",
[IsInverseSemigroup and IsFinite],
IsGroupAsSemigroup);

# different method for ideals

InstallMethod(IsTrivial, "for a semigroup with generators",
[IsSemigroup and HasGeneratorsOfSemigroup],
function(S)
  local gens;

  if not IsFinite(S) then
    return false;
  fi;
  gens := GeneratorsOfSemigroup(S);
  return Length(gens) > 0 and IsIdempotent(gens[1])
         and ForAll(gens, x -> gens[1] = x);
end);

# same method for ideals

InstallMethod(IsUnitRegularMonoid, "for an acting semigroup",
[IsActingSemigroup],
function(S)
  local G, H, o, scc, graded, tester, gens, rhofunc, dom, rho, rep, m, j;

  if not (IsTransformationSemigroup(S) or IsPartialPermSemigroup(S)) then
    TryNextMethod();
  elif not IsRegularSemigroup(S) then
    return false;
  fi;

  G := GroupOfUnits(S);

  if G = fail then
    return false;
  elif IsTrivial(G) then
    return IsBand(S);
  fi;

  H       := Range(IsomorphismPermGroup(G));
  o       := LambdaOrb(S);
  scc     := OrbSCC(o);
  graded  := GradedLambdaOrbs(G);
  tester  := IdempotentTester(S);
  gens    := o!.gens;
  rhofunc := RhoFunc(S);

  for m in [2 .. Length(scc)] do
    dom := Union(Orbits(H, o[scc[m][1]], OnPoints));
    if not IsSubgroup(Action(H, dom),
                      Action(LambdaOrbSchutzGp(o, m), o[scc[m][1]])) then
      return false;
    elif Length(scc[m]) > 1 then
      rho := rhofunc(EvaluateWord(gens,
                                  TraceSchreierTreeForward(o, scc[m][1])));
      for j in scc[m] do
        if not o[j] in graded then
          rep := EvaluateWord(gens, TraceSchreierTreeForward(o, j));
          if not ForAny(GradedLambdaOrb(G, rep, true), x -> tester(x, rho))
              then
            return false;
          fi;
        fi;
      od;
    fi;
  od;
  return true;
end);

InstallMethod(IsUnitRegularMonoid, "for a semigroup",
[IsSemigroup],
function(S)
  local G, x;

  if not IsRegularSemigroup(S) then
    return false;
  elif not IsFinite(S) then
    TryNextMethod();
  fi;

  G := GroupOfUnits(S);

  if G = fail then
    return false;
  elif IsTrivial(G) then
    return IsBand(S);
  fi;

  for x in S do
    if ForAll(G, y -> x * y * x <> x) then
      return false;
    fi;
  od;
  return true;
end);

# same method for ideals

InstallMethod(IsZeroGroup, "for a semigroup",
[IsSemigroup],
function(S)

  if HasParent(S) and HasIsZeroGroup(Parent(S)) and IsZeroGroup(Parent(S)) then
    return S = Parent(S);
  elif not IsFinite(S) then
    TryNextMethod();
  fi;

  if MultiplicativeZero(S) = fail then
    Info(InfoSemigroups, 2, "the semigroup does not have a zero");
    return false;
  fi;

  if NrHClasses(S) = 2 then
    return ForAll(GreensHClasses(S), IsGroupHClass);
  fi;

  Info(InfoSemigroups, 2, "the semigroup has more than two H-classes");
  return false;
end);

# same method for ideals

InstallMethod(IsZeroRectangularBand, "for a semigroup",
[IsSemigroup],
function(S)

  if not IsFinite(S) then
    TryNextMethod();
  elif not IsZeroSimpleSemigroup(S) then
    Info(InfoSemigroups, 2, "the semigroup is not 0-simple");
    return false;
  fi;

  return IsHTrivial(S);
end);

# different method for ideals

InstallMethod(IsZeroSemigroup, "for a semigroup", [IsSemigroup],
function(S)
  local z, gens, i, j;

  if HasParent(S) and HasIsZeroSemigroup(Parent(S))
      and IsZeroSemigroup(Parent(S)) then
    return true;
  elif not IsFinite(S) then
    TryNextMethod();
  fi;

  z := MultiplicativeZero(S);

  if z = fail then
    Info(InfoSemigroups, 2, "the semigroup does not have a zero");
    return false;
  fi;

  gens := GeneratorsOfSemigroup(S);
  for i in [1 .. Length(gens)] do
    for j in [1 .. Length(gens)] do
      if not gens[i] * gens[j] = z then
        Info(InfoSemigroups, 2, "the product of generators ", i, " and ", j,
             " is not the multiplicative zero \n", z);
        return false;
      fi;
    od;
  od;

  return true;
end);

# same method for ideals

InstallMethod(IsZeroSemigroup, "for an inverse semigroup",
[IsInverseSemigroup], IsTrivial);

# same method for ideals

InstallMethod(IsZeroSimpleSemigroup, "for an acting semigroup",
[IsActingSemigroup],
function(S)
  local iter, D;

  if MultiplicativeZero(S) = fail then
    return false;
  elif IsClosedData(SemigroupData(S)) then
    return IsRegularSemigroup(S) and NrDClasses(S) = 2;
  fi;
  iter := IteratorOfDClasses(S);
  D := NextIterator(iter);
  if IsDoneIterator(iter) or not IsRegularDClass(D) then
    return false;
  fi;
  D := NextIterator(iter);
  return IsDoneIterator(iter) and IsRegularDClass(D);
end);

# same method for ideals

InstallMethod(IsZeroSimpleSemigroup, "for a semigroup",
[IsSemigroup], 1,  # to beat the library method
function(S)
  if not IsFinite(S) then
    TryNextMethod();
  fi;

  return MultiplicativeZero(S) <> fail and NrDClasses(S) = 2 and
         IsRegularSemigroup(S);
end);

# same method for ideals

InstallMethod(IsZeroSimpleSemigroup, "for a finite inverse semigroup",
[IsInverseSemigroup and IsFinite],
S -> MultiplicativeZero(S) <> fail and NrDClasses(S) = 2);

InstallMethod(IsNilpotentSemigroup, "for a semigroup",
[IsSemigroup],
function(S)
  if not IsFinite(S) then
    TryNextMethod();
  fi;

  if HasNrIdempotents(S) and NrIdempotents(S) <> 1 then
    return false;
  fi;
  if MultiplicativeZero(S) = fail then
    return false;
  fi;
  return NrIdempotents(S) = 1;
end);

# WW the following lets us get higher code coverage

InstallMethod(IsFinite, "for a finitely presented semigroup",
[IsFpSemigroup],
function(S)
  if IsEmpty(RelationsOfFpSemigroup(S)) or
      ForAll(RelationsOfFpSemigroup(S), x -> IsIdenticalObj(x[1], x[2])) then
    # TODO add nr gens is higher than nr relations
    return false;
  fi;
  TryNextMethod();
end);

InstallMethod(IsSemigroupWithAdjoinedZero, "for a semigroup", [IsSemigroup],
x -> UnderlyingSemigroupOfSemigroupWithAdjoinedZero(x) <> fail);

InstallMethod(IsSurjectiveSemigroup, "for a semigroup",
[IsSemigroup],
S -> IsEmpty(IndecomposableElements(S)));

InstallMethod(IsCryptoGroup, "for a semigroup", [IsSemigroup],
function(S)
  local H, A, s, C, gens, PairsInHRelation, NrH, LookUp, pair, pos1, pos2;
  if not IsCompletelyRegularSemigroup(S) then
    return false;
  fi;
  H := GreensHRelation(S);
  PairsInHRelation := [];
  NrH := NrHClasses(S);
  # create a list of pairs generating Greens H-relation as an equiv. relation.
  for A in EquivalenceClasses(H) do
    for s in A do
      Add(PairsInHRelation, [s, Representative(A)]);
    od;
  od;
  gens := [];
  C := SemigroupCongruence(S, gens);
  LookUp := EquivalenceRelationCanonicalLookup(C);
  for pair in PairsInHRelation do
    pos1 := LookUp[PositionCanonical(S, pair[1])];
    pos2 := LookUp[PositionCanonical(S, pair[2])];
    if not pos1 = pos2 then
      Add(gens, pair);
      C := SemigroupCongruence(S, gens);
      if NrCongruenceClasses(C) < NrH then
        return false;
      fi;
      LookUp := EquivalenceRelationCanonicalLookup(C);
    fi;
  od;
  return true;
end);