#############################################################################
##
##  attributes/attr.gi
##  Copyright (C) 2013-2022                              James D. Mitchell
##
##  Licensing information can be found in the README file of this package.
##
#############################################################################
##

# This file contains methods for finding various attributes of finite
# semigroups, which satisfy CanUseFroidurePin or where no better method is
# known.

# Note about the difference between One and MultiplicativeNeutralElement
# (the same goes for Zero and MultplicativeZero):
#
# One(s) returns One(Representative(s)) if it belongs to s, so that
# One(s) = Transformation([1 .. DegreeOfTransformationSemigroup(s)]) if s is a
# transformation semigroup and it returns fail otherwise, or it returns
# PartialPerm([1 .. DegreeOfPartialPermSemigroup]) if this belongs to s.
#
# MultiplicativeNeutralElement on the other hand returns the element of s that
# acts as the identity, note that this can be equal to One(s) but it can also
# not be equal to One(s).
#
# A semigroup satisfies IsMonoidAsSemigroup(s) if
# MultiplicativeNeutralElement(x) <> fail, so it could be that One(s) returns
# fail but IsMonoidAsSemigroup is still true.

SEMIGROUPS.InjectionPrincipalFactor := function(D, constructor)
  local map, inv, G, mat, rep, R, L, x, RR, LL, rms, iso, hom, i, j;

  map := IsomorphismPermGroup(GroupHClass(D));
  inv := InverseGeneralMapping(map);

  G := Range(map);
  mat := [];
  rep := MultiplicativeNeutralElement(GroupHClass(D));
  R := HClassReps(LClass(D, rep));
  L := HClassReps(RClass(D, rep));

  for i in [1 .. Length(L)] do
    mat[i] := [];
    for j in [1 .. Length(R)] do
      x := L[i] * R[j];
      if x in D then
        mat[i][j] := x ^ map;
      else
        mat[i][j] := 0;
      fi;
    od;
  od;

  RR := EmptyPlist(Length(R));
  LL := EmptyPlist(Length(L));

  for j in [1 .. Length(R)] do
    for i in [1 .. Length(L)] do
      if mat[i][j] <> 0 then
        RR[j] := ((mat[i][j] ^ -1) ^ inv) * L[i];
        break;
      fi;
    od;
  od;

  for i in [1 .. Length(L)] do
    for j in [1 .. Length(R)] do
      if mat[i][j] <> 0 then
        LL[i] := R[j] * (mat[i][j] ^ -1) ^ inv;
        break;
      fi;
    od;
  od;

  rms := constructor(G, mat);

  iso := function(x)
    local i, j;

    if not x in D then
      return fail;
    fi;

    i := PositionProperty(R, y -> y in RClass(D, x));
    j := PositionProperty(L, y -> y in LClass(D, x));

    return Objectify(TypeReesMatrixSemigroupElements(rms),
                     [i, (rep * RR[i] * x * LL[j]) ^ map, j, mat]);
  end;

  inv := function(x)
    if x![1] = 0 then
      return fail;
    fi;
    return R[x![1]] * (x![2] ^ InverseGeneralMapping(map)) * L[x![3]];
  end;
  hom := MappingByFunction(D, rms, iso, inv);
  SetIsInjective(hom, true);
  SetIsTotal(hom, true);
  return hom;
end;

#############################################################################
## 1. Default methods, for which there are currently no better methods.
#############################################################################

# Don't use ClosureSemigroup here since the order of the generators matters
# and ClosureSemigroup shuffles the generators.

InstallMethod(GeneratorsSmallest,
"for a semigroup with CanUseFroidurePin",
[CanUseFroidurePin],
function(S)
  local iter, gens, T, closure, x;

  iter := IteratorSorted(S);
  gens := [NextIterator(iter)];
  T    := Semigroup(gens);

  if CanUseLibsemigroupsFroidurePin(S) then
    closure := {S, coll, opts} ->
               ClosureSemigroupOrMonoidNC(Semigroup, S, coll, opts);
  else
    closure := ClosureSemigroup;
  fi;

  for x in iter do
    if not x in T then
      T := closure(T, [x], SEMIGROUPS.OptionsRec(T));
      Add(gens, x);
      if T = S then
        break;
      fi;
    fi;
  od;
  return gens;
end);

InstallMethod(SmallestElementSemigroup, "for a semigroup",
[IsSemigroup],
function(S)
  if not IsFinite(S) then
    TryNextMethod();
  fi;
  return NextIterator(IteratorSorted(S));
end);

InstallMethod(LargestElementSemigroup, "for a semigroup",
[IsSemigroup],
function(S)
  if not IsFinite(S) then
    TryNextMethod();
  fi;
  return EnumeratorSorted(S)[Size(S)];
end);

InstallMethod(NrIdempotents, "for a semigroup", [IsSemigroup],
S -> Length(Idempotents(S)));

InstallMethod(GroupOfUnits, "for a semigroup", [IsSemigroup],
function(S)
  local H, map, U, iso;

  if not IsFinite(S) then
    TryNextMethod();
  elif MultiplicativeNeutralElement(S) = fail then
    return fail;
  fi;

  H := GreensHClassOfElementNC(S, MultiplicativeNeutralElement(S));
  map := IsomorphismPermGroup(H);

  U := Semigroup(List(GeneratorsOfGroup(Range(map)),
                      x -> x ^ InverseGeneralMapping(map)));

  iso := SemigroupIsomorphismByFunctionNC(U,
                                          Range(map),
                                          x -> x ^ map,
                                          x -> x ^ InverseGeneralMapping(map));
  SetIsomorphismPermGroup(U, iso);
  SetIsGroupAsSemigroup(U, true);
  UseIsomorphismRelation(U, Range(iso));
  return U;
end);

# same method for ideals

InstallMethod(IsomorphismReesMatrixSemigroup, "for a D-class",
[IsGreensDClass],
function(D)
  if NrIdempotents(D) <> NrHClasses(D) then
    ErrorNoReturn("the argument (a Green's D-class) is not a semigroup");
  fi;

  return InjectionPrincipalFactor(D);
end);

# same method for ideal

InstallMethod(IrredundantGeneratingSubset,
"for a multiplicative element collection",
[IsMultiplicativeElementCollection],
function(coll)
  local gens, nrgens, deg, out, redund, i, x;

  if (IsSemigroup(coll) and HasGeneratorsOfSemigroup(coll))
      or (HasIsSemigroupIdeal(coll) and IsSemigroupIdeal(coll)) then
    coll := ShallowCopy(GeneratorsOfSemigroup(coll));
  elif not IsMutable(coll) then
    coll := ShallowCopy(coll);
  fi;

  if Size(coll) = 1 then
    return coll;
  fi;

  gens := Set(coll);
  nrgens := Length(gens);

  if nrgens = 1 then
    return gens;
  elif IsGeneratorsOfActingSemigroup(coll) then
    deg := ActionDegree(coll);
    Shuffle(coll);
    Sort(coll, {x, y} -> ActionRank(x, deg) > ActionRank(y, deg));
  fi;

  out := EmptyPlist(Length(coll));
  redund := EmptyPlist(Length(coll));
  i := 0;

  repeat
    i := i + 1;
    x := coll[i];
    if InfoLevel(InfoSemigroups) >= 3 then
      PrintFormatted(
        "at \t{} of \t{} with \t{} redundant, \t{} non-redundant\n",
        i,
        Length(coll),
        Length(redund),
        Length(out));
    fi;

    if not x in redund and not x in out then
      if Length(gens) > 1 and x in Semigroup(Difference(gens, [x])) then
        AddSet(redund, x);
        gens := Difference(gens, [x]);
      else
        AddSet(out, x);
      fi;
    fi;
  until Length(redund) + Length(out) = nrgens;

  if InfoLevel(InfoSemigroups) >= 3 then
    Print("\n");
  fi;

  return out;
end);

# same method for ideals

InstallMethod(MinimalIdeal, "for a semigroup",
[IsSemigroup],
function(S)
  local I;
  if not IsFinite(S) then
    TryNextMethod();
  fi;
  I := SemigroupIdealByGeneratorsNC(S,
                                    [RepresentativeOfMinimalIdeal(S)],
                                    SEMIGROUPS.OptionsRec(S));
  SetIsSimpleSemigroup(I, true);
  return I;
end);

InstallMethod(PrincipalFactor, "for a Green's D-class",
[IsGreensDClass], D -> Range(InjectionPrincipalFactor(D)));

InstallMethod(NormalizedPrincipalFactor, "for a Green's D-class",
[IsGreensDClass], D -> Range(InjectionNormalizedPrincipalFactor(D)));

# different method for ideals, not yet implemented

InstallMethod(SmallSemigroupGeneratingSet, "for a list or collection",
[IsListOrCollection],
function(coll)
  if Length(coll) < 2 then
    return coll;
  fi;
  return GeneratorsOfSemigroup(Semigroup(coll, rec(small := true)));
end);

# different method for ideals, not yet implemented

InstallMethod(SmallSemigroupGeneratingSet,
"for a finite semigroup", [IsSemigroup and IsFinite],
S -> SmallSemigroupGeneratingSet(GeneratorsOfSemigroup(S)));

InstallMethod(SmallMonoidGeneratingSet,
"for a multiplicative element with one collection",
[IsMultiplicativeElementWithOneCollection],
function(coll)
  if Length(coll) < 2 then
    return coll;
  fi;
  return GeneratorsOfMonoid(Monoid(coll, rec(small := true)));
end);

# same method for ideals

InstallMethod(SmallMonoidGeneratingSet, "for a finite monoid",
[IsFinite and IsMonoid],
function(S)
  if Length(GeneratorsOfMonoid(S)) < 2 then
    return GeneratorsOfMonoid(S);
  fi;
  return SmallMonoidGeneratingSet(GeneratorsOfMonoid(S));
end);

InstallMethod(SmallInverseSemigroupGeneratingSet,
"for a multiplicative element coll",
[IsMultiplicativeElementCollection],
function(coll)
  if not IsGeneratorsOfInverseSemigroup(coll) then
    ErrorNoReturn("the argument (a mult. elt. coll.) does not ",
                  "satisfy IsGeneratorsOfInverseSemigroup");
  fi;
  if Length(coll) < 2 then
    return coll;
  fi;
  return GeneratorsOfInverseSemigroup(InverseSemigroup(coll,
                                                       rec(small := true)));
end);

InstallMethod(SmallInverseSemigroupGeneratingSet,
"for an inverse semigroup with inverse op",
[IsInverseSemigroup and IsGeneratorsOfInverseSemigroup],
S -> SmallSemigroupGeneratingSet(GeneratorsOfInverseSemigroup(S)));

InstallMethod(SmallInverseMonoidGeneratingSet,
"for generators of an inverse monoid",
[IsMultiplicativeElementWithOneCollection],
function(coll)
  if not IsGeneratorsOfInverseSemigroup(coll) then
    ErrorNoReturn("the argument (a mult. elt. coll.) do not satisfy ",
                  "IsGeneratorsOfInverseSemigroup");
  fi;
  # The empty list does not satisfy IsGeneratorsOfInverseSemigroup
  Assert(1, not IsEmpty(coll));
  if Length(coll) = 1 then
    if coll[1] = One(coll) then
      return [];
    fi;
    return coll;
  fi;
  return GeneratorsOfInverseMonoid(InverseMonoid(coll, rec(small := true)));
end);

InstallMethod(SmallInverseMonoidGeneratingSet,
"for an inverse monoid with inverse op",
[IsInverseMonoid and IsGeneratorsOfInverseSemigroup],
function(S)
  if IsEmpty(GeneratorsOfInverseMonoid(S)) then
    return GeneratorsOfInverseMonoid(S);
  fi;
  return SmallMonoidGeneratingSet(GeneratorsOfInverseMonoid(S));
end);

InstallMethod(SmallGeneratingSet, "for a semigroup",
[IsSemigroup],
function(S)

  if HasGeneratorsOfSemigroupIdeal(S) then
    return MinimalIdealGeneratingSet(S);
  elif HasGeneratorsOfInverseMonoid(S) then
    return SmallInverseMonoidGeneratingSet(S);
  elif HasGeneratorsOfInverseSemigroup(S) then
    return SmallInverseSemigroupGeneratingSet(S);
  elif HasGeneratorsOfMonoid(S) then
    return SmallMonoidGeneratingSet(S);
  fi;

  return SmallSemigroupGeneratingSet(S);
end);

InstallMethod(StructureDescription, "for a Brandt semigroup",
[IsBrandtSemigroup],
function(S)
  local D;
  D := MaximalDClasses(S)[1];
  return Concatenation("B(", StructureDescription(GroupHClass(D)), ", ",
                       String(NrRClasses(D)), ")");
end);

# same method for ideals

InstallMethod(StructureDescription, "for a group as semigroup",
[IsGroupAsSemigroup],
function(S)
  if IsGroup(S) then
    TryNextMethod();
  fi;
  return StructureDescription(Range(IsomorphismPermGroup(S)));
end);

# same method for ideals

InstallMethod(MultiplicativeZero, "for a semigroup",
[IsSemigroup],
function(S)
  local gens, D, rep;

  if IsSemigroupIdeal(S)
      and HasMultiplicativeZero(SupersemigroupOfIdeal(S)) then
    return MultiplicativeZero(SupersemigroupOfIdeal(S));
  elif HasMinimalDClass(S) then
    D := MinimalDClass(S);
    if HasSize(D) then
      if IsTrivial(D) then
        return Representative(D);
      fi;
      return fail;
    fi;
  elif IsSemigroupIdeal(S) then
    return MultiplicativeZero(SupersemigroupOfIdeal(S));
  elif not IsFinite(S) then
    Info(InfoWarning,
         1,
         "may not be able to find the multiplicative zero, ",
         "the semigroup is infinite");
    # Cannot currently test this line, because the next method runs forever
    TryNextMethod();
  fi;

  rep := RepresentativeOfMinimalIdeal(S);
  gens := GeneratorsOfSemigroup(S);

  if ForAll(gens, x -> x * rep = rep and rep * x = rep) then
    return rep;
  fi;

  return fail;
end);

InstallMethod(MultiplicativeZero, "for a free semigroup",
[IsFreeSemigroup], ReturnFail);

InstallMethod(MultiplicativeZero, "for a free inverse semigroup",
[IsFreeInverseSemigroup], ReturnFail);

InstallMethod(LengthOfLongestDClassChain, "for a semigroup",
[IsSemigroup],
function(S)
  local D, min;

  if not IsFinite(S) then
    TryNextMethod();
  fi;

  D := DigraphReverse(PartialOrderOfDClasses(S));
  Assert(1, Length(DigraphSources(D)) = 1);
  min := DigraphSources(D)[1];  # minimal D-class
  SetMinimalDClass(S, GreensDClasses(S)[min]);
  SetRepresentativeOfMinimalIdeal(S, Representative(
                                     GreensDClasses(S)[min]));

  return DigraphLongestDistanceFromVertex(D, min);
end);

InstallMethod(NilpotencyDegree, "for a finite semigroup",
[IsSemigroup and IsFinite],
function(S)
  if not IsNilpotentSemigroup(S) then
    return fail;
  fi;
  return LengthOfLongestDClassChain(S) + 1;
end);

InstallMethod(MinimalDClass, "for a semigroup", [IsSemigroup],
S -> GreensDClassOfElementNC(S, RepresentativeOfMinimalIdeal(S)));

#############################################################################
## 2. Methods for attributes where there are known better methods for acting
##    semigroups.
#############################################################################

InstallMethod(IsGreensDGreaterThanFunc,
"for a semigroup with CanUseFroidurePin",
[IsSemigroup and CanUseFroidurePin],
function(S)
  local D, id;

  if not IsFinite(S) then
    TryNextMethod();
  fi;

  D := PartialOrderOfDClasses(S);
  id := GreensDRelation(S)!.data.id;

  return function(x, y)
    local u, v;
    if x = y then
      return false;
    fi;
    u := id[PositionCanonical(S, x)];
    v := id[PositionCanonical(S, y)];
    return u <> v and IsReachable(D, u, v);
  end;
end);

InstallMethod(MaximalDClasses,
"for a semigroup with CanUseFroidurePin",
[IsSemigroup and CanUseFroidurePin],
function(S)
  local D;
  if NrDClasses(S) = 1 then
    return DClasses(S);
  fi;
  D := PartialOrderOfDClasses(S);
  return DClasses(S){DigraphSources(D)};
end);

InstallMethod(MaximalDClasses,
"for a finite monoid as semigroup with mult. neutral elt",
[IsFinite and IsMonoidAsSemigroup and HasMultiplicativeNeutralElement],
S -> [DClass(S, MultiplicativeNeutralElement(S))]);

InstallMethod(MaximalLClasses,
"for a semigroup that CanUseFroidurePin",
[IsSemigroup and CanUseFroidurePin],
function(S)

  if NrLClasses(S) = 1 then
    return LClasses(S);
  fi;

  return LClasses(S){DigraphSources(PartialOrderOfLClasses(S))};
end);

InstallMethod(MaximalRClasses,
"for a semigroup that CanUseFroidurePin",
[IsSemigroup and CanUseFroidurePin],
function(S)

  if NrRClasses(S) = 1 then
    return RClasses(S);
  fi;

  return RClasses(S){DigraphSources(PartialOrderOfRClasses(S))};
end);

# same method for ideals

InstallMethod(StructureDescriptionMaximalSubgroups,
"for a semigroup", [IsSemigroup],
function(S)
  local out, D;

  if not IsFinite(S) then
    TryNextMethod();
  fi;

  out := [];
  for D in RegularDClasses(S) do
    AddSet(out, StructureDescription(GroupHClass(D)));
  od;

  return out;
end);

InstallMethod(IdempotentGeneratedSubsemigroup, "for a semigroup",
[IsSemigroup],
function(S)
  local out;
  if not IsFinite(S) then
    TryNextMethod();
  fi;
  out := Semigroup(Idempotents(S), rec(small := true));
  SetIsIdempotentGenerated(out, true);
  if HasIsSemigroupWithCommutingIdempotents(S)
      and IsSemigroupWithCommutingIdempotents(S) then
    SetIsSemigroupWithCommutingIdempotents(out, true);
  fi;
  return out;
end);

InstallMethod(IdempotentGeneratedSubsemigroup,
"for a Rees matrix subsemigroup",
[IsReesMatrixSubsemigroup],
function(R)
  local mat, I, J, nrrows, nrcols, min, max, gens, out, i;

  if not IsFinite(R) or not IsReesMatrixSemigroup(R)
      or not IsGroup(UnderlyingSemigroup(R)) then
    TryNextMethod();
  fi;

  mat := Matrix(R);
  I := Rows(R);
  J := Columns(R);
  nrrows := Length(I);
  nrcols := Length(J);

  min := Minimum(nrrows, nrcols);
  max := Maximum(nrrows, nrcols);
  gens := EmptyPlist(max);
  for i in [1 .. min] do
    Add(gens, RMSElement(R, I[i], mat[J[i]][I[i]] ^ -1, J[i]));
  od;
  for i in [min + 1 .. nrrows] do
    Add(gens, RMSElement(R, I[i], mat[J[1]][I[i]] ^ -1, J[1]));
  od;
  for i in [min + 1 .. nrcols] do
    Add(gens, RMSElement(R, I[1], mat[J[i]][I[1]] ^ -1, J[i]));
  od;
  out := Semigroup(gens);
  SetIsRegularSemigroup(out, true);
  SetIsIdempotentGenerated(out, true);
  SetIsSimpleSemigroup(out, true);
  return out;
end);

InstallMethod(IdempotentGeneratedSubsemigroup,
"for a Rees 0-matrix subsemigroup",
[IsReesZeroMatrixSubsemigroup],
function(R)
  local mat, gr, gens, I, J, nrrows, k, out, i, j;

  if not IsFinite(R) or not IsReesZeroMatrixSemigroup(R)
      or not IsGroup(UnderlyingSemigroup(R)) then
    TryNextMethod();
  fi;

  mat := Matrix(R);
  gr := RZMSDigraph(R);
  gens := [];

  if IsCompleteBipartiteDigraph(ReducedDigraph(gr)) or IsEmptyDigraph(gr) then
    Add(gens, MultiplicativeZero(R));
  fi;

  gr := OutNeighbours(UndirectedSpanningForest(gr));
  I := Rows(R);
  J := Columns(R);
  nrrows := Length(I);

  for i in [1 .. nrrows] do
    for j in gr[i] do
      k := J[j - nrrows];
      Add(gens, RMSElement(R, I[i], mat[k][I[i]] ^ -1, k));
    od;
  od;

  out := Semigroup(gens);
  SetIsRegularSemigroup(out, true);
  SetIsIdempotentGenerated(out, true);
  return out;
end);

InstallMethod(InjectionPrincipalFactor, "for a Green's D-class (Semigroups)",
[IsGreensDClass],
function(D)
  if not IsRegularDClass(D) then
    ErrorNoReturn("the argument (a Green's D-class) is not regular");
  elif NrHClasses(D) = NrIdempotents(D) then
    return SEMIGROUPS.InjectionPrincipalFactor(D, ReesMatrixSemigroup);
  fi;
  return SEMIGROUPS.InjectionPrincipalFactor(D, ReesZeroMatrixSemigroup);
end);

InstallMethod(InjectionNormalizedPrincipalFactor,
"for a Green's D-class (Semigroups)",
[IsGreensDClass],
function(D)
  local iso1, iso2, rms, inv1, inv2, iso, inv, hom;

  if not IsRegularDClass(D) then
    ErrorNoReturn("the argument (a Green's D-class) is not regular");
  elif NrHClasses(D) = NrIdempotents(D) then
    iso1 := SEMIGROUPS.InjectionPrincipalFactor(D, ReesMatrixSemigroup);
    iso2 := RMSNormalization(Range(iso1));
  else
    iso1 := SEMIGROUPS.InjectionPrincipalFactor(D, ReesZeroMatrixSemigroup);
    iso2 := RZMSNormalization(Range(iso1));
  fi;

  rms := Range(iso2);
  inv1 := InverseGeneralMapping(iso1);
  inv2 := InverseGeneralMapping(iso2);
  iso := x -> (x ^ iso1) ^ iso2;
  inv := x -> (x ^ inv2) ^ inv1;
  hom := MappingByFunction(D, rms, iso, inv);
  SetIsInjective(hom, true);
  SetIsTotal(hom, true);
  return hom;
end);

InstallMethod(MultiplicativeNeutralElement,
"for a semigroup with CanUseFroidurePin + generators",
[IsSemigroup and CanUseFroidurePin and HasGeneratorsOfSemigroup],
function(S)
  local D, e;

  if not IsFinite(S) then
    TryNextMethod();
  elif IsMultiplicativeElementWithOneCollection(S) and One(S) in S then
    return One(S);
  elif Length(MaximalDClasses(S)) > 1 then
    return fail;
  fi;

  D := MaximalDClasses(S)[1];

  if NrHClasses(D) <> 1 or not IsRegularDClass(D) then
    return fail;
  fi;

  e := Idempotents(D)[1];

  if ForAll(GeneratorsOfSemigroup(S), x -> e * x = x and x * e = x) then
    return e;
  fi;
  return fail;
end);

# same method for inverse/ideals

InstallMethod(RepresentativeOfMinimalIdeal, "for a semigroup",
[IsSemigroup],
function(S)

  if HasMultiplicativeZero(S) and MultiplicativeZero(S) <> fail then
    return MultiplicativeZero(S);
  elif HasIsSimpleSemigroup(S) and IsSimpleSemigroup(S) then
    # This catches known trivial semigroups
    return Representative(S);
  elif IsSemigroupIdeal(S) and
      (HasRepresentativeOfMinimalIdeal(SupersemigroupOfIdeal(S))
       or not HasGeneratorsOfSemigroup(S)) then
    return RepresentativeOfMinimalIdeal(SupersemigroupOfIdeal(S));
  elif not IsFinite(S) then
    TryNextMethod();
  fi;

  return RepresentativeOfMinimalIdealNC(S);
end);

InstallMethod(RepresentativeOfMinimalIdealNC, "for a finite semigroup",
[IsSemigroup and IsFinite],
function(S)
  local D, pos;
  D   := PartialOrderOfDClasses(S);
  pos := DigraphSinks(D)[1];
  Assert(1, Length(DigraphSinks(D)) = 1);
  return Representative(DClasses(S)[pos]);
end);

InstallMethod(InversesOfSemigroupElementNC,
"for a group as semigroup and a multiplicative element",
[IsGroupAsSemigroup and CanUseFroidurePin, IsMultiplicativeElement],
function(G, x)
  local i, iso, inv;
  if IsMultiplicativeElementWithInverse(x) then
    i := InverseOp(x);
    if i <> fail then
      return [i];
    fi;
  fi;
  iso := IsomorphismPermGroup(G);
  inv := InverseGeneralMapping(iso);
  return [((x ^ iso) ^ -1) ^ inv];
end);

InstallMethod(InversesOfSemigroupElementNC,
"for a semigroup that can use froidure-pin and a multiplicative element",
[CanUseFroidurePin, IsMultiplicativeElement],
function(S, a)
  local R, L, inverses, e, f, s;
  R := RClass(S, a);
  L := LClass(S, a);
  inverses := EmptyPlist(NrIdempotents(R) * NrIdempotents(L));

  for e in Idempotents(R) do
    s := RightGreensMultiplierNC(S, a, e) * e;
    for f in Idempotents(L) do
      Add(inverses, f * s);
    od;
  od;
  return inverses;
end);

InstallMethod(InversesOfSemigroupElement,
"for a semigroup that can use froidure-pin and a multiplicative element",
[CanUseFroidurePin, IsMultiplicativeElement],  # to beat the library method
function(S, x)
  if not IsFinite(S) then
    TryNextMethod();
  elif not x in S then
    ErrorNoReturn("the 2nd argument (a mult. element) must belong to the 1st ",
                  "argument (a semigroup)");
  fi;
  return InversesOfSemigroupElementNC(S, x);
end);

InstallMethod(OneInverseOfSemigroupElementNC,
"for a semigroup and a multiplicative element",
[IsSemigroup, IsMultiplicativeElement],
function(S, x)
    if not IsFinite(S) then
        TryNextMethod();
    fi;
    return First(EnumeratorSorted(S),
    y -> x * y * x = x and y * x * y = y);
end);

InstallMethod(OneInverseOfSemigroupElementNC,
"for CanUseFroidurePin and a multiplicative element",
[CanUseFroidurePin, IsMultiplicativeElement],
function(S, a)
  local R, L, e, f, s;
  R := RClass(S, a);
  L := LClass(S, a);
  e := Idempotents(R);
  if IsEmpty(e) then
    return fail;
  fi;
  e := e[1];
  f := Idempotents(L);
  if IsEmpty(f) then
    return fail;
  fi;
  f := f[1];
  s := RightGreensMultiplierNC(S, a, e);
  return  f * s * e;
end);

InstallMethod(OneInverseOfSemigroupElement,
"for a semigroup and a multiplicative element",
[IsSemigroup, IsMultiplicativeElement],
function(S, x)
  if not IsFinite(S) then
    ErrorNoReturn("the semigroup is not finite");
  elif not x in S then
    ErrorNoReturn("the 2nd argument (a mult. element) must belong to the 1st ",
                  "argument (a semigroup)");
  fi;
  return OneInverseOfSemigroupElementNC(S, x);
end);

InstallMethod(UnderlyingSemigroupOfSemigroupWithAdjoinedZero,
"for a semigroup",
[IsSemigroup],
function(S)
  local zero, gens, T;

  if HasIsSemigroupWithAdjoinedZero(S)
      and not IsSemigroupWithAdjoinedZero(S) then
    return fail;
  fi;

  zero := MultiplicativeZero(S);
  if zero = fail then
    return fail;
  fi;

  gens := GeneratorsOfSemigroup(S);
  if Length(gens) = 1 then
    return fail;
  elif not zero in gens then
    return fail;
  fi;

  T := Semigroup(Difference(gens, [zero]));

  if zero in T then
    return fail;
  fi;
  return T;
end);

BindGlobal("_SemigroupSizeByIndexPeriod",
function(S)
  local gen, ind;
  gen := MinimalSemigroupGeneratingSet(S)[1];
  ind := IndexPeriodOfSemigroupElement(gen);
  if ind[1] = 1 then
    SetIsGroupAsSemigroup(S, true);
  fi;
  return Sum(ind) - 1;
end);

InstallMethod(Size,
"for a monogenic transformation semigroup with minimal generating set",
[IsMonogenicSemigroup and HasMinimalSemigroupGeneratingSet and
 IsTransformationSemigroup],
10,  # to beat IsActingSemigroup
_SemigroupSizeByIndexPeriod);

InstallMethod(Size,
"for a monogenic partial perm semigroup with minimal generating set",
[IsMonogenicSemigroup and HasMinimalSemigroupGeneratingSet and
 IsPartialPermSemigroup],
10,  # to beat IsActingSemigroup
_SemigroupSizeByIndexPeriod);

InstallMethod(Size,
"for a monogenic bipartition semigroup with minimal generating set",
[IsMonogenicSemigroup and HasMinimalSemigroupGeneratingSet and
 IsBipartitionSemigroup],
10,  # to beat IsActingSemigroup
_SemigroupSizeByIndexPeriod);

InstallMethod(Size,
"for a monogenic semigroup of matrices over finite field with minimal gen set",
[IsMonogenicSemigroup and HasMinimalSemigroupGeneratingSet and
 IsMatrixOverFiniteFieldSemigroup],
_SemigroupSizeByIndexPeriod);

MakeReadWriteGlobal("_SemigroupSizeByIndexPeriod");
Unbind(_SemigroupSizeByIndexPeriod);

InstallMethod(IndecomposableElements, "for a semigroup", [IsSemigroup],
function(S)
  local out, D;

  if HasIsSurjectiveSemigroup(S) and IsSurjectiveSemigroup(S) then
    return [];
  fi;
  out := [];
  for D in MaximalDClasses(S) do
    if not IsRegularDClass(D) then
      AddSet(out, Representative(D));
    fi;
  od;
  return out;
end);

InstallMethod(MinimalSemigroupGeneratingSet, "for a free semigroup",
[IsFreeSemigroup], GeneratorsOfSemigroup);

InstallMethod(MinimalSemigroupGeneratingSet, "for a semigroup",
[IsSemigroup],
function(S)
  local gens, indecomp, id, T, zero, iso, inv, G, x, D, non_unit_gens, classes,
  po, nbs;

  if IsTrivial(S) then
    return [Representative(S)];
  elif IsGroupAsSemigroup(S) then
    iso := IsomorphismPermGroup(S);
    inv := InverseGeneralMapping(iso);
    G := Range(iso);
    return Images(inv, MinimalGeneratingSet(G));
  elif IsMonogenicSemigroup(S) then
    return [Representative(MaximalDClasses(S)[1])];
  fi;

  gens := IrredundantGeneratingSubset(S);

  # A semigroup that has a 2-generating set but is not monogenic has rank 2.
  if Length(gens) = 2 then
    return gens;
  fi;

  # A generating set for a semigroup that has either a one/zero adjoined is
  # minimal if and only if it contains that one/zero, and is minimal for the
  # semigroup without the one/zero.
  if IsMonoidAsSemigroup(S) and IsTrivial(GroupOfUnits(S)) then
    id := MultiplicativeNeutralElement(S);
    T := Semigroup(Filtered(gens, x -> x <> id));
    return Concatenation([id], MinimalSemigroupGeneratingSet(T));
  elif IsSemigroupWithAdjoinedZero(S) then
    zero := MultiplicativeZero(S);
    T := Semigroup(Filtered(gens, x -> x <> zero));
    return Concatenation([zero], MinimalSemigroupGeneratingSet(T));
  fi;

  # The indecomposable elements are contains in any generating set. If the
  # indecomposable elements (or if not, the indecomposable elements plus a
  # single element) generate the semigroup, then you have a minimal generating
  # set.
  indecomp := IndecomposableElements(S);
  if Length(gens) = Length(indecomp) then
    return indecomp;
  elif not IsEmpty(indecomp) then
    x := Difference(gens, Semigroup(indecomp));
    if Length(x) = 1 then
      return Concatenation(x, indecomp);
    fi;
  fi;

  # A generating set for a monoid that consists of a minimal generating set for
  # the group of units and exactly one generator in each D-class immediately
  # below the group of units is minimal.
  if IsMonoidAsSemigroup(S) then
    D := DClass(S, MultiplicativeNeutralElement(S));
    non_unit_gens := Filtered(gens, x -> not x in D);
    classes := List(non_unit_gens, x -> Position(DClasses(S), DClass(S, x)));
    if IsDuplicateFreeList(classes) then
      po := PartialOrderOfDClasses(S);
      po := DigraphReflexiveTransitiveReduction(po);
      nbs := OutNeighboursOfVertex(po, Position(DClasses(S), D));
      if ForAll(classes, x -> x in nbs) then
        iso := IsomorphismPermGroup(GroupOfUnits(S));
        inv := InverseGeneralMapping(iso);
        G := Range(iso);
        return Concatenation(Images(inv, MinimalGeneratingSet(G)),
                             non_unit_gens);
      fi;
    fi;
  fi;

  # An irredundant generating set of a finite semigroup that contains at most
  # one generator per D-class is minimal.
  if IsFinite(S) and (IsDTrivial(S) or
      Length(Set(gens, x -> DClass(S, x))) = Length(gens)) then
    return gens;
  fi;

  ErrorNoReturn("no further methods for computing minimal generating sets ",
                "are implemented");
end);

InstallMethod(MinimalMonoidGeneratingSet, "for a free monoid",
[IsFreeMonoid], GeneratorsOfMonoid);

InstallMethod(MinimalMonoidGeneratingSet, "for a monoid",
[IsMonoid],
function(S)
  local one, gens, new;

  one := One(S);
  if IsTrivial(S) then
    return [one];
  fi;

  gens := MinimalSemigroupGeneratingSet(S);
  if not IsTrivial(GroupOfUnits(S)) then
    return gens;
  fi;
  new := Difference(gens, [one]);
  if One(new) = one then
    # The One of the non-identity generators is the One, so One is not needed.
    return new;
  fi;

  # This currently applies to only partial perm monoids: sometimes, the One
  # of the non-One generators is not the One of the monoid. Therefore the One
  # has to be included in the GeneratorsOfMonoid. WARNING: therefore
  # MinimalMonoidGeneratingSet may include the One even though, mathematically,
  # it shouldn't be needed. For example, see symmetric inverse monoid on 1 pt.
  return gens;
end);

InstallMethod(NambooripadPartialOrder, "for a semigroup",
[IsSemigroup],
function(S)
  local elts, p, func, out, i, j;

  if not IsFinite(S) then
    ErrorNoReturn("the argument (a semigroup) is not finite");
  elif not IsRegularSemigroup(S) then
    ErrorNoReturn("the argument (a semigroup) is not regular");
  elif IsInverseSemigroup(S) then
    return NaturalPartialOrder(S);
  fi;

  Info(InfoWarning, 2, "NambooripadPartialOrder: this method ",
                       "fully enumerates its argument!");

  elts := ShallowCopy(Elements(S));
  p    := Sortex(elts, {x, y} -> IsGreensDGreaterThanFunc(S)(y, x)) ^ -1;
  func := NambooripadLeqRegularSemigroup(S);
  out  := List([1 .. Size(S)], x -> []);

  for i in [1 .. Size(S)] do
    for j in [i + 1 .. Size(S)] do
      if func(elts[i], elts[j]) then
        AddSet(out[j ^ p], i ^ p);
      fi;
    od;
  od;
  return out;
end);

InstallMethod(NambooripadLeqRegularSemigroup, "for a semigroup",
[IsSemigroup],
function(S)
  if not IsFinite(S) then
    ErrorNoReturn("the argument (a semigroup) is not finite");
  elif not IsRegularSemigroup(S) then
    ErrorNoReturn("the argument (a semigroup) is not regular");
  elif IsInverseSemigroup(S) then
    return NaturalLeqInverseSemigroup(S);
  fi;

  return
    function(x, y)
      local E;
      E := Idempotents(S);
      return ForAny(E, e -> e * y = x)
        and ForAny(E, f -> y * f = x);
    end;
end);

SEMIGROUPS.ExistsTransversal := function(a, b, n)
    local exists, class, i;
    if DegreeOfTransformation(a) > n or
        DegreeOfTransformation(b) > n then
        ErrorNoReturn("Transformation does not",
        "belong to a transformation semigroup of degree n");
    fi;
    for class in KernelOfTransformation(a, n) do
        exists := false;
        for i in [1 .. Size(class)] do
            if class[i] ^ a = class[i] ^ b then
                exists := true;
                break;
            fi;
        od;
        if not exists then
            return false;
        fi;
    od;
    return true;
end;

InstallMethod(RegularLeqTransformationSemigroupNC,
#intended for internal use; see MitschLeqSemigroup for public use
"for a transformation semigroup",
[IsTransformationSemigroup],
function(S)
    local deg;
    deg := DegreeOfTransformationSemigroup(S);
    return
        function(x, y)
            # Only returns the correct answer if y is a regular element
            return IsRefinementKernelOfTransformation(x, y, deg)
             and SEMIGROUPS.ExistsTransversal(x, y, deg);
        end;
end);

InstallMethod(MitschLeqSemigroupNC,
"for a semigroup",
[IsSemigroup],
function(S)
    return 
        function(x, y)
            if x = y then
                return true;
            else
                return ForAny(Elements(S), s -> x = x * s and x = y * s) and
                    ForAny(Elements(S), t -> t * y = x and t * x = x);
            fi;
        end;
end);

InstallMethod(MitschLeqSemigroup,
"for a semigroup",
[IsSemigroup],
function(S)
    if IsInverseSemigroup(S) then
        return NaturalLeqInverseSemigroup(S);
    elif IsRegularSemigroup(S) and IsTransformationSemigroup(S) then
        return RegularLeqTransformationSemigroupNC(S);
    elif IsRegularSemigroup(S) then
        return NambooripadLeqRegularSemigroup(S);
    else 
        return MitschLeqSemigroupNC(S);
    fi;
end);

InstallMethod(MitschOrderOfSemigroup,
"for a finite transformation semigroup",
[IsTransformationSemigroup],
function(S)
    local elts, p, func1, func2, out, i, j, regular, D, a;
    elts := ShallowCopy(AsListCanonical(S));
    p    := Sortex(elts, {x, y} -> IsGreensDGreaterThanFunc(S)(y, x)) ^ -1;
    func1 := RegularLeqTransformationSemigroupNC(S);
    func2 := MitschLeqSemigroupNC(S);
    out  := List([1 .. Size(S)], x -> []);
    regular := BlistList([1 .. Size(S)], []);
    for D in RegularDClasses(S) do
        for a in D do
            i := PositionCanonical(S, a) ^ (p ^ -1);
            regular[i] := true;
        od;
    od;
    for j in [Size(S), Size(S) - 1 .. 1] do
        if regular[j] then
            for i in [j - 1, j - 2 .. 1] do
                if func1(elts[i], elts[j]) then
                    AddSet(out[j ^ p], i ^ p);
                fi;
            od;
        else
            for i in [j - 1, j - 2 .. 1] do
                if func2(elts[i], elts[j]) then
                    AddSet(out[j ^ p], i ^ p);
                fi;
            od;
        fi;
    od;
    return out;
end);

InstallMethod(MitschOrderOfSemigroup,
"for a finite regular transformation semigroup",
[IsRegularSemigroup and IsTransformationSemigroup],
function(S)
    local elts, p, func, out, i, j; 
    elts := ShallowCopy(Elements(S));
    p    := Sortex(elts, {x, y} -> IsGreensDGreaterThanFunc(S)(y, x)) ^ -1;
    func := RegularLeqTransformationSemigroupNC(S);
    out  := List([1 .. Size(S)], x -> []);
    for i in [1 .. Size(S)] do
        for j in [i + 1 .. Size(S)] do
            if func(elts[i], elts[j]) then
                AddSet(out[j ^ p], i ^ p);
            fi;
        od;
    od;
    return out;
end);

InstallMethod(MitschOrderOfSemigroup,
"for a finite semigroup",
[IsFinite and IsSemigroup],
function(S)
    local i, iso, T, MT, MS, eltsS, eltsT, idx_map, q;
    iso := IsomorphismTransformationSemigroup(S);
    T := Range(iso);
    eltsS := Elements(S);
    eltsT := Elements(T);
    idx_map := List([1 .. Size(S)], i -> Position(eltsT, eltsS[i] ^ iso));
    q := PermList(idx_map);
    MT := MitschOrderOfSemigroup(T);
    MS := [];
    for i in [1 .. Size(S)] do
        MS[i] := AsSet(OnTuples(MT[i ^ q], q ^ -1));
    od;
    return MS;
end);

InstallMethod(DumbMitschOrderOfSemigroup,
"for a finite semigroup",
[IsSemigroup and IsFinite],
function(S)
    local func, out, i, j, elts;
    func := MitschLeqSemigroup(S);
    elts := Elements(S);
    out  := List([1 .. Size(S)], x -> []);
    for i in [1 .. Size(S)] do
        for j in [1 .. Size(S)] do
            if i = j then
                continue;
            elif func(elts[i], elts[j]) then
                AddSet(out[j], i);
            fi;
        od;
    od;
    return out;
end);

InstallMethod(LeftIdentity,
"for semigroup with CanUseFroidurePin and mult. elt.",
[IsSemigroup and CanUseFroidurePin, IsMultiplicativeElement],
function(S, x)
  local i, p, result;
  if not x in S then
    Error("the 2nd argument (a mult. elt.) does not belong to the 1st ",
          "argument (a semigroup)");
  elif IsMonoid(S) then
    return One(S);
  elif IsMonoidAsSemigroup(S) then
    return MultiplicativeNeutralElement(S);
  elif IsIdempotent(x) then
    return x;
  fi;

  i := PositionCanonical(S, x);
  p := DigraphPath(LeftCayleyDigraph(S), i, i);
  if p = fail then
    return fail;
  fi;
  result := EvaluateWord(GeneratorsOfSemigroup(S), Reversed(p[2]));
  return result ^ SmallestIdempotentPower(result);
end);

InstallMethod(RightIdentity,
"for semgroup with CanUseFroidurePin and mult. elt.",
[IsSemigroup and CanUseFroidurePin, IsMultiplicativeElement],
function(S, x)
  local i, p, result;
  if not x in S then
    Error("the 2nd argument (a mult. elt.) does not belong to the 1st ",
          "argument (a semigroup)");
  elif IsMonoid(S) then
    return One(S);
  elif IsMonoidAsSemigroup(S) then
    return MultiplicativeNeutralElement(S);
  elif IsIdempotent(x) then
    return x;
  fi;

  i := PositionCanonical(S, x);
  p := DigraphPath(RightCayleyDigraph(S), i, i);
  if p = fail then
    return fail;
  fi;
  result := EvaluateWord(GeneratorsOfSemigroup(S), p[2]);
  return result ^ SmallestIdempotentPower(result);
end);

InstallMethod(MultiplicationTableWithCanonicalPositions,
"for a semigroup with CanUseFroidurePin",
[IsSemigroup and CanUseFroidurePin],
function(S)
  local n, sortedlist, t, tinv, M;
  n          := Size(S);
  sortedlist := AsSortedList(S);

  t    := PermList(List([1 .. n], i -> PositionCanonical(S, sortedlist[i])));
  tinv := t ^ -1;
  M    := MultiplicationTable(S);

  return List([1 .. n], i -> List([1 .. n], j -> M[i ^ tinv][j ^ tinv] ^ t));
end);

InstallMethod(TransposedMultiplicationTableWithCanonicalPositions,
"for a semigroup with CanUseFroidurePin",
[IsSemigroup and CanUseFroidurePin],
S -> TransposedMat(MultiplicationTableWithCanonicalPositions(S)));

InstallMethod(MinimalFaithfulTransformationDegree, "for a right zero semigroup",
[IsRightZeroSemigroup],
function(S)
  local max, deg;

  max := 0;
  deg := 0;
  while max < Size(S) do
    deg := deg + 1;
    if (deg mod 3) = 0 then
      max := 3 ^ (deg / 3);
    elif (deg mod 3) = 1 then
      max := 4 * 3 ^ ((deg - 4) / 3);
    else
      max := 2 * 3 ^ ((deg - 2) / 3);
    fi;
  od;
  return deg;
end);

InstallMethod(MinimalFaithfulTransformationDegree, "for a left zero semigroup",
[IsLeftZeroSemigroup],
function(S)
  local max, deg, N, r;
  max := 0;
  deg := 0;
  while max < Size(S) do
    deg := deg + 1;
    for r in [1 .. deg - 1] do
      N := r ^ (deg - r);
      if N > max then
        max := N;
      fi;
    od;
  od;
  return deg;
end);
