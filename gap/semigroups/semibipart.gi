#############################################################################
##
##  semigroups/semibipart.gi
##  Copyright (C) 2013-2022                               James D. Mitchell
##
##  Licensing information can be found in the README file of this package.
##
#############################################################################
##

# this file contains methods for every operation/attribute/property that is
# specific to bipartition semigroups.

#############################################################################
## Random - bipartitions
#############################################################################

InstallMethod(SEMIGROUPS_ProcessRandomArgsCons,
[IsBipartitionSemigroup, IsList],
{_, params} -> SEMIGROUPS_ProcessRandomArgsCons(IsSemigroup, params));

InstallMethod(SEMIGROUPS_ProcessRandomArgsCons,
[IsBipartitionMonoid, IsList],
{_, params} -> SEMIGROUPS_ProcessRandomArgsCons(IsSemigroup, params));

InstallMethod(RandomSemigroupCons, "for IsBipartitionSemigroup and list",
[IsBipartitionSemigroup, IsList],
{_, params} -> Semigroup(List([1 .. params[1]],
                              i -> RandomBipartition(params[2]))));

InstallMethod(RandomMonoidCons, "for IsBipartitionMonoid and list",
[IsBipartitionMonoid, IsList],
{_, params} -> Monoid(List([1 .. params[1]],
                           i -> RandomBipartition(params[2]))));

InstallMethod(RandomInverseSemigroupCons,
"for IsBipartitionSemigroup and list", [IsBipartitionSemigroup, IsList],
SEMIGROUPS.DefaultRandomInverseSemigroup);

InstallMethod(RandomInverseMonoidCons,
"for IsBipartitionMonoid and list", [IsBipartitionMonoid, IsList],
SEMIGROUPS.DefaultRandomInverseMonoid);

#############################################################################
## Random - block bijections
#############################################################################

InstallMethod(SEMIGROUPS_ProcessRandomArgsCons,
[IsBlockBijectionSemigroup, IsList],
{_, params} -> SEMIGROUPS_ProcessRandomArgsCons(IsSemigroup, params));

InstallMethod(SEMIGROUPS_ProcessRandomArgsCons,
[IsBlockBijectionMonoid, IsList],
{_, params} -> SEMIGROUPS_ProcessRandomArgsCons(IsSemigroup, params));

InstallMethod(RandomSemigroupCons,
"for IsBlockBijectionSemigroup and a list",
[IsBlockBijectionSemigroup, IsList],
function(_, params)
  return Semigroup(List([1 .. params[1]],
                        i -> RandomBlockBijection(params[2])));
end);

InstallMethod(RandomMonoidCons,
"for IsBlockBijectionMonoid and a list",
[IsBlockBijectionMonoid, IsList],
function(_, params)
  return Monoid(List([1 .. params[1]],
                     i -> RandomBlockBijection(params[2])));
end);

InstallMethod(RandomInverseSemigroupCons,
"for IsBlockBijectionSemigroup and a list",
[IsBlockBijectionSemigroup, IsList],
function(_, params)
  return InverseSemigroup(List([1 .. params[1]],
                               i -> RandomBlockBijection(params[2])));
end);

InstallMethod(RandomInverseMonoidCons,
"for IsBlockBijectionMonoid and a list",
[IsBlockBijectionMonoid, IsList],
function(_, params)
  return InverseMonoid(List([1 .. params[1]],
                            i -> RandomBlockBijection(params[2])));
end);

#############################################################################
## Printing and viewing
#############################################################################

InstallMethod(SemigroupViewStringPrefix, "for a bipartition semigroup",
[IsBipartitionSemigroup], S -> "\>bipartition\< ");

InstallMethod(SemigroupViewStringPrefix, "for a bipartition *-semigroup",
[IsBipartitionSemigroup and IsStarSemigroup],
function(S)
  if HasIsInverseSemigroup(S) and IsInverseSemigroup(S) then
    TryNextMethod();
  fi;
  return "\>bipartition\< *-";
end);

InstallMethod(SemigroupViewStringPrefix, "for a block bijection semigroup",
[IsBlockBijectionSemigroup], S -> "\>block bijection\< ");

InstallMethod(SemigroupViewStringPrefix, "for a block bijection *-semigroup",
[IsBlockBijectionSemigroup and IsStarSemigroup],
function(S)
  if HasIsInverseSemigroup(S) and IsInverseSemigroup(S) then
    TryNextMethod();
  fi;
  # TODO(later) A block bijection *-semigroup is necessarily inverse, install a
  # true method for this
  return "\>block bijection\< *-";
end);

InstallMethod(SemigroupViewStringSuffix, "for a bipartition semigroup",
[IsBipartitionSemigroup],
function(S)
  return Concatenation("\>degree \>",
                       ViewString(DegreeOfBipartitionSemigroup(S)),
                       "\<\< ");
end);

# same method for ideals

InstallMethod(GroupOfUnits, "for an acting bipartition semigroup",
[IsBipartitionSemigroup and IsActingSemigroup],
function(S)
  local R, G, deg, U, map;

  if MultiplicativeNeutralElement(S) = fail then
    return fail;
  fi;

  R := GreensRClassOfElementNC(S, MultiplicativeNeutralElement(S));
  G := SchutzenbergerGroup(R);
  deg := DegreeOfBipartitionSemigroup(S);

  U := Semigroup(List(GeneratorsOfGroup(G), x -> AsBipartition(x, deg)));
  SetIsGroupAsSemigroup(U, true);
  UseIsomorphismRelation(U, G);

  map := SemigroupIsomorphismByFunctionNC(U,
                                          G,
                                          AsPermutation,
                                          x -> AsBipartition(x, deg));
  SetIsomorphismPermGroup(U, map);

  return U;
end);

InstallImmediateMethod(IsBlockBijectionSemigroup, IsBipartitionSemigroup and
HasGeneratorsOfSemigroup, 0,
S -> ForAll(GeneratorsOfSemigroup(S), IsBlockBijection));

InstallImmediateMethod(IsPartialPermBipartitionSemigroup,
IsBipartitionSemigroup and HasGeneratorsOfSemigroup, 0,
S -> ForAll(GeneratorsOfSemigroup(S), IsPartialPermBipartition));

InstallImmediateMethod(IsPermBipartitionGroup, IsBipartitionSemigroup and
HasGeneratorsOfSemigroup, 0,
S -> ForAll(GeneratorsOfSemigroup(S), IsPermBipartition));

InstallMethod(IsBlockBijectionSemigroup, "for a bipartition semigroup ideal",
[IsBipartitionSemigroup and IsSemigroupIdeal],
function(S)
  if IsBlockBijectionSemigroup(SupersemigroupOfIdeal(S)) then
    return true;
  fi;
  return ForAll(GeneratorsOfSemigroup(S), IsBlockBijection);
  # TODO(later) this could be better only have to check the generators of the
  # ideal times the generators of the semigroup on the left and right.
end);

InstallMethod(IsPartialPermBipartitionSemigroup,
"for a bipartition semigroup ideal",
[IsBipartitionSemigroup and IsSemigroupIdeal],
function(S)
  if IsPartialPermBipartitionSemigroup(SupersemigroupOfIdeal(S)) then
    return true;
  fi;
  return ForAll(GeneratorsOfSemigroup(S), IsPartialPermBipartition);
end);

InstallMethod(IsPermBipartitionGroup, "for a bipartition semigroup ideal",
[IsBipartitionSemigroup and IsSemigroupIdeal],
function(S)
  if IsPermBipartitionGroup(SupersemigroupOfIdeal(S)) then
    return true;
  fi;
  return ForAll(GeneratorsOfSemigroup(S), IsPermBipartition);
end);

InstallMethod(NaturalLeqInverseSemigroup, "for a bipartition semigroup",
[IsBipartitionSemigroup],
function(S)
  if not IsInverseSemigroup(S) then
    ErrorNoReturn("the argument is not an inverse semigroup");
  elif IsBlockBijectionSemigroup(S) then
    return NaturalLeqBlockBijection;
  elif IsPartialPermBipartitionSemigroup(S) then
    return NaturalLeqPartialPermBipartition;
  fi;
  TryNextMethod();  # This should be the default method for an
                    # inverse semigroup
end);

InstallMethod(NaturalPartialOrder,
"for an inverse block bijection semigroup",
[IsBlockBijectionSemigroup and IsInverseSemigroup],
function(S)
  local elts, n, out, i, j;

  elts := Elements(S);
  n := Length(elts);
  out := List([1 .. n], x -> []);

  for i in [n, n - 1 .. 2] do
    for j in [i - 1, i - 2 .. 1] do
      if NaturalLeqBlockBijection(elts[j], elts[i]) then
        AddSet(out[i], j);
      fi;
    od;
  od;

  return out;
end);

InstallMethod(NaturalPartialOrder,
"for an inverse partial perm bipartition semigroup",
[IsPartialPermBipartitionSemigroup and IsInverseSemigroup],
function(S)
  local elts, p, n, out, i, j;

  elts := ShallowCopy(Elements(S));
  n := Length(elts);
  out := List([1 .. n], x -> []);
  p := Sortex(elts, PartialPermLeqBipartition) ^ -1;

  for i in [n, n - 1 .. 2] do
    for j in [i - 1, i - 2 .. 1] do
      if NaturalLeqPartialPermBipartition(elts[j], elts[i]) then
        AddSet(out[i ^ p], j ^ p);
      fi;
    od;
  od;

  Perform(out, ShrinkAllocationPlist);
  return out;
end);

# The relative order of the methods for the constructor IsomorphismSemigroup is
# important do not change it! They should be ordered from lowest rank to
# highest so that the correct method is used.

InstallMethod(AsMonoid, "for a bipartition semigroup",
[IsBipartitionSemigroup],
function(S)
  if MultiplicativeNeutralElement(S) = fail then
    return fail;  # so that we do the same as the GAP/ref manual says
  fi;
  return Range(IsomorphismMonoid(IsBipartitionMonoid, S));
end);

InstallMethod(IsomorphismMonoid, "for IsBipartitionMonoid and a semigroup",
[IsBipartitionMonoid, IsSemigroup], SEMIGROUPS.DefaultIsomorphismMonoid);

InstallMethod(IsomorphismMonoid, "for IsBipartitionMonoid and a monoid",
[IsBipartitionMonoid, IsMonoid],
{_, S} -> IsomorphismSemigroup(IsBipartitionSemigroup, S));

# this is just a composition of IsomorphismTransformationSemigroup and the
# method below for IsomorphismBipartitionSemigroup...

InstallMethod(IsomorphismSemigroup,
"for IsBipartitionSemigroup and a semigroup",
[IsBipartitionSemigroup, IsSemigroup], SEMIGROUPS.DefaultIsomorphismSemigroup);

InstallMethod(IsomorphismSemigroup,
"for IsBipartitionSemigroup and a transformation semigroup with generators",
[IsBipartitionSemigroup,
 IsTransformationSemigroup and HasGeneratorsOfSemigroup],
function(_, S)
  local n, T;

  n := Maximum(1, DegreeOfTransformationSemigroup(S));
  T := Semigroup(List(GeneratorsOfSemigroup(S), x -> AsBipartition(x, n)));
  UseIsomorphismRelation(S, T);

  return SemigroupIsomorphismByFunctionNC(S,
                                          T,
                                          x -> AsBipartition(x, n),
                                          AsTransformation);
end);

# the converse of the previous method

InstallMethod(IsomorphismSemigroup,
"for IsBipartitionSemigroup and a partial perm semigroup with generators",
[IsBipartitionSemigroup, IsPartialPermSemigroup and HasGeneratorsOfSemigroup],
function(_, S)
  local n, T;

  n := Maximum(DegreeOfPartialPermSemigroup(S),
               CodegreeOfPartialPermSemigroup(S));
  T := Semigroup(List(GeneratorsOfSemigroup(S), x -> AsBipartition(x, n)));
  UseIsomorphismRelation(S, T);

  return SemigroupIsomorphismByFunctionNC(S,
                                          T,
                                          x -> AsBipartition(x, n),
                                          AsPartialPerm);
end);

InstallMethod(IsomorphismSemigroup,
"for IsBipartitionSemigroup and partial perm inverse semigp with generators",
[IsBipartitionSemigroup, IsPartialPermSemigroup and IsInverseSemigroup and
 HasGeneratorsOfInverseSemigroup],
function(_, S)
  local n, T;

  n := Maximum(DegreeOfPartialPermSemigroup(S),
               CodegreeOfPartialPermSemigroup(S));
  T := InverseSemigroup(List(GeneratorsOfInverseSemigroup(S),
                             x -> AsBipartition(x, n)));
  UseIsomorphismRelation(S, T);

  return SemigroupIsomorphismByFunctionNC(S,
                                          T,
                                          x -> AsBipartition(x, n),
                                          AsPartialPerm);
end);

InstallMethod(IsomorphismSemigroup,
"for IsBipartitionSemigroup and a perm group with generators",
[IsBipartitionSemigroup, IsPermGroup and HasGeneratorsOfGroup],
function(_, S)
  local n, T;

  n := LargestMovedPoint(S);
  T := Semigroup(List(GeneratorsOfGroup(S), x -> AsBipartition(x, n)));
  UseIsomorphismRelation(S, T);

  return SemigroupIsomorphismByFunctionNC(S,
                                          T,
                                          x -> AsBipartition(x, n),
                                          AsPermutation);
end);

# fall back method

InstallMethod(IsomorphismSemigroup,
"for IsBlockBijectionSemigroup and semigroup",
[IsBlockBijectionSemigroup, IsSemigroup],
function(filter, S)
  local iso1, inv1, iso2, inv2;

  if not IsInverseSemigroup(S) then
    ErrorNoReturn("the 2nd argument must be an inverse semigroup");
  fi;

  iso1 := IsomorphismPartialPermSemigroup(S);
  inv1 := InverseGeneralMapping(iso1);
  iso2 := IsomorphismSemigroup(filter, Range(iso1));
  inv2 := InverseGeneralMapping(iso2);

  return SemigroupIsomorphismByFunctionNC(S,
                                          Range(iso2),
                                          x -> (x ^ iso1) ^ iso2,
                                          x -> (x ^ inv2) ^ inv1);
end);

# this is one way, i.e. no converse method

InstallMethod(IsomorphismSemigroup,
"for IsBlockBijectionSemigroup and a partial perm semigroup with generators",
[IsBlockBijectionSemigroup,
 IsPartialPermSemigroup and HasGeneratorsOfSemigroup],
function(_, S)
  local n, T, inv;

  n := Maximum(DegreeOfPartialPermSemigroup(S),
               CodegreeOfPartialPermSemigroup(S)) + 1;
  T := Semigroup(List(GeneratorsOfSemigroup(S), x -> AsBlockBijection(x, n)));
  UseIsomorphismRelation(S, T);

  # AsPartialPerm for a block bijection created using AsBlockBijection with
  # argument a partial perm
  inv := function(x)
    local blocks, n, bigblock, lookup, out, i;

    blocks := IntRepOfBipartition(x);
    n := DegreeOfBipartition(x);
    bigblock := blocks[n];

    # find the images of [1..n]
    lookup := EmptyPlist(n - 1);
    for i in [1 .. n - 1] do
      lookup[blocks[i + n]] := i;
    od;

    # put it together
    out := [1 .. n - 1] * 0;
    for i in [1 .. n - 1] do
      if blocks[i] <> bigblock then
        out[i] := lookup[blocks[i]];
      fi;
    od;

    return PartialPerm(out);
  end;

  return SemigroupIsomorphismByFunctionNC(S,
                                          T,
                                          x -> AsBlockBijection(x, n),
                                          inv);
end);

# this is one way, i.e. no converse method

InstallMethod(IsomorphismSemigroup,
"for an inverse partial perm semigroup with generators",
[IsBlockBijectionSemigroup, IsPartialPermSemigroup and IsInverseSemigroup and
 HasGeneratorsOfInverseSemigroup],
function(_, S)
  local n, T, inv;

  n := DegreeOfPartialPermSemigroup(S) + 1;
  T := InverseSemigroup(List(GeneratorsOfInverseSemigroup(S),
                             x -> AsBlockBijection(x, n)));
  UseIsomorphismRelation(S, T);

  # AsPartialPerm for a block bijection created using AsBlockBijection with
  # argument a partial perm
  inv := function(x)
    local blocks, n, bigblock, lookup, out, i;

    blocks := IntRepOfBipartition(x);
    n := DegreeOfBipartition(x);
    bigblock := blocks[n];

    # find the images of [1..n]
    lookup := EmptyPlist(n - 1);
    for i in [1 .. n - 1] do
      lookup[blocks[i + n]] := i;
    od;

    # put it together
    out := [1 .. n - 1] * 0;
    for i in [1 .. n - 1] do
      if blocks[i] <> bigblock then
        out[i] := lookup[blocks[i]];
      fi;
    od;

    return PartialPerm(out);
  end;

  return SemigroupIsomorphismByFunctionNC(S,
                                          T,
                                          x -> AsBlockBijection(x, n),
                                          inv);
end);

InstallMethod(IsomorphismSemigroup,
"for IsBipartitionSemigroup and a semigroup ideal",
[IsBipartitionSemigroup, IsSemigroupIdeal and HasGeneratorsOfSemigroupIdeal],
function(_, I)
  local iso, inv, J;

  iso := IsomorphismSemigroup(IsBipartitionSemigroup,
                              SupersemigroupOfIdeal(I));
  inv := InverseGeneralMapping(iso);
  J := SemigroupIdeal(Range(iso), Images(iso, GeneratorsOfSemigroupIdeal(I)));
  UseIsomorphismRelation(I, J);

  return SemigroupIsomorphismByFunctionNC(I, J, x -> x ^ iso, x -> x ^ inv);
end);

InstallMethod(IsomorphismSemigroup,
"for IsBlockBijectionSemigroup and a semigroup ideal",
[IsBlockBijectionSemigroup, IsSemigroupIdeal and
 HasGeneratorsOfSemigroupIdeal],
function(_, I)
  local iso, inv, J;

  iso := IsomorphismSemigroup(IsBlockBijectionSemigroup,
                              SupersemigroupOfIdeal(I));
  inv := InverseGeneralMapping(iso);
  J := SemigroupIdeal(Range(iso), Images(iso, GeneratorsOfSemigroupIdeal(I)));
  UseIsomorphismRelation(I, J);

  return SemigroupIsomorphismByFunctionNC(I, J, x -> x ^ iso, x -> x ^ inv);
end);

InstallMethod(IsomorphismSemigroup,
"for IsBlockBijectionSemigroup and a block bijection semigroup",
[IsBlockBijectionSemigroup, IsBlockBijectionSemigroup],
{_, S} -> SemigroupIsomorphismByFunctionNC(S, S, IdFunc, IdFunc));

InstallMethod(IsomorphismSemigroup,
"for IsBipartitionSemigroup and a bipartition semigroup",
[IsBipartitionSemigroup, IsBipartitionSemigroup],
{_, S} -> SemigroupIsomorphismByFunctionNC(S, S, IdFunc, IdFunc));

# TODO(later) could have a method for IsomorphismSemigroup for
# IsPartialPermBipartitions and IsBlockBijectionSemigroup too... or just for
# general inverse semigroups, via composing IsomorphismPartialPermSemigroup and
# the isomorphism to a block bijection semigroup.

InstallMethod(IsGeneratorsOfInverseSemigroup, "for a bipartition collection",
[IsBipartitionCollection],
function(coll)
  return ForAll(coll, IsBlockBijection)
    or ForAll(coll, IsPartialPermBipartition);
end);

InstallMethod(GeneratorsOfInverseSemigroup,
"for an inverse bipartition semigroup with generators",
[IsBipartitionSemigroup and IsInverseSemigroup and HasGeneratorsOfSemigroup],
function(S)
  local gens, pos, x;

  gens := ShallowCopy(GeneratorsOfSemigroup(S));
  for x in gens do
    pos := Position(gens, x ^ -1);
    if pos <> fail and x <> x ^ -1 then
      Remove(gens, pos);
    fi;
  od;
  MakeImmutable(gens);
  return gens;
end);

InstallMethod(GeneratorsOfInverseMonoid,
"for an inverse bipartition monoid with generators",
[IsBipartitionSemigroup and IsInverseMonoid and HasGeneratorsOfMonoid],
function(S)
  local gens, one, pos, x;

  gens := ShallowCopy(GeneratorsOfMonoid(S));
  one := One(S);
  for x in gens do
    pos := Position(gens, x ^ -1);
    if pos <> fail and (x <> x ^ -1 or x = one) then
      Remove(gens, pos);
    fi;
  od;
  MakeImmutable(gens);
  return gens;
end);

InstallImmediateMethod(GeneratorsOfSemigroup,
IsBipartitionSemigroup and HasGeneratorsOfInverseSemigroup, 0,
function(S)
  local gens, x;

  gens := ShallowCopy(GeneratorsOfInverseSemigroup(S));
  for x in gens do
    if not IsPermBipartition(x) then
      x := x ^ -1;
      if not x in gens then
        Add(gens, x);
      fi;
    fi;
  od;
  MakeImmutable(gens);
  return gens;
end);

InstallImmediateMethod(GeneratorsOfMonoid,
IsBipartitionMonoid and HasGeneratorsOfInverseMonoid, 0,
function(S)
  local gens, x;

  gens := ShallowCopy(GeneratorsOfInverseMonoid(S));
  for x in gens do
    if not IsPermBipartition(x) then
      x := x ^ -1;
      if not x in gens then
        Add(gens, x);
      fi;
    fi;
  od;
  MakeImmutable(gens);
  return gens;
end);

InstallMethod(DegreeOfBipartitionSemigroup, "for a bipartition semigroup",
[IsBipartitionSemigroup], S -> DegreeOfBipartition(Representative(S)));

InstallMethod(\<, "for bipartition semigroups",
[IsBipartitionSemigroup, IsBipartitionSemigroup],
function(S, T)
  if DegreeOfBipartitionSemigroup(S) <> DegreeOfBipartitionSemigroup(T) then
    return DegreeOfBipartitionSemigroup(S) < DegreeOfBipartitionSemigroup(T);
  fi;
  TryNextMethod();
end);
