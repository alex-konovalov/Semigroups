############################################################################
##
##  semigroups/semiboolmat.gi
##  Copyright (C) 2015-2022                              James D. Mitchell
##
##  Licensing information can be found in the README file of this package.
##
#############################################################################
##

# This file contains methods for semigroups of boolean matrices.

#############################################################################
## 0. Random
#############################################################################

InstallMethod(SEMIGROUPS_ProcessRandomArgsCons,
[IsBooleanMatSemigroup, IsList],
{_, params} -> SEMIGROUPS_ProcessRandomArgsCons(IsSemigroup, params));

InstallMethod(SEMIGROUPS_ProcessRandomArgsCons,
[IsBooleanMatMonoid, IsList],
{_, params} -> SEMIGROUPS_ProcessRandomArgsCons(IsSemigroup, params));

InstallMethod(RandomSemigroupCons,
"for IsBooleanMatSemigroup and list",
[IsBooleanMatSemigroup, IsList],
function(_, params)
  return Semigroup(List([1 .. params[1]], i -> RandomMatrix(IsBooleanMat,
                                                            params[2])));
end);

InstallMethod(RandomMonoidCons,
"for IsBooleanMatMonoid and list",
[IsBooleanMatMonoid, IsList],
function(_, params)
  return Monoid(List([1 .. params[1]], i -> RandomMatrix(IsBooleanMat,
                                                         params[2])));
end);

InstallMethod(RandomInverseSemigroupCons, "for IsBooleanMatSemigroup and list",
[IsBooleanMatSemigroup, IsList], SEMIGROUPS.DefaultRandomInverseSemigroup);

InstallMethod(RandomInverseMonoidCons, "for IsBooleanMatMonoid and list",
[IsBooleanMatMonoid, IsList], SEMIGROUPS.DefaultRandomInverseMonoid);

#############################################################################
## 1. Isomorphisms
#############################################################################

# fallback method: via a transformation semigroup

InstallMethod(IsomorphismSemigroup,
"for IsBooleanMatSemigroup and a semigroup",
[IsBooleanMatSemigroup, IsSemigroup],
SEMIGROUPS.DefaultIsomorphismSemigroup);

InstallMethod(IsomorphismSemigroup,
"for IsBooleanMatSemigroup and a boolean mat semigroup",
[IsBooleanMatSemigroup, IsBooleanMatSemigroup],
{_, S} -> SemigroupIsomorphismByFunctionNC(S, S, IdFunc, IdFunc));

# It seems necessary that the method below occurs after the fallback method in
# this file, in order that it be selected.

InstallMethod(IsomorphismSemigroup,
"for IsBooleanMatSemigroup and a transformation semigroup",
[IsBooleanMatSemigroup, IsTransformationSemigroup],
function(_, S)
  local n, T;
  n := Maximum(1, DegreeOfTransformationSemigroup(S));
  T := Semigroup(List(GeneratorsOfSemigroup(S), x -> AsBooleanMat(x, n)));
  UseIsomorphismRelation(S, T);
  return SemigroupIsomorphismByFunctionNC(S,
                                          T,
                                          x -> AsBooleanMat(x, n),
                                          AsTransformation);
end);

# If the second argument here is a transformation semigroup, then
# DefaultIsomorphismMonoid uses IsomorphismTransformationMonoid, which detects
# the MultiplicativeNeutralElement of the second argument, and reduces the
# degree accordingly.

InstallMethod(AsMonoid, "for a boolean mat semigroup",
[IsBooleanMatSemigroup],
function(S)
  if MultiplicativeNeutralElement(S) = fail then
    return fail;  # so that we do the same as the GAP / ref manual says
  fi;
  return Range(IsomorphismMonoid(IsBooleanMatMonoid, S));
end);

InstallMethod(IsomorphismMonoid, "for IsBooleanMatMonoid and a semigroup",
[IsBooleanMatMonoid, IsSemigroup], SEMIGROUPS.DefaultIsomorphismMonoid);

InstallMethod(IsomorphismMonoid, "for IsBooleanMatMonoid and a monoid",
[IsBooleanMatMonoid, IsMonoid],
{_, S} -> IsomorphismSemigroup(IsBooleanMatSemigroup, S));

InstallMethod(IsomorphismMonoid,
"for IsBooleanMatMonoid and a boolean mat monoid",
[IsBooleanMatMonoid, IsBooleanMatMonoid],
{_, S} -> SemigroupIsomorphismByFunctionNC(S, S, IdFunc, IdFunc));
