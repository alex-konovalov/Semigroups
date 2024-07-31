############################################################################
##
##  semigroups/semipbr.gi
##  Copyright (C) 2015-2022                              James D. Mitchell
##
##  Licensing information can be found in the README file of this package.
##
#############################################################################

# TODO(later) IsomorphismSemigroup for IsBooleanMatSemigroup
#
# This file contains methods for semigroups of PBRs.

#############################################################################
## ?. Random
#############################################################################

InstallMethod(SEMIGROUPS_ProcessRandomArgsCons, [IsPBRSemigroup, IsList],
{_, params} -> SEMIGROUPS_ProcessRandomArgsCons(IsSemigroup, params));

InstallMethod(SEMIGROUPS_ProcessRandomArgsCons, [IsPBRMonoid, IsList],
{_, params} -> SEMIGROUPS_ProcessRandomArgsCons(IsSemigroup, params));

InstallMethod(RandomSemigroupCons, "for IsPBRSemigroup and a list",
[IsPBRSemigroup, IsList],
{_, params} -> Semigroup(List([1 .. params[1]], i -> RandomPBR(params[2]))));

InstallMethod(RandomMonoidCons, "for IsPBRMonoid and a list",
[IsPBRMonoid, IsList],
{_, params} -> Monoid(List([1 .. params[1]], i -> RandomPBR(params[2]))));

InstallMethod(RandomInverseSemigroupCons, "for IsPBRSemigroup and a list",
[IsPBRSemigroup, IsList], SEMIGROUPS.DefaultRandomInverseSemigroup);

InstallMethod(RandomInverseMonoidCons, "for IsPBRMonoid and a list",
[IsPBRMonoid, IsList], SEMIGROUPS.DefaultRandomInverseMonoid);

InstallMethod(SemigroupViewStringPrefix, "for a pbr semigroup",
[IsPBRSemigroup], S -> "\>pbr\< ");

InstallMethod(SemigroupViewStringSuffix, "for a pbr semigroup",
[IsPBRSemigroup],
function(S)
  return Concatenation("\>degree \>",
                       ViewString(DegreeOfPBRSemigroup(S)),
                       "\<\< ");
end);

InstallMethod(DegreeOfPBRSemigroup, "for a PBR semigroup",
[IsPBRSemigroup], S -> DegreeOfPBR(Representative(S)));

# fall back method via a transformation semigroup

InstallMethod(IsomorphismSemigroup, "for IsPBRSemigroup and a semigroup",
[IsPBRSemigroup, IsSemigroup], SEMIGROUPS.DefaultIsomorphismSemigroup);

InstallMethod(IsomorphismSemigroup,
"for IsPBRSemigroup and a transformation semigroup",
[IsPBRSemigroup, IsTransformationSemigroup],
function(_, S)
  local deg, T;

  deg := Maximum(1, DegreeOfTransformationSemigroup(S));
  T := Semigroup(List(GeneratorsOfSemigroup(S), x -> AsPBR(x, deg)));
  UseIsomorphismRelation(S, T);

  return SemigroupIsomorphismByFunctionNC(S,
                                          T,
                                          x -> AsPBR(x, deg),
                                          AsTransformation);
end);

# The following is not a monoid isomorphism

InstallMethod(IsomorphismSemigroup,
"for IsPBRSemigroup and a bipartition semigroup",
[IsPBRSemigroup, IsBipartitionSemigroup],
function(_, S)
  local T;

  T := Semigroup(List(GeneratorsOfSemigroup(S), AsPBR));
  UseIsomorphismRelation(S, T);

  return SemigroupIsomorphismByFunctionNC(S,
                                          T,
                                          AsPBR,
                                          AsBipartition);
end);

InstallMethod(IsomorphismSemigroup,
"for IsPBRSemigroup and a pbr semigroup",
[IsPBRSemigroup, IsPBRSemigroup],
{_, S} -> SemigroupIsomorphismByFunctionNC(S, S, IdFunc, IdFunc));

InstallMethod(AsMonoid, "for a PBR semigroup",
[IsPBRSemigroup],
function(S)
  if MultiplicativeNeutralElement(S) = fail then
    return fail;  # so that we do the same as the GAP / ref manual says
  fi;
  return Range(IsomorphismMonoid(IsPBRMonoid, S));
end);

InstallMethod(IsomorphismMonoid, "for IsPBRMonoid and a semigroup",
[IsPBRMonoid, IsSemigroup], SEMIGROUPS.DefaultIsomorphismMonoid);

InstallMethod(IsomorphismMonoid, "for IsPBRMonoid and a monoid",
[IsPBRMonoid, IsMonoid], SEMIGROUPS.DefaultIsomorphismMonoid);

InstallMethod(IsomorphismMonoid, "for IsPBRMonoid and a transformation monoid",
[IsPBRMonoid, IsTransformationMonoid],
function(_, S)
  local deg, T;

  deg := Maximum(1, DegreeOfTransformationSemigroup(S));
  T := Monoid(List(GeneratorsOfSemigroup(S), x -> AsPBR(x, deg)));
  UseIsomorphismRelation(S, T);

  return SemigroupIsomorphismByFunctionNC(S,
                                          T,
                                          x -> AsPBR(x, deg),
                                          AsTransformation);
end);

InstallMethod(IsomorphismMonoid, "for IsPBRMonoid and a pbr monoid",
[IsPBRMonoid, IsPBRMonoid],
{_, S} -> SemigroupIsomorphismByFunctionNC(S, S, IdFunc, IdFunc));

InstallMethod(\<, "for pbr semigroups",
[IsPBRSemigroup, IsPBRSemigroup],
function(S, T)
  if DegreeOfPBRSemigroup(S) <> DegreeOfPBRSemigroup(T) then
    return DegreeOfPBRSemigroup(S) < DegreeOfPBRSemigroup(T);
  fi;
  TryNextMethod();
end);
