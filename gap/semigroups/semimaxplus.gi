############################################################################
##
##  semigroups/semimaxplus.gi
##  Copyright (C) 2015-2022                              James D. Mitchell
##
##  Licensing information can be found in the README file of this package.
##
#############################################################################
##

# This file contains implementations for semigroups of max-plus, min-plus,
# tropical max-plus, and tropical min-plus matrices.

#############################################################################
## Random inverse semigroups and monoids, no better method currently
#############################################################################

for _IsXMatrix in ["IsMaxPlusMatrix",
                   "IsMinPlusMatrix",
                   "IsTropicalMaxPlusMatrix",
                   "IsTropicalMinPlusMatrix",
                   "IsProjectiveMaxPlusMatrix",
                   "IsNTPMatrix",
                   "IsIntegerMatrix"] do

  _IsXSemigroup := Concatenation(_IsXMatrix, "Semigroup");
  _IsXMonoid := Concatenation(_IsXMatrix, "Monoid");

  InstallMethod(RandomInverseSemigroupCons,
  Concatenation("for ", _IsXSemigroup, " and a list"),
  [ValueGlobal(_IsXSemigroup), IsList],
  SEMIGROUPS.DefaultRandomInverseSemigroup);

  InstallMethod(RandomInverseMonoidCons,
  Concatenation("for ", _IsXMonoid, " and a list"),
  [ValueGlobal(_IsXMonoid), IsList],
  SEMIGROUPS.DefaultRandomInverseMonoid);

od;

Unbind(_IsXMatrix);
Unbind(_IsXMonoid);
Unbind(_IsXSemigroup);

#############################################################################
## Random for matrices with 0 additional parameters
#############################################################################

_InstallRandom0 := function(params)
  local IsXMatrix, FilterPlaceHolder, IsXSemigroup, IsXMonoid;

  if not IsString(params) then
    IsXMatrix         := params[1];
    FilterPlaceHolder := params[2];
  else
    IsXMatrix         := params;
    FilterPlaceHolder := params;
  fi;

  IsXSemigroup := Concatenation(IsXMatrix, "Semigroup");
  IsXMonoid := Concatenation(IsXMatrix, "Monoid");

  InstallMethod(SEMIGROUPS_ProcessRandomArgsCons,
  [ValueGlobal(IsXSemigroup), IsList],
  function(_, params)
    return SEMIGROUPS_ProcessRandomArgsCons(IsSemigroup, params);
  end);

  InstallMethod(SEMIGROUPS_ProcessRandomArgsCons,
  [ValueGlobal(IsXMonoid), IsList],
  function(_, params)
    return SEMIGROUPS_ProcessRandomArgsCons(IsSemigroup, params);
  end);

  InstallMethod(RandomSemigroupCons,
  Concatenation("for ", IsXSemigroup, " and a list"),
  [ValueGlobal(IsXSemigroup), IsList],
  function(_, params)
    return Semigroup(List([1 .. params[1]],
                          i -> RandomMatrix(ValueGlobal(FilterPlaceHolder),
                                            params[2])));
  end);

  InstallMethod(RandomMonoidCons,
  Concatenation("for ", IsXMonoid, " and a list"),
  [ValueGlobal(IsXMonoid), IsList],
  function(_, params)
    return Monoid(List([1 .. params[1]],
                       i -> RandomMatrix(ValueGlobal(FilterPlaceHolder),
                                         params[2])));
  end);
end;

for _IsXMatrix in ["IsMaxPlusMatrix",
                   "IsMinPlusMatrix",
                   ["IsIntegerMatrix", "Integers"],
                   "IsProjectiveMaxPlusMatrix"] do
  _InstallRandom0(_IsXMatrix);
od;

Unbind(_IsXMatrix);
Unbind(_InstallRandom0);

#############################################################################
## Random for matrices with 1 additional parameters
#############################################################################

_ProcessArgs1 := function(_, params)
  if Length(params) < 1 then  # nr gens
    params[1] := Random(1, 20);
  elif not IsPosInt(params[1]) then
    return "the 2nd argument (number of generators) must be a pos int";
  fi;

  if Length(params) < 2 then  # degree / dimension
    params[2] := Random(1, 20);
  fi;

  if not IsPosInt(params[2]) then
    return "the 3rd argument (matrix dimension) must be a pos int";
  elif Length(params) < 3 then  # threshold
    params[3] := Random(1, 20);
  fi;

  if not IsPosInt(params[3]) then
    return "the 4th argument (semiring threshold) must be a pos int";
  elif Length(params) > 3 then
    return "there must be at most four arguments";
  fi;
  return params;
end;

_InstallRandom1 := function(IsXMatrix)
  local IsXSemigroup, IsXMonoid;

  IsXSemigroup := Concatenation(IsXMatrix, "Semigroup");
  IsXMonoid := Concatenation(IsXMatrix, "Monoid");

  InstallMethod(SEMIGROUPS_ProcessRandomArgsCons,
  [ValueGlobal(IsXSemigroup), IsList], _ProcessArgs1);

  InstallMethod(SEMIGROUPS_ProcessRandomArgsCons,
  [ValueGlobal(IsXMonoid), IsList], _ProcessArgs1);

  InstallMethod(RandomSemigroupCons,
  Concatenation("for ", IsXSemigroup, " and a list"),
  [ValueGlobal(IsXSemigroup), IsList],
  function(_, params)
    return Semigroup(List([1 .. params[1]],
                          i -> RandomMatrix(ValueGlobal(IsXMatrix),
                                            params[2],
                                            params[3])));
  end);

  InstallMethod(RandomMonoidCons,
  Concatenation("for ", IsXMonoid, " and a list"),
  [ValueGlobal(IsXMonoid), IsList],
  function(_, params)
    return Monoid(List([1 .. params[1]],
                        i -> RandomMatrix(ValueGlobal(IsXMatrix),
                                          params[2],
                                          params[3])));
  end);
end;

for _IsXMatrix in ["IsTropicalMaxPlusMatrix",
                   "IsTropicalMinPlusMatrix"] do
  _InstallRandom1(_IsXMatrix);
od;

Unbind(_IsXMatrix);
Unbind(_InstallRandom1);
Unbind(_ProcessArgs1);

#############################################################################
## Random for matrices with 2 additional parameters
#############################################################################

InstallMethod(SEMIGROUPS_ProcessRandomArgsCons,
[IsNTPMatrixSemigroup, IsList],
function(_, params)
  if Length(params) < 1 then  # nr gens
    params[1] := Random(1, 20);
  elif not IsPosInt(params[1]) then
    return "the 2nd argument (number of generators) must be a pos int";
  fi;
  if Length(params) < 2 then  # dimension
    params[2] := Random(1, 20);
  elif not IsPosInt(params[2]) then
    return "the 3rd argument (matrix dimension) must be a pos int";
  fi;
  if Length(params) < 3 then  # threshold
    params[3] := Random(1, 20);
  elif not IsPosInt(params[3]) then
    return "the 4th argument (semiring threshold) must be a pos int";
  fi;
  if Length(params) < 4 then  # period
    params[4] := Random(1, 20);
  elif not IsPosInt(params[4]) then
    return "the 5th argument (semiring period) must be a pos int";
  fi;
  if Length(params) > 4 then
    return "there must be at most 5 arguments";
  fi;

  return params;
end);

InstallMethod(SEMIGROUPS_ProcessRandomArgsCons, [IsNTPMatrixMonoid, IsList],
{_, params} -> SEMIGROUPS_ProcessRandomArgsCons(IsNTPMatrixSemigroup, params));

InstallMethod(RandomSemigroupCons,
"for IsNTPMatrixSemigroup and a list",
[IsNTPMatrixSemigroup, IsList],
function(_, params)
  return Semigroup(List([1 .. params[1]],
                        i -> RandomMatrix(IsNTPMatrix,
                                          params[2],
                                          params[3],
                                          params[4])));
end);

InstallMethod(RandomMonoidCons,
"for IsNTPMatrixMonoid and a list",
[IsNTPMatrixMonoid, IsList],
function(_, params)
  return Monoid(List([1 .. params[1]],
                      i -> RandomMatrix(IsNTPMatrix,
                                        params[2],
                                        params[3],
                                        params[4])));
end);

#############################################################################
## 1. Isomorphisms
#############################################################################

#############################################################################
## Isomorphism from an arbitrary semigroup to a matrix semigroup, via a
## transformation semigroup
#############################################################################

# 0 additional parameters

for _IsXMatrix in ["IsMaxPlusMatrix",
                   "IsMinPlusMatrix",
                   "IsIntegerMatrix",
                   "IsProjectiveMaxPlusMatrix"] do

  _IsXSemigroup := Concatenation(_IsXMatrix, "Semigroup");

  InstallMethod(IsomorphismSemigroup,
  Concatenation("for ", _IsXSemigroup, " and a semigroup"),
  [ValueGlobal(_IsXSemigroup), IsSemigroup],
  SEMIGROUPS.DefaultIsomorphismSemigroup);

  InstallMethod(IsomorphismSemigroup,
  Concatenation("for ", _IsXSemigroup, " and a ", _IsXSemigroup),
  [ValueGlobal(_IsXSemigroup), ValueGlobal(_IsXSemigroup)],
  function(_, S)
    return SemigroupIsomorphismByFunctionNC(S, S, IdFunc, IdFunc);
  end);

od;

Unbind(_IsXMatrix);
Unbind(_IsXSemigroup);

# 1 additional parameters

for _IsXMatrix in ["IsTropicalMaxPlusMatrix",
                   "IsTropicalMinPlusMatrix"] do

  _IsXSemigroup := Concatenation(_IsXMatrix, "Semigroup");

  InstallMethod(IsomorphismSemigroup,
  Concatenation("for ", _IsXSemigroup, ", pos int, and a semigroup"),
  [ValueGlobal(_IsXSemigroup), IsPosInt, IsSemigroup],
  function(filter, threshold, S)
    local iso1, inv1, iso2, inv2;

    iso1 := IsomorphismTransformationSemigroup(S);
    inv1 := InverseGeneralMapping(iso1);
    iso2 := IsomorphismSemigroup(filter, threshold, Range(iso1));
    inv2 := InverseGeneralMapping(iso2);

    return SemigroupIsomorphismByFunctionNC(S,
                                            Range(iso2),
                                            x -> (x ^ iso1) ^ iso2,
                                            x -> (x ^ inv2) ^ inv1);
  end);

  InstallMethod(IsomorphismSemigroup,
  Concatenation("for ", _IsXSemigroup, ", and a semigroup"),
  [ValueGlobal(_IsXSemigroup), IsSemigroup],
  function(filter, S)
    return IsomorphismSemigroup(filter, 1, S);
  end);

  InstallMethod(IsomorphismSemigroup,
  Concatenation("for ", _IsXSemigroup, " and a ", _IsXSemigroup),
  [ValueGlobal(_IsXSemigroup), IsPosInt, ValueGlobal(_IsXSemigroup)],
  function(_, threshold, S)
    if threshold = ThresholdTropicalMatrix(Representative(S)) then
      return SemigroupIsomorphismByFunctionNC(S, S, IdFunc, IdFunc);
    fi;
    TryNextMethod();
  end);
od;

Unbind(_IsXMatrix);
Unbind(_IsXSemigroup);

# 2 additional parameters

InstallMethod(IsomorphismSemigroup,
"for IsNTPMatrixSemigroup, pos int, pos int, and a semigroup",
[IsNTPMatrixSemigroup, IsPosInt, IsPosInt, IsSemigroup],
function(filter, threshold, period, S)
  local iso1, inv1, iso2, inv2;

  iso1 := IsomorphismTransformationSemigroup(S);
  inv1 := InverseGeneralMapping(iso1);
  iso2 := IsomorphismSemigroup(filter, threshold, period, Range(iso1));
  inv2 := InverseGeneralMapping(iso2);

  return SemigroupIsomorphismByFunctionNC(S,
                                          Range(iso2),
                                          x -> (x ^ iso1) ^ iso2,
                                          x -> (x ^ inv2) ^ inv1);
end);

InstallMethod(IsomorphismSemigroup,
"for IsNTPMatrixSemigroup and a semigroup",
[IsNTPMatrixSemigroup, IsSemigroup],
{_, S} -> IsomorphismSemigroup(IsNTPMatrixSemigroup, 1, 1, S));

InstallMethod(IsomorphismSemigroup,
"for IsNTPMatrixSemigroup, pos int, pos int, and a semigroup",
[IsNTPMatrixSemigroup, IsPosInt, IsPosInt, IsNTPMatrixSemigroup],
function(_, threshold, period, S)
  if threshold = ThresholdNTPMatrix(Representative(S))
      and period = PeriodNTPMatrix(Representative(S)) then
    return SemigroupIsomorphismByFunctionNC(S, S, IdFunc, IdFunc);
  fi;
  TryNextMethod();
end);

#############################################################################
## Isomorphism from a transformation semigroup to a matrix semigroup
## 0 additional parameters!!!
#############################################################################

## These are installed inside a function so that the value of IsXMatrix and
## IsXSemigroup are retained as local variables.

_InstallIsomorphism0 := function(filter)
  local IsXMatrix, IsXSemigroup, IsXMonoid;

  IsXMatrix := filter;
  IsXSemigroup := Concatenation(filter, "Semigroup");
  IsXMonoid := Concatenation(filter, "Monoid");

  InstallMethod(AsMonoid,
  Concatenation("for a semigroup in ", IsXSemigroup),
  [ValueGlobal(IsXSemigroup)],
  function(S)
    if MultiplicativeNeutralElement(S) = fail then
      return fail;  # so that we do the same as the GAP/ref manual says
    fi;
    return Range(IsomorphismMonoid(ValueGlobal(IsXMonoid), S));
  end);

  InstallMethod(IsomorphismMonoid,
  Concatenation("for ", IsXMonoid, " and a semigroup"),
  [ValueGlobal(IsXMonoid), IsSemigroup],
  SEMIGROUPS.DefaultIsomorphismMonoid);

  InstallMethod(IsomorphismMonoid,
  Concatenation("for ", IsXMonoid, " and a monoid"),
  [ValueGlobal(IsXMonoid), IsMonoid],
  function(_, S)
    return IsomorphismSemigroup(ValueGlobal(IsXSemigroup), S);
  end);

  if IsXMatrix <> "IsIntegerMatrix" then
    InstallMethod(IsomorphismSemigroup,
    Concatenation("for ", IsXSemigroup,
                  " and a transformation semigroup with generators"),
    [ValueGlobal(IsXSemigroup),
     IsTransformationSemigroup and HasGeneratorsOfSemigroup],
    function(_, S)
      local n, map, T;

      n    := Maximum(DegreeOfTransformationSemigroup(S), 1);
      map  := x -> AsMatrix(ValueGlobal(IsXMatrix), x, n);
      T := Semigroup(List(GeneratorsOfSemigroup(S), map));
      UseIsomorphismRelation(S, T);

      return SemigroupIsomorphismByFunctionNC(S,
                                              T,
                                              map,
                                              AsTransformation);
    end);
  fi;
end;

for _IsXMatrix in ["IsMaxPlusMatrix",
                   "IsMinPlusMatrix",
                   "IsIntegerMatrix",
                   "IsProjectiveMaxPlusMatrix"] do
  _InstallIsomorphism0(_IsXMatrix);
od;

Unbind(_IsXMatrix);
Unbind(_InstallIsomorphism0);

#############################################################################
## Isomorphism from a transformation semigroup to a matrix semigroup
## 1 additional parameters!!!
#############################################################################

# These are installed inside a function so that the value of IsXMatrix and
# IsXSemigroup are retained as a local variables.

_InstallIsomorphism1 := function(filter)
  local IsXMatrix, IsXSemigroup, IsXMonoid;

  IsXMatrix := filter;
  IsXSemigroup := Concatenation(filter, "Semigroup");
  IsXMonoid := Concatenation(filter, "Monoid");

  InstallMethod(AsMonoid,
  Concatenation("for a semigroup in ", IsXSemigroup),
  [ValueGlobal(IsXSemigroup)],
  function(S)
    if MultiplicativeNeutralElement(S) = fail then
      return fail;  # so that we do the same as the GAP/ref manual says
    fi;
    return Range(IsomorphismMonoid(ValueGlobal(IsXMonoid), S));
  end);

  InstallMethod(IsomorphismMonoid,
  Concatenation("for ", IsXMonoid, ", pos int, and a semigroup"),
  [ValueGlobal(IsXMonoid), IsPosInt, IsSemigroup],
  function(filter, threshold, S)
    local iso1, inv1, iso2, inv2;

    iso1 := IsomorphismTransformationMonoid(S);
    inv1 := InverseGeneralMapping(iso1);
    iso2 := IsomorphismMonoid(filter, threshold, Range(iso1));
    inv2 := InverseGeneralMapping(iso2);

    return SemigroupIsomorphismByFunctionNC(S,
                                            Range(iso2),
                                            x -> (x ^ iso1) ^ iso2,
                                            x -> (x ^ inv2) ^ inv1);
  end);

  InstallMethod(IsomorphismMonoid,
  Concatenation("for ", IsXMonoid, " and a semigroup"),
  [ValueGlobal(IsXMonoid), IsSemigroup],
  function(filter, S)
    return IsomorphismMonoid(filter, 1, S);
  end);

  InstallMethod(IsomorphismMonoid,
  Concatenation("for ", IsXMonoid, ", and a semigroup in ", IsXSemigroup),
  [ValueGlobal(IsXMonoid), ValueGlobal(IsXSemigroup)],
  function(filter, S)
    return IsomorphismMonoid(filter,
                             ThresholdTropicalMatrix(Representative(S)),
                             S);
  end);

  InstallMethod(IsomorphismMonoid,
  Concatenation("for ", IsXMonoid, ", pos int, and a monoid"),
  [ValueGlobal(IsXMonoid), IsPosInt, IsMonoid],
  function(_, threshold, S)
    return IsomorphismSemigroup(ValueGlobal(IsXSemigroup), threshold, S);
  end);

  InstallMethod(IsomorphismSemigroup,
  Concatenation("for ", IsXSemigroup,
                ", pos int, and a transformation semigroup with generators"),
  [ValueGlobal(IsXSemigroup), IsPosInt,
   IsTransformationSemigroup and HasGeneratorsOfSemigroup],
  function(_, threshold, S)
    local n, map, T;

    n    := Maximum(DegreeOfTransformationSemigroup(S), 1);
    map  := x -> AsMatrix(ValueGlobal(IsXMatrix), x, n, threshold);
    T := Semigroup(List(GeneratorsOfSemigroup(S), map));
    UseIsomorphismRelation(S, T);

    return SemigroupIsomorphismByFunctionNC(S,
                                            T,
                                            map,
                                            AsTransformation);
  end);

  InstallMethod(IsomorphismSemigroup,
  Concatenation("for ", IsXSemigroup,
                " and a transformation semigroup with generators"),
  [ValueGlobal(IsXSemigroup),
   IsTransformationSemigroup and HasGeneratorsOfSemigroup],
  function(filt, S)
    return IsomorphismSemigroup(filt, 1, S);
  end);
end;

for _IsXMatrix in ["IsTropicalMaxPlusMatrix",
                   "IsTropicalMinPlusMatrix"] do
  _InstallIsomorphism1(_IsXMatrix);
od;

Unbind(_IsXMatrix);
Unbind(_InstallIsomorphism1);

#############################################################################
## Isomorphism from a transformation semigroup to a matrix semigroup
## 2 additional parameters!!!
#############################################################################

InstallMethod(AsMonoid, "for an ntp matrix semigroup",
[IsNTPMatrixSemigroup],
function(S)
  if MultiplicativeNeutralElement(S) = fail then
    return fail;  # so that we do the same as the GAP/ref manual says
  fi;
  return Range(IsomorphismMonoid(IsNTPMatrixMonoid, S));
end);

InstallMethod(IsomorphismMonoid,
"for IsNTPMatrixMonoid, pos int, pos int, and a semigroup",
[IsNTPMatrixMonoid, IsPosInt, IsPosInt, IsSemigroup],
function(filter, threshold, period, S)
  local iso1, inv1, iso2, inv2;

  iso1 := IsomorphismTransformationMonoid(S);
  inv1 := InverseGeneralMapping(iso1);
  iso2 := IsomorphismMonoid(filter, threshold, period, Range(iso1));
  inv2 := InverseGeneralMapping(iso2);

  return SemigroupIsomorphismByFunctionNC(S,
                                          Range(iso2),
                                          x -> (x ^ iso1) ^ iso2,
                                          x -> (x ^ inv2) ^ inv1);
end);

InstallMethod(IsomorphismMonoid,
"for IsNTPMatrixMonoid and a semigroup",
[IsNTPMatrixMonoid, IsSemigroup],
{filter, S} -> IsomorphismMonoid(filter, 1, 1, S));

InstallMethod(IsomorphismMonoid,
"for IsNTPMatrixMonoid and a ntp matrix semigroup",
[IsNTPMatrixMonoid, IsNTPMatrixSemigroup],
function(filter, S)
  return IsomorphismMonoid(filter,
                           ThresholdNTPMatrix(Representative(S)),
                           PeriodNTPMatrix(Representative(S)),
                           S);
end);

InstallMethod(IsomorphismMonoid,
"for IsNTPMatrixMonoid, pos int, pos int, and a semigroup",
[IsNTPMatrixMonoid, IsPosInt, IsPosInt, IsMonoid],
{_, threshold, period, S}
-> IsomorphismSemigroup(IsNTPMatrixSemigroup, threshold, period, S));

InstallMethod(IsomorphismSemigroup,
"for IsNTPMatrixSemigroup, pos int, pos int, trans semigroup with gens",
[IsNTPMatrixSemigroup, IsPosInt, IsPosInt,
 IsTransformationSemigroup and HasGeneratorsOfSemigroup],
function(_, threshold, period, S)
  local n, map, T;

  n := Maximum(DegreeOfTransformationSemigroup(S), 1);
  map := x -> AsMatrix(IsNTPMatrix, x, n, threshold, period);
  T := Semigroup(List(GeneratorsOfSemigroup(S), map));
  UseIsomorphismRelation(S, T);

  return SemigroupIsomorphismByFunctionNC(S,
                                          T,
                                          x -> AsMatrix(IsNTPMatrix,
                                                        x,
                                                        n,
                                                        threshold,
                                                        period),
                                          AsTransformation);
end);

#############################################################################
## IsFinite and required methods for max-plus and min-plus matrix semigroups.
#############################################################################

## Method from corollary 10, page 148, of:
## I. Simon, Limited subsets of the free monoid,
## Proc. of the 19th Annual Symposium on the Foundations of Computer Science,
## IEEE, 1978, pp. 143-150.
## https://tinyurl.com/h8er92u

InstallMethod(IsFinite,
"for a min-plus matrix semigroup",
[IsMinPlusMatrixSemigroup], SUM_FLAGS,
function(S)
  local gens, id, mat, row, val;

  if IsEnumerated(Enumerate(S, 8192)) then
    return true;
  fi;

  gens := GeneratorsOfSemigroup(S);
  for mat in gens do
    for row in mat do
      for val in row do
        if val < 0 then
          TryNextMethod();
        fi;
      od;
    od;
  od;
  id := Idempotents(Semigroup(List(gens,
                                   x -> AsMatrix(IsTropicalMinPlusMatrix,
                                                 x,
                                                 1))));
  for mat in id do
    mat := AsMatrix(IsMinPlusMatrix, mat);
    if mat ^ 2 <> mat ^ 3 then
      return false;
    fi;
  od;
  return true;
end);

## The next two methods (IsFinite, IsTorsion for Max-plus) rely primarily on:
## a)
## Theorem 2.1 (positive solution to burnside problem) and
## theorem 2.2 (decidability of torsion problem), page 2 et.al, from:
## S. Gaubert, On the burnside problem for semigroups of matrices in the
## (max, +) algebra, Semigroup Forum, Volume 52, pp 271-292, 1996.
## https://tinyurl.com/znhk52m
## b)
## An unpublished result by J.D Mitchell & S. Burrell relating isomorphism of
## normalized max-plus matrix semigroups to min-plus matrix semigroups.
## (N.B.) b) is optional but preferable, for alternatives see a).

InstallMethod(IsFinite,
"for max-plus matrix semigroups",
[IsMaxPlusMatrixSemigroup], SUM_FLAGS,
function(S)
  if IsEnumerated(Enumerate(S, 8192)) then
    return true;
  fi;
  return IsTorsion(S);
end);

InstallMethod(IsTorsion,
"for a max-plus matrix semigroup",
[IsMaxPlusMatrixSemigroup],
function(S)
  local gens, dim, func, m, rad, T;

  gens := GeneratorsOfSemigroup(S);
  dim := DimensionOfMatrixOverSemiring(Representative(gens));

  func := function(i)
    return List([1 .. dim],
                j -> Maximum(List([1 .. Length(gens)], k -> gens[k][i][j])));
  end;

  m := Matrix(IsMaxPlusMatrix, List([1 .. dim], func));

  # Case: SpectralRadius = - infinity
  rad := SpectralRadius(m);
  if rad = -infinity then
    return true;
  elif rad <> 0 then
    return false;
  fi;

  # Case: SpectralRadius = 0
  T := NormalizeSemigroup(S);
  gens := List(GeneratorsOfSemigroup(T),
               x -> Matrix(IsMinPlusMatrix, -AsList(x)));
  return IsFinite(Semigroup(gens));
end);

## A method based on the original solution by S. Gaubert (On the burnside
## problem for semigroups of matrices in the (max, +) algebra), but
## modified by S. Burrell (see thesis https://tinyurl.com/gr94xha).

InstallMethod(NormalizeSemigroup,
"for a finitely generated semigroup of max-plus matrices",
[IsMaxPlusMatrixSemigroup],
function(S)
  local gens, dim, func, m, critcol, d, ngens, i;

  gens := GeneratorsOfSemigroup(S);
  dim := DimensionOfMatrixOverSemiring(Representative(gens));

  func := function(i)
    return List([1 .. dim],
                j -> Maximum(List([1 .. Length(gens)], k -> gens[k][i][j])));
  end;

  # Sum with respect to max-plus algebra of generators of S.
  m := Matrix(IsMaxPlusMatrix, List([1 .. dim], func));

  critcol := RadialEigenvector(m);
  d := List([1 .. dim], i -> List([1 .. dim], j -> -infinity));
  for i in [1 .. dim] do
    d[i][i] := critcol[i];
  od;
  d := Matrix(IsMaxPlusMatrix, d);

  ngens := List(gens, g -> InverseOp(d) * g * d);
  return Semigroup(ngens);
end);
