#############################################################################
##
##  semigroups/semiffmat.gi
##  Copyright (C) 2015-2022                              James D. Mitchell
##                                                         Markus Pfeiffer
##
##  Licensing information can be found in the README file of this package.
##
#############################################################################
##

# Contents:
# 1. Isomorphisms for semigroups
# 2. Isomorphisms for monoids
# 3. Printing and viewing
# 4. Random
# 5. Methods for acting semigroup setup
# 6. Properties of matrix over finite field semigroups

#############################################################################
# 1. Isomorphisms for semigroups
#############################################################################

# fallback method: via a transformation semigroup

InstallMethod(IsomorphismSemigroup,
"for IsMatrixOverFiniteFieldSemigroup and a semigroup",
[IsMatrixOverFiniteFieldSemigroup, IsSemigroup],
SEMIGROUPS.DefaultIsomorphismSemigroup);

InstallMethod(IsomorphismSemigroup,
"for IsMatrixOverFiniteFieldSemigroup, a ring, and a semigroup",
[IsMatrixOverFiniteFieldSemigroup, IsRing, IsSemigroup],
function(filt, R, S)
  local iso1, inv1, iso2, inv2;

  if not (IsField(R) and IsFinite(R)) then
    ErrorNoReturn("the 2nd argument (a ring) must be a finite field");
  fi;

  iso1 := IsomorphismTransformationSemigroup(S);
  inv1 := InverseGeneralMapping(iso1);
  iso2 := IsomorphismSemigroup(filt, R, Range(iso1));
  inv2 := InverseGeneralMapping(iso2);

  return SemigroupIsomorphismByFunctionNC(S,
                                          Range(iso2),
                                          x -> (x ^ iso1) ^ iso2,
                                          x -> (x ^ inv2) ^ inv1);
end);

InstallMethod(IsomorphismSemigroup,
"for IsMatrixOverFiniteFieldSemigroup and a finite field matrix semigroup",
[IsMatrixOverFiniteFieldSemigroup, IsMatrixOverFiniteFieldSemigroup],
{_, S} -> SemigroupIsomorphismByFunctionNC(S, S, IdFunc, IdFunc));

InstallMethod(IsomorphismSemigroup,
"for IsMatrixOverFiniteFieldSemigroup, ring, and matrix over ff semigroup",
[IsMatrixOverFiniteFieldSemigroup,
 IsRing,
 IsMatrixOverFiniteFieldSemigroup],
function(_, R, S)
  local D, map, inv, T;
  D := BaseDomain(Representative(S));
  if D = R then
    return SemigroupIsomorphismByFunctionNC(S, S, IdFunc, IdFunc);
  elif Size(D) <= Size(R) and IsIdenticalObj(FamilyObj(D), FamilyObj(R))
      and DegreeOverPrimeField(R) mod DegreeOverPrimeField(D) = 0 then
    map := x -> Matrix(R, x);
    inv := x -> Matrix(D, x);
    T   := Semigroup(List(GeneratorsOfSemigroup(S), map));
    return SemigroupIsomorphismByFunctionNC(S, T, map, inv);
  fi;
  TryNextMethod();  # take an isomorphism to a transformation semigroup
end);

# This is for converting semigroups of GAP library matrices over finite fields
# to IsMatrixOverFiniteFieldSemigroup
InstallMethod(IsomorphismSemigroup,
"for IsMatrixOverFiniteFieldSemigroup and a semigroup of matrices over a ff",
[IsMatrixOverFiniteFieldSemigroup,
 IsSemigroup and HasGeneratorsOfSemigroup and IsFFECollCollColl],
function(_, S)
  local R, map, T;
  # The following line is required because of the weirdness in constructor
  # method selection, if the method for IsMatrixOverFiniteFieldSemigroup was
  # after this method, then the next 3 lines wouldn't be required, but at the
  # same time that'd be less robust.
  if IsMatrixOverFiniteFieldSemigroup(S) then
    TryNextMethod();
  fi;
  R := DefaultFieldOfMatrix(Representative(S));
  map := x -> Matrix(R, x);
  T := Semigroup(List(GeneratorsOfSemigroup(S), map));
  return SemigroupIsomorphismByFunctionNC(S, T, map, AsList);
end);

InstallMethod(IsomorphismSemigroup,
"for IsMatrixOverFiniteFieldSemigroup, a ring, and a ff mat. semigroup",
[IsMatrixOverFiniteFieldSemigroup,
 IsRing,
 IsSemigroup and HasGeneratorsOfSemigroup and IsFFECollCollColl],
function(_, R, S)
  local D, map, T;
  # The following line is required because of the weirdness in constructor
  # method selection, if the method for IsMatrixOverFiniteFieldSemigroup was
  # after this method, then the next 3 lines wouldn't be required, but at the
  # same time that'd be less robust.
  if IsMatrixOverFiniteFieldSemigroup(S) then
    TryNextMethod();
  fi;
  D := BaseDomain(Representative(S));
  if Size(D) <= Size(R) and IsIdenticalObj(FamilyObj(D), FamilyObj(R))
      and DegreeOverPrimeField(R) mod DegreeOverPrimeField(D) = 0 then
    map := x -> Matrix(R, x);
    T := Semigroup(List(GeneratorsOfSemigroup(S), map));
    return SemigroupIsomorphismByFunctionNC(S, T, map, AsList);
  fi;
  TryNextMethod();
end);

InstallMethod(IsomorphismSemigroup,
"for IsMatrixOverFiniteFieldSemigroup and transformation semigroup with gens",
[IsMatrixOverFiniteFieldSemigroup,
 IsTransformationSemigroup and HasGeneratorsOfSemigroup],
 {_, S} -> IsomorphismSemigroup(IsMatrixOverFiniteFieldSemigroup, GF(2), S));

InstallMethod(IsomorphismSemigroup,
"for IsMatrixOverFiniteFieldSemigroup, a ring, and a transformation semigroup",
[IsMatrixOverFiniteFieldSemigroup,
 IsRing,
 IsTransformationSemigroup and HasGeneratorsOfSemigroup],
function(_, R, S)
  local n, basis, map, iso, inv, gens;

  if not (IsField(R) and IsFinite(R)) then
    ErrorNoReturn("the 2nd argument (a ring) must be a finite field");
  fi;

  n := DegreeOfTransformationSemigroup(S);
  # TODO(later) when GAP allows 0-dimensional matrices and Semigroups requires
  # that version of GAP, then the following if-statement can be removed.
  if n = 0 then
    n := 1;
  fi;
  basis := IdentityMatrix(R, n);
  map := x -> Unpack(basis){ImageListOfTransformation(x, n)};
  iso := x -> Matrix(R, map(x));
  inv := x -> Transformation([1 .. n], i -> PositionNonZero(x[i]));
  gens := List(GeneratorsOfSemigroup(S), iso);

  return SemigroupIsomorphismByFunctionNC(S, Semigroup(gens), iso, inv);
end);

#############################################################################
# 2. Isomorphisms for monoids
#############################################################################

InstallMethod(AsMonoid, "for a matrix over finite field semigroup",
[IsMatrixOverFiniteFieldSemigroup],
function(S)
  if MultiplicativeNeutralElement(S) = fail then
    return fail;  # so that we do the same as the GAP/ref manual says
  fi;
  return Range(IsomorphismMonoid(IsMatrixOverFiniteFieldMonoid, S));
end);

InstallMethod(IsomorphismMonoid,
"for IsMatrixOverFiniteFieldMonoid and a semigroup",
[IsMatrixOverFiniteFieldMonoid, IsSemigroup],
SEMIGROUPS.DefaultIsomorphismMonoid);

InstallMethod(IsomorphismMonoid,
"for IsMatrixOverFiniteFieldMonoid, a ring, and a semigroup",
[IsMatrixOverFiniteFieldMonoid, IsRing, IsSemigroup],
function(filt, R, S)
  local iso1, inv1, iso2, inv2;

  iso1 := IsomorphismTransformationMonoid(S);
  inv1 := InverseGeneralMapping(iso1);
  iso2 := IsomorphismMonoid(filt, R, Range(iso1));
  inv2 := InverseGeneralMapping(iso2);

  return SemigroupIsomorphismByFunctionNC(S,
                                          Range(iso2),
                                          x -> (x ^ iso1) ^ iso2,
                                          x -> (x ^ inv2) ^ inv1);
end);

InstallMethod(IsomorphismMonoid,
"for IsMatrixOverFiniteFieldMonoid and a monoid",
[IsMatrixOverFiniteFieldMonoid, IsMonoid],
{_, S} -> IsomorphismSemigroup(IsMatrixOverFiniteFieldSemigroup, S));

InstallMethod(IsomorphismMonoid,
"for IsMatrixOverFiniteFieldMonoid, a ring, and a monoid",
[IsMatrixOverFiniteFieldMonoid, IsRing, IsMonoid],
{_, R, S} -> IsomorphismSemigroup(IsMatrixOverFiniteFieldSemigroup, R, S));

InstallMethod(IsomorphismMonoid,
"for IsMatrixOverFiniteFieldMonoid and a matrix over finite field monoid",
[IsMatrixOverFiniteFieldMonoid, IsMatrixOverFiniteFieldMonoid],
{_, S} -> SemigroupIsomorphismByFunctionNC(S, S, IdFunc, IdFunc));

InstallMethod(IsomorphismMonoid,
"for IsMatrixOverFiniteFieldMonoid, a ring, and a matrix over ff monoid",
[IsMatrixOverFiniteFieldMonoid, IsRing, IsMatrixOverFiniteFieldMonoid],
{_, R, S} -> IsomorphismSemigroup(IsMatrixOverFiniteFieldSemigroup, R, S));

#############################################################################
# 3. Viewing and printing
#############################################################################

InstallMethod(SemigroupViewStringSuffix,
"for a matrix over finite field semigroup",
[IsMatrixOverFiniteFieldSemigroup],
function(S)
  local n;
  if UserPreference("semigroups", "ViewObj") <> "semigroups-pkg" then
    TryNextMethod();
  fi;
  n := ViewString(NrRows(Representative(S)));
  return Concatenation("\>\>", n, "x", n, "\< \>matrices\< \>over\< \>",
                       ViewString(BaseDomain(S)), "\<\< ");
end);

InstallMethod(ViewObj, "for a general linear monoid",
[IsGeneralLinearMonoid],
Maximum(RankFilter(IsMonoid and HasGeneratorsOfMonoid),
        RankFilter(IsMatrixOverFiniteFieldSemigroup
                   and HasGeneratorsOfSemigroup))
- RankFilter(IsGeneralLinearMonoid) + 1,
function(S)
  PrintFormatted("<general linear monoid {1}x{1} over {2}>",
                 NrRows(Representative(S)),
                 BaseDomain(S));
end);

InstallMethod(PrintString, "for general linear monoid",
[IsGeneralLinearMonoid],
7,  # to beat the method for monoids with generators
function(M)
  local rep, str;

  rep := Representative(M);
  str := Concatenation("GLM(",
                       String(NrRows(rep)),
                       ", ",
                       String(Characteristic(BaseDomain(M))));
  if Characteristic(BaseDomain(M)) <> 1 then
    Append(str, " ^ ");
    Append(str, String(Log(Size(BaseDomain(M)),
                           Characteristic(BaseDomain(M)))));
  fi;
  Append(str, ")");
  return str;
end);

InstallMethod(PrintObj, "for general linear monoid",
[IsGeneralLinearMonoid],
7,  # to beat the method for monoids with generators
function(M)
  Print(PrintString(M));
end);

#############################################################################
# 4. Random
#############################################################################

InstallMethod(SEMIGROUPS_ProcessRandomArgsCons,
[IsMatrixOverFiniteFieldSemigroup, IsList],
function(_, params)

  if Length(params) < 1 then  # nr gens
    params[1] := Random(1, 20);
  elif not IsPosInt(params[1]) then
    return "the 2nd argument (number of generators) is not a pos int";
  fi;
  if Length(params) < 2 then  # dimension
    params[2] := Random(1, 20);
  elif not IsPosInt(params[2]) then
    return "the 3rd argument (matrix dimension) is not a pos int";
  fi;
  if Length(params) < 3 then  # field
    params[3] := GF(Random(Primes), Random(1, 9));
  elif not IsField(params[3]) or not IsFinite(params[3]) then
    return "the 4th argument is not a finite field";
  fi;
  if Length(params) < 4 then  # ranks
    params[4] := [1 .. params[2]];
  elif not IsList(params[4])
      or not ForAll(params[4], x -> IsPosInt(x) and x <= params[2]) then
    return "the 5th argument (matrix ranks) is not a list of pos ints";
  fi;

  if Length(params) > 4 then
    return "there must be at most 5 arguments";
  fi;

  return params;
end);

InstallMethod(SEMIGROUPS_ProcessRandomArgsCons,
[IsMatrixOverFiniteFieldMonoid, IsList],
function(_, params)
  return SEMIGROUPS_ProcessRandomArgsCons(IsMatrixOverFiniteFieldSemigroup,
                                          params);
end);

InstallMethod(RandomSemigroupCons,
"for IsMatrixOverFiniteFieldSemigroup and list",
[IsMatrixOverFiniteFieldSemigroup, IsList],
function(_, params)  # params = [nrgens, dim, field, ranks]
  return Semigroup(List([1 .. params[1]], i -> RandomMatrix(params[3],
                                                            params[2],
                                                            params[4])));
end);

InstallMethod(RandomMonoidCons,
"for IsMatrixOverFiniteFieldMonoid and list",
[IsMatrixOverFiniteFieldMonoid, IsList],
function(_, params)  # params = [nrgens, dim, field, ranks]
  return Monoid(List([1 .. params[1]], i -> RandomMatrix(params[3],
                                                         params[2],
                                                         params[4])));
end);

InstallMethod(RandomInverseSemigroupCons,
"for IsMatrixOverFiniteFieldSemigroup and list",
[IsMatrixOverFiniteFieldSemigroup, IsList],
function(filt, params)
  return AsSemigroup(filt,
                     params[3],
                     RandomInverseSemigroup(IsPartialPermSemigroup,
                                            params[1],
                                            params[2]));
end);

InstallMethod(RandomInverseMonoidCons,
"for IsMatrixOverFiniteFieldMonoid and list",
[IsMatrixOverFiniteFieldMonoid, IsList],
function(filt, params)
    return AsMonoid(filt,
                    params[3],
                    RandomInverseMonoid(IsPartialPermMonoid,
                                        params[1],
                                        params[2]));
end);

InstallMethod(BaseDomain, "for a matrix over finite field semigroup",
[IsMatrixOverFiniteFieldSemigroup], S -> BaseDomain(Representative(S)));

InstallMethod(IsGeneratorsOfInverseSemigroup, "for an ffe coll coll coll ",
[IsFFECollCollColl],
coll -> IsGeneratorsOfSemigroup(coll) and ForAll(coll, x -> x ^ -1 <> fail));

#############################################################################
# 5. Methods for acting semigroups setup
#############################################################################

InstallGlobalFunction(MatrixOverFiniteFieldRowSpaceRightAction,
function(_, vsp, m)
  local nvsp, deg, i;

  Assert(1, IsRowBasisOverFiniteField(vsp));
  Assert(1, IsMatrixObjOverFiniteField(m));
  Assert(1, Rank(vsp) > 0);

  # This takes care of the token element
  if Rank(vsp) > NrRows(m) then
    return RowSpaceBasis(m);
  else
    nvsp := Unpack(vsp!.rows * m);
  fi;
  TriangulizeMat(nvsp);

  deg := Length(nvsp);
  for i in [deg, deg - 1 .. 1] do
    if IsZero(nvsp[i]) then
      Remove(nvsp, i);
    fi;
  od;

  return NewRowBasisOverFiniteField(IsPlistRowBasisOverFiniteFieldRep,
                                    BaseDomain(vsp),
                                    nvsp);
end);

InstallGlobalFunction(MatrixOverFiniteFieldLocalRightInverse,
function(S, V, mat)
  local n, k, W, se, zv, u, j, i;

  Assert(1, IsMatrixOverFiniteFieldSemigroup(S));
  Assert(1, IsRowBasisOverFiniteField(V));
  Assert(1, IsMatrixObjOverFiniteField(mat));
  Assert(1, NrRows(mat) > 0);
  Assert(1, Rank(V) > 0);

  n := NrRows(mat);
  k := Rank(V);

  W := Unpack(V!.rows * mat);

  for i in [1 .. k] do
    Append(W[i], V!.rows[i]);
  od;
  se := SemiEchelonMat(W);
  # If the matrix does not act injectively on V, then there is no right inverse
  # TODO(later) I think we can now simplify things below
  if Number(se.heads{[1 .. n]}, IsZero) > n - k then
    return fail;
  fi;

  for i in [1 .. Length(se.vectors)] do
    W[i] := ShallowCopy(se.vectors[i]);
  od;

  zv := [1 .. 2 * n] * Zero(BaseDomain(mat));
  for i in [1 .. n - Length(W)] do
    Add(W, ShallowCopy(zv));
  od;

  # add missing heads
  u := One(BaseDomain(mat));
  j := k + 1;
  for i in [1 .. n] do
    if se.heads[i] = 0 then
      W[j][i] := u;
      W[j][n + i] := u;
      j := j + 1;
    fi;
  od;
  TriangulizeMat(W);

  return Matrix(W{[1 .. n]}{[n + 1 .. 2 * n]}, mat);
end);

# Returns an invertible matrix.
# TODO(later): make pretty and efficient (in that order).  In particular the
# setup for the matrix should be much more efficient.
InstallGlobalFunction(MatrixOverFiniteFieldSchutzGrpElement,
function(_, x, y)
  local deg, n, eqs, idx, col, row, res;

  Assert(1, IsMatrixObjOverFiniteField(x));
  Assert(1, IsMatrixObjOverFiniteField(y));

  n := Rank(x);
  deg := NrRows(x);

  eqs := TransposedMatMutable(Concatenation(TransposedMat(x),
                                            TransposedMat(y)));
  TriangulizeMat(eqs);

  idx := [];
  col := 1;
  row := 1;

  while col <= deg do
    while IsZero(eqs[row, col]) and col <= deg do
      col := col + 1;
    od;
    if col <= deg then
      Add(idx, col);
      row := row + 1;
      col := col + 1;
    fi;
  od;
  res := Matrix(BaseDomain(x), eqs{[1 .. n]}{idx + deg});
  Assert(1, res ^ (-1) <> fail);
  return res;
end);

# StabilizerAction
InstallGlobalFunction(MatrixOverFiniteFieldStabilizerAction,
function(_, x, m)
  local n, k, rsp, zv, i;
  Assert(1, IsMatrixObjOverFiniteField(x));
  Assert(1, IsFFECollColl(m));
  Assert(1, not IsZero(x));
  Assert(1, not IsZero(m));

  n := NrRows(m);
  k := Rank(x);
  rsp := ShallowCopy(m * RowSpaceBasis(x)!.rows);

  zv := [1 .. n] * Zero(BaseDomain(x));
  for i in [1 .. n - k] do
    Add(rsp, ShallowCopy(zv));
  od;

  return Matrix(RowSpaceTransformationInv(x) * rsp, x);
end);

# This should be doable in a much more efficient way
InstallGlobalFunction(MatrixOverFiniteFieldLambdaConjugator,
function(_, x, y)
  local xse, h, p, yse, q;
  Assert(1, IsMatrixObjOverFiniteField(x));
  Assert(1, IsMatrixObjOverFiniteField(y));
  xse := SemiEchelonMat(Unpack(x));
  h := Filtered(xse.heads, x -> x <> 0);
  p := One(BaseDomain(x))
       * PermutationMat(SortingPerm(h), Length(h), BaseDomain(x));
  yse := SemiEchelonMat(Unpack(y));
  h := Filtered(yse.heads, x -> x <> 0);
  q := One(BaseDomain(y))
       * PermutationMat(SortingPerm(h), Length(h), BaseDomain(y));
  return p * q ^ (-1);
end);

# Is there a complete direct way of testing whether this idempotent exists
# (without constructing it)?  The method below is already pretty efficient.

InstallGlobalFunction(MatrixOverFiniteFieldIdempotentTester,
function(_, x, y)
  Assert(1, IsPlistRowBasisOverFiniteFieldRep(x));
  Assert(1, IsPlistRowBasisOverFiniteFieldRep(y));
  return MatrixOverFiniteFieldIdempotentCreator(_, x, y) <> fail;
end);

# Attempt to construct an idempotent m with RowSpace(m) = x
# ColumnSpace(m) = y

InstallGlobalFunction(MatrixOverFiniteFieldIdempotentCreator,
function(S, x, y)
  local m, inv;

  Assert(1, IsMatrixOverFiniteFieldSemigroup(S));
  Assert(1, IsRowBasisOverFiniteField(x));
  Assert(1, Rank(x) <> 0);
  Assert(1, IsRowBasisOverFiniteField(y));
  Assert(1, Rank(y) <> 0);
  Assert(1, Length(x!.rows[1]) = Length(y!.rows[1]));

  m := Matrix(BaseDomain(S), TransposedMat(y!.rows) * x!.rows);
  inv := MatrixOverFiniteFieldLocalRightInverse(S, x, m);
  if inv = fail then
    return fail;
  fi;
  return m * inv;
end);

InstallMethod(IsGeneratorsOfSemigroup, "for an ffe coll coll coll",
[IsFFECollCollColl],
function(coll)
  local rep;
  Assert(1, not IsEmpty(coll));
  rep := Representative(coll);
  if IsMatrixObjOverFiniteField(rep) then
    return ForAll(coll, x -> NrRows(x) = NrRows(coll[1])
                             and BaseDomain(x) = BaseDomain(coll[1])
                             and NrRows(x) = NrCols(x));
  fi;
  TryNextMethod();
end);

#############################################################################
# 6. Properties of matrix over finite field semigroups
#############################################################################

# FIXME(later) this method is not correct (although it works as documented)
# This should check whether <S> = GLM of the right dimensions/field

InstallMethod(IsFullMatrixMonoid, "for a semigroup",
[IsSemigroup], ReturnFalse);
