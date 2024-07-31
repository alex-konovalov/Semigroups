############################################################################
##
##  elements/ffmat.gi
##  Copyright (C) 2016-2022                              James D. Mitchell
##                                                         Markus Pfeiffer
##
##  Licensing information can be found in the README file of this package.
##
#############################################################################
##

#############################################################################
# This file contains the implementations of the operations etc declared in
# ffmat.gd for matrix objects over finite fields.
#############################################################################

#############################################################################
# The file is organised as follows:
#
# 1. Random matrices
# 2. Rows bases etc
# 3. Attributes etc for IsMatrixObjOverFiniteField
# 4. Helper functions
#############################################################################

# The following are only used in this file and so are declared here in the gi
# file.

BindGlobal("PlistRowBasisOverFiniteFieldFamily",
           NewFamily("PlistRowBasisOverFiniteFieldFamily",
           IsRowBasisOverFiniteField, CanEasilyCompareElements));

BindGlobal("PlistRowBasisOverFiniteFieldType",
           NewType(PlistRowBasisOverFiniteFieldFamily,
                   IsRowBasisOverFiniteField
                   and IsPlistRowBasisOverFiniteFieldRep));

InstallMethod(IsMatrixObjOverFiniteField, "for a matrix obj",
[IsMultiplicativeElement],
function(m)
  return IsMatrixObj(m)
   and IsField(BaseDomain(m))
   and IsFinite(BaseDomain(m))
   and NrRows(m) = NrCols(m);
end);

InstallMethod(OneMutable, "for an FFE coll coll coll",
[IsFFECollCollColl], coll -> One(Representative(coll)));

###############################################################################
# 1. Random matrices
###############################################################################

# Note that: the following methods implement the RandomMatrix interface for
# IsMatrixOverSemiring in the Semigroups package and do not related to anything
# similar in the GAP library for IsMatrixObj (if they exist).

InstallMethod(RandomMatrixOp, "for a finite field and pos int",
[IsField and IsFinite, IsPosInt],
function(field, n)
  local xy, i, j;

  xy := List([1 .. n], x -> EmptyPlist(n));
  for i in [1 .. n] do
    for j in [1 .. n] do
      xy[i][j] := Random(field);
    od;
  od;
  return Matrix(field, xy);
end);

InstallMethod(RandomMatrixOp,
"for a finite field, dimension, and list of ranks",
[IsField and IsFinite, IsPosInt, IsList],
function(R, n, ranks)
  local z, rk, mat, zv, conj, j;

  if ForAny(ranks, x -> (x < 0) or (x > n)) then
    ErrorNoReturn("the list of ranks has to consist of numbers > 0 and < n");
  fi;

  z := Zero(R);
  # Choose a matrix of given rank
  rk := Random(ranks);
  if rk = 0 then
    return ZeroMatrix(R, n, n);
  fi;
  mat := Unpack(Random(GL(rk, R)));
  # Extend it to n x n
  zv := [1 .. n - rk] * z;
  for j in [1 .. rk] do
    Append(mat[j], zv);
  od;
  zv := [1 .. n] * z;
  for j in [1 .. n - rk] do
    Add(mat, zv);
  od;
  # Swirl around
  # Is Permuting rows/columns enough?
  conj := Random(GL(n, R));  # PermutationMat(Random(Sym(n)), n, R);
  return Matrix(R, mat ^ conj);
end);

InstallMethod(RandomMatrixOp,
"for a finite field, dimension, and pos int",
[IsField and IsFinite, IsPosInt, IsPosInt],
{R, n, rank} -> RandomMatrixOp(R, n, [rank]));

#############################################################################
# 2. Rows bases etc
#############################################################################

InstallMethod(NewRowBasisOverFiniteField,
"for IsPlistRowBasisOverFiniteFieldRep, a ring, and a list",
[IsPlistRowBasisOverFiniteFieldRep, IsRing, IsList],
function(_, basedomain, l)
  local b;
  b := Objectify(PlistRowBasisOverFiniteFieldType, rec(rows := l));
  SetBaseDomain(b, basedomain);
  return b;
end);

InstallMethod(Rank, "for a plist rowbasis", [IsPlistRowBasisOverFiniteFieldRep],
v -> Length(v!.rows));

InstallMethod(\=, "for an rowbasis",
[IsPlistRowBasisOverFiniteFieldRep, IsPlistRowBasisOverFiniteFieldRep],
{x, y} -> BaseDomain(x) = BaseDomain(y) and x!.rows = y!.rows);

InstallMethod(\<, "for an rowbasis",
[IsPlistRowBasisOverFiniteFieldRep, IsPlistRowBasisOverFiniteFieldRep],
{x, y} -> Rank(x) < Rank(y) or (Rank(x) = Rank(y) and (x!.rows < y!.rows)));

InstallMethod(ViewString, "for a plist rowbasis",
[IsPlistRowBasisOverFiniteFieldRep],
function(v)
  return STRINGIFY("<rowbasis of rank ",
                   Rank(v),
                   " over ",
                   BaseDomain(v),
                   ">");
end);

InstallMethod(String, "for a plist rowbasis",
[IsPlistRowBasisOverFiniteFieldRep],
function(v)
  return STRINGIFY("NewRowBasisOverFiniteField(",
                   "IsPlistRowBasisOverFiniteFieldRep, ",
                   BaseDomain(v),
                   ", ",
                   v!.rows, ")");
end);

SEMIGROUPS.HashFunctionForPlistRowBasisOverFiniteField := function(x, data)
  if Rank(x) = 0 then
    return 1;
  fi;
  Assert(1, IsRecord(data));
  return data.func(x!.rows, data.data);
end;

InstallMethod(ChooseHashFunction, "for plist row basis over finite field",
[IsPlistRowBasisOverFiniteFieldRep, IsInt],
function(x, hashlen)
  local data;
  if Rank(x) <> 0 then
    data := ChooseHashFunction(x!.rows, hashlen);
  else
    data := hashlen;
  fi;
  return rec(func := SEMIGROUPS.HashFunctionForPlistRowBasisOverFiniteField,
             data := data);
end);

#############################################################################
# 3. Attributes etc for IsMatrixObjOverFiniteField
#############################################################################

InstallMethod(RowSpaceBasis, "for a matrix obj over finite field",
[IsMatrixObj],
function(m)
  if not IsMatrixObjOverFiniteField(m) then
    TryNextMethod();
  fi;
  return ComputeRowSpaceAndTransformation(m)[1];
end);

InstallMethod(RowSpaceTransformation, "for a matrix obj over finite field",
[IsMatrixObj],
function(m)
  if not IsMatrixObjOverFiniteField(m) then
    TryNextMethod();
  fi;
  return ComputeRowSpaceAndTransformation(m)[2];
end);

InstallMethod(RowSpaceTransformationInv, "for a matrix obj over finite field",
[IsMatrixObj],
function(m)
  if not IsMatrixObjOverFiniteField(m) then
    TryNextMethod();
  fi;
  return ComputeRowSpaceAndTransformation(m)[3];
end);

# Should this go in a helper function, it also works similarly to the thing
# done below.
InstallMethod(RightInverse, "for a matrix obj over finite field",
[IsMatrixObj],
function(m)
  local deg, u, rsp, zv, se, i;

  if not IsMatrixObjOverFiniteField(m) then
    TryNextMethod();
  fi;

  deg := NrRows(m);
  u := One(BaseDomain(m));

  rsp := Unpack(m);
  zv := [1 .. deg] * Zero(BaseDomain(m));
  for i in [1 .. deg] do
    Append(rsp[i], zv);
    rsp[i][deg + i] := u;
  od;
  se := SemiEchelonMat(rsp);

  for i in [1 .. Length(se.vectors)] do
    rsp[i] := ShallowCopy(se.vectors[i]);
  od;
  for i in [1 .. deg] do
    if se.heads[i] = 0 then
      rsp[i][i] := u;
      rsp[i][deg + i] := Zero(BaseDomain(m));
    fi;
  od;
  TriangulizeMat(rsp);

  return Matrix(rsp{[1 .. deg]}{[deg + 1 .. 2 * deg]}, m);
end);

InstallMethod(LeftInverse, "for a matrix obj over finite field",
[IsMatrixObj],
function(m)
  if not IsMatrixObjOverFiniteField(m) then
    TryNextMethod();
  fi;
  return TransposedMat(RightInverse(TransposedMat(m)));
end);

#############################################################################
# 4. Helper functions
#############################################################################

InstallGlobalFunction(ComputeRowSpaceAndTransformation,
function(m)
  local deg, bd, bas, tr, tri, sinv, rsp, zv, heads, tm, i;

  Assert(1, IsMatrixObjOverFiniteField(m));

  deg := NrRows(m);
  bd := BaseDomain(m);
  if IsZero(m) then
    bas := [];
    tr := IdentityMat(deg, bd);
    tri := tr;
    sinv := fail;
  else
    rsp := Unpack(m);
    zv := [1 .. deg] * Zero(bd);
    for i in [1 .. deg] do
      Append(rsp[i], ShallowCopy(zv));
      rsp[i][deg + i] := One(bd);
    od;
    TriangulizeMat(rsp);

    heads := [];
    bas := rsp{[1 .. deg]}{[1 .. deg]};
    for i in [deg, deg - 1 .. 1] do
      if IsZero(bas[i]) then
        Remove(bas, i);
      else
        heads[PositionNonZero(bas[i])] := i;
      fi;
    od;
    # Check whether this matrix has a semigroup inverse, i.e. a matrix t such
    # that t * m * t = t and m * t * m = m. If it does this matrix is the
    # transformation we computed otherwise we set fail
    tm := TransposedMat(bas);
    sinv := true;
    for i in [1 .. deg] do
      if not IsBound(heads[i]) then
        if not IsZero(tm[i]) then
          sinv := fail;
        fi;
      fi;
    od;
    # This is obviously totally ridiculous to do the same computation twice
    if sinv = true then
       sinv := RightInverse(m);
    fi;
    tr := rsp{[1 .. deg]}{[deg + 1 .. 2 * deg]};
    tri := tr ^ (-1);
  fi;

  ConvertToVectorRep(bas);
  MakeImmutable(bas);
  bas := NewRowBasisOverFiniteField(IsPlistRowBasisOverFiniteFieldRep, bd, bas);
  return [bas, tr, tri];
end);
