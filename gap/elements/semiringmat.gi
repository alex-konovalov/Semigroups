############################################################################
##
##  elements/semiringmat.gi
##  Copyright (C) 2015-2022                              James D. Mitchell
##
##  Licensing information can be found in the README file of this package.
##
#############################################################################
##

# This file contains declarations for matrices over semirings.

# A matrix over semiring <mat> is:
#
#   mat![i] = the ith row
#
# it is also square, any additional data (like the threshold for tropical
# matrices), is contained in the positions from Length(mat![1]) + 1 onwards.

#############################################################################
# Internal
#############################################################################

SEMIGROUPS.TropicalizeMat := function(mat, threshold)
  local n, i, j;

  n := Length(mat);
  mat[n + 1] := threshold;
  for i in [1 .. n] do
    for j in [1 .. n] do
      if IsInt(mat[i, j]) then
        mat[i, j] := AbsInt(mat[i, j]);
        if mat[i, j] > threshold then
          mat[i, j] := threshold;
        fi;
      fi;
    od;
  od;
  return mat;
end;

SEMIGROUPS.NaturalizeMat := function(x, threshold, period)
  local n, i, j;

  n := Length(x);
  x[n + 1] := threshold;
  x[n + 2] := period;
  for i in [1 .. n] do
    for j in [1 .. n] do
      x[i][j] := AbsInt(x[i][j]);
      if x[i][j] > threshold then
        x[i][j] := threshold + (x[i][j] - threshold) mod period;
      fi;
    od;
  od;
  return x;
end;

SEMIGROUPS.HashFunctionMatrixOverSemiring := function(x, data)
  local n, h, i, j;
  n := DimensionOfMatrixOverSemiring(x);
  h := 0;
  for i in [1 .. n] do
    for j in [1 .. n] do
      if x![i][j] <> infinity and x![i][j] <> -infinity then
        h := ((h / 4) + x![i][j]) mod data;
      fi;
    od;
  od;
  return h + 1;
end;

SEMIGROUPS.MatrixTrans := function(x, dim, zero, one)
  local mat, i;

  mat := List([1 .. dim], x -> ShallowCopy([1 .. dim] * 0 + zero));
  for i in [1 .. dim] do
    mat[i, i ^ x] := one;
  od;
  return mat;
end;

#############################################################################
# Pickler
#############################################################################

InstallMethod(IO_Pickle, "for a matrix over semiring",
[IsFile, IsPlistMatrixOverSemiringPositionalRep],
function(file, mat)
  local pickle, i;

  if IO_Write(file, "MOSR") = fail then
    return IO_Error;
  fi;
  pickle := [SEMIGROUPS_FilterOfMatrixOverSemiring(mat), []];
  i := 1;
  while IsBound(mat![i]) do
    pickle[2, i] := mat![i];
    i := i + 1;
  od;

  return IO_Pickle(file, pickle);
end);

IO_Unpicklers.MOSR := function(file)
  local arg;
  arg := IO_Unpickle(file);
  if arg = IO_Error then
    return IO_Error;
  elif arg[1] = IsBooleanMat then
    Perform(arg[2], ConvertToBlistRep);
  fi;
  return CallFuncList(MatrixNC, arg);
end;

InstallMethod(IsGeneratorsOfSemigroup, "for a generalized row vector",
[IsGeneralizedRowVector],
# TODO(MatrixObj-later) is this the best way to recognise a collection of
# MatrixObj?
function(coll)
  local n;
  if ForAll(coll, IsMatrixObj)
      and ForAll(coll, x -> BaseDomain(x) = Integers) then
    n := NrRows(Representative(coll));
    return ForAll(coll, x -> NrRows(x) = n and NrCols(x) = n);
  fi;
  TryNextMethod();
end);

InstallMethod(IsGeneratorsOfSemigroup,
"for a matrix over semiring collection",
[IsMatrixOverSemiringCollection],
function(coll)
  local n;
  if IsGreensClass(coll) or IsSemigroup(coll) then
    return true;
  elif (IsTropicalMaxPlusMatrixCollection(coll)
        or IsTropicalMinPlusMatrixCollection(coll))
      and ForAny(coll, x -> ThresholdTropicalMatrix(x)
                            <> ThresholdTropicalMatrix(coll[1])) then
    return false;
  elif IsNTPMatrixCollection(coll)
      and (ForAny(coll, x -> ThresholdNTPMatrix(x)
                             <> ThresholdNTPMatrix(coll[1]))
           or ForAny(coll, x -> PeriodNTPMatrix(x)
                                <> PeriodNTPMatrix(coll[1]))) then
    return false;
  fi;
  n := DimensionOfMatrixOverSemiring(coll[1]);
  return ForAll(coll, x -> DimensionOfMatrixOverSemiring(x) = n);
end);

#############################################################################
# Constructors
#############################################################################

# Note that MatrixNC changes its argument in place!!

InstallMethod(MatrixNC, "for a type and list",
[IsType, IsList],
function(type, mat)
  MakeImmutable(mat);
  return Objectify(type, mat);
end);

InstallMethod(MatrixNC, "for a filter and list", [IsOperation, IsList],
{filter, mat} -> MatrixNC(SEMIGROUPS_TypeOfMatrixOverSemiringCons(filter), mat));

InstallMethod(MatrixNC, "for a filter, list, function",
[IsOperation, IsList, IsFunction],
function(filter, mat, preproc)
  return MatrixNC(SEMIGROUPS_TypeOfMatrixOverSemiringCons(filter),
                  preproc(mat));
end);

InstallMethod(MatrixNC,
"for a plist matrix over semiring positional rep and mutable list",
[IsPlistMatrixOverSemiringPositionalRep, IsList and IsMutable],
function(sample, mat)
  local n, filter;

  # transfer whatever comes after the rows of the matrix, i.e. threshold,
  # period etc.
  n := Length(sample![1]) + 1;
  while IsBound(sample![n]) do
    mat[n] := sample![n];
    n := n + 1;
  od;

  # Cannot use TypeObj(sample) since it can contain information about
  # properties satisfied (or not) by x.
  filter := SEMIGROUPS_FilterOfMatrixOverSemiring(sample);
  return MatrixNC(SEMIGROUPS_TypeOfMatrixOverSemiringCons(filter), mat);
end);

InstallMethod(Matrix,
"for a filter, homogeneous list, pos int, and pos int",
[IsOperation, IsHomogeneousList, IsInt, IsInt],
function(filter, mat, threshold, period)
  local checker, row;

  if not IsRectangularTable(mat) or Length(mat) <> Length(mat[1]) then
    TryNextMethod();
  elif filter <> IsNTPMatrix then
    TryNextMethod();
  fi;

  checker := SEMIGROUPS_MatrixOverSemiringEntryCheckerCons(filter,
                                                           threshold,
                                                           period);
  for row in mat do
    if not ForAll(row, checker) then
      ErrorNoReturn("the entries in the 2nd argument do not define a matrix ",
                    "of type ", NameFunction(filter));
    fi;
  od;

  return MatrixNC(filter,
                  List(mat, ShallowCopy),
                  x -> SEMIGROUPS.NaturalizeMat(x, threshold, period));
end);

InstallMethod(Matrix,
"for a filter, homogeneous list, and pos int",
[IsOperation, IsHomogeneousList, IsPosInt],
function(filter, mat, threshold)
  local checker, row;

  if not IsRectangularTable(mat) or Length(mat) <> Length(mat[1]) then
    ErrorNoReturn("the 2nd argument must define a square matrix");
  elif filter <> IsTropicalMaxPlusMatrix
      and filter <> IsTropicalMinPlusMatrix then
    ErrorNoReturn("cannot create a matrix from the given arguments");
  fi;

  checker := SEMIGROUPS_MatrixOverSemiringEntryCheckerCons(filter,
                                                           threshold);
  for row in mat do
    if not ForAll(row, checker) then
      ErrorNoReturn("the entries in the 2nd argument do not define a matrix ",
                    "of type ", NameFunction(filter));
    fi;
  od;

  return MatrixNC(filter,
                  List(mat, ShallowCopy),
                  x -> SEMIGROUPS.TropicalizeMat(x, threshold));
end);

InstallMethod(Matrix, "for a filter and homogeneous list",
[IsOperation, IsHomogeneousList],
function(filter, mat)
  local row;

  if not IsRectangularTable(mat) or Length(mat) <> Length(mat[1]) then
    TryNextMethod();
  elif not filter in [IsBooleanMat,
                      IsMaxPlusMatrix,
                      IsMinPlusMatrix,
                      IsProjectiveMaxPlusMatrix] then
    TryNextMethod();
  elif filter = IsBooleanMat then
    return BooleanMat(mat);
  fi;

  for row in mat do
    if not ForAll(row, SEMIGROUPS_MatrixOverSemiringEntryCheckerCons(filter))
        then
      ErrorNoReturn("the entries in the 2nd argument do not define a matrix ",
                    "of type ", NameFunction(filter));
    fi;
  od;

  return MatrixNC(filter, List(mat, ShallowCopy));
end);

InstallMethod(Matrix, "for a semiring and empty list",
[IsSemiring, IsList and IsEmpty],
function(semiring, mat)
  if IsIntegers(semiring) then
    return Matrix(Integers, mat);
  fi;
  TryNextMethod();
end);

InstallMethod(Matrix, "for a semiring and matrix over semiring",
[IsSemiring, IsMatrixOverSemiring],
{R, mat} -> Matrix(R, AsList(mat)));

InstallMethod(RandomMatrix, "for an operation and pos int",
[IsOperation, IsPosInt], RandomMatrixCons);

InstallMethod(RandomMatrix, "for an operation, pos int, and int",
[IsOperation, IsPosInt, IsInt], RandomMatrixCons);

InstallMethod(RandomMatrix, "for an operation, pos int, int, and int",
[IsOperation, IsPosInt, IsInt, IsInt], RandomMatrixCons);

InstallMethod(RandomMatrix, "for a semiring and non-negative int",
[IsSemiring, IsInt],
function(semiring, dim)
  if dim < 0 then
    TryNextMethod();
  fi;
  return RandomMatrixOp(semiring, dim);
end);

InstallMethod(RandomMatrix, "for a semiring, non-negative int, and pos int",
[IsSemiring, IsInt, IsPosInt],
function(semiring, dim, rank)
  if dim < 0 then
    TryNextMethod();
  fi;
  return RandomMatrixOp(semiring, dim, rank);
end);

InstallMethod(RandomMatrix, "for a semiring, non-negative int, and list",
[IsSemiring, IsInt, IsList],
function(semiring, dim, ranks)
  if dim < 0 then
    TryNextMethod();
  fi;
  return RandomMatrixOp(semiring, dim, ranks);
end);

InstallMethod(AsTransformation, "for a matrix over semiring",
[IsMatrixOverSemiring],
function(mat)
  local one, dim;

  one := One(mat);
  dim := DimensionOfMatrixOverSemiring(mat);
  if Union(AsList(mat)) <> Union(AsList(one))
      or ForAny([1 .. dim], i -> Number(mat[i], j -> j = one[1][1]) <> 1) then
    return fail;
  fi;

  one := one[1][1];
  return Transformation(List([1 .. dim], i -> Position(mat[i], one)));
end);

InstallMethod(AsMutableList, "for matrix over semiring",
[IsMatrixOverSemiring],
mat -> List([1 .. NrRows(mat)], i -> ShallowCopy(mat[i])));

InstallMethod(AsList, "for matrix over semiring",
[IsMatrixOverSemiring],
mat -> List([1 .. NrRows(mat)], i -> mat[i]));

InstallMethod(Iterator, "for a matrix over semiring",
[IsMatrixOverSemiring],
function(mat)
  local iter;

  iter := rec(pos := 0);

  iter.NextIterator := function(iter)
    if IsDoneIterator(iter) then
      return fail;
    fi;
    iter!.pos := iter!.pos + 1;
    return mat[iter!.pos];
  end;

  iter.IsDoneIterator := function(iter)
    if iter!.pos = Length(mat[1]) then
      return true;
    fi;
    return false;
  end;

  iter.ShallowCopy := _ -> rec(pos := 0);

  return IteratorByFunctions(iter);
end);

InstallOtherMethod(\[\], "for a matrix over semiring and a pos int",
[IsPlistMatrixOverSemiringPositionalRep, IsPosInt],
function(mat, pos)
  if pos > Length(mat![1]) then
    ErrorNoReturn("the position is greater than the dimension of the matrix");

  fi;
  return mat![pos];
end);

InstallMethod(MatElm,
"for a plist matrix over semiring positional rep, and two pos ints",
[IsPlistMatrixOverSemiringPositionalRep, IsPosInt, IsPosInt],
function(mat, row, col)
  if Maximum(row, col) > NumberRows(mat) then
    ErrorNoReturn(
      StringFormatted("the 1st argument (a matrix) only is {1}x{1}, ",
                      NrRows(mat)),
      StringFormatted("but trying to access [{}, {}]", row, col));
  fi;
  return mat![row][col];
end);

InstallMethod(IsBound\[\],
"for a plist matrix over semiring positional rep and pos int",
[IsPlistMatrixOverSemiringPositionalRep, IsPosInt],
{mat, pos} -> IsBound(mat![pos]) and pos <= Length(mat![1]));

InstallMethod(TransposedMatImmutable, "for a matrix over semiring",
[IsPlistMatrixOverSemiringPositionalRep],
function(x)
  local n, y, i, j;

  n := DimensionOfMatrixOverSemiring(x);
  y := EmptyPlist(n + 2);
  for i in [1 .. n] do
    y[i] := [];
    for j in [1 .. n] do
      y[i][j] := x[j][i];
    od;
  od;

  return MatrixNC(x, y);
end);

InstallMethod(OneMutable, "for a matrix over semiring",
[IsMatrixOverSemiring], OneImmutable);

InstallMethod(OneMutable, "for a matrix over semiring collection",
[IsMatrixOverSemiringCollection], OneImmutable);

InstallMethod(OneImmutable, "for a matrix over semiring collection",
[IsMatrixOverSemiringCollection],
function(coll)
  if IsGeneratorsOfSemigroup(coll) then
    return OneImmutable(Representative(coll));
  fi;
  return fail;
end);

InstallMethod(InverseMutable, "for a matrix over semiring",
[IsMatrixOverSemiring], ReturnFail);

InstallMethod(InverseImmutable, "for a matrix over semiring",
[IsMatrixOverSemiring], ReturnFail);

InstallMethod(IsGeneratorsOfInverseSemigroup,
"for a matrix over semiring coll",
[IsMatrixOverSemiringCollection], ReturnFalse);

InstallMethod(DimensionOfMatrixOverSemiring, "for a matrix over a semiring",
[IsMatrixOverSemiring], NumberColumns);

InstallMethod(NumberRows, "for a matrix over a semiring",
[IsMatrixOverSemiring], NumberColumns);

InstallMethod(NumberColumns, "for a matrix over a semiring",
[IsMatrixOverSemiring],
function(mat)
  if IsBound(mat[1]) then
    return Length(mat[1]);
  fi;
  return 0;
end);

InstallMethod(DimensionOfMatrixOverSemiringCollection,
"for a matrix over semiring collection",
[IsMatrixOverSemiringCollection],
function(coll)
  local dim;

  dim := DimensionOfMatrixOverSemiring(Representative(coll));
  if not ForAll(coll, x -> DimensionOfMatrixOverSemiring(x) = dim) then
    ErrorNoReturn("the argument <coll> must be a collection of ",
                  "matrices of equal dimension");
  fi;
  return dim;
end);

# The next method is required because the previous one will try to enumerate
# the whole semigroup to check that the elements all have the same dimension,
# which they have to by default anyway.

InstallMethod(DimensionOfMatrixOverSemiringCollection,
"for a matrix over semiring semigroup",
[IsMatrixOverSemiringSemigroup],
S -> DimensionOfMatrixOverSemiring(Representative(S)));

InstallMethod(Display, "for a matrix over semiring collection",
[IsMatrixOverSemiringCollection],
function(coll)
  Print(DisplayString(coll));
end);

InstallMethod(DisplayString, "for a matrix over semiring collection",
[IsMatrixOverSemiringCollection],
coll -> JoinStringsWithSeparator(List(coll, DisplayString), "\n"));

InstallMethod(DisplayString, "for a matrix over semiring",
[IsMatrixOverSemiring],
function(x)
  local n, max, length, pad, str, i, j;

  n := DimensionOfMatrixOverSemiring(x);

  # find the max entry
  max := 0;
  for i in [1 .. n] do
    for j in [1 .. n] do
      if x[i][j] = infinity then
        length := 1;
      elif x[i][j] = -infinity then
        length := 2;
      else
        length := Length(String(x[i][j]));
      fi;
      if length > max then
        max := length;
      fi;
    od;
  od;

  pad := function(entry)
    local n;
    if entry = infinity then
      entry := "∞";
      n := 1;
    elif entry = -infinity then
      entry := "-∞";
      n := 2;
    else
      entry := String(entry);
      n := Length(entry);
    fi;
    return Concatenation(ListWithIdenticalEntries(max - n, ' '),
                         entry, " ");
  end;

  str := "";
  for i in [1 .. n] do
    for j in [1 .. n] do
      Append(str, pad(x[i][j]));
    od;
    Remove(str, Length(str));
    Append(str, "\n");
  od;
  return str;
end);

InstallMethod(ViewString, "for a matrix over semiring", [IsMatrixOverSemiring],
function(x)
  local str;
  if DimensionOfMatrixOverSemiring(x) < 9 then
    return PrintString(x);
  fi;
  str := "<";
  Append(str, String(DimensionOfMatrixOverSemiring(x)));
  Append(str, "x");
  Append(str, String(DimensionOfMatrixOverSemiring(x)));
  Append(str, " ");
  Append(str, SEMIGROUPS_TypeViewStringOfMatrixOverSemiring(x));
  Append(str, " matrix>");
  return str;
end);

InstallMethod(PrintString, "for a matrix over semiring collection",
[IsMatrixOverSemiringCollection],
function(coll)
  local str, i;
  if IsGreensClass(coll) or IsSemigroup(coll) then
    TryNextMethod();
  fi;
  str := ShallowCopy(PrintString(coll[1]));
  for i in [2 .. Length(coll)]  do
    Append(str, "\>");
    Append(str, PrintString(coll[i]));
    Append(str, "\<, ");
  od;
  Remove(str, Length(str));
  Remove(str, Length(str));
  return str;
end);

InstallMethod(PrintString, "for a matrix over semiring",
[IsMatrixOverSemiring],
function(x)
  local n, str, i, j;

  n := DimensionOfMatrixOverSemiring(x);
  str := "\>\>Matrix(\<\>";
  Append(str, NameFunction(SEMIGROUPS_FilterOfMatrixOverSemiring(x)));
  Append(str, "\<, \>[");
  for i in [1 .. n] do
    Append(str, "\>\>[");
    for j in [1 .. n] do
      if IsBooleanMat(x) then
        if x[i][j] then
          Append(str, String(1));
        else
          Append(str, String(0));
        fi;
      else
        Append(str, String(x[i][j]));
      fi;

      Append(str, ", ");
    od;
    Remove(str, Length(str));
    Remove(str, Length(str));
    Append(str, "]\<, \<");
  od;

  for i in [1 .. 4] do
    Remove(str, Length(str));
  od;
  Append(str, "\<\<]");

  if IsNTPMatrix(x) then
    Append(str, ", \>");
    Append(str, PrintString(ThresholdNTPMatrix(x)));
    Append(str, "\<");
    Append(str, ", \>");
    Append(str, PrintString(PeriodNTPMatrix(x)));
    Append(str, "\<");
  elif IsTropicalMatrix(x) then
    Append(str, ", \>");
    Append(str, PrintString(ThresholdTropicalMatrix(x)));
    Append(str, "\<");
  fi;
  Append(str, "\<)\<");

  return str;
end);

InstallMethod(String, "for a matrix over semiring",
[IsMatrixOverSemiring],
function(x)
  local str;

  str := "Matrix(";
  Append(str, NameFunction(SEMIGROUPS_FilterOfMatrixOverSemiring(x)));
  Append(str, ", ");
  Append(str, String(AsList(x)));

  if IsNTPMatrix(x) then
    Append(str, ", ");
    Append(str, String(ThresholdNTPMatrix(x)));
    Append(str, ", ");
    Append(str, String(PeriodNTPMatrix(x)));
  elif IsTropicalMatrix(x) then
    Append(str, ", ");
    Append(str, String(ThresholdTropicalMatrix(x)));
  fi;
  Append(str, ")");

  return str;
end);

InstallMethod(\=, "for matrices over a semiring",
[IsPlistMatrixOverSemiringPositionalRep,
 IsPlistMatrixOverSemiringPositionalRep],
function(x, y)
  local n, i;
  if not SEMIGROUPS_FilterOfMatrixOverSemiring(x) =
      SEMIGROUPS_FilterOfMatrixOverSemiring(y) then
    return false;
  fi;

  n := Length(x![1]);
  if Length(y![1]) <> n then
    return false;
  fi;

  i := 1;
  while IsBound(x![i]) do
    if x![i] <> y![i] then
      return false;
    fi;
    i := i + 1;
  od;

  return true;
end);

InstallMethod(\<, "for matrices over a semiring",
[IsPlistMatrixOverSemiringPositionalRep,
 IsPlistMatrixOverSemiringPositionalRep],
function(x, y)
  local n, i;

  if SEMIGROUPS_FilterOfMatrixOverSemiring(x) <>
      SEMIGROUPS_FilterOfMatrixOverSemiring(y) then
    ErrorNoReturn("the matrices are not of the same type");
  fi;
  n := Length(x![1]);
  if n < Length(y![1]) then
    return true;
  elif n > Length(y![1]) then
    return false;
  fi;

  i := 1;
  while IsBound(x![i]) do
    if x![i] < y![i] then
      return true;
    elif x![i] > y![i] then
      return false;
    fi;
    i := i + 1;
  od;
  return false;
end);

InstallMethod(ChooseHashFunction, "for a matrix over semiring",
[IsMatrixOverSemiring, IsInt],
  function(_, hashlen)
  return rec(func := SEMIGROUPS.HashFunctionMatrixOverSemiring,
             data := hashlen);
end);
