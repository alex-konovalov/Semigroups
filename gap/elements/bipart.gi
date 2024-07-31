############################################################################
##
##  elements/bipart.gi
##  Copyright (C) 2013-2022                              James D. Mitchell
##
##  Licensing information can be found in the README file of this package.
##
#############################################################################
##

#############################################################################
# Family and type.
#
# One per degree to avoid lists with bipartitions of different degrees
# belonging to IsAssociativeElementCollection.
#############################################################################

BindGlobal("TYPES_BIPART", []);
BindGlobal("TYPE_BIPART",
function(n)
  local fam, type;

  n := n + 1;  # since the degree can be 0

  if IsBound(TYPES_BIPART[n]) then
    return TYPES_BIPART[n];
  fi;

  fam := NewFamily(Concatenation("BipartitionFamily", String(n - 1)),
                   IsBipartition,
                   CanEasilySortElements,
                   CanEasilySortElements);

  type := NewType(fam,
                  IsBipartition and IsInternalRep);
  TYPES_BIPART[n] := type;
  return type;
end);

#############################################################################
# Pickler
#############################################################################

InstallMethod(IO_Pickle, "for a bipartition",
[IsFile, IsBipartition],
function(file, x)
  if IO_Write(file, "BIPA") = fail then
    return IO_Error;
  fi;
  return IO_Pickle(file, IntRepOfBipartition(x));
end);

IO_Unpicklers.BIPA := function(file)
  local blocks;

  blocks := IO_Unpickle(file);
  if blocks = IO_Error then
    return IO_Error;
  fi;
  return BIPART_NC(blocks);
end;

#############################################################################
# Implications
#############################################################################

InstallTrueMethod(IsPermBipartition, IsTransBipartition
                                     and IsDualTransBipartition);

InstallTrueMethod(IsBlockBijection, IsPermBipartition);

#############################################################################
# GAP level - directly using interface to C/C++ level
#############################################################################

# Fundamental attributes

InstallMethod(DegreeOfBipartition, "for a bipartition",
[IsBipartition], BIPART_DEGREE);

InstallMethod(NrBlocks, "for a bipartition",
[IsBipartition], BIPART_NR_BLOCKS);

InstallMethod(NrLeftBlocks, "for a bipartition",
[IsBipartition], BIPART_NR_LEFT_BLOCKS);

InstallMethod(RankOfBipartition, "for a bipartition",
[IsBipartition], x -> BIPART_RANK(x, 0));

# Constructors

InstallGlobalFunction(Bipartition,
function(classes)
  local n, copy, i, j;

  if not IsList(classes)
      or ForAny(classes, x -> not IsHomogeneousList(x)
                              or not IsDuplicateFree(x)) then
    ErrorNoReturn("the argument does not consist of duplicate-free ",
                  "homogeneous lists");
  fi;

  n := Sum(classes, Length) / 2;

  if n >= 2 ^ 29 then
    ErrorNoReturn("the maximum degree of a bipartition is 2 ^ 29 - 1");
  elif not ForAll(classes, x -> ForAll(x,
                                       i -> (IsPosInt(i) or IsNegInt(i))
                                            and AbsInt(i) <= n)) then
    ErrorNoReturn("the argument does not consist of lists of ",
                  "integers from [-", n, " .. -1, 1 .. ", n, "]");
  elif not IsEmpty(classes)
      and Union(classes) <> Concatenation([-n .. -1], [1 .. n]) then
    ErrorNoReturn("the union of the argument <classes> is not ",
                  "[-", n, " .. -1, 1 .. ", n, "]");
  fi;

  copy := List(classes, ShallowCopy);
  for i in [1 .. Length(copy)] do
    for j in [1 .. Length(copy[i])] do
      if copy[i][j] < 0 then
        copy[i][j] := AbsInt(copy[i][j]) + n;
      fi;
    od;
  od;

  Perform(copy, Sort);
  Sort(copy);

  for i in [1 .. Length(copy)] do
    for j in [1 .. Length(copy[i])] do
      if copy[i][j] > n then
        copy[i][j] := -copy[i][j] + n;
      fi;
    od;
  od;
  return BIPART_NC(copy);
end);

InstallMethod(BipartitionByIntRep, "for a list", [IsHomogeneousList],
function(blocks)
  local n, next, seen, i;
  n := Length(blocks);
  if not IsEvenInt(n) then
    ErrorNoReturn("the degree of a bipartition must be even, found ", n);
  elif n >= 2 ^ 30 then
    ErrorNoReturn("the length of the argument (a list) exceeds ",
                  "2 ^ 30 - 1");
  elif not (IsEmpty(blocks) or IsPosInt(blocks[1])) then
    ErrorNoReturn("the items in the argument (a list) must be positive ",
                  "integers");
  fi;

   next := 0;
   seen := BlistList([1 .. Maximum(blocks)], []);

   for i in [1 .. n] do
     if not seen[blocks[i]] then
       next := next + 1;
       if blocks[i] <> next then
         ErrorNoReturn("expected ", next, " but found ", blocks[i],
                       ", in position ", i);
       fi;
       seen[blocks[i]] := true;
    fi;
  od;

  return BIPART_NC(blocks);
end);

InstallMethod(IdentityBipartition, "for zero", [IsZeroCyc],
_ -> Bipartition([]));

InstallMethod(IdentityBipartition, "for a positive integer", [IsPosInt],
function(n)
  local blocks, i;

  if n >= 2 ^ 29 then
    ErrorNoReturn("the argument (a pos. int) must not exceed 2 ^ 29 - 1");
  fi;
  blocks := EmptyPlist(2 * n);

  for i in [1 .. n] do
    blocks[i] := i;
    blocks[i + n] := i;
  od;

  return BIPART_NC(blocks);
end);

InstallMethod(RandomBipartition, "for a random source and pos int",
[IsRandomSource, IsPosInt],
function(rs, n)
  local out, nrblocks, vals, j, i;

  if n >= 2 ^ 29 then
    ErrorNoReturn("the argument (a pos. int.) must not exceed 2 ^ 29 - 1");
  fi;
  out := EmptyPlist(2 * n);
  nrblocks := 0;
  vals := [1];

  for i in [1 .. 2 * n] do
    j := Random(rs, vals);
    if j = nrblocks + 1 then
      nrblocks := nrblocks + 1;
      Add(vals, nrblocks + 1);
    fi;
    out[i] := j;
  od;

  return BIPART_NC(out);
end);

InstallMethod(RandomBipartition, "for a pos int", [IsPosInt],
n -> RandomBipartition(GlobalMersenneTwister, n));

InstallMethod(RandomBlockBijection, "for a random source and pos int",
[IsRandomSource, IsPosInt],
function(rs, n)
  local out, nrblocks, j, free, i;

  if n >= 2 ^ 29 then
    ErrorNoReturn("the argument (a pos. int.) must not exceed 2 ^ 29 - 1");
  fi;

  out := EmptyPlist(2 * n);
  out[1] := 1;
  nrblocks := 1;

  for i in [2 .. n] do
    j := Random(rs, [1 .. nrblocks + 1]);
    if j = nrblocks + 1 then
      nrblocks := nrblocks + 1;
    fi;
    out[i] := j;
  od;

  free := [n + 1 .. 2 * n];
  for i in [1 .. nrblocks] do
    j := Random(rs, free);
    out[j] := i;
    RemoveSet(free, j);
  od;

  for i in free do
    out[i] := Random(rs, [1 .. nrblocks]);
  od;

  return BIPART_NC(out);
end);

InstallMethod(RandomBlockBijection, "for a pos int", [IsPosInt],
n -> RandomBlockBijection(GlobalMersenneTwister, n));

# Operators

InstallMethod(PermLeftQuoBipartition, "for a bipartition and bipartition",
IsIdenticalObj, [IsBipartition, IsBipartition],
function(x, y)

  if LeftBlocks(x) <> LeftBlocks(y) or RightBlocks(x) <> RightBlocks(y) then
    ErrorNoReturn("the arguments (bipartitions) do not have equal left ",
                  "and right blocks");
  fi;
  return BIPART_PERM_LEFT_QUO(x, y);
end);

# Attributes

InstallMethod(DomainOfBipartition, "for a bipartition", [IsBipartition],
function(x)
  local out;
  out := [];
  for x in ExtRepOfObj(LeftBlocks(x)) do
    if IsPosInt(x[1]) then
      Append(out, x);
    fi;
  od;
  return out;
end);

InstallMethod(CodomainOfBipartition, "for a bipartition", [IsBipartition],
function(x)
  local out;
  out := [];
  for x in ExtRepOfObj(RightBlocks(x)) do
    if IsPosInt(x[1]) then
      Append(out, -x);
    fi;
  od;
  return out;
end);

InstallMethod(ExtRepOfObj, "for a bipartition", [IsBipartition],
BIPART_EXT_REP);

InstallMethod(IntRepOfBipartition, "for a bipartition", [IsBipartition],
BIPART_INT_REP);

# xx ^ * - linear - 2 * degree

InstallMethod(LeftProjection, "for a bipartition", [IsBipartition],
BIPART_LEFT_PROJ);

InstallMethod(RightProjection, "for a bipartition", [IsBipartition],
BIPART_RIGHT_PROJ);

# linear - 2 * degree

InstallMethod(StarOp, "for a bipartition", [IsBipartition], BIPART_STAR);

InstallMethod(ChooseHashFunction, "for a bipartition",
[IsBipartition, IsInt],
{_, hashlen} -> rec(func := BIPART_HASH, data := hashlen));

#############################################################################
# GAP level
#############################################################################

# Attributes

# not a synonym since NrTransverseBlocks also applies to blocks

InstallMethod(NrTransverseBlocks, "for a bipartition", [IsBipartition],
RankOfBipartition);

InstallMethod(NrRightBlocks, "for a bipartition", [IsBipartition],
x -> NrBlocks(x) - NrLeftBlocks(x) + NrTransverseBlocks(x));

InstallMethod(OneMutable, "for a bipartition",
[IsBipartition], x -> IdentityBipartition(DegreeOfBipartition(x)));

InstallMethod(OneMutable, "for a bipartition collection",
[IsBipartitionCollection], x ->
IdentityBipartition(DegreeOfBipartitionCollection(x)));

# the Other is to avoid warning on opening GAP

InstallOtherMethod(InverseMutable, "for a bipartition", [IsBipartition],
function(x)
  if IsBlockBijection(x) or IsPartialPermBipartition(x) then
    return Star(x);
  fi;
  return fail;
end);

# Properties

InstallMethod(IsBlockBijection, "for a bipartition",
[IsBipartition],
x -> NrBlocks(x) = NrLeftBlocks(x) and NrRightBlocks(x) = NrLeftBlocks(x));

InstallMethod(IsPartialPermBipartition, "for a bipartition",
[IsBipartition],
function(x)
  return NrLeftBlocks(x) = DegreeOfBipartition(x)
    and NrRightBlocks(x) = DegreeOfBipartition(x);
end);

# a bipartition is a transformation if and only if the second row is a
# permutation of [1 .. n], where n is the degree.

InstallMethod(IsTransBipartition, "for a bipartition",
[IsBipartition],
function(x)
  return NrLeftBlocks(x) = NrTransverseBlocks(x)
   and NrRightBlocks(x) = DegreeOfBipartition(x);
end);

InstallMethod(IsDualTransBipartition, "for a bipartition", [IsBipartition],
function(x)
  return NrRightBlocks(x) = NrTransverseBlocks(x)
   and NrLeftBlocks(x) = DegreeOfBipartition(x);
end);

InstallMethod(IsPermBipartition, "for a bipartition",
[IsBipartition],
function(x)
  return IsPartialPermBipartition(x)
    and NrTransverseBlocks(x) = DegreeOfBipartition(x);
end);

# Fundamental operators

InstallMethod(\*, "for a bipartition and a perm",
[IsBipartition, IsPerm],
function(x, p)
  if LargestMovedPoint(p) <= DegreeOfBipartition(x) then
    return x * AsBipartition(p, DegreeOfBipartition(x));
  fi;
  ErrorNoReturn("the largest moved point of the 2nd argument ",
                "(a permutation) exceeds",
                " the degree of the 1st argument (a bipartition)");
end);

InstallMethod(\*, "for a perm and a bipartition",
[IsPerm, IsBipartition],
function(p, x)
  if LargestMovedPoint(p) <= DegreeOfBipartition(x) then
    return AsBipartition(p, DegreeOfBipartition(x)) * x;
  fi;
  ErrorNoReturn("the largest moved point of the 1st argument ",
                "(a permutation) exceeds",
                " the degree of the 2nd argument (a bipartition)");
end);

InstallMethod(\*, "for a bipartition and a transformation",
[IsBipartition, IsTransformation],
function(x, f)
  if DegreeOfTransformation(f) <= DegreeOfBipartition(x) then
    return x * AsBipartition(f, DegreeOfBipartition(x));
  fi;
  ErrorNoReturn("the degree of the 2nd argument (a transformation)",
                " exceeds the degree of the 1st argument",
                " (a bipartition)");
end);

InstallMethod(\*, "for a transformation and a bipartition",
[IsTransformation, IsBipartition],
function(f, g)
  if DegreeOfTransformation(f) <= DegreeOfBipartition(g) then
    return AsBipartition(f, DegreeOfBipartition(g)) * g;
  fi;
  ErrorNoReturn("the degree of the 1st argument (a transformation)",
                " exceeds the degree of the 2nd argument",
                " (a bipartition)");
end);

InstallMethod(\*, "for a bipartition and a partial perm",
[IsBipartition, IsPartialPerm],
function(f, g)
  local n;
  n := DegreeOfBipartition(f);
  if ForAll([1 .. n], i -> i ^ g <= n) then
    return f * AsBipartition(g, DegreeOfBipartition(f));
  fi;
  ErrorNoReturn("the 2nd argument (a partial perm) does not map ",
                "[1 .. ", String(n), "] into [1 .. ", String(n), "]");
end);

InstallMethod(\*, "for a partial perm and a bipartition",
[IsPartialPerm, IsBipartition],
function(f, g)
  local n;
  n := DegreeOfBipartition(g);
  if ForAll([1 .. n], i -> i ^ f <= n) then
    return AsBipartition(f, DegreeOfBipartition(g)) * g;
  fi;
  ErrorNoReturn("the 1st argument (a partial perm) does not map [1 .. ",
                String(n), "] into [1 .. ", String(n), "]");
end);

InstallMethod(\^, "for a bipartition and permutation",
[IsBipartition, IsPerm], {f, p} -> p ^ -1 * f * p);

# Other operators

InstallMethod(PartialPermLeqBipartition, "for a bipartition and a bipartition",
IsIdenticalObj, [IsBipartition, IsBipartition],
function(x, y)
  if not (IsPartialPermBipartition(x) and IsPartialPermBipartition(y)) then
    ErrorNoReturn("the arguments (bipartitions) do not both satisfy ",
                  "IsPartialPermBipartition");
  fi;

  return AsPartialPerm(x) < AsPartialPerm(y);
end);

# Changing representations

InstallMethod(AsBipartition, "for a permutation and zero",
[IsPerm, IsZeroCyc],
{f, n} -> Bipartition([]));

InstallMethod(AsBipartition, "for a permutation",
[IsPerm], x -> AsBipartition(x, LargestMovedPoint(x)));

InstallMethod(AsBipartition, "for a partial perm",
[IsPartialPerm],
function(x)
  return AsBipartition(x, Maximum(DegreeOfPartialPerm(x),
                                  CodegreeOfPartialPerm(x)));
end);

InstallMethod(AsBipartition, "for a partial perm and zero",
[IsPartialPerm, IsZeroCyc], {f, n} -> Bipartition([]));

InstallMethod(AsBipartition, "for a transformation",
[IsTransformation], x -> AsBipartition(x, DegreeOfTransformation(x)));

InstallMethod(AsBipartition, "for a transformation and zero",
[IsTransformation, IsZeroCyc], {f, n} -> Bipartition([]));

InstallMethod(AsBipartition, "for a bipartition", [IsBipartition], IdFunc);

InstallMethod(AsBipartition, "for a bipartition", [IsBipartition, IsZeroCyc],
{f, n} -> Bipartition([]));

InstallMethod(AsBipartition, "for a pbr and zero", [IsPBR, IsZeroCyc],
{f, n} -> Bipartition([]));

InstallMethod(AsBipartition, "for a pbr and pos int",
[IsPBR, IsPosInt],
function(x, deg)
  if not IsBipartitionPBR(x) then
    ErrorNoReturn("the 1st argument (a pbr) does not satisfy",
                  " 'IsBipartitionPBR'");
  fi;

  return AsBipartition(AsBipartition(x), deg);
end);

InstallMethod(AsBipartition, "for a pbr",
[IsPBR],
function(x)
  if not IsBipartitionPBR(x) then
    ErrorNoReturn("the argument (a pbr) does not satisfy 'IsBipartitionPBR'");
  fi;
  return Bipartition(Union(ExtRepOfObj(x)));
end);

InstallMethod(AsBlockBijection, "for a partial perm",
[IsPartialPerm],
function(x)
  return AsBlockBijection(x, Maximum(DegreeOfPartialPerm(x),
                                     CodegreeOfPartialPerm(x)) + 1);
end);

# Viewing, printing etc

InstallMethod(ViewString, "for a bipartition",
[IsBipartition],
function(x)
  local str, ext, i;

  if DegreeOfBipartition(x) = 0 then
    return "\><empty bipartition>\<";
  elif IsBlockBijection(x) then
    str := "\>\><block bijection:\< ";
  else
    str := "\>\><bipartition:\< ";
  fi;

  ext := ExtRepOfObj(x);
  Append(str, "\>");
  Append(str, String(ext[1]));
  Append(str, "\<");

  for i in [2 .. Length(ext)] do
    Append(str, ", \>");
    Append(str, String(ext[i]));
    Append(str, "\<");
  od;
  Append(str, ">\<");
  return str;
end);

InstallMethod(String, "for a bipartition", [IsBipartition],
x -> Concatenation("Bipartition(", String(ExtRepOfObj(x)), ")"));

InstallMethod(PrintString, "for a bipartition",
[IsBipartition],
function(x)
  local ext, str, i;
  if DegreeOfBipartition(x) = 0 then
    return "\>\>Bipartition(\< \>[]\<)\<";
  fi;
  ext := ExtRepOfObj(x);
  str := Concatenation("\>\>Bipartition(\< \>[ ", PrintString(ext[1]));
  for i in [2 .. Length(ext)] do
    Append(str, ",\< \>");
    Append(str, PrintString(ext[i]));
  od;
  Append(str, " \<]");
  Append(str, " )\<");
  return str;
end);

InstallMethod(PrintString, "for a bipartition collection",
[IsBipartitionCollection],
function(coll)
  local str, i;

  if IsGreensClass(coll) or IsSemigroup(coll) then
    TryNextMethod();
  fi;

  str := "\>[ ";
  for i in [1 .. Length(coll)] do
    if not i = 1 then
      Append(str, " ");
    fi;
    Append(str, "\>");
    Append(str, PrintString(coll[i]));
    if not i = Length(coll) then
      Append(str, ",\<\n");
    else
      Append(str, " ]\<\n");
    fi;
  od;
  return str;
end);

# Bipartition collections

InstallMethod(DegreeOfBipartitionCollection, "for a bipartition semigroup",
[IsBipartitionSemigroup], DegreeOfBipartitionSemigroup);

InstallMethod(DegreeOfBipartitionCollection, "for a bipartition collection",
[IsBipartitionCollection], coll -> DegreeOfBipartition(coll[1]));

#############################################################################
# All of the methods in this section could be done in C/C++
#############################################################################

# Change representations . . .

InstallMethod(AsBipartition, "for a permutation and pos int",
[IsPerm, IsPosInt],
function(x, n)
  if n >= 2 ^ 29 then
    ErrorNoReturn("the 2nd argument (a pos. int.) exceeds 2 ^ 29 - 1");
  elif OnSets([1 .. n], x) <> [1 .. n] then
    ErrorNoReturn("the 1st argument (a permutation) does not permute ",
                  "[1 .. ", String(n), "]");
  fi;
  return BIPART_NC(Concatenation([1 .. n], ListPerm(x ^ -1, n)));
end);

InstallMethod(AsPartialPerm, "for a bipartition", [IsBipartition],
function(x)
  local n, blocks, nrleft, im, out, i;

  if not IsPartialPermBipartition(x) then
    ErrorNoReturn("the argument (a bipartition) does not define ",
                  "a partial perm");
  fi;

  n      := DegreeOfBipartition(x);
  blocks := IntRepOfBipartition(x);
  nrleft := NrLeftBlocks(x);
  im     := [1 .. n] * 0;

  for i in [n + 1 .. 2 * n] do
    if blocks[i] <= nrleft then
      im[blocks[i]] := i - n;
    fi;
  od;

  out := EmptyPlist(n);
  for i in [1 .. n] do
    out[i] := im[blocks[i]];
  od;
  return PartialPermNC(out);
end);

InstallMethod(AsPermutation, "for a bipartition", [IsBipartition],
function(x)
  local n, blocks, im, out, i;

  if not IsPermBipartition(x) then
    ErrorNoReturn("the argument (a bipartition) does not define a ",
                  "permutation");
  fi;

  n      := DegreeOfBipartition(x);
  blocks := IntRepOfBipartition(x);
  im     := EmptyPlist(n);

  for i in [n + 1 .. 2 * n] do
    im[blocks[i]] := i - n;
  od;

  out := EmptyPlist(n);
  for i in [1 .. n] do
    out[i] := im[blocks[i]];
  od;
  return PermList(out);
end);

InstallMethod(AsTransformation, "for a bipartition", [IsBipartition],
function(x)
  local n, blocks, nr, im, out, i;

  if not IsTransBipartition(x) then
    ErrorNoReturn("the argument (a bipartition) does not define a ",
                  "transformation");
  fi;

  n      := DegreeOfBipartition(x);
  blocks := IntRepOfBipartition(x);
  nr     := NrLeftBlocks(x);
  im     := EmptyPlist(n);

  for i in [n + 1 .. 2 * n] do
    if blocks[i] <= nr then
      im[blocks[i]] := i - n;
    fi;
  od;

  out := EmptyPlist(n);
  for i in [1 .. n] do
    out[i] := im[blocks[i]];
  od;
  return TransformationNC(out);
end);

InstallMethod(AsBipartition, "for a partial perm and pos int",
[IsPartialPerm, IsPosInt],
function(x, n)
  local r, out, y, j, i;

  if n >= 2 ^ 29 then
    ErrorNoReturn("the 2nd argument (a pos. int.) exceeds 2 ^ 29 - 1");
  fi;

  r   := n;
  out := EmptyPlist(2 * n);
  y   := x ^ -1;

  for i in [1 .. n] do
    out[i] := i;
    j      := i ^ y;
    if j <> 0 then
      out[n + i] := j;
    else
      r          := r + 1;
      out[n + i] := r;
    fi;
  od;
  return BIPART_NC(out);
end);

InstallMethod(AsBipartition, "for a transformation and a positive integer",
[IsTransformation, IsPosInt],
function(f, n)
  local r, ker, out, g, i;

  if n >= 2 ^ 29 then
    ErrorNoReturn("the 2nd argument (a pos. int.) exceeds 2 ^ 29 - 1");
  elif n < DegreeOfTransformation(f) then
    # Verify f is a transformation on [1 .. n].
    for i in [1 .. n] do
      if i ^ f > n then
        ErrorNoReturn("the 1st argument (a transformation) does not map [1 .. ",
                      String(n), "] to itself");
      fi;
    od;
  fi;

  r := RankOfTransformation(f, n);
  ker := FlatKernelOfTransformation(f, n);

  out := EmptyPlist(2 * n);
  g := List([1 .. n], x -> 0);

  # The inverse of f.
  for i in [1 .. n] do
    g[i ^ f] := i;
  od;

  for i in [1 .. n] do
    out[i] := ker[i];
    if g[i] <> 0 then
      out[n + i] := ker[g[i]];
    else
      r := r + 1;
      out[n + i] := r;
    fi;
  od;
  return BIPART_NC(out);
end);

InstallMethod(AsBipartition, "for a bipartition and pos int",
[IsBipartition, IsPosInt],
function(f, n)
  local deg, blocks, out, nrblocks, nrleft, lookup, j, i;

  if n >= 2 ^ 29 then
    ErrorNoReturn("the 2nd argument (a pos. int.) exceeds 2 ^ 29 - 1");
  fi;
  deg := DegreeOfBipartition(f);
  if n = deg then
    return f;
  fi;
  blocks := IntRepOfBipartition(f);
  out := [];
  nrblocks := 0;

  if n < deg then
    for i in [1 .. n] do
      out[i] := blocks[i];
      if out[i] > nrblocks then
        nrblocks := nrblocks + 1;
      fi;
    od;
    nrleft := nrblocks;
    lookup := EmptyPlist(NrBlocks(f));
    for i in [n + 1 .. 2 * n] do
      j := blocks[i + deg - n];
      if j > nrleft then
        if not IsBound(lookup[j]) then
          nrblocks := nrblocks + 1;
          lookup[j] := nrblocks;
        fi;
        j := lookup[j];
      fi;
      out[i] := j;
    od;
  else  # n > deg
    for i in [1 .. deg] do
      out[i] := blocks[i];
    od;
    nrblocks := NrLeftBlocks(f);
    for i in [deg + 1 .. n] do
      nrblocks := nrblocks + 1;
      out[i] := nrblocks;
    od;
    nrleft := nrblocks;  # = n - deg + NrLeftBlocks(f)
    for i in [n + 1 .. n + deg] do
      if blocks[i - n + deg] <= nrleft - n + deg then  # it's a left block
        out[i] := blocks[i - n + deg];
      else
        out[i] := blocks[i - n + deg] + n - deg;
      fi;
    od;
    nrblocks := NrBlocks(f) + n - deg;
    for i in [n + deg + 1 .. 2 * n] do
      nrblocks := nrblocks + 1;
      out[i] := nrblocks;
    od;
  fi;
  return BIPART_NC(out);
end);

# same as AsBipartition except that all undefined points are in a single block
# together with an extra (pair of) points.

InstallMethod(AsBlockBijection, "for a partial perm and pos int",
[IsPartialPerm, IsPosInt],
function(f, n)
  local bigblock, nr, out, i;

  if n >= 2 ^ 29 then
    ErrorNoReturn("the 2nd argument (a pos. int.) exceeds 2 ^ 29 - 1");
  elif n <= Maximum(DegreeOfPartialPerm(f), CodegreeOfPartialPerm(f)) then
    ErrorNoReturn("the 2nd argument (a pos. int.) is less than or equal to ",
                  "the maximum of the degree and codegree of the ",
                  "1st argument (a partial perm)");
  fi;

  nr := 0;
  out := [1 .. 2 * n] * 0;
  bigblock := n;

  for i in [1 .. n - 1] do
    if i ^ f = 0 then
      if bigblock = n then
        nr := nr + 1;
        bigblock := nr;
      fi;
      out[i] := bigblock;
    else
      nr := nr + 1;
      out[i] := nr;
      out[n + i ^ f] := nr;
    fi;
  od;

  out[n] := bigblock;
  out[2 * n] := bigblock;

  for i in [n + 1 .. 2 * n - 1] do
    if out[i] = 0 then
      out[i] := bigblock;
    fi;
  od;

  return BIPART_NC(out);
end);

InstallMethod(AsBlockBijection, "for a bipartition and pos int",
[IsBipartition, IsPosInt],
function(x, n)
  if not IsPartialPermBipartition(x) then
    ErrorNoReturn("the 1st argument (a bipartition) is not a ",
                  "partial perm bipartition");
  fi;
  return AsBlockBijection(AsPartialPerm(x), n);
end);

InstallMethod(AsBlockBijection, "for a bipartition",
[IsBipartition],
function(x)
  if not IsPartialPermBipartition(x) then
    ErrorNoReturn("the argument (a bipartion) does not satisfy ",
                  "IsPartialPermBipartition");
  fi;
  return AsBlockBijection(AsPartialPerm(x));
end);

InstallMethod(NaturalLeqBlockBijection, "for a bipartition and bipartition",
IsIdenticalObj, [IsBipartition, IsBipartition],
function(x, y)
  local xblocks, yblocks, n, lookup, i;

  if not IsBlockBijection(x) or not IsBlockBijection(y) then
    ErrorNoReturn("the arguments (bipartitions) are not block bijections");
  elif NrBlocks(x) > NrBlocks(y) then
    return false;
  fi;

  xblocks := IntRepOfBipartition(x);
  yblocks := IntRepOfBipartition(y);
  n       := DegreeOfBipartition(x);

  lookup := [];
  for i in [1 .. n] do
    if IsBound(lookup[yblocks[i]]) and lookup[yblocks[i]] <> xblocks[i] then
      return false;
    else
      lookup[yblocks[i]] := xblocks[i];
    fi;
  od;
  for i in [n + 1 .. 2 * n] do
    if lookup[yblocks[i]] <> xblocks[i] then
      return false;
    fi;
  od;
  return true;
end);

InstallMethod(NaturalLeqPartialPermBipartition,
"for a bipartition and bipartition",
IsIdenticalObj, [IsBipartition, IsBipartition],
function(x, y)
  local n, xblocks, yblocks, val, i;

  if not IsPartialPermBipartition(x) or not IsPartialPermBipartition(y) then
    ErrorNoReturn("the arguments (bipartitions) are not partial perm ",
                  "bipartitions");
  fi;

  n := DegreeOfBipartition(x);

  xblocks := IntRepOfBipartition(x);
  yblocks := IntRepOfBipartition(y);

  for i in [n + 1 .. 2 * n] do
    val := xblocks[i];
    if val <= n and val <> yblocks[i] then
      return false;
    fi;
  od;
  return true;
end);

InstallMethod(IsUniformBlockBijection, "for a bipartition",
[IsBipartition],
function(x)
  local blocks, n, sizesleft, sizesright, i;

  if not IsBlockBijection(x) then
    return false;
  fi;

  blocks := IntRepOfBipartition(x);
  n := DegreeOfBipartition(x);
  sizesleft := [1 .. NrBlocks(x)] * 0;
  sizesright := [1 .. NrBlocks(x)] * 0;

  for i in [1 .. n] do
    sizesleft[blocks[i]] := sizesleft[blocks[i]] + 1;
  od;
  for i in [n + 1 .. 2 * n] do
    sizesright[blocks[i]] := sizesright[blocks[i]] + 1;
  od;
  for i in [1 .. NrBlocks(x)] do
    if sizesright[i] <> sizesleft[i] then
      return false;
    fi;
  od;

  return true;
end);

InstallMethod(IndexPeriodOfSemigroupElement, "for a bipartition",
[IsBipartition], x -> SEMIGROUPS.IndexPeriodByRank(x, RankOfBipartition));
