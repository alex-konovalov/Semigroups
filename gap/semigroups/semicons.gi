############################################################################
##
##  semigroups/semicons.gi
##  Copyright (C) 2015-2022                              James D. Mitchell
##                                                          Wilf A. Wilson
##
##  Licensing information can be found in the README file of this package.
##
############################################################################
##

# Trivial semigroup: main method

InstallGlobalFunction(TrivialSemigroup,
function(arg)
  local S;

  if Length(arg) = 0 then
    S := TrivialSemigroupCons(IsTransformationSemigroup, 0);
  elif Length(arg) = 1 and IsInt(arg[1]) and arg[1] >= 0 then
    S := TrivialSemigroupCons(IsTransformationSemigroup, arg[1]);
  elif Length(arg) = 1 and IsOperation(arg[1]) then
    S := TrivialSemigroupCons(arg[1], 0);
  elif Length(arg) = 2 and IsOperation(arg[1]) and IsInt(arg[2])
      and arg[2] >= 0 then
    S := TrivialSemigroupCons(arg[1], arg[2]);
  else
    ErrorNoReturn("the arguments must be a non-negative integer or ",
                  "a filter and a non-negative integer");
  fi;
  SetIsTrivial(S, true);
  return S;
end);

# Trivial semigroup: constructors

InstallMethod(TrivialSemigroupCons,
"for IsTransformationSemigroup and an integer",
[IsTransformationSemigroup, IsInt],
function(_, deg)
  if deg = 0 then
    return Semigroup(IdentityTransformation);
  fi;
  return Semigroup(ConstantTransformation(deg, 1));
end);

InstallMethod(TrivialSemigroupCons,
"for IsPartialPermSemigroup and an integer",
[IsPartialPermSemigroup, IsInt],
{_, n} -> Semigroup(PartialPerm([1 .. n])));

InstallMethod(TrivialSemigroupCons,
"for IsBipartitionSemigroup and an integer",
[IsBipartitionSemigroup, IsInt],
function(_, deg)
  local n;
  n := Maximum(deg, 1);
  return Semigroup(Bipartition([Concatenation(List([1 .. n], x -> [-x, x]))]));
end);

InstallMethod(TrivialSemigroupCons,
"for IsBlockBijectionSemigroup and an integer",
[IsBlockBijectionSemigroup, IsInt],
{_, deg} -> TrivialSemigroupCons(IsBipartitionSemigroup, Maximum(deg, 1)));

InstallMethod(TrivialSemigroupCons,
"for IsPBRSemigroup and an integer",
[IsPBRSemigroup, IsInt],
{_, deg} -> Semigroup(IdentityPBR(Maximum(deg, 1))));

InstallMethod(TrivialSemigroupCons,
"for IsBooleanMatSemigroup and an integer",
[IsBooleanMatSemigroup, IsInt],
function(_, deg)
  local n;
  n := Maximum(deg, 1);
  return Semigroup(BooleanMat(List([1 .. n], x -> BlistList([1 .. n], [x]))));
end);

# Trivial semigroup: other constructors

for _IsXSemigroup in ["IsFpSemigroup",
                      "IsFpMonoid",
                      "IsNTPMatrixSemigroup",
                      "IsMaxPlusMatrixSemigroup",
                      "IsMinPlusMatrixSemigroup",
                      "IsTropicalMaxPlusMatrixSemigroup",
                      "IsTropicalMinPlusMatrixSemigroup",
                      "IsProjectiveMaxPlusMatrixSemigroup",
                      "IsIntegerMatrixSemigroup",
                      "IsReesMatrixSemigroup",
                      "IsReesZeroMatrixSemigroup"] do
  InstallMethod(TrivialSemigroupCons,
  Concatenation("for ", _IsXSemigroup, " and an integer"),
  [ValueGlobal(_IsXSemigroup), IsInt],
  function(filter, deg)
    return AsSemigroup(filter,
                       TrivialSemigroupCons(IsTransformationSemigroup, deg));
  end);
od;

Unbind(_IsXSemigroup);

# Monogenic semigroup: main method

InstallGlobalFunction(MonogenicSemigroup,
function(arg)
  local filter, m, r, S;

  if Length(arg) = 2  then
    filter := IsTransformationSemigroup;
    m := arg[1];
    r := arg[2];
  elif Length(arg) = 3 then
    filter := arg[1];
    m := arg[2];
    r := arg[3];
  fi;

  if not IsBound(m) or not IsPosInt(m) or not IsPosInt(r)
      or not IsOperation(filter) then
    ErrorNoReturn("the arguments must be 2 positive integers or a filter ",
                  "and a 2 positive integers");
  fi;

  S := MonogenicSemigroupCons(filter, m, r);

  SetSize(S, m + r - 1);
  SetIsMonogenicSemigroup(S, true);
  if m = 1 then
    SetIsGroupAsSemigroup(S, true);
  else
    SetIsGroupAsSemigroup(S, false);
    SetIsRegularSemigroup(S, false);
  fi;

  SetIsZeroSemigroup(S, r = 1 and m < 3);
  SetMinimalSemigroupGeneratingSet(S, GeneratorsOfSemigroup(S));

  return S;
end);

# Monogenic semigroup: constructors

InstallMethod(MonogenicSemigroupCons,
"for a IsTransformationSemigroup and two positive integers",
[IsTransformationSemigroup, IsPosInt, IsPosInt],
function(_, m, r)
  local t;

  t := [1 .. r] + 1;
  t[r] := 1;

  if not m = 1 then  # m = 1 specifies a cyclic group
    Append(t, [1 .. m] + r - 1);
  fi;

  return Semigroup(Transformation(t));
end);

InstallMethod(MonogenicSemigroupCons,
"for a IsPartialPermSemigroup and two positive integers",
[IsPartialPermSemigroup, IsPosInt, IsPosInt],
function(_, m, r)
  local cyclic_group, nilpotent_offset, nilpotent, im;

  if m = 1 and r = 1 then
    return Semigroup(PartialPerm([], []));
  elif r = 1 then
    cyclic_group := [];
    nilpotent_offset := 0;
  else
    cyclic_group := [1 .. r] + 1;
    cyclic_group[r] := 1;
    nilpotent_offset := r;
  fi;
  nilpotent := [1 .. m - 1] + nilpotent_offset;
  im := Concatenation(cyclic_group, [0], nilpotent);

  return Semigroup(PartialPerm(im));
end);

InstallMethod(MonogenicSemigroupCons,
"for a IsBipartitionSemigroup and two positive integers",
[IsBipartitionSemigroup, IsPosInt, IsPosInt],
{_, m, r} -> MonogenicSemigroupCons(IsBlockBijectionSemigroup, m, r));

InstallMethod(MonogenicSemigroupCons,
"for IsBlockBijectionSemigroup and two positive integers",
[IsBlockBijectionSemigroup, IsPosInt, IsPosInt],
function(_, m, r)
  local out, offset, i;

  if m = 1 and r = 1 then
    return Semigroup(Bipartition([[1, -1]]));
  fi;

  out := [];
  if r = 1 then
    offset := 1;
  else
    for i in [1 .. r - 1] do
      Add(out, [i, -i - 1]);
    od;
    Add(out, [r, -1]);
    offset := r + 1;
  fi;

  if not m = 1 then
    Add(out, [offset, -offset, offset + 1, -(offset + m)]);
    for i in [offset + 2 .. offset + m] do
      Add(out, [i, -i + 1]);
    od;
  fi;

  return Semigroup(Bipartition(out));
end);

# Monogenic semigroup: other constructors

for _IsXSemigroup in ["IsPBRSemigroup",
                      "IsBooleanMatSemigroup",
                      "IsNTPMatrixSemigroup",
                      "IsMaxPlusMatrixSemigroup",
                      "IsMinPlusMatrixSemigroup",
                      "IsTropicalMaxPlusMatrixSemigroup",
                      "IsTropicalMinPlusMatrixSemigroup",
                      "IsProjectiveMaxPlusMatrixSemigroup",
                      "IsIntegerMatrixSemigroup",
                      "IsReesMatrixSemigroup",
                      "IsReesZeroMatrixSemigroup"] do
  InstallMethod(MonogenicSemigroupCons,
  Concatenation("for ", _IsXSemigroup, " and two positive integers"),
  [ValueGlobal(_IsXSemigroup), IsPosInt, IsPosInt],
  function(filter, m, r)
    return AsSemigroup(filter,
                       MonogenicSemigroupCons(IsTransformationSemigroup, m, r));
  end);
od;
Unbind(_IsXSemigroup);

# Rectangular band: main method

InstallGlobalFunction(RectangularBand,
function(arg)
  local filter, m, n, S;

  if Length(arg) = 2  then
    filter := IsTransformationSemigroup;
    m := arg[1];
    n := arg[2];
  elif Length(arg) = 3 then
    filter := arg[1];
    m := arg[2];
    n := arg[3];
  fi;

  if not IsBound(m) or not IsPosInt(m) or not IsPosInt(n)
      or not IsOperation(filter) then
    ErrorNoReturn("the arguments must be 2 positive integers or a filter ",
                  "and a 2 positive integers");
  fi;

  S := RectangularBandCons(filter, m, n);

  SetSize(S, m * n);
  SetIsRectangularBand(S, true);
  SetNrRClasses(S, m);
  SetNrLClasses(S, n);
  if m <> 1 or n <> 1 then
    SetIsGroupAsSemigroup(S, false);
    SetIsZeroSemigroup(S, false);
    SetIsTrivial(S, false);
  fi;
  SetIsRightZeroSemigroup(S, m = 1);
  SetIsLeftZeroSemigroup(S, n = 1);

  return S;
end);

# Rectangular band: constructors

InstallMethod(RectangularBandCons,
"for a filter and a positive integer and positive integer",
[IsTransformationSemigroup, IsPosInt, IsPosInt],
function(filter, m, n)
  local L, R, div, gen, gens, min, out, i;

  if m = 1 then
    return RightZeroSemigroup(filter, n);
  elif n = 1 then
    return LeftZeroSemigroup(filter, m);
  fi;

  # don't do:
  # DirectProduct(LeftZeroSemigroup(m), RightZeroSemigroup(n));
  # because we know a generating set.

  L := LeftZeroSemigroup(filter, m);
  R := RightZeroSemigroup(filter, n);
  div := DegreeOfTransformationSemigroup(L);

  gen := function(l, r)
    return Transformation(Concatenation(ListTransformation(L.(l), div),
                                        ListTransformation(R.(r)) + div));
  end;

  gens := [];
  min := Minimum(m, n);

  for i in [1 .. min] do  # 'diagonal' generators
    Add(gens, gen(i, i));
  od;

  for i in [min + 1 .. n] do  # additional generators when n > m
    Add(gens, gen(1, i));
  od;

  for i in [min + 1 .. m] do  # additional generators when n < m
    Add(gens, gen(i, 1));
  od;

  out := Semigroup(gens);
  SetMinimalSemigroupGeneratingSet(out, GeneratorsOfSemigroup(out));
  return out;
end);

InstallMethod(RectangularBandCons,
"for a filter and two positive integers",
[IsBipartitionSemigroup, IsPosInt, IsPosInt],
function(_, m, n)
  local max, min, out, nrpoints, partitions, neg, i;

  max := Maximum(m, n);
  min := Minimum(m, n);
  out := EmptyPlist(max);

  # Find a small degree of partition monoid in which to embed rectangular band
  nrpoints := 1;
  while NrPartitionsSet([1 .. nrpoints]) < max do
    nrpoints := nrpoints + 1;
  od;

  partitions := PartitionsSet([1 .. nrpoints]);

  for i in [1 .. min] do
    Add(out, Bipartition(Concatenation(partitions[i], -1 * partitions[i])));
  od;

  neg := -1 * partitions[1];
  for i in [min + 1 .. m] do
    Add(out, Bipartition(Concatenation(partitions[i], neg)));
  od;

  for i in [min + 1 .. n] do
    Add(out, Bipartition(Concatenation(partitions[1], -1 * partitions[i])));
  od;

  return Semigroup(out);
end);

InstallMethod(RectangularBandCons,
"for a filter and a positive integer and positive integer",
[IsReesMatrixSemigroup, IsPosInt, IsPosInt],
function(_, m, n)
  local id, mat;

  id := ();
  mat := List([1 .. n], x -> List([1 .. m], y -> id));
  return ReesMatrixSemigroup(Group(id), mat);
end);

InstallMethod(RectangularBandCons,
"for IsPBRSemigroup and a pos int, and pos int",
[IsPBRSemigroup, IsPosInt, IsPosInt],
function(filter, m, n)
  return AsSemigroup(filter,
                     RectangularBandCons(IsBipartitionSemigroup, m, n));
end);

# Rectangular band: other constructors

for _IsXSemigroup in ["IsBooleanMatSemigroup",
                      "IsNTPMatrixSemigroup",
                      "IsMaxPlusMatrixSemigroup",
                      "IsMinPlusMatrixSemigroup",
                      "IsTropicalMaxPlusMatrixSemigroup",
                      "IsTropicalMinPlusMatrixSemigroup",
                      "IsProjectiveMaxPlusMatrixSemigroup",
                      "IsIntegerMatrixSemigroup"] do
  InstallMethod(RectangularBandCons,
  Concatenation("for ", _IsXSemigroup, ", pos int, and pos int"),
  [ValueGlobal(_IsXSemigroup), IsPosInt, IsPosInt],
  function(filter, m, n)
    return AsSemigroup(filter,
                       RectangularBandCons(IsTransformationSemigroup, m, n));
  end);
od;
Unbind(_IsXSemigroup);

# Free semilattice: main method

InstallGlobalFunction(FreeSemilattice,
function(arg...)
  local filter, n, S;

  if Length(arg) = 1  then
    filter := IsTransformationSemigroup;
    n := arg[1];
  elif Length(arg) = 2 then
    filter := arg[1];
    n := arg[2];
  else
    ErrorNoReturn("expected 2 arguments found ", Length(arg));
  fi;

  if not IsPosInt(n) or not IsOperation(filter) then
    ErrorNoReturn("the arguments must be a positive integer or a filter ",
                  "and a positive integer");
  fi;

  S := FreeSemilatticeCons(filter, n);

  if "IsMagmaWithOne" in NamesFilter(filter) then
    SetSize(S, 2 ^ n);
  else
    SetSize(S, 2 ^ n - 1);
  fi;

  SetIsSemilattice(S, true);

  return S;
end);

# Free semilattice: constructors

InstallMethod(FreeSemilatticeCons,
"for IsFpSemigroup and a pos int",
[IsFpSemigroup, IsPosInt],
function(_, n)
    local F, gen, l, i, j, commR, idemR;
    F := FreeSemigroup(n);
    gen := GeneratorsOfSemigroup(F);
    l := Length(gen);

    commR := [];
    for i in [1 .. l - 1] do
        for j in [i + 1 .. l] do
            Add(commR, [gen[i] * gen[j], gen[j] * gen[i]]);
        od;
    od;

    idemR := List(gen, x -> [x * x, x]);
    return F / Concatenation(commR, idemR);
end);

InstallMethod(FreeSemilatticeCons,
"for IsFpSemigroup and a pos int",
[IsFpMonoid, IsPosInt],
function(_, n)
    local F, gen, l, i, j, commR, idemR;
    F := FreeMonoid(n);
    gen := GeneratorsOfSemigroup(F);
    l := Length(gen);

    commR := [];
    for i in [1 .. l - 1] do
        for j in [i + 1 .. l] do
            Add(commR, [gen[i] * gen[j], gen[j] * gen[i]]);
        od;
    od;

    idemR := List(gen, x -> [x * x, x]);
    return F / Concatenation(commR, idemR);
end);

InstallMethod(FreeSemilatticeCons,
"for IsTransformationSemigroup and a pos int",
[IsTransformationSemigroup, IsPosInt],
function(_, n)
    local gen, i, L;
    gen := [];
    for i in [1 .. n] do
        L := [1 .. n + 1];
        L[i] := n + 1;
        Add(gen, Transformation(L));
    od;
    return Semigroup(gen);
end);

InstallMethod(FreeSemilatticeCons,
"for IsTransformationSemigroup and a pos int",
[IsTransformationMonoid, IsPosInt],
function(_, n)
    local gen, i, L;
    gen := [];
    for i in [1 .. n] do
        L := [1 .. n + 1];
        L[i] := n + 1;
        Add(gen, Transformation(L));
    od;
    return Monoid(gen);
end);

InstallMethod(FreeSemilatticeCons,
"for IsPartialPermSemigroup and a pos int",
[IsPartialPermSemigroup, IsPosInt],
function(_, n)
    local gen, i, L;
    gen := [];
    for i in [1 .. n] do
        L := [1 .. n];
        Remove(L, i);
        Add(gen, PartialPerm(L, L));
    od;
    return Semigroup(gen);
end);

InstallMethod(FreeSemilatticeCons,
"for IsPartialPermSemigroup and a pos int",
[IsPartialPermMonoid, IsPosInt],
function(_, n)
    local gen, i, L;
    gen := [];
    for i in [1 .. n] do
        L := [1 .. n];
        Remove(L, i);
        Add(gen, PartialPerm(L, L));
    od;
    return Monoid(gen);
end);

# Free semilattice: other constructors

for _IsXSemigroup in ["IsBipartitionSemigroup",
                      "IsPBRSemigroup",
                      "IsBooleanMatSemigroup",
                      "IsNTPMatrixSemigroup",
                      "IsMaxPlusMatrixSemigroup",
                      "IsMinPlusMatrixSemigroup",
                      "IsTropicalMaxPlusMatrixSemigroup",
                      "IsTropicalMinPlusMatrixSemigroup",
                      "IsProjectiveMaxPlusMatrixSemigroup",
                      "IsIntegerMatrixSemigroup"] do
  InstallMethod(FreeSemilatticeCons,
  Concatenation("for ", _IsXSemigroup, ", and pos int"),
  [ValueGlobal(_IsXSemigroup), IsPosInt],
  function(filter, n)
    return AsSemigroup(filter,
                       FreeSemilatticeCons(IsTransformationSemigroup, n));
  end);
od;

for _IsXMonoid in ["IsBipartitionMonoid",
                    "IsPBRMonoid",
                    "IsBooleanMatMonoid",
                    "IsNTPMatrixMonoid",
                    "IsMaxPlusMatrixMonoid",
                    "IsMinPlusMatrixMonoid",
                    "IsTropicalMaxPlusMatrixMonoid",
                    "IsTropicalMinPlusMatrixMonoid",
                    "IsProjectiveMaxPlusMatrixMonoid",
                    "IsIntegerMatrixMonoid"] do
  InstallMethod(FreeSemilatticeCons,
  Concatenation("for ", _IsXMonoid, ", and pos int"),
  [ValueGlobal(_IsXMonoid), IsPosInt],
  function(filter, n)
    return AsMonoid(filter,
                    FreeSemilatticeCons(IsTransformationMonoid, n));
  end);
od;

Unbind(_IsXSemigroup);
Unbind(_IsXMonoid);

# Zero semigroup: main method

InstallGlobalFunction(ZeroSemigroup,
function(arg)
  local filter, n, S;

  if Length(arg) = 1  then
    filter := IsTransformationSemigroup;
    n := arg[1];
  elif Length(arg) = 2 then
    filter := arg[1];
    n := arg[2];
  fi;

  if not IsBound(n) or not IsPosInt(n) or not IsOperation(filter) then
    ErrorNoReturn("the arguments must be a positive integer or a filter ",
                  "and a positive integer");
  fi;

  S := ZeroSemigroupCons(filter, n);

  SetSize(S, n);
  SetIsZeroSemigroup(S, true);
  SetMultiplicativeZero(S, S.1 ^ 2);
  SetIsGroupAsSemigroup(S, IsTrivial(S));
  SetIsRegularSemigroup(S, IsTrivial(S));
  SetIsMonogenicSemigroup(S, n <= 2);
  SetMinimalSemigroupGeneratingSet(S, GeneratorsOfSemigroup(S));
  return S;
end);

# Zero semigroup: constructors

InstallMethod(ZeroSemigroupCons,
"for IsTransformationSemigroup and a positive integer",
[IsTransformationSemigroup, IsPosInt],
function(_, n)
  local out, max, deg, N, R, gens, im, iter, r, i;

  if n = 1 then
    out := Semigroup(Transformation([1]));
    SetMultiplicativeZero(out, out.1);
    return out;
  fi;

  # calculate the minimal possible degree
  max := 0;
  deg := 0;
  while max < n do
    deg := deg + 1;
    for r in [1 .. deg - 1] do
      N := r ^ (deg - r);
      if N > max then
        max := N;
        R := r;
      fi;
    od;
  od;

  gens := [];
  im   := [1 .. R] * 0 + 1;
  iter := IteratorOfTuples([1 .. R], deg - R);
  NextIterator(iter);  # skip the zero

  for i in [1 .. n - 1] do
    Add(gens, Transformation(Concatenation(im, NextIterator(iter))));
  od;

  out := Semigroup(gens, rec(acting := false));
  SetMultiplicativeZero(out, ConstantTransformation(deg, 1));

  return out;
end);

InstallMethod(ZeroSemigroupCons,
"for IsPartialPermSemigroup and a positive integer",
[IsPartialPermSemigroup, IsPosInt],
function(_, n)
  local zero, gens, out, i;

  zero := PartialPerm([], []);
  if n = 1 then
    gens := [zero];
  else
    gens := EmptyPlist(n - 1);
    for i in [1 .. n - 1] do
      gens[i] := PartialPerm([2 * i - 1], [2 * i]);
    od;
  fi;
  out := Semigroup(gens);
  SetMultiplicativeZero(out, zero);
  return out;
end);

InstallMethod(ZeroSemigroupCons,
"for a filter and a positive integer",
[IsBlockBijectionSemigroup, IsPosInt],
function(_, n)
  local zero, gens, points, pair, out, i;

  if n = 1 then
    zero := Bipartition([[1, -1]]);
    gens := [zero];
  elif n = 2 then
    points := Concatenation([1 .. 3], [-3 .. -1]);
    zero := Bipartition([points]);
    gens := [Bipartition([[1, -2], [-1, 2, 3, -3]])];
  else
    points := Concatenation([1 .. 2 * (n - 1)], -[1 .. 2 * (n - 1)]);
    zero := Bipartition([points]);
    gens := EmptyPlist(n - 1);
    for i in [1 .. n - 1] do
      pair := [2 * i - 1, -(2 * i)];
      gens[i] := Bipartition([pair, Difference(points, pair)]);
    od;
  fi;
  out := Semigroup(gens);
  SetMultiplicativeZero(out, zero);
  return out;
end);

InstallMethod(ZeroSemigroupCons,
"for a filter and a positive integer",
[IsBipartitionSemigroup, IsPosInt],
function(_, n)
  local zero, out;

  if n = 2 then
    zero := Bipartition([[1], [2], [-1], [-2]]);
    out := Semigroup(Bipartition([[1, -2], [2], [-1]]));
    SetMultiplicativeZero(out, zero);
    return out;
  fi;

  return AsSemigroup(IsBipartitionSemigroup,
                     ZeroSemigroupCons(IsTransformationSemigroup, n));
end);

InstallMethod(ZeroSemigroupCons,
"for a IsReesZeroMatrixSemigroup and a positive integer",
[IsReesZeroMatrixSemigroup, IsPosInt],
function(_, n)
  local mat;

  if n = 1 then
    ErrorNoReturn("there is no Rees 0-matrix semigroup of order 1");
  fi;
  mat := [[1 .. n - 1] * 0];
  return ReesZeroMatrixSemigroup(Group(()), mat);
end);

# Zero semigroup: other constructors

for _IsXSemigroup in ["IsPBRSemigroup",
                      "IsBooleanMatSemigroup",
                      "IsNTPMatrixSemigroup",
                      "IsMaxPlusMatrixSemigroup",
                      "IsMinPlusMatrixSemigroup",
                      "IsTropicalMaxPlusMatrixSemigroup",
                      "IsTropicalMinPlusMatrixSemigroup",
                      "IsProjectiveMaxPlusMatrixSemigroup",
                      "IsIntegerMatrixSemigroup"] do
  InstallMethod(ZeroSemigroupCons,
  Concatenation("for ", _IsXSemigroup, " and a positive integer"),
  [ValueGlobal(_IsXSemigroup), IsPosInt],
  function(filter, n)
    return AsSemigroup(filter,
                       ZeroSemigroupCons(IsTransformationSemigroup, n));
  end);
od;
Unbind(_IsXSemigroup);

# Left zero semigroup: main method

InstallGlobalFunction(LeftZeroSemigroup,
function(arg)
  local filt, n, S, max, deg, N, R, gens, im, iter, r, i;

  if Length(arg) = 1 then
    filt := IsTransformationSemigroup;
    n    := arg[1];
  elif Length(arg) = 2 then
    filt := arg[1];
    n    := arg[2];
  fi;

  if not IsBound(filt) or not IsFilter(filt) or not IsPosInt(n) then
    ErrorNoReturn("the arguments must be a positive integer or ",
                  "a filter and a positive integer");
  elif n = 1 then
    return TrivialSemigroup(filt);
  elif filt <> IsTransformationSemigroup then
    S := RectangularBand(filt, n, 1);
    SetIsLeftZeroSemigroup(S, true);
    return S;
  fi;

  # calculate the minimal possible degree
  max := 0;
  deg := 0;
  while max < n do
    deg := deg + 1;
    for r in [1 .. deg - 1] do
      N := r ^ (deg - r);
      if N > max then
        max := N;
        R := r;
      fi;
    od;
  od;

  gens := [];
  im   := [1 .. R];
  iter := IteratorOfTuples([1 .. R], deg - R);

  for i in [1 .. n] do
    Add(gens, Transformation(Concatenation(im, NextIterator(iter))));
  od;

  S := Semigroup(gens, rec(acting := false));
  SetIsLeftZeroSemigroup(S, true);
  return S;
end);

# Right zero semigroup: main method

InstallGlobalFunction(RightZeroSemigroup,
function(arg)
  local filt, n, S, max, deg, ker, add, iter, gens, i;

  if Length(arg) = 1 then
    filt := IsTransformationSemigroup;
    n    := arg[1];
  elif Length(arg) = 2 then
    filt := arg[1];
    n    := arg[2];
  fi;

  if not IsBound(filt) or not IsFilter(filt) or not IsPosInt(n) then
    ErrorNoReturn("the arguments must be a positive integer or ",
                  "a filter and a positive integer");
  elif n = 1 then
    return TrivialSemigroup(filt);
  elif filt <> IsTransformationSemigroup then
    S := RectangularBand(filt, 1, n);
    SetIsRightZeroSemigroup(S, true);
    return S;
  fi;

  # calculate the minimal possible degree
  max := 0;
  deg := 0;
  while max < n do
    deg := deg + 1;
    if (deg mod 3) = 0 then
      max := 3 ^ (deg / 3);
    elif (deg mod 3) = 1 then
      max := 4 * 3 ^ ((deg - 4) / 3);
    else
      max := 2 * 3 ^ ((deg - 2) / 3);
    fi;
  od;

  # make the first class of the kernel
  if (deg mod 3) = 0 then
    ker := [[1 .. 3]];
    add := 3;
  elif (deg mod 3) = 1 then
    ker := [[1 .. 4]];
    add := 4;
  else
    ker := [[1 .. 2]];
    add := 2;
  fi;

  # add remaining classes in kernel (all of size 3)
  while add < deg do
    Add(ker, [1 .. 3] + add);
    add := add + 3;
  od;

  iter := IteratorOfCartesianProduct(ker);

  gens := [];
  for i in [1 .. n] do
    Add(gens, TransformationByImageAndKernel(NextIterator(iter), ker));
  od;

  S := Semigroup(gens, rec(acting := false));
  SetIsRightZeroSemigroup(S, true);
  return S;
end);

InstallGlobalFunction(BrandtSemigroup,
function(arg)
  local S;

  if Length(arg) = 1 and IsPosInt(arg[1]) then
    S := BrandtSemigroupCons(IsPartialPermSemigroup, Group(()), arg[1]);
  elif Length(arg) = 2 and IsOperation(arg[1]) and IsPosInt(arg[2]) then
    S := BrandtSemigroupCons(arg[1], Group(()), arg[2]);
  elif Length(arg) = 2 and IsGroup(arg[1]) and IsPosInt(arg[2]) then
    S := BrandtSemigroupCons(IsPartialPermSemigroup, arg[1], arg[2]);
  elif Length(arg) = 3 and IsOperation(arg[1]) and IsGroup(arg[2])
      and IsPosInt(arg[3]) then
    S := BrandtSemigroupCons(arg[1], arg[2], arg[3]);
  else
    ErrorNoReturn("the arguments must be a positive integer or a filter and",
                   " a positive integer, or  a perm group and positive ",
                   "integer, or a filter, perm group, and positive ",
                   "integer");
  fi;
  SetIsZeroSimpleSemigroup(S, true);
  SetIsBrandtSemigroup(S, true);
  return S;
end);

InstallMethod(BrandtSemigroupCons,
"for IsPartialPermSemigroup, a perm group, and a positive integer",
[IsPartialPermSemigroup, IsPermGroup, IsPosInt],
function(_, G, n)
  local gens, one, m, i, x;

  gens := [];

  if IsTrivial(G) then
    if n = 1 then
      Add(gens, PartialPerm([1], [1]));
      Add(gens, EmptyPartialPerm());
    else
      for i in [2 .. n] do
        Add(gens, PartialPerm([1], [i]));
      od;
    fi;
  else
    one := PartialPerm(MovedPoints(G), MovedPoints(G));
    for x in GeneratorsOfGroup(G) do
      Add(gens, one * x);
    od;
    m := LargestMovedPoint(G) - SmallestMovedPoint(G) + 1;
    for i in [1 .. n - 1] do
      Add(gens, PartialPerm(MovedPoints(G), MovedPoints(G) + m * i));
    od;
    if n = 1 then
      Add(gens, EmptyPartialPerm());
    fi;
  fi;

  return InverseSemigroup(gens);
end);

InstallMethod(BrandtSemigroupCons,
"for IsReesZeroMatrixSemigroup, a finite group, and a positive integer",
[IsReesZeroMatrixSemigroup, IsGroup and IsFinite, IsPosInt],
function(_, G, n)
  local mat, i;
  mat := [];
  for i in [1 .. n] do
    Add(mat, ListWithIdenticalEntries(n, 0));
    mat[i][i] := One(G);
  od;

  return ReesZeroMatrixSemigroup(G, mat);
end);

for _IsXSemigroup in ["IsTransformationSemigroup",
                      "IsBipartitionSemigroup",
                      "IsPBRSemigroup",
                      "IsBooleanMatSemigroup",
                      "IsNTPMatrixSemigroup",
                      "IsMaxPlusMatrixSemigroup",
                      "IsMinPlusMatrixSemigroup",
                      "IsTropicalMaxPlusMatrixSemigroup",
                      "IsTropicalMinPlusMatrixSemigroup",
                      "IsProjectiveMaxPlusMatrixSemigroup",
                      "IsIntegerMatrixSemigroup"] do
  InstallMethod(BrandtSemigroupCons,
  Concatenation("for ", _IsXSemigroup, " and a positive integer"),
  [ValueGlobal(_IsXSemigroup), IsPermGroup, IsPosInt],
  function(filter, G, n)
    return AsSemigroup(filter,
                       BrandtSemigroupCons(IsPartialPermSemigroup, G, n));
  end);
od;
Unbind(_IsXSemigroup);

InstallMethod(StrongSemilatticeOfSemigroups,
"for a digraph, a list, and a list",
[IsDigraph, IsList, IsList],
function(D, semigroups, homomorphisms)
  local out, pos, err, efam, etype, type, maps, n, rtclosure, paths, path, len,
   tobecomposed, firsthom, gens, i, j;

  if not IsMeetSemilatticeDigraph(DigraphReflexiveTransitiveClosure(D)) then
    ErrorNoReturn("the reflexive transitive closure of the 1st argument ",
                  "(a digraph) must be a meet semilattice");
  fi;
  pos := PositionProperty(semigroups, x -> not IsSemigroup(x));
  if pos <> fail then
    ErrorNoReturn("the 2nd argument (a list) must consist of semigroups, ",
                  "but found ", TNAM_OBJ(semigroups[pos]), " in position ", pos);
  elif DigraphNrVertices(D) <> Length(semigroups) then
    err := Concatenation(
             "the 2nd argument (a list) must have length {}, ",
             "the number of vertices of the 1st argument (a digraph)",
             ", but found length {}");
    ErrorNoReturn(StringFormatted(err,
                                  DigraphNrVertices(D),
                                  Length(semigroups)));
  fi;
  pos := PositionProperty(homomorphisms, x -> not IsList(x));
  if pos <> fail then
    ErrorNoReturn("the 3rd argument (a list) must consist of lists, ",
                  "but found ",
                  TNAM_OBJ(homomorphisms[pos]),
                  " in position ",
                  pos);
  elif DigraphNrVertices(D) <> Length(homomorphisms) then
    err := Concatenation(
             "the 3rd argument (a list) must have length {}, ",
             "the number of vertices of the 1st argument (a digraph)",
             ", but found length {}");
    ErrorNoReturn(StringFormatted(err,
                  DigraphNrVertices(D),
                  Length(homomorphisms)));
  fi;

  out := OutNeighbours(D);
  for i in [1 .. DigraphNrVertices(D)] do
    if Length(homomorphisms[i]) <> Length(out[i]) then
      err := Concatenation(
               "the 3rd argument (a list) must have the same shape ",
               "as the out-neighbours of the 1st argument (a digraph), ",
               "expected shape {} but found {}");
      ErrorNoReturn(StringFormatted(err,
                                    List(out, Length),
                                    List(homomorphisms, Length)));
    fi;
    pos := PositionProperty(homomorphisms[i],
                            x -> not IsSemigroupHomomorphism(x));
    if pos <> fail then
        ErrorNoReturn("the 3rd argument (a list) must consist ",
                      "of lists of homomorphisms, but position ",
                      StringFormatted("[{}, {}]", i, pos),
                      " is not a homomorphism");
    fi;

    for j in [1 .. Length(homomorphisms[i])] do
      if Source(homomorphisms[i][j]) <> semigroups[out[i][j]] then
        err := Concatenation("expected the homomorphism in position {} of the ",
                             "3rd argument to have source equal to position {} ",
                             "in the 2nd argument");
        ErrorNoReturn(StringFormatted(err, [i, j], out[i][j]));
      elif Range(homomorphisms[i][j]) <> semigroups[i] then
        err := Concatenation("expected the homomorphism in position {} of the ",
                             "3rd argument to have range equal to position {} ",
                             "in the 2nd argument");
        ErrorNoReturn(StringFormatted(err, [i, j], i));
      fi;
    od;
  od;

  efam := NewFamily("StrongSemilatticeOfSemigroupsElementsFamily", IsSSSE);
  etype := NewType(efam, IsSSSERep);

  type := NewType(CollectionsFamily(efam),
                  IsStrongSemilatticeOfSemigroups
                    and IsComponentObjectRep
                    and IsAttributeStoringRep);

  # the next section converts the list of homomorphisms into a matrix,
  # composing when necessary.
  maps := [];
  n := Length(semigroups);
  rtclosure := DigraphReflexiveTransitiveClosure(D);
  for i in [1 .. n] do
    Add(maps, []);
    for j in [1 .. n] do
      if i = j then
        # First check that if a homomorphism from i to i was defined, it
        # is the identity
        if IsDigraphEdge(D, [i, i]) then
          if homomorphisms[i][Position(OutNeighboursOfVertex(D, i), i)]
              <> IdentityMapping(semigroups[i]) then
             ErrorNoReturn("Expected homomorphism from ",
                           i, " to ", i,
                           " to be the identity");
           fi;
        fi;
        Add(maps[i], IdentityMapping(semigroups[i]));
      elif IsDigraphEdge(rtclosure, [i, j]) then
        paths        := IteratorOfPaths(D, i, j);
        path         := NextIterator(paths);
        len          := Length(path[2]);
        tobecomposed := List([1 .. len],
                              x -> homomorphisms[path[1][x]][path[2][x]]);
        firsthom     := CompositionMapping(tobecomposed);

        # now check the first composition is the same as the composition along
        # all other paths from i to j
        while not IsDoneIterator(paths) do
          path         := NextIterator(paths);
          len          := Length(path[2]);
          tobecomposed := List([1 .. len],
                                x -> homomorphisms[path[1][x]][path[2][x]]);
          if CompositionMapping(tobecomposed) <> firsthom then
            ErrorNoReturn("Composing homomorphisms along different paths from ",
                          i,
                          " to ",
                          j,
                          " does not produce the same result. The ",
                          "homomorphisms must commute");
          fi;
        od;
        # If no errors so far, then all paths commute and we can add the comp.
        Add(maps[i], firsthom);
        # TODO(later) for larger digraphs, the current method will compute some
        # compositions of homomorphisms several times.  For example, take
        # Digraph([[], [1], [1], [2, 3], [4]]). It defines a meet-semilattice
        # and the SSS initialisation will check that composing the
        # homomorphisms 1->3->4 and 1->2->4 give the same result. Later on in
        # the initialisation, it will also check equivalence of the paths
        # 1->2->4->5 and 1->3->4->5, but will not be re-using previously
        # computed information on what the composition 1->3->4 equals, say.
        # Saving the homomorphsisms already computed using some sort of dynamic
        # programming approach may improve the speed (at the cost of memory).
      else
        Add(maps[i], fail);
      fi;
    od;
  od;

  out := rec();

  gens := [];
  for i in [1 .. Length(semigroups)] do
    Append(gens, List(GeneratorsOfSemigroup(semigroups[i]),
                      x -> Objectify(etype, [out, i, x])));
  od;

  ObjectifyWithAttributes(out,
                          type,
                          SemilatticeOfStrongSemilatticeOfSemigroups,
                          rtclosure,
                          SemigroupsOfStrongSemilatticeOfSemigroups,
                          semigroups,
                          HomomorphismsOfStrongSemilatticeOfSemigroups,
                          maps,
                          ElementTypeOfStrongSemilatticeOfSemigroups,
                          etype,
                          GeneratorsOfMagma,
                          gens);
  return out;
end);

InstallMethod(Size, "for a strong semilattice of semigroups",
[IsStrongSemilatticeOfSemigroups],
S -> Sum(SemigroupsOfStrongSemilatticeOfSemigroups(S), Size));

InstallMethod(ViewString, "for a strong semilattice of semigroups",
[IsStrongSemilatticeOfSemigroups],
function(S)
  local size;
  size := Size(SemigroupsOfStrongSemilatticeOfSemigroups(S));
  return Concatenation("<strong semilattice of ",
                       String(size),
                       " semigroups>");
end);

InstallMethod(SSSE,
"for a strong semilattice of semigroups, a pos int, and an associative elt",
[IsStrongSemilatticeOfSemigroups, IsPosInt, IsAssociativeElement],
function(S, n, x)
  if n > Size(SemigroupsOfStrongSemilatticeOfSemigroups(S)) then
    ErrorNoReturn("expected 2nd argument to be an integer between 1 and ",
                  "the size of the semilattice, i.e. ",
                  Size(SemigroupsOfStrongSemilatticeOfSemigroups(S)));
  elif not x in SemigroupsOfStrongSemilatticeOfSemigroups(S)[n] then
    ErrorNoReturn("where S, n and x are the 1st, 2nd and 3rd arguments ",
                  "respectively, expected x to be an element of ",
                  "SemigroupsOfStrongSemilatticeOfSemigroups(S)[n]");
  fi;
  return Objectify(ElementTypeOfStrongSemilatticeOfSemigroups(S), [S, n, x]);
end);

InstallMethod(\=, "for SSSEs", IsIdenticalObj,
[IsSSSERep, IsSSSERep],
{x, y} -> x![1] = y![1] and x![2] = y![2] and x![3] = y![3]);

InstallMethod(\<, "for SSSEs", IsIdenticalObj, [IsSSSERep, IsSSSERep],
{x, y} -> (x![2] < y![2]) or (x![2] = y![2] and x![3] < y![3]));

InstallMethod(\*, "for SSSEs", IsIdenticalObj,
[IsSSSERep, IsSSSERep],
function(x, y)
  local D, meet, maps;
  D    := SemilatticeOfStrongSemilatticeOfSemigroups(x![1]);
  meet := PartialOrderDigraphMeetOfVertices(D, x![2], y![2]);
  maps := HomomorphismsOfStrongSemilatticeOfSemigroups(x![1]);
  return SSSE(x![1],
              meet,
              (x![3] ^ (maps[meet][x![2]])) * (y![3] ^ (maps[meet][y![2]])));
end);

InstallMethod(ViewString, "for a SSSE", [IsSSSERep],
x -> Concatenation("SSSE(", ViewString(x![2]), ", ", ViewString(x![3]), ")"));

InstallMethod(UnderlyingSemilatticeOfSemigroups, "for a SSSE rep",
[IsSSSERep], x -> x![1]);
