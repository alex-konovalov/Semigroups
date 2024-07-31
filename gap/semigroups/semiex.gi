#############################################################################
##
##  semigroups/semiex.gi
##  Copyright (C) 2013-2022                               James D. Mitchell
##
##  Licensing information can be found in the README file of this package.
##
#############################################################################
##

# for testing purposes

# BlocksOfPartition := function(partition)
#   local blocks, lookup, n, i, j;
#
#   blocks := []; lookup := []; n := 0;
#   for i in [1 .. Length(partition)] do
#     blocks[i] := [n + 1 .. partition[i] + n];
#     for j in blocks[i] do
#       lookup[j] := i;
#     od;
#     n := n + partition[i];
#   od;
#   return [blocks, lookup];
# end;
#
# IsEndomorphismOfPartition := function(bl, f)
#   local imblock, x;
#
#   for x in bl[1] do  #blocks
#     imblock := bl[1][bl[2][x[1] ^ f]];
#     if not ForAll(x, y -> y ^ f in imblock) then
#       return false;
#     fi;
#   od;
#   return true;
# end;
#
# NrEndomorphismsPartition := function(partition)
#   local bl;
#   bl := BlocksOfPartition(partition);
#   return Number(FullTransformationSemigroup(Sum(partition)), x ->
#     IsEndomorphismOfPartition(bl, x));
# end;

# From the `The rank of the semigroup of transformations stabilising a
# partition of a finite set', by Araujo, Bentz, Mitchell, and Schneider (2014).

InstallMethod(EndomorphismsPartition, "for a list of positive integers",
[IsCyclotomicCollection],
function(partition)
  local s, r, distinct, equal, prev, n, blocks, unique, didprevrepeat, gens, x,
  m, y, w, p, i, j, k, block;

  if not ForAll(partition, IsPosInt) then
    ErrorNoReturn("the argument (a cyclo. coll.) does not consist of ",
                  "positive integers");
  elif ForAll(partition, x -> x = 1) then
    return FullTransformationMonoid(Length(partition));
  elif Length(partition) = 1 then
    return FullTransformationMonoid(partition[1]);
  elif not IsSortedList(partition) then
    partition := ShallowCopy(partition);
    Sort(partition);
  fi;

  # preprocessing...

  s := 0;          # nr of distinct block sizes
  r := 0;          # nr of block sizes with at least one other block of equal
                   # size
  distinct := [];  # indices of blocks with distinct block sizes
  equal := [];     # indices of blocks with at least one other block of equal
                   # size, partitioned according to the sizes of the blocks
  prev := 0;       # size of the previous block
  n := 0;          # the degree of the transformations
  blocks := [];    # the actual blocks of the partition
  unique := [];    # blocks of a unique size

  for i in [1 .. Length(partition)] do
    blocks[i] := [n + 1 .. partition[i] + n];
    n := n + partition[i];
    if partition[i] > prev then
      s := s + 1;
      distinct[s] := i;
      prev := partition[i];
      didprevrepeat := false;
      AddSet(unique, i);
    elif not didprevrepeat then
      # repeat block size
      r := r + 1;
      equal[r] := [i - 1, i];
      didprevrepeat := true;
      RemoveSet(unique, i - 1);
    else
      Add(equal[r], i);
    fi;
  od;

  # get the generators of T(X,P) over Sigma(X,P)...
  # from the proof of Theorem 3.3
  gens := [];
  for i in [1 .. Length(distinct) - 1] do
    for j in [i + 1 .. Length(distinct)] do
      x := [1 .. n];
      for k in [1 .. Length(blocks[distinct[i]])] do
        x[blocks[distinct[i]][k]] := blocks[distinct[j]][k];
      od;
      Add(gens, Transformation(x));
    od;
  od;

  for block in equal do
    x := [1 .. n];
    x{blocks[block[1]]} := blocks[block[2]];
    Add(gens, Transformation(x));
  od;

  # get the generators of Sigma(X,P) over S(X,P)...

  # the generators from B (swap blocks of adjacent distinct sizes)...
  for i in [1 .. s - 1] do
    x := [1 .. n];
    # map up
    for j in [1 .. Length(blocks[distinct[i]])] do
      x[blocks[distinct[i]][j]] := blocks[distinct[i + 1]][j];
      x[blocks[distinct[i + 1]][j]] := blocks[distinct[i]][j];
    od;
    # map down
    for j in [Length(blocks[distinct[i]]) + 1 ..
              Length(blocks[distinct[i + 1]])] do
      x[blocks[distinct[i + 1]][j]] := blocks[distinct[i]][1];
    od;
    Add(gens, Transformation(x));
  od;

  # the generators from C...
  if Length(blocks[distinct[1]]) <> 1 then
    x := [1 .. n];
    x[1] := 2;
    Add(gens, Transformation(x));
  fi;

  for i in [2 .. s] do
    if Length(blocks[distinct[i]]) - Length(blocks[distinct[i - 1]]) > 1 then
      x := [1 .. n];
      x[blocks[distinct[i]][1]] := x[blocks[distinct[i]][2]];
      Add(gens, Transformation(x));
    fi;
  od;

  # get the generators of S(X,P)...
  if s = r or s - r >= 2 then
    # 2 generators for the r wreath products of symmetric groups
    for i in [1 .. r] do
      m := Length(equal[i]);       # WreathProduct(S_n, S_m) m blocks of size n
      n := partition[equal[i][1]];
      x := blocks{equal[i]};

      if n > 1 then
        x[2] := Permuted(x[2], (1, 2));
      fi;

      if IsOddInt(m) or IsOddInt(n) then
        x := Permuted(x, PermList(Concatenation([2 .. m], [1])));
      else
        x := Permuted(x, PermList(Concatenation([1], [3 .. m], [2])));
      fi;

      x := MappingPermListList(Concatenation(blocks{equal[i]}),
                               Concatenation(x));
      Add(gens, AsTransformation(x));

      y := blocks{equal[i]};
      y[1] := Permuted(y[1], PermList(Concatenation([2 .. n], [1])));
      y := Permuted(y, (1, 2));
      y := MappingPermListList(Concatenation(blocks{equal[i]}),
                               Concatenation(y));
      Add(gens, AsTransformation(y));
    od;
  elif s - r = 1 and r >= 1 then
    # JDM this case should be changed as in the previous case
    # 2 generators for the r-1 wreath products of symmetric groups
    for i in [1 .. r - 1] do
      m := Length(equal[i]);       # WreathProduct(S_n, S_m) m blocks of size n
      n := partition[equal[i][1]];
      x := blocks{equal[i]};

      if n > 1 then
        x[2] := Permuted(x[2], (1, 2));
      fi;

      if IsOddInt(m) or IsOddInt(n) then
        x := Permuted(x, PermList(Concatenation([2 .. m], [1])));
      else
        x := Permuted(x, PermList(Concatenation([1], [3 .. m], [2])));
      fi;

      x := MappingPermListList(Concatenation(blocks{equal[i]}),
                               Concatenation(x));
      Add(gens, AsTransformation(x));

      y := blocks{equal[i]};
      y[1] := Permuted(y[1], PermList(Concatenation([2 .. n], [1])));
      y := Permuted(y, (1, 2));
      y := MappingPermListList(Concatenation(blocks{equal[i]}),
                               Concatenation(y));
      Add(gens, AsTransformation(y));
    od;

    # 3 generators for (S_{n_k}wrS_{m_k})\times S_{l_1}
    m := Length(equal[r]);
    n := partition[equal[r][1]];
    if IsOddInt(m) or IsOddInt(n) then
      x := Permuted(blocks{equal[r]}, PermList(Concatenation([2 .. m], [1])));
    else
      x := Permuted(blocks{equal[r]},
                    PermList(Concatenation([1], [3 .. m], [2])));
    fi;

    if n > 1 then
      x[2] := Permuted(x[2], (1, 2));
    fi;
    x := MappingPermListList(Concatenation(blocks{equal[r]}),
                             Concatenation(x));
    Add(gens, AsTransformation(x));  # (x, id)=u in the paper

    y := Permuted(blocks{equal[r]}, (1, 2));
    y[1] := Permuted(y[1], PermList(Concatenation([2 .. n], [1])));
    y := MappingPermListList(Concatenation(blocks{equal[r]}),
                             Concatenation(y));
    # (y, (1,2,\ldots, l_1))=v in the paper
    y := y * MappingPermListList(blocks[unique[1]],
                                 Concatenation(blocks[unique[1]]{[2 ..
                                               Length(blocks[unique[1]])]},
                                               [blocks[unique[1]][1]]));
    Add(gens, AsTransformation(y));

    if Length(blocks[unique[1]]) > 1 then
      w := MappingPermListList(blocks[unique[1]],
                               Permuted(blocks[unique[1]], (1, 2)));
      Add(gens, AsTransformation(w));  # (id, (1,2))=w in the paper
    fi;
  fi;
  if s - r >= 2 then  # the (s-r) generators of W_2 in the proof
    for i in [1 .. s - r - 1] do
      if Length(blocks[unique[i]]) <> 1 then
        x := Permuted(blocks[unique[i]], (1, 2));
      else
        x := ShallowCopy(blocks[unique[i]]);
      fi;
      if IsOddInt(Length(blocks[unique[i + 1]])) then
        p := PermList(Concatenation([2 .. Length(blocks[unique[i + 1]])],
                                    [1]));
        Append(x, Permuted(blocks[unique[i + 1]], p));
      else

        p := PermList(Concatenation([1], [3 .. Length(blocks[unique[i + 1]])],
                                    [2]));
        Append(x, Permuted(blocks[unique[i + 1]], p));
      fi;
      x := MappingPermListList(Union(blocks[unique[i]],
                                     blocks[unique[i + 1]]), x);
      if x <> () then
        Add(gens, AsTransformation(x));
      fi;
    od;

    x := [];
    if partition[unique[1]] <> 1 then
      if IsOddInt(partition[unique[1]]) then
        Append(x, Permuted(blocks[unique[1]],
                           PermList(Concatenation([2 ..
                           Length(blocks[unique[1]])], [1]))));
      else
        Append(x, Permuted(blocks[unique[1]],
                           PermList(Concatenation([1],
                           [3 .. Length(blocks[unique[1]])], [2]))));
      fi;
    else
      Append(x, blocks[unique[1]]);
    fi;
    Append(x, Permuted(blocks[unique[s - r]], (1, 2)));
    x := MappingPermListList(Concatenation(blocks[unique[1]],
                                           blocks[unique[s - r]]), x);
    Add(gens, AsTransformation(x));
  fi;

  return Semigroup(gens);
end);

# Matrix semigroups . . .

# The full matrix semigroup is generated by a generating set
# for the general linear group plus one element of rank n - 1

InstallMethod(GeneralLinearMonoid, "for pos int and pos int",
[IsPosInt, IsPosInt],
function(d, q)
  local gens, x, S;
  gens := GeneratorsOfGroup(GL(d, q));
  gens := List(gens, x -> Matrix(GF(q), x));
  x := OneMutable(gens[1]);
  x[d][d] := Z(q) * 0;
  Add(gens, x);
  S := Monoid(gens);
  SetSize(S, q ^ (d * d));
  SetIsGeneralLinearMonoid(S, true);
  SetFilterObj(S, IsRegularActingSemigroupRep);
  return S;
end);

InstallMethod(SpecialLinearMonoid, "for pos int and pos int",
[IsPosInt, IsPosInt],
function(d, q)
  local gens, x, S;
  gens := GeneratorsOfGroup(SL(d, q));
  x := OneMutable(gens[1]);
  x[d][d] := Z(q) * 0;
  gens := List(gens, x -> Matrix(GF(q), x));
  Add(gens, x);
  S := Monoid(gens);
  SetFilterObj(S, IsRegularActingSemigroupRep);
  return S;
end);

InstallMethod(MunnSemigroup, "for a semilattice", [IsSemigroup],
S -> InverseSemigroup(GeneratorsOfMunnSemigroup(S), rec(small := true)));

InstallMethod(GeneratorsOfMunnSemigroup, "for a semilattice", [IsSemigroup],
function(S)
  local po, au, id, su, gr, out, e, map, p, min, pos, x, i, j, k;

  if not IsSemilattice(S) then
    ErrorNoReturn("the argument (a semigroup) is not a semilattice");
  fi;

  po := DigraphReflexiveTransitiveClosure(PartialOrderOfDClasses(S));
  au := [];  # automorphism groups partitions by size
  id := [];  # ideals (as sets of indices) partitioned by size
  su := [];  # induced subdigraphs corresponding to ideals

  for x in OutNeighbors(po) do
    gr := InducedSubdigraph(po, SortedList(x));
    if not IsBound(au[Length(x)]) then
      au[Length(x)] := [];
      id[Length(x)] := [];
      su[Length(x)] := [];
    fi;
    Add(au[Length(x)], AutomorphismGroup(gr)
                       ^ MappingPermListList(DigraphVertices(gr),
                                             SortedList(x)));
    Add(id[Length(x)], SortedList(x));
    Add(su[Length(x)], gr);
  od;

  out := [PartialPerm(Last(id)[1], Last(id)[1])];

  for i in [Length(id), Length(id) - 1 .. 3] do
    if not IsBound(id[i]) then
      continue;
    fi;
    for j in [1 .. Length(id[i])] do
      e := PartialPerm(id[i][j], id[i][j]);
      for p in GeneratorsOfGroup(au[i][j]) do
        Add(out, e * p);
      od;
      for k in [j + 1 .. Length(id[i])] do
        map := IsomorphismDigraphs(su[i][j], su[i][k]);
        if map <> fail then
          p := MappingPermListList(id[i][j], DigraphVertices(su[i][j]))
                 * map * MappingPermListList(DigraphVertices(su[i][k]),
                                             id[i][k]);
          Add(out, e * p);
        fi;
      od;
    od;
  od;

  min := id[1][1][1];  # the index of the element in the minimal ideal
  Add(out, PartialPerm([min], [min]));

  # All ideals of size 2 are isomorphic and have trivial automorphism group
  for j in [1 .. Length(id[2])] do
    e := PartialPermNC(id[2][j], id[2][j]);
    Add(out, e);
    pos := Position(id[2][j], min);
    for k in [j + 1 .. Length(id[2])] do
      if Position(id[2][k], min) = pos then
        Add(out, PartialPerm(id[2][j], id[2][k]));
      else
        Add(out, PartialPerm(id[2][j], Reversed(id[2][k])));
      fi;
    od;
  od;

  return out;
end);

InstallMethod(OrderEndomorphisms, "for a positive integer", [IsPosInt],
function(n)
  local gens, S, i;

  gens := EmptyPlist(n);
  gens[1] := Transformation(Concatenation([1], [1 .. n - 1]));

  for i in [1 .. n - 1] do
    gens[i + 1] := [1 .. n];
    gens[i + 1][i] := i + 1;
    gens[i + 1] := TransformationNC(gens[i + 1]);
  od;

  S := Monoid(gens);
  SetFilterObj(S, IsRegularActingSemigroupRep);
  return S;
end);

InstallMethod(PartialOrderEndomorphisms, "for a positive integer", [IsPosInt],
function(n)
  local x, gens, S, i;

  x := [1 .. n + 1];
  gens := [];
  for i in [1 .. n] do
    x[i] := n + 1;
    Add(gens, Transformation(x));
    x[i] := i;
  od;

  S := Monoid(OrderEndomorphisms(n), gens);
  SetFilterObj(S, IsRegularActingSemigroupRep);
  return S;
end);

InstallMethod(OrderAntiEndomorphisms, "for a positive integer", [IsPosInt],
function(n)
  local S;
  S := Monoid(OrderEndomorphisms(n), Transformation(Reversed([1 .. n])));
  SetFilterObj(S, IsRegularActingSemigroupRep);
  return S;
end);

InstallMethod(PartialOrderAntiEndomorphisms, "for a positive integer",
[IsPosInt],
function(n)
  local S;
  S := Monoid(PartialOrderEndomorphisms(n), Transformation(Reversed([1 .. n])));
  SetFilterObj(S, IsRegularActingSemigroupRep);
  return S;
end);

InstallMethod(PartialTransformationMonoid, "for a positive integer",
[IsPosInt],
function(n)
  local a, b, c, d, S;

  a := [2, 1];
  b := [0 .. n - 1];
  b[1] := n;
  c := [1 .. n + 1];
  c[1] := n + 1;     # partial
  d := [2, 2];

  if n = 1 then
    S := Monoid(TransformationNC(c));
  elif n = 2 then
    S := Monoid(List([a, c, d], TransformationNC));
  else
    S := Monoid(List([a, b, c, d], TransformationNC));
  fi;

  SetFilterObj(S, IsRegularActingSemigroupRep);
  return S;
end);

InstallMethod(CatalanMonoid, "for a positive integer",
[IsPosInt],
function(n)
  local gens, next, i;

  if n = 1 then
    return Monoid(IdentityTransformation);
  fi;

  gens := [];

  for i in [1 .. n - 1] do
    next := [1 .. n];
    next[i + 1] := i;
    Add(gens, Transformation(next));
  od;

  return Monoid(gens, rec(acting := false));
end);

InstallMethod(PartitionMonoid, "for an integer", [IsInt],
function(n)
  local gens, M;

  if n < 0 then
    ErrorNoReturn("the argument (an int) is not >= 0");
  elif n = 0 then
    return Monoid(Bipartition([]));
  elif n = 1 then
    return Monoid(Bipartition([[1], [-1]]));
  fi;

  gens := List(GeneratorsOfGroup(SymmetricGroup(n)), x -> AsBipartition(x, n));
  Add(gens, AsBipartition(PartialPermNC([2 .. n], [2 .. n]), n));
  Add(gens, Bipartition(Concatenation([[1, 2, -1, -2]],
                                        List([3 .. n], x -> [x, -x]))));

  M := Monoid(gens);
  SetFilterObj(M, IsRegularActingSemigroupRep);
  SetIsStarSemigroup(M, true);
  SetSize(M, Bell(2 * n));
  return M;
end);

InstallMethod(DualSymmetricInverseMonoid, "for an integer", [IsInt],
function(n)
  local gens;

  if n < 0 then
    ErrorNoReturn("the argument (an int) is not >= 0");
  elif n = 0 then
    return Monoid(Bipartition([]));
  elif n = 1 then
    return Monoid(Bipartition([[1, -1]]));
  fi;

  gens := List(GeneratorsOfGroup(SymmetricGroup(n)), x -> AsBipartition(x, n));

  if n = 2 then
    Add(gens, Bipartition([[1, 2, -1, -2]]));
  else
    Add(gens, Bipartition(Concatenation([[1, 2, -3], [3, -1, -2]],
                                           List([4 .. n], x -> [x, -x]))));
  fi;
  return InverseMonoid(gens);
end);

InstallMethod(PartialDualSymmetricInverseMonoid, "for an integer", [IsInt],
function(n)
  local gens;

  if n < 0 then
    ErrorNoReturn("the argument (an int) is not >= 0");
  elif n = 0 then
    return Monoid(Bipartition([]));
  elif n = 1 or n = 2 then
    return PartialUniformBlockBijectionMonoid(n);
  fi;

  gens := Set([PermList(Concatenation([2 .. n], [1])), (1, 2)]);
  gens := List(gens, x -> AsBipartition(x, n + 1));
  Add(gens, Bipartition(Concatenation([[1, 2, -3], [-1, -2, 3]],
                                      List([4 .. n + 1], x -> [x, -x]))));
  Add(gens, Bipartition(Concatenation([[1, n + 1, -1, - n - 1]],
                                        List([2 .. n], x -> [x, -x]))));
  return InverseMonoid(gens);
end);

InstallMethod(BrauerMonoid, "for an integer", [IsInt],
function(n)
  local gens, M;

  if n < 0 then
    ErrorNoReturn("the argument (an int) is not >= 0");
  elif n = 0 then
    return Monoid(Bipartition([]));
  elif n = 1 then
    return Monoid(Bipartition([[1, -1]]));
  fi;

  gens := List(GeneratorsOfGroup(SymmetricGroup(n)), x -> AsBipartition(x, n));
  Add(gens, Bipartition(Concatenation([[1, 2]],
                                        List([3 .. n],
                                             x -> [x, -x]), [[-1, -2]])));
  M := Monoid(gens);
  SetFilterObj(M, IsRegularActingSemigroupRep);
  SetIsStarSemigroup(M, true);
  return M;
end);

InstallMethod(PartialBrauerMonoid, "for an integer", [IsInt],
function(n)
  local S;

  if n < 0 then
    ErrorNoReturn("the argument (an int) is not >= 0");
  fi;

  S := Semigroup(BrauerMonoid(n),
                 AsSemigroup(IsBipartitionSemigroup,
                             SymmetricInverseMonoid(n)));
  SetFilterObj(S, IsRegularActingSemigroupRep);
  SetIsStarSemigroup(S, true);
  return S;
end);

InstallMethod(JonesMonoid, "for an integer",
[IsInt],
function(n)
  local gens, next, i, j, M;

  if n < 0 then
    ErrorNoReturn("the argument (an int) is not >= 0");
  elif n = 0 then
    return Monoid(Bipartition([]));
  elif n = 1 then
    return Monoid(Bipartition([[1, -1]]));
  fi;

  gens := [];
  for i in [1 .. n - 1] do
    next := [[i, i + 1], [-i, -i - 1]];
    for j in [1 .. i - 1] do
      Add(next, [j, -j]);
    od;
    for j in [i + 2 .. n] do
      Add(next, [j, -j]);
    od;
    Add(gens, Bipartition(next));
  od;

  M := Monoid(gens);
  SetFilterObj(M, IsRegularActingSemigroupRep);
  SetIsStarSemigroup(M, true);
  return M;
end);

InstallMethod(AnnularJonesMonoid, "for an integer", [IsInt],
function(n)
  local p, x, M, j;

  if n < 0 then
    ErrorNoReturn("the argument (an int) is not >= 0");
  elif n = 0 or n = 1 then
    return JonesMonoid(n);
  fi;

  p := PermList(Concatenation([n], [1 .. n - 1]));

  x := [[1, 2], [-1, -2]];
  for j in [3 .. n] do
    Add(x, [j, -j]);
  od;
  x := Bipartition(x);

  M := Monoid(x, AsBipartition(p));
  SetFilterObj(M, IsRegularActingSemigroupRep);
  SetIsStarSemigroup(M, true);
  return M;
end);

InstallMethod(PartialJonesMonoid, "for an integer",
[IsInt],
function(n)
  local gens, next, i, j, M;

  if n < 0 then
    ErrorNoReturn("the argument (an int) is not >= 0");
  elif n = 0 then
    return Monoid(Bipartition([]));
  elif n = 1 then
    return Monoid(Bipartition([[1, -1]]), Bipartition([[1], [-1]]));
  fi;

  gens := ShallowCopy(GeneratorsOfMonoid(JonesMonoid(n)));

  for i in [1 .. n] do
    next := [[i], [-i]];
    for j in [1 .. i - 1] do
      Add(next, [j, -j]);
    od;
    for j in [i + 1 .. n] do
      Add(next, [j, -j]);
    od;
    Add(gens, Bipartition(next));
  od;

  M := Monoid(gens);
  SetFilterObj(M, IsRegularActingSemigroupRep);
  SetIsStarSemigroup(M, true);
  return M;
end);

InstallMethod(MotzkinMonoid, "for an integer",
[IsInt],
function(n)
  local gens, M;

  if n < 0 then
    ErrorNoReturn("the argument (an int) is not >= 0");
  elif n = 0 then
    return Monoid(Bipartition([]));
  fi;

  gens := List(GeneratorsOfInverseSemigroup(POI(n)),
               x -> AsBipartition(x, n));
  M := Monoid(JonesMonoid(n), gens);
  SetFilterObj(M, IsRegularActingSemigroupRep);
  SetIsStarSemigroup(M, true);
  return M;
end);

InstallMethod(POI, "for a positive integer", [IsPosInt],
function(n)
  local out, i;

  if n = 1 then
    return SymmetricInverseMonoid(n);
  fi;

  out := EmptyPlist(n);
  out[1] := PartialPermNC([0 .. n - 1]);
  for i in [0 .. n - 2] do
    out[i + 2] := [1 .. n];
    out[i + 2][(n - i) - 1] := n - i;
    out[i + 2][n - i] := 0;
    out[i + 2] := PartialPermNC(out[i + 2]);
  od;
  return InverseMonoid(out);
end);

InstallMethod(POPI, "for a positive integer", [IsPosInt],
function(n)
  if n <= 2 then
    return SymmetricInverseMonoid(n);
  fi;
  return InverseMonoid(PartialPermNC(Concatenation([2 .. n], [1])),
                       PartialPermNC(Concatenation([1 .. n - 2], [n])));
end);

InstallMethod(PODI, "for a positive integer", [IsPosInt],
function(n)
  if n <= 2 then
    return SymmetricInverseMonoid(n);
  fi;
  return InverseMonoid(POI(n), PartialPerm(Reversed([1 .. n])));
end);

InstallMethod(PORI, "for a positive integer", [IsPosInt],
function(n)
  if n <= 3 then
    return SymmetricInverseMonoid(n);
  fi;
  return InverseMonoid(PartialPermNC(Concatenation([2 .. n], [1])),
                       PartialPermNC(Concatenation([1 .. n - 2], [n])),
                       PartialPerm(Reversed([1 .. n])));
end);

InstallMethod(PlanarUniformBlockBijectionMonoid, "for a positive integer",
[IsPosInt],
function(n)
  local gens, next, i, j;

  if n = 1 then
    return InverseMonoid(Bipartition([[1, -1]]));
  fi;

  gens := [];

  # (2,2)-transapsis generators
  for i in [1 .. n - 1] do
    next := [];
    for j in [1 .. i - 1] do
      next[j] := j;
      next[n + j] := j;
    od;
    next[i] := i;
    next[i + 1] := i;
    next[i + n] := i;
    next[i + n + 1] := i;
    for j in [i + 2 .. n] do
      next[j] := j - 1;
      next[n + j] := j - 1;
    od;
    gens[i] := BipartitionByIntRep(next);
  od;

  return InverseMonoid(gens);
end);

InstallMethod(UniformBlockBijectionMonoid, "for a positive integer",
[IsPosInt],
function(n)
  local gens;
  if n = 1 then
    return InverseMonoid(Bipartition([[1, -1]]));
  fi;

  gens := List(GeneratorsOfGroup(SymmetricGroup(n)), x -> AsBipartition(x, n));
  Add(gens, Bipartition(Concatenation([[1, 2, -1, -2]],
                                        List([3 .. n], x -> [x, -x]))));
  return InverseMonoid(gens);
end);

InstallMethod(PartialUniformBlockBijectionMonoid, "for a positive integer",
[IsPosInt],
function(n)
  local gens;
  if n = 1 then
    return InverseMonoid(Bipartition([[1, -1], [2, -2]]),
                         Bipartition([[1, 2, -1, -2]]));
  fi;

  gens := Set([PermList(Concatenation([2 .. n], [1])), (1, 2)]);
  gens := List(gens, x -> AsBipartition(x, n + 1));
  Add(gens, Bipartition(Concatenation([[1, 2, -1, -2]],
                                        List([3 .. n + 1], x -> [x, -x]))));
  Add(gens, Bipartition(Concatenation([[1, n + 1, -1, - n - 1]],
                                        List([2 .. n], x -> [x, -x]))));
  return InverseMonoid(gens);
end);

InstallMethod(RookPartitionMonoid, "for a positive integer", [IsPosInt],
function(n)
  local S;
  S := Monoid(PartialUniformBlockBijectionMonoid(n),
               Bipartition(Concatenation([[1], [-1]],
                                         List([2 .. n + 1], x -> [x, -x]))));
  SetFilterObj(S, IsRegularActingSemigroupRep);
  SetIsStarSemigroup(S, true);
  return S;
end);

InstallMethod(ApsisMonoid,
"for a positive integer and positive integer",
[IsPosInt, IsPosInt],
function(m, n)
  local gens, next, S, b, i, j;

  if n = 1 and m = 1 then
    return InverseMonoid(Bipartition([[1], [-1]]));
  fi;

  gens := [];

  if n < m then
    next := [];

    # degree k identity bipartition
    for i in [1 .. n] do
      next[i] := i;
      next[n + i] := i;
    od;
    gens[1] := BipartitionByIntRep(next);
    S := InverseMonoid(gens);
    SetFilterObj(S, IsRegularActingSemigroupRep);
    SetIsStarSemigroup(S, true);
    return S;
  fi;

  # m-apsis generators
  for i in [1 .. n - m + 1] do
    next := [];
    b := 1;

    for j in [1 .. i - 1] do
      next[j] := b;
      next[n + j] := b;
      b := b + 1;
    od;

    for j in [i .. i + m - 1] do
      next[j] := b;
    od;
    b := b + 1;

    for j in [i + m .. n] do
      next[j] := b;
      next[n + j] := b;
      b := b + 1;
    od;

    for j in [i .. i + m - 1] do
      next[n + j] := b;
    od;

    gens[i] := BipartitionByIntRep(next);
  od;

  S := Monoid(gens);
  SetFilterObj(S, IsRegularActingSemigroupRep);
  SetIsStarSemigroup(S, true);
  return S;
end);

InstallMethod(CrossedApsisMonoid,
"for a positive integer and positive integer",
[IsPosInt, IsPosInt],
function(m, n)
  local gens, S;

  if n = 1 then
    if m = 1 then
      return InverseMonoid(Bipartition([[1], [-1]]));
    else
      return InverseMonoid(Bipartition([[1, -1]]));
    fi;
  fi;

  gens := List(GeneratorsOfGroup(SymmetricGroup(n)), x -> AsBipartition(x, n));
  if m <= n then
    Add(gens, Bipartition(Concatenation([[1 .. m]],
                                          List([m + 1 .. n],
                                               x -> [x, -x]), [[-m .. -1]])));
  fi;

  S := Monoid(gens);
  SetFilterObj(S, IsRegularActingSemigroupRep);
  SetIsStarSemigroup(S, true);
  return S;
end);

InstallMethod(PlanarModularPartitionMonoid,
"for a positive integer and positive integer",
[IsPosInt, IsPosInt],
function(m, n)
  local gens, next, b, S, i, j;

  if n < m then
    return PlanarUniformBlockBijectionMonoid(n);
  elif n = 1 then
    return InverseMonoid(Bipartition([[1], [-1]]));
  fi;

  gens := [];

  # (2,2)-transapsis generators
  for i in [1 .. n - 1] do
    next := [];
    for j in [1 .. i - 1] do
      next[j] := j;
      next[n + j] := j;
    od;
    next[i] := i;
    next[i + 1] := i;
    next[i + n] := i;
    next[i + n + 1] := i;
    for j in [i + 2 .. n] do
      next[j] := j - 1;
      next[n + j] := j - 1;
    od;
    gens[i] := BipartitionByIntRep(next);
  od;

  # m-apsis generators
  for i in [1 .. n - m + 1] do
    next := [];
    b := 1;

    for j in [1 .. i - 1] do
      next[j] := b;
      next[n + j] := b;
      b := b + 1;
    od;

    for j in [i .. i + m - 1] do
      next[j] := b;
    od;
    b := b + 1;

    for j in [i + m .. n] do
      next[j] := b;
      next[n + j] := b;
      b := b + 1;
    od;

    for j in [i .. i + m - 1] do
      next[n + j] := b;
    od;

    gens[n - 1 + i] := BipartitionByIntRep(next);
  od;

  S := Monoid(gens);
  SetFilterObj(S, IsRegularActingSemigroupRep);
  SetIsStarSemigroup(S, true);
  return S;
end);

InstallMethod(PlanarPartitionMonoid, "for a positive integer",
[IsPosInt], n -> PlanarModularPartitionMonoid(1, n));

InstallMethod(ModularPartitionMonoid,
"for a positive integer and positive integer",
[IsPosInt, IsPosInt],
function(m, n)
  local gens, S;

  if n = 1 then
    return InverseMonoid(Bipartition([[1], [-1]]));
  fi;

  gens := List(GeneratorsOfGroup(SymmetricGroup(n)), x -> AsBipartition(x, n));
  Add(gens, Bipartition(Concatenation([[1, 2, -1, -2]],
                                        List([3 .. n], x -> [x, -x]))));
  if m <= n then
    Add(gens, Bipartition(Concatenation([[1 .. m]],
                                          List([m + 1 .. n],
                                               x -> [x, -x]), [[-m .. -1]])));
  fi;
  S := Monoid(gens);
  SetFilterObj(S, IsRegularActingSemigroupRep);
  SetIsStarSemigroup(S, true);
  return S;
end);

InstallMethod(SingularPartitionMonoid, "for a positive integer",
[IsPosInt],
function(n)
  local blocks, i;

  if n = 1 then
    return SemigroupIdeal(PartitionMonoid(1), Bipartition([[1], [-1]]));
  fi;

  blocks := [[1, 2, -1, -2]];
  for i in [3 .. n] do
    blocks[i - 1] := [i, -i];
  od;
  return SemigroupIdeal(PartitionMonoid(n), Bipartition(blocks));
end);

InstallMethod(SingularTransformationSemigroup, "for a positive integer",
[IsPosInt],
function(n)
  local x, S;
  if n = 1 then
    ErrorNoReturn("the argument (an int) is not > 1");
  fi;
  x := TransformationNC(Concatenation([1 .. n - 1], [n - 1]));
  S := FullTransformationSemigroup(n);
  return SemigroupIdeal(S, x);
end);

InstallMethod(SingularOrderEndomorphisms, "for a positive integer",
[IsPosInt],
function(n)
  local x, S;
  if n = 1 then
    ErrorNoReturn("the argument (an int) is not > 1");
  fi;
  x := TransformationNC(Concatenation([1 .. n - 1], [n - 1]));
  S := OrderEndomorphisms(n);
  return SemigroupIdeal(S, x);
end);

InstallMethod(SingularBrauerMonoid, "for a positive integer",
[IsPosInt],
function(n)
  local blocks, x, S, i;

  if n = 1 then
    ErrorNoReturn("the argument (an int) is not > 1");
  fi;

  blocks := [[1, 2], [-1, -2]];
  for i in [3 .. n] do
    blocks[i] := [i, -i];
  od;
  x := Bipartition(blocks);
  S := BrauerMonoid(n);
  return SemigroupIdeal(S, x);
end);

InstallMethod(SingularJonesMonoid, "for a positive integer",
[IsPosInt],
function(n)
  local blocks, x, S, i;
  if n = 1 then
    ErrorNoReturn("the argument (an int) is not > 1");
  fi;

  blocks := [[1, 2], [-1, -2]];
  for i in [3 .. n] do
    blocks[i] := [i, -i];
  od;
  x := Bipartition(blocks);
  S := JonesMonoid(n);
  return SemigroupIdeal(S, x);
end);

InstallMethod(SingularDualSymmetricInverseMonoid, "for a positive integer",
[IsPosInt],
function(n)
  local blocks, x, S, i;
  if n = 1 then
    ErrorNoReturn("the argument (an int) is not > 1");
  fi;

  blocks := [[1, 2, -1, -2]];
  for i in [3 .. n] do
    blocks[i - 1] := [i, -i];
  od;
  x := Bipartition(blocks);
  S := DualSymmetricInverseMonoid(n);
  return SemigroupIdeal(S, x);
end);

InstallMethod(SingularPlanarUniformBlockBijectionMonoid,
"for a positive integer", [IsPosInt],
function(n)
  local blocks, x, S, i;
  if n = 1 then
    ErrorNoReturn("the argument (an int) is not > 1");
  fi;

  blocks := [[1, 2, -1, -2]];
  for i in [3 .. n] do
    blocks[i - 1] := [i, -i];
  od;

  x := Bipartition(blocks);
  S := PlanarUniformBlockBijectionMonoid(n);
  return SemigroupIdeal(S, x);
end);

InstallMethod(SingularUniformBlockBijectionMonoid,
"for a positive integer", [IsPosInt],
function(n)
  local blocks, x, S, i;
  if n = 1 then
    ErrorNoReturn("the argument (an int) is not > 1");
  fi;

  blocks := [[1, 2, -1, -2]];
  for i in [3 .. n] do
    blocks[i - 1] := [i, -i];
  od;

  x := Bipartition(blocks);
  S := UniformBlockBijectionMonoid(n);
  return SemigroupIdeal(S, x);
end);

InstallMethod(SingularApsisMonoid,
"for a positive integer and positive integer",
[IsPosInt, IsPosInt],
function(m, n)
  local blocks, x, S, i;
  if m > n then
    ErrorNoReturn("the 1st argument (a pos. int.) is not <= to the ",
                  "2nd argument (a pos. int.)");
  fi;

  blocks := [[1 .. m], [-m .. -1]];
  for i in [m + 1 .. n] do
    blocks[i - m + 2] := [i, -i];
  od;

  x := Bipartition(blocks);
  S := ApsisMonoid(m, n);
  return SemigroupIdeal(S, x);
end);

InstallMethod(SingularCrossedApsisMonoid,
"for a positive integer and positive integer",
[IsPosInt, IsPosInt],
function(m, n)
  local blocks, x, S, i;
  if m > n then
    ErrorNoReturn("the 1st argument (a pos. int.) is not <= to the ",
                  "2nd argument (a pos. int.)");
  fi;

  blocks := [[1 .. m], [-m .. -1]];
  for i in [m + 1 .. n] do
    blocks[i - m + 2] := [i, -i];
  od;

  x := Bipartition(blocks);
  S := CrossedApsisMonoid(m, n);
  return SemigroupIdeal(S, x);
end);

InstallMethod(SingularPlanarModularPartitionMonoid,
"for a positive integer and positive integer",
[IsPosInt, IsPosInt],
function(m, n)
  local blocks, x, S, i;
  if n = 1 then
    if m = 1 then
      return SemigroupIdeal(PlanarModularPartitionMonoid(1, 1),
                            Bipartition([[1], [-1]]));
    else
      ErrorNoReturn("the 2nd argument (a pos. int.) must be > 1",
                    " when the 1st argument (a pos. int.) is also > 1");
    fi;
  fi;

  blocks := [[1, 2, -1, -2]];
  for i in [3 .. n] do
    blocks[i - 1] := [i, -i];
  od;

  x := Bipartition(blocks);
  S := PlanarModularPartitionMonoid(m, n);
  return SemigroupIdeal(S, x);
end);

InstallMethod(SingularPlanarPartitionMonoid, "for a positive integer",
[IsPosInt],
function(n)
  local blocks, x, S, i;
  if n = 1 then
    return SemigroupIdeal(PlanarPartitionMonoid(1), Bipartition([[1], [-1]]));
  fi;

  blocks := [[1, 2, -1, -2]];
  for i in [3 .. n] do
    blocks[i - 1] := [i, -i];
  od;

  x := Bipartition(blocks);
  S := PlanarPartitionMonoid(n);
  return SemigroupIdeal(S, x);
end);

InstallMethod(SingularModularPartitionMonoid,
"for a positive integer and positive integer",
[IsPosInt, IsPosInt],
function(m, n)
  local blocks, x, S, i;
  if n = 1 then
    if m = 1 then
      return SemigroupIdeal(ModularPartitionMonoid(1, 1),
                            Bipartition([[1], [-1]]));
    else
      ErrorNoReturn("the 2nd argument (a pos. int.) must be > 1",
                    " when the 1st argument (a pos. int.) is also > 1");
    fi;
  fi;

  blocks := [[1, 2, -1, -2]];
  for i in [3 .. n] do
    blocks[i - 1] := [i, -i];
  od;

  x := Bipartition(blocks);
  S := ModularPartitionMonoid(m, n);
  return SemigroupIdeal(S, x);
end);

#############################################################################
## 2. Standard examples - known generators
#############################################################################

InstallMethod(RegularBooleanMatMonoid, "for a pos int",
[IsPosInt],
function(n)
  local gens, i, j;

  if n = 1 then
    return Monoid(BooleanMat([[true]]), BooleanMat([[false]]));
  elif n = 2 then
    return Monoid(Matrix(IsBooleanMat, [[0, 1], [1, 0]]),
                  Matrix(IsBooleanMat, [[1, 0], [0, 0]]),
                  Matrix(IsBooleanMat, [[1, 0], [1, 1]]));
  fi;

  gens := [];

  gens[2] := List([1 .. n], x -> BlistList([1 .. n], []));
  for j in [1 .. n - 1] do
    gens[2][j][j + 1] := true;
  od;
  gens[2][n][1] := true;

  for i in [3, 4] do
    gens[i] := List([1 .. n], x -> BlistList([1 .. n], []));
    for j in [1 .. n - 1] do
      gens[i][j][j] := true;
    od;
  od;
  gens[3][n][1] := true;
  gens[3][n][n] := true;

  Apply(gens, BooleanMat);

  gens[1] := AsBooleanMat((1, 2), n);

  return Monoid(gens);
end);

InstallMethod(GossipMonoid, "for a positive integer",
[IsPosInt],
function(n)
  local gens, i, j, x, m;

  if n = 1 then
    return Semigroup(Matrix(IsBooleanMat, [[true]]));
  fi;

  gens := [];
  for i in [1 .. n - 1] do
    for j in [i + 1 .. n] do
      x := List([1 .. n], k -> BlistList([1 .. n], [k]));
      x[i][j] := true;
      x[j][i] := true;
      Add(gens, BooleanMat(x));
    od;
  od;

  m := Monoid(gens);
  SetNrIdempotents(m, Bell(n));
  return m;
end);

InstallMethod(UnitriangularBooleanMatMonoid, "for a positive integer",
[IsPosInt],
function(n)
  local gens, x, i, j;

  if n = 1 then
    return Semigroup(Matrix(IsBooleanMat, [[true]]));
  fi;

  gens := [];
  for i in [1 .. n - 1] do
    for j in [i + 1 .. n] do
      x := List([1 .. n], k -> BlistList([1 .. n], [k]));
      x[i][j] := true;
      Add(gens, BooleanMat(x));
    od;
  od;

  return Monoid(gens);
end);

InstallMethod(TriangularBooleanMatMonoid, "for a positive integer",
[IsPosInt],
function(n)
  local gens, x, i;

  if n = 1 then
    return Semigroup(Matrix(IsBooleanMat, [[true]]));
  fi;

  gens := [];
  for i in [1 .. n] do
    x := List([1 .. n], k -> BlistList([1 .. n], [k]));
    x[i][i] := false;
    Add(gens, BooleanMat(x));
  od;

  return Monoid(UnitriangularBooleanMatMonoid(n), gens);
end);

#############################################################################
## 3. Standard examples - calculated generators
#############################################################################

InstallMethod(ReflexiveBooleanMatMonoid, "for a positive integer",
[IsPosInt],
function(n)
  if not IsBound(SEMIGROUPS.GENERATORS.Reflex) then
    SEMIGROUPS.GENERATORS.Reflex :=
      ReadGenerators(Concatenation(SEMIGROUPS.PackageDir,
                                   "/data/gens/reflex.pickle.gz"));
  fi;

  if n = 6 and not IsBound(SEMIGROUPS.GENERATORS.Reflex[6]) then
    Info(InfoSemigroups, 2, "reading generators; this may take some time");
    Add(SEMIGROUPS.GENERATORS.Reflex,
        ReadGenerators(Concatenation(SEMIGROUPS.PackageDir,
                                   "/data/gens/reflex-6.pickle.gz")));
  fi;

  if not IsBound(SEMIGROUPS.GENERATORS.Reflex[n]) then
    ErrorNoReturn("generators for this monoid are only provided up to ",
                  "dimension 6");
  fi;

  return Monoid(SEMIGROUPS.GENERATORS.Reflex[n]);
end);

InstallMethod(HallMonoid, "for a positive integer",
[IsPosInt],
function(n)
  local gens, p;

  if not IsBound(SEMIGROUPS.GENERATORS.Hall) then
    SEMIGROUPS.GENERATORS.Hall :=
      ReadGenerators(Concatenation(SEMIGROUPS.PackageDir,
                                   "/data/gens/hall.pickle.gz"));
  fi;

  if n = 8 then
    gens := GeneratorsOfSemigroup(FullBooleanMatMonoid(8));
    p := PositionProperty(gens,
                           x -> ListWithIdenticalEntries(8, false)
                                in AsList(x));
    return Monoid(gens{[1 .. p - 1]}, gens{[p + 1 .. Length(gens)]});
  fi;

  if not IsBound(SEMIGROUPS.GENERATORS.Hall[n]) then
    ErrorNoReturn("generators for this monoid are only known up to dimension ",
                  "8");
  fi;

  return Monoid(SEMIGROUPS.GENERATORS.Hall[n]);
end);

InstallMethod(FullBooleanMatMonoid, "for a positive integer",
[IsPosInt],
function(n)
  if not IsBound(SEMIGROUPS.GENERATORS.FullBool) then
    SEMIGROUPS.GENERATORS.FullBool :=
      ReadGenerators(Concatenation(SEMIGROUPS.PackageDir,
                                   "/data/gens/fullbool.pickle.gz"));
  fi;

  if n = 8 and not IsBound(SEMIGROUPS.GENERATORS.FullBool[8]) then
    Info(InfoSemigroups, 2, "reading generators; this may take some time");
    Add(SEMIGROUPS.GENERATORS.FullBool,
        ReadGenerators(Concatenation(SEMIGROUPS.PackageDir,
                                   "/data/gens/fullbool-8.pickle.gz")));
  fi;

  if not IsBound(SEMIGROUPS.GENERATORS.FullBool[n]) then
    ErrorNoReturn("generators for this monoid are only known up to dimension ",
                  "8");
  fi;

  return Monoid(SEMIGROUPS.GENERATORS.FullBool[n]);
end);

#############################################################################
## Tropical matrix monoids
#############################################################################

InstallMethod(FullTropicalMaxPlusMonoid, "for pos int and pos int",
[IsPosInt, IsPosInt],
function(dim, threshold)
  local gens, i, j;

  if dim <> 2 then
    ErrorNoReturn("the 1st argument (dimension) must be 2");
  fi;

  gens := [Matrix(IsTropicalMaxPlusMatrix, [[-infinity, 0],
                                            [-infinity, -infinity]],
                                            threshold),
           Matrix(IsTropicalMaxPlusMatrix, [[-infinity, 0],
                                            [0, -infinity]],
                                            threshold),
           Matrix(IsTropicalMaxPlusMatrix, [[-infinity, 0],
                                            [0, 0]],
                                            threshold),
           Matrix(IsTropicalMaxPlusMatrix, [[-infinity, 1],
                                            [0, -infinity]],
                                            threshold)];

  for i in [1 .. threshold] do
    Add(gens, Matrix(IsTropicalMaxPlusMatrix,
                     [[-infinity, 0], [0, i]],
                     threshold));
    for j in [1 .. i] do
      Add(gens, Matrix(IsTropicalMaxPlusMatrix,
                       [[0, j], [i, 0]],
                       threshold));
    od;
  od;

  return Monoid(gens);
end);

InstallMethod(FullTropicalMinPlusMonoid, "for pos int and pos int",
[IsPosInt, IsPosInt],
function(dim, threshold)
  local gens, i, j, k;

  if dim = 2  then
    gens := [Matrix(IsTropicalMinPlusMatrix, [[infinity, 0],
                                              [0, infinity]],
                                              threshold),
             Matrix(IsTropicalMinPlusMatrix, [[infinity, 0],
                                              [1, infinity]],
                                              threshold),
             Matrix(IsTropicalMinPlusMatrix, [[infinity, 0],
                                              [infinity, infinity]],
                                              threshold)];
    for i in [0 .. threshold] do
      Add(gens, Matrix(IsTropicalMinPlusMatrix,
                       [[infinity, 0], [0, i]],
                       threshold));
    od;
  elif dim = 3 then
    gens := [Matrix(IsTropicalMinPlusMatrix,
                    [[infinity, infinity, 0],
                     [0, infinity, infinity],
                     [infinity, 0, infinity]],
                    threshold),
             Matrix(IsTropicalMinPlusMatrix,
                    [[infinity, infinity, 0],
                     [infinity, 0, infinity],
                     [0, infinity, infinity]],
                    threshold),
             Matrix(IsTropicalMinPlusMatrix,
                    [[infinity, infinity, 0],
                     [infinity, 0, infinity],
                     [infinity, infinity, infinity]],
                    threshold),
             Matrix(IsTropicalMinPlusMatrix,
                    [[infinity, infinity, 0],
                     [infinity, 0, infinity],
                     [1, infinity, infinity]],
                    threshold)];

    for i in [0 .. threshold] do
      Add(gens, Matrix(IsTropicalMinPlusMatrix,
                       [[infinity, infinity, 0],
                        [infinity, 0, infinity],
                        [0, i, infinity]],
                       threshold));
      Add(gens, Matrix(IsTropicalMinPlusMatrix,
                       [[infinity, 0, i],
                        [i, infinity, 0],
                        [0, i, infinity]],
                        threshold));
      for j in [1 .. i] do
        Add(gens, Matrix(IsTropicalMinPlusMatrix,
                         [[infinity, 0, 0],
                          [0, infinity, i],
                          [0, j, infinity]],
                         threshold));
      od;

      for j in [1 .. threshold] do
        Add(gens, Matrix(IsTropicalMinPlusMatrix,
                         [[infinity, 0, 0],
                          [0, infinity, i],
                          [j, 0, infinity]],
                         threshold));
      od;
    od;

    for i in [1 .. threshold] do
      for j in [i .. threshold] do
        for k in [1 .. j - 1] do
          Add(gens, Matrix(IsTropicalMinPlusMatrix,
                           [[infinity, 0, i],
                            [j, infinity, 0],
                            [0, k, infinity]],
                           threshold));
        od;
      od;
    od;
  else
    ErrorNoReturn("the 1st argument (dimension) must be 2 or 3");
  fi;

  return Monoid(gens);
end);

########################################################################
# PBR monoids
########################################################################

InstallMethod(FullPBRMonoid, "for a positive integer", [IsPosInt],
function(n)
  local gens;

  gens := [[PBR([[]], [[1]]), PBR([[-1, 1]], [[1]]),
            PBR([[-1]], [[]]), PBR([[-1]], [[1]]),
            PBR([[-1]], [[-1, 1]])],

           [PBR([[], [-1]], [[2], [-2, 1]]),
            PBR([[-2, 1], [-1]], [[2], []]),
            PBR([[-1, 2], [-2]], [[1], [2]]),
            PBR([[-1], [-2]], [[1], [-2, 2]]),
            PBR([[-2], [2]], [[1], [2]]),
            PBR([[-2], [-1]], [[1], [1, 2]]),
            PBR([[-2], [-1]], [[1], [2]]),
            PBR([[-2], [-1]], [[1], [-2]]),
            PBR([[-2], [-1]], [[2], [1]]),
            PBR([[-2], [-2, -1]], [[1], [2]])]];

  if n > 2 then
    ErrorNoReturn("the argument (a pos. int.) must be at most 2");
  fi;
  return Monoid(gens[n]);
end);
