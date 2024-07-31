#############################################################################
##
##  semigroups/semitrans.gi
##  Copyright (C) 2013-2022                              James D. Mitchell
##
##  Licensing information can be found in the README file of this package.
##
#############################################################################
##

# This file contains methods for every operation/attribute/property that is
# specific to transformation semigroups.

#############################################################################
## Random
#############################################################################

InstallMethod(SEMIGROUPS_ProcessRandomArgsCons,
[IsTransformationSemigroup, IsList],
{_, params} -> SEMIGROUPS_ProcessRandomArgsCons(IsSemigroup, params));

InstallMethod(SEMIGROUPS_ProcessRandomArgsCons,
[IsTransformationMonoid, IsList],
{_, params} -> SEMIGROUPS_ProcessRandomArgsCons(IsSemigroup, params));

InstallMethod(RandomSemigroupCons, "for IsTransformationSemigroup and a list",
[IsTransformationSemigroup, IsList],
function(_, params)
  return Semigroup(List([1 .. params[1]], i ->
                   RandomTransformation(params[2])));
end);

InstallMethod(RandomMonoidCons, "for IsTransformationMonoid and a list",
[IsTransformationMonoid, IsList],
{_, params}
-> Monoid(List([1 .. params[1]], i -> RandomTransformation(params[2]))));

InstallMethod(RandomInverseSemigroupCons,
"for IsTransformationSemigroup and a list",
[IsTransformationSemigroup, IsList],
SEMIGROUPS.DefaultRandomInverseSemigroup);

InstallMethod(RandomInverseMonoidCons,
"for IsTransformationMonoid and a list",
[IsTransformationMonoid, IsList],
SEMIGROUPS.DefaultRandomInverseMonoid);

#############################################################################
## Operators
#############################################################################

InstallMethod(\<, "for transformation semigroups",
[IsTransformationSemigroup, IsTransformationSemigroup],
function(S, T)
  if DegreeOfTransformationSemigroup(S)
      <> DegreeOfTransformationSemigroup(T) then
    return DegreeOfTransformationSemigroup(S)
      < DegreeOfTransformationSemigroup(T);
  fi;
  TryNextMethod();
end);

InstallMethod(\^, "for a transformation semigroup with generators and perm",
[IsTransformationCollection, IsPerm],
{coll, p} -> List(coll, x -> x ^ p));

InstallMethod(\^, "for a transformation semigroup with generators and perm",
[IsTransformationSemigroup and HasGeneratorsOfSemigroup, IsPerm],
{S, p} -> Semigroup(GeneratorsOfSemigroup(S) ^ p));

#############################################################################
## Isomorphisms
#############################################################################

InstallMethod(IsomorphismSemigroup,
"for IsTransformationSemigroup and a semigroup",
[IsTransformationSemigroup, IsSemigroup],
{_, S} -> IsomorphismTransformationSemigroup(S));

InstallMethod(IsomorphismMonoid,
"for IsTransformationMonoid and a semigroup",
[IsTransformationMonoid, IsSemigroup],
{_, S} -> IsomorphismTransformationMonoid(S));

# TODO(later) AntiIsomorphismTransformationSemigroup using LeftCayleyGraph

InstallMethod(IsomorphismTransformationSemigroup,
"for a semigroup with CanUseFroidurePin",
[CanUseFroidurePin],
ToBeat([CanUseFroidurePin], [IsFpMonoid]),
function(S)
  local cay, deg, gen, next, T, i, iso, inv;
  if not IsFinite(S) then
    ErrorNoReturn("the argument (a semigroup) is not finite");
  elif IsPartialPermSemigroup(S) or IsTransformationSemigroup(S) then
    # Apparently this clause is required in GAP 4.10
    TryNextMethod();
  fi;

  cay := OutNeighbours(RightCayleyDigraph(S));
  deg := Size(S);
  gen := [];

  for i in [1 .. Length(cay[1])] do
    next := List([1 .. deg], j -> cay[j][i]);
    if MultiplicativeNeutralElement(S) = fail then
      Add(next, i);
    fi;
    Add(gen, Transformation(next));
  od;

  T := Semigroup(gen);
  UseIsomorphismRelation(S, T);

  iso := x -> EvaluateWord(gen, MinimalFactorization(S, x));
  inv := x -> EvaluateWord(GeneratorsOfSemigroup(S), Factorization(T, x));

  return SemigroupIsomorphismByFunctionNC(S, T, iso, inv);
end);

InstallMethod(IsomorphismTransformationSemigroup,
"for a boolean matrix semigroup with generators",
[IsBooleanMatSemigroup and HasGeneratorsOfSemigroup],
SUM_FLAGS,
function(S)
  local T, map, inv, n, pts, o, pos, i;
  n := Length(Representative(S)![1]);
  if ForAll(GeneratorsOfSemigroup(S), IsTransformationBooleanMat) then
    T := Semigroup(List(GeneratorsOfSemigroup(S), AsTransformation));
    map := AsTransformation;
    inv := x -> AsBooleanMat(x, n);
  else
    pts := [];
    for i in [1 .. n] do
      o := Enumerate(Orb(S, BlistList([1 .. n], [i]), OnBlist));
      pts := Union(pts, AsList(o));
    od;
    pos := List([1 .. n], x -> Position(pts, BlistList([1 .. n], [x])));
    T := Semigroup(List(GeneratorsOfSemigroup(S),
                        x -> TransformationOpNC(x, pts, OnBlist)));
    map := x -> TransformationOpNC(x, pts, OnBlist);
    inv := x -> BooleanMat(List([1 .. n], i -> pts[pos[i] ^ x]));
  fi;
  UseIsomorphismRelation(S, T);

  return SemigroupIsomorphismByFunctionNC(S, T, map, inv);
end);

InstallMethod(IsomorphismTransformationSemigroup,
"for a bipartition semigroup with generators",
[IsBipartitionSemigroup and HasGeneratorsOfSemigroup],
function(S)
  local T, n;

  if not ForAll(GeneratorsOfSemigroup(S), IsTransBipartition) then
    TryNextMethod();
  fi;

  T := Semigroup(List(GeneratorsOfSemigroup(S), AsTransformation));
  n := DegreeOfBipartitionSemigroup(S);
  UseIsomorphismRelation(S, T);

  return SemigroupIsomorphismByFunctionNC(S,
                                          T,
                                          AsTransformation,
                                          x -> AsBipartition(x, n));
end);

InstallMethod(IsomorphismTransformationSemigroup,
"for semigroup of binary relations with generators",
[IsSemigroup and IsGeneralMappingCollection and HasGeneratorsOfSemigroup],
function(S)
  local n, pts, o, pos, T, map, inv, i;

  if not IsBinaryRelationOnPointsRep(Representative(S)) then
    TryNextMethod();
  fi;
  n := DegreeOfBinaryRelation(GeneratorsOfSemigroup(S)[1]);
  pts := EmptyPlist(2 ^ n);

  for i in [1 .. n] do
    o := Orb(S, [i], OnPoints);
    Enumerate(o);
    pts := Union(pts, AsList(o));
  od;
  ShrinkAllocationPlist(pts);
  pos := List([1 .. n], x -> Position(pts, [x]));
  T := Semigroup(List(GeneratorsOfSemigroup(S),
                 x -> TransformationOpNC(x, pts, OnPoints)));

  map := x -> TransformationOpNC(x, pts, OnPoints);
  inv := x -> BinaryRelationOnPoints(List([1 .. n], i -> pts[pos[i] ^ x]));
  return SemigroupIsomorphismByFunctionNC(S, T, map, inv);
end);

# The next method is copied directly from the GAP library the only change is
# the return value which uses SemigroupIsomorphismByFunctionNC here but
# MagmaIsomorphismByFunctionsNC in the GAP library.

InstallMethod(IsomorphismTransformationMonoid, "for a semigroup",
[IsSemigroup],
1,  # to beat the GAP library version
function(S)
  local iso1, inv1, iso2, inv2;
  if MultiplicativeNeutralElement(S) = fail then
      ErrorNoReturn("the argument must be a semigroup with a ",
                    "multiplicative neutral element");
  fi;
  iso1 := IsomorphismTransformationSemigroup(S);
  inv1 := InverseGeneralMapping(iso1);
  iso2 := IsomorphismTransformationMonoid(Range(iso1));
  inv2 := InverseGeneralMapping(iso2);
  UseIsomorphismRelation(S, Range(iso2));
  return SemigroupIsomorphismByFunctionNC(S,
                                          Range(iso2),
                                          x -> (x ^ iso1) ^ iso2,
                                          x -> (x ^ inv2) ^ inv1);
end);

# The next method is copied directly from the GAP library the only change is
# the return value which uses SemigroupIsomorphismByFunctionNC here but
# MagmaIsomorphismByFunctionsNC in the GAP library.

InstallMethod(IsomorphismTransformationMonoid,
"for a transformation semigroup with known generators",
[IsTransformationSemigroup and HasGeneratorsOfSemigroup],
1,  # to beat the GAP library version
function(S)
  local id, dom, T, inv;
  if IsMonoid(S) then
    return SemigroupIsomorphismByFunctionNC(S, S, IdFunc, IdFunc);
  elif MultiplicativeNeutralElement(S) = fail then
    ErrorNoReturn("the argument must be a semigroup with a ",
                  "multiplicative neutral element");
  fi;
  id := MultiplicativeNeutralElement(S);
  dom := ImageSetOfTransformation(id, DegreeOfTransformationSemigroup(S));
  T := Monoid(List(GeneratorsOfSemigroup(S), x -> TransformationOp(x, dom)));
  UseIsomorphismRelation(S, T);
  inv := function(x)
    local out, i;
    out := [1 .. DegreeOfTransformationSemigroup(S)];
    for i in [1 .. Length(dom)] do
      out[dom[i]] := dom[i ^ x];
    od;
    return id * Transformation(out);
  end;
  return SemigroupIsomorphismByFunctionNC(S,
                                          T,
                                          x -> TransformationOp(x, dom),
                                          inv);
end);

# The next method is copied directly from the GAP library the only change is
# the return value which uses SemigroupIsomorphismByFunctionNC here but
# MagmaIsomorphismByFunctionsNC in the GAP library.

InstallMethod(IsomorphismTransformationSemigroup, "for partial perm semigroup",
[IsPartialPermSemigroup],
function(S)
  local n, T, inv;

  n := Maximum(DegreeOfPartialPermCollection(S),
               CodegreeOfPartialPermCollection(S)) + 1;

  T := Semigroup(List(GeneratorsOfSemigroup(S), x -> AsTransformation(x, n)));
  UseIsomorphismRelation(S, T);

  inv := function(x)
    local out, j, i;
    out := [];
    for i in [1 .. n - 1] do
      j := i ^ x;
      if j <> n then
        out[i] := j;
      else
        out[i] := 0;
      fi;
    od;
    return PartialPerm(out);
  end;

  return SemigroupIsomorphismByFunctionNC(S,
                                          T,
                                          x -> AsTransformation(x, n),
                                          inv);
end);

#############################################################################
## Algebraic attributes
#############################################################################

# same method for ideals

InstallMethod(GroupOfUnits, "for a transformation semigroup",
[IsTransformationSemigroup],
function(S)
  local H, map, G, U, iso;

  if MultiplicativeNeutralElement(S) = fail then
    return fail;
  fi;

  H := GreensHClassOfElementNC(S, MultiplicativeNeutralElement(S));
  map := InverseGeneralMapping(IsomorphismPermGroup(H));
  G := Source(map);
  U := Semigroup(List(GeneratorsOfGroup(G), x -> x ^ map));
  SetIsGroupAsSemigroup(U, true);
  UseIsomorphismRelation(U, G);

  iso := SemigroupIsomorphismByFunctionNC(U,
                                          G,
                                          PermutationOfImage,
                                          x -> x ^ map);
  SetIsomorphismPermGroup(U, iso);

  return U;
end);

# can probably do better than this

InstallMethod(Idempotents, "for a transformation semigroup and pos int",
[IsTransformationSemigroup, IsPosInt],
function(S, rank)
  local deg;
  deg := DegreeOfTransformationSemigroup(S);
  if rank > deg then
    return [];
  fi;
  return Filtered(Idempotents(S),
                              x -> RankOfTransformation(x, deg) = rank);
end);

#############################################################################
## Degree
#############################################################################

InstallMethod(DegreeOfTransformationCollection,
"for a transformation semigroup",
[IsTransformationSemigroup], DegreeOfTransformationSemigroup);

InstallMethod(DegreeOfTransformationSemigroup,
"for a transformation semigroup ideal",
[IsTransformationSemigroup and IsSemigroupIdeal],
I -> DegreeOfTransformationSemigroup(SupersemigroupOfIdeal(I)));

#############################################################################
## Action on points and pairs
#############################################################################

InstallMethod(DigraphOfAction,
"for a transformation collection, list, and action",
[IsTransformationCollection, IsList, IsFunction],
function(coll, list, act)
  local n, map, out, in_, labels, genstoapply, i, y, index, D, j;

  # TODO(later) arg checks

  n := Length(list);
  if n = 0 then
    return EmptyDigraph(n);
  fi;

  map := HashMap(Length(list));
  for i in [1 .. Length(list)] do
    map[list[i]] := i;
  od;

  # We track the out-neighbours and in-neighbours because at least one
  # application (finding the representative of the minimal ideal) requires
  # this.
  out         := List([1 .. n], x -> []);
  in_         := List([1 .. n], x -> []);
  labels      := List([1 .. n], x -> []);
  genstoapply := [1 .. Length(coll)];

  i := 1;
  repeat
    for j in genstoapply do
      y := act(list[i], coll[j]);
      if y <> fail then
        index := map[y];
        if index = fail then
          n := n + 1;
          list[n] := y;
          map[y] := n;
          Add(out, []);
          Add(in_, []);
          Add(labels, []);
          index := n;
        fi;
        if not i in in_[index] then
          Add(out[i], index);
          Add(in_[index], i);
          Add(labels[i], j);
        fi;
      fi;
    od;
    i := i + 1;
  until i > n;

  D := DigraphNC(out);
  SetDigraphVertexLabels(D, list);
  SetDigraphEdgeLabelsNC(D, labels);
  SetInNeighbours(D, in_);
  return D;
end);

InstallMethod(DigraphOfAction,
"for a transformation semigroup with generators, list, and action",
[IsTransformationSemigroup and HasGeneratorsOfSemigroup, IsList, IsFunction],
{S, list, act} -> DigraphOfAction(GeneratorsOfSemigroup(S), list, act));

InstallMethod(DigraphOfActionOnPoints,
"for a transformation collection and int",
[IsTransformationCollection, IsInt],
function(coll, n)
  local act;

  if n < 0 then
    ErrorNoReturn("the 2nd argument (an integer) must be non-negative");
  fi;

  act := function(pt, x)
    local y;
    y := OnPoints(pt, x);
    if y >= 1 and y <= n then
      return y;
    fi;
    return fail;
  end;

  return DigraphOfAction(coll, [1 .. n], act);
end);

InstallMethod(DigraphOfActionOnPoints,
"for a transformation semigroup with known generators and int",
[IsTransformationSemigroup and HasGeneratorsOfSemigroup, IsInt],
{S, n} -> DigraphOfActionOnPoints(GeneratorsOfSemigroup(S), n));

InstallMethod(DigraphOfActionOnPoints,
"for a transformation semigroup with known generators",
[IsTransformationSemigroup and HasGeneratorsOfSemigroup],
S -> DigraphOfActionOnPoints(S, DegreeOfTransformationSemigroup(S)));

InstallMethod(FixedPointsOfTransformationSemigroup,
"for a transformation semigroup with generators",
[IsTransformationSemigroup and HasGeneratorsOfSemigroup],
function(S)
  local n, gens;
  n    := DegreeOfTransformationSemigroup(S);
  gens := GeneratorsOfSemigroup(S);
  return Filtered([1 .. n], i -> ForAll(gens, x -> i ^ x = i));
end);

InstallMethod(MovedPoints, "for a transformation semigroup with generators",
[IsTransformationSemigroup and HasGeneratorsOfSemigroup],
function(S)
  return Difference([1 .. DegreeOfTransformationSemigroup(S)],
                    FixedPointsOfTransformationSemigroup(S));
end);

InstallMethod(IsConnectedTransformationSemigroup,
"for a transformation semigroup",
[IsTransformationSemigroup],
S -> IsConnectedDigraph(DigraphOfActionOnPoints(S)));

InstallMethod(IsTransitive,
"for a transformation collection and a positive int",
[IsTransformationCollection, IsPosInt],
{coll, n} -> IsStronglyConnectedDigraph(DigraphOfActionOnPoints(coll, n)));

InstallMethod(IsTransitive,
"for a transformation collection and homog. list",
[IsTransformationCollection, IsHomogeneousList],
function(coll, set)
  local n, p;
  # The check for IsSSortedList is here because <set> might be strictly sorted
  # but not know it.
  if not (IsPosInt(set[1]) and IsSSortedList(set)) then
    ErrorNoReturn("the 2nd argument (a list) must be a set of positive ",
                  "integers");
  fi;

  n := Length(set);
  p := MappingPermListList(set, [1 .. n]);
  return IsTransitive(coll ^ p, n);
end);

InstallMethod(IsTransitive,
"for a transformation semigroup with generators and a pos. int.",
[IsTransformationSemigroup and HasGeneratorsOfSemigroup, IsPosInt],
{S, n} -> IsTransitive(GeneratorsOfSemigroup(S), n));

InstallMethod(IsTransitive,
"for a transformation semigroup with generators",
[IsTransformationSemigroup and HasGeneratorsOfSemigroup],
S -> IsTransitive(S, DegreeOfTransformationSemigroup(S)));

InstallMethod(IsTransitive,
"for a transformation semigroup with generators and a list",
[IsTransformationSemigroup and HasGeneratorsOfSemigroup, IsList],
{S, set} -> IsTransitive(GeneratorsOfSemigroup(S), set));

InstallMethod(ComponentRepsOfTransformationSemigroup,
"for a transformation semigroup", [IsTransformationSemigroup],
function(S)
  local D, C;
  D := DigraphMutableCopy(DigraphOfActionOnPoints(S));
  C := DigraphStronglyConnectedComponents(D).comps;
  DigraphRemoveLoops(QuotientDigraph(D, C));
  return List(DigraphSources(D), x -> DigraphVertexLabel(D, x)[1]);
end);

InstallMethod(ComponentsOfTransformationSemigroup,
"for a transformation semigroup", [IsTransformationSemigroup],
S -> DigraphConnectedComponents(DigraphOfActionOnPoints(S)).comps);

InstallMethod(CyclesOfTransformationSemigroup,
"for a transformation semigroup", [IsTransformationSemigroup],
S -> DigraphStronglyConnectedComponents(DigraphOfActionOnPoints(S)).comps);

InstallMethod(RepresentativeOfMinimalIdealNC,
"for a transformation semigroup with known generators",
[IsTransformationSemigroup and HasGeneratorsOfSemigroup],
RankFilter(IsActingSemigroup),
# to beat the default method for acting semigroups
function(S)
  local n, result, rank, image, labels, D, squashable, paths, seen, neighbours,
  map, nothing_squashed, pos, x, y, i, pair;

  n      := DegreeOfTransformationSemigroup(S);
  result := Product(GeneratorsOfSemigroup(S));
  rank   := RankOfTransformation(result, n);

  # Take the product of the generators is an arbitrary choice, the aim is to
  # try to find a smallish set to use to generate the nodes in the digraph
  # below, and also we might get lucky and find that the product of the
  # generators is of rank 1 or n, in which case we can stop right away.

  if rank = n then
    SetIsGroupAsSemigroup(S, true);
    return result;
  elif rank = 1 then
    return result;
  elif HasSize(S) and Size(S) < Binomial(n, 2) then
    TryNextMethod();
  elif HasLambdaOrb(S) and IsClosedOrbit(LambdaOrb(S)) then
    TryNextMethod();
  fi;

  # Form the digraph of action on points and pairs of points inside the image
  # set of the product of the generators. If n is very large, then it isn't
  # feasible to create a digraph with O(n ^ 2) vertices, so we use the image
  # set of the product of the generators in the hope that this is smaller.
  image := ImageSetOfTransformation(result, n);
  labels := List(ImageSetOfTransformation(result, n), x -> [x]);
  Append(labels, Combinations(ImageSetOfTransformation(result, n), 2));
  D := DigraphOfAction(S, labels, OnSets);

  # Perform a bfs through the reverse of the digraph D to find all those "pair"
  # nodes from which a "point" node is reachable, and to find the edge labels
  # of the path from the "pair" node to the "point" node. When such paths are
  # known we can squash all possible pairs of points in the image of <result>
  # into single points.

  # Sets of size 1 are squashable!
  squashable        := PositionsProperty(DigraphVertexLabels(D),
                                         x -> Size(x) = 1);
  paths             := [];
  paths{squashable} := List([1 .. Length(squashable)], x -> []);
  seen              := BlistList(DigraphVertices(D), squashable);

  for x in squashable do
    neighbours := InNeighboursOfVertex(D, x);
    for y in neighbours do
      if not seen[y] then
        seen[y] := true;
        Add(squashable, y);
        paths[y] := Concatenation([DigraphEdgeLabel(D, y, x)], paths[x]);
      fi;
    od;
  od;

  # The labels may have changed because ActionDigraph may generate additional
  # nodes, so we must renew the labels.
  labels := Filtered(DigraphVertices(D),
                     i -> Size(DigraphVertexLabel(D, i)) = 2
                          and IsBound(paths[i]));
  if IsEmpty(labels) then
    # This means there are no paths from any pair of points in the image of
    # result that can be collapsed.
    return result;
  fi;
  paths  := paths{labels};
  labels := DigraphVertexLabels(D){labels};
  map    := HashMap(Length(labels));
  for i in [1 .. Length(labels)] do
    map[labels[i]] := i;
  od;

  # Form an element of the semigroup that squashes every possible pair of
  # points in the image of <result>.
  repeat
    nothing_squashed := true;
    for pair in IteratorOfCombinations(image, 2) do
      # To ensure that every pair is eventually squashed, we have to see where
      # the pair has ended up under result.
      pair := OnSets(pair, result);
      if Size(pair) = 1 then
        result := result * result;
        image := ImageSetOfTransformation(result, n);
        nothing_squashed := false;
        break;
      fi;
      pos := map[pair];
      if pos <> fail then
        result := result * EvaluateWord(GeneratorsOfSemigroup(S), paths[pos]);
        image := ImageSetOfTransformation(result, n);
        nothing_squashed := false;
        break;
      fi;
    od;
  until nothing_squashed or Size(image) = 1;
  return result;
end);

# same method for ideals

InstallMethod(IsSynchronizingSemigroup, "for a transformation semigroup",
[IsTransformationSemigroup],
function(S)
  local N;
  N := DegreeOfTransformationSemigroup(S);
  if N = 0 then
    return false;
  elif HasMultiplicativeZero(S) and MultiplicativeZero(S) <> fail then
    return RankOfTransformation(MultiplicativeZero(S), N) = 1;
  else
    return RankOfTransformation(RepresentativeOfMinimalIdeal(S), N) = 1;
  fi;
end);

#############################################################################
## Smallest, largest element
#############################################################################

BindGlobal("SEMIGROUPS_SmallestLargestElementRClass",
function(R, BaseModifier, Cmp)
  local o, m, rep, n, base1, S, out, scc, gens, y, base2, p, x, i;

  if Size(R) = 1 then
    return Representative(R);
  fi;

  o     := LambdaOrb(R);
  m     := LambdaOrbSCCIndex(R);
  rep   := Representative(R);
  n     := DegreeOfTransformationSemigroup(Parent(R));
  base1 := BaseModifier(DuplicateFreeList(ImageListOfTransformation(rep, n)));
  S     := StabChainOp(LambdaOrbSchutzGp(o, m), rec(base := base1));
  out   := rep * LargestElementStabChain(S, ());
  scc   := OrbSCC(o)[m];
  gens  := o!.gens;

  for i in [2 .. Length(scc)] do
    y     := rep * EvaluateWord(gens,
                                TraceSchreierTreeOfSCCForward(o, m, scc[i]));
    base2 := BaseModifier(DuplicateFreeList(ImageListOfTransformation(y, n)));
    p     := MappingPermListList(base1, base2);

    x := y * LargestElementConjugateStabChain(S, p);
    if Cmp(x, out) then
      out := x;
    fi;
  od;

  return out;
end);

InstallMethod(LargestElementRClass, "for an R-class of an acting semigroup",
[IsGreensRClass and IsActingSemigroupGreensClass],
function(R)
  if not IsTransformationSemigroup(Parent(R)) then
    TryNextMethod();
  fi;
  return SEMIGROUPS_SmallestLargestElementRClass(R, IdFunc, {x, y} -> x > y);
end);

InstallMethod(SmallestElementRClass, "for an R-class of an acting semigroup",
[IsGreensRClass and IsActingSemigroupGreensClass],
function(R)
  if not IsTransformationSemigroup(Parent(R)) then
    TryNextMethod();
  fi;
  return SEMIGROUPS_SmallestLargestElementRClass(R, Reversed, \<);
end);

InstallMethod(SmallestElementSemigroup,
"for an acting transformation semigroup",
[IsTransformationSemigroup and IsActingSemigroup],
function(S)
  local n, min;

  n := DegreeOfTransformationSemigroup(S);
  if n = 0 then
    return IdentityTransformation;
  elif HasAsSSortedList(S) then
    return AsSSortedList(S)[1];
  elif HasEnumeratorSorted(S) then
    return EnumeratorSorted(S)[1];
  fi;

  min := Minimum(Union(List(GeneratorsOfSemigroup(S),
                            x -> ImageSetOfTransformation(x, n))));

  if ConstantTransformation(n, min) in MinimalIdeal(S) then
    return ConstantTransformation(n, min);
  fi;

  return Minimum(List(RClasses(S), SmallestElementRClass));
end);

InstallMethod(LargestElementSemigroup, "for an acting transformation semigroup",
[IsTransformationSemigroup and IsActingSemigroup],
function(S)
  local n, max;

  n := DegreeOfTransformationSemigroup(S);
  if n = 0 then
    return IdentityTransformation;
  elif HasAsSSortedList(S) then
    return AsSSortedList(S)[Size(S)];
  elif HasEnumeratorSorted(S) then
    return EnumeratorSorted(S)[Size(S)];
  fi;

  max := Maximum(Union(List(GeneratorsOfSemigroup(S),
                            x -> ImageSetOfTransformation(x, n))));

  if ConstantTransformation(n, max) in MinimalIdeal(S) then
    return ConstantTransformation(n, max);
  fi;

  return Maximum(List(RClasses(S), LargestElementRClass));
end);

#############################################################################
# Constructions (e.g. wreath product)
#############################################################################

InstallMethod(WreathProduct,
"for a transformation monoid and a permutation group",
[IsTransformationMonoid, IsPermGroup],
{M, G} -> WreathProduct(M, AsMonoid(IsTransformationMonoid, G)));

InstallMethod(WreathProduct,
"for a permutation group and a transformation semigroup",
[IsPermGroup, IsTransformationSemigroup],
{G, S} -> WreathProduct(AsMonoid(IsTransformationMonoid, G), S));

InstallMethod(WreathProduct,
"for a transformation monoid and a transformation semigroup",
[IsTransformationMonoid, IsTransformationSemigroup],
function(M, S)
  local m, gensM, gensS, orbs, n, rimage, maps, next, gen1, newmap, x, y, s, i;

  if not IsMonoidAsSemigroup(S) then
    ErrorNoReturn("the 2nd argument (a transformation semigroup) ",
                  "should be a monoid (as semigroup)");
  fi;

  m := DegreeOfTransformationCollection(M);

  gensM := List(GeneratorsOfMonoid(M), x -> ImageListOfTransformation(x, m));
  gensS := GeneratorsOfSemigroup(S);

  orbs := List(ComponentsOfTransformationSemigroup(S), Minimum);
  n := DegreeOfTransformationCollection(S);
  rimage := [1 .. n];

  for x in orbs do
    for y in gensS do
      RemoveSet(rimage, x ^ y);
    od;
  od;

  maps := [];  # final generating set for the wreath product

  # move copies of M as by the action induced by S
  next := [1 .. m * n];
  for s in gensS do
    for i in [1 .. n] do
      next{[1 .. m] + (i - 1) * m} := [1 .. m] + (i ^ s - 1) * m;
    od;
    Add(maps, Transformation(next));
  od;

  gen1 := gensS[1];
  for i in orbs do
    newmap := ShallowCopy(ImageListOfTransformation(maps[1], m * n));
    for x in gensM do
      newmap{[1 .. m] + (i - 1) * m} := x + (i ^ gen1 - 1) * m;
      Add(maps, Transformation(newmap));
    od;
  od;

  for i in rimage do
    newmap := OnTuples([1 .. m * n], maps[1]);
    for x in gensM do
      newmap{[1 .. m] + (i - 1) * m} := x + (i ^ gen1 - 1) * m;
      Add(maps, Transformation(newmap));
    od;
  od;

  return Semigroup(maps);
end);

#############################################################################
# Endomorphisms of digraphs
#############################################################################

InstallMethod(EndomorphismMonoid, "for a digraph", [IsDigraph],
function(digraph)
  local hook, S;

  if HasGeneratorsOfEndomorphismMonoidAttr(digraph)
      or SEMIGROUPS.DefaultOptionsRec.acting = false then
    return Monoid(GeneratorsOfEndomorphismMonoidAttr(digraph),
                  rec(small := true));
  fi;

  S := [AsMonoid(IsTransformationMonoid, AutomorphismGroup(digraph))];

  hook := function(S, f)
    S[1] := ClosureMonoid(S[1], f);
  end;

  return HomomorphismDigraphsFinder(digraph,
                                    digraph,
                                    hook,
                                    S,
                                    infinity,
                                    fail,
                                    false,
                                    DigraphVertices(digraph),
                                    [],
                                    fail,
                                    fail)[1];
end);

InstallMethod(EndomorphismMonoid, "for a digraph and a homogeneous list",
[IsDigraph, IsHomogeneousList],
function(digraph, colors)
  local hook, S;

  hook := function(S, f)
    S[1] := ClosureSemigroup(S[1], f);
  end;

  S := [AsMonoid(IsTransformationMonoid,
                 AutomorphismGroup(digraph, colors))];

  return HomomorphismDigraphsFinder(digraph, digraph, hook, S, infinity,
                                    fail, false, DigraphVertices(digraph), [],
                                    colors, colors)[1];

end);

InstallMethod(DigraphCore,
"for a digraph with generators of endomorphism monoid",
[IsDigraph and HasGeneratorsOfEndomorphismMonoidAttr],
function(D)
  local x;
  x := RepresentativeOfMinimalIdeal(EndomorphismMonoid(D));
  return ImageSetOfTransformation(x, DigraphNrVertices(D));
end);

#############################################################################
# Iterators
#############################################################################

# This is faster than using the iterator method for LibsemigroupsFroidurePin
# for n = 7 or so onwards

InstallMethod(Iterator, "for a full transformation semigroup",
[IsTransformationSemigroup and IsFullTransformationSemigroup and
 HasGeneratorsOfSemigroup],
function(S)
  local iter;

  if HasAsSSortedList(S) or HasAsListCanonical(S) then
    # This is much faster
    TryNextMethod();
  fi;

  iter := IteratorByFunctions(rec(
    tups := IteratorOfTuples([1 .. DegreeOfTransformationSemigroup(S)],
                             DegreeOfTransformationSemigroup(S)),
    parent := S,

    NextIterator := iter -> TransformationNC(NextIterator(iter!.tups)),

    IsDoneIterator := iter -> IsDoneIterator(iter!.tups),

    ShallowCopy := iter ->
      rec(parent := S,
          tups := IteratorOfTuples([1 .. DegreeOfTransformationSemigroup(S)],
                                   DegreeOfTransformationSemigroup(S))),

    PrintObj := function(iter)
                  Print("<iterator of semigroup>");
                  return;
                end));
  return iter;
end);
