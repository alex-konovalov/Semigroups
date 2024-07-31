#############################################################################
##
#W  standard/elements/bipart.tst
#Y  Copyright (C) 2014-2022                               Attila Egri-Nagy
##                                                       James D. Mitchell
##
##  Licensing information can be found in the README file of this package.
##
#############################################################################
##

#@local ElementNumber, G, Length, N, NumberElement, S, an, bp, classes
#@local classes2, e, elts, enum, f, filename, g, gens, l, n, r, triples, x, y
gap> START_TEST("Semigroups package: standard/elements/bipart.tst");
gap> LoadPackage("semigroups", false);;

#
gap> SEMIGROUPS.StartTest();

# the number of iterations, change here to get faster test
gap> N := 333;;

# BipartitionTest2: BASICS
gap> classes := [[1, 2, 3, -2], [4, -5], [5, -7], [6, -3, -4], [7], [-1],
> [-6]];;
gap> f := Bipartition(classes);
<bipartition: [ 1, 2, 3, -2 ], [ 4, -5 ], [ 5, -7 ], [ 6, -3, -4 ], [ 7 ],
 [ -1 ], [ -6 ]>
gap> LeftProjection(f);
<bipartition: [ 1, 2, 3, -1, -2, -3 ], [ 4, -4 ], [ 5, -5 ], [ 6, -6 ],
 [ 7 ], [ -7 ]>

# BipartitionTest3: different order of classes
gap> classes2 := [[-6], [1, 2, 3, -2], [4, -5], [5, -7], [6, -3, -4], [-1],
> [7]];;
gap> f = Bipartition(classes2);
true
gap> f := Bipartition([[1, 2, -3, -5, -6], [3, -2, -4], [4, 7],
> [5, -7, -8, -9], [6], [8, 9, -1]]);
<bipartition: [ 1, 2, -3, -5, -6 ], [ 3, -2, -4 ], [ 4, 7 ], [ 5, -7, -8, -9 ]
  , [ 6 ], [ 8, 9, -1 ]>
gap> LeftProjection(f);
<bipartition: [ 1, 2, -1, -2 ], [ 3, -3 ], [ 4, 7 ], [ 5, -5 ], [ 6 ],
 [ 8, 9, -8, -9 ], [ -4, -7 ], [ -6 ]>

# BipartitionTest4: ASSOCIATIVITY
gap> l := List([1 .. 3 * N], i -> RandomBipartition(17));;
gap> triples := List([1 .. N], i -> [l[i], l[i + 1], l[i + 2]]);;
gap> ForAll(triples, x -> ((x[1] * x[2]) * x[3]) = (x[1] * (x[2] * x[3])));
true

# BipartitionTest5: EMBEDDING into T_n
gap> l := List([1, 2, 3, 4, 5, 15, 35, 1999], RandomTransformation);;
gap> ForAll(l, t -> t = AsTransformation(AsBipartition(t)));
true

# BipartitionTest6: checking IsTransBipartitition
gap> l := List([1, 2, 3, 4, 5, 15, 35, 1999, 30101, 54321], i ->
> RandomTransformation(i));;
gap> ForAll(l, t -> IsTransBipartition(AsBipartition(t)));
true

# BipartitionTest7: check big size, identity, multiplication
gap> bp := RandomBipartition(7000);;
gap> bp * One(bp) = bp;
true
gap> One(bp) * bp = bp;
true

# BipartitionTest8: check BlocksIdempotentTester, first a few little examples
gap> l := BLOCKS_NC([[-1], [-2], [-3, -4]]);;
gap> r := BLOCKS_NC([[-1], [-2, -3, -4]]);;
gap> BLOCKS_E_TESTER(l, r);
true
gap> e := BLOCKS_E_CREATOR(l, r);
<bipartition: [ 1 ], [ 2, 3, 4 ], [ -1 ], [ -2 ], [ -3, -4 ]>
gap> IsIdempotent(e);
true

# BipartitionTest9: JDM is this the right behaviour?
gap> RightBlocks(e) = l;
true
gap> LeftBlocks(e) = r;
true

# BipartitionTest10: AsBipartition for a bipartition
gap> f := Bipartition([[1, 2, 3], [4, -1, -3], [5, 6, -4, -5],
> [-2], [-6]]);;
gap> AsBipartition(f, 8);
<bipartition: [ 1, 2, 3 ], [ 4, -1, -3 ], [ 5, 6, -4, -5 ], [ 7 ], [ 8 ],
 [ -2 ], [ -6 ], [ -7 ], [ -8 ]>
gap> AsBipartition(f, 6);
<bipartition: [ 1, 2, 3 ], [ 4, -1, -3 ], [ 5, 6, -4, -5 ], [ -2 ], [ -6 ]>
gap> AsBipartition(f, 4);
<bipartition: [ 1, 2, 3 ], [ 4, -1, -3 ], [ -2 ], [ -4 ]>

# BipartitionTest11: AsPartialPerm for bipartitions
gap> S := DualSymmetricInverseMonoid(3);;
gap> Number(S, IsPartialPermBipartition);
6
gap> S := PartitionMonoid(3);;
gap> Number(S, IsPartialPermBipartition);
34
gap> Size(SymmetricInverseMonoid(3));
34
gap> S := SymmetricInverseMonoid(3);;
gap> ForAll(S, x -> AsPartialPerm(AsBipartition(x)) = x);
true
gap> elts := Filtered(PartitionMonoid(3), IsPartialPermBipartition);;
gap> ForAll(elts, x -> AsBipartition(AsPartialPerm(x), 3) = x);
true

# BipartitionTest12: AsPermutation for bipartitions
gap> G := SymmetricGroup(5);;
gap> ForAll(G, x -> AsPermutation(AsBipartition(x)) = x);
true
gap> G := GroupOfUnits(PartitionMonoid(3));
<block bijection group of degree 3 with 2 generators>
gap> ForAll(G, x -> AsBipartition(AsPermutation(x), 3) = x);
true

# BipartitionTest22: AsBlockBijection and
# IsomorphismSemigroup(IsBlockBijectionSemigroup for an inverse semigroup of
# partial perms
gap> S := InverseSemigroup(
> PartialPerm([1, 2, 3, 6, 8, 10], [2, 6, 7, 9, 1, 5]),
> PartialPerm([1, 2, 3, 4, 6, 7, 8, 10], [3, 8, 1, 9, 4, 10, 5, 6]));;
gap> AsBlockBijection(S.1);
<block bijection: [ 1, -2 ], [ 2, -6 ], [ 3, -7 ],
 [ 4, 5, 7, 9, 11, -3, -4, -8, -10, -11 ], [ 6, -9 ], [ 8, -1 ], [ 10, -5 ]>

# BipartitionTest24: NaturalLeqBlockBijection
gap> S := DualSymmetricInverseMonoid(4);;
gap> f := Bipartition([[1, -2], [2, -1], [3, -3], [4, -4]]);;
gap> g := Bipartition([[1, 4, -3], [2, -1, -2], [3, -4]]);;
gap> NaturalLeqBlockBijection(f, g);
false
gap> NaturalLeqBlockBijection(f, f);
true
gap> NaturalLeqBlockBijection(f, g);
false
gap> NaturalLeqBlockBijection(g, f);
false
gap> NaturalLeqBlockBijection(g, g);
true
gap> f := Bipartition([[1, 4, 2, -1, -2, -3], [3, -4]]);
<block bijection: [ 1, 2, 4, -1, -2, -3 ], [ 3, -4 ]>
gap> NaturalLeqBlockBijection(f, g);
true
gap> NaturalLeqBlockBijection(g, f);
false
gap> First(Idempotents(S), e -> e * g = f);
<block bijection: [ 1, 2, -1, -2 ], [ 3, -3 ], [ 4, -4 ]>
gap> Set(Filtered(S, f -> NaturalLeqBlockBijection(f, g)));
[ <block bijection: [ 1, 2, 3, 4, -1, -2, -3, -4 ]>,
  <block bijection: [ 1, 2, 4, -1, -2, -3 ], [ 3, -4 ]>,
  <block bijection: [ 1, 3, 4, -3, -4 ], [ 2, -1, -2 ]>,
  <block bijection: [ 1, 4, -3 ], [ 2, 3, -1, -2, -4 ]>,
  <block bijection: [ 1, 4, -3 ], [ 2, -1, -2 ], [ 3, -4 ]> ]
gap> Filtered(S, f -> ForAny(Idempotents(S), e -> e * f = g));
[ <block bijection: [ 1, 4, -3 ], [ 2, -1, -2 ], [ 3, -4 ]> ]
gap> Set(Filtered(S, f -> ForAny(Idempotents(S), e -> e * g = f)));
[ <block bijection: [ 1, 2, 3, 4, -1, -2, -3, -4 ]>,
  <block bijection: [ 1, 2, 4, -1, -2, -3 ], [ 3, -4 ]>,
  <block bijection: [ 1, 3, 4, -3, -4 ], [ 2, -1, -2 ]>,
  <block bijection: [ 1, 4, -3 ], [ 2, 3, -1, -2, -4 ]>,
  <block bijection: [ 1, 4, -3 ], [ 2, -1, -2 ], [ 3, -4 ]> ]

# BipartitionTest25: Factorization/EvaluateWord
gap> S := DualSymmetricInverseMonoid(6);;
gap> f := S.1 * S.2 * S.3 * S.2 * S.1;
<block bijection: [ 1, 6, -4 ], [ 2, -2, -3 ], [ 3, -5 ], [ 4, -6 ],
 [ 5, -1 ]>
gap> EvaluateWord(GeneratorsOfSemigroup(S), Factorization(S, f));
<block bijection: [ 1, 6, -4 ], [ 2, -2, -3 ], [ 3, -5 ], [ 4, -6 ],
 [ 5, -1 ]>
gap> S := PartitionMonoid(3);;
gap> f := Bipartition([[1, -2, -3], [2, 3], [-1]]);;
gap> EvaluateWord(GeneratorsOfSemigroup(S), Factorization(S, f));
<bipartition: [ 1, -2, -3 ], [ 2, 3 ], [ -1 ]>
gap> S := AsSemigroup(IsBipartitionSemigroup, SymmetricInverseMonoid(5));
<inverse bipartition monoid of degree 5 with 3 generators>
gap> f := S.1 * S.2 * S.3 * S.2 * S.1;
<bipartition: [ 1 ], [ 2, -2 ], [ 3, -4 ], [ 4, -5 ], [ 5, -3 ], [ -1 ]>
gap> EvaluateWord(GeneratorsOfSemigroup(S), Factorization(S, f));
<bipartition: [ 1 ], [ 2, -2 ], [ 3, -4 ], [ 4, -5 ], [ 5, -3 ], [ -1 ]>
gap> S := Semigroup(
> [Bipartition([[1, 2, 3, 5, -1, -4], [4], [-2, -3], [-5]]),
>  Bipartition([[1, 2, 4], [3, 5, -1, -4], [-2, -5], [-3]]),
>  Bipartition([[1, 2], [3, -1, -3], [4, 5, -4, -5], [-2]]),
>  Bipartition([[1, 3, 4, -4], [2], [5], [-1, -2, -3], [-5]]),
>  Bipartition([[1, -3], [2, -5], [3, -1], [4, 5], [-2, -4]])]);;
gap> x := S.1 * S.2 * S.3 * S.4 * S.5;
<bipartition: [ 1, 2, 3, 5 ], [ 4 ], [ -1, -3, -5 ], [ -2, -4 ]>
gap> EvaluateWord(GeneratorsOfSemigroup(S), Factorization(S, x));
<bipartition: [ 1, 2, 3, 5 ], [ 4 ], [ -1, -3, -5 ], [ -2, -4 ]>
gap> IsInverseSemigroup(S);
false

# bipartition: PartialPermLeqBipartition 1/3
gap> x := Bipartition([[1, 2, 4, 5, -2], [3, -1, -3], [-4], [-5]]);;
gap> y := Bipartition([[1, 3, -2], [2, 4, -5], [5, -1, -4], [-3]]);;
gap> PartialPermLeqBipartition(x, y);
Error, the arguments (bipartitions) do not both satisfy IsPartialPermBipartiti\
on

# bipartition: PartialPermLeqBipartition 2/3
gap> x := Bipartition([[1, -4], [2, -1], [3], [4, -5], [5], [-2], [-3]]);;
gap> y := Bipartition([[1, -4], [2, -3], [3], [4], [5], [-1], [-2], [-5]]);;
gap> PartialPermLeqBipartition(x, y);
false
gap> PartialPermLeqBipartition(y, x);
true

# bipartition: PartialPermLeqBipartition 3/3
gap> x := Bipartition([[1, -4], [2, -1], [3], [4, -5], [5], [-2], [-3], [6],
> [-6]]);;
gap> y := Bipartition([[1, -4], [2, -3], [3], [4], [5], [-1], [-2], [-5]]);;
gap> PartialPermLeqBipartition(x, y);
Error, no method found! For debugging hints type ?Recovery from NoMethodFound
Error, no 1st choice method found for `PartialPermLeqBipartition' on 2 argumen\
ts

# bipartition: NaturalLeqBlockBijection  1/3
gap> x := Bipartition([[1, 2, -1, -2], [3, -3]]);;
gap> y := Bipartition([[1], [2], [3, -3], [-1, -2]]);;
gap> NaturalLeqBlockBijection(x, y);
Error, the arguments (bipartitions) are not block bijections

# bipartition: NaturalLeqBlockBijection  2/3
gap> x := Bipartition([[1, 2, -4], [3, 4, -1, -2, -3]]);;
gap> y := Bipartition([[1, 2, -3], [3, -1, -2]]);;
gap> NaturalLeqBlockBijection(x, y);
Error, no method found! For debugging hints type ?Recovery from NoMethodFound
Error, no 1st choice method found for `NaturalLeqBlockBijection' on 2 argument\
s

# bipartition: NaturalLeqBlockBijection 3/3
gap> x := IdentityBipartition(10);;
gap> NaturalLeqBlockBijection(x, x);
true

# bipartition: NaturalLeqPartialPermBipartition 1/4
gap> x := Bipartition([[1, 2, 4, 5, -2], [3, -1, -3], [-4], [-5]]);;
gap> y := Bipartition([[1, 3, -2], [2, 4, -5], [5, -1, -4], [-3]]);;
gap> NaturalLeqPartialPermBipartition(x, y);
Error, the arguments (bipartitions) are not partial perm bipartitions

# bipartition: NaturalLeqPartialPermBipartition 2/4
gap> x := Bipartition([[1, -4], [2, -1], [3], [4, -5], [5], [-2],
> [-3]]);;
gap> y := Bipartition([[1, -4], [2, -3], [3], [4], [5], [-1], [-2], [-5]]);;
gap> NaturalLeqPartialPermBipartition(x, y);
false
gap> NaturalLeqPartialPermBipartition(y, x);
false
gap> NaturalLeqPartialPermBipartition(y, y);
true

# bipartition: NaturalLeqPartialPermBipartition 3/4
gap> x := Bipartition([[1, -4], [2, -1], [3], [4, -5], [5], [-2], [-3], [6],
> [-6]]);;
gap> y := Bipartition([[1, -4], [2, -3], [3], [4], [5], [-1], [-2], [-5]]);;
gap> NaturalLeqPartialPermBipartition(x, y);
Error, no method found! For debugging hints type ?Recovery from NoMethodFound
Error, no 1st choice method found for `NaturalLeqPartialPermBipartition' on 2 \
arguments

# bipartition: NaturalLeqPartialPermBipartition 4/4
gap> x := Bipartition([[1, -4], [2], [3, -3], [4, -1], [-2]]);;
gap> NaturalLeqPartialPermBipartition(x, x);
true

# bipartition: InverseMutable, for a non-invertible bipartition
gap> x := Bipartition([[1], [2], [3, -3], [-1, -2]]);;
gap> InverseMutable(x);
fail

# bipartition: \*, for bipartition and perm 1/2
gap> Bipartition([[1], [2], [3, -3], [-1, -2]]) * (1, 3, 2);
<bipartition: [ 1 ], [ 2 ], [ 3, -2 ], [ -1, -3 ]>

# bipartition: \*, for bipartition and perm 2/2
gap> Bipartition([[1], [2], [3, -3], [-1, -2]]) * (1, 2)(4, 5);
Error, the largest moved point of the 2nd argument (a permutation) exceeds the\
 degree of the 1st argument (a bipartition)

# bipartition: \*, for perm and bipartition 1/2
gap> (1, 2) * Bipartition([[1], [2], [3, -3], [-1, -2]]);
<bipartition: [ 1 ], [ 2 ], [ 3, -3 ], [ -1, -2 ]>

# bipartition: \*, for perm and bipartition 2/2
gap> (1, 2, 4) * Bipartition([[1], [2], [3, -3], [-1, -2]]);
Error, the largest moved point of the 1st argument (a permutation) exceeds the\
 degree of the 2nd argument (a bipartition)

# bipartition: \*, for bipartition and transformation 1/2
gap> Bipartition([[1, 2, -1, -2], [3, -3]]) *
> Transformation([3, 3, 2]);
<bipartition: [ 1, 2, -3 ], [ 3, -2 ], [ -1 ]>

# bipartition: \*, for bipartition and transformation 2/2
gap> Bipartition([[1, 2, -1, -2], [3, -3]]) *
> Transformation([3, 4, 2, 4]);
Error, the degree of the 2nd argument (a transformation) exceeds the degree of\
 the 1st argument (a bipartition)

# bipartition: \*, for transformation and bipartition 1/2
gap> Transformation([1, 3, 2])
> * Bipartition([[1, 3], [2, -1], [-2, -3]]);
<bipartition: [ 1, 2 ], [ 3, -1 ], [ -2, -3 ]>

# bipartition: \*, for transformation and bipartition 2/2
gap> Transformation([1, 4, 4, 1]) *
> Bipartition([[1, 3], [2, -1], [-2, -3]]);
Error, the degree of the 1st argument (a transformation) exceeds the degree of\
 the 2nd argument (a bipartition)

# bipartition: \*, for bipartition and partial perm 1/2
gap> Bipartition([[1, 2, -1, -2], [3, -3]]) *
> PartialPerm([1, 3, 2]);
<block bijection: [ 1, 2, -1, -3 ], [ 3, -2 ]>

# bipartition: \*, for bipartition and partial perm 2/2
gap> Bipartition([[1, 2, -1, -2], [3, -3]]) *
> PartialPerm([3, 2, 4]);
Error, the 2nd argument (a partial perm) does not map [1 .. 3] into [1 .. 3]

# bipartition: \*, for partial perm and bipartition 1/2
gap> PartialPerm([1, 3, 2]) * Bipartition([[1, 3], [2, -1], [-2, -3]]);
<bipartition: [ 1, 2 ], [ 3, -1 ], [ -2, -3 ]>

# bipartition: \*, for partial perm and bipartition 2/2
gap> PartialPerm([1, 4]) * Bipartition([[1, 3], [2, -1], [-2, -3]]);
Error, the 1st argument (a partial perm) does not map [1 .. 3] into [1 .. 3]

# bipartition: \^, for bipartition and perm 1/1
gap> Bipartition([[1, -3], [2], [3, -2], [4, -1, -4]]) ^ (1, 2, 3, 4);
<bipartition: [ 1, -1, -2 ], [ 2, -4 ], [ 3 ], [ 4, -3 ]>

# bipartition: \<, for bipartitions 1/2
gap> Bipartition([[1, 2, 3, -1, -2, -3]]) <
> Bipartition([[1, 3], [2, -1], [-2, -3]]);
true

# bipartition: \<, for bipartitions 2/2
gap> Bipartition([[1, 2, 3, -1, -2, -3], [4, -4]]) <
> Bipartition([[1, 3], [2, -1], [-2, -3]]);
true

# bipartition: PermLeftQuoBipartition, error 1/2
gap> x := Bipartition([[1, 2], [-1, -2]]);;
gap> y := Bipartition([[1, -1, -2], [2]]);;
gap> PermLeftQuoBipartition(x, y);
Error, the arguments (bipartitions) do not have equal left and right blocks

# bipartition: PermLeftQuoBipartition, result 2/2
gap> x := Bipartition([[1, 2], [-1, -2]]);;
gap> PermLeftQuoBipartition(x, x);
()

# bipartition: AsPartialPerm, error 1/1
gap> AsPartialPerm(Bipartition([[1, 2, -2], [-1]]));
Error, the argument (a bipartition) does not define a partial perm

# bipartition: AsPermutation, error 1/1
gap> AsPermutation(Bipartition([[1, 2, -2], [-1]]));
Error, the argument (a bipartition) does not define a permutation

# bipartition: AsTransformation, error 1/1
gap> AsTransformation(Star(Bipartition([[1, 2, -2], [-1]])));
Error, the argument (a bipartition) does not define a transformation

# bipartition: AsBipartition, for a perm and pos int, error 1/1
gap> AsBipartition((1, 2, 3, 5), 4);
Error, the 1st argument (a permutation) does not permute [1 .. 4]

# bipartition: AsBipartition, for a transformation and pos int, error 1/1
gap> AsBipartition(Transformation([4, 4, 4, 4]), 2);
Error, the 1st argument (a transformation) does not map [1 .. 2] to itself

# bipartition: AsBipartition, for a bipartition and 0 1/1
gap> AsBipartition(Bipartition([[1, 2, -1, -2], [3, -3]]), 0);
<empty bipartition>

# bipartition: AsBlockBijection, for a partial perm and 0 1/1
gap> AsBlockBijection(PartialPerm([4, 1, 3, 2]), 0);
Error, no method found! For debugging hints type ?Recovery from NoMethodFound
Error, no 1st choice method found for `AsBlockBijection' on 2 arguments

# bipartition: AsBlockBijection, for a partial perm and pos int, error 1/1
gap> AsBlockBijection(PartialPerm([1, 3, 2, 4]), 1);
Error, the 2nd argument (a pos. int.) is less than or equal to the maximum of \
the degree and codegree of the 1st argument (a partial perm)

# bipartition: IsUniformBlockBijection, for a bipartition 1/3
gap> IsUniformBlockBijection(Bipartition([[1, 2, -1, -2], [3, -3]]));
true

# bipartition: IsUniformBlockBijection, for a bipartition 2/3
gap> x := Bipartition([[1, -1], [2, 3, -2], [-3]]);;
gap> IsUniformBlockBijection(x);
false

# bipartition: IsUniformBlockBijection, for a bipartition 3/3
gap> x := Bipartition([[1, 3, -2], [2, -1, -3]]);;
gap> IsUniformBlockBijection(x);
false

# bipartition: IsDualTransBipartition, for a bipartition 1/2
gap> x := Bipartition([[1, 3, -2], [2, -1, -3]]);;
gap> IsDualTransBipartition(x);
false

# bipartition: IsDualTransBipartition, for a bipartition 2/2
gap> x := Star(AsBipartition(Transformation([2, 1, 2])));;
gap> IsDualTransBipartition(x);
true

# bipartition: RightProjection
gap> x := Bipartition([[1, 2, 4, 5, -1], [3, 6, -2], [-3, -6], [-4, -5]]);;
gap> RightProjection(x);
<bipartition: [ 1, -1 ], [ 2, -2 ], [ 3, 6 ], [ 4, 5 ], [ -3, -6 ],
 [ -4, -5 ]>

# bipartition: RightProjection, LeftProjection
gap> x := Bipartition([[1, 2], [-1, -2, 3], [-3, -4, -5], [4, 5]]);;
gap> RightProjection(x);
<bipartition: [ 1, 2, -1, -2 ], [ 3, 4, 5 ], [ -3, -4, -5 ]>
gap> LeftProjection(StarOp(x));
<bipartition: [ 1, 2, -1, -2 ], [ 3, 4, 5 ], [ -3, -4, -5 ]>
gap> LeftProjection(x);
<bipartition: [ 1, 2 ], [ 3, -3 ], [ 4, 5 ], [ -1, -2 ], [ -4, -5 ]>
gap> RightProjection(StarOp(x));
<bipartition: [ 1, 2 ], [ 3, -3 ], [ 4, 5 ], [ -1, -2 ], [ -4, -5 ]>

# bipartition: RightProjection, LeftProjection
gap> x := Bipartition([[1, -2], [2, 3, 4], [5, -1, -3], [6, 7, 8],
> [9, 10, -7, -8, -9], [11], [-4, -5, -6], [-10, -11]]);;
gap> RightProjection(x);
<bipartition: [ 1, 3, -1, -3 ], [ 2, -2 ], [ 4, 5, 6 ],
 [ 7, 8, 9, -7, -8, -9 ], [ 10, 11 ], [ -4, -5, -6 ], [ -10, -11 ]>
gap> LeftProjection(StarOp(x));
<bipartition: [ 1, 3, -1, -3 ], [ 2, -2 ], [ 4, 5, 6 ],
 [ 7, 8, 9, -7, -8, -9 ], [ 10, 11 ], [ -4, -5, -6 ], [ -10, -11 ]>
gap> LeftProjection(x);
<bipartition: [ 1, -1 ], [ 2, 3, 4 ], [ 5, -5 ], [ 6, 7, 8 ],
 [ 9, 10, -9, -10 ], [ 11 ], [ -2, -3, -4 ], [ -6, -7, -8 ], [ -11 ]>
gap> RightProjection(StarOp(x));
<bipartition: [ 1, -1 ], [ 2, 3, 4 ], [ 5, -5 ], [ 6, 7, 8 ],
 [ 9, 10, -9, -10 ], [ 11 ], [ -2, -3, -4 ], [ -6, -7, -8 ], [ -11 ]>

# bipartition: RightProjection, LeftProjection
gap> x := Bipartition([[1, 3, -2, -4], [2], [4, 6, -1, -3, -5], [5, 8],
> [7, -6, -9], [9, 10], [-7, -8, -10]]);
<bipartition: [ 1, 3, -2, -4 ], [ 2 ], [ 4, 6, -1, -3, -5 ], [ 5, 8 ],
 [ 7, -6, -9 ], [ 9, 10 ], [ -7, -8, -10 ]>
gap> RightProjection(x);
<bipartition: [ 1, 3, 5, -1, -3, -5 ], [ 2, 4, -2, -4 ], [ 6, 9, -6, -9 ],
 [ 7, 8, 10 ], [ -7, -8, -10 ]>
gap> LeftProjection(StarOp(x));
<bipartition: [ 1, 3, 5, -1, -3, -5 ], [ 2, 4, -2, -4 ], [ 6, 9, -6, -9 ],
 [ 7, 8, 10 ], [ -7, -8, -10 ]>
gap> LeftProjection(x);
<bipartition: [ 1, 3, -1, -3 ], [ 2 ], [ 4, 6, -4, -6 ], [ 5, 8 ], [ 7, -7 ],
 [ 9, 10 ], [ -2 ], [ -5, -8 ], [ -9, -10 ]>
gap> RightProjection(StarOp(x));
<bipartition: [ 1, 3, -1, -3 ], [ 2 ], [ 4, 6, -4, -6 ], [ 5, 8 ], [ 7, -7 ],
 [ 9, 10 ], [ -2 ], [ -5, -8 ], [ -9, -10 ]>

# bipartition: Bipartition 1/3
gap> Bipartition("test");
Error, the argument does not consist of duplicate-free homogeneous lists
gap> Bipartition(["test"]);
Error, the argument does not consist of duplicate-free homogeneous lists
gap> Bipartition([[1, 2], [3, "a"]]);
Error, the argument does not consist of duplicate-free homogeneous lists
gap> Bipartition([[1, 2], [3, 3]]);
Error, the argument does not consist of duplicate-free homogeneous lists

# bipartition: Bipartition 2/3
gap> Bipartition([[1, 2], [3, E(3)]]);
Error, the argument does not consist of lists of integers from [-
2 .. -1, 1 .. 2]

# bipartition: Bipartition 3/3
gap> Bipartition([[1, 2], [3, 4]]);
Error, the argument does not consist of lists of integers from [-
2 .. -1, 1 .. 2]

# bipartition: OneMutable, for a bipartition collection 1/1
gap> OneMutable([IdentityBipartition(2)]);
<block bijection: [ 1, -1 ], [ 2, -2 ]>

# bipartition: BipartitionByIntRep 1/5
gap> BipartitionByIntRep([1, 2, 3]);
Error, the degree of a bipartition must be even, found 3

# bipartition: BipartitionByIntRep 2/5
gap> BipartitionByIntRep([1, 2, 3, "a"]);
Error, no method found! For debugging hints type ?Recovery from NoMethodFound
Error, no 1st choice method found for `BipartitionByIntRep' on 1 arguments

# bipartition: BipartitionByIntRep 3/5
gap> BipartitionByIntRep([1, 2, 3, 5]);
Error, expected 4 but found 5, in position 4

# bipartition: BipartitionByIntRep 4/5
gap> BipartitionByIntRep([1, 3, 3, 5]);
Error, expected 2 but found 3, in position 2

# bipartition: BipartitionByIntRep 5/5
gap> BipartitionByIntRep([1, 2, 3, 1]);
<bipartition: [ 1, -2 ], [ 2 ], [ -1 ]>

# BipartitionByIntRep
gap> BipartitionByIntRep([1, 3, 3, 4]);
Error, expected 2 but found 3, in position 2
gap> BipartitionByIntRep([1, 2, 4, 4]);
Error, expected 3 but found 4, in position 3

# bipartition: BIPART_LAMBDA_CONJ 1/2
gap> x := Bipartition([[1, 3, -2, -3], [2, -1]]);;
gap> BIPART_LAMBDA_CONJ(x, LeftOne(x));
(1,2)

# bipartition: BIPART_LAMBDA_CONJ 2/2
gap> x := Bipartition([[1, 3, -2, -3], [2, -1]]);;
gap> BIPART_LAMBDA_CONJ(LeftOne(x), x);
(1,2)

# bipartition: PrintString, for a bipartition 1/1
gap> PrintString(Bipartition([[1, 2, -1, -2], [3, -3]]));
"\>\>Bipartition(\< \>[ [ 1, 2, -1, -2 ],\< \>[ 3, -3 ] \<] )\<"

# bipartition: PrintString, for a bipartition collection, 1
gap> PrintString([Bipartition([[1, 2, -1, -2], [3, -3]]),
> Bipartition([[1, 2, -1, -2], [3, -3]])]);
"\>[ \>\>\>Bipartition(\< \>[ [ 1, 2, -1, -2 ],\< \>[ 3, -3 ] \<] )\<,\<\n \>\
\>\>Bipartition(\< \>[ [ 1, 2, -1, -2 ],\< \>[ 3, -3 ] \<] )\< ]\<\n"

# bipartition: PrintString, for a bipartition collection, 2
gap> S := Semigroup(Bipartition([[1, 2, -1, -2], [3, -3]]));;
gap> PrintString(S);
"\>Semigroup(\>\n\>\>[ \>\>\>Bipartition(\< \>[ [ 1, 2, -1, -2 ],\< \>[ 3, -3 \
] \<] )\< ]\<\n\<\> \<)\<\<"

# bipartition: PrintString, for a bipartition collection, 3
gap> x := GreensRClassOfElement(
> Semigroup([
>   Bipartition([[1, 2, 3, -1, -3], [-2]]),
>   Bipartition([[1, 2, -2], [3], [-1], [-3]])]),
>   Bipartition([[1, 2, -1, -3], [3], [-2]]));;
gap> PrintString(x);
"\>\>\>GreensRClassOfElement\<(\>\>Semigroup(\>\n\>\>[ \>\>\>Bipartition(\< \>\
[ [ 1, 2, 3, -1, -3 ],\< \>[ -2 ] \<] )\<,\<\n \>\>\>Bipartition(\< \>[ [ 1, 2\
, -2 ],\< \>[ 3 ],\< \>[ -1 ],\< \>[ -3 ] \<] )\< ]\<\n\<\> \<)\<\<,\< \>\>\>B\
ipartition(\< \>[ [ 1, 2, -1, -3 ],\< \>[ 3 ],\< \>[ -2 ] \<] )\<\<)\<\<"

# bipartition: DegreeOfBipartitionCollection, for a semigroup 1/1
gap> DegreeOfBipartitionCollection(PartitionMonoid(2));
2

# bipartition: DegreeOfBipartitionCollection, error 1/1
gap> x := Bipartition([[1, 2, -2], [-1]]);;
gap> y := Bipartition([[1, 3], [2, -1], [-2], [-3]]);;
gap> IsBipartitionCollection([x, y]);
false

# bipartition: AsBipartition, for a PBR and 0, 1
gap> AsBipartition(EmptyPBR(1), 0);
<empty bipartition>

# bipartition: AsBipartition, for a PBR and pos int, 1
gap> AsBipartition(PBR([[-1], [-2]], [[], []]), 2);
Error, the 1st argument (a pbr) does not satisfy 'IsBipartitionPBR'

# bipartition: AsBipartition, for a PBR and pos int, 2
gap> AsBipartition(PBR(
> [[-3, 1, 3], [-1, 2], [-3, 1, 3]],
> [[-1, 2], [-2], [-3, 1, 3]]), 3);
<bipartition: [ 1, 3, -3 ], [ 2, -1 ], [ -2 ]>

# bipartition: AsBipartition, for a PBR, 1
gap> AsBipartition(PBR([[-1], [-2]], [[], []]));
Error, the argument (a pbr) does not satisfy 'IsBipartitionPBR'

# bipartition: AsBipartition, for a PBR, 2
gap> AsBipartition(PBR(
> [[-3, 1, 3], [-1, 2], [-3, 1, 3]],
> [[-1, 2], [-2], [-3, 1, 3]]));
<bipartition: [ 1, 3, -3 ], [ 2, -1 ], [ -2 ]>

# bipartition: RandomBlockBijection, 1
gap> ForAll([1 .. 20], x -> IsBlockBijection(RandomBlockBijection(x)));
true

# bipartition: bug in BIPART_LAMBDA_CONJ
gap> BIPART_LAMBDA_CONJ(Bipartition([[1, -2], [2, -3], [3], [-1]]),
>                       Bipartition([[1, -1, -2], [2, -3], [3]]));
(1,3,2)

# bipartition: empty bipartition tests for int/ext rep
gap> x := Bipartition([]);
<empty bipartition>
gap> ExtRepOfObj(x);
[  ]
gap> IntRepOfBipartition(x);
[  ]

# Test bipartition of degree 0
gap> x := Bipartition([]);;
gap> NrLeftBlocks(x * x);
0
gap> NrRightBlocks(x * x);
0
gap> DegreeOfBipartition(x * x);
0
gap> RightBlocks(x * x);
<empty blocks>
gap> LeftBlocks(x * x);
<empty blocks>
gap> RankOfBipartition(x * x);
0

# bipartition: IndexPeriodOfSemigroupElement, for a bipartition
gap> x := Bipartition(
> [[1, 4, -8], [2, -4], [3, 5, -1], [6, -9], [7, -7], [8, -5], [9, 10, -3],
> [-2], [-6], [-10]]);;
gap> IndexPeriodOfSemigroupElement(x);
[ 3, 3 ]

# Test TYPE_BIPART
gap> TYPE_BIPART(3);;
gap> TYPE_BIPART(3);;

# Test pickling
gap> filename := Filename(DirectoryTemporary(), "bipart.p");;
gap> x := Bipartition(
> [[1, 4, -8], [2, -4], [3, 5, -1], [6, -9], [7, -7], [8, -5], [9, 10, -3],
> [-2], [-6], [-10]]);;
gap> WriteGenerators(filename, [x]);
IO_OK
gap> x = ReadGenerators(filename)[1];
true
gap> Exec("rm ", filename);
gap> filename := Concatenation(SEMIGROUPS.PackageDir,
> "/tst/standard/elements/bipart.tst");;
gap> f := IO_File(filename, "r");;
gap> IO_Unpicklers.BIPA(f);
IO_Error
gap> IO_Pickle(f, x);
IO_Error
gap> IO_Close(f);
true

# Test identity bipartition of degree 0
gap> IdentityBipartition(0);
<empty bipartition>

# Test String
gap> x := Bipartition(
> [[1, 4, -8], [2, -4], [3, 5, -1], [6, -9], [7, -7], [8, -5], [9, 10, -3],
> [-2], [-6], [-10]]);;
gap> String(x);
"Bipartition([ [ 1, 4, -8 ], [ 2, -4 ], [ 3, 5, -1 ], [ 6, -9 ], [ 7, -7 ], [ \
8, -5 ], [ 9, 10, -3 ], [ -2 ], [ -6 ], [ -10 ] ])"
gap> x = EvalString(String(x));
true

# Test PrintString (for degree 0)
gap> PrintString(IdentityBipartition(0));
"\>\>Bipartition(\< \>[]\<)\<"

# bipartition: AsBlockBijection, for a partial perm bipartition
gap> x := Bipartition([[1, 3], [2, 4, -2], [5, -1, -3, -4], [-5]]);;
gap> AsBlockBijection(x);
Error, the argument (a bipartion) does not satisfy IsPartialPermBipartition
gap> AsBlockBijection(x, 3);
Error, the 1st argument (a bipartition) is not a partial perm bipartition
gap> n := 4;;
gap> S := SymmetricInverseMonoid(n);
<symmetric inverse monoid of degree 4>
gap> gens := List(GeneratorsOfInverseMonoid(S), AsBipartition);;
gap> ForAll(gens, IsPartialPermBipartition);
true
gap> for x in gens do
>   for y in gens do
>     if not AsBlockBijection(x * y, n + 1)
>         = AsBlockBijection(x, n + 1) * AsBlockBijection(y, n + 1) then
>       Print("fail\n");
>     fi;
>   od;
> od;
gap> AsBlockBijection(One(gens[1])) = IdentityBipartition(5);
true
gap> x := Bipartition([[1, -4], [2, -1], [3], [4], [-2], [-3]]);;
gap> AsBlockBijection(x, 0);
Error, no method found! For debugging hints type ?Recovery from NoMethodFound
Error, no 1st choice method found for `AsBlockBijection' on 2 arguments
gap> AsBlockBijection(x, 3);
Error, the 2nd argument (a pos. int.) is less than or equal to the maximum of \
the degree and codegree of the 1st argument (a partial perm)
gap> AsBlockBijection(x, 4);
Error, the 2nd argument (a pos. int.) is less than or equal to the maximum of \
the degree and codegree of the 1st argument (a partial perm)
gap> AsBlockBijection(x);
<block bijection: [ 1, -4 ], [ 2, -1 ], [ 3, 4, 5, -2, -3, -5 ]>
gap> AsBlockBijection(x, 6);
<block bijection: [ 1, -4 ], [ 2, -1 ], [ 3, 4, 5, 6, -2, -3, -5, -6 ]>

# DomainOfBipartition and CodomainOfBipartition
gap> x := Bipartition([]);
<empty bipartition>
gap> DomainOfBipartition(x);
[  ]
gap> CodomainOfBipartition(x);
[  ]
gap> x := Bipartition([[1, -3], [2, -2], [3, -4], [4, -1]]);;
gap> DomainOfBipartition(x);
[ 1, 2, 3, 4 ]
gap> CodomainOfBipartition(x);
[ -1, -2, -3, -4 ]
gap> x := Bipartition([[1, 2], [3], [4], [-1], [-2, -3], [-4]]);;
gap> DomainOfBipartition(x);
[  ]
gap> CodomainOfBipartition(x);
[  ]
gap> x := Bipartition([[1], [2, 6, -1, -2, -3], [3, -4], [4, -5], [5, -6]]);;
gap> DomainOfBipartition(x);
[ 2, 6, 3, 4, 5 ]
gap> CodomainOfBipartition(x);
[ -1, -2, -3, -4, -5, -6 ]
gap> x := Bipartition([[1, -1, -4], [2, 3, 6, -2, -3], [4, 5, -5], [-6]]);;
gap> DomainOfBipartition(x);
[ 1, 2, 3, 6, 4, 5 ]
gap> CodomainOfBipartition(x);
[ -1, -4, -2, -3, -5 ]

# Test error messages for when creating a bipartition with degree too large.
# We create enum, as opposed to a range [1 .. 2 ^ 33] to allow this test to
# work in the 32-bit version.
gap> enum := EnumeratorByFunctions(Integers,
>                                  rec(ElementNumber := {enum, x} -> x,
>                                  NumberElement := {enum, x} -> x,
>                                  Length := x -> 2 ^ 33));;
gap> Bipartition([enum]);
Error, the maximum degree of a bipartition is 2 ^ 29 - 1
gap> BipartitionByIntRep(enum);
Error, the length of the argument (a list) exceeds 2 ^ 30 - 1
gap> IdentityBipartition(2 ^ 31);
Error, the argument (a pos. int) must not exceed 2 ^ 29 - 1
gap> RandomBipartition(2 ^ 31);
Error, the argument (a pos. int.) must not exceed 2 ^ 29 - 1
gap> RandomBlockBijection(2 ^ 31);
Error, the argument (a pos. int.) must not exceed 2 ^ 29 - 1
gap> AsBipartition((), 2 ^ 31);
Error, the 2nd argument (a pos. int.) exceeds 2 ^ 29 - 1
gap> AsBipartition(PartialPerm([]), 2 ^ 31);
Error, the 2nd argument (a pos. int.) exceeds 2 ^ 29 - 1
gap> AsBipartition(Transformation([]), 2 ^ 31);
Error, the 2nd argument (a pos. int.) exceeds 2 ^ 29 - 1
gap> AsBipartition(Bipartition([]), 2 ^ 31);
Error, the 2nd argument (a pos. int.) exceeds 2 ^ 29 - 1
gap> AsBlockBijection(PartialPerm([]), 2 ^ 31);
Error, the 2nd argument (a pos. int.) exceeds 2 ^ 29 - 1

# Bipartition
gap> Bipartition([[1, 2], [-1, 1]]);
Error, the union of the argument <classes> is not [-2 .. -1, 1 .. 2]

# AsBipartition, for a partial perm
gap> AsBipartition(PartialPermNC([1 .. 10]));;

# BipartitionByIntRep, bad input
gap> BipartitionByIntRep(['a', 'a']);
Error, the items in the argument (a list) must be positive integers
gap> BipartitionByIntRep(['a']);
Error, the degree of a bipartition must be even, found 1

#
gap> SEMIGROUPS.StopTest();
gap> STOP_TEST("Semigroups package: standard/elements/bipart.tst");
