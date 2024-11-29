############################################################################
##
#W  standard/semigroups/semitrans.tst
#Y  Copyright (C) 2015-2022                                 Wilf A. Wilson
##
##  Licensing information can be found in the README file of this package.
##
#############################################################################
##

#@local B, BruteForceInverseCheck, BruteForceIsoCheck, C, CC, D, DP, F
#@local LoopIterator, M, Noop, R, S, S1, S2, T, TC, TestIterator, W, WW, acting
#@local coll, gr, inv, iso, iter1, iter2, len, list, map, n, rels, valid, x, y
#@local a, b
gap> START_TEST("Semigroups package: standard/semigroups/semitrans.tst");
gap> LoadPackage("semigroups", false);;

#
gap> SEMIGROUPS.StartTest();;
gap> Noop := 0;;
gap> TestIterator := function(S, it)
> local LoopIterator;
> LoopIterator := function(it)
>   local valid, len, x;
>   valid := true;;
>   len := 0;
>   for x in it do
>     len := len + 1;
>     if not x in S then
>       valid := false;
>       break;
>     fi;
>   od;
>   return valid and IsDoneIterator(it) and len = Size(S);
> end;
> return LoopIterator(it) and LoopIterator(ShallowCopy(it));
> end;;

# SemiTransTest1
# RepresentativeOfMinimalIdeal and IsSynchronizingSemigroup for T_n
gap> S := Semigroup(Transformation([1]));;
gap> RepresentativeOfMinimalIdeal(S);
IdentityTransformation
gap> IsSynchronizingSemigroup(S);
false
gap> ForAll([2 .. 10], x ->
> IsSynchronizingSemigroup(FullTransformationMonoid(x)));
true
gap> for n in [2 .. 10] do
>   Print(RepresentativeOfMinimalIdeal(FullTransformationMonoid(n)), "\n");
> od;
Transformation( [ 1, 1 ] )
Transformation( [ 1, 1, 1 ] )
Transformation( [ 1, 1, 1, 1 ] )
Transformation( [ 1, 1, 1, 1, 1 ] )
Transformation( [ 1, 1, 1, 1, 1, 1 ] )
Transformation( [ 1, 1, 1, 1, 1, 1, 1 ] )
Transformation( [ 1, 1, 1, 1, 1, 1, 1, 1 ] )
Transformation( [ 1, 1, 1, 1, 1, 1, 1, 1, 1 ] )
Transformation( [ 1, 1, 1, 1, 1, 1, 1, 1, 1, 1 ] )
gap> IsSynchronizingSemigroup(MinimalIdeal(FullTransformationMonoid(3)));
true

# SemiTransTest2
# IsSynchronizingSemigroup
gap> S := Semigroup([
> Transformation([1, 1, 4, 3, 1]),
> Transformation([2, 1, 3, 4, 2])]);
<transformation semigroup of degree 5 with 2 generators>
gap> IsSynchronizingSemigroup(S);
false
gap> S := Semigroup(S);;
gap> RepresentativeOfMinimalIdeal(S);
Transformation( [ 2, 2, 4, 3, 2 ] )
gap> IsSynchronizingSemigroup(S);
false
gap> S := Semigroup([
> Transformation([2, 6, 7, 2, 6, 9, 9, 1, 1, 5]),
> Transformation([3, 8, 1, 9, 9, 4, 10, 5, 10, 6]),
> Transformation([7, 1, 4, 3, 2, 7, 7, 6, 6, 5])]);
<transformation semigroup of degree 10 with 3 generators>
gap> IsSynchronizingSemigroup(S);
true
gap> S := Semigroup(S);;
gap> RepresentativeOfMinimalIdeal(S);
Transformation( [ 7, 7, 7, 7, 7, 7, 7, 7, 7, 7 ] )
gap> IsSynchronizingSemigroup(S);
true
gap> S := Semigroup(S);;
gap> MultiplicativeZero(S);
fail
gap> IsSynchronizingSemigroup(S);
true
gap> S := Semigroup([
> Transformation([4, 6, 5, 4, 3, 9, 10, 2, 2, 9]),
> Transformation([5, 7, 10, 4, 6, 7, 4, 1, 1, 3]),
> Transformation([6, 7, 9, 4, 2, 4, 7, 5, 9, 7])]);
<transformation semigroup of degree 10 with 3 generators>
gap> IsSynchronizingSemigroup(S);
true
gap> S := Semigroup(S);;
gap> RepresentativeOfMinimalIdeal(S);
Transformation( [ 4, 4, 4, 4, 4, 4, 4, 4, 4, 4 ] )
gap> IsSynchronizingSemigroup(S);
true
gap> HasMultiplicativeZero(S);
false
gap> S := Semigroup(S);;
gap> MultiplicativeZero(S);
Transformation( [ 4, 4, 4, 4, 4, 4, 4, 4, 4, 4 ] )
gap> IsSynchronizingSemigroup(S);
true
gap> S := Semigroup(Transformation([1, 2, 2, 3]));
<commutative transformation semigroup of degree 4 with 1 generator>
gap> MultiplicativeZero(S);
Transformation( [ 1, 2, 2, 2 ] )
gap> IsSynchronizingSemigroup(S);
false

# SemiTransTest3
# FixedPointsOfTransformationSemigroup for a transformation semigroup with
# generators
gap> S := FullTransformationMonoid(3);;
gap> FixedPointsOfTransformationSemigroup(S);
[  ]
gap> S := Semigroup([
> Transformation([1, 2, 4, 4, 5, 6]),
> Transformation([1, 1, 3, 4, 6, 6]),
> Transformation([1, 1, 3, 4, 5, 6])]);;
gap> FixedPointsOfTransformationSemigroup(S);
[ 1, 4, 6 ]

# SemiTransTest4
# MovedPoints for a transformation semigroup with generators
gap> S := FullTransformationMonoid(4);;
gap> MovedPoints(S);
[ 1 .. 4 ]
gap> S := Semigroup([
> Transformation([1, 2, 3, 4, 5, 6]),
> Transformation([1, 1, 3, 4, 6, 6]),
> Transformation([1, 1, 4, 4, 5, 6])]);;
gap> MovedPoints(S);
[ 2, 3, 5 ]

# SemiTransTest5
# \^ for a transformation semigroup and a transformation or a permutation
gap> S := FullTransformationMonoid(4);;
gap> S ^ () = S;
true
gap> S ^ (1, 3) = S;
true
gap> S := S ^ (1, 5)(2, 4, 6)(3, 7);
<transformation monoid of degree 7 with 3 generators>
gap> Size(S) = 4 ^ 4;
true
gap> GeneratorsOfSemigroup(S);
[ IdentityTransformation, Transformation( [ 1, 2, 3, 7, 4, 5, 6 ] ), 
  Transformation( [ 1, 2, 3, 5, 4 ] ), Transformation( [ 1, 2, 3, 4, 5, 5 ] ) 
 ]
gap> S := Semigroup([
> Transformation([2, 6, 7, 2, 6, 1, 1, 5]),
>  Transformation([3, 8, 1, 4, 5, 6, 7, 1]),
>  Transformation([4, 3, 2, 7, 7, 6, 6, 5])]);;
gap> GeneratorsOfSemigroup(S ^ (1, 7, 8, 6, 10)(3, 9, 5, 4));
[ Transformation( [ 1, 10, 2, 10, 5, 4, 2, 7, 8, 7 ] ), 
  Transformation( [ 1, 6, 3, 4, 5, 7, 9, 8, 7 ] ), 
  Transformation( [ 1, 9, 8, 8, 5, 4, 3, 10, 2, 10 ] ) ]

# SemiTransTest6
# DigraphOfActionOnPoints for a transformation semigroup (and a pos int)
gap> gr := DigraphOfActionOnPoints(FullTransformationSemigroup(4));
<immutable digraph with 4 vertices, 9 edges>
gap> OutNeighbours(gr);
[ [ 1, 2 ], [ 2, 3, 1 ], [ 3, 4 ], [ 4, 1 ] ]
gap> S := Semigroup([
> Transformation([2, 6, 7, 2, 6, 1, 1, 5]),
>  Transformation([4, 3, 2, 7, 7, 6, 6, 5]),
>  Transformation([3, 8, 1, 4, 5, 6, 7, 1])]);;
gap> DigraphOfActionOnPoints(S, -1);
Error, the 2nd argument (an integer) must be non-negative
gap> DigraphOfActionOnPoints(S, 5);
<immutable digraph with 5 vertices, 9 edges>
gap> gr := DigraphOfActionOnPoints(S);
<immutable digraph with 8 vertices, 22 edges>
gap> DigraphOfActionOnPoints(S, 0) = EmptyDigraph(0);
true
gap> DigraphOfActionOnPoints(S, 8) = gr;
true
gap> OutNeighbours(gr);
[ [ 2, 4, 3 ], [ 6, 3, 8 ], [ 7, 2, 1 ], [ 2, 7, 4 ], [ 6, 7, 5 ], [ 1, 6 ], 
  [ 1, 6, 7 ], [ 5, 1 ] ]
gap> DigraphOfActionOnPoints(FullTransformationMonoid(1));
<immutable empty digraph with 0 vertices>
gap> DigraphOfActionOnPoints(FullTransformationMonoid(2), 1);
<immutable digraph with 1 vertex, 1 edge>

# SemiTransTest9
# Idempotents for a transformation semigroup and a pos int
gap> Idempotents(FullTransformationMonoid(3), 4);
[  ]
gap> Idempotents(FullTransformationMonoid(3), 3);
[ IdentityTransformation ]
gap> Idempotents(FullTransformationMonoid(3), 2);
[ Transformation( [ 1, 2, 1 ] ), Transformation( [ 1, 2, 2 ] ), 
  Transformation( [ 3, 2, 3 ] ), Transformation( [ 2, 2 ] ), 
  Transformation( [ 1, 3, 3 ] ), Transformation( [ 1, 1 ] ) ]
gap> Idempotents(FullTransformationMonoid(3), 1);
[ Transformation( [ 1, 1, 1 ] ), Transformation( [ 2, 2, 2 ] ), 
  Transformation( [ 3, 3, 3 ] ) ]
gap> S := Semigroup([
> Transformation([5, 1, 3, 1, 4, 2, 5, 2]),
>  Transformation([7, 1, 7, 4, 2, 5, 6, 3]),
>  Transformation([8, 4, 6, 5, 7, 8, 8, 7])]);;
gap> Idempotents(S, 9);
[  ]
gap> Length(Idempotents(S, 3));
988
gap> AsSet(Idempotents(S, 1));
[ Transformation( [ 1, 1, 1, 1, 1, 1, 1, 1 ] ), 
  Transformation( [ 2, 2, 2, 2, 2, 2, 2, 2 ] ), 
  Transformation( [ 3, 3, 3, 3, 3, 3, 3, 3 ] ), 
  Transformation( [ 4, 4, 4, 4, 4, 4, 4, 4 ] ), 
  Transformation( [ 5, 5, 5, 5, 5, 5, 5, 5 ] ), 
  Transformation( [ 6, 6, 6, 6, 6, 6, 6, 6 ] ), 
  Transformation( [ 7, 7, 7, 7, 7, 7, 7, 7 ] ), 
  Transformation( [ 8, 8, 8, 8, 8, 8, 8, 8 ] ) ]

# SemiTransTest12
gap> S := Semigroup(PartialPerm([2, 3], [1, 4]));;
gap> R := RClass(S, RepresentativeOfMinimalIdeal(S));
<Green's R-class: <empty partial perm>>
gap> S := Semigroup([
> Transformation([1, 3, 4, 1, 3, 5]),
>  Transformation([5, 1, 6, 1, 6, 3])]);;
gap> R := HClass(S, Transformation([4, 5, 3, 4, 5, 5]));
<Green's H-class: Transformation( [ 4, 5, 3, 4, 5, 5 ] )>

# SemiTransTest13
# EndomorphismMonoid
gap> gr := Digraph([[1, 2], [1, 2]]);;
gap> GeneratorsOfEndomorphismMonoidAttr(gr);
[ Transformation( [ 2, 1 ] ), IdentityTransformation, 
  Transformation( [ 1, 1 ] ) ]
gap> S := EndomorphismMonoid(gr);
<transformation monoid of degree 2 with 2 generators>
gap> Elements(S);
[ Transformation( [ 1, 1 ] ), IdentityTransformation, 
  Transformation( [ 2, 1 ] ), Transformation( [ 2, 2 ] ) ]
gap> S := EndomorphismMonoid(Digraph([[1, 2], [1, 2]]), [1, 1]);
<transformation monoid of degree 2 with 2 generators>
gap> Elements(S);
[ Transformation( [ 1, 1 ] ), IdentityTransformation, 
  Transformation( [ 2, 1 ] ), Transformation( [ 2, 2 ] ) ]
gap> S := EndomorphismMonoid(Digraph([[1, 2], [1, 2]]));
<transformation monoid of degree 2 with 2 generators>
gap> Elements(S);
[ Transformation( [ 1, 1 ] ), IdentityTransformation, 
  Transformation( [ 2, 1 ] ), Transformation( [ 2, 2 ] ) ]
gap> IsFullTransformationMonoid(S);
true
gap> S := EndomorphismMonoid(Digraph([[2], [2]]));
<commutative transformation monoid of degree 2 with 1 generator>
gap> Elements(S);
[ IdentityTransformation, Transformation( [ 2, 2 ] ) ]
gap> S := EndomorphismMonoid(Digraph([[2], [2]]), [1, 1]);
<commutative transformation monoid of degree 2 with 1 generator>
gap> Elements(S);
[ IdentityTransformation, Transformation( [ 2, 2 ] ) ]
gap> S := EndomorphismMonoid(Digraph([[2], [2]]), [1, 2]);
<trivial transformation group of degree 0 with 1 generator>

# BruteForceIsoCheck helper functions
gap> BruteForceIsoCheck := function(iso)
>   local x, y;
>   if not IsInjective(iso) or not IsSurjective(iso) then
>     return false;
>   fi;
>   for x in Generators(Source(iso)) do
>     for y in Generators(Source(iso)) do
>       if x ^ iso * y ^ iso <> (x * y) ^ iso then
>         return false;
>       fi;
>     od;
>   od;
>   return true;
> end;;
gap> BruteForceInverseCheck := function(map)
> local inv;
>   inv := InverseGeneralMapping(map);
>   return ForAll(Source(map), x -> x = (x ^ map) ^ inv)
>     and ForAll(Range(map), x -> x = (x ^ inv) ^ map);
> end;;

# isomorphism from RMS to transformation semigroup
gap> S := RectangularBand(IsReesMatrixSemigroup, 5, 5);;
gap> map := IsomorphismSemigroup(IsTransformationSemigroup, S);
<Rees matrix semigroup 5x5 over Group(())> -> 
<transformation semigroup of size 25, degree 26 with 5 generators>
gap> BruteForceIsoCheck(map);
true
gap> BruteForceInverseCheck(map);
true

# isomorphism from RZMS to transformation semigroup
gap> S := ZeroSemigroup(IsReesZeroMatrixSemigroup, 10);;
gap> map := IsomorphismSemigroup(IsTransformationSemigroup, S);
<Rees 0-matrix semigroup 9x1 over Group(())> -> 
<commutative transformation semigroup of size 10, degree 11 with 9 generators>
gap> BruteForceIsoCheck(map);
true
gap> BruteForceInverseCheck(map);
true

# isomorphism from fp semigroup to transformation semigroup
gap> S := AsSemigroup(IsFpSemigroup, JonesMonoid(5));;
gap> map := IsomorphismSemigroup(IsTransformationSemigroup, S);
<fp semigroup with 5 generators and 28 relations of length 120> -> 
<transformation monoid of size 42, degree 42 with 4 generators>
gap> BruteForceIsoCheck(map);
true
gap> BruteForceInverseCheck(map);
true

# isomorphism from pbr semigroup to transformation semigroup
gap> S := FullPBRMonoid(1);;
gap> map := IsomorphismSemigroup(IsTransformationSemigroup, S);
<pbr monoid of size 16, degree 1 with 4 generators> -> 
<transformation monoid of size 16, degree 16 with 4 generators>
gap> BruteForceIsoCheck(map);
true
gap> BruteForceInverseCheck(map);
true

# isomorphism from bipartition semigroup to transformation semigroup
gap> S := Semigroup(
> Bipartition([[1, 4, 6, 7, 8, 10], [2, 5, -1, -2, -8],
>              [3, -3, -6, -7, -9], [9, -4, -5], [-10]]),
> Bipartition([[1, 2, 6, 7, -3, -4, -6], [3, 4, 5, 10, -2, -10],
>              [8, -8], [9, -1], [-5], [-7, -9]]));;
gap> map := IsomorphismSemigroup(IsTransformationSemigroup, S);
<bipartition semigroup of size 7, degree 10 with 2 generators> -> 
<transformation semigroup of size 7, degree 8 with 2 generators>
gap> BruteForceIsoCheck(map);
true
gap> BruteForceInverseCheck(map);
true

# isomorphism from block bijection semigroup to transformation semigroup
gap> S := Semigroup([
> Bipartition([[1, 3, -2, -5], [2, 4, -1], [5, -3, -4]]),
>  Bipartition([[1, 3, -1], [2, 4, -2, -3], [5, -4, -5]]),
>  Bipartition([[1, 4, 5, -2], [2, 3, -1, -3, -4, -5]]),
>  Bipartition([[1, -5], [2, 3, -1, -2], [4, -4], [5, -3]]),
>  Bipartition([[1, 2, -2], [3, -3, -4, -5], [4, 5, -1]])]);
<block bijection semigroup of degree 5 with 5 generators>
gap> map := IsomorphismSemigroup(IsTransformationSemigroup, S);
<block bijection semigroup of size 54, degree 5 with 5 generators> -> 
<transformation semigroup of size 54, degree 55 with 5 generators>
gap> BruteForceIsoCheck(map);
true
gap> BruteForceInverseCheck(map);
true

# isomorphism from transformation semigroup to transformation semigroup
gap> S := Semigroup(Transformation([5, 2, 2, 3, 2]),
>                   Transformation([1, 4, 2, 3, 4]));;
gap> map := IsomorphismSemigroup(IsTransformationSemigroup, S);;
gap> map = IdentityMapping(S);
true
gap> BruteForceIsoCheck(map);
true
gap> BruteForceInverseCheck(map);
true

# isomorphism from partial perm semigroup to transformation semigroup
gap> S := Semigroup(PartialPerm([1, 2, 3, 4], [4, 5, 1, 2]),
>                   PartialPerm([1, 2, 4], [1, 3, 5]));;
gap> map := IsomorphismSemigroup(IsTransformationSemigroup, S);
<partial perm semigroup of rank 4 with 2 generators> -> 
<transformation semigroup of degree 6 with 2 generators>
gap> BruteForceIsoCheck(map);
true
gap> BruteForceInverseCheck(map);
true

# isomorphism from boolean mat semigroup to transformation semigroup
gap> S := Monoid(Matrix(IsBooleanMat,
>        [[0, 1], [1, 0]]),
>                Matrix(IsBooleanMat,
>        [[0, 1], [1, 0]]),
>                Matrix(IsBooleanMat,
>        [[1, 0], [1, 1]]),
>                Matrix(IsBooleanMat,
>        [[1, 0], [0, 0]]));;
gap> map := IsomorphismSemigroup(IsTransformationSemigroup, S);
<monoid of 2x2 boolean matrices with 4 generators> -> 
<transformation monoid of degree 4 with 4 generators>
gap> BruteForceIsoCheck(map);
true
gap> BruteForceInverseCheck(map);
true

# isomorphism from max plus mat semigroup to transformation semigroup
gap> S := Semigroup(Matrix(IsMaxPlusMatrix,
>        [[0, -4], [-4, -1]]),
>                   Matrix(IsMaxPlusMatrix,
>        [[0, -3], [-3, -1]]));;
gap> map := IsomorphismSemigroup(IsTransformationSemigroup, S);
<semigroup of size 26, 2x2 max-plus matrices with 2 generators> -> 
<transformation semigroup of size 26, degree 27 with 2 generators>
gap> BruteForceIsoCheck(map);
true
gap> BruteForceInverseCheck(map);
true

# isomorphism from min plus mat semigroup to transformation semigroup
gap> S := Semigroup(Matrix(IsMinPlusMatrix,
>        [[0, 4], [4, 1]]),
>                   Matrix(IsMinPlusMatrix,
>        [[0, 3], [3, 1]]));;
gap> map := IsomorphismSemigroup(IsTransformationSemigroup, S);
<semigroup of size 26, 2x2 min-plus matrices with 2 generators> -> 
<transformation semigroup of size 26, degree 27 with 2 generators>
gap> BruteForceIsoCheck(map);
true
gap> BruteForceInverseCheck(map);
true

# isomorphism from tropical max plus mat semigroup to transformation
#   semigroup
gap> S := Semigroup(Matrix(IsTropicalMaxPlusMatrix,
>        [[0, 4], [4, 1]], 10),
>                   Matrix(IsTropicalMaxPlusMatrix,
>        [[0, 3], [3, 1]], 10));;
gap> map := IsomorphismSemigroup(IsTransformationSemigroup, S);
<semigroup of size 13, 2x2 tropical max-plus matrices with 2 generators> -> 
<transformation semigroup of size 13, degree 14 with 2 generators>
gap> BruteForceIsoCheck(map);
true
gap> BruteForceInverseCheck(map);
true

# isomorphism from tropical min plus mat semigroup to transformation
#   semigroup
gap> S := Semigroup(Matrix(IsTropicalMinPlusMatrix,
>        [[0, 4], [4, 1]], 5),
>                   Matrix(IsTropicalMinPlusMatrix,
>        [[0, 3], [3, 1]], 5));;
gap> map := IsomorphismSemigroup(IsTransformationSemigroup, S);
<semigroup of size 18, 2x2 tropical min-plus matrices with 2 generators> -> 
<transformation semigroup of size 18, degree 19 with 2 generators>
gap> BruteForceIsoCheck(map);
true
gap> BruteForceInverseCheck(map);
true

# isomorphism from ntp mat semigroup to transformation
#   semigroup. This is the general linear semigroup over the field with 3
#   elements
gap> S := Monoid(
> Matrix(IsNTPMatrix,
>        [[1, 0, 0],
>         [0, 2, 0],
>         [0, 0, 2]],
>        0, 3),
> Matrix(IsNTPMatrix,
>        [[1, 0, 2],
>         [1, 0, 0],
>         [0, 1, 0]],
>        0, 3),
> Matrix(IsNTPMatrix,
>        [[2, 0, 0],
>         [0, 2, 0],
>         [0, 0, 0]],
>        0, 3));
<monoid of 3x3 ntp matrices with 3 generators>
gap> IsomorphismSemigroup(IsTransformationSemigroup, S);
<monoid of size 19683, 3x3 ntp matrices with 3 generators> -> 
<transformation monoid of size 19683, degree 19683 with 3 generators>

# isomorphism from ntp mat semigroup to transformation
#   semigroup. This is the general linear semigroup over the field with 2
#   elements
gap> S := Monoid(
> Matrix(IsNTPMatrix,
>        [[1, 1], [0, 1]], 0, 2),
> Matrix(IsNTPMatrix,
>        [[0, 1], [1, 0]], 0, 2),
> Matrix(IsNTPMatrix,
>        [[1, 0], [0, 0]], 0, 2));
<monoid of 2x2 ntp matrices with 3 generators>
gap> map := IsomorphismSemigroup(IsTransformationSemigroup, S);
<monoid of size 16, 2x2 ntp matrices with 3 generators> -> 
<transformation monoid of size 16, degree 16 with 3 generators>
gap> BruteForceInverseCheck(map);
true
gap> BruteForceIsoCheck(map);
true

# isomorphism from an integer mat semigroup to transformation semigroup
gap> S := Semigroup(
>  Matrix(Integers,
>     [[0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
>      [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
>      [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
>      [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0],
>      [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
>      [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
>      [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
>      [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
>      [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
>      [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
>      [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
>      [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
>      [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
>      [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
>      [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
>      [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
>      [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]),
>  Matrix(Integers,
>     [[0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
>      [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
>      [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
>      [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
>      [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
>      [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
>      [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
>      [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
>      [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
>      [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
>      [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
>      [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
>      [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
>      [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
>      [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
>      [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
>      [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]),
>  Matrix(Integers,
>     [[1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
>      [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0],
>      [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0],
>      [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
>      [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
>      [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
>      [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
>      [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0],
>      [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
>      [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0],
>      [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
>      [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0],
>      [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
>      [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0],
>      [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
>      [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
>      [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]),
>  Matrix(Integers,
>     [[0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
>      [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
>      [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
>      [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0],
>      [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
>      [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
>      [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
>      [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
>      [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
>      [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
>      [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
>      [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
>      [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
>      [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
>      [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
>      [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
>      [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]));;
gap> map := IsomorphismSemigroup(IsTransformationSemigroup, S);
<semigroup of size 16, 17x17 integer matrices with 4 generators> -> 
<transformation semigroup of size 16, degree 17 with 4 generators>
gap> BruteForceInverseCheck(map);
true
gap> BruteForceIsoCheck(map);
true

# AsSemigroup:
#   convert from IsPBRSemigroup to IsTransformationSemigroup
gap> S := Semigroup([
> PBR([[-2], [-1], [-2], [-2]], [[2], [1, 3, 4], [], []]),
> PBR([[-3], [-3], [-3], [-3]], [[], [], [1, 2, 3, 4], []])]);
<pbr semigroup of degree 4 with 2 generators>
gap> T := AsSemigroup(IsTransformationSemigroup, S);
<transformation semigroup of size 5, degree 6 with 2 generators>
gap> Size(S) = Size(T);
true
gap> NrDClasses(S) = NrDClasses(T);
true
gap> NrRClasses(S) = NrRClasses(T);
true
gap> NrLClasses(S) = NrLClasses(T);
true
gap> NrIdempotents(S) = NrIdempotents(T);
true
gap> map := IsomorphismSemigroup(IsTransformationSemigroup, S);;
gap> BruteForceIsoCheck(map);
true
gap> BruteForceInverseCheck(map);
true

# AsSemigroup:
#   convert from IsFpSemigroup to IsTransformationSemigroup
gap> F := FreeSemigroup(2);; AssignGeneratorVariables(F);;
gap> rels := [[s1 * s2, s2], [s2 ^ 2, s2], [s1 ^ 3, s1]];;
gap> S := F / rels;
<fp semigroup with 2 generators and 3 relations of length 12>
gap> T := AsSemigroup(IsTransformationSemigroup, S);
<transformation semigroup of size 5, degree 6 with 2 generators>
gap> Size(S) = Size(T);
true
gap> NrDClasses(S) = NrDClasses(T);
true
gap> NrRClasses(S) = NrRClasses(T);
true
gap> NrLClasses(S) = NrLClasses(T);
true
gap> NrIdempotents(S) = NrIdempotents(T);
true
gap> map := IsomorphismSemigroup(IsTransformationSemigroup, S);;
gap> BruteForceIsoCheck(map);
true
gap> BruteForceInverseCheck(map);
true

# AsSemigroup:
#   convert from IsBipartitionSemigroup to IsTransformationSemigroup
gap> S := Semigroup([
> Bipartition([[1, 3, 4, -2], [2, -1], [-3], [-4]]),
> Bipartition([[1, 2, 3, 4, -3], [-1], [-2], [-4]])]);
<bipartition semigroup of degree 4 with 2 generators>
gap> T := AsSemigroup(IsTransformationSemigroup, S);
<transformation semigroup of degree 4 with 2 generators>
gap> Size(S) = Size(T);
true
gap> NrDClasses(S) = NrDClasses(T);
true
gap> NrRClasses(S) = NrRClasses(T);
true
gap> NrLClasses(S) = NrLClasses(T);
true
gap> NrIdempotents(S) = NrIdempotents(T);
true
gap> map := IsomorphismSemigroup(IsTransformationSemigroup, S);;
gap> BruteForceIsoCheck(map);
true
gap> BruteForceInverseCheck(map);
true

# AsSemigroup:
#   convert from IsTransformationSemigroup to IsTransformationSemigroup
gap> S := Semigroup([
> Transformation([2, 1, 2, 2]), Transformation([3, 3, 3, 3])]);
<transformation semigroup of degree 4 with 2 generators>
gap> T := AsSemigroup(IsTransformationSemigroup, S);
<transformation semigroup of degree 4 with 2 generators>
gap> Size(S) = Size(T);
true
gap> NrDClasses(S) = NrDClasses(T);
true
gap> NrRClasses(S) = NrRClasses(T);
true
gap> NrLClasses(S) = NrLClasses(T);
true
gap> NrIdempotents(S) = NrIdempotents(T);
true
gap> map := IsomorphismSemigroup(IsTransformationSemigroup, S);;
gap> BruteForceIsoCheck(map);
true
gap> BruteForceInverseCheck(map);
true

# AsSemigroup:
#   convert from IsBooleanMatSemigroup to IsTransformationSemigroup
gap> S := Semigroup([
> Matrix(IsBooleanMat,
>        [[false, true, false, false],
>         [true, false, false, false],
>         [false, true, false, false],
>         [false, true, false, false]]),
> Matrix(IsBooleanMat,
>        [[false, false, true, false],
>         [false, false, true, false],
>         [false, false, true, false],
>         [false, false, true, false]])]);
<semigroup of 4x4 boolean matrices with 2 generators>
gap> T := AsSemigroup(IsTransformationSemigroup, S);
<transformation semigroup of degree 4 with 2 generators>
gap> Size(S) = Size(T);
true
gap> NrDClasses(S) = NrDClasses(T);
true
gap> NrRClasses(S) = NrRClasses(T);
true
gap> NrLClasses(S) = NrLClasses(T);
true
gap> NrIdempotents(S) = NrIdempotents(T);
true
gap> map := IsomorphismSemigroup(IsTransformationSemigroup, S);;
gap> BruteForceIsoCheck(map);
true
gap> BruteForceInverseCheck(map);
true

# AsSemigroup:
#   convert from IsMaxPlusMatrixSemigroup to IsTransformationSemigroup
gap> S := Semigroup([
> Matrix(IsMaxPlusMatrix,
>        [[-infinity, 0, -infinity, -infinity],
>         [0, -infinity, -infinity, -infinity],
>         [-infinity, 0, -infinity, -infinity],
>         [-infinity, 0, -infinity, -infinity]]),
> Matrix(IsMaxPlusMatrix,
>        [[-infinity, -infinity, 0, -infinity],
>         [-infinity, -infinity, 0, -infinity],
>         [-infinity, -infinity, 0, -infinity],
>         [-infinity, -infinity, 0, -infinity]])]);
<semigroup of 4x4 max-plus matrices with 2 generators>
gap> T := AsSemigroup(IsTransformationSemigroup, S);
<transformation semigroup of size 5, degree 6 with 2 generators>
gap> Size(S) = Size(T);
true
gap> NrDClasses(S) = NrDClasses(T);
true
gap> NrRClasses(S) = NrRClasses(T);
true
gap> NrLClasses(S) = NrLClasses(T);
true
gap> NrIdempotents(S) = NrIdempotents(T);
true
gap> map := IsomorphismSemigroup(IsTransformationSemigroup, S);;
gap> BruteForceIsoCheck(map);
true
gap> BruteForceInverseCheck(map);
true

# AsSemigroup:
#   convert from IsMinPlusMatrixSemigroup to IsTransformationSemigroup
gap> S := Semigroup([
> Matrix(IsMinPlusMatrix,
>        [[infinity, 0, infinity, infinity],
>         [0, infinity, infinity, infinity],
>         [infinity, 0, infinity, infinity],
>         [infinity, 0, infinity, infinity]]),
> Matrix(IsMinPlusMatrix,
>        [[infinity, infinity, 0, infinity],
>         [infinity, infinity, 0, infinity],
>         [infinity, infinity, 0, infinity],
>         [infinity, infinity, 0, infinity]])]);
<semigroup of 4x4 min-plus matrices with 2 generators>
gap> T := AsSemigroup(IsTransformationSemigroup, S);
<transformation semigroup of size 5, degree 6 with 2 generators>
gap> Size(S) = Size(T);
true
gap> NrDClasses(S) = NrDClasses(T);
true
gap> NrRClasses(S) = NrRClasses(T);
true
gap> NrLClasses(S) = NrLClasses(T);
true
gap> NrIdempotents(S) = NrIdempotents(T);
true
gap> map := IsomorphismSemigroup(IsTransformationSemigroup, S);;
gap> BruteForceIsoCheck(map);
true
gap> BruteForceInverseCheck(map);
true

# AsSemigroup:
#   convert from IsProjectiveMaxPlusMatrixSemigroup to IsTransformationSemigroup
gap> S := Semigroup([
> Matrix(IsProjectiveMaxPlusMatrix,
>        [[-infinity, 0, -infinity, -infinity],
>         [0, -infinity, -infinity, -infinity],
>         [-infinity, 0, -infinity, -infinity],
>         [-infinity, 0, -infinity, -infinity]]),
> Matrix(IsProjectiveMaxPlusMatrix,
>        [[-infinity, -infinity, 0, -infinity],
>         [-infinity, -infinity, 0, -infinity],
>         [-infinity, -infinity, 0, -infinity],
>         [-infinity, -infinity, 0, -infinity]])]);
<semigroup of 4x4 projective max-plus matrices with 2 generators>
gap> T := AsSemigroup(IsTransformationSemigroup, S);
<transformation semigroup of size 5, degree 6 with 2 generators>
gap> Size(S) = Size(T);
true
gap> NrDClasses(S) = NrDClasses(T);
true
gap> NrRClasses(S) = NrRClasses(T);
true
gap> NrLClasses(S) = NrLClasses(T);
true
gap> NrIdempotents(S) = NrIdempotents(T);
true
gap> map := IsomorphismSemigroup(IsTransformationSemigroup, S);;
gap> BruteForceIsoCheck(map);
true
gap> BruteForceInverseCheck(map);
true

# AsSemigroup:
#   convert from IsIntegerMatrixSemigroup to IsTransformationSemigroup
gap> S := Semigroup([
> Matrix(Integers,
>        [[0, 1, 0, 0],
>         [1, 0, 0, 0],
>         [0, 1, 0, 0],
>         [0, 1, 0, 0]]),
> Matrix(Integers,
>        [[0, 0, 1, 0],
>         [0, 0, 1, 0],
>         [0, 0, 1, 0],
>         [0, 0, 1, 0]])]);
<semigroup of 4x4 integer matrices with 2 generators>
gap> T := AsSemigroup(IsTransformationSemigroup, S);
<transformation semigroup of size 5, degree 6 with 2 generators>
gap> Size(S) = Size(T);
true
gap> NrDClasses(S) = NrDClasses(T);
true
gap> NrRClasses(S) = NrRClasses(T);
true
gap> NrLClasses(S) = NrLClasses(T);
true
gap> NrIdempotents(S) = NrIdempotents(T);
true
gap> map := IsomorphismSemigroup(IsTransformationSemigroup, S);;
gap> BruteForceIsoCheck(map);
true
gap> BruteForceInverseCheck(map);
true

# AsSemigroup:
#   convert from IsTropicalMaxPlusMatrixSemigroup to IsTransformationSemigroup
gap> S := Semigroup([
> Matrix(IsTropicalMaxPlusMatrix,
>        [[-infinity, 0, -infinity, -infinity],
>         [0, -infinity, -infinity, -infinity],
>         [-infinity, 0, -infinity, -infinity],
>         [-infinity, 0, -infinity, -infinity]], 3),
> Matrix(IsTropicalMaxPlusMatrix,
>        [[-infinity, -infinity, 0, -infinity],
>         [-infinity, -infinity, 0, -infinity],
>         [-infinity, -infinity, 0, -infinity],
>         [-infinity, -infinity, 0, -infinity]], 3)]);
<semigroup of 4x4 tropical max-plus matrices with 2 generators>
gap> T := AsSemigroup(IsTransformationSemigroup, S);
<transformation semigroup of size 5, degree 6 with 2 generators>
gap> Size(S) = Size(T);
true
gap> NrDClasses(S) = NrDClasses(T);
true
gap> NrRClasses(S) = NrRClasses(T);
true
gap> NrLClasses(S) = NrLClasses(T);
true
gap> NrIdempotents(S) = NrIdempotents(T);
true
gap> map := IsomorphismSemigroup(IsTransformationSemigroup, S);;
gap> BruteForceIsoCheck(map);
true
gap> BruteForceInverseCheck(map);
true

# AsSemigroup:
#   convert from IsTropicalMinPlusMatrixSemigroup to IsTransformationSemigroup
gap> S := Semigroup([
> Matrix(IsTropicalMinPlusMatrix,
>        [[infinity, 0, infinity, infinity],
>         [0, infinity, infinity, infinity],
>         [infinity, 0, infinity, infinity],
>         [infinity, 0, infinity, infinity]], 5),
> Matrix(IsTropicalMinPlusMatrix,
>        [[infinity, infinity, 0, infinity],
>         [infinity, infinity, 0, infinity],
>         [infinity, infinity, 0, infinity],
>         [infinity, infinity, 0, infinity]], 5)]);
<semigroup of 4x4 tropical min-plus matrices with 2 generators>
gap> T := AsSemigroup(IsTransformationSemigroup, S);
<transformation semigroup of size 5, degree 6 with 2 generators>
gap> Size(S) = Size(T);
true
gap> NrDClasses(S) = NrDClasses(T);
true
gap> NrRClasses(S) = NrRClasses(T);
true
gap> NrLClasses(S) = NrLClasses(T);
true
gap> NrIdempotents(S) = NrIdempotents(T);
true
gap> map := IsomorphismSemigroup(IsTransformationSemigroup, S);;
gap> BruteForceIsoCheck(map);
true
gap> BruteForceInverseCheck(map);
true

# AsSemigroup:
#   convert from IsNTPMatrixSemigroup to IsTransformationSemigroup
gap> S := Semigroup([
> Matrix(IsNTPMatrix,
>        [[0, 1, 0, 0],
>         [1, 0, 0, 0],
>         [0, 1, 0, 0],
>         [0, 1, 0, 0]], 5, 1),
> Matrix(IsNTPMatrix,
>        [[0, 0, 1, 0],
>         [0, 0, 1, 0],
>         [0, 0, 1, 0],
>         [0, 0, 1, 0]], 5, 1)]);
<semigroup of 4x4 ntp matrices with 2 generators>
gap> T := AsSemigroup(IsTransformationSemigroup, S);
<transformation semigroup of size 5, degree 6 with 2 generators>
gap> Size(S) = Size(T);
true
gap> NrDClasses(S) = NrDClasses(T);
true
gap> NrRClasses(S) = NrRClasses(T);
true
gap> NrLClasses(S) = NrLClasses(T);
true
gap> NrIdempotents(S) = NrIdempotents(T);
true
gap> map := IsomorphismSemigroup(IsTransformationSemigroup, S);;
gap> BruteForceIsoCheck(map);
true
gap> BruteForceInverseCheck(map);
true

# AsSemigroup:
#   convert from IsReesZeroMatrixSemigroup to IsTransformationSemigroup
gap> S := ReesZeroMatrixSemigroup(Group([(1, 2)]), [[()], [()]]);
<Rees 0-matrix semigroup 1x2 over Group([ (1,2) ])>
gap> T := AsSemigroup(IsTransformationSemigroup, S);
<transformation semigroup of size 5, degree 6 with 3 generators>
gap> Size(S) = Size(T);
true
gap> NrDClasses(S) = NrDClasses(T);
true
gap> NrRClasses(S) = NrRClasses(T);
true
gap> NrLClasses(S) = NrLClasses(T);
true
gap> NrIdempotents(S) = NrIdempotents(T);
true
gap> map := IsomorphismSemigroup(IsTransformationSemigroup, S);;
gap> BruteForceIsoCheck(map);
true
gap> BruteForceInverseCheck(map);
true

# AsMonoid:
#   convert from IsReesZeroMatrixSemigroup to IsTransformationMonoid
gap> S := ReesZeroMatrixSemigroup(Group([(1, 2)]), [[()]]);
<Rees 0-matrix semigroup 1x1 over Group([ (1,2) ])>
gap> T := AsMonoid(IsTransformationMonoid, S);
<transformation monoid of size 3, degree 3 with 2 generators>
gap> Size(S) = Size(T);
true
gap> NrDClasses(S) = NrDClasses(T);
true
gap> NrRClasses(S) = NrRClasses(T);
true
gap> NrLClasses(S) = NrLClasses(T);
true
gap> NrIdempotents(S) = NrIdempotents(T);
true
gap> map := IsomorphismMonoid(IsTransformationMonoid, S);;
gap> BruteForceIsoCheck(map);
true
gap> BruteForceInverseCheck(map);
true

# AsSemigroup:
#   convert from IsReesMatrixSemigroup to IsTransformationSemigroup
gap> S := ReesMatrixSemigroup(Group([(1, 2)]), [[()], [()]]);
<Rees matrix semigroup 1x2 over Group([ (1,2) ])>
gap> T := AsSemigroup(IsTransformationSemigroup, S);
<transformation semigroup of size 4, degree 5 with 2 generators>
gap> Size(S) = Size(T);
true
gap> NrDClasses(S) = NrDClasses(T);
true
gap> NrRClasses(S) = NrRClasses(T);
true
gap> NrLClasses(S) = NrLClasses(T);
true
gap> NrIdempotents(S) = NrIdempotents(T);
true
gap> map := IsomorphismSemigroup(IsTransformationSemigroup, S);;
gap> BruteForceIsoCheck(map);
true
gap> BruteForceInverseCheck(map);
true

# AsMonoid:
#   convert from IsReesMatrixSemigroup to IsTransformationMonoid
gap> S := ReesMatrixSemigroup(Group([(1, 2)]), [[()]]);
<Rees matrix semigroup 1x1 over Group([ (1,2) ])>
gap> T := AsMonoid(IsTransformationMonoid, S);
<commutative transformation monoid of size 2, degree 2 with 1 generator>
gap> Size(S) = Size(T);
true
gap> NrDClasses(S) = NrDClasses(T);
true
gap> NrRClasses(S) = NrRClasses(T);
true
gap> NrLClasses(S) = NrLClasses(T);
true
gap> NrIdempotents(S) = NrIdempotents(T);
true
gap> map := IsomorphismMonoid(IsTransformationMonoid, S);;
gap> BruteForceIsoCheck(map);
true
gap> BruteForceInverseCheck(map);
true

# AsSemigroup:
#   convert from IsReesZeroMatrixSemigroup to IsTransformationSemigroup
gap> S := ReesZeroMatrixSemigroup(Group([(1, 2)]), [[()], [0]]);
<Rees 0-matrix semigroup 1x2 over Group([ (1,2) ])>
gap> T := AsSemigroup(IsTransformationSemigroup, S);
<transformation semigroup of size 5, degree 6 with 4 generators>
gap> Size(S) = Size(T);
true
gap> NrDClasses(S) = NrDClasses(T);
true
gap> NrRClasses(S) = NrRClasses(T);
true
gap> NrLClasses(S) = NrLClasses(T);
true
gap> NrIdempotents(S) = NrIdempotents(T);
true
gap> map := IsomorphismSemigroup(IsTransformationSemigroup, S);;
gap> BruteForceIsoCheck(map);
true
gap> BruteForceInverseCheck(map);
true

# AsSemigroup:
#   convert from IsPBRMonoid to IsTransformationSemigroup
gap> S := Monoid([
> PBR([[-2], [-3], [-2]], [[], [1, 3], [2]]),
> PBR([[-2], [-2], [-2]], [[], [1, 2, 3], []])]);
<pbr monoid of degree 3 with 2 generators>
gap> T := AsSemigroup(IsTransformationSemigroup, S);
<transformation monoid of size 5, degree 5 with 2 generators>
gap> Size(S) = Size(T);
true
gap> NrDClasses(S) = NrDClasses(T);
true
gap> NrRClasses(S) = NrRClasses(T);
true
gap> NrLClasses(S) = NrLClasses(T);
true
gap> NrIdempotents(S) = NrIdempotents(T);
true
gap> map := IsomorphismSemigroup(IsTransformationSemigroup, S);;
gap> BruteForceIsoCheck(map);
true
gap> BruteForceInverseCheck(map);
true

# AsSemigroup:
#   convert from IsFpMonoid to IsTransformationSemigroup
gap> F := FreeMonoid(2);; AssignGeneratorVariables(F);;
gap> rels := [[m1 * m2, m2], [m2 ^ 2, m2], [m1 ^ 3, m1], [m2 * m1 ^ 2, m2]];;
gap> S := F / rels;
<fp monoid with 2 generators and 4 relations of length 16>
gap> T := AsSemigroup(IsTransformationSemigroup, S);
<transformation monoid of size 5, degree 5 with 2 generators>
gap> Size(S) = Size(T);
true
gap> NrDClasses(S) = NrDClasses(T);
true
gap> NrRClasses(S) = NrRClasses(T);
true
gap> NrLClasses(S) = NrLClasses(T);
true
gap> NrIdempotents(S) = NrIdempotents(T);
true
gap> map := IsomorphismSemigroup(IsTransformationSemigroup, S);;
gap> BruteForceIsoCheck(map);
true
gap> BruteForceInverseCheck(map);
true

# AsSemigroup:
#   convert from IsBipartitionMonoid to IsTransformationSemigroup
gap> S := Monoid([
> Bipartition([[1, 3, -2], [2, -3], [-1]]),
> Bipartition([[1, 2, 3, -2], [-1], [-3]])]);
<bipartition monoid of degree 3 with 2 generators>
gap> T := AsSemigroup(IsTransformationSemigroup, S);
<transformation monoid of degree 3 with 2 generators>
gap> Size(S) = Size(T);
true
gap> NrDClasses(S) = NrDClasses(T);
true
gap> NrRClasses(S) = NrRClasses(T);
true
gap> NrLClasses(S) = NrLClasses(T);
true
gap> NrIdempotents(S) = NrIdempotents(T);
true
gap> map := IsomorphismSemigroup(IsTransformationSemigroup, S);;
gap> BruteForceIsoCheck(map);
true
gap> BruteForceInverseCheck(map);
true

# AsSemigroup:
#   convert from IsTransformationMonoid to IsTransformationSemigroup
gap> S := Monoid([
> Transformation([2, 3, 2]), Transformation([2, 2, 2])]);
<transformation monoid of degree 3 with 2 generators>
gap> T := AsSemigroup(IsTransformationSemigroup, S);
<transformation monoid of degree 3 with 2 generators>
gap> Size(S) = Size(T);
true
gap> NrDClasses(S) = NrDClasses(T);
true
gap> NrRClasses(S) = NrRClasses(T);
true
gap> NrLClasses(S) = NrLClasses(T);
true
gap> NrIdempotents(S) = NrIdempotents(T);
true
gap> map := IsomorphismSemigroup(IsTransformationSemigroup, S);;
gap> BruteForceIsoCheck(map);
true
gap> BruteForceInverseCheck(map);
true

# AsSemigroup:
#   convert from IsBooleanMatMonoid to IsTransformationSemigroup
gap> S := Monoid([
> Matrix(IsBooleanMat,
>        [[false, true, false],
>         [false, false, true],
>         [false, true, false]]),
> Matrix(IsBooleanMat,
>        [[false, true, false],
>         [false, true, false],
>         [false, true, false]])]);
<monoid of 3x3 boolean matrices with 2 generators>
gap> T := AsSemigroup(IsTransformationSemigroup, S);
<transformation monoid of degree 3 with 2 generators>
gap> Size(S) = Size(T);
true
gap> NrDClasses(S) = NrDClasses(T);
true
gap> NrRClasses(S) = NrRClasses(T);
true
gap> NrLClasses(S) = NrLClasses(T);
true
gap> NrIdempotents(S) = NrIdempotents(T);
true
gap> map := IsomorphismSemigroup(IsTransformationSemigroup, S);;
gap> BruteForceIsoCheck(map);
true
gap> BruteForceInverseCheck(map);
true

# AsSemigroup:
#   convert from IsMaxPlusMatrixMonoid to IsTransformationSemigroup
gap> S := Monoid([
> Matrix(IsMaxPlusMatrix,
>        [[-infinity, 0, -infinity],
>         [-infinity, -infinity, 0],
>         [-infinity, 0, -infinity]]),
> Matrix(IsMaxPlusMatrix,
>        [[-infinity, 0, -infinity],
>         [-infinity, 0, -infinity],
>         [-infinity, 0, -infinity]])]);
<monoid of 3x3 max-plus matrices with 2 generators>
gap> T := AsSemigroup(IsTransformationSemigroup, S);
<transformation monoid of size 5, degree 5 with 2 generators>
gap> Size(S) = Size(T);
true
gap> NrDClasses(S) = NrDClasses(T);
true
gap> NrRClasses(S) = NrRClasses(T);
true
gap> NrLClasses(S) = NrLClasses(T);
true
gap> NrIdempotents(S) = NrIdempotents(T);
true
gap> map := IsomorphismSemigroup(IsTransformationSemigroup, S);;
gap> BruteForceIsoCheck(map);
true
gap> BruteForceInverseCheck(map);
true

# AsSemigroup:
#   convert from IsMinPlusMatrixMonoid to IsTransformationSemigroup
gap> S := Monoid([
> Matrix(IsMinPlusMatrix,
>        [[infinity, 0, infinity],
>         [infinity, infinity, 0],
>         [infinity, 0, infinity]]),
> Matrix(IsMinPlusMatrix,
>        [[infinity, 0, infinity],
>         [infinity, 0, infinity],
>         [infinity, 0, infinity]])]);
<monoid of 3x3 min-plus matrices with 2 generators>
gap> T := AsSemigroup(IsTransformationSemigroup, S);
<transformation monoid of size 5, degree 5 with 2 generators>
gap> Size(S) = Size(T);
true
gap> NrDClasses(S) = NrDClasses(T);
true
gap> NrRClasses(S) = NrRClasses(T);
true
gap> NrLClasses(S) = NrLClasses(T);
true
gap> NrIdempotents(S) = NrIdempotents(T);
true
gap> map := IsomorphismSemigroup(IsTransformationSemigroup, S);;
gap> BruteForceIsoCheck(map);
true
gap> BruteForceInverseCheck(map);
true

# AsSemigroup:
#   convert from IsProjectiveMaxPlusMatrixMonoid to IsTransformationSemigroup
gap> S := Monoid([
> Matrix(IsProjectiveMaxPlusMatrix,
>        [[-infinity, 0, -infinity],
>         [-infinity, -infinity, 0],
>         [-infinity, 0, -infinity]]),
> Matrix(IsProjectiveMaxPlusMatrix,
>        [[-infinity, 0, -infinity],
>         [-infinity, 0, -infinity],
>         [-infinity, 0, -infinity]])]);
<monoid of 3x3 projective max-plus matrices with 2 generators>
gap> T := AsSemigroup(IsTransformationSemigroup, S);
<transformation monoid of size 5, degree 5 with 2 generators>
gap> Size(S) = Size(T);
true
gap> NrDClasses(S) = NrDClasses(T);
true
gap> NrRClasses(S) = NrRClasses(T);
true
gap> NrLClasses(S) = NrLClasses(T);
true
gap> NrIdempotents(S) = NrIdempotents(T);
true
gap> map := IsomorphismSemigroup(IsTransformationSemigroup, S);;
gap> BruteForceIsoCheck(map);
true
gap> BruteForceInverseCheck(map);
true

# AsSemigroup:
#   convert from IsIntegerMatrixMonoid to IsTransformationSemigroup
gap> S := Monoid([
> Matrix(Integers,
>        [[0, 1, 0],
>         [0, 0, 1],
>         [0, 1, 0]]),
> Matrix(Integers,
>        [[0, 1, 0],
>         [0, 1, 0],
>         [0, 1, 0]])]);
<monoid of 3x3 integer matrices with 2 generators>
gap> T := AsSemigroup(IsTransformationSemigroup, S);
<transformation monoid of size 5, degree 5 with 2 generators>
gap> Size(S) = Size(T);
true
gap> NrDClasses(S) = NrDClasses(T);
true
gap> NrRClasses(S) = NrRClasses(T);
true
gap> NrLClasses(S) = NrLClasses(T);
true
gap> NrIdempotents(S) = NrIdempotents(T);
true
gap> map := IsomorphismSemigroup(IsTransformationSemigroup, S);;
gap> BruteForceIsoCheck(map);
true
gap> BruteForceInverseCheck(map);
true

# AsSemigroup:
#   convert from IsTropicalMaxPlusMatrixMonoid to IsTransformationSemigroup
gap> S := Monoid([
> Matrix(IsTropicalMaxPlusMatrix,
>        [[-infinity, 0, -infinity],
>         [-infinity, -infinity, 0],
>         [-infinity, 0, -infinity]], 5),
> Matrix(IsTropicalMaxPlusMatrix,
>        [[-infinity, 0, -infinity],
>         [-infinity, 0, -infinity],
>         [-infinity, 0, -infinity]], 5)]);
<monoid of 3x3 tropical max-plus matrices with 2 generators>
gap> T := AsSemigroup(IsTransformationSemigroup, S);
<transformation monoid of size 5, degree 5 with 2 generators>
gap> Size(S) = Size(T);
true
gap> NrDClasses(S) = NrDClasses(T);
true
gap> NrRClasses(S) = NrRClasses(T);
true
gap> NrLClasses(S) = NrLClasses(T);
true
gap> NrIdempotents(S) = NrIdempotents(T);
true
gap> map := IsomorphismSemigroup(IsTransformationSemigroup, S);;
gap> BruteForceIsoCheck(map);
true
gap> BruteForceInverseCheck(map);
true

# AsSemigroup:
#   convert from IsTropicalMinPlusMatrixMonoid to IsTransformationSemigroup
gap> S := Monoid([
> Matrix(IsTropicalMinPlusMatrix,
>        [[infinity, 0, infinity],
>         [infinity, infinity, 0],
>         [infinity, 0, infinity]], 1),
> Matrix(IsTropicalMinPlusMatrix,
>        [[infinity, 0, infinity],
>         [infinity, 0, infinity],
>         [infinity, 0, infinity]], 1)]);
<monoid of 3x3 tropical min-plus matrices with 2 generators>
gap> T := AsSemigroup(IsTransformationSemigroup, S);
<transformation monoid of size 5, degree 5 with 2 generators>
gap> Size(S) = Size(T);
true
gap> NrDClasses(S) = NrDClasses(T);
true
gap> NrRClasses(S) = NrRClasses(T);
true
gap> NrLClasses(S) = NrLClasses(T);
true
gap> NrIdempotents(S) = NrIdempotents(T);
true
gap> map := IsomorphismSemigroup(IsTransformationSemigroup, S);;
gap> BruteForceIsoCheck(map);
true
gap> BruteForceInverseCheck(map);
true

# AsSemigroup:
#   convert from IsNTPMatrixMonoid to IsTransformationSemigroup
gap> S := Monoid([
> Matrix(IsNTPMatrix,
>        [[0, 1, 0],
>         [0, 0, 1],
>         [0, 1, 0]], 1, 3),
> Matrix(IsNTPMatrix,
>        [[0, 1, 0],
>         [0, 1, 0],
>         [0, 1, 0]], 1, 3)]);
<monoid of 3x3 ntp matrices with 2 generators>
gap> T := AsSemigroup(IsTransformationSemigroup, S);
<transformation monoid of size 5, degree 5 with 2 generators>
gap> Size(S) = Size(T);
true
gap> NrDClasses(S) = NrDClasses(T);
true
gap> NrRClasses(S) = NrRClasses(T);
true
gap> NrLClasses(S) = NrLClasses(T);
true
gap> NrIdempotents(S) = NrIdempotents(T);
true
gap> map := IsomorphismSemigroup(IsTransformationSemigroup, S);;
gap> BruteForceIsoCheck(map);
true
gap> BruteForceInverseCheck(map);
true

# AsMonoid:
#   convert from IsPBRMonoid to IsTransformationMonoid
gap> S := Monoid([
> PBR([[-2], [-3], [-2]], [[], [1, 3], [2]]),
> PBR([[-2], [-2], [-2]], [[], [1, 2, 3], []])]);
<pbr monoid of degree 3 with 2 generators>
gap> T := AsMonoid(IsTransformationMonoid, S);
<transformation monoid of size 5, degree 5 with 2 generators>
gap> Size(S) = Size(T);
true
gap> NrDClasses(S) = NrDClasses(T);
true
gap> NrRClasses(S) = NrRClasses(T);
true
gap> NrLClasses(S) = NrLClasses(T);
true
gap> NrIdempotents(S) = NrIdempotents(T);
true
gap> map := IsomorphismMonoid(IsTransformationMonoid, S);;
gap> BruteForceIsoCheck(map);
true
gap> BruteForceInverseCheck(map);
true

# AsMonoid:
#   convert from IsFpMonoid to IsTransformationMonoid
gap> F := FreeMonoid(2);; AssignGeneratorVariables(F);;
gap> rels := [[m1 * m2, m2], [m2 ^ 2, m2], [m1 ^ 3, m1], [m2 * m1 ^ 2, m2]];;
gap> S := F / rels;
<fp monoid with 2 generators and 4 relations of length 16>
gap> T := AsMonoid(IsTransformationMonoid, S);
<transformation monoid of size 5, degree 5 with 2 generators>
gap> Size(S) = Size(T);
true
gap> NrDClasses(S) = NrDClasses(T);
true
gap> NrRClasses(S) = NrRClasses(T);
true
gap> NrLClasses(S) = NrLClasses(T);
true
gap> NrIdempotents(S) = NrIdempotents(T);
true
gap> map := IsomorphismMonoid(IsTransformationMonoid, S);;
gap> BruteForceIsoCheck(map);
true
gap> BruteForceInverseCheck(map);
true

# AsMonoid:
#   convert from IsBipartitionMonoid to IsTransformationMonoid
gap> S := Monoid([
> Bipartition([[1, 3, -2], [2, -3], [-1]]),
> Bipartition([[1, 2, 3, -2], [-1], [-3]])]);
<bipartition monoid of degree 3 with 2 generators>
gap> T := AsMonoid(IsTransformationMonoid, S);
<transformation monoid of degree 3 with 2 generators>
gap> Size(S) = Size(T);
true
gap> NrDClasses(S) = NrDClasses(T);
true
gap> NrRClasses(S) = NrRClasses(T);
true
gap> NrLClasses(S) = NrLClasses(T);
true
gap> NrIdempotents(S) = NrIdempotents(T);
true
gap> map := IsomorphismMonoid(IsTransformationMonoid, S);;
gap> BruteForceIsoCheck(map);
true
gap> BruteForceInverseCheck(map);
true

# AsMonoid:
#   convert from IsTransformationMonoid to IsTransformationMonoid
gap> S := Monoid([
> Transformation([2, 3, 2]), Transformation([2, 2, 2])]);
<transformation monoid of degree 3 with 2 generators>
gap> T := AsMonoid(IsTransformationMonoid, S);
<transformation monoid of degree 3 with 2 generators>
gap> Size(S) = Size(T);
true
gap> NrDClasses(S) = NrDClasses(T);
true
gap> NrRClasses(S) = NrRClasses(T);
true
gap> NrLClasses(S) = NrLClasses(T);
true
gap> NrIdempotents(S) = NrIdempotents(T);
true
gap> map := IsomorphismMonoid(IsTransformationMonoid, S);;
gap> BruteForceIsoCheck(map);
true
gap> BruteForceInverseCheck(map);
true

# AsMonoid:
#   convert from IsBooleanMatMonoid to IsTransformationMonoid
gap> S := Monoid([
> Matrix(IsBooleanMat,
>        [[false, true, false],
>         [false, false, true],
>         [false, true, false]]),
> Matrix(IsBooleanMat,
>        [[false, true, false],
>         [false, true, false],
>         [false, true, false]])]);
<monoid of 3x3 boolean matrices with 2 generators>
gap> T := AsMonoid(IsTransformationMonoid, S);
<transformation monoid of degree 3 with 2 generators>
gap> Size(S) = Size(T);
true
gap> NrDClasses(S) = NrDClasses(T);
true
gap> NrRClasses(S) = NrRClasses(T);
true
gap> NrLClasses(S) = NrLClasses(T);
true
gap> NrIdempotents(S) = NrIdempotents(T);
true
gap> map := IsomorphismMonoid(IsTransformationMonoid, S);;
gap> BruteForceIsoCheck(map);
true
gap> BruteForceInverseCheck(map);
true

# AsMonoid:
#   convert from IsMaxPlusMatrixMonoid to IsTransformationMonoid
gap> S := Monoid([
> Matrix(IsMaxPlusMatrix,
>        [[-infinity, 0, -infinity],
>         [-infinity, -infinity, 0],
>         [-infinity, 0, -infinity]]),
> Matrix(IsMaxPlusMatrix,
>        [[-infinity, 0, -infinity],
>         [-infinity, 0, -infinity],
>         [-infinity, 0, -infinity]])]);
<monoid of 3x3 max-plus matrices with 2 generators>
gap> T := AsMonoid(IsTransformationMonoid, S);
<transformation monoid of size 5, degree 5 with 2 generators>
gap> Size(S) = Size(T);
true
gap> NrDClasses(S) = NrDClasses(T);
true
gap> NrRClasses(S) = NrRClasses(T);
true
gap> NrLClasses(S) = NrLClasses(T);
true
gap> NrIdempotents(S) = NrIdempotents(T);
true
gap> map := IsomorphismMonoid(IsTransformationMonoid, S);;
gap> BruteForceIsoCheck(map);
true
gap> BruteForceInverseCheck(map);
true

# AsMonoid:
#   convert from IsMinPlusMatrixMonoid to IsTransformationMonoid
gap> S := Monoid([
> Matrix(IsMinPlusMatrix,
>        [[infinity, 0, infinity],
>         [infinity, infinity, 0],
>         [infinity, 0, infinity]]),
> Matrix(IsMinPlusMatrix,
>        [[infinity, 0, infinity],
>         [infinity, 0, infinity],
>         [infinity, 0, infinity]])]);
<monoid of 3x3 min-plus matrices with 2 generators>
gap> T := AsMonoid(IsTransformationMonoid, S);
<transformation monoid of size 5, degree 5 with 2 generators>
gap> Size(S) = Size(T);
true
gap> NrDClasses(S) = NrDClasses(T);
true
gap> NrRClasses(S) = NrRClasses(T);
true
gap> NrLClasses(S) = NrLClasses(T);
true
gap> NrIdempotents(S) = NrIdempotents(T);
true
gap> map := IsomorphismMonoid(IsTransformationMonoid, S);;
gap> BruteForceIsoCheck(map);
true
gap> BruteForceInverseCheck(map);
true

# AsMonoid:
#   convert from IsProjectiveMaxPlusMatrixMonoid to IsTransformationMonoid
gap> S := Monoid([
> Matrix(IsProjectiveMaxPlusMatrix,
>        [[-infinity, 0, -infinity],
>         [-infinity, -infinity, 0],
>         [-infinity, 0, -infinity]]),
> Matrix(IsProjectiveMaxPlusMatrix,
>        [[-infinity, 0, -infinity],
>         [-infinity, 0, -infinity],
>         [-infinity, 0, -infinity]])]);
<monoid of 3x3 projective max-plus matrices with 2 generators>
gap> T := AsMonoid(IsTransformationMonoid, S);
<transformation monoid of size 5, degree 5 with 2 generators>
gap> Size(S) = Size(T);
true
gap> NrDClasses(S) = NrDClasses(T);
true
gap> NrRClasses(S) = NrRClasses(T);
true
gap> NrLClasses(S) = NrLClasses(T);
true
gap> NrIdempotents(S) = NrIdempotents(T);
true
gap> map := IsomorphismMonoid(IsTransformationMonoid, S);;
gap> BruteForceIsoCheck(map);
true
gap> BruteForceInverseCheck(map);
true

# AsMonoid:
#   convert from IsIntegerMatrixMonoid to IsTransformationMonoid
gap> S := Monoid([
> Matrix(Integers,
>        [[0, 1, 0],
>         [0, 0, 1],
>         [0, 1, 0]]),
> Matrix(Integers,
>        [[0, 1, 0],
>         [0, 1, 0],
>         [0, 1, 0]])]);
<monoid of 3x3 integer matrices with 2 generators>
gap> T := AsMonoid(IsTransformationMonoid, S);
<transformation monoid of size 5, degree 5 with 2 generators>
gap> Size(S) = Size(T);
true
gap> NrDClasses(S) = NrDClasses(T);
true
gap> NrRClasses(S) = NrRClasses(T);
true
gap> NrLClasses(S) = NrLClasses(T);
true
gap> NrIdempotents(S) = NrIdempotents(T);
true
gap> map := IsomorphismMonoid(IsTransformationMonoid, S);;
gap> BruteForceIsoCheck(map);
true
gap> BruteForceInverseCheck(map);
true

# AsMonoid:
#   convert from IsTropicalMaxPlusMatrixMonoid to IsTransformationMonoid
gap> S := Monoid([
> Matrix(IsTropicalMaxPlusMatrix,
>        [[-infinity, 0, -infinity],
>         [-infinity, -infinity, 0],
>         [-infinity, 0, -infinity]], 4),
> Matrix(IsTropicalMaxPlusMatrix,
>        [[-infinity, 0, -infinity],
>         [-infinity, 0, -infinity],
>         [-infinity, 0, -infinity]], 4)]);
<monoid of 3x3 tropical max-plus matrices with 2 generators>
gap> T := AsMonoid(IsTransformationMonoid, S);
<transformation monoid of size 5, degree 5 with 2 generators>
gap> Size(S) = Size(T);
true
gap> NrDClasses(S) = NrDClasses(T);
true
gap> NrRClasses(S) = NrRClasses(T);
true
gap> NrLClasses(S) = NrLClasses(T);
true
gap> NrIdempotents(S) = NrIdempotents(T);
true
gap> map := IsomorphismMonoid(IsTransformationMonoid, S);;
gap> BruteForceIsoCheck(map);
true
gap> BruteForceInverseCheck(map);
true

# AsMonoid:
#   convert from IsTropicalMinPlusMatrixMonoid to IsTransformationMonoid
gap> S := Monoid([
> Matrix(IsTropicalMinPlusMatrix,
>        [[infinity, 0, infinity],
>         [infinity, infinity, 0],
>         [infinity, 0, infinity]], 5),
> Matrix(IsTropicalMinPlusMatrix,
>        [[infinity, 0, infinity],
>         [infinity, 0, infinity],
>         [infinity, 0, infinity]], 5)]);
<monoid of 3x3 tropical min-plus matrices with 2 generators>
gap> T := AsMonoid(IsTransformationMonoid, S);
<transformation monoid of size 5, degree 5 with 2 generators>
gap> Size(S) = Size(T);
true
gap> NrDClasses(S) = NrDClasses(T);
true
gap> NrRClasses(S) = NrRClasses(T);
true
gap> NrLClasses(S) = NrLClasses(T);
true
gap> NrIdempotents(S) = NrIdempotents(T);
true
gap> map := IsomorphismMonoid(IsTransformationMonoid, S);;
gap> BruteForceIsoCheck(map);
true
gap> BruteForceInverseCheck(map);
true

# AsMonoid:
#   convert from IsNTPMatrixMonoid to IsTransformationMonoid
gap> S := Monoid([
> Matrix(IsNTPMatrix,
>        [[0, 1, 0],
>         [0, 0, 1],
>         [0, 1, 0]], 5, 1),
> Matrix(IsNTPMatrix,
>        [[0, 1, 0],
>         [0, 1, 0],
>         [0, 1, 0]], 5, 1)]);
<monoid of 3x3 ntp matrices with 2 generators>
gap> T := AsMonoid(IsTransformationMonoid, S);
<transformation monoid of size 5, degree 5 with 2 generators>
gap> Size(S) = Size(T);
true
gap> NrDClasses(S) = NrDClasses(T);
true
gap> NrRClasses(S) = NrRClasses(T);
true
gap> NrLClasses(S) = NrLClasses(T);
true
gap> NrIdempotents(S) = NrIdempotents(T);
true
gap> map := IsomorphismMonoid(IsTransformationMonoid, S);;
gap> BruteForceIsoCheck(map);
true
gap> BruteForceInverseCheck(map);
true

# AsMonoid:
#   convert from IsPBRSemigroup to IsTransformationMonoid
gap> S := Semigroup([
> PBR([[-1], [-2], [-2], [-2], [-2]], [[1], [2, 3, 4, 5], [], [], []]),
> PBR([[-2], [-1], [-1], [-1], [-1]], [[2, 3, 4, 5], [1], [], [], []])]);
<pbr semigroup of degree 5 with 2 generators>
gap> T := AsMonoid(IsTransformationMonoid, S);
<commutative transformation monoid of size 2, degree 2 with 1 generator>
gap> Size(S) = Size(T);
true
gap> NrDClasses(S) = NrDClasses(T);
true
gap> NrRClasses(S) = NrRClasses(T);
true
gap> NrLClasses(S) = NrLClasses(T);
true
gap> NrIdempotents(S) = NrIdempotents(T);
true
gap> map := IsomorphismMonoid(IsTransformationMonoid, S);;
gap> BruteForceIsoCheck(map);
true
gap> BruteForceInverseCheck(map);
true

# AsMonoid:
#   convert from IsFpSemigroup to IsTransformationMonoid
gap> F := FreeSemigroup(2);; AssignGeneratorVariables(F);;
gap> rels := [[s1 ^ 2, s1], [s1 * s2, s2], [s2 * s1, s2], [s2 ^ 2, s1]];;
gap> S := F / rels;
<fp semigroup with 2 generators and 4 relations of length 14>
gap> T := AsMonoid(IsTransformationMonoid, S);
<commutative transformation monoid of size 2, degree 2 with 1 generator>
gap> Size(S) = Size(T);
true
gap> NrDClasses(S) = NrDClasses(T);
true
gap> NrRClasses(S) = NrRClasses(T);
true
gap> NrLClasses(S) = NrLClasses(T);
true
gap> NrIdempotents(S) = NrIdempotents(T);
true
gap> map := IsomorphismMonoid(IsTransformationMonoid, S);;
gap> BruteForceIsoCheck(map);
true
gap> BruteForceInverseCheck(map);
true

# AsMonoid:
#   convert from IsBipartitionSemigroup to IsTransformationMonoid
gap> S := Semigroup([
> Bipartition([[1, -1], [2, 3, 4, 5, -2], [-3], [-4], [-5]]),
> Bipartition([[1, -2], [2, 3, 4, 5, -1], [-3], [-4], [-5]])]);
<bipartition semigroup of degree 5 with 2 generators>
gap> T := AsMonoid(IsTransformationMonoid, S);;
gap> Size(S) = Size(T);
true
gap> NrDClasses(S) = NrDClasses(T);
true
gap> NrRClasses(S) = NrRClasses(T);
true
gap> NrLClasses(S) = NrLClasses(T);
true
gap> NrIdempotents(S) = NrIdempotents(T);
true
gap> map := IsomorphismMonoid(IsTransformationMonoid, S);;
gap> BruteForceIsoCheck(map);
true
gap> BruteForceInverseCheck(map);
true

# AsMonoid:
#   convert from IsTransformationSemigroup to IsTransformationMonoid
gap> S := Semigroup([
> Transformation([1, 2, 2, 2, 2]), Transformation([2, 1, 1, 1, 1])]);
<transformation semigroup of degree 5 with 2 generators>
gap> T := AsMonoid(IsTransformationMonoid, S);;
gap> Size(S) = Size(T);
true
gap> NrDClasses(S) = NrDClasses(T);
true
gap> NrRClasses(S) = NrRClasses(T);
true
gap> NrLClasses(S) = NrLClasses(T);
true
gap> NrIdempotents(S) = NrIdempotents(T);
true
gap> map := IsomorphismMonoid(IsTransformationMonoid, S);;
gap> BruteForceIsoCheck(map);
true
gap> BruteForceInverseCheck(map);
true

# AsMonoid:
#   convert from IsBooleanMatSemigroup to IsTransformationMonoid
gap> S := Semigroup([
> Matrix(IsBooleanMat,
>        [[true, false, false, false, false],
>         [false, true, false, false, false],
>         [false, true, false, false, false],
>         [false, true, false, false, false],
>         [false, true, false, false, false]]),
> Matrix(IsBooleanMat,
>        [[false, true, false, false, false],
>         [true, false, false, false, false],
>         [true, false, false, false, false],
>         [true, false, false, false, false],
>         [true, false, false, false, false]])]);
<semigroup of 5x5 boolean matrices with 2 generators>
gap> T := AsMonoid(IsTransformationMonoid, S);
<commutative transformation monoid of size 2, degree 2 with 1 generator>
gap> Size(S) = Size(T);
true
gap> NrDClasses(S) = NrDClasses(T);
true
gap> NrRClasses(S) = NrRClasses(T);
true
gap> NrLClasses(S) = NrLClasses(T);
true
gap> NrIdempotents(S) = NrIdempotents(T);
true
gap> map := IsomorphismMonoid(IsTransformationMonoid, S);;
gap> BruteForceIsoCheck(map);
true
gap> BruteForceInverseCheck(map);
true

# AsMonoid:
#   convert from IsMaxPlusMatrixSemigroup to IsTransformationMonoid
gap> S := Semigroup([
> Matrix(IsMaxPlusMatrix,
>        [[0, -infinity, -infinity, -infinity, -infinity],
>         [-infinity, 0, -infinity, -infinity, -infinity],
>         [-infinity, 0, -infinity, -infinity, -infinity],
>         [-infinity, 0, -infinity, -infinity, -infinity],
>         [-infinity, 0, -infinity, -infinity, -infinity]]),
> Matrix(IsMaxPlusMatrix,
>        [[-infinity, 0, -infinity, -infinity, -infinity],
>         [0, -infinity, -infinity, -infinity, -infinity],
>         [0, -infinity, -infinity, -infinity, -infinity],
>         [0, -infinity, -infinity, -infinity, -infinity],
>         [0, -infinity, -infinity, -infinity, -infinity]])]);
<semigroup of 5x5 max-plus matrices with 2 generators>
gap> T := AsMonoid(IsTransformationMonoid, S);
<commutative transformation monoid of size 2, degree 2 with 1 generator>
gap> Size(S) = Size(T);
true
gap> NrDClasses(S) = NrDClasses(T);
true
gap> NrRClasses(S) = NrRClasses(T);
true
gap> NrLClasses(S) = NrLClasses(T);
true
gap> NrIdempotents(S) = NrIdempotents(T);
true
gap> map := IsomorphismMonoid(IsTransformationMonoid, S);;
gap> BruteForceIsoCheck(map);
true
gap> BruteForceInverseCheck(map);
true

# AsMonoid:
#   convert from IsMinPlusMatrixSemigroup to IsTransformationMonoid
gap> S := Semigroup([
> Matrix(IsMinPlusMatrix,
>        [[0, infinity, infinity, infinity, infinity],
>         [infinity, 0, infinity, infinity, infinity],
>         [infinity, 0, infinity, infinity, infinity],
>         [infinity, 0, infinity, infinity, infinity],
>         [infinity, 0, infinity, infinity, infinity]]),
> Matrix(IsMinPlusMatrix,
>        [[infinity, 0, infinity, infinity, infinity],
>         [0, infinity, infinity, infinity, infinity],
>         [0, infinity, infinity, infinity, infinity],
>         [0, infinity, infinity, infinity, infinity],
>         [0, infinity, infinity, infinity, infinity]])]);
<semigroup of 5x5 min-plus matrices with 2 generators>
gap> T := AsMonoid(IsTransformationMonoid, S);
<commutative transformation monoid of size 2, degree 2 with 1 generator>
gap> Size(S) = Size(T);
true
gap> NrDClasses(S) = NrDClasses(T);
true
gap> NrRClasses(S) = NrRClasses(T);
true
gap> NrLClasses(S) = NrLClasses(T);
true
gap> NrIdempotents(S) = NrIdempotents(T);
true
gap> map := IsomorphismMonoid(IsTransformationMonoid, S);;
gap> BruteForceIsoCheck(map);
true
gap> BruteForceInverseCheck(map);
true

# AsMonoid:
#   convert from IsProjectiveMaxPlusMatrixSemigroup to IsTransformationMonoid
gap> S := Semigroup([
> Matrix(IsProjectiveMaxPlusMatrix,
>        [[0, -infinity, -infinity, -infinity, -infinity],
>         [-infinity, 0, -infinity, -infinity, -infinity],
>         [-infinity, 0, -infinity, -infinity, -infinity],
>         [-infinity, 0, -infinity, -infinity, -infinity],
>         [-infinity, 0, -infinity, -infinity, -infinity]]),
> Matrix(IsProjectiveMaxPlusMatrix,
>        [[-infinity, 0, -infinity, -infinity, -infinity],
>         [0, -infinity, -infinity, -infinity, -infinity],
>         [0, -infinity, -infinity, -infinity, -infinity],
>         [0, -infinity, -infinity, -infinity, -infinity],
>         [0, -infinity, -infinity, -infinity, -infinity]])]);
<semigroup of 5x5 projective max-plus matrices with 2 generators>
gap> T := AsMonoid(IsTransformationMonoid, S);
<commutative transformation monoid of size 2, degree 2 with 1 generator>
gap> Size(S) = Size(T);
true
gap> NrDClasses(S) = NrDClasses(T);
true
gap> NrRClasses(S) = NrRClasses(T);
true
gap> NrLClasses(S) = NrLClasses(T);
true
gap> NrIdempotents(S) = NrIdempotents(T);
true
gap> map := IsomorphismMonoid(IsTransformationMonoid, S);;
gap> BruteForceIsoCheck(map);
true
gap> BruteForceInverseCheck(map);
true

# AsMonoid:
#   convert from IsIntegerMatrixSemigroup to IsTransformationMonoid
gap> S := Semigroup([
> Matrix(Integers,
>        [[1, 0, 0, 0, 0],
>         [0, 1, 0, 0, 0],
>         [0, 1, 0, 0, 0],
>         [0, 1, 0, 0, 0],
>         [0, 1, 0, 0, 0]]),
> Matrix(Integers,
>        [[0, 1, 0, 0, 0],
>         [1, 0, 0, 0, 0],
>         [1, 0, 0, 0, 0],
>         [1, 0, 0, 0, 0],
>         [1, 0, 0, 0, 0]])]);
<semigroup of 5x5 integer matrices with 2 generators>
gap> T := AsMonoid(IsTransformationMonoid, S);
<commutative transformation monoid of size 2, degree 2 with 1 generator>
gap> Size(S) = Size(T);
true
gap> NrDClasses(S) = NrDClasses(T);
true
gap> NrRClasses(S) = NrRClasses(T);
true
gap> NrLClasses(S) = NrLClasses(T);
true
gap> NrIdempotents(S) = NrIdempotents(T);
true
gap> map := IsomorphismMonoid(IsTransformationMonoid, S);;
gap> BruteForceIsoCheck(map);
true
gap> BruteForceInverseCheck(map);
true

# AsMonoid:
#   convert from IsTropicalMaxPlusMatrixSemigroup to IsTransformationMonoid
gap> S := Semigroup([
> Matrix(IsTropicalMaxPlusMatrix,
>        [[0, -infinity, -infinity, -infinity, -infinity],
>         [-infinity, 0, -infinity, -infinity, -infinity],
>         [-infinity, 0, -infinity, -infinity, -infinity],
>         [-infinity, 0, -infinity, -infinity, -infinity],
>         [-infinity, 0, -infinity, -infinity, -infinity]], 4),
> Matrix(IsTropicalMaxPlusMatrix,
>        [[-infinity, 0, -infinity, -infinity, -infinity],
>         [0, -infinity, -infinity, -infinity, -infinity],
>         [0, -infinity, -infinity, -infinity, -infinity],
>         [0, -infinity, -infinity, -infinity, -infinity],
>         [0, -infinity, -infinity, -infinity, -infinity]], 4)]);
<semigroup of 5x5 tropical max-plus matrices with 2 generators>
gap> T := AsMonoid(IsTransformationMonoid, S);
<commutative transformation monoid of size 2, degree 2 with 1 generator>
gap> Size(S) = Size(T);
true
gap> NrDClasses(S) = NrDClasses(T);
true
gap> NrRClasses(S) = NrRClasses(T);
true
gap> NrLClasses(S) = NrLClasses(T);
true
gap> NrIdempotents(S) = NrIdempotents(T);
true
gap> map := IsomorphismMonoid(IsTransformationMonoid, S);;
gap> BruteForceIsoCheck(map);
true
gap> BruteForceInverseCheck(map);
true

# AsMonoid:
#   convert from IsTropicalMinPlusMatrixSemigroup to IsTransformationMonoid
gap> S := Semigroup([
> Matrix(IsTropicalMinPlusMatrix,
>        [[0, infinity, infinity, infinity, infinity],
>         [infinity, 0, infinity, infinity, infinity],
>         [infinity, 0, infinity, infinity, infinity],
>         [infinity, 0, infinity, infinity, infinity],
>         [infinity, 0, infinity, infinity, infinity]], 1),
> Matrix(IsTropicalMinPlusMatrix,
>        [[infinity, 0, infinity, infinity, infinity],
>         [0, infinity, infinity, infinity, infinity],
>         [0, infinity, infinity, infinity, infinity],
>         [0, infinity, infinity, infinity, infinity],
>         [0, infinity, infinity, infinity, infinity]], 1)]);
<semigroup of 5x5 tropical min-plus matrices with 2 generators>
gap> T := AsMonoid(IsTransformationMonoid, S);
<commutative transformation monoid of size 2, degree 2 with 1 generator>
gap> Size(S) = Size(T);
true
gap> NrDClasses(S) = NrDClasses(T);
true
gap> NrRClasses(S) = NrRClasses(T);
true
gap> NrLClasses(S) = NrLClasses(T);
true
gap> NrIdempotents(S) = NrIdempotents(T);
true
gap> map := IsomorphismMonoid(IsTransformationMonoid, S);;
gap> BruteForceIsoCheck(map);
true
gap> BruteForceInverseCheck(map);
true

# AsMonoid:
#   convert from IsNTPMatrixSemigroup to IsTransformationMonoid
gap> S := Semigroup([
> Matrix(IsNTPMatrix,
>        [[1, 0, 0, 0, 0],
>         [0, 1, 0, 0, 0],
>         [0, 1, 0, 0, 0],
>         [0, 1, 0, 0, 0],
>         [0, 1, 0, 0, 0]], 3, 5),
> Matrix(IsNTPMatrix,
>        [[0, 1, 0, 0, 0],
>         [1, 0, 0, 0, 0],
>         [1, 0, 0, 0, 0],
>         [1, 0, 0, 0, 0],
>         [1, 0, 0, 0, 0]], 3, 5)]);
<semigroup of 5x5 ntp matrices with 2 generators>
gap> T := AsMonoid(IsTransformationMonoid, S);
<commutative transformation monoid of size 2, degree 2 with 1 generator>
gap> Size(S) = Size(T);
true
gap> NrDClasses(S) = NrDClasses(T);
true
gap> NrRClasses(S) = NrRClasses(T);
true
gap> NrLClasses(S) = NrLClasses(T);
true
gap> NrIdempotents(S) = NrIdempotents(T);
true
gap> map := IsomorphismMonoid(IsTransformationMonoid, S);;
gap> BruteForceIsoCheck(map);
true
gap> BruteForceInverseCheck(map);
true

# AsSemigroup:
#   convert from free band to IsTransformationSemigroup
gap> S := FreeBand(2);;
gap> T := AsSemigroup(IsTransformationSemigroup, S);
<transformation semigroup of size 6, degree 7 with 2 generators>
gap> Size(S) = Size(T);
true
gap> NrDClasses(S) = NrDClasses(T);
true
gap> NrRClasses(S) = NrRClasses(T);
true
gap> NrLClasses(S) = NrLClasses(T);
true
gap> NrIdempotents(S) = NrIdempotents(T);
true
gap> map := IsomorphismSemigroup(IsTransformationSemigroup, S);;
gap> BruteForceIsoCheck(map);
true
gap> BruteForceInverseCheck(map);
true

# AsSemigroup:
#   convert from perm group  to IsTransformationSemigroup
gap> S := DihedralGroup(IsPermGroup, 6);;
gap> T := AsSemigroup(IsTransformationSemigroup, S);
<transformation group of degree 3 with 2 generators>
gap> Size(S) = Size(T);
true
gap> NrDClasses(S) = NrDClasses(T);
true
gap> NrRClasses(S) = NrRClasses(T);
true
gap> NrLClasses(S) = NrLClasses(T);
true
gap> NrIdempotents(S) = NrIdempotents(T);
true
gap> map := IsomorphismSemigroup(IsTransformationSemigroup, S);;
gap> BruteForceIsoCheck(map);
true
gap> BruteForceInverseCheck(map);
true

# AsSemigroup:
#   convert from non-perm group  to IsTransformationSemigroup
gap> S := DihedralGroup(6);;
gap> T := AsSemigroup(IsTransformationSemigroup, S);
<transformation monoid of size 6, degree 6 with 5 generators>
gap> Size(S) = Size(T);
true
gap> NrDClasses(S) = NrDClasses(T);
true
gap> NrRClasses(S) = NrRClasses(T);
true
gap> NrLClasses(S) = NrLClasses(T);
true
gap> NrIdempotents(S) = NrIdempotents(T);
true
gap> map := IsomorphismSemigroup(IsTransformationSemigroup, S);;
gap> BruteForceIsoCheck(map);
true
gap> BruteForceInverseCheck(map);
true

# AsSemigroup:
#   convert from IsBlockBijectionSemigroup to IsTransformationSemigroup
gap> S := InverseSemigroup(Bipartition([[1, -1, -3],
>         [2, 3, -2]]));;
gap> T := AsSemigroup(IsTransformationSemigroup, S);
<transformation semigroup of size 5, degree 6 with 2 generators>
gap> Size(S) = Size(T);
true
gap> NrDClasses(S) = NrDClasses(T);
true
gap> NrRClasses(S) = NrRClasses(T);
true
gap> NrLClasses(S) = NrLClasses(T);
true
gap> NrIdempotents(S) = NrIdempotents(T);
true
gap> map := IsomorphismSemigroup(IsTransformationSemigroup, S);;
gap> BruteForceIsoCheck(map);
true
gap> BruteForceInverseCheck(map);
true

# AsSemigroup:
#   convert from IsBlockBijectionMonoid to IsTransformationMonoid
gap> S := InverseMonoid([
> Bipartition([[1, -1, -3], [2, 3, -2]])]);;
gap> T := AsMonoid(IsTransformationMonoid, S);
<transformation monoid of size 6, degree 6 with 2 generators>
gap> Size(S) = Size(T);
true
gap> NrDClasses(S) = NrDClasses(T);
true
gap> NrRClasses(S) = NrRClasses(T);
true
gap> NrLClasses(S) = NrLClasses(T);
true
gap> NrIdempotents(S) = NrIdempotents(T);
true
gap> map := IsomorphismMonoid(IsTransformationMonoid, S);;
gap> BruteForceIsoCheck(map);
true
gap> BruteForceInverseCheck(map);
true

# AsSemigroup:
#   convert from IsBlockBijectionMonoid to IsTransformationSemigroup
gap> S := InverseMonoid([
> Bipartition([[1, -1, -3], [2, 3, -2]])]);;
gap> T := AsSemigroup(IsTransformationSemigroup, S);
<transformation monoid of size 6, degree 6 with 2 generators>
gap> Size(S) = Size(T);
true
gap> NrDClasses(S) = NrDClasses(T);
true
gap> NrRClasses(S) = NrRClasses(T);
true
gap> NrLClasses(S) = NrLClasses(T);
true
gap> NrIdempotents(S) = NrIdempotents(T);
true
gap> map := IsomorphismSemigroup(IsTransformationSemigroup, S);;
gap> BruteForceIsoCheck(map);
true
gap> BruteForceInverseCheck(map);
true

# AsSemigroup:
#   convert from IsPartialPermSemigroup to IsTransformationSemigroup
gap> S := InverseSemigroup(PartialPerm([1, 2], [2, 1]),
>                          PartialPerm([1, 2], [3, 1]));
<inverse partial perm semigroup of rank 3 with 2 generators>
gap> T := AsSemigroup(IsTransformationSemigroup, S);
<transformation semigroup of degree 4 with 3 generators>
gap> Size(S) = Size(T);
true
gap> NrDClasses(S) = NrDClasses(T);
true
gap> NrRClasses(S) = NrRClasses(T);
true
gap> NrLClasses(S) = NrLClasses(T);
true
gap> NrIdempotents(S) = NrIdempotents(T);
true
gap> map := IsomorphismSemigroup(IsTransformationSemigroup, S);;
gap> BruteForceIsoCheck(map);
true
gap> BruteForceInverseCheck(map);
true

# AsSemigroup:
#   convert from IsPartialPermMonoid to IsTransformationMonoid
gap> S := InverseMonoid(PartialPerm([1, 2], [2, 1]),
>                       PartialPerm([1, 2], [3, 1]));
<inverse partial perm monoid of rank 3 with 2 generators>
gap> T := AsMonoid(IsTransformationMonoid, S);
<transformation monoid of degree 4 with 3 generators>
gap> Size(S) = Size(T);
true
gap> NrDClasses(S) = NrDClasses(T);
true
gap> NrRClasses(S) = NrRClasses(T);
true
gap> NrLClasses(S) = NrLClasses(T);
true
gap> NrIdempotents(S) = NrIdempotents(T);
true
gap> map := IsomorphismMonoid(IsTransformationMonoid, S);;
gap> BruteForceIsoCheck(map);
true
gap> BruteForceInverseCheck(map);
true

# AsSemigroup:
#   convert from IsPartialPermMonoid to IsTransformationSemigroup
gap> S := InverseMonoid(PartialPerm([1, 2], [2, 1]),
>                       PartialPerm([1, 2], [3, 1]));
<inverse partial perm monoid of rank 3 with 2 generators>
gap> T := AsSemigroup(IsTransformationSemigroup, S);
<transformation monoid of degree 4 with 3 generators>
gap> Size(S) = Size(T);
true
gap> NrDClasses(S) = NrDClasses(T);
true
gap> NrRClasses(S) = NrRClasses(T);
true
gap> NrLClasses(S) = NrLClasses(T);
true
gap> NrIdempotents(S) = NrIdempotents(T);
true
gap> map := IsomorphismSemigroup(IsTransformationSemigroup, S);;
gap> BruteForceIsoCheck(map);
true
gap> BruteForceInverseCheck(map);
true

# Size: for a monogenic transformation semigroup, 1
gap> S := MonogenicSemigroup(1, 1);;
gap> Size(S);
1
gap> S := Semigroup(S);;
gap> IsMonogenicSemigroup(S);
true
gap> Size(S);
1

# Size: for a monogenic transformation semigroup, 2
gap> S := MonogenicSemigroup(5, 1);;
gap> Size(S);
5
gap> S := Semigroup(S);;
gap> IsMonogenicSemigroup(S);
true
gap> Size(S);
5

# Size: for a monogenic transformation semigroup, 3
gap> S := MonogenicSemigroup(1, 10);;
gap> Size(S);
10
gap> S := Semigroup(S);;
gap> IsMonogenicSemigroup(S);
true
gap> Size(S);
10

# Size: for a monogenic transformation semigroup, 4
gap> S := MonogenicSemigroup(7, 11);;
gap> Size(S);
17
gap> S := Semigroup(S);;
gap> IsMonogenicSemigroup(S);
true
gap> Size(S);
17

# Size: for a monogenic transformation monoid, 1
gap> S := MonogenicSemigroup(1, 1);;
gap> S := Monoid(S);;
gap> IsMonogenicMonoid(S);
true
gap> Size(S);
1

# Size: for a monogenic transformation monoid, 2
gap> S := MonogenicSemigroup(5, 1);;
gap> S := Monoid(S);;
gap> IsMonogenicMonoid(S);
true
gap> Size(S);
6

# Size: for a monogenic transformation semigroup, 3
gap> S := MonogenicSemigroup(1, 10);;
gap> S := Monoid(S);;
gap> IsMonogenicMonoid(S);
true
gap> Size(S);
10

# Size: for a monogenic transformation semigroup, 4
gap> S := MonogenicSemigroup(7, 11);;
gap> S := Monoid(S);;
gap> IsMonogenicMonoid(S);
true
gap> Size(S);
18

# Size: for a monogenic transformation semigroup, 4
gap> S := Monoid(Transformation([2, 3, 1]));;
gap> IsMonogenicMonoid(S);
true
gap> Size(S);
3
gap> S := Monoid(Transformation([2, 3, 1, 1]));;
gap> IsMonogenicMonoid(S);
true
gap> Size(S);
4

# Test LargestElementSemigroup
gap> gr := Digraph([[2, 3, 4, 5, 7, 8, 9, 10], [3, 5, 6, 7, 10, 1, 8, 9],
> [1, 4, 5, 6, 2, 7, 8, 10], [1, 3, 8, 9], [3, 7, 8, 1, 2],
> [3, 7, 2, 8, 10], [2, 3, 6, 10, 1, 5, 8], [1, 2, 3, 5, 6, 7, 10, 4, 9],
> [1, 2, 8, 4, 10], [1, 3, 6, 8, 9, 2, 7]]);;
gap> S := EndomorphismMonoid(gr);;
gap> LargestElementSemigroup(S) = Maximum(AsSet(S));
true
gap> LargestElementSemigroup(S);
Transformation( [ 10, 8, 7, 8, 6, 10, 3, 2, 9, 1 ] )

# RepresentativeOfMinimalIdeal: for a transformation semigroup on many points
gap> x := ListWithIdenticalEntries(49999, 1);;
gap> Add(x, 2);
gap> x := Transformation(x);;
gap> S := Semigroup(x);
<commutative transformation semigroup of degree 50000 with 1 generator>
gap> RepresentativeOfMinimalIdeal(S);
<transformation on 50000 pts with rank 1>
gap> x := ListWithIdenticalEntries(99, 1);;
gap> Add(x, 2);
gap> x := Transformation(x);;
gap> S := Semigroup(x);
<commutative transformation semigroup of degree 100 with 1 generator>
gap> Size(S);
2
gap> RepresentativeOfMinimalIdeal(S);
<transformation on 100 pts with rank 1>

# RepresentativeOfMinimalIdeal: for a transformation group
gap> S := Semigroup([
> Transformation([1, 4, 1, 4, 1]),
> Transformation([4, 1, 4, 1, 4])]);;
gap> RepresentativeOfMinimalIdeal(S);
Transformation( [ 4, 1, 4, 1, 4 ] )
gap> S := Semigroup([
> Transformation([2, 3, 4, 5, 1]),
> Transformation([2, 1])]);;
gap> RepresentativeOfMinimalIdeal(S);
Transformation( [ 1, 3, 4, 5, 2 ] )

# Test RandomSemigroup
gap> RandomSemigroup(IsTransformationSemigroup);;
gap> RandomSemigroup(IsTransformationSemigroup, 2);;
gap> RandomSemigroup(IsTransformationSemigroup, 2, 2);;
gap> RandomSemigroup(IsTransformationSemigroup, "a");;
Error, the 2nd argument (number of generators) must be a pos int
gap> RandomSemigroup(IsTransformationSemigroup, 2, "a");;
Error, the 3rd argument (degree or dimension) must be a pos int
gap> RandomMonoid(IsTransformationMonoid);;
gap> RandomMonoid(IsTransformationMonoid, 2);;
gap> RandomMonoid(IsTransformationMonoid, 2, 2);;
gap> RandomMonoid(IsTransformationMonoid, "a");;
Error, the 2nd argument (number of generators) must be a pos int
gap> RandomMonoid(IsTransformationMonoid, 2, "a");;
Error, the 3rd argument (degree or dimension) must be a pos int

# Test IsConnectedTransformationSemigroup
gap> S := Semigroup(Transformation([1, 2, 3, 3, 3]),
> Transformation([1, 1, 3, 3, 3]));;
gap> IsConnectedTransformationSemigroup(S);
false
gap> S := DirectProduct(S, S);;
gap> IsConnectedTransformationSemigroup(S);
false
gap> S := FullTransformationMonoid(3);;
gap> IsConnectedTransformationSemigroup(S);
true

#
gap> S := Semigroup(Transformation([1, 2, 3, 3, 3]),
>                   Transformation([1, 1, 3, 3, 3]));;
gap> IsTransitive(S);
false
gap> IsTransitive(S, 1);
true
gap> IsTransitive(S, 2);
false
gap> S := FullTransformationMonoid(3);;
gap> IsTransitive(S, 1);
true
gap> IsTransitive(S, 2);
true
gap> IsTransitive(S, 3);
true
gap> IsTransitive(S, 4);
false
gap> IsTransitive(S, [1 .. 3]);
true
gap> IsTransitive(S, [1 .. 5]);
false
gap> IsTransitive(S, [1, 3]);
false
gap> IsTransitive(S, [3, 1]);
Error, the 2nd argument (a list) must be a set of positive integers

# Test Idempotents with specified ranks
gap> S := Semigroup(FullTransformationMonoid(3), rec(acting := false));;
gap> Set(Idempotents(S, 0));
Error, no method found! For debugging hints type ?Recovery from NoMethodFound
Error, no 1st choice method found for `Idempotents' on 2 arguments
gap> Set(Idempotents(S, 1));
[ Transformation( [ 1, 1, 1 ] ), Transformation( [ 2, 2, 2 ] ), 
  Transformation( [ 3, 3, 3 ] ) ]
gap> Set(Idempotents(S, 2));
[ Transformation( [ 1, 1 ] ), Transformation( [ 1, 2, 1 ] ), 
  Transformation( [ 1, 2, 2 ] ), Transformation( [ 1, 3, 3 ] ), 
  Transformation( [ 2, 2 ] ), Transformation( [ 3, 2, 3 ] ) ]
gap> Set(Idempotents(S, 3));
[ IdentityTransformation ]
gap> Set(Idempotents(S, 4));
[  ]

# Test IteratorSorted
gap> S1 := Semigroup(FullTransformationMonoid(3), rec(acting := false));;
gap> S2 := Semigroup(FullTransformationMonoid(3), rec(acting := true));;
gap> iter1 := IteratorSorted(S1);;
gap> iter2 := IteratorSorted(S2);;
gap> for x in iter1 do
> if x <> NextIterator(iter2) then
> Print("Problem in IteratorSorted\n");
> fi;
> od;
gap> S1 := Semigroup(FullTransformationMonoid(3), rec(acting := false));;
gap> S2 := Semigroup(FullTransformationMonoid(3), rec(acting := true));;
gap> AsSet(S2);;
gap> iter1 := IteratorSorted(S1);;
gap> iter2 := IteratorSorted(S2);;
gap> for x in iter1 do
> if x <> NextIterator(iter2) then
> Print("Problem in IteratorSorted\n");
> fi;
> od;

# Test \< for transformation semigroups
gap> coll := [Semigroup([
>      Transformation([2, 2, 2, 4, 3]),
>      Transformation([5, 2, 2, 1, 5])]),
>  Semigroup([
>      Transformation([4, 4, 3, 1, 2]),
>      Transformation([4, 1, 4, 2, 4])]),
>  Semigroup([
>      Transformation([3, 5, 1, 5, 1]),
>      Transformation([4, 5, 5, 5, 3])])];;
gap> IsSet(coll);
false
gap> Sort(coll);
gap> coll[1] < coll[1];
false
gap> S := Semigroup(coll[1], Transformation([6, 6, 6, 6, 6, 6]));;
gap> coll[1] < S;
true
gap> S < coll[1];
false
gap> S := Semigroup(AsTransformation((2, 3, 4)));;
gap> T := Semigroup(S, Transformation([2, 2, 2, 2]));;
gap> S < T;
true
gap> T < S;
false

# Test Smallest/LargestElementSemigroup
gap> S := Semigroup(AsTransformation((2, 3, 4)),
>                   Transformation([2, 2, 2, 2]));;
gap> SmallestElementSemigroup(S);
IdentityTransformation
gap> LargestElementSemigroup(S);
Transformation( [ 4, 4, 4, 4 ] )
gap> S := Semigroup(IdentityTransformation);;
gap> SmallestElementSemigroup(S);
IdentityTransformation
gap> LargestElementSemigroup(S);
IdentityTransformation
gap> S := Semigroup(FullTransformationMonoid(3));;
gap> SmallestElementSemigroup(S);
Transformation( [ 1, 1, 1 ] )
gap> LargestElementSemigroup(S);
Transformation( [ 3, 3, 3 ] )
gap> S := Semigroup(AsTransformation((2, 3, 4)),
>                   Transformation([2, 2, 2, 2]));;
gap> AsSet(S);;
gap> SmallestElementSemigroup(S);
IdentityTransformation
gap> LargestElementSemigroup(S);
Transformation( [ 4, 4, 4, 4 ] )
gap> S := Semigroup(AsTransformation((2, 3, 4)),
>                   Transformation([2, 2, 2, 2]));;
gap> EnumeratorSorted(S);;
gap> SmallestElementSemigroup(S);
IdentityTransformation
gap> LargestElementSemigroup(S);
Transformation( [ 4, 4, 4, 4 ] )

# Test IsomorphismTransformationSemigroup for an ideal
gap> S := FullTransformationMonoid(3);
<full transformation monoid of degree 3>
gap> x := MinimalIdeal(S);
<simple transformation semigroup ideal of degree 3 with 1 generator>
gap> map := IsomorphismTransformationSemigroup(x);;
gap> x := Range(map);;
gap> IsSimpleSemigroup(x);
true
gap> Size(x) = 3;
true
gap> x;
<simple transformation semigroup ideal of size 3, degree 3 with 1 generator>
gap> BruteForceInverseCheck(map);
true
gap> BruteForceIsoCheck(map);
true

# Test GroupOfUnits
gap> S := FullTransformationMonoid(3);;
gap> GroupOfUnits(S);
<transformation group of degree 3 with 2 generators>
gap> S := SingularTransformationMonoid(3);;
gap> GroupOfUnits(S);
fail

# Test ComponentRepsOfTransformationSemigroup
gap> S := FullTransformationMonoid(3);;
gap> S := DirectProduct(S, S, S, S);;
gap> ComponentRepsOfTransformationSemigroup(S);
[ 1, 4, 7, 10 ]
gap> ComponentsOfTransformationSemigroup(S);
[ [ 1, 2, 3 ], [ 4, 5, 6 ], [ 7, 8, 9 ], [ 10, 11, 12 ] ]
gap> CyclesOfTransformationSemigroup(S);
[ [ 1, 2, 3 ], [ 4, 5, 6 ], [ 7, 8, 9 ], [ 10, 11, 12 ] ]
gap> S := SemigroupIdeal(S, S.1);;
gap> ComponentsOfTransformationSemigroup(S);
Error, no method found! For debugging hints type ?Recovery from NoMethodFound
Error, no 1st choice method found for `DigraphOfActionOnPoints' on 1 arguments
gap> CyclesOfTransformationSemigroup(S);
Error, no method found! For debugging hints type ?Recovery from NoMethodFound
Error, no 1st choice method found for `DigraphOfActionOnPoints' on 1 arguments

# Test IsomorphismSemigroup for a semigroup of binary relations on points
gap> B := Monoid(BinaryRelationOnPoints([[2], [1, 2], [1, 3]]),
>                BinaryRelationOnPoints([[3], [1, 2], [1, 3]]),
>                BinaryRelationOnPoints([[1, 2, 3], [1, 2], [3]]));;
gap> Size(B);
16
gap> IsMonoid(B);
true
gap> iso := IsomorphismTransformationSemigroup(B);;
gap> T := Range(iso);
<transformation monoid of degree 6 with 3 generators>
gap> Size(T);
16
gap> IsMonoid(T);
true
gap> BruteForceIsoCheck(iso);
true
gap> BruteForceInverseCheck(iso);
true

# IsomorphismTransformationSemigroup for an fp monoid
gap> F := FreeMonoid(2);;
gap> M := F / [[F.1 * F.2 ^ 2, F.2 ^ 2],
>              [F.2 ^ 3, F.2 ^ 2],
>              [F.1 ^ 4, F.1],
>              [F.2 * F.1 ^ 2 * F.2, F.2 ^ 2],
>              [F.2 * F.1 ^ 3 * F.2, F.2],
>              [(F.2 * F.1) ^ 2 * F.2, F.2],
>              [F.2 ^ 2 * F.1 ^ 3, F.2 ^ 2],
>              [F.2 * (F.2 * F.1) ^ 2, F.2 ^ 2 * F.1 ^ 2]];;
gap> Size(M);
40
gap> iso := IsomorphismTransformationSemigroup(M);;
gap> T := Range(iso);;
gap> IsTransformationSemigroup(T);
true
gap> IsMonoid(T);
true
gap> Size(T);
40
gap> Size(M);
40

# Test DigraphOfAction
gap> D := DigraphOfAction(FullTransformationMonoid(1), [[1]], OnSets);
<immutable digraph with 1 vertex, 1 edge>
gap> D := DigraphOfAction(FullTransformationMonoid(1), [1], OnPoints);
<immutable digraph with 1 vertex, 1 edge>
gap> D := DigraphOfAction(FullTransformationMonoid(1), [1 .. 3], OnPoints);
<immutable digraph with 3 vertices, 3 edges>
gap> D := DigraphOfAction(FullTransformationMonoid(1), [1 .. 2], OnPoints);
<immutable digraph with 2 vertices, 2 edges>
gap> D := DigraphOfAction(FullTransformationMonoid(1), [], OnRight);
<immutable empty digraph with 0 vertices>
gap> IsEmptyDigraph(D);
true
gap> S := FullTransformationMonoid(4);
<full transformation monoid of degree 4>
gap> list := Concatenation(List([1 .. 4], x -> [x]),
>                          Combinations([1 .. 4], 2));
[ [ 1 ], [ 2 ], [ 3 ], [ 4 ], [ 1, 2 ], [ 1, 3 ], [ 1, 4 ], [ 2, 3 ], 
  [ 2, 4 ], [ 3, 4 ] ]
gap> D := DigraphOfAction(S, list, OnSets);
<immutable digraph with 10 vertices, 28 edges>
gap> OutNeighbours(D);
[ [ 1, 2 ], [ 2, 3, 1 ], [ 3, 4 ], [ 4, 1 ], [ 5, 8 ], [ 6, 9, 8 ], 
  [ 7, 5, 9, 1 ], [ 8, 10, 6 ], [ 9, 6, 7, 5 ], [ 10, 7, 6 ] ]
gap> DigraphVertexLabels(D);
[ [ 1 ], [ 2 ], [ 3 ], [ 4 ], [ 1, 2 ], [ 1, 3 ], [ 1, 4 ], [ 2, 3 ], 
  [ 2, 4 ], [ 3, 4 ] ]
gap> DigraphEdgeLabels(D);
[ [ 1, 2 ], [ 1, 2, 3 ], [ 1, 2 ], [ 1, 2 ], [ 1, 2 ], [ 1, 2, 3 ], 
  [ 1, 2, 3, 4 ], [ 1, 2, 3 ], [ 1, 2, 3, 4 ], [ 1, 2, 4 ] ]

# Iterator, for a full transformation monoid
gap> S := FullTransformationMonoid(4);;
gap> y := Iterator(S);
<iterator of semigroup>
gap> for x in y do od;
gap> S := FullTransformationMonoid(4);; Elements(S);;
gap> y := Iterator(S);
<iterator>
gap> for x in y do od;
gap> S := FullTransformationMonoid(3);;
gap> TestIterator(S, Iterator(S));
true

# Tests wreath product of transf. semgp. and perm. group
gap> T := FullTransformationMonoid(3);;
gap> C := Group((1, 3));;
gap> TC := WreathProduct(T, C);;
gap> Size(TC) = 39366;
true
gap> CC := AsMonoid(IsTransformationMonoid, C);;
gap> DP := DirectProduct(T, CC);;
gap> IsSubsemigroup(TC, DP);
true
gap> C := Group((1, 2));;
gap> TC := WreathProduct(T, C);;
gap> CC := AsMonoid(IsTransformationMonoid, C);;
gap> DP := DirectProduct(T, CC);;
gap> IsSubsemigroup(TC, DP);
true

# Test wreath product of perm. group and transf. semgp.
gap> W := WreathProduct(Group((1, 2)), FullTransformationMonoid(3));;
gap> Size(W);
216
gap> Transformation([5, 6, 1, 2, 3, 4]) in W;
true
gap> Transformation([5, 5, 1, 2, 3, 4]) in W;
false

# Tests wreath product of a monoid not satisfying IsTransformationMonoid
gap> S := Semigroup(Transformation([1, 2, 3, 3, 3]));;
gap> C := Group((1, 2));;
gap> WW := WreathProduct(C, S);;
gap> Size(WW);
32
gap> Transformation([2, 1, 4, 3, 6, 5, 6, 5, 6, 5]) in WW;
true
gap> Transformation([2, 1, 4, 3, 6, 5, 6, 5, 7, 8]) in WW;
false

# WreathProduct bad input
gap> WreathProduct(FullTransformationMonoid(2),
> SingularTransformationMonoid(2));
Error, the 2nd argument (a transformation semigroup) should be a monoid (as se\
migroup)

# DigraphCore
gap> D := CompleteBipartiteDigraph(4, 4);
<immutable complete bipartite digraph with bicomponent sizes 4 and 4>
gap> GeneratorsOfEndomorphismMonoid(D);;
gap> IsIsomorphicDigraph(CompleteDigraph(2),
>    InducedSubdigraph(D, DigraphCore(D)));
true
gap> D := CycleDigraph(10);
<immutable cycle digraph with 10 vertices>
gap> GeneratorsOfEndomorphismMonoid(D);;
gap> DigraphCore(D);
[ 1, 2, 3, 4, 5, 6, 7, 8, 9, 10 ]

# IsomorphismTransformationSemigroup
gap> S := FullTransformationMonoid(2);
<full transformation monoid of degree 2>
gap> map := IsomorphismTransformationSemigroup(S);;
gap> ForAll(S, x -> x ^ map = x);
true
gap> IsomorphismTransformationSemigroup(GraphInverseSemigroup(CycleDigraph(2)));
Error, the argument (a semigroup) is not finite
gap> F := FreeMonoid(2);
<free monoid on the generators [ m1, m2 ]>
gap> R := [[F.1 ^ 2, F.1]];
[ [ m1^2, m1 ] ]
gap> IsomorphismTransformationSemigroup(F / R);
Error, the argument (a semigroup) is not finite
gap> IsomorphismTransformationSemigroup(MinimalIdeal(FreeBand(2)));
<simple semigroup ideal of size 4, with 1 generator> -> 
<transformation semigroup of size 4, degree 5 with 3 generators>

# IsRefinementOfKernelTransformation
gap> a := Transformation([2,4,3,2]);
Transformation( [ 2, 4, 3, 2 ] )
gap> b := Transformation([3,3,1,3]);
Transformation( [ 3, 3, 1, 3 ] )
gap> IsRefinementKernelOfTransformation(a, b, 4);
false
gap> IsRefinementKernelOfTransformation(b, a, 4);
true
gap> IsRefinementKernelOfTransformation(b, a, 3);
Error, Degree of the first transformation greater than 3.
Expecting a degree at most n, found 4 instead.

#
gap> SEMIGROUPS.StopTest();
gap> STOP_TEST("Semigroups package: standard/semigroups/semitrans.tst");
