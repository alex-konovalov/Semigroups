#############################################################################
##
#W  standard/properties.tst
#Y  Copyright (C) 2011-15                                James D. Mitchell
##
##  Licensing information can be found in the README file of this package.
##
#############################################################################
##
gap> START_TEST("Semigroups package: standard/properties.tst");
gap> LoadPackage("semigroups", false);;

#
gap> SEMIGROUPS.StartTest();

# properties: IsBand, for a semigroup, 1/2
gap> S := Semigroup(
> [Bipartition([[1, 2, 7, -1], [3, 4, 5, -2, -3], [6, -5], [-4],
>      [-6, -7]]),
>   Bipartition([[1, 3, 4, 7], [2, 6], [5, -3, -4, -5], [-1, -2, -6],
>      [-7]]), Bipartition([[1, 4, 6], [2, 3, 5, 7, -1, -4],
>      [-2, -5, -7], [-3, -6]]),
>   Bipartition([[1, 6, -1, -3, -5, -6], [2, 3, 4, 7, -2],
>      [5, -4, -7]]),
>   Bipartition([[1, 4, 5, -2], [2, 7, -5], [3, 6, -7], [-1],
>      [-3, -4, -6]]),
>   Bipartition([[1, 5], [2, 4, -1, -3], [3, 6, 7, -4, -5], [-2, -7],
>      [-6]])]);;
gap> IsBand(S);
false

# properties: IsBand, for an ideal, 2/2
gap> S := Semigroup(
>  PBR([[], [-2, 2], [-3, -1, 2]],
>        [[-3, -2, 3], [-2, 2], [-3, -2, 2]]),
>  PBR([[-2, -1, 1, 2, 3], [-3, -1, 1, 3], [-2, -1, 1]],
>        [[-2, -1], [-3, -1], [-2, -1, 2]]),
>  PBR([[-3, -2, -1, 1, 2, 3], [-2, 1], [-3, -2, 3]],
>        [[-2, -1, 1, 2, 3], [-3, -1, 1, 2, 3], [-3, -2, 1, 3]]),
>  PBR([[-2, 1, 2, 3], [-3, -2, -1, 2, 3], [-3, -1, 1, 2]],
>        [[-1, 3], [-2, -1, 2, 3], [3]]),
>  PBR([[-3, -1, 1, 2], [-2, -1, 2, 3], [-1, 1]],
>        [[1, 3], [-1, 1], [-3, -2, 1, 2, 3]]),
>  PBR([[-2, 1, 2], [-3, -2, -1, 2], [-3, -2, 2, 3]],
>        [[-3, -2, 1, 2, 3], [1, 2, 3], [-2, -1, 1]]),
>  PBR([[-2, 1, 2], [-3, 2], [-3, -2, 1, 2]],
>        [[2, 3], [-2, -1, 1, 2, 3], [-3, -2, -1, 1]]),
>  PBR([[-3, -1, 1, 3], [-2], [-3, 1, 3]],
>        [[-3, -1, 1, 2, 3], [-2, -1, 3], [-1, 1, 2]]),
>  PBR([[-2, 2, 3], [-3, -1, 1, 2, 3], [-3, 1, 2]],
>        [[-3, -2, -1, 1, 3], [-3, -1, 3], [-3, -1, 1, 2]]),
>  PBR([[-3, 2, 3], [-3, -1, 2], [-3, 3]],
>        [[-2, -1, 3], [-2, 1, 3], [-2, 1, 3]]),
>  PBR([[-2, -1], [-2, 1, 2], [-3, -1, 1]],
>        [[-1, 1, 2, 3], [-3, -1, 2, 3], [-3, 2, 3]]));;
gap> IsBand(S);
false
gap> I := SemigroupIdeal(S,
> PBR([[-3, -2, 2, 3], [-3, -2, 1, 2, 3], [-3, -2, 1, 2, 3]],
>     [[-3, -2], [-3, -2, -1], [-3, -2, -1]]));
<pbr semigroup ideal of degree 3 with 1 generator>
gap> IsBand(I);
true
gap> J := SemigroupIdeal(I,
> PBR([[-3, -2, 2, 3], [-3, -2, 1, 2, 3], [-3, -2, 1, 2, 3]],
>     [[-3, -2], [-3, -2, -1], [-3, -2, -1]]));
<regular pbr semigroup ideal of degree 3 with 1 generator>
gap> IsBand(J);
true

# properties: IsBand, for an inverse semigroup, 1/1
gap> S := InverseSemigroup(
> [Bipartition([[1, -6], [2, -2], [3, -1], [4, -4], [5], [6],
>      [-3], [-5]]), Bipartition([[1, -1], [2, -6], [3, -3],
>      [4, -2], [5, -4], [6], [-5]]),
>   Bipartition([[1, -1], [2, -6], [3, -5], [4], [5, -2], [6],
>      [-3], [-4]]), Bipartition([[1, -1], [2, -3], [3, -5],
>      [4], [5], [6, -6], [-2], [-4]]),
>   Bipartition([[1, -3], [2], [3], [4, -6], [5, -4], [6, -5],
>      [-1], [-2]]),
>   Bipartition([[1, -3], [2, -5], [3], [4, -4], [5, -1],
>      [6, -2], [-6]])]);;
gap> IsBand(S);
false
gap> IsBand(IdempotentGeneratedSubsemigroup(S));
true

# properties: IsBlockGroup, 1/?
gap> S := Semigroup([Transformation([6, 2, 8, 8, 7, 8, 4, 8]),
>   Transformation([6, 7, 4, 2, 8, 1, 5, 8])]);
<transformation semigroup of degree 8 with 2 generators>
gap> IsBlockGroup(S);
true
gap> I := SemigroupIdeal(S, Transformation([1, 8, 8, 8, 8, 8, 5, 8]));;
gap> IsBlockGroup(I);
true

# properties: IsBlockGroup, 2/?
gap> S := JonesMonoid(3);
<regular bipartition *-monoid of degree 3 with 2 generators>
gap> IsInverseSemigroup(S);
false
gap> IsBlockGroup(S);
false

# properties: IsBlockGroup, 3/?
gap> S := Semigroup([BooleanMat([[true, true], [true, true]]),
>  BooleanMat([[false, false], [false, true]])]);
<semigroup of 2x2 boolean matrices with 2 generators>
gap> IsBlockGroup(S);
false

# properties: IsBlockGroup, 4/?
gap> S := Semigroup(
>  Matrix(IsTropicalMaxPlusMatrix, [[0, 1, 1, 2, 0, 3, 0, -infinity],
>      [5, 1, 1, 2, -infinity, -infinity, 0, 2],
>      [0, 3, -infinity, 1, -infinity, -infinity, 2, 1],
>      [-infinity, -infinity, -infinity, 0, -infinity, 3, 1, 1],
>      [1, 2, 1, 2, 1, 1, 2, 1], [1, 2, 5, 2, -infinity, 2, 2, 1],
>      [1, 0, -infinity, 2, -infinity, 0, 0, 2],
>      [2, -infinity, 5, 2, 4, 1, 3, 3]], 6),
>  Matrix(IsTropicalMaxPlusMatrix, [[1, 3, 0, 4, -infinity, 2, 1, -infinity],
>      [2, 5, 2, 5, -infinity, 0, 1, -infinity],
>      [2, -infinity, -infinity, 1, 3, 2, 2, 1],
>      [1, 4, 1, 3, -infinity, 1, 1, 3],
>      [3, 0, 1, 1, 1, 2, -infinity, -infinity],
>      [1, 1, -infinity, 1, 2, 0, 1, 2], [3, 0, 1, 1, 1, 1, 1, 2],
>      [0, -infinity, 0, 3, 1, 1, 2, 1]], 6),
>  Matrix(IsTropicalMaxPlusMatrix, [[1, 4, -infinity, 2, 1, 3, 2, 1],
>      [-infinity, 1, 2, 0, 1, 1, 2, 1],
>      [1, 2, 0, -infinity, 0, 1, -infinity, -infinity],
>      [-infinity, 3, 1, -infinity, 2, 0, 2, 1],
>      [1, -infinity, 2, 2, -infinity, 5, 2, 0],
>      [-infinity, 0, -infinity, 0, -infinity, 1, 1, -infinity],
>      [-infinity, 1, 0, 1, 3, 2, 1, 1], [3, 2, -infinity, 0, 2, 2, 2, 1]], 6),
>  Matrix(IsTropicalMaxPlusMatrix, [[2, 3, 3, 0, -infinity, 1, 1, 2],
>      [-infinity, 2, 0, -infinity, -infinity, 0, -infinity, -infinity],
>      [3, 0, 4, -infinity, -infinity, -infinity, -infinity, 6],
>      [1, 0, 0, -infinity, 0, 2, 1, 3], [2, 3, 5, 2, 3, 0, -infinity, 0],
>      [0, -infinity, 2, -infinity, 0, 1, 2, -infinity],
>      [0, 0, 1, 0, -infinity, 2, 2, 4], [0, 3, 1, -infinity, 3, 1, 1, 1]], 6),
>  Matrix(IsTropicalMaxPlusMatrix, [[3, -infinity, -infinity, 1, 3, 1, 2, 1],
>      [4, 1, 1, 2, -infinity, 3, 1, 5], [2, 3, 1, 2, 3, 2, 1, 1],
>      [2, 2, -infinity, 3, 3, 3, 1, 0], [-infinity, 2, 1, 1, 2, 1, 1, 0],
>      [2, 1, -infinity, 2, 2, 1, 1, -infinity],
>      [1, 3, 2, 0, -infinity, 2, 4, 1],
>      [1, 2, -infinity, 1, -infinity, -infinity, -infinity, -infinity]], 6),
>  Matrix(IsTropicalMaxPlusMatrix, [[3, 0, 1, 1, 0, 0, 2, 3],
>      [4, 1, 0, 0, 3, 1, 2, 2], [2, -infinity, 0, 2, -infinity, 1, 2, 3],
>      [3, 0, 2, 1, -infinity, -infinity, 3, -infinity],
>      [2, 0, -infinity, 1, -infinity, 3, -infinity, -infinity],
>      [3, 1, 2, 2, 1, -infinity, 1, 0], [2, 3, -infinity, 1, 3, 1, 2, 0],
>      [2, 2, 1, 0, 3, 1, 1, 1]], 6),
>  Matrix(IsTropicalMaxPlusMatrix, [[3, 0, 2, -infinity, 0, 2, 0, -infinity],
>      [2, 4, 0, 1, -infinity, 1, 2, 1],
>      [-infinity, 3, 0, 3, -infinity, 3, -infinity, 2],
>      [4, -infinity, 2, -infinity, -infinity, 1, 1, 3],
>      [-infinity, 3, 0, 6, 2, 0, 0, 1], [-infinity, 2, 2, 1, 2, 0, 0, 0],
>      [5, 3, 2, 0, -infinity, 0, 5, 1],
>      [-infinity, 1, 4, 4, 2, -infinity, 4, 3]], 6),
>  Matrix(IsTropicalMaxPlusMatrix, [[3, 3, 1, 0, 2, 4, 1, -infinity],
>      [3, 0, 0, 0, 0, 5, -infinity, 2],
>      [-infinity, -infinity, 1, 4, 4, 4, 1, 2], [0, 1, 1, 0, 1, 2, 0, 0],
>      [3, 0, 1, 5, -infinity, 0, 1, 2],
>      [-infinity, 0, -infinity, 2, 1, 3, 1, 0],
>      [4, 2, 2, -infinity, 1, 2, -infinity, 2],
>      [1, -infinity, 2, 4, 1, 0, 4, 1]], 6));
<semigroup of 8x8 tropical max-plus matrices with 8 generators>
gap> IsBlockGroup(S);
true

# properties: IsBlockGroup, for an infinite semigroup, 5/?
gap> S := FreeSemigroup(1);;
gap> IsBlockGroup(S);
true
gap> S := FreeSemigroup(2);;
gap> IsBlockGroup(S);
Error, no method found! For debugging hints type ?Recovery from NoMethodFound
Error, no 3rd choice method found for `IsBlockGroup' on 1 arguments

# properties: IsBrandtSemigroup, 1
gap> S := Semigroup([Transformation([2, 1, 5, 5, 5]),
> Transformation([4, 5, 3, 1, 5])]);
<transformation semigroup of degree 5 with 2 generators>
gap> IsBrandtSemigroup(S);
false
gap> S := Semigroup(S);;
gap> x := Transformation([5, 5, 5, 4, 5]);;
gap> I := SemigroupIdeal(S, x);;
gap> IsBrandtSemigroup(I);
true
gap> S := FreeSemigroup(1);;
gap> IsBrandtSemigroup(S);
false

# properties: IsZeroSimpleSemigroup, bug, 1
gap> IsZeroSimpleSemigroup(ZeroSemigroup(2));
false

# properties: IsZeroSimpleSemigroup, inverse, 2
gap> S := DualSymmetricInverseMonoid(3);
<inverse block bijection monoid of degree 3 with 3 generators>
gap> IsZeroSimpleSemigroup(S);
false

# properties: IsZeroSimpleSemigroup, inverse, 3
gap> S := InverseSemigroup([
>   PartialPerm([1]),
>   PartialPerm([])]);
<inverse partial perm monoid of rank 1 with 2 generators>
gap> IsZeroSimpleSemigroup(S);
true

# properties: IsZeroSimpleSemigroup, infinite, 4
gap> IsZeroSimpleSemigroup(FreeSemigroup(5));
false

# properties: IsZeroSimpleSemigroup, finite, 5
gap> S := ReesZeroMatrixSemigroup(Group(()), [[0, 0], [0, 0]]);;
gap> S := AsSemigroup(IsTransformationSemigroup, S);;
gap> IsZeroSimpleSemigroup(S);
false

# properties: IsZeroSimpleSemigroup, finite inverse, 6
gap> S := SymmetricInverseMonoid(2);;
gap> S := AsSemigroup(IsBooleanMatSemigroup, S);;
gap> IsInverseSemigroup(S);
true
gap> IsZeroSimpleSemigroup(S);
false

# properties: IsCongruenceFreeSemigroup, trivial, 1
gap> IsCongruenceFreeSemigroup(TrivialSemigroup());
true

# properties: IsCongruenceFreeSemigroup, group, 2
gap> S := AsSemigroup(IsTransformationSemigroup, AlternatingGroup(5));
<transformation group of size 60, degree 5 with 2 generators>
gap> IsCongruenceFreeSemigroup(S);
true

# properties: IsCongruenceFreeSemigroup, group, 3
gap> IsCongruenceFreeSemigroup(AlternatingGroup(5));
true

# properties: IsCongruenceFreeSemigroup, 4
gap> S := FullTransformationMonoid(3);;
gap> D := PrincipalFactor(DClass(S, S.3));
<Rees 0-matrix semigroup 3x3 over Group([ (1,2) ])>
gap> IsCongruenceFreeSemigroup(D);
false

# properties: IsCongruenceFreeSemigroup, 5
gap> R := ReesZeroMatrixSemigroup(Group([()]),
> [[(), (), 0], [(), 0, ()], [0, (), ()]]);;
gap> IsCongruenceFreeSemigroup(R);
true

# properties: IsCongruenceFreeSemigroup, 6
gap> R := ReesZeroMatrixSemigroup(Group([()]),
> [[(), (), 0], [(), (), 0], [0, (), ()]]);;
gap> IsCongruenceFreeSemigroup(R);
false

# properties: IsCongruenceFreeSemigroup, 7
gap> S := FreeSemigroup(1);;
gap> IsCongruenceFreeSemigroup(S);
Error, no method found! For debugging hints type ?Recovery from NoMethodFound
Error, no 3rd choice method found for `IsCongruenceFreeSemigroup' on 1 argumen\
ts

# properties: IsCliffordSemigroup, ideal, 1
gap> I := SemigroupIdeal(Semigroup(
>    [Transformation([1, 4, 3, 2]), Transformation([2, 1, 4, 3]), Tran\
> sformation([3, 2, 1, 3]), Transformation([3, 3, 1]), Transformation([\
> 4, 4, 4, 3])]), [Transformation([4, 3, 4, 4])]);;
gap> IsCliffordSemigroup(I);
false

# properties: IsCliffordSemigroup, parent, 2
gap> S := IdempotentGeneratedSubsemigroup(SymmetricInverseMonoid(3));;
gap> IsCliffordSemigroup(S);
true
gap> I := SemigroupIdeal(S, PartialPerm([1, 2, 3], [1, 2, 3]));
<inverse partial perm semigroup ideal of rank 3 with 1 generator>
gap> IsCliffordSemigroup(I);
true
gap> I := SemigroupIdeal(S, PartialPerm([1, 2, 3], [1, 2, 3]));
<inverse partial perm semigroup ideal of rank 3 with 1 generator>
gap> GeneratorsOfSemigroup(I);;
gap> IsCliffordSemigroup(I);
true

# doesn't know it is inverse
gap> S := ReesZeroMatrixSemigroup(Group(()), [[()]]);;
gap> S := Range(IsomorphismSemigroup(IsBooleanMatSemigroup, S));;
gap> IsCliffordSemigroup(S);
true
gap> I := SemigroupIdeal(S, Random(S));;
gap> IsCliffordSemigroup(I);
true
gap> I := SemigroupIdeal(S, Random(S));;
gap> GeneratorsOfSemigroup(I);;
gap> IsCliffordSemigroup(I);
true

# properties: IsCliffordSemigroup, non-inverse, 3
gap> S := ZeroSemigroup(2);;
gap> IsInverseSemigroup(S);
false
gap> IsCliffordSemigroup(S);
false

# properties: IsCliffordSemigroup, non-completely regular, 4
gap> S := ZeroSemigroup(2);;
gap> IsCompletelyRegularSemigroup(S);
false
gap> IsCliffordSemigroup(S);
false

# properties: IsCliffordSemigroup, group, 5
gap> S := AsSemigroup(IsPartialPermSemigroup, Group((1, 2, 3)));
<partial perm group of rank 3 with 1 generator>
gap> IsCliffordSemigroup(S);
true

# properties: IsCliffordSemigroup, non-regular, 6
gap> S := ZeroSemigroup(2);;
gap> IsCliffordSemigroup(S);
false

# properties: IsCliffordSemigroup, infinite, 6
gap> S := FreeSemigroup(2);;
gap> IsCliffordSemigroup(S);
Error, no method found! For debugging hints type ?Recovery from NoMethodFound
Error, no 4th choice method found for `IsCliffordSemigroup' on 1 arguments

# properties: IsCommutativeSemigroup, 1
gap> S := Semigroup([Transformation([1, 1, 3, 5, 4]),
>  Transformation([1, 2, 1, 5, 4])]);;
gap> IsCommutativeSemigroup(S);
true

# properties: IsCommutativeSemigroup, 2
gap> S := JonesMonoid(3);
<regular bipartition *-monoid of degree 3 with 2 generators>
gap> IsCommutativeSemigroup(S);
false

# properties: IsCommutativeSemigroup, 3
gap> S := FreeSemigroup(3);;
gap> IsCommutativeSemigroup(S);
Error, no method found! For debugging hints type ?Recovery from NoMethodFound
Error, no 3rd choice method found for `IsCommutativeSemigroup' on 1 arguments

# properties: IsCompletelyRegularSemigroup, 1
gap> S := Monoid(
> BooleanMat([[false, true, false],
>             [true, false, false],
>             [false, false, true]]),
> BooleanMat([[false, true, false],
>             [false, false, true],
>             [true, false, false]]));
<monoid of 3x3 boolean matrices with 2 generators>
gap> IsCompletelyRegularSemigroup(S);
true
gap> I := SemigroupIdeal(S, S.1);;
gap> IsCompletelyRegularSemigroup(I);
true

# properties: IsCompletelyRegularSemigroup, 2
gap> S := Semigroup(GroupOfUnits(FullTransformationMonoid(3)));
<transformation semigroup of degree 3 with 2 generators>
gap> IsCompletelyRegularSemigroup(S);
true
gap> I := SemigroupIdeal(S, S.1);;
gap> GeneratorsOfSemigroup(I);;
gap> IsCompletelyRegularSemigroup(I);
true

# properties: IsCompletelyRegularSemigroup, 3
gap> S := MonogenicSemigroup(IsBooleanMatSemigroup, 3, 2);;
gap> IsRegularSemigroup(S);
false
gap> IsCompletelyRegularSemigroup(S);
false
gap> S := FreeSemigroup(1);;
gap> IsCompletelyRegularSemigroup(S);
Error, no method found! For debugging hints type ?Recovery from NoMethodFound
Error, no 3rd choice method found for `IsCompletelyRegularSemigroup' on 1 argu\
ments

# properties: IsCompletelyRegularSemigroup, 4
gap> T := AsSemigroup(IsTransformationSemigroup, FullBooleanMatMonoid(3));
<transformation monoid of degree 8 with 5 generators>
gap> IsRegularSemigroup(T);
false
gap> IsCompletelyRegularSemigroup(T);
false

# properties: IsCompletelySimpleSemigroup, 1
gap> S := Semigroup(Matrix(IsMaxPlusMatrix, [[0, -4], [-4, -1]]),
>                   Matrix(IsMaxPlusMatrix, [[0, -3], [-3, -1]]));
<semigroup of 2x2 max-plus matrices with 2 generators>
gap> IsCompletelySimpleSemigroup(S);
false
gap> S := FreeSemigroup(2);;
gap> IsCompletelySimpleSemigroup(S);
Error, no method found! For debugging hints type ?Recovery from NoMethodFound
Error, no 3rd choice method found for `IsCompletelySimpleSemigroup' on 1 argum\
ents

# properties: IsEUnitaryInverseSemigroup, non-inverse op, 1
gap> S := Semigroup([Transformation([5, 7, 1, 6, 8, 8, 8, 8]),
>  Transformation([1, 3, 4, 8, 8, 7, 5, 8]),
>  Transformation([3, 8, 8, 8, 1, 4, 2, 8]),
>  Transformation([1, 8, 2, 3, 7, 8, 6, 8])]);
<transformation semigroup of degree 8 with 4 generators>
gap> IsEUnitaryInverseSemigroup(S);
false

# properties: IsEUnitaryInverseSemigroup, inverse op, 2
gap> S := InverseSemigroup([PartialPerm([1, 2, 3], [1, 3, 5]),
>  PartialPerm([1, 2, 3, 4, 6], [7, 5, 2, 6, 4])]);
<inverse partial perm semigroup of rank 7 with 2 generators>
gap> IsEUnitaryInverseSemigroup(S);
false

# properties: IsEUnitaryInverseSemigroup, infinite, 3
gap> S := FreeInverseSemigroup(3);;
gap> IsEUnitaryInverseSemigroup(S);
Error, no method found! For debugging hints type ?Recovery from NoMethodFound
Error, no 4th choice method found for `IsEUnitaryInverseSemigroup' on 1 argume\
nts

# properties: IsFactorisableInverseMonoid, 1
gap> S := DualSymmetricInverseMonoid(3);
<inverse block bijection monoid of degree 3 with 3 generators>
gap> IsFactorisableInverseMonoid(S);
false
gap> T := InverseSemigroup(FactorisableDualSymmetricInverseMonoid(3));
<inverse block bijection monoid of degree 3 with 3 generators>
gap> IsFactorisableInverseMonoid(T);
true

# properties: IsFactorisableInverseMonoid, 2
gap> S := InverseSemigroup(PartialPerm([1, 2], [3, 1]),
>                          PartialPerm([1, 2, 3], [1, 3, 4]));;
gap> IsFactorisableInverseMonoid(S);
false
gap> S := InverseMonoid(S);;
gap> IsFactorisableInverseMonoid(S);
false

# properties: IsFactorisableInverseMonoid, 3
gap> S := FreeInverseSemigroup(2);;
gap> IsFactorisableInverseMonoid(S);
Error, no method found! For debugging hints type ?Recovery from NoMethodFound
Error, no 3rd choice method found for `IsFactorisableInverseMonoid' on 1 argum\
ents

# properties: IsXTrivial, non-acting, 1
gap> S := Semigroup(
> Matrix(IsTropicalMaxPlusMatrix, [[-infinity, -infinity],
>                                  [4, 0]], 8),
> Matrix(IsTropicalMaxPlusMatrix, [[3, 1], [-infinity, 0]], 8));
<semigroup of 2x2 tropical max-plus matrices with 2 generators>
gap> IsHTrivial(S);
true
gap> IsLTrivial(S);
false
gap> IsRTrivial(S);
true
gap> I := SemigroupIdeal(S,
> Matrix(IsTropicalMaxPlusMatrix, [[8, 8], [7, 5]], 8));
<semigroup ideal of 2x2 tropical max-plus matrices with 1 generator>
gap> IsHTrivial(I);
true
gap> IsLTrivial(I);
false
gap> IsRTrivial(I);
true
gap> S := Semigroup(BooleanMat([[1, 0, 0], [1, 0, 0], [0, 1, 0]]));
<commutative semigroup of 3x3 boolean matrices with 1 generator>
gap> IsHTrivial(S);
true
gap> IsLTrivial(S);
true
gap> IsRTrivial(S);
true
gap> I := SemigroupIdeal(S, MultiplicativeZero(S));
<commutative semigroup ideal of 3x3 boolean matrices with 1 generator>
gap> IsHTrivial(I);
true
gap> IsLTrivial(I);
true
gap> IsRTrivial(I);
true

# properties: IsXTrivial, trans, 2
gap> S := Semigroup([Transformation([4, 1, 3, 5, 5, 1]),
> Transformation([6, 1, 6, 3, 2, 4])]);
<transformation semigroup of degree 6 with 2 generators>
gap> IsHTrivial(S);
false
gap> IsLTrivial(S);
false
gap> IsRTrivial(S);
false

# properties: IsXTrivial, pperm, 3
gap> S := Semigroup([
>  PartialPerm([1, 2, 3, 6, 7, 8, 9], [10, 5, 9, 6, 3, 8, 4]),
>  PartialPerm([1, 2, 3, 4, 7, 8, 10], [1, 4, 2, 5, 6, 11, 7]),
>  PartialPerm([1, 2, 3, 4, 5, 7, 10], [2, 8, 4, 7, 5, 3, 6]),
>  PartialPerm([1, 2, 4, 5, 7, 9, 11], [7, 10, 1, 11, 9, 4, 2]),
>  PartialPerm([1, 2, 4, 7, 8, 9, 11], [10, 7, 8, 5, 9, 1, 3])]);
<partial perm semigroup of rank 11 with 5 generators>
gap> IsHTrivial(S);
false
gap> IsLTrivial(S);
false
gap> IsRTrivial(S);
false

# properties: IsXTrivial, acting, true 4
gap> S := InverseSemigroup(
> [Bipartition([[1, 4, 5, -1, -4, -5], [2, -2], [3, -3]]),
>   Bipartition([[1, -1], [2, -2], [3, 4, 5, -3, -4, -5]]),
>   Bipartition([[1, -1], [2, 3, 5, -2, -3, -5], [4, -4]]),
>   Bipartition([[1, 2, 4, 5, -1, -2, -4, -5], [3, -3]]),
>   Bipartition([[1, 2, 3, 5, -1, -2, -3, -5], [4, -4]])]);
<inverse block bijection semigroup of degree 5 with 5 generators>
gap> IsHTrivial(S);
true
gap> IsLTrivial(S);
true
gap> IsRTrivial(S);
true
gap> I := SemigroupIdeal(S, S.1);
<inverse bipartition semigroup ideal of degree 5 with 1 generator>
gap> IsHTrivial(I);
true
gap> IsLTrivial(I);
true
gap> IsRTrivial(I);
true
gap> S := Semigroup(S);;
gap> IsHTrivial(S);
true
gap> IsLTrivial(S);
true
gap> IsRTrivial(S);
true
gap> I := SemigroupIdeal(S, S.1);;
gap> IsHTrivial(I);
true
gap> IsLTrivial(I);
true
gap> IsRTrivial(I);
true

# properties: IsXTrivial, acting, false, 5
gap> S := Semigroup(
>  Bipartition([[1, 2, 3, 4, 5, -6], [6, -1, -2, -3, -4, -5]]),
>  Bipartition([[1, 2, 6, -1, -5, -6], [3, 5, -2, -3], [4, -4]]));;
gap> IsHTrivial(S);
false
gap> IsLTrivial(S);
false
gap> IsRTrivial(S);
false
gap> S := Semigroup(
>  Bipartition([[1, 2, 3, 4, 5, -6], [6, -1, -2, -3, -4, -5]]),
>  Bipartition([[1, 2, 6, -1, -5, -6], [3, 5, -2, -3], [4, -4]]));;
gap> Size(S);;
gap> IsHTrivial(S);
false
gap> IsLTrivial(S);
false
gap> IsRTrivial(S);
false

# properties: IsXTrivial, acting, true, 5
gap> S :=
> Monoid(Transformation([1, 1, 1, 2, 1, 5, 3]),
>  Transformation([1, 2, 1, 2]), Transformation([1, 1, 1, 3, 1, 2, 5]),
>  Transformation([1, 1, 3, 3]), Transformation([1, 2, 3, 4, 1, 2]),
>  Transformation([1, 1, 3, 4, 5, 5]),
>  Transformation([1, 2, 3, 4, 1, 6, 3]),
>  Transformation([1, 2, 1, 4, 5, 6, 5]));;
gap> IsRTrivial(S);
true
gap> S := AsSemigroup(IsBipartitionSemigroup, S);;
gap> IsRTrivial(S);
true

# properties: IsXTrivial, infinite semigroup, 7
gap> S := FreeSemigroup(2);;
gap> IsHTrivial(S);
Error, no method found! For debugging hints type ?Recovery from NoMethodFound
Error, no 2nd choice method found for `IsHTrivial' on 1 arguments
gap> IsLTrivial(S);
Error, no method found! For debugging hints type ?Recovery from NoMethodFound
Error, no 2nd choice method found for `IsLTrivial' on 1 arguments
gap> IsRTrivial(S);
Error, no method found! For debugging hints type ?Recovery from NoMethodFound
Error, no 2nd choice method found for `IsRTrivial' on 1 arguments
gap> IsDTrivial(S);
Error, no method found! For debugging hints type ?Recovery from NoMethodFound
Error, no 2nd choice method found for `IsRTrivial' on 1 arguments

# properties: IsLTrivial, rho, 1/1
gap> S := FullTransformationMonoid(3);;
gap> IsLTrivial(S);
false
gap> S := Semigroup(S);
<transformation monoid of degree 3 with 3 generators>
gap> Size(S);
27
gap> IsLTrivial(S);
false
gap> IsRTrivial(S);
false

# properties: IsRTrivial, trans, 1/1
gap> S := Semigroup(Transformation([1, 2, 2, 2]));
<commutative transformation semigroup of degree 4 with 1 generator>
gap> IsRTrivial(S);
true

# properties: IsRTrivial, pperm, 1/1
gap> S := Semigroup(PartialPerm([1, 2], [1, 2]));
<trivial partial perm group of rank 2 with 1 generator>
gap> IsRTrivial(S);
true

# properties: IsGroupAsSemigroup, parent, non-acting, 1
gap> S := AsSemigroup(IsBooleanMatSemigroup, Group((1, 2, 3)));
<commutative semigroup of 3x3 boolean matrices with 1 generator>
gap> I := SemigroupIdeal(S, S.1);
<commutative semigroup ideal of 3x3 boolean matrices with 1 generator>
gap> IsGroupAsSemigroup(S);
true
gap> IsGroupAsSemigroup(I);
true

# properties: IsGroupAsSemigroup, infinite, 2
gap> IsGroupAsSemigroup(FreeSemigroup(2));
Error, no method found! For debugging hints type ?Recovery from NoMethodFound
Error, no 3rd choice method found for `IsGroupAsSemigroup' on 1 arguments

# properties: IsGroupAsSemigroup, parent, acting, 3
gap> S := AsSemigroup(IsBipartitionSemigroup, Group((1, 2, 3)));
<block bijection group of degree 3 with 1 generator>
gap> IsGroupAsSemigroup(S);
true
gap> I := SemigroupIdeal(S, S.1);
<commutative inverse bipartition semigroup ideal of degree 3 with 1 generator>
gap> IsGroupAsSemigroup(I);
true

# properties: IsGroupAsSemigroup, 4
gap> S := Semigroup(Transformation([1, 2, 3, 1, 2, 3]) * (1, 2, 3));
<commutative transformation semigroup of degree 6 with 1 generator>
gap> IsGroupAsSemigroup(S);
true

# properties: IsGroupAsSemigroup, for IsGroup groups, 5
gap> IsGroupAsSemigroup(SymmetricGroup(5));
true
gap> IsGroupAsSemigroup(Semigroup(Transformation([1])));
true

# properties: IsGroupAsSemigroup, for maximal rank acting semigroup, 6
gap> S := Semigroup(Transformation([2, 3, 1]));;
gap> IsGroupAsSemigroup(S);
true
gap> IsGroupAsSemigroup(AsSemigroup(IsMatrixOverFiniteFieldSemigroup, S));
true

# properties: IsIdempotentGenerated, 1
gap> S :=
> Semigroup(
> [Bipartition([[1, 2, 3, 4, 5, 6, 7, -1, -2, -3, -4, -5, -6, -7]]),
>   Bipartition([[1, 2, 3, 4, 5, 6, -1, -2, -3, -4, -5, -6], [7, -7]]),
>   Bipartition([[1, 5, -1, -5], [2, 3, 4, 6, 7, -2, -3, -4, -6, -7]]),
>   Bipartition([[1, 2, 7, -1, -2, -7], [3, 4, 5, 6, -3, -4, -5, -6]])]);
<block bijection semigroup of degree 7 with 4 generators>
gap> IsIdempotentGenerated(S);
true

# properties: IsIdempotentGenerated, 2
gap> S := Monoid([BooleanMat([[true, true], [true, true]]),
>  BooleanMat([[true, false], [true, true]]),
>  BooleanMat([[false, false], [true, true]])]);
<monoid of 2x2 boolean matrices with 3 generators>
gap> IsIdempotentGenerated(S);
true

# properties: IsIdempotentGenerated, 3
gap> S := Semigroup([PartialPerm([1, 2, 4, 5], [2, 5, 3, 6]),
>  PartialPerm([1, 2, 4, 5], [5, 1, 3, 4])]);
<partial perm semigroup of rank 4 with 2 generators>
gap> IsIdempotentGenerated(S);
false

# properties: IsIdempotentGenerated, 4
gap> S := Semigroup([PartialPerm([1, 2, 4, 5], [1, 2, 4, 5]),
>  PartialPerm([1, 2, 4, 5], [5, 1, 3, 4])]);
<partial perm semigroup of rank 4 with 2 generators>
gap> IsIdempotentGenerated(S);
false

# properties: IsIdempotentGenerated, 6
gap> S := FreeSemigroup(1);;
gap> IsIdempotentGenerated(S);
Error, no method found! For debugging hints type ?Recovery from NoMethodFound
Error, no 3rd choice method found for `IsIdempotentGenerated' on 1 arguments

# properties: IsIdempotentGenerated, 5
gap> S := AsSemigroup(IsBooleanMatSemigroup,
>                     SingularTransformationMonoid(3));;
gap> IsIdempotentGenerated(S);
true

# properties: IsIdempotentGenerated, 7

# Performance testing: T_9 used to take seconds
gap> S := FullTransformationMonoid(9);;
gap> S := Monoid(S, rec(acting := true));;
gap> IsIdempotentGenerated(S);
false
gap> S := Semigroup(GeneratorsOfMonoid(S), rec(acting := true));;
gap> IsIdempotentGenerated(S);
false

# Coverage and performance testing
gap> S := FullTransformationMonoid(8);;
gap> S := Semigroup(GeneratorsOfMonoid(S), rec(acting := true));;
gap> IsIdempotentGenerated(S);
false
gap> S := Semigroup(S, rec(acting := true));;
gap> Idempotents(S);;
gap> IsIdempotentGenerated(S);
false

# properties: IsIdempotentGenerated, 8
gap> S := Semigroup([Transformation([3, 2, 1]), Transformation([2, 2, 2])]);
<transformation semigroup of degree 3 with 2 generators>
gap> IsIdempotentGenerated(S);
false
gap> I := SemigroupIdeal(S, S.1 ^ 2);;
gap> IsIdempotentGenerated(I);
false
gap> I = S;
true

# properties: IsInverseSemigroup, 1
gap> S := Semigroup([PartialPerm([1, 2, 3, 5], [2, 3, 5, 7]),
>  PartialPerm([1, 2, 3, 6], [2, 5, 3, 1]),
>  PartialPerm([2, 3, 5, 7], [1, 2, 3, 5]),
>  PartialPerm([1, 2, 3, 5], [6, 1, 3, 2])]);;
gap> IsInverseSemigroup(S);
true

# properties: IsInverseSemigroup, 2
gap> IsInverseSemigroup(FullTransformationMonoid(3));
false

# properties: IsInverseSemigroup, 3
gap> S := Semigroup(
> [BooleanMat([[true, false, true, true, true, false, false, true],
>       [true, false, true, true, true, true, true, false],
>       [true, true, true, false, false, false, false, false],
>       [true, false, true, true, false, false, false, true],
>       [true, false, true, false, true, true, true, true],
>       [false, true, false, true, true, true, false, true],
>       [true, false, false, false, true, false, true, false],
>       [false, true, true, false, true, false, true, false]]),
>   BooleanMat([[true, false, true, false, true, false, true, false],
>       [false, false, true, true, true, true, false, true],
>       [false, false, false, true, false, false, true, false],
>       [true, true, false, true, false, false, true, false],
>       [true, true, true, false, false, true, true, true],
>       [false, true, true, true, true, false, true, false],
>       [false, true, false, false, false, false, true, false],
>       [true, true, false, true, true, true, true, false]])]);;
gap> GreensDClasses(S);;
gap> IsInverseSemigroup(S);
false

# WW: This is removed since, at the moment, a different no method found error
# is given depending on which packages are loaded
## properties: IsInverseSemigroup, infinite, 4
#gap> S := FreeSemigroup(2);;
#gap> IsInverseSemigroup(S);
#Error, no method found! For debugging hints type ?Recovery from NoMethodFound
#Error, no 2nd choice method found for `CayleyGraphDualSemigroup' on 1 argument\
#s

# properties: IsLeftSimple, non-regular, 1
gap> S := RegularBooleanMatMonoid(3);
<monoid of 3x3 boolean matrices with 4 generators>
gap> IsRegularSemigroup(S);
false
gap> IsLeftSimple(S);
false

# properties: IsLeftSimple, left zero, 2
gap> S := TrivialSemigroup();
<trivial transformation group of degree 0 with 1 generator>
gap> IsLeftZeroSemigroup(S);
true
gap> IsLeftSimple(S);
true

# # properties: IsLeftSimple, known L-classes, 3
gap> S := Monoid([Matrix(GF(11), [[0 * Z(11)]]),
>  Matrix(GF(11), [[Z(11)]]),
>  Matrix(GF(11), [[Z(11) ^ 4]]),
>  Matrix(GF(11), [[Z(11) ^ 5]]),
>  Matrix(GF(11), [[Z(11) ^ 8]]),
>  Matrix(GF(11), [[Z(11) ^ 9]])]);;
gap> NrLClasses(S);
2
gap> IsLeftSimple(S);
false

# properties: IsLeftSimple, acting, 4
gap> S := JonesMonoid(3);
<regular bipartition *-monoid of degree 3 with 2 generators>
gap> IsLeftSimple(S);
false

# properties: IsLeftSimple, non-acting, 5
gap> S := RegularBooleanMatMonoid(3);
<monoid of 3x3 boolean matrices with 4 generators>
gap> IsLeftSimple(S);
false

# properties: IsLeftSimple, infinite, 6
gap> S := FreeSemigroup(4);;
gap> IsLeftSimple(S);
Error, no method found! For debugging hints type ?Recovery from NoMethodFound
Error, no 3rd choice method found for `IsLeftSimple' on 1 arguments

# properties: IsLeftZeroSemigroup, 1
gap> S := LeftZeroSemigroup(4);;
gap> IsLeftZeroSemigroup(S);
true
gap> I := SemigroupIdeal(S, S.1);;
gap> IsLeftZeroSemigroup(I);
true

# properties: IsLeftZeroSemigroup, 2
gap> S := AsSemigroup(IsTransformationSemigroup,
> RectangularBand(IsReesMatrixSemigroup, 2, 2));
<transformation semigroup of size 4, degree 5 with 2 generators>
gap> IsLeftZeroSemigroup(S);
false

# properties: IsLeftZeroSemigroup, 3
gap> S := FreeSemigroup(1);;
gap> IsLeftZeroSemigroup(S);
Error, no method found! For debugging hints type ?Recovery from NoMethodFound
Error, no 3rd choice method found for `IsLeftZeroSemigroup' on 1 arguments

# properties: IsLeftZeroSemigroup, 4
gap> S := LeftZeroSemigroup(IsTransformationSemigroup, 4);;
gap> S := Semigroup(S, rec(acting := true));;
gap> IsLeftZeroSemigroup(S);
true
gap> I := SemigroupIdeal(S, S.1);;
gap> GeneratorsOfSemigroup(I);;
gap> IsLeftZeroSemigroup(I);
true

# properties: IsMonogenicSemigroup, 1
gap> S := Semigroup(MonogenicSemigroup(10, 10));
<commutative transformation semigroup of degree 20 with 1 generator>
gap> IsMonogenicSemigroup(S);
true

# properties: IsMonogenicSemigroup, 2
gap> S := Semigroup(Elements(MonogenicSemigroup(10, 10)));
<transformation semigroup of degree 20 with 19 generators>
gap> IsMonogenicSemigroup(S);
true

# properties: IsMonogenicSemigroup, 3
gap> IsMonogenicSemigroup(BrauerMonoid(3));
false

# properties: IsMonogenicSemigroup, 4
gap> IsMonogenicSemigroup(SymmetricInverseMonoid(3));
false

# properties: IsMonogenicSemigroup, 5
gap> IsMonogenicSemigroup(AsSemigroup(IsBooleanMatSemigroup,
> Group((1, 2, 3), (2, 3))));
false

# properties: IsMonogenicSemigroup, 6
gap> IsMonogenicSemigroup(FreeSemigroup(1));
true

# properties: IsMonogenicSemigroup, 7
gap> IsMonogenicSemigroup(FreeInverseSemigroup(1));
Error, no method found! For debugging hints type ?Recovery from NoMethodFound
Error, no 3rd choice method found for `IsMonogenicSemigroup' on 1 arguments

# properties: IsMonogenicSemigroup, 8
gap> S := SymmetricInverseSemigroup(3);;
gap> GreensDClasses(S);;
gap> IsMonogenicSemigroup(S);
false

# properties: IsMonogenicSemigroup, 9
gap> S := MonogenicSemigroup(IsTransformationSemigroup, 3, 2);;
gap> S := Semigroup(S.1, S.1 ^ 2);;
gap> GreensDClasses(S);;
gap> IsMonogenicSemigroup(S);
true

# properties: IsMonogenicSemigroup, 10
gap> S := Semigroup([
>  Transformation([2, 6, 7, 2, 6, 9, 9, 1, 1, 5]),
>  Transformation([6, 9, 9, 6, 9, 1, 1, 2, 2, 6]),
>  Transformation([2, 6, 7, 2, 6, 9, 9, 1, 1, 5])]);;
gap> HasIsMonogenicSemigroup(S);
false
gap> IsMonogenicSemigroup(S);
true

# properties: IsMonogenicSemigroup, 11
# test for the ImmediateMethod
gap> S := CyclicGroup(IsPermGroup, 10);;
gap> GeneratorsOfSemigroup(S);;
gap> HasIsMonogenicSemigroup(S);
true
gap> IsMonogenicSemigroup(S);
true
gap> x := MinimalSemigroupGeneratingSet(S)[1];;
gap> S := Semigroup(x, x, x);;
gap> IsMonogenicSemigroup(S);
true
gap> S := Subsemigroup(FullTransformationMonoid(2), []);;
gap> IsEmpty(S);
true
gap> IsMonogenicSemigroup(S);
false

# properties: IsMonogenicInverseSemigroup, 1
gap> IsMonogenicInverseSemigroup(AsSemigroup(IsBooleanMatSemigroup,
>                                            Group((1, 2, 3), (2, 3))));
false

# properties: IsMonogenicInverseSemigroup, 2
gap> IsMonogenicInverseSemigroup(SymmetricInverseMonoid(3));
false

# properties: IsMonogenicInverseSemigroup, 3
gap> IsMonogenicInverseSemigroup(InverseSemigroup(
> PartialPerm([1, 2, 3, 4, 5, 6, 7, 8], [10, 7, 2, 5, 6, 9, 3, 8])));
true

# properties: IsMonogenicInverseSemigroup, 4
gap> IsMonogenicInverseSemigroup(InverseSemigroup(
> PartialPerm([1, 2, 3, 4, 5, 6, 7, 8], [10, 7, 2, 5, 6, 9, 3, 8]),
> PartialPerm([1, 2, 3, 4, 5, 6, 7, 8], [10, 7, 2, 5, 6, 9, 3, 8])));
true

# properties: IsMonogenicInverseSemigroup, 5
gap> IsMonogenicInverseSemigroup(
> InverseSemigroup(Elements(InverseSemigroup(
> PartialPerm([1, 2, 3, 4, 5, 6, 7, 8], [10, 7, 2, 5, 6, 9, 3, 8])))));
true

# properties: IsMonogenicInverseSemigroup, 6
gap> IsMonogenicInverseSemigroup(BrauerMonoid(3));
false

# properties: IsMonogenicInverseSemigroup, 7
gap> S := FreeInverseSemigroup(1);;
gap> IsMonogenicInverseSemigroup(S);
true
gap> S := FreeInverseSemigroup(2);;
gap> IsMonogenicInverseSemigroup(S);
Error, no method found! For debugging hints type ?Recovery from NoMethodFound
Error, no 4th choice method found for `IsMonogenicInverseSemigroup' on 1 argum\
ents

# properties: IsMonogenicMonoid, 1
gap> S := AsSemigroup(IsBooleanMatSemigroup,
>                     Group((1, 2, 3), (2, 3)));;
gap> S := Monoid(S);;
gap> IsMonogenicMonoid(S);
false

# properties: IsMonogenicMonoid, 2
gap> IsMonogenicMonoid(SymmetricInverseMonoid(3));
false

# properties: IsMonogenicMonoid, 3
gap> IsMonogenicMonoid(Monoid(
> PartialPerm([1, 2, 3, 4, 5, 6, 7, 8], [10, 7, 2, 5, 6, 9, 3, 8])));
true

# properties: IsMonogenicMonoid, 4
gap> IsMonogenicMonoid(Monoid(
> PartialPerm([1, 2, 3, 4, 5, 6, 7, 8], [10, 7, 2, 5, 6, 9, 3, 8]),
> PartialPerm([1, 2, 3, 4, 5, 6, 7, 8], [10, 7, 2, 5, 6, 9, 3, 8])));
true

# properties: IsMonogenicMonoid, 5
gap> IsMonogenicMonoid(
> Monoid(Elements(Monoid(
> PartialPerm([1, 2, 3, 4, 5, 6, 7, 8], [10, 7, 2, 5, 6, 9, 3, 8])))));
true

# properties: IsMonogenicMonoid, 6
gap> IsMonogenicMonoid(BrauerMonoid(3));
false

# properties: IsMonogenicMonoid, 7
gap> S := FreeMonoid(1);;
gap> IsMonogenicMonoid(S);
true
gap> S := FreeMonoid(2);;
gap> IsMonogenicMonoid(S);
Error, no method found! For debugging hints type ?Recovery from NoMethodFound
Error, no 3rd choice method found for `IsMonogenicMonoid' on 1 arguments

# properties: IsMonogenicMonoid, 8
gap> S := SymmetricInverseMonoid(3);;
gap> GreensDClasses(S);;
gap> IsMonogenicMonoid(S);
false

# properties: IsMonogenicMonoid, 9
gap> S := MonogenicSemigroup(IsTransformationSemigroup, 3, 2);;
gap> S := Monoid(S.1, S.1 ^ 2);;
gap> GreensDClasses(S);;
gap> IsMonogenicMonoid(S);
true

# properties: IsMonogenicMonoid, 9
gap> S := Monoid(Transformation([2, 1, 2, 3, 4]),
>                Transformation([2, 1, 2, 3, 4]));;
gap> HasIsMonogenicMonoid(S) and IsMonogenicMonoid(S);
true

# properties: IsMonogenicInverseMonoid, 1
gap> S := AsSemigroup(IsBooleanMatSemigroup, SymmetricGroup(3));;
gap> S := Monoid(S);;
gap> IsMonogenicInverseMonoid(S);
false

# properties: IsMonogenicInverseMonoid, 2
gap> IsMonogenicInverseMonoid(SymmetricInverseMonoid(3));
false

# properties: IsMonogenicInverseMonoid, 3
gap> IsMonogenicInverseMonoid(InverseMonoid(
> PartialPerm([1, 2, 3, 4, 5, 6, 7, 8], [10, 7, 2, 5, 6, 9, 3, 8])));
true

# properties: IsMonogenicInverseMonoid, 4
gap> IsMonogenicInverseMonoid(InverseMonoid(
> PartialPerm([1, 2, 3, 4, 5, 6, 7, 8], [10, 7, 2, 5, 6, 9, 3, 8]),
> PartialPerm([1, 2, 3, 4, 5, 6, 7, 8], [10, 7, 2, 5, 6, 9, 3, 8])));
true

# properties: IsMonogenicInverseMonoid, 5
gap> IsMonogenicInverseMonoid(
> InverseMonoid(Elements(InverseMonoid(
> PartialPerm([1, 2, 3, 4, 5, 6, 7, 8], [10, 7, 2, 5, 6, 9, 3, 8])))));
true

# properties: IsMonogenicInverseMonoid, 6
gap> IsMonogenicInverseMonoid(BrauerMonoid(3));
false

# properties: IsMonogenicInverseMonoid, 7
gap> S := FreeGroup(2);;
gap> GeneratorsOfInverseMonoid(S);;
gap> IsMonogenicInverseMonoid(S);
Error, no method found! For debugging hints type ?Recovery from NoMethodFound
Error, no 3rd choice method found for `IsMonogenicInverseMonoid' on 1 argument\
s

# properties: IsMonoidAsSemigroup, 1
gap> S := Semigroup(Transformation([1, 4, 6, 2, 5, 3, 7, 8, 9, 9]),
> Transformation([6, 3, 2, 7, 5, 1, 8, 8, 9, 9]));;
gap> IsMonoidAsSemigroup(S);
true

# properties: IsMonoidAsSemigroup, 2
gap> S := FreeGroup(1);;
gap> IsMonoidAsSemigroup(S);
true
gap> S := FreeSemigroup(1);;
gap> IsMonoidAsSemigroup(S);
Error, no method found! For debugging hints type ?Recovery from NoMethodFound
Error, no 2nd choice method found for `MultiplicativeNeutralElement' on 1 argu\
ments

# properties: IsOrthodoxSemigroup, 1
gap> gens := [Transformation([1, 1, 1, 4, 5, 4]),
>  Transformation([1, 2, 3, 1, 1, 2]),
>  Transformation([1, 2, 3, 1, 1, 3]),
>  Transformation([5, 5, 5, 5, 5, 5])];;
gap> S := Semigroup(gens);
<transformation semigroup of degree 6 with 4 generators>
gap> IsOrthodoxSemigroup(S);
true

# properties: IsOrthodoxSemigroup, 2
gap> S := Semigroup(
>  PBR(
>   [[-5, -4, -3, -2, -1, 1, 2, 4, 5], [-3, -1, 2, 6],
>    [-6, -4, -3, -2, 2, 5], [-6, -3, -2, 1, 2, 3, 4, 6],
>    [-5, -4, -2, 1, 2, 5], [-4, -3, -2, -1, 6]],
>   [[-6, -5, -4, -1, 1, 3, 4, 6], [-4, -2, 1, 2, 4, 6],
>    [-5, -4, -3, -2, 3, 5, 6], [-6, -5, -4, -2, 1, 2, 3, 4],
>    [-6, -5, -4, 1, 3], [-6, -5, -4, -2, 1, 4, 5]]),
>  PBR(
>   [[-6, -5, -3, -2, 1, 3, 4], [-6, -5, -4, -3, -2, -1, 1, 2, 3, 6],
>    [-1, 1, 2, 3, 4, 5], [-6, -5, -3, -1, 1, 6],
>    [-5, -4, -2, -1, 1, 4, 5, 6], [-6, -4, -3, -2, -1, 1, 3]],
>   [[-4, 1, 6], [-6, -5, -4, -3, -1, 3, 5, 6], [-5, -4, -3, -2, 4, 5, 6],
>    [-2, -1, 1, 2, 3, 4, 6], [-5, -4, -3, -1, 2, 4, 5],
>    [-6, -5, -3, 1, 3, 4]]),
>  PBR(
>   [[-6, -5, -4, 2, 3, 5, 6], [-6, -5, -4, -3, -2, -1, 1, 2, 4],
>   [-6, -5, -4, -3, -2, -1, 1, 3, 6], [-6, -2, -1, 2, 4], [-5, -1, 1, 2, 3],
>   [-6, -5, -3, -2, -1, 1, 2, 4, 6]],
>   [[-5, -4, -3, -2, 1, 5, 6], [-5, -3, -1, 2, 3, 5, 6],
>    [-6, -4, -3, -1, 1, 2, 3, 4, 5], [-5, -4, 1, 4, 5], [-5, -4, -2, 4, 6],
>    [-5, -3, -1, 1, 2, 3, 4, 5, 6]]),
>  PBR(
>   [[-4, -2, -1, 2, 5], [-6, -5, -2, -1, 1, 4], [-6, -3, -1, 3, 5],
>    [-6, -4, -2, -1, 3, 6], [-5, -4, -2, 2, 4, 6], [-4, -2, -1, 1, 3, 5, 6]],
>   [[-4, 1, 4, 6], [-3, -2, 1, 4, 5, 6], [-4, -2, 1, 2, 4, 5],
>    [-6, -5, -1, 1, 3, 4, 5, 6], [-6, -5, -4, -3, 1, 3, 5, 6],
>    [-6, -5, -4, 3, 6]]),
>  PBR(
>   [[-6, -4, -3, 3, 6], [-5, -3, 2, 5, 6], [-6, -2, -1, 1, 3, 4, 5],
>    [-3, -2, -1, 1, 2, 3, 4, 5], [-6, -5, -2, 3, 5], [-5, -4, -3, 2, 3, 5]],
>   [[-3, 1, 2, 3, 6], [-5, -4, -3, -1, 1, 2, 4, 6], [-6, -4, -3, -2, -1, 2],
>    [-5, -4, 1, 3, 4, 5, 6], [-6, -5, -4, 5, 6],
>    [-6, -4, -1, 1, 2, 3, 5, 6]]),
>  PBR(
>   [[-5, -3, -1, 4, 5], [-5, -3, 2, 4, 5, 6],
>    [-6, -5, -4, -2, -1, 1, 3, 5, 6], [-6, -5, 4, 5, 6],
>    [-6, -1, 1, 2, 5, 6], [-3, -1, 1, 2, 4]],
>   [[-6, -4, -3, -2, -1, 1, 2, 3, 4, 6], [-6, -5, -2, 1, 2, 4],
>    [-5, -3, -1, 3, 5, 6], [-6, -5, -4, -3, -1, 3, 4, 6],
>    [-4, -3, 1, 3, 4, 6], [-6, -5, -4, -2, 1, 2, 3, 4, 6]]));
<pbr semigroup of degree 6 with 6 generators>
gap> IsOrthodoxSemigroup(S);
false

# properties: IsOrthodoxSemigroup, 3
gap> IsOrthodoxSemigroup(FullTransformationMonoid(3));
false

# properties: IsRectangularBand, 1
gap> S := Semigroup(RectangularBand(IsReesMatrixSemigroup, 4, 4));
<subsemigroup of 4x4 Rees matrix semigroup with 16 generators>
gap> IsRectangularBand(S);
true

# properties: IsRectangularBand, 2
gap> S := FullTransformationMonoid(3);;
gap> IsRectangularBand(S);
false

# properties: IsRectangularBand, 3
gap> IsRectangularBand(FreeBand(2));
false

# properties: IsRectangularBand, 4
gap> S := ReesMatrixSemigroup(Group([(1, 2)]),
> [[(), (), (), (), ()], [(), (), (), (), ()], [(), (), (), (), ()],
>  [(), (), (), (), ()], [(), (), (), (), ()]]);;
gap> IsBand(S);
false
gap> IsRectangularBand(S);
false

# properties: IsRectangularBand, 5
gap> S := ReesMatrixSemigroup(Group([(1, 2)]),
> [[(), (), (), (), ()], [(), (), (), (), ()], [(), (), (), (), ()],
>  [(), (), (), (), ()], [(), (), (), (), ()]]);;
gap> IsRectangularBand(S);
false

# properties: IsRectangularBand, 5
gap> IsRectangularBand(FreeSemigroup(2));
Error, no method found! For debugging hints type ?Recovery from NoMethodFound
Error, no 3rd choice method found for `IsRectangularBand' on 1 arguments

# properties: IsRegularSemigroup, 1/7
gap> S := ReesMatrixSemigroup(Group([(1, 2)]),
> [[(), (), (), (), ()], [(), (), (), (), ()], [(), (), (), (), ()],
>  [(), (), (), (), ()], [(), (), (), (), ()]]);;
gap> IsRegularSemigroup(S);
true
gap> IsRegularSemigroup(AsSemigroup(IsTransformationSemigroup, S));
true

# properties: IsRegularSemigroup, 2/7
gap> S := ReesMatrixSemigroup(Group([(1, 2)]),
> [[(), (), (), (), ()], [(), (), (), (), ()], [(), (), (), (), ()],
>  [(), (), (), (), ()], [(), (), (), (), ()]]);;
gap> IsRegularSemigroup(S);
true

# properties: IsRegularSemigroup, 3/7
gap> gens := [Transformation([1, 2, 4, 3, 6, 5, 4]),
>  Transformation([1, 2, 5, 6, 3, 4, 5]),
>  Transformation([2, 1, 2, 2, 2, 2, 2])];;
gap> S := Semigroup(gens);
<transformation semigroup of degree 7 with 3 generators>
gap> IsCompletelyRegularSemigroup(S);
true
gap> IsRegularSemigroup(S);
true

# properties: IsRegularSemigroup, 4/7
gap> S := AsSemigroup(IsTransformationSemigroup, PartitionMonoid(3));
<transformation monoid of size 203, degree 203 with 4 generators>
gap> DClasses(S);;
gap> IsRegularSemigroup(S);
true
gap> S := Semigroup(PartitionMonoid(3));
<bipartition monoid of degree 3 with 4 generators>
gap> DClasses(S);;
gap> IsRegularSemigroup(S);
true

# properties: IsRegularSemigroup, 5/7
gap> S := Semigroup([Bipartition([[1, 2, 3, 4, -1, -3], [-2], [-4]]),
>  Bipartition([[1, 2, 4, -4], [3, -3], [-1], [-2]]),
>  Bipartition([[1, 3], [2, 4, -1], [-2, -3, -4]]),
>  Bipartition([[1, -4], [2, 4, -1, -3], [3, -2]])]);;
gap> IsRegularSemigroup(S);
false

# properties: IsRegularSemigroup, 6/7
gap> gens := [Transformation([1, 2, 4, 3, 6, 5, 4]),
>  Transformation([1, 2, 5, 6, 3, 4, 5]),
>  Transformation([2, 1, 2, 2, 2, 2, 2])];;
gap> S := AsSemigroup(IsBipartitionSemigroup, Semigroup(gens));
<bipartition semigroup of degree 7 with 3 generators>
gap> IsCompletelyRegularSemigroup(S);
true
gap> IsRegularSemigroup(S);
true

# properties: IsRegularSemigroup, 7/7
gap> S := ReesMatrixSemigroup(Group([(1, 2)]),
> [[(), (), (), (), ()], [(), (), (), (), ()]]);;
gap> IsRegularSemigroup(AsSemigroup(IsBipartitionSemigroup, S));
true

# properties: IsRegularSemigroup, 8
gap> S := Semigroup(Transformation([3, 1, 3, 5, 4, 5, 5, 7]),
>                   Transformation([1, 1, 8, 4, 4, 4, 6, 2]),
>                   Transformation([2, 7, 7, 2, 8, 6, 7, 3]),
>                   Transformation([4, 2, 5, 7, 2, 5, 8, 5]),
>                   Transformation([2, 5, 2, 1, 2, 8, 3, 6]),
>                   Transformation([8, 6, 7, 2, 2, 4, 6, 5]),
>                   Transformation([4, 8, 5, 2, 5, 8, 4, 2]),
>                   Transformation([4, 1, 4, 4, 2, 2, 3, 5]),
>                   rec(acting := true));;
gap> data := SemigroupData(S);;
gap> Enumerate(data, 500);;
gap> IsRegularSemigroup(S);
false

# properties: IsRegularSemigroup, 9
gap> S := Semigroup(FullTransformationMonoid(4));;
gap> Size(S);;
gap> IsRegularSemigroup(S);
true
gap> S := Semigroup(PartitionMonoid(3));;
gap> Size(S);;
gap> IsRegularSemigroup(S);
true

# properties: IsRegularSemigroup, 9
gap> S := Semigroup(PartitionMonoid(3));;
gap> IsStarSemigroup(S);
true
gap> IsRegularSemigroup(S);
true

# properties: IsRegularElementSemigroup, 1/8
gap> S := Semigroup([Transformation([6, 9, 10, 1, 11, 3, 6, 6, 2, 10, 12, 2]),
>  Transformation([7, 8, 8, 11, 2, 11, 10, 2, 11, 4, 4, 7])]);
<transformation semigroup of degree 12 with 2 generators>
gap> x := Transformation([3, 10, 5, 10, 7, 2, 5, 6, 12, 11, 11, 9]);;
gap> IsRegularSemigroupElement(S, x);
false
gap> IsRegularSemigroupElementNC(S, x);
false
gap> x := Transformation([1, 1, 1, 10, 1, 10, 12, 1, 10, 10, 10, 1]);;
gap> IsRegularSemigroupElement(S, x);
false
gap> IsRegularSemigroupElementNC(S, x);
false

# properties: IsRegularElementSemigroup, 2/8
gap> S := Semigroup([Transformation([6, 9, 10, 1, 11, 3, 6, 6, 2, 10, 12, 2]),
>  Transformation([7, 8, 8, 11, 2, 11, 10, 2, 11, 4, 4, 7])]);
<transformation semigroup of degree 12 with 2 generators>
gap> Size(S);
2030
gap> x := Transformation([1, 1, 1, 10, 1, 10, 12, 1, 10, 10, 10, 1]);;
gap> IsRegularSemigroupElement(S, x);
false
gap> IsRegularSemigroupElementNC(S, x);
false

# properties: IsRegularElementSemigroup, 3/8
gap> IsRegularSemigroupElement(FullTransformationMonoid(3),
> Transformation([1, 1, 1]));
true
gap> IsRegularSemigroupElementNC(FullTransformationMonoid(3),
> Transformation([1, 1, 1]));
true

# properties: IsRegularElementSemigroup, 4/8
gap> S := Semigroup(FullTransformationMonoid(3));
<transformation monoid of degree 3 with 3 generators>
gap> IsRegularSemigroupElement(S, Transformation([1, 1, 1]));
true
gap> IsRegularSemigroupElementNC(S, Transformation([1, 1, 1]));
true

# properties: IsRegularElementSemigroup, 5/8
gap> S := Semigroup([Transformation([6, 9, 10, 1, 11, 3, 6, 6, 2, 10, 12, 2]),
>  Transformation([7, 8, 8, 11, 2, 11, 10, 2, 11, 4, 4, 7])]);
<transformation semigroup of degree 12 with 2 generators>
gap> IsRegularSemigroupElement(AsSemigroup(IsBipartitionSemigroup, S),
> Bipartition([
>  [1, 2, 3, 4, 5, 7, -4, -10, -11, -12], [6, 11, -6, -7, -9],
>  [8, 9, 10, -2, -3, -5, -8], [12, -1]]));
false
gap> x := Bipartition([[1, 2, 6, 10, -1, -3, -4, -5, -7],
> [3, 5, 7, 11, -2, -8, -9], [4, 8, 9, 12, -10], [-6, -11, -12]]);;
gap> IsRegularSemigroupElement(AsSemigroup(IsBipartitionSemigroup, S), x);
false
gap> IsRegularSemigroupElementNC(AsSemigroup(IsBipartitionSemigroup, S), x);
false

# properties: IsRegularElementSemigroup, 6/8
gap> S := Semigroup([Transformation([6, 9, 10, 1, 11, 3, 6, 6, 2, 10, 12, 2]),
>  Transformation([7, 8, 8, 11, 2, 11, 10, 2, 11, 4, 4, 7])]);
<transformation semigroup of degree 12 with 2 generators>
gap> Size(S);
2030
gap> x := Bipartition([[1, 2, 6, 10, -1, -3, -4, -5, -7],
> [3, 5, 7, 11, -2, -8, -9], [4, 8, 9, 12, -10], [-6, -11, -12]]);;
gap> IsRegularSemigroupElement(AsSemigroup(IsBipartitionSemigroup, S), x);
false
gap> IsRegularSemigroupElementNC(AsSemigroup(IsBipartitionSemigroup, S), x);
false

# properties: IsRegularElementSemigroup, 7/8
gap> IsRegularSemigroupElement(PartitionMonoid(3),
> Bipartition([[1, 2, 3, -1, -2], [-3]]));
true
gap> IsRegularSemigroupElementNC(PartitionMonoid(3),
> Bipartition([[1, 2, 3, -1, -2], [-3]]));
true

# properties: IsRegularElementSemigroup, 8/8
gap> S := Semigroup(PartitionMonoid(3));
<bipartition monoid of degree 3 with 4 generators>
gap> IsRegularSemigroupElement(S, Bipartition([[1, -1], [2, 3, -2, -3]]));
true
gap> IsRegularSemigroupElementNC(S, Bipartition([[1, -1], [2, 3, -2, -3]]));
true

# properties: IsRegularElementSemigroup (for non-acting semigroup) 9
gap> S := RegularBooleanMatMonoid(3);;
gap> x := Matrix(IsBooleanMat, [[1, 0, 1], [1, 0, 0], [0, 0, 1]]);;
gap> IsRegularSemigroupElement(S, x);
true

# properties: IsRegularElementSemigroup (for acting semigroup) 9
gap> S := Semigroup(FullTransformationMonoid(3));;
gap> Size(S);;
gap> IsRegularSemigroupElementNC(S, Transformation([4, 4, 4, 4]));
false

# properties: IsRightSimple, non-regular, 1
gap> S := RegularBooleanMatMonoid(3);
<monoid of 3x3 boolean matrices with 4 generators>
gap> IsRegularSemigroup(S);
false
gap> IsRightSimple(S);
false

# properties: IsRightSimple, right zero, 2
gap> S := TrivialSemigroup();
<trivial transformation group of degree 0 with 1 generator>
gap> IsRightZeroSemigroup(S);
true
gap> IsRightSimple(S);
true

# # properties: IsRightSimple, known L-classes, 3
# gap> S := Monoid([Matrix(GF(11), [[0 * Z(11)]]),
# >  Matrix(GF(11), [[Z(11)]]),
# >  Matrix(GF(11), [[Z(11) ^ 4]]),
# >  Matrix(GF(11), [[Z(11) ^ 5]]),
# >  Matrix(GF(11), [[Z(11) ^ 8]]),
# >  Matrix(GF(11), [[Z(11) ^ 9]])]);
# <monoid of 1x1 prime field matrices with 6 generators>
# gap> NrRClasses(S);
# 2
# gap> IsRightSimple(S);
# false

# properties: IsRightSimple, acting, 4
gap> S := JonesMonoid(3);
<regular bipartition *-monoid of degree 3 with 2 generators>
gap> IsRightSimple(S);
false

# properties: IsRightSimple, non-acting, 5
gap> S := RegularBooleanMatMonoid(3);
<monoid of 3x3 boolean matrices with 4 generators>
gap> IsRightSimple(S);
false

# properties: IsRightSimple, infinite, 6
gap> IsRightSimple(FreeSemigroup(2));
Error, no method found! For debugging hints type ?Recovery from NoMethodFound
Error, no 3rd choice method found for `IsRightSimple' on 1 arguments

# properties: IsRightZeroSemigroup, 1
gap> S := RightZeroSemigroup(4);;
gap> IsRightZeroSemigroup(S);
true
gap> I := SemigroupIdeal(S, S.1);;
gap> IsRightZeroSemigroup(I);
true

# properties: IsRightZeroSemigroup, 2
gap> S := AsSemigroup(IsTransformationSemigroup,
> RectangularBand(IsReesMatrixSemigroup, 2, 2));
<transformation semigroup of size 4, degree 5 with 2 generators>
gap> IsRightZeroSemigroup(S);
false

# properties: IsRightZeroSemigroup, 3
gap> IsRightZeroSemigroup(FreeSemigroup(10));
Error, no method found! For debugging hints type ?Recovery from NoMethodFound
Error, no 3rd choice method found for `IsRightZeroSemigroup' on 1 arguments

# properties: IsRightZeroSemigroup, 4
gap> S := RightZeroSemigroup(IsTransformationSemigroup, 4);;
gap> S := Semigroup(S, rec(acting := true));;
gap> IsRightZeroSemigroup(S);
true
gap> I := SemigroupIdeal(S, S.1);;
gap> GeneratorsOfSemigroup(I);;
gap> IsRightZeroSemigroup(I);
true

# properties: IsSemilattice, 1/?
gap> T := Monoid([Transformation([6, 2, 3, 4, 6, 6]),
>   Transformation([1, 6, 6, 4, 5, 6]),
>   Transformation([1, 2, 6, 4, 6, 6]),
>   Transformation([6, 6, 3, 4, 5, 6]),
>   Transformation([1, 6, 6, 6, 5, 6]),
>   Transformation([1, 2, 6, 6, 6, 6]),
>   Transformation([6, 2, 3, 6, 6, 6]),
>   Transformation([6, 6, 3, 6, 5, 6])]);
<transformation monoid of degree 6 with 8 generators>
gap> IsSemilattice(T);
true
gap> I := SemigroupIdeal(T, T.1);
<commutative inverse transformation semigroup ideal of degree 6 with
  1 generator>
gap> IsSemilattice(I);
true
gap> T := Semigroup(T);
<transformation monoid of degree 6 with 8 generators>
gap> IsInverseSemigroup(T);
true
gap> IsSemilattice(T);
true
gap> I := SemigroupIdeal(T, T.1);
<inverse transformation semigroup ideal of degree 6 with 1 generator>
gap> IsSemilattice(I);
true
gap> T := Semigroup(T);;
gap> IsInverseSemigroup(T);;
gap> I := SemigroupIdeal(T, T.1);
<inverse transformation semigroup ideal of degree 6 with 1 generator>
gap> IsSemilattice(I);
true
gap> T := Semigroup(T);;
gap> IsInverseSemigroup(T);;
gap> IsSemilattice(T);
true
gap> I := SemigroupIdeal(T, T.1);;
gap> GeneratorsOfSemigroup(I);;
gap> IsSemilattice(I);
true
gap> T := Semigroup(T);;
gap> IsSemilattice(T);
true
gap> I := SemigroupIdeal(T, T.1);;
gap> IsSemilattice(I);
true
gap> IsSemilattice(FreeInverseSemigroup(1));
Error, no method found! For debugging hints type ?Recovery from NoMethodFound
Error, no 3rd choice method found for `IsCommutativeSemigroup' on 1 arguments

# properties: IsSimpleSemigroup, 1/?
gap> S := AsSemigroup(IsTransformationSemigroup, RegularBooleanMatMonoid(3));
<transformation monoid of degree 8 with 4 generators>
gap> IsRegularSemigroup(S);
false
gap> IsSimpleSemigroup(S);
false

# properties: IsSimpleSemigroup, 2/?
gap> S := AsSemigroup(IsTransformationSemigroup, RegularBooleanMatMonoid(3));
<transformation monoid of degree 8 with 4 generators>
gap> IsCompletelyRegularSemigroup(S);
false
gap> IsSimpleSemigroup(S);
false

# properties: IsSimpleSemigroup, 3/?
gap> S := AsSemigroup(IsTransformationSemigroup, RegularBooleanMatMonoid(3));
<transformation monoid of degree 8 with 4 generators>
gap> NrDClasses(S);
10
gap> IsSimpleSemigroup(S);
false

# properties: IsSimpleSemigroup, 3/?
gap> S := Semigroup([Transformation([4, 1, 6, 6, 6, 6]),
>  Transformation([5, 4, 2, 6, 3, 6]),
>  Transformation([2, 6, 6, 1, 6, 6]),
>  Transformation([6, 3, 5, 2, 1, 6])]);
<transformation semigroup of degree 6 with 4 generators>
gap> I := SemigroupIdeal(S, S.1);;
gap> IsSimpleSemigroup(I);
false

# Test IsSimpleSemigroup (for a semigroup that magically knows it is not
# regular)
gap> S := AsSemigroup(IsTransformationSemigroup, FullBooleanMatMonoid(3));;
gap> HasIsRegularSemigroup(S);
false
gap> SetIsRegularSemigroup(S, false);
gap> IsSimpleSemigroup(S);
false

# properties: IsTrivial, 1
gap> S := TrivialSemigroup();
<trivial transformation group of degree 0 with 1 generator>
gap> Size(S);
1
gap> IsTrivial(S);
true

# properties: IsTrivial, 2
gap> S := FreeSemigroup(1);;
gap> x := GeneratorsOfSemigroup(S);;
gap> S := S / [[x[1] * x[1], x[1]]];
<fp semigroup on the generators [ s1 ]>
gap> IsTrivial(S);
true

# properties: IsTrivial, 3
gap> S := FreeSemigroup(1);;
gap> x := GeneratorsOfSemigroup(S);;
gap> S := S / [[x[1], x[1]]];
<fp semigroup on the generators [ s1 ]>
gap> IsTrivial(S);
false

# properties: IsUnitRegularMonoid, 1/7
gap> IsUnitRegularMonoid(FullTransformationMonoid(3));
true

# properties: IsUnitRegularMonoid, 2/7
gap> IsUnitRegularMonoid(SingularTransformationSemigroup(3));
false

# properties: IsUnitRegularMonoid, error, 3/7
gap> IsUnitRegularMonoid(FreeInverseSemigroup(3));
Error, no method found! For debugging hints type ?Recovery from NoMethodFound
Error, no 3rd choice method found for `IsUnitRegularMonoid' on 1 arguments

# properties: IsUnitRegularMonoid, 4/7
gap> IsUnitRegularMonoid(Semigroup(SingularTransformationSemigroup(3),
> IdentityTransformation));
false

# properties: IsUnitRegularMonoid, 5/7
gap> S := AsSemigroup(IsTransformationSemigroup, RegularBooleanMatMonoid(3));
<transformation monoid of degree 8 with 4 generators>
gap> IsUnitRegularMonoid(S);
false

# properties: IsUnitRegularMonoid, 6/7
gap> IsUnitRegularMonoid(PartitionMonoid(3));
false

# properties: IsUnitRegularMonoid, 7/7
gap> S := Semigroup([Transformation([1, 2, 3, 3]),
>  Transformation([2, 3, 1, 1]), Transformation([2, 1, 3, 3]),
>  Transformation([4, 2, 3, 3]), Transformation([3, 4, 1, 1]),
>  Transformation([4, 1, 2, 2]), Transformation([2, 3, 3, 1]),
>  Transformation([1, 2, 3, 1]), Transformation([3, 3, 1, 2]),
>  Transformation([3, 2, 3, 1]), Transformation([2, 1, 3, 1]),
>  Transformation([2, 3, 1])]);;
gap> IsRegularSemigroup(S);
true
gap> IsUnitRegularMonoid(S);
false

# Test IsUnitRegularMonoid (for a non-regular non-acting semigroup)
gap> IsUnitRegularMonoid(FullBooleanMatMonoid(3));
false

# Test IsUnitRegularMonoid (for a non-acting semigroup with no group of units)
gap> IsUnitRegularMonoid(LeftZeroSemigroup(4));
false
gap> IsUnitRegularMonoid(LeftZeroSemigroup(1));
true
gap> IsUnitRegularMonoid(InverseMonoid(PartialPerm([1], [1]),
>                                      PartialPerm([], [])));
true
gap> IsUnitRegularMonoid(InverseMonoid(PartialPerm([2, 1]),
>                                      PartialPerm([], [])));
true
gap> IsUnitRegularMonoid(InverseMonoid(PartialPerm([1], [1]),
>                                      PartialPerm([], []), rec(acting :=
>                                      false)));
true
gap> IsUnitRegularMonoid(InverseMonoid(PartialPerm([2, 1]),
>                                      PartialPerm([], []), rec(acting :=
>                                      false)));
true

# properties: IsZeroGroup, 1
gap> IsZeroGroup(JonesMonoid(3));
false

# properties: IsZeroGroup, 2
gap> IsZeroGroup(ZeroSemigroup(2));
false

# properties: IsZeroGroup, 3
gap> IsZeroGroup(SymmetricInverseMonoid(3));
false

# properties: IsZeroGroup, 4
gap> S := Semigroup(PartialPerm([1]), PartialPerm([]));
<partial perm monoid of rank 1 with 2 generators>
gap> IsZeroGroup(S);
true
gap> I := SemigroupIdeal(S, PartialPerm([]));;
gap> IsZeroGroup(I);
false

# properties: IsZeroGroup, 5
gap> IsZeroGroup(FreeSemigroup(2));
Error, no method found! For debugging hints type ?Recovery from NoMethodFound
Error, no 3rd choice method found for `IsZeroGroup' on 1 arguments

# properties: IsZeroRectangularBand, 1
gap> S := ReesZeroMatrixSemigroup(Group([()]), [[(), ()], [(), ()]]);
<Rees 0-matrix semigroup 2x2 over Group(())>
gap> IsZeroRectangularBand(S);
true
gap> I := SemigroupIdeal(S, MultiplicativeZero(S));;
gap> IsZeroRectangularBand(I);
false

# properties: IsZeroRectangularBand, 2
gap> S := ReesZeroMatrixSemigroup(Group([(1, 2)]), [[(), ()], [(), ()]]);
<Rees 0-matrix semigroup 2x2 over Group([ (1,2) ])>
gap> IsZeroRectangularBand(S);
false

# properties: IsZeroRectangularBand, 3
gap> IsZeroRectangularBand(FullTransformationMonoid(2));
false

# properties: IsZeroRectangularBand, 4
gap> S := ReesZeroMatrixSemigroup(Group([()]), [[(), ()], [(), ()]]);
<Rees 0-matrix semigroup 2x2 over Group(())>

# properties: IsZeroRectangularBand, 5
gap> IsZeroRectangularBand(FreeSemigroup(20));
Error, no method found! For debugging hints type ?Recovery from NoMethodFound
Error, no 3rd choice method found for `IsZeroRectangularBand' on 1 arguments

# properties: IsZeroSemigroup, 1
gap> S := Semigroup(ZeroSemigroup(IsPartialPermSemigroup, 3));
<partial perm semigroup of rank 2 with 2 generators>
gap> IsZeroSemigroup(S);
true
gap> T := SemigroupIdeal(S, S.1);;
gap> IsZeroSemigroup(T);
true

# properties: IsZeroSemigroup, 2
gap> S := Semigroup(BrauerMonoid(3));
<bipartition monoid of degree 3 with 3 generators>
gap> IsZeroSemigroup(S);
false

# properties: IsZeroSemigroup, 3
gap> S := Semigroup(DualSymmetricInverseMonoid(3));
<block bijection monoid of degree 3 with 3 generators>
gap> IsZeroSemigroup(S);
false

# properties: IsZeroSemigroup, 3
gap> IsZeroSemigroup(FreeSemigroup(3));
Error, no method found! For debugging hints type ?Recovery from NoMethodFound
Error, no 3rd choice method found for `IsZeroSemigroup' on 1 arguments

# properties: IsNilpotentSemigroup, 1
gap> S := ReesZeroMatrixSemigroup(Group(()), [[()]]);
<Rees 0-matrix semigroup 1x1 over Group(())>
gap> IsNilpotentSemigroup(S);
false

# properties: IsNilpotentSemigroup, 2
gap> S := ReesMatrixSemigroup(Group(()), [[()]]);
<Rees matrix semigroup 1x1 over Group(())>
gap> IsNilpotentSemigroup(S);
true

# properties: IsNilpotentSemigroup, 3
gap> S := ReesZeroMatrixSemigroup(Group(()), [[0]]);
<Rees 0-matrix semigroup 1x1 over Group(())>
gap> IsNilpotentSemigroup(S);
true

# properties: IsNilpotentSemigroup, 4
gap> S := Semigroup(Transformation([1, 1, 2, 3, 4]));
<commutative transformation semigroup of degree 5 with 1 generator>
gap> IsNilpotentSemigroup(S);
true

# properties: IsNilpotentSemigroup, 5
gap> S := Semigroup([
>  PartialPerm([1, 2, 3, 4], [1, 2, 5, 3]),
>  PartialPerm([1, 2, 3, 5], [4, 1, 3, 5])]);
<partial perm semigroup of rank 5 with 2 generators>
gap> IsNilpotentSemigroup(S);
false

# properties: IsNilpotentSemigroup, 6
gap> S := Semigroup([
>  PartialPerm([1, 2, 3, 4], [1, 2, 5, 3]),
>  PartialPerm([1, 2, 3, 5], [4, 1, 3, 5])]);
<partial perm semigroup of rank 5 with 2 generators>
gap> NrIdempotents(S);
3
gap> IsNilpotentSemigroup(S);
false

# properties: IsNilpotentSemigroup, 7
gap> S := Semigroup([
>  PartialPerm([2], [1]), PartialPerm([1, 2], [3, 1]),
>  PartialPerm([1, 2], [4, 1]), PartialPerm([1, 2], [5, 1]),
>  PartialPerm([3], [5]), PartialPerm([2, 3], [3, 5]),
>  PartialPerm([1, 3], [3, 5]), PartialPerm([1, 2, 3], [3, 1, 5]),
>  PartialPerm([1, 2, 3], [3, 4, 5]), PartialPerm([3, 4], [5, 3]),
>  PartialPerm([2, 4], [4, 5]), PartialPerm([2, 3, 4], [4, 5, 3]),
>  PartialPerm([1, 2, 4], [3, 1, 5]), PartialPerm([1, 2, 4], [4, 1, 5]),
>  PartialPerm([1, 2, 3, 4], [4, 1, 5, 3])]);
<partial perm semigroup of rank 4 with 15 generators>
gap> IsNilpotentSemigroup(S);
true

# properties: IsNilpotentSemigroup, 8
gap> S := FreeSemigroup(1);;
gap> IsNilpotentSemigroup(S);
Error, no method found! For debugging hints type ?Recovery from NoMethodFound
Error, no 3rd choice method found for `IsNilpotentSemigroup' on 1 arguments
gap> S := Semigroup(Transformation([2, 1]));;
gap> IsNilpotentSemigroup(S);
false

# properties: IsRectangularGroup, 1
gap> R := RectangularBand(10, 10);;
gap> G := AsSemigroup(IsTransformationSemigroup, SymmetricGroup(5));;
gap> S := DirectProduct(R, G);;
gap> IsRectangularGroup(S);
true
gap> S := DirectProduct(G, R);;
gap> IsRectangularGroup(S);
true
gap> IsRectangularGroup(PartitionMonoid(3));
false

# PropertiesTest58: IsSemigroupWithAdjoinedZero
gap> S := SymmetricInverseMonoid(10);;
gap> IsSemigroupWithAdjoinedZero(S);
false
gap> S := FullTransformationMonoid(12);;
gap> IsSemigroupWithAdjoinedZero(S);
false
gap> S := ReesMatrixSemigroup(SymmetricGroup(4), [[(1, 3, 2), (4, 2)]]);
<Rees matrix semigroup 2x1 over Sym( [ 1 .. 4 ] )>
gap> IsSemigroupWithAdjoinedZero(S);
false
gap> S := ReesZeroMatrixSemigroup(SymmetricGroup(4), [[(1, 3, 2), (4, 2)]]);
<Rees 0-matrix semigroup 2x1 over Sym( [ 1 .. 4 ] )>
gap> IsSemigroupWithAdjoinedZero(S);
true

# properties: IsSemigroupWithCommutingIdempotents, 1
gap> S := SymmetricInverseMonoid(3);;
gap> IsSemigroupWithCommutingIdempotents(S);
true
gap> S := FullTransformationMonoid(4);;
gap> IsSemigroupWithCommutingIdempotents(S);
false

# Example of a block group whose idempotents do not commute
gap> S := Semigroup([Transformation([2, 2]), Transformation([1, 3, 3])]);;
gap> IsSemigroupWithCommutingIdempotents(S);
false
gap> IsBlockGroup(S);
true

#
gap> S := MonogenicSemigroup(5, 8);;
gap> IsSemigroupWithCommutingIdempotents(S);
true
gap> S := Semigroup([
> Transformation([6, 9, 9, 10, 13, 1, 9, 9, 9, 4, 9, 9, 5, 9, 9, 9, 9, 9,
>  9, 1]),
> Transformation([7, 9, 9, 11, 14, 2, 9, 9, 9, 16, 9, 9, 18, 9, 9, 9, 9, 9,
>  9, 2]),
> Transformation([8, 9, 9, 12, 15, 3, 9, 9, 9, 17, 9, 9, 19, 9, 9, 9, 9, 9,
>  9, 3]),
> Transformation([9, 6, 9, 9, 9, 9, 1, 9, 9, 9, 4, 9, 9, 5, 9, 10, 9, 13, 9,
>  4]),
> Transformation([9, 9, 6, 9, 9, 9, 9, 1, 9, 9, 9, 4, 9, 9, 5, 9, 10, 9, 13,
>  5])]);;
gap> IsSemigroupWithCommutingIdempotents(S);
true

# properties: IsSemigroupWithCommutingIdempotents, 2
gap> S := FullTransformationMonoid(3);;
gap> IdempotentGeneratedSubsemigroup(S);;
gap> IsSemigroupWithCommutingIdempotents(S);
false
gap> S := Semigroup([
> Transformation([6, 9, 9, 10, 13, 1, 9, 9, 9, 4, 9, 9, 5, 9, 9, 9, 9, 9,
>  9, 1]),
> Transformation([7, 9, 9, 11, 14, 2, 9, 9, 9, 16, 9, 9, 18, 9, 9, 9, 9, 9,
>  9, 2]),
> Transformation([8, 9, 9, 12, 15, 3, 9, 9, 9, 17, 9, 9, 19, 9, 9, 9, 9, 9,
>  9, 3]),
> Transformation([9, 6, 9, 9, 9, 9, 1, 9, 9, 9, 4, 9, 9, 5, 9, 10, 9, 13, 9,
>  4]),
> Transformation([9, 9, 6, 9, 9, 9, 9, 1, 9, 9, 9, 4, 9, 9, 5, 9, 10, 9, 13,
>  5])]);;
gap> IdempotentGeneratedSubsemigroup(S);;
gap> IsSemigroupWithCommutingIdempotents(S);
true

# properties: true methods for IsMonogenicSemigroup and IsRegularSemigroup
gap> S := Semigroup(Matrix(IsIntegerMatrix,
>                   [[1, 0, 0], [0, 1, 0], [0, 0, 0]]));
<commutative semigroup of 3x3 integer matrices with 1 generator>
gap> IsMonogenicSemigroup(S);
true
gap> HasIsFinite(S) or HasIsGroupAsSemigroup(S);
false
gap> IsRegularSemigroup(S);
true
gap> HasIsFinite(S);
true
gap> HasIsGroupAsSemigroup(S);
true
gap> IsFinite(S) and IsGroupAsSemigroup(S);
true

# properties: IsSurjectiveSemigroup, for an fp semigroup, 1
gap> F := FreeSemigroup(1);
<free semigroup on the generators [ s1 ]>
gap> S := F / [];;
gap> IsSurjectiveSemigroup(S);
false
gap> S := F / [[F.1, F.1]];
<fp semigroup on the generators [ s1 ]>
gap> IsSurjectiveSemigroup(S);
false
gap> S := F / [[F.1 ^ 3, F.1]];
<fp semigroup on the generators [ s1 ]>
gap> IsSurjectiveSemigroup(S);
true
gap> S := F / [[F.1 ^ 3, F.1 ^ 2]];
<fp semigroup on the generators [ s1 ]>
gap> IsSurjectiveSemigroup(S);
false
gap> F := FreeSemigroup(3);
<free semigroup on the generators [ s1, s2, s3 ]>
gap> S := F / [[F.2, F.1], [F.2 ^ 3, F.2], [F.2, F.3]];
<fp semigroup on the generators [ s1, s2, s3 ]>
gap> IsSurjectiveSemigroup(S);
true

# properties: IsSurjectiveSemigroup, for a transformation semigroup, 1
gap> S := MonogenicSemigroup(6, 2);;
gap> IsSurjectiveSemigroup(S);
false
gap> S := FullTransformationMonoid(3);;
gap> IsSurjectiveSemigroup(S);
true

#properties: IsCrytoGroup, for a semilattice of groups
gap> G1 := AlternatingGroup(4);;
gap> G2 := SymmetricGroup(3);;
gap> G3 := AlternatingGroup(5);;
gap> gr := Digraph([[1, 3], [2, 3], [3]]);;
gap> sgn := function(x)
> if SignPerm(x) = 1 then
> return ();
> fi;
> return (1, 2);
> end;;
gap> hom13 := GroupHomomorphismByFunction(G1, G3, sgn);;
gap> hom23 := GroupHomomorphismByFunction(G2, G3, sgn);;
gap> S := AsSemigroup(IsPartialPermSemigroup,
> gr,
> [G1, G2, G3], [[1, 3, hom13], [2, 3, hom23]]);;
gap> IsCryptoGroup(S);
true

#IsCryptoGroup, for a Rees Matrix semigroup
gap> G:=SymmetricGroup(5);;
gap> M:=[[(1,2),(2,4)],[(1,4),(1,2,3,4,5)]];;
gap> R:=ReesMatrixSemigroup(G,M);;
gap> IsCryptoGroup(R);
true

# SEMIGROUPS_UnbindVariables
gap> Unbind(D);
gap> Unbind(I);
gap> Unbind(G);
gap> Unbind(J);
gap> Unbind(M);
gap> Unbind(R);
gap> Unbind(S);
gap> Unbind(T);
gap> Unbind(gens);
gap> Unbind(x);
gap> Unbind(G1);
gap> Unbind(G2);
gap> Unbind(G3);
gap> Unbind(gr);
gap> Unbind(sgn);
gap> Unbind(hom13);
gap> Unbind(hom23);

#
gap> SEMIGROUPS.StopTest();
gap> STOP_TEST("Semigroups package: standard/properties.tst");
