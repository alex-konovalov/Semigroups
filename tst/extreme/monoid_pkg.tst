#############################################################################
##
#W  extreme/monoid_pkg.tst
#Y  Copyright (C) 2011-15                                James D. Mitchell
##
##  Licensing information can be found in the README file of this package.
#
#############################################################################
##
## a concatenation of relevant tests from the monoid/tst.

#@local BigMonoids, C, D, H, I, M, S, SmallMonoids, T, a, acting, b, c, c3, c4
#@local cs1, cs2, cs3, cs4, cs5, d, dc, dr, f, g, g1, g2, g3, g4, g5, g6, g7
#@local g8, g9, gens, gr, h, i, idem, iso, m, m1, m10, m11, m12, m13, m14, m15
#@local m16, m17, m18, m19, m2, m20, m21, m22, m23, m3, m4, m5, m6, m7, m8, m9
#@local mat, o, r, r2, rc, res, rms, s, semis, sizes, t, x
gap> START_TEST("Semigroups package: extreme/monoid_pkg.tst");
gap> LoadPackage("semigroups", false);;

#
gap> SEMIGROUPS.StartTest();
gap> SEMIGROUPS.DefaultOptionsRec.acting := true;;

# MonoidPkgTest2
gap> g := CyclicGroup(3);;
gap> r := GF(2);;
gap> gr := GroupRing(r, g);;
gap> iso := IsomorphismTransformationSemigroup(gr);;
gap> s := Range(iso);;
gap> Size(s);
8
gap> SmallGeneratingSet(s);;
gap> s := Semigroup(IrredundantGeneratingSubset(last));;
gap> NrDClasses(s);
4
gap> sizes := List(GreensDClasses(s), Size);;
gap> Sort(sizes);;
gap> sizes;
[ 1, 1, 3, 3 ]
gap> PartialOrderOfDClasses(s);
<immutable digraph with 4 vertices, 4 edges>
gap> IsRegularSemigroup(s);
true
gap> ForAll(s, x -> x in s);
true
gap> MultiplicativeNeutralElement(s);
IdentityTransformation
gap> h := List(s, x -> InversesOfSemigroupElement(s, x));;
gap> Sort(h);
gap> h;
[ [ Transformation( [ 1, 1, 1, 1, 1, 1, 1, 1 ] ) ],
  [ IdentityTransformation ], [ Transformation( [ 1, 3, 5, 1, 7, 7, 3, 5 ] ) ]
    , [ Transformation( [ 1, 4, 1, 4, 1, 4, 1, 4 ] ) ],
  [ Transformation( [ 1, 5, 7, 1, 3, 3, 5, 7 ] ) ],
  [ Transformation( [ 1, 6, 7, 4, 3, 8, 5, 2 ] ) ],
  [ Transformation( [ 1, 7, 3, 1, 5, 5, 7, 3 ] ) ],
  [ Transformation( [ 1, 8, 5, 4, 7, 2, 3, 6 ] ) ] ]
gap> IsMonoidAsSemigroup(s);
true
gap> IsGroupAsSemigroup(s);
false
gap> i := MinimalIdeal(s);
<simple transformation semigroup ideal of degree 8 with 1 generator>
gap> Size(i);
1
gap> MultiplicativeZero(s);
Transformation( [ 1, 1, 1, 1, 1, 1, 1, 1 ] )
gap> MultiplicativeZero(s) in i;
true
gap> h := List(GreensDClasses(s), GroupHClass);;
gap> h := Set(h, StructureDescription);
[ "1", "1", "C3", "C3" ]
gap> IsCliffordSemigroup(s);
true

# MonoidPkgTest3
gap> a := Idempotent([3, 5, 6, 7, 8], [1, 2, 1, 1, 2, 3, 4, 5]) * (3, 5);;
gap> b := a * (3, 5) * (3, 6, 7, 8);;
gap> s := Semigroup(a, b);;
gap> IsGroupAsSemigroup(s);
true

# MonoidPkgTest4
gap> gens := [Transformation([3, 5, 3, 3, 5, 6]),
> Transformation([6, 2, 4, 2, 2, 6])];;
gap> S := Semigroup(gens);;
gap> H := GroupHClass(GreensDClassOfElement(S, Elements(S)[1]));
<Green's H-class: Transformation( [ 6, 2, 2, 2, 2, 6 ] )>
gap> Transformation([6, 2, 2, 2, 2, 6]) in H;
true
gap> IsomorphismPermGroup(H);
MappingByFunction( <Green's H-class: Transformation( [ 6, 2, 2, 2, 2, 6 ] )>
 , Group(()), function( x ) ... end, function( x ) ... end )

# MonoidPkgTest5
gap> gens := [Transformation([4, 4, 8, 8, 8, 8, 4, 8]),
>   Transformation([8, 2, 8, 2, 5, 5, 8, 8]),
>   Transformation([8, 8, 3, 7, 8, 3, 7, 8]),
>   Transformation([8, 6, 6, 8, 6, 8, 8, 8])];;
gap> S := Semigroup(gens);;
gap> Size(S);
30
gap> NrDClasses(S);
6
gap> List(GreensDClasses(S), Size);
[ 9, 1, 1, 9, 1, 9 ]
gap> IsRegularSemigroup(S);
false
gap> NrRClasses(S);
12
gap> NrLClasses(S);
12
gap> IsBlockGroup(S);
false
gap> NrIdempotents(S);
15
gap> List(GreensDClasses(S), IsRegularDClass);
[ true, true, true, true, true, false ]
gap> d := GreensDClasses(S)[2];;
gap> GreensRClasses(d);;
gap> GreensLClasses(d);;
gap> SchutzenbergerGroup(d);
Group(())
gap> h := List(GreensDClasses(S), function(d) if IsRegularDClass(d)
> then return GroupHClass(d); else return fail; fi; end);;
gap> MultiplicativeNeutralElement(S);
fail
gap> IsMonoidAsSemigroup(S);
false
gap> GroupOfUnits(S);
fail
gap> MultiplicativeZero(S);
Transformation( [ 8, 8, 8, 8, 8, 8, 8, 8 ] )
gap> h := Filtered(h, x -> not x = fail);
[ <Green's H-class: Transformation( [ 2, 2, 8, 8, 8, 8, 2, 8 ] )>,
  <Green's H-class: Transformation( [ 8, 2, 8, 2, 5, 5, 8, 8 ] )>,
  <Green's H-class: Transformation( [ 8, 8, 3, 7, 8, 3, 7, 8 ] )>,
  <Green's H-class: Transformation( [ 8, 5, 5, 8, 5, 8, 8, 8 ] )>,
  <Green's H-class: Transformation( [ 8, 8, 8, 8, 8, 8, 8, 8 ] )> ]
gap> List(h, StructureDescription);
[ "1", "1", "1", "1", "1" ]
gap> IsHTrivial(S);
true
gap> IsLTrivial(S);
false
gap> IsRTrivial(S);
false
gap> NrIdempotents(S);
15
gap> IsIdempotentGenerated(S);
true
gap> IsSemiband(S);
true
gap> IsCommutative(S);
false
gap> IsBand(S);
false

# MonoidPkgTest6: from greens.tst
gap> gens := [Transformation([4, 5, 7, 1, 8, 6, 1, 7]),
>  Transformation([5, 5, 3, 8, 3, 7, 4, 6]),
>  Transformation([5, 7, 4, 4, 1, 4, 4, 4]),
>  Transformation([7, 1, 4, 3, 6, 1, 3, 7])];;
gap> m := Semigroup(gens);;
gap> o := LambdaOrb(m);; Enumerate(o);;
gap> AsSet(o);
[ [ 0 ], [ 1 ], [ 1, 3 ], [ 1, 3, 4 ], [ 1, 3, 4, 6, 7 ], [ 1, 3, 4, 7 ],
  [ 1, 3, 6 ], [ 1, 3, 6, 7 ], [ 1, 3, 7 ], [ 1, 4 ], [ 1, 4, 5 ],
  [ 1, 4, 5, 6, 7, 8 ], [ 1, 4, 5, 7 ], [ 1, 4, 6 ], [ 1, 4, 6, 7 ],
  [ 1, 4, 6, 7, 8 ], [ 1, 4, 7 ], [ 1, 4, 8 ], [ 1, 6 ], [ 1, 6, 7 ],
  [ 1, 6, 7, 8 ], [ 1, 6, 8 ], [ 1, 7 ], [ 1, 7, 8 ], [ 1, 8 ], [ 3 ],
  [ 3, 4 ], [ 3, 4, 5 ], [ 3, 4, 5, 6, 7, 8 ], [ 3, 4, 5, 7 ],
  [ 3, 4, 5, 7, 8 ], [ 3, 4, 5, 8 ], [ 3, 4, 6 ], [ 3, 4, 6, 7 ],
  [ 3, 4, 6, 7, 8 ], [ 3, 4, 6, 8 ], [ 3, 4, 7 ], [ 3, 4, 7, 8 ],
  [ 3, 4, 8 ], [ 3, 5 ], [ 3, 5, 7 ], [ 3, 5, 8 ], [ 3, 6 ], [ 3, 6, 7 ],
  [ 3, 6, 7, 8 ], [ 3, 6, 8 ], [ 3, 7 ], [ 3, 7, 8 ], [ 3, 8 ], [ 4 ],
  [ 4, 5 ], [ 4, 5, 6 ], [ 4, 5, 6, 7 ], [ 4, 5, 6, 7, 8 ], [ 4, 5, 7 ],
  [ 4, 5, 7, 8 ], [ 4, 5, 8 ], [ 4, 6 ], [ 4, 6, 7 ], [ 4, 6, 8 ], [ 4, 7 ],
  [ 4, 7, 8 ], [ 4, 8 ], [ 5 ], [ 5, 6 ], [ 5, 6, 7 ], [ 5, 6, 8 ], [ 5, 7 ],
  [ 5, 7, 8 ], [ 5, 8 ], [ 6 ], [ 6, 7 ], [ 6, 7, 8 ], [ 6, 8 ], [ 7 ],
  [ 7, 8 ], [ 8 ] ]
gap> gens := [Transformation([1, 5, 2, 2, 3, 5, 2]),
>  Transformation([7, 3, 6, 5, 2, 4, 1]),
>  Transformation([7, 5, 3, 2, 5, 5, 6])];;
gap> m := Monoid(gens);;
gap> o := LambdaOrb(m);; Enumerate(o);; AsSet(o);
[ [ 0 ], [ 1, 2 ], [ 1, 2, 3 ], [ 1, 2, 3, 4, 5 ], [ 1, 2, 3, 4, 5, 6, 7 ],
  [ 1, 2, 3, 4, 6 ], [ 1, 2, 3, 5 ], [ 1, 2, 3, 5, 6 ], [ 1, 2, 3, 6 ],
  [ 1, 2, 4 ], [ 1, 2, 4, 5 ], [ 1, 2, 4, 5, 6 ], [ 1, 2, 5 ], [ 1, 2, 6 ],
  [ 1, 3 ], [ 1, 3, 4 ], [ 1, 3, 4, 5, 6 ], [ 1, 3, 4, 6 ], [ 1, 3, 5 ],
  [ 1, 3, 6 ], [ 1, 4 ], [ 1, 4, 5 ], [ 1, 4, 5, 6 ], [ 1, 4, 6 ], [ 1, 5 ],
  [ 1, 5, 6 ], [ 1, 6 ], [ 2 ], [ 2, 3 ], [ 2, 3, 4 ], [ 2, 3, 4, 5 ],
  [ 2, 3, 4, 5, 7 ], [ 2, 3, 4, 6 ], [ 2, 3, 4, 6, 7 ], [ 2, 3, 5 ],
  [ 2, 3, 5, 6 ], [ 2, 3, 5, 6, 7 ], [ 2, 3, 5, 7 ], [ 2, 3, 6 ],
  [ 2, 3, 6, 7 ], [ 2, 3, 7 ], [ 2, 4 ], [ 2, 4, 5 ], [ 2, 4, 5, 6 ],
  [ 2, 4, 5, 6, 7 ], [ 2, 4, 5, 7 ], [ 2, 4, 6 ], [ 2, 4, 7 ], [ 2, 5 ],
  [ 2, 5, 6 ], [ 2, 5, 7 ], [ 2, 6 ], [ 2, 6, 7 ], [ 2, 7 ], [ 3 ], [ 3, 4 ],
  [ 3, 4, 5 ], [ 3, 4, 5, 6 ], [ 3, 4, 5, 6, 7 ], [ 3, 4, 6 ],
  [ 3, 4, 6, 7 ], [ 3, 4, 7 ], [ 3, 5 ], [ 3, 5, 6 ], [ 3, 5, 7 ], [ 3, 6 ],
  [ 3, 6, 7 ], [ 3, 7 ], [ 4 ], [ 4, 5 ], [ 4, 5, 6 ], [ 4, 5, 6, 7 ],
  [ 4, 5, 7 ], [ 4, 6 ], [ 4, 6, 7 ], [ 4, 7 ], [ 5 ], [ 5, 6 ], [ 5, 6, 7 ],
  [ 5, 7 ], [ 6 ], [ 6, 7 ] ]
gap> Length(Enumerate(RhoOrb(m)));
207
gap> gens := [[Transformation([3, 4, 4, 3, 1, 1, 5])],
> [Transformation([1, 1, 4, 3]), Transformation([2, 2, 2, 2]),
> Transformation([3, 3, 1, 4])], [Transformation([4, 4, 2, 3, 3]),
> Transformation([5, 2, 4, 3, 1])],
> [Transformation([1, 5, 4, 1, 5]), Transformation([2, 4, 1, 3, 1])],
> [Transformation([4, 1, 2, 3]), Transformation([4, 3, 4, 1])],
> [Transformation([2, 1, 3, 1, 4, 3]),
>   Transformation([2, 2, 2, 2, 1, 2]),
>   Transformation([5, 3, 4, 3, 5, 6]),
>   Transformation([6, 4, 1, 4, 5, 3]),
> Transformation([6, 5, 2, 6, 3, 4])],
> [Transformation([3, 5, 5, 1, 4, 7, 5])],
> [Transformation([2, 5, 6, 1, 1, 3]),
> Transformation([3, 1, 6, 2, 5, 2]),
> Transformation([5, 4, 2, 3, 3, 5]),
> Transformation([6, 6, 5, 5, 2, 2])],
> [Transformation([1, 5, 3, 2, 3]), Transformation([4, 3, 2, 5, 2]),
>   Transformation([5, 4, 1, 2, 2]), Transformation([5, 5, 5, 1, 1])],
> [Transformation([2, 4, 4, 7, 2, 1, 2])],
> [Transformation([3, 4, 2, 4, 6, 7, 4]),
>   Transformation([4, 6, 3, 2, 4, 5, 4]),
>   Transformation([6, 2, 3, 5, 5, 2, 2]),
>   Transformation([6, 5, 4, 5, 2, 4, 4]),
>   Transformation([7, 6, 7, 5, 6, 5, 7])],
>  [Transformation([3, 2, 3, 3, 1]),
> Transformation([4, 5, 1, 2, 4])],
>  [Transformation([1, 4, 3, 4]), Transformation([2, 2, 1, 1]),
>    Transformation([3, 1, 3, 4]), Transformation([4, 4, 3, 1])],
> [Transformation([1, 2, 2, 3, 3]), Transformation([4, 3, 4, 3, 2]),
>   Transformation([5, 3, 4, 5, 4])],
> [Transformation([4, 3, 6, 4, 6, 1]),
>   Transformation([4, 4, 4, 6, 3, 1])],
> [Transformation([1, 4, 3, 4]), Transformation([3, 3, 3, 3]),
>   Transformation([3, 4, 1, 4]), Transformation([4, 3, 1, 4])],
> [Transformation([1, 3, 3, 5, 2]), Transformation([3, 4, 5, 1, 1])],
> [Transformation([2, 6, 4, 6, 5, 2]),
>   Transformation([3, 5, 6, 2, 5, 1]),
>   Transformation([5, 1, 3, 3, 3, 1]),
>   Transformation([6, 4, 4, 6, 6, 3])],
> [Transformation([1, 3, 3, 3])],
> [Transformation([4, 1, 2, 2, 3]), Transformation([4, 2, 3, 2, 2])],
> [Transformation([1, 4, 6, 4, 4, 7, 2]),
>   Transformation([1, 6, 5, 1, 7, 2, 7]),
>   Transformation([2, 2, 7, 2, 1, 4, 4]),
>   Transformation([5, 6, 2, 6, 3, 3, 5])],
> [Transformation([1, 1, 3, 1]), Transformation([4, 2, 3, 4]),
>   Transformation([4, 4, 2, 2])], [Transformation([3, 2, 1, 1]),
>   Transformation([4, 1, 3, 2]), Transformation([4, 4, 1, 2])],
> [Transformation([1, 6, 4, 2, 5, 3, 2]),
> Transformation([4, 1, 4, 7, 4, 4, 5])],
>   [Transformation([2, 4, 5, 4, 4])],
>   [Transformation([1, 4, 2, 3]), Transformation([4, 3, 3, 3])],
>   [Transformation([1, 1, 3, 1, 4])],
>   [Transformation([4, 3, 3, 6, 7, 2, 3]),
>   Transformation([6, 6, 4, 4, 2, 1, 4])],
>   [Transformation([2, 2, 4, 6, 4, 3]),
>   Transformation([3, 4, 1, 1, 5, 2]),
>   Transformation([4, 4, 6, 4, 6, 1])],
>   [Transformation([3, 5, 4, 2, 1, 2, 2]),
>   Transformation([7, 7, 1, 5, 7, 1, 6])],
>   [Transformation([3, 4, 1, 4]), Transformation([4, 3, 2, 2]),
>   Transformation([4, 4, 1, 4])],
>   [Transformation([3, 7, 4, 4, 3, 3, 5]),
>   Transformation([4, 6, 1, 1, 6, 4, 1]),
>   Transformation([6, 5, 7, 2, 1, 1, 3])],
>   [Transformation([1, 2, 4, 1]), Transformation([4, 1, 2, 1]),
>   Transformation([4, 2, 2, 4])],
>   [Transformation([2, 1, 2, 2]), Transformation([2, 4, 1, 1]),
>   Transformation([4, 2, 4, 3]), Transformation([4, 4, 1, 2])],
>   [Transformation([1, 1, 1, 1, 1, 4]),
>   Transformation([3, 3, 2, 4, 1, 3]),
>   Transformation([4, 5, 2, 4, 4, 5]),
>   Transformation([5, 3, 2, 6, 6, 4]),
>   Transformation([6, 6, 5, 5, 1, 1])],
>   [Transformation([1, 2, 4, 1]), Transformation([2, 4, 1, 2]),
>   Transformation([3, 3, 1, 4]), Transformation([3, 4, 1, 2]),
>   Transformation([4, 1, 4, 3])],
>   [Transformation([1, 7, 6, 1, 7, 5, 5]),
>   Transformation([2, 7, 1, 4, 7, 6, 2]),
>   Transformation([4, 3, 7, 2, 6, 3, 4]),
>   Transformation([4, 7, 2, 1, 7, 5, 4]),
>   Transformation([5, 7, 5, 5, 5, 3, 5])],
>   [Transformation([2, 4, 4, 3])],
>   [Transformation([4, 6, 5, 1, 4, 4])],
>   [Transformation([2, 3, 4, 5, 3]), Transformation([4, 1, 5, 1, 3]),
>   Transformation([4, 1, 5, 5, 3])],
>   [Transformation([1, 3, 1, 2, 2]), Transformation([2, 3, 5, 2, 4]),
>   Transformation([2, 4, 3, 2, 5]), Transformation([4, 4, 2, 1, 2])],
>   [Transformation([1, 4, 2, 4]), Transformation([2, 2, 1, 4]),
>   Transformation([3, 2, 2, 2])],
>   [Transformation([1, 5, 1, 1, 5]),
> Transformation([4, 3, 1, 3, 2])],
>   [Transformation([1, 3, 4, 4]), Transformation([2, 1, 3, 3]),
> Transformation([4, 1, 3, 4]), Transformation([4, 2, 3, 3])],
>   [Transformation([4, 3, 2, 2, 1, 4, 2]),
>   Transformation([6, 5, 2, 7, 2, 2, 7])],
>   [Transformation([2, 4, 4, 3]), Transformation([3, 4, 1, 3]),
>   Transformation([4, 1, 3, 2]), Transformation([4, 4, 1, 1])],
>   [Transformation([1, 2, 5, 2, 1]), Transformation([3, 2, 2, 4, 2]),
>   Transformation([4, 5, 1, 1, 2]), Transformation([5, 5, 5, 2, 1])],
>   [Transformation([1, 2, 4, 4]), Transformation([2, 1, 2, 1]),
>   Transformation([2, 3, 2, 3]), Transformation([3, 2, 1, 3]),
>   Transformation([3, 4, 3, 2])],
>   [Transformation([1, 1, 1, 2, 2])],
>   [Transformation([4, 4, 3, 3, 3, 2]),
>   Transformation([4, 6, 3, 6, 4, 3]),
>   Transformation([6, 4, 1, 3, 4, 5])],
>   [Transformation([1, 1, 4, 3]), Transformation([3, 1, 3, 2])],
>   [Transformation([1, 3, 5, 3, 3]), Transformation([1, 5, 4, 4, 3]),
>  Transformation([2, 5, 3, 1, 1])],
>   [Transformation([3, 2, 3, 4]), Transformation([3, 4, 3, 1]),
>  Transformation([3, 4, 4, 4]), Transformation([4, 3, 1, 3])],
>   [Transformation([2, 2, 5, 2, 2, 5]),
> Transformation([2, 6, 5, 2, 6, 3]),
> Transformation([4, 2, 4, 5, 5, 6]),
>       Transformation([5, 4, 1, 4, 2, 2])],
> [Transformation([1, 1, 3, 4]), Transformation([3, 1, 2, 2])],
>   [Transformation([1, 1, 4, 5, 5, 3]),
> Transformation([6, 4, 4, 5, 6, 5])],
>  [Transformation([1, 4, 5, 3, 1, 7, 3]),
>  Transformation([1, 6, 6, 5, 2, 4, 2])],
>   [Transformation([3, 3, 1, 2, 3]), Transformation([5, 5, 1, 5, 3]),
>  Transformation([5, 5, 5, 5, 2])],
>   [Transformation([1, 2, 5, 1, 5, 6]),
>   Transformation([5, 4, 5, 5, 3, 2])],
>   [Transformation([1, 2, 1, 3]), Transformation([2, 3, 4, 4]),
>  Transformation([4, 1, 1, 1])],
>  [Transformation([1, 2, 2, 3, 2]), Transformation([4, 3, 2, 4, 1]),
> Transformation([5, 1, 2, 2, 1]), Transformation([5, 2, 4, 1, 4]),
> Transformation([5, 5, 4, 2, 2])],
> [Transformation([2, 1, 2, 3]), Transformation([2, 2, 3, 2])],
> [Transformation([4, 2, 1, 3])],
>   [Transformation([1, 2, 3, 4]), Transformation([2, 2, 3, 4]),
> Transformation([2, 2, 4, 3])],
>   [Transformation([2, 1, 2, 1]), Transformation([3, 4, 2, 4])],
>   [Transformation([3, 4, 1, 2, 2, 2]),
>   Transformation([4, 4, 4, 2, 5, 3]),
>   Transformation([5, 6, 6, 5, 5, 4])],
>   [Transformation([1, 4, 1, 6, 4, 6]),
>   Transformation([2, 4, 2, 5, 5, 6]),
>   Transformation([3, 6, 2, 1, 4, 6]),
>   Transformation([4, 6, 2, 4, 1, 2])],
>   [Transformation([1, 3, 3, 3]), Transformation([2, 1, 3, 1]),
>   Transformation([3, 1, 2, 3])],
>   [Transformation([1, 4, 1, 2]), Transformation([2, 2, 3, 2]),
>   Transformation([3, 3, 4, 3]), Transformation([4, 3, 3, 4]),
>   Transformation([4, 4, 4, 2])],
>   [Transformation([1, 2, 1, 4]), Transformation([4, 1, 1, 2]),
>   Transformation([4, 3, 3, 2])],
>   [Transformation([2, 3, 6, 7, 1, 2, 6])],
>   [Transformation([4, 1, 1, 3, 3, 3])],
>   [Transformation([3, 3, 2, 7, 5, 5, 1]),
>   Transformation([3, 5, 5, 4, 1, 3, 2]),
>   Transformation([4, 1, 3, 6, 6, 6, 5]),
>   Transformation([7, 2, 7, 2, 7, 7, 2])],
>   [Transformation([1, 1, 7, 5, 2, 1, 2]),
>   Transformation([2, 7, 2, 6, 7, 5, 7]),
>   Transformation([4, 5, 7, 4, 3, 1, 4])],
>   [Transformation([3, 6, 4, 4, 2, 5, 1]),
>   Transformation([4, 1, 2, 5, 7, 7, 3]),
>   Transformation([4, 4, 1, 1, 6, 2, 7]),
>   Transformation([5, 7, 6, 6, 1, 4, 5])],
>   [Transformation([1, 1, 1, 2]), Transformation([1, 3, 1, 3]),
>   Transformation([1, 4, 3, 3]), Transformation([3, 1, 1, 1]),
>   Transformation([4, 2, 3, 4])],
>   [Transformation([1, 3, 3, 2, 1, 3]),
>   Transformation([1, 5, 5, 6, 5, 2]),
>   Transformation([6, 3, 1, 1, 5, 5]),
>   Transformation([6, 3, 1, 5, 2, 4])],
>   [Transformation([2, 6, 1, 3, 1, 5]),
>   Transformation([4, 3, 3, 5, 5, 5]),
>   Transformation([4, 5, 6, 4, 4, 2]),
>   Transformation([6, 3, 5, 4, 1, 4])],
>   [Transformation([3, 1, 2, 2, 3]), Transformation([3, 2, 1, 2, 5]),
>       Transformation([3, 3, 4, 2, 4])],
>   [Transformation([1, 7, 1, 6, 6, 5, 3]),
>   Transformation([2, 6, 5, 6, 1, 5, 6]),
>   Transformation([3, 4, 6, 1, 5, 1, 6]),
>   Transformation([7, 5, 7, 2, 5, 7, 4])],
>   [Transformation([2, 1, 2, 2, 4]),
>   Transformation([2, 1, 4, 1, 3]),
>   Transformation([3, 3, 1, 3, 2]),
>   Transformation([5, 4, 5, 4, 5])],
>   [Transformation([2, 1, 4, 3]), Transformation([2, 3, 4, 4]),
>   Transformation([3, 3, 1, 1])],
>   [Transformation([2, 1, 1, 2])],
>   [Transformation([1, 3, 1, 3, 3]), Transformation([2, 1, 1, 4, 1]),
>   Transformation([4, 5, 1, 5, 4]), Transformation([5, 4, 3, 4, 2]),
>   Transformation([5, 5, 5, 3, 4])],
>   [Transformation([5, 5, 5, 5, 5])],
>   [Transformation([3, 2, 1, 2, 6, 6]),
>   Transformation([6, 2, 1, 4, 3, 2])],
>   [Transformation([3, 4, 4, 2, 4, 7, 2]),
>   Transformation([4, 1, 7, 7, 7, 1, 3]),
>   Transformation([5, 5, 5, 4, 4, 3, 4]),
>   Transformation([6, 6, 6, 3, 6, 7, 2]),
>   Transformation([7, 7, 5, 1, 7, 2, 3])],
>   [Transformation([1, 5, 3, 3, 1, 2, 2]),
>   Transformation([3, 4, 1, 6, 3, 4, 5]),
>   Transformation([4, 1, 2, 1, 6, 7, 5]),
>   Transformation([4, 2, 7, 2, 4, 1, 1]),
>   Transformation([7, 7, 7, 1, 5, 4, 4])],
>   [Transformation([1, 3, 2, 6, 5, 5]),
>   Transformation([3, 1, 2, 5, 6, 2]),
>   Transformation([5, 5, 1, 5, 3, 5]),
>   Transformation([6, 6, 1, 5, 6, 2])],
>   [Transformation([1, 4, 3, 3, 4, 3]),
>   Transformation([3, 1, 2, 5, 2, 5]),
>   Transformation([3, 2, 1, 6, 5, 4]),
>   Transformation([5, 2, 1, 1, 3, 1]),
>   Transformation([6, 4, 1, 1, 1, 1])],
>   [Transformation([4, 2, 3, 3, 4])],
>   [Transformation([1, 4, 4, 4, 3, 1, 5]),
>   Transformation([4, 7, 3, 6, 1, 7, 6])],
>   [Transformation([4, 3, 5, 7, 7, 1, 6])],
>   [Transformation([2, 2, 4, 1])],
>   [Transformation([1, 1, 2, 6, 4, 6]),
>   Transformation([4, 2, 3, 1, 2, 2]),
>   Transformation([4, 2, 4, 3, 6, 5])],
>   [Transformation([2, 3, 6, 4, 7, 4, 6]),
>   Transformation([4, 4, 3, 2, 6, 4, 6]),
>   Transformation([4, 6, 6, 5, 4, 6, 7]),
>   Transformation([5, 6, 1, 6, 3, 5, 1])],
>   [Transformation([1, 1, 5, 3, 1]),
>   Transformation([2, 2, 4, 2, 3]),
>   Transformation([2, 3, 4, 4, 5]),
>   Transformation([2, 4, 2, 4, 5])],
>   [Transformation([3, 1, 1, 5, 3]),
> Transformation([3, 3, 5, 3, 1])],
>   [Transformation([4, 3, 3, 5, 2, 5]),
>   Transformation([6, 1, 2, 4, 1, 3])],
>   [Transformation([2, 3, 4, 3, 3]), Transformation([3, 5, 2, 4, 2]),
>   Transformation([3, 5, 2, 5, 2]),
> Transformation([5, 3, 3, 5, 2])]];;
gap> semis := List(gens, Semigroup);;
gap> res := List(semis, x -> [NrRClasses(x), Size(x)]);
[ [ 3, 4 ], [ 2, 10 ], [ 3, 14 ], [ 12, 211 ], [ 4, 28 ], [ 378, 4818 ],
  [ 2, 5 ], [ 92, 7142 ], [ 81, 615 ], [ 2, 4 ], [ 158, 2255 ], [ 18, 99 ],
  [ 9, 50 ], [ 16, 76 ], [ 17, 77 ], [ 6, 13 ], [ 19, 330 ], [ 120, 1263 ],
  [ 1, 1 ], [ 14, 53 ], [ 216, 1306 ], [ 6, 12 ], [ 15, 235 ], [ 23, 235 ],
  [ 2, 2 ], [ 3, 9 ], [ 2, 2 ], [ 17, 206 ], [ 22, 506 ], [ 24, 340 ],
  [ 7, 39 ], [ 99, 495 ], [ 10, 18 ], [ 10, 100 ], [ 34, 843 ], [ 14, 210 ],
  [ 546, 3538 ], [ 2, 3 ], [ 2, 3 ], [ 35, 448 ], [ 21, 515 ], [ 9, 14 ],
  [ 5, 11 ], [ 17, 23 ], [ 28, 763 ], [ 15, 199 ], [ 21, 170 ], [ 11, 142 ],
  [ 2, 2 ], [ 33, 1259 ], [ 6, 25 ], [ 64, 426 ], [ 9, 40 ], [ 46, 388 ],
  [ 6, 25 ], [ 11, 49 ], [ 48, 391 ], [ 7, 40 ], [ 13, 18 ], [ 6, 48 ],
  [ 30, 792 ], [ 7, 11 ], [ 1, 3 ], [ 2, 3 ], [ 8, 17 ], [ 15, 115 ],
  [ 49, 1724 ], [ 8, 45 ], [ 6, 46 ], [ 8, 66 ], [ 2, 4 ], [ 1, 3 ],
  [ 322, 4344 ], [ 30, 661 ], [ 1597, 63890 ], [ 10, 76 ], [ 173, 9084 ],
  [ 74, 3931 ], [ 15, 117 ], [ 163, 4804 ], [ 14, 106 ], [ 10, 28 ],
  [ 1, 2 ], [ 53, 328 ], [ 1, 1 ], [ 17, 26 ], [ 172, 1443 ], [ 230, 15176 ],
  [ 83, 1382 ], [ 158, 1074 ], [ 2, 2 ], [ 26, 535 ], [ 3, 6 ], [ 3, 3 ],
  [ 44, 1834 ], [ 158, 1776 ], [ 19, 326 ], [ 9, 45 ], [ 32, 379 ],
  [ 23, 149 ] ]
gap> m := semis[32];;
gap> Size(m);
495
gap> ForAll(GreensRClasses(m), x -> ForAll(Idempotents(x), y -> y in x));
true
gap> idem := Set(Concatenation(List(GreensRClasses(m), Idempotents)));
[ Transformation( [ 1, 1, 1, 1, 1, 1, 1 ] ),
  Transformation( [ 1, 1, 1, 1, 1, 1 ] ),
  Transformation( [ 1, 1, 1, 4, 1, 1, 1 ] ),
  Transformation( [ 1, 1, 3, 1, 1, 1, 1 ] ),
  Transformation( [ 1, 1, 3, 1, 1, 1, 3 ] ),
  Transformation( [ 1, 1, 3, 1, 1, 1 ] ),
  Transformation( [ 1, 1, 3, 3, 1, 1, 1 ] ),
  Transformation( [ 1, 1, 3, 3, 1, 1, 3 ] ),
  Transformation( [ 1, 1, 3, 3, 1, 1 ] ),
  Transformation( [ 1, 1, 3, 6, 6, 6 ] ),
  Transformation( [ 1, 1, 4, 4, 1, 1, 1 ] ),
  Transformation( [ 1, 1, 4, 4, 1, 1, 4 ] ),
  Transformation( [ 1, 1, 7, 1, 1, 1, 7 ] ),
  Transformation( [ 1, 1, 7, 7, 1, 1, 7 ] ),
  Transformation( [ 1, 2, 1, 1, 1, 1, 1 ] ),
  Transformation( [ 1, 2, 1, 1, 1, 1, 2 ] ),
  Transformation( [ 1, 2, 1, 1, 1, 1 ] ),
  Transformation( [ 1, 2, 2, 2, 1, 1, 2 ] ),
  Transformation( [ 1, 2, 2, 2, 2, 1, 2 ] ),
  Transformation( [ 1, 2, 3, 3, 1, 1 ] ),
  Transformation( [ 1, 2, 7, 7, 1, 1, 7 ] ),
  Transformation( [ 1, 3, 3, 3, 1, 1, 3 ] ),
  Transformation( [ 1, 3, 3, 3, 3, 1, 3 ] ),
  Transformation( [ 1, 4, 4, 4, 1, 1, 4 ] ),
  Transformation( [ 1, 4, 4, 4, 4, 1, 4 ] ),
  Transformation( [ 1, 5, 5, 5, 5, 1, 5 ] ),
  Transformation( [ 1, 7, 1, 1, 1, 1, 7 ] ),
  Transformation( [ 1, 7, 3, 3, 1, 1, 7 ] ),
  Transformation( [ 1, 7, 7, 7, 1, 1, 7 ] ),
  Transformation( [ 1, 7, 7, 7, 7, 1, 7 ] ),
  Transformation( [ 2, 2, 2, 2, 2, 2, 2 ] ),
  Transformation( [ 2, 2, 2, 2, 2, 2 ] ),
  Transformation( [ 2, 2, 7, 2, 2, 2, 7 ] ),
  Transformation( [ 2, 2, 7, 7, 2, 2, 7 ] ),
  Transformation( [ 3, 3, 3, 3, 3, 3, 3 ] ),
  Transformation( [ 3, 3, 3, 3, 3, 3 ] ),
  Transformation( [ 3, 3, 3, 4, 3, 3, 3 ] ),
  Transformation( [ 3, 7, 3, 3, 3, 3, 7 ] ),
  Transformation( [ 4, 4, 3, 4, 4, 4, 3 ] ),
  Transformation( [ 4, 4, 3, 4, 4, 4, 4 ] ),
  Transformation( [ 4, 4, 4, 4, 4, 4, 4 ] ),
  Transformation( [ 5, 3, 3, 3, 5, 5, 3 ] ),
  Transformation( [ 5, 4, 4, 4, 5, 5, 4 ] ),
  Transformation( [ 5, 5, 3, 3, 5, 5, 3 ] ),
  Transformation( [ 5, 5, 3, 3, 5, 5, 5 ] ),
  Transformation( [ 5, 5, 3, 3, 5, 5 ] ),
  Transformation( [ 5, 5, 3, 4, 5, 5, 3 ] ),
  Transformation( [ 5, 5, 3, 4, 5, 5, 5 ] ),
  Transformation( [ 5, 5, 3, 4, 5, 5 ] ),
  Transformation( [ 5, 5, 3, 5, 5, 5, 3 ] ),
  Transformation( [ 5, 5, 3, 5, 5, 5, 5 ] ),
  Transformation( [ 5, 5, 3, 5, 5, 5 ] ),
  Transformation( [ 5, 5, 4, 4, 5, 5, 4 ] ),
  Transformation( [ 5, 5, 4, 4, 5, 5, 5 ] ),
  Transformation( [ 5, 5, 5, 4, 5, 5, 5 ] ),
  Transformation( [ 5, 5, 5, 5, 5, 5, 5 ] ),
  Transformation( [ 5, 5, 5, 5, 5, 5 ] ),
  Transformation( [ 5, 5, 7, 5, 5, 5, 7 ] ),
  Transformation( [ 5, 5, 7, 7, 5, 5, 7 ] ),
  Transformation( [ 5, 7, 3, 3, 5, 5, 7 ] ),
  Transformation( [ 5, 7, 5, 5, 5, 5, 7 ] ),
  Transformation( [ 5, 7, 7, 7, 5, 5, 7 ] ),
  Transformation( [ 6, 2, 2, 2, 2, 6, 2 ] ),
  Transformation( [ 6, 2, 2, 2, 6, 6, 2 ] ),
  Transformation( [ 6, 2, 6, 6, 6, 6, 2 ] ),
  Transformation( [ 6, 2, 6, 6, 6, 6, 6 ] ),
  Transformation( [ 6, 3, 3, 3, 3, 6, 3 ] ),
  Transformation( [ 6, 3, 3, 3, 6, 6, 3 ] ),
  Transformation( [ 6, 4, 4, 4, 4, 6, 4 ] ),
  Transformation( [ 6, 4, 4, 4, 6, 6, 4 ] ),
  Transformation( [ 6, 5, 5, 5, 5, 6, 5 ] ),
  Transformation( [ 6, 6, 3, 3, 6, 6, 3 ] ),
  Transformation( [ 6, 6, 3, 3, 6, 6, 6 ] ),
  Transformation( [ 6, 6, 3, 3, 6, 6 ] ),
  Transformation( [ 6, 6, 3, 6, 6, 6, 3 ] ),
  Transformation( [ 6, 6, 3, 6, 6, 6, 6 ] ),
  Transformation( [ 6, 6, 3, 6, 6, 6 ] ),
  Transformation( [ 6, 6, 4, 4, 6, 6, 4 ] ),
  Transformation( [ 6, 6, 4, 4, 6, 6, 6 ] ),
  Transformation( [ 6, 6, 6, 4, 6, 6, 6 ] ),
  Transformation( [ 6, 6, 6, 6, 6, 6, 6 ] ),
  Transformation( [ 6, 6, 6, 6, 6, 6 ] ),
  Transformation( [ 6, 6, 7, 6, 6, 6, 7 ] ),
  Transformation( [ 6, 6, 7, 7, 6, 6, 7 ] ),
  Transformation( [ 6, 7, 3, 3, 6, 6, 7 ] ),
  Transformation( [ 6, 7, 6, 6, 6, 6, 7 ] ),
  Transformation( [ 6, 7, 7, 7, 6, 6, 7 ] ),
  Transformation( [ 6, 7, 7, 7, 7, 6, 7 ] ),
  Transformation( [ 7, 2, 7, 7, 7, 7, 7 ] ),
  Transformation( [ 7, 7, 3, 3, 7, 7, 7 ] ),
  Transformation( [ 7, 7, 3, 7, 7, 7, 7 ] ),
  Transformation( [ 7, 7, 7, 7, 7, 7, 7 ] ) ]
gap> idem = Set(Idempotents(m));
true
gap> H := GreensHClasses(m);;
gap> I := Concatenation(List(GreensRClasses(m), GreensHClasses));;
gap> ForAll(H, x -> Number(I, y -> Representative(x) in y) = 1);
true
gap> m := semis[68];;
gap> H := GreensHClasses(m);;
gap> I := Concatenation(List(GreensRClasses(m), GreensHClasses));;
gap> ForAll(H, x -> Number(I, y -> Representative(x) in y) = 1);
true
gap> m := semis[74];;
gap> r := GreensRClassOfElement(m, Transformation([2, 1, 2, 2, 1, 2, 1]));;
gap> d := DClassOfRClass(r);;
gap> dr := GreensRClasses(d);;
gap> r2 := First(dr, x -> x = r);;
gap> DClassOfRClass(r2) = d;
true
gap> m := Semigroup(GeneratorsOfSemigroup(m));
<transformation semigroup of degree 7 with 3 generators>
gap> r := GreensRClassOfElement(m, Transformation([2, 1, 2, 2, 1, 2, 1]));;
gap> d := DClassOfRClass(r);;
gap> dr := GreensRClasses(d);;
gap> r2 := First(dr, x -> x = r);;
gap> DClassOfRClass(r2) = d;
true
gap> res := List(semis, x -> [Length(GreensLClasses(x)), Size(x)]);
[ [ 3, 4 ], [ 5, 10 ], [ 2, 14 ], [ 19, 211 ], [ 9, 28 ], [ 46, 4818 ],
  [ 2, 5 ], [ 39, 7142 ], [ 25, 615 ], [ 2, 4 ], [ 789, 2255 ], [ 21, 99 ],
  [ 11, 50 ], [ 25, 76 ], [ 42, 77 ], [ 10, 13 ], [ 23, 330 ], [ 87, 1263 ],
  [ 1, 1 ], [ 24, 53 ], [ 195, 1306 ], [ 9, 12 ], [ 15, 235 ], [ 28, 235 ],
  [ 2, 2 ], [ 7, 9 ], [ 2, 2 ], [ 18, 206 ], [ 26, 506 ], [ 25, 340 ],
  [ 10, 39 ], [ 45, 495 ], [ 13, 18 ], [ 11, 100 ], [ 94, 843 ], [ 15, 210 ],
  [ 80, 3538 ], [ 2, 3 ], [ 2, 3 ], [ 103, 448 ], [ 21, 515 ], [ 10, 14 ],
  [ 7, 11 ], [ 14, 23 ], [ 27, 763 ], [ 14, 199 ], [ 20, 170 ], [ 13, 142 ],
  [ 2, 2 ], [ 30, 1259 ], [ 9, 25 ], [ 23, 426 ], [ 17, 40 ], [ 34, 388 ],
  [ 8, 25 ], [ 13, 49 ], [ 31, 391 ], [ 10, 40 ], [ 17, 18 ], [ 12, 48 ],
  [ 68, 792 ], [ 10, 11 ], [ 1, 3 ], [ 2, 3 ], [ 8, 17 ], [ 22, 115 ],
  [ 201, 1724 ], [ 7, 45 ], [ 10, 46 ], [ 11, 66 ], [ 2, 4 ], [ 1, 3 ],
  [ 363, 4344 ], [ 68, 661 ], [ 2423, 63890 ], [ 11, 76 ], [ 57, 9084 ],
  [ 84, 3931 ], [ 12, 117 ], [ 156, 4804 ], [ 16, 106 ], [ 10, 28 ],
  [ 1, 2 ], [ 52, 328 ], [ 1, 1 ], [ 20, 26 ], [ 257, 1443 ], [ 74, 15176 ],
  [ 333, 1382 ], [ 74, 1074 ], [ 2, 2 ], [ 28, 535 ], [ 3, 6 ], [ 3, 3 ],
  [ 35, 1834 ], [ 93, 1776 ], [ 18, 326 ], [ 16, 45 ], [ 25, 379 ],
  [ 33, 149 ] ]
gap> ForAll(GreensLClasses(m), x ->
> ForAll(Idempotents(x), y -> y in x));
true
gap> idem := Set(Concatenation(List(GreensLClasses(m), Idempotents)));
[ Transformation( [ 1, 1, 1, 1, 1, 1, 1 ] ),
  Transformation( [ 1, 1, 1, 1, 5, 1, 1 ] ),
  Transformation( [ 1, 1, 1, 1, 5, 1, 5 ] ),
  Transformation( [ 1, 1, 1, 1, 5, 5, 1 ] ),
  Transformation( [ 1, 1, 1, 4, 1, 1, 1 ] ),
  Transformation( [ 1, 1, 1, 4, 1, 4, 1 ] ),
  Transformation( [ 1, 1, 1, 4, 4, 1, 4 ] ),
  Transformation( [ 1, 1, 1, 4, 5, 1, 5 ] ),
  Transformation( [ 1, 1, 1, 5, 5, 1, 5 ] ),
  Transformation( [ 1, 1, 4, 4, 1, 1, 1 ] ),
  Transformation( [ 1, 1, 4, 4, 4, 1, 4 ] ),
  Transformation( [ 1, 1, 5, 5, 5, 1, 5 ] ),
  Transformation( [ 1, 2, 1, 1, 1, 1, 1 ] ),
  Transformation( [ 1, 2, 1, 1, 2, 1, 1 ] ),
  Transformation( [ 1, 2, 1, 1, 2, 1, 2 ] ),
  Transformation( [ 1, 2, 1, 1, 2, 2, 2 ] ),
  Transformation( [ 1, 2, 1, 1, 5, 1, 1 ] ),
  Transformation( [ 1, 2, 1, 2, 2, 1, 2 ] ),
  Transformation( [ 1, 2, 1, 2, 2, 2, 2 ] ),
  Transformation( [ 1, 2, 2, 1, 1, 1, 1 ] ),
  Transformation( [ 1, 2, 2, 1, 1, 2, 1 ] ),
  Transformation( [ 1, 2, 2, 1, 2, 2, 1 ] ),
  Transformation( [ 1, 2, 2, 1, 5, 5, 1 ] ),
  Transformation( [ 1, 4, 1, 4, 4, 1, 4 ] ),
  Transformation( [ 1, 4, 1, 4, 4, 4, 4 ] ),
  Transformation( [ 1, 5, 1, 1, 5, 1, 1 ] ),
  Transformation( [ 1, 5, 1, 1, 5, 1, 5 ] ),
  Transformation( [ 1, 5, 1, 1, 5, 5, 5 ] ),
  Transformation( [ 1, 5, 1, 4, 5, 4, 5 ] ),
  Transformation( [ 1, 5, 1, 5, 5, 1, 5 ] ),
  Transformation( [ 1, 5, 1, 5, 5, 5, 5 ] ),
  Transformation( [ 1, 5, 5, 1, 5, 5, 1 ] ),
  Transformation( [ 2, 2, 2, 2, 2, 2, 2 ] ),
  Transformation( [ 2, 2, 2, 2, 2, 6, 2 ] ),
  Transformation( [ 2, 2, 2, 2, 5, 2, 2 ] ),
  Transformation( [ 2, 2, 2, 2, 5, 2, 5 ] ),
  Transformation( [ 2, 2, 2, 2, 5, 5, 2 ] ),
  Transformation( [ 2, 2, 2, 2, 6, 6, 2 ] ),
  Transformation( [ 2, 2, 2, 2, 7, 2, 7 ] ),
  Transformation( [ 2, 2, 2, 5, 5, 2, 5 ] ),
  Transformation( [ 2, 2, 2, 6, 2, 6, 2 ] ),
  Transformation( [ 2, 2, 2, 7, 7, 2, 7 ] ),
  Transformation( [ 2, 2, 5, 5, 5, 2, 5 ] ),
  Transformation( [ 2, 2, 7, 7, 7, 2, 7 ] ),
  Transformation( [ 3, 3, 3, 3, 3, 3, 3 ] ),
  Transformation( [ 3, 3, 3, 3, 5, 3, 3 ] ),
  Transformation( [ 3, 3, 3, 3, 5, 3, 5 ] ),
  Transformation( [ 3, 3, 3, 3, 5, 5, 3 ] ),
  Transformation( [ 3, 3, 3, 3, 7, 3, 7 ] ),
  Transformation( [ 3, 3, 3, 4, 3, 3, 3 ] ),
  Transformation( [ 3, 3, 3, 4, 3, 4, 3 ] ),
  Transformation( [ 3, 3, 3, 4, 4, 3, 4 ] ),
  Transformation( [ 3, 3, 3, 4, 5, 3, 5 ] ),
  Transformation( [ 3, 3, 3, 4, 7, 3, 7 ] ),
  Transformation( [ 3, 3, 3, 5, 5, 3, 5 ] ),
  Transformation( [ 3, 3, 3, 7, 7, 3, 7 ] ),
  Transformation( [ 3, 4, 3, 4, 4, 3, 4 ] ),
  Transformation( [ 3, 4, 3, 4, 4, 4, 4 ] ),
  Transformation( [ 3, 5, 3, 3, 5, 3, 3 ] ),
  Transformation( [ 3, 5, 3, 3, 5, 3, 5 ] ),
  Transformation( [ 3, 5, 3, 3, 5, 5, 5 ] ),
  Transformation( [ 3, 5, 3, 4, 5, 4, 5 ] ),
  Transformation( [ 3, 5, 3, 5, 5, 3, 5 ] ),
  Transformation( [ 3, 5, 3, 5, 5, 5, 5 ] ),
  Transformation( [ 3, 7, 3, 3, 7, 3, 7 ] ),
  Transformation( [ 3, 7, 3, 3, 7, 7, 7 ] ),
  Transformation( [ 3, 7, 3, 4, 7, 4, 7 ] ),
  Transformation( [ 3, 7, 3, 7, 7, 3, 7 ] ),
  Transformation( [ 3, 7, 3, 7, 7, 7, 7 ] ),
  Transformation( [ 4, 3, 3, 4, 3, 3, 4 ] ),
  Transformation( [ 4, 3, 3, 4, 4, 3, 4 ] ),
  Transformation( [ 4, 3, 3, 4, 4, 4, 4 ] ),
  Transformation( [ 4, 3, 3, 4, 5, 5, 4 ] ),
  Transformation( [ 4, 4, 4, 4, 4, 4, 4 ] ),
  Transformation( [ 4, 4, 4, 4, 5, 4, 4 ] ),
  Transformation( [ 4, 4, 4, 4, 5, 4, 5 ] ),
  Transformation( [ 4, 4, 4, 4, 5, 5, 4 ] ),
  Transformation( [ 4, 4, 4, 4, 7, 4, 7 ] ),
  Transformation( [ 4, 5, 4, 4, 5, 4, 4 ] ),
  Transformation( [ 4, 5, 4, 4, 5, 4, 5 ] ),
  Transformation( [ 4, 5, 4, 4, 5, 5, 5 ] ),
  Transformation( [ 4, 5, 5, 4, 5, 5, 4 ] ),
  Transformation( [ 4, 7, 4, 4, 7, 4, 7 ] ),
  Transformation( [ 4, 7, 4, 4, 7, 7, 7 ] ),
  Transformation( [ 5, 2, 2, 5, 5, 2, 5 ] ),
  Transformation( [ 5, 2, 2, 5, 5, 5, 5 ] ),
  Transformation( [ 5, 2, 5, 5, 5, 5, 5 ] ),
  Transformation( [ 5, 3, 3, 5, 5, 3, 5 ] ),
  Transformation( [ 5, 3, 3, 5, 5, 5, 5 ] ),
  Transformation( [ 5, 5, 3, 3, 5, 5, 5 ] ),
  Transformation( [ 5, 5, 4, 4, 5, 5, 5 ] ),
  Transformation( [ 5, 5, 5, 4, 5, 4, 5 ] ),
  Transformation( [ 5, 5, 5, 4, 5, 5, 5 ] ),
  Transformation( [ 5, 5, 5, 5, 5, 5, 5 ] ),
  Transformation( [ 6, 2, 2, 6, 6, 6, 6 ] ),
  Transformation( [ 6, 2, 6, 2, 2, 6, 2 ] ),
  Transformation( [ 6, 2, 6, 6, 2, 6, 2 ] ),
  Transformation( [ 6, 2, 6, 6, 2, 6, 6 ] ),
  Transformation( [ 6, 2, 6, 6, 6, 6, 6 ] ),
  Transformation( [ 6, 6, 6, 6, 6, 6, 6 ] ),
  Transformation( [ 6, 6, 6, 6, 7, 6, 7 ] ),
  Transformation( [ 6, 6, 6, 7, 7, 6, 7 ] ),
  Transformation( [ 6, 6, 7, 7, 7, 6, 7 ] ),
  Transformation( [ 6, 7, 6, 6, 7, 6, 7 ] ),
  Transformation( [ 6, 7, 6, 7, 7, 6, 7 ] ),
  Transformation( [ 7, 2, 2, 7, 2, 2, 7 ] ),
  Transformation( [ 7, 2, 2, 7, 5, 5, 7 ] ),
  Transformation( [ 7, 2, 2, 7, 6, 6, 7 ] ),
  Transformation( [ 7, 2, 2, 7, 7, 2, 7 ] ),
  Transformation( [ 7, 2, 2, 7, 7, 7, 7 ] ),
  Transformation( [ 7, 2, 7, 7, 2, 7, 7 ] ),
  Transformation( [ 7, 2, 7, 7, 5, 7, 7 ] ),
  Transformation( [ 7, 2, 7, 7, 7, 7, 7 ] ),
  Transformation( [ 7, 3, 3, 7, 3, 3, 7 ] ),
  Transformation( [ 7, 3, 3, 7, 7, 3, 7 ] ),
  Transformation( [ 7, 3, 3, 7, 7, 7, 7 ] ),
  Transformation( [ 7, 5, 5, 7, 5, 5, 7 ] ),
  Transformation( [ 7, 5, 7, 7, 5, 7, 7 ] ),
  Transformation( [ 7, 6, 6, 7, 6, 6, 7 ] ),
  Transformation( [ 7, 6, 6, 7, 7, 6, 7 ] ),
  Transformation( [ 7, 7, 3, 3, 7, 7, 7 ] ),
  Transformation( [ 7, 7, 4, 4, 7, 7, 7 ] ),
  Transformation( [ 7, 7, 7, 4, 7, 4, 7 ] ),
  Transformation( [ 7, 7, 7, 4, 7, 7, 7 ] ),
  Transformation( [ 7, 7, 7, 6, 7, 6, 7 ] ),
  Transformation( [ 7, 7, 7, 7, 5, 5, 7 ] ),
  Transformation( [ 7, 7, 7, 7, 5, 7, 7 ] ),
  Transformation( [ 7, 7, 7, 7, 6, 6, 7 ] ),
  Transformation( [ 7, 7, 7, 7, 7, 6, 7 ] ),
  Transformation( [ 7, 7, 7, 7, 7, 7, 7 ] ) ]
gap> idem = Set(Idempotents(m));
true
gap> m := semis[30];;
gap> r := GreensLClassOfElement(m, Transformation([3, 3, 3, 3, 3, 3, 5]));;
gap> d := DClassOfLClass(r);;
gap> dr := GreensLClasses(d);;
gap> r2 := First(dr, x -> x = r);;
gap> DClassOfLClass(r2) = d;
true
gap> m := Semigroup(GeneratorsOfSemigroup(m));
<transformation semigroup of degree 7 with 2 generators>
gap>  r := GreensLClassOfElement(m, Transformation([3, 3, 3, 3, 3, 3, 5]));
<Green's L-class: Transformation( [ 3, 3, 3, 3, 3, 3, 5 ] )>
gap> Transformation([3, 3, 3, 3, 3, 3, 5]) in last;
true
gap> d := DClassOfLClass(r);;
gap> dr := GreensLClasses(d);;
gap> r2 := First(dr, x -> x = r);;
gap> DClassOfLClass(r2) = d;
true
gap> List(semis, s -> Length(GreensHClasses(s)));
[ 3, 5, 3, 77, 13, 1281, 2, 1032, 231, 2, 1355, 57, 28, 48, 57, 12, 139, 508,
  1, 36, 801, 10, 71, 130, 2, 7, 2, 83, 158, 172, 22, 285, 17, 40, 377, 67,
  1285, 2, 2, 212, 153, 14, 9, 22, 239, 65, 91, 55, 2, 367, 15, 168, 26, 207,
  14, 29, 274, 22, 17, 26, 253, 10, 1, 2, 13, 64, 605, 20, 25, 33, 2, 1,
  1520, 307, 9625, 41, 1885, 945, 54, 1297, 58, 18, 1, 173, 1, 25, 737, 2807,
  636, 495, 2, 201, 3, 3, 471, 715, 118, 28, 197, 88 ]
gap> ForAll(semis, s ->
> Number(GreensHClasses(s), IsGroupHClass) = Length(Idempotents(s)));
true
gap> List(semis, s -> Number(GreensDClasses(s), IsRegularDClass));
[ 1, 2, 2, 4, 3, 6, 1, 5, 4, 1, 6, 3, 3, 4, 3, 3, 4, 4, 1, 4, 6, 4, 4, 4, 1,
  2, 1, 3, 5, 5, 3, 5, 3, 3, 5, 4, 6, 1, 1, 4, 4, 3, 3, 4, 4, 4, 4, 3, 1, 4,
  3, 4, 4, 4, 4, 3, 6, 3, 3, 3, 4, 3, 1, 2, 2, 4, 4, 3, 3, 3, 1, 1, 5, 3, 7,
  3, 5, 5, 5, 5, 2, 3, 1, 4, 1, 4, 5, 6, 5, 5, 1, 3, 1, 1, 6, 4, 3, 3, 4, 3 ]
gap> List(semis, s -> Set(GreensDClasses(s), x -> Length(Idempotents(x))));
[ [ 0, 1 ], [ 1, 4 ], [ 1, 2 ], [ 1, 5, 7, 30 ], [ 1, 4 ],
  [ 0, 1, 6, 11, 167, 168 ], [ 0, 1 ], [ 2, 6, 42, 169, 197 ],
  [ 0, 2, 5, 18, 58 ], [ 0, 1 ], [ 0, 1, 5, 8, 46, 159 ], [ 0, 1, 5, 19 ],
  [ 0, 2, 4, 11 ], [ 0, 1, 2, 4, 14 ], [ 0, 1, 3, 12 ], [ 0, 1, 2, 3 ],
  [ 2, 5, 17, 39 ], [ 0, 1, 6, 24, 137 ], [ 1 ], [ 0, 1, 3, 10 ],
  [ 0, 1, 4, 6, 7, 221 ], [ 0, 1, 2, 3 ], [ 1, 4, 12, 24 ], [ 0, 1, 7, 34 ],
  [ 0, 1 ], [ 0, 1, 3 ], [ 0, 1 ], [ 0, 5, 9, 36 ], [ 0, 1, 5, 17, 50 ],
  [ 0, 1, 7, 63 ], [ 0, 1, 4, 8 ], [ 0, 1, 2, 7, 13, 69 ], [ 0, 1, 2, 4 ],
  [ 4, 17 ], [ 0, 1, 2, 6, 20, 93 ], [ 1, 4, 10, 24 ], [ 0, 1, 7, 105, 199 ],
  [ 0, 1 ], [ 0, 1 ], [ 0, 1, 5, 13, 48 ], [ 1, 5, 20, 51 ], [ 0, 1, 2, 3 ],
  [ 0, 1, 3 ], [ 0, 1, 2, 3 ], [ 2, 7, 27, 82 ], [ 1, 4, 9, 24 ],
  [ 0, 1, 3, 5, 38 ], [ 4, 6, 24 ], [ 0, 1 ], [ 1, 6, 47, 121 ],
  [ 0, 1, 4, 5 ], [ 0, 1, 5, 14, 42 ], [ 0, 1, 3, 8 ], [ 0, 1, 6, 80 ],
  [ 1, 3, 6 ], [ 0, 1, 4, 11 ], [ 0, 1, 4, 6, 20, 65 ], [ 0, 1, 4, 10 ],
  [ 0, 1, 2 ], [ 2, 4, 10 ], [ 0, 1, 5, 34, 62 ], [ 0, 1, 2 ], [ 1 ], [ 1 ],
  [ 0, 3, 4 ], [ 0, 1, 6, 26 ], [ 0, 2, 6, 47, 121 ], [ 2, 3, 10 ],
  [ 1, 4, 11 ], [ 3, 4, 15 ], [ 0, 1 ], [ 1 ], [ 0, 1, 3, 7, 122, 248 ],
  [ 0, 7, 12, 111 ], [ 0, 1, 7, 9, 258, 430, 889 ], [ 0, 1, 4, 20 ],
  [ 0, 1, 6, 12, 231, 324 ], [ 0, 1, 3, 6, 143, 163 ], [ 1, 3, 4, 24 ],
  [ 0, 1, 5, 7, 140, 277 ], [ 0, 5, 23 ], [ 0, 1, 4 ], [ 1 ], [ 0, 1, 5, 52 ],
  [ 1 ], [ 0, 1, 2 ], [ 0, 1, 7, 11, 177 ], [ 0, 1, 2, 7, 38, 390, 434 ],
  [ 0, 5, 9, 40, 114 ], [ 0, 1, 2, 6, 32, 65 ], [ 0, 1 ], [ 0, 6, 16, 74 ],
  [ 0, 1 ], [ 0, 1 ], [ 1, 4, 6, 65, 114 ], [ 0, 1, 7, 40, 200 ],
  [ 0, 5, 8, 44 ], [ 0, 1, 3, 10 ], [ 0, 1, 6, 73 ], [ 0, 1, 4, 33 ] ]
gap> List(semis, x -> [Length(GreensDClasses(x))]);
[ [ 3 ], [ 2 ], [ 2 ], [ 4 ], [ 3 ], [ 9 ], [ 2 ], [ 5 ], [ 6 ], [ 2 ],
  [ 75 ], [ 10 ], [ 4 ], [ 8 ], [ 12 ], [ 5 ], [ 4 ], [ 16 ], [ 1 ], [ 10 ],
  [ 101 ], [ 5 ], [ 4 ], [ 8 ], [ 2 ], [ 3 ], [ 2 ], [ 6 ], [ 7 ], [ 6 ],
  [ 4 ], [ 19 ], [ 8 ], [ 3 ], [ 13 ], [ 4 ], [ 36 ], [ 2 ], [ 2 ], [ 14 ],
  [ 4 ], [ 7 ], [ 4 ], [ 11 ], [ 4 ], [ 4 ], [ 7 ], [ 3 ], [ 2 ], [ 4 ],
  [ 4 ], [ 7 ], [ 6 ], [ 16 ], [ 4 ], [ 7 ], [ 8 ], [ 4 ], [ 13 ], [ 3 ],
  [ 7 ], [ 7 ], [ 1 ], [ 2 ], [ 4 ], [ 9 ], [ 10 ], [ 3 ], [ 3 ], [ 3 ],
  [ 2 ], [ 1 ], [ 54 ], [ 10 ], [ 32 ], [ 4 ], [ 7 ], [ 15 ], [ 5 ], [ 22 ],
  [ 7 ], [ 5 ], [ 1 ], [ 17 ], [ 1 ], [ 14 ], [ 62 ], [ 11 ], [ 26 ], [ 15 ],
  [ 2 ], [ 8 ], [ 3 ], [ 3 ], [ 6 ], [ 19 ], [ 4 ], [ 5 ], [ 6 ], [ 13 ] ]
gap> List(semis, s -> Length(Idempotents(s)));
[ 1, 5, 3, 43, 9, 354, 1, 416, 83, 1, 220, 25, 17, 21, 16, 6, 63, 168, 1, 15,
  240, 8, 41, 43, 1, 4, 1, 50, 74, 79, 13, 92, 7, 25, 122, 39, 314, 1, 1, 67,
  77, 6, 7, 7, 118, 38, 47, 34, 1, 175, 10, 62, 13, 93, 11, 16, 97, 15, 4,
  16, 102, 4, 1, 2, 7, 34, 176, 15, 16, 22, 1, 1, 381, 130, 1595, 25, 574,
  316, 33, 430, 28, 9, 1, 63, 1, 5, 197, 872, 173, 106, 1, 96, 1, 1, 191,
  248, 57, 14, 86, 38 ]
gap> a := Transformation([2, 1, 4, 5, 6, 3]);;
gap> b := Transformation([2, 3, 1, 5, 4, 1]);;
gap> M := Semigroup(a, b);;
gap> GreensLClassOfElement(M, a);
<Green's L-class: Transformation( [ 2, 1, 4, 5, 6, 3 ] )>
gap> Transformation([2, 1, 4, 5, 6, 3]) in last;
true
gap> f := FreeSemigroup(3);;
gap> a := f.1;; b := f.2;; c := f.3;;
gap> s := f / [[a ^ 2, a], [b ^ 2, b], [c ^ 2, c], [a * b, a],
> [b * a, b], [a * c, a], [c * a, c], [b * c, b], [c * b, c]];
<fp semigroup with 3 generators and 9 relations of length 30>
gap> Size(s);
3
gap> GreensLClassOfElement(s, s.1);
<Green's L-class: s1>
gap> gens := [Transformation([2, 2, 5, 2, 3]),
> Transformation([2, 5, 3, 5, 3])];;
gap> S := Semigroup(gens);;
gap> f := Transformation([5, 5, 3, 5, 3]);;
gap> GreensHClassOfElement(S, f);;
gap> Representative(last);
Transformation( [ 5, 5, 3, 5, 3 ] )
gap> IsTrivial(SchutzenbergerGroup(last2));
true
gap> gens := [Transformation([4, 1, 4, 5, 3]),
> Transformation([5, 3, 5, 4, 3])];;
gap> S := Semigroup(gens);;
gap> C := GreensLClassOfElement(S, gens[1] * gens[2] * gens[1]);
<Green's L-class: Transformation( [ 5, 3, 5, 4, 3 ] )>
gap> Transformation([5, 3, 5, 4, 3]) in last;
true
gap> gens := [Transformation([5, 1, 1, 5, 1]),
> Transformation([5, 2, 4, 3, 2])];;
gap> S := Semigroup(gens);;
gap> gens := [Transformation([1, 2, 1, 2, 1]),
> Transformation([3, 4, 2, 1, 4])];;
gap> S := Semigroup(gens);;
gap> RClassReps(S);
[ Transformation( [ 1, 2, 1, 2, 1 ] ), Transformation( [ 3, 4, 2, 1, 4 ] ),
  Transformation( [ 1, 2, 2, 1, 2 ] ), Transformation( [ 2, 1, 2, 1, 1 ] ) ]
gap> a := Transformation([2, 1, 4, 5, 6, 3]);;
gap> b := Transformation([2, 3, 1, 5, 4, 1]);;
gap> M := Semigroup(a, b);;
gap> rc := GreensRClassOfElement(M, a * b * a);
<Green's R-class: Transformation( [ 4, 1, 6, 5, 2, 2 ] )>
gap> Transformation([5, 2, 1, 4, 3, 3]) in last;
true
gap> gens := [Transformation([3, 5, 2, 5, 1]),
> Transformation([4, 3, 2, 1, 5])];;
gap> S := Semigroup(gens);;
gap> f := Transformation([2, 4, 2, 5, 3]);;
gap> r := RClass(S, f);
<Green's R-class: Transformation( [ 2, 4, 2, 5, 3 ] )>
gap> Transformation([3, 1, 3, 5, 2]) in last;
true
gap> LambdaOrb(r);
<closed orbit, 25 points with Schreier tree with log>
gap> AsList(last);
[ [ 0 ], [ 1, 2, 3, 5 ], [ 1, 2, 3, 4, 5 ], [ 2, 3, 4, 5 ], [ 1, 2, 5 ],
  [ 1, 3, 5 ], [ 3, 4, 5 ], [ 1, 2, 3 ], [ 2, 4, 5 ], [ 2, 3, 5 ],
  [ 2, 3, 4 ], [ 1, 5 ], [ 2, 5 ], [ 1, 3 ], [ 4, 5 ], [ 3, 5 ], [ 2, 3 ],
  [ 2, 4 ], [ 1, 2 ], [ 5 ], [ 3, 4 ], [ 1 ], [ 3 ], [ 4 ], [ 2 ] ]
gap> LambdaOrbMults(LambdaOrb(r), LambdaOrbSCCIndex(r))[LambdaOrbSCCIndex(r)];
[ IdentityTransformation, IdentityTransformation ]
gap> SchutzenbergerGroup(r);
Group([ (1,3,2,5) ])
gap> gens := [Transformation([4, 1, 5, 2, 4]),
> Transformation([4, 4, 1, 5, 3])];;
gap> gens := [Transformation([4, 4, 3, 5, 3]),
> Transformation([5, 1, 1, 4, 1]),
> Transformation([5, 5, 4, 4, 5])];;
gap> S := Semigroup(gens);;
gap> f := Transformation([4, 5, 5, 5, 5]);;
gap> SchutzenbergerGroup(GreensDClassOfElement(S, f));
Group([ (4,5) ])
gap> SchutzenbergerGroup(GreensRClassOfElement(S, f));
Group([ (4,5) ])
gap> SchutzenbergerGroup(GreensLClassOfElement(S, f));
Group([ (4,5) ])
gap> SchutzenbergerGroup(GreensHClassOfElement(S, f));
Group([ (4,5) ])
gap>  S := Semigroup([Transformation([6, 4, 4, 4, 6, 1]),
> Transformation([6, 5, 1, 6, 2, 2])]);;
gap> AsSet(Enumerate(LambdaOrb(S)));
[ [ 0 ], [ 1 ], [ 1, 2, 5, 6 ], [ 1, 4 ], [ 1, 4, 6 ], [ 2 ], [ 2, 5 ],
  [ 2, 5, 6 ], [ 2, 6 ], [ 4 ], [ 4, 6 ], [ 5 ], [ 6 ] ]
gap> S := Semigroup([Transformation([2, 3, 4, 1]),
> Transformation([3, 3, 1, 1])]);;
gap> Idempotents(S, 1);
[  ]
gap> Idempotents(S, 2);
[ Transformation( [ 1, 1, 3, 3 ] ), Transformation( [ 1, 3, 3, 1 ] ),
  Transformation( [ 2, 2, 4, 4 ] ), Transformation( [ 4, 2, 2, 4 ] ) ]
gap> Idempotents(S, 3);
[  ]
gap> Idempotents(S, 4);
[ IdentityTransformation ]
gap> Idempotents(S);
[ IdentityTransformation, Transformation( [ 1, 1, 3, 3 ] ),
  Transformation( [ 1, 3, 3, 1 ] ), Transformation( [ 2, 2, 4, 4 ] ),
  Transformation( [ 4, 2, 2, 4 ] ) ]
gap> S := Semigroup([Transformation([2, 4, 1, 2]),
> Transformation([3, 3, 4, 1])]);;
gap> AsSet(Enumerate(RhoOrb(S)));
[ [ 0 ], [ 1, 1, 1, 1 ], [ 1, 1, 1, 2 ], [ 1, 1, 2, 1 ], [ 1, 1, 2, 2 ],
  [ 1, 1, 2, 3 ], [ 1, 2, 1, 1 ], [ 1, 2, 2, 1 ], [ 1, 2, 3, 1 ] ]

# MonoidPkgTest7: from install_no_grape.tst
gap> gens := [Transformation([4, 3, 3, 6, 7, 2, 3]),
>   Transformation([6, 6, 4, 4, 2, 1, 4])];;
gap> s := Semigroup(gens);;
gap> Length(GreensRClasses(s));
17
gap> s := Semigroup(gens);;
gap> NrRClasses(s);
17
gap> f := Transformation([3, 3, 3, 3, 3, 2, 3]);;
gap> r := RClass(s, f);
<Green's R-class: Transformation( [ 3, 3, 3, 3, 3, 2, 3 ] )>
gap> Transformation([3, 3, 3, 3, 3, 2, 3]) in last;
true
gap> LambdaOrb(r);
<closed orbit, 19 points with Schreier tree with log>
gap> AsSet(LambdaOrb(r));
[ [ 0 ], [ 1 ], [ 1, 2, 4, 6 ], [ 1, 4 ], [ 1, 4, 6 ], [ 1, 6 ], [ 2 ],
  [ 2, 3 ], [ 2, 3, 4, 6 ], [ 2, 3, 4, 6, 7 ], [ 2, 3, 6 ], [ 2, 4 ],
  [ 2, 4, 6 ], [ 2, 6 ], [ 3 ], [ 3, 6 ], [ 4 ], [ 4, 6 ], [ 6 ] ]
gap> SchutzenbergerGroup(r);
Group([ (2,3) ])
gap> Number(GreensDClasses(s), IsRegularDClass);
3
gap> s := Semigroup(gens);
<transformation semigroup of degree 7 with 2 generators>
gap> NrRegularDClasses(s);
3

# MonoidPkgTest8
gap> g1 := Transformation([2, 2, 4, 4, 5, 6]);;
gap> g2 := Transformation([5, 3, 4, 4, 6, 6]);;
gap> m1 := Monoid(g1, g2);;
gap> g1 := Transformation([5, 4, 4, 2, 1]);;
gap> g2 := Transformation([2, 5, 5, 4, 1]);;
gap> m2 := Monoid(g1, g2);;
gap> g1 := Transformation([1, 2, 1, 3, 3]);;
gap> g2 := Transformation([2, 2, 3, 5, 5]);;
gap> m3 := Monoid(g1, g2);;
gap> g1 := Transformation([8, 7, 5, 3, 1, 3, 8, 8]);;
gap> g2 := Transformation([5, 1, 4, 1, 4, 4, 7, 8]);;
gap> m4 := Monoid(g1, g2);;
gap> g1 := Transformation([3, 1, 2, 3, 2, 3, 2, 3]);;
gap> g2 := Transformation([2, 5, 8, 5, 2, 5, 7, 8]);;
gap> m5 := Monoid(g1, g2);;
gap> g1 := Transformation([3, 3, 2, 6, 2, 4, 4, 6]);;
gap> g2 := Transformation([5, 1, 7, 8, 7, 5, 8, 1]);;
gap> m6 := Semigroup(g1, g2);;
gap> g1 := Transformation([3, 3, 2, 6, 2, 4, 4, 6, 3, 4, 6]);;
gap> g2 := Transformation([4, 4, 6, 1, 3, 3, 3, 3, 11, 11, 11]);;
gap> m7 := Monoid(g1, g2);;  # (this is a good example!)
gap> g1 := Transformation([3, 3, 2, 6, 2, 4, 4, 6, 3, 4, 6]);;
gap> g2 := Transformation([4, 4, 6, 1, 3, 3, 3, 3, 11, 11, 11]);;
gap> g3 := Transformation([2, 2, 3, 4, 4, 6, 6, 6, 6, 6, 11]);;
gap> m8 := Monoid(g1, g2, g3);;
gap> g1 := Transformation([3, 3, 2, 6, 2, 4, 4, 6, 3, 4, 6]);;
gap> g2 := Transformation([4, 4, 6, 1, 3, 3, 3, 3, 11, 11, 11]);;
gap> g3 := Transformation([2, 2, 3, 4, 4, 6, 6, 6, 6, 6, 11]);;
gap> g4 := Transformation([2, 2, 3, 4, 4, 6, 6, 6, 6, 11, 11]);;
gap> m9 := Monoid(g1, g2, g3, g4);;
gap> g1 := Transformation([12, 3, 6, 4, 6, 11, 9, 6, 6, 7, 6, 12]);;
gap> g2 := Transformation([10, 7, 2, 11, 7, 3, 12, 4, 3, 8, 7, 5]);;
gap> m11 := Monoid(g1, g2);;
gap> g1 := Transformation([3, 2, 12, 2, 7, 9, 4, 2, 1, 12, 11, 12]);;
gap> g2 := Transformation([3, 6, 12, 7, 2, 2, 3, 6, 1, 7, 11, 1]);;
gap> m14 := Monoid(g1, g2);;
gap> g1 := Transformation([2, 2, 3, 4, 5, 6]);;
gap> g2 := Transformation([2, 3, 4, 5, 6, 1]);;
gap> m15 := Monoid(g1, g2);;
gap> g1 := Transformation([2, 1, 4, 5, 6, 7, 3, 2, 1]);;
gap> g2 := Transformation([2, 1, 4, 2, 1, 4, 2, 1, 4]);;
gap> m18 := Monoid(g1, g2);;
gap> g1 := Transformation([5, 2, 5, 5, 8, 10, 8, 5, 2, 10]);;
gap> g2 := Transformation([2, 2, 5, 5, 5, 8, 8, 8, 8, 8]);;
gap> m22 := Monoid(g1, g2);;
gap> g1 := Transformation([4, 6, 3, 8, 5, 6, 10, 4, 3, 7]);;
gap> g2 := Transformation([5, 6, 6, 3, 8, 6, 3, 7, 8, 4]);;
gap> g3 := Transformation([8, 6, 3, 2, 8, 10, 9, 2, 6, 2]);;
gap> m23 := Monoid(g1, g2, g3);;

# MonoidPkgTest9
gap> SmallMonoids := [m1, m2, m3, m4, m5, m6, m7, m8, m9, m11, m14, m15, m18,
> m22, m23];;
gap> List(SmallMonoids, IsCompletelyRegularSemigroup);
[ false, true, false, false, true, true, true, true, true, false, false,
  false, false, true, false ]
gap> List(SmallMonoids, IsRegularSemigroup);
[ false, true, false, false, true, true, true, true, true, false, false,
  true, true, true, false ]
gap> List(SmallMonoids, IsSimpleSemigroup);
[ false, false, false, false, false, true, false, false, false, false, false,
  false, false, false, false ]
gap> List(SmallMonoids, IsCompletelySimpleSemigroup);
[ false, false, false, false, false, true, false, false, false, false, false,
  false, false, false, false ]
gap> List(SmallMonoids, IsInverseSemigroup);
[ false, true, false, false, false, false, false, false, false, false, false,
  false, false, false, false ]
gap> List(SmallMonoids, IsCliffordSemigroup);
[ false, true, false, false, false, false, false, false, false, false, false,
  false, false, false, false ]
gap> List(SmallMonoids, IsGroupAsSemigroup);
[ false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false ]
gap> List(SmallMonoids, IsZeroSemigroup);
[ false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false ]
gap> List(SmallMonoids, IsLeftZeroSemigroup);
[ false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false ]
gap> List(SmallMonoids, IsRightZeroSemigroup);
[ false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false ]
gap> List(SmallMonoids, IsCommutativeSemigroup);
[ false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false ]
gap> List(SmallMonoids, IsZeroGroup);
[ false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false ]

# MonoidPkgTest10
gap> gens := [Transformation([2, 4, 1, 5, 4, 4, 7, 3, 8, 1]),
>   Transformation([3, 2, 8, 8, 4, 4, 8, 6, 5, 7]),
>   Transformation([4, 10, 6, 6, 1, 2, 4, 10, 9, 7]),
>   Transformation([6, 2, 2, 4, 9, 9, 5, 10, 1, 8]),
>   Transformation([6, 4, 1, 6, 6, 8, 9, 6, 2, 2]),
>   Transformation([6, 8, 1, 10, 6, 4, 9, 1, 9, 4]),
>   Transformation([8, 6, 2, 3, 3, 4, 8, 6, 2, 9]),
>   Transformation([9, 1, 2, 8, 1, 5, 9, 9, 9, 5]),
>   Transformation([9, 3, 1, 5, 10, 3, 4, 6, 10, 2]),
>   Transformation([10, 7, 3, 7, 1, 9, 8, 8, 4, 10])];;
gap> s := Semigroup(gens);;
gap> o := Orb(s, [1, 2, 3, 4], OnSets);
<open orbit, 1 points>
gap> Enumerate(o);
<closed orbit, 351 points>
gap> List(OrbSCC(o), x -> o{x});
[ [ [ 1, 2, 3, 4 ], [ 1, 2, 4, 5 ], [ 2, 3, 4, 8 ], [ 1, 2, 8, 9 ],
      [ 2, 3, 5, 6 ], [ 1, 4, 6, 8 ], [ 1, 4, 6, 10 ], [ 4, 6, 8, 9 ],
      [ 3, 4, 5, 8 ], [ 1, 3, 4, 5 ], [ 2, 4, 6, 9 ], [ 2, 4, 6, 8 ],
      [ 1, 5, 8, 9 ], [ 2, 3, 6, 8 ], [ 1, 2, 5, 9 ], [ 1, 2, 6, 9 ],
      [ 2, 3, 4, 5 ], [ 1, 6, 8, 10 ], [ 3, 4, 6, 7 ], [ 3, 7, 8, 9 ],
      [ 4, 6, 9, 10 ], [ 4, 5, 7, 8 ], [ 1, 6, 9, 10 ], [ 1, 6, 8, 9 ],
      [ 3, 6, 9, 10 ], [ 2, 6, 7, 9 ], [ 2, 4, 5, 8 ], [ 3, 5, 6, 10 ],
      [ 1, 2, 3, 10 ], [ 4, 6, 7, 10 ], [ 2, 4, 6, 7 ], [ 4, 8, 9, 10 ],
      [ 2, 3, 6, 9 ], [ 1, 2, 4, 8 ], [ 2, 4, 6, 10 ], [ 2, 4, 7, 8 ],
      [ 1, 8, 9, 10 ], [ 1, 4, 6, 9 ], [ 3, 5, 9, 10 ], [ 1, 3, 4, 10 ],
      [ 2, 5, 8, 9 ], [ 2, 4, 5, 6 ], [ 1, 2, 6, 10 ], [ 2, 4, 7, 10 ],
      [ 1, 4, 5, 7 ], [ 2, 4, 5, 7 ], [ 6, 8, 9, 10 ], [ 1, 3, 4, 8 ],
      [ 1, 5, 6, 9 ], [ 1, 2, 4, 9 ], [ 1, 2, 4, 6 ], [ 3, 4, 6, 8 ],
      [ 1, 3, 5, 6 ], [ 1, 3, 9, 10 ], [ 3, 5, 7, 8 ], [ 1, 3, 4, 7 ],
      [ 3, 7, 8, 10 ], [ 2, 6, 8, 9 ], [ 4, 7, 8, 9 ], [ 4, 5, 6, 10 ],
      [ 1, 2, 6, 7 ], [ 7, 8, 9, 10 ], [ 1, 3, 7, 8 ], [ 2, 5, 6, 10 ],
      [ 3, 4, 6, 9 ], [ 1, 4, 9, 10 ], [ 2, 3, 8, 9 ], [ 3, 4, 7, 8 ],
      [ 1, 3, 5, 7 ], [ 2, 5, 6, 9 ], [ 2, 3, 4, 6 ], [ 1, 4, 8, 10 ],
      [ 3, 6, 8, 9 ], [ 3, 4, 8, 9 ], [ 1, 5, 6, 10 ], [ 2, 3, 9, 10 ],
      [ 1, 4, 8, 9 ], [ 4, 7, 8, 10 ], [ 4, 5, 8, 10 ], [ 1, 7, 8, 10 ],
      [ 3, 6, 7, 8 ], [ 2, 5, 9, 10 ], [ 1, 4, 7, 10 ], [ 2, 4, 5, 9 ],
      [ 4, 5, 6, 8 ], [ 1, 7, 8, 9 ], [ 3, 5, 6, 8 ], [ 1, 3, 6, 10 ],
      [ 1, 2, 6, 8 ], [ 2, 6, 9, 10 ], [ 2, 7, 9, 10 ], [ 4, 7, 9, 10 ],
      [ 2, 4, 5, 10 ], [ 2, 3, 5, 10 ], [ 1, 3, 7, 10 ], [ 2, 5, 6, 8 ],
      [ 1, 6, 7, 10 ], [ 2, 3, 4, 9 ], [ 1, 3, 5, 10 ], [ 1, 2, 9, 10 ],
      [ 2, 3, 5, 7 ], [ 1, 4, 6, 7 ], [ 4, 5, 6, 9 ], [ 1, 4, 7, 9 ],
      [ 1, 4, 5, 6 ], [ 1, 7, 9, 10 ], [ 2, 4, 9, 10 ], [ 6, 7, 9, 10 ],
      [ 1, 4, 7, 8 ], [ 2, 3, 4, 10 ], [ 1, 2, 5, 8 ], [ 1, 2, 3, 5 ],
      [ 2, 4, 8, 9 ], [ 1, 2, 4, 10 ], [ 2, 3, 5, 9 ], [ 4, 6, 8, 10 ],
      [ 2, 6, 7, 10 ], [ 4, 6, 7, 8 ], [ 3, 4, 5, 6 ], [ 1, 3, 7, 9 ],
      [ 1, 2, 7, 8 ], [ 2, 3, 4, 7 ], [ 1, 2, 5, 6 ], [ 3, 4, 8, 10 ],
      [ 2, 4, 8, 10 ], [ 2, 6, 7, 8 ], [ 3, 4, 5, 7 ], [ 1, 4, 5, 10 ],
      [ 4, 5, 9, 10 ], [ 1, 6, 7, 9 ], [ 3, 4, 9, 10 ], [ 1, 2, 5, 10 ],
      [ 3, 4, 7, 10 ], [ 1, 4, 5, 8 ], [ 5, 6, 9, 10 ], [ 1, 2, 7, 9 ],
      [ 2, 3, 5, 8 ], [ 2, 3, 7, 8 ], [ 1, 3, 4, 6 ], [ 1, 3, 5, 9 ],
      [ 3, 7, 9, 10 ], [ 4, 6, 7, 9 ], [ 3, 4, 5, 10 ], [ 1, 4, 5, 9 ],
      [ 2, 4, 7, 9 ], [ 2, 5, 7, 8 ], [ 3, 4, 6, 10 ], [ 1, 5, 6, 8 ],
      [ 3, 4, 5, 9 ], [ 1, 2, 4, 7 ], [ 5, 6, 8, 9 ], [ 1, 5, 7, 8 ],
      [ 1, 2, 3, 9 ], [ 1, 3, 8, 9 ], [ 1, 2, 3, 8 ], [ 1, 3, 6, 9 ],
      [ 1, 2, 5, 7 ], [ 1, 2, 3, 7 ], [ 1, 3, 4, 9 ], [ 1, 5, 9, 10 ],
      [ 5, 6, 8, 10 ], [ 2, 3, 6, 10 ], [ 1, 2, 7, 10 ], [ 1, 3, 5, 8 ],
      [ 1, 3, 8, 10 ], [ 2, 6, 8, 10 ], [ 2, 8, 9, 10 ], [ 2, 5, 6, 7 ],
      [ 1, 2, 8, 10 ], [ 2, 3, 6, 7 ], [ 3, 4, 7, 9 ], [ 5, 6, 7, 8 ],
      [ 1, 5, 8, 10 ], [ 2, 5, 8, 10 ], [ 4, 5, 6, 7 ], [ 3, 5, 6, 7 ],
      [ 3, 5, 6, 9 ], [ 4, 5, 8, 9 ] ],
  [ [ 2, 4, 5 ], [ 6, 8, 10 ], [ 1, 3, 4 ], [ 2, 3, 8 ], [ 1, 4, 6 ],
      [ 4, 6, 10 ], [ 2, 6, 8 ], [ 2, 4, 6 ], [ 2, 4, 8 ], [ 1, 8, 9 ],
      [ 4, 8, 10 ], [ 5, 8, 9 ], [ 3, 4, 8 ], [ 3, 7, 8 ], [ 1, 6, 9 ],
      [ 2, 4, 9 ], [ 8, 9, 10 ], [ 7, 9, 10 ], [ 1, 5, 8 ], [ 3, 6, 8 ],
      [ 1, 3, 6 ], [ 2, 5, 9 ], [ 1, 2, 9 ], [ 2, 3, 5 ], [ 1, 6, 10 ],
      [ 4, 8, 9 ], [ 4, 7, 8 ], [ 1, 9, 10 ], [ 4, 6, 9 ], [ 4, 9, 10 ],
      [ 1, 4, 8 ], [ 7, 8, 10 ], [ 1, 4, 9 ], [ 2, 5, 8 ], [ 2, 9, 10 ],
      [ 2, 6, 9 ], [ 4, 7, 9 ], [ 1, 4, 5 ], [ 1, 7, 10 ], [ 1, 2, 7 ],
      [ 3, 4, 9 ], [ 1, 2, 6 ], [ 4, 6, 8 ], [ 2, 6, 10 ], [ 2, 8, 9 ],
      [ 1, 2, 10 ], [ 1, 2, 4 ], [ 3, 5, 9 ], [ 4, 5, 8 ], [ 5, 6, 10 ],
      [ 2, 3, 10 ], [ 3, 7, 10 ], [ 4, 6, 7 ], [ 7, 8, 9 ], [ 5, 6, 8 ],
      [ 3, 4, 6 ], [ 1, 6, 8 ], [ 2, 4, 10 ], [ 6, 7, 10 ], [ 2, 4, 7 ],
      [ 3, 4, 5 ], [ 1, 3, 7 ], [ 3, 8, 10 ], [ 6, 7, 8 ], [ 6, 8, 9 ],
      [ 4, 5, 6 ], [ 3, 5, 10 ], [ 2, 3, 9 ], [ 6, 9, 10 ], [ 4, 5, 7 ],
      [ 4, 5, 10 ], [ 2, 5, 10 ], [ 3, 6, 9 ], [ 1, 3, 10 ], [ 1, 2, 8 ],
      [ 2, 3, 6 ], [ 1, 2, 5 ], [ 3, 9, 10 ], [ 5, 7, 8 ], [ 5, 9, 10 ],
      [ 1, 5, 9 ], [ 1, 4, 10 ], [ 3, 8, 9 ], [ 1, 3, 8 ], [ 1, 2, 3 ],
      [ 1, 3, 9 ], [ 3, 5, 8 ], [ 3, 4, 10 ], [ 1, 7, 9 ], [ 1, 5, 6 ],
      [ 2, 7, 8 ], [ 3, 4, 7 ], [ 1, 5, 7 ], [ 1, 8, 10 ], [ 4, 7, 10 ],
      [ 3, 6, 7 ], [ 1, 4, 7 ], [ 2, 5, 7 ], [ 1, 7, 8 ], [ 2, 3, 7 ],
      [ 4, 5, 9 ], [ 5, 6, 9 ], [ 2, 3, 4 ], [ 1, 3, 5 ], [ 6, 7, 9 ],
      [ 3, 7, 9 ], [ 1, 6, 7 ], [ 2, 7, 9 ], [ 3, 6, 10 ], [ 2, 6, 7 ],
      [ 2, 8, 10 ], [ 2, 5, 6 ], [ 1, 5, 10 ], [ 2, 7, 10 ], [ 3, 5, 6 ],
      [ 5, 8, 10 ], [ 3, 5, 7 ], [ 5, 6, 7 ] ],
  [ [ 4, 6 ], [ 2, 6 ], [ 2, 10 ], [ 4, 8 ], [ 6, 10 ], [ 4, 9 ], [ 5, 8 ],
      [ 1, 8 ], [ 4, 10 ], [ 7, 8 ], [ 6, 8 ], [ 5, 9 ], [ 4, 5 ], [ 1, 7 ],
      [ 8, 10 ], [ 1, 4 ], [ 8, 9 ], [ 1, 9 ], [ 3, 5 ], [ 1, 6 ], [ 3, 4 ],
      [ 2, 8 ], [ 3, 6 ], [ 2, 4 ], [ 2, 9 ], [ 4, 7 ], [ 3, 8 ], [ 1, 3 ],
      [ 1, 2 ], [ 2, 3 ], [ 3, 7 ], [ 2, 5 ], [ 1, 10 ], [ 3, 10 ], [ 6, 7 ],
      [ 7, 10 ], [ 3, 9 ], [ 6, 9 ], [ 9, 10 ], [ 7, 9 ], [ 1, 5 ], [ 5, 7 ],
      [ 5, 6 ], [ 2, 7 ], [ 5, 10 ] ],
  [ [ 9 ], [ 4 ], [ 5 ], [ 6 ], [ 3 ], [ 8 ], [ 10 ], [ 1 ], [ 2 ], [ 7 ] ] ]
gap> g1 := Transformation([1, 4, 11, 11, 7, 2, 6, 2, 5, 5, 10]);;
gap> g2 := Transformation([2, 4, 4, 2, 10, 5, 11, 11, 11, 6, 7]);;
gap> m10 := Monoid(g1, g2);;
gap> g1 := Transformation([10, 8, 7, 4, 1, 4, 10, 10, 7, 2]);;
gap> g2 := Transformation([5, 2, 5, 5, 9, 10, 8, 3, 8, 10]);;
gap> m12 := Monoid(g1, g2);;
gap> g1 := Transformation([2, 1, 4, 5, 3, 7, 8, 9, 10, 6]);;
gap> g2 := Transformation([1, 2, 4, 3, 5, 6, 7, 8, 9, 10]);;
gap> g3 := Transformation([1, 2, 3, 4, 5, 6, 10, 9, 8, 7]);;
gap> g4 := Transformation([9, 1, 4, 3, 6, 9, 3, 4, 3, 9]);;
gap> m13 := Monoid(g1, g2, g3, g4);;
gap> g1 := Transformation([13, 10, 9, 5, 1, 5, 13, 13, 8, 2, 7, 2, 6]);;
gap> g2 := Transformation([6, 11, 12, 10, 4, 10, 13, 5, 8, 5, 11, 6, 9]);;
gap> m16 := Semigroup(g1, g2);;
gap> g1 := Transformation([12, 10, 8, 5, 1, 5, 12, 12, 8, 2, 6, 2]);;
gap> g2 := Transformation([5, 6, 10, 11, 10, 4, 10, 12, 5, 7, 4, 10]);;
gap> g3 := Transformation([6, 8, 12, 5, 4, 8, 10, 7, 4, 1, 10, 11]);;
gap> m17 := Monoid(g1, g2, g3);;
gap> g1 := Transformation([2, 3, 4, 5, 1, 8, 7, 6, 2, 7]);;
gap> g2 := Transformation([5, 4, 1, 2, 3, 7, 6, 5, 4, 1]);;
gap> g3 := Transformation([2, 1, 4, 3, 2, 1, 4, 4, 3, 3]);;
gap> m19 := Monoid(g1, g2, g3);;
gap> g1 := Transformation([2, 3, 4, 5, 1, 8, 7, 6, 2, 7]);;
gap> g2 := Transformation([2, 3, 4, 5, 6, 8, 7, 1, 2, 2]);;
gap> m20 := Monoid(g1, g2);;
gap> g1 := Transformation([2, 3, 4, 5, 1, 8, 7, 6, 2, 7]);;
gap> g2 := Transformation([3, 8, 7, 4, 1, 4, 3, 3, 7, 2]);;
gap> m21 := Monoid(g1, g2);;
gap> BigMonoids := [m10, m12, m13, m16, m17, m19, m20, m21];;
gap> g1 := Transformation([2, 2, 4, 4, 5, 6]);;
gap> g2 := Transformation([5, 3, 4, 4, 6, 6]);;
gap> m1 := Monoid(g1, g2);;
gap> g1 := Transformation([5, 4, 4, 2, 1]);;
gap> g2 := Transformation([2, 5, 5, 4, 1]);;
gap> m2 := Monoid(g1, g2);;
gap> g1 := Transformation([1, 2, 1, 3, 3]);;
gap> g2 := Transformation([2, 2, 3, 5, 5]);;
gap> m3 := Monoid(g1, g2);;
gap> g1 := Transformation([8, 7, 5, 3, 1, 3, 8, 8]);;
gap> g2 := Transformation([5, 1, 4, 1, 4, 4, 7, 8]);;
gap> m4 := Monoid(g1, g2);;
gap> g1 := Transformation([3, 1, 2, 3, 2, 3, 2, 3]);;
gap> g2 := Transformation([2, 5, 8, 5, 2, 5, 7, 8]);;
gap> m5 := Monoid(g1, g2);;
gap> g1 := Transformation([3, 3, 2, 6, 2, 4, 4, 6]);;
gap> g2 := Transformation([5, 1, 7, 8, 7, 5, 8, 1]);;
gap> m6 := Semigroup(g1, g2);;
gap> g1 := Transformation([3, 3, 2, 6, 2, 4, 4, 6, 3, 4, 6]);;
gap> g2 := Transformation([4, 4, 6, 1, 3, 3, 3, 3, 11, 11, 11]);;
gap> m7 := Monoid(g1, g2);;  # (this is a good example!)
gap> g1 := Transformation([3, 3, 2, 6, 2, 4, 4, 6, 3, 4, 6]);;
gap> g2 := Transformation([4, 4, 6, 1, 3, 3, 3, 3, 11, 11, 11]);;
gap> g3 := Transformation([2, 2, 3, 4, 4, 6, 6, 6, 6, 6, 11]);;
gap> m8 := Monoid(g1, g2, g3);;
gap> g1 := Transformation([3, 3, 2, 6, 2, 4, 4, 6, 3, 4, 6]);;
gap> g2 := Transformation([4, 4, 6, 1, 3, 3, 3, 3, 11, 11, 11]);;
gap> g3 := Transformation([2, 2, 3, 4, 4, 6, 6, 6, 6, 6, 11]);;
gap> g4 := Transformation([2, 2, 3, 4, 4, 6, 6, 6, 6, 11, 11]);;
gap> m9 := Monoid(g1, g2, g3, g4);;
gap> g1 := Transformation([12, 3, 6, 4, 6, 11, 9, 6, 6, 7, 6, 12]);;
gap> g2 := Transformation([10, 7, 2, 11, 7, 3, 12, 4, 3, 8, 7, 5]);;
gap> m11 := Monoid(g1, g2);;
gap> g1 := Transformation([3, 2, 12, 2, 7, 9, 4, 2, 1, 12, 11, 12]);;
gap> g2 := Transformation([3, 6, 12, 7, 2, 2, 3, 6, 1, 7, 11, 1]);;
gap> m14 := Monoid(g1, g2);;
gap> g1 := Transformation([2, 2, 3, 4, 5, 6]);;
gap> g2 := Transformation([2, 3, 4, 5, 6, 1]);;
gap> m15 := Monoid(g1, g2);;
gap> g1 := Transformation([2, 1, 4, 5, 6, 7, 3, 2, 1]);;
gap> g2 := Transformation([2, 1, 4, 2, 1, 4, 2, 1, 4]);;
gap> m18 := Monoid(g1, g2);;
gap> g1 := Transformation([5, 2, 5, 5, 8, 10, 8, 5, 2, 10]);;
gap> g2 := Transformation([2, 2, 5, 5, 5, 8, 8, 8, 8, 8]);;
gap> m22 := Monoid(g1, g2);;
gap> g1 := Transformation([4, 6, 3, 8, 5, 6, 10, 4, 3, 7]);;
gap> g2 := Transformation([5, 6, 6, 3, 8, 6, 3, 7, 8, 4]);;
gap> g3 := Transformation([8, 6, 3, 2, 8, 10, 9, 2, 6, 2]);;
gap> m23 := Monoid(g1, g2, g3);;
gap> SmallMonoids :=
> [m1, m2, m3, m4, m5, m6, m7, m8, m9, m11, m14, m15, m18, m22, m23];;
gap> List(SmallMonoids, IsCompletelyRegularSemigroup);
[ false, true, false, false, true, true, true, true, true, false, false,
  false, false, true, false ]
gap> List(BigMonoids, IsCompletelyRegularSemigroup);
[ true, false, false, false, false, false, true, false ]
gap> g1 := Transformation([3, 3, 2, 6, 2, 4, 4, 6]);;
gap> g2 := Transformation([5, 1, 7, 8, 7, 5, 8, 1]);;
gap> cs1 := Semigroup(g1, g2);;
gap> IsCompletelySimpleSemigroup(cs1);
true
gap> g1 := Transformation([2, 3, 4, 5, 1, 8, 7, 6, 2, 7]);;
gap> g2 := Transformation([2, 3, 4, 5, 6, 8, 7, 1, 2, 2]);;
gap> cs2 := Semigroup(g1, g2);;
gap> IsCompletelySimpleSemigroup(cs2);
true
gap> g1 := Transformation([2, 1, 1, 2, 1]);;
gap> g2 := Transformation([3, 4, 3, 4, 4]);;
gap> g3 := Transformation([3, 4, 3, 4, 3]);;
gap> g4 := Transformation([4, 3, 3, 4, 4]);;
gap> cs3 := Semigroup(g1, g2, g3, g4);;
gap> IsCompletelySimpleSemigroup(cs3);
true
gap> g1 := Transformation([4, 4, 4, 1, 1, 6, 7, 8, 9, 10, 11, 1]);;
gap> g2 := Transformation([6, 6, 6, 7, 7, 1, 4, 8, 9, 10, 11, 7]);;
gap> g3 := Transformation([8, 8, 8, 9, 9, 10, 11, 1, 4, 6, 7, 9]);;
gap> g4 := Transformation([2, 2, 2, 4, 4, 6, 7, 8, 9, 10, 11, 4]);;
gap> g5 := Transformation([1, 1, 1, 5, 5, 6, 7, 8, 9, 10, 11, 5]);;
gap> g6 := Transformation([1, 1, 4, 4, 4, 6, 7, 8, 9, 10, 11, 1]);;
gap> g7 := Transformation([1, 1, 7, 4, 4, 6, 7, 8, 9, 10, 11, 6]);;
gap> cs4 := Semigroup(g1, g2, g3, g4, g5, g6, g7);;
gap> IsCompletelySimpleSemigroup(cs4);
true
gap> g1 := Transformation([1, 2, 2, 1, 2]);;
gap> g2 := Transformation([3, 4, 3, 4, 4]);;
gap> g3 := Transformation([3, 4, 3, 4, 3]);;
gap> g4 := Transformation([4, 3, 3, 4, 4]);;
gap> cs5 := Semigroup(g1, g2, g3, g4);;
gap> IsCompletelySimpleSemigroup(cs5);
true
gap> dc := GreensDClassOfElement(m14, Transformation(
> [12, 2, 1, 3, 6, 6, 12, 2, 3, 3, 11, 3]));;
gap> dc = MinimalIdeal(m14);
false
gap> dc := GreensDClassOfElement(m9, Transformation(
> [3, 3, 2, 6, 2, 4, 4, 6, 3, 4, 6]));;
gap> d := GreensDClassOfElement(m14, Transformation(
> [12, 2, 1, 3, 6, 6, 12, 2, 3, 3, 11, 3]));;
gap> g := GroupHClassOfGreensDClass(d);;
gap> s := Semigroup(AsList(g));;
gap> IsGroupAsSemigroup(s);
true
gap> IsGroupAsSemigroup(Range(IsomorphismTransformationSemigroup(
>  Group([(2, 4)(3, 5), (1, 2, 3, 5, 4)]))));
true
gap> IsGroupAsSemigroup(m14);
false
gap> List(SmallMonoids, IsCliffordSemigroup);
[ false, true, false, false, false, false, false, false, false, false, false,
  false, false, false, false ]
gap> List(BigMonoids, IsCliffordSemigroup);
[ false, false, false, false, false, false, false, false ]
gap> ForAll(GreensDClasses(m2), x -> Length(GreensHClasses(x)) = 1 and
> IsRegularDClass(x));
true
gap> IsCliffordSemigroup(m2);
true
gap> ForAll(GreensDClasses(m2), x -> Length(GreensHClasses(x)) = 1 and
> IsRegularDClass(x));
true
gap> g1 := Transformation([1, 2, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4,
> 4, 4, 4, 4]);;
gap> g2 := Transformation([1, 2, 3, 4, 5, 6, 7, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4,
> 4, 4, 4, 4]);;
gap> g3 := Transformation([1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 4, 4, 4, 4, 4,
> 4, 4, 4, 4, 4]);;
gap> g4 := Transformation([1, 2, 3, 4, 4, 4, 4, 4, 4, 4, 4, 12, 13, 14, 15,
> 16, 4, 4, 4, 4, 4]);;
gap> g5 := Transformation([1 .. 21]);;
gap> c3 := Semigroup(g1, g2, g3, g4, g5);;
gap> IsCliffordSemigroup(c3);
true
gap> Size(c3);
5
gap> ForAll(GreensDClasses(c3), x -> Length(GreensHClasses(x)) = 1 and
> IsRegularDClass(x));
true
gap> g1 := g1 * (1, 2);;
gap> g2 := Transformation([1, 2, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4,
> 4, 4, 4, 4]) * (1, 2, 3, 4);;
gap> g3 := Transformation([1, 2, 3, 4, 5, 6, 7, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4,
> 4, 4, 4, 4]) * (5, 6);;
gap> g4 := Transformation([1, 2, 3, 4, 5, 6, 7, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4,
> 4, 4, 4, 4]) * (5, 6, 7);;
gap> g5 := Transformation([1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 4, 4, 4, 4, 4,
> 4, 4, 4, 4, 4]) * (8, 9);;
gap> g6 := Transformation([1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 4, 4, 4, 4, 4,
> 4, 4, 4, 4, 4]) * (10, 11);;
gap> g7 := Transformation([1, 2, 3, 4, 4, 4, 4, 4, 4, 4, 4, 12, 13, 14, 15,
> 16, 17, 18, 19, 20, 21]) * (12, 13);;
gap> g8 := Transformation(
> [1, 2, 3, 4, 4, 4, 4, 4, 4, 4, 4, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]) *
> (12, 13, 14, 15, 16);;
gap> g9 := Transformation([1 .. 21]) * (17, 18, 19, 20, 21);;
gap> c4 := Semigroup(g1, g2, g3, g4, g5, g6, g7, g8, g9);;
gap> IsCliffordSemigroup(c4);
true
gap> ForAll(GreensDClasses(c3), x -> Length(GreensHClasses(x)) = 1 and
> IsRegularDClass(x));
true
gap> ForAll(GreensDClasses(c4), x -> Length(GreensHClasses(x)) = 1 and
> IsRegularDClass(x));
true
gap> List(SmallMonoids, IsRegularSemigroup);
[ false, true, false, false, true, true, true, true, true, false, false,
  true, true, true, false ]
gap> List(BigMonoids, IsRegularSemigroup);
[ true, false, false, false, false, true, true, false ]
gap> List([c3, c4], IsInverseSemigroup);
[ true, true ]
gap> IsBand(c3);
true
gap> IsBand(c4);
false
gap> List(SmallMonoids, IsBand);
[ false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false ]
gap> List(BigMonoids, IsBand);
[ false, false, false, false, false, false, false, false ]
gap> g := Group(());;
gap> mat := [[(), (), ()], [(), (), ()], [(), (), ()], [(), (), ()]];;
gap> rms := ReesMatrixSemigroup(g, mat);;
gap> s := Range(IsomorphismTransformationSemigroup(rms));;
gap> IsRectangularBand(s);
true
gap> IsBand(s);
true
gap> IsSemiband(FullTransformationSemigroup(4));
false
gap> Size(Semigroup(Idempotents(FullTransformationSemigroup(4))));
233
gap> 4 ^ 4 - Factorial(4) + 1;
233
gap> ForAll(SmallMonoids, x -> not IsSemiband(x));
true
gap> List(SmallMonoids, IsOrthodoxSemigroup);
[ false, true, false, false, false, false, true, true, true, false, false,
  false, false, true, false ]
gap> s := SmallMonoids[1];
<non-regular transformation monoid of degree 6 with 2 generators>
gap> IsRegularSemigroup(s);
false
gap> IsOrthodoxSemigroup(s);
false
gap> t := Semigroup(Idempotents(s));
<transformation monoid of degree 6 with 3 generators>
gap> Size(t);
4
gap> s := SmallMonoids[7];;
gap> Size(s);;
gap> t := Semigroup(Idempotents(s));;
gap> IsBand(t);
true
gap> IsRectangularBand(t);
false
gap> g := Group(());;
gap> mat := [[(), (), (), (), (), ()]];;
gap> rms := ReesMatrixSemigroup(g, mat);;
gap> s := Range(IsomorphismTransformationSemigroup(rms));;
gap> IsLeftZeroSemigroup(s);
true
gap> IsRightZeroSemigroup(s);
false
gap> mat := TransposedMat(mat);;
gap> rms := ReesMatrixSemigroup(g, mat);;
gap> s := Range(IsomorphismTransformationSemigroup(rms));;
gap> IsRightZeroSemigroup(s);
true
gap> IsLeftZeroSemigroup(s);
false
gap> List(BigMonoids, IsLeftZeroSemigroup);
[ false, false, false, false, false, false, false, false ]
gap> List(BigMonoids, IsRightZeroSemigroup);
[ false, false, false, false, false, false, false, false ]
gap> gens := [Transformation([2, 2, 4, 4, 6, 6, 8, 8, 10, 10, 12, 12, 2]),
> Transformation([1, 1, 3, 3, 5, 5, 7, 7, 9, 9, 11, 11, 3]),
> Transformation([1, 7, 3, 9, 5, 11, 7, 1, 9, 3, 11, 5, 5]),
> Transformation([7, 7, 9, 9, 11, 11, 1, 1, 3, 3, 5, 5, 7])];;
gap> S := Semigroup(gens);;
gap> IsSimpleSemigroup(S);
true
gap> IsCompletelySimpleSemigroup(S);
true
gap> gens := [Transformation([1, 2, 4, 3, 6, 5, 4]),
> Transformation([1, 2, 5, 6, 3, 4, 5]),
> Transformation([2, 1, 2, 2, 2, 2, 2])];;
gap> S := Semigroup(gens);;
gap> IsCompletelyRegularSemigroup(S);
true
gap> gens := [Transformation([2, 4, 5, 3, 7, 8, 6, 9, 1]),
> Transformation([3, 5, 6, 7, 8, 1, 9, 2, 4])];;
gap> S := Semigroup(gens);;
gap> IsGroupAsSemigroup(S);
true
gap> IsCommutativeSemigroup(S);
true
gap> gens := [Transformation([1, 2, 4, 5, 6, 3, 7, 8]),
> Transformation([3, 3, 4, 5, 6, 2, 7, 8]),
> Transformation([1, 2, 5, 3, 6, 8, 4, 4])];;
gap> S := Semigroup(gens);;
gap> IsCliffordSemigroup(S);
true
gap> gens := [Transformation([1, 1, 1, 4, 4, 4, 7, 7, 7, 1]),
> Transformation([2, 2, 2, 5, 5, 5, 8, 8, 8, 2]),
> Transformation([3, 3, 3, 6, 6, 6, 9, 9, 9, 3]),
> Transformation([1, 1, 1, 4, 4, 4, 7, 7, 7, 4]),
> Transformation([1, 1, 1, 4, 4, 4, 7, 7, 7, 7])];;
gap> S := Semigroup(gens);;
gap> IsBand(S);
true
gap> IsRectangularBand(S);
true
gap> S := FullTransformationSemigroup(4);;
gap> x := Transformation([1, 2, 3, 1]);;
gap> D := GreensDClassOfElement(S, x);;
gap> T := Semigroup(Elements(D));;
gap> IsSemiband(T);
true
gap> gens := [Transformation([1, 1, 1, 4, 5, 4]),
>  Transformation([1, 2, 3, 1, 1, 2]),
>  Transformation([1, 2, 3, 1, 1, 3]),
>  Transformation([5, 5, 5, 5, 5, 5])];;
gap> S := Semigroup(gens);;
gap> IsOrthodoxSemigroup(S);
true
gap> gens := [Transformation([2, 1, 4, 3, 5]),
>  Transformation([3, 2, 3, 1, 1])];;
gap> S := Semigroup(gens);;
gap> IsRightZeroSemigroup(S);
false
gap> gens := [Transformation([1, 2, 3, 3, 1]),
>  Transformation([1, 2, 4, 4, 1])];;
gap> S := Semigroup(gens);;
gap> IsRightZeroSemigroup(S);
true
gap> gens := [Transformation([2, 1, 4, 3, 5]),
>  Transformation([3, 2, 3, 1, 1])];;
gap> S := Semigroup(gens);;
gap> IsRightZeroSemigroup(S);
false
gap> gens := [Transformation([1, 2, 3, 3, 1]),
>  Transformation([1, 2, 3, 3, 3])];;
gap> S := Semigroup(gens);;
gap> IsLeftZeroSemigroup(S);
true
gap> gens := [Transformation([4, 7, 6, 3, 1, 5, 3, 6, 5, 9]),
>  Transformation([5, 3, 5, 1, 9, 3, 8, 7, 4, 3]),
>  Transformation([5, 10, 10, 1, 7, 6, 6, 8, 7, 7]),
>  Transformation([7, 4, 3, 3, 2, 2, 3, 2, 9, 3]),
>  Transformation([8, 1, 3, 4, 9, 6, 3, 7, 1, 6])];;
gap> S := Semigroup(gens);;
gap> IsZeroSemigroup(S);
false
gap> gens := [Transformation([1, 4, 2, 6, 6, 5, 2]),
> Transformation([1, 6, 3, 6, 2, 1, 6])];;
gap> S := Semigroup(gens);;
gap> MultiplicativeZero(S);
Transformation( [ 1, 1, 1, 1, 1, 1, 1 ] )

#
gap> SEMIGROUPS.StopTest();
gap> STOP_TEST("Semigroups package: extreme/monoid_pkg.tst");
