#############################################################################
##
##  semigroups/semipperm.gi
##  Copyright (C) 2013-2022                              James D. Mitchell
##
##  Licensing information can be found in the README file of this package.
##
#############################################################################
##

# This file contains methods for every operation/attribute/property that is
# specific to semigroups of partial perms.

#############################################################################
## Random
#############################################################################

InstallMethod(SEMIGROUPS_ProcessRandomArgsCons,
[IsPartialPermSemigroup, IsList],
function(filt, params)
  return SEMIGROUPS_ProcessRandomArgsCons(IsSemigroup, params);
end);

InstallMethod(SEMIGROUPS_ProcessRandomArgsCons,
[IsPartialPermMonoid, IsList],
function(filt, params)
  return SEMIGROUPS_ProcessRandomArgsCons(IsSemigroup, params);
end);

InstallMethod(RandomSemigroupCons, "for IsPartialPermSemigroup and a list",
[IsPartialPermSemigroup, IsList],
function(filt, params)
  return Semigroup(List([1 .. params[1]],
                        i -> UniformRandomPartialPerm(params[2])));
end);

InstallMethod(RandomMonoidCons, "for IsPartialPermMonoid and a list",
[IsPartialPermMonoid, IsList],
function(filt, params)
  return Monoid(List([1 .. params[1]],
                     i -> UniformRandomPartialPerm(params[2])));
end);

InstallMethod(RandomInverseSemigroupCons,
"for IsPartialPermSemigroup and a list",
[IsPartialPermSemigroup, IsList],
function(filt, params)
  return InverseSemigroup(List([1 .. params[1]],
                               i -> UniformRandomPartialPerm(params[2])));
end);

InstallMethod(RandomInverseMonoidCons,
"for IsPartialPermMonoid and a list",
[IsPartialPermMonoid, IsList],
function(filt, params)
  return InverseMonoid(List([1 .. params[1]],
                            i -> UniformRandomPartialPerm(params[2])));
end);

#############################################################################
## Operators
#############################################################################

InstallMethod(\<, "for partial perm semigroups",
[IsPartialPermSemigroup, IsPartialPermSemigroup],
function(S, T)
  if DegreeOfPartialPermSemigroup(S)
      <> DegreeOfPartialPermSemigroup(T)
      or CodegreeOfPartialPermSemigroup(S)
      <> CodegreeOfPartialPermSemigroup(T) then
    return DegreeOfPartialPermSemigroup(S)
      < DegreeOfPartialPermSemigroup(T) or
      (DegreeOfPartialPermSemigroup(S)
       = DegreeOfPartialPermSemigroup(T)
       and CodegreeOfPartialPermSemigroup(S)
       < CodegreeOfPartialPermSemigroup(T));
  fi;
  TryNextMethod();
end);

#############################################################################
## Isomorphisms
#############################################################################

InstallMethod(IsomorphismSemigroup,
"for IsPartialPermSemigroup and a semigroup",
[IsPartialPermSemigroup, IsSemigroup],
function(filt, S)
  return IsomorphismPartialPermSemigroup(S);
end);

InstallMethod(IsomorphismMonoid,
"for IsPartialPermMonoid and a semigroup",
[IsPartialPermMonoid, IsSemigroup],
function(filt, S)
  return IsomorphismPartialPermMonoid(S);
end);

InstallMethod(IsomorphismPartialPermSemigroup,
"for a bipartition semigroup with generators",
[IsBipartitionSemigroup and HasGeneratorsOfSemigroup],
function(S)
  local T, n;

  if not ForAll(GeneratorsOfSemigroup(S), IsPartialPermBipartition) then
    TryNextMethod();
  fi;

  T := Semigroup(List(GeneratorsOfSemigroup(S), AsPartialPerm));
  UseIsomorphismRelation(S, T);
  n := DegreeOfBipartitionSemigroup(S);
  return SemigroupIsomorphismByFunctionNC(S,
                                          T,
                                          AsPartialPerm,
                                          x -> AsBipartition(x, n));
end);

InstallMethod(IsomorphismPartialPermSemigroup,
"for bipartition inverse semigroup with generators",
[IsBipartitionSemigroup and IsInverseSemigroup and
 HasGeneratorsOfInverseSemigroup],
function(S)
  local T, n;

  if not ForAll(GeneratorsOfInverseSemigroup(S),
                IsPartialPermBipartition) then
    TryNextMethod();
  fi;

  T := InverseSemigroup(List(GeneratorsOfInverseSemigroup(S),
                             AsPartialPerm));
  UseIsomorphismRelation(S, T);
  n := DegreeOfBipartitionSemigroup(S);

  return SemigroupIsomorphismByFunctionNC(S,
                                          T,
                                          AsPartialPerm,
                                          x -> AsBipartition(x, n));
end);

InstallMethod(IsomorphismPartialPermSemigroup, "for a semigroup ideal",
[IsSemigroupIdeal and HasGeneratorsOfSemigroupIdeal],
function(I)
  local iso, inv, J;

  iso := IsomorphismPartialPermSemigroup(SupersemigroupOfIdeal(I));
  inv := InverseGeneralMapping(iso);
  J := SemigroupIdeal(Range(iso), Images(iso, GeneratorsOfSemigroupIdeal(I)));
  UseIsomorphismRelation(I, J);

  return SemigroupIsomorphismByFunctionNC(I, J, x -> x ^ iso, x -> x ^ inv);
end);

InstallMethod(IsomorphismPartialPermSemigroup, "for a group as semigroup",
[IsGroupAsSemigroup],
function(G)
  local perm_iso, perm_inv, perm_grp, pperm_iso, pperm_inv;

  if IsPartialPermSemigroup(G) then
    TryNextMethod();
  fi;

  perm_iso := IsomorphismPermGroup(G);
  perm_inv := InverseGeneralMapping(perm_iso);
  perm_grp := Range(perm_iso);
  GeneratorsOfGroup(perm_grp);  # to make sure that the following line calls
                                # the library method for IsPermGroup and
                                # HasGensOfGp
  pperm_iso := IsomorphismPartialPermSemigroup(perm_grp);
  pperm_inv := InverseGeneralMapping(pperm_iso);
  return SemigroupIsomorphismByFunctionNC(G,
                                          Range(pperm_iso),
                                          x -> (x ^ perm_iso) ^ pperm_iso,
                                          x -> (x ^ pperm_inv) ^ perm_inv);
end);

InstallMethod(IsomorphismPartialPermSemigroup,
"for a group with adjoined zero",
[IsMagmaWithZeroAdjoined and IsZeroGroup],
function(S)
  local zero, inj_zm, inv_zm, grp, one, iso, inv, T, iso_pp, inv_pp;

  zero := MultiplicativeZero(S);
  inj_zm := UnderlyingInjectionZeroMagma(S);
  inv_zm := InverseGeneralMapping(inj_zm);
  grp := Source(inj_zm);

  if IsTrivial(grp) then
    # Special case: if <grp> is trivial, then `IsomorphismPartialPermSemigroup`
    # will map to <{EmptyPartialPerm}>, to which we can't easily adjoin a zero.
    one := MultiplicativeNeutralElement(S);  # S = {zero, one}
    iso := function(x)
      if x = zero then
        return EmptyPartialPerm();
      fi;
      return PartialPerm([1]);
    end;
    inv := function(x)
      if DegreeOfPartialPerm(x) = 0 then
        return zero;
      fi;
      return one;
    end;
    T := SymmetricInverseSemigroup(1);
    return SemigroupIsomorphismByFunctionNC(S, T, iso, inv);
  fi;

  iso_pp := IsomorphismPartialPermSemigroup(grp);
  inv_pp := InverseGeneralMapping(iso_pp);
  T := InverseMonoid(GeneratorsOfInverseSemigroup(Range(iso_pp)),
                     EmptyPartialPerm());

  iso := function(x)
    if x = zero then
      return EmptyPartialPerm();
    fi;
    return (x ^ inv_zm) ^ iso_pp;
  end;

  inv := function(x)
    if DegreeOfPartialPerm(x) = 0 then
      return zero;
    fi;
    return (x ^ inv_pp) ^ inj_zm;
  end;

  return SemigroupIsomorphismByFunctionNC(S, T, iso, inv);
end);

# The next method is copied directly from the GAP library the only change is
# the return value which uses SemigroupHomomorphismByFunction here but
# MagmaIsomorphismByFunctionNC in the GAP library.

InstallMethod(IsomorphismPartialPermSemigroup, "for a semigroup",
[IsSemigroup],
function(S)
  local set, iso, gens, T;

  if not IsInverseSemigroup(S) then
    ErrorNoReturn("the argument must be an inverse semigroup");
  fi;

  set := AsSet(S);

  iso := function(x)
    local dom;
    dom := Set(set * InversesOfSemigroupElement(S, x)[1]);
    return PartialPermNC(List(dom, y -> Position(set, y)),
                         List(List(dom, y -> y * x),
                              y -> Position(set, y)));
  end;

  gens := GeneratorsOfSemigroup(S);

  T := InverseSemigroup(List(gens, iso));
  UseIsomorphismRelation(S, T);

  return SemigroupHomomorphismByFunctionNC(S, T, iso);
end);

# The next method is copied directly from the GAP library the only change is
# the return value which uses SemigroupIsomorphismByFunctionNC here but
# MagmaIsomorphismByFunctionsNC in the GAP library.

InstallMethod(IsomorphismPartialPermSemigroup, "for a partial perm semigroup",
[IsPartialPermSemigroup],
S -> SemigroupIsomorphismByFunctionNC(S, S, IdFunc, IdFunc));

InstallMethod(SmallerDegreePartialPermRepresentation,
"for an inverse semigroup with inverse op",
[IsInverseSemigroup and IsGeneratorsOfInverseSemigroup],
function(S)
  local map1, map2;
  map1 := IsomorphismPartialPermSemigroup(S);
  map2 := SmallerDegreePartialPermRepresentation(Range(map1));
  return CompositionMapping(map2, map1);
end);

InstallMethod(SmallerDegreePartialPermRepresentation,
"for an inverse semigroup of partial permutations",
[IsInverseSemigroup and IsPartialPermSemigroup],
function(S)
  local oldgens, newgens, D, e, h, lambdaorb, He, sup, trivialse, schutz,
  sigmainv, enum, orbits, cosets, stabpp, psi, rho, rhoinv, stab, nrcosets, j,
  reps, gen, offset, rep, box, subbox, T, map, inv, d, k, i, m;

  oldgens := GeneratorsOfSemigroup(S);
  newgens := List(oldgens, x -> []);
  D := JoinIrreducibleDClasses(S);

  for d in D do
    e := RightOne(Representative(d));

    # Generate representatives for all the H-Classes in the R-Class of He
    h := HClassReps(GreensRClassOfElement(d, e));
    lambdaorb := List(h, ImageSetOfPartialPerm);

    He := GreensHClassOfElementNC(S, e);
    sup := SupremumIdempotentsNC(Minorants(S, e), e);
    trivialse := not ForAny(He, x -> NaturalLeqInverseSemigroup(S)(sup, x)
                                     and x <> e);

    if IsActingSemigroup(S) then
      schutz := SchutzenbergerGroup(He);
      sigmainv := x -> x ^ InverseGeneralMapping(IsomorphismPermGroup(He));
    else
      schutz := Group(());
      enum := Enumerator(He);
      for k in enum do
        schutz := ClosureGroup(schutz, AsPermutation(k));
      od;
      sigmainv := x -> AsPartialPerm(x, DomainOfPartialPerm(e));
    fi;

    ##  Se is the subgroup of He whose elements have the same minorants as e
    if trivialse then
      orbits := [[ActionDegree(He) + 1]];
      cosets := [e];
      stabpp := He;
    else
      psi := ActionHomomorphism(schutz,
                                Difference(DomainOfPartialPerm(e),
                                           DomainOfPartialPerm(sup)));
      rho := SmallerDegreePermutationRepresentation(Image(psi));
      rhoinv := InverseGeneralMapping(rho);
      orbits := Orbits(Image(rho));
    fi;

    for i in orbits do
      if not trivialse then
        stab := ImagesSet(InverseGeneralMapping(psi),
                          ImagesSet(rhoinv, Stabilizer(Image(rho), i[1])));
        cosets := RightTransversal(schutz, stab);
        stabpp := Set(stab, sigmainv);
      fi;

      # Generate representatives for ALL the cosets the generator will act on
      # Divide every H-Class in the R-Class into 'cosets' like stab in He
      nrcosets := Size(h) * Length(cosets);
      j := 0;
      reps := EmptyPlist(nrcosets);
      for k in [1 .. Size(h)] do
        for m in [1 .. Length(cosets)] do
          j := j + 1;
          reps[j] := cosets[m] * h[k];
        od;
      od;

      # Loop over old generators of S to calculate its action on the cosets
      for j in [1 .. Length(oldgens)] do
        gen := oldgens[j];
        offset := Length(newgens[j]);

        # Loop over cosets to calculate the image of each under the generator
        for k in [1 .. nrcosets] do
          rep := reps[k] * gen;
          # Will the new generator will be defined at this point?
          if not rep * rep ^ (-1) in stabpp then
            Add(newgens[j], 0);
          else
            box := Position(lambdaorb, ImageSetOfPartialPerm(rep));
            if trivialse then
              subbox := 1;
            else
              # instead of AsPermutation we could do ^ sigma
              subbox := PositionCanonical(cosets,
                                          AsPermutation(rep * h[box] ^ -1));
            fi;
            Add(newgens[j], (box - 1) * Length(cosets) + subbox + offset);
          fi;
        od;
      od;
    od;
  od;
  Apply(newgens, PartialPermNC);
  T := InverseSemigroup(newgens);

  # Return identity mapping if nothing has been accomplished; else the result.
  if NrMovedPoints(T) > NrMovedPoints(S)
      or (NrMovedPoints(T) = NrMovedPoints(S)
          and ActionDegree(T) >= ActionDegree(S)) then
    return IdentityMapping(S);
  fi;

  map := x -> EvaluateWord(newgens, Factorization(S, x));
  inv := x -> EvaluateWord(oldgens, Factorization(T, x));

  return SemigroupIsomorphismByFunctionNC(S, T, map, inv);
end);

#############################################################################
## Algebraic attributes
#############################################################################

InstallMethod(Idempotents, "for a partial perm semigroup and pos int",
[IsPartialPermSemigroup, IsInt],
function(S, rank)
  return Filtered(Idempotents(S), x -> RankOfPartialPerm(x) = rank);
end);

# this should really be in the library

InstallImmediateMethod(GeneratorsOfSemigroup,
IsPartialPermSemigroup and IsGroup and HasGeneratorsOfGroup,
0,
function(G)
  if IsEmpty(GeneratorsOfGroup(G)) then
    # WW: really this should be `return [One(G)];`, but this fails when running
    #     GAP's `tst/testinstall.g` for some reason that I can't figure out.
    TryNextMethod();
  fi;
  return GeneratorsOfGroup(G);
end);

# it just so happens that the MultiplicativeNeutralElement of a semigroup of
# partial permutations has to coincide with the One. This is not the case for
# transformation semigroups

# same method for ideals

InstallMethod(MultiplicativeNeutralElement, "for a partial perm semigroup",
[IsPartialPermSemigroup], One);

# same method for ideals

InstallMethod(GroupOfUnits, "for a partial perm semigroup",
[IsPartialPermSemigroup],
function(S)
  local H, map, inv, G, U, iso;

  if MultiplicativeNeutralElement(S) = fail then
    return fail;
  fi;

  H := GreensHClassOfElementNC(S, MultiplicativeNeutralElement(S));
  map := IsomorphismPermGroup(H);
  inv := InverseGeneralMapping(map);
  G := Range(map);

  U := Semigroup(List(GeneratorsOfGroup(G), x -> x ^ inv));
  SetIsGroupAsSemigroup(U, true);
  UseIsomorphismRelation(U, G);

  iso := SemigroupIsomorphismByFunctionNC(U,
                                          G,
                                          x -> x ^ map,
                                          x -> x ^ inv);
  SetIsomorphismPermGroup(U, iso);

  return U;
end);

# the following method is required to beat the method for
# IsPartialPermCollection in the library.

InstallOtherMethod(One, "for a partial perm semigroup ideal",
[IsPartialPermSemigroup and IsSemigroupIdeal],
function(I)
  local pts, x;

  if HasGeneratorsOfSemigroup(I) then
    x := One(GeneratorsOfSemigroup(I));
    if x in I then
      return x;
    else
      return fail;
    fi;
  fi;

  pts := Union(ComponentsOfPartialPermSemigroup(I));
  x := PartialPermNC(pts, pts);

  if x in I then
    return x;
  fi;
  return fail;
end);

InstallMethod(NaturalLeqInverseSemigroup, "for a partial perm semigroup",
[IsPartialPermSemigroup],
function(S)
  if not IsInverseSemigroup(S) then
    ErrorNoReturn("the argument is not an inverse semigroup");
  fi;
  return NaturalLeqPartialPerm;
end);

#############################################################################
## Degree, rank
#############################################################################

InstallMethod(DegreeOfPartialPermSemigroup,
"for a partial perm semigroup ideal",
[IsPartialPermSemigroup and IsSemigroupIdeal],
function(I)
  local dom;
  dom := DomainOfPartialPermCollection(I);
  if IsEmpty(dom) then
    return 0;
  fi;
  return Maximum(dom);
end);

InstallMethod(CodegreeOfPartialPermSemigroup,
"for a partial perm semigroup ideal",
[IsPartialPermSemigroup and IsSemigroupIdeal],
function(I)
  local im;
  im := ImageOfPartialPermCollection(I);
  if IsEmpty(im) then
    return 0;
  fi;
  return Maximum(im);
end);

InstallMethod(RankOfPartialPermSemigroup,
"for a partial perm semigroup",
[IsPartialPermSemigroup], RankOfPartialPermCollection);

InstallMethod(RankOfPartialPermSemigroup,
"for a partial perm semigroup ideal",
[IsPartialPermSemigroup and IsSemigroupIdeal],
function(I)
  return Length(DomainOfPartialPermCollection(I));
end);

#############################################################################
## Domain, image
#############################################################################

BindGlobal("_DomainImageOfPartialPermIdeal",
function(I, DomainOrImage, InversesOrGenerators)
  local O, S, hash, val, x, y;

  O := DomainOrImage(GeneratorsOfSemigroupIdeal(I));
  S := SupersemigroupOfIdeal(I);
  if O = DomainOrImage(S) then
    return O;
  fi;
  O := ShallowCopy(O);
  hash := HashSet();
  for x in O do
    for y in InversesOrGenerators do
      val := x ^ y;
      if val <> 0 and not val in hash then
        Add(O, val);
        AddSet(hash, val);
      fi;
    od;
  od;
  return Set(O);
end);

InstallMethod(ImageOfPartialPermCollection,
"for a partial perm semigroup ideal",
[IsPartialPermSemigroup and IsSemigroupIdeal],
function(I)
  local S;
  S := SupersemigroupOfIdeal(I);
  return _DomainImageOfPartialPermIdeal(I,
                                        ImageOfPartialPermCollection,
                                        GeneratorsOfSemigroup(S));
end);

InstallMethod(DomainOfPartialPermCollection,
"for a partial perm semigroup ideal",
[IsPartialPermSemigroup and IsSemigroupIdeal],
function(I)
  local S;
  S := SupersemigroupOfIdeal(I);
  return _DomainImageOfPartialPermIdeal(I,
                                        DomainOfPartialPermCollection,
                                        List(GeneratorsOfSemigroup(S),
                                             InverseOp));
end);

#############################################################################
## Action on points
#############################################################################

InstallMethod(FixedPointsOfPartialPermSemigroup,
"for a partial perm semigroup with generators",
[IsPartialPermSemigroup and HasGeneratorsOfSemigroup],
function(S)
  local n, gens;
  n    := DegreeOfPartialPermSemigroup(S);
  gens := GeneratorsOfSemigroup(S);
  return Filtered([1 .. n], i -> ForAll(gens, x -> i ^ x = i));
end);

InstallMethod(FixedPointsOfPartialPermSemigroup,
"for a partial perm semigroup ideal",
[IsPartialPermSemigroup and IsSemigroupIdeal],
function(I)
  local S, F;

  S := SupersemigroupOfIdeal(I);
  F := FixedPointsOfPartialPermSemigroup(S);
  return Intersection(F, DomainOfPartialPermCollection(I));
end);

InstallMethod(DigraphOfActionOnPoints, "for a partial perm semigroup",
[IsPartialPermSemigroup],
S -> DigraphOfActionOnPoints(S, Maximum(DegreeOfPartialPermSemigroup(S),
                                        CodegreeOfPartialPermSemigroup(S))));

InstallMethod(DigraphOfActionOnPoints, "for a partial perm semigroup",
[IsPartialPermSemigroup, IsInt],
function(S, n)
  local gens, out, range, i, x;

  if n < 0 then
    ErrorNoReturn("the 2nd argument (an integer) must be non-negative");
  elif n = 0 then
    return EmptyDigraph(0);
  elif HasDigraphOfActionOnPoints(S)
      and n = Maximum(DegreeOfPartialPermSemigroup(S),
                      CodegreeOfPartialPermSemigroup(S)) then
    return DigraphOfActionOnPoints(S);
  elif IsSemigroupIdeal(S) then
    gens := GeneratorsOfSemigroup(SupersemigroupOfIdeal(S));
  else
    gens := GeneratorsOfSemigroup(S);
  fi;

  out := List([1 .. n], x -> []);
  for i in [1 .. n] do
    for x in gens do
      range := i ^ x;
      if range <= n and range > 0 then
        Add(out[i], range);
      fi;
    od;
  od;
  return DigraphNC(out);
end);

InstallMethod(ComponentRepsOfPartialPermSemigroup,
"for a partial perm semigroup", [IsPartialPermSemigroup],
function(S)
  local D, C;
  D := DigraphMutableCopy(DigraphOfActionOnPoints(S));
  C := DigraphStronglyConnectedComponents(D).comps;
  DigraphRemoveLoops(QuotientDigraph(D, C));
  return List(DigraphSources(D), x -> DigraphVertexLabel(D, x)[1]);
end);

InstallMethod(ComponentsOfPartialPermSemigroup,
"for a partial perm semigroup", [IsPartialPermSemigroup],
function(S)
  return DigraphConnectedComponents(DigraphOfActionOnPoints(S)).comps;
end);

InstallMethod(CyclesOfPartialPermSemigroup,
"for a partial perm semigroup", [IsPartialPermSemigroup],
function(S)
  local D, C, F;
  D := DigraphOfActionOnPoints(S);
  C := DigraphStronglyConnectedComponents(D).comps;
  C := Filtered(C, x -> Size(x) > 1);
  F := FixedPointsOfPartialPermSemigroup(S);
  Append(C, List(F, x -> [x]));
  return C;
end);

InstallMethod(RepresentativeOfMinimalIdealNC,
"for a partial perm semigroup with generators",
[IsPartialPermSemigroup and HasGeneratorsOfSemigroup], 1,
function(S)
  local D, N, stack, Q, M, seen, good, labels, next, result, root, x;

  D := DigraphOfActionOnPoints(S);
  N := Length(GeneratorsOfSemigroup(S));

  # A point occurs in the domain/image of a partial perm in the minimal ideal
  # if and only if no node in D reachable from that point has degree < N.
  # We perform a simple DFS to find such nodes.
  stack := Stack();

  Q := QuotientDigraph(D, DigraphStronglyConnectedComponents(D).comps);
  M := DigraphNrVertices(Q);
  seen := BlistList([1 .. M], []);
  good := BlistList([1 .. M], [1 .. M]);
  labels := DigraphVertexLabels(Q);

  for root in [1 .. M] do
    if not seen[root] then
      Push(stack, root);
      while Size(stack) > 0 do
        next := Pop(stack);
        if next < 0 then
          # Postorder: all neighbours of -next already processed
          next := -next;
          if good[next]
              and ForAny(OutNeighboursOfVertex(Q, next), x -> not good[x]) then
            good[next] := false;
          fi;
        elif not seen[next] then
          seen[next] := true;
          if good[next]
              and ForAny(labels[next],
                         x -> Length(OutNeighboursOfVertex(D, x)) < N) then
            good[next] := false;
          fi;
          # To mark the starting point of the neighbours of next in stack
          Push(stack, -next);
          for x in OutNeighboursOfVertex(Q, next) do
            Push(stack, x);
          od;
        fi;
      od;
    fi;
  od;

  result := [];
  for x in [1 .. M] do
    if good[x] then
      UniteSet(result, labels[x]);
    fi;
  od;

  # Minimal ideal contains an idempotent!
  return PartialPermNC(result, result);
end);
