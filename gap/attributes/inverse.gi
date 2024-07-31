#############################################################################
##
##  attributes/inverse.gi
##  Copyright (C) 2013-2022                              James D. Mitchell
##                                                          Wilf A. Wilson
##                                                        Rhiannon Dougall
##                                                          Robert Hancock
##
##  Licensing information can be found in the README file of this package.
##
#############################################################################
##

InstallMethod(IdempotentGeneratedSubsemigroup,
"for an inverse semigroup with inverse op",
[IsInverseSemigroup and IsGeneratorsOfInverseSemigroup],
function(S)
  local out;
  if not IsFinite(S) then
    TryNextMethod();
  fi;
  # Use acting := false since the output of this is a semilattice which is
  # J-trivial and hence it is better to use the Froidure-Pin Algorithm
  out := InverseSemigroup(Idempotents(S), rec(small := true, acting := false));
  SetIsSemilattice(out, true);
  return out;
end);

# fall back method

InstallMethod(NaturalPartialOrder, "for a semigroup",
[IsSemigroup],
function(S)
  local elts, p, func, out, i, j;

  if not IsFinite(S) then
    ErrorNoReturn("the argument (a semigroup) is not finite");
  elif not IsInverseSemigroup(S) then
    ErrorNoReturn("the argument (a semigroup) is not an inverse semigroup");
  fi;

  Info(InfoWarning, 2, "NaturalPartialOrder: this method ",
                       "fully enumerates its argument!");

  elts := ShallowCopy(Elements(S));
  p    := Sortex(elts, {x, y} -> IsGreensDGreaterThanFunc(S)(y, x)) ^ -1;
  func := NaturalLeqInverseSemigroup(S);
  out  := List([1 .. Size(S)], x -> []);

  # <elts> is sorted so that D_elts[i] < D_elts[j] => i < j.
  # Thus NaturalLeqInverseSemigroup(S)(i, j) => i <= j.

  for i in [1 .. Size(S)] do
    for j in [i + 1 .. Size(S)] do
      if func(elts[i], elts[j]) then
        AddSet(out[j ^ p], i ^ p);
      fi;
    od;
  od;
  return out;
end);

# fall back method

InstallMethod(NaturalLeqInverseSemigroup, "for a semigroup",
[IsSemigroup],
function(S)

  if not IsFinite(S) then
    ErrorNoReturn("the argument (a semigroup) is not finite");
  elif not IsInverseSemigroup(S) then
    ErrorNoReturn("the argument (a semigroup) is not an inverse semigroup");
  fi;

  return
    function(x, y)
      local z;
      z := InversesOfSemigroupElement(S, x)[1];
      return x * z = y * z;
    end;
end);

# same method for ideals

InstallMethod(CharacterTableOfInverseSemigroup,
"for an inverse semigroup of partial permutations",
[IsInverseSemigroup and IsPartialPermSemigroup and IsActingSemigroup],
function(S)
  local reps, p, H, C, r, tbl, id, l, A, o, lookup, conjclass, conjlens,
  j, conjreps, dom, subsets, x, m, u, k, h, i, n, y;

  reps := ShallowCopy(DClassReps(S));
  p := Sortex(reps, function(x, y)
                      return RankOfPartialPerm(x) > RankOfPartialPerm(y)
                             or (RankOfPartialPerm(x) = RankOfPartialPerm(y)
                                 and x > y);
                    end);

  H := List(reps, e -> SchutzenbergerGroup(HClass(S, e)));
  C := [];  # The group character matrices
  r := 0;

  # The block diagonal matrix of group character matrices
  for h in H do
    tbl := CharacterTable(h);
    id := IdentificationOfConjugacyClasses(tbl);
    tbl := Irr(tbl);
    l := Length(id);
    for i in [1 + r .. l + r] do
      C[i] := [];
      for j in [1 .. r] do
        C[i][j] := 0;
        C[j][i] := 0;
      od;

      for j in [1 + r .. l + r] do
        C[i][j] := tbl[i - r][Position(id, j - r)];
      od;
    od;
    r := r + l;
  od;

  A := List([1 .. r], x -> [1 .. r] * 0);
  o := LambdaOrb(S);
  lookup := OrbSCCLookup(o);

  conjclass := [ConjugacyClasses(H[1])];
  conjlens := [0];

  for i in [2 .. Length(H)] do
    Add(conjclass, ConjugacyClasses(H[i]));
    conjlens[i] := conjlens[i - 1] + Length(conjclass[i - 1]);
  od;

  j := 0;
  conjreps := [];
  for i in [1 .. Length(H)] do
    dom := DomainOfPartialPerm(reps[i]);
    subsets := Filtered(o, x -> IsSubset(dom, x));
    for n in [1 .. Length(conjclass[i])] do
      j := j + 1;
      conjreps[n + conjlens[i]] :=
        AsPartialPerm(Representative(conjclass[i][n]), dom);
      for y in subsets do
        x := RestrictedPartialPerm(conjreps[n + conjlens[i]], y);
        if y = ImageSetOfPartialPerm(x) then
          l := Position(o, y);
          m := lookup[l];
          u := LambdaOrbMult(o, m, l);
          x := AsPermutation(u[1] * x * u[2]);
          m := (m - 1) ^ p;
          k := PositionProperty(conjclass[m], class -> x in class)
               + conjlens[m];
          A[k][j] := A[k][j] + 1;
        fi;
      od;
    od;
  od;
  return [C * A, conjreps];
end);

# same method for ideals

InstallMethod(IsGreensDGreaterThanFunc, "for an inverse acting semigroup rep",
[IsInverseActingSemigroupRep],
function(S)
  local D, o;

  D := PartialOrderOfDClasses(S);
  o := LambdaOrb(S);

  return function(x, y)
    local u, v;
    if x = y then
      return false;
    fi;
    u := OrbSCCLookup(o)[Position(o, LambdaFunc(S)(x))] - 1;
    v := OrbSCCLookup(o)[Position(o, LambdaFunc(S)(y))] - 1;
    return u <> v and IsReachable(D, u, v);
  end;
end);

# same method for ideals

InstallMethod(PrimitiveIdempotents, "for a semigroup",
[IsSemigroup],
function(S)
  local T, i, gr, prims;

  if not IsFinite(S) then
    ErrorNoReturn("the argument (a semigroup) is not finite");
  elif not IsInverseSemigroup(S) then
    ErrorNoReturn("the argument (a semigroup) is not an inverse semigroup");
  elif MultiplicativeZero(S) = fail then
    return Idempotents(MinimalIdeal(S));
  fi;

  T := IdempotentGeneratedSubsemigroup(S);
  i := Position(Elements(T), MultiplicativeZero(S));
  # TODO(later): NaturalPartialOrder should return a Digraph but
  # NaturalPartialOrder is declared in GAP library, and so we can't.
  gr := DigraphReflexiveTransitiveReduction(Digraph(NaturalPartialOrder(T)));
  prims := InNeighboursOfVertex(gr, i);
  return EnumeratorSorted(T){prims};
end);

InstallMethod(PrimitiveIdempotents, "for acting inverse semigroup rep",
[IsInverseActingSemigroupRep],
function(s)
  local o, scc, rank, min, l, min2, m;

  o := LambdaOrb(s);
  scc := OrbSCC(o);
  rank := LambdaRank(s);
  min := ActionDegree(s);

  if MultiplicativeZero(s) = fail then
    for m in [2 .. Length(scc)] do
      l := rank(o[scc[m][1]]);
      if l < min then
        min := l;
      fi;
    od;
    return Idempotents(s, min);
  fi;

  # s has a multiplicative zero
  for m in [2 .. Length(scc)] do
    l := rank(o[scc[m][1]]);
    if l < min then
      min2 := min;
      min := l;
    fi;
  od;
  return Idempotents(s, min2);
end);

# same method for ideals
# TODO(later) a non-inverse-op version of this

InstallMethod(IsJoinIrreducible,
"for inverse semigroup with inverse op and a multiplicative element",
[IsInverseSemigroup and IsGeneratorsOfInverseSemigroup,
 IsMultiplicativeElement],
function(S, x)
  local elts, leq, y, i, k, j, sup;

  if not x in S then
    ErrorNoReturn("the 2nd argument (a mult. elt.) does not belong to ",
                  "the 1st argument (an inverse semigroup)");
  fi;

  if IsMultiplicativeZero(S, x) then
    return false;
  fi;

  elts := ShallowCopy(Idempotents(S));
  SortBy(elts, ActionRank(S));
  leq := NaturalLeqInverseSemigroup(S);

  y := LeftOne(x);
  i := Position(elts, y);

  # Find an element smaller than y, k
  k := First([i - 1, i - 2 .. 1], j -> leq(elts[j], elts[i]));

  # If there is no smaller element k: true
  if k = fail then
    return true;
  fi;

  # Look for other elements smaller than y which are not smaller than k
  j := First([1 .. k - 1], j -> leq(elts[j], elts[i])
                                and not leq(elts[j], elts[k]));

  if j = fail then
    return true;
  elif Size(HClassNC(S, y)) = 1 then
    return false;
  fi;

  sup := SupremumIdempotentsNC(Minorants(S, y), x);

  return y <> sup and ForAny(HClassNC(S, y), x -> leq(sup, x) and x <> y);
end);

# same method for ideals

InstallMethod(IsMajorantlyClosed,
"for inverse semigroup with inverse op and inverse semigroup with inverse op",
[IsInverseSemigroup and IsGeneratorsOfInverseSemigroup,
 IsInverseSemigroup and IsGeneratorsOfInverseSemigroup],
function(S, T)
  if not IsSubsemigroup(S, T) then
    ErrorNoReturn("the 2nd argument (an inverse semigroup) is not a",
                  " subsemigroup of the 1st argument (an inverse semigroup)");
  fi;
  return IsMajorantlyClosedNC(S, Elements(T));
end);

# same method for ideals

InstallMethod(IsMajorantlyClosed,
"for an inverse semigroup with inverse op and mult. element collection",
[IsInverseSemigroup and IsGeneratorsOfInverseSemigroup,
 IsMultiplicativeElementCollection],
function(S, T)
  if not IsSubset(S, T) then
    ErrorNoReturn("the 2nd argument (a mult. elt. coll) is not a ",
                  "subset of the 1st argument (an inverse semigroup)");
  fi;
  return IsMajorantlyClosedNC(S, T);
end);

# same method for ideals

InstallMethod(IsMajorantlyClosedNC,
"for an inverse semigroup with inverse op and mult. element collection",
[IsInverseSemigroup and IsGeneratorsOfInverseSemigroup,
 IsMultiplicativeElementCollection],
function(S, T)
  local leq, t, iter, u;

  if Size(S) = Size(T) then
    return true;
  fi;

  leq := NaturalLeqInverseSemigroup(S);
  for t in T do
    iter := Iterator(S);
    for u in iter do
      if leq(t, u) and not u in T then
        return false;
      fi;
    od;
  od;
  return true;
end);

# same method for ideals

InstallMethod(JoinIrreducibleDClasses,
"for an inverse semigroup of partial permutations",
[IsInverseSemigroup and IsPartialPermSemigroup],
function(S)
  local D, elts, out, seen_zero, rep, i, leq, k, minorants, singleline, h, mov,
        d, j, p;

  D := GreensDClasses(S);
  elts := Set(Idempotents(S));
  out := EmptyPlist(Length(D));
  seen_zero := false;

  for d in D do
    rep := LeftOne(Representative(d));

    if not seen_zero and IsMultiplicativeZero(S, rep) then
      seen_zero := true;
      continue;
    fi;

    i := Position(elts, rep);
    leq := NaturalLeqInverseSemigroup(S);
    k := First([i - 1, i - 2 .. 1], j -> leq(elts[j], rep));

    if k = fail then  # d is the minimal non-trivial D-class
                      # WW what do I mean by 'non-trivial' here?
      Add(out, d);
      continue;
    fi;

    minorants := [k];
    singleline := true;

    if IsActingSemigroup(S) then
      h := SchutzenbergerGroup(d);
    else
      h := GroupHClass(d);
    fi;

    for j in [1 .. k - 1] do
      if leq(elts[j], rep) then
        if singleline and not leq(elts[j], elts[k]) then
          # rep is the lub of {elts[j], elts[k]}, not quite
          singleline := false;
          if IsTrivial(h) then
            break;
          fi;
        else
          Add(minorants, j);
        fi;
      fi;
    od;

    if singleline then
      Add(out, d);
      continue;
    elif IsTrivial(h) then
      continue;
    fi;

    minorants := Union(List(minorants, j -> DomainOfPartialPerm(elts[j])));

    if DomainOfPartialPerm(rep) = minorants then
      # rep=lub(minorants) but rep not in minorants
      continue;
    fi;

    for p in h do
      mov := MovedPoints(p);
      if not IsEmpty(mov) and ForAll(mov, x -> not x in minorants) then
        # rep * p <> rep and rep, rep * p > lub(minorants) and rep || rep * p
        # and hence neither rep * p nor rep is of any set.
        Add(out, d);
        break;
      fi;
    od;
  od;

  return out;
end);

# same method for ideals

InstallMethod(JoinIrreducibleDClasses,
"for inverse semigroup with inverse op",
[IsInverseSemigroup and IsGeneratorsOfInverseSemigroup],
function(S)
  return Filtered(GreensDClasses(S),
                  x -> IsJoinIrreducible(S, Representative(x)));
end);

# same method for ideals

InstallMethod(MajorantClosure,
"for inverse semigroup with inverse op and semigroup",
[IsInverseSemigroup and IsGeneratorsOfInverseSemigroup, IsSemigroup],
function(S, T)
  if not IsSubsemigroup(S, T) then
    ErrorNoReturn("the 2nd argument (a semigroup) is not a subset ",
                  "of the 1st argument (an inverse semigroup)");
  fi;
  return MajorantClosureNC(S, Elements(T));
end);

# same method for ideals

InstallMethod(MajorantClosure,
"for an inverse semigroup with inverse op and mult. element collection",
[IsInverseSemigroup and IsGeneratorsOfInverseSemigroup,
 IsMultiplicativeElementCollection],
function(S, T)
  if not IsSubset(S, T) then
    ErrorNoReturn("the 2nd argument (a mult. elt. coll.) is not a subset",
                  " of the 1st argument (an inverse semigroup)");
  fi;
  return MajorantClosureNC(S, T);
end);

# same method for ideals

InstallMethod(MajorantClosureNC,
"for an inverse semigroup with inverse op and mult. element collection",
[IsInverseSemigroup and IsGeneratorsOfInverseSemigroup,
 IsMultiplicativeElementCollection],
function(S, T)
  local elts, n, out, ht, k, leq, val, t, i;

  elts := Elements(S);
  n := Length(elts);
  out := EmptyPlist(n);
  ht := HTCreate(T[1]);
  k := 0;

  for t in T do
    HTAdd(ht, t, true);
    Add(out, t);
    k := k + 1;
  od;
  leq := NaturalLeqInverseSemigroup(S);
  for t in out do
    for i in [1 .. n] do
      if leq(t, elts[i]) then
        val := HTValue(ht, elts[i]);
        if val = fail then
          k := k + 1;
          Add(out, elts[i]);
          HTAdd(ht, elts[i], true);
          if k = Size(S) then
            return out;
          fi;
        fi;
      fi;
    od;
  od;
  return out;
end);

# same method for ideals

InstallMethod(Minorants,
"for an inverse semigroup and multiplicative element",
[IsInverseSemigroup and IsGeneratorsOfInverseSemigroup,
 IsMultiplicativeElement],
function(S, f)
  local elts, i, out, rank, j, leq, k;

  if not f in S then
    ErrorNoReturn("the 2nd argument (a mult. elt.) is not an element of ",
                  "the 1st argument (an inverse semigroup)");
  fi;

  if HasNaturalPartialOrder(S) then
    elts := Elements(S);
    i := Position(elts, f);
    return elts{NaturalPartialOrder(S)[i]};
  fi;

  # Always true if S is a D-class rep of an inverse sgp
  if IsIdempotent(f) then
    out := EmptyPlist(NrIdempotents(S));
    elts := ShallowCopy(Idempotents(S));
  else
    out := EmptyPlist(Size(S));
    elts := ShallowCopy(Elements(S));
  fi;

  # Minorants always have lesser rank.
  # If we sort the elts by rank then we can cut down our search space
  if IsActingSemigroup(S) then
    rank := ActionRank(S);
    SortBy(elts, rank);
  else
    rank := function(x, y)
      return IsGreensDGreaterThanFunc(S)(y, x);
    end;
    Sort(elts, rank);
  fi;

  i := Position(elts, f);
  j := 0;
  leq := NaturalLeqInverseSemigroup(S);
  for k in [1 .. i - 1] do
    if leq(elts[k], f) and f <> elts[k] then
      j := j + 1;
      out[j] := elts[k];
    fi;
  od;
  ShrinkAllocationPlist(out);
  return out;
end);

# same method for ideals
# TODO(later): rename this RightCosets

InstallMethod(RightCosetsOfInverseSemigroup,
"for inverse semigroup and inverse semigroup",
[IsInverseSemigroup and IsGeneratorsOfInverseSemigroup,
 IsInverseSemigroup and IsGeneratorsOfInverseSemigroup],
function(S, T)
  local elts, min, usedreps, out, coset, s, t;

  if not IsSubsemigroup(S, T) then
    ErrorNoReturn("the 2nd argument (an inverse semigroup) must be ",
                  "a subsemigroup of the 1st argument (an inverse ",
                  "semigroup)");
  fi;

  elts := Elements(T);

  if not IsMajorantlyClosedNC(S, elts) then
    ErrorNoReturn("the 2nd argument (an inverse semigroup) must be ",
                  "majorantly closed");
  fi;

  min := RepresentativeOfMinimalIdeal(T);
  usedreps := [];
  out := [];

  for s in RClass(S, min) do

    # Check if Ts is a duplicate coset
    if not ForAny(usedreps, x -> s * x ^ -1 in elts) then
      Add(usedreps, s);

      coset := [];
      for t in elts do
        Add(coset, t * s);
      od;
      coset := Set(coset);

      # Generate the majorant closure of Ts to create the coset

      coset := MajorantClosureNC(S, coset);
      Add(out, coset);
    fi;
  od;

  return out;
end);

# same method for ideals

InstallMethod(SameMinorantsSubgroup,
"for a group H-class of an inverse semigroup with inverse op",
[IsGroupHClass],
function(H)
  local S, e, F, out, x, leq;

  S := Parent(H);

  if not IsGeneratorsOfInverseSemigroup(S) then
    ErrorNoReturn("the parent of the argument (a group H-class)",
                  " must be an inverse semigroup");
  fi;

  e := Representative(H);
  F := Minorants(S, e);
  out := [];
  leq := NaturalLeqInverseSemigroup(S);
  for x in H do
    if x = e or ForAll(F, f -> leq(f, x)) then
      Add(out, x);
    fi;
  od;
  return out;
end);

InstallGlobalFunction(SupremumIdempotentsNC,
function(coll, x)
  local dom, i, part, rep, reps, out, todo, inter;

  if IsPartialPerm(x) then

    if IsList(coll) and IsEmpty(coll) then
      return PartialPerm([]);
    fi;
    dom := DomainOfPartialPermCollection(coll);
    return PartialPerm(dom, dom);

  elif IsBipartition(x) and IsBlockBijection(x) then

    if IsList(coll) and IsEmpty(coll) then
      return Bipartition([Concatenation([1 .. DegreeOfBipartition(x)],
                                        -[1 .. DegreeOfBipartition(x)])]);
    fi;

    reps := List(coll, ExtRepOfObj);
    todo := [1 .. DegreeOfBipartition(x)];
    out := [];
    for i in todo do
      inter := [];
      for rep in reps do
        for part in rep do
          if i in part then
            Add(inter, part);
            break;
          fi;
        od;
      od;
      inter := Intersection(inter);
      AddSet(out, inter);
      todo := Difference(todo, inter);
    od;
    return Bipartition(out);

  elif IsBipartition(x) and IsPartialPermBipartition(x) then
    # TODO(later) shouldn't there be a check here like above?
    return AsBipartition(SupremumIdempotentsNC(
                         List(coll, AsPartialPerm), PartialPerm([])),
                         DegreeOfBipartition(x));
  fi;
  ErrorNoReturn("the argument is not a collection of partial perms, block ",
                "bijections, or partial perm bipartitions");
end);

# same method for ideals

InstallMethod(VagnerPrestonRepresentation,
"for an inverse semigroup with inverse op",
[IsInverseSemigroup and IsGeneratorsOfInverseSemigroup],
function(S)
  local gens, elts, out, iso, T, inv, i;

  gens := GeneratorsOfSemigroup(S);
  elts := Elements(S);
  out := EmptyPlist(Length(gens));

  iso := function(x)
    local dom;
    dom := Set(elts * (x ^ -1));
    return PartialPerm(List(dom, y -> Position(elts, y)),
                       List(List(dom, y -> y * x), y -> Position(elts, y)));
  end;

  for i in [1 .. Length(gens)] do
    out[i] := iso(gens[i]);
  od;

  T := InverseSemigroup(out);
  inv := x -> EvaluateWord(GeneratorsOfSemigroup(S), Factorization(T, x));

  return SemigroupIsomorphismByFunctionNC(S, T, iso, inv);
end);

InstallMethod(InversesOfSemigroupElementNC,
"for an inverse semigroup and a multiplicative element",
[IsInverseSemigroup and IsGeneratorsOfInverseSemigroup,
 IsMultiplicativeElement], SUM_FLAGS, {_, elm} -> [elm ^ -1]);
