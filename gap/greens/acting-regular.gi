#############################################################################
##
##  greens/acting-regular.gi
##  Copyright (C) 2013-2021                              James D. Mitchell
##
##  Licensing information can be found in the README file of this package.
##
#############################################################################
##

## This file contains methods for Green's classes of regular acting semigroups.

# See the start of greens/acting.gi for details of how to create Green's
# classes of acting semigroups.

# There are two types of methods here, those for IsRegularGreensClass (i.e.
# those Green's classes containing an idempotent) and those for
# IsRegularActingRepGreensClass (i.e. those that are known from the point of
# creation that they belong to a regular semigroup, which knew from its point
# of creation that it was regular).

#############################################################################
## This file contains methods for Green's classes etc for acting semigroups.
## It is organized as follows:
##
##   1. Helper functions for the creation of Green's classes, and lambda-rho
##      stuff.
##
##   2. Individual Green's classes (constructors, size, membership)
##
##   3. Collections of Green's classes (GreensXClasses, XClassReps, NrXClasses)
##
##   4. Idempotents and NrIdempotents
##
##   5. Regularity of Green's classes
##
##   6. Iterators and enumerators
##
#############################################################################

#############################################################################
## 1. Helper functions for the creation of Green's classes . . .
#############################################################################

InstallMethod(RhoCosets, "for a regular class of an acting semigroup",
[IsRegularGreensClass and IsActingSemigroupGreensClass],
function(C)
  local S;
  S := Parent(C);
  return [LambdaIdentity(S)(LambdaRank(S)(LambdaFunc(S)(Representative(C))))];
end);

InstallMethod(LambdaCosets, "for a regular class of an acting semigroup",
[IsRegularGreensClass and IsActingSemigroupGreensClass], RhoCosets);

# same method for inverse

InstallMethod(SchutzenbergerGroup, "for D-class of regular acting semigroup",
[IsRegularDClass and IsActingSemigroupGreensClass],
D -> LambdaOrbSchutzGp(LambdaOrb(D), LambdaOrbSCCIndex(D)));

# same method for inverse

InstallMethod(SchutzenbergerGroup,
"for H-class of regular acting semigroup rep",
[IsRegularActingRepGreensClass and
 IsGreensHClass],
function(H)
  local S, rep, p;
  S := Parent(H);
  rep := Representative(H);
  SEMIGROUPS.RectifyLambda(H);
  p := LambdaConjugator(S)(H!.rep, rep);
  return LambdaOrbSchutzGp(LambdaOrb(H), LambdaOrbSCCIndex(H)) ^ p;
end);

# The following methods (for \< for Green's classes) should not be applied to
# IsRegularGreensClass since they rely on the fact that these are Green's
# classes of a regular semigroup, which uses the data structures of semigroup
# that knew it was regular from the point of creation.

# Same method for inverse

InstallMethod(\<,
"for a Green's D-classes of a regular acting semigroup rep",
[IsGreensDClass and IsActingSemigroupGreensClass and
 IsRegularActingRepGreensClass,
 IsGreensDClass and IsActingSemigroupGreensClass and
 IsRegularActingRepGreensClass],
function(x, y)
  local S, scc;
  if Parent(x) <> Parent(y) or x = y then
    return false;
  fi;
  S    := Parent(x);
  scc  := OrbSCCLookup(LambdaOrb(S));
  return scc[Position(LambdaOrb(S), LambdaFunc(S)(Representative(x)))]
         < scc[Position(LambdaOrb(S), LambdaFunc(S)(Representative(y)))];
end);

# Same method for inverse

InstallMethod(\<,
"for a Green's R-classes of a regular acting semigroup rep",
[IsGreensRClass and IsRegularActingRepGreensClass,
 IsGreensRClass and IsRegularActingRepGreensClass],
function(x, y)
  if Parent(x) <> Parent(y) or x = y then
    return false;
  fi;
  return RhoFunc(Parent(x))(Representative(x))
         < RhoFunc(Parent(x))(Representative(y));
end);

# Same method for inverse

InstallMethod(\<,
"for a Green's L-classes of a regular acting semigroup rep",
[IsGreensLClass and IsRegularActingRepGreensClass,
 IsGreensLClass and IsRegularActingRepGreensClass],
function(x, y)
  if Parent(x) <> Parent(y) or x = y then
    return false;
  fi;
  return LambdaFunc(Parent(x))(Representative(x))
         < LambdaFunc(Parent(x))(Representative(y));
end);

#############################################################################
## 2. Individual classes . . .
#############################################################################

InstallMethod(Size, "for a regular D-class of an acting semigroup",
[IsRegularDClass and IsActingSemigroupGreensClass],
function(D)
  return Size(SchutzenbergerGroup(D)) * Length(LambdaOrbSCC(D))
   * Length(RhoOrbSCC(D));
end);

#############################################################################
## 3. Collections of classes, and reps
#############################################################################

# different method for inverse.

# Note that these are not rectified!

# this method could apply to regular ideals but is not used since the rank of
# IsActingSemigroup and IsSemigroupIdeal is higher than the rank for this
# method. Anyway the data of an ideal must be enumerated to the end to know the
# DClassReps, and to know the LambdaOrb, so these methods are equal.

# Do not use the following method for IsRegularSemigroup, in case a semigroup
# learns it is regular after it is created, since the order of the D-class reps
# and D-classes might be important and should not change depending on what the
# semigroup learns about itself.

InstallMethod(DClassReps,
"for a regular acting semigroup rep with generators",
[IsRegularActingSemigroupRep
 and HasGeneratorsOfSemigroup],
function(S)
  local o, out, m;
  o := LambdaOrb(S);
  out := EmptyPlist(Length(OrbSCC(o)));
  for m in [2 .. Length(OrbSCC(o))] do
    out[m - 1] := LambdaOrbRep(o, m);
  od;
  return out;
end);

# different method for inverse/ideals

# Do not use the following method for IsRegularSemigroup, in case a semigroup
# learns it is regular after it is created, since the order of the D-class reps
# and D-classes might be important and should not change depending on what the
# semigroup learns about itself.

InstallMethod(GreensDClasses,
"for a regular acting semigroup rep with generators",
[IsRegularActingSemigroupRep
 and HasGeneratorsOfSemigroup],
function(S)
  local o, scc, out, SetRho, RectifyRho, D, i;

  o := LambdaOrb(S);
  scc := OrbSCC(o);
  out := EmptyPlist(Length(scc) - 1);
  Enumerate(RhoOrb(S));
  SetRho := SEMIGROUPS.SetRho;
  RectifyRho := SEMIGROUPS.RectifyRho;
  for i in [2 .. Length(scc)] do
    # don't use GreensDClassOfElementNC here to avoid rectifying lambda
    D := SEMIGROUPS.CreateDClass(S, LambdaOrbRep(o, i), false);
    SetLambdaOrb(D, o);
    SetLambdaOrbSCCIndex(D, i);
    SetRho(D);
    RectifyRho(D);
    out[i - 1] := D;
  od;
  return out;
end);

# same method for inverse/ideals

# Do not use the following method for IsRegularSemigroup, in case a semigroup
# learns it is regular after it is created, since the order of the D-class reps
# and D-classes might be important and should not change depending on what the
# semigroup learns about itself.

InstallMethod(RClassReps,
"for a regular acting semigroup rep",
[IsRegularActingSemigroupRep],
S -> Concatenation(List(GreensDClasses(S), RClassReps)));

# same method for inverse/ideals

# Do not use the following method for IsRegularSemigroup, in case a semigroup
# learns it is regular after it is created, since the order of the D-class reps
# and D-classes might be important and should not change depending on what the
# semigroup learns about itself.

InstallMethod(GreensRClasses, "for a regular acting semigroup rep",
[IsRegularActingSemigroupRep],
S -> Concatenation(List(GreensDClasses(S), GreensRClasses)));

#############################################################################

# same method for inverse/ideals

InstallMethod(NrDClasses, "for a regular acting semigroup with generators",
[IsActingSemigroup and IsRegularSemigroup and HasGeneratorsOfSemigroup],
S -> Length(OrbSCC(LambdaOrb(S))) - 1);

# same method for inverse semigroups, same for ideals

InstallMethod(NrLClasses, "for a regular acting semigroup",
[IsActingSemigroup and IsRegularSemigroup],
S -> Length(Enumerate(LambdaOrb(S))) - 1);

# same method for inverse semigroups

InstallMethod(NrLClasses, "for a D-class of regular acting semigroup",
[IsActingSemigroupGreensClass and IsRegularDClass],
D -> Length(LambdaOrbSCC(D)));

# different method for inverse semigroups, same for ideals

InstallMethod(NrRClasses, "for a regular acting semigroup",
[IsActingSemigroup and IsRegularSemigroup],
S -> Length(Enumerate(RhoOrb(S), infinity)) - 1);

# different method for inverse semigroups

InstallMethod(NrRClasses, "for a D-class of regular acting semigroup",
[IsActingSemigroupGreensClass and IsRegularDClass],
D -> Length(RhoOrbSCC(D)));

# different method for inverse semigroups

InstallMethod(NrHClasses, "for a D-class of regular acting semigroup",
[IsActingSemigroupGreensClass and IsRegularDClass],
R -> Length(LambdaOrbSCC(R)) * Length(RhoOrbSCC(R)));

# different method for inverse semigroups

InstallMethod(NrHClasses, "for a L-class of regular acting semigroup",
[IsActingSemigroupGreensClass and IsRegularGreensClass and IsGreensLClass],
L -> Length(RhoOrbSCC(L)));

# same method for inverse semigroups

InstallMethod(NrHClasses, "for a R-class of regular acting semigroup",
[IsActingSemigroupGreensClass and IsRegularGreensClass and IsGreensRClass],
R -> Length(LambdaOrbSCC(R)));

# different method for inverse/ideals

# Do not use the following method for IsRegularSemigroup, in case a semigroup
# learns it is regular after it is created, since the order of the D-class reps
# and D-classes might be important and should not change depending on what the
# semigroup learns about itself.

InstallMethod(PartialOrderOfDClasses,
"for a regular acting semigroup rep with generators",
[IsRegularActingSemigroupRep and HasGeneratorsOfSemigroup],
function(S)
  local D, n, out, o, gens, lookup, lambdafunc, i, x, y;

  D := GreensDClasses(S);
  n := Length(D);
  out := List([1 .. n], x -> EmptyPlist(n));
  o := LambdaOrb(S);
  gens := o!.gens;
  lookup := OrbSCCLookup(o);
  lambdafunc := LambdaFunc(S);

  for i in [1 .. n] do
    for x in gens do
      for y in RClassReps(D[i]) do
        AddSet(out[i], lookup[Position(o, lambdafunc(x * y))] - 1);
      od;
      for y in LClassReps(D[i]) do
        AddSet(out[i], lookup[Position(o, lambdafunc(y * x))] - 1);
      od;
    od;
  od;

  Perform(out, ShrinkAllocationPlist);
  D := DigraphNC(IsMutableDigraph, out);
  DigraphRemoveLoops(D);
  MakeImmutable(D);
  return D;
end);

#############################################################################
## 4. Idempotents . . .
#############################################################################

# different method for inverse, same for ideals

InstallMethod(NrIdempotents, "for a regular acting semigroup",
[IsRegularSemigroup and IsActingSemigroup],
function(S)
  local nr, tester, rho_o, scc, lambda_o, rhofunc, lookup, rep, rho, j, i, k;

  nr       := 0;
  tester   := IdempotentTester(S);
  rho_o    := RhoOrb(S);
  scc      := OrbSCC(rho_o);
  lambda_o := LambdaOrb(S);
  Enumerate(lambda_o, infinity);
  rhofunc  := RhoFunc(S);
  lookup   := OrbSCCLookup(rho_o);

  for i in [2 .. Length(lambda_o)] do
    # TODO(later) this could be better, just multiply by next element of the
    # Schreier tree
    rep := EvaluateWord(lambda_o, TraceSchreierTreeForward(lambda_o, i));
    rho := rhofunc(rep);
    j := lookup[Position(rho_o, rho)];
    for k in scc[j] do
      if tester(lambda_o[i], rho_o[k]) then
        nr := nr + 1;
      fi;
    od;
  od;

  return nr;
end);

InstallMethod(NrIdempotents, "for a regular acting *-semigroup",
[IsRegularStarSemigroup and IsActingSemigroup],
function(S)
  local nr, tester, o, scc, vals, x, i, j, k;

  nr     := 0;
  tester := IdempotentTester(S);
  o      := Enumerate(LambdaOrb(S));
  scc    := OrbSCC(o);

  for i in [2 .. Length(scc)] do
    vals := scc[i];
    for j in [1 .. Length(vals)] do
      nr := nr + 1;
      x  := o[vals[j]];
      for k in [j + 1 .. Length(vals)] do
        if tester(x, o[vals[k]]) then
          nr := nr + 2;
        fi;
      od;
    od;
  od;
  return nr;
end);

InstallMethod(NrIdempotents, "for a regular star bipartition acting semigroup",
[IsRegularStarSemigroup and IsActingSemigroup and IsBipartitionSemigroup and
 HasGeneratorsOfSemigroup],
function(S)
  if Length(Enumerate(LambdaOrb(S))) > 5000 then
    return Sum(NrIdempotentsByRank(S));
  fi;
  TryNextMethod();
end);

# TODO(later) methods NrIdempotentsByRank for other types of semigroup.

InstallMethod(NrIdempotentsByRank,
"for a regular star bipartition acting semigroup",
[IsRegularStarSemigroup and IsActingSemigroup and IsBipartitionSemigroup and
 HasGeneratorsOfSemigroup],
function(S)
  local o, opts;
  if DegreeOfBipartitionSemigroup(S) = 0 then
    return [1];
  fi;
  o := Enumerate(LambdaOrb(S));
  opts := SEMIGROUPS.OptionsRec(S);
  return BIPART_NR_IDEMPOTENTS(o,
                               OrbSCC(o),
                               OrbSCCLookup(o),
                               opts.nr_threads);
end);

#############################################################################
## 5. Regular classes . . .
#############################################################################

# same method for inverse semigroups, same for ideals

InstallMethod(NrRegularDClasses, "for a regular acting semigroup",
[IsActingSemigroup and IsRegularSemigroup], NrDClasses);

#############################################################################
## 6. Iterators and enumerators . . .
#############################################################################

#############################################################################
## 6.a. for all classes
#############################################################################

# different method for inverse

InstallMethod(IteratorOfLClasses, "for a regular acting semigroup",
[IsActingSemigroup and IsRegularSemigroup],
function(S)
  if HasGreensLClasses(S) then
    return IteratorList(GreensLClasses(S));
  fi;

  return IteratorByIterator(IteratorOfLClassReps(S),
                            x -> GreensLClassOfElementNC(S, x),
                            [],
                            fail,
                            rec(PrintObj :=
                                function(iter)
                                  Print("<iterator of L-classes>");
                                  return;
                                end));
end);

# same method for inverse

InstallMethod(IteratorOfDClasses, "for a regular acting semigroup",
[IsActingSemigroup and IsRegularSemigroup],
function(S)
  if HasGreensDClasses(S) then
    return IteratorList(GreensDClasses(S));
  fi;
  return IteratorByIterator(IteratorOfDClassReps(S),
                            x -> GreensDClassOfElementNC(S, x),
                            [],
                            fail,
                            rec(PrintObj :=
                                function(iter)
                                  Print("<iterator of D-classes>");
                                  return;
                                end));
end);

# different method for inverse

# Notes: the only purpose for this is the method for NumberElement.  Otherwise
# use (if nothing much is known) IteratorOfRClasses or if everything is know
# just use RClasses.

# Use IsRegularSemigroup instead of IsRegularActingSemigroupRep since the order
# does not matter.

InstallMethod(EnumeratorOfRClasses, "for a regular acting semigroup",
[IsActingSemigroup and IsRegularSemigroup],
function(S)
  return EnumeratorByFunctions(CollectionsFamily(FamilyObj(S)), rec(

    parent := S,

    Length := enum -> NrRClasses(enum!.parent),

    Membership := function(R, enum)
      return Representative(R) in enum!.parent;
    end,

    NumberElement := function(enum, R)
      local pos;
      pos := Position(RhoOrb(enum!.parent),
       RhoFunc(enum!.parent)(Representative(R)));
      if pos = fail then
        return fail;
      fi;
      return pos - 1;
    end,

   ElementNumber := function(enum, nr)
    local S, o, m;
    S := enum!.parent;
    o := RhoOrb(S);
    if nr + 1 > Length(OrbSCCLookup(o)) then
      return fail;
    fi;
    m := OrbSCCLookup(o)[nr + 1];
    return
      GreensRClassOfElementNC(S,
                              RhoOrbMult(o, m, nr + 1)[1] * RhoOrbRep(o, m));
   end,

   PrintObj := function(enum)
     Print("<enumerator of R-classes of ", ViewString(S), ">");
     return;
   end));
end);

# different method for inverse

InstallMethod(IteratorOfDClassData, "for regular acting semigroup",
[IsActingSemigroup and IsRegularSemigroup],
function(S)
  local record, o, scc, func;

  if not IsClosedOrbit(LambdaOrb(S)) then
    record := rec(m := fail, graded := IteratorOfGradedLambdaOrbs(S));
    record.NextIterator := function(iter)
      local l, rep, m;

      m := iter!.m;

      if IsBound(iter!.o) and iter!.o = fail then
        return fail;
      fi;

      if m = fail or m = Length(OrbSCC(iter!.o)) then
        m := 1;
        l := 1;
        iter!.o := NextIterator(iter!.graded);
        if iter!.o = fail then
          return fail;
        fi;
      else
        m := m + 1;
        l := OrbSCC(iter!.o)[m][1];
      fi;
      iter!.m := m;

      # rep has rectified lambda val and rho val.
      rep := LambdaOrbRep(iter!.o, m) * LambdaOrbMult(iter!.o, m, l)[2];
      return [S, m, iter!.o, 1, GradedRhoOrb(S, rep, false)[1], rep, false];
    end;

    record.ShallowCopy := iter -> rec(m := fail,
                                      graded := IteratorOfGradedLambdaOrbs(S));
    return IteratorByNextIterator(record);
  else
    o := LambdaOrb(S);
    scc := OrbSCC(o);

    func := function(iter, m)
      local rep;
      # rep has rectified lambda val and rho val.
      rep := EvaluateWord(o, TraceSchreierTreeForward(o, scc[m][1]));
      return [S, m, o, 1, GradedRhoOrb(S, rep, false)[1], rep, false];
    end;

    return IteratorByIterator(IteratorList([2 .. Length(scc)]), func);
  fi;
end);

# no method required for inverse (it's not used for anything)

InstallMethod(IteratorOfLClassData, "for regular acting semigroup",
[IsActingSemigroup and IsRegularSemigroup],
function(s)
  local o, func, iter;

  o := LambdaOrb(s);

  func := function(iter, i)
    local rep;

    # <rep> has lambda val corresponding to <i>
    rep := EvaluateWord(o, TraceSchreierTreeForward(o, i));

    # <rep> has rho val in position 1 of GradedRhoOrb(s, rep, false).
    # We don't rectify the rho val of <rep> in <o> since we require to
    # enumerate RhoOrb(s) to do this, if we use GradedRhoOrb(s, rep,
    # true) then this get more complicated.
    return [s, 1, GradedRhoOrb(s, rep, false)[1], rep, true];
  end;

  if not IsClosedOrbit(o) then
    iter := IteratorByOrbFunc(o, func, 2);
  else
    return IteratorByIterator(IteratorList([2 .. Length(o)]), func);
  fi;

  return iter;
end);

# different method for inverse

InstallMethod(IteratorOfRClassData, "for regular acting semigroup",
[IsActingSemigroup and IsRegularSemigroup],
function(s)
  local o, func, iter;

  o := RhoOrb(s);

  func := function(iter, i)
    local rep;

    # <rep> has rho val corresponding to <i>
    rep := EvaluateWord(o, Reversed(TraceSchreierTreeForward(o, i)));

    # <rep> has lambda val in position 1 of GradedLambdaOrb(s, rep, false).
    # We don't rectify the lambda val of <rep> in <o> since we require to
    # enumerate LambdaOrb(s) to do this, if we use GradedLambdaOrb(s, rep,
    # true) then this gets more complicated.
    return [s, 1, GradedLambdaOrb(s, rep, false), rep, true];
  end;

  return IteratorByIterator(IteratorList([2 .. Length(o)]), func);
end);

# same method for inverse

InstallMethod(IteratorOfDClassReps, "for a regular acting semigroup",
[IsActingSemigroup and IsRegularSemigroup],
function(s)
  if HasDClassReps(s) then
    return IteratorList(DClassReps(s));
  fi;
  return IteratorByIterator(IteratorOfDClassData(s),
                            x -> x[6],
                            [],
                            fail,
                            rec(PrintObj := function(iter)
                                  Print("<iterator of D-class reps>");
                                  return;
                                end));
end);

# different method for inverse

InstallMethod(IteratorOfLClassReps, "for a regular acting semigroup",
[IsActingSemigroup and IsRegularSemigroup],
S -> IteratorByIterator(IteratorOfLClassData(S),
                        x -> x[4],
                        [],
                        fail,
                        rec(PrintObj := function(iter)
                              Print("<iterator of L-class reps>");
                              return;
                            end)));

########################################################################
# 7.b. for individual classes
########################################################################

# different method for inverse

InstallMethod(Enumerator, "for a regular D-class of an acting semigroup",
[IsRegularDClass and IsActingSemigroupGreensClass],
function(D)
  local convert_out, convert_in, rho_scc, lambda_scc, enum;

  if HasAsList(D) then
    return AsList(D);
  elif HasAsSSortedList(D) then
    return AsSSortedList(D);
  fi;

  convert_out := function(enum, tuple)
    local D, rep, act;
    if tuple = fail then
      return fail;
    fi;
    D := enum!.parent;
    rep := Representative(D);
    act := StabilizerAction(Parent(D));
    return act(RhoOrbMult(RhoOrb(D), RhoOrbSCCIndex(D),
               tuple[1])[1] * rep, tuple[2])
           * LambdaOrbMult(LambdaOrb(D), LambdaOrbSCCIndex(D), tuple[3])[1];
  end;

  convert_in := function(enum, elt)
    local D, S, k, l, f;

    D := enum!.parent;
    S := Parent(D);

    k := Position(RhoOrb(D), RhoFunc(S)(elt));
    if OrbSCCLookup(RhoOrb(D))[k] <> RhoOrbSCCIndex(D) then
      return fail;
    fi;

    l := Position(LambdaOrb(D), LambdaFunc(S)(elt));

    if OrbSCCLookup(LambdaOrb(D))[l] <> LambdaOrbSCCIndex(D) then
      return fail;
    fi;

    f := RhoOrbMult(RhoOrb(D), RhoOrbSCCIndex(D), k)[2] * elt
     * LambdaOrbMult(LambdaOrb(D), LambdaOrbSCCIndex(D), l)[2];

    return [k, LambdaPerm(S)(Representative(D), f), l];
  end;

  rho_scc    := OrbSCC(RhoOrb(D))[RhoOrbSCCIndex(D)];
  lambda_scc := OrbSCC(LambdaOrb(D))[LambdaOrbSCCIndex(D)];
  enum := EnumeratorOfCartesianProduct(rho_scc,
                                       SchutzenbergerGroup(D),
                                       lambda_scc);
  return SEMIGROUPS.ActingGreensClassEnum(D, enum, convert_out, convert_in);
end);

