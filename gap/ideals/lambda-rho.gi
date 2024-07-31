############################################################################
##
##  ideals/lambda-rho.gi
##  Copyright (C) 2013-2022                              James D. Mitchell
##
##  Licensing information can be found in the README file of this package.
##
#############################################################################
##

InstallMethod(AsList, "for an ideal orb", [IsIdealOrb],
o -> Concatenation(List(o!.orbits, AsList)));

InstallMethod(Enumerate, "for an ideal orb, and a number",
[IsIdealOrb, IsCyclotomic],
function(o, limit)
  local newlookfunc;

  if IsClosedOrbit(o) then
    return o;
  fi;

  newlookfunc := {data, x} -> IsClosedOrbit(o) or Length(o) >= limit;
  Enumerate(SemigroupData(o!.parent), infinity, newlookfunc);

  return o;
end);

InstallMethod(Enumerate, "for an ideal orb, a number, and a function",
[IsIdealOrb, IsCyclotomic, IsFunction],
function(o, limit, lookfunc)
  local newlookfunc;

  newlookfunc := {data, x} -> IsClosedOrbit(o) or Length(o) >= limit;
  if IsLambdaOrb(o) then
    Enumerate(SemigroupData(o!.parent), infinity,
              rec(lookfunc := newlookfunc, lambdalookfunc := lookfunc));
  elif IsRhoOrb(o) then
    Enumerate(SemigroupData(o!.parent), infinity,
              rec(lookfunc := newlookfunc, rholookfunc := lookfunc));
  fi;

  return o;
end);

InstallMethod(Length, "for a ideal orb", [IsIdealOrb],
o -> Sum(o!.lens));

InstallMethod(Length, "for an ideal inverse orb",
[IsIdealOrb and IsInverseOrb], o -> Length(o!.orbit));

InstallMethod(IsBound\[\], "for an ideal orb and positive integer",
[IsIdealOrb, IsPosInt],
function(o, i)
  local nr;

  nr := 1;
  while IsBound(o!.orbits[nr]) and i > Length(o!.orbits[nr]) do
    i := i - Length(o!.orbits[nr]);
    nr := nr + 1;
  od;
  return IsBound(o!.orbits[nr]) and IsBound(o!.orbits[nr][i]);
end);

InstallMethod(IsBound\[\], "for an inverse ideal orb and positive integer",
[IsIdealOrb and IsInverseOrb, IsPosInt], {o, i} -> IsBound(o!.orbit[i]));

InstallMethod(ELM_LIST, "for an ideal orb and positive integer",
[IsIdealOrb, IsPosInt],
function(o, i)
  local nr;

  nr := 1;
  while i > Length(o!.orbits[nr]) do
    i := i - Length(o!.orbits[nr]);
    nr := nr + 1;
  od;
  return o!.orbits[nr][i];
end);

InstallMethod(ELM_LIST, "for an inverse ideal orb and positive integer",
[IsIdealOrb and IsInverseOrb, IsPosInt], {o, i} -> o!.orbit[i]);

# same method for inverse ideal orbs

InstallMethod(\in, "for an object and ideal orb",
[IsObject, IsIdealOrb], {obj, o} -> HTValue(o!.ht, obj) <> fail);

# same method for inverse ideal orbs

InstallMethod(Position, "for an ideal orb, object, zero cyc",
[IsIdealOrb, IsObject, IsZeroCyc], {o, obj, _} -> HTValue(o!.ht, obj));

# same method for inverse ideal orbs

InstallMethod(OrbitGraph, "for an ideal orb", [IsIdealOrb], o -> o!.orbitgraph);

InstallMethod(ViewObj, "for a ideal orb",
[IsIdealOrb],
function(o)
  Print("<");
  if IsClosedOrbit(o) then
    Print("closed ");
  else
    Print("open ");
  fi;
  if IsInverseOrb(o) then
    Print("inverse ");
  fi;
  Print("ideal ");
  if IsLambdaOrb(o) then
    Print("lambda ");
  else
    Print("rho ");
  fi;
  Print("orbit with ", Length(o) - 1, " points");

  if not IsInverseOrb(o) then
    Print(" in ", Length(o!.orbits) - 1, " components");
  fi;
  Print(">");
  return;
end);

# different method for inverse semigroup ideals

InstallMethod(LambdaOrb, "for an acting semigroup ideal",
[IsActingSemigroup and IsSemigroupIdeal],
function(I)
  local S, gens, record, htopts, fam;

  S := SupersemigroupOfIdeal(I);
  gens := List(GeneratorsOfSemigroup(S), x -> ConvertToInternalElement(S, x));

  record := rec();
  record.orbits := [[fail]];
  record.lens := [1];
  record.parent := I;
  record.scc := [[1]];
  record.scc_reps := [fail];
  record.scc_lookup := [1];
  record.schreiergen := [fail];
  record.schreierpos := [fail];
  record.orbitgraph := [[]];
  record.looking := false;
  record.gens := gens;
  record.orbschreierpos := [];
  record.orbschreiergen := [];
  record.orbschreiercmp := [];
  # <o!.orbits[i]> is obtained from the component
  # <o!.orbits[o!.orbschreiercmp[i]]> by applying right multiplying some
  # element of the ideal with lambda value in position <o!.schreierpos[i]> by
  # <o!.schreiergen[i]>.
  record.orbtogen := [];
  # ComponentOfIndex(o, Position(o, LambdaFunc(M)(gens[orbtogen[i]])))=i
  # and <orbtogen[ComponentOfIndex(Position(o, LambdaFunc(I)(gens[i])))]=i>
  # i.e. component <i> arises from <gens[orbtogen[i]]>.

  htopts := ShallowCopy(LambdaOrbOpts(I));
  htopts.treehashsize := SEMIGROUPS.OptionsRec(I).hashlen;
  record.ht := HTCreate(LambdaFunc(I)(gens[1]), htopts);

  fam := CollectionsFamily(FamilyObj(LambdaFunc(I)(Representative(I))));

  return Objectify(NewType(fam, IsIdealOrb and IsLambdaOrb), record);
end);

InstallMethod(RhoOrb, "for an acting semigroup ideal",
[IsActingSemigroup and IsSemigroupIdeal],
function(I)
  local S, gens, record, htopts, fam;

  S := SupersemigroupOfIdeal(I);
  gens := List(GeneratorsOfSemigroup(S), x -> ConvertToInternalElement(S, x));

  record := rec();
  record.orbits := [[fail]];
  record.lens := [1];
  record.parent := I;
  record.scc := [[1]];
  record.scc_reps := [fail];
  record.scc_lookup := [1];
  record.schreiergen := [fail];
  record.schreierpos := [fail];
  record.orbitgraph := [[]];
  record.looking := false;
  record.gens := gens;
  record.orbschreierpos := [];
  record.orbschreiergen := [];
  record.orbschreiercmp := [];
  # <o!.orbits[i]> is obtained from the component
  # <o!.orbits[o!.orbschreiercmp[i]]> by applying left multiplying some
  # element of the ideal with rho value in position <o!.schreierpos[i]> by
  # <o!.schreiergen[i]>.
  record.orbtogen := [];
  # <ComponentOfIndex(o, Position(o, RhoFunc(I)(gens[orbtogen[i]])))=i>
  # and <orbtogen[ComponentOfIndex(Position(o, RhoFunc(I)(gens[i])))]=i>
  # i.e. component <i> arises from <gens[orbtogen[i]]>.
  htopts := ShallowCopy(RhoOrbOpts(I));
  htopts.treehashsize := SEMIGROUPS.OptionsRec(I).hashlen;
  record.ht := HTCreate(RhoFunc(I)(gens[1]), htopts);

  fam := CollectionsFamily(FamilyObj(RhoFunc(I)(Representative(I))));
  return Objectify(NewType(fam, IsIdealOrb and IsRhoOrb), record);
end);

# The entire lambda orbit of an ideal of an inverse semigroup is obtained from
# the lambda values of the generators (and their inverses) of the ideal by
# acting on the right by the generators (and their inverses) of the
# supersemigroup. Hence we require a different case here.

# Don't think that this applies to semigroups of matrices over finite fields,
# so this doesn't require us to use ConvertToInternalElement
# TODO(FixExtremeTests): check that this is really correct

InstallMethod(LambdaOrb, "for an inverse acting semigroup rep ideal",
[IsInverseActingSemigroupRep and IsSemigroupIdeal],
function(I)
  local record, gens, lambdafunc, o, ht, nr, nrgens, lambda, InstallPointInOrb,
   x, i;

  record := ShallowCopy(LambdaOrbOpts(I));
  record.scc_reps := [FakeOne(GeneratorsOfSemigroupIdeal(I))];

  record.schreier := true;
  record.orbitgraph := true;
  record.storenumbers := true;
  record.log := true;
  record.parent := I;
  record.treehashsize := SEMIGROUPS.OptionsRec(I).hashlen;
  record.orbtogen := [];
  # orbtogen[Position(o, LambdaFunc(I)(gens[i]))]=i and

  gens := GeneratorsOfSemigroupIdeal(I);
  lambdafunc := LambdaFunc(I);

  o := Orb(GeneratorsOfSemigroup(SupersemigroupOfIdeal(I)),
           LambdaOrbSeed(I),
           LambdaAct(I),
           record);

  # install the lambda values of the generators
  ht := o!.ht;
  nr := 1;
  nrgens := Length(gens);
  lambdafunc := LambdaFunc(I);

  #
  InstallPointInOrb := function(lambda)
    nr := nr + 1;
    HTAdd(ht, lambda, nr);
    Add(o!.orbit, lambda);
    Add(o!.schreierpos, fail);
    Add(o!.schreiergen, fail);
    Add(o!.orbitgraph, []);
  end;
  #

  for i in [1 .. nrgens] do
    x := gens[i];
    lambda := lambdafunc(x);
    if HTValue(ht, lambda) = fail then
      InstallPointInOrb(lambda);
      o!.orbtogen[nr] := i;
    fi;

    lambda := lambdafunc(x ^ -1);
    if HTValue(ht, lambda) = fail then
      InstallPointInOrb(lambda);
      o!.orbtogen[nr] := nrgens + i;
    fi;
  od;

  o!.pos := 2;
  # don't apply the generators of the supersemigroup of <I> to the dummy point
  # at the start of the orbit (otherwise we just get the lambda orbit of the
  # supersemigroup

  SetFilterObj(o, IsLambdaOrb and IsInverseOrb and IsIdealOrb);
  return o;
end);

# For an ideal rho orb <o>, rho value <pt> of <x>, <x> itself an element of the
# ideal, <pos> is the position in <o> of the rho value from which <x> was
# obtained by right multiplication by, the <gen>th generator of the parent of
# <o>, <ind> is the index of the generator of the ideal which we are adding (if
# applicable).
#
# This assumes that <pt> is not in <o> already, and that either:
#
#   - <pos=gen=fail> and we are updating with the <ind>th generator of the
#     *ideal*; or
#
#   - <pos>, <gen> are positive integers and <ind=fail>

InstallGlobalFunction(UpdateIdealLambdaOrb,
function(o, pt, x, pos, gen, ind, lookfunc)
  local I, record, len, S, gens, new, ht, found, nrorb, cmp, i;

  I := o!.parent;
  record := ShallowCopy(LambdaOrbOpts(I));
  record.schreier := true;
  record.orbitgraph := true;
  record.storenumbers := true;
  record.log := true;
  record.parent := I;
  record.treehashsize := SEMIGROUPS.OptionsRec(I).hashlen;

  len := Length(o);

  if len <> 0 then
    record.gradingfunc := function(_, x)
      return HTValue(o!.ht, x) <> fail;
      # return x in o;
    end;
    record.onlygrades := {x, _} -> not x;
    record.onlygradesdata := fail;
  fi;

  S := SupersemigroupOfIdeal(I);
  gens := List(GeneratorsOfSemigroup(S), x -> ConvertToInternalElement(S, x));
  new := Orb(gens, pt, LambdaAct(I), record);
  Enumerate(new);

  ht := o!.ht;

  if lookfunc = ReturnFalse then
    for i in [1 .. Length(new)] do
      HTAdd(ht, new[i], i + len);
    od;
  else
    o!.looking := true;
    o!.found := false;
    found := false;
    for i in [1 .. Length(new)] do
      HTAdd(ht, new[i], i + len);
      if not found and lookfunc(new, new[i]) then
        o!.found := i;
        found := true;
      fi;
    od;
  fi;

  o!.scc_reps[Length(o!.scc) + 1] := x;

  Append(o!.scc_lookup, OrbSCCLookup(new) + Length(o!.scc));
  Append(o!.scc, OrbSCC(new) + len);
  Append(o!.schreiergen, new!.schreiergen);
  Add(o!.schreierpos, fail);
  for i in [2 .. Length(new)] do
    Add(o!.schreierpos, new!.schreierpos[i] + len);
  od;
  Append(o!.orbitgraph, new!.orbitgraph + len);

  Unbind(new!.scc);
  Unbind(new!.trees);
  Unbind(new!.scc_lookup);
  Unbind(new!.mults);
  Unbind(new!.schutz);
  Unbind(new!.reverse);
  Unbind(new!.rev);
  Unbind(new!.schutzstab);
  Unbind(new!.factorgroups);
  Unbind(new!.factors);
  Unbind(new!.orbitgraph);
  Unbind(new!.schreiergen);
  Unbind(new!.schreierpos);

  o!.orbits[Length(o!.orbits) + 1] := new;
  o!.lens[Length(o!.orbits)] := Length(new);

  nrorb := Length(o!.orbits);
  o!.orbschreierpos[nrorb] := pos;
  o!.orbschreiergen[nrorb] := gen;

  if pos <> fail then
    # find the component containing <pos>
    cmp := 1;
    while pos > Length(o!.orbits[cmp]) do
      pos := pos - Length(o!.orbits[cmp]);
      cmp := cmp + 1;
    od;
    o!.orbschreiercmp[nrorb] := cmp;
  else
    o!.orbschreiercmp[nrorb] := fail;
  fi;

  if ind <> fail then
    o!.orbtogen[nrorb] := ind;
  fi;
  return len + 1;
end);

# For an ideal rho orb <o>, rho value <pt> of <x>, <x> itself an element of the
# ideal, <pos> is the position in <o> of the rho value from which <x> was
# obtained by right multiplication by, the <gen>th generator of the parent of
# <o>, <ind> is the index of the generator of the ideal which we are adding (if
# applicable).
#
# This assumes that <pt> is not in <o> already, and that either:
#
#   - <pos=gen=fail> and we are updating with the <ind>th generator of the
#     *ideal*; or
#
#   - <pos>, <gen> are positive integers and <ind=fail>

InstallGlobalFunction(UpdateIdealRhoOrb,
function(o, pt, x, pos, gen, ind, lookfunc)
  local I, record, len, S, gens, new, ht, found, nrorb, cmp, i;

  I := o!.parent;
  record := ShallowCopy(RhoOrbOpts(I));
  record.schreier := true;
  record.orbitgraph := true;
  record.storenumbers := true;
  record.log := true;
  record.parent := I;
  record.treehashsize := SEMIGROUPS.OptionsRec(I).hashlen;

  len := Length(o);

  if len <> 0 then
    record.gradingfunc    := {_, x} -> HTValue(o!.ht, x) <> fail;
    record.onlygrades     := {x, _} -> not x;
    record.onlygradesdata := fail;
  fi;

  S := SupersemigroupOfIdeal(I);
  gens := List(GeneratorsOfSemigroup(S), x -> ConvertToInternalElement(S, x));
  new := Orb(gens, pt, RhoAct(I), record);
  Enumerate(new);

  ht := o!.ht;

  if lookfunc = ReturnFalse then
    for i in [1 .. Length(new)] do
      HTAdd(ht, new[i], i + len);
    od;
  else
    o!.looking := true;
    o!.found := false;
    found := false;
    for i in [1 .. Length(new)] do
      HTAdd(ht, new[i], i + len);
      if not found and lookfunc(new, new[i]) then
        o!.found := i;
        found := true;
      fi;
    od;
  fi;

  o!.scc_reps[Length(o!.scc) + 1] := x;

  Append(o!.scc_lookup, OrbSCCLookup(new) + Length(o!.scc));
  Append(o!.scc, OrbSCC(new) + len);
  Append(o!.schreiergen, new!.schreiergen);
  Add(o!.schreierpos, fail);
  for i in [2 .. Length(new)] do
    Add(o!.schreierpos, new!.schreierpos[i] + len);
  od;
  Append(o!.orbitgraph, new!.orbitgraph + len);

  Unbind(new!.scc);
  Unbind(new!.trees);
  Unbind(new!.scc_lookup);
  Unbind(new!.mults);
  Unbind(new!.schutz);
  Unbind(new!.reverse);
  Unbind(new!.rev);
  Unbind(new!.schutzstab);
  Unbind(new!.factorgroups);
  Unbind(new!.factors);
  Unbind(new!.orbitgraph);
  Unbind(new!.schreiergen);
  Unbind(new!.schreierpos);

  o!.orbits[Length(o!.orbits) + 1] := new;
  o!.lens[Length(o!.orbits)] := Length(new);

  nrorb := Length(o!.orbits);
  o!.orbschreierpos[nrorb] := pos;
  o!.orbschreiergen[nrorb] := gen;

  if pos <> fail then
    # find the component containing <pos>
    cmp := 1;
    while pos > Length(o!.orbits[cmp]) do
      pos := pos - Length(o!.orbits[cmp]);
      cmp := cmp + 1;
    od;
    o!.orbschreiercmp[nrorb] := cmp;
  else
    o!.orbschreiercmp[nrorb] := fail;
  fi;

  # jj assume that if a generator is passed into UpadateIdealRhoOrb then
  # pos = the index of the generator and ind<>fail.
  if ind <> fail then
    o!.orbtogen[nrorb] := ind;
  fi;
  return len + 1;
end);

InstallMethod(EvaluateWord, "for an ideal orb and an ideal word (Semigroups)",
[IsIdealOrb, IsList], 2,  # to beat the methods for lambda/rho orbs below
function(o, w)
  local super_gens, I, ideal_gens, res, i;
  # it is safe to use <GeneratorsOfSemigroup> here since an ideal can't be
  # obtained using <ClosureSemigroup>
  super_gens := o!.gens;
  # = GeneratorsOfSemigroup(SupersemigroupOfIdeal(o!.parent));
  I := o!.parent;
  ideal_gens := List(GeneratorsOfSemigroupIdeal(I),
                     x -> ConvertToInternalElement(I, x));
  res := ideal_gens[AbsInt(w[2])] ^ SignInt(w[2]);

  for i in [1 .. Length(w[1])] do
    res := super_gens[w[1][i]] * res;
  od;
  for i in [1 .. Length(w[3])] do
    res := res * super_gens[w[3][i]];
  od;
  return res;
end);

InstallMethod(EvaluateWord, "for a lambda orb and a word (Semigroups)",
[IsLambdaOrb, IsList], 1,  # to beat the methods for IsXCollection
{o, w} -> EvaluateWord(o!.gens, w));

InstallMethod(EvaluateWord, "for a rho orb and a word (Semigroups)",
[IsRhoOrb, IsList], 1,  # to beat the methods for IsXCollection
{o, w} -> EvaluateWord(o!.gens, w));

# returns a triple [leftword, nr, rightword] where <leftword>, <rightword> are
# words in the generators of the supersemigroup of the ideal, and <nr> is the
# index of a generator of the ideal.

InstallMethod(TraceSchreierTreeForward,
"for an inverse semigroup ideal orbit and a positive integer",
[IsInverseOrb and IsIdealOrb, IsPosInt],
function(o, i)
  local schreierpos, schreiergen, rightword, nr;

  schreierpos := o!.schreierpos;
  schreiergen := o!.schreiergen;

  rightword := [];

  while schreierpos[i] <> fail do
    Add(rightword, schreiergen[i]);
    i := schreierpos[i];
  od;

  if o!.orbtogen[i] > Length(GeneratorsOfSemigroupIdeal(o!.parent)) then
    nr := -o!.orbtogen[i] + Length(GeneratorsOfSemigroupIdeal(o!.parent));
  else
    nr := o!.orbtogen[i];
  fi;

  return [[], nr, Reversed(rightword)];
end);

# returns a triple [leftword, nr, rightword] where <leftword>, <rightword> are
# words in the generators of the supersemigroup of the ideal, and <nr> is the
# index of a generator of the ideal.

InstallMethod(TraceSchreierTreeForward,
"for an ideal orbit and positive integer",
[IsIdealOrb, IsPosInt],
function(o, i)
  local orbschreierpos, orbschreiergen, orbschreiercmp, schreierpos,
  schreiergen, leftword, rightword, nr, j;

  orbschreierpos := o!.orbschreierpos;
  orbschreiergen := o!.orbschreiergen;
  orbschreiercmp := o!.orbschreiercmp;

  schreierpos := o!.schreierpos;
  schreiergen := o!.schreiergen;

  leftword := [];
  rightword := [];

  # find the component <nr> containing <i>
  nr := 1;
  j := i;
  while j > Length(o!.orbits[nr]) do
    j := j - Length(o!.orbits[nr]);
    nr := nr + 1;
  od;

  # trace back to the start of the component
  while schreierpos[i] <> fail do
    Add(rightword, schreiergen[i]);
    i := schreierpos[i];
  od;

  while orbschreiergen[nr] <> fail do
    Add(leftword, orbschreiergen[nr]);

    i := orbschreierpos[nr];
    nr := orbschreiercmp[nr];

    while schreierpos[i] <> fail do
      Add(rightword, schreiergen[i]);
      i := schreierpos[i];
    od;

  od;

  return [Reversed(leftword), o!.orbtogen[nr], Reversed(rightword)];
end);
