###########################################################################
##
##  main/froidure-pin.gi
##  Copyright (C) 2015-2022                              James D. Mitchell
##
##  Licensing information can be found in the README file of this package.
##
#############################################################################
##

# This file contains methods for accessing the kernel level version of the
# Froidure-Pin algorithm for enumerating arbitrary semigroups.

#  For some details see:
#
#  V. Froidure, and J.-E. Pin, Algorithms for computing finite semigroups.
#  Foundations of computational mathematics (Rio de Janeiro, 1997), 112-126,
#  Springer, Berlin,  1997.

InstallMethod(CanUseFroidurePin, "for a semigroup",
[IsSemigroup], S -> CanUseGapFroidurePin(S) or
                    CanUseLibsemigroupsFroidurePin(S));

InstallMethod(HasFroidurePin, "for a semigroup",
[IsSemigroup], S -> HasGapFroidurePin(S) or
                    HasLibsemigroupsFroidurePin(S));

InstallTrueMethod(CanUseFroidurePin, CanUseGapFroidurePin);

for x in [IsMatrixOverFiniteFieldSemigroup,
          IsGraphInverseSubsemigroup,
          IsMcAlisterTripleSubsemigroup,
          IsSemigroup and IsFreeBandElementCollection,
          IsPermGroup,
          IsFreeInverseSemigroupCategory] do
  InstallTrueMethod(CanUseGapFroidurePin, x);
od;
Unbind(x);

InstallMethod(CanUseGapFroidurePin, "for a semigroup",
[IsSemigroup], ReturnFalse);

InstallTrueMethod(CanUseGapFroidurePin,
IsSemigroup and HasMultiplicationTable and HasGeneratorsOfSemigroup);

InstallImmediateMethod(CanUseGapFroidurePin,
IsReesZeroMatrixSubsemigroup and HasRowsOfReesZeroMatrixSemigroup
    and HasColumnsOfReesZeroMatrixSemigroup, 0,
function(R)
  return IsPermGroup(UnderlyingSemigroup(R))
    or CanUseFroidurePin(UnderlyingSemigroup(R));
end);

InstallImmediateMethod(CanUseGapFroidurePin,
IsReesZeroMatrixSubsemigroup and HasGeneratorsOfSemigroup, 0,
R -> CanUseFroidurePin(ParentAttr(R)));

InstallImmediateMethod(CanUseGapFroidurePin,
IsReesMatrixSubsemigroup and HasRowsOfReesMatrixSemigroup
    and HasColumnsOfReesMatrixSemigroup, 0,
function(R)
  return IsPermGroup(UnderlyingSemigroup(R))
    or CanUseFroidurePin(UnderlyingSemigroup(R));
end);

InstallImmediateMethod(CanUseGapFroidurePin,
IsReesMatrixSubsemigroup and HasGeneratorsOfSemigroup, 0,
R -> CanUseFroidurePin(ParentAttr(R)));

# The next method is supposed to catch proper subsemigroups of quotient
# semigroups
InstallImmediateMethod(CanUseGapFroidurePin,
IsAssociativeElementCollColl and HasGeneratorsOfSemigroup, 0,
function(S)
  if IsEmpty(GeneratorsOfSemigroup(S)) then
    return false;
  fi;
  return (not IsQuotientSemigroup(S))
    and IsCongruenceClass(GeneratorsOfSemigroup(S)[1]);
end);

InstallTrueMethod(CanUseGapFroidurePin,
IsSemigroupIdeal and IsReesMatrixSubsemigroup);

InstallTrueMethod(CanUseGapFroidurePin,
IsSemigroupIdeal and IsReesZeroMatrixSubsemigroup);

# Objects in IsDualSemigroupRep also CanUseGapFroidurePin but this is set
# at creation in attr/dual.gi

InstallMethod(GapFroidurePin, "for a semigroup with CanUseGapFroidurePin",
[CanUseGapFroidurePin],
function(S)
  local data, hashlen, nrgens, nr, val, i;

  data := rec(elts := [],
              final := [],
              first := [],
              found := false,
              genslookup := [],
              left := [],
              len := 1,
              lenindex := [],
              nrrules := 0,
              parent := S,
              prefix := [],
              reduced := [[]],
              right := [],
              rules := [],
              stopper := false,
              suffix := [],
              words := []);

  hashlen         := SEMIGROUPS.OptionsRec(S).hashlen;

  data.gens := ShallowCopy(GeneratorsOfSemigroup(S));
  nrgens    := Length(data.gens);
  data.ht   := HTCreate(data.gens[1], rec(treehashsize := hashlen));
  nr        := 0;
  data.one  := false;
  data.pos  := 1;
  data.lenindex[1] := 1;
  data.genstoapply := [1 .. nrgens];

  # add the generators
  for i in data.genstoapply do
    val := HTValue(data.ht, data.gens[i]);
    if val = fail then  # new generator
      nr := nr + 1;
      HTAdd(data.ht, data.gens[i], nr);
      data.elts[nr] := data.gens[i];
      data.words[nr] := [i];
      data.first[nr] := i;
      data.final[nr] := i;
      data.prefix[nr] := 0;
      data.suffix[nr] := 0;
      data.left[nr] := EmptyPlist(nrgens);
      data.right[nr] := EmptyPlist(nrgens);
      data.genslookup[i] := nr;
      data.reduced[nr] := List([1 .. nrgens], ReturnFalse);

      if data.one = false and ForAll(data.gens,
                                     y -> data.gens[i] * y = y
                                        and y * data.gens[i] = y) then
        data.one := nr;
      fi;
    else  # duplicate generator
      data.genslookup[i] := val;
      data.nrrules := data.nrrules + 1;
      data.rules[data.nrrules] := [[i], [val]];
    fi;
  od;

  data.nr := nr;
  return data;
end);

#############################################################################
# 1. Internal methods
#############################################################################

# This is a fallback method in case we don't know any better way to check this

# InstallMethod(IsFinite,
# "for a semigroup with CanUseGapFroidurePin and known generators",
# [CanUseGapFroidurePin and HasGeneratorsOfSemigroup],
# function(S)
#   return Size(S) < infinity;
# end);

InstallMethod(AsSet,
"for a semigroup with CanUseGapFroidurePin and known generators",
[CanUseGapFroidurePin and HasGeneratorsOfSemigroup],
function(S)
  if not IsFinite(S) then
    ErrorNoReturn("the argument (a semigroup) is not finite");
  fi;
  return SortedList(RUN_FROIDURE_PIN(GapFroidurePin(S), -1,
                                     InfoLevel(InfoSemigroups) > 0).elts);
end);

InstallMethod(AsList,
"for a semigroup with CanUseGapFroidurePin and known generators",
[CanUseGapFroidurePin and HasGeneratorsOfSemigroup],
AsListCanonical);

InstallMethod(AsListCanonical,
"for a semigroup with CanUseGapFroidurePin and known generators",
[CanUseGapFroidurePin and HasGeneratorsOfSemigroup],
function(S)
  if not IsFinite(S) then
    ErrorNoReturn("the argument (a semigroup) is not finite");
  fi;
  return RUN_FROIDURE_PIN(GapFroidurePin(S), -1,
                          InfoLevel(InfoSemigroups) > 0).elts;
end);

# For ideals and other generatorless semigroups

InstallMethod(AsListCanonical, "for a semigroup with CanUseGapFroidurePin",
[CanUseGapFroidurePin],
function(S)
  GeneratorsOfSemigroup(S);
  return AsListCanonical(S);
end);

InstallMethod(Enumerator,
"for a semigroup with CanUseGapFroidurePin and known generators",
[CanUseGapFroidurePin and HasGeneratorsOfSemigroup],
function(S)
  if (IsReesMatrixSubsemigroup(S) or IsReesZeroMatrixSubsemigroup(S))
      and HasIsWholeFamily(S) and IsWholeFamily(S) then
    TryNextMethod();
  fi;
  return EnumeratorCanonical(S);
end);

InstallMethod(EnumeratorSorted,
"for a semigroup with CanUseGapFroidurePin and known generators",
[CanUseGapFroidurePin and HasGeneratorsOfSemigroup],
function(S)
  if not IsFinite(S) then
    ErrorNoReturn("the argument (a semigroup) is not finite");
  fi;
  TryNextMethod();
end);

InstallMethod(EnumeratorCanonical,
"for a semigroup with CanUseGapFroidurePin",
[CanUseGapFroidurePin],
function(S)
  local enum;

  if HasAsListCanonical(S) then
    return AsListCanonical(S);
  fi;

  enum := rec();

  # TODO store S in enum and use in NumberElement
  enum.NumberElement := {enum, x} -> PositionCanonical(S, x);

  # TODO store S in enum and use it here
  enum.ElementNumber := function(_, nr)
    local fp;
    fp := GapFroidurePin(S);
    if not (IsBound(fp.elts) and nr < Length(fp.elts) and IsBound(fp.elts[nr]))
        then
      fp := RUN_FROIDURE_PIN(fp, nr, InfoLevel(InfoSemigroups) > 0);
    fi;

    if nr <= Length(fp.elts) and IsBound(fp.elts[nr]) then
      return fp.elts[nr];
    fi;
    return fail;
  end;

  # TODO store S in enum and use it here
  enum.Length := enum -> Size(S);

  # TODO store S in enum and use it here
  enum.AsList := _ -> AsListCanonical(S);

  # TODO store S in enum and use it here
  enum.Membership := {x, enum} -> PositionCanonical(S, x) <> fail;

  enum.IsBound\[\] := function(enum, nr)
    return nr <= Length(enum);
  end;

  enum := EnumeratorByFunctions(S, enum);
  SetIsSemigroupEnumerator(enum, true);
  return enum;
end);

InstallMethod(IteratorCanonical,
"for a semigroup with CanUseGapFroidurePin",
[CanUseGapFroidurePin],
S -> IteratorFiniteList(EnumeratorCanonical(S)));

InstallMethod(Iterator,
"for a semigroup with CanUseGapFroidurePin",
[CanUseGapFroidurePin],
S -> IteratorFiniteList(Enumerator(S)));

InstallMethod(IteratorSorted,
"for a semigroup with CanUseGapFroidurePin",
[CanUseGapFroidurePin],
S -> IteratorFiniteList(EnumeratorSorted(S)));

# different method for ideals

InstallMethod(Size,
"for a semigroup with CanUseGapFroidurePin and known generators",
[CanUseGapFroidurePin and HasGeneratorsOfSemigroup],
function(S)
  return Length(RUN_FROIDURE_PIN(GapFroidurePin(S), -1,
                                 InfoLevel(InfoSemigroups) > 0).elts);
end);

# different method for ideals

InstallMethod(\in,
"for mult. elt. and a semigroup with CanUseGapFroidurePin + generators",
[IsMultiplicativeElement,
 CanUseGapFroidurePin and HasGeneratorsOfSemigroup],
{x, S} -> PositionCanonical(S, x) <> fail);

# different method for ideals

InstallMethod(Idempotents,
"for a semigroup with CanUseGapFroidurePin and known generators",
[CanUseGapFroidurePin and HasGeneratorsOfSemigroup],
function(S)
  if not IsFinite(S) then
    ErrorNoReturn("the argument (a semigroup) is not finite");
  fi;
  return EnumeratorCanonical(S){IdempotentsSubset(S, [1 .. Size(S)])};
end);

InstallMethod(PositionCanonical,
"for a semigroup with CanUseGapFroidurePin, generators, and mult. elt",
[CanUseGapFroidurePin and HasGeneratorsOfSemigroup,
 IsMultiplicativeElement],
function(S, x)
  local fp, ht, nr, val, limit, pos;

  if FamilyObj(x) <> ElementsFamily(FamilyObj(S)) then
    return fail;
  fi;

  fp := GapFroidurePin(S);
  ht := fp.ht;
  nr := fp.nr;
  repeat
    val := HTValue(ht, x);
    if val <> fail then
      return val;
    fi;
    limit := nr + 1;
    fp := RUN_FROIDURE_PIN(fp, limit, InfoLevel(InfoSemigroups) > 0);
    pos := fp.pos;
    nr := fp.nr;
  until pos > nr;

  return HTValue(ht, x);
end);

# Position exists so that we can call it on objects with an uninitialised data
# structure, without first having to initialise the data structure to realise
# that <x> is not in it.

# This returns the current position of x, if it is already known to belong to
# S.

InstallMethod(Position,
"for a semigroup with CanUseGapFroidurePin, mult. element, zero cyc",
[CanUseGapFroidurePin, IsMultiplicativeElement, IsZeroCyc],
PositionOp);

InstallMethod(PositionOp,
"for a semigroup with CanUseGapFroidurePin, multi. element, zero cyc",
[CanUseGapFroidurePin, IsMultiplicativeElement, IsZeroCyc],
function(S, x, _)
  if FamilyObj(x) <> ElementsFamily(FamilyObj(S)) then
    return fail;
  fi;
  return HTValue(GapFroidurePin(S).ht, x);
end);

InstallMethod(PositionSortedOp,
"for a semigroup with CanUseGapFroidurePin, generators and mult. elt.",
[CanUseGapFroidurePin and HasGeneratorsOfSemigroup,
 IsMultiplicativeElement],
function(S, x)
  if FamilyObj(x) <> ElementsFamily(FamilyObj(S)) then
    return fail;
  elif not IsFinite(S) then
    ErrorNoReturn("the 1st argument (a semigroup) is not finite");
  fi;
  return Position(AsSet(S), x);
end);

InstallMethod(IsEnumerated, "for a semigroup with CanUseGapFroidurePin",
[CanUseGapFroidurePin],
function(S)
  local fp;
  if HasGapFroidurePin(S) then
    fp := GapFroidurePin(S);
    return fp.pos > fp.nr;
  fi;
  return false;
end);

# the main algorithm

InstallMethod(Enumerate,
"for a semigroup with CanUseGapFroidurePin and known generators and pos int",
[CanUseGapFroidurePin and HasGeneratorsOfSemigroup, IsInt],
function(S, limit)
  RUN_FROIDURE_PIN(GapFroidurePin(S), limit, InfoLevel(InfoSemigroups) > 0);
  return S;
end);

InstallMethod(Enumerate,
"for a semigroup with CanUseGapFroidurePin and known generators",
[CanUseGapFroidurePin and HasGeneratorsOfSemigroup],
S -> Enumerate(S, -1));

# same method for ideals

InstallMethod(RightCayleyGraphSemigroup,
"for a semigroup with CanUseGapFroidurePin",
[CanUseGapFroidurePin], 3,
function(S)
  if not IsFinite(S) then
    ErrorNoReturn("the argument (a semigroup) is not finite");
  fi;
  return RUN_FROIDURE_PIN(GapFroidurePin(S), -1,
                          InfoLevel(InfoSemigroups) > 0).right;
end);

InstallMethod(RightCayleyDigraph,
"for a semigroup with CanUseGapFroidurePin rep",
[CanUseGapFroidurePin],
function(S)
  local D;
  if not IsFinite(S) then
    ErrorNoReturn("the argument (a semigroup) is not finite");
  fi;

  D := DigraphNC(MakeImmutable(RightCayleyGraphSemigroup(S)));
  SetFilterObj(D, IsCayleyDigraph);
  SetSemigroupOfCayleyDigraph(D, S);
  SetGeneratorsOfCayleyDigraph(D, GeneratorsOfSemigroup(S));
  return D;
end);

# same method for ideals

InstallMethod(LeftCayleyGraphSemigroup,
"for a semigroup with CanUseGapFroidurePin",
[CanUseGapFroidurePin], 3,
function(S)
  if not IsFinite(S) then
    ErrorNoReturn("the argument (a semigroup) is not finite");
  fi;
  return RUN_FROIDURE_PIN(GapFroidurePin(S), -1,
                          InfoLevel(InfoSemigroups) > 0).left;
end);

InstallMethod(LeftCayleyDigraph,
"for a semigroup with CanUseGapFroidurePin rep",
[CanUseGapFroidurePin],
function(S)
  local D;
  if not IsFinite(S) then
    ErrorNoReturn("the argument (a semigroup) is not finite");
  fi;
  D := DigraphNC(MakeImmutable(LeftCayleyGraphSemigroup(S)));
  SetFilterObj(D, IsCayleyDigraph);
  SetSemigroupOfCayleyDigraph(D, S);
  SetGeneratorsOfCayleyDigraph(D, GeneratorsOfSemigroup(S));
  return D;
end);

InstallMethod(NrIdempotents, "for a semigroup with CanUseGapFroidurePin rep",
[CanUseGapFroidurePin],
function(S)
  if not IsFinite(S) then
    Error("the argument (a semigroup) is not finite");
  fi;
  return Length(Idempotents(S));
end);

InstallMethod(Factorization,
"for a semigroup with CanUseGapFroidurePin and a positive integer",
[CanUseGapFroidurePin, IsPosInt], MinimalFactorization);

InstallMethod(MinimalFactorization,
"for a semigroup with CanUseGapFroidurePin and a pos. int.",
[CanUseGapFroidurePin, IsPosInt],
function(S, i)
  local words;

  if i > Size(S) then
    ErrorNoReturn("the 2nd argument (a positive integer) is greater ",
                  "than the size of the 1st argument (a semigroup)");
  fi;

  words := RUN_FROIDURE_PIN(GapFroidurePin(S),
                            i + 1,
                            InfoLevel(InfoSemigroups) > 0).words;
  return ShallowCopy(words[i]);
end);

InstallMethod(MinimalFactorization,
"for a semigroup with CanUseGapFroidurePin and a multiplicative element",
[CanUseGapFroidurePin, IsMultiplicativeElement],
function(S, x)
  if not x in S then
    ErrorNoReturn("the 2nd argument (a mult. elt.) is not an element ",
                  "of the 1st argument (a semigroup)");
  fi;
  return Factorization(S, PositionCanonical(S, x));
end);

InstallMethod(Factorization,
"for a semigroup with CanUseGapFroidurePin and a multiplicative element",
[CanUseGapFroidurePin, IsMultiplicativeElement], MinimalFactorization);

InstallMethod(RulesOfSemigroup,
"for a semigroup with CanUseGapFroidurePin",
[CanUseGapFroidurePin],
function(S)
  if not IsFinite(S) then
    Error("the argument (a semigroup) is not finite");
  fi;
  return RUN_FROIDURE_PIN(GapFroidurePin(S), -1,
                          InfoLevel(InfoSemigroups) > 0).rules;
end);

InstallMethod(IdempotentsSubset,
"for a semigroup with CanUseGapFroidurePin + known generators, hom. list",
[CanUseGapFroidurePin and HasGeneratorsOfSemigroup,
 IsHomogeneousList],
function(S, list)
  local fp, left, final, prefix, elts, out, i, j, pos;

  fp := RUN_FROIDURE_PIN(GapFroidurePin(S),
                         Maximum(list) + 1,
                         InfoLevel(InfoSemigroups) > 0);
  left   := fp.left;
  final := fp.final;
  prefix := fp.prefix;
  elts := fp.elts;

  out := [];
  for pos in list do
    i := pos;
    j := pos;
    repeat
      j := left[j][final[i]];
      i := prefix[i];
    until i = 0;
    if j = pos then
      Add(out, pos);
    fi;
  od;
  return out;
end);

InstallMethod(FirstLetter,
"for a semigroup with CanUseGapFroidurePin and a pos. int.",
[CanUseGapFroidurePin, IsPosInt],
function(S, i)
  local fp;

  if i > Size(S) then
    ErrorNoReturn("the 2nd argument (a positive integer) is greater ",
                  "than the size of the 1st argument (a semigroup)");
  fi;

  fp := RUN_FROIDURE_PIN(GapFroidurePin(S),
                         i + 1,
                         InfoLevel(InfoSemigroups) > 0);
  return fp.first[i];
end);

InstallMethod(FirstLetter,
"for a semigroup with CanUseGapFroidurePin and a multiplicative element",
[CanUseGapFroidurePin, IsMultiplicativeElement],
function(S, x)
  if not x in S then
    ErrorNoReturn("the 2nd argument (a mult. elt.) is not an element ",
                  "of the 1st argument (a semigroup)");
  fi;
  return FirstLetter(S, PositionCanonical(S, x));
end);

InstallMethod(FinalLetter,
"for a semigroup with CanUseGapFroidurePin and a pos. int.",
[CanUseGapFroidurePin, IsPosInt],
function(S, i)
  local fp;

  if i > Size(S) then
    ErrorNoReturn("the 2nd argument (a positive integer) is greater ",
                  "than the size of the 1st argument (a semigroup)");
  fi;

  fp := RUN_FROIDURE_PIN(GapFroidurePin(S),
                         i + 1,
                         InfoLevel(InfoSemigroups) > 0);
  return fp.final[i];
end);

InstallMethod(FinalLetter,
"for a semigroup with CanUseGapFroidurePin and a multiplicative element",
[CanUseGapFroidurePin, IsMultiplicativeElement],
function(S, x)
  if not x in S then
    ErrorNoReturn("the 2nd argument (a mult. elt.) is not an element ",
                  "of the 1st argument (a semigroup)");
  fi;
  return FinalLetter(S, PositionCanonical(S, x));
end);

InstallMethod(Prefix,
"for a semigroup with CanUseGapFroidurePin and a pos. int.",
[CanUseGapFroidurePin, IsPosInt],
function(S, i)
  local fp;

  if i > Size(S) then
    ErrorNoReturn("the 2nd argument (a positive integer) is greater ",
                  "than the size of the 1st argument (a semigroup)");
  fi;

  fp := RUN_FROIDURE_PIN(GapFroidurePin(S),
                         i + 1,
                         InfoLevel(InfoSemigroups) > 0);
  return fp.prefix[i];
end);

InstallMethod(Prefix,
"for a semigroup with CanUseGapFroidurePin and a multiplicative element",
[CanUseGapFroidurePin, IsMultiplicativeElement],
function(S, x)
  if not x in S then
    ErrorNoReturn("the 2nd argument (a mult. elt.) is not an element ",
                  "of the 1st argument (a semigroup)");
  fi;
  return Prefix(S, PositionCanonical(S, x));
end);

InstallMethod(Suffix,
"for a semigroup with CanUseGapFroidurePin and a pos. int.",
[CanUseGapFroidurePin, IsPosInt],
function(S, i)
  local fp;

  if i > Size(S) then
    ErrorNoReturn("the 2nd argument (a positive integer) is greater ",
                  "than the size of the 1st argument (a semigroup)");
  fi;

  fp := RUN_FROIDURE_PIN(GapFroidurePin(S),
                         i + 1,
                         InfoLevel(InfoSemigroups) > 0);
  return fp.suffix[i];
end);

InstallMethod(Suffix,
"for a semigroup with CanUseGapFroidurePin and a multiplicative element",
[CanUseGapFroidurePin, IsMultiplicativeElement],
function(S, x)
  if not x in S then
    ErrorNoReturn("the 2nd argument (a mult. elt.) is not an element ",
                  "of the 1st argument (a semigroup)");
  fi;
  return Suffix(S, PositionCanonical(S, x));
end);
