###########################################################################
##
#W  fropin.gi
#Y  Copyright (C) 2015                                   James D. Mitchell
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

InstallTrueMethod(IsEnumerableSemigroupRep, 
IsSemigroup and IsGeneratorsOfEnumerableSemigroup);

# This is optional, but it is useful in several places, for example, to be able
# to use MinimalFactorization with a perm group.
InstallTrueMethod(IsEnumerableSemigroupRep, IsGroup and IsFinite);

# This should be removed ultimately, but is included now because there are too
# few methods for fp semigroup and monoids at present.
InstallTrueMethod(IsEnumerableSemigroupRep, IsFpSemigroup and IsFinite);
InstallTrueMethod(IsEnumerableSemigroupRep, IsFpMonoid and IsFinite);

InstallTrueMethod(IsEnumerableSemigroupRep, 
IsReesMatrixSubsemigroup and IsGeneratorsOfEnumerableSemigroup);

InstallTrueMethod(IsEnumerableSemigroupRep, 
IsReesZeroMatrixSubsemigroup and IsGeneratorsOfEnumerableSemigroup);

InstallTrueMethod(IsEnumerableSemigroupRep,
                  IsQuotientSemigroup and IsGeneratorsOfEnumerableSemigroup);

# Methods for IsGeneratorsOfEnumerableSemigroup
InstallTrueMethod(IsGeneratorsOfEnumerableSemigroup,
                  IsGeneratorsOfActingSemigroup);

InstallTrueMethod(IsGeneratorsOfEnumerableSemigroup,
                  IsBipartitionCollection);
InstallTrueMethod(IsGeneratorsOfEnumerableSemigroup,
                  IsTransformationCollection);
InstallTrueMethod(IsGeneratorsOfEnumerableSemigroup,
                  IsPartialPermCollection);
InstallTrueMethod(IsGeneratorsOfEnumerableSemigroup,
                  IsMatrixOverFiniteFieldCollection);

InstallTrueMethod(IsGeneratorsOfEnumerableSemigroup,
                  IsPBRCollection);

InstallTrueMethod(IsGeneratorsOfEnumerableSemigroup,
                  IsGraphInverseSubsemigroup and IsFinite);

InstallMethod(IsGeneratorsOfEnumerableSemigroup,
"for a matrix over semiring collection", [IsMatrixOverSemiringCollection],
IsGeneratorsOfSemigroup);

# The HasRows and HasColumns is currently essential due to some problems in the
# Rees(Zero)MatrixSemigroup code.

InstallImmediateMethod(IsGeneratorsOfEnumerableSemigroup,
IsReesZeroMatrixSubsemigroup and HasRows and HasColumns, 0, 
function(R)
  return IsGeneratorsOfEnumerableSemigroup([Representative(R)]);
end);

InstallMethod(IsGeneratorsOfEnumerableSemigroup,
"for a Rees 0-matrix semigroup element collection",
[IsReesZeroMatrixSemigroupElementCollection],
function(coll)
  local R;
  R := ReesMatrixSemigroupOfFamily(FamilyObj(Representative(coll)));
  return IsPermGroup(UnderlyingSemigroup(R))
    or IsEnumerableSemigroupRep(UnderlyingSemigroup(R));
end);

InstallImmediateMethod(IsGeneratorsOfEnumerableSemigroup, 
IsQuotientSemigroup and HasQuotientSemigroupPreimage, 0,
function(S)
  return IsGeneratorsOfEnumerableSemigroup(QuotientSemigroupPreimage(S));
end);

# The HasRows and HasColumns is currently essential due to some problems in the
# Rees(Zero)MatrixSemigroup code.

InstallImmediateMethod(IsGeneratorsOfEnumerableSemigroup,
IsReesMatrixSubsemigroup and HasRows and HasColumns, 0, 
function(R)
  return IsGeneratorsOfEnumerableSemigroup([Representative(R)]);
end);

InstallMethod(IsGeneratorsOfEnumerableSemigroup,
"for a Rees matrix semigroup element collection",
[IsReesMatrixSemigroupElementCollection],
function(coll)
  local R;
  R := ReesMatrixSemigroupOfFamily(FamilyObj(Representative(coll)));
  return IsPermGroup(UnderlyingSemigroup(R))
    or IsEnumerableSemigroupRep(UnderlyingSemigroup(R));
end);

InstallMethod(IsGeneratorsOfEnumerableSemigroup,
"for a free band element collection",
[IsFreeBandElementCollection],
function(coll)
  return Length(ContentOfFreeBandElementCollection(coll)) < 5;
end);

InstallMethod(IsGeneratorsOfEnumerableSemigroup,
"for a multiplicative element collection",
[IsMultiplicativeElementCollection], ReturnFalse);

# This function is used to initialise the data record for an enumerable
# semigroup which does not have a C++ implementation.

BindGlobal("INIT_FROPIN",
function(S)
  local data, hashlen, nrgens, nr, val, i;

  if (not IsSemigroup(S)) or Length(GeneratorsOfSemigroup(S)) = 0 then
    ErrorNoReturn("Semigroups: INIT_FROPIN: usage,\n",
                  "the argument must be a semigroup with at least 1 ",
                  "generator,");
  elif IsBound(S!.__en_semi_fropin) then
    return S!.__en_semi_fropin;
  fi;

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

  data.report     := SEMIGROUPS.OptionsRec(S).report;
  data.batch_size := SEMIGROUPS.OptionsRec(S).batch_size;
  hashlen         := SEMIGROUPS.OptionsRec(S).hashlen.L;

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
    if val = fail then # new generator
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
    else # duplicate generator
      data.genslookup[i] := val;
      data.nrrules := data.nrrules + 1;
      data.rules[data.nrrules] := [[i], [val]];
    fi;
  od;

  data.nr := nr;
  S!.__en_semi_fropin := data;
  return data;
end);

BIND_GLOBAL("FROPIN_GET", function(S, str)
  if not (IsBound(S!.__en_semi_fropin) 
          and IsBound(S!.__en_semi_fropin.(str))) then
    return fail;
  fi;
  return S!.__en_semi_fropin.(str);
end);

#############################################################################
# 1. Internal methods
#############################################################################

InstallMethod(AsSet, "for an enumerable semigroup with known generators",
[IsEnumerableSemigroupRep and HasGeneratorsOfSemigroup], EN_SEMI_AS_SET);

InstallMethod(EnumeratorSorted,
"for an enumerable semigroup with known generators",
[IsEnumerableSemigroupRep and HasGeneratorsOfSemigroup],
function(S)
  local enum;

  if HasAsSSortedList(S) then
    return AsSSortedList(S);
  elif Length(GeneratorsOfSemigroup(S)) = 0
      or not (IsTransformationSemigroup(S)
              or IsPartialPermSemigroup(S)
              or IsBipartitionSemigroup(S)
              or IsBooleanMatSemigroup(S)
              or IsPBRSemigroup(S)
              or IsMatrixOverSemiringSemigroup(S)) then
     # This method only works for semigroups to which the SemigroupsPlusPlus
     # code applies
    TryNextMethod();
  fi;

  enum := rec();

  enum.NumberElement := function(enum, x)
    return EN_SEMI_POSITION_SORTED(S, x);
  end;

  enum.ElementNumber := function(enum, nr)
    return EN_SEMI_ELEMENT_NUMBER_SORTED(S, nr);
  end;

  enum.Length := enum -> Size(S);

  enum.Membership := function(enum, x)
    return PositionCanonical(S, x) <> fail;
  end;

  enum.IsBound\[\] := function(enum, nr)
    return nr <= Size(S);
  end;

  enum := EnumeratorByFunctions(S, enum);
  SetIsSemigroupEnumerator(enum, true);
  SetIsSSortedList(enum, true);

  return enum;
end);

InstallMethod(IteratorSorted,
"for an enumerable semigroup with known generators",
[IsEnumerableSemigroupRep and HasGeneratorsOfSemigroup], 8,
# to beat the generic method for transformation semigroups, FIXME
function(S)
  local iter;

  if HasAsSSortedList(S) then
    return IteratorList(AsSSortedList(S));
  fi;

  iter        := rec();
  iter.pos    := 0;
  iter.parent := S;

  iter.NextIterator   := EN_SEMI_NEXT_ITERATOR_SORTED;
  iter.IsDoneIterator := EN_SEMI_IS_DONE_ITERATOR;

  iter.ShallowCopy := function(iter)
    return rec(pos := 0, parent := iter!.parent);
  end;

  return IteratorByFunctions(iter);
end);

InstallMethod(AsList, "for an enumerable semigroup with known generators",
[IsEnumerableSemigroupRep and HasGeneratorsOfSemigroup], AsListCanonical);

InstallMethod(AsListCanonical,
"for an enumerable semigroup with known generators",
[IsEnumerableSemigroupRep and HasGeneratorsOfSemigroup], EN_SEMI_AS_LIST);

# FIXME why is the next method required?
InstallMethod(AsListCanonical, "for an enumerable semigroup",
[IsEnumerableSemigroupRep],
function(S)
  GeneratorsOfSemigroup(S);
  return AsListCanonical(S);
end);

InstallMethod(Enumerator, "for an enumerable semigroup with known generators",
[IsEnumerableSemigroupRep and HasGeneratorsOfSemigroup], 2,
function(S)
  if HasAsList(S) then
    return AsList(S);
  elif Length(GeneratorsOfSemigroup(S)) = 0 then
    TryNextMethod();
  fi;
  return EnumeratorCanonical(S);
end);

InstallMethod(EnumeratorCanonical,
"for an enumerable semigroup with known generators",
[IsEnumerableSemigroupRep and HasGeneratorsOfSemigroup], 2,
# to beat the generic method for a Rees matrix semigroup, FIXME!!
function(S)
  local enum;

  if HasAsListCanonical(S) then
    return AsListCanonical(S);
  elif Length(GeneratorsOfSemigroup(S)) = 0 then
    TryNextMethod();
  fi;

  enum := rec();

  enum.NumberElement := function(enum, x)
    return PositionCanonical(S, x);
  end;

  enum.ElementNumber := function(enum, nr)
    return EN_SEMI_ELEMENT_NUMBER(S, nr);
  end;

  # FIXME this should be Size(S) hack around RZMS
  enum.Length := enum -> EN_SEMI_SIZE(S);

  enum.AsList := function(enum)
    return AsListCanonical(S);
  end;

  enum.Membership := function(x, enum)
    return PositionCanonical(S, x) <> fail;
  end;

  # FIXME this should be Size(S) hack around RZMS
  enum.IsBound\[\] := function(enum, nr)
    return nr <= EN_SEMI_SIZE(S);
  end;

  enum := EnumeratorByFunctions(S, enum);
  SetIsSemigroupEnumerator(enum, true);
  return enum;
end);

InstallMethod(ELMS_LIST, "for a semigroup enumerator and a list",
[IsSemigroupEnumerator, IsList],
function(enum, list)
  local out, y, x;

  out := [];
  for x in list do
    y := enum[x];
    if y <> fail then
      Add(out, y);
    else
      ErrorNoReturn("Semigroups: ELMS_LIST: List Elements, <list>[", x,
                    "] must have an assigned value,");
    fi;
  od;
  return out;
end);

InstallMethod(Iterator, "for semigroup enumerator sorted",
[IsSemigroupEnumerator and IsSSortedList],
function(enum)
  return IteratorSorted(UnderlyingCollection(enum));
end);

InstallMethod(Iterator, "for an enumerable semigroup with known generators",
[IsEnumerableSemigroupRep and HasGeneratorsOfSemigroup],
2, # to beat the generic method for a Rees matrix semigroup, FIXME!!
IteratorCanonical);

InstallMethod(IteratorCanonical,
"for an enumerable semigroup with known generators",
[IsEnumerableSemigroupRep and HasGeneratorsOfSemigroup],
function(S)
  local iter;

  if HasAsListCanonical(S) then
    return IteratorList(AsListCanonical(S));
  fi;

  iter        := rec();
  iter.pos    := 0;
  iter.parent := S;

  iter.NextIterator   := EN_SEMI_NEXT_ITERATOR;
  iter.IsDoneIterator := EN_SEMI_IS_DONE_ITERATOR;

  iter.ShallowCopy := function(iter)
    return rec(pos := 0, parent := S);
  end;

  return IteratorByFunctions(iter);
end);

InstallMethod(Iterator, "for semigroup enumerator",
[IsSemigroupEnumerator],
function(enum)
  return Iterator(UnderlyingCollection(enum));
end);

# different method for ideals

InstallMethod(Size, "for an enumerable semigroup with known generators",
[IsSemigroup and HasGeneratorsOfSemigroup], EN_SEMI_SIZE);

# different method for ideals

InstallMethod(\in,
"for multiplicative element and an enumerable semigroup with known generators",
[IsMultiplicativeElement,
 IsEnumerableSemigroupRep and HasGeneratorsOfSemigroup],
function(x, S)
  return PositionCanonical(S, x) <> fail;
end);

# different method for ideals

InstallMethod(Idempotents, "for an enumerable semigroup with known generators",
[IsEnumerableSemigroupRep and HasGeneratorsOfSemigroup],
function(S)
  local pos, elts;
  # Positions (canonical) of idempotents.
  pos := EN_SEMI_IDEMPOTENTS(S); 
  if HasAsListCanonical(S) then 
    # Avoids duplicating idempotents in memory in the cpp semigroup case.
    return AsListCanonical(S){pos};
  fi;
  # It could be that we fully enumerated the non-cpp semigroup but just didn't
  # call AsListCanonical.
  elts := FROPIN_GET(S, "elts");
  if elts <> fail and Length(elts) >= pos[Length(pos)] then 
    return elts{pos};
  fi;
  # Uses less memory and may be faster if we don't have AsListCanonical.
  return EnumeratorCanonical(S){pos}; 
end);

InstallMethod(PositionCanonical,
"for an enumerable semigroup with known generators and multiplicative element",
[IsEnumerableSemigroupRep and HasGeneratorsOfSemigroup,
 IsMultiplicativeElement],
function(S, x)
  if FamilyObj(x) <> ElementsFamily(FamilyObj(S)) then
    return fail;
  fi;

  if (IsTransformation(x)
      and DegreeOfTransformation(x) > DegreeOfTransformationSemigroup(S))
      or (IsPartialPerm(x)
          and DegreeOfPartialPerm(x) > DegreeOfPartialPermSemigroup(S)) then
    return fail;
  fi;

  return EN_SEMI_POSITION(S, x);
end);

InstallMethod(PositionSortedOp,
"for an enumerable semigroup with known generators and multiplicative element",
[IsEnumerableSemigroupRep and HasGeneratorsOfSemigroup,
 IsMultiplicativeElement],
function(S, x)
  local gens;

  if not (IsAssociativeElement(x) or IsMatrixOverSemiring(x))
      or FamilyObj(x) <> ElementsFamily(FamilyObj(S)) then
    return fail;
  fi;

  gens := GeneratorsOfSemigroup(S);

  if (IsTransformation(x)
      and DegreeOfTransformation(x) >
      DegreeOfTransformationCollection(gens))
      or
      (IsPartialPerm(x)
       and DegreeOfPartialPerm(x) >
       DegreeOfPartialPermCollection(gens)) then
    return fail;
  fi;
  return EN_SEMI_POSITION_SORTED(S, x);
end);

InstallMethod(Display, "for an enumerable semigroup with known generators",
[IsEnumerableSemigroupRep and HasGeneratorsOfSemigroup],
function(S)

  Print("<");
  if EN_SEMI_IS_DONE(S) then
    Print("fully ");
  else
    Print("partially ");
  fi;

  Print("enumerated semigroup with ", EN_SEMI_CURRENT_SIZE(S));
  Print(" elements, ", EN_SEMI_CURRENT_NR_RULES(S), " rules, ");
  Print("max word length ", EN_SEMI_CURRENT_MAX_WORD_LENGTH(S), ">");
  return;
end);

# the main algorithm

InstallMethod(Enumerate,
"for an enumerable semigroup with known generators and pos int",
[IsEnumerableSemigroupRep and HasGeneratorsOfSemigroup, IsPosInt],
EN_SEMI_ENUMERATE);

InstallMethod(Enumerate, "for an enumerable semigroup with known generators",
[IsEnumerableSemigroupRep and HasGeneratorsOfSemigroup],
function(S)
  return Enumerate(S, 1152921504606846975);
end);

# same method for ideals

InstallMethod(RightCayleyGraphSemigroup, "for an enumerable semigroup rep",
[IsEnumerableSemigroupRep], 3,
function(S)
  if not IsFinite(S) then
    TryNextMethod();
  fi;
  return EN_SEMI_RIGHT_CAYLEY_GRAPH(S);
end);

# same method for ideals

InstallMethod(LeftCayleyGraphSemigroup, 
"for an enumerable semigroup rep",
[IsEnumerableSemigroupRep], 3,
function(S)
  if not IsFinite(S) then
    TryNextMethod();
  fi;
  return EN_SEMI_LEFT_CAYLEY_GRAPH(S);
end);

InstallMethod(MultiplicationTable, "for an enumerable semigroup",
[IsEnumerableSemigroupRep], EN_SEMI_CAYLEY_TABLE);

InstallMethod(NrIdempotents, "for an enumerable semigroup rep",
[IsEnumerableSemigroupRep],
function(S)
  if not IsFinite(S) then
    TryNextMethod();
  elif HasIdempotents(S) then 
    return Length(Idempotents(S));
  fi;

  return EN_SEMI_NR_IDEMPOTENTS(S);
end);

InstallMethod(MinimalFactorization,
"for an enumerable semigroup and a multiplicative element",
[IsEnumerableSemigroupRep, IsMultiplicativeElement],
function(S, x)
  if not x in S then
    ErrorNoReturn("Semigroups: MinimalFactorization:\n",
                  "the second argument <x> is not an element ",
                  "of the first argument <S>,");
  fi;
  return EN_SEMI_FACTORIZATION(S, PositionCanonical(S, x));
end);