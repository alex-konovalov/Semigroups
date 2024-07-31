###########################################################################
##
##  libsemigroups/froidure-pin.gi
##  Copyright (C) 2022                                   James D. Mitchell
##
##  Licensing information can be found in the README file of this package.
##
###########################################################################
##

# We have the following loop instead of IsMatrixOverSemiringSemigroup because
# semigroups of matrices over a finite field below to
# IsMatrixOverSemiringSemigroup, but cannot compute LibsemigroupsFroidurePin

InstallTrueMethod(CanUseFroidurePin, CanUseLibsemigroupsFroidurePin);

for x in [IsFpSemigroup,
          IsFpMonoid,
          IsTransformationSemigroup,
          IsBooleanMatSemigroup,
          IsIntegerMatrixSemigroup,
          IsIntegerMatrixMonoid,
          IsMaxPlusMatrixSemigroup,
          IsMinPlusMatrixSemigroup,
          IsTropicalMinPlusMatrixSemigroup,
          IsTropicalMaxPlusMatrixSemigroup,
          IsNTPMatrixSemigroup,
          IsProjectiveMaxPlusMatrixSemigroup,
          IsBipartitionSemigroup,
          IsPBRSemigroup,
          IsTransformationSemigroup,
          IsPartialPermSemigroup] do
  InstallTrueMethod(CanUseLibsemigroupsFroidurePin,
                    x and HasGeneratorsOfSemigroup);
  InstallTrueMethod(CanUseLibsemigroupsFroidurePin,
                    x and IsSemigroupIdeal);
od;

InstallMethod(CanUseLibsemigroupsFroidurePin, "for a semigroup", [IsSemigroup],
ReturnFalse);

InstallImmediateMethod(CanUseLibsemigroupsFroidurePin,
IsQuotientSemigroup and HasQuotientSemigroupCongruence, 0,
Q -> CanUseLibsemigroupsCongruence(QuotientSemigroupCongruence(Q)));

###########################################################################
## Function for getting the correct record from the `libsemigroups` record.
###########################################################################

DeclareOperation("FroidurePinMemFnRec", [IsSemigroup]);

InstallMethod(FroidurePinMemFnRec, "for a transformation semigroup",
[IsTransformationSemigroup],
function(S)
  if DegreeOfTransformationSemigroup(S) <= 16
      and IsBound(LIBSEMIGROUPS_HPCOMBI_ENABLED) then
    return libsemigroups.FroidurePinTransf16;
  elif DegreeOfTransformationSemigroup(S) <= 2 ^ 16 then
    return libsemigroups.FroidurePinTransfUInt2;
  elif DegreeOfTransformationSemigroup(S) <= 2 ^ 32 then
    return libsemigroups.FroidurePinTransfUInt4;
  else
    # Cannot currently test the next line
    Error("transformation degree is too high!");
  fi;
end);

InstallMethod(FroidurePinMemFnRec, "for a partial perm semigroup",
[IsPartialPermSemigroup],
function(S)
  local N;
  N := Maximum(DegreeOfPartialPermSemigroup(S),
               CodegreeOfPartialPermSemigroup(S));
  if N <= 16 and IsBound(LIBSEMIGROUPS_HPCOMBI_ENABLED) then
    return libsemigroups.FroidurePinPPerm16;
  elif N <= 2 ^ 16 then
    return libsemigroups.FroidurePinPPermUInt2;
  elif N <= 2 ^ 32 then
    return libsemigroups.FroidurePinPPermUInt4;
  else
    # Cannot currently test the next line
    Error("partial perm degree is too high!");
  fi;
end);

InstallMethod(FroidurePinMemFnRec, "for a boolean matrix semigroup",
[IsBooleanMatSemigroup],
function(S)
  local N;
  N := DimensionOfMatrixOverSemiring(Representative(S));
  if N <= 8 then
    return libsemigroups.FroidurePinBMat8;
  else
    return libsemigroups.FroidurePinBMat;
  fi;
end);

InstallMethod(FroidurePinMemFnRec, "for a bipartition semigroup",
[IsBipartitionSemigroup], S -> libsemigroups.FroidurePinBipart);

InstallMethod(FroidurePinMemFnRec, "for an integer matrix semigroup",
[IsIntegerMatrixSemigroup], S -> libsemigroups.FroidurePinIntMat);

InstallMethod(FroidurePinMemFnRec, "for an integer matrix monoid",
[IsIntegerMatrixMonoid], S -> libsemigroups.FroidurePinIntMat);

InstallMethod(FroidurePinMemFnRec, "for an max-plus matrix semigroup",
[IsMaxPlusMatrixSemigroup], S -> libsemigroups.FroidurePinMaxPlusMat);

InstallMethod(FroidurePinMemFnRec, "for an min-plus matrix semigroup",
[IsMinPlusMatrixSemigroup], S -> libsemigroups.FroidurePinMinPlusMat);

InstallMethod(FroidurePinMemFnRec, "for a tropical max-plus matrix semigroup",
[IsTropicalMaxPlusMatrixSemigroup],
S -> libsemigroups.FroidurePinMaxPlusTruncMat);

InstallMethod(FroidurePinMemFnRec, "for a tropical min-plus matrix semigroup",
[IsTropicalMinPlusMatrixSemigroup],
S -> libsemigroups.FroidurePinMinPlusTruncMat);

InstallMethod(FroidurePinMemFnRec, "for an ntp matrix semigroup",
[IsNTPMatrixSemigroup], S -> libsemigroups.FroidurePinNTPMat);

InstallMethod(FroidurePinMemFnRec,
"for a projective max-plus matrix semigroup",
[IsProjectiveMaxPlusMatrixSemigroup],
S -> libsemigroups.FroidurePinProjMaxPlusMat);

InstallMethod(FroidurePinMemFnRec, "for a pbr semigroup",
[IsPBRSemigroup], S -> libsemigroups.FroidurePinPBR);

InstallMethod(FroidurePinMemFnRec, "for an fp semigroup",
[IsFpSemigroup], S -> libsemigroups.FroidurePinBase);

InstallMethod(FroidurePinMemFnRec, "for an fp monoid",
[IsFpMonoid], S -> libsemigroups.FroidurePinBase);

InstallMethod(FroidurePinMemFnRec, "for quotient semigroup",
[IsQuotientSemigroup], S -> libsemigroups.FroidurePinBase);

BindGlobal("_GetElement",
function(coll, x)
  Assert(1, IsMultiplicativeElementCollection(coll) or IsMatrixObj(x));
  Assert(1, IsMultiplicativeElement(x) or IsMatrixObj(x));
  if IsPartialPermCollection(coll) then
    return [x, Maximum(DegreeOfPartialPermCollection(coll),
                       CodegreeOfPartialPermCollection(coll))];
  elif IsTransformationCollection(coll) then
    return [x, DegreeOfTransformationCollection(coll)];
  elif IsElementOfFpSemigroupCollection(coll) then
    return SEMIGROUPS.ExtRepObjToWord(ExtRepOfObj(x)) - 1;
  elif IsElementOfFpMonoidCollection(coll) then
    if IsOne(x) then
      return [0];
    fi;
    return SEMIGROUPS.ExtRepObjToWord(ExtRepOfObj(x));
  fi;
  return x;
end);

###########################################################################
## Constructor - constructs a libsemigroups LibsemigroupsFroidurePin object, #
## and adds the generators of the semigroup to that.
###########################################################################

InstallMethod(HasLibsemigroupsFroidurePin,
"for a semigroup with CanUseLibsemigroupsFroidurePin",
[IsSemigroup and CanUseLibsemigroupsFroidurePin],
function(S)
  return IsBound(S!.LibsemigroupsFroidurePin)
      and IsValidGapbind14Object(S!.LibsemigroupsFroidurePin);
end);

InstallMethod(HasLibsemigroupsFroidurePin,
              "for a semigroup",
              [IsSemigroup],
              ReturnFalse);

InstallGlobalFunction(LibsemigroupsFroidurePin,
function(S)
  local C, record, T, add_generator, coll, x;
  Assert(1, IsSemigroup(S));
  Assert(1, CanUseLibsemigroupsFroidurePin(S));
  if HasLibsemigroupsFroidurePin(S) then
    return S!.LibsemigroupsFroidurePin;
  elif IsFpSemigroup(S) or IsFpMonoid(S) then
    C := LibsemigroupsCongruence(UnderlyingCongruence(S));
    return libsemigroups.Congruence.quotient_froidure_pin(C);
  elif IsQuotientSemigroup(S) then
    C := QuotientSemigroupCongruence(S);
    if not HasGeneratingPairsOfMagmaCongruence(C) then
      GeneratingPairsOfMagmaCongruence(C);
    fi;
    C := LibsemigroupsCongruence(C);
    return libsemigroups.Congruence.quotient_froidure_pin(C);
  fi;
  Unbind(S!.LibsemigroupsFroidurePin);
  record := FroidurePinMemFnRec(S);
  T  := record.make();
  add_generator := record.add_generator;
  coll := GeneratorsOfSemigroup(S);
  for x in coll do
    add_generator(T, _GetElement(coll, x));
  od;
  S!.LibsemigroupsFroidurePin := T;
  return T;
end);

###########################################################################
## Size/IsFinite
###########################################################################

InstallMethod(Size, "for a semigroup with CanUseLibsemigroupsFroidurePin",
[IsSemigroup and CanUseLibsemigroupsFroidurePin],
function(S)
  if not IsFinite(S) then
    return infinity;
  fi;
  return FroidurePinMemFnRec(S).size(LibsemigroupsFroidurePin(S));
end);

InstallMethod(IsFinite, "for a semigroup with CanUseLibsemigroupsFroidurePin",
[IsSemigroup and CanUseLibsemigroupsFroidurePin],
function(S)
  if IsFpSemigroup(S) or IsFpMonoid(S) or IsQuotientSemigroup(S) then
    TryNextMethod();
  fi;
  return FroidurePinMemFnRec(S).size(LibsemigroupsFroidurePin(S)) < infinity;
end);

###########################################################################
## AsSet/AsList etc
###########################################################################

InstallMethod(AsSet, "for a semigroup with CanUseLibsemigroupsFroidurePin",
[IsSemigroup and CanUseLibsemigroupsFroidurePin],
function(S)
  local result, sorted_at, T, i;
  if not IsFinite(S) then
    Error("the argument (a semigroup) is not finite");
  elif IsPartialPermSemigroup(S) or IsFpSemigroup(S) or IsFpMonoid(S)
      or IsQuotientSemigroup(S) then
    # Special case required because < for libsemigroups PartialPerms and < for
    # GAP partial perms are different; and also for IsFpSemigroup and
    # IsFpMonoid and IsQuotientSemigroup because there's no sorted_at
    return AsSet(AsList(S));
  fi;
  result := EmptyPlist(Size(S));
  sorted_at := FroidurePinMemFnRec(S).sorted_at;
  T := LibsemigroupsFroidurePin(S);
  for i in [1 .. Size(S)] do
    result[i] := sorted_at(T, i - 1);
  od;
  SetIsSSortedList(result, true);
  return result;
end);

InstallMethod(AsListCanonical,
"for a semigroup with CanUseLibsemigroupsFroidurePin",
[IsSemigroup and CanUseLibsemigroupsFroidurePin],
function(S)
  local result, at, T, i;
  if not IsFinite(S) then
    Error("the argument (a semigroup) is not finite");
  elif IsFpSemigroup(S) or IsFpMonoid(S) or IsQuotientSemigroup(S) then
    at := {T, i} -> EvaluateWord(GeneratorsOfSemigroup(S),
                                 FroidurePinMemFnRec(S).factorisation(T, i) + 1);
  else
    at := FroidurePinMemFnRec(S).at;
  fi;
  result := EmptyPlist(Size(S));
  T := LibsemigroupsFroidurePin(S);
  for i in [1 .. Size(S)] do
    result[i] := at(T, i - 1);
  od;
  return result;
end);

InstallMethod(AsList,
"for a semigroup with CanUseLibsemigroupsFroidurePin",
[IsSemigroup and CanUseLibsemigroupsFroidurePin], AsListCanonical);

###########################################################################
## Position etc
###########################################################################

InstallMethod(PositionCanonical,
"for a semigroup with CanUseLibsemigroupsFroidurePin and mult. element",
[IsSemigroup and CanUseLibsemigroupsFroidurePin, IsMultiplicativeElement],
function(S, x)
  local T, record, word, pos, C;

  if IsPartialPermSemigroup(S) then
    if DegreeOfPartialPermSemigroup(S) < DegreeOfPartialPerm(x)
        or CodegreeOfPartialPermSemigroup(S) < CodegreeOfPartialPerm(x) then
      return fail;
    fi;
  elif IsTransformationSemigroup(S) then
    if DegreeOfTransformationSemigroup(S) < DegreeOfTransformation(x) then
      return fail;
    fi;
  elif IsFpSemigroup(S) or IsFpMonoid(S) then
    if not x in S then
      return fail;
    fi;
    T := LibsemigroupsFroidurePin(S);
    record := FroidurePinMemFnRec(S);
    word := _GetElement(S, x);
    pos := record.current_position(T, word);
    while pos < 0 do
      record.enumerate(T, record.current_size(T) + 1);
      pos := record.current_position(T, word);
    od;
    return pos + 1;
  elif IsQuotientSemigroup(S) then
    T := QuotientSemigroupPreimage(S);
    C := QuotientSemigroupCongruence(S);
    return CongruenceWordToClassIndex(C, Factorization(T, Representative(x)));
  fi;
  pos := FroidurePinMemFnRec(S).position(LibsemigroupsFroidurePin(S),
                                         _GetElement(S, x));
  if pos < 0 then
    return fail;
  fi;
  return pos + 1;
end);

InstallMethod(Position,
"for a semigroup with CanUseLibsemigroupsFroidurePin, mult. element, and zero",
[IsSemigroup and CanUseLibsemigroupsFroidurePin,
 IsMultiplicativeElement,
 IsZeroCyc],
PositionOp);

InstallMethod(PositionOp,
"for a semigroup with CanUseLibsemigroupsFroidurePin, mult. element, and zero",
[IsSemigroup and CanUseLibsemigroupsFroidurePin,
 IsMultiplicativeElement,
 IsZeroCyc],
function(S, x, _)
  local pos;
  if IsPartialPermSemigroup(S) then
    if DegreeOfPartialPermSemigroup(S) < DegreeOfPartialPerm(x)
        or CodegreeOfPartialPermSemigroup(S) < CodegreeOfPartialPerm(x) then
      return fail;
    fi;
  elif IsTransformationSemigroup(S) then
    if DegreeOfTransformationSemigroup(S) < DegreeOfTransformation(x) then
      return fail;
    fi;
  fi;

  pos := FroidurePinMemFnRec(S).current_position(LibsemigroupsFroidurePin(S),
                                                 _GetElement(S, x));
  if pos < 0 then
    return fail;
  else
    return pos + 1;
  fi;
end);

InstallMethod(PositionSortedOp,
"for a semigroup with CanUseLibsemigroupsFroidurePin and mult. element",
[IsSemigroup and CanUseLibsemigroupsFroidurePin, IsMultiplicativeElement],
function(S, x)
  local pos;
  if not IsFinite(S) then
    Error("the 1st argument (a semigroup) is not finite");
  elif IsPartialPermSemigroup(S) then
    if DegreeOfPartialPermSemigroup(S) < DegreeOfPartialPerm(x)
        or CodegreeOfPartialPermSemigroup(S) < CodegreeOfPartialPerm(x) then
      return fail;
    fi;
    # Special case required because < for libsemigroups PartialPerms and < for
    # GAP partial perms are different.
    return Position(AsSet(S), x);
  elif IsTransformationSemigroup(S) then
    if DegreeOfTransformationSemigroup(S) < DegreeOfTransformation(x) then
      return fail;
    fi;
  fi;
  pos := FroidurePinMemFnRec(S).sorted_position(LibsemigroupsFroidurePin(S),
                                                _GetElement(S, x));
  if pos < 0 then
    return fail;
  else
    return pos + 1;
  fi;
end);

###########################################################################
## Membership
###########################################################################

InstallMethod(\in,
"for mult. element and a semigroup with CanUseLibsemigroupsFroidurePin",
[IsMultiplicativeElement, IsSemigroup and CanUseLibsemigroupsFroidurePin],
{x, S} -> PositionCanonical(S, x) <> fail);

###########################################################################
## NrIdempotents
###########################################################################

InstallMethod(NrIdempotents,
"for a semigroup with CanUseLibsemigroupsFroidurePin",
[IsSemigroup and CanUseLibsemigroupsFroidurePin],
function(S)
  local F;
  if not IsFinite(S) then
    Error("the argument (a semigroup) is not finite");
  elif IsFpSemigroup(S) or IsFpMonoid(S) or IsQuotientSemigroup(S) then
    return Length(IdempotentsSubset(S, [1 .. Size(S)]));
  fi;
  F := LibsemigroupsFroidurePin(S);
  return FroidurePinMemFnRec(S).number_of_idempotents(F);
end);

InstallMethod(Idempotents,
"for a semigroup with CanUseLibsemigroupsFroidurePin",
[IsSemigroup and CanUseLibsemigroupsFroidurePin],
function(S)
  if not IsFinite(S) then
    Error("the argument (a semigroup) is not finite");
  fi;
  return FroidurePinMemFnRec(S).idempotents(LibsemigroupsFroidurePin(S));
end);

###########################################################################
## MinimalFactorization
###########################################################################

InstallMethod(MinimalFactorization,
"for a semigroup with CanUseLibsemigroupsFroidurePin and pos. int",
[IsSemigroup and CanUseLibsemigroupsFroidurePin, IsPosInt],
function(S, i)
  local F;
  F := LibsemigroupsFroidurePin(S);
  return FroidurePinMemFnRec(S).factorisation(F, i - 1) + 1;
end);

InstallMethod(MinimalFactorization,
"for a semigroup with CanUseLibsemigroupsFroidurePin and mult. element",
[IsSemigroup and CanUseLibsemigroupsFroidurePin, IsMultiplicativeElement],
function(S, x)
  if not x in S then
    Error("the 2nd argument (a mult. elt.) must belong to the ",
          "1st argument (a semigroup)");
  fi;
  return MinimalFactorization(S, PositionCanonical(S, x));
end);

InstallMethod(Factorization,
"for a semigroup with CanUseLibsemigroupsFroidurePin and pos. int",
[IsSemigroup and CanUseLibsemigroupsFroidurePin, IsPosInt],
MinimalFactorization);

InstallMethod(Factorization,
"for a semigroup with CanUseLibsemigroupsFroidurePin and mult. element",
[IsSemigroup and CanUseLibsemigroupsFroidurePin, IsMultiplicativeElement],
MinimalFactorization);

###########################################################################
## Prefixes, Suffixes, etc.
###########################################################################

InstallMethod(FirstLetter,
"for a semigroup with CanUseLibsemigroupsFroidurePin and pos. int",
[IsSemigroup and CanUseLibsemigroupsFroidurePin, IsPosInt],
function(S, i)
  local F;
  F := LibsemigroupsFroidurePin(S);
  return FroidurePinMemFnRec(S).first_letter(F, i - 1) + 1;
end);

InstallMethod(FirstLetter,
"for a semigroup with CanUseLibsemigroupsFroidurePin and mult. element",
[IsSemigroup and CanUseLibsemigroupsFroidurePin, IsMultiplicativeElement],
function(S, x)
  if not x in S then
    Error("the 2nd argument (a mult. elt.) must belong to the ",
          "1st argument (a semigroup)");
  fi;
  return FirstLetter(S, PositionCanonical(S, x));
end);

InstallMethod(FinalLetter,
"for a semigroup with CanUseLibsemigroupsFroidurePin and pos. int",
[IsSemigroup and CanUseLibsemigroupsFroidurePin, IsPosInt],
function(S, i)
  local F;
  F := LibsemigroupsFroidurePin(S);
  return FroidurePinMemFnRec(S).final_letter(F, i - 1) + 1;
end);

InstallMethod(FinalLetter,
"for a semigroup with CanUseLibsemigroupsFroidurePin and mult. element",
[IsSemigroup and CanUseLibsemigroupsFroidurePin, IsMultiplicativeElement],
function(S, x)
  if not x in S then
    Error("the 2nd argument (a mult. elt.) must belong to the ",
          "1st argument (a semigroup)");
  fi;
  return FinalLetter(S, PositionCanonical(S, x));
end);

InstallMethod(Prefix,
"for a semigroup with CanUseLibsemigroupsFroidurePin and pos. int",
[IsSemigroup and CanUseLibsemigroupsFroidurePin, IsPosInt],
function(S, i)
  local F;
  F := LibsemigroupsFroidurePin(S);
  return FroidurePinMemFnRec(S).prefix(F, i - 1) + 1;
end);

InstallMethod(Prefix,
"for a semigroup with CanUseLibsemigroupsFroidurePin and mult. element",
[IsSemigroup and CanUseLibsemigroupsFroidurePin, IsMultiplicativeElement],
function(S, x)
  if not x in S then
    Error("the 2nd argument (a mult. elt.) must belong to the ",
          "1st argument (a semigroup)");
  fi;
  return Prefix(S, PositionCanonical(S, x));
end);

InstallMethod(Suffix,
"for a semigroup with CanUseLibsemigroupsFroidurePin and pos. int",
[IsSemigroup and CanUseLibsemigroupsFroidurePin, IsPosInt],
function(S, i)
  local F;
  F := LibsemigroupsFroidurePin(S);
  return FroidurePinMemFnRec(S).suffix(F, i - 1) + 1;
end);

InstallMethod(Suffix,
"for a semigroup with CanUseLibsemigroupsFroidurePin and mult. element",
[IsSemigroup and CanUseLibsemigroupsFroidurePin, IsMultiplicativeElement],
function(S, x)
  if not x in S then
    Error("the 2nd argument (a mult. elt.) must belong to the ",
          "1st argument (a semigroup)");
  fi;
  return Suffix(S, PositionCanonical(S, x));
end);

###########################################################################
## Enumerate
###########################################################################

InstallMethod(Enumerate,
"for a semigroup with CanUseLibsemigroupsFroidurePin and pos int",
[IsSemigroup and CanUseLibsemigroupsFroidurePin, IsInt],
function(S, n)
  FroidurePinMemFnRec(S).enumerate(LibsemigroupsFroidurePin(S), n);
  return S;
end);

InstallMethod(Enumerate,
"for a semigroup with CanUseLibsemigroupsFroidurePin",
[IsSemigroup and CanUseLibsemigroupsFroidurePin],
function(S)
  FroidurePinMemFnRec(S).enumerate(LibsemigroupsFroidurePin(S), -1);
  return S;
end);

InstallMethod(IsEnumerated,
"for a semigroup with CanUseLibsemigroupsFroidurePin",
[IsSemigroup and CanUseLibsemigroupsFroidurePin],
S -> FroidurePinMemFnRec(S).finished(LibsemigroupsFroidurePin(S)));

###########################################################################
## Cayley graphs etc
###########################################################################

InstallMethod(LeftCayleyGraphSemigroup,
"for a semigroup with CanUseLibsemigroupsFroidurePin",
[IsSemigroup and CanUseLibsemigroupsFroidurePin],
function(S)
  local F;
  if not IsFinite(S) then
    Error("the argument (a semigroup) is not finite");
  fi;
  F := LibsemigroupsFroidurePin(S);
  return FroidurePinMemFnRec(S).left_cayley_graph(F) + 1;
end);

InstallMethod(LeftCayleyDigraph,
"for a semigroup with CanUseLibsemigroupsFroidurePin",
[IsSemigroup and CanUseLibsemigroupsFroidurePin],
function(S)
  local D;
  if not IsFinite(S) then
    Error("the argument (a semigroup) is not finite");
  fi;
  D := DigraphNC(LeftCayleyGraphSemigroup(S));
  SetFilterObj(D, IsCayleyDigraph);
  SetSemigroupOfCayleyDigraph(D, S);
  SetGeneratorsOfCayleyDigraph(D, GeneratorsOfSemigroup(S));
  return D;
end);

InstallMethod(RightCayleyGraphSemigroup,
"for a semigroup with CanUseLibsemigroupsFroidurePin",
[IsSemigroup and CanUseLibsemigroupsFroidurePin],
function(S)
  local F;
  if not IsFinite(S) then
    Error("the argument (a semigroup) is not finite");
  fi;
  F := LibsemigroupsFroidurePin(S);
  return FroidurePinMemFnRec(S).right_cayley_graph(F) + 1;
end);

InstallMethod(RightCayleyDigraph,
"for a semigroup with CanUseLibsemigroupsFroidurePin",
[IsSemigroup and CanUseLibsemigroupsFroidurePin],
function(S)
  local D;
  if not IsFinite(S) then
    Error("the argument (a semigroup) is not finite");
  fi;
  D := DigraphNC(RightCayleyGraphSemigroup(S));
  SetFilterObj(D, IsCayleyDigraph);
  SetSemigroupOfCayleyDigraph(D, S);
  SetGeneratorsOfCayleyDigraph(D, GeneratorsOfSemigroup(S));
  return D;
end);

########################################################################
## Enumerators
########################################################################

InstallMethod(EnumeratorSorted,
"for a semigroup with CanUseLibsemigroupsFroidurePin",
[IsSemigroup and CanUseLibsemigroupsFroidurePin],
function(S)
  local sorted_at, T, enum;

  if not IsFinite(S) then
    Error("the argument (a semigroup) is not finite");
  elif IsPartialPermSemigroup(S) or IsFpSemigroup(S) or IsFpMonoid(S)
      or IsQuotientSemigroup(S) then
    # Special case required because < for libsemigroups ParialPerms and < for
    # GAP partial perms are different.
    return AsSet(S);
  fi;

  sorted_at := FroidurePinMemFnRec(S).sorted_at;
  T := LibsemigroupsFroidurePin(S);

  enum := rec();

    # TODO S should be stored in enum, and then used below
  enum.NumberElement := function(_, x)
    return PositionSortedOp(S, x);
  end;

  enum.ElementNumber := function(_, nr)
    return sorted_at(T, nr - 1);
  end;

  enum.Length := enum -> Size(S);

  enum.Membership := function(x, _)
    return PositionCanonical(S, x) <> fail;
  end;

  enum.IsBound\[\] := function(_, nr)
    return nr <= Size(S);
  end;

  enum := EnumeratorByFunctions(S, enum);
  SetIsSemigroupEnumerator(enum, true);
  SetIsSSortedList(enum, true);

  return enum;
end);

InstallMethod(Enumerator,
"for a semigroup with CanUseLibsemigroupsFroidurePin",
[IsSemigroup and CanUseLibsemigroupsFroidurePin], 6, EnumeratorCanonical);

InstallMethod(EnumeratorCanonical,
"for a semigroup with CanUseLibsemigroupsFroidurePin",
[IsSemigroup and CanUseLibsemigroupsFroidurePin],
function(S)
  local T, enum, factorisation, at;

  if HasAsListCanonical(S) then
    return AsListCanonical(S);
  fi;

  T := LibsemigroupsFroidurePin(S);

  enum := rec();

  # TODO S should be stored in enum and used in NumberElement
  enum.NumberElement := {_, x} -> PositionCanonical(S, x);

  if IsFpSemigroup(S) or IsFpMonoid(S) or IsQuotientSemigroup(S) then
    factorisation := FroidurePinMemFnRec(S).minimal_factorisation;
    enum.ElementNumber := function(enum, nr)
      if nr > Length(enum) then
        return fail;
      fi;
      return EvaluateWord(GeneratorsOfSemigroup(S),
                          factorisation(T, nr - 1) + 1);
    end;
  else
    at := FroidurePinMemFnRec(S).at;
    enum.ElementNumber := function(enum, nr)
      if nr > Length(enum) then
        return fail;
      else
        return at(T, nr - 1);
      fi;
    end;
  fi;

  # TODO S should be stored in enum and used in Length
  enum.Length := function(_)
    if not IsFinite(S) then
      return infinity;
    else
      return Size(S);
    fi;
  end;

  # TODO S should be stored in enum and used in Membership
  enum.Membership := {x, enum} -> PositionCanonical(S, x) <> fail;

  # TODO S should be stored in enum and used in IsBound
  enum.IsBound\[\] := {enum, nr} -> nr <= Size(S);

  enum := EnumeratorByFunctions(S, enum);
  SetIsSemigroupEnumerator(enum, true);

  return enum;
end);

# The next method is necessary since it does not necessarily involve
# enumerating the entire semigroup in the case that the semigroup is partially
# enumerated and <list> only contains indices that are within the so far
# enumerated range. The default methods in the library do, because they require
# the length of the enumerator to check that the list of positions is valid.

InstallMethod(ELMS_LIST, "for a semigroup enumerator and a list",
[IsSemigroupEnumerator, IsList],
function(enum, list)
  local S, result, factorisation, at, T, i;

  S := UnderlyingCollection(enum);
  if not CanUseLibsemigroupsFroidurePin(S) then
    TryNextMethod();
  fi;
  result := EmptyPlist(Length(list));
  if IsFpSemigroup(S) or IsFpMonoid(S) or IsQuotientSemigroup(S) then
    factorisation := FroidurePinMemFnRec(S).minimal_factorisation;
    at := {T, nr} -> EvaluateWord(GeneratorsOfSemigroup(S),
                                  factorisation(T, nr) + 1);
  else
    at := FroidurePinMemFnRec(S).at;
  fi;
  T := LibsemigroupsFroidurePin(S);
  for i in list do
    Add(result, at(T, i - 1));
  od;
  return result;
end);

########################################################################
## Iterators
########################################################################

InstallMethod(IteratorCanonical,
"for a semigroup with CanUseLibsemigroupsFroidurePin",
[IsSemigroup and CanUseLibsemigroupsFroidurePin],
S -> IteratorList(EnumeratorCanonical(S)));

InstallMethod(Iterator,
"for a semigroup with CanUseLibsemigroupsFroidurePin",
[IsSemigroup and CanUseLibsemigroupsFroidurePin], IteratorCanonical);

InstallMethod(IteratorSorted,
"for a semigroup with CanUseLibsemigroupsFroidurePin",
[IsSemigroup and CanUseLibsemigroupsFroidurePin],
S -> IteratorList(EnumeratorSorted(S)));

########################################################################
## MultiplicationTable
########################################################################

InstallMethod(MultiplicationTable,
"for a semigroup with CanUseLibsemigroupsFroidurePin",
[IsSemigroup and CanUseLibsemigroupsFroidurePin],
function(S)
  local N, result, pos_to_pos_sorted, product, T, next, k, i, j;

  if not IsFinite(S) then
    Error("the argument (a semigroup) is not finite");
  fi;
  N      := Size(S);
  result := List([1 .. N], x -> EmptyPlist(N));
  T := LibsemigroupsFroidurePin(S);
  if IsFpSemigroup(S) or IsFpMonoid(S) or IsQuotientSemigroup(S) then
    pos_to_pos_sorted := {T, i} -> i;
    product := FroidurePinMemFnRec(S).product_by_reduction;
    FroidurePinMemFnRec(S).enumerate(T, N + 1);
  else
    pos_to_pos_sorted := FroidurePinMemFnRec(S).position_to_sorted_position;
    product := FroidurePinMemFnRec(S).fast_product;
  fi;
  for i in [0 .. N - 1] do
    next := result[pos_to_pos_sorted(T, i) + 1];
    for j in [0 .. N - 1] do
      k := pos_to_pos_sorted(T, j) + 1;
      next[k] := pos_to_pos_sorted(T, product(T, i, j)) + 1;
    od;
  od;
  return result;
end);

########################################################################
## ClosureSemigroupOrMonoidNC
########################################################################

# TODO(later) require a ClosureSemigroupDestructive that uses closure directly,
# not copy then closure.

InstallMethod(ClosureSemigroupOrMonoidNC,
"for fn, CanUseLibsemigroupsFroidurePin, finite list, and record",
[IsFunction,
 IsSemigroup and CanUseLibsemigroupsFroidurePin,
 IsFinite and IsList,
 IsRecord],
function(Constructor, S, coll, opts)
  local n, R, M, N, CppT, add_generator, generator, T, x, i;

  # opts must be copied and processed before calling this function
  # coll must be copied before calling this function
  if ForAll(coll, x -> x in S) then
    # To avoid copying unless necessary!
    return S;
  fi;

  if not IsMutable(coll) then
    coll := ShallowCopy(coll);
  fi;

  coll := Shuffle(coll);
  if IsGeneratorsOfActingSemigroup(coll) then
    n := ActionDegree(coll);
    Sort(coll, function(x, y)
                 return ActionRank(x, n) > ActionRank(y, n);
               end);
  elif Length(coll) < 120 then
    Sort(coll, IsGreensDGreaterThanFunc(Semigroup(coll)));
  fi;

  R := FroidurePinMemFnRec(S);

  # Perform the closure
  if IsPartialPermSemigroup(S) or IsTransformationSemigroup(S) then
    if IsPartialPermSemigroup(S) then
      M := Maximum(DegreeOfPartialPermCollection(coll),
                   CodegreeOfPartialPermCollection(coll));
      N := Maximum(DegreeOfPartialPermSemigroup(S),
                   CodegreeOfPartialPermSemigroup(S));
    else
      M := DegreeOfTransformationCollection(coll);
      N := DegreeOfTransformationSemigroup(S);
    fi;
    if M > N then
      # Can't use closure, TODO(later) use copy_closure
      # FIXME(later) if M goes larger than the type of R can support this will
      # end badly
      CppT  := R.make();
      add_generator := R.add_generator;
      for x in GeneratorsOfSemigroup(S) do
        add_generator(CppT, [x, M]);
      od;
      R.closure(CppT, List(coll, x -> [x, M]));
    else
      CppT := R.copy(LibsemigroupsFroidurePin(S));
      R.closure(CppT, List(coll, x -> [x, N]));
    fi;
  else
    CppT := R.copy(LibsemigroupsFroidurePin(S));
    R.closure(CppT, coll);
  fi;

  generator := R.generator;

  # Recover the new generating set from the closure
  coll := EmptyPlist(R.number_of_generators(CppT));
  for i in [1 .. R.number_of_generators(CppT)] do
    Add(coll, generator(CppT, i - 1));
  od;
  # Construct new semigroup so as to reset all attributes
  T := Constructor(coll, opts);
  T!.LibsemigroupsFroidurePin := CppT;
  return T;
end);

########################################################################
## New in v4
########################################################################

InstallMethod(RulesOfSemigroup,
"for a semigroup with CanUseLibsemigroupsFroidurePin",
[IsSemigroup and CanUseLibsemigroupsFroidurePin],
function(S)
  if not IsFinite(S) then
    Error("the argument (a semigroup) is not finite");
  fi;
  Enumerate(S);
  return FroidurePinMemFnRec(S).rules(LibsemigroupsFroidurePin(S)) + 1;
end);

InstallMethod(IdempotentsSubset,
"for a semigroup with CanUseLibsemigroupsFroidurePin and hom. list",
[IsSemigroup and CanUseLibsemigroupsFroidurePin, IsHomogeneousList],
function(S, list)
  local product_by_reduction, is_idempotent, T;
  if not IsFinite(S) then
    Error("the 1st argument (a semigroup) is not finite");
  elif IsFpSemigroup(S) or IsFpMonoid(S) or IsQuotientSemigroup(S) then
    product_by_reduction := FroidurePinMemFnRec(S).product_by_reduction;
    is_idempotent := {T, x} -> product_by_reduction(T, x, x) = x;
  else
    is_idempotent := FroidurePinMemFnRec(S).is_idempotent;
  fi;
  T := LibsemigroupsFroidurePin(S);
  return Filtered(list, x -> is_idempotent(T, x - 1));
end);
