###########################################################################
##
##  libsemigroups/cong.gi
##  Copyright (C) 2022                                   James D. Mitchell
##
##  Licensing information can be found in the README file of this package.
##
###########################################################################
##

## This file contains the interface to libsemigroups Congruence objects.

###########################################################################
# Categories + properties + true methods
###########################################################################

# Unless explicitly excluded below, any left, right, or 2-sided congruence
# satisfies CanUseLibsemigroupsCongruence if its range has generators and
# CanUseFroidurePin, and the congruence has GeneratingPairs. The main reason to
# exclude some types of congruences from having CanUseLibsemigroupsCongruence
# is because there are better methods specifically for that type of congruence,
# and to avoid inadvertently computing a libsemigroups Congruence object.
# Note that any congruence with generating pairs whose range/source has
# CanUseFroidurePin, can use libsemigroups Congruence objects in theory (and
# they could also in practice), but we exclude this, for the reasons above.
#
# The fundamental operation for Congruences that satisfy
# CanUseLibsemigroupsCongruence is EquivalenceRelationPartition, and any type
# of congruence not satisfying CanUseLibsemigroupsCongruence should implement
# EquivalenceRelationPartition, and then the other methods will be available.

InstallImmediateMethod(CanUseLibsemigroupsCongruence,
                       IsLeftRightOrTwoSidedCongruence
                       and HasRange,
                       0,
                       C -> CanUseFroidurePin(Range(C))
                       and HasGeneratorsOfSemigroup(Range(C))
                       or (HasIsFreeSemigroup(Range(C))
                           and IsFreeSemigroup(Range(C)))
                       or (HasIsFreeMonoid(Range(C))
                           and IsFreeMonoid(Range(C))));

InstallMethod(CanUseLibsemigroupsCongruence,
"for a left, right, or 2-sided congruence that can compute partition",
[CanComputeEquivalenceRelationPartition],
ReturnFalse);

# TODO(later) remove CanUseLibsemigroupsCongruences?

InstallTrueMethod(CanUseLibsemigroupsCongruences,
                  IsSemigroup and CanUseFroidurePin);
InstallTrueMethod(CanUseLibsemigroupsCongruences,
                  IsFpSemigroup);
InstallTrueMethod(CanUseLibsemigroupsCongruences,
                  IsFpMonoid);
InstallTrueMethod(CanUseLibsemigroupsCongruences,
                  HasIsFreeSemigroup and IsFreeSemigroup);
InstallTrueMethod(CanUseLibsemigroupsCongruences,
                  HasIsFreeMonoid and IsFreeMonoid);
InstallTrueMethod(CanUseLibsemigroupsCongruence,
                  IsInverseSemigroupCongruenceByKernelTrace);

###########################################################################
# Functions/methods that are declared in this file and that use the
# libsemigroups object directly
###########################################################################

DeclareAttribute("LibsemigroupsCongruenceConstructor",
IsSemigroup and CanUseLibsemigroupsCongruences);

# Construct a libsemigroups::Congruence from some GAP object

InstallMethod(LibsemigroupsCongruenceConstructor,
"for a transformation semigroup with CanUseLibsemigroupsCongruences",
[IsTransformationSemigroup and CanUseLibsemigroupsCongruences],
function(S)
  local N;
  N := DegreeOfTransformationSemigroup(S);
  if N <= 16 and IsBound(LIBSEMIGROUPS_HPCOMBI_ENABLED) then
    return libsemigroups.Congruence.make_from_froidurepin_leasttransf;
  elif N <= 2 ^ 16 then
    return libsemigroups.Congruence.make_from_froidurepin_transfUInt2;
  elif N <= 2 ^ 32 then
    return libsemigroups.Congruence.make_from_froidurepin_transfUInt4;
  else
    # Cannot currently test the next line
    Error("transformation degree is too high!");
  fi;
end);

InstallMethod(LibsemigroupsCongruenceConstructor,
"for a partial perm semigroup with CanUseLibsemigroupsCongruences",
[IsPartialPermSemigroup and CanUseLibsemigroupsCongruences],
function(S)
  local N;
  N := Maximum(DegreeOfPartialPermSemigroup(S),
               CodegreeOfPartialPermSemigroup(S));
  if N <= 16 and IsBound(LIBSEMIGROUPS_HPCOMBI_ENABLED) then
    return libsemigroups.Congruence.make_from_froidurepin_leastpperm;
  elif N <= 2 ^ 16 then
    return libsemigroups.Congruence.make_from_froidurepin_ppermUInt2;
  elif N <= 2 ^ 32 then
    return libsemigroups.Congruence.make_from_froidurepin_ppermUInt4;
  else
    # Cannot currently test the next line
    Error("partial perm degree is too high!");
  fi;
end);

InstallMethod(LibsemigroupsCongruenceConstructor,
"for a boolean matrix semigroup with CanUseLibsemigroupsCongruences",
[IsBooleanMatSemigroup and CanUseLibsemigroupsCongruences],
function(S)
  if DimensionOfMatrixOverSemiring(Representative(S)) <= 8 then
    return libsemigroups.Congruence.make_from_froidurepin_bmat8;
  fi;
  return libsemigroups.Congruence.make_from_froidurepin_bmat;
end);

InstallMethod(LibsemigroupsCongruenceConstructor,
"for a matrix semigroup with CanUseLibsemigroupsCongruences",
[IsMatrixOverSemiringSemigroup and CanUseLibsemigroupsCongruences],
function(_)
  # Why does this work for types other than boolean matrices?
  return libsemigroups.Congruence.make_from_froidurepin_bmat;
end);

InstallMethod(LibsemigroupsCongruenceConstructor,
"for a bipartition semigroup with CanUseLibsemigroupsCongruences",
[IsBipartitionSemigroup and CanUseLibsemigroupsCongruences],
_ -> libsemigroups.Congruence.make_from_froidurepin_bipartition);

InstallMethod(LibsemigroupsCongruenceConstructor,
"for a PBR semigroup and CanUseLibsemigroupsCongruences",
[IsPBRSemigroup and CanUseLibsemigroupsCongruences],
_ -> libsemigroups.Congruence.make_from_froidurepin_pbr);

InstallMethod(LibsemigroupsCongruenceConstructor,
"for a quotient semigroup and CanUseLibsemigroupsCongruences",
[IsQuotientSemigroup and CanUseLibsemigroupsCongruences],
_ -> libsemigroups.Congruence.make_from_froidurepinbase);

# Get the libsemigroups::Congruence object associated to a GAP object

BindGlobal("LibsemigroupsCongruence",
function(C)
  local S, make, CC, factor, N, tc, table, add_pair, pair;

  Assert(1, CanUseLibsemigroupsCongruence(C));

  if IsBound(C!.LibsemigroupsCongruence)
      and IsValidGapbind14Object(C!.LibsemigroupsCongruence) then
      # Tested in workspace tests
    return C!.LibsemigroupsCongruence;
  fi;
  Unbind(C!.LibsemigroupsCongruence);

  S  := Range(C);
  if IsFpSemigroup(S) or (HasIsFreeSemigroup(S) and IsFreeSemigroup(S))
      or IsFpMonoid(S) or (HasIsFreeMonoid(S) and IsFreeMonoid(S)) then
    make := libsemigroups.Congruence.make_from_fpsemigroup;
    CC := make(CongruenceHandednessString(C), LibsemigroupsFpSemigroup(S));
    factor := Factorization;
  elif CanUseLibsemigroupsFroidurePin(S) then
    CC := LibsemigroupsCongruenceConstructor(S)(CongruenceHandednessString(C),
                                                LibsemigroupsFroidurePin(S));
    factor := MinimalFactorization;
  elif CanUseGapFroidurePin(S) then
    N := Length(GeneratorsOfSemigroup(Range(C)));
    tc := libsemigroups.ToddCoxeter.make(CongruenceHandednessString(C));
    libsemigroups.ToddCoxeter.set_number_of_generators(tc, N);
    if IsRightMagmaCongruence(C) then
      table := RightCayleyGraphSemigroup(Range(C)) - 1;
    else
      table := LeftCayleyGraphSemigroup(Range(C)) - 1;
    fi;
    libsemigroups.ToddCoxeter.prefill(tc, table);
    CC := libsemigroups.Congruence.make_from_table(
            CongruenceHandednessString(C), "none");
    libsemigroups.Congruence.set_number_of_generators(CC, N);
    libsemigroups.Congruence.add_runner(CC, tc);
    factor := MinimalFactorization;
  else
    TryNextMethod();
  fi;
  add_pair := libsemigroups.Congruence.add_pair;
  for pair in GeneratingPairsOfLeftRightOrTwoSidedCongruence(C) do
    add_pair(CC, factor(S, pair[1]) - 1, factor(S, pair[2]) - 1);
  od;
  C!.LibsemigroupsCongruence := CC;
  return CC;
end);

########################################################################

DeclareOperation("CongruenceWordToClassIndex",
                 [CanUseLibsemigroupsCongruence, IsHomogeneousList]);
DeclareOperation("CongruenceWordToClassIndex",
                 [CanUseLibsemigroupsCongruence, IsMultiplicativeElement]);

InstallMethod(CongruenceWordToClassIndex,
"for CanUseLibsemigroupsCongruence and hom. list",
[CanUseLibsemigroupsCongruence, IsHomogeneousList],
function(C, word)
  local CC;
  CC := LibsemigroupsCongruence(C);
  return libsemigroups.Congruence.word_to_class_index(CC, word - 1) + 1;
end);

InstallMethod(CongruenceWordToClassIndex,
"for CanUseLibsemigroupsCongruence and hom. list",
[CanUseLibsemigroupsCongruence, IsMultiplicativeElement],
{C, x} -> CongruenceWordToClassIndex(C, MinimalFactorization(Range(C), x)));

########################################################################

InstallMethod(CongruenceLessNC,
"for CanUseLibsemigroupsCongruence and two mult. elements",
[CanUseLibsemigroupsCongruence,
 IsMultiplicativeElement,
 IsMultiplicativeElement],
function(C, elm1, elm2)
  local S, pos1, pos2, lookup, word1, word2, CC;

  S := Range(C);
  if CanUseFroidurePin(S) then
    pos1 := PositionCanonical(S, elm1);
    pos2 := PositionCanonical(S, elm2);
    if HasEquivalenceRelationCanonicalLookup(C) then
      lookup := EquivalenceRelationCanonicalLookup(C);
      return lookup[pos1] < lookup[pos2];
    else
      word1 := MinimalFactorization(S, pos1);
      word2 := MinimalFactorization(S, pos2);
    fi;
  elif IsFpSemigroup(S) or (HasIsFreeSemigroup(S) and IsFreeSemigroup(S))
      or IsFpMonoid(S) or (HasIsFreeMonoid(S) and IsFreeMonoid(S))
      or IsQuotientSemigroup(S) then
    word1 := Factorization(S, elm1);
    word2 := Factorization(S, elm2);
  else
    # Cannot currently test the next line
    Assert(0, false);
  fi;
  CC := LibsemigroupsCongruence(C);
  return libsemigroups.Congruence.less(CC, word1 - 1, word2 - 1);
end);

###########################################################################
# Functions/methods that are declared elsewhere and that use the
# libsemigroups object directly
###########################################################################

InstallMethod(NrEquivalenceClasses,
"for CanUseLibsemigroupsCongruence with known generating pairs",
[CanUseLibsemigroupsCongruence and
 HasGeneratingPairsOfLeftRightOrTwoSidedCongruence],
function(C)
  local number_of_classes, result;
  number_of_classes := libsemigroups.Congruence.number_of_classes;
  result := number_of_classes(LibsemigroupsCongruence(C));
  if result = -2 then
    return infinity;
  fi;
  return result;
end);

InstallMethod(CongruenceTestMembershipNC,
"for CanUseLibsemigroupsCongruence with known gen. pairs and 2 mult. elts",
[CanUseLibsemigroupsCongruence and
 HasGeneratingPairsOfLeftRightOrTwoSidedCongruence,
 IsMultiplicativeElement,
 IsMultiplicativeElement],
100,
function(C, elm1, elm2)
  local S, pos1, pos2, lookup, word1, word2, CC;

  S    := Range(C);
  if IsFpSemigroup(S) or (HasIsFreeSemigroup(S) and IsFreeSemigroup(S))
      or IsFpMonoid(S) or (HasIsFreeMonoid(S) and IsFreeMonoid(S)) then
    word1 := Factorization(S, elm1);
    word2 := Factorization(S, elm2);
  elif CanUseFroidurePin(S) then
    pos1 := PositionCanonical(S, elm1);
    pos2 := PositionCanonical(S, elm2);
    if HasEquivalenceRelationLookup(C) then
      lookup := EquivalenceRelationLookup(C);
      return lookup[pos1] = lookup[pos2];
    else
      word1 := MinimalFactorization(S, pos1);
      word2 := MinimalFactorization(S, pos2);
    fi;
  else
    # Cannot currently test the next line
    Assert(0, false);
  fi;
  CC := LibsemigroupsCongruence(C);
  return libsemigroups.Congruence.contains(CC, word1 - 1, word2 - 1);
end);

InstallMethod(EquivalenceRelationPartition,
"for CanUseLibsemigroupsCongruence with known generating pairs",
[CanUseLibsemigroupsCongruence and
 HasGeneratingPairsOfLeftRightOrTwoSidedCongruence],
function(C)
  local S, CC, ntc, gens, class, i, j;
  S := Range(C);
  if not IsFinite(S) or CanUseLibsemigroupsFroidurePin(S) then
    CC := LibsemigroupsCongruence(C);
    ntc := libsemigroups.Congruence.ntc(CC) + 1;
    gens := GeneratorsOfSemigroup(S);
    for i in [1 .. Length(ntc)] do
      class := ntc[i];
      for j in [1 .. Length(class)] do
        class[j] := EvaluateWord(gens, class[j]);
      od;
    od;
    return ntc;
  elif CanUseGapFroidurePin(S) then
    # in this case libsemigroups.Congruence.ntc doesn't work, because S is not
    # represented in the libsemigroups object
    return Filtered(EquivalenceRelationPartitionWithSingletons(C),
                    x -> Size(x) > 1);
  fi;
  TryNextMethod();
end);

# Methods for congruence classes

InstallMethod(\<,
"for congruence classes of CanUseLibsemigroupsCongruence", IsIdenticalObj,
[IsLeftRightOrTwoSidedCongruenceClass, IsLeftRightOrTwoSidedCongruenceClass],
1,  # to beat the method in congruences/cong.gi for
    # IsLeftRightOrTwoSidedCongruenceClass
function(class1, class2)
  local C, word1, word2, CC;

  C := EquivalenceClassRelation(class1);
  if not CanUseLibsemigroupsCongruence(C)
      or not HasGeneratingPairsOfLeftRightOrTwoSidedCongruence(C) then
    TryNextMethod();
  elif C <> EquivalenceClassRelation(class2) then
    return false;
  fi;

  word1 := Factorization(Range(C), Representative(class1));
  word2 := Factorization(Range(C), Representative(class2));
  CC := LibsemigroupsCongruence(C);
  return libsemigroups.Congruence.less(CC, word1 - 1, word2 - 1);
end);

InstallMethod(EquivalenceClasses,
"for CanUseLibsemigroupsCongruence with known generating pairs",
[CanUseLibsemigroupsCongruence and
 HasGeneratingPairsOfLeftRightOrTwoSidedCongruence],
function(C)
  local result, CC, gens, class_index_to_word, rep, i;

  if NrEquivalenceClasses(C) = infinity then
    ErrorNoReturn("the argument (a congruence) must have a finite ",
                  "number of classes");
  fi;

  result := EmptyPlist(NrEquivalenceClasses(C));
  CC := LibsemigroupsCongruence(C);
  gens := GeneratorsOfSemigroup(Range(C));
  class_index_to_word := libsemigroups.Congruence.class_index_to_word;
  for i in [1 .. NrEquivalenceClasses(C)] do
    rep := EvaluateWord(gens, class_index_to_word(CC, i - 1) + 1);
    result[i] := EquivalenceClassOfElementNC(C, rep);
  od;
  return result;
end);

###########################################################################
# Methods NOT using libsemigroups object directly but that use an
# operation or function that only applies to CanUseLibsemigroupsCongruence
###########################################################################

InstallMethod(EquivalenceRelationPartitionWithSingletons,
"for CanUseLibsemigroupsCongruence with known generating pairs",
[CanUseLibsemigroupsCongruence and
 HasGeneratingPairsOfLeftRightOrTwoSidedCongruence],
function(C)
  local part, word, i, x;
  if not IsFinite(Range(C)) then
    ErrorNoReturn("the argument (a congruence) must have finite range");
  fi;

  part := [];
  for x in Range(C) do
    word := MinimalFactorization(Range(C), x);
    i := CongruenceWordToClassIndex(C, word);
    if not IsBound(part[i]) then
      part[i] := [];
    fi;
    Add(part[i], x);
  od;

  return part;
end);

InstallMethod(ImagesElm,
"for CanUseLibsemigroupsCongruence with known gen. pairs and a mult. elt.",
[CanUseLibsemigroupsCongruence and
 HasGeneratingPairsOfLeftRightOrTwoSidedCongruence, IsMultiplicativeElement],
function(cong, elm)
  local lookup, id, part, pos;

  if HasIsFinite(Range(cong)) and IsFinite(Range(cong))
      and CanUseFroidurePin(Range(cong)) then
    lookup := EquivalenceRelationCanonicalLookup(cong);
    id     := lookup[PositionCanonical(Range(cong), elm)];
    return EnumeratorCanonical(Range(cong)){Positions(lookup, id)};
  elif IsFpSemigroup(Range(cong))
      or (HasIsFreeSemigroup(Range(cong)) and IsFreeSemigroup(Range(cong)))
      or IsFpMonoid(Range(cong))
      or (HasIsFreeSemigroup(Range(cong)) and IsFreeMonoid(Range(cong)))
      or IsQuotientSemigroup(Range(cong)) then
    part := EquivalenceRelationPartition(cong);
    pos := PositionProperty(part, l -> [elm, l[1]] in cong);
    if pos = fail then
      return [elm];  # singleton
    fi;
    return part[pos];  # non-singleton
  fi;
  # Shouldn't be able to reach here
  Assert(0, false);
end);
