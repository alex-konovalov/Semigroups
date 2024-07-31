#############################################################################
##
##  congruences/conguniv.gi
##  Copyright (C) 2015-2022                               Michael C. Young
##
##  Licensing information can be found in the README file of this package.
##
#############################################################################
##
## This file contains methods for the unique universal congruence on a
## semigroup, that is the relation SxS on a semigroup S.
##

InstallMethod(UniversalSemigroupCongruence, "for a semigroup",
[IsSemigroup],
function(S)
  local fam, C;
  fam := GeneralMappingsFamily(ElementsFamily(FamilyObj(S)),
                               ElementsFamily(FamilyObj(S)));
  C := Objectify(NewType(fam,
                         IsSemigroupCongruence
                         and IsMagmaCongruence
                         and CanComputeEquivalenceRelationPartition
                         and IsAttributeStoringRep),
                    rec());
  SetSource(C, S);
  SetRange(C, S);
  SetIsUniversalSemigroupCongruence(C, true);
  return C;
end);

InstallMethod(IsUniversalSemigroupCongruence, "for a semigroup congruence",
[IsSemigroupCongruence],
C -> NrEquivalenceClasses(C) = 1);

InstallImmediateMethod(IsUniversalSemigroupCongruence,
IsSemigroupCongruence and HasNrEquivalenceClasses, 0,
C -> NrEquivalenceClasses(C) = 1);

InstallMethod(EquivalenceRelationCanonicalLookup,
"for a universal semigroup congruence",
[IsUniversalSemigroupCongruence],
C -> ListWithIdenticalEntries(Size(Range(C)), 1));

InstallMethod(EquivalenceRelationPartition,
"for a universal semigroup congruence",
[IsUniversalSemigroupCongruence],
C -> [AsList(Range(C))]);

InstallMethod(ViewObj, "for universal semigroup congruence",
[IsUniversalSemigroupCongruence],
function(C)
  Print("<universal semigroup congruence over ");
  ViewObj(Range(C));
  Print(">");
end);

InstallMethod(\=, "for two universal semigroup congruences",
[IsUniversalSemigroupCongruence, IsUniversalSemigroupCongruence],
{lhop, rhop} -> Range(lhop) = Range(rhop));

InstallMethod(\=,
"for universal congruence and RZMS congruence by linked triple",
[IsUniversalSemigroupCongruence, IsRZMSCongruenceByLinkedTriple],
ReturnFalse);

InstallMethod(\=,
"for RZMS congruence by linked triple and universal congruence",
[IsRZMSCongruenceByLinkedTriple, IsUniversalSemigroupCongruence],
ReturnFalse);

InstallMethod(\=,
"for universal congruence and semigroup congruence with generating pairs",
[IsUniversalSemigroupCongruence,
 IsSemigroupCongruence and HasGeneratingPairsOfMagmaCongruence],
{U, C} -> Range(U) = Range(C) and NrEquivalenceClasses(C) = 1);

InstallMethod(\=,
"for universal congruence and semigroup congruence with generating pairs",
[IsSemigroupCongruence and HasGeneratingPairsOfMagmaCongruence,
 IsUniversalSemigroupCongruence],
 {C, U} -> U = C);

InstallMethod(CongruenceTestMembershipNC,
"for universal semigroup congruence and two multiplicative elements",
[IsUniversalSemigroupCongruence,
 IsMultiplicativeElement, IsMultiplicativeElement], ReturnTrue);

InstallMethod(IsSubrelation,
"for a universal semigroup congruence and a semigroup congruence",
[IsUniversalSemigroupCongruence, IsSemigroupCongruence],
function(U, C)
  if Range(U) <> Range(C) then
    Error("the 1st and 2nd arguments are congruences over different",
          " semigroups");
  fi;
  return true;
end);

InstallMethod(IsSubrelation,
"for a semigroup congruence and a universal semigroup congruence",
[IsSemigroupCongruence, IsUniversalSemigroupCongruence],
function(C, U)
  if Range(U) <> Range(C) then
    Error("the 1st and 2nd arguments are congruences over different",
          " semigroups");
  fi;
  return C = U;
end);

InstallMethod(ImagesElm,
"for universal semigroup congruence and element",
[IsUniversalSemigroupCongruence, IsMultiplicativeElement],
function(C, x)
  if not x in Range(C) then
    ErrorNoReturn("the 2nd argument (a mult. elt.) does not belong to ",
                  "the range of the 1st argument (a congruence)");
  fi;
  return AsList(Range(C));
end);

InstallMethod(NrEquivalenceClasses,
"for universal semigroup congruence",
[IsUniversalSemigroupCongruence], C -> 1);

InstallMethod(JoinSemigroupCongruences,
"for semigroup congruence and universal congruence",
[IsSemigroupCongruence, IsUniversalSemigroupCongruence],
function(C, U)
  if Range(C) <> Range(U) then
    ErrorNoReturn("cannot form the join of congruences over different",
                  " semigroups");
  fi;
  return U;
end);

InstallMethod(JoinSemigroupCongruences,
"for universal congruence and semigroup congruence",
[IsUniversalSemigroupCongruence, IsSemigroupCongruence],
function(U, C)
  if Range(C) <> Range(U) then
    ErrorNoReturn("cannot form the join of congruences over different",
                  " semigroups");
  fi;
  return U;
end);

InstallMethod(MeetSemigroupCongruences,
"for semigroup congruence and universal congruence",
[IsSemigroupCongruence, IsUniversalSemigroupCongruence],
function(C, U)
  if Range(C) <> Range(U) then
    ErrorNoReturn("cannot form the meet of congruences over different",
                  " semigroups");
  fi;
  return C;
end);

InstallMethod(MeetSemigroupCongruences,
"for universal congruence and semigroup congruence",
[IsUniversalSemigroupCongruence, IsSemigroupCongruence],
function(U, C)
  if Range(C) <> Range(U) then
    ErrorNoReturn("cannot form the meet of congruences over different",
                  " semigroups");
  fi;
  return C;
end);

InstallMethod(EquivalenceClasses, "for universal semigroup congruence",
[IsUniversalSemigroupCongruence],
C -> [EquivalenceClassOfElement(C, Representative(Range(C)))]);

InstallMethod(EquivalenceClassOfElementNC,
"for universal semigroup congruence and associative element",
[IsUniversalSemigroupCongruence, IsMultiplicativeElement],
function(C, x)
  local fam, class;
  fam := CollectionsFamily(FamilyObj(x));
  class := Objectify(NewType(fam,
                             IsUniversalSemigroupCongruenceClass
                             and IsLeftRightOrTwoSidedCongruenceClass),
                     rec());

  SetParentAttr(class, Range(C));
  SetEquivalenceClassRelation(class, C);
  SetRepresentative(class, x);

  return class;
end);

InstallMethod(\in,
"for mult. element and universal semigroup congruence class",
[IsMultiplicativeElement, IsUniversalSemigroupCongruenceClass],
{x, class} -> x in Parent(class));

# TODO(later) more \* methods for universal and non-universal congruences??
InstallMethod(\*,
"for two universal semigroup congruence classes",
[IsUniversalSemigroupCongruenceClass, IsUniversalSemigroupCongruenceClass],
function(lhop, rhop)
  if EquivalenceClassRelation(lhop) <> EquivalenceClassRelation(rhop) then
    ErrorNoReturn("the arguments (cong. classes) are not classes of the same ",
                  "congruence");
  fi;
  return lhop;
end);

InstallMethod(Size,
"for universal semigroup congruence class",
[IsUniversalSemigroupCongruenceClass],
C -> Size(Range(EquivalenceClassRelation(C))));

InstallMethod(\=,
"for two universal semigroup congruence classes",
[IsUniversalSemigroupCongruenceClass, IsUniversalSemigroupCongruenceClass],
{lhop, rhop} -> EquivalenceClassRelation(lhop) = EquivalenceClassRelation(rhop));

InstallMethod(GeneratingPairsOfMagmaCongruence,
"for universal semigroup congruence",
[IsUniversalSemigroupCongruence],
function(C)
  local S, it, z, x, m, iso, r, n, colBlocks, rowBlocks, rmscong, pairs, d;
  S := Range(C);
  if Size(S) = 1 then
    return [];
  fi;
  it := Iterator(S);
  z := MultiplicativeZero(S);
  if z <> fail then
    if IsZeroSimpleSemigroup(S) then
      # Just link zero to any non-zero element
      x := NextIterator(it);
      if x = z then
        return [[z, NextIterator(it)]];
      else
        return [[x, z]];
      fi;
    else
      # Link zero to a representative of each maximal D-class
      return List(MaximalDClasses(S), cl -> [z, Representative(cl)]);
    fi;
  fi;

  # Otherwise we have no zero: use the minimal ideal
  m := MinimalIdeal(S);

  # Use the linked triple
  iso := IsomorphismReesMatrixSemigroup(m);
  r := Range(iso);
  n := UnderlyingSemigroup(r);
  colBlocks := [[1 .. Size(Matrix(r)[1])]];
  rowBlocks := [[1 .. Size(Matrix(r))]];
  rmscong := RMSCongruenceByLinkedTriple(r, n, colBlocks, rowBlocks);
  C := CongruenceByIsomorphism(iso, rmscong);
  pairs := ShallowCopy(GeneratingPairsOfSemigroupCongruence(C));

  if IsSimpleSemigroup(S) then
    return pairs;
  fi;
  # We must relate each maximal D-class to the minimal ideal
  z := GeneratorsOfSemigroupIdeal(m)[1];
  for d in MaximalDClasses(S) do
    Add(pairs, [z, Representative(d)]);
  od;
  return pairs;
end);
