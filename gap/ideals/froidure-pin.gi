###########################################################################
##
##  ideals/froidure-pin.gi
##  Copyright (C) 2014-2022                              James D. Mitchell
##
##  Licensing information can be found in the README file of this package.
##
#############################################################################
##

# This file contains method specific to ideals of semigroups.

# We use the result of running the Froidure-Pin algorithm on the supersemigroup
# of an ideal to calculate elements, size, test membership, find idempotents,
# etc. We get a generating set and use that otherwise.

InstallMethod(PositionsInSupersemigroup,
"for a semigroup ideal with known generators",
[IsSemigroupIdeal and HasGeneratorsOfSemigroupIdeal and
 CanUseFroidurePin],
function(I)
  local S, L, R, D, result, pos, x;
  S := SupersemigroupOfIdeal(I);
  L := LeftCayleyDigraph(S);
  R := RightCayleyDigraph(S);
  D := DigraphEdgeUnion(L, R);
  # This could be better, we could use the quotient of the above graph by its
  # sccs.

  result := [];
  for x in GeneratorsOfSemigroupIdeal(I) do
    pos := PositionCanonical(S, x);
    if not pos in result then
      AddSet(result, pos);
      UniteSet(result, VerticesReachableFrom(D, pos));
    fi;
  od;

  return result;
end);

InstallMethod(PositionsInSupersemigroup,
"for a left semigroup ideal with known generators",
[IsLeftSemigroupIdeal and HasGeneratorsOfSemigroupIdeal and
 CanUseFroidurePin],
function(I)
  local S, L, result, pos, x;
  S := SupersemigroupOfIdeal(I);
  L := LeftCayleyDigraph(S);

  result := [];
  for x in GeneratorsOfSemigroupIdeal(I) do
    pos := PositionCanonical(S, x);
    if not pos in result then
      AddSet(result, pos);
      UniteSet(result, VerticesReachableFrom(L, pos));
    fi;
  od;

  return result;
end);

InstallMethod(PositionsInSupersemigroup,
"for a right semigroup ideal with known generators",
[IsRightSemigroupIdeal and HasGeneratorsOfSemigroupIdeal and
 CanUseFroidurePin],
function(I)
  local S, R, result, pos, x;
  S := SupersemigroupOfIdeal(I);
  R := RightCayleyDigraph(S);

  result := [];
  for x in GeneratorsOfSemigroupIdeal(I) do
    pos := PositionCanonical(S, x);
    if not pos in result then
      AddSet(result, pos);
      UniteSet(result, VerticesReachableFrom(R, pos));
    fi;
  od;

  return result;
end);

InstallMethod(GeneratorsOfInverseSemigroup,
"for an inverse semigroup ideal with inverse op and generators",
[IsSemigroupIdeal and IsInverseSemigroup
 and IsGeneratorsOfInverseSemigroup and HasGeneratorsOfSemigroupIdeal],
GeneratorsOfSemigroup);

InstallMethod(Enumerator,
"semigroup ideal with generators and CanUseFroidurePin",
[IsSemigroupIdeal and HasGeneratorsOfSemigroupIdeal and CanUseFroidurePin],
2,  # To beat the method for IsSemigroup and CanUseFroidurePin
function(I)
  local en, record;
  en := EnumeratorCanonical(SupersemigroupOfIdeal(I));

  record := rec();
  # TODO store en in enum
  record.NumberElement :=
  {enum, elt} -> Position(PositionsInSupersemigroup(I), Position(en, elt));

  record.ElementNumber := {enum, nr} -> en[PositionsInSupersemigroup(I)[nr]];

  record.IsBound\[\] := {enum, nr} -> IsBound(PositionsInSupersemigroup(I)[nr]);

  record.Length := enum -> Length(PositionsInSupersemigroup(I));

  return EnumeratorByFunctions(I, record);
end);

InstallMethod(Size, "for a semigroup ideal with generators",
[IsSemigroupIdeal and HasGeneratorsOfSemigroupIdeal],
I -> Length(Enumerator(I)));

InstallMethod(\in,
"for a multiplicative element and semigroup ideal with generators",
[IsMultiplicativeElement,
 IsSemigroup and CanUseFroidurePin and IsSemigroupIdeal
 and HasGeneratorsOfSemigroupIdeal],
{x, I} -> Position(Enumerator(I), x) <> fail);

# The method for GeneratorsOfSemigroup for a semigroup ideal must
# not rely in any way on the output of the Froidure-Pin algorithm when run on
# the ideal. In order to run the Froidure-Pin algorithm requires its input
# semigroup (ideal) to have a generating set, and so if the method below
# requires the output of the F-P algorithm (Green's relations, etc), then we
# get caught in an infinite loop: finding the generating set calls the F-P
# algorithm which tries to find a generating set, and so on.

InstallMethod(GeneratorsOfSemigroup, "for a semigroup ideal with generators",
[IsSemigroupIdeal and HasGeneratorsOfSemigroupIdeal],
function(I)
  local U;
  U := ClosureSemigroup(Semigroup(MinimalIdealGeneratingSet(I)),
                        Enumerator(I));
  return GeneratorsOfSemigroup(U);
end);

InstallMethod(Idempotents, "for a semigroup ideal with generators",
[IsSemigroupIdeal and HasGeneratorsOfSemigroupIdeal and CanUseFroidurePin],
function(I)
  local S, en;
  S := SupersemigroupOfIdeal(I);
  en := EnumeratorCanonical(S);
  return en{IdempotentsSubset(S, PositionsInSupersemigroup(I))};
end);
