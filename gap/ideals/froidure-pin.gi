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
  # TODO store I in record, and use that in the functions below
  # TODO store en in record, and use that in the functions below
  record.NumberElement := function(_, elt)
    return Position(PositionsInSupersemigroup(I), Position(en, elt));
  end;

  # TODO store I in record, and use that in the functions below
  # TODO store en in record, and use that in the functions below
  record.ElementNumber := function(_, nr)
    return en[PositionsInSupersemigroup(I)[nr]];
  end;

  # TODO store I in record, and use that in the functions below
  # TODO store en in record, and use that in the functions below
  record.IsBound\[\] := function(_, nr)
    return IsBound(PositionsInSupersemigroup(I)[nr]);
  end;

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
