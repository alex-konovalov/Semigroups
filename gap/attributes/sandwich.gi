#############################################################################
##
##  attributes/sandwich.gi
##  Copyright (C) 2024                                    Murray T. Whyte
##
##  Licensing information can be found in the README file of this package.
##
#############################################################################
##

# This file contains an implementation of sandwich variants of semigroups.
#
# TODO: Write a method for getting generating sets for sandwich semigroups.

InstallMethod(SandwichSemigroup, "for a semigroup and an element",
[IsSemigroup, IsAssociativeElement],
function(S, a)
  local fam, sandwich, filts, type, forward, backward, map;

    if not a in S then
      ErrorNoReturn("expected 2nd argument to be an element of 1st argument");
    fi;

    fam := NewFamily("SandwichSemigroupElementsFamily",
                     IsSandwichSemigroupElement, CanEasilyCompareElements);
    sandwich := rec();
    Objectify(NewType(CollectionsFamily(fam),
                      IsSandwichSemigroup and
                      IsWholeFamily and
                      IsAttributeStoringRep),
              sandwich);
    filts := IsSandwichSemigroupElement;

    type := NewType(fam, filts);
    fam!.type := type;

    SetSandwichSemigroupOfFamily(fam, sandwich);
    SetElementsFamily(FamilyObj(sandwich), fam);

    # TODO(MTW) set the bijection from the original semigroup into the sandwich
    SetSandwichElement(sandwich, a);
    SetSandwichElement(fam, a);

    SetUnderlyingSemigroup(sandwich, S);
    SetUnderlyingSemigroup(fam, S);

    forward  := s -> SEMIGROUPS.SandwichSemigroupElementNC(sandwich, s);
    backward := s -> s![1];

    map := MappingByFunction(sandwich, S, backward, forward);
    SetInverseBijectionSandwichSemigroup(sandwich, map);

    return sandwich;
end);

SEMIGROUPS.SandwichSemigroupElementNC := function(SandwichSemigroup, s)
  return Objectify(ElementsFamily(FamilyObj(SandwichSemigroup))!.type, [s]);
end;

InstallMethod(BijectionSandwichSemigroup, "for a semigroup and an element",
[IsSemigroup, IsAssociativeElement],
function(S, a)
  local forward, backward, sandwich_S;

  sandwich_S := SandwichSemigroup(S, a);

  forward  := s -> SEMIGROUPS.SandwichSemigroupElementNC(sandwich_S, s);
  backward := s -> s![1];

  return MappingByFunction(S, sandwich_S, forward, backward);
end);

## Technical methods
InstallMethod(\*, "for sandwich semigroup elements",
IsIdenticalObj,
[IsSandwichSemigroupElement, IsSandwichSemigroupElement],
{x, y} -> Objectify(FamilyObj(x)!.type, [x![1] * SandwichElement(FamilyObj(x)) * y![1]]));

InstallMethod(\=, "for sandwich semigroup elements",
IsIdenticalObj,
[IsSandwichSemigroupElement, IsSandwichSemigroupElement],
{x, y} -> x![1] = y![1]);

InstallMethod(Size, "for a sandwich semigroup",
[IsSandwichSemigroup],
S -> Size(UnderlyingSemigroup(S)));

InstallMethod(AsList, "for a sandwich semigroup",
[IsSandwichSemigroup],
10,  # add rank to beat enumeration methods
S -> List(UnderlyingSemigroup(S), s -> SEMIGROUPS.SandwichSemigroupElementNC(S, s)));

InstallMethod(\<, "for sandwich semigroup elements",
IsIdenticalObj,
[IsSandwichSemigroupElement, IsSandwichSemigroupElement],
{x, y} -> x![1] < y![1]);

InstallMethod(AsSSortedList, "for a sandwich semigroup",
[IsSandwichSemigroup], S -> SortedList(AsList(S)));

InstallMethod(ChooseHashFunction, "for a sandwich semigroup element and int",
[IsSandwichSemigroupElement, IsInt],
function(x, data)
  local H, hashfunc;

  H        := ChooseHashFunction(x![1], data);
  hashfunc := {a, b} -> H.func(a![1], b);
  return rec(func := hashfunc, data := H.data);
end);

InstallMethod(PrintObj, "for a sandwich semigroup",
[IsSandwichSemigroup],
function(S)
# If we know the name of the underlying semigroup, it would be cool to use it
    Print("<sandwich semigroup of size ", Size(S), " and sandwich element ", SandwichElement(S), ">");
end);

InstallMethod(ViewObj, "for a sandwich semigroup",
[IsSandwichSemigroup], PrintObj);

InstallMethod(PrintObj, "for a sandwich semigroup element",
[IsSandwichSemigroupElement],
function(x)
    Print("<", x![1], " in sandwich semigroup>");
    end);

InstallMethod(ViewObj, "for a sandwich semigroup element",
[IsSandwichSemigroupElement], PrintObj);

InstallMethod(GeneratorsOfSemigroup, "for a sandwich semigroup",
[IsSandwichSemigroup],
function(S)
  local T, a, i, P, A, B, map, gens, U, D, y, j, layer, x;

    T := UnderlyingSemigroup(S);
    a := SandwichElement(S);
    i := Position(DClasses(T), DClass(T, a));
    P := PartialOrderOfDClasses(T);
    A := VerticesReachableFrom(P, i);
    AddSet(A, i);
    B := Difference(DigraphVertices(P), A);

    map := InverseGeneralMapping(InverseBijectionSandwichSemigroup(S));

    gens := [];
    for j in B do
      Append(gens, List(DClasses(T)[j], x -> x ^ map));
    od;

    U := Semigroup(gens);

    while Size(U) < Size(S) do
        for layer in DigraphLayers(P, i) do
           for j in layer do
                D := DClasses(T)[j];
                for x in D do
                    y := x ^ map;
                    if not y in U then
                        Add(gens, y);
                        U := Semigroup(gens);
                    fi;
                od;
           od;
        od;
    od;
    return gens;
end);
