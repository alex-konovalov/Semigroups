#############################################################################
##
##  greens/generic.gi
##  Copyright (C) 2016-2022                              James D. Mitchell
##
##  Licensing information can be found in the README file of this package.
##
#############################################################################
##

# This file contains methods for Green's relations and classes of semigroups
# where the particular representation of the Green's classes is not important.

#############################################################################
##
## Contents:
##
##   1. Technical Green's stuff (types, representative, etc)
##
##   2. Green's relations
##
##   3. Individual Green's classes, and equivalence classes of Green's
##      relations (constructors, size, membership)
##
##   4. Collections of Green's classes (GreensXClasses, XClassReps, NrXClasses)
##
##   5. Idempotents and NrIdempotents
##
##   6. Regularity of Green's classes
##
##   7. Properties of Green's classes
##
##   8. Iterators, enumerators etc
##
##   9. Viewing, printing, displaying
##
#############################################################################

#############################################################################
## 1. Technical Green's classes stuff . . .
#############################################################################

# This method differs from the library one in that it always returns true or
# false, whereas the library method gives an error if the types of the classes
# are not the same.  But unfortunately this disagrees with the definition of
# equality of congruences...

InstallMethod(\=, "for Green's relations",
[IsGreensRelation, IsGreensRelation], 5,  # to beat the method for congruences
function(rel1, rel2)
  if Source(rel1) <> Source(rel2) then
    return false;  # This is different than in the library
  elif IsGreensRRelation(rel1) then
    return IsGreensRRelation(rel2);
  elif IsGreensLRelation(rel1) then
    return IsGreensLRelation(rel2);
  elif IsGreensHRelation(rel1) then
    return IsGreensHRelation(rel2);
  elif IsGreensDRelation(rel1) then
    return IsGreensDRelation(rel2);
  elif IsGreensJRelation(rel1) then
    return IsGreensJRelation(rel2);
  fi;
end);

InstallMethod(\=, "for Green's classes",
[IsGreensClass, IsGreensClass],
function(x, y)
  if EquivalenceClassRelation(x) = EquivalenceClassRelation(y) then
    # the classes are of the same type
    return Parent(x) = Parent(y) and Representative(x) in y;
  fi;
  return false;
end);

InstallMethod(\<, "for Green's classes",
[IsGreensClass, IsGreensClass],
function(x, y)
  if EquivalenceClassRelation(x) = EquivalenceClassRelation(y) then
    return Parent(x) = Parent(y)
           and RepresentativeSmallest(x) < RepresentativeSmallest(y);
  fi;
  return false;
end);

InstallMethod(IsRegularDClass, "for a D-class of a semigroup",
[IsGreensDClass], IsRegularGreensClass);

InstallMethod(MultiplicativeNeutralElement,
"for a H-class of a semigroup", [IsGreensHClass],
function(H)
  if not IsGroupHClass(H) then
    return fail;
  fi;
  return Idempotents(H)[1];
end);

# The following method isn't tested anywhere, I can't think of an example to
# test it on, and hence is currently commented out.
#
# InstallMethod(IsomorphismPermGroup, "for H-class of a semigroup",
# [IsGreensHClass],
# function(H)
#   local G, x, map, inv;
#
#   if not IsGroupHClass(H) then
#     ErrorNoReturn("the argument (a Green's H-class) is not a group");
#   fi;
#
#   G := Group(());
#   for x in H do
#     x := Permutation(x, AsSet(H), OnRight);
#     if not x in G then
#       G := ClosureGroup(G, x);
#       if Size(G) = Size(H) then
#         break;
#       fi;
#     fi;
#   od;
#   map := function(x)
#     if not x in H then
#       ErrorNoReturn("the argument does not belong to the domain of the ",
#                     "function");
#     fi;
#     return Permutation(x, AsSet(H), OnRight);
#   end;
#   inv := function(x)
#     if not x in G then
#       ErrorNoReturn("the argument does not belong to the domain of the ",
#                     "function");
#     fi;
#     # This really sucks performancewise
#     return First(H, h -> map(h) = x);
#   end;
#   return SemigroupIsomorphismByFunctionNC(H, G, map, inv);
# end);

InstallMethod(StructureDescription, "for a Green's H-class",
[IsGreensHClass],
function(H)
  if not IsGroupHClass(H) then
    return fail;
  fi;
  return StructureDescription(Range(IsomorphismPermGroup(H)));
end);

#############################################################################
## 2. Green's relations
#############################################################################

# same method for ideals

InstallMethod(GreensJRelation, "for a finite semigroup",
[IsFinite and IsSemigroup], GreensDRelation);

#############################################################################
## 3. Individual classes . . .
#############################################################################

InstallMethod(IsGreensClassNC, "for a Green's class",
[IsGreensClass], ReturnFalse);

InstallMethod(OneImmutable, "for an H-class",
[IsGreensHClass],
function(H)
  if not IsGroupHClass(H) then
    TryNextMethod();
  fi;
  return Idempotents(H)[1];
end);

InstallMethod(DClass, "for an R-class", [IsGreensRClass], DClassOfRClass);
InstallMethod(DClass, "for an L-class", [IsGreensLClass], DClassOfLClass);
InstallMethod(DClass, "for an H-class", [IsGreensHClass], DClassOfHClass);
InstallMethod(LClass, "for an H-class", [IsGreensHClass], LClassOfHClass);
InstallMethod(RClass, "for an H-class", [IsGreensHClass], RClassOfHClass);

InstallMethod(GreensJClassOfElement,
"for a finite semigroup and multiplicative element",
[IsSemigroup and IsFinite, IsMultiplicativeElement], GreensDClassOfElement);

InstallMethod(GreensJClassOfElementNC,
"for a finite semigroup and multiplicative element",
[IsSemigroup and IsFinite, IsMultiplicativeElement], GreensJClassOfElement);

# Green's class of a Green's class (finer from coarser)

InstallMethod(GreensRClassOfElement,
"for a D-class and multiplicative element",
[IsGreensDClass, IsMultiplicativeElement],
{D, x} -> EquivalenceClassOfElement(GreensRRelation(Parent(D)), x));

InstallMethod(GreensLClassOfElement,
"for a D-class and multiplicative element",
[IsGreensDClass, IsMultiplicativeElement],
{D, x} -> EquivalenceClassOfElement(GreensLRelation(Parent(D)), x));

InstallMethod(GreensHClassOfElement,
"for a Green's class and multiplicative element",
[IsGreensClass, IsMultiplicativeElement],
{C, x} -> EquivalenceClassOfElement(GreensHRelation(Parent(C)), x));

InstallMethod(GreensRClassOfElementNC,
"for a finite semigroup and multiplicative element",
[IsSemigroup and IsFinite, IsMultiplicativeElement],
{S, x} -> EquivalenceClassOfElementNC(GreensRRelation(S), x));

InstallMethod(GreensLClassOfElementNC,
"for a finite semigroup and multiplicative element",
[IsSemigroup and IsFinite, IsMultiplicativeElement],
{S, x} -> EquivalenceClassOfElementNC(GreensLRelation(S), x));

InstallMethod(GreensHClassOfElementNC,
"for a finite semigroup and multiplicative element",
[IsSemigroup and IsFinite, IsMultiplicativeElement],
{S, x} -> EquivalenceClassOfElementNC(GreensHRelation(S), x));

InstallMethod(GreensDClassOfElementNC,
"for a finite semigroup and multiplicative element",
[IsSemigroup and IsFinite, IsMultiplicativeElement],
{S, x} -> EquivalenceClassOfElementNC(GreensDRelation(S), x));

# Fallback methods

InstallMethod(GreensRClassOfElementNC,
"for a D-class and multiplicative element",
[IsGreensDClass, IsMultiplicativeElement], GreensRClassOfElement);

InstallMethod(GreensLClassOfElementNC,
"for a D-class and multiplicative element",
[IsGreensDClass, IsMultiplicativeElement], GreensLClassOfElement);

InstallMethod(GreensHClassOfElementNC,
"for a Green's class and multiplicative element",
[IsGreensClass, IsMultiplicativeElement], GreensHClassOfElement);

InstallMethod(GreensJClassOfElementNC,
"for a finite semigroup and multiplicative element",
[IsSemigroup and IsFinite, IsMultiplicativeElement], GreensDClassOfElementNC);

# Green's classes of an element of a semigroup

InstallMethod(GreensRClassOfElement,
"for a possibly finite semigroup and multiplicative element",
[IsSemigroup, IsMultiplicativeElement],
RankFilter(IsFinite),  # to beat the library method for IsSemigroup and IsFinite
function(S, x)
  if not IsFinite(S) then
    TryNextMethod();
  fi;
  return EquivalenceClassOfElement(GreensRRelation(S), x);
end);

InstallMethod(GreensLClassOfElement,
"for a possibly finite semigroup and multiplicative element",
[IsSemigroup, IsMultiplicativeElement],
RankFilter(IsFinite),  # to beat the library method for IsSemigroup and IsFinite
function(S, x)
  if not IsFinite(S) then
    TryNextMethod();
  fi;
  return EquivalenceClassOfElement(GreensLRelation(S), x);
end);

InstallMethod(GreensHClassOfElement,
"for a possibly finite semigroup and multiplicative element",
[IsSemigroup, IsMultiplicativeElement],
RankFilter(IsFinite),  # to beat the library method for IsSemigroup and IsFinite
function(S, x)
  if not IsFinite(S) then
    TryNextMethod();
  fi;
  return EquivalenceClassOfElement(GreensHRelation(S), x);
end);

InstallMethod(GreensDClassOfElement,
"for a possibly finite semigroup and multiplicative element",
[IsSemigroup, IsMultiplicativeElement],
RankFilter(IsFinite),  # to beat the library method for IsSemigroup and IsFinite
function(S, x)
  if not IsFinite(S) then
    TryNextMethod();
  fi;
  return EquivalenceClassOfElement(GreensDRelation(S), x);
end);

# Green's class of a Green's class (coarser from finer)

InstallMethod(DClassOfRClass, "for an R-class of a semigroup",
[IsGreensRClass],
function(R)
  return EquivalenceClassOfElement(GreensDRelation(Parent(R)),
                                   Representative(R));
end);

InstallMethod(DClassOfLClass, "for an L-class of a semigroup",
[IsGreensLClass],
function(L)
  return EquivalenceClassOfElement(GreensDRelation(Parent(L)),
                                   Representative(L));
end);

InstallMethod(DClassOfHClass, "for an H-class of a semigroup",
[IsGreensHClass],
function(H)
  return EquivalenceClassOfElement(GreensDRelation(Parent(H)),
                                   Representative(H));
end);

InstallMethod(RClassOfHClass, "for an H-class of a semigroup",
[IsGreensHClass],
function(H)
  return EquivalenceClassOfElement(GreensRRelation(Parent(H)),
                                   Representative(H));
end);

InstallMethod(LClassOfHClass, "for an H-class of a semigroup",
[IsGreensHClass],
function(H)
  return EquivalenceClassOfElement(GreensLRelation(Parent(H)),
                                   Representative(H));
end);

#############################################################################
## 4. Collections of classes, and reps
#############################################################################

# Numbers of classes . . .

InstallMethod(NrLClasses, "for a Green's D-class",
[IsGreensDClass], D -> Length(GreensLClasses(D)));

InstallMethod(NrRClasses, "for a Green's D-class",
[IsGreensDClass], D -> Length(GreensRClasses(D)));

InstallMethod(NrHClasses, "for a Green's D-class",
[IsGreensDClass], D -> NrRClasses(D) * NrLClasses(D));

InstallMethod(NrHClasses, "for a Green's L-class",
[IsGreensLClass], L -> NrRClasses(DClassOfLClass(L)));

InstallMethod(NrHClasses, "for a Green's R-class",
[IsGreensRClass], R -> NrLClasses(DClassOfRClass(R)));

InstallMethod(NrRegularDClasses, "for a semigroup",
[IsSemigroup], S -> Length(RegularDClasses(S)));

InstallMethod(NrDClasses, "for a semigroup",
[IsSemigroup], S -> Length(GreensDClasses(S)));

InstallMethod(NrLClasses, "for a semigroup",
[IsSemigroup], S -> Length(GreensLClasses(S)));

InstallMethod(NrRClasses, "for a semigroup",
[IsSemigroup], S -> Length(GreensRClasses(S)));

InstallMethod(NrHClasses, "for a semigroup",
[IsSemigroup], S -> Length(GreensHClasses(S)));

# Representatives

InstallMethod(DClassReps, "for a semigroup",
[IsSemigroup], S -> List(GreensDClasses(S), Representative));

InstallMethod(RClassReps, "for a semigroup",
[IsSemigroup], S -> List(GreensRClasses(S), Representative));

InstallMethod(LClassReps, "for a semigroup",
[IsSemigroup], S -> List(GreensLClasses(S), Representative));

InstallMethod(HClassReps, "for a semigroup",
[IsSemigroup], S -> List(GreensHClasses(S), Representative));

InstallMethod(RClassReps, "for a Green's D-class",
[IsGreensDClass], C -> List(GreensRClasses(C), Representative));

InstallMethod(LClassReps, "for a Green's D-class",
[IsGreensDClass], C -> List(GreensLClasses(C), Representative));

InstallMethod(HClassReps, "for a Green's class",
[IsGreensClass], C -> List(GreensHClasses(C), Representative));

# Green's classes of a semigroup

InstallMethod(RegularDClasses, "for a semigroup",
[IsSemigroup], S -> Filtered(GreensDClasses(S), IsRegularDClass));

# We cannot use Left/RightCayleyDigraph below because this is only implemented
# for CanUseFroidurePin
InstallMethod(PartialOrderOfDClasses, "for a finite semigroup",
[IsSemigroup and IsFinite],
function(S)
  local L, R, D;
  L  := LeftCayleyGraphSemigroup(S);
  R  := RightCayleyGraphSemigroup(S);
  D := Digraph(IsMutableDigraph, List([1 .. Length(L)],
                                      i -> Concatenation(L[i], R[i])));
  D := QuotientDigraph(D, DigraphStronglyConnectedComponents(D).comps);
  # WW: I do not see how the ordering of the vertices of <gr> is guaranteed
  #     to match the ordering of GreensDClasses(S).
  Apply(OutNeighbours(D), Set);
  DigraphRemoveLoops(D);
  MakeImmutable(D);
  return D;
end);

InstallMethod(LeftGreensMultiplier, "for two Green's R-classes",
[IsGreensRClass, IsGreensRClass],
function(R1, R2)
  local a, b;

  if Source(R1) <> Source(R2) then
    ErrorNoReturn("the 1st and 2nd arguments (R-classes) must belong ",
                  "to the same semigroup");
  fi;

  a := Representative(R1);
  b := First(HClassReps(R1), x -> x in R2);

  if b = fail then
    ErrorNoReturn("the 1st and 2nd arguments (R-classes) do not belong ",
                  "to the same D-class");
  fi;

  return LeftGreensMultiplierNC(Source(R1), a, b);
end);

InstallMethod(RightGreensMultiplier, "for two Green's L-classes",
[IsGreensLClass, IsGreensLClass],
function(L1, L2)
  local a, b;

  if Source(L1) <> Source(L2) then
    ErrorNoReturn("the 1st and 2nd arguments (L-classes) must belong ",
                  "to the same semigroup");
  fi;

  a := Representative(L1);
  b := First(HClassReps(L1), x -> x in L2);

  if b = fail then
    ErrorNoReturn("the 1st and 2nd arguments (L-classes) do not belong ",
                  "to the same D-class");
  fi;

  return RightGreensMultiplierNC(Source(L1), a, b);
end);

InstallMethod(LeftGreensMultiplier,
"for a semigroup and L-related elements",
[IsSemigroup, IsMultiplicativeElement, IsMultiplicativeElement],
function(S, a, b)
  if not b in S or not a in LClass(S, b) then
    ErrorNoReturn("the 2nd and 3rd arguments (mult. elts.) must belong ",
                  "to the same L-class of the 1st argument (a semigroup)");
  fi;
  return LeftGreensMultiplierNC(S, a, b);
end);

InstallMethod(RightGreensMultiplier,
"for a semigroup and R-related elements",
[IsSemigroup, IsMultiplicativeElement, IsMultiplicativeElement],
function(S, a, b)
  if not b in S or not a in RClass(S, b) then
    ErrorNoReturn("the 2nd and 3rd arguments (mult. elts.) must belong ",
                  "to the same R-class of the 1st argument (a semigroup)");
  fi;
  return RightGreensMultiplierNC(S, a, b);
end);

#############################################################################
## 5. Idempotents . . .
#############################################################################

InstallMethod(NrIdempotents, "for a Green's class",
[IsGreensClass], C -> Length(Idempotents(C)));

InstallMethod(Idempotents, "for a Green's class",
[IsGreensClass], C -> Filtered(AsSet(C), IsIdempotent));

#############################################################################
## 6. Regular classes . . .
#############################################################################

InstallMethod(IsRegularGreensClass, "for a Green's class",
[IsGreensClass], C -> First(Enumerator(C), IsIdempotent) <> fail);

#############################################################################
## 7. Properties of Green's classes . . .
#############################################################################

InstallMethod(IsHTrivial, "for a Green's class",
[IsGreensClass], C -> NrHClasses(C) = Size(C));

InstallMethod(IsLTrivial, "for a Green's D-class",
[IsGreensDClass], D -> NrLClasses(D) = Size(D));

InstallMethod(IsRTrivial, "for a Green's D-class",
[IsGreensDClass], D -> NrRClasses(D) = Size(D));

#############################################################################
## 8. Enumerators, iterators etc
#############################################################################

InstallMethod(IteratorOfDClasses, "for a finite semigroup",
[IsSemigroup and IsFinite], S -> IteratorList(GreensDClasses(S)));

InstallMethod(IteratorOfRClasses, "for a finite semigroup",
[IsSemigroup and IsFinite], S -> IteratorList(GreensRClasses(S)));

#############################################################################
## 9. Viewing, printing, etc . . .
#############################################################################

# Viewing, printing, etc

InstallMethod(ViewString, "for a Green's class", [IsGreensClass],
function(C)
  local str;

  str := "\><";
  Append(str, "\>Green's\< ");

  if IsGreensDClass(C) then
    Append(str, "D");
  elif IsGreensRClass(C) then
    Append(str, "R");
  elif IsGreensLClass(C) then
    Append(str, "L");
  elif IsGreensHClass(C) then
    Append(str, "H");
  fi;
  Append(str, "-class: ");
  Append(str, ViewString(Representative(C)));
  Append(str, ">\<");

  return str;
end);

InstallMethod(ViewString, "for a Green's relation",
[IsGreensRelation], 11,  # to beat the method for congruences
function(rel)
  local str;

  str := "\><";
  Append(str, "\>Green's\< ");

  if IsGreensDRelation(rel) then
    Append(str, "D");
  elif IsGreensRRelation(rel) then
    Append(str, "R");
  elif IsGreensLRelation(rel) then
    Append(str, "L");
  elif IsGreensHRelation(rel) then
    Append(str, "H");
  fi;
  Append(str, "-relation of ");
  Append(str, ViewString(Source(rel)));
  Append(str, ">\<");

  return str;
end);

InstallMethod(ViewObj, "for a Green's relation",
[IsGreensRelation], 11,  # to beat the method for congruences
function(rel)
  Print(ViewString(rel));
  return;
end);

InstallMethod(PrintObj, "for a Green's class",
[IsGreensClass],
function(C)
  Print(PrintString(C));
  return;
end);

InstallMethod(PrintObj, "for a Green's relation",
[IsGreensRelation], 2,
function(rel)
  Print(PrintString(rel));
  return;
end);

InstallMethod(PrintString, "for a Green's class",
[IsGreensClass],
function(C)
  local str;

  str := "\>\>\>Greens";
  if IsGreensDClass(C) then
    Append(str, "D");
  elif IsGreensRClass(C) then
    Append(str, "R");
  elif IsGreensLClass(C) then
    Append(str, "L");
  elif IsGreensHClass(C) then
    Append(str, "H");
  fi;
  Append(str, "ClassOfElement\<(\>");
  Append(str, PrintString(Parent(C)));
  Append(str, ",\< \>");
  Append(str, PrintString(Representative(C)));
  Append(str, "\<)\<\<");

  return str;
end);

InstallMethod(PrintString, "for a Green's relation",
[IsGreensRelation], 2,
function(rel)
  local str;

  str := "\>\>\>Greens";
  if IsGreensDRelation(rel) then
    Append(str, "D");
  elif IsGreensRRelation(rel) then
    Append(str, "R");
  elif IsGreensLRelation(rel) then
    Append(str, "L");
  elif IsGreensHRelation(rel) then
    Append(str, "H");
  fi;
  Append(str, "Relation\<(\>\n");
  Append(str, PrintString(Source(rel)));
  Append(str, "\<)\<\<");

  return str;
end);
