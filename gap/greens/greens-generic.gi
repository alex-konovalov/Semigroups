#############################################################################
##
#W  greens-generic.gi
#Y  Copyright (C) 2015                                   James D. Mitchell
##
##  Licensing information can be found in the README file of this package.
##
#############################################################################
##

# This file contains methods for Green's relations and classes of semigroups
# that satisfy IsSemigroup.

#############################################################################
## This file contains methods for Green's classes etc for arbitrary finite
## semigroups.
##
## It is organized as follows:
##
##   1. Helper functions for the creation of Green's classes, and lambda-rho
##      stuff.
##
##   2. Technical Green's stuff (types, representative, etc)
##
##   3. Green's relations
##
##   4. Individual Green's classes, and equivalence classes of Green's
##      relations (constructors, size, membership)
##
##   5. Collections of Green's classes (GreensXClasses, XClassReps, NrXClasses)
##
##   6. Idempotents and NrIdempotents
##
##   7. Regularity of Green's classes
##
##   8. Iterators, enumerators etc
##
##   9. Viewing, printing, displaying
##
#############################################################################

#############################################################################
## The main idea is to store all of the information about all Green's classes
## of a particular type in the corresponding Green's relation. An individual
## Green's class only stores the index of the equivalence class corresponding
## to the Green's class, then looks everything up in the data contained in the
## Green's relation. The equivalence class data structures for R-, L-, H-,
## D-classes of a finite semigroup <S> are stored in the !.data component of
## the corresponding Green's relation.
#############################################################################

#############################################################################
## 1. Helper functions for the creation of Green's classes/relations . . .
#############################################################################

# there are no methods for EquivalenceClassOfElementNC in this case since we
# require the variable <pos> below, and if it can't be determined, then we
# can't make the Green's class.

SEMIGROUPS.EquivalenceClassOfElement := function(rel, rep, type)
  local pos, out, S;

  pos := Position(Source(rel), rep);
  if pos = fail then
    ErrorNoReturn("Semigroups: SEMIGROUPS.EquivalenceClassOfElement: usage,\n",
                  "the element in the 2nd argument does not belong to the ",
                  "semigroup,");
  fi;

  out := rec();
  S := Source(rel);
  # TODO set IsInverseOpClass here???
  ObjectifyWithAttributes(out, type(S), EquivalenceClassRelation, rel,
                          Representative, rep, ParentAttr, S);

  out!.index := rel!.data.id[pos];

  return out;
end;

SEMIGROUPS.GreensXClasses := function(S,
                                      GreensXRelation,
                                      GreensXClassOfElement)
  local comps, elts, out, C, i;

  comps := GreensXRelation(S)!.data.comps;
  elts := SEMIGROUP_AS_LIST(GenericSemigroupData(S));
  out := EmptyPlist(Length(comps));

  for i in [1 .. Length(comps)] do
    C := GreensXClassOfElement(S, elts[comps[i][1]]);
    C!.index := i;
    out[i] := C;
  od;
  return out;
end;

SEMIGROUPS.XClassReps := function(S, GreensXRelation)
  local comps, elts, out, i;

  comps := GreensXRelation(S)!.data.comps;
  elts := SEMIGROUP_AS_LIST(GenericSemigroupData(S));
  out := EmptyPlist(Length(comps));
  for i in [1 .. Length(comps)] do
    out[i] := elts[comps[i][1]];
  od;
  return out;
end;

SEMIGROUPS.GreensXClassesOfClass := function(C,
                                             GreensXRelation,
                                             GreensXClassOfElement)
  local S, comp, id, seen, elts, out, i;

  S := Parent(C);
  comp := EquivalenceClassRelation(C)!.data.comps[C!.index];
  id := GreensXRelation(Parent(C))!.data.id;
  seen := BlistList([1 .. Maximum(id)], []);
  elts := SEMIGROUP_AS_LIST(GenericSemigroupData(S));
  out := EmptyPlist(Length(comp));

  for i in comp do
    if not seen[id[i]] then
      seen[id[i]] := true;
      C := GreensXClassOfElement(S, elts[i]);
      C!.index := id[i];
      Add(out, C);
    fi;
  od;

  return out;
end;

SEMIGROUPS.XClassRepsOfClass := function(C, GreensXRelation)
  local S, comp, id, seen, elts, out, i;

  S := Parent(C);
  comp := EquivalenceClassRelation(C)!.data.comps[C!.index];
  id := GreensXRelation(Parent(C))!.data.id;
  seen := BlistList([1 .. Maximum(id)], []);
  elts := SEMIGROUP_AS_LIST(GenericSemigroupData(S));
  out := EmptyPlist(Length(comp));

  for i in comp do
    if not seen[id[i]] then
      seen[id[i]] := true;
      Add(out, elts[i]);
    fi;
  od;

  return out;
end;

SEMIGROUPS.XClassIndex := function(C)
  local pos;
  if not IsBound(C!.index) then
    # in case of classes created using EquivalenceClassOfElementNC
    pos := Position(Parent(C), Representative(C));
    C!.index := EquivalenceClassRelation(C)!.data.id[pos];
  fi;
  return C!.index;
end;

#############################################################################
## 2. Technical Green's classes stuff . . .
#############################################################################

# this should be removed after the library method for AsSSortedList
# for a Green's class is removed. The default AsSSortedList for a collection
# is what should be used (it is identical)! FIXME

InstallMethod(AsSSortedList, "for a Green's class",
[IsGreensClass], C -> ConstantTimeAccessList(EnumeratorSorted(C)));

InstallMethod(Size, "for a generic semigroup Green's class",
[IsGreensClass],
function(C)
  return Length(EquivalenceClassRelation(C)!.
                data.comps[SEMIGROUPS.XClassIndex(C)]);
end);

InstallMethod(\in,
"for a multiplicative element and a generic semigroup Green's class",
[IsMultiplicativeElement, IsGreensClass],
function(x, C)
  local pos;
  pos := Position(Parent(C), x);
  return pos <> fail
    and EquivalenceClassRelation(C)!.data.id[pos] = SEMIGROUPS.XClassIndex(C);
end);

#JDM: is this necessary? I.e. is there a similar method in the library?

InstallMethod(\=, "for Green's classes",
[IsGreensClass, IsGreensClass],
function(x, y)
  if (IsGreensRClass(x) and IsGreensRClass(y))
      or (IsGreensLClass(x) and IsGreensLClass(y))
      or (IsGreensDClass(x) and IsGreensDClass(y))
      or (IsGreensHClass(x) and IsGreensHClass(y)) then
    return Parent(x) = Parent(y) and Representative(x) in y;
  fi;
  return false;
end);

#JDM: is this necessary? I.e. is there a similar method in the library?

InstallMethod(\<, "for Green's classes",
[IsGreensClass, IsGreensClass],
function(x, y)
  if   (IsGreensRClass(x) and IsGreensRClass(y))
      or (IsGreensLClass(x) and IsGreensLClass(y))
      or (IsGreensDClass(x) and IsGreensDClass(y))
      or (IsGreensHClass(x) and IsGreensHClass(y)) then
    return Parent(x) = Parent(y)
           and Representative(x) < Representative(y)
           and (not Representative(x) in y);
  fi;
  return false;
end);

InstallMethod(IsRegularDClass, "for a D-class of a semigroup",
[IsGreensDClass], IsRegularClass);

InstallMethod(MultiplicativeNeutralElement,
"for a H-class of a semigroup", [IsGreensHClass],
function(H)
  if not IsGroupHClass(H) then
    return fail;
  fi;
  return Idempotents(H)[1];
end);

InstallMethod(IsomorphismPermGroup, "for H-class of a semigroup",
[IsGreensHClass],
function(H)
  local G, p, h;

  if not IsGroupHClass(H) then
    ErrorNoReturn("Semigroups: IsomorphismPermGroup: usage,\n",
                  "the H-class is not a group,");
  fi;

  G := Group(());

  for h in H do 
    p := Permutation(h, AsSet(H), OnRight);
    if not p in G then 
      G := ClosureGroup(G, p);
      if Size(G) = Size(H) then 
        break;
      fi;
    fi;
  od;
  return MappingByFunction(H, G, h -> Permutation(h, AsSet(H), OnRight));
end);
  

InstallMethod(StructureDescription, "for a Green's H-class",
[IsGreensHClass],
function(H)
  if not IsGroupHClass(H) then
    return fail;
  fi;
  return StructureDescription(Range(IsomorphismPermGroup(H)));
end);

InstallMethod(DClassType, "for a generic semigroup",
[IsSemigroup],
function(S)
  return NewType(FamilyObj(S), IsEquivalenceClass
                               and IsEquivalenceClassDefaultRep
                               and IsGreensDClass);
end);

InstallMethod(HClassType, "for a generic semigroup",
[IsSemigroup],
function(S)
  return NewType(FamilyObj(S), IsEquivalenceClass
                               and IsEquivalenceClassDefaultRep
                               and IsGreensHClass);
end);

InstallMethod(LClassType, "for a generic semigroup",
[IsSemigroup],
function(S)
  return NewType(FamilyObj(S), IsEquivalenceClass
                               and IsEquivalenceClassDefaultRep
                               and IsGreensLClass);
end);

InstallMethod(RClassType, "for a generic semigroup",
[IsSemigroup],
function(S)
  return NewType(FamilyObj(S), IsEquivalenceClass
                               and IsEquivalenceClassDefaultRep
                               and IsGreensRClass);
end);

#############################################################################
## 3. Green's relations
#############################################################################

# same method for ideals

InstallMethod(GreensRRelation, "for a generic semigroup",
[IsSemigroup],
function(S)
  local fam, rel;

  fam := GeneralMappingsFamily(ElementsFamily(FamilyObj(S)),
                               ElementsFamily(FamilyObj(S)));

  rel := Objectify(NewType(fam,
                           IsEquivalenceRelation
                             and IsEquivalenceRelationDefaultRep
                             and IsGreensRRelation),
                           rec());
  SetSource(rel, S);
  SetRange(rel, S);
  SetIsLeftSemigroupCongruence(rel, true);

  if HasIsFinite(S) and IsFinite(S) then
    SetIsFiniteSemigroupGreensRelation(rel, true);
  fi;

  if not IsActingSemigroup(S) then
    rel!.data := GABOW_SCC(RightCayleyGraphSemigroup(S));
  fi;

  return rel;
end);

# same method for ideals

InstallMethod(GreensLRelation, "for a generic semigroup",
[IsSemigroup],
function(S)
  local fam, rel;

  fam := GeneralMappingsFamily(ElementsFamily(FamilyObj(S)),
                               ElementsFamily(FamilyObj(S)));

  rel := Objectify(NewType(fam,
                           IsEquivalenceRelation
                             and IsEquivalenceRelationDefaultRep
                             and IsGreensLRelation),
                           rec());
  SetSource(rel, S);
  SetRange(rel, S);
  SetIsRightSemigroupCongruence(rel, true);

  if HasIsFinite(S) and IsFinite(S) then
    SetIsFiniteSemigroupGreensRelation(rel, true);
  fi;
  if not IsActingSemigroup(S) then
    rel!.data := GABOW_SCC(LeftCayleyGraphSemigroup(S));
  fi;
  return rel;
end);

# same method for ideals

InstallMethod(GreensJRelation, "for a generic semigroup",
[IsSemigroup], GreensDRelation);

# same method for ideals

InstallMethod(GreensDRelation, "for a generic semigroup",
[IsSemigroup],
function(S)
  local fam, rel;

  fam := GeneralMappingsFamily(ElementsFamily(FamilyObj(S)),
                               ElementsFamily(FamilyObj(S)));

  rel := Objectify(NewType(fam,
                           IsEquivalenceRelation
                           and IsEquivalenceRelationDefaultRep
                           and IsGreensDRelation),
                   rec());
  SetSource(rel, S);
  SetRange(rel, S);

  if HasIsFinite(S) and IsFinite(S) then
    SetIsFiniteSemigroupGreensRelation(rel, true);
  fi;
  if not IsActingSemigroup(S) then
    rel!.data := SCC_UNION_LEFT_RIGHT_CAYLEY_GRAPHS(GreensRRelation(S)!.data,
                                                    GreensLRelation(S)!.data);
  fi;

  return rel;
end);

# same method for ideals

InstallMethod(GreensHRelation, "for a generic semigroup",
[IsSemigroup],
function(S)
    local fam, rel;

  fam := GeneralMappingsFamily(ElementsFamily(FamilyObj(S)),
                               ElementsFamily(FamilyObj(S)));

  rel := Objectify(NewType(fam, IsEquivalenceRelation
                                and IsEquivalenceRelationDefaultRep
                                and IsGreensHRelation), rec());

  SetSource(rel, S);
  SetRange(rel, S);

  if HasIsFinite(S) and IsFinite(S) then
    SetIsFiniteSemigroupGreensRelation(rel, true);
  fi;
  if not IsActingSemigroup(S) then
    rel!.data := FIND_HCLASSES(GreensRRelation(S)!.data,
                               GreensLRelation(S)!.data);
  fi;
  return rel;
end);

#############################################################################
## 4. Individual classes . . .
#############################################################################

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

InstallMethod(Enumerator, "for a generic semigroup Green's class",
[IsGreensClass],
function(C)
  local data, rel;
  data := Enumerate(GenericSemigroupData(Parent(C)));
  rel := EquivalenceClassRelation(C);
  # gaplint: ignore 2
  return SEMIGROUP_AS_LIST(data){
    rel!.data.comps[SEMIGROUPS.XClassIndex(C)]};
end);

InstallMethod(EquivalenceClassOfElement,
"for a generic semigroup Green's R-relation and a multiplicative element",
[IsGreensRRelation, IsMultiplicativeElement],
function(rel, rep)
  return SEMIGROUPS.EquivalenceClassOfElement(rel, rep, RClassType);
end);

InstallMethod(EquivalenceClassOfElement,
"for a generic semigroup Green's L-relation and a multiplicative element",
[IsGreensLRelation, IsMultiplicativeElement],
function(rel, rep)
  return SEMIGROUPS.EquivalenceClassOfElement(rel, rep, LClassType);
end);

InstallMethod(EquivalenceClassOfElement,
"for a generic semigroup Green's H-relation and a multiplicative element",
[IsGreensHRelation, IsMultiplicativeElement],
function(rel, rep)
  return SEMIGROUPS.EquivalenceClassOfElement(rel, rep, HClassType);
end);

InstallMethod(EquivalenceClassOfElement,
"for a generic semigroup Green's D-relation and a multiplicative element",
[IsGreensDRelation, IsMultiplicativeElement],
function(rel, rep)
  return SEMIGROUPS.EquivalenceClassOfElement(rel, rep, DClassType);
end);

# Green's classes of an element of a semigroup

InstallMethod(GreensRClassOfElement,
"for a finite semigroup and multiplicative element",
[IsSemigroup and IsFinite, IsMultiplicativeElement],
function(S, x)
  return EquivalenceClassOfElement(GreensRRelation(S), x);
end);

InstallMethod(GreensLClassOfElement,
"for a finite semigroup and multiplicative element",
[IsSemigroup and IsFinite, IsMultiplicativeElement],
function(S, x)
  return EquivalenceClassOfElement(GreensLRelation(S), x);
end);

InstallMethod(GreensHClassOfElement,
"for a finite semigroup and multiplicative element",
[IsSemigroup and IsFinite, IsMultiplicativeElement],
function(S, x)
  return EquivalenceClassOfElement(GreensHRelation(S), x);
end);

InstallMethod(GreensDClassOfElement,
"for a finite semigroup and multiplicative element",
[IsSemigroup and IsFinite, IsMultiplicativeElement],
function(S, x)
  return EquivalenceClassOfElement(GreensDRelation(S), x);
end);

InstallMethod(GreensJClassOfElement,
"for a finite semigroup and multiplicative element",
[IsSemigroup and IsFinite, IsMultiplicativeElement], GreensDClassOfElement);

# No check Green's classes of an element of a semigroup

InstallMethod(GreensRClassOfElementNC,
"for a finite semigroup and multiplicative element",
[IsSemigroup and IsFinite, IsMultiplicativeElement],
function(S, x)
  return EquivalenceClassOfElementNC(GreensRRelation(S), x);
end);

InstallMethod(GreensLClassOfElementNC,
"for a finite semigroup and multiplicative element",
[IsSemigroup and IsFinite, IsMultiplicativeElement],
function(S, x)
  return EquivalenceClassOfElementNC(GreensLRelation(S), x);
end);

InstallMethod(GreensHClassOfElementNC,
"for a finite semigroup and multiplicative element",
[IsSemigroup and IsFinite, IsMultiplicativeElement],
function(S, x)
  return EquivalenceClassOfElementNC(GreensHRelation(S), x);
end);

InstallMethod(GreensDClassOfElementNC,
"for a finite semigroup and multiplicative element",
[IsSemigroup and IsFinite, IsMultiplicativeElement],
function(S, x)
  return EquivalenceClassOfElementNC(GreensDRelation(S), x);
end);

InstallMethod(GreensJClassOfElementNC,
"for a finite semigroup and multiplicative element",
[IsSemigroup and IsFinite, IsMultiplicativeElement], GreensDClassOfElementNC);

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

# Green's class of a Green's class (finer from coarser)

InstallMethod(GreensRClassOfElement,
"for a D-class and multiplicative element",
[IsGreensDClass, IsMultiplicativeElement],
function(D, x)
  return EquivalenceClassOfElement(GreensRRelation(Parent(D)), x);
end);

InstallMethod(GreensLClassOfElement,
"for a D-class and multiplicative element",
[IsGreensDClass, IsMultiplicativeElement],
function(D, x)
  return EquivalenceClassOfElement(GreensLRelation(Parent(D)), x);
end);

InstallMethod(GreensHClassOfElement,
"for a Green's class and multiplicative element",
[IsGreensClass, IsMultiplicativeElement],
function(C, x)
  return EquivalenceClassOfElement(GreensHRelation(Parent(C)), x);
end);

#############################################################################
## 5. Collections of classes, and reps
#############################################################################

## numbers of classes

InstallMethod(NrDClasses, "for a semigroup",
[IsSemigroup], S -> Length(GreensDRelation(S)!.data.comps));

InstallMethod(NrRegularDClasses, "for a semigroup",
[IsSemigroup], S -> Length(RegularDClasses(S)));

InstallMethod(NrLClasses, "for a semigroup",
[IsSemigroup], S -> Length(GreensLRelation(S)!.data.comps));

InstallMethod(NrLClasses, "for a Green's D-class",
[IsGreensDClass], D -> Length(GreensLClasses(D)));

InstallMethod(NrRClasses, "for a semigroup",
[IsSemigroup], S -> Length(GreensRRelation(S)!.data.comps));

InstallMethod(NrRClasses, "for a Green's D-class",
[IsGreensDClass], D -> Length(GreensRClasses(D)));

InstallMethod(NrHClasses, "for a semigroup",
[IsSemigroup], S -> Length(GreensHRelation(S)!.data.comps));

InstallMethod(NrHClasses, "for a Green's D-class",
[IsGreensDClass], D -> NrRClasses(D) * NrLClasses(D));

InstallMethod(NrHClasses, "for a Green's L-class",
[IsGreensLClass], L -> NrRClasses(DClassOfLClass(L)));

InstallMethod(NrHClasses, "for a Green's R-class",
[IsGreensRClass], R -> NrLClasses(DClassOfRClass(R)));

## Green's classes of a semigroup

InstallMethod(RegularDClasses, "for a semigroup",
[IsSemigroup], S -> Filtered(GreensDClasses(S), IsRegularDClass));

# same method for ideals

InstallMethod(GreensLClasses, "for a generic semigroup",
[IsSemigroup],
function(S)
  if not IsFinite(S) then
    TryNextMethod();
  fi;
  return SEMIGROUPS.GreensXClasses(S, GreensLRelation, GreensLClassOfElement);
end);

# same method for ideals

InstallMethod(GreensRClasses, "for a generic semigroup",
[IsSemigroup],
function(S)
  if not IsFinite(S) then
    TryNextMethod();
  fi;
  return SEMIGROUPS.GreensXClasses(S, GreensRRelation, GreensRClassOfElement);
end);

# same method for ideals

InstallMethod(GreensHClasses, "for a generic semigroup",
[IsSemigroup],
function(S)
  if not IsFinite(S) then
    TryNextMethod();
  fi;
  return SEMIGROUPS.GreensXClasses(S, GreensHRelation, GreensHClassOfElement);
end);

# same method for ideals

InstallMethod(GreensDClasses, "for a generic semigroup",
[IsSemigroup],
function(S)
  if not IsFinite(S) then
    TryNextMethod();
  fi;
  return SEMIGROUPS.GreensXClasses(S, GreensDRelation, GreensDClassOfElement);
end);

## Green's classes of a Green's class

InstallMethod(GreensLClasses, "for a Green's D-class",
[IsGreensDClass],
function(C)
  return SEMIGROUPS.GreensXClassesOfClass(C, GreensLRelation,
                                          GreensLClassOfElement);
end);

InstallMethod(GreensRClasses, "for a Green's D-class",
[IsGreensDClass],
function(C)
  return SEMIGROUPS.GreensXClassesOfClass(C, GreensRRelation,
                                          GreensRClassOfElement);
end);

InstallMethod(GreensHClasses, "for a generic semigroup Green's class",
[IsGreensClass], 2, # to beat the library method
function(C)
  if not (IsGreensRClass(C) or IsGreensLClass(C) or IsGreensDClass(C)) then
    ErrorNoReturn("Semigroups: GreensHClasses ",
                  "(for a generic semigroup Green's class): usage,\n",
                  "the argument should be a Green's R-, L-, or D-class,");
  fi;
  return SEMIGROUPS.GreensXClassesOfClass(C, GreensHRelation,
                                          GreensHClassOfElement);
end);

## Representatives

InstallMethod(DClassReps, "for a semigroup",
[IsSemigroup], S -> SEMIGROUPS.XClassReps(S, GreensDRelation));

InstallMethod(RClassReps, "for a semigroup",
[IsSemigroup], S -> SEMIGROUPS.XClassReps(S, GreensRRelation));

InstallMethod(LClassReps, "for a semigroup",
[IsSemigroup], S -> SEMIGROUPS.XClassReps(S, GreensLRelation));

InstallMethod(HClassReps, "for a semigroup",
[IsSemigroup], S -> SEMIGROUPS.XClassReps(S, GreensHRelation));

InstallMethod(RClassReps, "for a Green's D-class (Semigroups)",
[IsGreensDClass], D -> SEMIGROUPS.XClassRepsOfClass(D, GreensRRelation));

InstallMethod(LClassReps, "for a Green's D-class (Semigroups)",
[IsGreensDClass], D -> SEMIGROUPS.XClassRepsOfClass(D, GreensLRelation));

InstallMethod(HClassReps, "for a Green's class (Semigroups)",
[IsGreensClass], C -> SEMIGROUPS.XClassRepsOfClass(C, GreensHRelation));

## Partial order of D-classes

InstallMethod(PartialOrderOfDClasses, "for a finite semigroup",
[IsSemigroup and IsFinite],
function(S)
  local comps, id, right_id, left_id, right_comps, left_comps, right, left,
   genstoapply, out, seen, i, j, k, l;

  comps       := GreensDRelation(S)!.data.comps;
  id          := GreensDRelation(S)!.data.id;
  right_id    := GreensRRelation(S)!.data.id;
  left_id     := GreensLRelation(S)!.data.id;
  right_comps := GreensRRelation(S)!.data.comps;
  left_comps  := GreensLRelation(S)!.data.comps;
  right       := RightCayleyGraphSemigroup(S);
  left        := LeftCayleyGraphSemigroup(S);

  genstoapply := [1 .. Length(right[1])];
  out := [];

  for i in [1 .. Length(comps)] do # loop over D-classes
    out[i] := [];
    seen := BlistList([1 .. Maximum(left_id)], []);
    for j in comps[i] do           # loop over L-classes of a D-class
      if not seen[left_id[j]] then
        seen[left_id[j]] := true;
        for k in left_comps[left_id[j]] do
          for l in genstoapply do
            AddSet(out[i], id[right[k][l]]);
          od;
        od;
      fi;
    od;
    seen := BlistList([1 .. Maximum(right_id)], []);
    for j in comps[i] do           # loop over R-classes of a D-class
      if not seen[right_id[j]] then
        seen[right_id[j]] := true;
        for k in right_comps[right_id[j]] do
          for l in genstoapply do
            AddSet(out[i], id[left[k][l]]);
          od;
        od;
      fi;
    od;
  od;
  return out;
end);

#############################################################################
## 6. Idempotents . . .
#############################################################################

InstallMethod(NrIdempotents, "for a Green's class",
[IsGreensClass], C -> Length(Idempotents(C)));

InstallMethod(Idempotents, "for a Green's class",
[IsGreensClass],
function(C)
  local data, rel, positions, idempotents, x;

  data := Enumerate(GenericSemigroupData(Parent(C)));
  rel := EquivalenceClassRelation(C);

  if IsBound(data!.idempotents) then
    positions := Intersection(rel!.data.comps[SEMIGROUPS.XClassIndex(C)],
                              data!.idempotents);
    # FIXME could just use Enumerator here?
    return SEMIGROUP_AS_LIST(data){positions};
  fi;

  idempotents := [];

  for x in C do
    if IsIdempotent(x) then
      Add(idempotents, x);
      if IsGreensHClass(C) then
        break;
      fi;
    fi;
  od;

  return idempotents;
end);

#############################################################################
## 7. Regular classes . . .
#############################################################################

InstallMethod(IsRegularClass, "for a Green's class of a semigroup",
[IsGreensClass], C -> First(Enumerator(C), x -> IsIdempotent(x)) <> fail);

InstallTrueMethod(IsRegularClass, IsRegularDClass);
InstallTrueMethod(IsRegularClass, IsInverseOpClass);
InstallTrueMethod(IsHClassOfRegularSemigroup,
                  IsInverseOpClass and IsGreensHClass);

#############################################################################
## 8. Enumerators, iterators etc
#############################################################################

InstallMethod(IteratorOfDClasses, "for a finite semigroup",
[IsSemigroup and IsFinite], GreensDClasses);

InstallMethod(IteratorOfRClasses, "for a finite semigroup",
[IsSemigroup and IsFinite], GreensRClasses);

#############################################################################
## 9. Viewing, printing, etc . . .
#############################################################################

# Viewing, printing, etc

InstallMethod(ViewString, "for a Green's class",
[IsGreensClass],
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
[IsGreensRelation], 2, # to beat the method for congruences
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

# TODO: remove/improve the library method for congruences, so that this is
# obsolete.

InstallMethod(ViewObj, "for a Green's relation",
[IsGreensRelation], 2, # to beat the method for congruences
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
