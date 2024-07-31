#############################################################################
##
##  attributes/dual.gi
##  Copyright (C) 2018-2022                              James D. Mitchell
##                                                              Finn Smith
##
##  Licensing information can be found in the README file of this package.
##
#############################################################################
##

# This file contains an implementation of dual semigroups. We only provide
# enough functionality to allow dual semigroups to work as semigroups. This is
# to avoid having to install versions of every function in Semigroups specially
# for dual semigroup representations. In some cases special functions would be
# faster.

InstallMethod(DualSemigroup, "for a semigroup",
[IsSemigroup],
function(S)
  local fam, dual, filts, type, map;

  if IsDualSemigroupRep(S) then
    if HasGeneratorsOfSemigroup(S) then
      return Semigroup(List(GeneratorsOfSemigroup(S),
                            UnderlyingElementOfDualSemigroupElement));
    fi;
    ErrorNoReturn("this dual semigroup cannot be constructed ",
                  "without knowing generators");
  fi;

  fam  := NewFamily("DualSemigroupElementsFamily", IsDualSemigroupElement);
  dual := rec();
  ObjectifyWithAttributes(dual,
                          NewType(CollectionsFamily(fam),
                                  IsSemigroup and
                                  IsWholeFamily and
                                  IsDualSemigroupRep and
                                  IsAttributeStoringRep),
                          DualSemigroup,
                          S,
                          CanUseGapFroidurePin,
                          CanUseFroidurePin(S));

  filts := IsDualSemigroupElement;
  if IsMultiplicativeElementWithOne(Representative(S)) then
    filts := filts and IsMultiplicativeElementWithOne;
  fi;

  type       := NewType(fam, filts);
  fam!.type  := type;

  SetDualSemigroupOfFamily(fam, dual);
  SetElementsFamily(FamilyObj(dual), fam);

  if HasIsFinite(S) then
    SetIsFinite(dual, IsFinite(S));
  fi;

  if IsTransformationSemigroup(S) then
    map := AntiIsomorphismDualSemigroup(dual);
    SetAntiIsomorphismTransformationSemigroup(dual, map);
  fi;

  if HasGeneratorsOfSemigroup(S) then
    SetGeneratorsOfSemigroup(dual,
                             List(GeneratorsOfSemigroup(S),
                                  x -> SEMIGROUPS.DualSemigroupElementNC(dual,
                                                                         x)));
  fi;

  if HasGeneratorsOfMonoid(S) then
    SetGeneratorsOfMonoid(dual,
                          List(GeneratorsOfMonoid(S),
                               x -> SEMIGROUPS.DualSemigroupElementNC(dual,
                                                                      x)));
  fi;
  return dual;
end);

SEMIGROUPS.DualSemigroupElementNC := function(S, s)
  if not IsDualSemigroupElement(s) then
    return Objectify(ElementsFamily(FamilyObj(S))!.type, [s]);
  fi;
  return s![1];
end;

InstallMethod(AntiIsomorphismDualSemigroup, "for a semigroup",
[IsSemigroup],
function(S)
  local dual, inv, iso;

  dual := DualSemigroup(S);
  iso  := x -> SEMIGROUPS.DualSemigroupElementNC(dual, x);
  inv  := x -> SEMIGROUPS.DualSemigroupElementNC(S, x);
  return MappingByFunction(S, dual, iso, inv);
end);

InstallGlobalFunction(UnderlyingElementOfDualSemigroupElement,
function(s)
  if not IsDualSemigroupElement(s) then
    ErrorNoReturn("the argument is not an element represented as a dual ",
                  "semigroup element");
  fi;
  return s![1];
end);

################################################################################
## Technical methods
################################################################################

InstallMethod(OneMutable, "for a dual semigroup element",
[IsDualSemigroupElement and IsMultiplicativeElementWithOne],
function(s)
  local S, x;
  S := DualSemigroupOfFamily(FamilyObj(s));
  x := SEMIGROUPS.DualSemigroupElementNC(DualSemigroup(S), s);
  return SEMIGROUPS.DualSemigroupElementNC(S, OneMutable(x));
end);

InstallMethod(MultiplicativeNeutralElement, "for a dual semigroup",
[IsDualSemigroupRep],
10,  # add rank to beat enumeration methods
function(S)
  local m;
  m := MultiplicativeNeutralElement(DualSemigroup(S));
  if m <> fail then
    return SEMIGROUPS.DualSemigroupElementNC(S, m);
  fi;
  return fail;
end);

InstallMethod(Representative, "for a dual semigroup",
[IsDualSemigroupRep],
function(S)
  if HasGeneratorsOfSemigroup(S) then
    return GeneratorsOfSemigroup(S)[1];
  fi;
  return SEMIGROUPS.DualSemigroupElementNC(S, Representative(DualSemigroup(S)));
end);

InstallMethod(Size, "for a dual semigroup", [IsDualSemigroupRep],
10,  # add rank to beat enumeration methods
S -> Size(DualSemigroup(S)));

InstallMethod(AsList, "for a dual semigroup",
[IsDualSemigroupRep],
10,  # add rank to beat enumeration methods
S -> List(DualSemigroup(S), s -> SEMIGROUPS.DualSemigroupElementNC(S, s)));

InstallMethod(\*, "for dual semigroup elements",
IsIdenticalObj,
[IsDualSemigroupElement, IsDualSemigroupElement],
{x, y} -> Objectify(FamilyObj(x)!.type, [y![1] * x![1]]));

InstallMethod(\=, "for dual semigroup elements",
IsIdenticalObj,
[IsDualSemigroupElement, IsDualSemigroupElement],
{x, y} -> x![1] = y![1]);

InstallMethod(\<, "for dual semigroup elements",
IsIdenticalObj,
[IsDualSemigroupElement, IsDualSemigroupElement],
{x, y} -> x![1] < y![1]);

InstallMethod(ViewObj, "for dual semigroup elements",
[IsDualSemigroupElement], PrintObj);

InstallMethod(PrintObj, "for dual semigroup elements",
[IsDualSemigroupElement],
function(x)
  Print("<", ViewString(x![1]), " in the dual semigroup>");
end);

InstallMethod(ViewObj, "for a dual semigroup",
[IsDualSemigroupRep], PrintObj);

InstallMethod(PrintObj, "for a dual semigroup",
[IsDualSemigroupRep],
function(S)
  Print("<dual semigroup of ",
        ViewString(DualSemigroup(S)),
        ">");
end);

# InstallMethod(ViewString, "for dual semigroup elements",
# [IsDualSemigroupElement], PrintString);
#
# InstallMethod(PrintString, "for dual semigroup elements",
# [IsDualSemigroupElement],
# x -> StringFormatted("<{!v} in the dual semigroup>", x![1]);
#
# InstallMethod(ViewString, "for a dual semigroup",
# [IsDualSemigroupRep], PrintString);
#
# InstallMethod(PrintString, "for a dual semigroup",
# [IsDualSemigroupRep],
# S -> StringFormatted("<dual semigroup of {!v}>", DualSemigroup(S));

InstallMethod(ChooseHashFunction, "for a dual semigroup element and int",
[IsDualSemigroupElement, IsInt],
function(x, data)
  local H, hashfunc;

  H        := ChooseHashFunction(x![1], data);
  hashfunc := {a, b} -> H.func(a![1], b);
  return rec(func := hashfunc, data := H.data);
end);
