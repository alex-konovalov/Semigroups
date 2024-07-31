############################################################################
##
##  congruences/cong.gi
##  Copyright (C) 2015-2022                               Michael C. Young
##
##  Licensing information can be found in the README file of this package.
##
#############################################################################
##
## This file contains some general functions, operations and attributes of
## semigroup congruences.  Methods for specific types of congruence are
## implemented in the following files:
##
##       conginv.gi     - Inverse semigroups
##       congpairs.gi   - Congruences with generating pairs
##       congrees.gi    - Rees congruences
##       congrms.gi     - (0-)simple Rees matrix semigroups
##       congsimple.gi  - (0-)simple semigroups
##       conguniv.gi    - Universal congruences
##
## cong.gd contains declarations for many of these.
##

# This file contains implementations of methods for congruences that don't
# assume any particular representation.

########################################################################
# 0. Categories
########################################################################

InstallMethod(CongruenceHandednessString, "for a right congruence",
[IsRightMagmaCongruence and IsRightSemigroupCongruence], C -> "right");

InstallMethod(CongruenceHandednessString, "for a left congruence",
[IsLeftMagmaCongruence and IsLeftSemigroupCongruence], C -> "left");

InstallMethod(CongruenceHandednessString, "for a 2-sided congruence",
[IsMagmaCongruence and IsSemigroupCongruence], C -> "2-sided");

# This is required for QuotientSemigroups and their subsemigroups.
InstallImmediateMethod(CanEasilyCompareElements,
IsCongruenceClass and HasEquivalenceClassRelation, 0,
C -> CanUseLibsemigroupsCongruence(EquivalenceClassRelation(C)));

########################################################################
# Flexible functions for creating congruences
########################################################################

InstallGlobalFunction(SemigroupCongruence,
function(arg)
  local S, opts, s_opts, x, pairs, cong;
  if not Length(arg) >= 2 then
    ErrorNoReturn("at least 2 arguments are required");
  elif not IsSemigroup(arg[1]) then
    ErrorNoReturn("the 1st argument is not a semigroup");
  fi;
  S := arg[1];

  # Set up any options
  if IsRecord(arg[Length(arg)]) then
    opts := arg[Length(arg)];
    arg := arg{[1 .. Length(arg) - 1]};
  else
    opts := rec();
  fi;
  s_opts := SEMIGROUPS.OptionsRec(S);
  for x in RecNames(s_opts) do
    if not IsBound(opts.(x)) then
      opts.(x) := s_opts.(x);
    fi;
  od;

  if IsHomogeneousList(arg[2]) then
    # We should have a list of generating pairs
    if Length(arg) = 2 then
      pairs := arg[2];
      if not IsEmpty(pairs) then
        if (not IsList(pairs[1])) or IsMatrixObj(pairs[1]) then
          pairs := [pairs];
        fi;
      fi;
    elif Length(arg) > 2 then
      pairs := arg{[2 .. Length(arg)]};
    fi;
    if not ForAll(pairs, p -> Size(p) = 2) then
      ErrorNoReturn("the 2nd argument (a list of lists) contains lists ",
                    "of size not equal to 2");
    elif not ForAll(pairs, p -> p[1] in S and p[2] in S) then
      ErrorNoReturn("the 2nd argument (a list of lists) contains items ",
                    "that do not belong to the 1st argument (a semigroup)");
    fi;

    # Remove any reflexive pairs
    pairs := Filtered(pairs, p -> p[1] <> p[2]);

    # Decide which representation to use
    if not IsFinite(S)
        or ((HasIsSimpleSemigroup(S) or IsActingSemigroup(S)
           or HasSize(S) or IsReesMatrixSemigroup(S))
          and IsSimpleSemigroup(S)) or
         ((HasIsZeroSimpleSemigroup(S) or IsActingSemigroup(S)
           or HasSize(S) or IsReesZeroMatrixSemigroup(S))
          and IsZeroSimpleSemigroup(S)) then
      return SemigroupCongruenceByGeneratingPairs(S, pairs);
    elif IsInverseSemigroup(S) and IsGeneratorsOfInverseSemigroup(S) and
         Size(S) >= opts.cong_by_ker_trace_threshold then
      cong := SemigroupCongruenceByGeneratingPairs(S, pairs);
      cong := AsInverseSemigroupCongruenceByKernelTrace(cong);
      SetGeneratingPairsOfMagmaCongruence(cong, pairs);
      return cong;
    else
      return SemigroupCongruenceByGeneratingPairs(S, pairs);
    fi;
  elif IsGeneralMapping(arg[2]) and
      ((IsRMSCongruenceByLinkedTriple(arg[3]) and IsSimpleSemigroup(S))
       or (IsRZMSCongruenceByLinkedTriple(arg[3]) and IsZeroSimpleSemigroup(S)))
      then
    # We should have a congruence of an isomorphic RMS/RZMS
    if Range(arg[2]) = Range(arg[3]) and S = Source(arg[2]) then
      return CongruenceByIsomorphism(arg[2], arg[3]);
    else
      ErrorNoReturn("the range of the 3rd argument (a congruence) is ",
                    "not a Rees (0-)matrix semigroup isomorphic to the ",
                    "1st argument");
    fi;
  elif HasIsSemigroupIdeal(arg[2])
      and IsSemigroupIdeal(arg[2])
      and Parent(arg[2]) = S then
    return ReesCongruenceOfSemigroupIdeal(arg[2]);
  elif Length(arg) = 3
      and IsInverseSemigroup(arg[2])
      and IsGeneratorsOfInverseSemigroup(arg[2])
      and IsDenseList(arg[3])
      and IsInverseSemigroup(S)
      and IsGeneratorsOfInverseSemigroup(S) then
    # We should have the kernel and trace of a congruence on an inverse
    # semigroup
    return InverseSemigroupCongruenceByKernelTrace(S, arg[2], arg[3]);
  fi;
  ErrorNoReturn("the arguments are not valid for this function");
end);

BindGlobal("_LeftOrRightCong",
function(CongruenceConstructor, arg)
  local S, pairs;
  if not Length(arg) >= 2 then
    ErrorNoReturn("at least 2 arguments are required");
  elif not IsSemigroup(arg[1]) then
    ErrorNoReturn("the 1st argument is not a semigroup");
  fi;
  S := arg[1];

  if IsHomogeneousList(arg[2]) then
    # We should have a list of generating pairs
    if Length(arg) = 2 then
      pairs := arg[2];
      if not IsEmpty(pairs) and not IsList(pairs[1]) then
        pairs := [pairs];
      fi;
    elif Length(arg) > 2 then
      pairs := arg{[2 .. Length(arg)]};
    fi;
    if not ForAll(pairs, p -> Size(p) = 2) then
      ErrorNoReturn("the 2nd argument (a list of lists) contains lists ",
                    "of size not equal to 2");
    elif not ForAll(pairs, p -> p[1] in S and p[2] in S) then
      ErrorNoReturn("the 2nd argument (a list of lists) contains items ",
                    "that do not belong to the 1st argument (a semigroup)");
    fi;
    # Remove any reflexive pairs
    pairs := Filtered(pairs, p -> p[1] <> p[2]);
    return CongruenceConstructor(S, pairs);
  else
    ErrorNoReturn("the arguments are not valid for this function");
  fi;
end);

InstallGlobalFunction(LeftSemigroupCongruence,
arg -> _LeftOrRightCong(LeftSemigroupCongruenceByGeneratingPairs, arg));

InstallGlobalFunction(RightSemigroupCongruence,
arg -> _LeftOrRightCong(RightSemigroupCongruenceByGeneratingPairs, arg));

########################################################################
# Trivial congruence
########################################################################

InstallMethod(TrivialCongruence, "for a semigroup",
[IsSemigroup], S -> SemigroupCongruence(S, []));

########################################################################
# Congruence operators
########################################################################

InstallMethod(IsSuperrelation, "for semigroup congruences",
[IsLeftRightOrTwoSidedCongruence, IsLeftRightOrTwoSidedCongruence],
{lhop, rhop} -> IsSubrelation(rhop, lhop));

########################################################################
# Congruence classes
########################################################################

InstallMethod(EquivalenceClassOfElement,
"for a left, right, or 2-sided semigroup congruence and mult. elt.",
[IsLeftRightOrTwoSidedCongruence, IsMultiplicativeElement],
function(C, x)
  if not x in Range(C) then
    ErrorNoReturn("the 2nd argument (a mult. elt.) does not belong ",
                  "to the range of the 1st argument (a ",
                  CongruenceHandednessString(C),
                  " congruence)");
  fi;
  return EquivalenceClassOfElementNC(C, x);
end);

InstallMethod(EquivalenceClassOfElementNC,
"for a left, right, or 2-sided congruence and mult. elt.",
[IsLeftRightOrTwoSidedCongruence, IsMultiplicativeElement],
function(C, x)
  local filt, class;
  if IsMagmaCongruence(C) then
    # IsCongruenceClass is declared in the GAP library and it does not belong
    # to IsAttributeStoringRep
    filt := IsCongruenceClass and IsAttributeStoringRep;
  elif IsLeftMagmaCongruence(C) then
    # IsLeftCongruenceClass is declared in the Semigroups pkg and does belong
    # to IsAttributeStoringRep
    filt := IsLeftCongruenceClass;
  else
    Assert(1, IsRightMagmaCongruence(C));
    filt := IsRightCongruenceClass;
  fi;

  class := Objectify(NewType(FamilyObj(Range(C)), filt), rec());
  SetParentAttr(class, Range(C));
  SetEquivalenceClassRelation(class, C);
  SetRepresentative(class, x);
  if HasIsFinite(Range(C)) and IsFinite(Range(C)) then
    SetIsFinite(class, true);
  fi;

  return class;
end);

########################################################################
# Congruence class attributes
########################################################################

# Maybe these should only be for CanComputeEquivalenceRelationPartition?

InstallMethod(AsList,
"for a class of a left, right, or 2-sided semigroup congruence",
[IsLeftRightOrTwoSidedCongruenceClass],
C -> ImagesElm(EquivalenceClassRelation(C), Representative(C)));

InstallMethod(Enumerator,
"for a class of a left, right, or 2-sided semigroup congruence",
[IsLeftRightOrTwoSidedCongruenceClass],
6,  # To beat the library method for magma congruence classes
AsList);

InstallMethod(Size,
"for a class of a left, right, or 2-sided semigroup congruence",
[IsLeftRightOrTwoSidedCongruenceClass],
C -> Size(AsList(C)));

########################################################################
# Congruence class operators
########################################################################

# Multiplication for congruence classes: only makes sense for 2-sided
InstallMethod(\*, "for two congruence classes",
[IsCongruenceClass, IsCongruenceClass],
function(lhop, rhop)
  if EquivalenceClassRelation(lhop) <> EquivalenceClassRelation(rhop) then
    ErrorNoReturn("the arguments (cong. classes) are not classes of the same ",
                  "congruence");
  fi;
  return EquivalenceClassOfElementNC(EquivalenceClassRelation(lhop),
                                     Representative(lhop) *
                                     Representative(rhop));
end);

InstallMethod(\=,
"for classes of a left, right, or 2-sided semigroup congruence",
IsIdenticalObj,
[IsLeftRightOrTwoSidedCongruenceClass, IsLeftRightOrTwoSidedCongruenceClass],
function(lhop, rhop)
  return EquivalenceClassRelation(lhop) = EquivalenceClassRelation(rhop)
    and [Representative(lhop), Representative(rhop)]
    in EquivalenceClassRelation(lhop);
end);

InstallMethod(\in,
"for a mult. elt. and a class of a left, right or 2-sided congruence",
[IsMultiplicativeElement, IsLeftRightOrTwoSidedCongruenceClass],
3,  # to beat the library method
function(x, class)
  local C;
  C := EquivalenceClassRelation(class);
  return x in Range(C) and [x, Representative(class)] in C;
end);

InstallMethod(ViewObj,
"for a left, right, or 2-sided congruence class",
[IsLeftRightOrTwoSidedCongruenceClass],
function(C)
  local string;
  string := CongruenceHandednessString(EquivalenceClassRelation(C));
  Print("<", string, " congruence class of ");
  ViewObj(Representative(C));
  Print(">");
end);

########################################################################
# Congruence class actions
########################################################################

InstallMethod(OnLeftCongruenceClasses,
"for a left congruence class and a multiplicative element",
[IsLeftRightOrTwoSidedCongruenceClass, IsMultiplicativeElement],
function(class, x)
  local C;
  # This is necessary because IsCongruenceClass is not a sub-category of
  # IsLeftCongruenceClass or IsRightCongruenceClass
  if IsRightCongruenceClass(class) then
    TryNextMethod();
  fi;
  C := EquivalenceClassRelation(class);
  return EquivalenceClassOfElementNC(C, x * Representative(class));
end);

InstallMethod(OnRightCongruenceClasses,
"for a right congruence class and a multiplicative element",
[IsLeftRightOrTwoSidedCongruenceClass, IsMultiplicativeElement],
function(class, x)
  local C;
  # This is necessary because IsCongruenceClass is not a sub-category of
  # IsLeftCongruenceClass or IsRightCongruenceClass
  if IsLeftCongruenceClass(class) then
    TryNextMethod();
  fi;
  C := EquivalenceClassRelation(class);
  return EquivalenceClassOfElementNC(C, Representative(class) * x);
end);
