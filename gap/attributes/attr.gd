#############################################################################
##
##  attributes/attr.gd
##  Copyright (C) 2013-2022                              James D. Mitchell
##
##  Licensing information can be found in the README file of this package.
##
#############################################################################
##

# This file contains declarations for attributes of semigroups.

DeclareOperation("IrredundantGeneratingSubset",
                 [IsMultiplicativeElementCollection]);

DeclareAttribute("GroupOfUnits", IsSemigroup);
DeclareAttribute("IdempotentGeneratedSubsemigroup", IsSemigroup);
DeclareAttribute("InjectionPrincipalFactor", IsGreensDClass);
DeclareAttribute("InjectionNormalizedPrincipalFactor", IsGreensDClass);
DeclareAttribute("RepresentativeOfMinimalIdeal", IsSemigroup);
DeclareOperation("RepresentativeOfMinimalIdealNC", [IsSemigroup]);
DeclareSynonymAttr("RepresentativeOfMinimalDClass",
                   RepresentativeOfMinimalIdeal);
DeclareAttribute("MinimalIdeal", IsSemigroup);
DeclareAttribute("PrincipalFactor", IsGreensDClass);
DeclareAttribute("NormalizedPrincipalFactor", IsGreensDClass);
DeclareAttribute("MultiplicativeZero", IsSemigroup);
DeclareAttribute("LengthOfLongestDClassChain", IsSemigroup);

# We use IsListOrCollection here because some collections of semigroup
# generators (such as elements/congruence classes in a quotient semigroup) do
# not satisfy IsMultiplicativeElementCollection (although the classes
# themselves do satisfy IsMultiplicativeElement).
DeclareAttribute("SmallSemigroupGeneratingSet",
                 IsListOrCollection);
DeclareAttribute("SmallMonoidGeneratingSet",
                 IsMultiplicativeElementWithOneCollection);
DeclareAttribute("SmallInverseSemigroupGeneratingSet",
                 IsMultiplicativeElementCollection);
DeclareAttribute("SmallInverseMonoidGeneratingSet",
                 IsMultiplicativeElementWithOneCollection);

DeclareAttribute("MinimalSemigroupGeneratingSet",
                 IsSemigroup);
DeclareAttribute("MinimalMonoidGeneratingSet",
                 IsMonoid);
DeclareAttribute("MinimalInverseSemigroupGeneratingSet",
                 IsSemigroup);
DeclareAttribute("MinimalInverseMonoidGeneratingSet",
                 IsMonoid);

DeclareAttribute("SmallestElementSemigroup", IsSemigroup);
DeclareAttribute("LargestElementSemigroup", IsSemigroup);

DeclareAttribute("StructureDescription", IsBrandtSemigroup);
DeclareAttribute("StructureDescription", IsGroupAsSemigroup);
DeclareAttribute("StructureDescriptionMaximalSubgroups",
                 IsSemigroup);
DeclareAttribute("MaximalDClasses", IsSemigroup);
DeclareAttribute("MaximalLClasses", IsSemigroup);
DeclareAttribute("MaximalRClasses", IsSemigroup);
DeclareAttribute("MinimalDClass", IsSemigroup);
DeclareAttribute("IsGreensDGreaterThanFunc", IsSemigroup);

DeclareAttribute("UnderlyingSemigroupOfSemigroupWithAdjoinedZero",
                 IsSemigroup);

DeclareOperation("InversesOfSemigroupElementNC",
                 [IsSemigroup, IsMultiplicativeElement]);
DeclareOperation("OneInverseOfSemigroupElementNC",
                 [IsSemigroup, IsMultiplicativeElement]);
DeclareOperation("OneInverseOfSemigroupElement",
                 [IsSemigroup, IsMultiplicativeElement]);

DeclareAttribute("IndecomposableElements", IsSemigroup);
DeclareAttribute("NambooripadLeqRegularSemigroup", IsSemigroup);
DeclareAttribute("NambooripadPartialOrder", IsSemigroup);

DeclareOperation("KernelContainment",
                 [IsTransformation, IsTransformation, IsPosInt]);
DeclareAttribute("RegularLeqTransformationSemigroupNC", IsTransformationSemigroup);
DeclareAttribute("MitschLeqSemigroupNC", IsSemigroup);
DeclareAttribute("MitschLeqSemigroup", IsSemigroup);
DeclareAttribute("MitschOrderOfTransformationSemigroup",
                 IsFinite and IsTransformationSemigroup);
DeclareAttribute("MitschOrderOfSemigroup", IsFinite and IsSemigroup);
DeclareAttribute("DumbMitschOrderOfSemigroup", IsFinite and IsSemigroup);

DeclareOperation("LeftIdentity", [IsSemigroup, IsMultiplicativeElement]);
DeclareOperation("RightIdentity", [IsSemigroup, IsMultiplicativeElement]);

DeclareAttribute("MultiplicationTableWithCanonicalPositions",
                 IsSemigroup and CanUseFroidurePin);
DeclareAttribute("TransposedMultiplicationTableWithCanonicalPositions",
                 IsSemigroup and CanUseFroidurePin);

DeclareAttribute("MinimalFaithfulTransformationDegree", IsSemigroup);
DeclareAttribute("SmallerDegreeTransformationRepresentation", IsSemigroup);

# TODO(later)
# DeclareAttribute("MinimalFaithfulTransformationRepresentation", IsSemigroup);
