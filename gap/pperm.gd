#############################################################################
###
##W  pperm.gd
##Y  Copyright (C) 2011-12                                James D. Mitchell
###
###  Licensing information can be found in the README file of this package.
###
##############################################################################
###

# internal use only
DeclareGlobalFunction("DenseRangeList");
DeclareGlobalFunction("InternalRepOfPartialPerm");
DeclareGlobalFunction("SEMIGROUPS_HashFunctionForPP");

# everything else
DeclareCategory("IsAssociativeElementWithSemigroupInverse", IsAssociativeElement);
DeclareCategoryCollections("IsAssociativeElementWithSemigroupInverse");
DeclareCategory("IsPartialPerm", IsMultiplicativeElementWithOne and
 IsAssociativeElementWithAction and IsAssociativeElementWithSemigroupInverse); 

DeclareCategoryCollections("IsPartialPerm");
DeclareSynonym("IsPartialPermSemigroup", IsSemigroup and
IsPartialPermCollection);

DeclareGlobalFunction("PartialPerm");
DeclareGlobalFunction("PartialPermNC");
DeclareOperation("AsPartialPerm", [IsObject]);
DeclareOperation("AsPartialPermNC", [IsObject]);

DeclareAttribute("DegreeOfPartialPerm", IsPartialPerm);
DeclareAttribute("DegreeOfPartialPermCollection", IsPartialPermCollection);
DeclareAttribute("DegreeOfPartialPermSemigroup", IsPartialPermSemigroup);
DeclareAttribute("DomainOfPartialPerm", IsPartialPerm);
DeclareAttribute("DomainOfPartialPermCollection", IsPartialPermCollection);
DeclareAttribute("FixedPointsOfPartialPerm", IsPartialPerm);
DeclareAttribute("IndexPeriodOfPartialPerm", IsPartialPerm);
DeclareAttribute("RangeOfPartialPerm", IsPartialPerm);
DeclareAttribute("RangeOfPartialPermCollection", IsPartialPermCollection);
DeclareAttribute("RangeSetOfPartialPerm", IsPartialPerm);
DeclareAttribute("RankOfPartialPerm", IsPartialPerm);

DeclareOperation("NaturalLeqPartialPerm", [IsPartialPerm, IsPartialPerm]);
DeclareOperation("OnIntegerSetsWithPartialPerm", [IsCyclotomicCollection, IsPartialPerm]);
DeclareOperation("OnIntegerTuplesWithPartialPerm", [IsCyclotomicCollection, IsPartialPerm]);
DeclareOperation("RestrictedPartialPermNC", [IsPartialPerm, IsList]);
DeclareOperation("RestrictedPartialPerm", [IsPartialPerm, IsList]);

DeclareGlobalFunction("PartialPermOp");
DeclareGlobalFunction("PartialPermAction");
DeclareGlobalFunction("InverseSemigroupAction");
DeclareGlobalFunction("PartialPermActionHomomorphism");
DeclareGlobalFunction("InverseSemigroupActionHomomorphism");

DeclareGlobalFunction("PrettyPrintPP");
DeclareGlobalFunction("RandomPartialPerm");

