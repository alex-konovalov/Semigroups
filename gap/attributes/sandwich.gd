############################################################################
##
##  attributes/sandwich.gd
##  Copyright (C) 2024                                    Murray T. Whyte
##
##  Licensing information can be found in the README file of this package.
##
#############################################################################
##

DeclareCategory("IsSandwichSemigroupElement", IsAssociativeElement);
DeclareCategoryCollections("IsSandwichSemigroupElement");
DeclareOperation("SandwichSemigroup", [IsSemigroup, IsAssociativeElement]);
DeclareCategory("IsSandwichSemigroup", IsSemigroup);
DeclareAttribute("SandwichElement", IsSandwichSemigroup);
DeclareAttribute("SandwichSemigroupOfFamily", IsFamily);
DeclareOperation("BijectionSandwichSemigroup",
                 [IsSemigroup, IsAssociativeElement]);

DeclareSynonym("IsSandwichSubsemigroup",
                IsSemigroup and IsSandwichSemigroupElementCollection);

InstallTrueMethod(CanUseGapFroidurePin, IsSandwichSubsemigroup);
DeclareAttribute("InverseBijectionSandwichSemigroup",
                 IsSandwichSemigroup);
