############################################################################
##
##  congruences/conglatt.gd
##  Copyright (C) 2016-2022                               Michael C. Young
##
##  Licensing information can be found in the README file of this package.
##
#############################################################################
##
## This file contains functions for a poset of congruences.
##
## When the congruences of a semigroup are computed, they form a lattice with
## respect to containment.  The information about the congruences' positions in
## this lattice may be stored in an IsCongruencePoset object (a component object
## based on a record) and can be retrieved from this object using the methods in
## this file.
##

DeclareCategory("IsCongruencePoset", IsDigraph);

DeclareAttribute("UnderlyingSemigroupOfCongruencePoset", IsCongruencePoset);
DeclareAttribute("PosetOfPrincipalCongruences", IsCongruencePoset);
DeclareAttribute("JoinSemilatticeOfCongruences", IsCongruencePoset);
DeclareAttribute("MinimalCongruences", IsCongruencePoset);

DeclareAttribute("CongruencesOfPoset", IsCongruencePoset);

# Constructs the poset object consisting of the congruences given in the
# argument.
DeclareOperation("PosetOfCongruences", [IsListOrCollection]);
DeclareAttribute("JoinSemilatticeOfCongruences", IsListOrCollection);

DeclareAttribute("GeneratingPairsOfPrincipalCongruences", IsSemigroup);
DeclareAttribute("GeneratingPairsOfPrincipalLeftCongruences", IsSemigroup);
DeclareAttribute("GeneratingPairsOfPrincipalRightCongruences", IsSemigroup);

DeclareAttribute("PosetOfPrincipalCongruences", IsSemigroup);
DeclareAttribute("PosetOfPrincipalLeftCongruences", IsSemigroup);
DeclareAttribute("PosetOfPrincipalRightCongruences", IsSemigroup);

DeclareOperation("PosetOfPrincipalCongruences",
                 [IsSemigroup, IsListOrCollection]);
DeclareOperation("PosetOfPrincipalLeftCongruences",
                 [IsSemigroup, IsListOrCollection]);
DeclareOperation("PosetOfPrincipalRightCongruences",
                 [IsSemigroup, IsListOrCollection]);

DeclareAttribute("LatticeOfCongruences", IsSemigroup);
DeclareAttribute("LatticeOfLeftCongruences", IsSemigroup);
DeclareAttribute("LatticeOfRightCongruences", IsSemigroup);

DeclareAttribute("CayleyDigraphOfCongruences", IsSemigroup);
DeclareAttribute("CayleyDigraphOfLeftCongruences", IsSemigroup);
DeclareAttribute("CayleyDigraphOfRightCongruences", IsSemigroup);

DeclareOperation("CayleyDigraphOfCongruences",
                 [IsSemigroup, IsListOrCollection]);
DeclareOperation("CayleyDigraphOfLeftCongruences",
                 [IsSemigroup, IsListOrCollection]);
DeclareOperation("CayleyDigraphOfRightCongruences",
                 [IsSemigroup, IsListOrCollection]);

DeclareCategory("IsCayleyDigraphOfCongruences", IsCongruencePoset);

DeclareOperation("LatticeOfCongruences",
                 [IsSemigroup, IsListOrCollection]);
DeclareOperation("LatticeOfLeftCongruences",
                 [IsSemigroup, IsListOrCollection]);
DeclareOperation("LatticeOfRightCongruences",
                 [IsSemigroup, IsListOrCollection]);

DeclareAttribute("CongruencesOfSemigroup", IsSemigroup);
DeclareAttribute("LeftCongruencesOfSemigroup", IsSemigroup);
DeclareAttribute("RightCongruencesOfSemigroup", IsSemigroup);

DeclareAttribute("MinimalCongruencesOfSemigroup", IsSemigroup);
DeclareAttribute("MinimalLeftCongruencesOfSemigroup", IsSemigroup);
DeclareAttribute("MinimalRightCongruencesOfSemigroup", IsSemigroup);

DeclareOperation("MinimalCongruencesOfSemigroup",
                 [IsSemigroup, IsListOrCollection]);
DeclareOperation("MinimalCongruencesOfSemigroup",
                 [IsSemigroup, IsIterator]);

DeclareOperation("MinimalLeftCongruencesOfSemigroup",
                 [IsSemigroup, IsListOrCollection]);
DeclareOperation("MinimalRightCongruencesOfSemigroup",
                 [IsSemigroup, IsListOrCollection]);

DeclareAttribute("PrincipalCongruencesOfSemigroup", IsSemigroup);
DeclareAttribute("PrincipalLeftCongruencesOfSemigroup", IsSemigroup);
DeclareAttribute("PrincipalRightCongruencesOfSemigroup", IsSemigroup);

DeclareOperation("PrincipalCongruencesOfSemigroup",
                 [IsSemigroup, IsListOrCollection]);
DeclareOperation("PrincipalLeftCongruencesOfSemigroup",
                 [IsSemigroup, IsListOrCollection]);
DeclareOperation("PrincipalRightCongruencesOfSemigroup",
                 [IsSemigroup, IsListOrCollection]);

DeclareAttribute("GeneratingCongruencesOfJoinSemilattice", IsCongruencePoset);

DeclareGlobalFunction("_ClosureLattice");
DeclareGlobalFunction("WrappedTwoSidedCongruence");
