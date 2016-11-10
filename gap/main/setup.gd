############################################################################
##
#W  setup.gd
#Y  Copyright (C) 2013-15                                James D. Mitchell
##
##  Licensing information can be found in the README file of this package.
##
#############################################################################
##

# This file contains declarations of everything required for a semigroup
# belonging to IsActingSemigroup...

# The rank of IsActingSemigroup is incremented by 8 so that it is greater than
# IsSemigroup and IsFinite and HasGeneratorsOfSemigroup, and IsSemigroupIdeal
# and IsFinite and HasGeneratorsOfSemigroupIdeal
DeclareCategory("IsActingSemigroup", IsEnumerableSemigroupRep and IsFinite, 8);

DeclareProperty("IsGeneratorsOfActingSemigroup",
                IsMultiplicativeElementCollection);
DeclareProperty("IsActingSemigroupWithFixedDegreeMultiplication",
                IsActingSemigroup);

DeclareCategory("IsActingSemigroupGreensClass", IsGreensClass);

DeclareAttribute("ActionDegree", IsMultiplicativeElement);
DeclareAttribute("ActionDegree", IsMultiplicativeElementCollection);
DeclareAttribute("ActionRank", IsSemigroup);
DeclareOperation("ActionRank", [IsMultiplicativeElement, IsInt]);
DeclareAttribute("MinActionRank", IsSemigroup);

DeclareAttribute("RhoAct", IsSemigroup);
DeclareAttribute("LambdaAct", IsSemigroup);

DeclareAttribute("LambdaOrbOpts", IsSemigroup);
DeclareAttribute("RhoOrbOpts", IsSemigroup);

DeclareAttribute("LambdaRank", IsSemigroup);
DeclareAttribute("RhoRank", IsSemigroup);

DeclareAttribute("LambdaFunc", IsSemigroup);
DeclareAttribute("RhoFunc", IsSemigroup);

DeclareAttribute("RhoInverse", IsSemigroup);
DeclareAttribute("LambdaInverse", IsSemigroup);
DeclareAttribute("LambdaBound", IsSemigroup);
DeclareAttribute("RhoBound", IsSemigroup);
DeclareAttribute("LambdaIdentity", IsSemigroup);
DeclareAttribute("RhoIdentity", IsSemigroup);
DeclareAttribute("LambdaPerm", IsSemigroup);
DeclareAttribute("LambdaConjugator", IsSemigroup);

DeclareAttribute("LambdaOrbSeed", IsSemigroup);
DeclareAttribute("RhoOrbSeed", IsSemigroup);

DeclareAttribute("IdempotentTester", IsSemigroup);
DeclareAttribute("IdempotentCreator", IsSemigroup);

DeclareAttribute("StabilizerAction", IsSemigroup);
DeclareAttribute("SchutzGpMembership", IsSemigroup);

DeclareOperation("FakeOne", [IsCollection]);
