############################################################################# 
## 
#W  semigroups.gd
#Y  Copyright (C) 2011-12                                 James D. Mitchell
## 
##  Licensing information can be found in the README file of this package. 
## 
############################################################################# 
##

DeclareGlobalFunction("ClosureInverseSemigroup");
DeclareGlobalFunction("ClosureInverseSemigroupNC");
DeclareGlobalFunction("ClosureSemigroup");
DeclareGlobalFunction("ClosureSemigroupNC");

DeclareAttribute("GeneratorsOfInverseMonoid", IsInverseSemigroup);
DeclareAttribute("GeneratorsOfInverseSemigroup", IsInverseSemigroup);

DeclareGlobalFunction("InverseMonoid");
DeclareGlobalFunction("InverseSemigroup");

DeclareOperation("InverseMonoidByGenerators", [IsPartialPermCollection]);
DeclareOperation("InverseSemigroupByGenerators", [IsPartialPermCollection]);
DeclareOperation("InverseMonoidByGeneratorsNC", [IsPartialPermCollection, 
IsPartialPermCollection, IsRecord]);
DeclareOperation("InverseSemigroupByGeneratorsNC", [IsPartialPermCollection, 
IsPartialPermCollection, IsRecord]);

DeclareSynonymAttr("IsPartialPermSemigroup", IsSemigroup and
IsPartialPermCollection);
DeclareProperty("IsPartialPermMonoid", IsPartialPermSemigroup);

DeclareOperation("RandomBinaryRelationSemigroup", [IsPosInt, IsPosInt]);
DeclareOperation("RandomBlockGroup", [IsPosInt, IsPosInt]);
DeclareOperation("RandomInverseSemigroup", [IsPosInt, IsPosInt]);
DeclareOperation("RandomInverseMonoid", [IsPosInt, IsPosInt]);
DeclareOperation("RandomTransformationMonoid", [IsPosInt, IsPosInt]);
DeclareOperation("RandomTransformationSemigroup", [IsPosInt, IsPosInt]);

DeclareGlobalFunction("RegularSemigroup");

DeclareOperation("SubsemigroupByProperty", [IsSemigroup, IsFunction]);

#EOF
