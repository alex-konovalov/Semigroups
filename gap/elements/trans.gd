############################################################################
##
##  elements/trans.gd
##  Copyright (C) 2015-2022                              James D. Mitchell
##
##  Licensing information can be found in the README file of this package.
##
#############################################################################

DeclareAttribute("CanonicalTransformation", IsTransformation);
DeclareOperation("CanonicalTransformation", [IsTransformation, IsInt]);
DeclareOperation("TransformationByImageAndKernel",
                 [IsHomogeneousList, IsCyclotomicCollColl]);
DeclareOperation("IsRefinementKernelOfTransformation",
                [IsTransformation, IsTransformation, IsInt]);
DeclareOperation("IsRefinementKernelOfTransformation",
                [IsTransformation, IsTransformation]);
