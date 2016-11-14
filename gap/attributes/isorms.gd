############################################################################
##
#W  isorms.gd
#Y  Copyright (C) 2014-15                                James D. Mitchell
##
##  Licensing information can be found in the README file of this package.
##
#############################################################################
##

DeclareCategory("IsRMSIsoByTriple", IsGeneralMapping and IsSPGeneralMapping
                                    and IsTotal and IsSingleValued and
                                    IsInjective and IsSurjective and
                                    IsAttributeStoringRep);
DeclareCategory("IsRZMSIsoByTriple", IsGeneralMapping and IsSPGeneralMapping
                                     and IsTotal and IsSingleValued and
                                     IsInjective and IsSurjective and
                                     IsAttributeStoringRep);

DeclareGlobalFunction("RMSIsoByTriple");
DeclareGlobalFunction("RZMSIsoByTriple");

DeclareOperation("ELM_LIST", [IsRMSIsoByTriple, IsPosInt]);
DeclareOperation("ELM_LIST", [IsRZMSIsoByTriple, IsPosInt]);

DeclareProperty("IsAutomorphismGroupOfRMSOrRZMS", IsGroup and IsFinite);
