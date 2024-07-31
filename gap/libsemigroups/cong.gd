############################################################################
##
##  libsemigroups/cong.gd
##  Copyright (C) 2022                                   James D. Mitchell
##
##  Licensing information can be found in the README file of this package.
##
############################################################################

# A congruence satisfies CanUseLibsemigroupsCongruence if it should use a
# libsemigroups Congruence object to compute things about itself.
DeclareProperty("CanUseLibsemigroupsCongruence",
                CanComputeEquivalenceRelationPartition);

# A semigroup satisfies this property if its congruences should belong to
# CanUseLibsemigroupsCongruence.
DeclareProperty("CanUseLibsemigroupsCongruences", IsSemigroup);

InstallTrueMethod(CanComputeEquivalenceRelationPartition,
                  CanUseLibsemigroupsCongruence);

# The next operation is the only one supplied by libsemigroups/cong.gd/i that
# is exported.

DeclareOperation("CongruenceLessNC",
                 [CanUseLibsemigroupsCongruence,
                  IsMultiplicativeElement,
                  IsMultiplicativeElement]);
