#############################################################################
##
##  ideals/ideals.gd
##  Copyright (C) 2013-2022                               James D. Mitchell
##
##  Licensing information can be found in the README file of this package.
##
#############################################################################

DeclareSynonymAttr("GeneratorsOfSemigroupIdeal",
  GeneratorsOfMagmaIdeal);
DeclareSynonymAttr("GeneratorsOfLeftSemigroupIdeal",
  GeneratorsOfLeftMagmaIdeal);
DeclareSynonymAttr("GeneratorsOfRightSemigroupIdeal",
  GeneratorsOfRightMagmaIdeal);

DeclareGlobalFunction("SemigroupIdeal");
DeclareGlobalFunction("LeftSemigroupIdeal");
DeclareGlobalFunction("RightSemigroupIdeal");

DeclareOperation("SemigroupIdealByGenerators",
                 [IsSemigroup, IsListOrCollection]);
DeclareOperation("SemigroupIdealByGenerators",
                 [IsSemigroup, IsListOrCollection, IsRecord]);
DeclareOperation("SemigroupIdealByGeneratorsNC",
                 [IsSemigroup, IsListOrCollection, IsRecord]);

DeclareAttribute("MinimalIdealGeneratingSet", IsSemigroupIdeal);

# the <Parent> of an ideal is the semigroup in which the ideal was created,
# i.e.  the first argument of <SemigroupIdeal(S, I)>. The
# <SupersemigroupOfIdeal> is the object containing <GeneratorsOfSemigroup>
# which are used to compute the ideal. For a regular semigroup ideal,
# <SupersemigroupOfIdeal> will always be the top most semigroup used to create
# any of the predecessors of the current ideal. For example, if <S> is a
# semigroup, <I> is a regular ideal of <S>, and <J> is an ideal of <I>, then
# <Parent(J)> is <I> and <SupersemigroupOfIdeal(J)> is <S>.  This is to avoid
# computing a generating set for <I>, in this example, which is expensive and
# unnecessary since <I> is regular (in which case the Green's relations of <I>
# are just restrictions of the Green's relations on <S>).
#
# If <S> is a semigroup, <I> is a non-regular ideal of <S>, <J> is an ideal of
# <I>, then <SupersemigroupOfIdeal(J)> is <I>, since we anyway currently have
# to use a <GeneratorsOfSemigroup(I)> to compute anything about <I> other than
# its size and membership.

DeclareAttribute("SupersemigroupOfIdeal", IsSemigroupIdeal);

InstallTrueMethod(IsSemigroup, IsSemigroupIdeal);

DeclareAttribute("Ideals", IsSemigroup);
