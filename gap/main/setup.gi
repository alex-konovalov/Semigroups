###########################################################################
##
##  main/setup.gi
##  Copyright (C) 2013-2022                              James D. Mitchell
##
##  Licensing information can be found in the README file of this package.
##
#############################################################################
##

###############################################################################
# Setup - install the basic things required for specific acting semigroups    #
###############################################################################

# IsGeneratorsOfActingSemigroup

InstallMethod(IsGeneratorsOfActingSemigroup, "for a list or collection",
[IsListOrCollection], ReturnFalse);

# In the below can't do ReturnTrue, since GAP insists that we use
# InstallTrueMethod.
#
# InstallTrueMethod(IsGeneratorsOfActingSemigroup, IsTransformationCollection);
#
# can't do InstallTrueMethod for the above since this is not picked up
# if Semigroups is loaded after any transformation semigroup has been created.
# It seems that since IsTransformationCollection has had its implied filters
# installed, if we add an additional implied filter
# IsGeneratorsOfActingSemigroup, then this is ignored. I think this is a bug.

InstallMethod(IsGeneratorsOfActingSemigroup, "for a transformation collection",
[IsTransformationCollection], x -> true);  # gaplint: disable=W038

InstallMethod(IsGeneratorsOfActingSemigroup, "for a partial perm collection",
[IsPartialPermCollection], x -> true);  # gaplint: disable=W038

InstallMethod(IsGeneratorsOfActingSemigroup, "for a bipartition collection",
[IsBipartitionCollection], x -> true);  # gaplint: disable=W038

InstallMethod(IsGeneratorsOfActingSemigroup,
"for a Rees 0-matrix semigroup element collection",
[IsReesZeroMatrixSemigroupElementCollection],
function(coll)
  local R;
  R := ReesMatrixSemigroupOfFamily(FamilyObj(Representative(coll)));
  return IsPermGroup(UnderlyingSemigroup(R)) and IsRegularSemigroup(R);
end);

InstallMethod(IsGeneratorsOfActingSemigroup,
"for a McAlister triple element collection",
[IsMcAlisterTripleSemigroupElementCollection],
function(coll)
  return
  IsPermGroup(McAlisterTripleSemigroupGroup(MTSEParent(Representative(coll))));
end);

InstallMethod(IsGeneratorsOfActingSemigroup,
"for an ffe coll coll coll",
# TODO(MatrixObj-later) is this the best way to recognise a collection of
# MatrixObj?
[IsFFECollCollColl],
function(coll)
  return IsGeneratorsOfSemigroup(coll)
    and (IsEmpty(coll) or ForAll(coll, IsMatrixObjOverFiniteField));
end);

InstallTrueMethod(IsGeneratorsOfActingSemigroup,
IsMatrixOverFiniteFieldSemigroup);

# the largest point involved in the action

InstallMethod(ActionDegree, "for a transformation",
[IsTransformation], DegreeOfTransformation);

InstallMethod(ActionDegree, "for a partial perm",
[IsPartialPerm], x -> Maximum(DegreeOfPartialPerm(x),
                              CodegreeOfPartialPerm(x)));

InstallMethod(ActionDegree, "for a bipartition",
[IsBipartition], DegreeOfBipartition);

InstallMethod(ActionDegree, "for a Rees 0-matrix semigroup element",
[IsReesZeroMatrixSemigroupElement],
function(x)
  if x![1] = 0 then
    return 0;
  fi;
  return NrMovedPoints(x![2]) + 1;
end);

InstallMethod(ActionDegree, "for a McAlister semigroup element",
[IsMcAlisterTripleSemigroupElement], _ -> 0);

InstallMethod(ActionDegree, "for a matrix obj", [IsMatrixObj],
function(m)
  if not IsMatrixObjOverFiniteField(m) then
    TryNextMethod();
  fi;
  return NrRows(m);
end);

InstallMethod(ActionDegree, "for a transformation collection",
[IsTransformationCollection], DegreeOfTransformationCollection);

InstallMethod(ActionDegree, "for a partial perm collection",
[IsPartialPermCollection], x -> Maximum(DegreeOfPartialPermCollection(x),
                                        CodegreeOfPartialPermCollection(x)));

InstallMethod(ActionDegree, "for a bipartition collection",
[IsBipartitionCollection], DegreeOfBipartitionCollection);

InstallMethod(ActionDegree, "for a Rees 0-matrix semigroup element collection",
[IsReesZeroMatrixSemigroupElementCollection],
function(coll)
  local R;
  if ForAny(coll, x -> x![1] <> 0) then
    R := ReesMatrixSemigroupOfFamily(FamilyObj(Representative(coll)));
    return NrMovedPoints(UnderlyingSemigroup(R)) + 1;
  fi;
  return 0;
end);

InstallMethod(ActionDegree, "for a ffe coll coll coll",
[IsFFECollCollColl],
function(coll)
  Assert(1, ForAll(coll, IsMatrixObjOverFiniteField));
  return NrRows(Representative(coll));
end);

InstallMethod(ActionDegree, "for a McAlister semigroup element collection",
[IsMcAlisterTripleSemigroupElementCollection],
coll -> MaximumList(List(coll, ActionDegree)));

InstallMethod(ActionDegree, "for a transformation semigroup",
[IsTransformationSemigroup], DegreeOfTransformationSemigroup);

InstallMethod(ActionDegree, "for a partial perm semigroup",
[IsPartialPermSemigroup], x -> Maximum(DegreeOfPartialPermSemigroup(x),
                                       CodegreeOfPartialPermSemigroup(x)));

InstallMethod(ActionDegree, "for a partial perm inverse semigroup",
[IsPartialPermSemigroup and IsInverseSemigroup], DegreeOfPartialPermSemigroup);

InstallMethod(ActionDegree, "for a bipartition semigroup",
[IsBipartitionSemigroup], DegreeOfBipartitionSemigroup);

InstallMethod(ActionDegree, "for a Rees 0-matrix subsemigroup with generators",
[IsReesZeroMatrixSubsemigroup and HasGeneratorsOfSemigroup],
function(R)
  local parent;
  if ForAny(GeneratorsOfSemigroup(R), x -> x![1] <> 0) then
    parent := ReesMatrixSemigroupOfFamily(ElementsFamily(FamilyObj(R)));
    return NrMovedPoints(UnderlyingSemigroup(parent)) + 1;
  fi;
  return 0;
end);

InstallMethod(ActionDegree, "for a McAlister triple subsemigroup",
[IsMcAlisterTripleSubsemigroup], _ -> 0);

InstallMethod(ActionDegree, "for a matrix over finite field semigroup",
[IsMatrixOverFiniteFieldSemigroup], S -> ActionDegree(Representative(S)));

# the number of points in the range of the action

InstallMethod(ActionRank, "for a transformation and integer",
[IsTransformation, IsInt], RANK_TRANS_INT);

InstallMethod(ActionRank, "for a transformation semigroup",
[IsTransformationSemigroup],
function(s)
  local deg;
  deg := DegreeOfTransformationSemigroup(s);
  return function(f)
    return RANK_TRANS_INT(f, deg);
  end;
end);

InstallMethod(ActionRank, "for a partial perm and integer",
[IsPartialPerm, IsInt], {f, _} -> RankOfPartialPerm(f));

InstallMethod(ActionRank, "for a partial perm semigroup",
[IsPartialPermSemigroup], _ -> RankOfPartialPerm);

InstallMethod(ActionRank, "for a bipartition and integer",
[IsBipartition, IsInt], BIPART_RANK);

InstallMethod(ActionRank, "for a bipartition semigroup",
[IsBipartitionSemigroup], _ -> RankOfBipartition);

InstallMethod(ActionRank,
"for a Rees 0-matrix semigroup element and integer",
[IsReesZeroMatrixSemigroupElement, IsInt],
function(f, _)
  local parent;
  if f![1] = 0 then
    return 0;
  else
    parent := ReesMatrixSemigroupOfFamily(FamilyObj(f));
    return NrMovedPoints(UnderlyingSemigroup(parent)) + 1;
  fi;
end);

InstallMethod(ActionRank, "for a Rees 0-matrix subsemigroup",
[IsReesZeroMatrixSubsemigroup],
function(R)
  return function(x)
    local parent;
    if x![1] = 0 then
      return 0;
    else
      parent := ReesMatrixSemigroupOfFamily(ElementsFamily(FamilyObj(R)));
      return NrMovedPoints(UnderlyingSemigroup(parent)) + 1;
    fi;
  end;
end);

InstallMethod(ActionRank, "for a McAlister triple semigroup element and int",
[IsMcAlisterTripleSemigroupElement, IsInt],
{f, _} -> f[1]);

InstallMethod(ActionRank, "for a McAlister triple subsemigroup",
[IsMcAlisterTripleSubsemigroup],
S -> x -> ActionDegree(S));

InstallMethod(ActionRank, "for a matrix object and integer",
[IsMatrixObj, IsInt],
function(x, _)
  if not IsMatrixObjOverFiniteField(x) then
    TryNextMethod();
  fi;
  return Rank(RowSpaceBasis(x));
end);

InstallMethod(ActionRank, "for a matrix semigroup",
[IsMatrixOverFiniteFieldSemigroup],
_ -> x -> Rank(RowSpaceBasis(x)));

# the minimum possible rank of an element

InstallMethod(MinActionRank, "for a transformation semigroup",
[IsTransformationSemigroup], _ -> 1);

InstallMethod(MinActionRank, "for a partial perm semigroup",
[IsPartialPermSemigroup], _ -> 0);

InstallMethod(MinActionRank, "for a bipartition semigroup",
[IsBipartitionSemigroup], _ -> 0);

InstallMethod(MinActionRank, "for a Rees 0-matrix subsemigroup",
[IsReesZeroMatrixSubsemigroup], _ -> 0);

InstallMethod(MinActionRank, "for a McAlister triple subsemigroup",
[IsMcAlisterTripleSubsemigroup], _ -> 1);

InstallMethod(MinActionRank, "for a matrix semigroup",
[IsMatrixOverFiniteFieldSemigroup], _ -> 0);

# options passed to LambdaOrb(s) when it is created

InstallMethod(LambdaOrbOpts, "for a transformation semigroup",
[IsTransformationSemigroup], S -> rec(forflatplainlists := true));

InstallMethod(LambdaOrbOpts, "for a partial perm semigroup",
[IsPartialPermSemigroup], S -> rec(forflatplainlists := true));

InstallMethod(LambdaOrbOpts, "for a bipartition semigroup",
[IsBipartitionSemigroup], S -> rec());

InstallMethod(LambdaOrbOpts, "for a Rees 0-matrix subsemigroup",
[IsReesZeroMatrixSubsemigroup], S -> rec());

InstallMethod(LambdaOrbOpts, "for a McAlister triple subsemigroup",
[IsMcAlisterTripleSubsemigroup], S -> rec());

InstallMethod(LambdaOrbOpts, "for a matrix semigroup",
[IsMatrixOverFiniteFieldSemigroup], s -> rec());

InstallMethod(RhoOrbOpts, "for a transformation semigroup",
[IsTransformationSemigroup], S -> rec(forflatplainlists := true));

InstallMethod(RhoOrbOpts, "for a partial perm semigroup",
[IsPartialPermSemigroup], S -> rec(forflatplainlists := true));

InstallMethod(RhoOrbOpts, "for a bipartition semigroup",
[IsBipartitionSemigroup], S -> rec());

InstallMethod(RhoOrbOpts, "for a Rees 0-matrix subsemigroup",
[IsReesZeroMatrixSubsemigroup], S -> rec());

InstallMethod(RhoOrbOpts, "for a McAlister triple subsemigroup",
[IsMcAlisterTripleSubsemigroup], S -> rec());

InstallMethod(RhoOrbOpts, "for a matrix semigroup",
[IsMatrixOverFiniteFieldSemigroup], s -> rec());

# the lambda and rho acts
InstallMethod(LambdaAct, "for a transformation semigroup",
[IsTransformationSemigroup],
function(S)
  local deg;
  deg := DegreeOfTransformationSemigroup(S);
  return
    function(set, f)
      return OnPosIntSetsTrans(set, f, deg);
    end;
end);

InstallMethod(LambdaAct, "for a partial perm semigroup",
[IsPartialPermSemigroup], _ -> OnPosIntSetsPartialPerm);

InstallMethod(LambdaAct, "for a bipartition semigroup",
[IsBipartitionSemigroup], _ -> BLOCKS_RIGHT_ACT);

InstallMethod(LambdaAct, "for a Rees 0-matrix subsemigroup",
[IsReesZeroMatrixSubsemigroup], x -> function(pt, x)
  if x![1] = 0 or pt = 0 then
    return 0;
  elif pt = -1 or x![4][pt][x![1]] <> 0 then
    return x![3];
  else
    return 0;
  fi;
end);

InstallMethod(LambdaAct, "for a McAlister triple subsemigroup",
[IsMcAlisterTripleSubsemigroup],
function(S)
  local act, digraph;
  S := MTSEParent(Representative(S));
  act     := McAlisterTripleSemigroupAction(S);
  digraph := McAlisterTripleSemigroupPartialOrder(S);
  return
  function(pt, x)
    if pt = 0 then
      return act(x[1], x[2] ^ -1);
    fi;
    return PartialOrderDigraphJoinOfVertices(digraph,
                                             act(pt, x[2] ^ -1),
                                             act(x[1], x[2] ^ -1));
  end;
end);

InstallMethod(LambdaAct, "for a matrix over finite field semigroup",
[IsMatrixOverFiniteFieldSemigroup],
S -> {vsp, mat} -> MatrixOverFiniteFieldRowSpaceRightAction(S, vsp, mat));

InstallMethod(RhoAct, "for a transformation semigroup",
[IsTransformationSemigroup],
S -> {set, f} -> ON_KERNEL_ANTI_ACTION(set,
                                       f,
                                       DegreeOfTransformationSemigroup(S)));

InstallMethod(RhoAct, "for a partial perm semigroup",
[IsPartialPermSemigroup], S ->
{set, f} -> OnPosIntSetsPartialPerm(set, f ^ -1));

InstallMethod(RhoAct, "for a partial perm semigroup",
[IsBipartitionSemigroup], x -> BLOCKS_LEFT_ACT);

InstallMethod(RhoAct, "for a Rees 0-matrix subsemigroup",
[IsReesZeroMatrixSubsemigroup], x -> function(pt, x)
  if x![1] = 0 or pt = 0 then
    return 0;
  elif pt = -1 or x![4][x![3]][pt] <> 0 then
    return x![1];
  else
    return 0;
  fi;
end);

InstallMethod(RhoAct, "for a McAlister triple subsemigroup",
[IsMcAlisterTripleSubsemigroup],
function(S)
  local act, digraph;
  S := MTSEParent(Representative(S));
  act     := McAlisterTripleSemigroupAction(S);
  digraph := McAlisterTripleSemigroupPartialOrder(S);
  return
    function(pt, x)
      if pt = 0 then
        return x[1];
      fi;
      return PartialOrderDigraphJoinOfVertices(digraph,
                                               act(pt, x[2]),
                                               x[1]);
    end;
end);

InstallMethod(RhoAct, "for a matrix semigroup",
[IsMatrixOverFiniteFieldSemigroup],
S -> {vsp, mat} -> LambdaAct(S)(vsp, TransposedMat(mat)));

# the seed or dummy start point for LambdaOrb

InstallMethod(LambdaOrbSeed, "for a transformation semigroup",
[IsTransformationSemigroup], _ -> [0]);

InstallMethod(LambdaOrbSeed, "for a partial perm semigroup",
[IsPartialPermSemigroup], _ -> [0]);

InstallMethod(LambdaOrbSeed, "for a bipartition semigroup",
[IsBipartitionSemigroup],
S -> BLOCKS_NC([[1 .. DegreeOfBipartitionSemigroup(S) + 1]]));

InstallMethod(LambdaOrbSeed, "for a Rees 0-matrix subsemigroup",
[IsReesZeroMatrixSubsemigroup], S -> -1);

InstallMethod(LambdaOrbSeed, "for a McAlister triple subsemigroup",
[IsMcAlisterTripleSubsemigroup], S -> 0);

InstallMethod(LambdaOrbSeed,
"for a matrix over finite field semigroup",
[IsMatrixOverFiniteFieldSemigroup],
function(S)
    local deg;
    deg := NrRows(Representative(S)) + 2;
    return NewRowBasisOverFiniteField(IsPlistRowBasisOverFiniteFieldRep,
                                      BaseDomain(S),
                                      NullMat(deg, deg, BaseDomain(S)));
end);

# the seed or dummy start point for RhoOrb

InstallMethod(RhoOrbSeed, "for a transformation semigroup",
[IsTransformationSemigroup], _ -> [0]);

InstallMethod(RhoOrbSeed, "for a partial perm semigroup",
[IsPartialPermSemigroup], _ -> [0]);

InstallMethod(RhoOrbSeed, "for a bipartition semigroup",
[IsBipartitionSemigroup],
S -> BLOCKS_NC([[1 .. DegreeOfBipartitionSemigroup(S) + 1]]));

InstallMethod(RhoOrbSeed, "for a Rees 0-matrix subsemigroup",
[IsReesZeroMatrixSubsemigroup], _ -> -1);

InstallMethod(RhoOrbSeed, "for a McAlister triple subsemigroup",
[IsMcAlisterTripleSubsemigroup], _ -> 0);

InstallMethod(RhoOrbSeed, "for a matrix semigroup",
[IsMatrixOverFiniteFieldSemigroup], LambdaOrbSeed);

# the function calculating the lambda or rho value of an element

InstallMethod(LambdaFunc, "for a transformation semigroup",
[IsTransformationSemigroup],
S -> f -> IMAGE_SET_TRANS_INT(f, DegreeOfTransformationSemigroup(S)));

InstallMethod(LambdaFunc, "for a partial perm semigroup",
[IsPartialPermSemigroup], x -> IMAGE_SET_PPERM);

InstallMethod(LambdaFunc, "for a bipartition semigroup",
[IsBipartitionSemigroup], x -> BIPART_RIGHT_BLOCKS);

InstallMethod(LambdaFunc, "for a Rees 0-matrix subsemigroup",
[IsReesZeroMatrixSubsemigroup], R -> function(x)
  if x![1] <> 0 then
    return x![3];
  fi;
  return 0;
end);

InstallMethod(LambdaFunc, "for a McAlister triple subsemigroup",
[IsMcAlisterTripleSubsemigroup],
function(S)
  local act;
  act := McAlisterTripleSemigroupAction(MTSEParent(Representative(S)));
  return x -> act(x[1], x[2] ^ -1);
end);

# a function that returns the row space
InstallMethod(LambdaFunc, "for a matrix semigroup",
[IsMatrixOverFiniteFieldSemigroup], _ -> RowSpaceBasis);

InstallMethod(RhoFunc, "for a transformation semigroup",
[IsTransformationSemigroup],
S -> f -> FLAT_KERNEL_TRANS_INT(f, DegreeOfTransformationSemigroup(S)));

InstallMethod(RhoFunc, "for a partial perm semigroup",
[IsPartialPermSemigroup], _ -> DOMAIN_PPERM);

InstallMethod(RhoFunc, "for a bipartition semigroup",
[IsBipartitionSemigroup], _ -> BIPART_LEFT_BLOCKS);

InstallMethod(RhoFunc, "for a Rees 0-matrix subsemigroup",
[IsReesZeroMatrixSubsemigroup], _ -> (x -> x![1]));

InstallMethod(RhoFunc, "for a McAlister triple subsemigroup",
[IsMcAlisterTripleSubsemigroup],
_ -> x -> x[1]);

InstallMethod(RhoFunc, "for a matrix semigroup",
[IsMatrixOverFiniteFieldSemigroup],
S -> mat -> LambdaFunc(S)(TransposedMat(mat)));

# The function used to calculate the rank of lambda or rho value

InstallMethod(LambdaRank, "for a transformation semigroup",
[IsTransformationSemigroup], _ -> Length);

InstallMethod(LambdaRank, "for a partial perm semigroup",
[IsPartialPermSemigroup], _ -> Length);

InstallMethod(LambdaRank, "for a bipartition semigroup",
[IsBipartitionSemigroup], _ -> BLOCKS_RANK);

InstallMethod(LambdaRank, "for a Rees 0-matrix subsemigroup",
[IsReesZeroMatrixSubsemigroup], R ->
function(x)
  local parent;
  if x = 0 then
    return 0;
  else
    parent := ReesMatrixSemigroupOfFamily(ElementsFamily(FamilyObj(R)));
    return NrMovedPoints(UnderlyingSemigroup(parent)) + 1;
  fi;
end);

InstallMethod(LambdaRank, "for a McAlister subsemigroup",
[IsMcAlisterTripleSubsemigroup], S ->
function(x)
  local T;
  if x = 0 then
    return 0;
  fi;
  T := MTSEParent(Representative(S));
  return ActionRank(MTSE(T, x, One(McAlisterTripleSemigroupGroup(T))), 0);
end);

# Why are there row spaces and matrices passed in here?
InstallMethod(LambdaRank, "for a matrix semigroup",
[IsMatrixOverFiniteFieldSemigroup], x -> Rank);

InstallMethod(RhoRank, "for a transformation semigroup",
[IsTransformationSemigroup], _ -> function(x)
  if IsEmpty(x) then
    return 0;
  else
    return MaximumList(x);
  fi;
end);

InstallMethod(RhoRank, "for a partial perm semigroup",
[IsPartialPermSemigroup], _ -> Length);

InstallMethod(RhoRank, "for a bipartition semigroup",
[IsBipartitionSemigroup], _ -> BLOCKS_RANK);

InstallMethod(RhoRank, "for a Rees 0-matrix subsemigroup",
[IsReesZeroMatrixSubsemigroup], LambdaRank);

InstallMethod(RhoRank, "for a matrix semigroup",
[IsMatrixOverFiniteFieldSemigroup], LambdaRank);

InstallMethod(RhoRank, "for a McAlister subsemigroup",
[IsMcAlisterTripleSubsemigroup], S ->
function(x)
  local T;
  if x = 0 then
    return 0;
  fi;
  T := MTSEParent(Representative(S));
  return ActionRank(MTSE(T, x, One(McAlisterTripleSemigroupGroup(T))), 0);
end);

# if g=LambdaInverse(X, f) and X^f=Y, then Y^g=X and g acts on the right
# like the inverse of f on Y.

InstallMethod(LambdaInverse, "for a transformation semigroup",
[IsTransformationSemigroup], S -> INV_LIST_TRANS);

InstallMethod(LambdaInverse, "for a partial perm semigroup",
[IsPartialPermSemigroup], S -> {_, f} -> f ^ -1);

InstallMethod(LambdaInverse, "for a McAlister triple subsemigroup",
[IsMcAlisterTripleSubsemigroup], S -> {_, f} -> f ^ -1);

InstallMethod(LambdaInverse, "for a bipartition semigroup",
[IsBipartitionSemigroup], S -> BLOCKS_INV_RIGHT);

InstallMethod(LambdaInverse, "for a Rees 0-matrix subsemigroup",
[IsReesZeroMatrixSubsemigroup], S ->
function(k, x)
  local i;
  if x![1] = 0 or k = 0 then
    return x;
  fi;
  i := First([1 .. Length(x![4][x![3]])], i -> x![4][x![3]][i] <> 0);
  return Objectify(FamilyObj(x)!.type,
                   [i,
                    (x![4][k][x![1]] * x![2] * x![4][x![3]][i]) ^ -1,
                    k,
                    x![4]]);
end);

# if g = RhoInverse(X, f) and f ^ X = Y (this is a left action), then
# g ^ Y = X and g acts on the left like the inverse of f on Y.

InstallMethod(LambdaInverse, "for a matrix semigroup",
[IsMatrixOverFiniteFieldSemigroup], S ->
{rsp, mat} -> MatrixOverFiniteFieldLocalRightInverse(S, rsp, mat));

InstallMethod(RhoInverse, "for a transformation semigroup",
[IsTransformationSemigroup], S -> INV_KER_TRANS);

InstallMethod(RhoInverse, "for a partial perm semigroup",
[IsPartialPermSemigroup], S -> {_, f} -> f ^ -1);

InstallMethod(RhoInverse, "for a McAlister triple subsemigroup",
[IsMcAlisterTripleSubsemigroup], S -> {_, f} -> f ^ -1);

# JDM better method for this!!

InstallMethod(RhoInverse, "for a Rees 0-matrix subsemigroup",
[IsReesZeroMatrixSubsemigroup], S ->
function(k, x)
  local i;
  if x![1] = 0 or k = 0 then
    return x;
  fi;
  i := First([1 .. Length(x![4])], i -> x![4][i][x![1]] <> 0);
  return Objectify(FamilyObj(x)!.type,
                   [k,
                    (x![4][i][x![1]] * x![2] * x![4][x![3]][k]) ^ -1,
                    i,
                    x![4]]);
end);

InstallMethod(RhoInverse, "for a bipartition semigroup",
[IsBipartitionSemigroup], S -> BLOCKS_INV_LEFT);

InstallMethod(RhoInverse, "for a matrix semigroup",
[IsMatrixOverFiniteFieldSemigroup], s ->
function(rsp, mat)
  return TransposedMat(MatrixOverFiniteFieldLocalRightInverse(s,
                          rsp, TransposedMat(mat)));
end);

InstallMethod(LambdaBound, "for a transformation semigroup",
[IsTransformationSemigroup], s ->
function(r)
  if r < 100 then
    return Factorial(r);
  else
    return infinity;
  fi;
end);

InstallMethod(RhoBound, "for a transformation semigroup",
[IsTransformationSemigroup], LambdaBound);

InstallMethod(LambdaBound, "for a partial perm semigroup",
[IsPartialPermSemigroup], s ->
function(r)
  if r < 100 then
    return Factorial(r);
  else
    return infinity;
  fi;
end);
InstallMethod(RhoBound, "for a partial perm semigroup",
[IsPartialPermSemigroup], LambdaBound);

InstallMethod(LambdaBound, "for a bipartition semigroup",
[IsBipartitionSemigroup], s ->
function(r)
  if r < 100 then
    return Factorial(r);
  else
    return infinity;
  fi;
end);

InstallMethod(RhoBound, "for a bipartition semigroup",
[IsBipartitionSemigroup], LambdaBound);

InstallMethod(LambdaBound, "for a Rees 0-matrix semigroup",
[IsReesZeroMatrixSubsemigroup], s ->
function(r)
  if r < 100 then
    return Factorial(r);
  else
    return infinity;
  fi;
end);

InstallMethod(RhoBound, "for a Rees 0-matrix semigroup",
[IsReesZeroMatrixSubsemigroup], LambdaBound);

InstallMethod(LambdaBound, "for a McAlister subsemigroup",
[IsMcAlisterTripleSubsemigroup], S ->
function(r)
  local G;
  G := McAlisterTripleSemigroupGroup(MTSEParent(Representative(S)));
  return Size(Stabilizer(G, r, McAlisterTripleSemigroupAction(S)));
end);

InstallMethod(RhoBound, "for a McAlister subsemigroup",
[IsMcAlisterTripleSubsemigroup], LambdaBound);

InstallMethod(LambdaBound, "for a matrix semigroup",
[IsMatrixOverFiniteFieldSemigroup], S ->
function(r)
  if r = 0 then
    return 1;
  elif r < 100 then
    return Size(GL(NrRows(Representative(S)), BaseDomain(S)));
  else
    return infinity;
  fi;
end);

InstallMethod(RhoBound, "for a matrix semigroup",
[IsMatrixOverFiniteFieldSemigroup], LambdaBound);

# LamdaIdentity(s) returns a function that returns
# the identity element of the Schutzenberger group
# elements produced by LambdaPerm

# TODO(later) these functions don't need the argument <r> any more

InstallMethod(LambdaIdentity, "for a transformation semigroup",
[IsTransformationSemigroup], _ -> _ -> ());

InstallMethod(RhoIdentity, "for a transformation semigroup",
[IsTransformationSemigroup], _ -> _ -> ());

InstallMethod(LambdaIdentity, "for a partial perm semigroup",
[IsPartialPermSemigroup], _ -> _ -> ());

InstallMethod(RhoIdentity, "for a partial perm semigroup",
[IsPartialPermSemigroup], _ -> _ -> ());

InstallMethod(LambdaIdentity, "for a bipartition semigroup",
[IsBipartitionSemigroup], _ -> _ -> ());

InstallMethod(RhoIdentity, "for a bipartition semigroup",
[IsBipartitionSemigroup], _ -> _ -> ());

InstallMethod(LambdaIdentity, "for a Rees 0-matrix semigroup",
[IsReesZeroMatrixSubsemigroup], _ -> _ -> ());

InstallMethod(RhoIdentity, "for a Rees 0-matrix semigroup",
[IsReesZeroMatrixSubsemigroup], _ -> _ -> ());

InstallMethod(LambdaIdentity, "for a McAlister triple subsemigroup",
[IsMcAlisterTripleSubsemigroup], _ -> _ -> ());

InstallMethod(RhoIdentity, "for a McAlister triple subsemigroup",
[IsMcAlisterTripleSubsemigroup], LambdaIdentity);

InstallMethod(LambdaIdentity, "for a matrix semigroup",
[IsMatrixOverFiniteFieldSemigroup],
S -> r -> IdentityMat(r, BaseDomain(Representative(S))));

InstallMethod(RhoIdentity, "for a matrix semigroup",
[IsMatrixOverFiniteFieldSemigroup],
S -> r -> IdentityMat(r, BaseDomain(Representative(S))));

# LambdaPerm(s) returns a permutation from two acting semigroup elements with
# equal LambdaFunc and RhoFunc. This is required to check if one of the two
# elements belongs to the schutz gp of a lambda orb.

InstallMethod(LambdaPerm, "for a transformation semigroup",
[IsTransformationSemigroup], S -> PermLeftQuoTransformationNC);

InstallMethod(LambdaPerm, "for a partial perm semigroup",
[IsPartialPermSemigroup], S -> PERM_LEFT_QUO_PPERM_NC);

InstallMethod(LambdaPerm, "for a bipartition semigroup",
[IsBipartitionSemigroup], S -> BIPART_PERM_LEFT_QUO);

InstallMethod(LambdaPerm, "for a Rees 0-matrix subsemigroup",
[IsReesZeroMatrixSubsemigroup], S ->
function(x, y)
  if x![1] = 0 or y![1] = 0 then
    return ();
  fi;
  return x![2] ^ -1 * y![2];
end);

InstallMethod(LambdaPerm, "for a McAlister triple subsemigroup",
[IsMcAlisterTripleSubsemigroup], _ -> {x, y} -> x[2] ^ -1 * y[2]);

InstallMethod(LambdaPerm, "for a matrix semigroup",
[IsMatrixOverFiniteFieldSemigroup],
S -> {x, y} -> MatrixOverFiniteFieldSchutzGrpElement(S, x, y));

# Returns a permutation mapping LambdaFunc(S)(x) to LambdaFunc(S)(y) so that
# yx ^ -1(i) = p(i) when RhoFunc(S)(x) = RhoFunc(S)(y)!!

InstallMethod(LambdaConjugator, "for a transformation semigroup",
[IsTransformationSemigroup], _ -> TRANS_IMG_CONJ);

InstallMethod(LambdaConjugator, "for a partial perm semigroup",
[IsPartialPermSemigroup],
_ -> {x, y} -> MappingPermListList(IMAGE_PPERM(x), IMAGE_PPERM(y)));

InstallMethod(LambdaConjugator, "for a bipartition semigroup",
[IsBipartitionSemigroup], S -> BIPART_LAMBDA_CONJ);

InstallMethod(LambdaConjugator, "for a Rees 0-matrix subsemigroup",
[IsReesZeroMatrixSubsemigroup], S -> {x, y} -> ());
# FIXME(later) is this right???? This is not right!!

InstallMethod(LambdaConjugator, "for a McAlister triple subsemigroup",
[IsMcAlisterTripleSubsemigroup],
function(S)
  local T, G, act;
  T := MTSEParent(Representative(S));
  G := McAlisterTripleSemigroupGroup(T);
  act := MTSUnderlyingAction(T);  # MTSAction is not an action, causes problems
  return {x, y} -> RepresentativeAction(G,
                                        LambdaFunc(S)(x),
                                        LambdaFunc(S)(y),
                                        act);
end);

InstallMethod(LambdaConjugator, "for a matrix semigroup",
[IsMatrixOverFiniteFieldSemigroup], S ->
{x, y} -> MatrixOverFiniteFieldLambdaConjugator(S, x, y));

# the function used to test if there is an idempotent with the specified
# lambda and rho values.

InstallMethod(IdempotentTester, "for a transformation semigroup",
[IsTransformationSemigroup], S ->
function(img, ker)
  if IsEmpty(img) then
    return IsEmpty(ker);
  fi;
  return IsInjectiveListTrans(img, ker) and Length(img) = MaximumList(ker);
end);

InstallMethod(IdempotentTester, "for a partial perm semigroup",
[IsPartialPermSemigroup], S -> \=);

InstallMethod(IdempotentTester, "for a bipartition semigroup",
[IsBipartitionSemigroup], S -> BLOCKS_E_TESTER);

InstallMethod(IdempotentTester, "for a Rees 0-matrix subsemigroup",
[IsReesZeroMatrixSubsemigroup], R ->
function(j, i)
  local parent;
  if i = 0 and j = 0 then
    return true;
  fi;
  parent := ReesMatrixSemigroupOfFamily(ElementsFamily(FamilyObj(R)));
  return Matrix(parent)[j][i] <> 0;
end);

InstallMethod(IdempotentTester, "for a McAlister triple subsemigroup",
[IsMcAlisterTripleSubsemigroup], S -> {x, y} -> x = y);

InstallMethod(IdempotentTester, "for a matrix semigroup",
[IsMatrixOverFiniteFieldSemigroup],
S -> {x, y} -> MatrixOverFiniteFieldIdempotentTester(S, x, y));

# the function used to create an idempotent with the specified lambda and rho
# values.

InstallMethod(IdempotentCreator, "for a transformation semigroup",
[IsTransformationSemigroup], S -> IDEM_IMG_KER_NC);

InstallMethod(IdempotentCreator, "for a partial perm semigp",
[IsPartialPermSemigroup], S -> PartialPermNC);

InstallMethod(IdempotentCreator, "for a bipartition semigroup",
[IsBipartitionSemigroup], S -> BLOCKS_E_CREATOR);

InstallMethod(IdempotentCreator, "for a Rees 0-matrix subsemigroup",
[IsReesZeroMatrixSubsemigroup], R ->
function(j, i)
  local mat;
  if i = 0 and j = 0 then
    return Objectify(TypeReesMatrixSemigroupElements(R), [0]);
  fi;
  mat := Matrix(ReesMatrixSemigroupOfFamily(ElementsFamily(FamilyObj(R))));
  return Objectify(TypeReesMatrixSemigroupElements(R),
                   [i, mat[j][i] ^ -1, j, mat]);
end);

InstallMethod(IdempotentCreator, "for a McAlister triple subsemigroup",
[IsMcAlisterTripleSubsemigroup], S ->
function(x, _)
  local T;
  T := MTSEParent(Representative(S));
  return MTSE(T, x, One(McAlisterTripleSemigroupGroup(T)));
end);

InstallMethod(IdempotentCreator, "for a matrix semigroup",
[IsMatrixOverFiniteFieldSemigroup],
S -> {x, y} -> MatrixOverFiniteFieldIdempotentCreator(S, x, y));

# the action of elements of the stabiliser of a lambda-value on any element of
# the semigroup with that lambda-value

# StabilizerAction will be \* for transformation and partial perm semigroups
# and something else for semigroups of bipartitions.

InstallMethod(StabilizerAction, "for a transformation semigroup",
[IsTransformationSemigroup], S -> OnRight);

InstallMethod(StabilizerAction, "for a partial perm semigroup",
[IsPartialPermSemigroup], S -> OnRight);

InstallMethod(StabilizerAction, "for a bipartition semigroup",
[IsBipartitionSemigroup], S -> BIPART_STAB_ACTION);

InstallMethod(StabilizerAction, "for a Rees 0-matrix subsemigroup",
[IsReesZeroMatrixSubsemigroup], S ->
function(x, p)
  if x![1] = 0 then
    return x;
  fi;
  return Objectify(TypeObj(x), [x![1], x![2] * p, x![3], x![4]]);
end);

InstallMethod(StabilizerAction, "for a McAlister triple subsemigroup",
[IsMcAlisterTripleSubsemigroup], S ->
function(x, p)
  local T;
  T := MTSEParent(x);
  return MTSE(T, x[1], x[2] * p);
end);

InstallMethod(StabilizerAction, "for a matrix semigroup",
[IsMatrixOverFiniteFieldSemigroup],
S -> {x, y} -> MatrixOverFiniteFieldStabilizerAction(S, x, y));

# IsActingSemigroupWithFixedDegreeMultiplication should be <true> if and only
# if it is only possible to multiply elements of the type in the semigroup with
# equal degrees.

InstallMethod(IsActingSemigroupWithFixedDegreeMultiplication,
"for a transformation semigroup",
[IsTransformationSemigroup and IsActingSemigroup], ReturnFalse);

InstallTrueMethod(IsActingSemigroupWithFixedDegreeMultiplication,
IsBipartitionSemigroup and IsActingSemigroup);

InstallMethod(IsActingSemigroupWithFixedDegreeMultiplication,
"for an acting partial perm semigroup",
[IsPartialPermSemigroup and IsActingSemigroup], ReturnFalse);

# this is not really relevant here.
InstallMethod(IsActingSemigroupWithFixedDegreeMultiplication,
"for an acting Rees 0-matrix subsemigroup",
[IsReesZeroMatrixSubsemigroup and IsActingSemigroup], ReturnFalse);

InstallMethod(IsActingSemigroupWithFixedDegreeMultiplication,
"for a McAlister triple subsemigroup",
[IsMcAlisterTripleSubsemigroup and IsActingSemigroup], ReturnFalse);

InstallTrueMethod(IsActingSemigroupWithFixedDegreeMultiplication,
                  IsMatrixOverFiniteFieldSemigroup);

InstallMethod(SchutzGpMembership, "for a transformation semigroup",
[IsTransformationSemigroup], _ -> {stab, x} -> SiftedPermutation(stab, x) = ());

InstallMethod(SchutzGpMembership, "for a partial perm semigroup",
[IsPartialPermSemigroup], _ -> {stab, x} -> SiftedPermutation(stab, x) = ());

InstallMethod(SchutzGpMembership, "for a Rees 0-matrix subsemigroup",
[IsReesZeroMatrixSubsemigroup],
_ -> {stab, x} -> SiftedPermutation(stab, x) = ());

InstallMethod(SchutzGpMembership, "for a McAlister triple subsemigroup",
[IsMcAlisterTripleSubsemigroup],
_ -> {stab, x} -> SiftedPermutation(stab, x) = ());

InstallMethod(SchutzGpMembership, "for a bipartition semigroup",
[IsBipartitionSemigroup],
_ -> {stab, x} -> SiftedPermutation(stab, x) = ());

InstallMethod(SchutzGpMembership, "for a matrix semigroup",
[IsMatrixOverFiniteFieldSemigroup], _ -> {stab, x} -> x in stab);

# One or a fake one for those types of object without one.

InstallMethod(FakeOne, "for a transformation collection",
[IsTransformationCollection], One);

InstallMethod(FakeOne, "for a partial perm collection",
[IsPartialPermCollection], One);

InstallMethod(FakeOne, "for a bipartition collection",
[IsBipartitionCollection], One);

InstallMethod(FakeOne, "for a Rees 0-matrix semigroup element collection",
[IsReesZeroMatrixSemigroupElementCollection], R -> SEMIGROUPS.UniversalFakeOne);

InstallMethod(FakeOne, "for a McAlister triple semigroup element collection",
[IsMcAlisterTripleSemigroupElementCollection],
S -> SEMIGROUPS.UniversalFakeOne);

# Matrix semigroup elements
InstallMethod(FakeOne, "for an FFE coll coll coll",
[IsFFECollCollColl],
function(coll)
  Assert(1, ForAll(coll, IsMatrixObjOverFiniteField));
  Assert(1, ForAll(coll, x -> NrRows(x) = NrRows(Representative(coll))));
  return One(Representative(coll));
end);

# missing hash functions

SEMIGROUPS.HashFunctionRZMSE := function(x, data, func)
  if x![1] = 0 then
    return 1;
  fi;
  # Use some big primes that are near the default hash table size
  if IsNBitsPcWordRep(x![2]) then
    return (104723 * x![1] + 104729 * x![3] + func(x![2], data))
      mod data[2] + 1;
  else
    return (104723 * x![1] + 104729 * x![3] + func(x![2], data)) mod data + 1;
  fi;
end;

InstallMethod(ChooseHashFunction,
"for a Rees 0-matrix semigroup element and integer",
[IsReesZeroMatrixSemigroupElement, IsInt],
function(x, hashlen)
  local R, data, under, func;

  R := ReesMatrixSemigroupOfFamily(FamilyObj(x));
  if IsMultiplicativeZero(R, x) then
    x := EmptyPlist(3);
    x[2] := Representative(UnderlyingSemigroup(R));
  fi;
  if IsNBitsPcWordRep(x![2]) then
    under := ChooseHashFunction(x![2], hashlen).func;
    data := ChooseHashFunction(x![2], hashlen).data;
  else
    under := ChooseHashFunction(x![2], hashlen).func;
    data := ChooseHashFunction(x![2], hashlen).data;
  fi;
  if data = fail then
    data := hashlen;
  fi;

  func := {x, hashlen} -> SEMIGROUPS.HashFunctionRZMSE(x, data, under);

  return rec(func := func, data := data);
end);

# fallback method for hashing

InstallMethod(ChooseHashFunction, "for an object and an int",
[IsObject, IsInt],
1,
{obj, hashlen} -> rec(func := {v, data} -> 1, data := fail));

# The next two methods are more general than might seem necessary but
# apparently ReesZeroMatrixSemigroup's satisfying IsWholeFamily are not in
# IsActingSemigroup but their ideals are, and we still require a method for
# ConvertToInternalElement as a result.

InstallMethod(ConvertToInternalElement, "for a semigroup and mult. elt.",
[IsSemigroup, IsMultiplicativeElement], {_, x} -> x);

InstallMethod(ConvertToExternalElement, "for a semigroup and mult. elt.",
[IsSemigroup, IsMultiplicativeElement], {_, x} -> x);

InstallMethod(ConvertToInternalElement,
"for an acting matrix over ff semigroup and matrix obj",
[IsActingSemigroup and IsMatrixOverFiniteFieldSemigroup, IsMatrixObj],
function(S, mat)
  local bd, n;

  Assert(1, IsMatrixObjOverFiniteField(mat));
  if NrRows(mat) = NrRows(Representative(S)) + 1 then
    return mat;
  fi;
  Assert(1, NrRows(mat) = NrRows(Representative(S)));

  bd  := BaseDomain(mat);
  n   := NrRows(mat);
  mat := List([1 .. n],
              i -> Concatenation(mat[i], [Zero(bd)]));
  Add(mat, ZeroMatrix(bd, 1, n + 1)[1]);
  mat[n + 1, n + 1] := One(bd);
  return Matrix(bd, mat);
end);

InstallMethod(ConvertToExternalElement,
"for an acting matrix over ff semigroup and matrix obj",
[IsActingSemigroup and IsMatrixOverFiniteFieldSemigroup, IsMatrixObj],
function(S, mat)
  local n;

  Assert(1, IsMatrixObjOverFiniteField(mat));
  if NrRows(mat) = NrRows(Representative(S)) then
    return mat;
  fi;
  Assert(1, NrRows(mat) = NrRows(Representative(S)) + 1);

  n := NrRows(mat) - 1;
  return Matrix(Unpack(mat){[1 .. n]}{[1 .. n]}, mat);
end);

InstallMethod(WeakInverse, "for a transformation",
[IsTransformation], InverseOfTransformation);

InstallMethod(WeakInverse, "for a partial perm",
[IsPartialPerm], INV);

InstallMethod(WeakInverse, "for a bipartition",
[IsBipartition], Star);
