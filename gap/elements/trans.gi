############################################################################
##
##  elements/trans.gi
##  Copyright (C) 2015-2022                              James D. Mitchell
##
##  Licensing information can be found in the README file of this package.
##
#############################################################################

InstallMethod(CanonicalTransformation, "for a transformation",
[IsTransformation], f -> CanonicalTransformation(f, DegreeOfTransformation(f)));

InstallMethod(CanonicalTransformation, "for a transformation",
[IsTransformation, IsInt],
function(f, n)
  local digraph;
  if n < DegreeOfTransformation(f) then
    ErrorNoReturn("the second argument (an integer) must be at least ",
                  "the degree of the first argument (a transformation)");
  fi;

  digraph := AsDigraph(f, n);
  return AsTransformation(OnDigraphs(digraph,
                                     BlissCanonicalLabelling(digraph)));
end);

InstallMethod(TransformationByImageAndKernel, "for an image and partition",
[IsHomogeneousList, IsCyclotomicCollColl],
function(im, ker)
  local flat, i;

  if not ForAll(ker, class -> ForAll(class, IsPosInt)) then
    ErrorNoReturn("the argument must be a list of lists of pos ints");
  fi;

  flat := Union(ker);

  if flat <> [1 .. Length(flat)] then
    ErrorNoReturn("the union of the second argument (a partition) must ",
                  "be [1 .. ", Length(flat), "]");
  fi;

  for i in [1 .. Length(ker)] do
    flat{ker[i]} := [1 .. Length(ker[i])] * 0 + i;
  od;
  return TransformationByImageAndKernel(im, flat);
end);

InstallMethod(IndexPeriodOfSemigroupElement, "for a transformation",
[IsTransformation], IndexPeriodOfTransformation);

InstallMethod(IsRefinementKernelOfTransformation,
"for two transformations in a semigroup of degree n",
[IsTransformation, IsTransformation, IsInt],
function(a, b, n)
    local m, i, idx, q, class;
    if DegreeOfTransformation(a) > n then 
        ErrorNoReturn("Degree of the first transformation greater than ", n,
            ".\nExpecting a degree at most n, found ", DegreeOfTransformation(a),
            " instead.");
    fi;
    if DegreeOfTransformation(b) > n then 
        ErrorNoReturn("Degree of the second transformation greater than ", n,
            ".\nExpecting a degree at most n, found ", DegreeOfTransformation(b),
            " instead.");
    fi;
    q := [];
    for class in KernelOfTransformation(a, n) do
        m := Minimum(class);
        for i in class do
            q[i] := m;
        od;
    od;
    for class in KernelOfTransformation(b, n) do
        idx := q[class[1]];
        for i in class do
            if q[i] <> idx then
                return false;
            fi;
        od;
    od;
    return true;
end);

InstallMethod(IsRefinementKernelOfTransformation,
"for two transformations",
[IsTransformation, IsTransformation],
function(a, b)
    local m, i, idx, q, class, n;
    n := Maximum(DegreeOfTransformation(a), DegreeOfTransformation(b));
    q := [];
    for class in KernelOfTransformation(a, n) do
        m := Minimum(class);
        for i in class do
            q[i] := m;
        od;
    od;
    for class in KernelOfTransformation(b, n) do
        idx := q[class[1]];
        for i in class do
            if q[i] <> idx then
                return false;
            fi;
        od;
    od;
    return true;
end);