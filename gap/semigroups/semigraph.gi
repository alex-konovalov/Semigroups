#############################################################################
##
##  semigroups/semigraph.gi
##  Copyright (C) 2014-2022               Zak Mesyan and James D. Mitchell
##
##  Licensing information can be found in the README file of this package.
##
#############################################################################
##

InstallMethod(AsMonoid, "for a graph inverse semigroup",
[IsGraphInverseSemigroup], ReturnFail);

InstallMethod(ViewString, "for a graph inverse semigroup",
[IsGraphInverseSemigroup],
RankFilter(IsGroupAsSemigroup),  # to beat library method for groups as semigrps
function(S)
  local D, finiteness;

  D := GraphOfGraphInverseSemigroup(S);

  if IsAcyclicDigraph(D) then
    finiteness := "finite";
  else
    finiteness := "infinite";
  fi;

  return PRINT_STRINGIFY(
    StringFormatted("<{} graph inverse semigroup with {}, {}>",
    finiteness,
    Pluralize(DigraphNrVertices(D), "vertex"),
    Pluralize(DigraphNrEdges(D), "edge")));
end);

InstallMethod(AssignGeneratorVariables, "for an inverse semigroup",
[IsGraphInverseSemigroup],
function(S)
  DoAssignGenVars(GeneratorsOfInverseSemigroup(S));
end);

InstallMethod(GraphInverseSemigroup, "for a digraph",
[IsDigraph],
function(graph)
  local fam, S, gens, i;

  fam := NewFamily("GraphInverseSemigroupElementsFamily",
                   IsGraphInverseSemigroupElement,
                   CanEasilySortElements,
                   CanEasilySortElements);

  # create the semigroup
  S := Objectify(NewType(CollectionsFamily(fam),
                         IsWholeFamily and IsGraphInverseSubsemigroup and
                         IsAttributeStoringRep),
                 rec());

  if not IsAcyclicDigraph(graph) then
    Info(InfoWarning, 1, "the graph defines an infinite semigroup!");
    SetIsFinite(S, false);
  else
    SetIsFinite(S, true);
  fi;

  # store the type of the elements in the family
  fam!.type := NewType(fam, IsGraphInverseSemigroupElement);
  fam!.semigroup := S;

  gens := [];
  for i in [1 .. DigraphNrVertices(graph) + DigraphNrEdges(graph)] do
    Add(gens, Objectify(fam!.type, [[i], graph]));
  od;
  SetGeneratorsOfSemigroup(S,
                           Concatenation(gens,
                                         List([1 .. DigraphNrEdges(graph)],
                                              x -> gens[x] ^ -1)));
  SetGeneratorsOfInverseSemigroup(S, gens);
  SetGraphOfGraphInverseSemigroup(S, graph);
  return S;
end);

InstallMethod(IsVertex, "for a graph inverse semigroup element",
[IsGraphInverseSemigroupElement],
x -> Length(x![1]) = 1 and AbsInt(x![1][1]) > Length(DigraphSource(x![2])));

InstallMethod(MultiplicativeZero, "for a graph inverse semigroup",
[IsGraphInverseSemigroup],
function(S)
  return Objectify(ElementsFamily(FamilyObj(S))!.type,
                                  [[0], GraphOfGraphInverseSemigroup(S)]);
end);

InstallMethod(ZeroOp, "for a graph inverse semigroup element",
[IsGraphInverseSemigroupElement],
x -> Objectify(FamilyObj(x)!.type, [[0], x![2]]));

InstallMethod(IsZero, "for a graph inverse semigroup element",
[IsGraphInverseSemigroupElement], x -> x![1][1] = 0);

InstallMethod(Source, "for a graph inverse semigroup element",
[IsGraphInverseSemigroupElement],
function(x)
  if IsVertex(x) then
    return x;
  elif x![1][1] > 0 then
    return Objectify(FamilyObj(x)!.type,
                     [[DigraphSource(x![2])[x![1][1]] + DigraphNrEdges(x![2])],
                      x![2]]);
  elif x![1][1] < 0 then
    return Objectify(FamilyObj(x)!.type,
                     [[DigraphRange(x![2])[-x![1][1]] + DigraphNrEdges(x![2])],
                      x![2]]);
  fi;
  ErrorNoReturn("the argument (a graph inverse semigroup element) ",
                "must not be the zero element");
end);

InstallMethod(Range, "for a graph inverse semigroup element",
[IsGraphInverseSemigroupElement],
function(x)
  if IsVertex(x) then
    return x;
  elif x![1][Length(x![1])] > 0 then
    return Objectify(FamilyObj(x)!.type,
                     [[DigraphRange(x![2])[x![1][Length(x![1])]] +
                       DigraphNrEdges(x![2])],
                      x![2]]);
  elif x![1][Length(x![1])] < 0 then
    return Objectify(FamilyObj(x)!.type,
                     [[DigraphSource(x![2])[-x![1][Length(x![1])]] +
                       DigraphNrEdges(x![2])],
                      x![2]]);
  fi;
  ErrorNoReturn("the argument (a graph inverse semigroup element) ",
                "must not be the zero element");
end);

InstallMethod(String, "for a graph inverse semigroup element",
[IsGraphInverseSemigroupElement],
function(x)
  local str, gr, i;

  if x![1] = [0] then
    return String(0);
  fi;

  str := "";
  gr := x![2];
  for i in x![1] do
    if i > Length(DigraphSource(gr)) then
      Append(str, "v_");
      Append(str, String(i - Length(DigraphSource(gr))));
    elif i > 0 then
      Append(str, "e_");
      Append(str, String(i));
    else
      Append(str, "e_");
      Append(str, String(-i));
      Append(str, "^-1");
    fi;
  od;
  return str;
end);

InstallMethod(PrintObj, "for a graph inverse semigroup",
[IsGraphInverseSemigroup],
function(S)
  Print(String(S));
end);

InstallMethod(String, "for a graph inverse semigroup",
[IsGraphInverseSemigroup],
function(S)
  local str;
  str := "GraphInverseSemigroup( ";
  Append(str, String(GraphOfGraphInverseSemigroup(S)));
  Append(str, " )");
  return str;
end);

InstallMethod(\^, "for a graph inverse semigroup element and neg. integer",
[IsGraphInverseSemigroupElement, IsNegInt],
function(x, n)
  if IsZero(x) or IsVertex(x) then
    return x;
  fi;
  return Objectify(FamilyObj(x)!.type, [Reversed(x![1]) * -1, x![2]]) ^ -n;
end);

InstallMethod(\<, "for elements of a graph inverse semigroup",
[IsGraphInverseSemigroupElement, IsGraphInverseSemigroupElement],
{x, y} -> x![1] < y![1]);

InstallMethod(\=, "for elements of a graph inverse semigroup",
[IsGraphInverseSemigroupElement, IsGraphInverseSemigroupElement],
{x, y} -> x![1] = y![1]);

InstallMethod(\*, "for elements of a graph inverse semigroup",
[IsGraphInverseSemigroupElement, IsGraphInverseSemigroupElement],
function(x, y)
  local type, graph, range, source, xobj, yobj, i, j;

  type := FamilyObj(x)!.type;
  graph := x![2];
  range := DigraphRange(graph);
  source := DigraphSource(graph);

  if IsZero(x) or IsZero(y) then
    return Zero(x);
  elif IsVertex(x) then
    if Source(y) = x then
      return y;
    fi;
    return Zero(x);
  elif IsVertex(y) then
    if Range(x) = y then
      return x;
    fi;
    return Zero(x);
  fi;

  xobj := x;
  yobj := y;
  x := x![1];
  y := y![1];
  i := 0;
  j := Length(x) + 1;

  while i < Length(y) and j > 1 do
    i := i + 1;
    j := j - 1;
    if SignInt(x[j]) = SignInt(y[i]) then
      if x[j] > 0 and range[x[j]] = source[y[i]] then
        return Objectify(type, [Concatenation(x{[1 .. j]},
                                              y{[i .. Length(y)]}),
                                              graph]);
      elif x[j] < 0 and source[-x[j]] = range[-y[i]] then
        return Objectify(type, [Concatenation(x{[1 .. j]},
                                              y{[i .. Length(y)]}),
                                              graph]);
      else
        return Zero(xobj);
      fi;
    elif x[j] < 0 and y[i] > 0 then
      if y[i] <> -x[j] then
        return Zero(xobj);
      fi;
    else
      if x[j] <> -y[i] and range[x[j]] <> range[-y[i]] then
        return Zero(xobj);
      else
        return Objectify(type, [Concatenation(x{[1 .. j]},
                                              y{[i .. Length(y)]}),
                                              graph]);
      fi;
    fi;
  od;
  # x or y cancelled completely...
  if i < Length(y) then
    return Objectify(type, [y{[i + 1 .. Length(y)]}, graph]);
  elif j > 1 then
    return Objectify(type, [x{[1 .. j - 1]}, graph]);
  else  # x = y ^ -1
    return Range(yobj);
  fi;
end);

InstallMethod(VerticesOfGraphInverseSemigroup,
"for a graph inverse semigroup",
[IsGraphInverseSemigroup],
function(S)
  local graph, m, result, i;
  graph := GraphOfGraphInverseSemigroup(S);
  m := DigraphNrEdges(graph);
  result := [];
  for i in [m + 1 .. DigraphNrVertices(graph) + m] do
    Add(result, Objectify(ElementsFamily(FamilyObj(S))!.type, [[i], graph]));
  od;
  return result;
end);

InstallMethod(IndexOfVertexOfGraphInverseSemigroup,
"for a graph inverse semigroup element",
[IsGraphInverseSemigroupElement],
function(x)
  if not IsVertex(x) then
    ErrorNoReturn(x, " must be a vertex of a graph inverse semigroup");
  fi;
  return x![1][1] - DigraphNrEdges(x![2]);
end);
