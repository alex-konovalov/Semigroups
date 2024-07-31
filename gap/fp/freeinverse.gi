###############################################################################
##
##  fp/freeinverse.gi
##  Copyright (C) 2013-2022                                Julius Jonusas
##
##  Licensing information can be found in the README file of this package.
##
###############################################################################
##
##  Internal representation of the elements of free inverse semigroups is
##  is given as a list:
##  [
##  number of generators,
##  number of vertices,
##  finish vertex,
##  parent list (for each vertex gives the name of a parent),
##  list of labels (from a parent to a child),
##  adjacency list for every vertex
##  ]
##
##  For example an element xxx^-1yy^-1 is represented by:
##  [2, 4, 2, [fail, 1, 2, 2], [fail, 1, 1, 4], [2, , , ,], [3, 1 , ,4],
##     [ , 2, , ], [, , 2, ]];
##
##  Note that if x1, x2, ... are the generators, then in the internal
##  representation of x1 is 1, x1^-1 by 2, x2 by 3 and so on.
##

InstallTrueMethod(IsGeneratorsOfInverseSemigroup,
                  IsFreeInverseSemigroupElementCollection);

InstallImmediateMethod(IsFinite, IsFreeInverseSemigroup, 0, ReturnFalse);

############################################################################
##
## FreeInverseSemigroup( <rank>[, names] )
## FreeInverseSemigroup( name1, name2, ... )
## FreeInverseSemigroup( names )
##

InstallGlobalFunction(FreeInverseSemigroup,
function(arg)
  local names, F, type, gens, opts, S, m;

  # Get and check the argument list, and construct names if necessary.
  if Length(arg) = 1 and IsInt(arg[1]) and 0 < arg[1] then
    names := List([1 .. arg[1]],
                  i -> Concatenation("x", String(i)));
    MakeImmutable(names);
  elif Length(arg) = 2 and IsInt(arg[1]) and 0 < arg[1]
      and IsString(arg[2]) then
    names := List([1 .. arg[1]],
                  i -> Concatenation(arg[2], String(i)));
    MakeImmutable(names);
  elif Length(arg) = 1 and IsList(arg[1]) and IsEmpty(arg[1]) then
    names := arg[1];
  elif 1 <= Length(arg) and ForAll(arg, IsString) then
    names := arg;
  elif Length(arg) = 1 and IsList(arg[1])
      and ForAll(arg[1], IsString) then
    names := arg[1];
  else
    ErrorNoReturn("FreeInverseSemigroup(<name1>,<name2>..) or ",
                  "FreeInverseSemigroup(<rank> [, name]),");
  fi;

  if IsEmpty(names) then
    ErrorNoReturn("the number of generators of a free inverse semigroup must ",
                  "be non-zero");
  fi;

  F := NewFamily("FreeInverseSemigroupElementsFamily",
                 IsFreeInverseSemigroupElement,
                 CanEasilySortElements);

  type := NewType(F, IsFreeInverseSemigroupElement and IsPositionalObjectRep);

  gens := EmptyPlist(Length(names));
  for m in [1 .. Length(names)] do
    gens[m] := Objectify(type, [Length(names), 2, 2, [fail, 1],
                                [fail, 2 * m - 1], [], []]);
    gens[m]![6][2 * m - 1] := 2;
    gens[m]![7][2 * m] := 1;
  od;

  names := Concatenation(List(names, x -> [x, Concatenation(x, "^-1")]));
  StoreInfoFreeMagma(F, names, IsFreeInverseSemigroupElement);
  opts := SEMIGROUPS.ProcessOptionsRec(SEMIGROUPS.DefaultOptionsRec,
                                       rec(batch_size := 401));
  # We require a smallish batch_size because otherwise the iterators are
  # unreasonably slow.
  S := Objectify(NewType(FamilyObj(gens),
                         IsFreeInverseSemigroupCategory
                          and IsInverseSemigroup
                          and IsAttributeStoringRep),
                 rec(opts := opts));
  SetGeneratorsOfInverseSemigroup(S, gens);
  SetIsFreeInverseSemigroup(S, true);
  SetIsSimpleSemigroup(S, false);

  FamilyObj(S)!.semigroup := S;
  F!.semigroup := S;

  SetIsWholeFamily(S, true);
  SetIsTrivial(S, Length(names) = 0);

  return S;
end);

############################################################################
##
## ViewObj
##

InstallMethod(ViewObj, "for a free inverse semigroup element",
[IsFreeInverseSemigroupElement], PrintObj);

InstallMethod(PrintObj, "for a free inverse semigroup element",
[IsFreeInverseSemigroupElement],
function(x)

  if UserPreference("semigroups", "FreeInverseSemigroupElementDisplay")
      = "minimal" then
    Print(MinimalWord(x));
  else
    Print(CanonicalForm(x));
  fi;

  return;
end);

InstallMethod(ViewObj,
"for a free inverse semigroup containing the whole family",
[IsFreeInverseSemigroupCategory],
function(S)
  if GAPInfo.ViewLength * 10 < Length(GeneratorsOfMagma(S)) then
    Print("<free inverse semigroup with ",
          Length(GeneratorsOfInverseSemigroup(S)),
           " generators>");
  else
    Print("<free inverse semigroup on the generators ",
          GeneratorsOfInverseSemigroup(S), ">");
  fi;
end);

############################################################################
##
## MinimalWord
##

InstallMethod(MinimalWord, "for a free inverse semigroup element",
[IsFreeInverseSemigroupElement],
function(x)
  local InvertGenerator, is_a_child_of, gen, stop_start, i, j, path, words,
   pos, part, temp_word, out, names;

  InvertGenerator := function(n)
    if n mod 2 = 0 then
      return n - 1;
    fi;
    return n + 1;
  end;

  is_a_child_of := x![4];
  gen := x![5];
  stop_start := [];  # stop_start[i]=j if vertex i is the jth vertex in the path
                     # from the stop to the start vertex.
  i := x![3];
  j := 1;
  path := [];

  while i <> fail do
    stop_start[i] := j;
    path[j] := i;
    j := j + 1;
    i := is_a_child_of[i];  # parent of i
  od;

  words := EmptyPlist(j - 1);
  pos := [];   # keeps track of the vertices already visited
  part := [];  # keeps track of the part of the tree, that vertex i is in

  i := x![2];  # nr of vertices
  while i > 0 do
    temp_word := [];
    j := i;
    while not IsBound(pos[j]) and not IsBound(stop_start[j]) do
      Add(temp_word, InvertGenerator(gen[j]));
      j := is_a_child_of[j];
    od;
    temp_word := Concatenation(List(Reversed(temp_word), InvertGenerator),
                               temp_word);
    if IsBound(stop_start[j]) and not IsBound(words[stop_start[j]]) then
      # first time in this part of the tree
      words[stop_start[j]] := temp_word;
      part[j] := stop_start[j];
      pos[j] := 0;
    else  # been in this part before
      words[part[j]] := Concatenation(words[part[j]]{[1 .. pos[j]]},
                                      temp_word,
                                      words[part[j]]{[pos[j] + 1 ..
                                                      Length(words[part[j]])]});
    fi;
    i := i - 1;
  od;

  out := [];
  path := Reversed(path);

  names := FamilyObj(x)!.names;

  for i in path do
    Append(out, List(words[stop_start[i]], l -> Concatenation(names[l], "*")));
    if i + 1 <= Length(path) then
      Add(out, Concatenation(names[gen[path[i + 1]]], "*"));
    fi;
  od;

  out := Concatenation (out);
  if out[Length(out)] = '*' then
    Remove(out);  # removes the last entry
  fi;

  return out;
end);

##############################################################################
##
## CanonicalForm( s )
##
##

InstallMethod(CanonicalForm, "for a free inverse semigroup element",
[IsFreeInverseSemigroupElement],
function(tree)
  local InvertGenerator, children, fork, tail, maxleftreducedpath,
  maxleftreduced, groupelem, i, mlr, output, pivot;

  InvertGenerator := function(n)
    if n mod 2 = 0 then
      return n - 1;
    fi;
    return n + 1;
  end;

  children := function(n)
    local list, i;

    list := [];
    for i in [1 .. Length(tree![4])] do
      if tree![4][i] = n then
        Add(list, i);
      fi;
    od;
    return list;
  end;

  fork := function(list1, list2)
    local i, result;

    result := [];
    for i in list2 do
      Add(result, Concatenation(list1, [i]));
    od;
    return result;
  end;

  tail := list -> list[Length(list)];

  maxleftreducedpath := fork([], children(1));
  for pivot in maxleftreducedpath do
    while children(tail(pivot)) <> [] do
      maxleftreducedpath := fork(pivot, children(tail(pivot)));
      Add(pivot, tail(children(tail(pivot))));
    od;
  od;

  maxleftreduced := [];
  for i in [1 .. Length(maxleftreducedpath)] do
    maxleftreduced[i] := List(maxleftreducedpath[i], x -> tree![5][x]);
    maxleftreduced[i] := Concatenation(maxleftreduced[i],
                                       Reversed(List(maxleftreduced[i],
                                                     InvertGenerator)));
  od;

  groupelem := [];
  i := tree![3];
  while i <> 1 do
    Add(groupelem, i);
    i := tree![4][i];
  od;
  groupelem := Reversed(List(groupelem, x -> tree![5][x]));

  mlr := maxleftreduced;
  if Length(mlr) = 1 and Length(mlr[1]) = 2 and Length(groupelem) > 0 and
      ((mlr[1][1] mod 2 = 1 and mlr[1][2] = mlr[1][1] + 1) or
       (mlr[1][1] mod 2 = 0 and mlr[1][2] = mlr[1][1] - 1)) then
    output := Concatenation(List(groupelem, x -> FamilyObj(tree)!.names[x]));
  else
    output :=
          Concatenation(List(Concatenation(Concatenation(Set(mlr)), groupelem),
                             x -> FamilyObj(tree)!.names[x]));
  fi;
  return output;
end);

##############################################################################
##
## Equality
##

InstallMethod(\=, "for elements of a free inverse semigroup",
IsIdenticalObj,
[IsFreeInverseSemigroupElement, IsFreeInverseSemigroupElement],
function(tree1, tree2)
  local isequal, i;

  isequal := true;
  for i in [1 .. 5 + tree1![2]] do
    if tree1![i] <> tree2![i] then
      isequal := false;
      break;
    fi;
  od;

  if not isequal then
    isequal := CanonicalForm(tree1) = CanonicalForm(tree2);
  fi;
  return isequal;
end);

InstallMethod(\<, "for elements of a free inverse semigroup",
IsIdenticalObj,
[IsFreeInverseSemigroupElement, IsFreeInverseSemigroupElement],
{tree1, tree2} -> CanonicalForm(tree1) < CanonicalForm(tree2));

InstallMethod(ChooseHashFunction, "for a free inverse semigroup element",
[IsFreeInverseSemigroupElement, IsInt],
  function(x, hashlen)
  local sample, record, func;
  sample := List(CanonicalForm(x), IntChar);
  record := ChooseHashFunction(sample, hashlen);
  func := {x, data} -> record.func(List(CanonicalForm(x), IntChar), data);
  return rec(func := func, data := record.data);
end);

##############################################################################
##
## Multiplication
##

InstallMethod(\*, "for elements of a free inverse semigroup",
IsIdenticalObj,
[IsFreeInverseSemigroupElement, IsFreeInverseSemigroupElement],
function(tree1, tree2)
  local new_names, product, i, parent, InvertGenerator;

  InvertGenerator := function(n)
    if n mod 2 = 0 then
      return n - 1;
    fi;
    return n + 1;
  end;

  new_names    := [];
  new_names[1] := tree1![3];

  # product := StructuralCopy(tree1);
  product := [];
  for i in [1 .. tree1![2] + 5] do
    product[i] := ShallowCopy(tree1![i]);
  od;

  for i in [2 .. tree2![2]] do
    parent := new_names[tree2![4][i]];
    if parent <= tree1![2] and IsBound(tree1![parent + 5][tree2![5][i]]) then
      new_names[i] := tree1![parent + 5][tree2![5][i]];
    else
      product[2] := product[2] + 1;
      new_names[i] := product[2];
      product[4][product[2]] := parent;
      product[5][product[2]] := tree2![5][i];
      product[product[2] + 5] := [];
      product[product[2] + 5][InvertGenerator(tree2![5][i])] := parent;
      product[parent + 5][tree2![5][i]] := product[2];
    fi;

  od;
  product[3] := new_names[tree2![3]];
  return Objectify(TypeObj(tree1), product);
end);

##############################################################################
##
## Inverse
##

InstallMethod(\^, "for elements of a free inverse semigroup",
[IsFreeInverseSemigroupElement, IsNegInt],
function(tree, n)
  local product, old_names, new_names, label, current_old, result, i, j;

  product := [];
  product[1] := tree![1];
  product[2] := tree![2];
  old_names := [];
  old_names[1] := tree![3];
  new_names := [];
  new_names[tree![3]] := 1;
  product[4] := [];
  product[5] := [];

  label := 2;

  for i in [1 .. tree![2]] do
    product[5 + i] := [];
    for j in [1 .. 2 * tree![1]] do
      if IsBound(tree![old_names[i] + 5][j]) then
        current_old := tree![old_names[i] + 5][j];
        if not IsBound(new_names[current_old]) then
          old_names[label] := current_old;
          new_names[current_old] := label;
          product[4][new_names[current_old]] := i;
          product[5][new_names[current_old]] := j;
          label := label + 1;
        fi;
        product[5 + i][j] := new_names[current_old];
      fi;
    od;
  od;

  product[3] := new_names[1];
  product[4][1] := fail;
  product[5][1] := fail;

  result := Objectify(TypeObj(tree), product);
  return result ^ (-n);
end);

###########################################################################
##
## Size
##

InstallMethod(Size, "for a free inverse semigroup",
[IsFreeInverseSemigroupCategory], S -> infinity);

InstallMethod(IsFreeInverseSemigroup, "for a semigroup",
[IsSemigroup],
function(s)
  local gens, occurs, used, list, g, i;

  if not IsInverseSemigroup(s) then
    return false;
  elif IsFreeInverseSemigroupElementCollection(s) then
    gens := Generators(s);
    occurs := BlistList([1 .. Length(FamilyObj(gens[1])!.names) / 2], []);
    used := BlistList([1 .. Length(FamilyObj(gens[1])!.names) / 2], []);
    for g in gens do
      list := g![5];
      for i in [2 .. Length(list)] do
        used[Int((list[i] + 1) / 2)] := true;
      od;
      if g![2] = 2 then
        occurs[Int((g![5][2] + 1) / 2)] := true;
      fi;
    od;

    if occurs = used then
      return true;
    fi;
  fi;

  ErrorNoReturn("cannot determine the answer");
end);
