############################################################################
##
##  elements/pperm.gi
##  Copyright (C) 2016-2022                                 Wilf A. Wilson
##
##  Licensing information can be found in the README file of this package.
##
#############################################################################

InstallMethod(IndexPeriodOfSemigroupElement, "for a partial perm",
[IsPartialPerm], IndexPeriodOfPartialPerm);

InstallMethod(CyclesOfPartialPerm, "for a partial perm", [IsPartialPerm],
function(f)
  return DigraphAllSimpleCircuits(AsDigraph(f));
end);

DeclareGlobalVariable("_RANDOM_PPERM_CACHED_VALUES");
MakeReadWriteGlobal("_RANDOM_PPERM_CACHED_VALUES");
_RANDOM_PPERM_CACHED_VALUES := WeakPointerObj([]);

InstallMethod(UniformRandomPartialPerm, "for a positive integer", [IsPosInt],
function(n)
  local cache, num_bijections, r, im, unused_vals, num_undefined,
  num_each_defined, pos, i, j;

  cache := Immutable(_RANDOM_PPERM_CACHED_VALUES);

  if not IsBound(cache[n + 1]) then
    # TODO check that all the values in cache are bound
    cache := [];
    cache[1] := [1];
    for i in [2 .. n + 1] do
      cache[i] := [1];
      for j in [2 .. i] do
        cache[i][j] := cache[i][j - 1] + (i - 1) * cache[i - 1][j - 1];
      od;
    od;
  fi;

  # The number of partial perms from a set of size i to a set of size j.
  num_bijections := function(i, j)
    local tmp;
    if j < i then
      tmp := i;
      i := j;
      j := tmp;
    fi;
    return Sum([0 .. i], r -> Binomial(i, r) * Binomial(j, r) * Factorial(r));
  end;

  num_bijections := function(i, j)
    local tmp;
    if j > i then
      tmp := i;
      i := j;
      j := tmp;
    fi;
    return cache[i + 1][j + 1];
  end;

  # Rank so far
  r := 0;
  im := [];
  # TODO update to datastructures 0.3.0
  unused_vals := HashSet([1 .. n]);

  for i in [1 .. n] do
    num_undefined := num_bijections(n - i, n - r);
    num_each_defined := num_bijections(n - i, n - r - 1);
    pos := Random(1, num_undefined + (n - r) * num_each_defined);
    if pos <= num_undefined then
      im[i] := 0;  # undefined
    else
      pos := pos - num_undefined;
      im[i] := Set(unused_vals)[QuoInt(pos - 1, num_each_defined) + 1];
      RemoveSet(unused_vals, im[i]);
      r := r + 1;
    fi;
  od;
  _RANDOM_PPERM_CACHED_VALUES := WeakPointerObj(cache);
  return PartialPermNC(im);
end);
