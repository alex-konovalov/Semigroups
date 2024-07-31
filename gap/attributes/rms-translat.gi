#############################################################################
##
# W  rms-translat.gi
# Y  Copyright (C) 2016-22                                      Finn Smith
##
##  Licensing information can be found in the README file of this package.
##
#############################################################################
##
#############################################################################
## This file contains special methods for translation semigroups and
## translational hulls of completely simple and 0-simple semigroups.
##
## These methods are based on the constructions given in
## Petrich, M. (1968)
## 'The translational hull of a completely 0-simple semigroup',
## Glasgow Mathematical Journal, 9(01), p. 1.
## doi: 10.1017/s0017089500000239
##
## A.H Clifford, Mario Petrich, (1977)
## 'Some classes of completely regular semigroups',
## Journal of Algebra, Volume 46, Issue 2, 1977, Pages 462-480,
## http://dx.doi.org/10.1016/0021-8693(77)90383-0.
#############################################################################

# TODO(later): compute translations of zero-simple semigroups using this

# TODO(later): swap Rows/Columns if one is smaller

#############################################################################
# 1. Internal Functions
#############################################################################

# Converts a pair of lists to a left translation without validation
SEMIGROUPS.RZMSTupleToLeftTranslation := function(S, idx_list, gp_list)
  local zero, L, foo;

  zero := MultiplicativeZero(S);
  L    := LeftTranslations(S);

  foo := function(x)
    if x = zero then
      return zero;
    elif idx_list[x[1]] <> 0 then
      return RMSElement(S,
                        idx_list[x[1]],
                        gp_list[x[1]] * x[2],
                        x[3]);
    else
      return zero;
    fi;
  end;
  return LeftTranslationNC(L, MappingByFunction(S, S, foo));
end;

# Converts a pair of lists to a right translation without validation
SEMIGROUPS.RZMSTupleToRightTranslation := function(S, idx_list, gp_list)
  local zero, R, foo;

  zero := MultiplicativeZero(S);
  R    := RightTranslations(S);

  foo := function(x)
    if x = zero then
      return zero;
    elif idx_list[x[3]] <> 0 then
      return RMSElement(S,
                        x[1],
                        x[2] * gp_list[x[3]],
                        idx_list[x[3]]);
    else
      return zero;
    fi;
  end;
  return RightTranslationNC(R, MappingByFunction(S, S, foo));
end;

# Converts a pair of pairs of lists to a bitranslation without validation
SEMIGROUPS.RZMSTupleToBitranslation := function(H, x)
  local S, l, r;

  S := UnderlyingSemigroup(H);
  l := SEMIGROUPS.RZMSTupleToLeftTranslation(S, x[1][1], x[1][2]);
  r := SEMIGROUPS.RZMSTupleToRightTranslation(S, x[2][1], x[2][2]);

  return BitranslationNC(H, l, r);
end;

# Converts the transformation underlying a left translation into the arguments
# required for the LeftTranslationsOfNormalRMS function.
# Arguments are:
# 1. L, a left translations semigroup over a normalised RMS over a group,
# 2. - a dense list of length the underlying reps of left translations on S OR
#    - a mapping on S
#    in either case, the second argument must define a left translation on S.
SEMIGROUPS.LeftTransToNormalRMSTupleNC := function(L, x)
  local S, I, G, one, group_func, trans, t, s, i;

  S          := UnderlyingSemigroup(L);
  I          := Rows(S);
  G          := UnderlyingSemigroup(S);
  one        := One(G);
  group_func := [];
  trans      := [];

  if IsDenseList(x) and
      Length(x) = Length(UnderlyingRepresentatives(LeftTranslations(S))) then
    for i in I do
      # This relies on UnderlyingRepresentatives not being interfered with
      t             := AsListCanonical(S)[x[i]];
      trans[i]      := t![1];
      group_func[i] := t![2];
    od;
  elif IsGeneralMapping(x) and Source(x) = Range(x) and Source(x) = S then
    for i in I do
      s             := RMSElement(S, i, one, 1);
      t             := s ^ x;
      trans[i]      := t![1];
      group_func[i] := t![2];
    od;
  fi;
  return [group_func, Transformation(trans)];
end;

SEMIGROUPS.RightTransToNormalRMSTupleNC := function(R, x)
  local S, J, G, one, group_func, trans, s, t, j;

  S          := UnderlyingSemigroup(R);
  J          := Columns(S);
  G          := UnderlyingSemigroup(S);
  one        := One(G);
  group_func := [];
  trans      := [];

  if IsDenseList(x) and
      Length(x) = Length(UnderlyingRepresentatives(RightTranslations(S))) then
    for j in J do
      # This relies on UnderlyingRepresentatives not being interfered with
      t             := AsListCanonical(S)[x[j]];
      trans[j]      := t![3];
      group_func[j] := t![2];
    od;
  elif IsGeneralMapping(x) and Source(x) = Range(x) and Source(x) = S then
    for j in J do
      s         := RMSElement(S, 1, one, j);
      t         := s ^ x;
      trans[j]  := t![3];
      group_func[j] := t![2];
    od;
  fi;
  return [group_func, Transformation(trans)];
end;

# TODO(later): This should go somewhere else
SEMIGROUPS.IsNormalRMSOverGroup := function(S)
  local mat, T, one;

  if not IsReesMatrixSemigroup(S) then
    return false;
  fi;

  T := UnderlyingSemigroup(S);

  if not IsGroupAsSemigroup(T) then
    return false;
  fi;

  mat := Matrix(S);
  one := MultiplicativeNeutralElement(T);
  return ForAll(mat[1], x -> x = one) and ForAll(mat, x -> x[1] = one);
end;

# Hash translations by their underlying transformations
SEMIGROUPS.HashFunctionForRMSTranslations :=
{x, data} -> ORB_HashFunctionForTransformations(x![2], data);

# Hash linked pairs as sum of hashes
SEMIGROUPS.HashFunctionForRMSBitranslations := function(x, data)
    return (SEMIGROUPS.HashFunctionForRMSTranslations(x![1], data)
      + SEMIGROUPS.HashFunctionForRMSTranslations(x![2], data)) mod data + 1;
end;

# Finds the transformations on the indices of a finite 0-simple semigroup
# which are candidates for translations, when combined with a function from
# the index sets to the group.
SEMIGROUPS.RZMSLinkedIndexFuncs := function(S)
  local mat, I, M, Li, bt, tau, sigma, out;

  mat := MatrixOfReesZeroMatrixSemigroup(S);
  I := [1 .. Length(mat[1])];
  M := [1 .. Length(mat)];

  Li := List(I, i -> PositionsProperty(mat, row -> row[i] <> 0));

  bt := function(k)
    local failed, j, mu;
    for j in Union([0], I) do
      tau[k] := j;
      sigma[k + 1] := [];
      failed := false;
      if j <> 0 then
        for mu in Li[j] do
          sigma[k + 1][mu] := Intersection(sigma[k][mu], Li[k]);
          if Length(sigma[k][mu]) = 0 then
            failed := true;
            break;
          fi;
        od;
        if not failed then
          for mu in M do
            if not IsBound(sigma[k + 1][mu]) then
              sigma[k + 1][mu] := Difference(sigma[k][mu], Li[k]);
            fi;
            if Length(sigma[k + 1][mu]) = 0 then
              failed := true;
              break;
            fi;
          od;
        fi;
      else
        for mu in M do
          sigma[k + 1][mu] := Difference(sigma[k][mu], Li[k]);
          if Length(sigma[k + 1][mu]) = 0 then
            failed := true;
            break;
          fi;
        od;
      fi;
      if failed then
        continue;
      fi;
      if k = Length(I) then
        Add(out, [ShallowCopy(tau), IteratorOfCartesianProduct(sigma[k + 1])]);
      else
        bt(k + 1);
      fi;
    od;
  end;

  tau := [];
  sigma := [List(M, x -> Union([0], M))];
  out := [];
  bt(1);
  return out;
end;

SEMIGROUPS.RZMSLinkingGraph := function(S, tau, sigma)
  local r, mat, D, i, mu;

  r := Size(Rows(S));
  mat := MatrixOfReesZeroMatrixSemigroup(S);
  D := NullDigraph(IsMutableDigraph, Length(Rows(S)) + Length(Columns(S)));

  for i in Rows(S) do
    if tau[i] <> 0 then
      for mu in Columns(S) do
        if sigma[mu] <> 0 then
          if mat[mu][tau[i]] <> 0 then
            DigraphAddEdges(D, [[i, mu + r], [mu + r, i]]);
          fi;
        fi;
      od;
    fi;
  od;

  return D;
end;

SEMIGROUPS.RZMSGroupLinkingConditions := function(S, tau, sigma)
  local D, sccs, reps, r, rep, dive, mat, conditions, row_definitions,
  column_definitions, e, cc;

  D := SEMIGROUPS.RZMSLinkingGraph(S, tau, sigma);
  sccs := DigraphStronglyConnectedComponents(D);
  reps := [];

  r := Length(Rows(S));

  for cc in Filtered(sccs.comps, x -> Size(x) > 1) do
    rep := cc[1];
    if rep > r then
      rep := OutNeighboursOfVertex(D, rep)[1];
    fi;
    Add(reps, rep);
  od;

  dive := function(v, scc_rep)
    local y, z, defns, x, w;
    if v <= r then
      y := row_definitions[v];
    else
      y := column_definitions[v - r];
    fi;
    for w in OutNeighboursOfVertex(D, v) do
      if w <= r then
        z := w;
        defns := row_definitions;
        x := [mat[v - r][tau[w]] ^ -1 * y[1], y[2] * mat[sigma[v - r]][w]];
      else
        z := w - r;
        defns := column_definitions;
        x := [mat[z][tau[v]] * y[1], y[2] * mat[sigma[z]][v] ^ -1];
      fi;
      if IsBound(defns[z]) then
        Add(conditions[scc_rep], [defns[z], x]);
      else
        defns[z] := x;
        dive(w, scc_rep);
      fi;
    od;
  end;

  mat := MatrixOfReesZeroMatrixSemigroup(S);
  conditions := List([1 .. r], x -> []);
  row_definitions := [];
  column_definitions := [];
  e := One(UnderlyingSemigroup(S));

  for rep in reps do
    row_definitions[rep] := [e, e];
    dive(rep, rep);
  od;

  return rec(reps := reps,
             sccs := sccs,
             conditions := conditions,
             row_definitions := row_definitions,
             column_definitions := column_definitions);
end;

SEMIGROUPS.RZMSLinkedGroupFunctions := function(S, tau, sigma)
  local r, conds, conditions, allowed_vals, reps, vals, keep, sccs, comps,
  ids, row_definitions, column_definitions, out, phi, psi, rep, z, cond, g, tup,
  i, v;

  r := Length(Rows(S));

  conds := SEMIGROUPS.RZMSGroupLinkingConditions(S, tau, sigma);
  conditions := conds.conditions;
  allowed_vals := [];
  reps := conds.reps;
  for rep in reps do
    vals := AsList(UnderlyingSemigroup(S));
    for cond in conditions[rep] do
      keep := [];
      for g in vals do
        if cond[1][1] * g * cond[1][2] = cond[2][1] * g * cond[2][2] then
          Add(keep, g);
        fi;
      od;
      vals := keep;
      if Length(vals) = 0 then
        break;
      fi;
    od;
    Add(allowed_vals, vals);
  od;
  if Length(allowed_vals) <> Length(reps) or ForAny(allowed_vals, IsEmpty) then
    return [];
  fi;

  sccs := conds.sccs;
  comps := sccs.comps;
  ids := sccs.id;
  row_definitions := conds.row_definitions;
  column_definitions := conds.column_definitions;

  out := [];
  for tup in EnumeratorOfCartesianProduct(allowed_vals) do
    phi := [];
    psi := [];
    for i in [1 .. Size(reps)] do
      rep := reps[i];
      for v in comps[ids[rep]] do
        if v <= r then
          phi[v] := row_definitions[v][1] * tup[i] * row_definitions[v][2];
        else
          z := v - r;
          psi[z] := column_definitions[z][1] *
                    tup[i] *
                    column_definitions[z][2];
        fi;
      od;
    od;
    Add(out, [phi, psi]);
  od;
  return out;
end;

SEMIGROUPS.BitranslationsRZMS := function(H, opt...)
  local S, out, idx_funcs, nr_only, nr, tau, sigma_it, sigma, gp_funcs,
  empty_bitrans, x, y;

  S         := UnderlyingSemigroup(H);
  out       := [];
  idx_funcs := SEMIGROUPS.RZMSLinkedIndexFuncs(S);
  nr_only   := opt = ["nr_only"];
  nr        := 0;

  for x in idx_funcs do
    tau := x[1];
    sigma_it := x[2];
    while not IsDoneIterator(sigma_it) do
      sigma := NextIterator(sigma_it);
      gp_funcs := SEMIGROUPS.RZMSLinkedGroupFunctions(S, tau, sigma);
      if nr_only then
        nr := nr + Length(gp_funcs);
      else
        for y in gp_funcs do
          Add(out, [[tau, y[1]], [sigma, y[2]]]);
        od;
      fi;
    od;
  od;

  if nr_only then
    return nr + 1;
  fi;

  empty_bitrans := [[List(Rows(S), x -> 0), []],
                    [List(Columns(S), x -> 0), []]];
  Add(out, empty_bitrans);

  Apply(out, x -> SEMIGROUPS.RZMSTupleToBitranslation(H, x));

  return out;
end;

SEMIGROUPS.NormalRMSInitialisedLinkedFuncs := function(S, G, mat, mat_inv_rows,
                                                       c, d_inv, x, y)
  local I, M, tau, sigma, g_pos, bt, out, mu;

  I           := Rows(S);
  M           := Columns(S);
  tau         := [x];
  sigma       := List(I, i -> List(M, mu -> ShallowCopy(M)));
  sigma[1][1] := [y];

  for mu in [2 .. Length(M)] do
    g_pos := PositionCanonical(G, d_inv[mu] * mat[mu][x] * c[1]);
    sigma[1][mu] := mat_inv_rows[1][g_pos];
    if IsEmpty(sigma[1][mu]) then
      return [];
    fi;
  od;

  bt := function(k)
    local g_pos, consistent, j, mu, tup;
    if k = Length(I) + 1 then
      for tup in EnumeratorOfCartesianProduct(sigma[k - 1]) do
        Add(out, [ShallowCopy(tau), ShallowCopy(tup)]);
      od;
      return;
    fi;
    for j in I do
      consistent := true;
      tau[k] := j;
      for mu in M do
        g_pos := PositionCanonical(G, d_inv[mu] * mat[mu][j] * c[k]);
        sigma[k][mu] := Intersection(sigma[k - 1][mu],
                                     mat_inv_rows[k][g_pos]);
        if IsEmpty(sigma[k][mu]) then
          consistent := false;
          break;
        fi;
      od;
      if consistent then
        bt(k + 1);
      fi;
    od;
  end;

  out := [];
  bt(2);
  return out;
end;

SEMIGROUPS.NormalRMSLinkedTriples := function(S, opt...)
  local I, M, iso, inv, G, mat, nr_only, inv_rows, out, b, d_inv, c,
  linked_funcs, i, mu, a, x, y, func_pair;

  I := Rows(S);
  M := Columns(S);

  iso := IsomorphismPermGroup(UnderlyingSemigroup(S));
  inv := InverseGeneralMapping(iso);
  G := Semigroup(List(Generators(Range(iso)), AsTransformation));

  mat := StructuralCopy(MatrixOfReesMatrixSemigroup(S));
  mat := List(mat, row -> List(row, x -> AsTransformation(x ^ iso)));

  nr_only := opt = ["nr_only"];

  inv_rows := List(I, x -> List(G, y -> []));
  for i in I do
    for mu in M do
      Add(inv_rows[i][PositionCanonical(G, mat[mu][i])], mu);
    od;
  od;

  out := [];
  if nr_only then
    out := 0;
  fi;

  for a in G do
    b := AsPermutation(a) ^ inv;
    for x in I do
      d_inv := List(M, mu -> (mat[mu][x] * a) ^ -1);
      for y in M do
        c := List(I, i -> a * mat[y][i]);
        linked_funcs := SEMIGROUPS.NormalRMSInitialisedLinkedFuncs(S,
                                                                   G,
                                                                   mat,
                                                                   inv_rows,
                                                                   c,
                                                                   d_inv,
                                                                   x,
                                                                   y);
        if nr_only then
          out := out + Length(linked_funcs);
        else
          for func_pair in linked_funcs do
            Add(out, Concatenation([b], func_pair));
          od;
        fi;
      od;
    od;
  od;
  return out;
end;

SEMIGROUPS.BitranslationsNormalRMS := function(H, opt...)
  local S, out, nr_only, triple;

  S := UnderlyingSemigroup(H);

  H       := TranslationalHull(S);
  out     := [];
  nr_only := opt = ["nr_only"];

  if nr_only then
    return SEMIGROUPS.NormalRMSLinkedTriples(S, opt[1]);
  fi;

  for triple in SEMIGROUPS.NormalRMSLinkedTriples(S) do
    triple := Concatenation([triple[1]],
                            List(triple{[2, 3]}, Transformation));
    Add(out, _BitranslationOfNormalRMSByTripleNC(H, triple));
  od;
  return out;
end;

SEMIGROUPS.FamOfRMSLeftTranslationsByTriple := function()
  local fam, type;

  fam       := NewFamily("LeftTranslationsSemigroupElementsFamily",
                          _IsLeftTranslationOfNormalRMS);
  type      := NewType(fam, _IsLeftTranslationOfNormalRMS);
  fam!.type := type;
  return fam;
end;

SEMIGROUPS.FamOfRMSRightTranslationsByTriple := function()
  local fam, type;

  fam       := NewFamily("RightTranslationsSemigroupElementsFamily",
                          _IsRightTranslationOfNormalRMS);
  type      := NewType(fam, _IsRightTranslationOfNormalRMS);
  fam!.type := type;
  return fam;
end;

SEMIGROUPS.FamOfRMSBitranslationsByTriple := function()
  local fam, type;

  fam       := NewFamily("BitranslationsSemigroupElementsFamily",
                          _IsBitranslationOfNormalRMS);
  type      := NewType(fam, _IsBitranslationOfNormalRMS);
  fam!.type := type;
  return fam;
end;

#############################################################################
# 2. Methods for (zero) simple semigroups
#############################################################################

# The generators are generators of a partial transformation monoid to act on the
# index sets, together with functions to the generators of the group.
InstallMethod(GeneratorsOfSemigroup,
"for the semigroup of left/right translations of a finite 0-simple semigroup",
[IsTranslationsSemigroup and IsWholeFamily],
function(T)
  local S, iso, inv, rms, zero, left_trans, n, gens, G, group_gens, f, fa, t, a;

  S := UnderlyingSemigroup(T);
  if not (IsZeroSimpleSemigroup(S) and IsFinite(S)) then
    TryNextMethod();
  fi;

  iso        := IsomorphismReesZeroMatrixSemigroup(S);
  inv        := InverseGeneralMapping(iso);
  rms        := Range(iso);
  zero       := MultiplicativeZero(rms);
  left_trans := IsLeftTranslationsSemigroup(T);

  if left_trans then
    n := Length(Rows(rms));
  else
    n := Length(Columns(rms));
  fi;

  gens       := [];
  G          := UnderlyingSemigroup(rms);
  group_gens := GeneratorsOfGroup(G);

  for t in GeneratorsOfSemigroup(PartialTransformationMonoid(n)) do
    if left_trans then
      f := function(x)
        if (x = zero or x[1] ^ t = n + 1) then
          return zero;
        fi;
        return ReesMatrixSemigroupElement(rms, x[1] ^ t,
            x[2], x[3]);
      end;
      Add(gens, LeftTranslationNC(T, CompositionMapping(inv,
                                        MappingByFunction(rms, rms, f),
                                                        iso)));
    else
      f := function(x)
        if (x = zero or x[3] ^ t = n + 1) then
          return zero;
        fi;
        return ReesMatrixSemigroupElement(rms, x[1],
          x[2], x[3] ^ t);
      end;
      Add(gens, RightTranslationNC(T, CompositionMapping(inv,
                                          MappingByFunction(rms, rms, f),
                                                         iso)));
    fi;
  od;

  for a in group_gens do
    fa := function(x)
      if x = 1 then
        return a;
      fi;
      return MultiplicativeNeutralElement(G);
    end;
    if left_trans then
      f := function(x)
        if x = zero then
          return zero;
        fi;
        return ReesMatrixSemigroupElement(rms, x[1],
            fa(x[1]) * x[2], x[3]);
      end;
      Add(gens, LeftTranslationNC(T, CompositionMapping(inv,
                                        MappingByFunction(rms, rms, f),
                                                        iso)));
    else
      f := function(x)
        if x = zero then
          return zero;
        fi;
        return ReesMatrixSemigroupElement(rms, x[1],
          x[2] * fa(x[3]), x[3]);
      end;
      Add(gens, RightTranslationNC(T, CompositionMapping(
        inv, MappingByFunction(rms, rms, f), iso)));
    fi;
  od;
  return gens;
end);

# The generators are generators of a full transformation monoid to act on the
# index sets, together with functions to the generators of the group.
InstallMethod(GeneratorsOfSemigroup,
"for the semigroup of left/right translations of a finite simple semigroup",
[IsTranslationsSemigroup and IsWholeFamily],
function(T)
  local S, iso, inv, rms, L, n, gens, G, group_gens, IsNRMS, idgroup_func, f,
  fa, t, a;

  S := UnderlyingSemigroup(T);
  if not (IsSimpleSemigroup(S) and IsFinite(S)) then
    TryNextMethod();
  fi;

  iso  := IsomorphismReesMatrixSemigroup(S);
  inv  := InverseGeneralMapping(iso);
  rms  := Range(iso);
  L    := IsLeftTranslationsSemigroup(T);

  if L then
    n := Length(Rows(rms));
  else
    n := Length(Columns(rms));
  fi;
  gens      := [];
  G         := UnderlyingSemigroup(rms);
  group_gens := GeneratorsOfGroup(G);

  IsNRMS := SEMIGROUPS.IsNormalRMSOverGroup(S);
  if IsNRMS then
    idgroup_func := List([1 .. n], i -> MultiplicativeNeutralElement(G));
  fi;

  for t in GeneratorsOfSemigroup(FullTransformationMonoid(n)) do
    if L then
      if IsNRMS then
        Add(gens, LeftTranslationNC(T, idgroup_func, t));
      else
        f := function(x)
          return ReesMatrixSemigroupElement(rms, x[1] ^ t,
                                            x[2], x[3]);
        end;
        Add(gens, LeftTranslationNC(T, CompositionMapping(inv,
                                          MappingByFunction(rms, rms, f),
                                                          iso)));
      fi;
    else
      if IsNRMS then
        Add(gens, RightTranslationNC(T, idgroup_func, t));
      else
        f := function(x)
          return ReesMatrixSemigroupElement(rms, x[1],
            x[2], x[3] ^ t);
        end;
        Add(gens, RightTranslationNC(T,
                                     CompositionMapping(inv,
                                          MappingByFunction(rms, rms, f),
                                                        iso)));
      fi;
    fi;
  od;

  for a in group_gens do
    fa := function(x)
      if x = 1 then
        return a;
      fi;
      return MultiplicativeNeutralElement(G);
    end;
    if L then
      if IsNRMS then
        Add(gens, LeftTranslationNC(T,
                                    List([1 .. n], fa),
                                    IdentityTransformation));
      else
        f := function(x)
          return ReesMatrixSemigroupElement(rms, x[1],
              fa(x[1]) * x[2], x[3]);
        end;
        Add(gens, LeftTranslationNC(T, CompositionMapping(inv,
                                          MappingByFunction(rms, rms, f),
                                                          iso)));
      fi;
    else
      if IsNRMS then
        Add(gens, RightTranslationNC(T,
                                     List([1 .. n], fa),
                                     IdentityTransformation));
      else
        f := function(x)
          return ReesMatrixSemigroupElement(rms, x[1],
            x[2] * fa(x[3]), x[3]);
        end;
        Add(gens, RightTranslationNC(T,
                                     CompositionMapping(inv,
                                          MappingByFunction(rms, rms, f),
                                                        iso)));
      fi;
    fi;
  od;
  return gens;
end);

InstallMethod(Size,
"for the semigroup of translations of a completely 0-simple semigroup",
[IsTranslationsSemigroup and IsWholeFamily],
1,  # To beat the method for arbitrary underlying semigroups which calls AsList
function(T)
  local S, G, rms, n;
  S := UnderlyingSemigroup(T);
  if not (IsZeroSimpleSemigroup(S) and IsFinite(S)) then
    TryNextMethod();
  fi;
  rms := Range(IsomorphismReesZeroMatrixSemigroup(S));
  G   := UnderlyingSemigroup(rms);
  if IsLeftTranslationsSemigroup(T) then
    n := Length(Rows(rms));
  else
    n := Length(Columns(rms));
  fi;
  return (n * Size(G) + 1) ^ n;
end);

InstallMethod(Size,
"for the semigroup of translations of a completely simple semigroup",
[IsTranslationsSemigroup and IsWholeFamily],
1,  # To beat the method for arbitrary underlying semigroups which calls AsList
function(T)
  local S, G, rms, n;
  S := UnderlyingSemigroup(T);
  if not (IsSimpleSemigroup(S) and IsFinite(S)) then
    TryNextMethod();
  fi;
  rms := Range(IsomorphismReesMatrixSemigroup(S));
  G   := UnderlyingSemigroup(rms);
  if IsLeftTranslationsSemigroup(T) then
    n := Length(Rows(rms));
  else
    n := Length(Columns(rms));
  fi;
  return n ^ n * Size(G) ^ n;
end);

# Create a left translation of an IxJ normalised RMS over a group G.
# L should be a left translations semigroup
# group_func should be a function (represented as a list) from I to G
# t should be a transformation of I
InstallOtherMethod(LeftTranslation,
"for a semigroup of left translations, a dense list, and a transformation",
[_IsLeftTranslationOfNormalRMSSemigroup, IsDenseList, IsTransformation],
function(L, group_func, t)
  local S, G;

  S := UnderlyingSemigroup(L);
  G := UnderlyingSemigroup(S);

  if not (IsList(group_func) and
          ForAll(group_func, x -> x in G) and
          Size(group_func) = Size(Matrix(S)[1])) then
    ErrorNoReturn("the second argument must be a list of group elements ",
                  "of length equal to the number of rows of the underlying ",
                  "semigroup of the first argument");
  fi;

  if not (IsTransformation(t) and
          DegreeOfTransformation(t) <= Size(Matrix(S)[1])) then
    ErrorNoReturn("the third argument must be a transformation on ",
                  "the number of rows of the underlying semigroup of the ",
                  "first argument");
  fi;

  return LeftTranslationNC(L, group_func, t);
end);

InstallGlobalFunction(_LeftTranslationOfNormalRMSNC,
function(L, x, opt...)
  local tup, group_func, t;

  if IsEmpty(opt) then
    tup         := SEMIGROUPS.LeftTransToNormalRMSTupleNC(L, x);
    group_func  := tup[1];
    t           := tup[2];
  else
    group_func := x;
    t          := opt[1];
  fi;

  return Objectify(TypeLeftTranslationsSemigroupElements(L),
                   [group_func, t]);
end);

# Create a right translation of an IxJ normalised RMS over a group G.
# R should be a right translations semigroup
# group_func should be a function (represented as a list) from J to G
# t should be a transformation of J
InstallOtherMethod(RightTranslation,
"for a semigroup of right translations, a dense list, and a transformation",
[_IsRightTranslationOfNormalRMSSemigroup, IsDenseList, IsTransformation],
function(R, group_func, t)
  local S, G;

  S := UnderlyingSemigroup(R);
  G := UnderlyingSemigroup(S);

  if not (IsList(group_func) and
          ForAll(group_func, x -> x in G) and
          Size(group_func) = Size(MatrixOfReesMatrixSemigroup(S))) then
    ErrorNoReturn("the second argument must be a list of group elements ",
                  "of length equal to the number of rows of the underlying ",
                  "semigroup of the first argument");
  elif not (IsTransformation(t) and
          DegreeOfTransformation(t) <= Size(Matrix(S))) then
    ErrorNoReturn("the third argument must be a transformation on ",
                  "the number of columns of the underlying semigroup of the ",
                  "first argument");
  fi;

  return _RightTranslationOfNormalRMSNC(R, group_func, t);
end);

InstallGlobalFunction(_RightTranslationOfNormalRMSNC,
function(R, x, opt...)
  local tup, group_func, t;

  if IsEmpty(opt) then
    tup         := SEMIGROUPS.RightTransToNormalRMSTupleNC(R, x);
    group_func  := tup[1];
    t           := tup[2];
  else
    group_func := x;
    t          := opt[1];
  fi;

  return Objectify(TypeRightTranslationsSemigroupElements(R),
                   [group_func, t]);
end);

InstallOtherMethod(Bitranslation,
"for a bitranslation defined by a triple on a normal RMS",
[IsBitranslationsSemigroup, IsAssociativeElement, IsTransformation,
  IsTransformation],
function(H, g, chi, psi)
  local S, P, I, J, i, mu;

  S := UnderlyingSemigroup(H);

  if not SEMIGROUPS.IsNormalRMSOverGroup(S) then
    TryNextMethod();
  fi;

  P := Matrix(S);
  I := Rows(S);
  J := Columns(S);

  if not g in UnderlyingSemigroup(S) then
    ErrorNoReturn("the second argument must be an element of the group that ",
                  "the underlying semigroup of the first argument is defined ",
                  "over");
  elif LargestImageOfMovedPoint(chi) > Length(I) then
    ErrorNoReturn("the third argument must be a transformation on the rows of ",
                  "the underlying semigroup of the first argument");
  elif LargestImageOfMovedPoint(psi) > Length(J) then
    ErrorNoReturn("the fourth argument must be a transformation on the rows ",
                  "of the underlying semigroup of the first argument");
  fi;

  for i in I do
    for mu in J do
      if not P[mu][i ^ chi] * g * P[1 ^ psi][i]
              = P[mu][1 ^ chi] * g * P[mu ^ psi][i] then
        ErrorNoReturn("the arguments given do not define a bitranslation");
      fi;
    od;
  od;

  return _BitranslationOfNormalRMSByTripleNC(H, [g, chi, psi]);
end);

InstallGlobalFunction(_BitranslationOfNormalRMSByTripleNC,
function(H, triple)
  local S, P, I, M, left_group_func, right_group_func, l, r;

  S := UnderlyingSemigroup(H);
  P := Matrix(S);
  I := Rows(S);
  M := Columns(S);

  left_group_func  := List(I, i -> triple[1] * P[1 ^ triple[3]][i]);
  right_group_func := List(M, mu -> P[mu][1 ^ triple[2]] * triple[1]);

  l := LeftTranslationNC(LeftTranslations(S), left_group_func, triple[2]);
  r := RightTranslationNC(RightTranslations(S), right_group_func, triple[3]);

  return BitranslationNC(H, l, r);
end);

############################################################################
# 3. Technical Methods
############################################################################

InstallMethod(Representative,
"for a semigroup of left or right translations over a normalised RMS",
[_IsTranslationOfNormalRMSSemigroup and IsWholeFamily],
function(T)
  local e, G, S;

  S := UnderlyingSemigroup(T);
  G := UnderlyingSemigroup(S);
  e := MultiplicativeNeutralElement(G);

  if _IsLeftTranslationOfNormalRMSSemigroup(T) then
    return LeftTranslationNC(T,
                             List(Rows(S), x -> e),
                             IdentityTransformation);
  else
    return RightTranslationNC(T,
                              List(Columns(S), x -> e),
                              IdentityTransformation);
  fi;
end);

InstallMethod(\*, "for left translations of a normalised RMS",
IsIdenticalObj,
[_IsLeftTranslationOfNormalRMS, _IsLeftTranslationOfNormalRMS],
function(x, y)
  return Objectify(FamilyObj(x)!.type,
                   [List([1 .. Size(x![1])], i -> x![1][i ^ y![2]] * y![1][i]),
                    y![2] * x![2]]);
end);

InstallMethod(\=, "for left translations of a normalised RMS",
IsIdenticalObj,
[_IsLeftTranslationOfNormalRMS, _IsLeftTranslationOfNormalRMS],
{x, y} -> x![1] = y![1] and x![2] = y![2]);

InstallMethod(\<, "for left translations of a normalised RMS",
IsIdenticalObj,
[_IsLeftTranslationOfNormalRMS, _IsLeftTranslationOfNormalRMS],
{x, y} -> x![2] < y![2] or (x![2] = y![2] and x![1] < y![1]));

InstallMethod(\*, "for right translations of a normalised RMS",
IsIdenticalObj,
[_IsRightTranslationOfNormalRMS, _IsRightTranslationOfNormalRMS],
function(x, y)
  return Objectify(FamilyObj(x)!.type,
                   [List([1 .. Size(x![1])], j -> x![1][j] * y![1][j ^ x![2]]),
                    x![2] * y![2]]);
end);

InstallMethod(\=, "for right translations of a normalised RMS",
IsIdenticalObj,
[_IsRightTranslationOfNormalRMS, _IsRightTranslationOfNormalRMS],
{x, y} -> x![1] = y![1] and x![2] = y![2]);

InstallMethod(\<, "for right translations of a normalised RMS",
IsIdenticalObj,
[_IsRightTranslationOfNormalRMS, _IsRightTranslationOfNormalRMS],
{x, y} -> x![2] < y![2] or (x![2] = y![2] and x![1] < y![1]));

InstallMethod(\*, "for bitranslations of a normalised RMS",
IsIdenticalObj,
[_IsBitranslationOfNormalRMS, _IsBitranslationOfNormalRMS],
{x, y} -> Objectify(FamilyObj(x)!.type, [x![1] * y![1], x![2] * y![2]]));

InstallMethod(\=, "for bitranslations of a normalised RMS",
IsIdenticalObj,
[_IsBitranslationOfNormalRMS, _IsBitranslationOfNormalRMS],
{x, y} -> x![1] = y![1] and x![2] = y![2]);

InstallMethod(\<, "for bitranslations of a normalised RMS",
IsIdenticalObj,
[_IsBitranslationOfNormalRMS, _IsBitranslationOfNormalRMS],
{x, y} -> x![1] < y![1] or (x![1] = y![1] and x![2] < y![2]));

InstallMethod(\^, "for a semigroup element and a translation",
[IsReesMatrixSemigroupElement, _IsTranslationOfNormalRMS],
function(x, t)
  if _IsLeftTranslationOfNormalRMS(t) then
    return RMSElementNC(ReesMatrixSemigroupOfFamily(FamilyObj(x)),
                        x![1] ^ t![2],
                        t![1][x![1]] * x![2],
                        x![3]);
  else
    return RMSElementNC(ReesMatrixSemigroupOfFamily(FamilyObj(x)),
                        x![1],
                        x![2] * t![1][x![3]],
                        x![3] ^ t![2]);
  fi;
end);

InstallMethod(ChooseHashFunction, "for a left or right translation and int",
[_IsTranslationOfNormalRMS, IsInt],
function(_, hashlen)
  return rec(func := SEMIGROUPS.HashFunctionForRMSTranslations,
             data := hashlen);
end);

InstallMethod(ChooseHashFunction, "for a bitranslation and int",
[_IsBitranslationOfNormalRMS, IsInt],
function(_, hashlen)
  return rec(func := SEMIGROUPS.HashFunctionForRMSBitranslations,
             data := hashlen);
end);
