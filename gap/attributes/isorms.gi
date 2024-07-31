############################################################################
##
##  attributes/isorms.gi
##  Copyright (C) 2014-2022                              James D. Mitchell
##
##  Licensing information can be found in the README file of this package.
##
#############################################################################
##

#############################################################################
## This file contains functions for isomorphisms and automorphisms of Rees
## matrix and 0-matrix semigroup. The algorithm used in this file is described
## in:
##
##   J. Araújo, P. von Bünau, J. D. Mitchell, and M. Neunhoeffer,
##   ‘Computing automorphisms of semigroups’,
##   J. Symbolic Comput. 45 (2010) 373-392;
##   https://dx.doi.org/10.1016/j.jsc.2009.10.001.
##
## This file is organized as follows:
##
##   1. Internal functions for the avoidance of duplicate code.
##
##   2. Automorphism group functions (the main functions in this file)
##
##   3. Methods for automorphism group of RMS and RZMS (ViewObj,
##      IdentityMapping etc)
##
##   4. Isomorphisms
##
##   5. RMS/RZMSIsoByTriple (equality, <, ImagesRepresentative)
##
#############################################################################

#############################################################################
# 1. Internal functions
#############################################################################

# Find the stabiliser of the matrix of a Rees (0-)matrix semigroup under the
# action of the automorphism group of the R(Z)MSGraph via rearranging rows and
# columns

SEMIGROUPS.StabOfRMSMatrix := function(G, R)
  local OnMatrix, H, m, n;

  m := Length(Matrix(R)[1]);
  n := Length(Matrix(R));

  OnMatrix := function(mat, x)
    local rows;
    mat := StructuralCopy(mat);
    rows := Permutation(x, [1 .. n], function(i, p)
                                       return (i + m) ^ p - m;
                                     end);

    return List(Permuted(mat, rows), y -> Permuted(y, x));
  end;
  H := Stabilizer(G, Matrix(R), OnMatrix);
  Info(InfoSemigroups, 2, "the size of stabilizer of the matrix is ", Size(H));
  return H;
end;

# Find the pointwise stabiliser of the entries in the matrix of a Rees
# (0-)matrix semigroup under the action of the automorphism group of the
# underlying group.

SEMIGROUPS.StabOfRMSEntries := function(G, R)
  local H, entries, i;
  H := G;
  entries := MatrixEntries(R);
  i := PositionProperty(entries, x -> x <> 0 and x <> ());

  while not IsTrivial(H) and i <= Length(entries) do
    H := Stabilizer(H, entries[i], OnPoints);
    i := i + 1;
  od;

  Info(InfoSemigroups,
       2,
       "the size of the stabilizer of the matrix entries is ",
       Size(H));
  return H;
end;

# Theorem 3.4.1 in Howie's book, Fundamentals of Semigroup Theory. This
# function finds the values of the elements u_i and v_lambda of the underlying
# group of R2 for the choice of l, and g, by propagating the initial value x
# from u_1 to v_1, ..., v_n, and then from v_1 to u_2, ..., u_m.  It then
# checks that the equation in Theorem 3.4.1 holds for the values of u and v
# defined.

SEMIGROUPS.RMSInducedFunction := function(R1, R2, l, g, x)
  local mat1, mat2, m, n, out, i, j;

  mat1 := Matrix(R1);
  mat2 := Matrix(R2);
  m := Length(mat1[1]);
  n := Length(mat1);
  out := EmptyPlist(m + n);
  out[1] := x;

  for i in [m + 1 .. m + n] do
    # This is the inverse of v_lambda from Howie's book
    out[i] := mat2[i ^ l - m][1 ^ l] * x * ((mat1[i - m][1] ^ g) ^ -1);
  od;

  for i in [2 .. m] do
    out[i] := mat2[(m + 1) ^ l - m][i ^ l] ^ -1 * out[m + 1]
              * (mat1[1][i] ^ g);
  od;

  for j in [m + 2 .. n + m] do
    for i in [2 .. m] do
      if mat1[j - m][i] ^ g
          <> out[j] ^ -1 * mat2[j ^ l - m][i ^ l] * out[i] then
        return fail;
      fi;
    od;
  od;

  return out;
end;

SEMIGROUPS.RZMSInducedFunction := function(R, l, g, x, component)
  local mat, m, n, adj, rep, out, Q, q, v;

  mat      := Matrix(R);
  m        := Length(mat[1]);
  n        := Length(mat);
  adj      := OutNeighbours(RZMSDigraph(R));
  rep      := component[1];
  out      := EmptyPlist(m + n);
  out[rep] := x;
  Q        := [rep];
  q        := 1;

  while q <= Length(Q) do
    rep := Q[q];
    q   := q + 1;
    if rep <= m then
      for v in adj[rep] do
        if not IsBound(out[v]) then
          Add(Q, v);
          out[v] := mat[v ^ l - m][rep ^ l] * out[rep] / mat[v - m][rep] ^ g;
        elif mat[v - m][rep] ^ g
             <> (out[v] ^ -1) * mat[v ^ l - m][rep ^ l] * out[rep] then
          return fail;
        fi;
      od;
    else
      for v in adj[rep] do
        if not IsBound(out[v]) then
          Add(Q, v);
          out[v] := mat[rep ^ l - m][v ^ l] ^ -1 * out[rep] ^ -1
                    * (mat[rep - m][v] ^ g);
        elif mat[rep - m][v] ^ g
            <> out[rep] ^ -1 * mat[rep ^ l - m][v ^ l] * out[v] then
          return fail;
        fi;
      od;
    fi;
  od;
  return out;
end;

# TODO(later) the next function should be combined with the previous one.

SEMIGROUPS.RZMStoRZMSInducedFunction := function(rms1, rms2, l, g, groupelts)
  local mat1, mat2, m, rmsgraph, components, reps, imagelist, edges,
  bicomps, sub, perm, defined, orb, j, Last, involved, verts, v, new, i, k;

  mat1 := Matrix(rms1);
  mat2 := Matrix(rms2);
  m := Length(mat1[1]);
  rmsgraph := RZMSDigraph(rms1);
  components := DigraphConnectedComponents(rmsgraph).comps;

  if Length(groupelts) <> Length(components) then
    ErrorNoReturn("the 5th argument (a list) must have length ",
                  Length(components), ", but found ", Length(groupelts));
  fi;

  reps := List(components, Minimum);
  imagelist := [];
  imagelist{reps} := groupelts;

  for i in [1 .. Length(components)] do
    if Length(components) = 1 then
      edges := DigraphEdges(rmsgraph);
      bicomps := DigraphBicomponents(rmsgraph);
    else
      sub := InducedSubdigraph(rmsgraph, components[i]);
      perm := MappingPermListList(DigraphVertexLabels(sub),
                                  DigraphVertices(sub));
      edges := OnTuplesTuples(DigraphEdges(sub), perm ^ -1);
      bicomps := OnTuplesTuples(DigraphBicomponents(sub), perm ^ -1);
    fi;

    defined := [];
    orb := [reps[i]];
    j := 0;

    repeat
      j := j + 1;
      Last := orb[j];
      involved := Filtered(edges, x -> x[1] = Last and not x in defined);
      if not involved = [] then

        verts := List(involved, x -> x[2]);
        Append(orb, Filtered(verts, x -> not x in orb));

        for k in [1 .. Length(verts)] do
          v := verts[k];

          if Last in bicomps[1] then
            new := mat2[v ^ l - m][Last ^ l]
                   * imagelist[Last] * (mat1[v - m][Last] ^ g) ^ -1;
          else
            new := (mat2[Last ^ l - m][v ^ l]) ^ -1
                   * imagelist[Last] * (mat1[Last - m][v] ^ g);
          fi;

          if not IsBound(imagelist[v]) then
            imagelist[v] := new;
          elif not imagelist[v] = new then
            return fail;
          fi;
          defined := Union(defined, [involved[k], Reversed(involved[k])]);
        od;
      fi;
    until defined = edges;
  od;
  return imagelist;
end;

#############################################################################
# 2. Automorphism group functions
#############################################################################

# don't hit F5 for local variables here, it crashes vim!!
InstallMethod(AutomorphismGroup, "for a Rees 0-matrix semigroup",
[IsReesZeroMatrixSubsemigroup],
function(R)
  local G, m, n, aut_graph, components, t, aut_group, stab_aut_graph,
        hom, stab_aut_group, i, V, A, gens1, gens2, U, T, tester,
        g, x, map, cart, RZMSInducedFunction;

  G := UnderlyingSemigroup(R);

  if not (IsReesZeroMatrixSemigroup(R) and IsPermGroup(G)
          and IsZeroSimpleSemigroup(R)) then
    TryNextMethod();  # There is no such method at present
  fi;

  m := Length(Rows(R));
  n := Length(Columns(R));

  # automorphism group of the graph . . .

  aut_graph := AutomorphismGroup(RZMSDigraph(R), [[1 .. m], [m + 1 .. n + m]]);

  Info(InfoSemigroups, 2, "the graph has ", Size(aut_graph), " automorphisms");

  # stabiliser of the matrix under rearranging rows and columns by elements
  # of the automorphism group of the graph
  if m * n < 1000 then
    stab_aut_graph := SEMIGROUPS.StabOfRMSMatrix(aut_graph, R);
  else
    stab_aut_graph := Group(());
  fi;

  # automorphism group of the underlying group
  aut_group := AutomorphismGroup(G);
  Info(InfoSemigroups,
       2,
       "the underlying group has ",
       Size(aut_group),
       " automorphisms");

  # pointwise stabiliser of the entries in the matrix of R under the
  # automorphism group of the group
  stab_aut_group := SEMIGROUPS.StabOfRMSEntries(aut_group, R);

  # The following mathematically unnecessary separation of cases is needed to
  # support the AutPGrp package, whose method for `AutomorphismGroup` for the
  # trivial group does not set `InnerAutomorphismsAutomorphismGroup` at
  # creation, and no method is installed to calculate it.

  # homomorphism from Aut(G) to a perm rep of Aut(G) / Inn(G)
  if IsTrivial(G) then
    hom := IsomorphismPermGroup(aut_group);
  else
    hom := NaturalHomomorphismByNormalSubgroupNC(aut_group,
             InnerAutomorphismsAutomorphismGroup(aut_group));
    hom := CompositionMapping(IsomorphismPermGroup(ImagesSource(hom)), hom);
  fi;

  # V is isomorphic to Aut(Gamma) x (Aut(G) / Inn(G))
  # U is a subgroup of V contained in the subgroup we are looking for.
  V := DirectProduct(aut_graph, Image(hom));

  if IsTrivial(stab_aut_graph) and IsTrivial(stab_aut_group) then
    U := Group(());
  else
    gens1 := GeneratorsOfGroup(stab_aut_graph);
    gens2 := GeneratorsOfGroup(Image(hom, stab_aut_group));
    U := Group(Concatenation(Images(Embedding(V, 1), gens1),
                             Images(Embedding(V, 2), gens2)));
  fi;

  components := DigraphConnectedComponents(RZMSDigraph(R)).comps;
  t := Length(components);
  Info(InfoSemigroups, 2, "the graph has ", t, " connected components");

  T := RightTransversal(G, Centre(G));
  A := [];

  ##########################################################################
  # test whether for <x> in <V> there is a <map> such that
  # phi := [x ^ Projection(V, 1), x ^ Projection(V, 2) ^ hom ^ -1, map]
  # is a RZMSIsoByTriple, and add <phi> to <A> if it is!
  ##########################################################################

  RZMSInducedFunction := SEMIGROUPS.RZMSInducedFunction;

  tester := function(x)
    local y, found, g, i, tmp, map;
    y := PreImagesRepresentative(hom, x ^ Projection(V, 2));
    x := x ^ Projection(V, 1);
    tmp := [];
    found := false;
    for g in T do
      map := RZMSInducedFunction(R, x, y, g, components[1]);
      if map <> fail then
        tmp := tmp + map;
        found := true;
        break;
      fi;
    od;
    i := 1;
    while found and i < t do
      i := i + 1;
      found := false;
      for g in G do
        map := RZMSInducedFunction(R, x, y, g, components[i]);
        if map <> fail then
          tmp := tmp + map;
          found := true;
          break;
        fi;
      od;
    od;

    if found then
      AddSet(A, RZMSIsoByTripleNC(R, R, [x, y, tmp]));
    fi;
    return found;
  end;

  ##########################################################################

  if U <> V then  # some search required
    Info(InfoSemigroups, 2, "backtracking in the direct product of size ",
         Size(V), " . . . ");
    # This appears to do nothing, but the subgroup is computed when we call
    # Size, and the resulting isomorphisms-by-triple are stored in A by the
    # function tester
    U := BacktrackSearchStabilizerChainSubgroup(StabilizerChain(V),
                                                tester,
                                                ReturnTrue);
    Info(InfoSemigroups, 2, "found subgroup of size ", Size(U));
  else
    # U = V
    # This appears to do nothing, but the the resulting isomorphisms-by-triple
    # are stored in A by the function tester
    Perform(GeneratorsOfGroup(V), tester);
  fi;

  cart := [[]];
  for g in T do
    map := RZMSInducedFunction(R,
                               One(aut_graph),
                               One(aut_group),
                               g,
                               components[1]);
    if map <> fail then
      Add(cart[1], map);
    fi;
  od;

  for i in [2 .. t] do
    cart[i] := [];
    for g in G do
      map := RZMSInducedFunction(R,
                                 One(aut_graph),
                                 One(aut_group),
                                 g,
                                 components[i]);
      if map <> fail then
        Add(cart[i], map);
      fi;
    od;
  od;

  # put B together
  for map in EnumeratorOfCartesianProduct(cart) do
    x := RZMSIsoByTripleNC(R, R, [One(aut_graph), One(aut_group), Sum(map)]);
    AddSet(A, x);
  od;

  A := Group(A);
  SetIsAutomorphismGroupOfRMSOrRZMS(A, true);
  SetIsFinite(A, true);

  return A;
end);

# don't hit F5 for local variables here, it crashes vim!!
InstallMethod(AutomorphismGroup, "for a Rees matrix semigroup",
[IsReesMatrixSemigroup and IsWholeFamily],
function(R)
  local G, m, n, aut_graph, aut_group, stab_aut_graph,
        hom, stab_aut_group, V, A, gens1, gens2, U, T, tester,
        g, map, gens, RMSInducedFunction;

  G := UnderlyingSemigroup(R);
  if not (IsReesMatrixSemigroup(R) and IsPermGroup(G)
          and IsSimpleSemigroup(R)) then
    TryNextMethod();  # TODO(never) write such a method
  fi;

  m := Length(Rows(R));
  n := Length(Columns(R));

  # this is easy since the graph is complete bipartite

  if n = 1 and m = 1 then
    gens := GeneratorsOfGroup(AutomorphismGroup(G));
    if IsEmpty(gens) then
      gens := [IdentityMapping(G)];
    fi;
    A := Group(List(gens, x -> RMSIsoByTripleNC(R, R,
                                                [(), x, [One(G), One(G)]])));
    SetIsAutomorphismGroupOfRMSOrRZMS(A, true);
    SetIsFinite(A, true);
    return A;
  elif n = 2 and m = 1 then
    aut_graph := Group((2, 3));
    SetSize(aut_graph, 2);
  elif n > 2 and m = 1 then
    aut_graph := Group((2, 3),
                       PermList(Concatenation([1], [3 .. n + m], [2])));
    SetSize(aut_graph, Factorial(n));
  else
    aut_graph := DirectProduct(SymmetricGroup(m), SymmetricGroup(n));
  fi;

  Info(InfoSemigroups, 2, "the graph has ", Size(aut_graph), " automorphisms");

  # stabiliser of the matrix under rearranging rows and columns by elements
  # of the automorphism group of the graph
  if m * n < 1000 then
    stab_aut_graph := SEMIGROUPS.StabOfRMSMatrix(aut_graph, R);
  else
    stab_aut_graph := Group(());
  fi;

  # automorphism group of the underlying group
  aut_group := AutomorphismGroup(G);
  Info(InfoSemigroups,
       2,
       StringFormatted("there are {} group automorphisms", Size(aut_group)));

  # pointwise stabiliser of the entries in the matrix of R under the
  # automorphism group of the group
  stab_aut_group := SEMIGROUPS.StabOfRMSEntries(aut_group, R);

  # The following mathematically unnecessary separation of cases is needed to
  # support the AutPGrp package, whose method for `AutomorphismGroup` for the
  # trivial group does not set `InnerAutomorphismsAutomorphismGroup` at
  # creation, and no method is installed to calculate it.

  # homomorphism from Aut(G) to a perm rep of Aut(G) / Inn(G)
  if IsTrivial(G) then
    hom := IsomorphismPermGroup(aut_group);
  else
    hom := NaturalHomomorphismByNormalSubgroupNC(aut_group,
             InnerAutomorphismsAutomorphismGroup(aut_group));
    hom := CompositionMapping(IsomorphismPermGroup(ImagesSource(hom)), hom);
  fi;

  # V is isomorphic to Aut(Gamma) x (Aut(G) / Inn(G))
  # U is a subgroup of V contained in the subgroup we are looking for.
  V := DirectProduct(aut_graph, Image(hom));

  if IsTrivial(stab_aut_graph) and IsTrivial(stab_aut_group) then
    U := Group(());
  else
    gens1 := GeneratorsOfGroup(stab_aut_graph);
    gens2 := GeneratorsOfGroup(Image(hom, stab_aut_group));
    U := Group(Concatenation(Images(Embedding(V, 1), gens1),
                             Images(Embedding(V, 2), gens2)));
  fi;

  T := RightTransversal(G, Centre(G));
  A := [];

  ##########################################################################
  # test whether for <x> in <V> there is a <map> such that
  # phi := [x ^ Projection(V, 1), x ^ Projection(V, 2) ^ hom ^ -1, map]
  # is a RMSIsoByTriple, and add <phi> to <A> if it is!
  ##########################################################################

  RMSInducedFunction := SEMIGROUPS.RMSInducedFunction;

  tester := function(x)
    local y, map, g;
    y := PreImagesRepresentative(hom, x ^ Projection(V, 2));
    x := x ^ Projection(V, 1);
    for g in T do
      map := RMSInducedFunction(R, R, x, y, g);
      if map <> fail then
        AddSet(A, RMSIsoByTripleNC(R, R, [x, y, map]));
        return true;
      fi;
    od;
    return false;
  end;

  ##########################################################################

  if U <> V then
    Info(InfoSemigroups, 2, "backtracking in the direct product of size ",
         Size(V), " . . . ");
    # See the comments in the AutomorphismGroup(Rees 0-matrix semigroup) method
    U := BacktrackSearchStabilizerChainSubgroup(StabilizerChain(V),
                                                tester,
                                                ReturnTrue);
    Info(InfoSemigroups, 2, "found subgroup of size ", Size(U));
  else  # U = V
    # See the comments in the AutomorphismGroup(Rees 0-matrix semigroup) method
    Perform(GeneratorsOfGroup(V), tester);
  fi;

  for g in T do
    map := RMSInducedFunction(R,
                              R,
                              One(aut_graph),
                              One(aut_group),
                              g);
    if map <> fail then
      AddSet(A, RMSIsoByTripleNC(R, R, [One(aut_graph), One(aut_group), map]));
    fi;
  od;

  A := Group(A);
  SetIsAutomorphismGroupOfRMSOrRZMS(A, true);
  SetIsFinite(A, true);

  return A;
end);

#############################################################################
# 3. Methods for automorphism groups
#############################################################################

InstallMethod(ViewObj,
"for the automorphism group of a Rees (0-)matrix semigroup",
[IsAutomorphismGroupOfRMSOrRZMS],
function(G)
  Print("<automorphism group of ");
  ViewObj(Source(G.1));
  Print(" with ");
  Print(Pluralize(Length(GeneratorsOfGroup(G)), "generator"));
  Print(">");
end);

# InstallMethod(ViewString,
# "for the automorphism group of a Rees (0-)matrix semigroup",
# [IsAutomorphismGroupOfRMSOrRZMS],
# function(G)
#   local plural;
#
#   plural := "";
#   if Length(GeneratorsOfGroup(G)) > 1 then
#     plural := "s";
#   fi;
#
#   return StringFormatted(
#     "<automorphism group of {!v} with {!v} generator{}>",
#     Source(G.1),
#     Length(GeneratorsOfGroup(G)),
#     plural);
# end);

InstallMethod(IsomorphismPermGroup,
"for the automorphism group of a Rees (0-)matrix semigroup",
[IsAutomorphismGroupOfRMSOrRZMS],
function(G)
  local R, H, iso, x;

  R := Source(Representative(G));  # the Rees (0-)matrix semigroup
  H := [];
  for x in GeneratorsOfGroup(G) do
    Add(H, Permutation(x, R, OnPoints));
  od;
  H := Group(H);

  iso := GroupHomomorphismByImagesNC(G,
                                     H,
                                     GeneratorsOfGroup(G),
                                     GeneratorsOfGroup(H));
  SetInverseGeneralMapping(iso,
                           GroupHomomorphismByImagesNC(H,
                                                       G,
                                                       GeneratorsOfGroup(H),
                                                       GeneratorsOfGroup(G)));
  SetIsBijective(iso, true);
  SetNiceMonomorphism(G, iso);
  SetIsHandledByNiceMonomorphism(G, true);
  UseIsomorphismRelation(G, H);
  return iso;
end);

InstallMethod(IdentityMapping, "for a Rees matrix semigroup",
[IsReesMatrixSemigroup and IsWholeFamily],
function(R)
  local G;
  G := UnderlyingSemigroup(R);
  return RMSIsoByTripleNC(R, R,
                          [(),
                           IdentityMapping(G),
                           List([1 .. Length(Columns(R)) + Length(Rows(R))],
                                x -> One(G))]);
end);

InstallMethod(IdentityMapping, "for a Rees 0-matrix semigroup",
[IsReesZeroMatrixSemigroup and IsWholeFamily],
function(R)
  local G, tup;
  G := UnderlyingSemigroup(R);
  tup := List([1 .. Length(Columns(R)) + Length(Rows(R))], x -> One(G));
  return RZMSIsoByTripleNC(R, R, [(), IdentityMapping(G), tup]);
end);

#############################################################################
# 4. Isomorphisms
#############################################################################

InstallMethod(IsomorphismSemigroups,
"for finite whole family Rees matrix semigroups",
[IsReesMatrixSemigroup and IsWholeFamily and IsFinite,
 IsReesMatrixSemigroup and IsWholeFamily and IsFinite],
(RankFilter(IsSimpleSemigroup and IsFinite) - RankFilter(IsReesMatrixSemigroup
and IsWholeFamily and IsFinite)) + 10,  # to beat IsSimpleSemigroup and IsFinite
function(S, T)
  local G, H, mat, m, n, f, isograph, isogroup, RMSInducedFunction, map, l, g,
        tup;

  G := UnderlyingSemigroup(S);
  H := UnderlyingSemigroup(T);

  if not (IsGroupAsSemigroup(G) and IsGroupAsSemigroup(H)) then
    TryNextMethod();
  elif Size(S) <> Size(T)
      or Length(Columns(S)) <> Length(Columns(T))
      or Length(Rows(T)) <> Length(Rows(T)) then
    return fail;
  elif not (IsPermGroup(G) and IsPermGroup(H)) then
    TryNextMethod();
  fi;

  mat := Matrix(S);
  m := Length(mat[1]);
  n := Length(mat);

  if S = T then
    return RMSIsoByTriple(S, T, [(),
                                 IdentityMapping(G),
                                 ListWithIdenticalEntries(m + n, ())]);
  fi;

  f := IsomorphismGroups(G, H);
  if f = fail then
    return fail;
  fi;

  # for RMS without 0 the graphs are always isomorphic,
  # being complete bipartite.

  isograph := DirectProduct(SymmetricGroup(m), SymmetricGroup(n));
  # all isomorphisms from g1 to g2
  isogroup := List(Elements(AutomorphismGroup(G)), x -> x * f);

  # find an induced function, if there is one
  RMSInducedFunction := SEMIGROUPS.RMSInducedFunction;
  for l in isograph do
    for g in isogroup do
      for tup in Elements(H) do
        map := RMSInducedFunction(S, T, l, g, tup);
        if map <> fail then
          return RMSIsoByTriple(S, T, [l, g, map]);
        fi;
      od;
    od;
  od;
  return fail;
end);

InstallMethod(IsomorphismSemigroups,
"for finite whole family Rees 0-matrix semigroups",
[IsReesZeroMatrixSemigroup and IsWholeFamily and IsFinite,
 IsReesZeroMatrixSemigroup and IsWholeFamily and IsFinite],
function(S, T)
  local G, H, mat, m, n, f, groupiso, grS, grT, g, graphiso, tuples,
        RZMStoRZMSInducedFunction, map, l, tup;

  G := UnderlyingSemigroup(S);
  H := UnderlyingSemigroup(T);

  if not (IsRegularSemigroup(S) and IsGroupAsSemigroup(G) and
          IsRegularSemigroup(T) and IsGroupAsSemigroup(H)) then
    TryNextMethod();
  elif Size(S) <> Size(T)
      or Length(Columns(S)) <> Length(Columns(T))
      or Length(Rows(S)) <> Length(Rows(T)) then
    return fail;
  elif not (IsPermGroup(G) and IsPermGroup(H)) then
    TryNextMethod();
  fi;

  mat := Matrix(S);
  m := Length(mat[1]);
  n := Length(mat);

  if S = T then
    return RZMSIsoByTripleNC(S, T, [(),
                                  IdentityMapping(G),
                                  ListWithIdenticalEntries(m + n, ())]);
  fi;

  # every isomorphism of the groups
  f := IsomorphismGroups(G, H);
  if f = fail then
    return fail;
  fi;
  groupiso := List(AutomorphismGroup(G), x -> x * f);

  # every isomorphism of the graphs
  grS := RZMSDigraph(S);
  grT := RZMSDigraph(T);
  if grS <> grT then
    g := IsomorphismDigraphs(grS, grT);
    if g = fail then
      return fail;
    fi;
  else
    g := ();
  fi;
  graphiso := List(AutomorphismGroup(grS, [[1 .. m], [m + 1 .. n + m]]),
                   x -> x * g);

  tuples := EnumeratorOfCartesianProduct(
              List([1 .. Length(DigraphConnectedComponents(grS).comps)],
                   x -> H));
  # find an induced function, if there is one
  RZMStoRZMSInducedFunction := SEMIGROUPS.RZMStoRZMSInducedFunction;
  for l in graphiso do
    for g in groupiso do
      for tup in tuples do
        # TODO(never) it should be possible to cut this down
        map := RZMStoRZMSInducedFunction(S, T, l, g, tup);
        if map <> fail then
          return RZMSIsoByTripleNC(S, T, [l, g, map]);
        fi;
      od;
    od;
  od;
  return fail;
end);

#############################################################################
# 5. RMS/RZMSIsoByTriple
#############################################################################

InstallMethod(RMSIsoByTriple,
"for two Rees matrix semigroups and a dense list",
[IsReesMatrixSemigroup, IsReesMatrixSemigroup, IsDenseList],
function(R1, R2, triple)
  local graph_iso, group_iso, g2_elms_list, nrrows, nrcols, G1, G2;
  graph_iso := triple[1];
  group_iso := triple[2];
  g2_elms_list := triple[3];

  # Check number of rows and cols
  nrcols := Length(Rows(R1));  # rows of R1 are cols of the matrix
  nrrows := Length(Columns(R1));
  if nrcols <> Length(Rows(R2)) or nrrows <> Length(Columns(R2)) then
    ErrorNoReturn("the 1st and 2nd arguments (Rees matrix semigroups) ",
                  "have different numbers of rows and columns");
  fi;

  # Check graph isomorphism
  if not IsPerm(graph_iso) then
    ErrorNoReturn("the 1st entry in the 3rd argument (a triple) is ",
                  "not a permutation");
  elif LargestMovedPoint(graph_iso) > nrrows + nrcols then
    ErrorNoReturn("the 1st entry (a permutation) in the 3rd argument ",
                  "(a triple) is not a permutation on [1 .. ",
                  nrrows + nrcols, "]");
  elif ForAny([1 .. nrcols], x -> x ^ graph_iso > nrcols) then
    ErrorNoReturn("the 1st entry (a permutation) in the 3rd argument ",
                  "(a triple) maps rows to columns");
  fi;

  # Check group isomorphism
  G1 := UnderlyingSemigroup(R1);
  G2 := UnderlyingSemigroup(R2);
  if not (IsGroupHomomorphism(group_iso) and
          IsBijective(group_iso) and
          Source(group_iso) = G1 and
          Range(group_iso) = G2) then
    ErrorNoReturn("the 2nd entry in the 3rd argument (a triple)",
                  " is not an isomorphism between the underlying groups",
                  " of the 1st and 2nd arguments (Rees matrix semigroups)");
  fi;

  # Check map from rows and cols to H
  if Length(g2_elms_list) <> nrrows + nrcols then
    ErrorNoReturn("the 3rd entry (a list) in the 3rd argument (a triple)",
                  "does not have length equal to the number of rows and ",
                  "columns of the 1st argument (a Rees matrix semigroup)");
  elif not ForAll(g2_elms_list, x -> x in G2) then
    ErrorNoReturn("the 3rd entry (a list) in the 3rd argument (a triple)",
                  " does not consist of elements of the underlying group",
                  " of the 2nd argument (a Rees matrix semigroup)");
  elif SEMIGROUPS.RMSInducedFunction(R1, R2, graph_iso, group_iso,
                                     g2_elms_list[1]) <> g2_elms_list then
    ErrorNoReturn("the 3rd entry (a list) in the 3rd argument (a triple)",
                  " does not define an isomorphism");
  fi;

  return RMSIsoByTripleNC(R1, R2, triple);
end);

InstallMethod(RZMSIsoByTriple,
"for two Rees 0-matrix semigroups and a dense list",
[IsReesZeroMatrixSemigroup, IsReesZeroMatrixSemigroup, IsDenseList],
function(R1, R2, triple)
  local graph_iso, group_iso, g2_elms_list, nrrows, nrcols, graph1, graph2, G1,
        G2, reps, map, rep;
  graph_iso := triple[1];
  group_iso := triple[2];
  g2_elms_list := triple[3];

  # Check number of rows and cols
  nrrows := Length(Rows(R1));
  nrcols := Length(Columns(R1));
  if nrrows <> Length(Rows(R2)) or nrcols <> Length(Columns(R2)) then
    ErrorNoReturn("the 1st and 2nd arguments (Rees 0-matrix semigroups) ",
                  "have different numbers of rows and columns");
  fi;

  # Check graph isomorphism
  graph1 := RZMSDigraph(R1);
  graph2 := RZMSDigraph(R2);
  if not IsPerm(graph_iso) then
    ErrorNoReturn("the 1st entry in the 3rd argument (a triple) is ",
                  "not a permutation");
  elif not OnDigraphs(graph1, graph_iso) = graph2 then
    ErrorNoReturn("the 1st entry in the 3rd argument (a triple) is ",
                  "not an isomorphism from the graph of the 1st argument (a",
                  " Rees 0-matrix semigroup) and the graph of the 2nd ",
                  "argument (a Rees 0-matrix semigroup)");
  fi;

  # Check group isomorphism
  G1 := UnderlyingSemigroup(R1);
  G2 := UnderlyingSemigroup(R2);
  if not (IsGroupHomomorphism(group_iso) and
          IsBijective(group_iso) and
          Source(group_iso) = G1 and
          Range(group_iso) = G2) then
    ErrorNoReturn("the 2nd entry in the 3rd argument (a triple)",
                  " is not an isomorphism between the underlying groups",
                  " of the 1st and 2nd arguments (Rees 0-matrix semigroups)");
  fi;

  # Check map from rows and cols to H
  if Length(g2_elms_list) <> nrrows + nrcols then
    ErrorNoReturn("the 3rd entry (a list) in the 3rd argument (a triple)",
                  "does not have length equal to the number of rows and ",
                  "columns of the 1st argument (a Rees 0-matrix semigroup)");
  elif not ForAll(g2_elms_list, x -> x in G2) then
    ErrorNoReturn("the 3rd entry (a list) in the 3rd argument (a triple)",
                  " does not consist of elements of the underlying group",
                  " of the 2nd argument (a Rees 0-matrix semigroup)");
  fi;
  reps := List(DigraphConnectedComponents(graph1).comps, Representative);
  map := EmptyPlist(Length(reps));
  for rep in reps do
    map[rep] := g2_elms_list[rep];
  od;
  if SEMIGROUPS.RZMStoRZMSInducedFunction(R1, R2, graph_iso, group_iso, map)
      <> g2_elms_list then
    ErrorNoReturn("the 3rd entry (a list) in the 3rd argument (a triple)",
                  " does not define an isomorphism");
  fi;

  return RZMSIsoByTripleNC(R1, R2, triple);
end);

InstallMethod(RMSIsoByTripleNC,
"for two Rees matrix semigroups and a dense list",
[IsReesMatrixSemigroup, IsReesMatrixSemigroup, IsDenseList],
function(R1, R2, triple)
  local fam, out;
  fam := GeneralMappingsFamily(ElementsFamily(FamilyObj(R1)),
                               ElementsFamily(FamilyObj(R2)));
  out := Objectify(NewType(fam, IsRMSIsoByTriple), rec(triple := triple));
  SetSource(out, R1);
  SetRange(out, R2);
  return out;
end);

InstallMethod(RZMSIsoByTripleNC,
"for two Rees 0-matrix semigroups and a dense list",
[IsReesZeroMatrixSemigroup, IsReesZeroMatrixSemigroup, IsDenseList],
function(R1, R2, triple)
  local fam, out;
  fam := GeneralMappingsFamily(ElementsFamily(FamilyObj(R1)),
                               ElementsFamily(FamilyObj(R2)));
  out := Objectify(NewType(fam, IsRZMSIsoByTriple), rec(triple := triple));
  SetSource(out, R1);
  SetRange(out, R2);
  return out;
end);

InstallMethod(ELM_LIST, "for objects in `IsRMSIsoByTriple'",
[IsRMSIsoByTriple, IsPosInt], {x, i} -> x!.triple[i]);

InstallMethod(ELM_LIST, "for objects in `IsRZMSIsoByTriple'",
[IsRZMSIsoByTriple, IsPosInt], {x, i} -> x!.triple[i]);

InstallMethod(\=, "for objects in `IsRMSIsoByTriple'",
[IsRMSIsoByTriple, IsRMSIsoByTriple],
function(x, y)

  if Source(x) <> Source(y) or Range(x) <> Range(y) then
    return false;
  elif x[1] = y[1] and x[2] = y[2] and x[3] = y[3] then
    return true;
  fi;

  return OnTuples(GeneratorsOfSemigroup(Source(x)), x)
       = OnTuples(GeneratorsOfSemigroup(Source(x)), y);
end);

InstallMethod(\=, "for objects in `IsRZMSIsoByTriple'",
[IsRZMSIsoByTriple, IsRZMSIsoByTriple],
function(x, y)

  if Source(x) <> Source(y) or Range(x) <> Range(y) then
    return false;
  elif x[1] = y[1] and x[2] = y[2] and x[3] = y[3] then
    return true;
  fi;

  return OnTuples(GeneratorsOfSemigroup(Source(x)), x)
         = OnTuples(GeneratorsOfSemigroup(Source(x)), y);
end);

InstallMethod(\<, "for objects in `IsRMSIsoByTriple'",
IsIdenticalObj,
[IsRMSIsoByTriple, IsRMSIsoByTriple],
function(x, y)
  return OnTuples(GeneratorsOfSemigroup(Source(x)), x)
         < OnTuples(GeneratorsOfSemigroup(Source(x)), y);
end);

InstallMethod(\<, "for objects in `IsRZMSIsoByTriple'",
IsIdenticalObj,
[IsRZMSIsoByTriple, IsRZMSIsoByTriple],
function(x, y)
  return OnTuples(GeneratorsOfSemigroup(Source(x)), x)
         < OnTuples(GeneratorsOfSemigroup(Source(x)), y);
end);

InstallMethod(CompositionMapping2, "for objects in `IsRMSIsoByTriple'",
[IsRMSIsoByTriple, IsRMSIsoByTriple],
function(map2, map1)
  local n;
  n := Length(Rows(Source(map2))) + Length(Columns(Source(map2)));
  return RMSIsoByTripleNC(Source(map1),
                          Range(map2),
                          [map1[1] * map2[1],
                           map1[2] * map2[2],
                           List([1 .. n],
                                i -> map2[3][i ^ map1[1]] * map1[3][i] ^
                                                            map2[2])]);
end);

InstallMethod(CompositionMapping2, "for objects in `IsRZMSIsoByTriple'",
IsIdenticalObj, [IsRZMSIsoByTriple, IsRZMSIsoByTriple],
function(map2, map1)
  local n;
  n := Length(Rows(Source(map1))) + Length(Columns(Source(map1)));
  return RZMSIsoByTripleNC(Source(map1),
                           Range(map2),
                           [map1[1] * map2[1],
                            map1[2] * map2[2],
                            List([1 .. n],
                                 i -> map2[3][i ^ map1[1]] * map1[3][i] ^
                                                             map2[2])]);
end);

InstallMethod(ImagesElm, "for an RMS element under a mapping by a triple",
FamSourceEqFamElm, [IsRMSIsoByTriple, IsReesMatrixSemigroupElement],
{triple, x} -> [ImagesRepresentative(triple, x)]);

InstallMethod(ImagesElm, "for an RZMS element under a mapping by a triple",
FamSourceEqFamElm, [IsRZMSIsoByTriple, IsReesZeroMatrixSemigroupElement],
{triple, x} -> [ImagesRepresentative(triple, x)]);

InstallMethod(ImagesRepresentative,
"for an RMS element under a mapping by a triple",
FamSourceEqFamElm, [IsRMSIsoByTriple, IsReesMatrixSemigroupElement],
function(map, x)
  local m;
  m := Length(Rows(Source(map)));
  return RMSElementNC(Range(map),
                      x[1] ^ map[1],
                      map[3][x[1]] * x[2] ^ map[2] / map[3][x[3] + m],
                      (x[3] + m) ^ map[1] - m);
end);

InstallMethod(ImagesRepresentative,
"for an RZMS element under a mapping by a triple",
FamSourceEqFamElm, [IsRZMSIsoByTriple, IsReesZeroMatrixSemigroupElement],
function(map, x)
  local m;

  m := Length(Rows(Source(map)));
  if x = MultiplicativeZero(Source(map)) or map[3][x[1]] = 0
        or map[3][x[3] + m] = 0 then
    return MultiplicativeZero(Range(map));
  fi;
  return RMSElementNC(Range(map),
                      x[1] ^ map[1],
                      map[3][x[1]] * x[2] ^ map[2] / map[3][x[3] + m],
                      (x[3] + m) ^ map[1] - m);
end);

InstallMethod(InverseGeneralMapping, "for objects in `IsRMSIsoByTriple'",
[IsRMSIsoByTriple],
function(map)
  local n, inv;
  n := Length(Rows(Source(map))) + Length(Columns(Source(map)));
  inv := InverseGeneralMapping(map[2]);
  return RMSIsoByTripleNC(Range(map),
                          Source(map),
                          [map[1] ^ -1,
                           inv,
                           List([1 .. n],
                                i -> ((map[3][i ^ (map[1] ^ -1)] ^ inv)
                                      ^ -1))]);
end);

InstallMethod(InverseGeneralMapping, "for objects in `IsRMSIsoByTriple'",
[IsRMSIsoByTriple and IsOne], x -> x);

InstallMethod(InverseGeneralMapping, "for objects in `IsRZMSIsoByTriple'",
[IsRZMSIsoByTriple],
function(map)
  local n, inv;
  n := Length(Rows(Source(map))) + Length(Columns(Source(map)));
  inv := InverseGeneralMapping(map[2]);
  return RZMSIsoByTripleNC(Range(map),
                           Source(map),
                           [map[1] ^ -1,
                            inv,
                            List([1 .. n],
                                 i -> (map[3][i ^ (map[1] ^ -1)] ^ inv) ^ -1)]);
end);

InstallMethod(IsOne, "for objects in `IsRMSIsoByTriple'",
[IsRMSIsoByTriple],
map -> IsOne(map[1]) and IsOne(map[2]) and ForAll(map[3], IsOne));

InstallMethod(IsOne, "for objects in `IsRZMSIsoByTriple'",
[IsEndoGeneralMapping and IsRZMSIsoByTriple],
map -> IsOne(map[1]) and IsOne(map[2]) and ForAll(map[3], IsOne));

InstallMethod(PreImagesRepresentative,
"for an RMS element under a mapping by a triple",
FamRangeEqFamElm, [IsRMSIsoByTriple, IsReesMatrixSemigroupElement],
{map, x} -> ImagesRepresentative(InverseGeneralMapping(map), x));

InstallMethod(PreImagesRepresentative,
"for an RZMS element under a mapping by a triple",
FamRangeEqFamElm, [IsRZMSIsoByTriple, IsReesZeroMatrixSemigroupElement],
{map, x} -> ImagesRepresentative(InverseGeneralMapping(map), x));

InstallMethod(PrintObj, "for an object in `IsRMSIsoByTriple'",
[IsRMSIsoByTriple],
function(map)
  Print("RMSIsoByTriple ( ", Source(map), ", ", Range(map), ", [", map[1],
        ", ", map[2], ", ", map[3], "])");
  return;
end);

InstallMethod(PrintObj, "for an object in `IsRZMSIsoByTriple'",
[IsRZMSIsoByTriple],
function(map)
  Print("RZMSIsoByTriple ( ", Source(map), ", ", Range(map), ", ", map[1],
        ", ", map[2], ", ", map[3], " )");
  return;
end);

# InstallMethod(PrintString, "for an object in `IsRMSIsoByTriple'",
# [IsRMSIsoByTriple],
# function(map)
#   return StringFormatted("RMSIsoByTriple({}, {}, [{}, {}, {}])",
#                          Source(map),
#                          Range(map),
#                          map[1],
#                          map[2],
#                          map[3]);
# end);
#
# InstallMethod(PrintString, "for an object in `IsRZMSIsoByTriple'",
# [IsRZMSIsoByTriple],
# function(map)
#   return StringFormatted("RZMSIsoByTriple({}, {}, [{}, {}, {}])",
#                          Source(map),
#                          Range(map),
#                          map[1],
#                          map[2],
#                          map[3]);
# end);

InstallMethod(ViewObj, "for an object in `IsRMSIsoByTriple'",
[IsRMSIsoByTriple], map -> Print("(", map[1], ", ", map[2], ", ", map[3], ")"));

InstallMethod(ViewObj, "for object in `IsRZMSIsoByTriple'",
[IsRZMSIsoByTriple], map -> Print("(", map[1], ", ", map[2], ", ", map[3], ")"));

# InstallMethod(ViewString, "for an object in `IsRMSIsoByTriple'",
# [IsRMSIsoByTriple],
# function(map)
#   return StringFormatted("({!v}, {!v}, {!v})", map[1], map[2], map[3]);
# end);
#
# InstallMethod(ViewString, "for object in `IsRZMSIsoByTriple'",
# [IsRZMSIsoByTriple],
# function(map)
#   return StringFormatted("({!v}, {!v}, {!v})", map[1], map[2], map[3]);
# end);

InstallMethod(IsomorphismReesMatrixSemigroupOverPermGroup,
"for a semigroup",
[IsSemigroup],
function(S)
  local iso, T, G, isoG, invG, s;

  if not IsFinite(S) or not IsSimpleSemigroup(S) then
    ErrorNoReturn("the argument is not a finite simple semigroup");
  elif not IsReesMatrixSemigroup(S) then
    return IsomorphismReesMatrixSemigroup(S);
  elif not IsWholeFamily(S) then
    iso := IsomorphismReesMatrixSemigroup(S);
    T := Range(iso);
    if IsPermGroup(UnderlyingSemigroup(T)) then
      return iso;
    fi;
    return CompositionMapping(IsomorphismReesMatrixSemigroupOverPermGroup(T),
                              iso);
  fi;

  G := UnderlyingSemigroup(S);
  isoG := IsomorphismPermGroup(G);
  invG := InverseGeneralMapping(isoG);
  s := ReesMatrixSemigroup(Range(isoG),
                          List(Matrix(S), x -> OnTuples(x, isoG)));
  return SemigroupIsomorphismByFunctionNC(S, s,
           x -> RMSElement(s, x![1], x![2] ^ isoG, x![3]),
           x -> RMSElement(S, x![1], x![2] ^ invG, x![3]));
end);

InstallMethod(IsomorphismReesZeroMatrixSemigroupOverPermGroup,
"for a semigroup",
[IsSemigroup],
function(S)
  local iso, T, G, isoG, invG, s, func;

  if not IsFinite(S) or not IsZeroSimpleSemigroup(S) then
    ErrorNoReturn("the argument is not a finite 0-simple semigroup");
  elif not IsReesZeroMatrixSemigroup(S) then
    return IsomorphismReesZeroMatrixSemigroup(S);
  elif not IsWholeFamily(S) then
    iso := IsomorphismReesZeroMatrixSemigroup(S);
    T := Range(iso);
    if IsPermGroup(UnderlyingSemigroup(T)) then
      return iso;
    fi;
    return CompositionMapping(
             IsomorphismReesZeroMatrixSemigroupOverPermGroup(T), iso);
  fi;

  func := function(x, map)
    if x = 0 then
      return 0;
    fi;
    return x ^ map;
  end;

  G := UnderlyingSemigroup(S);
  isoG := IsomorphismPermGroup(G);
  invG := InverseGeneralMapping(isoG);
  s := ReesZeroMatrixSemigroup(Range(isoG),
                               List(Matrix(S),
                                    x -> List(x, y -> func(y, isoG))));

  return SemigroupIsomorphismByFunctionNC(S, s,
           function(x)
             if x![1] = 0 then
               return MultiplicativeZero(s);
             fi;
             return RMSElement(s, x![1], func(x![2], isoG), x![3]);
           end,
           function(x)
             if x![1] = 0 then
               return MultiplicativeZero(S);
             fi;
             return RMSElement(S, x![1], func(x![2], invG), x![3]);
           end);
end);

InstallMethod(CanonicalReesZeroMatrixSemigroup,
"for a Rees zero matrix semigroup",
[IsReesZeroMatrixSemigroup],
function(S)
  local Flatten3DPoint, Unflatten3DPoint, SetToZeroGroupMatrix,
  ZeroGroupMatrixToSet, RZMSMatrixIsomorphismGroup, M, G, m, n, setM, GG;
  # Go from a triple in I x J x {1 .. |G| + 1} to an integer in
  # [1 .. |I| * |J| * (|G| + 1)]. Inverse of Unflatten3DPoint.
  Flatten3DPoint := function(dimensions, point)
    return (point[1] - 1) * dimensions[2] * dimensions[3] +
      (point[2] - 1) * dimensions[3] + (point[3] - 1) + 1;
  end;

  # Go from an integer in [1 .. |I| * |J| * (|G| + 1)] to an element of
  # I x J x {1 .. |G| + 1}. Inverse of Flatten3DPoint.
  Unflatten3DPoint := function(dimensions, value)
     local ret;
     ret    := [];
     value  := value - 1;
     ret[3] := value mod dimensions[3] + 1;
     value  := value - (ret[3] - 1);
     value  := value / dimensions[3];
     ret[2] := value mod dimensions[2] + 1;
     value  := value - (ret[2] - 1);
     ret[1] := value / dimensions[2] + 1;
     return ret;
  end;

  # Unflatten the entries of a set representing a matrix over a 0-group and
  # return the corresponding matrix. Inverse of ZeroGroupMatrixToSet.
  SetToZeroGroupMatrix := function(set, nr_rows, nr_cols, G)
    local 0G, mat, dim, point, x;
    0G  := Concatenation([0], Enumerator(G));
    mat := List([1 .. nr_rows], a -> EmptyPlist(nr_cols));
    dim := [nr_rows, nr_cols, Size(G) + 1];
    for x in set do
      point                   := Unflatten3DPoint(dim, x);
      mat[point[1]][point[2]] := 0G[point[3]];
    od;
    return mat;
  end;

  # Flatten the entries of a matrix over a 0-group and return as a set of
  # integers. Inverse of SetToZeroGroupMatrix.
  ZeroGroupMatrixToSet := function(mat, nr_rows, nr_cols, G)
    local set, dim, i, j;
    set := [];
    dim := [nr_rows, nr_cols, Size(G) + 1];
    for i in [1 .. nr_rows] do
      for j in [1 .. nr_cols] do
        if mat[i][j] = 0 then
          Add(set, Flatten3DPoint(dim, [i, j, 1]));
        else
          Add(set,
            Flatten3DPoint(dim, [i, j, 1 + Position(Enumerator(G),
                                                               mat[i][j])]));
        fi;
      od;
    od;
    return set;
  end;

  # The representation of the group ((G \wr S_m) \times (G \wr S_n)) \rtimes
  # Aut(G) acting on [1 .. |I| * |J| * (|G| + 1)] where the integers correspond
  # to entries of a J x I matrix with entries from the 0-group G_0.
  RZMSMatrixIsomorphismGroup := function(nr_rows, nr_cols, G)
    local ApplyPermWholeDimension, ApplyPermSingleAssignDimension, dim, S, rows,
    cols, gens, elms, rmlt, grswaps, lmlt, gcswaps, auto;

    ApplyPermWholeDimension := function(dimensions, dim, perm)
      local map, point, i;
        map := [];
        for i in [1 .. Product(dimensions)] do
          point      := Unflatten3DPoint(dimensions, i);
          point[dim] := point[dim] ^ perm;
          map[i]     := Flatten3DPoint(dimensions, point);
        od;
      return PermList(map);
    end;

    ApplyPermSingleAssignDimension  := function(dimensions, dim,
                                                perm, fixdim, fixval)
      local map, point, i;
      map := [];
      for i in [1 .. Product(dimensions)] do
        point := Unflatten3DPoint(dimensions, i);
        if point[fixdim] = fixval then
          point[dim] := point[dim] ^ perm;
        fi;
        map[i] := Flatten3DPoint(dimensions, point);
      od;
      return PermList(map);
    end;

    dim := [nr_rows, nr_cols, Size(G) + 1];
    # Row Swaps
    S    := SymmetricGroup(nr_rows);
    rows := List(GeneratorsOfGroup(S),
                 x -> ApplyPermWholeDimension(dim, 1, x));

    # Col swaps
    S    := SymmetricGroup(nr_cols);
    cols := List(GeneratorsOfGroup(S),
                 x -> ApplyPermWholeDimension(dim, 2, x));

    gens := GeneratorsOfGroup(G);
    elms := ShallowCopy(Enumerator(G));

    # Apply g to each row (left multiplication by inverse):
    rmlt := List(gens, g -> PermList(Concatenation([1],
            1 + List(elms, e -> Position(elms, g ^ -1 * e)))));
    grswaps := List(rmlt, g -> ApplyPermSingleAssignDimension(dim, 3, g, 1, 1));

    # Apply g to each col (right multiplication):
    lmlt := List(gens, g -> PermList(Concatenation([1],
            1 + List(elms, e -> Position(elms, e * g)))));
    gcswaps := List(lmlt, g -> ApplyPermSingleAssignDimension(dim, 3, g, 2, 1));

    # Automorphisms of G
    S    := AutomorphismGroup(G);
    auto := Filtered(GeneratorsOfGroup(S), x -> not IsInnerAutomorphism(x));
    auto := List(auto, x -> List(Enumerator(G), a ->
            Position(Enumerator(G), a ^ x)));
    Apply(auto, a -> PermList(Concatenation([1], a + 1)));
    auto := List(auto, x -> ApplyPermWholeDimension(dim, 3, x));

    # The RZMS matrix isomorphism group
    return Group(Flat([rows, cols, grswaps, gcswaps, auto]));
  end;

  M    := Matrix(S);
  G    := UnderlyingSemigroup(S);
  if not IsGroup(UnderlyingSemigroup(S)) then
    ErrorNoReturn("the underlying semigroup of the argument ",
                  "(a Rees 0-matrix semigroup) is not a group");
  fi;
  m    := Length(M);
  n    := Length(M[1]);
  setM := ZeroGroupMatrixToSet(M, m, n, G);
  GG   := RZMSMatrixIsomorphismGroup(m, n, G);
  return ReesZeroMatrixSemigroup(G, SetToZeroGroupMatrix(
                                 CanonicalImage(GG, setM, OnSets), m, n, G));
end);

InstallMethod(CanonicalReesMatrixSemigroup,
"for a Rees matrix semigroup",
[IsReesMatrixSemigroup],
function(S)
  local G, mat;
  G   := UnderlyingSemigroup(S);
  if not IsGroup(G) then
    ErrorNoReturn("the underlying semigroup of the argument ",
                  "(a Rees 0-matrix semigroup) is not a group");
  fi;
  mat := Matrix(CanonicalReesZeroMatrixSemigroup(
           ReesZeroMatrixSemigroup(G, Matrix(S))));
  return ReesMatrixSemigroup(G, mat);
end);
