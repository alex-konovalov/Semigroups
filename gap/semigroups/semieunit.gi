#############################################################################
##
##  semigroups/semieunit.gi
##  Copyright (C) 2017-2022                               Christopher Russell
##
##  Licensing information can be found in the README file of this package.
##
#############################################################################

#############################################################################
# Methods for creating McAlister triple semigroups
#############################################################################

InstallMethod(McAlisterTripleSemigroup,
"for a group, digraph, digraph, and action",
[IsGroup, IsDigraph, IsDigraph, IsFunction],
function(G, X, Y, act)
  local anti_act, hom, out_nbrs, orbs, min, fam, filt, M, x, y;

  if not IsFinite(G) then
    ErrorNoReturn("the 1st argument (a group) is not finite");
  fi;

  anti_act := function(pt, g)
    return act(pt, g ^ -1);
  end;

  hom := ActionHomomorphism(G, DigraphVertices(X), anti_act);

  if ForAny(GeneratorsOfGroup(Image(hom)),
            g -> not IsDigraphAutomorphism(X, g)) then
    ErrorNoReturn("the 1st argument (a group) must act by order ",
                  "automorphisms on the 2nd argument (a partial order ",
                  "digraph)");
  elif not IsPartialOrderDigraph(X) then
    ErrorNoReturn("the 2nd argument (a digraph) must be a partial order ",
                  "digraph");
  fi;

  # Check that Y is a semilattice and an induced subdigraph of X
  if not Y = InducedSubdigraph(X, DigraphVertexLabels(Y)) then
    ErrorNoReturn("the 3rd argument <X> (a digraph) must be an induced ",
                  "subdigraph of the 2nd argument <Y> (a digraph) with ",
                  "vertex labels corresponding to the vertices of <X> on ",
                  "which <Y> was induced");
  elif not IsJoinSemilatticeDigraph(Y) then
    ErrorNoReturn("the 3rd argument (a digraph) must be a join-semilattice ",
                  "digraph");
  fi;

  # Check condition M2 (check that Y is an order ideal of X.)
  out_nbrs := OutNeighbors(X);
  for x in DigraphVertices(X) do
    if not x in DigraphVertexLabels(Y) then
      for y in DigraphSources(DigraphRemoveLoops(Y)) do
        if x in out_nbrs[DigraphVertexLabel(Y, y)] then
          ErrorNoReturn("the out-neighbours of each vertex of the 2nd ",
                        "argument (a digraph) which is in the 3rd argument ",
                        "<Y> (a digraph) must contain only vertices which ",
                        "are in <Y> - see the documentation for more details");
        fi;
      od;
    fi;
  od;

  orbs := Orbits(Image(hom));

  # Check condition M3 (check that G.Y = X.)
  if not ForAll(orbs, o -> ForAny(DigraphVertexLabels(Y), v -> v in o)) then
    ErrorNoReturn("every vertex of <X> must be in the orbit of some vertex ",
                  "of <X> which is in <Y> - see the documentation ",
                  "for more detail");
  fi;

  for x in DigraphVertices(X) do
    if not x in Union(orbs) and not (x in DigraphVertexLabels(Y)) then
      ErrorNoReturn("every vertex of <X> must be in the orbit of some ",
                    "vertex of <X> which is in <Y> - see the documentation",
                    " for more detail");
    fi;
  od;

  # Check condition M4 (essentially, check that G.Y = X is connected.)
  min := DigraphVertexLabel(Y, DigraphSinks(DigraphRemoveLoops(Y))[1]);
  if ForAny(GeneratorsOfGroup(Image(hom)), g -> min ^ g <> min) then
      ErrorNoReturn("<act> must fix the vertex of <X> which is the minimal ",
                    "vertex of <Y> - see the documentation for more detail");
  fi;

  fam := NewFamily("McAlisterTripleSemigroupFamily",
                   IsMcAlisterTripleSemigroupElement);

  # Check if this McAlister triple semigroup is a monoid
  if IsMeetSemilatticeDigraph(Y) then
    filt := IsMcAlisterTripleSemigroup and IsMonoid;
  else
    filt := IsMcAlisterTripleSemigroup;
  fi;

  # Create the semigroup itself
  M := Objectify(NewType(CollectionsFamily(fam), filt and IsAttributeStoringRep
                         and IsEUnitaryInverseSemigroup and IsWholeFamily),
                 rec());

  M!.elementType := NewType(fam, IsMcAlisterTripleSemigroupElementRep);

  SetMcAlisterTripleSemigroupGroup(M, G);
  SetMcAlisterTripleSemigroupAction(M, anti_act);
  SetMcAlisterTripleSemigroupUnderlyingAction(M, act);
  SetMcAlisterTripleSemigroupPartialOrder(M, X);
  SetMcAlisterTripleSemigroupSemilattice(M, Y);
  SetMcAlisterTripleSemigroupActionHomomorphism(M, hom);

  SetGeneratorsOfSemigroup(M, SEMIGROUPS.MTSSmallGen(M));
  return M;
end);

InstallMethod(McAlisterTripleSemigroup,
"for a perm group, digraph, and digraph",
[IsPermGroup, IsDigraph, IsDigraph],
{G, X, Y} -> McAlisterTripleSemigroup(G, X, Y, OnPoints));

InstallMethod(McAlisterTripleSemigroup,
"for a perm group, digraph, homogeneous list, and action",
[IsGroup, IsDigraph, IsHomogeneousList, IsFunction],
{G, X, sub_ver, act}
-> McAlisterTripleSemigroup(G, X, InducedSubdigraph(X, sub_ver), act));

InstallMethod(McAlisterTripleSemigroup,
"for a perm group, digraph, and homogeneous list",
[IsPermGroup, IsDigraph, IsHomogeneousList],
function(G, X, sub_ver)
  return McAlisterTripleSemigroup(G,
                                  X,
                                  InducedSubdigraph(X, sub_ver),
                                  OnPoints);
end);

#############################################################################
# Methods for McAlister triple semigroups
#############################################################################

InstallMethod(OneImmutable, "for a McAlister triple semigroup element",
[IsMcAlisterTripleSemigroupElement], x -> OneImmutable(MTSEParent(x)));

InstallMethod(OneImmutable,
"for a McAlister triple semigroup element collection",
[IsMcAlisterTripleSemigroupElementCollection],
function(coll)
  local Y;

  if not IsSemigroup(coll) then
    coll := MTSEParent(Representative(coll));
  fi;
  if not IsMonoid(coll) then
    return fail;
  fi;
  Y := McAlisterTripleSemigroupSemilattice(coll);
  return MTSE(coll, DigraphSources(DigraphRemoveLoops(Y))[1], ());
end);

InstallMethod(McAlisterTripleSemigroupComponents,
"for a McAlister triple semigroup",
[IsMcAlisterTripleSemigroup and IsWholeFamily],
function(S)
  local G, XX, YY, act, comps, id, next, o, v;

  G   := McAlisterTripleSemigroupGroup(S);
  XX  := McAlisterTripleSemigroupPartialOrder(S);
  YY  := McAlisterTripleSemigroupSemilattice(S);
  act := McAlisterTripleSemigroupAction(S);

  comps := [];
  id    := ListWithIdenticalEntries(DigraphNrVertices(XX), 0);
  next  := 1;

  for v in DigraphVertexLabels(YY) do
    if id[v] = 0 then
      o := Intersection(Orbit(G, v, act), DigraphVertexLabels(YY));
      Add(comps, o);
      id{o} := ListWithIdenticalEntries(Length(o), next);
      next  := next + 1;
    fi;
  od;
  return rec(comps := comps, id := id);
end);

InstallMethod(McAlisterTripleSemigroupQuotientDigraph,
"for a McAlister triple semigroup",
[IsMcAlisterTripleSemigroup and IsWholeFamily],
function(S)
  local YY_XX, comps, D;
  YY_XX := McAlisterTripleSemigroupSemilatticeVertexLabelInverseMap(S);
  # Convert components to vertices of Y, rather than their labels in X.
  comps := List(McAlisterTripleSemigroupComponents(S).comps, c -> YY_XX{c});
  D := DigraphMutableCopy(McAlisterTripleSemigroupSemilattice(S));
  D := QuotientDigraph(D, comps);
  DigraphRemoveAllMultipleEdges(D);
  MakeImmutable(D);
  return D;
end);

InstallMethod(McAlisterTripleSemigroupSemilatticeVertexLabelInverseMap,
"for a McAlister triple semigroup",
[IsMcAlisterTripleSemigroup and IsWholeFamily],
function(S)
  local XX, YY, XX_YY, YY_XX, i;
  XX    := McAlisterTripleSemigroupPartialOrder(S);
  YY    := McAlisterTripleSemigroupSemilattice(S);
  XX_YY := DigraphVertexLabels(YY);
  if XX_YY <> DigraphVertices(XX) then
    YY_XX := ListWithIdenticalEntries(DigraphNrVertices(XX), 0);
    for i in [1 .. Length(XX_YY)] do
      YY_XX[XX_YY[i]] := i;
    od;
  else
    return XX_YY;
  fi;
  return YY_XX;
end);

InstallMethod(String, "for a McAlister triple subsemigroup",
[IsMcAlisterTripleSubsemigroup],
RankFilter(IsInverseSemigroup and HasGeneratorsOfSemigroup),
function(S)
  local G, X, Y;
  if not IsWholeFamily(S) then
    return Concatenation("Semigroup(", String(GeneratorsOfSemigroup(S)), ")");
  fi;
  G := McAlisterTripleSemigroupGroup(S);
  X := McAlisterTripleSemigroupPartialOrder(S);
  Y := McAlisterTripleSemigroupSemilattice(S);
  return StringFormatted("McAlisterTripleSemigroup({}, {}, {})",
                         String(G),
                         String(X),
                         String(DigraphVertexLabels(Y)));
end);

InstallMethod(PrintObj, "for a McAlister triple subsemigroup",
[IsMcAlisterTripleSubsemigroup],
function(S)
  Print(String(S));
end);

# TODO(later) Linebreak hints

InstallMethod(ViewString, "for a McAlister triple semigroup",
[IsMcAlisterTripleSemigroup],
SUM_FLAGS,
# to beat the library method for IsInverseSemigroup, or IsInverseMonoid
function(S)
  local G;
  G := McAlisterTripleSemigroupGroup(S);
  return StringFormatted("<McAlister triple semigroup over {}>",
                         ViewString(G));
end);

InstallMethod(ViewString, "for a McAlister triple subsemigroup",
[IsMcAlisterTripleSubsemigroup],
SUM_FLAGS,
# to beat the library method for IsInverseSemigroup, or IsInverseMonoid
function(S)
  local G;
  if HasIsMcAlisterTripleSemigroup(S) and IsMcAlisterTripleSemigroup(S) then
    TryNextMethod();
  fi;
  G := McAlisterTripleSemigroupGroup(S);
  return Concatenation("<McAlister triple subsemigroup over ",
                       ViewString(G), ">");
end);

InstallMethod(IsomorphismSemigroups, "for two McAlister triple semigroups",
[IsMcAlisterTripleSemigroup, IsMcAlisterTripleSemigroup],
function(S, T)
  local YS, YT, XT, iso_g, iso_x, im_YS, rep, A, hom;

  iso_g := IsomorphismGroups(McAlisterTripleSemigroupGroup(S),
                             McAlisterTripleSemigroupGroup(T));

  if iso_g = fail then
    return fail;
  fi;

  YS := McAlisterTripleSemigroupSemilattice(S);
  YT := McAlisterTripleSemigroupSemilattice(T);
  XT := McAlisterTripleSemigroupPartialOrder(T);

  if not IsIsomorphicDigraph(YS, YT) then
    return fail;
  fi;

  iso_x := IsomorphismDigraphs(McAlisterTripleSemigroupPartialOrder(S), XT);

  if iso_x = fail then
    return fail;
  fi;

  im_YS := List(DigraphVertexLabels(YS), a -> a ^ iso_x);
  # if the restriction of iso_x to DigraphVertexLabels(YS) is not
  # DigraphVertexLabels(YT) then we need to compose iso_x with an
  # automorphism of McAlisterTripleSemilattice(T). Composing this with
  # iso_x will restrict to an isomorphism from (the labels of) YS to YT.
  if not im_YS = DigraphVertexLabels(YT) then
    A   := AutomorphismGroup(XT);
    rep := RepresentativeAction(A, im_YS, DigraphVertexLabels(YT), OnSets);
    if rep = fail then
      return fail;
    fi;
  else
    rep := ();
  fi;

  if ForAll(McAlisterTripleSemigroupGroup(S),
      g -> ForAll(DigraphVertices(McAlisterTripleSemigroupPartialOrder(S)),
      x -> (McAlisterTripleSemigroupAction(S)(x, g)) ^ (rep * iso_x) =
      McAlisterTripleSemigroupAction(T)((x ^ iso_x), (g ^ iso_g)) ^ rep)) then
    hom := SemigroupHomomorphismByFunctionNC(S,
                                             T,
                                             s -> MTSE(T,
                                                       s[1] ^ iso_x,
                                                       s[2] ^ iso_g));
    SetIsBijective(hom, true);
    return hom;
  fi;
  return fail;
end);

InstallMethod(McAlisterTripleSemigroupGroup,
"for a McAlister triple subsemigroup",
[IsMcAlisterTripleSubsemigroup],
S -> McAlisterTripleSemigroupGroup(MTSEParent(Representative(S))));

InstallMethod(McAlisterTripleSemigroupPartialOrder,

"for a McAlister triple subsemigroup",
[IsMcAlisterTripleSubsemigroup],
S -> McAlisterTripleSemigroupPartialOrder(MTSEParent(Representative(S))));

InstallMethod(McAlisterTripleSemigroupSemilattice,
"for a McAlister triple subsemigroup",
[IsMcAlisterTripleSubsemigroup],
S -> McAlisterTripleSemigroupSemilattice(MTSEParent(Representative(S))));

InstallMethod(McAlisterTripleSemigroupAction,
"for a McAlister triple subsemigroup",
[IsMcAlisterTripleSubsemigroup],
S -> McAlisterTripleSemigroupAction(MTSEParent(Representative(S))));

InstallMethod(McAlisterTripleSemigroupActionHomomorphism,
"for a McAlister triple subsemigroup",
[IsMcAlisterTripleSubsemigroup],
S -> MTSActionHomomorphism(MTSEParent(Representative(S))));

InstallMethod(McAlisterTripleSemigroupUnderlyingAction,
"for a McAlister triple subsemigroup",
[IsMcAlisterTripleSubsemigroup],
S -> MTSUnderlyingAction(MTSEParent(Representative(S))));

InstallMethod(McAlisterTripleSemigroupComponents,
"for a McAlister triple subsemigroup",
[IsMcAlisterTripleSubsemigroup],
S -> MTSComponents(MTSEParent(Representative(S))));

InstallMethod(McAlisterTripleSemigroupQuotientDigraph,
"for a McAlister triple subsemigroup",
[IsMcAlisterTripleSubsemigroup],
S -> MTSQuotientDigraph(MTSEParent(Representative(S))));

InstallMethod(McAlisterTripleSemigroupSemilatticeVertexLabelInverseMap,
"for a McAlister triple subsemigroup",
[IsMcAlisterTripleSubsemigroup],
S -> MTSSemilatticeVertexLabelInverseMap(MTSEParent(Representative(S))));

SEMIGROUPS.MTSSmallGen := function(S)
  local G, Sl, X_Y, Y_X, comps, RepAct, _Stab, act, gens, po, top, sl, above, c,
  stab, check, orbs, stabs, found, Gcj, j, nbrs, r, i, cat, pos, combined,
  new_orbs, g, n, sizes, Gc1, alpha, gs, u, nbr, v, o, orb;

   G      := McAlisterTripleSemigroupGroup(S);
   Sl     := McAlisterTripleSemigroupSemilattice(S);
   X_Y    := DigraphVertexLabels(Sl);
   Y_X    := McAlisterTripleSemigroupSemilatticeVertexLabelInverseMap(S);
   comps  := McAlisterTripleSemigroupComponents(S).comps;

   if McAlisterTripleSemigroupUnderlyingAction(S) = OnPoints then
     RepAct := {a, b} -> RepresentativeAction(G, b, a);
     _Stab  := {a} -> Stabilizer(G, a);
   else
     # Can't use McAlisterTripleSemigroupAction because it is an anti-action
     # but not an action and produces unexpected results with some of these
     # methods.
     act    := McAlisterTripleSemigroupUnderlyingAction(S);
     RepAct := {a, b} -> RepresentativeAction(G, b, a, act);
     gens   := Generators(G);
     _Stab  := {a} -> Stabilizer(G, a, act);
   fi;

   # We use reflexive transitive reductions so we can only check neighbours
   # u > v such that there is no w where u > w > v.
   gens := [];
   po   := MTSQuotientDigraph(S);  # Vertex i corresponds to comps[i].
   po   := DigraphReflexiveTransitiveReduction(po);
   top  := Reversed(DigraphTopologicalSort(po));  # Order D-classes top 1st.
   sl   := DigraphReflexiveTransitiveReduction(Sl);
   SetDigraphVertexLabels(sl, DigraphVertexLabels(Sl));  # Preserve labelling.
   for i in [1 .. Length(top)] do
     above := Filtered(top{[1 .. i - 1]}, j -> Y_X[j] in InNeighboursOfVertex(po,
              top[i]));
     c := comps[top[i]];

     if IsEmpty(above) then  # Add generating set for this D-class.
       stab := GeneratorsOfGroup(_Stab(c[1]));
       for g in stab do
         Add(gens, MTSE(S, c[1], g));  # Add gens of maximal subgroup of R-class.
       od;
       if Length(c) > 1 then  # Add reps from H-classes of R-class.
         for j in [1 .. Length(c) - 1] do
           Add(gens, MTSE(S, c[j], RepAct(c[j + 1], c[j])));
         od;
       elif IsEmpty(stab) then  # If D-class is just a single element, add it.
         Add(gens, MTSE(S, c[1], One(G)));
       fi;
       Add(gens, MTSE(S, c[Length(c)], RepAct(c[1], c[Length(c)])));

     else  # We may have already generated some elements of this D-class.

       check := false;  # Check stays false until we know we have generated at
                        # least one element in this D-class.

       # Figure out which subsections of the D-class are generated
       # stabs are maximal subgroups in these subsections
       # orbs are lambda values, correspond to vertex labels of MTSSemilattice.
       orbs  := [];
       stabs := [];
       found := [];
       for u in c do
         if not u in found then
           Gcj := _Stab(u);
           Add(orbs, [u]);
           Add(found, u);
           Add(stabs, Group(()));
           j    := Length(orbs);
           nbrs := List(InNeighboursOfVertex(sl, Y_X[u]), v -> X_Y[v]);
           for nbr in nbrs do
             for v in Difference(c, found) do
               if ForAny(Elements(RightCoset(Gcj, RepAct(v, u))),
                         x -> MTSAction(S)(nbr, x) in X_Y) then
                 Add(orbs[j], v);
               fi;
             od;

             r := RightCosets(Gcj, stabs[j]);
             i := 1;
             while i <= Length(r) do  # TODO(later): make this faster
               if r[i] = RightCoset(stabs[j], One(Gcj)) then
                 i := i + 1;
               elif MTSAction(S)(nbr, Representative(r[i])) in X_Y then
                 stabs[j] := ClosureGroup(stabs[j], Representative(r[i]));
                 r        := RightCosets(Gcj, stabs[j]);
                 i        := 1;
               else
                 i := i + 1;
               fi;
             od;
           od;
           found := Union(orbs);
         fi;
       od;

       # 1 Combine intersecting orbits.
       cat := Concatenation(orbs);
       while not IsDuplicateFreeList(cat) do
         i   := 0;
         pos := [];
         while not Size(pos) > 1 do
           i   := i + 1;
           pos := Positions(cat, cat[i]);
         od;

         combined := [];
         new_orbs := [];
         for o in orbs do
           if cat[i] in o then
             Append(combined, o);
           else
             Add(new_orbs, o);
           fi;
         od;
         Add(new_orbs, Set(combined));
         orbs := new_orbs;
         cat  := Concatenation(orbs);
       od;

       # 2 Add generators to link orbits.
       if Size(orbs) <> 1 then
         for orb in orbs{[2 .. Length(orbs)]} do
           g := MTSE(S, orbs[1][1], RepAct(orb[1], orbs[1][1]));
           Add(gens, g);
           Add(gens, g ^ -1);  # Could add less gens here
           check := true;
         od;
       fi;

       # 3 Determine (and add) missing generators of maximal subgroup.
       n     := Size(Gcj);
       sizes := List(stabs, Size);
       Gc1   := _Stab(orbs[1][1]);
       if not n in sizes then
         for i in [1 .. Size(stabs) - 1] do
           if IsSubgroup(stabs[1], stabs[i]) then
             continue;
           fi;
           alpha    := RepAct(orbs[i][1], orbs[1][1]);
           gs       := List(GeneratorsOfGroup(stabs[i]),
                      g -> (alpha ^ -1) * g * alpha);
           stabs[1] := ClosureGroup(stabs[1], gs);
           if stabs[1] = Gc1 then
             break;
           fi;
         od;

         # 3.1 If they are missing then add them.
         for g in GeneratorsOfGroup(Gc1) do
           if not g in stabs[1] then
             Add(gens, MTSE(S, orbs[1][1], g));
             check := true;
           fi;
         od;
       fi;

       # If we haven't added anything yet and nothing is generated by
       # higher D-classes then add an element.
       if not check and Length(nbrs) = 1 then
         Add(gens, MTSE(S, orbs[1][1], One(G)));
       fi;

     fi;
   od;
   return SmallSemigroupGeneratingSet(gens);
end;

InstallMethod(IsomorphismSemigroup,
"for IsMcAlisterTripleSemigroup and a semigroup",
[IsMcAlisterTripleSemigroup, IsSemigroup],
function(_, S)
  local Es, iso_pg, G, H, map, xx, M, iso, yy, ids, cong, grp, hom, map_G, Dcl,
  n, cosets, x, xiny, yinx, D, s, R, e, Ge, h, y_pos, x_pos, act, ah, edgy,
  act2, i, isom;

  if not IsEUnitaryInverseSemigroup(S) then
    ErrorNoReturn("the 2nd argument (a semigroup) is not E-unitary");
  fi;

  Es := IdempotentGeneratedSubsemigroup(S);
  if Size(Es) = 1 then
    iso_pg := IsomorphismPermGroup(S);
    G      := Range(iso_pg);
    map    := g -> PermList(Concatenation([1], ListPerm(g) + 1));
    H      := Group(List(Generators(G), map));
    map    := MappingByFunction(G, H, map);
    xx     := Digraph([[1]]);
    M      := McAlisterTripleSemigroup(H, xx, xx);

    iso := function(s)
      return MTSE(M, 1, (s ^ iso_pg) ^ map);
    end;
    isom := SemigroupHomomorphismByFunctionNC(S, M, iso);
    SetIsBijective(isom, true);
    return isom;
  fi;

  yy  := Digraph(NaturalPartialOrder(Es));
  ids := Elements(Es);

  cong   := MinimumGroupCongruence(S);
  grp    := S / cong;
  iso_pg := IsomorphismPermGroup(grp);  # This takes a long time, e.g. Sym5.
  G      := Range(iso_pg);
  if not IsEmpty(SmallGeneratingSet(G)) then
    G := Group(SmallGeneratingSet(G));
  fi;
  hom   := QuotientSemigroupHomomorphism(grp);
  map_G := CompositionMapping(iso_pg, hom);

  Dcl    := DClasses(S);
  n      := NrDClasses(S);
  cosets := [];
  x      := [];
  xiny   := [];
  yinx   := [];
  for i in [1 .. n] do
    D  := Dcl[i];
    s  := Representative(D);
    R  := RClass(D, s);
    e  := LeftOne(s);
    Ge := Group(List(SmallGeneratingSet(Group(Elements(HClass(D, e)))), g -> g ^
          map_G));
    cosets[i] := RightCosets(G, Ge);
    Append(x, Set(cosets[i], q -> [i, q]));
    for H in HClasses(R) do
      h     := Representative(H);
      y_pos := Position(ids, RightOne(h));
      x_pos := Position(x, [i, Ge * (h ^ map_G)]);

      yinx[y_pos] := x_pos;
      xiny[x_pos] := y_pos;
    od;
  od;

  act := function(a, g)
    local b;
    b := x[a];
    return Position(x, [b[1], b[2] * g]);
  end;

  ah   := ActionHomomorphism(G, [1 .. Size(x)], act);
  edgy := List(DigraphEdges(yy), e -> [yinx[e[1]], yinx[e[2]]]);
  xx   := EdgeOrbitsDigraph(Image(ah), edgy, Size(x));
  xx   := DigraphReflexiveTransitiveClosure(xx);
  yy   := DigraphReflexiveTransitiveClosure(yy);
  SetDigraphVertexLabels(yy, yinx);

  act2 := function(a, g)
    return a ^ (g ^ ah);
  end;

  M := McAlisterTripleSemigroup(G, xx, yy, act2);

  iso := function(s)
    return MTSE(M, yinx[Position(ids, LeftOne(s))], s ^ map_G);
  end;

  isom := SemigroupHomomorphismByFunctionNC(S, M, iso);
  SetIsBijective(isom, true);
  return isom;

end);

InstallMethod(IsWholeFamily, "for a McAlister triple semigroup",
[IsMcAlisterTripleSemigroupElementCollection],
C -> Size(Elements(C)[1]![3]) = Size(C));

#############################################################################
# Methods for McAlister triple elements
#############################################################################

InstallMethod(McAlisterTripleSemigroupElement,
"for a McAlister triple semigroup, pos int, and perm",
[IsMcAlisterTripleSemigroup, IsPosInt, IsMultiplicativeElementWithInverse],
function(S, A, g)
  if not A in DigraphVertexLabels(McAlisterTripleSemigroupSemilattice(S)) then
    ErrorNoReturn("the 2nd argument should be a vertex label of the ",
                  "join-semilattice of the McAlister triple");
  elif not g in McAlisterTripleSemigroupGroup(S) then
    ErrorNoReturn("the 3rd argument must an element of the group of the ",
                  "McAlister triple");
  elif not (McAlisterTripleSemigroupAction(S)(A, g ^ -1) in
      DigraphVertexLabels(McAlisterTripleSemigroupSemilattice(S))) then
    ErrorNoReturn("the arguments do not specify an element of the McAlister ",
                  "triple semigroup");
  fi;
  return Objectify(S!.elementType, [A, g, S]);
end);

InstallMethod(ELM_LIST,
"for a McAlister triple semigroup element rep and a pos int",
[IsMcAlisterTripleSemigroupElementRep, IsPosInt],
function(x, i)
  if i <= 2 then
    return x![i];
  fi;
  ErrorNoReturn("the 2nd argument (a pos. int.) must be at most 2");
end);

InstallMethod(McAlisterTripleSemigroupElementParent,
"for a McAlister triple semigroup element rep",
[IsMcAlisterTripleSemigroupElementRep], x -> x![3]);

InstallMethod(String, "for a McAlister triple semigroup element rep",
[IsMcAlisterTripleSemigroupElementRep],
function(x)
  return Concatenation("MTSE(", String(x![3]), ", ", String(x![1]), ", ",
                       String(x![2]), ")");
end);

# TODO(later) Linebreak hints

InstallMethod(ViewString, "for a McAlister triple semigroup element rep",
[IsMcAlisterTripleSemigroupElementRep],
x -> Concatenation("(", ViewString(x[1]), ", ", ViewString(x[2]), ")"));

InstallMethod(\=, "for two McAlister triple semigroup element reps",
IsIdenticalObj,
[IsMcAlisterTripleSemigroupElementRep, IsMcAlisterTripleSemigroupElementRep],
{x, y} -> x![1] = y![1] and x![2] = y![2] and x![3] = y![3]);

InstallMethod(\*, "for two McAlister triple semigroup element reps",
[IsMcAlisterTripleSemigroupElementRep, IsMcAlisterTripleSemigroupElementRep],
function(x, y)
  local S;
  S := McAlisterTripleSemigroupElementParent(x);
  if not S = McAlisterTripleSemigroupElementParent(y) then
    ErrorNoReturn("the arguments (McAlister triple elements) do not ",
                  "belong to the same McAlister triple semigroup");
  fi;
  return MTSE(S, DigraphVertexLabel(McAlisterTripleSemigroupPartialOrder(S),
               PartialOrderDigraphJoinOfVertices(
                 McAlisterTripleSemigroupPartialOrder(S), x[1],
                 McAlisterTripleSemigroupAction(S)(y[1], x[2]))),
             x[2] * y[2]);
end);

InstallMethod(\<, "for two McAlister triple semigroup element reps",
[IsMcAlisterTripleSemigroupElementRep, IsMcAlisterTripleSemigroupElementRep],
{x, y} -> x[1] < y[1] or (x[1] = y[1] and x[2] < y[2]));

InstallMethod(InverseOp, "for a McAlister triple semigroup element rep",
[IsMcAlisterTripleSemigroupElementRep],
function(x)
  return MTSE(x![3], McAlisterTripleSemigroupAction(x![3])(x[1], Inverse(x[2])),
            Inverse(x[2]));
end);

InstallMethod(\^, "for a McAlister triple semigroup element and a negative int",
[IsMcAlisterTripleSemigroupElement, IsNegInt],
{x, i} -> InverseOp(x ^ - i));

InstallMethod(LeftOne, "for a McAlister triple semigroup element rep",
[IsMcAlisterTripleSemigroupElementRep],
function(x)
  local S;
  S := MTSEParent(x);
  return MTSE(S, x[1], One(MTSGroup(S)));
end);

InstallMethod(RightOne, "for a McAlister triple semigroup element rep",
[IsMcAlisterTripleSemigroupElementRep],
function(x)
  local S;
  S := MTSEParent(x);
  return MTSE(S, MTSAction(S)(x[1], x[2] ^ -1), One(MTSGroup(S)));
end);

InstallMethod(ChooseHashFunction, "for McAlister triple semigroup elements",
[IsMcAlisterTripleSemigroupElement, IsInt],
function(x, hashlen)
  local data;
  data := [ChooseHashFunction(x[1], hashlen),
           ChooseHashFunction(x[2], hashlen),
           hashlen];
  return rec(func := SEMIGROUPS.HashFunctionForMcAlisterTripleSemigroupElements,
             data := data);
end);

SEMIGROUPS.HashFunctionForMcAlisterTripleSemigroupElements := function(x, data)
  return  (17 * data[1].func(x[1], data[1].data)
           + data[2].func(x[2], data[2].data)) mod data[3] + 1;
end;

###############################################################################
# F-inverse Semigroups
###############################################################################
# The connected components of the natural partial order will be the
# congruence classes of the minimum group congruence. Thus we can simply
# check that precisely one of the sources of the digraph of the natural
# partial order is in each connected component.
InstallMethod(IsFInverseMonoid, "for a semigroup", [IsSemigroup],
function(S)
  local comp, po;
  if not IsInverseMonoid(S) then
    return false;
  fi;
  po := Digraph(NaturalPartialOrder(S));
  for comp in DigraphConnectedComponents(po).comps do
    if not Size(Intersection(comp, DigraphSources(po))) = 1 then
      return false;
    fi;
  od;
  return true;
end);

InstallMethod(IsFInverseMonoid, "for a McAlister triple semigroup",
[IsMcAlisterTripleSemigroup], S -> IsMonoid(S) and IsFInverseSemigroup(S));

# A McAlister triple semigroup is F-inverse precisely when X, the partial
# order, is a join-semilattice.
InstallMethod(IsFInverseSemigroup, "for a McAlister triple semigroup",
[IsMcAlisterTripleSemigroup],
S -> IsJoinSemilatticeDigraph(McAlisterTripleSemigroupPartialOrder(S)));

# For an inverse semigroup S we denote \sigma_{e,f}  = \sigma \cap eSf x eSf.
# An E-unitary inverse semigroup is said to be an F-inverse semigroup if
# for each pair of idempotents (e,f): each \sigma_{e,f} class has a maximal
# element. It is simpler to find an isomorphism and use the above method.
InstallMethod(IsFInverseSemigroup, "for a semigroup", [IsSemigroup],
function(S)
  if not IsEUnitaryInverseSemigroup(S) then
    return false;
  fi;
  return IsFInverseSemigroup(AsSemigroup(IsMcAlisterTripleSemigroup, S));
end);

###############################################################################
# E-unitary inverse covers
###############################################################################
InstallMethod(EUnitaryInverseCover,
"for an inverse partial perm semigroup",
[IsInverseSemigroup and IsPartialPermCollection],
function(S)
  local gens, deg, units, G, P, embed, id, cover_gens, s, g, cover, i;
  gens  := GeneratorsOfSemigroup(S);
  deg   := DegreeOfPartialPermSemigroup(S);
  units := [];
  for s in gens do
    Add(units, SEMIGROUPS.PartialPermExtendToPerm(s, deg));
  od;
  G := InverseSemigroup(units);

  P     := DirectProduct(S, G);
  embed := SemigroupDirectProductInfo(P).embedding;
  if not IsMonoid(S) then
    id := PartialPerm([1 .. deg]);
  fi;
  cover_gens := [];
  for i in [1 .. Size(gens)] do
    s := embed(gens[i], 1);
    g := embed(units[i], 2);
    if not IsMonoid(S) then
      g := JoinOfPartialPerms(g, id);
    fi;
    Add(cover_gens, s * g);
  od;

  cover := SemigroupDirectProductInfo(P).projection;
  return SemigroupHomomorphismByFunctionNC(InverseSemigroup(cover_gens),
                                           S,
                                           x -> cover(x, 1));
end);

# This method extends a partial perm 'x' to a permutation of degree 'deg'.
SEMIGROUPS.PartialPermExtendToPerm := function(x, deg)
  local c, i, dom, image;
  image := [];
  # Turn all components into cycles.
  for c in ComponentsOfPartialPerm(x) do
    image[c[1]] := OnPoints(c[1], x);
    if Size(c) > 1 then
      for i in [1 .. Size(c) - 1] do
        image[c[i]] := OnPoints(c[i], x);
      od;
      image[c[i + 1]] := c[1];
    fi;
  od;
  dom := [1 .. deg];
  # Map everything else to itself.
  for i in dom do
    if not IsBound(image[i]) then
      image[i] := i;
    fi;
  od;
  return PartialPerm(dom, image);
end;

InstallMethod(EUnitaryInverseCover, "for a semigroup",
[IsSemigroup],
function(S)
  local cov, iso, T;
  if not IsInverseSemigroup(S) then
    ErrorNoReturn("the argument must be an inverse semigroup");
  fi;
  iso := IsomorphismPartialPermSemigroup(S);
  T   := Range(iso);
  cov := EUnitaryInverseCover(T);
  return CompositionMapping(InverseGeneralMapping(iso), cov);
end);

###############################################################################
# TODO(later):
# 1) Write hash function that works when the MTSGroup is not a perm group.
# 2) Consider hash function for improvements.
# 3) Write OrderIdeal and FindOrderIrreducibleElements for digraphs package
#    (order irreducible elements are the ones which generate the semilattice
#    and order ideals relate to checking condition M2 from Howie).
# 4) Line break hints for printing MTSEs and McAlisterTripleSemigroups.
# 5) Implement EUnitaryInverseCover which covers with a McAlisterTriple
# 6) Improve EUnitaryInverseCover by finding smaller covers
# 7) Implement function that turns MTS over a non-perm group into one that is
#    over a perm group.
# 8) Add to documentation of DigraphReverse returns a digraph where vertex i in
#    the reverse is adjacent to j in the reverse when j is adjacent to i in the
#    original
# 9) Consider shortening McAlisterTripleSemigroupX to McAlisterTripleX
###############################################################################
