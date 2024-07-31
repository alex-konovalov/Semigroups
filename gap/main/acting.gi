############################################################################
##
##  main/acting.gi
##  Copyright (C) 2013-2022                              James D. Mitchell
##
##  Licensing information can be found in the README file of this package.
##
#############################################################################
##

# local declarations . . .

# acting semigroups...

# same method for ideals

InstallMethod(SemigroupData, "for an acting inverse semigroup rep",
[IsInverseActingSemigroupRep], ReturnFail);

# different method for ideals

InstallMethod(SemigroupData, "for an acting semigroup and lambda orb",
[IsActingSemigroup, IsLambdaOrb],
function(S, lambda_orb)
  local gens, data;

  gens := List(GeneratorsOfSemigroup(S), x -> ConvertToInternalElement(S, x));

  data := rec(gens := gens,
              genstoapply := [1 .. Length(gens)],
              graph := [EmptyPlist(Length(gens))],
              ht := HTCreate(gens[1], rec(treehashsize :=
                                          SEMIGROUPS.OptionsRec(S).hashlen)),
              init := false,
              lambda_orb := lambda_orb,
              lambdarhoht := [],
              lenreps := [0],
              orbit := [[,,, FakeOne(gens)]],
              orblookup1 := [],
              orblookup2 := [],
              parent := S,
              pos := 0,
              reps := [],
              repslens := [],
              repslookup := [],
              rholookup := [1],
              schreiergen := [fail],
              schreiermult := [fail],
              schreierpos := [fail],
              stopper := false);

  Objectify(NewType(FamilyObj(S), IsSemigroupData), data);

  return data;
end);

InstallMethod(SemigroupData, "for an acting semigroup",
[IsActingSemigroup], S -> SemigroupData(S, LambdaOrb(S)));

# different method for regular ideals, regular/inverse semigroups, same method
# for non-regular ideals

InstallMethod(\in,
"for a multiplicative element and acting semigroup",
[IsMultiplicativeElement, IsActingSemigroup],
function(x, S)
  local data, ht, lambda, lambdao, l, m, rho, rhoo, lambdarhoht, rholookup,
  new, lookfunc, schutz, ind, reps, repslens, bound, max, membership,
  lambdaperm, n, found, i;

  if ElementsFamily(FamilyObj(S)) <> FamilyObj(x)
      or (IsActingSemigroupWithFixedDegreeMultiplication(S)
          and ActionDegree(x) <> ActionDegree(S))
      or (ActionDegree(x) > ActionDegree(S)) then
    return false;
  elif HasFroidurePin(S) and Position(S, x) <> fail then
    # check if x is already known to be in S
    return true;
  elif HasFroidurePin(S) and IsEnumerated(S) then
    return false;
  elif not (IsMonoid(S) and IsOne(x)) then
    if Length(Generators(S)) > 0
        and ActionRank(S)(x) >
        MaximumList(List(Generators(S), y -> ActionRank(S)(y))) then
      return false;
    fi;
  fi;

  if HasMinimalIdeal(S) then
    if ActionRank(S)(x) < ActionRank(S)(Representative(MinimalIdeal(S))) then
      return false;
    fi;
  fi;

  x := ConvertToInternalElement(S, x);

  data := SemigroupData(S);
  ht := data!.ht;

  # look for lambda!
  lambda := LambdaFunc(S)(x);
  lambdao := LambdaOrb(S);
  if not IsClosedOrbit(lambdao) then
    Enumerate(lambdao, infinity);
  fi;

  l := Position(lambdao, lambda);

  if l = fail then
    return false;
  fi;

  # strongly connected component of lambda orb
  m := OrbSCCLookup(lambdao)[l];

  # make sure lambda of x is in the first place of its scc
  if l <> OrbSCC(lambdao)[m][1] then
    x := x * LambdaOrbMult(lambdao, m, l)[2];
  fi;

  # check if x is an existing R-rep
  if HTValue(ht, x) <> fail then
    return true;
  fi;

  # check if rho is already known
  rho := RhoFunc(S)(x);
  rhoo := RhoOrb(S);
  l := Position(rhoo, rho);
  lambdarhoht := data!.lambdarhoht;
  rholookup := data!.rholookup;

  new := false;

  if l = fail then
    # rho is not already known, so we look for it
    if IsClosedOrbit(rhoo) then
      return false;
    fi;

    lookfunc := {_, x} -> rhoo[rholookup[x[6]]] = rho;

    data := Enumerate(data, infinity, lookfunc);
    l := PositionOfFound(data);

    # rho is not found, so x not in S
    if l = false then
      return false;
    fi;
    l := rholookup[l];
    new := true;
  fi;

  if not IsBound(lambdarhoht[l]) or not IsBound(lambdarhoht[l][m]) then
    new := true;
    # lambda-rho-combination not yet seen
    if IsClosedData(data) then
      return false;
    fi;

    # TODO lambdarhoht should be stored in data
    lookfunc := {data, x} -> IsBound(lambdarhoht[l])
                             and IsBound(lambdarhoht[l][m]);

    data := Enumerate(data, infinity, lookfunc);

    if not IsBound(lambdarhoht[l]) or not IsBound(lambdarhoht[l][m]) then
      return false;
    fi;
  fi;

  schutz := LambdaOrbStabChain(lambdao, m);
  ind := lambdarhoht[l][m];
  # the index of the list of reps with same lambda-rho value as x.

  # if the Schutzenberger group is the symmetric group, then x in S!
  if schutz = true then
    return true;
  fi;

  reps := data!.reps;
  repslens := data!.repslens;

  bound := LambdaBound(S)(LambdaRank(S)(lambda));
  if IsPosInt(bound) then
    max := bound / Size(LambdaOrbSchutzGp(lambdao, m));
  else
    max := bound;
  fi;

  if repslens[m][ind] = max then
    return true;
  fi;

  membership := SchutzGpMembership(S);

  # if schutz is false, then f has to be an R-rep which it is not...
  if schutz <> false then
    # check if x already corresponds to an element of reps[m][ind]
    lambdaperm := LambdaPerm(S);
    for n in [1 .. repslens[m][ind]] do
      if membership(schutz, lambdaperm(reps[m][ind][n], x)) then
        return true;
      fi;
    od;
  elif new and HTValue(ht, x) <> fail then
    return true;
  fi;

  if IsClosedData(data) then
    return false;
  elif repslens[m][ind] < max then
    # enumerate until we find f or finish
    n := repslens[m][ind];
    lookfunc := {data, x} -> repslens[m][ind] > n;
    if schutz = false then
      repeat
        # look for more R-reps with same lambda-rho value
        data := Enumerate(data, infinity, lookfunc);
        found := data!.found;
        if found <> false then
          if repslens[m][ind] = max or x = data[found][4] then
            return true;
          fi;
        fi;
      until found = false;
    else
      repeat
        # look for more R-reps with same lambda-rho value
        data := Enumerate(data, infinity, lookfunc);
        found := data!.found;
        if found <> false then
          if repslens[m][ind] = max then
            return true;
          fi;
          for i in [n + 1 .. repslens[m][ind]] do
            if membership(schutz, lambdaperm(reps[m][ind][i], x)) then
              return true;
            fi;
          od;
          n := repslens[m][ind];
        fi;
      until found = false;
    fi;
  fi;
  return false;
end);

# different for regular/inverse/ideals

InstallMethod(Size, "for an acting semigroup",
[IsActingSemigroup], 2,  # to beat the method for a Rees 0-matrix semigroup
function(S)
  local data, lenreps, repslens, o, scc, size, n, m, i;

  data := Enumerate(SemigroupData(S), infinity, ReturnFalse);
  lenreps  := data!.lenreps;
  repslens := data!.repslens;
  o   := LambdaOrb(S);
  scc := OrbSCC(o);

  size := 0;

  for m in [2 .. Length(scc)] do
    n := Size(LambdaOrbSchutzGp(o, m)) * Length(scc[m]);
    for i in [1 .. lenreps[m]] do
      size := size + n * repslens[m][i];
    od;
  od;

  return size;
end);

# data...

# same method for ideals

InstallMethod(\in, "for a multiplicative element and semigroup data",
[IsMultiplicativeElement, IsSemigroupData],
{f, data} -> Position(data, f) <> fail);

# same method for ideals

InstallMethod(ELM_LIST, "for semigroup data, and pos int",
[IsSemigroupData, IsPosInt], {o, nr} -> o!.orbit[nr]);

# same method for ideals

InstallMethod(Length, "for semigroup data", [IsSemigroupData],
data -> Length(data!.orbit));

# same method for ideals

InstallMethod(Enumerate, "for semigroup data", [IsSemigroupData],
data -> Enumerate(data, infinity, ReturnFalse));

# same method for ideals

InstallMethod(Enumerate, "for semigroup data and limit",
[IsSemigroupData, IsCyclotomic],
{data, limit} -> Enumerate(data, limit, ReturnFalse));

# different method for ideals...

# JDM: this has the same problem as orb in Issue #4, the log is not properly
# formed if the enumeration stops early.

InstallMethod(Enumerate,
"for an semigroup data, limit, and func",
[IsSemigroupData, IsCyclotomic, IsFunction],
function(data, limit, lookfunc)
  local looking, ht, orb, nr, i, graph, reps, repslens, lenreps, lambdarhoht,
  repslookup, orblookup1, orblookup2, rholookup, stopper, schreierpos,
  schreiergen, schreiermult, gens, nrgens, genstoapply, s, lambda,
  lambdaperm, o, oht, scc, lookup, membership, rho, rho_o, rho_orb, rho_nr,
  rho_ht, rho_schreiergen, rho_schreierpos, rho_log, rho_logind, rho_logpos,
  rho_depth, rho_depthmarks, rho_orbitgraph, htadd, htvalue, suc, x, pos, m,
  rhox, l, ind, pt, schutz, data_val, old, j, n;

  if lookfunc <> ReturnFalse then
    looking := true;
  else
    looking := false;
  fi;

  if IsClosedData(data) then
    if looking then
      data!.found := false;
    fi;
    return data;
  fi;

  data!.looking := looking;

  ht := data!.ht;        # so far found R-reps
  orb := data!.orbit;    # the so far found R-reps data
  nr := Length(orb);
  i := data!.pos;        # points in orb in position at most i have descendants
  graph := data!.graph;  # orbit graph of orbit of R-classes under left mult
  reps := data!.reps;    # reps grouped by equal lambda-scc-index and
                         # rho-value-index

  repslens := data!.repslens;       # Length(reps[m][i])=repslens[m][i]
  lenreps := data!.lenreps;         # lenreps[m]=Length(reps[m])

  lambdarhoht := data!.lambdarhoht;  # HTValue(lambdarhoht, [m,l])=position
                                     # in reps[m] of R-reps with
                                     # lambda-scc-index=m and rho-value-index=l

  repslookup := data!.repslookup;  # Position(orb, reps[m][i][j])
                                   # = repslookup[m][i][j]
                                   # = HTValue(ht, reps[m][i][j])

  orblookup1 := data!.orblookup1;  # orblookup1[i] position in reps[m]
                                   # containing orb[i][4] (the R-rep)

  orblookup2 := data!.orblookup2;  # orblookup2[i] position in
                                   # reps[m][orblookup1[i]]
                                   # containing orb[i][4] (the R-rep)

  rholookup := data!.rholookup;    # rholookup[i]=rho-value-index of orb[i][4]

  stopper := data!.stopper;        # stop at this place in the orbit

  # schreier
  schreierpos := data!.schreierpos;
  schreiergen := data!.schreiergen;
  schreiermult := data!.schreiermult;

  # generators
  gens := data!.gens;
  nrgens := Length(gens);
  genstoapply := data!.genstoapply;

  # lambda
  s := data!.parent;
  lambda := LambdaFunc(s);
  lambdaperm := LambdaPerm(s);

  o := data!.lambda_orb;
  oht := o!.ht;
  scc := OrbSCC(o);
  lookup := o!.scc_lookup;

  membership := SchutzGpMembership(s);

  # rho
  rho := RhoFunc(s);
  rho_o := RhoOrb(s);
  rho_orb := rho_o!.orbit;
  rho_nr := Length(rho_orb);
  rho_ht := rho_o!.ht;
  rho_schreiergen := rho_o!.schreiergen;
  rho_schreierpos := rho_o!.schreierpos;

  rho_log := rho_o!.log;
  rho_logind := rho_o!.logind;
  rho_logpos := rho_o!.logpos;
  rho_depth := rho_o!.depth;
  rho_depthmarks := rho_o!.depthmarks;

  rho_orbitgraph := rho_o!.orbitgraph;

  # initialise the data if necessary
  if data!.init = false then
    for i in [2 .. Length(scc)] do
      reps[i] := [];
      repslookup[i] := [];
      repslens[i] := [];
      lenreps[i] := 0;
    od;
    data!.init := true;
    i := data!.pos;
  fi;

  if IsBoundGlobal("ORBC") then
    htadd := HTAdd_TreeHash_C;
    htvalue := HTValue_TreeHash_C;
  else
    htadd := HTAdd;
    htvalue := HTValue;
  fi;

  while nr <= limit and i < nr and i <> stopper do

    i := i + 1;

    #               for the rho-orbit               #
    if rholookup[i] >= rho_depthmarks[rho_depth + 1] then
      rho_depth := rho_depth + 1;
      rho_depthmarks[rho_depth + 1] := rho_nr + 1;
    fi;
    rho_logind[rholookup[i]] := rho_logpos;
    suc := false;
    #                                               #

    for j in genstoapply do  # JDM
      x := gens[j] * orb[i][4];
      pos := htvalue(oht, lambda(x));
      m := lookup[pos];   # lambda-value-scc-index

      # put lambda(x) in the first position in its scc
      if pos <> scc[m][1] then
        x := x * LambdaOrbMult(o, m, pos)[2];
      fi;

      rhox := rho(x);
      l := htvalue(rho_ht, rhox);

      if l = fail then  # new rho-value, new R-rep

        #                update rho-orbit             #
        rho_nr := rho_nr + 1;
        l := rho_nr;
        rho_orb[rho_nr] := rhox;
        htadd(rho_ht, rhox, rho_nr);

        rho_orbitgraph[rho_nr] := EmptyPlist(nrgens);
        rho_orbitgraph[rholookup[i]][j] := rho_nr;

        rho_schreiergen[rho_nr] := j;
        rho_schreierpos[rho_nr] := rholookup[i];

        suc := true;
        rho_log[rho_logpos] := j;
        rho_log[rho_logpos + 1] := rho_nr;
        rho_logpos := rho_logpos + 2;
        rho_o!.logpos := rho_logpos;
        #                                              #

        nr := nr + 1;
        lenreps[m] := lenreps[m] + 1;
        ind := lenreps[m];
        lambdarhoht[l] := [];
        lambdarhoht[l][m] := ind;

        reps[m][ind] := [x];
        repslookup[m][ind] := [nr];
        repslens[m][ind] := 1;

        orblookup1[nr] := ind;
        orblookup2[nr] := 1;

        pt := [s, m, o, x, false, nr];
        # semigroup, lambda orb scc index, lambda orb, rep,
        # IsGreensClassNC, index in orbit

      elif not IsBound(lambdarhoht[l]) then
        # old rho-value, but new lambda-rho-combination
        # update rho orbit graph
        rho_orbitgraph[rholookup[i]][j] := l;
        nr := nr + 1;
        lenreps[m] := lenreps[m] + 1;
        ind := lenreps[m];
        lambdarhoht[l] := [];
        lambdarhoht[l][m] := ind;

        reps[m][ind] := [x];
        repslookup[m][ind] := [nr];
        repslens[m][ind] := 1;

        orblookup1[nr] := ind;
        orblookup2[nr] := 1;

        pt := [s, m, o, x, false, nr];
      elif not IsBound(lambdarhoht[l][m]) then
        # old rho-value, but new lambda-rho-combination

        # update rho orbit graph
        rho_orbitgraph[rholookup[i]][j] := l;

        nr := nr + 1;
        lenreps[m] := lenreps[m] + 1;
        ind := lenreps[m];
        lambdarhoht[l][m] := ind;

        reps[m][ind] := [x];
        repslookup[m][ind] := [nr];
        repslens[m][ind] := 1;

        orblookup1[nr] := ind;
        orblookup2[nr] := 1;

        pt := [s, m, o, x, false, nr];
      else
        # old lambda-rho combination
        ind := lambdarhoht[l][m];
        pt := [s, m, o, x, false, nr + 1];

        # check membership in Schutzenberger group via stabiliser chain
        schutz := LambdaOrbStabChain(o, m);

        if schutz = true then
          # the Schutzenberger group is the symmetric group
          graph[i][j] := repslookup[m][ind][1];
          rho_orbitgraph[rholookup[i]][j] := l;
          continue;
        else
          if schutz = false then
            # the Schutzenberger group is trivial
            data_val := htvalue(ht, x);
            if data_val <> fail then
              graph[i][j] := data_val;
              rho_orbitgraph[rholookup[i]][j] := l;
              continue;
            fi;
          else
            # the Schutzenberger group is neither trivial nor symmetric group
            old := false;
            for n in [1 .. repslens[m][ind]] do
              if membership(schutz, lambdaperm(reps[m][ind][n], x)) then
                old := true;
                graph[i][j] := repslookup[m][ind][n];
                rho_orbitgraph[rholookup[i]][j] := l;
                break;
              fi;
            od;
            if old then
              continue;
            fi;
          fi;
          nr := nr + 1;
          repslens[m][ind] := repslens[m][ind] + 1;
          reps[m][ind][repslens[m][ind]] := x;
          repslookup[m][ind][repslens[m][ind]] := nr;
          orblookup1[nr] := ind;
          orblookup2[nr] := repslens[m][ind];
          # update rho orbit graph and rholookup
          rho_orbitgraph[rholookup[i]][j] := l;
        fi;
      fi;
      rholookup[nr] := l;  # orb[nr] has rho-value in position l of the rho-orb

      orb[nr] := pt;
      schreierpos[nr] := i;     # orb[nr] is obtained from orb[i]
      schreiergen[nr] := j;     # by multiplying by gens[j]
      schreiermult[nr] := pos;  # and ends up in position <pos> of
                                # its lambda orb
      htadd(ht, x, nr);
      graph[nr] := EmptyPlist(nrgens);
      graph[i][j] := nr;

      # are we looking for something?
      if looking then
        # did we find it?
        data!.pos := i - 1;
        if lookfunc(data, pt) then
          data!.found := nr;
          rho_o!.depth := rho_depth;
          return data;
        fi;
      fi;
    od;

    # for the rho-orbit
    if suc then
      rho_log[rho_logpos - 2] := -rho_log[rho_logpos - 2];
    else
      rho_logind[rholookup[i]] := 0;
    fi;

  od;

  # for the data-orbit
  data!.pos := i;

  if looking then
    data!.found := false;
  fi;
  if nr = i then
    SetFilterObj(data, IsClosedData);
    SetFilterObj(rho_o, IsClosedOrbit);
    rho_o!.orbind := [1 .. rho_nr];
  fi;

  # for the rho-orbit
  if i <> 0 then
    rho_o!.pos := rholookup[i];
    rho_o!.depth := rho_depth;
  fi;

  return data;
end);

# not currently applicable for ideals

InstallMethod(OrbitGraph, "for semigroup data",
[IsSemigroupData], data -> data!.graph);

# not currently applicable for ideals

InstallMethod(OrbitGraphAsSets, "for semigroup data",
[IsSemigroupData], data -> List(data!.graph, Set));

# returns the index of the representative of the R-class containing x in the
# parent of data. Note that this depends on the state of the data, it only
# tells you if it is there already, it doesn't try to find it.

# same method for ideals

InstallMethod(Position,
"for semigroup data, multiplicative element, and zero cyc",
[IsSemigroupData, IsMultiplicativeElement, IsZeroCyc],
function(data, x, n)
  local S, o, l, m, val, schutz, lambdarhoht, ind, repslookup, reps, repslens,
  membership, lambdaperm;

  S := data!.parent;
  x := ConvertToInternalElement(S, x);
  o := data!.lambda_orb;
  l := Position(o, LambdaFunc(S)(x));

  if l = fail then
    return fail;
  fi;

  m := OrbSCCLookup(o)[l];

  if l <> OrbSCC(o)[m][1] then
    x := x * LambdaOrbMult(o, m, l)[2];
  fi;

  val := HTValue(data!.ht, x);
  schutz := LambdaOrbStabChain(o, m);

  if val <> fail then
    return val;
  elif schutz = false then
    return fail;
  fi;

  l := Position(RhoOrb(S), RhoFunc(S)(x));

  if l = fail then
    return fail;
  fi;

  lambdarhoht := data!.lambdarhoht;

  if not IsBound(lambdarhoht[l]) or not IsBound(lambdarhoht[l][m]) then
    return fail;
  fi;

  ind := lambdarhoht[l][m];
  repslookup := data!.repslookup[m][ind];

  if schutz = true then
    return repslookup[1];
  fi;

  reps := data!.reps[m][ind];
  repslens := data!.repslens[m][ind];
  membership := SchutzGpMembership(S);
  lambdaperm := LambdaPerm(S);

  for n in [1 .. repslens] do
    if membership(schutz, lambdaperm(reps[n], x)) then
      return repslookup[n];
    fi;
  od;
  return fail;
end);

InstallMethod(PositionOfFound, "for semigroup data",
[IsSemigroupData],
function(data)
  if not(data!.looking) then
    ErrorNoReturn("not looking for anything");
  fi;
  return data!.found;
end);

# same method for ideals

BindGlobal("SizeOfSemigroupData",
function(data)
  local lenreps, repslens, o, scc, size, n, m, i;

  if not IsSemigroupData(data) then
    ErrorNoReturn("the argument must be a semigroup data object");
  elif not data!.init then
    return 0;
  fi;

  lenreps := data!.lenreps;
  repslens := data!.repslens;
  o := LambdaOrb(data!.parent);
  scc := OrbSCC(o);

  size := 0;
  for m in [2 .. Length(scc)] do
    n := Size(LambdaOrbSchutzGp(o, m)) * Length(scc[m]);
    for i in [1 .. lenreps[m]] do
      size := size + n * repslens[m][i];
    od;
  od;
  return size;
end);

# different method for ideals

InstallMethod(ViewObj, [IsSemigroupData],
function(data)
  Print("<");

  if IsClosedData(data) then
    Print("closed ");
  else
    Print("open ");
  fi;
  Print("semigroup ");

  Print("data with ", Length(data!.orbit) - 1, " reps, ",
        Length(LambdaOrb(data!.parent)) - 1, " lambda-values, ",
        Length(RhoOrb(data!.parent)) - 1, " rho-values>");
  return;
end);

# we require a fake one in the case that the objects we are dealing with don't
# have one.

InstallMethod(String, "for the universal fake one",
[SEMIGROUPS_IsUniversalFakeOne], obj -> "<universal fake one>");

InstallMethod(\*,
"for the universal fake one and a multiplicative element",
[SEMIGROUPS_IsUniversalFakeOne, IsMultiplicativeElement],
{_, y} -> y);

InstallMethod(\*,
"for a multiplicative element and the universal fake one",
[IsMultiplicativeElement, SEMIGROUPS_IsUniversalFakeOne],
{x, _} -> x);

InstallMethod(\<, "for the universal fake one and a multiplicative element",
[SEMIGROUPS_IsUniversalFakeOne, IsMultiplicativeElement], ReturnTrue);

InstallMethod(\<, "for a multiplicative element and the universal fake one",
[IsMultiplicativeElement, SEMIGROUPS_IsUniversalFakeOne], ReturnFalse);
