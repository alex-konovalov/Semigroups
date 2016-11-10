if not IsBound(EN_SEMI_ENUMERATE) then
  InstallMethod(Enumerate, "for generic semigroup data, cyclotomic, function",
  [IsGenericSemigroupData, IsCyclotomic, IsFunction],
  function(data, limit, lookfunc)
    local looking, found, i, nr, len, one, stopper, nrrules, elts, gens,
    nrgens, genstoapply, genslookup, lenindex, first, final, prefix, suffix,
    words, right, left, reduced, ht, rules, htadd, htvalue, stop, lentoapply,
    b, s, r, new, newword, val, p, j, k;

    if lookfunc <> ReturnFalse then
      looking := true;
      # only applied to new elements, not old ones!!!
      data!.found := false;
      # in case we previously looked for something and found it
    else
      looking := false;
    fi;

    found := false;

    i := data!.pos;
    # current position we are about to apply gens to .. .
    nr := data!.nr;
    # number of elements found so far .. .

    if i > nr then
      SetFilterObj(data, IsClosedData);
      return data;
    fi;

    len := data!.len;
    # current word length
    one := data!.one;
    # < elts[one] > is the mult. neutral element
    stopper := data!.stopper;
    # stop when we have applied generators to elts[stopper]
    nrrules := data!.nrrules;
    # Length(rules)

    elts := data!.elts;
    # the so far enumerated elements
    gens := data!.gens;
    # the generators
    nrgens := Length(gens);
    genstoapply := data!.genstoapply;
    # list of indices of generators to apply in inner loop
    genslookup := data!.genslookup;
    # genslookup[i] = Position(elts, gens[i])
    # this is not always < i + 1 > !
    lenindex := data!.lenindex;
    # lenindex[len] = position in < words > and < elts > of
    # first element of length < len >
    first := data!.first;
    # elts[i] = gens[first[i]] * elts[suffix[i]], first letter
    final := data!.final;
    # elts[i] = elts[prefix[i]] * gens[final[i]]
    prefix := data!.prefix;
    # see final, 0 if prefix is empty i.e. elts[i] is a gen
    suffix := data!.suffix;
    # see first, 0 if suffix is empty i.e. elts[i] is a gen
    words := data!.words;
    # words[i] is a word in the gens equal to elts[i]

    right := data!.right;
    # elts[right[i][j]] = elts[i] * gens[j], right Cayley graph
    left := data!.left;
    # elts[left[i][j]] = gens[j] * elts[i], left Cayley graph
    reduced := data!.reduced;
    # words[right[i][j]] is reduced if reduced[i][j] = true
    ht := data!.ht;
    # HTValue(ht, x) = Position(elts, x)
    rules := data!.rules;
    # the relations

    if IsBoundGlobal("ORBC") then
      htadd := HTAdd_TreeHash_C;
      htvalue := HTValue_TreeHash_C;
    else
      htadd := HTAdd;
      htvalue := HTValue;
    fi;

    stop := false;

    while i <= nr and not stop do
      lentoapply := [1 .. len];
      while i <= nr and Length(words[i]) = len and not stop do
        b := first[i];
        s := suffix[i];
        # elts[i] = gens[b] * elts[s]
        for j in genstoapply do # consider < elts[i] * gens[j] >
          if s <> 0 and not reduced[s][j] then
            # < elts[s] * gens[j] > is not reduced
            r := right[s][j];
            # elts[r] = elts[s] * gens[j]
            if prefix[r] <> 0 then
              right[i][j] := right[left[prefix[r]][b]][final[r]];
              # elts[i] * gens[j] = gens[b] * elts[prefix[r]] * gens[final[r]];
              # reduced[i][j] = ([words[i], j] = words[right[i][j]])
              reduced[i][j] := false;
            elif r = one then
              # < elts[r] > is the identity
              right[i][j] := genslookup[b];
              reduced[i][j] := true;
              # < elts[i] * gens[j] = b > and it is reduced
            else # prefix[r] = 0, i.e. elts[r] is one of the generators
              right[i][j] := right[genslookup[b]][final[r]];
              # elts[i] * gens[j] = gens[b] * gens[final[r]];
              # reduced[i][j] = ([words[i], j] = words[right[i][j]])
              reduced[i][j] := false;
            fi;
          else # < elts[s] * gens[j] > is reduced
            new := elts[i] * gens[j];
            # < newword >= < elts[i] * gens[j] >
            newword := words[i]{lentoapply};
            # better than ShallowCopy
            newword[len + 1] := j;
            # using Concatenate here is very bad!
            val := htvalue(ht, new);

            if val <> fail then
              nrrules := nrrules + 1;
              rules[nrrules] := [newword, words[val]];
              right[i][j] := val;
              # < newword > and < words[val] > represent the same element (but
              # are not equal) and so < newword > is not reduced

            else # < new > is a new element!
              nr := nr + 1;
              htadd(ht, new, nr);

              if one = false
                  and ForAll(gens, y -> new * y = y and y * new = y) then
                one := nr;
              fi;

              if s <> 0 then
                suffix[nr] := right[s][j];
              else
                suffix[nr] := genslookup[j];
              fi;

              elts[nr] := new;
              words[nr] := newword;
              first[nr] := b;
              final[nr] := j;
              prefix[nr] := i;
              right[nr] := EmptyPlist(nrgens);
              left[nr] := EmptyPlist(nrgens);
              reduced[nr] := BlistList(genstoapply, []);

              right[i][j] := nr;
              reduced[i][j] := true;

              if looking and (not found) and lookfunc(data, nr) then
                found := true;
                stop := true;
                data!.found := nr;
              else
                stop := nr >= limit;
              fi;
            fi;
          fi;
        od;
        # finished applying gens to < elts[i] >
        stop := (stop or i = stopper);
        i := i + 1;
      od;
      # finished words of length < len > or < looking and found >
      if i > nr or Length(words[i]) <> len then
        # process words of length < len > into < left >
        if len > 1 then
          for j in [lenindex[len] .. i - 1] do
            # loop over all words of length < len - 1 >
            p := prefix[j];
            b := final[j];
            for k in genstoapply do
              left[j][k] := right[left[p][k]][b];
              # gens[k] * elts[j] = (gens[k] * elts[p]) * gens[b]
            od;
          od;
        elif len = 1 then
          for j in [lenindex[len] .. i - 1] do
            # loop over all words of length < 1 >
            b := final[j];
            for k in genstoapply do
              left[j][k] := right[genslookup[k]][b];
              # gens[k] * elts[j] = elts[k] * gens[b]
            od;
          od;
        fi;
        len := len + 1;
        lenindex[len] := i;
      fi;
    od;

    data!.nr := nr;
    data!.nrrules := nrrules;
    data!.one := one;
    data!.pos := i;
    data!.len := len;

    if i > nr then
      SetFilterObj(data, IsClosedData);
      # Unbind some of the unnecessary components here!
    fi;

    return data;
  end);
fi;
gap> G := Range(IsomorphismFpGroup(AlternatingGroup(5)));
<fp group of size 60 on the generators [ A_5.1, A_5.2 ]>
gap> IsomorphismFpSemigroup(G);
MappingByFunction( <fp group of size 60 on the generators
[ A_5.1, A_5.2 ]>, <fp semigroup on the generators [ s1, s2, s3, s4, s5
 ]>, function( x ) ... end, function( x ) ... end )
gap> map;
Error, Variable: 'map' must have a value
not in any function at *stdin*:3
gap> BruteForceIsoCheck(last);
true
gap> BruteForceInverseCheck(last2);
true
gap>

# Argh a similar method already exists in the library.

#InstallMethod(IsomorphismFpSemigroup, "for an fp group", 
#[IsFpGroup], 
#function(G)
#  local n, F, id, rels, map, S, inv, i, rel;
#
#  n  := Length(GeneratorsOfGroup(G));
#  F  := FreeSemigroup(2 * n + 1);
#  id := F.(2 * n + 1);
#  rels := [[id * id, id]];
#
#  for i in [1 .. n] do 
#    Add(rels, [F.(i) * id, F.(i)]);
#    Add(rels, [id * F.(i), F.(i)]);
#    Add(rels, [F.(i) * F.(i + n), id]);
#    Add(rels, [F.(i + n) * F.(i), id]);
#  od;
#
#  for i in [1 .. n] do 
#    Add(rels, [F.(i + n) * id, F.(i + n)]);
#    Add(rels, [id * F.(i + n), F.(i + n)]);
#  od;
#
#  map := function(U, word)
#    local ext, out, i;
#
#    ext := ExtRepOfObj(word);
#    if Length(ext) = 0 then 
#      return U.(2 * n + 1);
#    elif ext[2] > 0 then 
#      out := U.(ext[1]) ^ ext[2];
#    else 
#      out := U.(ext[1] + n) ^ -ext[2];
#    fi;
#
#    for i in [3, 5 .. Length(ext) - 1] do
#      if ext[i + 1] > 0 then 
#        out := out * U.(ext[i]) ^ ext[i + 1];
#      else 
#        out := out * U.(ext[i] + n) ^ -ext[i + 1];
#      fi;
#    od;
#    return out;
#  end;
#
#  for rel in RelatorsOfFpGroup(G) do
#    Add(rels, [map(F, rel), id]);
#  od;
#  
#  S := F / rels;
#  UseIsomorphismRelation(G, S);
#  
#  inv := function(x)
#    local ext, out, i;
#
#    ext := ExtRepOfObj(UnderlyingElement(x));
#
#    if ext[1] <= n then 
#      out := G.(ext[1]) ^ ext[2];
#    elif ext[1] <= 2 * n then 
#      out := G.(ext[1] - n) ^ -ext[2];
#    else 
#      out := One(G);
#    fi;
#
#    for i in [3, 5 .. Length(ext) - 1] do
#      if ext[i] <= n then 
#        out := out * G.(ext[i]) ^ ext[i + 1];
#      elif ext[i] <= 2 * n then 
#        out := out * G.(ext[i] - n) ^ -ext[i + 1];
#      fi;
#    od;
#
#    return out;
#  end;
#  return MagmaIsomorphismByFunctionsNC(G, S, x -> map(S, x), inv);
#end);


# TODO redo this

#InstallGlobalFunction(SEMIGROUPS.TestAll,
#function()
#  local dir_str, tst, dir, omit, filesplit, test, stringfile, str, filename;
#
#  Print("Reading all .tst files in the directory semigroups/tst/...\n\n");
#  dir_str :=
#   Concatenation(PackageInfo("semigroups")[1]!.InstallationPath, "/tst");
#  tst := DirectoryContents(dir_str);
#  dir := Directory(dir_str);
#
#  omit := SEMIGROUPS.OmitFromTests;
#
#  if Length(omit) > 0 then
#    Print("not testing files containing the strings");
#    for str in omit do
#      Print(", \"", str, "\"");
#    od;
#    Print(" . . .\n\n");
#  fi;
#
#  for filename in tst do
#
#    filesplit := SplitString(filename, ".");
#    if Length(filesplit) >= 2 and filesplit[Length(filesplit)] = "tst" then
#      test := true;
#      stringfile := StringFile(Concatenation(dir_str, "/", filename));
#      for str in omit do
#        if PositionSublist(stringfile, str) <> fail then
#          Print("not testing ", filename, ", it contains a test involving ",
#                str, ", which will not work . . .\n\n");
#          test := false;
#          break;
#        fi;
#      od;
#      if test then
#        Print("reading ", dir_str, "/", filename, " . . .\n");
#        Test(Filename(dir, filename));
#        Print("\n");
#      fi;
#    fi;
#  od;
#  return;
#end);
BindGlobal("TikzBipartitionRight",
function(x)
  return Concatenation(SEMIGROUPS.TikzInit,
                       "\\begin{center}\n",
                       TikzStringForBipartition(x),
                       "\\bigskip\n",
                       TikzStringForBlocks(RightBlocks(x), "none", "bottom"),
                       "\\end{center}\n",
                       SEMIGROUPS.TikzEnd);
end);

#

BindGlobal("TikzBipartitionLeft",
function(f)
  return Concatenation(SEMIGROUPS.TikzInit,
                       "\\begin{center}\n",
                       TikzStringForBipartition(f),
                       "\\bigskip\n",
                       TikzStringForBlocks(LeftBlocks(f), "none", "top"),
                       "\\end{center}\n",
                       SEMIGROUPS.TikzEnd);
end);

#

BindGlobal("TikzBipartitionLeftRight",
function(f)
  return Concatenation(SEMIGROUPS.TikzInit,
                       "\\begin{center}\n",
                       TikzStringForBlocks(LeftBlocks(f), "none", "top"),
                       "\\bigskip\n",
                       TikzStringForBipartition(f),
                       "\\bigskip\n",
                       TikzStringForBlocks(RightBlocks(f), "none", "bottom"),
                       "\\end{center}\n",
                       SEMIGROUPS.TikzEnd);
end);

#
# for bipartition

BindGlobal("TikzRightBlocks",
function(x)
  return Concatenation(SEMIGROUPS.TikzInit,
                       TikzStringForBlocks(RightBlocks(x), "bottom", "bottom"),
                       SEMIGROUPS.TikzEnd);
end);

# for bipartition

BindGlobal("TikzLeftBlocks",
function(f)
  return Concatenation(SEMIGROUPS.TikzInit,
                       TikzStringForBlocks(LeftBlocks(f), "top", "top"),
                       SEMIGROUPS.TikzEnd);
end);


#InstallMethod(IsAbundantSemigroup, "for a trans. semigroup",
#[IsTransformationSemigroup and HasGeneratorsOfSemigroup],
#function(s)
#  local iter, n, ht, ht_o, reg, i, data, f, ker, val, o, scc;
#
#  Info(InfoWarning, 1, "this will sometimes return a false positive.");
#
#  if HasIsRegularSemigroup(s) and IsRegularSemigroup(s) then
#    Info(InfoSemigroups, 2, "semigroup is regular");
#    return true;
#  fi;
#
#  iter:=IteratorOfRClassData(s); n:=ActionDegree(s);
#  ht:=HTCreate([1..n], rec(hashlen:=s!.opts!.hashlen!.S));
#  ht_o:=HTCreate([1,1,1,1], rec(hashlen:=s!.opts!.hashlen!.S));
#  reg:=[]; i:=0;
#
#  repeat
#    repeat #JDM this should become an method for IteratorOfRStarClasses
#           # and IsAbundantRClass...
#      data:=NextIterator(iter);
#    until HTValue(ht_o, data{[1,2,4,5]})=fail or IsDoneIterator(iter);
#    if not IsDoneIterator(iter) then
#      HTAdd(ht_o, data{[1,2,4,5]}, true);
#
#      #f:=RClassRepFromData(s, data); ker:=CanonicalTransSameKernel(f);
#      val:=HTValue(ht, ker);
#
#      if val=fail then #new kernel
#        i:=i+1; HTAdd(ht, ker, i);
#        val:=i; reg[val]:=false;
#      fi;
#
#      if reg[val]=false then #old kernel
#        #o:=ImageOrbitFromData(s, data); scc:=ImageOrbitSCCFromData(s, data);
#        reg[val]:=ForAny(scc, j-> IsInjectiveListTrans(o[j], ker));
#      fi;
#    fi;
#  until IsDoneIterator(iter);
#
#  return ForAll(reg, x-> x);
#end);

#InstallMethod(IsAdequateSemigroup,
#"for acting semigroup with generators",
#[IsActingSemigroup and HasGeneratorsOfSemigroup],
#s-> IsAbundantSemigroup(s) and IsBlockGroup(s));

# Here lies some dead code, may it rest in peace

#InstallMethod(JoinOfBlocks, "for blocks",
#[IsBlocks, IsBlocks],
#function(blocks1, blocks2)
#  local n, nrblocks1, nrblocks2, fuse, fuseit, x, y, lookup, nr, out, j, i;
#
#  n := DegreeOfBlocks(blocks1);
#
#  if NrBlocks(blocks1) = 1 then
#    return blocks1;
#  elif NrBlocks(blocks2) = 1 then
#    return blocks2;
#  fi;
#
#  nrblocks1 := NrBlocks(blocks1);
#  blocks1 := blocks1!.blocks;
#  blocks2 := blocks2!.blocks;
#
#  fuse := [1 .. nrblocks1 + blocks2[1]];
#
#  fuseit := function(i)
#    while fuse[i] < i do
#      i := fuse[i];
#    od;
#    return i;
#  end;
#
#  for i in [2 .. n + 1] do
#    x := fuseit(blocks1[i]);
#    y := fuseit(blocks2[i] + nrblocks1);
#    if x <> y then
#      if x < y then
#        fuse[y] := x;
#      else
#        fuse[x] := y;
#      fi;
#    fi;
#  od;
#
#  lookup := [];
#  out := [0];
#
#  for i in [2 .. n + 1] do
#    x := fuseit(blocks1[i]);
#    if not IsBound(lookup[x]) then
#      out[1] := out[1] + 1;
#      out[n + 1 + out[1]] := 1;
#      lookup[x] := out[1];
#    fi;
#    out[i] := lookup[x];
#  od;
#
#  return BlocksByIntRepNC(out);
#end);

BindGlobal("FuseLeftBlocks",
function(blocks, f)
  local n, fblocks, nrblocks, nrfblocks, fuse, fuseit, x, y, i;

  n := DegreeOfBlocks(blocks);
  fblocks := f!.blocks;
  nrblocks := NrBlocks(blocks);
  nrfblocks := NrBlocks(f);

  fuse := [1 .. nrblocks + nrfblocks];
  fuseit := function(i)
    while fuse[i] < i do
      i := fuse[i];
    od;
    return i;
  end;

  for i in [1 .. n] do
    x := fuseit(blocks[i]);
    y := fuseit(fblocks[n + i] + nrblocks);
    if x <> y then
      if x < y then
        fuse[y] := x;
      else
        fuse[x] := y;
      fi;
    fi;
  od;
  return fuseit;
end);

DeclareGlobalFunction("BlocksByExtRep");

InstallGlobalFunction(BlocksByExtRep,
function(ext)
  local n, tab, out, nr, i;

  n := Length(ext);
  tab := EmptyPlist(n);
  out := EmptyPlist(n + 2);
  out[n + 2] := [];
  nr := 0;

  for i in [1 .. n] do
    if ext[i] < 0 then
      out[i + 1] := -1 * ext[i];
      out[n + 1 + out[i + 1]] := 0;
    else
      out[i + 1] := ext[i];
      out[n + 1 + ext[i]] := 1;
    fi;
    if not IsBound(tab[out[i + 1]]) then
      tab[out[i + 1]] := true;
      nr := nr + 1;
    fi;
  od;

  out[1] := nr;
  out := Objectify(BlocksType, rec(blocks := out));
  return out;
end);

#

#Subsemigroups:=function(R)
#  local max, o, U, V;
#
#  max:=Set(MaximalSubsemigroups(R));
#  o:=ShallowCopy(max);
#
#  for U in o do
#    if Size(U)>1 then
#      for V in MaximalSubsemigroups(U) do
#        if not V in max then
#          AddSet(max, V);
#          Add(o, V);
#        fi;
#      od;
#    fi;
#  od;
#
#  return Concatenation(max, [R]);
#end;
#
##
#
#NumberOfSubsemigroups:=function(R)
#  local max, o, U, V, count;
#
#  max:=Set(MaximalSubsemigroups(R));
#  o:=ShallowCopy(max);
#  count:=Length(o)+1; # +1 for R itself
#
#  while not IsEmpty(o) do
#    U:=o[1];
#    if Size(U)>1 then
#      for V in MaximalSubsemigroups(U) do
#        if not V in max then
#          AddSet(max, V);
#          Add(o, V);
#          count:=count+1;
#          Print(count,"\n");
#        fi;
#      od;
#    fi;
#    Remove(o,1);
#  od;
#
#  return count;
#end;

DeclareSynonym("IsMatrixSemigroup", IsSemigroup and IsRingElementCollCollColl);
DeclareOperation("OneMutable", [IsRingElementCollCollColl]);

# a better method for MinimalIdeal of a simple semigroup.

InstallMethod(OneMutable, "for ring element coll coll coll",
[IsRingElementCollCollColl], x -> One(Representative(x)));

InstallMethod(IsGroupAsSemigroup, "for a matrix semigroup",
[IsMatrixSemigroup],
S -> IsGroupAsSemigroup(Range(IsomorphismTransformationSemigroup(S))));

# LambdaRhoLookup(d)[i]=j if orbit[j][4] in reps[i] (orbit[j][4] is one of the
# R-reps of the D-class d) and LambdaRhoLookup(d) is only bound for those
# indices i where there is an R-rep in the scc of the D-class in reps[i]

DeclareAttribute("LambdaRhoLookup", IsGreensDClass and
IsActingSemigroupGreensClass);

# this won't work for ideals, but isn't currently used for anything

InstallMethod(LambdaRhoLookup, "for a D-class of an acting semigroup",
[IsGreensDClass and IsActingSemigroupGreensClass],
function(d)
  local data, orb_scc, orblookup1, orblookup2, out, i;

  data := SemigroupData(Parent(d));

  # scc of R-reps corresponding to d
  orb_scc := SemigroupDataSCC(d);

  # positions in reps containing R-reps in d
  orblookup1 := data!.orblookup1;
  orblookup2 := data!.orblookup2;

  out := [];
  for i in orb_scc do
    if not IsBound(out[orblookup1[i]]) then
      out[orblookup1[i]] := [];
    fi;
    Add(out[orblookup1[i]], orblookup2[i]);
  od;

  return out;
end);

  # JDM below is an example of how to use FIND_SEMIGROUP, it used to be used in
  # Position . . .

  #lookfunc := function(data, i)
  #  return data!.elts[i] = x;
  #end;

  #FIND_SEMIGROUP(data, lookfunc, 1, infinity);

  #if data!.found <> false then
  #  return data!.found;
  #fi;

  #return fail;

# JDM the below works just fine currently not supporting non-compiled kernel.

if not IsBound(ENUMERATE_SEMIGROUP) then
  InstallMethod(Enumerate, "for generic semigroup data, cyclotomic, function",
  [IsGenericSemigroupData, IsCyclotomic, IsFunction],
  function(data, limit, lookfunc)
    local looking, found, i, nr, len, one, stopper, nrrules, elts, gens,
    nrgens, genstoapply, genslookup, lenindex, first, final, prefix, suffix,
    words, right, left, reduced, ht, rules, htadd, htvalue, stop, lentoapply,
    b, s, r, new, newword, val, p, j, k;

    if lookfunc <> ReturnFalse then
      looking := true;              # only applied to new elements, not old ones!!!
      data!.found := false;         # in case we previously looked for something and found it
    else
      looking := false;
    fi;

    found := false;

    i  := data!.pos;                    # current position we are about to apply gens to ...
    nr := data!.nr;                     # number of elements found so far...

    if i > nr then
      SetFilterObj(data, IsClosedData);
      return data;
    fi;

    len         := data!.len;         # current word length
    one         := data!.one;         # <elts[one]> is the mult. neutral element
    stopper     := data!.stopper;     # stop when we have applied generators to elts[stopper]
    nrrules     := data!.nrrules;     # Length(rules)

    elts        := data!.elts;        # the so far enumerated elements
    gens        := data!.gens;        # the generators
    nrgens      := Length(gens);
    genstoapply := data!.genstoapply; # list of indices of generators to apply in inner loop
    genslookup  := data!.genslookup;  # genslookup[i]=Position(elts, gens[i])
                                      # this is not always <i+1>!
    lenindex    := data!.lenindex;    # lenindex[len]=position in <words> and <elts> of
                                      # first element of length <len>
    first       := data!.first;       # elts[i]=gens[first[i]]*elts[suffix[i]], first letter
    final       := data!.final;       # elts[i]=elts[prefix[i]]*gens[final[i]]
    prefix      := data!.prefix;      # see final, 0 if prefix is empty i.e. elts[i] is a gen
    suffix      := data!.suffix;      # see first, 0 if suffix is empty i.e. elts[i] is a gen
    words       := data!.words;       # words[i] is a word in the gens equal to elts[i]
    right       := data!.right;       # elts[right[i][j]]=elts[i]*gens[j], right Cayley graph
    left        := data!.left;        # elts[left[i][j]]=gens[j]*elts[i], left Cayley graph
    reduced     := data!.reduced;     # words[right[i][j]] is reduced if reduced[i][j]=true
    ht          := data!.ht;          # HTValue(ht, x)=Position(elts, x)
    rules       := data!.rules;       # the relations

    if IsBoundGlobal("ORBC") then
      htadd   := HTAdd_TreeHash_C;
      htvalue := HTValue_TreeHash_C;
    else
      htadd   := HTAdd;
      htvalue := HTValue;
    fi;

    stop := false;

    while i <= nr and not stop do
      lentoapply := [1 .. len];
      while i <= nr and Length(words[i]) = len and not stop do
        b := first[i];                         # elts[i]=gens[b]*elts[s]
        s := suffix[i];
        for j in genstoapply do                # consider <elts[i]*gens[j]>
          if s <> 0 and not reduced[s][j] then # <elts[s]*gens[j]> is not reduced
            r := right[s][j];                  # elts[r]=elts[s]*gens[j]
            if prefix[r] <> 0 then
              right[i][j] := right[left[prefix[r]][b]][final[r]];
              # elts[i]*gens[j]=gens[b]*elts[prefix[r]]*gens[final[r]];
              # reduced[i][j]=([words[i],j]=words[right[i][j]])
              reduced[i][j] := false;
            elif r = one then               # <elts[r]> is the identity
              right[i][j] := genslookup[b];
              reduced[i][j] := false;        # <elts[i]*gens[j]=b> and it is reduced
            else # prefix[r]=0, i.e. elts[r] is one of the generators
              right[i][j] := right[genslookup[b]][final[r]];
              # elts[i]*gens[j]=gens[b]*gens[final[r]];
              # reduced[i][j]=([words[i],j]=words[right[i][j]])
              reduced[i][j] := false;
            fi;
          else # <elts[s]*gens[j]> is reduced
            new := elts[i] * gens[j];
            # <newword>=<elts[i]*gens[j]>
            newword := words[i]{lentoapply}; # better than ShallowCopy
            newword[len+1] := j;             # using Concatenate here is very bad!
            val := htvalue(ht, new);

            if val<>fail then
              nrrules := nrrules + 1;
              rules[nrrules] := [newword, words[val]];
              right[i][j] := val;
              # <newword> and <words[val]> represent the same element (but are not
              # equal) and so <newword> is not reduced

            else #<new> is a new element!
              nr := nr + 1;
              htadd(ht, new, nr);

              if one=false and ForAll(gens, y-> new * y=y and y * new=y) then
                one := nr;
              fi;

              if s <> 0 then
                suffix[nr] := right[s][j];
              else
                suffix[nr] := genslookup[j];
              fi;

              elts[nr]      := new;
              words[nr]     := newword;
              first[nr]     := b;
              final[nr]     := j;
              prefix[nr]    := i;
              right[nr]     := EmptyPlist(nrgens);
              left[nr]      := EmptyPlist(nrgens);
              reduced[nr]   := BlistList(genstoapply, []);
              right[i][j]   := nr;
              reduced[i][j] := true;

              if looking and (not found) and lookfunc(data, nr) then
                found := true;
                stop  := true;
                data!.found := nr;
              else
                stop := (nr >= limit);
              fi;
            fi;
          fi;
        od; # finished applying gens to <elts[i]>
        stop := (stop or i = stopper);
        i := i + 1;
      od; # finished words of length <len> or <looking and found>
      if i > nr or Length(words[i]) <> len then
        # process words of length <len> into <left>
        if len > 1 then
          for j in [lenindex[len] .. i - 1] do # loop over all words of length <len-1>
            p := prefix[j];
            b := final[j];
            for k in genstoapply do
              left[j][k] := right[left[p][k]][b];
              # gens[k]*elts[j]=(gens[k]*elts[p])*gens[b]
            od;
          od;
        elif len = 1 then
          for j in [lenindex[len] .. i - 1] do  # loop over all words of length <1>
            b := final[j];
            for k in genstoapply do
              left[j][k] := right[genslookup[k]][b];
              # gens[k]*elts[j]=elts[k]*gens[b]
            od;
          od;
        fi;
        len := len + 1;
        lenindex[len] := i;
      fi;
    od;

    data!.nr := nr;
    data!.nrrules := nrrules;
    data!.one := one;
    data!.pos := i;
    data!.len := len;

    if i>nr then
      SetFilterObj(data, IsClosedData);
      # Unbind some of the unnecessary components here!
    fi;

    return data;
  end);
fi;


# the following are GAP versions of some kernel functions used below, these are
# where most of the work in finding Green's relations/classes is done.

# the scc index 1 corresponds to the "deepest" scc, i.e. the minimal ideal in
# our case...

if not IsBound(SEMIGROUPS_GABOW_SCC) then # non-recursive version below...
  BindGlobal("SEMIGROUPS_GABOW_SCC",
  function(digraph)
    local n, stack1, len1, stack2, len2, id, count, comps, fptr, level, l, comp, w, v;

    n:=Length(digraph);

    if n=0 then
      return rec( comps:=[], id:=[]);
    fi;

    stack1:=EmptyPlist(n); len1:=0;
    stack2:=EmptyPlist(n); len2:=0;
    id:=[1..n]*0;
    count:=Length(digraph);
    comps:=[];
    fptr:=[];

    for v in [1..Length(digraph)] do
      if id[v]=0 then
        level:=1;
        fptr[1] := v; #fptr[0], vertex
        fptr[2] := 1; #fptr[2], index
        len1:=len1+1;
        stack1[len1]:=v;
        len2:=len2+1;
        stack2[len2]:=len1;
        id[v]:=len1;

        while level>0 do
          if fptr[2*level] > Length(digraph[fptr[2*level-1]]) then
            if stack2[len2]=id[fptr[2*level-1]] then
              len2:=len2-1;
              count:=count+1;
              l:=0;
              comp:=[];
              repeat
                w:=stack1[len1];
                id[w]:=count;
                len1:=len1-1; #pop from stack1
                l:=l+1;
                comp[l]:=w;
              until w=fptr[2*level-1];
              ShrinkAllocationPlist(comp);
              MakeImmutable(comp);
              Add(comps, comp);
            fi;
            level:=level-1;
          else
            w:=digraph[fptr[2*level-1]][fptr[2*level]];
            fptr[2*level]:=fptr[2*level]+1;

            if id[w]=0 then
              level:=level+1;
              fptr[2*level-1]:=w; #fptr[0], vertex
              fptr[2*level]:=1;   #fptr[2], index
              len1:=len1+1;
              stack1[len1]:=w;
              len2:=len2+1;
              stack2[len2]:=len1;
              id[w]:=len1;

            else # we saw <w> earlier in this run
              while stack2[len2] > id[w] do
                len2:=len2-1; # pop from stack2
              od;
            fi;
          fi;
        od;
      fi;
    od;

    MakeImmutable(id);
    ShrinkAllocationPlist(comps);
    MakeImmutable(comps);
    return rec(id:=id-Length(digraph), comps:=comps);
  end);
fi;

# returns the strongly connected components of union of two graphs <digraph1>
# and <digraph2> with strongly connected components <scc1> and <scc2> (as output
# by GABOW_SCC).

if not IsBound(SCC_UNION_LEFT_RIGHT_CAYLEY_GRAPHS) then
  BindGlobal("SCC_UNION_LEFT_RIGHT_CAYLEY_GRAPHS",
  function(scc1, scc2)
    local id1, comps1, id2, comps2, id, comps, nr, seen, comp, i, j;

    comps1:=scc1.comps;
    id2:=scc2.id;
    comps2:=scc2.comps;

    id:=[1..Length(scc1.id)]*0;
    comps:=[];
    nr:=0;

    seen:=BlistList([1..Length(comps2)], []);

    for comp in comps1 do
      if id[comp[1]]=0 then
        nr:=nr+1;
        comps[nr]:=[];
        for i in comp do
          if not seen[id2[i]] then
            seen[id2[i]]:=true;
            for j in comps2[id2[i]] do
              id[j]:=nr;
              Add(comps[nr], j);
            od;
          fi;
        od;
        MakeImmutable(comps[nr]);
        ShrinkAllocationPlist(comps[nr]);
      fi;
    od;
    ShrinkAllocationPlist(comps);
    MakeImmutable(comps);
    ShrinkAllocationPlist(id);
    MakeImmutable(id);

    return rec(comps:=comps, id:=id);
  end);
fi;

if not IsBound(FIND_HCLASSES) then
  BindGlobal("FIND_HCLASSES",
  function(left, right)
    local rightid, leftid, comps, nextpos, len, sorted, hindex, rindex, id,
     lookup, j, init, i;

    rightid:=right.id;
    leftid:=left.id;

    comps:=right.comps;
    nextpos:=EmptyPlist(Length(comps));
    nextpos[1]:=1;
    for i in [2..Length(comps)] do
      nextpos[i]:=nextpos[i-1]+Length(comps[i-1]);
    od;

    # List(sorted, i-> right.id[i])= right.id sorted
    len:=Length(rightid);
    sorted:=EmptyPlist(len);
    for i in [1..len] do
      sorted[nextpos[rightid[i]]]:=i;
      nextpos[rightid[i]]:=nextpos[rightid[i]]+1;
    od;

    hindex:=0;            # current H-class index
    rindex:=0;            # current R-class index
    id:=EmptyPlist(len);  # id component for H-class data structure
    comps:=[];
    lookup:=[1..Length(left.comps)]*0;
    # H-class corresponding to L-class in the current R-class <now>

    # browse the L-class table...
    for i in [1..len] do
      j:=sorted[i];
      if rightid[j]>rindex then # new R-class
        rindex:=rightid[j];
        init:=hindex;
        # H-class indices for elements of R-class <rindex> start at <init+1>
      fi;
      if lookup[leftid[j]]<=init then
        # we have a new H-class, otherwise, this is an existing H-class in the
        # current R-class.
        hindex:=hindex+1;
        lookup[leftid[j]]:=hindex;
        comps[hindex]:=[];
      fi;
      id[j]:=lookup[leftid[j]];
      Add(comps[lookup[leftid[j]]], j);
    od;

    return rec(id:=id, comps:=comps);
  end);
fi;

# commented out stuff

#InstallMethod(IsAbundantSemigroup, "for a trans. semigroup",
#[IsTransformationSemigroup and HasGeneratorsOfSemigroup],
#function(s)
#  local iter, n, ht, ht_o, reg, i, data, f, ker, val, o, scc;
#
#  Info(InfoWarning, 1, "this will sometimes return a false positive.");
#
#  if HasIsRegularSemigroup(s) and IsRegularSemigroup(s) then
#    Info(InfoSemigroups, 2, "semigroup is regular");
#    return true;
#  fi;
#
#  iter:=IteratorOfRClassData(s); n:=ActionDegree(s);
#  # replace s!.opts by SEMIGROUPS_OptionsRec here!
#  ht:=HTCreate([1..n], rec(hashlen:=s!.opts!.hashlen!.S));
#  ht_o:=HTCreate([1,1,1,1], rec(hashlen:=s!.opts!.hashlen!.S));
#  reg:=[]; i:=0;
#
#  repeat
#    repeat #JDM this should become an method for IteratorOfRStarClasses
#           # and IsAbundantRClass...
#      data:=NextIterator(iter);
#    until HTValue(ht_o, data{[1,2,4,5]})=fail or IsDoneIterator(iter);
#    if not IsDoneIterator(iter) then
#      HTAdd(ht_o, data{[1,2,4,5]}, true);
#
#      #f:=RClassRepFromData(s, data); ker:=CanonicalTransSameKernel(f);
#      val:=HTValue(ht, ker);
#
#      if val=fail then #new kernel
#        i:=i+1; HTAdd(ht, ker, i);
#        val:=i; reg[val]:=false;
#      fi;
#
#      if reg[val]=false then #old kernel
#        #o:=ImageOrbitFromData(s, data); scc:=ImageOrbitSCCFromData(s, data);
#        reg[val]:=ForAny(scc, j-> IsInjectiveListTrans(o[j], ker));
#      fi;
#    fi;
#  until IsDoneIterator(iter);
#
#  return ForAll(reg, x-> x);
#end);

#InstallMethod(IsAdequateSemigroup,
#"for acting semigroup with generators",
#[IsActingSemigroup and HasGeneratorsOfSemigroup],
#s-> IsAbundantSemigroup(s) and IsBlockGroup(s));
