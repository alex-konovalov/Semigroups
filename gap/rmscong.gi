InstallGlobalFunction(RMSCongruenceByLinkedTriple,
[IsReesZeroMatrixSemigroup and IsFinite,
 IsGroup, IsDenseList, IsDenseList],
function(s, n, colBlocks, rowBlocks)
  local g, mat, block, i, j, u, v, bi, bj, bu, bv;
  mat := Matrix(s);
  g := UnderlyingSemigroup(s);
  
  # Basic checks
  if not IsNormal(g,n) then
    Error("2nd argument <n> must be a normal subgroup,"); return;
  fi;
  if not ForAll(colBlocks, IsList) then
    Error("3rd argument <colBlocks> must be a list of lists,"); return;
  fi;
  if not ForAll(rowBlocks, IsList) then
    Error("4th argument <rowBlocks> must be a list of lists,"); return;
  fi;
  if SortedList(Flat(colBlocks)) <> [1..Size(mat[1])] then
    Error("3rd argument <colBlocks> must be a partition ",
          "of the columns of the matrix of <s>,"); return;
  fi;
  if SortedList(Flat(rowBlocks)) <> [1..Size(mat)] then
    Error("4th argument <rowBlocks> must be a partition ",
          "of the rows of the matrix of <s>,"); return;
  fi;
  
  if IsLinkedTriple(s, n, colBlocks, rowBlocks) then
    return RMSCongruenceByLinkedTripleNC(s, n, colBlocks, rowBlocks);
  else
    Error("Not a valid linked triple,"); return;
  fi;
end);

#

InstallGlobalFunction(RMSCongruenceByLinkedTripleNC,
[IsReesZeroMatrixSemigroup and IsFinite,
 IsGroup, IsDenseList, IsDenseList],
function(s, n, colBlocks, rowBlocks)
  local fam, cong, colLookup, rowLookup, i, j;
  # Calculate lookup table for equivalence relations
  colLookup := [];
  rowLookup := [];
  for i in [1..Length(colBlocks)] do
    for j in colBlocks[i] do
      colLookup[j] := i;
    od;
  od;
  for i in [1..Length(rowBlocks)] do
    for j in rowBlocks[i] do
      rowLookup[j] := i;
    od;
  od;
  # Construct the object
  fam := GeneralMappingsFamily(
                 ElementsFamily(FamilyObj(s)),
                 ElementsFamily(FamilyObj(s)) );
  cong := Objectify(
                  NewType(fam, IsRMSCongruenceByLinkedTriple),
                  rec(n := n,
                      colBlocks := colBlocks, colLookup := colLookup,
                      rowBlocks := rowBlocks, rowLookup := rowLookup) );
  SetSource(cong, s);
  SetRange(cong, s);
  return cong;
end);

#

InstallMethod(ViewObj,
"for Rees zero-matrix semigroup congruence by linked triple",
[IsRMSCongruenceByLinkedTriple],
function(cong)
  local rows, cols;
  rows := Size(Rows(Range(cong)));
  cols := Size(Columns(Range(cong)));
  Print("<semigroup congruence by linked triple on ",
        rows, "x", cols, " Rees 0-matrix semigroup>");
end);

#

InstallMethod(CongruencesOfSemigroup,
"for finite 0-simple Rees 0-matrix semigroup",
[IsReesZeroMatrixSemigroup and IsZeroSimpleSemigroup and IsFinite],
function(s)
  local congs, mat, g, AddRelation, maxColBlocks, maxRowBlocks,
        i, j, u, v, n, colBlocks, rowBlocks, colBlocksList, rowBlocksList,
        subpartitions;
  
  # Function to compute all subsets of a relation given by partitions
  subpartitions := function(part)
    local l;
    # Replace each class with a list of all partitions of that class
    l := List(part, PartitionsSet);
    # Produce all the combinations of partitions of classes
    l := Cartesian(l);
    # Concatenate these lists to produce complete partitions of the set
    l := List(l, Concatenation);
    # Finally sort each of these into the canonical order of its new classes
    l := SSortedList(l);
    return l;
  end;
  
  congs := [];
  mat := Matrix(s);
  g := UnderlyingSemigroup(s);
  
  # This function combines two congruence classes
  AddRelation := function(R, x, y)
    local xClass, yClass;
    xClass := PositionProperty(R, class -> x in class);
    yClass := PositionProperty(R, class -> y in class);
    if xClass <> yClass then
      Append(R[xClass],R[yClass]);
      Remove(R,yClass);
    fi;
  end;
  
  # Construct maximum column relation
  maxColBlocks := List([1..Size(mat[1])], i->[i]);
  for i in [1..Size(mat[1])] do
    for j in [i+1..Size(mat[1])] do
      if ForAll([1..Size(mat)], u->( (mat[u][i]=0) = (mat[u][j]=0) ) ) then
        AddRelation(maxColBlocks, i, j);
      fi;
    od;
  od;
  
  # Construct maximum row relation
  maxRowBlocks := List([1..Size(mat)], u->[u]);
  for u in [1..Size(mat)] do
    for v in [u+1..Size(mat)] do
      if ForAll([1..Size(mat[1])], i->( (mat[u][i]=0) = (mat[v][i]=0) ) ) then
        AddRelation(maxRowBlocks, u, v);
      fi;
    od;
  od;
  
  # Add the universal congruence
  Add(congs, UniversalSemigroupCongruence(s));
  
  # Compute all column and row relations which are subsets of the max relations
  colBlocksList := subpartitions(maxColBlocks);
  rowBlocksList := subpartitions(maxRowBlocks);
  
  # Go through all triples and check
  for n in NormalSubgroups(g) do
    for colBlocks in colBlocksList do
      for rowBlocks in rowBlocksList do
        if IsLinkedTriple(s, n, colBlocks, rowBlocks) then
          Add(congs, RMSCongruenceByLinkedTripleNC(s, n, colBlocks, rowBlocks));
        fi;
      od;
    od;
  od;
  
  return congs;
end);

#

InstallGlobalFunction(IsLinkedTriple,
function(s, n, colBlocks, rowBlocks)
  local mat, block, i, j, u, v, bi, bj, bu, bv;
  mat := Matrix(s);
  # Check axioms (L1) and (L2) from Howie p.86, then call NC function
  # Go through the column blocks
  for block in colBlocks do
    for bj in [2..Size(block)] do
      # Check columns have zeroes in all the same rows (L1)
      for u in [1..Size(mat)] do
        if (mat[u][block[1]] = 0) <> (mat[u][block[bj]] = 0) then
          return false;
        fi;
      od;
    od;
    # Check q-condition for all pairs of rows in this block (L2)
    for bi in [1..Size(block)] do
      for bj in [bi+1..Size(block)] do
        i := block[bi];
        j := block[bj];
        # Check all pairs of rows (u,v)
        for u in [1..Size(mat)] do
          if mat[u][i] = 0 then continue; fi;
          for v in [u+1..Size(mat)] do
            if mat[v][i] = 0 then continue; fi;
            if not (mat[u][i]*mat[v][i]^-1*mat[v][j]*mat[u][j]^-1) in n then
              return false;
            fi;
          od;
        od;
      od;
    od;
  od;
  
  # Go through the row blocks
  for block in rowBlocks do
    for bv in [2..Size(block)] do
      # Check rows have zeroes in all the same columns (L1)
      for i in [1..Size(mat[1])] do
        if (mat[block[1]][i] = 0) <> (mat[block[bv]][i] = 0) then
          return false;
        fi;
      od;
    od;
    # Check q-condition for all pairs of columns in this block (L2)
    for bu in [1..Size(block)] do
      for bv in [bi+1..Size(block)] do
        u := block[bu];
        v := block[bv];
        # Check all pairs of columns (i,j)
        for i in [1..Size(mat[1])] do
          if mat[u][i] = 0 then continue; fi;
          for j in [i+1..Size(mat[1])] do
            if mat[u][j] = 0 then continue; fi;
            if not (mat[u][i]*mat[v][i]^-1*mat[v][j]*mat[u][j]^-1) in n then
              return false;
            fi;
          od;
        od;
      od;
    od;
  od;
  return true;
end);

#

BindGlobal("LinkedElement",
function(elt)
  local mat, i, u, v, j;
  mat := Matrix(ReesMatrixSemigroupOfFamily(FamilyObj(elt)));
  i := elt[1];  # Column no
  u := elt[3];  # Row no
  for v in [1..Size(mat)] do
    if mat[v][i] <> 0 then break; fi;
  od;
  for j in [1..Size(mat[1])] do
    if mat[u][j] <> 0 then break; fi;
  od;
  return(mat[v][i] * elt[2] * mat[u][j]);
end);

#

InstallMethod( \=,
"for two Rees 0-matrix semigroup congruences by linked triple",
[IsRMSCongruenceByLinkedTriple, IsRMSCongruenceByLinkedTriple],
function(c1, c2)
  return( Range(c1) = Range(c2) and
          c1!.n = c2!.n and
          c1!.colRel = c2!.colRel and
          c1!.rowRel = c2!.rowRel );
end);

#

InstallMethod(\in,
"for Rees 0-matrix semigroup element collection and a semigroup congruence by linked triple",
[IsReesZeroMatrixSemigroupElementCollection, IsRMSCongruenceByLinkedTriple],
function(pair, cong)
  local s, mat, gpElt, row, col, rows, cols, a, i, u, j, b, v;
  
  # Check for validity
  if Size(pair) <> 2 then
    Error("usage: 1st argument <pair> must be a list of length 2,");
    return;
  fi;
  s := Range(cong);
  if not ForAll(pair, x-> x in s) then
    Error("usage: the elements of the 1st argument <pair> ",
          "must be in the range of the 2nd argument <cong>,");
    return;
  fi;
  
  # Handling the case when one or more of the pair are zero
  if pair[1] = pair[2] then
    return true;
  elif MultiplicativeZero(s) in pair then
    return false;
  fi;
  
  # Read the elements as (i,a,u) and (j,b,v)
  i := pair[1][1]; a := pair[1][2]; u := pair[1][3];
  j := pair[2][1]; b := pair[2][2]; v := pair[2][3];
  
  # First, the columns and rows must be related
  if not (cong!.colLookup[i] = cong!.colLookup[j] and
          cong!.rowLookup[u] = cong!.rowLookup[v]) then
    return false;
  fi;
  
  # Finally, check Lemma 3.5.6(2) in Howie
  mat := Matrix(s);
  rows := mat;
  cols := TransposedMat(mat);
  # Pick a valid column and row
  col := PositionProperty(rows[u], x-> x <> 0);
  row := PositionProperty(cols[i], x-> x <> 0);
  gpElt := mat[row][i] * a * mat[u][col] *
           Inverse(mat[row][j] * b * mat[v][col]);
  return(gpElt in cong!.n);
end);

#

InstallMethod(ImagesElm,
"for Rees 0-matrix semigroup congruence by linked triple and element",
[IsRMSCongruenceByLinkedTriple, IsReesZeroMatrixSemigroupElement],
function(cong, elm)
  local s, mat, images, i, a, u, row, col, j, b, v, nElm;
  s := Range(cong);
  mat := Matrix(s);
  if not elm in s then
    Error("1st and 2nd args <cong> and <elm> must refer to the same semigroup,");
    return;
  fi;
  # Special case for 0
  if elm = MultiplicativeZero(s) then
    return [elm];
  fi;
  # List of all elements congruent to elm under cong
  images := [];
  # Read the element as (i,a,u)
  i := elm[1]; a := elm[2]; u := elm[3];
  # Find a non-zero row for this class of columns
  for row in [1..Size(mat)] do
    if mat[row][i] <> 0 then break; fi;
  od;
  # Find a non-zero column for this class of rows
  for col in [1..Size(mat[1])] do
    if mat[u][col] <> 0 then break; fi;
  od;
  
  # Construct congruent elements as (j,b,v)
  for j in cong!.colBlocks[cong!.colLookup[i]] do
    for v in cong!.rowBlocks[cong!.rowLookup[u]] do
      for nElm in cong!.n do
        # Might be better to use congruence classes after all
        b := mat[row][j]^-1
             * nElm 
             * mat[row][i] 
             * a 
             * mat[u][col] 
             * mat[v][col]^-1;
        Add(images, ReesZeroMatrixSemigroupElement(s, j, b, v));
      od;
    od;
  od;
  return images;
end);

#

InstallMethod(EquivalenceClasses,
"for Rees 0-matrix semigroup congruence by linked triple",
[IsRMSCongruenceByLinkedTriple],
function(cong)
  local list, s, g, n, colBlocks, rowBlocks, colClass, rowClass, rep, elt;
  list := [];
  s := Range(cong);
  g := UnderlyingSemigroup(s);
  n := cong!.n;
  colBlocks := cong!.colBlocks;
  rowBlocks := cong!.rowBlocks;
  for colClass in [1..Size(colBlocks)] do
    for rowClass in [1..Size(rowBlocks)] do
      for rep in List(RightCosets(g,n), Representative) do
        elt := ReesZeroMatrixSemigroupElement(
                       s, colBlocks[colClass][1], rep, rowBlocks[rowClass][1] );
        Add(list, EquivalenceClassOfElement(cong, elt));
      od;
    od;
  od;
  # Add the zero class
  Add(list, EquivalenceClassOfElement(cong, MultiplicativeZero(s)));
  return list;
end);

#

InstallMethod(NrCongruenceClasses,
"for Rees 0-matrix semigroup congruence by linked triple",
[IsRMSCongruenceByLinkedTriple],
function(cong)
  local s, g;
  s := Range(cong);
  g := UnderlyingSemigroup(s);
  return( Index(g, cong!.n)    # Number of cosets of n
          * Size(cong!.colBlocks)       # Number of column blocks
          * Size(cong!.rowBlocks)       # Number of row blocks
          + 1 );                        # Class containing zero
end);

#

InstallMethod(JoinSemigroupCongruences,
"for two Rees 0-matrix semigroup congruences by linked triple",
[IsRMSCongruenceByLinkedTriple, IsRMSCongruenceByLinkedTriple],
function(c1, c2)
  local gens, n, colBlocks, cols, rowBlocks, rows, i, block, u;
  if Range(c1) <> Range(c2) then
    Error("congruences must be defined over the same semigroup,"); return;
  fi;
  # n is the product of the normal subgroups
  gens := Concatenation(GeneratorsOfGroup(c1!.n), GeneratorsOfGroup(c2!.n));
  n := Group(gens);
  # Calculate the union of the column and row relations
  colBlocks := []; cols := [1..Size(c1!.colLookup)];
  rowBlocks := []; rows := [1..Size(c1!.rowLookup)];
  while not IsEmpty(cols) do
    i := Remove(cols);
    block := Union(c1!.colBlocks[c1!.colLookup[i]],
                   c2!.colBlocks[c2!.colLookup[i]]);
    for i in block do Unbind(cols[i]); od;
    Add(colBlocks, block);
  od;
  while not IsEmpty(rows) do
    u := Remove(rows);
    block := Union(c1!.rowBlocks[c1!.rowLookup[u]],
                   c2!.rowBlocks[c2!.rowLookup[u]]);
    for u in block do Unbind(rows[u]); od;
    Add(rowBlocks, block);
  od;
  # Make the congruence and return it
  return RMSCongruenceByLinkedTripleNC(Range(c1), n, colBlocks, rowBlocks);
end);

#

InstallMethod(MeetSemigroupCongruences,
"for two Rees 0-matrix semigroup congruences by linked triple",
[IsRMSCongruenceByLinkedTriple, IsRMSCongruenceByLinkedTriple],
function(c1, c2)
  local n, colBlocks, cols, rowBlocks, rows, i, block, u;
  if Range(c1) <> Range(c2) then
    Error("congruences must be defined over the same semigroup,"); return;
  fi;
  # n is the intersection of the two normal subgroups
  n := Intersection(c1!.n, c2!.n);
  # Calculate the intersection of the column and row relations
  colBlocks := []; cols := [1..Size(c1!.colLookup)];
  rowBlocks := []; rows := [1..Size(c1!.rowLookup)];
  while not IsEmpty(cols) do
    i := Remove(cols);
    block := Intersection(c1!.colBlocks[c1!.colLookup[i]],
                          c2!.colBlocks[c2!.colLookup[i]]);
    for i in block do Unbind(cols[i]); od;
    Add(colBlocks, block);
  od;
  while not IsEmpty(rows) do
    u := Remove(rows);
    block := Intersection(c1!.rowBlocks[c1!.rowLookup[u]],
                          c2!.rowBlocks[c2!.rowLookup[u]]);
    for u in block do Unbind(rows[u]); od;
    Add(rowBlocks, block);
  od;
  # Make the congruence and return it
  return RMSCongruenceByLinkedTripleNC(Range(c1), n, colBlocks, rowBlocks);
end);

#

InstallMethod(RMSCongruenceClassByLinkedTriple,
"for semigroup congruence by linked triple, a coset and two positive integers",
[IsRMSCongruenceByLinkedTriple,
 IsRightCoset, IsPosInt, IsPosInt],
function(cong, nCoset, colClass, rowClass)
  local g;
  g := UnderlyingSemigroup(Range(cong));
  if not (ActingDomain(nCoset) = cong!.n and IsSubset(g, nCoset)) then
    Error("2nd argument <nCoset> must be a coset of <cong>'s field n in the ",
          "underlying (semi)group of the Rees 0-matrix semigroup,"); return;
  fi;
  if not colClass in [1..Size(cong!.colBlocks)] then
    Error("3rd argument <colClass> is out of range,"); return;
  fi;
  if not rowClass in [1..Size(cong!.rowBlocks)] then
    Error("4th argument <rowClass> is out of range,"); return;
  fi;
  return RMSCongruenceClassByLinkedTripleNC(cong, nCoset, colClass, rowClass);
end);

#

InstallMethod(RMSCongruenceClassByLinkedTripleNC,
"for semigroup congruence by linked triple, a coset and two positive integers",
[IsRMSCongruenceByLinkedTriple,
 IsRightCoset, IsPosInt, IsPosInt], 
function(cong, nCoset, colClass, rowClass)
  local fam, class;
  fam := FamilyObj(Range(cong));
  class := Objectify(NewType(fam, IsRMSCongruenceClassByLinkedTriple),
                   rec(nCoset := nCoset,
                       colClass := colClass,
                       rowClass := rowClass) );
  SetParentAttr(class, cong);
  SetRepresentative(class, CanonicalRepresentative(class));
  return class;
end);

#

InstallMethod(EquivalenceClassOfElement,
"for Rees 0-matrix semigroup congruence by linked triple and a Rees 0-matrix semigroup element",
[IsRMSCongruenceByLinkedTriple, IsReesZeroMatrixSemigroupElement],
function(cong, elt)
  # Check that the arguments make sense
  if not elt in Range(cong) then
    Error("usage: 2nd argument <elt> should be ",
          "in the semigroup of 1st argument <cong>");
    return;
  fi;
  return EquivalenceClassOfElementNC(cong, elt);
end);

#

InstallMethod(EquivalenceClassOfElementNC,
"for Rees 0-matrix semigroup congruence by linked triple and a Rees 0-matrix semigroup element",
[IsRMSCongruenceByLinkedTriple, IsReesZeroMatrixSemigroupElement],
function(cong, elt)
  local fam, class, mat, nCoset, colClass, rowClass;
  # Construct the object
  fam := CollectionsFamily( FamilyObj(elt));
  if elt = MultiplicativeZero(Range(cong)) then
    class := Objectify(NewType(fam, IsRMSCongruenceClassByLinkedTriple),
                       rec(nCoset := 0) );
    SetAsSSortedList(class,[elt]);
  else
    nCoset := RightCoset(cong!.n, LinkedElement(elt));
    colClass := cong!.colLookup[elt[1]];
    rowClass := cong!.rowLookup[elt[3]];
    class := Objectify(NewType(fam, IsRMSCongruenceClassByLinkedTriple),
                       rec(nCoset := nCoset,
                           colClass := colClass,
                           rowClass := rowClass) );
  fi;
  SetParentAttr(class, cong);
  SetEquivalenceClassRelation(class, cong);
  SetRepresentative(class, elt);
  return class;
end);

#

InstallMethod( \in,
"for Rees 0-matrix semigroup element and a congruence class by linked triple",
[IsReesZeroMatrixSemigroupElement, IsRMSCongruenceClassByLinkedTriple],
function(elt, class)
  local s, cong;
  cong := ParentAttr(class);
  s := Range(cong);
  # Special case for {0}
  if elt = MultiplicativeZero(s) then
    return(class!.nCoset = 0);
  fi;
  # Otherwise
  return( elt in s and
          cong!.colLookup[elt[1]] = class!.colClass and
          cong!.rowLookup[elt[3]] = class!.rowClass and
          LinkedElement(elt) in class!.nCoset );
end);

#

InstallMethod( \*,
"for two congruence classes by linked triple",
[IsRMSCongruenceClassByLinkedTriple, IsRMSCongruenceClassByLinkedTriple],
function(c1, c2)
  local elm;
  if not Parent(c1) = Parent(c2) then
    Error("<c1> and <c2> must be classes of the same congruence,"); return;
  fi;
  elm := Representative(c1) * Representative(c2);
  return( EquivalenceClassOfElementNC(Parent(c1), elm) );
end);

#

InstallMethod( \*,
"for a congruence class by linked triple and a list",
[IsRMSCongruenceClassByLinkedTriple, IsList],
function(class, list)
  return List(list, x -> class * x);
end);

#

InstallMethod( \*,
"for a list and a congruence class by linked triple",
[IsList, IsRMSCongruenceClassByLinkedTriple],
function(list, class)
  return List(list, x -> x * class);
end);

#

InstallMethod(Size,
"for congruence class by linked triple",
[IsRMSCongruenceClassByLinkedTriple],
function(class)
  local cong;
  # Special case for {0}
  if class!.nCoset = 0 then
    return 1;
  fi;
  # Otherwise
  cong := Parent(class);
  return( Size(cong!.n) *
          Size(cong!.colBlocks[class!.colClass]) *
          Size(cong!.rowBlocks[class!.rowClass]) );
end);

#

InstallMethod( \=,
"for two congruence classes by linked triple",
[IsRMSCongruenceClassByLinkedTriple, IsRMSCongruenceClassByLinkedTriple],
function(c1, c2)
  # Special case for {0}
  if c1!.nCoset = 0 and c2!.nCoset = 0 then
    return true;
  fi;
  # Otherwise
  return( c1!.nCoset = c2!.nCoset and
          c1!.colClass = c2!.colClass and
          c1!.rowClass = c2!.rowClass );
end);

#

InstallMethod(CanonicalRepresentative,
"for Rees 0-matrix semigroup congruence class by linked triple",
[IsRMSCongruenceClassByLinkedTriple],
function(class)
  local cong, s, mat, i, u, v, j, a;
  cong := Parent(class);
  s := Range(cong);
  # Special case for {0}
  if class!.nCoset = 0 then
    return MultiplicativeZero(s);
  fi;
  # Pick the first row and column from the classes
  i := cong!.colBlocks[class!.colClass][1];
  u := cong!.rowBlocks[class!.rowClass][1];
  # Pick another row and column with appropriate non-zero entries
  mat := Matrix(s);
  for v in [1..Size(mat)] do
    if mat[v][i] <> 0 then break; fi;
  od;
  for j in [1..Size(mat[1])] do
    if mat[u][j] <> 0 then break; fi;
  od;
  a := mat[v][i]^-1
       * CanonicalRightCosetElement(cong!.n, Representative(class!.nCoset))
       * mat[u][j]^-1;
  return ReesZeroMatrixSemigroupElement(s, i, a, u);
end);

#

#UnbindGlobal("LinkedElement");