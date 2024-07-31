#############################################################################
##
##  semigroups/semidp.gi
##  Copyright (C) 2017-2022                                 Wilf A. Wilson
##
##  Licensing information can be found in the README file of this package.
##
#############################################################################
##

### degreefunc := function(semigroup)
# Takes a semigroup and returns its degree.
#
### convert := function(element, degree, offset)
# Takes an element, the degree of the semigroup it belongs to, and an offset
# to say by how much to "increase" the values in its representation.
# The function then returns an object representing this offset element,
# in a form that is readily used by the following <combine> function.
#
### combine := function(list)
# Takes a list of elements in the form given by <convert>, and forms the
# corresponding direct product element.
#
### restrict := function(element, i, j)
# (Is used to compute the projections from the product onto its factors).
# Takes an element, and two integers i and j. The function then returns the
# restriction of then element corresponding to its "action" on [i + 1 .. i + j].
# It's kind of the inverse of convert & combine.

# See DirectProductOp for transformation semigroups or bipartition semigroups
# for examples of how to use SEMIGROUPS.DirectProductOp.

# TODO(later): add reference to a description & proof of this algorithm, when
# possible.

SEMIGROUPS.DirectProductOp := function(S, degree, convert, combine, restrict)
  local f, create, n, gens_old, gens_new, indecomp, pre_mult, pos_mult, out,
  degrees, offsets, idems, idem, factorization, y, len, w, hasindecomp, elt, p,
  x, indecomp_out, D, embedding, projection, i, choice;

  if not IsList(S) or IsEmpty(S) then
    ErrorNoReturn("the 1st argument is not a non-empty list");
  elif ForAll(S, HasGeneratorsOfInverseMonoid) then
    f := GeneratorsOfInverseMonoid;
    create := InverseMonoid;
  elif ForAll(S, IsMonoid) then
    f := GeneratorsOfMonoid;
    create := Monoid;
  else
    f := GeneratorsOfSemigroup;
    create := Semigroup;
  fi;

  n := Length(S);
  gens_old := List(S, f);
  gens_new := List([1 .. n], i -> []);
  indecomp := List([1 .. n], i -> []);
  pre_mult := List([1 .. n], i -> []);
  pos_mult := List([1 .. n], i -> []);
  out := [];

  # The semigroup <S[i]> has degree <degrees[i]>.
  # In the product, we "offset" the representation of <S[i]> by <offsets[i]>.
  # eg. if <S[i]> is a transformation semigroup on [1 .. m], then in the product
  # it is imagined as a transformation semigroup on [1 + offset .. m + offset].
  #
  # This way, the representations are "disjoint", and so the "union" of the
  # representations of all the factors gives a representation of the product.
  degrees := List(S, degree);
  offsets := [0];
  for i in [2 .. n] do
    offsets[i] := offsets[i - 1] + degrees[i - 1];
  od;

  # To create the embeddings of each factor into the product, we require an
  # idempotent from each factor. For the monoids, we take its identity.
  # Otherwise, we select an arbitrary idempotent from the minimal ideal, simply
  # because it is probably an efficient way to come up with a single idempotent.
  idems := EmptyPlist(n);
  for i in [1 .. n] do
    idem := MultiplicativeNeutralElement(S[i]);
    if idem = fail then
      idem := MultiplicativeNeutralElement(GroupHClass(MinimalDClass(S[i])));
    fi;
    idems[i] := convert(idem, degrees[i], offsets[i]);
  od;

  # For each factor <i> and for each generator <x> in <gens_old[i]>, either <x>
  # is indecomposable, or we may find a non-trivial factorization of <x>, and
  # hence express <x> as a product <x = pre_mult * x'> and <x = x'' * pos_mult>,
  # for some generators <x'> and <x''> in <gens_old[i]>, and for some elements
  # <pre_mult> and <pos_mult> in <S[i]>.
  #
  # We want to record which case happens, and in the second case, get our hands
  # on the relevant elements, and store them in <pre_mult[i]> and <pos_mult[i]>,
  # as appropriate.
  for i in [1 .. n] do
    if IsMonoidAsSemigroup(S[i]) then
      # For a monoid, every generator is decomposable. Simply convert each gen,
      # and use the identity as the pre_mult and pos_mult of each gen.
      for x in gens_old[i] do
        AddSet(gens_new[i], convert(x, degrees[i], offsets[i]));
      od;
      # Remember that idems[i] = MultiplicativeNeutralElement(S[i]).
      AddSet(pre_mult[i], idems[i]);
      AddSet(pos_mult[i], idems[i]);
    else
      for x in gens_old[i] do
        # Attempt to find a non-trivial factorization of <x>.
        factorization := NonTrivialFactorization(S[i], x);
        y := convert(x, degrees[i], offsets[i]);
        if factorization = fail then
          # <x> is indecomposable; record it as such.
          AddSet(indecomp[i], y);
        else
          # We can decompose <x>, so we can find a <pre_mult> and <pos_mult>.
          AddSet(gens_new[i], y);
          len := Length(factorization);
          if i > 1 then
            # <pos_mult>s are not needed for the first factor
            w := EvaluateWord(gens_old[i], factorization{[1 .. len - 1]});
            AddSet(pre_mult[i], convert(w, degrees[i], offsets[i]));
          fi;
          if i < n then
            # <pre_mult>s are not needed for the final factor
            w := EvaluateWord(gens_old[i], factorization{[2 .. len]});
            AddSet(pos_mult[i], convert(w, degrees[i], offsets[i]));
          fi;
        fi;
      od;
    fi;
  od;

  # Each indecomposable element of <S[i]> has to appear as a generator of the
  # product with every possible combination of elements from the other factors.
  hasindecomp := Filtered([1 .. n], i -> not IsEmpty(indecomp[i]));
  if not IsEmpty(hasindecomp) then
    elt := EmptyPlist(n);
    for i in [1 .. n] do
      # For each factor <i> with indecomposable elements, we are required to
      # get the Elements of all the other factors. If <i> is unique we do not
      # need to enumerate <S[i]>; otherwise, we must enumerate *every* factor.
      if hasindecomp <> [i] then
        elt[i] := List(Elements(S[i]), x -> convert(x, degrees[i], offsets[i]));
      fi;
    od;
    for i in hasindecomp do
      # For each factor <i> with indecomposable elements, and for each indecomp
      # generators <x>, we create the generator of the product that corresponds
      # to <x> with all possible combinations of other elements from the other
      # factors.
      #
      # This appears more complicated than necessary because of partial perms.
      p := List([1 .. i - 1], j -> [1 .. Length(elt[j])]);
      Add(p, [1 .. Length(indecomp[i])]);
      Append(p, List([i + 1 .. n], j -> [1 .. Length(elt[j])]));
      for choice in IteratorOfCartesianProduct(p) do
        # choice[j]: we are choosing <elt[j][choice[j]]> to be the element from
        #            the <j>^th factor, to appear with...
        # choice[i]: we are choosing <indecomp[i][choice[i]]>, the
        #            <choice[i]>^th indecomposable gen of the <i>^th factor.
        x := Concatenation(List([1 .. i - 1], j -> elt[j][choice[j]]),
                           [indecomp[i][choice[i]]],
                           List([i + 1 .. n], j -> elt[j][choice[j]]));
        AddSet(out, combine(x));
      od;
    od;
  fi;

  # The indecomposable elements of the produdct are precisely those generators
  # that we have already created. The product has indecomposable elements if and
  # only if any factor has indecomposable elements; the indecomposable elements
  # of the product are those such that the i^th projection of the element is
  # indecomposable, for some factor <i>.
  indecomp_out := ShallowCopy(out);

  # Each decomposable generator of <S[i]> will appear as a generator of the
  # product with every pos_mult in the j^th factor (j < i), and every pre_mult
  # in the k^th factor (k > i). (These strict inequalities are why we do not
  # require <pos_mult>s for the first factor, or <pre_mult>s for the final
  # factor.)
  #
  # If any <gens_new[i]> is empty, then no such generators can be created, and
  # so we skip this step.
  if not ForAny(gens_new, IsEmpty) then
    for i in [1 .. n] do
      # Again, this appears more complicated than it should.
      p := Concatenation(List([1 .. i - 1], j -> [1 .. Length(pos_mult[j])]),
                         [[1 .. Length(gens_new[i])]],
                         List([i + 1 .. n], j -> [1 .. Length(pre_mult[j])]));
      for choice in IteratorOfCartesianProduct(p) do
        x := Concatenation(List([1 .. i - 1], j -> pos_mult[j][choice[j]]),
                           [gens_new[i][choice[i]]],
                           List([i + 1 .. n], j -> pre_mult[j][choice[j]]));
        AddSet(out, combine(x));
      od;
    od;
  fi;

  D := create(out);
  SetIndecomposableElements(D, indecomp_out);
  SetIsSurjectiveSemigroup(D, IsEmpty(indecomp_out));
  if ForAny(gens_new, IsEmpty) then
    SetMinimalSemigroupGeneratingSet(D, indecomp_out);
  fi;

  # Store information to be able to construct embeddings and projections
  embedding := function(x, i)
    return combine(Concatenation(idems{[1 .. i - 1]},
                                 [convert(x, degrees[i], offsets[i])],
                                 idems{[i + 1 .. n]}));
  end;
  projection := {x, i} -> restrict(x, offsets[i], degrees[i]);
  SetSemigroupDirectProductInfo(D, rec(factors     := S,
                                       nrfactors   := n,
                                       embedding   := embedding,
                                       embeddings  := [],
                                       projection  := projection,
                                       projections := []));
  return D;
end;

# Transformation semigroups

InstallMethod(DirectProductOp, "for a list and a transformation semigroup",
[IsList, IsTransformationSemigroup],
function(list, S)
  local combine, convert, restrict;

  if IsEmpty(list) then
    ErrorNoReturn("the 1st argument (a list) is not non-empty");
  elif not ForAny(list, T -> IsIdenticalObj(S, T)) then
    ErrorNoReturn("the 2nd argument is not one of the semigroups ",
                  "contained in the 1st argument (a list)");
  elif not ForAll(list, IsTransformationSemigroup) then
    TryNextMethod();
  fi;

  combine := x -> Transformation(Concatenation(x));
  convert := {element, degree, offset} ->
               ImageListOfTransformation(element, degree) + offset;
  restrict := function(element, offset, degree)
    local im;
    im := ImageListOfTransformation(element, offset + degree);
    return Transformation(im{[offset + 1 .. offset + degree]} - offset);
  end;
  return SEMIGROUPS.DirectProductOp(list, DegreeOfTransformationSemigroup,
                                    convert, combine, restrict);
end);

# Partial perm semigroups

InstallMethod(DirectProductOp, "for a list and a partial perm semigroup",
[IsList, IsPartialPermSemigroup],
function(list, S)
  local degree, combine, convert, restrict;

  if IsEmpty(list) then
    ErrorNoReturn("the 1st argument (a list) is not non-empty");
  elif not ForAny(list, T -> IsIdenticalObj(S, T)) then
    ErrorNoReturn("the 2nd argument is not one of the semigroups ",
                  "contained in the 1st argument (a list)");
  elif not ForAll(list, IsPartialPermSemigroup) then
    TryNextMethod();
  fi;

  degree := S -> Maximum(DegreeOfPartialPermSemigroup(S),
                         CodegreeOfPartialPermSemigroup(S));
  combine := x -> PartialPerm(Concatenation(List(x, y -> y[1])),
                              Concatenation(List(x, y -> y[2])));
  convert := function(element, _, offset)
    return [DomainOfPartialPerm(element) + offset,
            ImageListOfPartialPerm(element) + offset];
  end;
  restrict := function(element, offset, _)
    local dom, start, stop, ran;
    dom := DomainOfPartialPerm(element);
    start := PositionSorted(dom, offset + 1);
    stop := PositionSorted(dom, offset + degree);
    if stop = Length(dom) + 1 or dom[stop] <> offset + degree then
      stop := stop - 1;
    fi;
    dom := dom{[start .. stop]} - offset;
    ran := ImageListOfPartialPerm(element){[start .. stop]} - offset;
    return PartialPerm(dom, ran);
  end;
  return SEMIGROUPS.DirectProductOp(list, degree, convert, combine, restrict);
end);

# Bipartition semigroups

InstallMethod(DirectProductOp, "for a list and a bipartition semigroup",
[IsList, IsBipartitionSemigroup],
function(list, S)
  local combine, convert, restrict;

  if IsEmpty(list) then
    ErrorNoReturn("the 1st argument (a list) is not non-empty");
  elif not ForAny(list, T -> IsIdenticalObj(S, T)) then
    ErrorNoReturn("the 2nd argument is not one of the semigroups ",
                  "contained in the 1st argument (a list)");
  elif not ForAll(list, IsBipartitionSemigroup) then
    TryNextMethod();
  fi;

  combine := x -> Bipartition(Concatenation(x));
  convert := function(element, _, offset)
    local x, i, j;
    x := List(ExtRepOfObj(element), ShallowCopy);
    for i in [1 .. Length(x)] do
      for j in [1 .. Length(x[i])] do
        if IsPosInt(x[i][j]) then
          x[i][j] := x[i][j] + offset;
        else
          x[i][j] := x[i][j] - offset;
        fi;
      od;
    od;
    return x;
  end;
  restrict := function(element, offset, degree)
    local new_bipartition, new_block, old_block, x;
    new_bipartition := [];
    for old_block in ExtRepOfObj(element) do
      if AbsInt(old_block[1]) in [offset + 1 .. offset + degree] then
        new_block := [];
        for x in old_block do
          if IsPosInt(x) then
            Add(new_block, x - offset);
          else
            Add(new_block, x + offset);
          fi;
        od;
        Add(new_bipartition, new_block);
      fi;
    od;
    return Bipartition(new_bipartition);
  end;
  return SEMIGROUPS.DirectProductOp(list,
                                    DegreeOfBipartitionSemigroup,
                                    convert,
                                    combine,
                                    restrict);
end);

# PBR semigroups

InstallMethod(DirectProductOp, "for a list and a pbr semigroup",
[IsList, IsPBRSemigroup],
function(list, S)
  local combine, convert, restrict;

  if IsEmpty(list) then
    ErrorNoReturn("the 1st argument (a list) is not non-empty");
  elif not ForAny(list, T -> IsIdenticalObj(S, T)) then
    ErrorNoReturn("the 2nd argument is not one of the semigroups ",
                  "contained in the 1st argument (a list)");
  elif not ForAll(list, IsPBRSemigroup) then
    TryNextMethod();
  fi;

  combine := x -> PBR(Concatenation(List(x, y -> y[1])),
                      Concatenation(List(x, y -> y[2])));
  convert := function(element, degree, offset)
    local x, i, j, k;
    x := ShallowCopy(ExtRepOfObj(element));
    for k in [1, 2] do
      for i in [1 .. degree] do
        for j in [1 .. Length(x[k][i])] do
          if IsPosInt(x[k][i][j]) then
            x[k][i][j] := x[k][i][j] + offset;
          else
            x[k][i][j] := x[k][i][j] - offset;
          fi;
        od;
      od;
    od;
    return x;
  end;
  restrict := function(element, offset, degree)
    local x, k, i, j;
    x := [ExtRepOfObj(element)[1]{[offset + 1 .. offset + degree]},
          ExtRepOfObj(element)[2]{[offset + 1 .. offset + degree]}];
    for k in [1, 2] do
      for i in [1 .. degree] do
        for j in [1 .. Length(x[k][i])] do
          if IsPosInt(x[k][i][j]) then
            x[k][i][j] := x[k][i][j] - offset;
          else
            x[k][i][j] := x[k][i][j] + offset;
          fi;
        od;
      od;
    od;
    return PBR(x[1], x[2]);
  end;
  return SEMIGROUPS.DirectProductOp(list, DegreeOfPBRSemigroup, convert,
                                    combine, restrict);
end);

# Other types of semigroups, or a hetergeneous list of semigroups

InstallMethod(DirectProductOp, "for a list and a semigroup",
[IsList, IsSemigroup],
function(list, S)
  local iso, prod, info;

  if IsEmpty(list) then
    ErrorNoReturn("the 1st argument (a list) is not non-empty");
  elif not ForAny(list, T -> IsIdenticalObj(S, T)) then
    ErrorNoReturn("the 2nd argument is not one of the semigroups ",
                  "contained in the 1st argument (a list)");
  elif not ForAll(list, IsSemigroup and IsFinite) then
    TryNextMethod();
  fi;

  iso := List(list, IsomorphismTransformationSemigroup);
  prod := DirectProduct(List(iso, Range));
  info := SemigroupDirectProductInfo(prod);
  info.factors := list;
  info.iso := iso;
  return prod;
end);

InstallMethod(Embedding,
"for a semigroup with semigroup direct product info and a pos int",
[IsSemigroup and HasSemigroupDirectProductInfo, IsPosInt],
function(D, i)
  local info, map;
  info := SemigroupDirectProductInfo(D);

  if IsBound(info.embeddings) and IsBound(info.embeddings[i]) then
    return info.embeddings[i];
  elif IsBound(info.nrfactors) and i > info.nrfactors then
    ErrorNoReturn("the 2nd argument (a pos. int.) is not in ",
                  "the range [1 .. ", info.nrfactors, "]");
  elif not IsBound(info.nrfactors) or not IsBound(info.embedding) then
    ErrorNoReturn("the direct product information for the 1st ",
                  "argument (a semigroup) is corrupted, please ",
                  "re-create the object");
  elif not IsBound(info.embeddings) then
    info.embeddings := [];
  fi;

  if IsBound(info.iso) then
    map := x -> info.embedding(x ^ info.iso[i], i);
    map := SemigroupHomomorphismByFunctionNC(info.factors[i], D, map);
  else
    map := SemigroupHomomorphismByFunctionNC(info.factors[i],
                                             D,
                                             x -> info.embedding(x, i));
  fi;
  info.embeddings[i] := map;
  return map;
end);

InstallMethod(Projection,
"for a semigroup with semigroup direct product info and a pos int",
[IsSemigroup and HasSemigroupDirectProductInfo, IsPosInt],
function(D, i)
  local info, map;
  info := SemigroupDirectProductInfo(D);

  if IsBound(info.projections) and IsBound(info.projections[i]) then
    return info.projections[i];
  elif IsBound(info.nrfactors) and i > info.nrfactors then
    ErrorNoReturn("the 2nd argument (a pos. int.) is not in ",
                  "the range [1 .. ", info.nrfactors, "]");
  elif not IsBound(info.nrfactors) or not IsBound(info.projection) then
    ErrorNoReturn("the direct product information for the 1st ",
                  "argument (a semigroup) is corrupted, please ",
                  "re-create the object");
  elif not IsBound(info.projections) then
    info.projections := [];
  fi;

  if IsBound(info.iso) then
    map := x -> info.projection(x, i) ^ InverseGeneralMapping(info.iso[i]);
    map := SemigroupHomomorphismByFunctionNC(D, info.factors[i], map);
  else
    map := SemigroupHomomorphismByFunctionNC(D,
                                             info.factors[i],
                                             x -> info.projection(x, i));
  fi;
  info.projections[i] := map;
  return map;
end);

InstallMethod(Size,
"for a semigroup with semigroup direct product info",
[IsSemigroup and HasSemigroupDirectProductInfo],
SUM_FLAGS,
function(D)
  if SemigroupDirectProductInfo(D).nrfactors = 1 then
    TryNextMethod();
  fi;
  return Product(List(SemigroupDirectProductInfo(D).factors, Size));
end);

InstallMethod(IsCommutativeSemigroup,
"for a semigroup with semigroup direct product info",
[IsSemigroup and HasSemigroupDirectProductInfo],
SUM_FLAGS,
function(D)
  if SemigroupDirectProductInfo(D).nrfactors = 1 then
    TryNextMethod();
  fi;
  return ForAll(SemigroupDirectProductInfo(D).factors, IsCommutativeSemigroup);
end);
