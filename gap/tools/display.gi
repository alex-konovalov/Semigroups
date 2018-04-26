#############################################################################
##
##  display.gi
##  Copyright (C) 2013-15                                James D. Mitchell
##
##  Licensing information can be found in the README file of this package.
##
#############################################################################
##

#############################################################################

SEMIGROUPS.TikzInit := Concatenation("%latex\n",
                                     "\\documentclass{minimal}\n",
                                     "\\usepackage{tikz}\n",
                                     "\\begin{document}\n");

SEMIGROUPS.TikzEnd := "\\end{document}";

SEMIGROUPS.TikzColors := ["red", "green", "blue", "cyan", "magenta", "yellow",
                          "black", "gray", "darkgray", "lightgray", "brown",
                          "lime", "olive", "orange", "pink", "purple", "teal",
                          "violet", "white"];

SEMIGROUPS.TikzArcPBR := Concatenation("\\newcommand{\\arc}{\\draw[semithick, ",
                                       "-{>[width = 1.5mm, length = ",
                                       "2.5mm]}]}\n");

SEMIGROUPS.TikzPBROpts         := rec(labels := false);
SEMIGROUPS.TikzBipartitionOpts := rec(colors        := false,
                                      beginDocument := true,
                                      endDocument   := true,
                                      labels        := true);
SEMIGROUPS.TikzBlocksOpts      := rec(labels := "above",
                                      edges  := "below",
                                      colors := false);

#############################################################################

InstallMethod(TikzString, "for a pbr",
[IsPBR],
function(x)
  return TikzString(x, SEMIGROUPS.TikzPBROpts);
end);

InstallMethod(TikzString, "for a pbr and record",
[IsPBR, IsRecord],
function(x, opts)
  local ext, n, str, coeff1, coeff2, jj, i, j;

  ext := ExtRepOfObj(x);
  n   := DegreeOfPBR(x);
  str := ShallowCopy(SEMIGROUPS.TikzInit);
  Append(str, "\\usetikzlibrary{arrows}\n");
  Append(str, "\\usetikzlibrary{arrows.meta}\n");
  Append(str, SEMIGROUPS.TikzArcPBR);
  Append(str, "\\begin{tikzpicture}[\n");
  Append(str, "  vertex/.style={circle, draw, fill=black, inner sep =");
  Append(str, "0.04cm},\n");
  Append(str, "  ghost/.style={circle, draw = none, inner sep = 0.14cm},\n");
  Append(str, "  botloop/.style={min distance = 8mm, out = -70, in = -110},\n");
  Append(str, "  toploop/.style={min distance = 8mm, out = 70, in = 110}]\n\n");

  # draw the vertices and their labels
  Append(str, "  % vertices and labels\n");
  Append(str, "  \\foreach \\i in {1,...,");
  Append(str, String(n));
  Append(str, "} {\n");

  if opts.labels then
    Append(str, "    \\node [vertex, label={[yshift=9mm]\\i}] ");
    Append(str, "at (\\i/1.5, 3) ");
    Append(str, "{};\n");
  else
    Append(str, "    \\node [vertex] at (\\i/1.5, 3) {};\n");
  fi;

  Append(str, "    \\node [ghost] (\\i) at (\\i/1.5, 3) {};\n");
  Append(str, "  }\n\n");

  Append(str, "  \\foreach \\i in {1,...,");
  Append(str, String(n));
  Append(str, "} {\n");

  if opts.labels then
    Append(str, "    \\node [vertex, label={[yshift=-15mm,");
    Append(str, "xshift=-0.5mm]-\\i}] at (\\i/1.5, 0) {};\n");
  else
    Append(str, "    \\node [vertex] at (\\i/1.5, 0) {};\n");
  fi;

  Append(str, "    \\node [ghost] (-\\i) at (\\i/1.5, 0) {};\n");
  Append(str, "  }\n\n");

  # draw the arcs
  for i in [1 .. n] do
    Append(str, "  % arcs from vertex ");
    Append(str, String(i));
    Append(str, "\n");

    for j in ext[1][i] do
      if j = i then
        Append(str, "  \\arc (");
        Append(str, String(i));
        Append(str, ") edge [toploop] (");
        Append(str, String(i));
        Append(str, ");\n");
      elif j > 0 then
        if i < j then
          coeff1 := 1;
          coeff2 := -1;
        else
          coeff1 := -1;
          coeff2 := 1;
        fi;

        Append(str, "  \\arc (");
        Append(str, String(i));
        Append(str, ") .. controls (");
        Append(str, String(i / 1.5 + (coeff1 * 0.4 * AbsInt(i - j))));
        Append(str, ", ");
        Append(str, String(Float(2.75 - (5 / (4 * n)) * AbsInt(i - j))));
        Append(str, ") and (");
        Append(str, String(j / 1.5 + (coeff2 * 0.4 * AbsInt(i - j))));
        Append(str, ", ");
        Append(str, String(Float(2.75 - (5 / (4 * n)) * AbsInt(i - j))));
        Append(str, ") .. (");
        Append(str, String(j));
        Append(str, ");\n");
      else
        Append(str, "  \\arc (");
        Append(str, String(i));
        Append(str, ") to (");
        Append(str, String(j));
        Append(str, ");\n");
      fi;
    od;
    Append(str, "\n");

    Append(str, "  % arcs from vertex -");
    Append(str, String(i));
    Append(str, "\n");
    for j in ext[2][i] do
      if j = -i then
        Append(str, "  \\arc (");
        Append(str, String(-i));
        Append(str, ") edge [botloop] (");
        Append(str, String(-i));
        Append(str, ");\n");
      elif j < 0 then
        jj := -j;
        if i < jj then
          coeff1 := 1;
          coeff2 := -1;
        else
          coeff1 := -1;
          coeff2 := 1;
        fi;

        Append(str, "  \\arc (");
        Append(str, String(-i));
        Append(str, ") .. controls (");
        Append(str, String(i / 1.5 + (coeff1 * 0.4 * AbsInt(i + j))));
        Append(str, ", ");
        Append(str, String(Float(0.25 + (5 / (4 * n)) * AbsInt(i + j))));
        Append(str, ") and (");
        Append(str, String(jj / 1.5 + (coeff2 * 0.4 * AbsInt(i + j))));
        Append(str, ", ");
        Append(str, String(Float(0.25 + (5 / (4 * n)) * AbsInt(i + j))));
        Append(str, ") .. (");
        Append(str, String(j));
        Append(str, ");\n");
      else
        Append(str, "  \\arc (");
        Append(str, String(-i));
        Append(str, ") to (");
        Append(str, String(j));
        Append(str, ");\n");
      fi;
    od;
    Append(str, "\n");
  od;

  Append(str, "\\end{tikzpicture}\n");
  Append(str, SEMIGROUPS.TikzEnd);
  return str;
end);

#############################################################################

InstallMethod(TikzString, "for a bipartition collection",
[IsBipartitionCollection],
function(coll)
  return TikzString(coll, SEMIGROUPS.TikzBipartitionOpts);
end);

InstallMethod(TikzString, "for a bipartition collection and record",
[IsBipartitionCollection, IsRecord],
function(coll, opts)
  local str, x;

  str := ShallowCopy(SEMIGROUPS.TikzInit);
  Append(str, "\\begin{center}");
  opts.beginDocument := false;
  opts.endDocument   := false;

  for x in coll do
    Append(str, TikzString(x, opts));
    Append(str, "\n\\bigskip\\bigskip\n\n");
  od;
  Append(str, "\\end{center}");

  Append(str, ShallowCopy(SEMIGROUPS.TikzEnd));
  return str;
end);

InstallMethod(TikzString, "for a bipartition",
[IsBipartition],
function(x)
  return TikzString(x, SEMIGROUPS.TikzBipartitionOpts);
end);

InstallMethod(TikzString, "for a bipartition and record",
[IsBipartition, IsRecord],
function(x, opts)
  local fill, draw, labels, ext, n, str, block, up, down, min, j, i, k;

  # Process the options
  SEMIGROUPS.ProcessOptionsRec(SEMIGROUPS.TikzBipartitionOpts, opts);

  if opts.colors and NrBlocks(x) < 20 then
    fill := i -> Concatenation("  \\fill[", SEMIGROUPS.TikzColors[i], "](");
    draw := i -> Concatenation("  \\draw[", SEMIGROUPS.TikzColors[i], "](");
  else
    fill := i -> "  \\fill(";
    draw := i -> "  \\draw(";
  fi;

  labels := opts.labels;

  ext := ExtRepOfObj(x);
  n   := DegreeOfBipartition(x);

  if opts.beginDocument = true then
    str := ShallowCopy(SEMIGROUPS.TikzInit);
  else
    str := "";
  fi;

  Append(str, "\\begin{tikzpicture}\n");

  # draw the lines
  for j in [1 .. Length(ext)] do
    block := ext[j];
    Append(str, "\n");
    Append(str, "  %block number ");
    Append(str, String(j));
    Append(str, "\n");
    Append(str, "  %vertices and labels\n");
    # vertices and their labels
    for i in block do
      if i > 0 then
        Append(str, fill(j));
        Append(str, String(i));
        Append(str, ", 2)circle(.125);\n");
        if labels then
          Append(str, draw(j));
          Append(str, String(i - 0.05));
          Append(str, ", 2.2) node [above] {$");
          Append(str, String(i));
          Append(str, "$};");
          Append(str, "\n");
        fi;
      else
        Append(str, fill(j));
        Append(str, String(-i));
        Append(str, ", 0)circle(.125);\n");
        if labels then
          Append(str, draw(j));
          Append(str, String(-i));
          Append(str, ", -0.2) node [below] {$-");
          Append(str, String(-i));
          Append(str, "$};");
          Append(str, "\n");
        fi;
      fi;
    od;

    Append(str, "\n  %lines\n");
    # lines
    up := [];
    down := [];
    for i in [2 .. Length(block)] do
      if block[i - 1] > 0 and block[i] > 0 then
        AddSet(up, block[i - 1]);
        AddSet(up, block[i]);
        Append(str, draw(j));
        Append(str, String(block[i - 1]));
        Append(str, ", 1.875) .. controls (");
        Append(str, String(block[i - 1]));
        Append(str, ", ");
        Append(str, String(Float(1.5 - (1 / (2 * n))
                               * (block[i] - block[i - 1]))));
        Append(str, ") and (");
        Append(str, String(block[i]));
        Append(str, ", ");
        Append(str, String(Float(1.5 - (1 / (2 * n))
                               * (block[i] - block[i - 1]))));
        Append(str, ") .. (");
        Append(str, String(block[i]));
        Append(str, ", 1.875);\n");
      elif block[i - 1] < 0 and block[i] < 0 then
        AddSet(down, block[i - 1]);
        AddSet(down, block[i]);
        Append(str, draw(j));
        Append(str, String(- block[i - 1]));
        Append(str, ", 0.125) .. controls (");
        Append(str, String(- block[i - 1]));
        Append(str, ", ");
        Append(str, String(Float(0.5 + (- 1 / (2 * n))
                               * (block[i] - block[i - 1]))));
        Append(str, ") and (");
        Append(str, String(- block[i]));
        Append(str, ", ");
        Append(str, String(Float(0.5 + (- 1 / (2 * n))
                               * (block[i] - block[i - 1]))));
        Append(str, ") .. (");
        Append(str, String(- block[i]));
        Append(str, ", 0.125);\n");
      elif block[i - 1] > 0 and block[i] < 0 then
        AddSet(down, block[i]);
        AddSet(up, block[i - 1]);
      elif block[i - 1] < 0 and block[i] > 0 then
        AddSet(down, block[i - 1]);
        AddSet(up, block[i]);
      fi;
    od;
    if Length(up) <> 0 and Length(down) <> 0 then
      min := [n + 1];
      down := down * -1;
      for i in up do
        for k in down do
          if AbsInt(i - k) < min[1] then
            min[1] := AbsInt(i - k);
            min[2] := i;
            min[3] := k;
          fi;
        od;
      od;
      Append(str, draw(j));
      Append(str, String(min[2]));
      Append(str, ", 2)--(");
      Append(str, String(min[3]));
      Append(str, ", 0);\n");
    fi;
  od;
  Append(str, "\\end{tikzpicture}\n\n");
  if opts.endDocument = true then
    Append(str, ShallowCopy(SEMIGROUPS.TikzEnd));
  fi;
  return str;
end);

#############################################################################

InstallMethod(DotString, "for a semigroup", [IsSemigroup],
function(S)
  return DotString(S, rec());
end);

InstallMethod(DotString, "for a semigroup and record",
[IsSemigroup, IsRecord],
function(S, opts)
  local es, elts, str, i, color, pos, gp, iso, inv, RMS, mat, G, x, rel, ii,
  di, j, dk, k, d, l, row, col;

  # process the options
  if not IsBound(opts.maximal) then
    opts.maximal := false;
  fi;
  if not IsBound(opts.number) then
    opts.number := true;
  fi;
  if not IsBound(opts.normal) then
    opts.normal := true;
  fi;
  if not IsBound(opts.highlight) then
    opts.highlight := false;  # JDM means highlight H-classes
  else
    for x in opts.highlight do
      if not IsBound(x.HighlightGroupHClassColor) then
        x.HighlightGroupHClassColor := "#880000";
      fi;

      if not IsBound(x.HighlightNonGroupHClassColor) then
        x.HighlightNonGroupHClassColor := "#FF0000";
      fi;
    od;
  fi;

  if not IsBound(opts.idempotentsemilattice) then
    opts.idempotentsemilattice := false;
  elif opts.idempotentsemilattice then
    es := IdempotentGeneratedSubsemigroup(S);
    elts := Elements(es);  # JDM could be enumerator sorted
  fi;

  str := "//dot\n";
  Append(str, "digraph  DClasses {\n");
  Append(str, "node [shape=plaintext]\n");
  Append(str, "edge [color=black,arrowhead=none]\n");
  i := 0;

  for d in DClasses(S) do

    i := i + 1;
    Append(str, String(i));
    Append(str, " [shape=box style=invisible ");
    Append(str, "label=<\n<TABLE BORDER=\"0\" CELLBORDER=\"1\"");
    Append(str, " CELLPADDING=\"10\" CELLSPACING=\"0\"");
    Append(str, Concatenation(" PORT=\"", String(i), "\">\n"));

    if opts.number then
      Append(str, "<TR BORDER=\"0\"><TD COLSPAN=\"");
      Append(str, String(NrRClasses(d)));
      Append(str, "\" BORDER = \"0\" > ");
      Append(str, String(i));
      Append(str, "</TD></TR>");
    fi;

    if not IsRegularDClass(d) then
      for l in LClasses(d) do
        Append(str, "<TR>");
        for x in HClasses(l) do
          color := "white";
          if opts.highlight <> false then
            pos := PositionProperty(opts.highlight,
                                    record -> x in record.HClasses);
            if pos <> fail then
              color := opts.highlight[pos].HighlightNonGroupHClassColor;
            fi;
          fi;
          Append(str, Concatenation("<TD CELLPADDING=\"10\" BGCOLOR=\"",
                                    color,
                                    "\"><font color=\"white\">*</font></TD>"));
        od;
        Append(str, "</TR>\n");
      od;
      Append(str, "</TABLE>>];\n");
      continue;
    fi;

    if opts.maximal then
      gp := StructureDescription(GroupHClass(d));
    fi;

    if opts.normal then
      iso := InjectionNormalizedPrincipalFactor(d);
    else
      iso := InjectionPrincipalFactor(d);
    fi;
    inv := InverseGeneralMapping(iso);
    RMS := Range(iso);
    mat := Matrix(RMS);
    G := UnderlyingSemigroup(RMS);

    for col in Columns(RMS) do  # Columns of RMS = RClasses
      Append(str, "<TR>");
      for row in Rows(RMS) do  # Rows of RMS = LClasses
        Append(str, "<TD BGCOLOR=\"");
        if opts.highlight <> false then
          x := HClass(d, RMSElement(RMS, row, Identity(G), col) ^ inv);
          pos := PositionProperty(opts.highlight, rcd -> x in rcd.HClasses);
        fi;
        if mat[col][row] <> 0 then
          # group H-class
          if opts.highlight <> false and pos <> fail then
            color := opts.highlight[pos].HighlightGroupHClassColor;
          else
            color := "gray";
          fi;
          Append(str, color);
          Append(str, "\"");
          if opts.maximal then
            Append(str, ">");
            Append(str, gp);
          else
            if opts.idempotentsemilattice then
              x := HClass(d, RMSElement(RMS, row, Identity(G), col) ^ inv);
              Append(str, " PORT=\"e");
              Append(str, String(Position(elts, Idempotents(x)[1])));
              Append(str, "\"");
            fi;
            Append(str, ">*");
          fi;
        else
          # non-group H-class
          if opts.highlight <> false and pos <> fail then
            color := opts.highlight[pos].HighlightNonGroupHClassColor;
          else
            color := "white";
          fi;
          Append(str, color);
          Append(str, "\">");
        fi;
        Append(str, "</TD>");
      od;
      Append(str, "</TR>\n");
    od;
    Append(str, "</TABLE>>];\n");
  od;

  # TODO make PartialOrderOfDClasses return a digraph
  rel := OutNeighbours(DigraphReflexiveTransitiveReduction(
                       Digraph(PartialOrderOfDClasses(S))));
  for i in [1 .. Length(rel)] do
    ii := String(i);
    for k in rel[i] do
      Append(str, Concatenation(ii, " -> ", String(k), "\n"));
    od;
  od;

  # add semilattice of idempotents
  if opts.idempotentsemilattice then
    Append(str, "edge [color=blue,arrowhead=none,style=dashed]\n");
    rel := NaturalPartialOrder(es);

    for i in [1 .. Length(rel)] do
      di := String(Position(DClasses(S), DClass(S, elts[i])));
      j := Difference(rel[i], Union(rel{rel[i]}));
      i := String(i);
      for k in j do
        dk := String(Position(DClasses(S), DClass(S, elts[k])));
        k := String(k);
        Append(str, Concatenation(di, ":e", i, " -> ", dk, ":e", k, "\n"));
      od;
    od;
  fi;
  Append(str, " }");

  return str;
end);

InstallMethod(DotSemilatticeOfIdempotents,
"for inverse semigroup with inverse op",
[IsInverseSemigroup and IsGeneratorsOfInverseSemigroup],
function(S)
  local U, rel, elts, str, nr, V, j, i, k, D, v;

  U := IdempotentGeneratedSubsemigroup(S);
  rel := NaturalPartialOrder(U);
  elts := Elements(U);

  str := "//dot\n";

  Append(str, "graph graphname {\n  node [shape=point]\n");
  Append(str, "ranksep=2;\n");

  nr := 0;
  for D in GreensDClasses(S) do
    nr := nr + 1;
    V := List(Idempotents(D), x -> String(Position(elts, x)));
    Append(str, Concatenation("subgraph cluster_", String(nr), "{\n"));
    for v in V do
      Append(str, v);
      Append(str, " ");
    od;
    Append(str, "\n");
    Append(str, "}\n");
  od;

  for i in [1 .. Length(rel)] do
    j := Difference(rel[i], Union(rel{rel[i]}));
    i := String(i);
    for k in j do
      k := String(k);
      Append(str, Concatenation(i, " -- ", k, "\n"));
    od;
  od;

  Append(str, " }");

  return str;
end);

InstallMethod(TexString, "for a transformation and a pos int",
[IsTransformation, IsPosInt],
function(f, deg)
  local str, i;

  if deg < DegreeOfTransformation(f) then
    ErrorNoReturn("Semigroups: TexString: usage,\n",
                  "the second argument (the degree) should be at ",
                  "least the degree of the first argument (a ",
                  "transformation),");
  fi;
  str := "\\begin{pmatrix}\n  ";
  for i in [1 .. deg] do
    Append(str, String(i));
    if i <> deg then
      Append(str, " & ");
    fi;
  od;
  Append(str, " \\\\\n  ");
  for i in [1 .. deg] do
    Append(str, String(i ^ f));
    if i <> deg then
      Append(str, " & ");
    fi;
  od;
  Append(str, "\n\\end{pmatrix}");
  return str;
end);

InstallMethod(TexString, "for a transformation",
[IsTransformation],
function(f)
  return TexString(f, DegreeOfTransformation(f));
end);

InstallMethod(TexString, "for a transformation collection",
[IsTransformationCollection],
function(coll)
  local deg;
  deg := DegreeOfTransformationCollection(coll);
  return JoinStringsWithSeparator(List(coll, x -> TexString(x, deg)), "\n");
end);
