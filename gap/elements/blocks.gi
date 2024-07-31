############################################################################
##
##  elements/blocks.gi
##  Copyright (C) 2013-2022                              James D. Mitchell
##
##  Licensing information can be found in the README file of this package.
##
#############################################################################
##

#############################################################################
# Blocks are stored internally as a list consisting of:
#
# [ nr of blocks, internal rep of blocks, transverse blocks ]
#
# <nr of blocks> is a non-negative integer, <internal rep of blocks>[i] = j if
# <i> belongs to the <j>th block, <transverse blocks>[j] = 1 if block <j> is
# transverse and 0 if it is not.
#############################################################################

#############################################################################
# GAP level - directly using interface to C/C++ level
#############################################################################

InstallMethod(LeftBlocks, "for a bipartition", [IsBipartition],
BIPART_LEFT_BLOCKS);

InstallMethod(RightBlocks, "for a bipartition", [IsBipartition],
BIPART_RIGHT_BLOCKS);

InstallMethod(ExtRepOfObj, "for blocks", [IsBlocks], BLOCKS_EXT_REP);

InstallMethod(ChooseHashFunction, "for blocks", [IsBlocks, IsInt],
function(_, hashlen)
  return rec(func := BLOCKS_HASH,
             data := hashlen);
end);

InstallMethod(DegreeOfBlocks, "for blocks", [IsBlocks], BLOCKS_DEGREE);
InstallMethod(RankOfBlocks, "for blocks", [IsBlocks], BLOCKS_RANK);
InstallMethod(NrBlocks, "for blocks", [IsBlocks], BLOCKS_NR_BLOCKS);
InstallMethod(\=, "for blocks", [IsBlocks, IsBlocks], BLOCKS_EQ);
InstallMethod(\<, "for blocks", [IsBlocks, IsBlocks], BLOCKS_LT);
InstallMethod(ProjectionFromBlocks, "for blocks", [IsBlocks], BLOCKS_PROJ);
InstallMethod(OnRightBlocks, "for blocks and a bipartition",
[IsBlocks, IsBipartition], BLOCKS_RIGHT_ACT);
InstallMethod(OnLeftBlocks, "for blocks and a bipartition",
[IsBlocks, IsBipartition], BLOCKS_LEFT_ACT);

#############################################################################
# GAP level - NOT directly using interface to C/C++ level
#############################################################################

InstallMethod(AsDigraph, "for blocks", [IsBlocks],
function(blocks)
  local ext, out, block, i;

  ext := ExtRepOfObj(blocks);
  out := List([1 .. DegreeOfBlocks(blocks)], x -> []);

  for block in ext do
    if block[1] > 0 then  # transverse block
      for i in block do
        out[i] := ShallowCopy(block);
        RemoveSet(out[i], i);
      od;
    else
      for i in block do
        out[-i] := block * -1;
      od;
    fi;
  od;
  return Digraph(out);
end);

InstallMethod(CanonicalBlocks, "for blocks", [IsBlocks],
function(blocks)
  local gr, canon, scc, rep, i;

  gr := AsDigraph(blocks);
  gr := OnDigraphs(gr, BlissCanonicalLabelling(gr));
  canon := [];

  scc := DigraphStronglyConnectedComponents(gr).comps;
  canon := ShallowCopy(scc);

  for i in [1 .. Length(scc)] do
    rep := scc[i][1];
    if IsDigraphEdge(gr, [rep, rep]) then
      canon[i] := -1 * canon[i];
    fi;
  od;

  return BLOCKS_NC(canon);
end);

# not a synonym since NrTransverseBlocks applies to a bipartition also
InstallMethod(NrTransverseBlocks, "for blocks", [IsBlocks], RankOfBlocks);

# Printing, viewing etc . . .

InstallMethod(String, "for blocks", [IsBlocks],
x -> Concatenation("BLOCKS_NC(", String(ExtRepOfObj(x)), ")"));

InstallMethod(ViewObj, "for blocks", [IsBlocks],
function(blocks)
  local ext, str, i;

  ext := ExtRepOfObj(blocks);
  if Length(ext) > 0 then
    Print("<blocks: ");
    if ext[1][1] < 0 then
      Print(-1 * ext[1]);
    else
      str := JoinStringsWithSeparator(List(ext[1], String), "*, ");
      Print("[ ", str, "* ]");
    fi;
    for i in [2 .. Length(ext)] do
      if ext[i][1] < 0 then
        Print(", ", -1 * ext[i]);
      else
        str := JoinStringsWithSeparator(List(ext[i], String), "*, ");
        Print(", [ ", str, "* ]");
      fi;
    od;
  else
    Print("<empty blocks");
  fi;

  Print(">");
end);

InstallMethod(PrintObj, "for blocks", [IsBlocks], 10,
function(blocks)
  Print(PrintString(blocks));
end);
