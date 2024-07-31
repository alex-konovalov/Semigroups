###########################################################################
##
##  libsemigroups/ranges.gi
##  Copyright (C) 2023                                   James D. Mitchell
##
##  Licensing information can be found in the README file of this package.
##
###########################################################################
##

InstallMethod(Iterator, "for a RangeObj", [IsRangeObj],
function(range)
  local iter;

  iter := rec();
  iter.RangeObj := range;
  iter.NextIterator := function(it)
    local result;
    result := Get(it!.RangeObj);
    Next(it!.RangeObj);
    return result;
  end;
  iter.IsDoneIterator := it -> AtEnd(it!.RangeObj);

  iter.ShallowCopy := function(it)
    local copy;
    copy := rec();
    copy.NextIterator := it.NextIterator;
    copy.IsDoneIterator := it.IsDoneIterator;
    # TODO should be Words(it.RangeObj)
    copy.RangeObj := it.RangeObj;
  end;

  return IteratorByFunctions(iter);
end);

InstallMethod(AsList, "for a RangeObj", [IsRangeObj],
function(range)
  local result, x;
  result := EmptyPlist(Count(range));
  for x in range do
    Add(result, x);
  od;
  return result;
end);
