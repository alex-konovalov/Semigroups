#############################################################################
##
##  tools/io.gi
##  Copyright (C) 2013-2022                              James D. Mitchell
##
##  Licensing information can be found in the README file of this package.
##
#############################################################################
##

#############################################################################
# Internal functions - for reading and writing generators to a file
#############################################################################

# This function sets the component <decoder> of the IO file object <f> to a
# function that can be called on the file object to decode its contents. This
# is not called before anything is read from <f>.
SEMIGROUPS.FileDecoder := function(f)
  local char;

  if not IsBound(f!.decoder) then
    Assert(1, IsBound(f!.rpos) and f!.rpos = 1);
    char := IO_ReadBlock(f, 1);
    if char in ["t", "p", "b"] then
      # Use old style decoding
      f!.decoder := x -> SEMIGROUPS.ReadGeneratorsLine(Chomp(IO_ReadLine(x)));
    else
      # Use IO pickling
      f!.decoder := IO_Unpickle;
    fi;
    # Rewind, this is probably a bad idea.
    f!.rpos := 1;
    f!.rdata := f!.rdata + 1;
  fi;
  return f!.decoder;
end;

# This function converts a line in an old style "generators" file into the
# corresponding object.
SEMIGROUPS.ReadGeneratorsLine := function(line)
  local i, k, out, m, deg, f, j;

  i := 2;
  k := 0;
  out := [];

  while i < Length(line) do
    m := Int([line[i]]);                                       # blocksize
    deg := Int(NormalizedWhitespace(line{[i + 1 .. m + i]}));  # max domain
    f := line{[m + i + 1 .. i + m * (deg + 1)]};
    k := k + 1;
    out[k] := EmptyPlist(deg);
    for j in [1 .. deg] do
      Add(out[k], Int(NormalizedWhitespace(f{[(j - 1) * m + 1 .. j * m]})));
    od;
    i := i + m * (deg + 1) + 1;
  od;

  if Length(line) = 0 then
    return IO_Nothing;
  elif line[1] = 't' then  # transformations
    Apply(out, TransformationNC);
  elif line[1] = 'p' then  # partial perms
    Apply(out, DensePartialPermNC);
  elif line[1] = 'b' then  # bipartitions
    Apply(out, BIPART_NC);
  fi;

  return out;
end;

# This function converts a transformation/partial perm/bipartition collection
# <coll> in a line of an old style "generators" file and writes that line to
# the file <file>, using IO_WriteLine.
SEMIGROUPS.WriteGeneratorsLine := function(file, coll)
  local append, line, deg, nrdigits, x, i;

  append := function(str, pt, m)
    local i, j;

    i := String(pt);
    for j in [1 .. m - Length(i)] do
      Append(str, " ");
    od;
    Append(str, i);
    return str;
  end;

  if IsTransformationCollection(coll) then
    line := "t";
    for x in coll do
      deg := String(DegreeOfTransformation(x));
      nrdigits := Length(deg);
      Append(line, String(nrdigits));
      Append(line, deg);
      for i in [1 .. DegreeOfTransformation(x)] do
        append(line, i ^ x, nrdigits);
      od;
    od;
  elif IsPartialPermCollection(coll) then
    line := "p";
    for x in coll do
      deg := String(DegreeOfPartialPerm(x));
      nrdigits := Length(String(Maximum(DegreeOfPartialPerm(x),
                                        CodegreeOfPartialPerm(x))));
      Append(line, String(nrdigits));
      append(line, deg, nrdigits);
      for i in [1 .. DegreeOfPartialPerm(x)] do
        append(line, i ^ x, nrdigits);
      od;
    od;
  elif IsBipartitionCollection(coll) then
    line := "b";
    for x in coll do
      deg := String(2 * DegreeOfBipartition(x));
      nrdigits := Length(deg);
      Append(line, String(nrdigits));
      Append(line, deg);
      for i in IntRepOfBipartition(x) do
        append(line, i, nrdigits);
      od;
    od;
  fi;
  if IO_WriteLine(file, line) = fail then
    # Cannot test this line
    return IO_Error;
  else
    return IO_OK;
  fi;
end;

#############################################################################
# User functions - for reading and writing generators to a file
#############################################################################

InstallGlobalFunction(ReadGenerators,
function(arg)
  local name, line_nr, file, decoder, i, obj, out;

  if Length(arg) = 1 then
    name    := arg[1];
    line_nr := 0;      # Read all data
  elif Length(arg) = 2 then
    name    := arg[1];
    line_nr := arg[2];
  else
    ErrorNoReturn("there should be 1 or 2 arguments");
  fi;

  if IsString(name) then
    name := UserHomeExpand(name);
    file := IO_CompressedFile(name, "r");
    if file = fail then
      ErrorNoReturn("could not open the file ", name);
    fi;
  elif IsFile(name) then
    file := name;
  else
    ErrorNoReturn("the 1st argument is not a string or a file");
  fi;

  if not (IsInt(line_nr) and line_nr >= 0) then
    ErrorNoReturn("the 2nd argument is not a positive integer");
  fi;

  decoder := SEMIGROUPS.FileDecoder(file);

  if line_nr <> 0 then
    # When the first arg is a file this means get the line_nr-th entry from the
    # last read entry and not necessarily from the start of the file.
    i := 0;
    repeat
      i   := i + 1;
      obj := decoder(file);
      # This is potentially more costly than necessary, since we fully
      # decode every line, and then just throw it away.
    until i = line_nr or obj = IO_Nothing;

    if IsString(arg[1]) then
      IO_Close(file);
    fi;
    if obj = IO_Nothing then
      ErrorNoReturn("the file only has ", i - 1, " further entries");
    fi;
    return obj;
  else
    i   := 0;
    out := [];
    obj := decoder(file);
    while obj <> IO_Nothing do
      i      := i + 1;
      out[i] := obj;
      obj    := decoder(file);
    od;

    if IsString(arg[1]) then
      IO_Close(file);
    fi;
    return out;
  fi;
end);

InstallGlobalFunction(WriteGenerators,
function(arg)
  local name, collcoll, mode, file, encoder, coll;

  if Length(arg) = 2 then
    name     := arg[1];
    collcoll := arg[2];
    mode     := "w";
    encoder  := fail;
  elif Length(arg) = 3 then
    if IsString(arg[3]) then
      name     := arg[1];
      collcoll := arg[2];
      mode     := arg[3];
      encoder  := fail;
    elif IsFunction(arg[3]) then
      name     := arg[1];
      collcoll := arg[2];
      mode     := "w";
      encoder  := arg[3];
    else
      ErrorNoReturn("the 3rd argument is not a string or a function");
    fi;
  elif Length(arg) = 4 then
    name     := arg[1];
    collcoll := arg[2];
    mode     := arg[3];
    encoder  := arg[4];
  else
    ErrorNoReturn("there should be 2, 3, or 4 arguments");
  fi;

  if not (mode = "a" or mode = "w") then
    ErrorNoReturn("the 3rd argument is not \"a\" or \"w\"");
  elif IsString(name) then
    name := UserHomeExpand(name);
    file := IO_CompressedFile(name, mode);
    if file = fail then
      # Cannot test this
      ErrorNoReturn("couldn't open the file ", name);
    fi;
  elif IsFile(name) then
    file := name;
  else
    ErrorNoReturn("the 1st argument is not a string or a file");
  fi;

  if not IsList(collcoll) or IsEmpty(collcoll) then
    if IsString(name) then
      IO_Close(file);
    fi;
    ErrorNoReturn("the 2nd argument is not a non-empty list");
  fi;

  if encoder = fail then
    encoder := IO_Pickle;
  elif not IsFunction(encoder) then
    if IsString(name) then
      IO_Close(file);
    fi;
    ErrorNoReturn("the 3rd or 4th argument is not a function");
  fi;

  # Check encoder is consistent with <coll>
  if encoder = SEMIGROUPS.WriteGeneratorsLine
      and ForAny(collcoll, x -> not (IsTransformationCollection(x)
                                     or IsPartialPermCollection(x)
                                     or IsBipartitionCollection(x))) then
    if IsString(name) then
      IO_Close(file);
    fi;
    ErrorNoReturn("the 2nd argument is incompatible with the file format");
  fi;

  for coll in collcoll do
    if IsSemigroup(coll)
        and not (IsReesMatrixSemigroup(coll)
                 or IsReesZeroMatrixSemigroup(coll)) then
      coll := GeneratorsOfSemigroup(coll);
      # We could use a smaller generating set (i.e. GeneratorsOfMonoid,
      # GeneratorsOfInverseSemigroup etc) but we have no way of knowing which
      # generators we wrote, so better always use GeneratorsOfSemigroup.
    fi;
    if encoder(file, coll) = IO_Error then
      # Cannot test this line
      return IO_Error;
    fi;
  od;

  if IsString(name) then
    IO_Close(file);
  fi;
  return IO_OK;
end);

InstallGlobalFunction(IteratorFromGeneratorsFile,
function(filename)
  local file, decoder, record;

  filename := UserHomeExpand(filename);
  file     := IO_CompressedFile(filename, "r");

  if file = fail then
    return fail;
  fi;

  decoder := SEMIGROUPS.FileDecoder(file);

  record := rec(file     := file,
                filename := filename,
                decoder  := decoder,
                current  := decoder(file));

  record.NextIterator := function(iter)
    local next;
    next := iter!.current;
    iter!.current := iter!.decoder(iter!.file);
    return next;
  end;

  record.IsDoneIterator := function(iter)
    if iter!.current = IO_Nothing then
      if not iter!.file!.closed then
        IO_Close(iter!.file);
      fi;
      return true;
    else
      return false;
    fi;
  end;

  record.ShallowCopy := function(iter)
    return rec(file     := IO_CompressedFile(iter!.filename, "r"),
               filename := iter!.filename,
               decoder  := iter!.decoder,
               current  := iter!.decoder(~.file));
  end;

  return IteratorByFunctions(record);
end);

################################################################################
# User functions for multiplication tables
################################################################################

InstallGlobalFunction(ReadMultiplicationTable,
function(arg)
  local name, line_nr, file, ReadMultiplicationTableLine, i, line, lines;
  if Length(arg) = 1 then
    name    := arg[1];
    line_nr := 0;
  elif Length(arg) = 2 then
    name    := arg[1];
    line_nr := arg[2];
  else
    ErrorNoReturn("there should be 1 or 2 arguments");
  fi;
  if IsString(name) then
    name := UserHomeExpand(name);
    file := IO_CompressedFile(name, "r");
    if file = fail then
      ErrorNoReturn("could not open the file \"", name, "\"");
    fi;
  elif IsFile(name) then
    file := name;
  else
    ErrorNoReturn("the 1st argument is not a string or a file");
  fi;
  if not (IsInt(line_nr) and line_nr >= 0) then
    ErrorNoReturn("the 2nd argument is not a positive integer");
  fi;
  ReadMultiplicationTableLine := SEMIGROUPS.ReadMultiplicationTableLine;

  if line_nr <> 0 then
    i := 0;
    repeat
      i    := i + 1;
      line := IO_ReadLine(file);
    until i = line_nr or line = "";
    if IsString(arg[1]) then
      IO_Close(file);
    elif line = "" then
      ErrorNoReturn("the file only has ", i - 1, " lines");
    fi;
    return ReadMultiplicationTableLine(Chomp(line), RootInt(Length(line)));
  else
    lines := IO_ReadLines(file);
    if IsString(arg[1]) then
      IO_Close(file);
    fi;
    Apply(lines, line -> ReadMultiplicationTableLine(Chomp(line),
                                                   RootInt(Length(line))));
    return lines;
  fi;
end);

SEMIGROUPS.ReadMultiplicationTableLine := function(line, n)
  local table, vals, row, entry, i, j;
  table := EmptyPlist(n);
  vals := [0 .. n - 1];
  for i in vals do
    row := EmptyPlist(n);
    for j in vals do
      entry := IntChar(line[i * n + j + 1]);
      if entry = 0 then
        row[j + 1] := 10;
      else
        row[j + 1] := entry;
      fi;
    od;
    table[i + 1] := row;
  od;
  return table;
end;

InstallGlobalFunction(WriteMultiplicationTable,
function(arg)
  local name, coll, mode, file, str, i, j, k, n;

  if Length(arg) = 2 then
    name := arg[1];
    coll := arg[2];
    mode := "w";
  elif Length(arg) = 3 then
    name := arg[1];
    coll := arg[2];
    mode := arg[3];
  else
    ErrorNoReturn("there must be 2 or 3 arguments");
  fi;

  if not (mode = "a" or mode = "w") then
    ErrorNoReturn("the 3rd argument is not \"a\" or \"w\"");
  elif IsString(name) then
    name := UserHomeExpand(name);
    file := IO_CompressedFile(name, mode);
    if file = fail then
      # Cannot test this
      ErrorNoReturn("couldn't open the file ", name);
    fi;
  elif IsFile(name) then
    file := name;
  else
    ErrorNoReturn("the 1st argument is not a string or a file");
  fi;

  for i in [1 .. Length(coll)] do
    n := Size(coll[i]);  # Don't assume all multiplication tables are same size.
    if not (IsRectangularTable(coll[i]) and IsInt(coll[i][1][1])) then
      if IsString(name) then
        IO_Close(file);
      fi;
      ErrorNoReturn("the 2nd argument is not a collection of rectangular ",
                    "tables containing only integers");
    elif not n < 256 then
      if IsString(name) then
        IO_Close(file);
      fi;
      ErrorNoReturn("the 2nd argument is not a collection of rectangular ",
                    "tables with at most 255 rows");
    fi;

    str := EmptyString(n ^ 2 + 1);  # + 1 for newline character
    for j in [1 .. n] do
      for k in [1 .. n] do
        if not (0 < coll[i][j][k] and coll[i][j][k] <= n) then
          if IsString(name) then
            IO_Close(file);
          fi;
          ErrorNoReturn("the 2nd argument is not a collection of ",
                        "rectangular tables with integer entries from [1, 2, ",
                        "..., n] (where n equals the number of rows of the ",
                        "table)");
        elif coll[i][j][k] = 10 then
          Add(str, '\000');  # We use CharInt(0) since CharInt(10) is newline.
        else
          Add(str, CharInt(coll[i][j][k]));
        fi;
      od;
    od;
    Add(str, '\n');

    if IO_Write(file, str) = fail then
      # Cannot test this line
      return IO_Error;
    fi;
  od;

  if IsString(name) then
    IO_Close(file);
  fi;
  return IO_OK;
end);

InstallGlobalFunction(IteratorFromMultiplicationTableFile,
function(str)
  local file, line, record, n;

  file := IO_CompressedFile(UserHomeExpand(str), "r");

  if file = fail then
    return fail;
  fi;

  line := IO_ReadLine(file);
  n := RootInt(Length(line));
  line := SEMIGROUPS.ReadMultiplicationTableLine(Chomp(line), n);
  record := rec(file := file, current := line);

  record.NextIterator := function(iter)
    local next;
    next := iter!.current;
    iter!.current := IO_ReadLine(iter!.file);
    if iter!.current <> "" then
      iter!.current
        := SEMIGROUPS.ReadMultiplicationTableLine(Chomp(iter!.current), n);
    fi;
    return next;
  end;

  record.IsDoneIterator := function(iter)
    if iter!.current = "" then
      if not iter!.file!.closed then
        IO_Close(iter!.file);
      fi;
      return true;
    else
      return false;
    fi;
  end;

  # TODO store str in iter
  record.ShallowCopy := function(_)
    local file, line;
    file := IO_CompressedFile(UserHomeExpand(str), "r");
    line := SEMIGROUPS.ReadMultiplicationTableLine(Chomp(IO_ReadLine(file)), n);
    return rec(file := file, current := line);
  end;

  return IteratorByFunctions(record);
end);
