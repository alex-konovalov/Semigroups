#############################################################################
##
#W  greens.gi
#Y  Copyright (C) 2011-12                                James D. Mitchell
##
##  Licensing information can be found in the README file of this package.
##
#############################################################################
##

# for convenience...

# new for 1.0! - EquivalenceClassRelation - "for a Green's class of acting semi"
##############################################################################

InstallMethod(EquivalenceClassRelation, "for a Green's class of acting semi",
[IsActingSemigroupGreensClass], 
function(x)

  if IsGreensRClass(x) then 
    return GreensRRelation(ParentSemigroup(x));
  elif IsGreensLClass(x) then 
    return GreensLRelation(ParentSemigroup(x));
  elif IsGreensDClass(x) then 
    return GreensDRelation(ParentSemigroup(x));
  elif IsGreensHClass(x) then 
    return GreensHRelation(ParentSemigroup(x));
  fi;

  return fail;
end);

# new for 1.0! - RhoOrbStabChain - "for an L-class of an acting semi"
##############################################################################

InstallMethod(RhoOrbStabChain, "for an L-class of an acting semi",
[IsGreensLClass and IsActingSemigroupGreensClass],
function(l)
  return StabChainImmutable(SchutzenbergerGroup(l));
end);

# new for 1.0! - RhoCosets - "for a D-class of an acting semigp"
##############################################################################

InstallMethod(RhoCosets, "for a D-class of an acting semigp",
[IsGreensDClass and IsActingSemigroupGreensClass], 
function(d)
  SchutzenbergerGroup(d);
  return RhoCosets(d);
end);

# new for 1.0! - SemigroupDataSCC - "for a D-class of an acting semigp"
##############################################################################
# JDM this is useful in PartialOrderOfDClasses...

InstallMethod(SemigroupDataSCC, "for a D-class of an acting semigroup",
[IsGreensDClass and IsActingSemigroupGreensClass],
function(d)
  local data;
  if not HasSemigroupDataIndex(d) then 
    return fail;
  fi;
  data:=SemigroupData(ParentSemigroup(d));

  # scc of R-reps corresponding to d 
  return OrbSCC(data)[OrbSCCLookup(data)[SemigroupDataIndex(d)]];
end);

# new for 1.0! - LambdaCosets - "for a D-class of an acting semigp"
##############################################################################

InstallMethod(LambdaCosets, "for a D-class of an acting semigroup",
[IsGreensDClass and IsActingSemigroupGreensClass],
function(d)
  return RightTransversal(LambdaOrbSchutzGp(LambdaOrb(d),
   LambdaOrbSCCIndex(d)), SchutzenbergerGroup(d));
end);

# new for 1.0! - LambdaOrbSCCIndex - "for a Green's class of an acting semigp"
##############################################################################

InstallMethod(LambdaOrbSCCIndex, "for a Green's class of an acting semigroup", 
[IsActingSemigroupGreensClass and IsGreensDClass], 
function(d)
  local o;
    
  if d!.lambda_m<>fail then 
    return d!.lambda_m;
  fi;

  o:=RhoOrb(d);
  return OrbSCCLookup(o)[Position(o,
   RhoFunc(ParentSemigroup(d))(Representative(d)))];
end);

# new for 1.0! - LambdaOrbSCC - "for Green's class of an acting semigroup"
############################################################################

InstallOtherMethod(LambdaOrbSCC, "for a Green's class of an acting semi",
[IsActingSemigroupGreensClass and IsGreensClass],
x-> OrbSCC(LambdaOrb(x))[LambdaOrbSCCIndex(x)]);

InstallOtherMethod(RhoOrbSCC, "for a Green's class of an acting semi",
[IsActingSemigroupGreensClass and IsGreensClass], 
x-> OrbSCC(RhoOrb(x))[RhoOrbSCCIndex(x)]);

# new for 1.0! - SchutzenbergerGroup - "for an R-class of an acting semigp."
#############################################################################

InstallOtherMethod(SchutzenbergerGroup, "for an R-class of an acting semigp.",
[IsGreensRClass and IsActingSemigroupGreensClass],
r-> LambdaOrbSchutzGp(LambdaOrb(r), LambdaOrbSCCIndex(r)));

# new for 1.0! - SchutzenbergerGroup - "for an L-class of an acting semigp."
#############################################################################

InstallOtherMethod(SchutzenbergerGroup, "for an L-class of an acting semigp.",
[IsGreensLClass and IsActingSemigroupGreensClass],
function(l)
  local o, m, p;

  o:=RhoOrb(l); m:=RhoOrbSCCIndex(l);
  
  if not IsGreensClassNC(l) then 
    p:=RhoPerm(ParentSemigroup(l))(RhoOrbRep(o, m), Representative(l));
    return RhoOrbSchutzGp(o, m, infinity)^p;
  fi;
  return RhoOrbSchutzGp(o, m, infinity); 
end);

#############################################################################
#############################################################################

# new for 1.0! - \= - "for Green's class and Green's class of acting semigp"
#############################################################################

InstallMethod(\=, "for Green's class and class of acting semigp",
[IsActingSemigroupGreensClass, IsActingSemigroupGreensClass],
function(x, y)
  if (IsGreensRClass(x) and IsGreensRClass(y)) or
   (IsGreensLClass(x) and IsGreensLClass(y)) or
   (IsGreensDClass(x) and IsGreensDClass(y)) or
   (IsGreensHClass(x) and IsGreensHClass(y)) then
    return ParentSemigroup(x)=ParentSemigroup(y) and Representative(x) in y;
  fi;
  return ParentSemigroup(x)=ParentSemigroup(y) and Representative(x) in y and
   Size(x)=Size(y);
end);

# new for 1.0! - \< - "for Green's class and Green's class of acting semigp"
#############################################################################

InstallMethod(\<, "for Green's class and class of acting semigp",
[IsActingSemigroupGreensClass, IsActingSemigroupGreensClass],
function(x, y)
  if (IsGreensRClass(x) and IsGreensRClass(y)) or
   (IsGreensLClass(x) and IsGreensLClass(y)) or
   (IsGreensDClass(x) and IsGreensDClass(y)) or
   (IsGreensHClass(x) and IsGreensHClass(y)) then
    return ParentSemigroup(x)=ParentSemigroup(y) and Representative(x) <
     Representative(y);
  fi;
  return fail;
end);

# new for 1.0! - \in - "for acting elt and D-class of acting semigp"
#############################################################################

#JDM revise this as per the other version of \in just deleted :)

InstallMethod(\in, "for acting elt and D-class of acting semigp.",
[IsActingElt, IsGreensDClass and IsActingSemigroupGreensClass],
function(f, d)
  local rep, s, g, m, o, scc, l, schutz, cosets, x;
  
  rep:=Representative(d); 
  s:=ParentSemigroup(d);
 
  # much much better performance using f[2]<>rep[2] below
  if ElementsFamily(FamilyObj(s)) <> FamilyObj(f) or f[2] <> rep[2] then
    return false;
  fi;

  g:=f;

  m:=LambdaOrbSCCIndex(d); o:=LambdaOrb(d); scc:=OrbSCC(o);

  l:=Position(o, LambdaFunc(s)(g));

  if l = fail or OrbSCCLookup(o)[l]<>m then 
    return false;
  fi;
  
  if l<>scc[m][1] then 
    g:=g*LambdaOrbMults(o, m)[l];
  fi;

  m:=RhoOrbSCCIndex(d); o:=RhoOrb(d); scc:=OrbSCC(o); 

  l:=Position(o, RhoFunc(s)(g));

  if l = fail or OrbSCCLookup(o)[l]<>m then 
    return false;
  fi;

  schutz:=RhoOrbStabChain(o, m);

  if schutz=true then 
    return true;
  fi;

  if l<>scc[m][1] then 
    g:=RhoOrbMults(o, m)[l][2]*g;
  fi;

  cosets:=LambdaCosets(d);
  g:=LambdaPerm(s)(rep, g);

  if schutz<>false then 
    for x in cosets do 
      if SiftedPermutation(schutz, g/x)=() then 
        return true;
      fi;
    od;
  else #JDM is search really necessary? 
    for x in cosets do 
      if g/x=() then 
        return true;
      fi;
    od;
  fi;

  return false;
end);

# new for 1.0! - \in - "for acting elt and L-class of acting semigp"
#############################################################################
#JDM this method differs from the one in 0.99. 

InstallMethod(\in, "for acting elt and L-class of acting semigp.",
[IsActingElt, IsGreensLClass and IsActingSemigroupGreensClass],
function(f, l)
  local rep, s, m, o, i, schutz, g, p;

  rep:=Representative(l); 
  s:=ParentSemigroup(l);

  #JDM degree causes problems for partial perms below...
  if ElementsFamily(FamilyObj(s)) <> FamilyObj(f) #or Degree(f) <> Degree(rep)
   or Rank(f) <> Rank(rep) or LambdaFunc(s)(f) <> LambdaFunc(s)(rep) then
    Info(InfoCitrus, 1, "degree, rank, or lambda value not equal to those of",
    " any of the L-class elements,");
    return false;
  fi;

  m:=RhoOrbSCCIndex(l);
  o:=RhoOrb(l);
  
  if not IsClosed(o) then 
    Enumerate(o, infinity);
  fi;

  i:=Position(o, RhoFunc(s)(f));

  if i = fail or OrbSCCLookup(o)[i]<>m then 
    return false;
  fi;

  schutz:=RhoOrbStabChain(l);

  if schutz=true then
    Info(InfoCitrus, 3, "Schutz. group of L-class is symmetric group");
    return true;
  fi;

  g:=RhoOrbMults(o, m)[i][2]*f;

  if g=rep then
    Info(InfoCitrus, 3, "element with rectified rho value equals ",
    "L-class representative");
    return true;
  elif schutz=false then
    Info(InfoCitrus, 3, "Schutz. group of L-class is trivial");
    return false;
  fi;
  
  return SiftedPermutation(schutz, LambdaPerm(s)(rep, g))=();
end);

# new for 1.0! - \in - "for acting elt and R-class of acting semigp"
#############################################################################
# Algorithm E. 

InstallMethod(\in, "for acting elt and R-class of acting semigp.",
[IsActingElt, IsGreensRClass and IsActingSemigroupGreensClass],
function(f, r)
  local rep, s, m, o, l, schutz, g;

  rep:=Representative(r); 
  s:=ParentSemigroup(r);

  #JDM degree causes problems for partial perms below...
  if ElementsFamily(FamilyObj(s)) <> FamilyObj(f) #or Degree(f) <> Degree(rep)
   or Rank(f) <> Rank(rep) or RhoFunc(s)(f) <> RhoFunc(s)(rep) then
    Info(InfoCitrus, 1, "degree, rank, or rho value not equal to those of",
    " any of the R-class elements,");
    return false;
  fi;

  m:=LambdaOrbSCCIndex(r);
  o:=LambdaOrb(r);
  
  if not IsClosed(o) then 
    Enumerate(o, infinity);
  fi;

  l:=Position(o, LambdaFunc(s)(f));

  if l = fail or OrbSCCLookup(o)[l]<>m then 
    return false;
  fi;

  schutz:=LambdaOrbStabChain(o, m);

  if schutz=true then
    Info(InfoCitrus, 3, "Schutz. group of R-class is symmetric group");
    return true;
  fi;

  g:=f*LambdaOrbMults(o, m)[l];

  if g=rep then
    Info(InfoCitrus, 3, "element with rectified lambda value equals ",
    "R-class representative");
    return true;
  elif schutz=false then
    Info(InfoCitrus, 3, "Schutz. group of R-class is trivial");
    return false;
  fi;

  return SiftedPermutation(schutz, LambdaPerm(s)(rep, g))=();
end);

#AAA

# new for 1.0! - AsList - "for an R-class of an acting semigp."
#############################################################################
# Algorithm D.

InstallOtherMethod(AsList, "for an R-class of an acting semigp.",
[IsGreensRClass and IsActingSemigroupGreensClass],
function(r)        
  local f, g, elts, o, m, mults, scc, p, i;
  
  f:=Representative(r); 
  o:=LambdaOrb(r); 
  m:=LambdaOrbSCCIndex(r);
 
  g:=List(SchutzenbergerGroup(r), x-> f*x);
  elts:=EmptyPlist(Size(r));
  
  mults:=LambdaOrbMults(o, m);
  scc:=OrbSCC(o)[m];
  
  for i in scc do
    p:=mults[i]; 
    Append(elts, g*p^-1);
  od;
  
  return elts;
end);

# new for 0.1! - AsSSortedList - "for a Green's class of an acting semigp"
#############################################################################
# this should be removed after the library method for AsSSortedList 
# for a Green's class is removed. The default AsSSortedList for a collection
# is what should be used (it is identical)!

InstallOtherMethod(AsSSortedList, "for a Green's class of an acting semigp",
[IsGreensClass and IsActingSemigroupGreensClass], 
function(c)
  return ConstantTimeAccessList(EnumeratorSorted(c));
end);

#CCC

# new for 1.0! - CreateDClass - not a user function! 
############################################################################# 
# Usage: arg[1] = semigroup; arg[2] = lambda orb scc index;
# arg[3] = lambda orb; arg[4] = rep; arg[5] = position in SemigroupData of rep.

# only for D-classes being created in GreensDClasses or similar!

InstallGlobalFunction(CreateDClass,  
function(arg) 
  local d, rep, o, l, m;
 
  d:=Objectify(DClassType(arg[1]), rec()); 
          
  SetParentSemigroup(d, arg[1]);
  SetLambdaOrb(d, arg[3]);
  SetLambdaOrbSCCIndex(d, arg[2]);
  SetSemigroupDataIndex(d, arg[5]);

  rep:=arg[4];
  o:=RhoOrb(arg[1]);
  
  if not IsClosed(o) then 
    Enumerate(o, infinity);
  fi;

  l:=Position(o, RhoFunc(arg[1])(rep));
  m:=OrbSCCLookup(o)[l];

  if l<>OrbSCC(o)[m][1] then 
    rep:=RhoOrbMults(o, m)[l][2]*rep;
  fi;

  SetRepresentative(d, rep);
  SetRhoOrb(d, o);
  SetRhoOrbSCCIndex(d, m);
  SetEquivalenceClassRelation(d, GreensDRelation(arg[1])); 
  SetIsGreensClassNC(d, false);

  return d; 
end); 

# mod for 1.0! - CreateLClass - not a user function!
#############################################################################

# so far only used in GreensLClasses of a D-class. 

InstallGlobalFunction(CreateLClass,
function(arg)
  local l;

  l:=Objectify(LClassType(arg[1]), rec());

  SetParentSemigroup(l, arg[1]);
  SetRhoOrbSCCIndex(l, arg[2]);
  SetRhoOrb(l, arg[3]);
  SetRepresentative(l, arg[4]);
  
  SetEquivalenceClassRelation(l, GreensLRelation(arg[1]));
  SetIsGreensClassNC(l, true); 
  return l;
end);

# mod for 1.0! - CreateRClass - not a user function!
#############################################################################
# Usage: arg[1] = semigroup; arg[2] = lambda orb scc index;
# arg[3] = lambda orb; arg[4] = rep; arg[5] = position in SemigroupData of rep.

# only use for R-classes created from SemigroupData. 

InstallGlobalFunction(CreateRClass,
function(arg)
  local r;
  
  r:=Objectify(RClassType(arg[1]), rec());

  SetParentSemigroup(r, arg[1]);
  SetLambdaOrbSCCIndex(r, arg[2]);
  SetLambdaOrb(r, arg[3]);
  SetRepresentative(r, arg[4]);
  SetSemigroupDataIndex(r, arg[5]);

  SetEquivalenceClassRelation(r, GreensRRelation(arg[1]));
  SetIsGreensClassNC(r, false);
  return r;
end);

#EEE

# mod for 1.0! - Enumerator - "for a D-class of acting semigp."
#############################################################################

InstallOtherMethod(Enumerator, "for a D-class of acting semigp.",
[IsGreensDClass and IsActingSemigroupGreensClass],
function(d)

    return EnumeratorByFunctions(d, rec(

    m:=Length(LambdaOrbSCC(d))*Size(LambdaOrbSchutzGp(LambdaOrb(d),
     LambdaOrbSCCIndex(d))),
    # size of any R-class in d.

    #######################################################################

    ElementNumber:=function(enum, pos)
    local q, n, m, R;

      if pos>Length(enum) then
        return fail;
      fi;

      R:=GreensRClasses(d);
      n:=pos-1;
      m:=enum!.m;

      q := QuoInt(n, m);
      pos:= [ q, n - q * m ]+1;

      return Enumerator(R[pos[1]])[pos[2]];
    end,

    #######################################################################

    NumberElement:=function(enum, f)
      
      s:=ParentSemigroup(d);

      if ElementsFamily(FamilyObj(s)) <> FamilyObj(f) or f[2] <> rep[2] then
        return fail;
      fi;

      g:=f;
      m:=LambdaOrbSCCIndex(d); o:=LambdaOrb(d); scc:=OrbSCC(o);
      l:=Position(o, LambdaFunc(s)(g));

      if l = fail or OrbSCCLookup(o)[l]<>m then
        return fail;
      fi;
     
      if l<>scc[m][1] then
        g:=g*LambdaOrbMults(o, m)[l];
      fi;

      m:=RhoOrbSCCIndex(d); o:=RhoOrb(d); scc:=OrbSCC(o);
      l:=Position(o, RhoFunc(s)(g));

      if l = fail or OrbSCCLookup(o)[l]<>m then
        return fail;
      fi;
      
      if l<>scc[m][1] then
        g:=RhoOrbMults(o, m)[l][2]*g;
      fi;

      schutz:=LambdaOrbStabChain(o, m);
      cosets:=RhoCosets(d);
      g:=LambdaPerm(s)(rep, g);
#JDM HERE
      if schutz=true then 
      
      elif schutz=false then 
        
      else
        for j in cosets do
        od;
      fi;

    end,
    #######################################################################
    
    Membership:=function(elm, enum)
      return elm in d;
    end,

    Length:=enum -> Size(d),

    PrintObj:=function(enum)
      Print( "<enumerator of D-class>");
    return;
  end));
end);

# mod for 1.0! - Enumerator - "for R-class of an acting semigroup"
##############################################################################

InstallMethod(Enumerator, "for R-class of an acting semigroup",
[IsGreensRClass and IsActingSemigroupGreensClass],
function(r)
  local o, m, mults, scc;

  o:=LambdaOrb(r); 
  m:=LambdaOrbSCCIndex(r);
  mults:=LambdaOrbMults(o, m);
  scc:=OrbSCC(o)[m];

  return EnumeratorByFunctions(r, rec(

    schutz:=Enumerator(SchutzenbergerGroup(r)),

    len:=Size(SchutzenbergerGroup(r)),

    #########################################################################

    ElementNumber:=function(enum, pos)
      local n, m, q;

      if pos>Length(enum) then 
        return fail;
      fi;

      if pos<=Length(enum!.schutz) then 
        return Representative(r)*enum!.schutz[pos];
      fi;

      n:=pos-1; m:=enum!.len;
      
      q:=QuoInt(n, m); 
      pos:=[ q, n - q * m]+1;
     
     return enum[pos[2]]/mults[scc[pos[1]]];
    end,

    #########################################################################
    
    NumberElement:=function(enum, f)
      local s, rep, o, m, l, g, j;

      s:=ParentSemigroup(r);
      rep:=Representative(r);
      
      if ElementsFamily(FamilyObj(s)) <> FamilyObj(f) or 
       #JDM degree causes problems for partial perms
       #Degree(f) <> Degree(rep) or 
       Rank(f) <> Rank(rep) or RhoFunc(s)(f) <> RhoFunc(s)(rep) then 
        return fail;
      fi;
      
      if f=rep then 
        return 1;
      fi;

      o:=LambdaOrb(r); m:=LambdaOrbSCCIndex(r);
      l:=Position(o, LambdaFunc(s)(f));

      if l = fail or OrbSCCLookup(o)[l]<>m then 
        return fail;
      fi;
     
      g:=f*mults[l];

      j:=Position(enum!.schutz, LambdaPerm(s)(rep, g));

      if j=fail then 
        return fail;
      fi;
      return enum!.len*(Position(scc, l)-1)+j;
    end,

    #########################################################################

    Membership:=function(elm, enum)
      return elm in r;
    end,

    Length:=enum-> Size(r),

    PrintObj:=function(enum)
      Print("<enumerator of R-class>");
      return;
    end));
end);

# mod for 1.0! - Enumerator - "for L-class of an acting semigroup"
##############################################################################

InstallMethod(Enumerator, "for L-class of an acting semigroup",
[IsGreensLClass and IsActingSemigroupGreensClass],
function(l)
  local o, m, mults, scc;

  o:=RhoOrb(l); 
  m:=RhoOrbSCCIndex(l);
  mults:=RhoOrbMults(o, m);
  scc:=OrbSCC(o)[m];

  return EnumeratorByFunctions(l, rec(

    schutz:=Enumerator(SchutzenbergerGroup(l)),

    len:=Size(SchutzenbergerGroup(l)),

    #########################################################################

    ElementNumber:=function(enum, pos)
      local n, m, q;

      if pos>Length(enum) then 
        return fail;
      fi;

      if pos<=Length(enum!.schutz) then 
        return Representative(l)*enum!.schutz[pos];
      fi;

      n:=pos-1; m:=enum!.len;
      
      q:=QuoInt(n, m); 
      pos:=[ q, n - q * m]+1;
     
     return mults[scc[pos[1]]][1]*enum[pos[2]];
    end,

    #########################################################################
    
    NumberElement:=function(enum, f)
      local s, rep, o, m, i, g, j;

      s:=ParentSemigroup(l);
      rep:=Representative(l);
      
      if ElementsFamily(FamilyObj(s)) <> FamilyObj(f) or 
       #JDM degree causes problems for partial perms
       #Degree(f) <> Degree(rep) or 
       Rank(f) <> Rank(rep) or LambdaFunc(s)(f) <> LambdaFunc(s)(rep) then 
        return fail;
      fi;
      
      if f=rep then 
        return 1;
      fi;

      o:=RhoOrb(l); m:=RhoOrbSCCIndex(l);
      i:=Position(o, RhoFunc(s)(f));

      if i = fail or OrbSCCLookup(o)[i]<>m then 
        return fail;
      fi;
     
      j:=Position(enum!.schutz, LambdaPerm(s)(rep, mults[i][2]*f));

      if j=fail then 
        return fail;
      fi;
      return enum!.len*(Position(scc, i)-1)+j;
    end,

    #########################################################################

    Membership:=function(elm, enum)
      return elm in l;
    end,

    Length:=enum-> Size(l),

    PrintObj:=function(enum)
      Print("<enumerator of L-class>");
      return;
    end));
end);

# mod for 1.0! - Enumerator - "for an acting semigroup"
#############################################################################
# Notes: this is not an enumerator as I could not get an enumerator to perform 
# well here. 

InstallMethod(Enumerator, "for an acting semigroup", 
[IsActingSemigroup and HasGeneratorsOfSemigroup], 
function(s)
  local out, iter, j, i;

  out:=EmptyPlist(Size(s)); 

  iter:=Iterator(s);
  j:=0;

  for i in iter do 
    j:=j+1;
    out[j]:=i;
  od;

  return Immutable(out);
end);

#GGG

# mod for 1.0! - GreensDClasses - "for an acting semigroup"
##############################################################################

InstallMethod(GreensDClasses, "for an acting semigroup",
[IsActingSemigroup], 
function(s)
  local data, r, scc, out, i;

  data:=Enumerate(SemigroupData(s), infinity, ReturnFalse);
  
  r:=data!.modifier;
  scc:=OrbSCC(data);
  out:=EmptyPlist(Length(scc));
  
  for i in [1+r..Length(scc)] do #JDM expand and remove CreateDClass
    out[i-r]:=CallFuncList(CreateDClass, data[scc[i][1]]);
  od;
  return out;
end);

# mod for 1.0! - GreensLClasses - "for an acting semigroup"
##############################################################################

InstallMethod(GreensLClasses, "for an acting semigroup",
[IsActingSemigroup], 
function(s)
  local D, out, d;

  D:=GreensDClasses(s);
  out:=EmptyPlist(NrLClasses(s));

  for d in D do 
    Append(out, GreensLClasses(d));
  od;
  return out;
end);

# mod for 1.0! - GreensLClasses - "for a D-class of an acting semigroup"
##############################################################################

InstallMethod(GreensLClasses, "for a D-class of an acting semigroup",
[IsActingSemigroupGreensClass and IsGreensDClass], 
function(d)
  local mults, scc, cosets, f, s, o, m, lrel, nc, out, k, g, l, j, i;
 
  mults:=LambdaOrbMults(LambdaOrb(d), LambdaOrbSCCIndex(d));
  scc:=LambdaOrbSCC(d);
  cosets:=LambdaCosets(d);
  f:=Representative(d);
 
  s:=ParentSemigroup(d);
  o:=RhoOrb(d);
  m:=RhoOrbSCCIndex(d);
  lrel:=GreensLClasses(s); 
  nc:=IsGreensClassNC(d);

  out:=EmptyPlist(Length(scc)*Length(cosets));

  k:=0;
  for j in cosets do
    g:=f*j;
    for i in scc do
      k:=k+1;
      l:=Objectify(LClassType(arg[1]), rec());

      SetParentSemigroup(l, s);
      SetRhoOrbSCCIndex(l, m);
      SetRhoOrb(l, o);
      SetRepresentative(l, g/mults[i]);
      SetEquivalenceClassRelation(l, lrel);
      SetIsGreensClassNC(l, nc); 
      out[k]:=l;
    od;
  od;

  return out;
end);

# new for 1.0! - GreensRClasses - "for a D-class of an acting semigroup"
##############################################################################

InstallMethod(GreensRClasses, "for a D-class of an acting semigroup",
[IsActingSemigroupGreensClass and IsGreensDClass], 
function(d)
  local mults, scc, cosets, f, s, o, m, rrel, nc, out, k, g, r, i, j;
 
  mults:=RhoOrbMults(RhoOrb(d), RhoOrbSCCIndex(d));
  scc:=RhoOrbSCC(d);
  cosets:=RhoCosets(d);
  f:=Representative(d);
 
  s:=ParentSemigroup(d);
  o:=LambdaOrb(d);
  m:=LambdaOrbSCCIndex(d);
  rrel:=GreensRRelation(s);    
  nc:=IsGreensClassNC(d); 

  out:=EmptyPlist(Length(scc)*Length(cosets));

  k:=0;
  for i in scc do
    g:=mults[i][1]*f;
    for j in cosets do
      k:=k+1;
      r:=Objectify(RClassType(s), rec());

      SetParentSemigroup(r, s);
      SetLambdaOrbSCCIndex(r, m);
      SetLambdaOrb(r, o);
      SetRepresentative(r, g*j^-1);
      SetEquivalenceClassRelation(r, rrel);
      SetIsGreensClassNC(r, nc);
      out[k]:=r;
    od;
  od;

  return out;
end);

# mod for 1.0! - GreensRClasses - "for an acting semigroup"
##############################################################################

InstallMethod(GreensRClasses, "for an acting semigroup",
[IsActingSemigroup], 
function(s)
  local data, orbit, r, out, i;

  data:=Enumerate(SemigroupData(s), infinity, ReturnFalse);
  
  orbit:=data!.orbit;
  r:=data!.modifier;
  
  out:=EmptyPlist(Length(orbit));

  for i in [1+r..Length(orbit)] do 
    out[i-r]:=CallFuncList(CreateRClass, orbit[i]);
  od;
  return out;
end);

# mod for 1.0! - GreensDClassOfElement - "for an acting semigp and elt."
#############################################################################

InstallOtherMethod(GreensDClassOfElement, "for an acting semigp and elt",
[IsActingSemigroup, IsActingElt],
function(s, f)
  local d, o, l, m;

  if not f in s then
    Error("the element does not belong to the semigroup,");
    return;
  fi;

  d:=Objectify(DClassType(s), rec());
  SetParentSemigroup(d, s);

  o:=LambdaOrb(s);
  l:=Position(o, LambdaFunc(s)(f));
  m:=OrbSCCLookup(o)[l];
  
  if l<>OrbSCC(o)[m][1] then 
    f:=f*LambdaOrbMults(o, m)[l];
  fi;

  SetLambdaOrb(d, o);
  SetLambdaOrbSCCIndex(d, m); 
  
  o:=GradedRhoOrb(s, f, true);
  l:=o!.rho_l; #Position(o, RhoFunc(s)(f));
  m:=OrbSCCLookup(o)[l];

  if l<>OrbSCC(o)[m][1] then 
    f:=RhoOrbMults(o, m)[l][2]*f;
  fi;

  SetRhoOrb(d, o);
  SetRhoOrbSCCIndex(d, m);

  SetRepresentative(d, f);
  SetEquivalenceClassRelation(d, GreensDRelation(s));
  SetIsGreensClassNC(d, false);
  return d;
end);

# mod for 1.0! - GreensDClassOfElementNC - "for an acting semigp and elt."
#############################################################################

InstallOtherMethod(GreensDClassOfElementNC, "for an acting semigp and elt",
[IsActingSemigroup, IsActingElt],
function(s, f)
  local d;

  d:=Objectify(DClassType(s), rec());
  SetParentSemigroup(d, s);

  SetLambdaOrb(d, GradedLambdaOrb(s, f, false));
  SetLambdaOrbSCCIndex(d, 1);
 
  SetRhoOrb(d, GradedRhoOrb(s, f, false));
  SetRhoOrbSCCIndex(d, 1);

  SetRepresentative(d, f);
  SetEquivalenceClassRelation(d, GreensDRelation(s));
  SetIsGreensClassNC(d, true);
  return d;
end);

# mod for 1.0! - GreensLClassOfElement - "for an acting semigp and elt."
#############################################################################

InstallOtherMethod(GreensLClassOfElement, "for an acting semigp and elt",
[IsActingSemigroup, IsActingElt],
function(s, f)
  local l, o, i, m, scc;

  if not f in s then
    Error("the element does not belong to the semigroup,");
    return;
  fi;
  
  l:=Objectify(LClassType(s), rec());
  SetParentSemigroup(l, s);
  
  o:=GradedRhoOrb(s, f, true);
  SetRhoOrb(l, o);
  
  i:=Position(o, RhoFunc(s)(f));
  m:=OrbSCCLookup(o)[i];
  
  SetRhoOrbSCCIndex(l, m);
  
  if i<>OrbSCC(o)[m][1] then 
    f:=RhoOrbMults(o, m)[i][2]*f;
  fi;

  SetRepresentative(l, f);
  SetEquivalenceClassRelation(l, GreensLRelation(s));
  SetIsGreensClassNC(l, false);
  return l;
end);

# mod for 1.0! - GreensLClassOfElementNC - "for an acting semigp and elt."
#############################################################################

InstallOtherMethod(GreensLClassOfElementNC, "for an acting semigp and elt",
[IsActingSemigroup, IsActingElt],
function(s, f)
  local l;

  l:=Objectify(LClassType(s), rec());
  
  SetParentSemigroup(l, s);
  SetRhoOrbSCCIndex(l, 1);
  SetRhoOrb(l, GradedRhoOrb(s, f, false));
  SetRepresentative(l, f);
  SetEquivalenceClassRelation(l, GreensLRelation(s));
  SetIsGreensClassNC(l, true);
  return l;
end);

# mod for 1.0! - GreensLClassOfElement - "for D-class of acting semi and elt"
#############################################################################
# Notes: can't call GreensLClassOfElementNC since we don't have a way to pass
# IsGreensClassNC(d) to it.

InstallOtherMethod(GreensLClassOfElement, "for D-class of acting semi and elt",
[IsGreensDClass and IsActingSemigroupGreensClass, IsActingElt],
function(d, f)
  local s, l, o, i, m;
    
  if not f in d then
    Error("the element does not belong to the D-class,");
    return;
  fi;
  
  s:=ParentSemigroup(d);
  l:=Objectify(LClassType(s), rec());

  SetParentSemigroup(l, s);
  SetRhoOrbSCCIndex(l, RhoOrbSCCIndex(d));
  
  o:=RhoOrb(d); 
  SetRhoOrb(l, o);
  i:=Position(o, RhoFunc(s)(f));
  m:=OrbSCCLookup(o)[i];

  if i<>OrbSCC(o)[m][1] then 
    f:=RhoOrbMults(o, m)[i][2]*f;
  fi;
  
  SetRepresentative(l, f);
  SetEquivalenceClassRelation(l, GreensRRelation(s));
  SetIsGreensClassNC(l, IsGreensClassNC(d));
  SetDClassOfLClass(l, d);
  return l;
end);

# mod for 1.0! - GreensLClassOfElementNC - "for D-class and acting elt"
#############################################################################

InstallOtherMethod(GreensLClassOfElementNC, "for D-class and acting elt",
[IsGreensDClass and IsActingSemigroupGreensClass, IsActingElt],
function(d, f)
  local s, l, o, i, m;

  s:=ParentSemigroup(d);
  l:=Objectify(LClassType(s), rec());

  SetParentSemigroup(l, s);
  SetRhoOrbSCCIndex(l, LambdaOrbSCCIndex(d));
  
  o:=RhoOrb(d); 
  SetRhoOrb(l, o);
  i:=Position(o, RhoFunc(s)(f));
  m:=OrbSCCLookup(o)[i];

  if i<>OrbSCC(o)[m][1] then 
    f:=LambdaOrbMults(o, m)[i][2]*f;
  fi;
  
  SetRepresentative(l, f);
  SetEquivalenceClassRelation(l, GreensRRelation(s));
  SetIsGreensClassNC(l, true);
  SetDClassOfLClass(l, d);
  return l;
end);

# mod for 1.0! - GreensRClassOfElement - "for D-class and acting elt"
#############################################################################
# Notes: can't call GreensRClassOfElementNC since we don't have a way to pass
# IsGreensClassNC(d) to it.

InstallOtherMethod(GreensRClassOfElement, "for D-class and acting elt",
[IsGreensDClass and IsActingSemigroupGreensClass, IsActingElt],
function(d, f)
  local s, r, o, l, m;
    
  if not f in d then
    Error("the element does not belong to the D-class,");
    return;
  fi;
  
  s:=ParentSemigroup(d);
  r:=Objectify(RClassType(s), rec());

  SetParentSemigroup(r, s);
  SetLambdaOrbSCCIndex(r, LambdaOrbSCCIndex(d));
  
  o:=LambdaOrb(d); 
  SetLambdaOrb(r, o);
  l:=Position(o, LambdaFunc(s)(f));
  m:=OrbSCCLookup(o)[l];

  if l<>OrbSCC(o)[m][1] then 
    f:=f*LambdaOrbMults(o, m)[l];
  fi;
  
  SetRepresentative(r, f);
  SetEquivalenceClassRelation(r, GreensRRelation(s));
  SetIsGreensClassNC(r, IsGreensClassNC(d));
  SetDClassOfRClass(r, d);
  return r;
end);

# mod for 1.0! - GreensRClassOfElementNC - "for D-class and acting elt"
#############################################################################

InstallOtherMethod(GreensRClassOfElementNC, "for D-class and acting elt",
[IsGreensDClass and IsActingSemigroupGreensClass, IsActingElt],
function(d, f)
  local s, r, o, l, m;

  s:=ParentSemigroup(d);
  r:=Objectify(RClassType(s), rec());

  SetParentSemigroup(r, s);
  SetLambdaOrbSCCIndex(r, LambdaOrbSCCIndex(d));
  
  o:=LambdaOrb(d); 
  SetLambdaOrb(r, o);
  l:=Position(o, LambdaFunc(s)(f));
  m:=OrbSCCLookup(o)[l];

  if l<>OrbSCC(o)[m][1] then 
    f:=f*LambdaOrbMults(o, m)[l];
  fi;
  
  SetRepresentative(r, f);
  SetEquivalenceClassRelation(r, GreensRRelation(s));
  SetIsGreensClassNC(r, true);
  SetDClassOfRClass(r, d);
  return r;
end);

# mod for 1.0! - GreensRClassOfElement - "for an acting semigp and elt."
#############################################################################

InstallOtherMethod(GreensRClassOfElement, "for an acting semigp and elt",
[IsActingSemigroup, IsActingElt],
function(s, f)
  local pos;

  if not f in s then
    Error("the element does not belong to the semigroup,");
    return;
  fi;

  pos:=Position(SemigroupData(s), f);
  return CallFuncList(CreateRClass, SemigroupData(s)[pos]);
end);

# mod for 1.0! - GreensRClassOfElementNC - "for an acting semigp and elt."
#############################################################################

InstallOtherMethod(GreensRClassOfElementNC, "for an acting semigp and elt",
[IsActingSemigroup, IsActingElt],
function(s, f)
  local pos, r;
  
  pos:=Position(SemigroupData(s), f);
  
  if pos<>fail then 
    return CallFuncList(CreateRClass, SemigroupData(s)[pos]);
  fi;  

  r:=Objectify(RClassType(s), rec());

  SetParentSemigroup(r, s);
  SetLambdaOrbSCCIndex(r, 1);
  SetLambdaOrb(r, GradedLambdaOrb(s, f, false));
  SetRepresentative(r, f);
  SetEquivalenceClassRelation(r, GreensRRelation(s));
  SetIsGreensClassNC(r, true);
  return r;
end);

# mod for 1.0! - GreensJClassOfElement - for an acting semi and elt."
#############################################################################

InstallOtherMethod(GreensJClassOfElement, "for acting semigroup and elt.",
[IsActingSemigroup and HasGeneratorsOfSemigroup, IsActingElt], 
GreensDClassOfElement);

#III

# new for 1.0! - Idempotents - "for a D-class of an acting semigp."
#############################################################################

InstallOtherMethod(Idempotents, "for a D-class of an acting semigp.",
[IsGreensDClass and IsActingSemigroupGreensClass],
function(d)
  local R, out, x;
  R:=GreensRClasses(d);
  out:=[];
  for x in R do 
    Append(out, Idempotents(x));
  od;
  return out;
end);

# mod for 1.0! - Idempotents - "for an R-class of an acting semigp"
#############################################################################

InstallOtherMethod(Idempotents, "for an R-class of an acting semigp.",
[IsGreensRClass and IsActingSemigroupGreensClass],
function(r)
  local s, out, rho, o, m, scc, j, tester, creator, i;

  if not IsRegularRClass(r) then
    return [];
  fi;
  
  s:=ParentSemigroup(r);

  if Rank(Representative(r))=Degree(s) then
    return [One(s)];
  fi;

  out:=[]; 
  
  rho:=RhoFunc(s)(Representative(r));
  o:=LambdaOrb(r); 
  m:=LambdaOrbSCCIndex(r);
  scc:=OrbSCC(o)[m];
  j:=0;
  tester:=IdempotentLambdaRhoTester(s);
  creator:=IdempotentLambdaRhoCreator(s);

  for i in scc do
    if tester(o[i], rho) then
      j:=j+1;
      out[j]:=creator(o[i], rho);
    fi;
  od;

  if HasNrIdempotents(r) then 
    SetNrIdempotents(r, j);   
  fi;

  return out;
end);

# new for 0.1! - IsGreensClassOfTransSemigp - "for a Green's class"
#############################################################################

InstallMethod(IsGreensClassOfTransSemigp, "for a Green's class",
[IsGreensClass], x-> IsTransformationSemigroup(ParentSemigroup(x)));

# new for 0.1! - IsGreensClass - "for a Green's class"
#############################################################################
# JDM remove these?

InstallOtherMethod(IsGreensClass, "for an object", [IsObject], ReturnFalse);
InstallOtherMethod(IsGreensRClass, "for an object", [IsObject], ReturnFalse);
InstallOtherMethod(IsGreensLClass, "for an object", [IsObject], ReturnFalse);
InstallOtherMethod(IsGreensHClass, "for an object", [IsObject], ReturnFalse);
InstallOtherMethod(IsGreensDClass, "for an object", [IsObject], ReturnFalse);

# new for 1.0! - IsRegularDClass - "for an D-class of an acting semi"
#############################################################################

InstallMethod(IsRegularDClass, "for an D-class of an acting semigp",
[IsGreensDClass and IsActingSemigroupGreensClass],
function(d)
  local s, data, rho, scc, o, tester, i;

  if HasNrIdempotents(d) then 
    return NrIdempotents(d)<>0;
  fi;

  s:=ParentSemigroup(d);
  data:=SemigroupData(s);
  
  if not IsGreensClassNC(d) then
    if data!.repslens[data!.orblookup1[d!.orbit_pos]]>1 then
      return false;
    fi;
  fi; 
  
  # is r the group of units...
  if Rank(Representative(d))=Degree(s) then
    return true;
  fi;   
 
  rho:=RhoFunc(s)(Representative(d));
  scc:=LambdaOrbSCC(d);
  o:=LambdaOrb(d); 
  tester:=IdempotentLambdaRhoTester(s);

  for i in scc do
    if tester(o[i], rho) then
      return true; 
    fi;
  od;
  return false;
end);

# new for 1.0! - IsRegularRClass - "for an R-class of an acting semi"
#############################################################################

InstallMethod(IsRegularRClass, "for an R-class of an acting semigp",
[IsGreensRClass and IsActingSemigroupGreensClass],
function(r)
  local s, data, rho, o, scc, tester, i;

  if HasNrIdempotents(r) then 
    return NrIdempotents(r)<>0;
  fi;

  s:=ParentSemigroup(r);
  data:=SemigroupData(s);
  
  if not IsGreensClassNC(r) then
    if data!.repslens[data!.orblookup1[r!.orbit_pos]]>1 then
      return false;
    fi;
  fi; 
  
  # is r the group of units...
  if Rank(Representative(r))=Degree(s) then
    return true;
  fi;   
 
  rho:=RhoFunc(s)(Representative(r));
  o:=LambdaOrb(r);
  scc:=LambdaOrbSCC(r);
  tester:=IdempotentLambdaRhoTester(s);

  for i in scc do
    if tester(o[i], rho) then
      return true; 
    fi;
  od;
  return false;
end);

# new for 1.0! - Iterator - "for an R-class of an acting semi"
#############################################################################

InstallMethod(Iterator, "for an R-class of an acting semigp",
[IsGreensRClass and IsActingSemigroupGreensClass],
function(r)
  local o, m, mults, iter, scc;

  o:=LambdaOrb(r); m:=LambdaOrbSCCIndex(r);
  mults:=LambdaOrbMults(o, m);
  scc:=OrbSCC(o)[m];

  if HasAsSSortedList(r) then 
    iter:=IteratorList(AsSSortedList(r));
  else
    iter:=IteratorByFunctions(rec(

      schutz:=List(SchutzenbergerGroup(r), x-> Representative(r)*x), 
      at:=[0,1],
      m:=Length(scc),
      n:=Size(SchutzenbergerGroup(r)), 

      IsDoneIterator:=iter-> iter!.at[1]=iter!.m and iter!.at[2]=iter!.n,

      NextIterator:=function(iter)
        local at;

        at:=iter!.at;
        
        if at[1]=iter!.m and at[2]=iter!.n then 
          return fail;
        fi;


        if at[1]<iter!.m then
          at[1]:=at[1]+1;
        else
          at[1]:=1; at[2]:=at[2]+1;
        fi;
       
        return iter!.schutz[at[2]]/mults[scc[at[1]]];
      end,
      
      ShallowCopy:=iter -> rec(schutz:=iter!.schutz, at:=[0,1], 
       m:=iter!.m, n:=iter!.n)));
    fi;
    
    SetIsIteratorOfRClassElements(iter, true);
    return iter;
end);

# mod for 1.0! - Iterator - "for a trivial acting semigroup"
#############################################################################
# Notes: required until Enumerator for a trans. semigp does not call iterator. 
# This works but is maybe not the best!

InstallOtherMethod(Iterator, "for a trivial acting semigp", 
[IsActingSemigroup and HasGeneratorsOfSemigroup and IsTrivial], 9999,
function(s)
  return TrivialIterator(Generators(s)[1]);
end);

# mod for 1.0! - Iterator - "for an acting semigroup"
#############################################################################

InstallMethod(Iterator, "for an acting semigroup",
[IsActingSemigroup and HasGeneratorsOfSemigroup],
function(s)
  local iter;

  Info(InfoCitrus, 4, "Iterator: for a trans. semigroup");

  iter:= IteratorByFunctions( rec(

    R:=IteratorOfRClasses(s),

    r:=fail, s:=s,

    NextIterator:=function(iter)

      if IsDoneIterator(iter) then
        return fail;
      fi;

      if iter!.r=fail or IsDoneIterator(iter!.r) then
        iter!.r:=Iterator(NextIterator(iter!.R));
      fi;

      return NextIterator(iter!.r);
    end,

    IsDoneIterator:= iter -> IsDoneIterator(iter!.R) and
     IsDoneIterator(iter!.r),

    ShallowCopy:= iter -> rec(R:=IteratorOfRClasses(s), r:=fail)));

  SetIsIteratorOfSemigroup(iter, true);

  return iter;
end);

# new for 0.5! - Iterator - "for a full transformation semigroup"
#############################################################################

InstallMethod(Iterator, "for a full transformation semigroup",
[IsTransformationSemigroup and IsFullTransformationSemigroup and HasGeneratorsOfSemigroup], 
function(s)
  local iter;
  
  Info(InfoCitrus, 4, "Iterator: for a full trans. semigroup");

  iter:= IteratorByFunctions( rec(

    s:=s,

    tups:=IteratorOfTuples([1..Degree(s)], Degree(s)),

    NextIterator:=iter-> TransformationNC(NextIterator(iter!.tups)),
  
    IsDoneIterator:=iter -> IsDoneIterator(iter!.tups),
    
    ShallowCopy:= iter -> rec(tups:=IteratorOfTuples([1..Degree(s)],
    Degree(s)))));

  SetIsIteratorOfSemigroup(iter, true);

  return iter;
end);

# new for 1.0! - IteratorOfDClasses - "for an acting semigroup"
#############################################################################

InstallMethod(IteratorOfDClasses, "for an acting semigroup",
[IsActingSemigroup],
function(s)
  local iter;
  
  if IsClosed(SemigroupData(s)) then 
    return IteratorList(GreensDClasses(s));
  fi;

  iter:=IteratorByFunctions( rec( 

    classes:=[],

    R:=IteratorOfRClassData(s),

    last_called_by_is_done:=false,

    next_value:=fail,

    IsDoneIterator:=function(iter)
      local R, X, x, d; 
      if iter!.last_called_by_is_done then 
        return iter!.next_value=fail;
      fi;
      
      iter!.last_called_by_is_done:=true;
      
      iter!.next_value:=fail;
       
      R:=iter!.R; X:=iter!.classes;
      
      repeat 
        x:=NextIterator(R);
      #JDM is there a better method?
      until x=fail or ForAll(X, d-> not x[4] in d);
      
      if x<>fail then 
        d:=DClassOfRClass(CallFuncList(CreateRClass, x));
        Add(X, d);
        iter!.next_value:=d;
        return false;
      fi;
      return true;
    end,

    NextIterator:=function(iter)
      if not iter!.last_called_by_is_done then 
        IsDoneIterator(iter);
      fi;
      iter!.last_called_by_is_done:=false;
      return iter!.next_value;
    end,
    
    ShallowCopy:=iter-> rec(classes:=[], R:=IteratorOfRClassData(s),
     last_called_by_is_done:=false, next_value:=fail)));
  SetIsIteratorOfDClasses(iter, true);
  return iter;
end);

# new for 1.0! - IteratorOfDClassReps - "for an acting semigroup"
#############################################################################

InstallMethod(IteratorOfDClassReps, "for an acting semigroup",
[IsActingSemigroup],
s-> IteratorByIterator(IteratorOfDClasses(s), Representative,
[IsIteratorOfDClassReps]));

# new for 1.0! - IteratorOfRClassData - "for an acting semigroup"
#############################################################################

InstallMethod(IteratorOfRClassData, "for an acting semigroup",
[IsActingSemigroup],
function(s)

  return IteratorByFunctions( rec( 
    
    i:=SemigroupData(s)!.modifier,

    IsDoneIterator:=iter-> IsClosed(SemigroupData(s)) and 
     iter!.i>=Length(SemigroupData(s)),

    NextIterator:=function(iter)
      local data;

      iter!.i:=iter!.i+1;
      
      data:=Enumerate(SemigroupData(s), iter!.i, ReturnFalse);

      if iter!.i>Length(data!.orbit) then 
        return fail;
      fi;
      return data!.orbit[iter!.i];
    end,
    
    ShallowCopy:=iter-> rec(i:=0)));
end);

# new for 1.0! - IteratorOfRClassReps - "for an acting semigroup"
#############################################################################

InstallMethod(IteratorOfRClassReps, "for an acting semigroup",
[IsActingSemigroup],
s-> IteratorByIterator(IteratorOfRClassData(s), x-> x[4],
[IsIteratorOfRClassReps]));

# new for 1.0! - IteratorOfRClasses - "for an acting semigroup"
#############################################################################

InstallMethod(IteratorOfRClasses, "for an acting semigroup",
[IsActingSemigroup],
s-> IteratorByIterator(IteratorOfRClassData(s), x->
CallFuncList(CreateRClass, x), [IsIteratorOfRClasses]));

#LLL

# new for 1.0! - LClassReps - "for an acting semigroup D-class"
#############################################################################

InstallOtherMethod(LClassReps, "for a D-class of an acting semigroup",
[IsGreensDClass and IsActingSemigroupGreensClass],
function(d)
  local o, m, mults, scc, cosets, f, out, k, i, j;
  
  o:=LambdaOrb(d); 
  m:=LambdaOrbSCCIndex(d);
  mults:=LambdaOrbMults(o, m);
  scc:=LambdaOrbSCC(d);
  cosets:=LambdaCosets(d);
  f:=Representative(d);
  
  out:=EmptyPlist(Length(scc)*Length(cosets));

  k:=0;
  for i in scc do
    for j in cosets do
      k:=k+1;
     out[k]:=f*(j/mults[i]);
    od;
  od;

  return out;
end);

#NNN

# new for 1.0! - NrIdempotents - "for a D-class of an acting semigp"
#############################################################################

InstallOtherMethod(NrIdempotents, "for a D-class of an acting semigroup",
[IsGreensDClass and IsActingSemigroupGreensClass],
d-> Sum(List(GreensRClasses(d), NrIdempotents)));

# new for 1.0! - NrIdempotents - "for an R-class of an acting semigp."
#############################################################################

InstallOtherMethod(NrIdempotents, "for an R-class of an acting semigp.",
[IsGreensRClass and IsActingSemigroupGreensClass],
function(r)
  local s, data, rho, o, m, scc, nr, tester, i;

  if HasIsRegularRClass(r) and not IsRegularRClass(r) then 
    return 0;
  fi;

  s:=ParentSemigroup(r);     

  # check if we already know this...
  if not IsGreensClassNC(r) and not (HasIsRegularRClass(r) and
   IsRegularRClass(r)) then
    data:=SemigroupData(s);
    if data!.repslens[data!.orblookup1[r!.orbit_pos]]>1 then
      return 0;
    fi;
  fi;

  # is r the group of units...
  if Rank(Representative(r))=Degree(s) then
    return 1;
  fi;

  rho:=RhoFunc(s)(Representative(r));
  o:=LambdaOrb(r); 
  m:=LambdaOrbSCCIndex(r);
  scc:=OrbSCC(o)[m];
  nr:=0;
  tester:=IdempotentLambdaRhoTester(s);

  for i in scc do
    if tester(o[i], rho) then
      nr:=nr+1;
    fi;
  od;

  return nr;
end);

# new for 0.1! - NrIdempotents - "for an acting semigroup"
#############################################################################

InstallMethod(NrIdempotents, "for an acting semigroup", 
[IsActingSemigroup and HasGeneratorsOfSemigroup],
function(s)
  local data, reps, repslookup, lenreps, repslens, rhofunc, tester, f, m, o,
  rho, nr, i, k;

  if HasIdempotents(s) then 
    return Length(Idempotents(s));
  fi;

  data:=Enumerate(SemigroupData(s), infinity, ReturnFalse);
  
  reps:=data!.reps; 
  repslookup:=data!.repslookup;
  lenreps:=data!.lenreps;
  repslens:=data!.repslens;

  rhofunc:=RhoFunc(s);
  tester:=IdempotentLambdaRhoTester(s);

  for i in [1..lenreps] do 
    f:=reps[i][1]; 
    m:=data[repslookup[i][1]][2];
    o:=data[repslookup[i][1]][3];
    rho:=rhofunc(f);
    for k in OrbSCC(o)[m] do 
      if tester(o[k], rho) then 
        nr:=nr+repslens[i];
      fi;
    od;
  od;

  return nr;
end);

# mod for 1.0! - NrDClasses - "for an acting semigroup"
#############################################################################

InstallMethod(NrDClasses, "for an acting semigroup",
[IsActingSemigroup and HasGeneratorsOfSemigroup],
s-> Length(OrbSCC(SemigroupData(s)))-SemigroupData(s)!.modifier);

# mod for 1.0! - NrRegularDClasses - "for an acting semigroup"
#############################################################################

InstallMethod(NrRegularDClasses, "for an acting semigroup",
[IsActingSemigroup and HasGeneratorsOfSemigroup],
function(s)
  local data, datascc, rhofunc, tester, nr, r, x, o, scc, rho, i, j;
  
  data:=Enumerate(SemigroupData(s), infinity, ReturnFalse);
  datascc:=OrbSCC(data);
  
  rhofunc:=RhoFunc(s);
  tester:=IdempotentLambdaRhoTester(s);
  nr:=0;
  r:=data!.modifier;

  for i in [1+r..Length(datascc)] do
    # data of the first R-class in the D-class corresponding to x
    x:=data[datascc[i][1]];
    o:=x[3]; scc:=OrbSCC(o)[x[2]]; 
    rho:=rhofunc(x[4]);

    for j in scc do  
      if tester(o[j], rho) then
        nr:=nr+1;
        break;
      fi;
    od;
  od;
  return nr;
end);

# mod for 1.0! - NrHClasses - "for a D-class of an acting semigroup"
#############################################################################

InstallOtherMethod(NrHClasses, "for a D-class of an acting semigroup",
[IsGreensDClass and IsActingSemigroupGreensClass],
function(d)
  return NrRClasses(d)*NrLClasses(d);
end);

# mod for 1.0! - NrLClasses - "for a D-class of an acting semigroup"
#############################################################################

InstallOtherMethod(NrLClasses, "for a D-class of an acting semigroup",       
[IsActingSemigroupGreensClass and IsGreensDClass],
d-> Length(LambdaCosets(d))*Length(LambdaOrbSCC(d)));

# mod for 1.0! - NrLClasses - "for an acting semigroup"
#############################################################################
#JDM could do better not to create the D-classes. Maybe not, we must store the
#schutz gp of the D-class somewhere and so it might as well be the D-class.

InstallMethod(NrLClasses, "for an acting semigroup",
[IsActingSemigroup], s-> Sum(List(GreensDClasses(s), NrLClasses)));

# mod for 1.0! - NrRClasses - "for a D-class of an acting semigroup"
#############################################################################

InstallOtherMethod(NrRClasses, "for a D-class of an acting semigroup",       
[IsActingSemigroupGreensClass and IsGreensDClass],
d-> Length(RhoCosets(d))*Length(RhoOrbSCC(d)));

# mod for 1.0! - NrRClasses - "for an acting semigroup"
#############################################################################

InstallMethod(NrRClasses, "for an acting semigroup",       
[IsActingSemigroup and HasGeneratorsOfSemigroup],        
function(s)
  local data;
  
  data:=Enumerate(SemigroupData(s), infinity, ReturnFalse);
  return Length(data!.orbit)-data!.modifier;
end);

#PPP

# new for 1.0! - ParentSemigroup - "for a Green's class of an acting semi"
#############################################################################

InstallMethod(ParentSemigroup, "for a Green's class of an acting semi",
[IsActingSemigroupGreensClass and IsGreensClass], x-> x!.s);

# mod for 1.0! - PartialOrderOfDClasses - "for an acting semigroup"
#############################################################################

InstallMethod(PartialOrderOfDClasses, "for an acting semigroup",
[IsActingSemigroup and HasGeneratorsOfSemigroup],
function(s)
  local d, n, out, gens, data, graph, datalookup, o, lambdafunc, rhofunc, scc, lookup, lambdarhoht, lambdaperm, repslookup, schutz, mults, reps, repslens, ht, l, m, val, j, f, i, x, k;

  d:=GreensDClasses(s); 
  n:=Length(d);
  out:=List([1..n], x-> EmptyPlist(n));
  gens:=Generators(s);  
  
  data:=SemigroupData(s);
  graph:=SemigroupData(s)!.graph;
  datalookup:=OrbSCCLookup(data)-SemigroupData(s)!.modifier;  
  reps:=data!.reps;
  repslens:=data!.repslens;
  ht:=data!.ht;
  repslookup:=data!.repslookup;
  
  lambdafunc:=LambdaFunc(s);
  rhofunc:=RhoFunc(s);
  lambdarhoht:=LambdaRhoHT(s);
  lambdaperm:=LambdaPerm(s);
  
  o:=LambdaOrb(s);
  scc:=OrbSCC(o); 
  lookup:=OrbSCCLookup(o);
  schutz:=o!.schutzstab;
  mults:=o!.mults;

  for i in [1..n] do
    for x in gens do
      # collect info about left multiplying R-class reps of d[i] by gens
      for j in SemigroupDataSCC(d[i]) do 
        for k in graph[j] do  
          AddSet(out[i], datalookup[k]);
        od;
      od;

      for f in LClassReps(d[i]) do
        # the below is an expanded version of Position(data, f * x)
        f:=f*x;
        l:=Position(o, lambdafunc(f));
        m:=lookup[l];
        val:=HTValue(lambdarhoht, Concatenation([m], rhofunc(f)));
        if not IsBound(schutz[m]) then 
          LambdaOrbSchutzGp(o, m);
        fi;
        if schutz[m]=true then 
          j:=repslookup[val][1];
        else
          if l<>scc[m][1] then 
            f:=f*mults[l];
          fi;
          if schutz[m]=false then 
            j:=HTValue(ht, f);
          else
            n:=0; j:=0;
            repeat 
              n:=n+1;
              if SiftedPermutation(schutz[m], lambdaperm(reps[val][n], f))=()
               then  
                j:=repslookup[val][n];
              fi;
            until j<>0;
          fi;
        fi;
        AddSet(out[i], datalookup[j]);
      od;
    od;
  od;
  Perform(out, ShrinkAllocationPlist);
  return out;
end);
 
# new for 0.7! - PrintObj - for IsIteratorOfDClassElements
############################################################################
   
InstallMethod(PrintObj, [IsIteratorOfDClassElements],
function(iter)
  Print( "<iterator of D-class>");
  return;
end);

# new for 0.1! - PrintObj - for IsIteratorOfRClassElements
############################################################################

InstallMethod(PrintObj, [IsIteratorOfRClassElements],
function(iter)
  Print("<iterator of R-class>");
  return;
end);

# new for 0.7! - PrintObj - IsIteratorOfLClassElements
############################################################################

InstallMethod(PrintObj, [IsIteratorOfLClassElements],
function(iter)
  Print( "<iterator of L-class>");
  return;
end);

# mod for 1.0! - PrintObj - for IsIteratorOfDClassReps
############################################################################

InstallMethod(PrintObj, [IsIteratorOfDClassReps],
function(iter)
  Print("<iterator of D-class reps>");
  return;
end);

# new for 0.1! - PrintObj - for IsIteratorOfLClassReps
############################################################################

InstallMethod(PrintObj, [IsIteratorOfLClassReps], 
function(iter)
  Print( "<iterator of L-class reps>");
  return;
end);

# mod for 1.0! - PrintObj - IsIteratorOfRClassReps
############################################################################

InstallMethod(PrintObj, [IsIteratorOfRClassReps],
function(iter)
  Print("<iterator of R-class reps>");
  return;
end);

# new for 0.1! - PrintObj - "for iterator of D-classes"
############################################################################

InstallMethod(PrintObj, [IsIteratorOfDClasses], 
function(iter)
  Print( "<iterator of D-classes>");
  return;
end);
 
# new for 0.1! - PrintObj - for IsIteratorOfLClasses
############################################################################

InstallMethod(PrintObj, [IsIteratorOfLClasses],
function(iter)
  Print( "<iterator of L-classes>");
  return;
end);

# new for 0.1! - PrintObj - for IsIteratorOfRClasses
############################################################################

InstallMethod(PrintObj, [IsIteratorOfRClasses],
function(iter)
  Print( "<iterator of R-classes>");
  return;
end); 

# mod for 0.8! - PrintObj - for IsIteratorOfSemigroup
############################################################################

InstallMethod(PrintObj, [IsIteratorOfSemigroup],
function(iter)
  if IsFullTransformationSemigroup(iter!.s) then
    Print("<iterator of full trans. semigroup>");
  elif IsTransformationSemigroup(iter!.s) then
    Print("<iterator of transformation semigroup>");
  elif IsPartialPermSemigroup(iter!.s) and IsInverseSemigroup(iter!.s) then
    Print("<iterator of inverse semigroup>");
  elif IsPartialPermSemigroup(iter!.s) then 
    Print("<iterator of semigroup of partial perms>");
  fi;
  return;
end);

#RRR

# mod for 1.0! - RClassReps - "for a D-class of an acting semigroup"
############################################################################

InstallOtherMethod(RClassReps, "for a D-class of an acting semigroup",
[IsActingSemigroupGreensClass and IsGreensDClass],
function(d)
  local o, m, f, mults, scc, cosets, out, k, g, i, j;

  o:=RhoOrb(d); 
  m:=RhoOrbSCCIndex(d);
  f:=Representative(d);
  mults:=RhoOrbMults(o, m);
  scc:=RhoOrbSCC(d);
  cosets:=RhoCosets(d);

  out:=EmptyPlist(Length(scc)*Length(cosets));
  SetNrRClasses(d, Length(scc)*Length(cosets));
  k:=0;

  for i in scc do
    g:=mults[i][1]*f;
    for j in cosets do
      k:=k+1;
      out[k]:=g*j^-1;
    od;
  od;

  return out;
end);

# mod for 1.0! - RClassReps - "for an acting semigroup"
############################################################################

InstallMethod(RClassReps, "for an acting semigroup",
[IsActingSemigroup and HasGeneratorsOfSemigroup],
function(s)
  local data, orbit, nr, r, out, i;

  data:=Enumerate(SemigroupData(s)); 
  orbit:=data!.orbit;
  nr:=Length(orbit);
  r:=data!.modifier;
  out:=EmptyPlist(nr-r);

  for i in [1+r..nr] do 
    out[i-r]:=orbit[i][4];
  od;
  return out;
end);

# new for 1.0! - DClassType - "for an acting semigroup"
############################################################################# 

InstallMethod(DClassType, "for an acting semigroups",
[IsActingSemigroup and HasGeneratorsOfSemigroup],
function(s);
  return NewType( FamilyObj( s ), IsEquivalenceClass and
          IsEquivalenceClassDefaultRep and IsGreensDClass and
          IsActingSemigroupGreensClass);
end);

# mod for 1.0! - LClassType - "for an acting semigroup"
############################################################################

InstallMethod(LClassType, "for an acting semigroup",
[IsActingSemigroup],
function(s);
  return NewType( FamilyObj( s ), IsEquivalenceClass and
         IsEquivalenceClassDefaultRep and IsGreensLClass and
         IsActingSemigroupGreensClass);
end);

# new for 1.0! - RClassType - "for an acting semigroup"
############################################################################

InstallMethod(RClassType, "for an acting semigroup",
[IsActingSemigroup and HasGeneratorsOfSemigroup],
function(s);
  return NewType( FamilyObj( s ), IsEquivalenceClass and
         IsEquivalenceClassDefaultRep and IsGreensRClass and
         IsActingSemigroupGreensClass);
end);

#SSS

# new for 1.0! - SchutzenbergerGroup - "for a D-class of an acting semigroup"
#############################################################################

InstallMethod(SchutzenbergerGroup, "for a D-class of an acting semigroup",
[IsGreensDClass and IsActingSemigroupGreensClass],
function(d)
  local o, m, lambda_schutz, lambda_stab, rho_schutz, rho_stab, schutz, p;
  
  o:=LambdaOrb(d); m:=LambdaOrbSCCIndex(d);
  lambda_schutz:=LambdaOrbSchutzGp(o, m); 
  lambda_stab:=LambdaOrbStabChain(o, m);
  
  o:=RhoOrb(d); m:=RhoOrbSCCIndex(d);
  rho_schutz:=RhoOrbSchutzGp(o, m, infinity);
  rho_stab:=RhoOrbStabChain(o, m);

  if rho_stab=true then
    schutz:=lambda_schutz;
    if lambda_stab=true then 
      SetRhoCosets(d, [()]);
      return lambda_schutz;
    fi;
  elif rho_stab=false then 
    SetRhoCosets(d, [()]);
    return rho_schutz;
  fi;

  p:=RhoPerm(ParentSemigroup(d))(RhoOrbRep(o, m), Representative(d));
  rho_schutz:=rho_schutz^p;

  if lambda_stab=false then 
    SetRhoCosets(d, Enumerator(rho_schutz));
    return lambda_schutz;
  elif lambda_stab=true then 
    schutz:=rho_schutz;
  else 
    schutz:=Intersection(lambda_schutz, rho_schutz);
  fi;

  SetRhoCosets(d, RightTransversal(rho_schutz, schutz));
  return schutz;
end);

# new for 1.0! - Size - "for a D-class of an acting semigp."
#############################################################################

InstallOtherMethod(Size, "for a D-class of an acting semigp.",
[IsGreensDClass and IsActingSemigroupGreensClass],
function(d)
  local l, r;
  
  l:=LambdaOrbSchutzGp(LambdaOrb(d), LambdaOrbSCCIndex(d));
  r:=RhoOrbSchutzGp(RhoOrb(d), RhoOrbSCCIndex(d), infinity);
  return Size(r)*Size(l)*Length(LambdaOrbSCC(d))*Length(RhoOrbSCC(d))/
   Size(SchutzenbergerGroup(d));
end);

# new for 1.0! - Size - "for an R-class of an acting semigp."
#############################################################################
# Algorithm C. 

InstallOtherMethod(Size, "for an R-class of an acting semigp.",
[IsGreensRClass and IsActingSemigroupGreensClass],
r-> Size(SchutzenbergerGroup(r))*Length(LambdaOrbSCC(r)));

# new for 1.0! - Size - "for an L-class of an acting semigp."
#############################################################################
# Algorithm C. 

InstallOtherMethod(Size, "for an L-class of an acting semigp.",
[IsGreensLClass and IsActingSemigroupGreensClass],
l-> Size(SchutzenbergerGroup(l))*Length(RhoOrbSCC(l)));

#UUU

# old 

# new for 0.1! - HClassReps - "for a transformation semigp."
############################################################################

InstallMethod(HClassReps, "for a transformation semigp.",
[IsTransformationSemigroup and HasGeneratorsOfSemigroup],
function(s)
  local out, iter, i, f;
  Info(InfoCitrus, 4, "HClassReps");

  out:=EmptyPlist(NrHClasses(s));
  iter:=IteratorOfHClassReps(s);
  i:=0;

  for f in iter do
    i:=i+1;
    out[i]:=f;
  od;

  return out;
end);

#DDD

# new for 1.0! - DClassOfLClass - "for a D-class of an acting semigroup"
#############################################################################

# only for L-classes not created during GreensLClasses! 

InstallMethod(DClassOfLClass, "for an L-class of an acting semigroup",
[IsGreensLClass and IsActingSemigroupGreensClass],
function(l)
  local s, f, d, o, lambda_l, m;

  s:=ParentSemigroup(l); 
  f:=Representative(l);
  d:=Objectify(DClassType(s), rec());

  SetParentSemigroup(d, s);
  SetRhoOrbSCCIndex(d, RhoOrbSCCIndex(l));
  SetRhoOrb(d, RhoOrb(l));
  
  o:=GradedLambdaOrb(s, f, IsGreensClassNC(l)<>true);
  SetLambdaOrb(d, o);

  if IsGreensClassNC(l) then 
    SetLambdaOrbSCCIndex(d, 1);
    SetRepresentative(d, f);
  else
    lambda_l:=o!.lambda_l; #position of LambdaFunc(s)(f) in o 
    m:=OrbSCCLookup(o)[lambda_l];
    SetLambdaOrbSCCIndex(d, m);
    if lambda_l<>OrbSCC(o)[m][1] then 
      SetRepresentative(d, f*LambdaOrbMults(o, m));
    else
      SetRepresentative(d, f);
    fi;
  fi;

  SetIsGreensClassNC(d, IsGreensClassNC(l)); 
  return d;
end);

# new for 1.0! - DClassOfRClass - "for a D-class of an acting semigroup"
#############################################################################

InstallMethod(DClassOfRClass, "for an R-class of an acting semigroup",
[IsGreensRClass and IsActingSemigroupGreensClass],
function(r)
  local s, f, d, o, rho_l, m;

  s:=ParentSemigroup(r); 
  f:=Representative(r);
  d:=Objectify(DClassType(s), rec());

  SetParentSemigroup(d, s);
  SetLambdaOrbSCCIndex(d, LambdaOrbSCCIndex(r));
  SetLambdaOrb(d, LambdaOrb(r));
  
  o:=GradedRhoOrb(s, f, IsGreensClassNC(r)<>true);
  SetRhoOrb(d, o);

  if IsGreensClassNC(r) then 
    SetLambdaOrbSCCIndex(d, 1);
    SetRepresentative(d, f);
  else
    rho_l:=o!.rho_l; #position of RhoFunc(s)(f) in o 
    m:=OrbSCCLookup(o)[rho_l];
    SetRhoOrbSCCIndex(d, m);
    if rho_l<>OrbSCC(o)[m][1] then 
      SetRepresentative(d, RhoOrbMults(o, m)*f);
    else
      SetRepresentative(d, f);
    fi;
  fi;

  SetIsGreensClassNC(d, IsGreensClassNC(r)); 
  return d;
end);

# mod for 1.0! - DClassReps - "for an acting semigroup"
#############################################################################

InstallMethod(DClassReps, "for an acting semigroup",
[IsActingSemigroup and HasGeneratorsOfSemigroup],
function(s)
  local data, scc, r, i, out, j;

  data:=Enumerate(SemigroupData(s), infinity, ReturnFalse);
  scc:=OrbSCC(data); 
  r:=Length(scc);
  i:=SemigroupData(s)!.modifier;
  
  out:=EmptyPlist(r-i);

  for j in [1+i..r] do 
    out[j-i]:=data[scc[j][1]][4];
  od;
  return out;
end);

# mod for 1.0! - EnumeratorOfRClasses - "for an acting semigroup"
#############################################################################
# Notes: the only purpose for this is the method for NumberElement.  Otherwise
# use (if nothing much is known) IteratorOfRClasses or if everything is know
# just use RClasses.

InstallMethod(EnumeratorOfRClasses, "for an acting semigroup",
[IsActingSemigroup and HasGeneratorsOfSemigroup], 
function(s)
  local enum;

  return EnumeratorByFunctions(s, rec(
    
    ElementNumber:=function(enum, pos)
      return GreensRClasses(s)[pos];
    end,

    NumberElement:=function(enum, r)
      return Position(SemigroupData(s), Representative(r))-
       SemigroupData(s)!.modifier;
    end,

    Membership:=function(r, enum)
      return Position(enum, r)<>fail;
    end,
    
    Length:=enum -> NrRClasses(s),

    PrintObj:=function(enum)
      Print( "<enumerator of R-classes>");
      return;
    end));

  return enum;
end);

# new for 0.1! - GreensHClasses - "for a transformation semigroup"
##############################################################################

InstallMethod(GreensHClasses, "for a transformation semigroup",
[IsTransformationSemigroup and HasGeneratorsOfSemigroup], 
function(s)
  local iter, out, i, h;

  Info(InfoCitrus, 4, "GreensHClasses");

  iter:=IteratorOfHClasses(s);
  out:=EmptyPlist(NrHClasses(s));
  i:=0;

  for h in iter do 
    i:=i+1;
    out[i]:=h;
  od;

  return out;
end);

# mod for 0.4! - Idempotents - "for a transformation semigroup"
#############################################################################

InstallOtherMethod(Idempotents, "for a transformation semigroup", 
[IsTransformationSemigroup and HasGeneratorsOfSemigroup],
function(s)
  local n, out, kers, imgs, j, i, ker, img;

  if IsRegularSemigroup(s) then 
    n:=DegreeOfTransformationSemigroup(s);

    if HasNrIdempotents(s) then 
      out:=EmptyPlist(NrIdempotents(s));
    else
      out:=[];
    fi;

    kers:=GradedKernelsOfTransSemigroup(s); 
    imgs:=GradedImagesOfTransSemigroup(s);

    j:=0;
    
    for i in [1..n] do
      for ker in kers[i] do
        for img in imgs[i] do 
          if IsInjectiveTransOnList(ker, img) then 
            j:=j+1;
            out[j]:=IdempotentNC(ker, img);
          fi;
        od;
      od;
    od;

    if not HasNrIdempotents(s) then 
      SetNrIdempotents(s, j);
    fi;
    return out;
  fi;

  return Concatenation(List(GreensRClasses(s), Idempotents));
end);

# new for 0.1! - Idempotents - "for a trans. semigroup and pos. int."
#############################################################################

InstallOtherMethod(Idempotents, "for a trans. semigroup and pos. int.", 
[IsTransformationSemigroup and HasGeneratorsOfSemigroup, IsPosInt],
function(s, i)
  local out, n, kers, imgs, j, ker, img, r;
  
  n:=DegreeOfTransformationSemigroup(s);
  
  if i>n then 
    return [];
  fi;

  if HasIdempotents(s) then 
    return Filtered(Idempotents(s), x-> RankOfTransformation(x)=i);
  fi; 

  if HasNrIdempotents(s) then
    out:=EmptyPlist(NrIdempotents(s));
  else
    out:=[];
  fi;

  if IsRegularSemigroup(s) then 

    kers:=GradedKernelsOfTransSemigroup(s)[i]; 
    imgs:=GradedImagesOfTransSemigroup(s)[i];
    j:=0;

    for ker in kers do
      for img in imgs do 
        if IsInjectiveTransOnList(ker, img) then 
          j:=j+1;
          out[j]:=IdempotentNC(ker, img);
        fi;
      od;
    od;

    return out;
  fi;

  for r in GreensRClasses(s) do 
    if RankOfTransformation(r!.rep)=i then 
      out:=Concatenation(out, Idempotents(r));
    fi;
  od;
  return out;
end);

# new for 0.1! - NrHClasses - "for a transformation semigroup"
#############################################################################
 
InstallMethod(NrHClasses, "for a transformation semigroup", 
[IsTransformationSemigroup and HasGeneratorsOfSemigroup],
function(s)
  Error("not yet implemented");
end);

# new for 0.1! - Size - "for a simple transformation semigroup"
#############################################################################
# JDM check this is actually superior to the above method for Size

InstallOtherMethod(Size, "for a simple transformation semigroup",
[IsSimpleSemigroup and IsTransformationSemigroup],
function(s)
  local gens, ims, kers, H;

  gens:=Generators(s);

  ims:=Size(Set(List(gens, ImageSetOfTransformation)));
  kers:=Size(Set(List(gens, CanonicalTransSameKernel)));
  H:=GreensHClassOfElement(s, gens[1]);

  return Size(H)*ims*kers;
end);

#EOF
