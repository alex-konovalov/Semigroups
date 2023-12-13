#############################################################################
##
#W  standard/libsemigroups/words.tst
#Y  Copyright (C) 2023                                     James Mitchell
##
##  Licensing information can be found in the README file of this package.
##
#############################################################################
##

#@local i, w
gap> START_TEST("Semigroups package: standard/libsemigroups/words.tst");
gap> LoadPackage("semigroups", false);;

# Set info levels and user preferences
gap> SEMIGROUPS.StartTest();

# Test words
gap> w := Words();;
gap> IsWords(w);
true
gap> TypeObj(w);
<Type: (WordsFamily, [ IsInternalRep, IsRangeObj, IsWords ]), data: fail>
gap> NumberOfLetters(w, 2);
gap> Count(w);
0
gap> FirstWord(w, []);
gap> LastWord(w, [1,1,1,1,1,1,1,1,1,1,1,1,1]);
gap> Count(w);
8191
gap> for i in [1 .. 1023] do Next(w); od;
gap> Get(w);
[ 0, 0, 0, 0, 0, 0, 0, 0, 0, 0 ]
gap> FirstWord(w, [0]);
gap> FirstWord(w);
[ 0 ]
gap> Get(w);
[ 0 ]
gap> LastWord(w, [0, 0, 0, 0, 0]);
gap> AsList(w);
[ [ 0 ], [ 1 ], [ 0, 0 ], [ 0, 1 ], [ 1, 0 ], [ 1, 1 ], [ 0, 0, 0 ], 
  [ 0, 0, 1 ], [ 0, 1, 0 ], [ 0, 1, 1 ], [ 1, 0, 0 ], [ 1, 0, 1 ], 
  [ 1, 1, 0 ], [ 1, 1, 1 ], [ 0, 0, 0, 0 ], [ 0, 0, 0, 1 ], [ 0, 0, 1, 0 ], 
  [ 0, 0, 1, 1 ], [ 0, 1, 0, 0 ], [ 0, 1, 0, 1 ], [ 0, 1, 1, 0 ], 
  [ 0, 1, 1, 1 ], [ 1, 0, 0, 0 ], [ 1, 0, 0, 1 ], [ 1, 0, 1, 0 ], 
  [ 1, 0, 1, 1 ], [ 1, 1, 0, 0 ], [ 1, 1, 0, 1 ], [ 1, 1, 1, 0 ], 
  [ 1, 1, 1, 1 ] ]
gap> ReductionOrdering(w, "lex");
gap> ReductionOrdering(w);
"lex"
gap> Count(w);
3
gap> AsList(w);
[ [ 0, 0 ], [ 0, 0, 0 ], [ 0, 0, 0, 0 ] ]
gap> UpperBound(w);
0
gap> MinimumWordLength(w, 2);
gap> FirstWord(w);
[ 0, 0 ]
gap> MaximumWordLength(w, 8);
gap> LastWord(w);
[ 0, 0, 0, 0, 0, 0, 0, 0 ]
gap> LastWord(w, [1, 1]);
gap> UpperBound(w, 5);
gap> Count(w);
22
gap> ww := Words(w);;
gap> IsIdenticalObj(w, ww);
false
gap> AsList(w);
[ [ 0, 0 ], [ 0, 0, 0 ], [ 0, 0, 0, 0 ], [ 0, 0, 0, 1 ], [ 0, 0, 1 ], 
  [ 0, 0, 1, 0 ], [ 0, 0, 1, 1 ], [ 0, 1 ], [ 0, 1, 0 ], [ 0, 1, 0, 0 ], 
  [ 0, 1, 0, 1 ], [ 0, 1, 1 ], [ 0, 1, 1, 0 ], [ 0, 1, 1, 1 ], [ 1 ], 
  [ 1, 0 ], [ 1, 0, 0 ], [ 1, 0, 0, 0 ], [ 1, 0, 0, 1 ], [ 1, 0, 1 ], 
  [ 1, 0, 1, 0 ], [ 1, 0, 1, 1 ] ]
gap> AtEnd(w);
true
gap> AtEnd(ww);
false
gap> AsList(ww);
[ [ 0, 0 ], [ 0, 0, 0 ], [ 0, 0, 0, 0 ], [ 0, 0, 0, 1 ], [ 0, 0, 1 ], 
  [ 0, 0, 1, 0 ], [ 0, 0, 1, 1 ], [ 0, 1 ], [ 0, 1, 0 ], [ 0, 1, 0, 0 ], 
  [ 0, 1, 0, 1 ], [ 0, 1, 1 ], [ 0, 1, 1, 0 ], [ 0, 1, 1, 1 ], [ 1 ], 
  [ 1, 0 ], [ 1, 0, 0 ], [ 1, 0, 0, 0 ], [ 1, 0, 0, 1 ], [ 1, 0, 1 ], 
  [ 1, 0, 1, 0 ], [ 1, 0, 1, 1 ] ]
gap> Init(ww);
gap> AsList(ww);
[  ]

# End 
gap> SEMIGROUPS.StopTest();
gap> STOP_TEST("Semigroups package: standard/libsemigroups/cong.tst");
