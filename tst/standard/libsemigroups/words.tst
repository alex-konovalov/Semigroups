#############################################################################
##
#W  standard/libsemigroups/words.tst
#Y  Copyright (C) 2023                                     James Mitchell
##
##  Licensing information can be found in the README file of this package.
##
#############################################################################
##

#@local i, w, ww
gap> START_TEST("Semigroups package: standard/libsemigroups/words.tst");
gap> LoadPackage("semigroups", false);;

# Set info levels and user preferences
gap> SEMIGROUPS.StartTest();

# Test Words
gap> w := Words();;
gap> IsWords(w);
true
gap> TypeObj(w);
<Type: (WordsFamily, [ IsInternalRep, IsRangeObj, IsWords ]), data: fail>
gap> NumberOfLetters(w, 2);
gap> Count(w);
0
gap> FirstWord(w, []);
gap> LastWord(w, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]);
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

# Test ToWord
gap> w := ToWord("abc");;
gap> IsToWord(w);
true
gap> w["ababcbabcbaabcba"];
[ 0, 1, 0, 1, 2, 1, 0, 1, 2, 1, 0, 0, 1, 2, 1, 0 ]
gap> ww := ToWord(w);;
gap> IsIdenticalObj(w, ww);
false
gap> Init(w);
gap> IsEmpty(w);
true
gap> w["ababcbabcbaabcba"];
Error, src/words.cpp:417:operator(): the 1st argument (input string) contains \
the letter 'a' that does not belong to the alphabet!
gap> ww["ababcbabcbaabcba"];
[ 0, 1, 0, 1, 2, 1, 0, 1, 2, 1, 0, 0, 1, 2, 1, 0 ]

# Test Strings
gap> w := Strings();;
gap> IsStrings(w);
true
gap> TypeObj(w);
<Type: (StringsFamily, [ IsInternalRep, IsRangeObj, IsStrings ]), data: fail>
gap> Alphabet(w, "ab");
gap> Count(w);
0
gap> FirstWord(w, "");
gap> LastWord(w, "bbbbbbbbbbbb");
gap> Count(w);
4095
gap> for i in [1 .. 1023] do Next(w); od;
gap> Get(w);
"aaaaaaaaaa"
gap> FirstWord(w, "a");
gap> FirstWord(w);
"a"
gap> Get(w);
"a"
gap> LastWord(w, "aaaaa");
gap> AsList(w);
[ "a", "b", "aa", "ab", "ba", "bb", "aaa", "aab", "aba", "abb", "baa", "bab",
  "bba", "bbb", "aaaa", "aaab", "aaba", "aabb", "abaa", "abab", "abba",
  "abbb", "baaa", "baab", "baba", "babb", "bbaa", "bbab", "bbba", "bbbb" ]
gap> ReductionOrdering(w, "lex");
gap> ReductionOrdering(w);
"lex"
gap> Count(w);
3
gap> AsList(w);
[ "aa", "aaa", "aaaa" ]
gap> UpperBound(w);
0
gap> MinimumWordLength(w, 2);
gap> FirstWord(w);
"aa"
gap> MaximumWordLength(w, 8);
gap> LastWord(w);
"aaaaaaaa"
gap> LastWord(w, "bb");
gap> UpperBound(w, 5);
gap> Count(w);
22
gap> ww := Strings(w);;
gap> IsIdenticalObj(w, ww);
false
gap> AsList(w);
[ "aa", "aaa", "aaaa", "aaab", "aab", "aaba", "aabb", "ab", "aba", "abaa",
  "abab", "abb", "abba", "abbb", "b", "ba", "baa", "baaa", "baab", "bab",
  "baba", "babb" ]
gap> AtEnd(w);
true
gap> AtEnd(ww);
false
gap> AsList(ww);
[ "aa", "aaa", "aaaa", "aaab", "aab", "aaba", "aabb", "ab", "aba", "abaa",
  "abab", "abb", "abba", "abbb", "b", "ba", "baa", "baaa", "baab", "bab",
  "baba", "babb" ]
gap> Init(ww);
gap> AsList(ww);
[  ]

# End
gap> SEMIGROUPS.StopTest();
gap> STOP_TEST("Semigroups package: standard/libsemigroups/cong.tst");
