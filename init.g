#############################################################################
##
##  init.g
##  Copyright (C) 2013-2022                              James D. Mitchell
##
##  Licensing information can be found in the README file of this package.
##
#############################################################################
##

if not IsBound(ORBC) then
  BindGlobal("HTAdd_TreeHash_C", fail);
  BindGlobal("HTValue_TreeHash_C", fail);
fi;

if LoadKernelExtension("semigroups") = false then
    Error("failed to load Semigroups kernel extension");
fi;

if not IsBound(UserHomeExpand) then
  BindGlobal("UserHomeExpand", USER_HOME_EXPAND);
fi;

if not IsBoundGlobal("IsTGapBind14Obj") then
  DeclareCategory("IsTGapBind14Obj", IsObject);
  BindGlobal("TheTypeTGapBind14Obj",
             NewType(NewFamily("TGapBind14ObjFamily"), IsTGapBind14Obj));
fi;

BindGlobal("SEMIGROUPS", rec());
MakeReadWriteGlobal("SEMIGROUPS");
SEMIGROUPS.GENERATORS := rec();
SEMIGROUPS.PackageDir := GAPInfo.PackagesLoaded.semigroups[1];

BindGlobal("LIBSEMIGROUPS_VERSION",
           Chomp(StringFile(Concatenation(SEMIGROUPS.PackageDir,
                                          "/.LIBSEMIGROUPS_VERSION"))));

# added when addressing issue #949
if not IsBound(PreImagesNC) then
    BindGlobal("PreImagesNC", PreImages);
fi;
if not IsBound(PreImagesElmNC) then
    BindGlobal("PreImagesElmNC", PreImagesElm);
fi;
if not IsBound(PreImagesSetNC) then
    BindGlobal("PreImagesSetNC", PreImagesSet);
fi;
if not IsBound(PreImagesRepresentativeNC) then
    BindGlobal("PreImagesRepresentativeNC", PreImagesRepresentative);
fi;

ReadPackage("semigroups", "gap/options.g");

ReadPackage("semigroups", "gap/elements/semiringmat.gd");
ReadPackage("semigroups", "gap/elements/star.gd");

ReadPackage("semigroups", "gap/elements/bipart.gd");
ReadPackage("semigroups", "gap/elements/blocks.gd");
ReadPackage("semigroups", "gap/elements/boolmat.gd");
ReadPackage("semigroups", "gap/elements/elements.gd");
ReadPackage("semigroups", "gap/elements/ffmat.gd");
ReadPackage("semigroups", "gap/elements/maxplusmat.gd");
ReadPackage("semigroups", "gap/elements/pbr.gd");
ReadPackage("semigroups", "gap/elements/pperm.gd");
ReadPackage("semigroups", "gap/elements/trans.gd");

ReadPackage("semigroups", "gap/libsemigroups/fpsemi.gd");
ReadPackage("semigroups", "gap/libsemigroups/froidure-pin.gd");
ReadPackage("semigroups", "gap/libsemigroups/sims1.gd");

ReadPackage("semigroups", "gap/main/froidure-pin.gd");
ReadPackage("semigroups", "gap/main/semiact.gd");
ReadPackage("semigroups", "gap/main/setup.gd");
ReadPackage("semigroups", "gap/main/lambda-rho.gd");
ReadPackage("semigroups", "gap/main/acting.gd");
ReadPackage("semigroups", "gap/main/graded.gd");
ReadPackage("semigroups", "gap/main/orbits.gd");

ReadPackage("semigroups", "gap/semigroups/semibipart.gd");
ReadPackage("semigroups", "gap/semigroups/semiboolmat.gd");
ReadPackage("semigroups", "gap/semigroups/semicons.gd");
ReadPackage("semigroups", "gap/semigroups/semidp.gd");
ReadPackage("semigroups", "gap/semigroups/semieunit.gd");
ReadPackage("semigroups", "gap/semigroups/semiex.gd");
ReadPackage("semigroups", "gap/semigroups/semiffmat.gd");
ReadPackage("semigroups", "gap/semigroups/semifp.gd");
ReadPackage("semigroups", "gap/semigroups/semigraph.gd");
ReadPackage("semigroups", "gap/semigroups/semigrp.gd");
ReadPackage("semigroups", "gap/semigroups/semintmat.gd");
ReadPackage("semigroups", "gap/semigroups/semimaxplus.gd");
ReadPackage("semigroups", "gap/semigroups/semipbr.gd");
ReadPackage("semigroups", "gap/semigroups/semipperm.gd");
ReadPackage("semigroups", "gap/semigroups/semiquo.gd");
ReadPackage("semigroups", "gap/semigroups/semiringmat.gd");
ReadPackage("semigroups", "gap/semigroups/semirms.gd");
ReadPackage("semigroups", "gap/semigroups/semitrans.gd");

ReadPackage("semigroups", "gap/semigroups/grpperm.gd");

ReadPackage("semigroups", "gap/ideals/acting.gd");
ReadPackage("semigroups", "gap/ideals/froidure-pin.gd");
ReadPackage("semigroups", "gap/ideals/ideals.gd");
ReadPackage("semigroups", "gap/ideals/lambda-rho.gd");

ReadPackage("semigroups", "gap/greens/froidure-pin.gd");
ReadPackage("semigroups", "gap/greens/generic.gd");
ReadPackage("semigroups", "gap/greens/acting.gd");

ReadPackage("semigroups", "gap/tools/display.gd");
ReadPackage("semigroups", "gap/tools/io.gd");
ReadPackage("semigroups", "gap/tools/iterators.gd");
ReadPackage("semigroups", "gap/tools/utils.gd");

ReadPackage("semigroups", "gap/attributes/acting.gd");
ReadPackage("semigroups", "gap/attributes/attr.gd");
ReadPackage("semigroups", "gap/attributes/dual.gd");
ReadPackage("semigroups", "gap/attributes/factor.gd");
ReadPackage("semigroups", "gap/attributes/inverse.gd");
ReadPackage("semigroups", "gap/attributes/isomorph.gd");
ReadPackage("semigroups", "gap/attributes/isorms.gd");
ReadPackage("semigroups", "gap/attributes/maximal.gd");
ReadPackage("semigroups", "gap/attributes/properties.gd");
ReadPackage("semigroups", "gap/attributes/homomorph.gd");
ReadPackage("semigroups", "gap/attributes/sandwich.gd");
ReadPackage("semigroups", "gap/attributes/semifp.gd");
ReadPackage("semigroups", "gap/attributes/translat.gd");
ReadPackage("semigroups", "gap/attributes/rms-translat.gd");

ReadPackage("semigroups", "gap/congruences/cong.gd");
ReadPackage("semigroups", "gap/congruences/congpart.gd");
ReadPackage("semigroups", "gap/congruences/conginv.gd");
ReadPackage("semigroups", "gap/congruences/conglatt.gd");
ReadPackage("semigroups", "gap/congruences/congpairs.gd");
ReadPackage("semigroups", "gap/congruences/congrees.gd");
ReadPackage("semigroups", "gap/congruences/congrms.gd");
ReadPackage("semigroups", "gap/congruences/congsemigraph.gd");
ReadPackage("semigroups", "gap/congruences/congsimple.gd");
ReadPackage("semigroups", "gap/congruences/conguniv.gd");
ReadPackage("semigroups", "gap/congruences/congwordgraph.gd");

ReadPackage("semigroups", "gap/libsemigroups/cong.gd");

ReadPackage("semigroups", "gap/fp/freeband.gd");
ReadPackage("semigroups", "gap/fp/freeinverse.gd");
ReadPackage("semigroups", "gap/fp/tietze.gd");
ReadPackage("semigroups", "gap/fp/word.gd");

ReadPackage("semigroups", "gap/obsolete.gd");

DeclareInfoClass("InfoSemigroups");
