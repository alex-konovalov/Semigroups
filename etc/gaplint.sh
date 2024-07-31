#!/bin/bash
set -e

gaplint --disable W004 $@ *.g gap/options.g gap/*.gi gap/*.gd gap/*/* doc/*.xml tst/*.tst tst/*/*.tst tst/*/*/*.tst
