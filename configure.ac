#
# Semigroups GAP package
#
# This file is part of the build system of a GAP kernel extension.
# Requires GNU autoconf, GNU automake and GNU libtool.
#

dnl ##
dnl ## Setup autoconf
dnl ##
AC_PREREQ([2.68])
AC_INIT([semigroups], [GAP package])
AC_CONFIG_SRCDIR([src/pkg.cpp])
AC_CONFIG_HEADERS([gen/pkgconfig.h:src/pkgconfig.h.in])
AC_CONFIG_MACRO_DIR([m4])

AX_PREFIX_CONFIG_H([src/semigroups-config.hpp],[semigroups],[gen/pkgconfig.h])

dnl ## abs_top_builddir seems to hold the top build dir for the subpackage
dnl ## libsemigroups which is why this contains ../
AC_PREFIX_DEFAULT('${abs_top_builddir}/../bin/')

dnl ##
dnl ## Set the language
dnl ##
AC_PROG_CXX
AC_LANG([C++])

AX_CXX_COMPILE_STDCXX_17(,[mandatory])

dnl ##
dnl ## Locate the GAP root dir
dnl ##
FIND_GAP

dnl ##
dnl ## Check for pthread, this seems to be required to compile with GCC
dnl ##
AX_PTHREAD(,[AC_MSG_ERROR([pthread is required])])
AC_CHECK_LIB([pthread], [pthread_create])

dnl ##
dnl ## Detect Windows resp. Cygwin
dnl ##
case $host_os in
  *cygwin* ) AC_SUBST(SYS_IS_CYGWIN, yes);;
esac


dnl ## Check for libsemigroups
AX_CHECK_LIBSEMIGROUPS

dnl ## User setting: Debug mode (off by default)
AC_ARG_ENABLE([debug],
    [AS_HELP_STRING([--enable-debug], [enable debug mode])],
    [AC_DEFINE([KERNEL_DEBUG], [1], [define if building in debug mode])],
    [enable_debug=no]
    )
AC_MSG_CHECKING([whether to enable debug mode])
AC_MSG_RESULT([$enable_debug])
KERNEL_DEBUG=$enable_debug
AC_SUBST(KERNEL_DEBUG)

# Check if HPCombi is enable, and available
AX_CHECK_HPCOMBI

dnl ##
dnl ## Output everything
dnl ##
AC_CONFIG_FILES([GNUmakefile])
AC_OUTPUT
