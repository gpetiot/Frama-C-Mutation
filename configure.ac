
m4_define([plugin_file],Makefile.in)

m4_define([FRAMAC_SHARE_ENV],
          [m4_normalize(m4_esyscmd([echo $FRAMAC_SHARE]))])

m4_define([FRAMAC_SHARE],
	  [m4_ifval(FRAMAC_SHARE_ENV,[FRAMAC_SHARE_ENV],
                                     [m4_esyscmd(frama-c -print-path)])])

m4_ifndef([FRAMAC_M4_MACROS], [m4_include(FRAMAC_SHARE/configure.ac)])

check_plugin(mutation,PLUGIN_RELATIVE_PATH(plugin_file),
	     [support for Mutation plug-in],yes,yes)


# Check Frama-C version
#######################

AC_MSG_CHECKING(for Frama-C version)
AC_MSG_RESULT($FRAMAC_VERSION)

VERSION_NUMBER=`echo $FRAMAC_VERSION | sed -n -e 's/[[a-zA-Z]]\+-\([[0-9]]\+\)-.*/\1/p'`
EXTRA_VERSION_NUMBER=`echo $FRAMAC_VERSION | sed -n -e 's/[[a-zA-Z]]\+-[[0-9]]\+-\(.*\)/\1/p'`
REQUIRED_NUMBER=20180502
REQUIRED_NAME=Chlorine

case $FRAMAC_VERSION in
  # $REQUIRED_NAME-$REQUIRED_NUMBER+dev*)
  #   # at the time being, must use the Frama-C development version
  #   ;;
  $REQUIRED_NAME-$REQUIRED_NUMBER*)
    if test -n "$EXTRA_VERSION_NUMBER"; then
      AC_MSG_WARN(no guarantee of compatibility with your Frama-C custom \
version of $REQUIRED_NAME)
    fi;;
  *)
    if test $VERSION_NUMBER -lt $REQUIRED_NUMBER; then
      AC_MSG_ERROR(Frama-C version must be at least \
$REQUIRED_NAME-$REQUIRED_NUMBER.)
    else
      AC_MSG_WARN(Frama-C version is more recent than $REQUIRED_NAME: \
use it at your own risk)
    fi;;
esac

# OCaml version
###############

OCAMLVERSION=`ocamlc -v | sed -n -e 's|.*version *\(.*\)$|\1|p' `

MAY_RUN_TESTS=yes

# C compiler and stdio.h
#########################

AC_CHECK_HEADERS([stdio.h],[HAVE_STDIO_H=yes],)

# not sure it can actually happens:
# look like the configure stops on error if no C compiler detected
if test -z $HAVE_STDIO_H; then
  MAY_RUN_TESTS=no
  AC_MSG_WARN([stdio.h missing: non-regression tests unavailable.])
fi


#######################
# Generating Makefile #
#######################

AC_SUBST(MAY_RUN_TESTS)
AC_SUBST(OCAMLVERSION)

write_plugin_config(Makefile)
