# SYNOPSIS
#
#   AX_LIB_SAMTOOLS([MINIMUM-VERSION], [ACTION-IF-TRUE], [ACTION-IF-FALSE])
#
# DESCRIPTION
#
#   This macro will check for the existence of samtools 'bam' library.
#   (http://samtools.sourceforge.net/). It does this by checking for the
#   header file bam.h and the bam library object file. These are
#   initially searched for in the include and lib subdirectory of the
#   --with-samtools=DIR, and if not found there directly within DIR
#   itself. This allows for --with-samtools to be specified as either
#   an install root (eg /usr/local) or as an unpacked and compiled
#   source tree.
#
#   NOTE: if you use AX_LIB_SAMTOOLS make sure you have also previously
#   called AX_LIB_ZLIB as samtools has a dependency on zlib too.
#
#   The following output variables are set using AC_SUBST:
#
#     SAMTOOLS_CPPFLAGS
#     SAMTOOLS_LDFLAGS
#     SAMTOOLS_VERSION (if MINIMUM-VERSION is not "")
#
#   The C preprocessor symbol HAVE_SAMTOOLS will be also defined with
#   AC_DEFINE if a functioning samtools is available.
#
# LICENSE
#
#   Copyright (c) 2009,2013 James Bonfield <jkb@sanger.ac.uk>
#
#   Copying and distribution of this file, with or without
#   modification, are permitted in any medium without royalty
#   provided the copyright notice and this notice are preserved.
#   This file is offered as-is, without any warranty.

AC_DEFUN([AX_LIB_SAMTOOLS],
[
  AC_ARG_WITH(samtools,
	      AC_HELP_STRING([--with-samtools=DIR],[look for samtools in DIR]),
	      [_samtools_with=$withval],[_samtools_with="no"])

  SAMTOOLS_ROOT=""
  if test "$_samtools_with" != "no"
  then
      SAMTOOLS_ROOT=$_samtools_with
  fi

  # Check if it's a working library
  samtools_ok=no
  _cppflags=$CPPFLAGS
  _libs=$LIBS
  for extra_lib in "" "-lm -lpthread"
  do
  if test "x$SAMTOOLS_ROOT" != "x"
  then
      CPPFLAGS="$_cppflags -I${SAMTOOLS_ROOT}/include"
      LIBS="$_libs -L${SAMTOOLS_ROOT}/lib -lbam $ZLIB_LDFLAGS $extra_lib"
      AC_LANG_PUSH([C])
      AC_SEARCH_LIBS(bam_header_read, bam,
  	  [AC_CHECK_HEADER(bam.h, samtools_ok=yes, samtools_ok=no)])
      AC_LANG_POP([C])

      if test "$samtools_ok" == "yes"
      then
          SAMTOOLS_LDFLAGS="-L${SAMTOOLS_ROOT}/lib -lbam $ZLIB_LDFLAGS $extra_lib"
  	  SAMTOOLS_CFLAGS="-I${SAMTOOLS_ROOT}/include"
          break
      else
  	  # Maybe DIR is a source/build directory instead of an install dir.
  	  # So try again
  	  CPPFLAGS="$_cppflags -I${SAMTOOLS_ROOT}"
	  LIBS="$_libs -L${SAMTOOLS_ROOT} -lbam $ZLIB_LDFLAGS $extra_lib" 
	  AC_LANG_PUSH([C])
  	  AC_LANG_C

	  unset ac_cv_search_bam_header_read
  	  AC_SEARCH_LIBS(bam_header_read, bam,
  	      [AC_CHECK_HEADER(bam.h, samtools_ok=yes, samtools_ok=no)])
          AC_LANG_POP([C])
  	  
  	  if test "$samtools_ok" == "yes"
          then
              SAMTOOLS_LDFLAGS="-L${SAMTOOLS_ROOT} -lbam $ZLIB_LDFLAGS $extra_lib"
  	      SAMTOOLS_CFLAGS="-I${SAMTOOLS_ROOT}"
              break
          else
              # Backout and whinge
              CPPFLAGS=$_cppflags
	      LIBS=$_libs
              AC_MSG_WARN([--with-samtools specified, but non-functioning])
  	  fi
      fi
  else
      # Maybe it works "out of the box"?
      LIBS="$_libs -lbam $ZLIB_LDFLAGS $extra_lib"

      AC_LANG_PUSH([C])
      AC_CHECK_LIB(bam, bam_header_read,
          [AC_CHECK_HEADER(bam.h, samtools_ok=yes, samtools_ok=no)])
      AC_LANG_POP([C])

      if test "$samtools_ok" = "yes"
      then
          SAMTOOLS_LDFLAGS="-lbam $ZLIB_LDFLAGS $extra_lib"
          SAMTOOLS_CFLAGS=
          break
      fi
  fi
  done

  # Backout of variable changes
  CPPFLAGS=$_cppflags
  LIBS=$_libs

  # Check version number
  if test "x$1" != "x" && test "$samtools_ok" = "yes"
  then
      AC_MSG_CHECKING([if samtools version >= $1])

      if test "x$SAMTOOLS_ROOT" == "x"
      then
          samtools_exe=samtools
      elif test -x "$SAMTOOLS_ROOT/bin/samtools"
      then
	  samtools_exe="$SAMTOOLS_ROOT/bin/samtools"
      else
	  samtools_exe="$SAMTOOLS_ROOT/samtools"
      fi

      SAMTOOLS_VERSION=`$samtools_exe 2>&1 | sed -n 's/Version: *\(.*\)/\1/p'`
      AC_MSG_CHECKING([samtools_version ($SAMTOOLS_VERSION)])

      v1=`expr "$1" : '\([[0-9]]*\)'`
      v2=`expr "$1" : '[[0-9]]*\.\([[0-9]]*\)'`
      v3=`expr "$1" : '[[0-9]]*\.[[0-9]]*\.\([[0-9]]*\)'`
      want_vers=`expr "${v1:-0}" "*" 1000000 + "${v2:-0}" "*" 1000 + "${v3:-0}"`

      v1=`expr "$SAMTOOLS_VERSION" : '\([[0-9]]*\)'`
      v2=`expr "$SAMTOOLS_VERSION" : '[[0-9]]*\.\([[0-9]]*\)'`
      v3=`expr "$SAMTOOLS_VERSION" : '[[0-9]]*\.[[0-9]]*\.\([[0-9]]*\)'`
      have_vers=`expr "${v1:-0}" "*" 1000000 + "${v2:-0}" "*" 1000 + "${v3:-0}"`
      if test `expr "$have_vers" ">=" "$want_vers"` = "1"
      then
          AC_MSG_RESULT([yes])
          AC_SUBST([SAMTOOLS_VERSION])
      else
          AC_MSG_RESULT([no wanted $want_vers got $have_vers])
	  samtools_ok="no"
      fi
  fi


  # Perform the substitutions
  if test "$samtools_ok" = "yes"
  then
      AC_DEFINE(HAVE_SAMTOOLS, 1,
          [Define to 1 if you have a functional libbam.])
      AC_SUBST([SAMTOOLS_LDFLAGS])
      AC_SUBST([SAMTOOLS_CFLAGS])
  else
      AC_MSG_WARN([No functioning samtools found])
  fi

  # Not sure how many of these are needed, but it's belt-and-braces mode
  AH_TEMPLATE([HAVE_SAMTOOLS], [Define if samtools is installed])
  AM_CONDITIONAL(HAVE_SAMTOOLS, test "$samtools_ok" = "yes")

  # Execute the conditional expressions
  if test "$samtools_ok" = "yes"
  then
     # This is the IF-YES path
     ifelse([$2],,:,[$2])
  else
     # This is the IF-NO path
     ifelse([$3],,:,[$3])
  fi

  # Tidy up
  unset samtools_ok
  unset _cppflags
  unset _libs
])
