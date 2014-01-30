bin_PROGRAMS = spatial_filter_mkII

spatial_filter_mkII_SOURCES = spatial_filter_mkII.c

spatial_filter_mkII_LDADD = @IO_LIB_LDFLAGS@ @SAMTOOLS_LDFLAGS@ @PNG_LIBS@ @LIBRTREE_LDFLAGS@ -L../shared -lhelper_funcs

AM_CPPFLAGS = @IO_LIB_CFLAGS@ @SAMTOOLS_CFLAGS@ @PNG_CFLAGS@ @LIBRTREE_CFLAGS@ -I@top_srcdir@/shared
