/* confdefs.h */
#define PACKAGE_NAME "The Glorious Glasgow Haskell Compilation System"
#define PACKAGE_TARNAME "ghc-8.2.0"
#define PACKAGE_VERSION "8.2.0"
#define PACKAGE_STRING "The Glorious Glasgow Haskell Compilation System 8.2.0"
#define PACKAGE_BUGREPORT "glasgow-haskell-bugs@haskell.org"
#define PACKAGE_URL ""
#define STDC_HEADERS 1
#define HAVE_SYS_TYPES_H 1
#define HAVE_SYS_STAT_H 1
#define HAVE_STDLIB_H 1
#define HAVE_STRING_H 1
#define HAVE_MEMORY_H 1
#define HAVE_STRINGS_H 1
#define HAVE_INTTYPES_H 1
#define HAVE_STDINT_H 1
#define HAVE_UNISTD_H 1
#define __EXTENSIONS__ 1
#define _ALL_SOURCE 1
#define _GNU_SOURCE 1
#define _POSIX_PTHREAD_SEMANTICS 1
#define _TANDEM_SOURCE 1
#define sUPPORTED_LLVM_VERSION (3,9)
#define STDC_HEADERS 1
#define _FILE_OFFSET_BITS 64
#define HAVE_CTYPE_H 1
#define HAVE_DIRENT_H 1
#define HAVE_ERRNO_H 1
#define HAVE_FCNTL_H 1
#define HAVE_LIMITS_H 1
#define HAVE_LOCALE_H 1
#define HAVE_PTHREAD_H 1
#define HAVE_SIGNAL_H 1
#define HAVE_SYS_PARAM_H 1
#define HAVE_SYS_TIME_H 1
#define HAVE_SYS_TIMEB_H 1
#define HAVE_TIME_H 1
#define HAVE_UTIME_H 1
#define HAVE_WINDOWS_H 1
#define HAVE_WINSOCK_H 1
#define HAVE_SCHED_H 1
#define TIME_WITH_SYS_TIME 1
#define HAVE_LONG_LONG 1
#define SIZEOF_CHAR 1
#define ALIGNMENT_CHAR 1
#define SIZEOF_DOUBLE 8
/* end confdefs.h.  */
#include <stdio.h>
#ifdef HAVE_SYS_TYPES_H
# include <sys/types.h>
#endif
#ifdef HAVE_SYS_STAT_H
# include <sys/stat.h>
#endif
#ifdef STDC_HEADERS
# include <stdlib.h>
# include <stddef.h>
#else
# ifdef HAVE_STDLIB_H
#  include <stdlib.h>
# endif
#endif
#ifdef HAVE_STRING_H
# if !defined STDC_HEADERS && defined HAVE_MEMORY_H
#  include <memory.h>
# endif
# include <string.h>
#endif
#ifdef HAVE_STRINGS_H
# include <strings.h>
#endif
#ifdef HAVE_INTTYPES_H
# include <inttypes.h>
#endif
#ifdef HAVE_STDINT_H
# include <stdint.h>
#endif
#ifdef HAVE_UNISTD_H
# include <unistd.h>
#endif
int
main ()
{
if (sizeof (double))
	 return 0;
  ;
  return 0;
}
