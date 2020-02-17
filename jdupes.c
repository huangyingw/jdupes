/* jdupes (C) 2015-2020 Jody Bruchon <jody@jodybruchon.com>
   Forked from fdupes 1.51 (C) 1999-2014 Adrian Lopez

   Permission is hereby granted, free of charge, to any person
   obtaining a copy of this software and associated documentation files
   (the "Software"), to deal in the Software without restriction,
   including without limitation the rights to use, copy, modify, merge,
   publish, distribute, sublicense, and/or sell copies of the Software,
   and to permit persons to whom the Software is furnished to do so,
   subject to the following conditions:

   The above copyright notice and this permission notice shall be
   included in all copies or substantial portions of the Software.

   THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS
   OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
   MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT.
   IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY
   CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT,
   TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION WITH THE
   SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE. */

#include <stdio.h>
#include <stdarg.h>
#include <stdlib.h>
#include <string.h>
#include <sys/types.h>
#include <fcntl.h>
#include <dirent.h>
#include <signal.h>
#include <unistd.h>
#include <stdlib.h>
#include <stdint.h>
#include <inttypes.h>
#ifndef OMIT_GETOPT_LONG
 #include <getopt.h>
#endif
#include <string.h>
#include <errno.h>
#include <libgen.h>
#include <sys/time.h>
#include "jdupes.h"
#include "string_malloc.h"
#include "xxhash.h"
#include "jody_sort.h"
#include "jody_win_unicode.h"
#include "jody_cacheinfo.h"
#include "version.h"

/* Headers for post-scanning actions */
#include "act_deletefiles.h"
#include "act_dedupefiles.h"
#include "act_linkfiles.h"
#include "act_printmatches.h"
#include "act_printjson.h"
#include "act_summarize.h"

/* Detect Windows and modify as needed */
#if defined _WIN32 || defined __CYGWIN__
 const char dir_sep = '\\';
 #ifdef UNICODE
  const wchar_t *FILE_MODE_RO = L"rbS";
 #else
  const char *FILE_MODE_RO = "rbS";
 #endif /* UNICODE */

#else /* Not Windows */
 const char *FILE_MODE_RO = "rb";
 const char dir_sep = '/';
 #ifdef UNICODE
  #error Do not define UNICODE on non-Windows platforms.
  #undef UNICODE
 #endif
#endif /* _WIN32 || __CYGWIN__ */

/* Windows + Unicode compilation */
#ifdef UNICODE
static wpath_t wname, wstr;
int out_mode = _O_TEXT;
int err_mode = _O_TEXT;
#endif /* UNICODE */

#ifndef NO_SYMLINKS
#include "jody_paths.h"
#endif

/* Behavior modification flags */
uint_fast32_t flags = 0, p_flags = 0;

static const char *program_name;

/* This gets used in many functions */
#ifdef ON_WINDOWS
 struct winstat s;
#else
 struct stat s;
#endif

/* Larger chunk size makes large files process faster but uses more RAM */
#define MIN_CHUNK_SIZE 4096
#define MAX_CHUNK_SIZE 16777216
#ifndef CHUNK_SIZE
 #define CHUNK_SIZE 65536
#endif
#ifndef PARTIAL_HASH_SIZE
 #define PARTIAL_HASH_SIZE 4096
#endif

static size_t auto_chunk_size = CHUNK_SIZE;

/* Maximum path buffer size to use; must be large enough for a path plus
 * any work that might be done to the array it's stored in. PATH_MAX is
 * not always true. Read this article on the false promises of PATH_MAX:
 * http://insanecoding.blogspot.com/2007/11/pathmax-simply-isnt.html
 * Windows + Unicode needs a lot more space than UTF-8 in Linux/Mac OS X
 */
#ifndef PATHBUF_SIZE
#define PATHBUF_SIZE 4096
#endif
/* Refuse to build if PATHBUF_SIZE is too small */
#if PATHBUF_SIZE < PATH_MAX
#error "PATHBUF_SIZE can't be less than PATH_MAX"
#endif

/* Size suffixes - this gets exported */
const struct size_suffix size_suffix[] = {
  /* Byte (someone may actually try to use this) */
  { "b", 1 },
  { "k", 1024 },
  { "kib", 1024 },
  { "m", 1048576 },
  { "mib", 1048576 },
  { "g", (uint64_t)1048576 * 1024 },
  { "gib", (uint64_t)1048576 * 1024 },
  { "t", (uint64_t)1048576 * 1048576 },
  { "tib", (uint64_t)1048576 * 1048576 },
  { "p", (uint64_t)1048576 * 1048576 * 1024},
  { "pib", (uint64_t)1048576 * 1048576 * 1024},
  { "e", (uint64_t)1048576 * 1048576 * 1048576},
  { "eib", (uint64_t)1048576 * 1048576 * 1048576},
  /* Decimal suffixes */
  { "kb", 1000 },
  { "mb", 1000000 },
  { "gb", 1000000000 },
  { "tb", 1000000000000 },
  { "pb", 1000000000000000 },
  { "eb", 1000000000000000000 },
  { NULL, 0 },
};

/* Assemble extension string from compile-time options */
const char *extensions[] = {
  #ifdef ON_WINDOWS
    "windows",
    #endif
    #ifdef UNICODE
    "unicode",
    #endif
    #ifdef OMIT_GETOPT_LONG
    "nolong",
    #endif
    #ifdef __FAST_MATH__
    "fastmath",
    #endif
    #ifdef DEBUG
    "debug",
    #endif
    #ifdef LOUD_DEBUG
    "loud",
    #endif
    #ifdef ENABLE_DEDUPE
    "fsdedup",
    #endif
    #ifdef LOW_MEMORY
    "lowmem",
    #endif
    #ifdef SMA_PAGE_SIZE
    "smapage",
    #endif
    #ifdef NO_PERMS
    "noperm",
    #endif
    #ifdef NO_HARDLINKS
    "nohardlink",
    #endif
    #ifdef NO_SYMLINKS
    "nosymlink",
    #endif
    #ifdef NO_USER_ORDER
    "nouserorder",
    #endif
    NULL
};

/* Tree to track each directory traversed */
struct travdone {
  struct travdone *left;
  struct travdone *right;
  jdupes_ino_t inode;
  dev_t device;
};
static struct travdone *travdone_head = NULL;

/* Extended filter tree head and static tag list */
struct extfilter *extfilter_head = NULL;
const struct extfilter_tags extfilter_tags[] = {
  { "dir",        X_DIR },
  { "size+",        X_SIZE_GT },
  { "size+=",        X_SIZE_GTEQ },
  { "size-=",        X_SIZE_LTEQ },
  { "size-",        X_SIZE_LT },
  { "size=",        X_SIZE_EQ },
  { NULL, 0 },
};

/* Required for progress indicator code */
static uintmax_t filecount = 0;
static uintmax_t progress = 0, item_progress = 0, dupecount = 0;
/* Number of read loops before checking progress indicator */
#define CHECK_MINIMUM 256

/* Hash/compare performance statistics (debug mode) */
#ifdef DEBUG
static unsigned int small_file = 0, partial_hash = 0, partial_elim = 0;
static unsigned int full_hash = 0, partial_to_full = 0, hash_fail = 0;
static uintmax_t comparisons = 0;
 #ifdef ON_WINDOWS
  #ifndef NO_HARDLINKS
static unsigned int hll_exclude = 0;
  #endif
 #endif
#endif /* DEBUG */

/* File tree head */
static file_t *filehead = NULL;
static file_t *filetail = NULL;

/* Directory/file parameter position counter */
static unsigned int user_item_count = 1;

/* Sort order reversal */
static int sort_direction = 1;

/* Signal handler */
static int interrupt = 0;

/* Progress indicator time */
struct timeval time1, time2;

/* For path name mangling */
char tempname[PATHBUF_SIZE * 2];

/***** End definitions, begin code *****/


/* Catch CTRL-C and either notify or terminate */
void sighandler(const int signum)
{
  (void)signum;
  if (interrupt || !ISFLAG(flags, F_SOFTABORT)) {
    fprintf(stderr, "\n");
    string_malloc_destroy();
    exit(EXIT_FAILURE);
  }
  interrupt = 1;
  return;
}

#ifndef ON_WINDOWS
void sigusr1(const int signum)
{
  (void)signum;
  if (!ISFLAG(flags, F_SOFTABORT)) SETFLAG(flags, F_SOFTABORT);
  else CLEARFLAG(flags, F_SOFTABORT);
  return;
}
#endif


/* Out of memory */
extern void oom(const char * const restrict msg)
{
  fprintf(stderr, "\nout of memory: %s\n", msg);
  string_malloc_destroy();
  exit(EXIT_FAILURE);
}


/* Null pointer failure */
extern void nullptr(const char * restrict func)
{
  static const char n[] = "(NULL)";
  if (func == NULL) func = n;
  fprintf(stderr, "\ninternal error: NULL pointer passed to %s\n", func);
  string_malloc_destroy();
  exit(EXIT_FAILURE);
}

/* Compare two hashes like memcmp() */
/* #define HASH_COMPARE(a,b) ((a > b) ? 1:((a == b) ? 0:-1)) */
/* Compare two hashes for equality only */
#define HASH_COMPARE(a,b) (a != b)


static inline char **cloneargs(const int argc, char **argv)
{
  static int x;
  static char **args;

  args = (char **)string_malloc(sizeof(char *) * (unsigned int)argc);
  if (args == NULL) oom("cloneargs() start");

  for (x = 0; x < argc; x++) {
    args[x] = (char *)string_malloc(strlen(argv[x]) + 1);
    if (args[x] == NULL) oom("cloneargs() loop");
    strcpy(args[x], argv[x]);
  }

  return args;
}


static int findarg(const char * const arg, const int start,
                const int argc, char **argv)
{
  int x;

  for (x = start; x < argc; x++)
    if (strcmp(argv[x], arg) == 0)
      return x;

  return x;
}

/* Find the first non-option argument after specified option. */
static int nonoptafter(const char *option, const int argc,
                char **oldargv, char **newargv)
{
  int x;
  int targetind;
  int testind;
  int startat = 1;

  targetind = findarg(option, 1, argc, oldargv);

  for (x = optind; x < argc; x++) {
    testind = findarg(newargv[x], startat, argc, oldargv);
    if (testind > targetind) return x;
    else startat = testind;
  }

  return x;
}


/* Update progress indicator if requested */
static void update_progress(const char * const restrict msg, const int file_percent)
{
  static int did_fpct = 0;

  /* The caller should be doing this anyway...but don't trust that they did */
  if (ISFLAG(flags, F_HIDEPROGRESS)) return;

  gettimeofday(&time2, NULL);

  if (progress == 0 || time2.tv_sec > time1.tv_sec) {
    fprintf(stderr, "\rProgress [%" PRIuMAX "/%" PRIuMAX ", %" PRIuMAX " pairs matched] %" PRIuMAX "%%",
      progress, filecount, dupecount, (progress * 100) / filecount);
    if (file_percent > -1 && msg != NULL) {
      fprintf(stderr, "  (%s: %d%%)         ", msg, file_percent);
      did_fpct = 1;
    } else if (did_fpct != 0) {
      fprintf(stderr, "                     ");
      did_fpct = 0;
    }
    fflush(stderr);
  }
  time1.tv_sec = time2.tv_sec;
  return;
}


/* Check file's stat() info to make sure nothing has changed
 * Returns 1 if changed, 0 if not changed, negative if error */
extern int file_has_changed(file_t * const restrict file)
{
  /* If -t/--nochangecheck specified then completely bypass this code */
  if (ISFLAG(flags, F_NOCHANGECHECK)) return 0;

  if (file == NULL || file->d_name == NULL) nullptr("file_has_changed()");
  LOUD(fprintf(stderr, "file_has_changed('%s')\n", file->d_name);)

  if (!ISFLAG(file->flags, F_VALID_STAT)) return -66;

  if (STAT(file->d_name, &s) != 0) return -2;
  if (file->inode != s.st_ino) return 1;
  if (file->size != s.st_size) return 1;
  if (file->device != s.st_dev) return 1;
  if (file->mtime != s.st_mtime) return 1;
  if (file->mode != s.st_mode) return 1;
#ifndef NO_PERMS
  if (file->uid != s.st_uid) return 1;
  if (file->gid != s.st_gid) return 1;
#endif
#ifndef NO_SYMLINKS
  if (lstat(file->d_name, &s) != 0) return -3;
  if ((S_ISLNK(s.st_mode) > 0) ^ ISFLAG(file->flags, F_IS_SYMLINK)) return 1;
#endif

  return 0;
}


extern inline int getfilestats(file_t * const restrict file)
{
  if (file == NULL || file->d_name == NULL) nullptr("getfilestats()");
  LOUD(fprintf(stderr, "getfilestats('%s')\n", file->d_name);)

  /* Don't stat the same file more than once */
  if (ISFLAG(file->flags, F_VALID_STAT)) return 0;
  SETFLAG(file->flags, F_VALID_STAT);

  if (STAT(file->d_name, &s) != 0) return -1;
  file->inode = s.st_ino;
  file->size = s.st_size;
  file->device = s.st_dev;
  file->mtime = s.st_mtime;
  file->mode = s.st_mode;
#ifndef NO_HARDLINKS
  file->nlink = s.st_nlink;
#endif
#ifndef NO_PERMS
  file->uid = s.st_uid;
  file->gid = s.st_gid;
#endif
#ifndef NO_SYMLINKS
  if (lstat(file->d_name, &s) != 0) return -1;
  if (S_ISLNK(s.st_mode) > 0) SETFLAG(file->flags, F_IS_SYMLINK);
#endif
  return 0;
}


static void add_extfilter(const char *option)
{
  char *opt, *p;
  struct extfilter *extf = extfilter_head;
  const struct extfilter_tags *tags = extfilter_tags;
  const struct size_suffix *ss = size_suffix;

  if (option == NULL) nullptr("add_extfilter()");

  LOUD(fprintf(stderr, "add_extfilter '%s'\n", option);)

  opt = string_malloc(strlen(option) + 1);
  if (opt == NULL) oom("add_extfilter option");
  strcpy(opt, option);
  p = opt;

  while (*p != ':' && *p != '\0') p++;

  /* Split tag string into *opt (tag) and *p (value) */
  if (*p == ':') {
    *p = '\0';
    p++;
  }

  while (tags->tag != NULL && strcmp(tags->tag, opt) != 0) tags++;
  if (tags->tag == NULL) goto bad_tag;

  /* Check for a tag that requires a value */
  if (tags->flags & XX_EXCL_DATA && *p == '\0') goto spec_missing;

  /* *p is now at the value, NOT the tag string! */

  if (extfilter_head != NULL) {
    /* Add to end of exclusion stack if head is present */
    while (extf->next != NULL) extf = extf->next;
    extf->next = string_malloc(sizeof(struct extfilter) + strlen(p) + 1);
    if (extf->next == NULL) oom("add_extfilter alloc");
    extf = extf->next;
  } else {
    /* Allocate extfilter_head if no exclusions exist yet */
    extfilter_head = string_malloc(sizeof(struct extfilter) + strlen(p) + 1);
    if (extfilter_head == NULL) oom("add_extfilter alloc");
    extf = extfilter_head;
  }

  /* Set tag value from predefined tag array */
  extf->flags = tags->flags;

  /* Initialize the new exclude element */
  extf->next = NULL;
  if (extf->flags & XX_EXCL_OFFSET) {
    /* Exclude uses a number; handle it with possible suffixes */
    *(extf->param) = '\0';
    /* Get base size */
    if (*p < '0' || *p > '9') goto bad_size_suffix;
    extf->size = strtoll(p, &p, 10);
    /* Handle suffix, if any */
    if (*p != '\0') {
      while (ss->suffix != NULL && strcasecmp(ss->suffix, p) != 0) ss++;
      if (ss->suffix == NULL) goto bad_size_suffix;
      extf->size *= ss->multiplier;
    }
  } else {
    /* Exclude uses string data; just copy it */
    extf->size = 0;
    if (*p != '\0') strcpy(extf->param, p);
    else *(extf->param) = '\0';
  }

  LOUD(fprintf(stderr, "Added extfilter: tag '%s', data '%s', size %lld, flags %d\n", opt, extf->param, (long long)extf->size, extf->flags);)
  string_free(opt);
  return;

spec_missing:
  fprintf(stderr, "extfilter spec missing or invalid: -X spec:data\n");
  exit(EXIT_FAILURE);
bad_tag:
  fprintf(stderr, "Invalid extfilter tag was specified\n");
  exit(EXIT_FAILURE);
bad_size_suffix:
  fprintf(stderr, "Invalid -X size suffix specified; use B or KMGTPE[i][B]\n");
  exit(EXIT_FAILURE);
}


/* Returns -1 if stat() fails, 0 if it's a directory, 1 if it's not */
extern int getdirstats(const char * const restrict name,
        jdupes_ino_t * const restrict inode, dev_t * const restrict dev,
        jdupes_mode_t * const restrict mode)
{
  if (name == NULL || inode == NULL || dev == NULL) nullptr("getdirstats");
  LOUD(fprintf(stderr, "getdirstats('%s', %p, %p)\n", name, (void *)inode, (void *)dev);)

  if (STAT(name, &s) != 0) return -1;
  *inode = s.st_ino;
  *dev = s.st_dev;
  *mode = s.st_mode;
  if (!S_ISDIR(s.st_mode)) return 1;
  return 0;
}


/* Check a pair of files for match exclusion conditions
 * Returns:
 *  0 if all condition checks pass
 * -1 or 1 on compare result less/more
 * -2 on an absolute exclusion condition met
 *  2 on an absolute match condition met
 * -3 on exclusion due to isolation
 * -4 on exlusion due to same filesystem
 * -5 on exclusion due to permissions */
extern int check_conditions(const file_t * const restrict file1, const file_t * const restrict file2)
{
  if (file1 == NULL || file2 == NULL || file1->d_name == NULL || file2->d_name == NULL) nullptr("check_conditions()");

  LOUD(fprintf(stderr, "check_conditions('%s', '%s')\n", file1->d_name, file2->d_name);)

  /* Exclude files that are not the same size */
  if (file1->size > file2->size) {
    LOUD(fprintf(stderr, "check_conditions: no match: size of file1 > file2 (%" PRIdMAX " > %" PRIdMAX ")\n",
      (intmax_t)file1->size, (intmax_t)file2->size));
    return -1;
  }
  if (file1->size < file2->size) {
    LOUD(fprintf(stderr, "check_conditions: no match: size of file1 < file2 (%" PRIdMAX " < %"PRIdMAX ")\n",
      (intmax_t)file1->size, (intmax_t)file2->size));
    return 1;
  }

#ifndef NO_USER_ORDER
  /* Exclude based on -I/--isolate */
  if (ISFLAG(flags, F_ISOLATE) && (file1->user_order == file2->user_order)) {
    LOUD(fprintf(stderr, "check_conditions: files ignored: parameter isolation\n"));
    return -3;
  }
#endif /* NO_USER_ORDER */

  /* Exclude based on -1/--one-file-system */
  if (ISFLAG(flags, F_ONEFS) && (file1->device != file2->device)) {
    LOUD(fprintf(stderr, "check_conditions: files ignored: not on same filesystem\n"));
    return -4;
  }

   /* Exclude files by permissions if requested */
  if (ISFLAG(flags, F_PERMISSIONS) &&
          (file1->mode != file2->mode
#ifndef NO_PERMS
          || file1->uid != file2->uid
          || file1->gid != file2->gid
#endif
          )) {
    return -5;
    LOUD(fprintf(stderr, "check_conditions: no match: permissions/ownership differ (-p on)\n"));
  }

  /* Hard link and symlink + '-s' check */
#ifndef NO_HARDLINKS
  if ((file1->inode == file2->inode) && (file1->device == file2->device)) {
    if (ISFLAG(flags, F_CONSIDERHARDLINKS)) {
      LOUD(fprintf(stderr, "check_conditions: files match: hard/soft linked (-H on)\n"));
      return 2;
    } else {
      LOUD(fprintf(stderr, "check_conditions: files ignored: hard/soft linked (-H off)\n"));
      return -2;
    }
  }
#endif

  /* Fall through: all checks passed */
  LOUD(fprintf(stderr, "check_conditions: all condition checks passed\n"));
  return 0;
}


/* Check for exclusion conditions for a single file (1 = fail) */
static int check_singlefile(file_t * const restrict newfile)
{
  char * restrict tp = tempname;
  int excluded;

  if (newfile == NULL) nullptr("check_singlefile()");

  LOUD(fprintf(stderr, "check_singlefile: checking '%s'\n", newfile->d_name));

  /* Exclude hidden files if requested */
  if (ISFLAG(flags, F_EXCLUDEHIDDEN)) {
    if (newfile->d_name == NULL) nullptr("check_singlefile newfile->d_name");
    strcpy(tp, newfile->d_name);
    tp = basename(tp);
    if (tp[0] == '.' && strcmp(tp, ".") && strcmp(tp, "..")) {
      LOUD(fprintf(stderr, "check_singlefile: excluding hidden file (-A on)\n"));
      return 1;
    }
  }

  /* Get file information and check for validity */
  const int i = getfilestats(newfile);
  if (i || newfile->size == -1) {
    LOUD(fprintf(stderr, "check_singlefile: excluding due to bad stat()\n"));
    return 1;
  }

  if (!S_ISDIR(newfile->mode)) {
    /* Exclude zero-length files if requested */
    if (newfile->size == 0 && !ISFLAG(flags, F_INCLUDEEMPTY)) {
    LOUD(fprintf(stderr, "check_singlefile: excluding zero-length empty file (-z not set)\n"));
    return 1;
  }

    /* Exclude files based on exclusion stack size specs */
    excluded = 0;
    for (struct extfilter *extf = extfilter_head; extf != NULL; extf = extf->next) {
      uint32_t sflag = extf->flags & XX_EXCL_SIZE;
      if (
           ((sflag == X_SIZE_EQ) && (newfile->size != extf->size)) ||
           ((sflag == X_SIZE_LTEQ) && (newfile->size <= extf->size)) ||
           ((sflag == X_SIZE_GTEQ) && (newfile->size >= extf->size)) ||
           ((sflag == X_SIZE_GT) && (newfile->size > extf->size)) ||
           ((sflag == X_SIZE_LT) && (newfile->size < extf->size))
      ) excluded = 1;
    }
    if (excluded) {
      LOUD(fprintf(stderr, "check_singlefile: excluding based on xsize limit (-x set)\n"));
      return 1;
    }
  }

#ifdef ON_WINDOWS
  /* Windows has a 1023 (+1) hard link limit. If we're hard linking,
   * ignore all files that have hit this limit */
 #ifndef NO_HARDLINKS
  if (ISFLAG(flags, F_HARDLINKFILES) && newfile->nlink >= 1024) {
  #ifdef DEBUG
    hll_exclude++;
  #endif
    LOUD(fprintf(stderr, "check_singlefile: excluding due to Windows 1024 hard link limit\n"));
    return 1;
  }
 #endif /* NO_HARDLINKS */
#endif /* ON_WINDOWS */
  return 0;
}


/* Initialize a new file entry, but don't connect to the file list */
static file_t *init_newfile(const size_t len)
{
  file_t * const restrict newfile = (file_t *)string_malloc(sizeof(file_t));

  if (!newfile) oom("init_newfile() file structure");

  LOUD(fprintf(stderr, "init_newfile(len %lu)\n", len));

  memset(newfile, 0, sizeof(file_t));
  newfile->d_name = (char *)string_malloc(len);
  if (!newfile->d_name) oom("init_newfile() filename");

#ifndef NO_USER_ORDER
  newfile->user_order = user_item_count;
#endif
  newfile->size = -1;
  newfile->next = NULL;
  newfile->dupe_prev = NULL;
  newfile->dupe_next = NULL;
  return newfile;
}


/* Attach new file to the end of the file list */
static void connect_newfile(file_t * const restrict newfile)
{
  LOUD(fprintf(stderr, "connect_newfile(%p, h %p t %p)\n", newfile, filehead, filetail));
  if (newfile == filehead || newfile == filetail) {
    LOUD(fprintf(stderr, "connect_newfile: newfile and filehead/filetail are the same!\n");)
    return;
  }
  if (filehead == NULL) filehead = newfile;
  else filetail->next = newfile;
  filetail = newfile;
  return;
}


/* Create a new traversal check object and initialize its values */
static struct travdone *travdone_alloc(const jdupes_ino_t inode, const dev_t device)
{
  struct travdone *trav;

  LOUD(fprintf(stderr, "travdone_alloc(%" PRIdMAX ", %" PRIdMAX ")\n", (intmax_t)inode, (intmax_t)device);)

  trav = (struct travdone *)string_malloc(sizeof(struct travdone));
  if (trav == NULL) {
    LOUD(fprintf(stderr, "travdone_alloc: malloc failed\n");)
    return NULL;
  }
  trav->left = NULL;
  trav->right = NULL;
  trav->inode = inode;
  trav->device = device;
  LOUD(fprintf(stderr, "travdone_alloc returned %p\n", (void *)trav);)
  return trav;
}


/* De-allocate the travdone tree */
static void travdone_free(struct travdone * const restrict cur)
{
  if (cur == NULL) return;
  if (cur->left != NULL) travdone_free(cur->left);
  if (cur->right != NULL) travdone_free(cur->right);
  string_free(cur);
  return;
}


/* Add a single file to the file tree */
static inline file_t *grokfile(const char * const restrict name)
{
  file_t * restrict newfile;

  if (!name) nullptr("grokfile()");
  LOUD(fprintf(stderr, "grokfile: '%s'\n", name));

  /* Allocate the file_t and the d_name entries */
  newfile = init_newfile(strlen(name) + 2);

  strcpy(newfile->d_name, name);

  /* Single-file [l]stat() and exclusion condition check */
  if (check_singlefile(newfile) != 0) {
    LOUD(fprintf(stderr, "grokfile: check_singlefile rejected file\n"));
    string_free(newfile->d_name);
    string_free(newfile);
    return NULL;
  }
  return newfile;
}


/* Load a directory's contents into the file list, recursing as needed */
static void grokdir(const char * const restrict dir,
                int recurse)
{
  file_t * restrict newfile;
  struct dirent *dirinfo;
  static int grokdir_level = 0;
  size_t dirlen;
  struct travdone *traverse;
  int i, single = 0;
  jdupes_ino_t inode;
  dev_t device, n_device;
  jdupes_mode_t mode;
#ifdef UNICODE
  WIN32_FIND_DATA ffd;
  HANDLE hFind = INVALID_HANDLE_VALUE;
  char *p;
#else
  DIR *cd;
#endif

  if (dir == NULL) nullptr("grokdir()");
  LOUD(fprintf(stderr, "grokdir: scanning '%s' (order %d, recurse %d)\n", dir, user_item_count, recurse));

  /* Double traversal prevention tree */
  i = getdirstats(dir, &inode, &device, &mode);
  if (i < 0) goto error_travdone;

  if (travdone_head == NULL) {
    travdone_head = travdone_alloc(inode, device);
    if (travdone_head == NULL) goto error_travdone;
  } else {
    traverse = travdone_head;
    while (1) {
      if (traverse == NULL) nullptr("grokdir() traverse");
      /* Don't re-traverse directories we've already seen */
      if (S_ISDIR(mode) && inode == traverse->inode && device == traverse->device) {
        LOUD(fprintf(stderr, "already seen item '%s', skipping\n", dir);)
        return;
      } else if (inode > traverse->inode || (inode == traverse->inode && device > traverse->device)) {
        /* Traverse right */
        if (traverse->right == NULL) {
          LOUD(fprintf(stderr, "traverse item right '%s'\n", dir);)
          traverse->right = travdone_alloc(inode, device);
          if (traverse->right == NULL) goto error_travdone;
          break;
        }
        traverse = traverse->right;
        continue;
      } else {
        /* Traverse left */
        if (traverse->left == NULL) {
          LOUD(fprintf(stderr, "traverse item left '%s'\n", dir);)
          traverse->left = travdone_alloc(inode, device);
          if (traverse->left == NULL) goto error_travdone;
          break;
        }
        traverse = traverse->left;
        continue;
      }
    }
  }

  item_progress++;
  grokdir_level++;

  /* if dir is actually a file, just add it to the file tree */
  if (i == 1) {
    newfile = grokfile(dir);
    if (newfile == NULL) {
      LOUD(fprintf(stderr, "grokfile rejected '%s'\n", dir));
      return;
    }
    single = 1;
    goto add_single_file;
  }

#ifdef UNICODE
  /* Windows requires \* at the end of directory names */
  strncpy(tempname, dir, PATHBUF_SIZE * 2 - 1);
  dirlen = strlen(tempname) - 1;
  p = tempname + dirlen;
  if (*p == '/' || *p == '\\') *p = '\0';
  strncat(tempname, "\\*", PATHBUF_SIZE * 2 - 1);

  if (!M2W(tempname, wname)) goto error_cd;

  LOUD(fprintf(stderr, "FindFirstFile: %s\n", dir));
  hFind = FindFirstFileW(wname, &ffd);
  if (hFind == INVALID_HANDLE_VALUE) { LOUD(fprintf(stderr, "\nfile handle bad\n")); goto error_cd; }
  LOUD(fprintf(stderr, "Loop start\n"));
  do {
    char * restrict tp = tempname;
    size_t d_name_len;

    /* Get necessary length and allocate d_name */
    dirinfo = (struct dirent *)string_malloc(sizeof(struct dirent));
    if (!W2M(ffd.cFileName, dirinfo->d_name)) continue;
#else
  cd = opendir(dir);
  if (!cd) goto error_cd;

  while ((dirinfo = readdir(cd)) != NULL) {
    char * restrict tp = tempname;
    size_t d_name_len;
#endif /* UNICODE */

    LOUD(fprintf(stderr, "grokdir: readdir: '%s'\n", dirinfo->d_name));
    if (!strcmp(dirinfo->d_name, ".") || !strcmp(dirinfo->d_name, "..")) continue;
    if (!ISFLAG(flags, F_HIDEPROGRESS)) {
      gettimeofday(&time2, NULL);
      if (progress == 0 || time2.tv_sec > time1.tv_sec) {
        fprintf(stderr, "\rScanning: %" PRIuMAX " files, %" PRIuMAX " dirs (in %u specified)",
            progress, item_progress, user_item_count);
      }
      time1.tv_sec = time2.tv_sec;
    }

    /* Assemble the file's full path name, optimized to avoid strcat() */
    dirlen = strlen(dir);
    d_name_len = strlen(dirinfo->d_name);
    memcpy(tp, dir, dirlen+1);
    if (dirlen != 0 && tp[dirlen-1] != dir_sep) {
      tp[dirlen] = dir_sep;
      dirlen++;
    }
    if (dirlen + d_name_len + 1 >= (PATHBUF_SIZE * 2)) goto error_overflow;
    tp += dirlen;
    memcpy(tp, dirinfo->d_name, d_name_len);
    tp += d_name_len;
    *tp = '\0';
    d_name_len++;

    /* Allocate the file_t and the d_name entries */
    newfile = init_newfile(dirlen + d_name_len + 2);

    tp = tempname;
    memcpy(newfile->d_name, tp, dirlen + d_name_len);

    /*** WARNING: tempname global gets reused by check_singlefile here! ***/

    /* Single-file [l]stat() and exclusion condition check */
    if (check_singlefile(newfile) != 0) {
      LOUD(fprintf(stderr, "grokdir: check_singlefile rejected file\n"));
      string_free(newfile->d_name);
      string_free(newfile);
      continue;
    }

    /* Optionally recurse directories, including symlinked ones if requested */
    if (S_ISDIR(newfile->mode)) {
      if (recurse) {
        /* --one-file-system - WARNING: this clobbers inode/mode */
        if (ISFLAG(flags, F_ONEFS)
            && (getdirstats(newfile->d_name, &inode, &n_device, &mode) == 0)
            && (device != n_device)) {
          LOUD(fprintf(stderr, "grokdir: directory: not recursing (--one-file-system)\n"));
          string_free(newfile->d_name);
          string_free(newfile);
          continue;
        }
#ifndef NO_SYMLINKS
        else if (ISFLAG(flags, F_FOLLOWLINKS) || !ISFLAG(newfile->flags, F_IS_SYMLINK)) {
          LOUD(fprintf(stderr, "grokdir: directory(symlink): recursing (-r/-R)\n"));
          grokdir(newfile->d_name, recurse);
        }
#else
        else {
          LOUD(fprintf(stderr, "grokdir: directory: recursing (-r/-R)\n"));
          grokdir(newfile->d_name, recurse);
        }
#endif
      } else { LOUD(fprintf(stderr, "grokdir: directory: not recursing\n")); }
      string_free(newfile->d_name);
      string_free(newfile);
      continue;
    } else {
add_single_file:
      /* Add regular files to list, including symlink targets if requested */
#ifndef NO_SYMLINKS
      if (!ISFLAG(newfile->flags, F_IS_SYMLINK) || (ISFLAG(newfile->flags, F_IS_SYMLINK) && ISFLAG(flags, F_FOLLOWLINKS))) {
#else
      if (S_ISREG(newfile->mode)) {
#endif
        connect_newfile(newfile);
        filecount++;
        progress++;

      } else {
        LOUD(fprintf(stderr, "grokdir: not a regular file: %s\n", newfile->d_name);)
        string_free(newfile->d_name);
        string_free(newfile);
        if (single == 1) {
          single = 0;
          goto skip_single;
        }
        continue;
      }
    }
    /* Skip directory stuff if adding only a single file */
    if (single == 1) {
      single = 0;
      goto skip_single;
    }
  }

#ifdef UNICODE
  while (FindNextFileW(hFind, &ffd) != 0);
  FindClose(hFind);
#else
  closedir(cd);
#endif

skip_single:
  grokdir_level--;
  if (grokdir_level == 0 && !ISFLAG(flags, F_HIDEPROGRESS)) {
    fprintf(stderr, "\rScanning: %" PRIuMAX " files, %" PRIuMAX " items (in %u specified)",
            progress, item_progress, user_item_count);
  }
  return;

error_travdone:
  fprintf(stderr, "\ncould not stat dir "); fwprint(stderr, dir, 1);
  return;
error_cd:
  fprintf(stderr, "\ncould not chdir to "); fwprint(stderr, dir, 1);
  return;
error_overflow:
  fprintf(stderr, "\nerror: a path buffer overflowed\n");
  exit(EXIT_FAILURE);
}


/* Hash part or all of a file */
static jdupes_hash_t *get_filehash(const file_t * const restrict checkfile,
                const size_t max_read)
{
  off_t fsize;
  /* This is an array because we return a pointer to it */
  static jdupes_hash_t hash[1];
  static jdupes_hash_t *chunk = NULL;
  FILE *file;
  int check = 0;
  XXH64_state_t *xxhstate;

  if (checkfile == NULL || checkfile->d_name == NULL) nullptr("get_filehash()");
  LOUD(fprintf(stderr, "get_filehash('%s', %" PRIdMAX ")\n", checkfile->d_name, (intmax_t)max_read);)

  /* Allocate on first use */
  if (chunk == NULL) {
    chunk = (jdupes_hash_t *)string_malloc(auto_chunk_size);
    if (!chunk) oom("get_filehash() chunk");
  }

  /* Get the file size. If we can't read it, bail out early */
  if (checkfile->size == -1) {
    LOUD(fprintf(stderr, "get_filehash: not hashing because stat() info is bad\n"));
    return NULL;
  }
  fsize = checkfile->size;

  /* Do not read more than the requested number of bytes */
  if (max_read > 0 && fsize > (off_t)max_read)
    fsize = (off_t)max_read;

  /* Initialize the hash and file read parameters (with filehash_partial skipped)
   *
   * If we already hashed the first chunk of this file, we don't want to
   * wastefully read and hash it again, so skip the first chunk and use
   * the computed hash for that chunk as our starting point.
   */

  *hash = 0;
  if (ISFLAG(checkfile->flags, F_HASH_PARTIAL)) {
    *hash = checkfile->filehash_partial;
    /* Don't bother going further if max_read is already fulfilled */
    if (max_read != 0 && max_read <= PARTIAL_HASH_SIZE) {
      LOUD(fprintf(stderr, "Partial hash size (%d) >= max_read (%" PRIuMAX "), not hashing anymore\n", PARTIAL_HASH_SIZE, (uintmax_t)max_read);)
      return hash;
    }
  }
  errno = 0;
#ifdef UNICODE
  if (!M2W(checkfile->d_name, wstr)) file = NULL;
  else file = _wfopen(wstr, FILE_MODE_RO);
#else
  file = fopen(checkfile->d_name, FILE_MODE_RO);
#endif
  if (file == NULL) {
    fprintf(stderr, "\n%s error opening file ", strerror(errno)); fwprint(stderr, checkfile->d_name, 1);
    return NULL;
  }
  /* Actually seek past the first chunk if applicable
   * This is part of the filehash_partial skip optimization */
  if (ISFLAG(checkfile->flags, F_HASH_PARTIAL)) {
    if (fseeko(file, PARTIAL_HASH_SIZE, SEEK_SET) == -1) {
      fclose(file);
      fprintf(stderr, "\nerror seeking in file "); fwprint(stderr, checkfile->d_name, 1);
      return NULL;
    }
    fsize -= PARTIAL_HASH_SIZE;
  }

  xxhstate = XXH64_createState();
  if (xxhstate == NULL) nullptr("xxhstate");
  XXH64_reset(xxhstate, 0);

  /* Read the file in CHUNK_SIZE chunks until we've read it all. */
  while (fsize > 0) {
    size_t bytes_to_read;

    if (interrupt) return 0;
    bytes_to_read = (fsize >= (off_t)auto_chunk_size) ? auto_chunk_size : (size_t)fsize;
    if (fread((void *)chunk, bytes_to_read, 1, file) != 1) {
      fprintf(stderr, "\nerror reading from file "); fwprint(stderr, checkfile->d_name, 1);
      fclose(file);
      return NULL;
    }

    XXH64_update(xxhstate, chunk, bytes_to_read);

    if ((off_t)bytes_to_read > fsize) break;
    else fsize -= (off_t)bytes_to_read;

    if (!ISFLAG(flags, F_HIDEPROGRESS)) {
      check++;
      if (check > CHECK_MINIMUM) {
        update_progress("hashing", (int)(((checkfile->size - fsize) * 100) / checkfile->size));
        check = 0;
      }
    }
  }

  fclose(file);

  *hash = XXH64_digest(xxhstate);
  XXH64_freeState(xxhstate);

  LOUD(fprintf(stderr, "get_filehash: returning hash: 0x%016jx\n", (uintmax_t)*hash));
  return hash;
}


/* Check two files for a match */
static int checkmatch(file_t * const restrict file1, file_t * const restrict file2)
{
  int cmpresult = 0;
  int cantmatch = 0;
  const jdupes_hash_t * restrict filehash;

  if (file1 == NULL || file2 == NULL || file1->d_name == NULL || file2->d_name == NULL) nullptr("checkmatch()");
  LOUD(fprintf(stderr, "checkmatch ('%s', '%s')\n", file1->d_name, file2->d_name));

  /* If device and inode fields are equal one of the files is a
   * hard link to the other or the files have been listed twice
   * unintentionally. We don't want to flag these files as
   * duplicates unless the user specifies otherwise. */

  /* Count the total number of comparisons requested */
  DBG(comparisons++;)

/* If considering hard linked files as duplicates, they are
 * automatically duplicates without being read further since
 * they point to the exact same inode. If we aren't considering
 * hard links as duplicates, we just return 0 */

  cmpresult = check_conditions(file1, file2);
  LOUD(fprintf(stderr, "check_conditions returned %d\n", cmpresult);)
  switch (cmpresult) {
    case 2: return 1;  /* linked files + -H switch */
    case -2: return 0;  /* linked files, no -H switch */
    case -3:    /* user order */
    case -4:    /* one filesystem */
    case -5:    /* permissions */
        cantmatch = 1;
        cmpresult = 0;
        break;
    default: break;
  }

  /* Print pre-check (early) match candidates if requested */
  if (ISFLAG(p_flags, P_EARLYMATCH)) printf("Early match check passed:\n   %s\n   %s\n\n", file1->d_name, file2->d_name);

  /* If preliminary matching succeeded, do main file data checks */
  if (cmpresult == 0) {
    LOUD(fprintf(stderr, "checkmatch: starting file data comparisons\n"));
    /* Attempt to exclude files quickly with partial file hashing */
    if (!ISFLAG(file1->flags, F_HASH_PARTIAL)) {
      filehash = get_filehash(file1, PARTIAL_HASH_SIZE);
      if (filehash == NULL) return 0;

      file1->filehash_partial = *filehash;
      SETFLAG(file1->flags, F_HASH_PARTIAL);
    }

    if (!ISFLAG(file2->flags, F_HASH_PARTIAL)) {
      filehash = get_filehash(file2, PARTIAL_HASH_SIZE);
      if (filehash == NULL) return 0;

      file2->filehash_partial = *filehash;
      SETFLAG(file2->flags, F_HASH_PARTIAL);
    }

    cmpresult = HASH_COMPARE(file1->filehash_partial, file2->filehash_partial);
    LOUD(if (!cmpresult) fprintf(stderr, "checkmatch: partial hashes match\n"));
    LOUD(if (cmpresult) fprintf(stderr, "checkmatch: partial hashes do not match\n"));
    DBG(partial_hash++;)

    /* Print partial hash matching pairs if requested */
    if (cmpresult == 0 && ISFLAG(p_flags, P_PARTIAL))
      printf("Partial hashes match:\n   %s\n   %s\n\n", file1->d_name, file1->d_name);

    if (file1->size <= PARTIAL_HASH_SIZE || ISFLAG(flags, F_PARTIALONLY)) {
      if (ISFLAG(flags, F_PARTIALONLY)) {
        LOUD(fprintf(stderr, "checkmatch: partial only mode: treating partial hash as full hash\n"));
      } else {
        LOUD(fprintf(stderr, "checkmatch: small file: copying partial hash to full hash\n"));
      }
      /* filehash_partial = filehash if file is small enough */
      if (!ISFLAG(file1->flags, F_HASH_FULL)) {
        file1->filehash = file1->filehash_partial;
        SETFLAG(file1->flags, F_HASH_FULL);
        DBG(small_file++;)
      }
      if (!ISFLAG(file1->flags, F_HASH_FULL)) {
        file1->filehash = file1->filehash_partial;
        SETFLAG(file1->flags, F_HASH_FULL);
        DBG(small_file++;)
      }
    } else if (cmpresult == 0) {
      if (ISFLAG(flags, F_SKIPHASH)) {
        /* Skip full file hashing if requested by the user */
        LOUD(fprintf(stderr, "checkmatch: skipping full file hashes (F_SKIPMATCH)\n"));
      } else {
        /* If partial match was correct, perform a full file hash match */
        if (!ISFLAG(file1->flags, F_HASH_FULL)) {
          filehash = get_filehash(file1, 0);
          if (filehash == NULL) return 0;

          file1->filehash = *filehash;
          SETFLAG(file1->flags, F_HASH_FULL);
        }

        if (!ISFLAG(file1->flags, F_HASH_FULL)) {
          filehash = get_filehash(file2, 0);
          if (filehash == NULL) return 0;

          file1->filehash = *filehash;
          SETFLAG(file1->flags, F_HASH_FULL);
        }

        /* Full file hash comparison */
        cmpresult = HASH_COMPARE(file1->filehash, file2->filehash);
        LOUD(if (!cmpresult) fprintf(stderr, "checkmatch: full hashes match\n"));
        LOUD(if (cmpresult) fprintf(stderr, "checkmatch: full hashes do not match\n"));
        DBG(full_hash++);
      }
    } else {
      DBG(partial_elim++);
    }
  }

  if ((cantmatch != 0) && (cmpresult == 0)) {
    LOUD(fprintf(stderr, "checkmatch: rejecting because match not allowed (cantmatch = 1)\n"));
    cmpresult = -1;
  }

  if (cmpresult != 0) {
    LOUD(fprintf(stderr, "checkmatch: files do not appear to match\n"));
    return 0;
  } else {
    /* All compares matched */
    DBG(partial_to_full++;)
    LOUD(fprintf(stderr, "checkmatch: files appear to match based on hashes\n"));
    return 1;
  }
  /* Fall through - should never be reached */
  return 0;
}


/* Do a byte-by-byte comparison in case two different files produce the
   same signature. Unlikely, but better safe than sorry. */
static inline int confirmmatch(FILE * const restrict file1, FILE * const restrict file2, const off_t size)
{
  static char *c1 = NULL, *c2 = NULL;
  size_t r1, r2;
  off_t bytes = 0;
  int check = 0;

  if (file1 == NULL || file2 == NULL) nullptr("confirmmatch()");
  LOUD(fprintf(stderr, "confirmmatch running\n"));

  /* Allocate on first use; OOM if either is ever NULLed */
  if (!c1) {
    c1 = (char *)string_malloc(auto_chunk_size);
    c2 = (char *)string_malloc(auto_chunk_size);
  }
  if (!c1 || !c2) oom("confirmmatch() c1/c2");

  fseek(file1, 0, SEEK_SET);
  fseek(file2, 0, SEEK_SET);

  do {
    if (interrupt) return 0;
    r1 = fread(c1, sizeof(char), auto_chunk_size, file1);
    r2 = fread(c2, sizeof(char), auto_chunk_size, file2);

    if (r1 != r2) return 0; /* file lengths are different */
    if (memcmp (c1, c2, r1)) return 0; /* file contents are different */

    if (!ISFLAG(flags, F_HIDEPROGRESS)) {
      check++;
      bytes += (off_t)r1;
      if (check > CHECK_MINIMUM) {
        update_progress("confirm", (int)((bytes * 100) / size));
        check = 0;
      }
    }
  } while (r2);

  return 1;
}


/* Count the following statistics:
   - Maximum number of files in a duplicate set (length of longest dupe chain)
   - Number of non-zero-length files that have duplicates (if n_files != NULL)
   - Total number of duplicate file sets (groups) */
extern unsigned int get_max_dupes(const file_t *files, unsigned int * const restrict max,
                unsigned int * const restrict n_files) {
  unsigned int groups = 0;

  if (files == NULL || max == NULL) nullptr("get_max_dupes()");
  LOUD(fprintf(stderr, "get_max_dupes(%p, %p, %p)\n", (const void *)files, (void *)max, (void *)n_files));

  *max = 0;
  if (n_files) *n_files = 0;

  while (files) {
    unsigned int n_dupes;
    file_t *curdupe;
// XXX
    if (ISFLAG(files->flags, F_DUPE_HEAD)) {
      groups++;
      if (n_files && files->size) (*n_files)++;
      n_dupes = 1;
      for (; curdupe; curdupe = curdupe->dupe_next) n_dupes++;
      if (n_dupes > *max) *max = n_dupes;
    }
    files = files->next;
  }
  return groups;
}


/* Sanity check a match list for match registration
 * Return value is one end of the list that file1 is within
 * direction: 0 = return last item, 1 = return first item */
static file_t *match_list_verify(file_t *file1,
                const file_t * const restrict file2, int direction)
{
  file_t *scan;
  file_t *start;

  /* Go to the start of the list, watching for an infinite loop */
  scan = file1;
  while (scan->dupe_prev != NULL && scan->dupe_prev != file1) scan = scan->dupe_prev;
  if (scan->dupe_prev == file1) {
    /* Break circular reference and warn the user */
    fprintf(stderr, "warning: circular reference in registerpair(), report this as a bug\n");
    scan->dupe_prev->dupe_next = NULL;
    scan->dupe_prev = NULL;
  }
  start = scan;

  /* Check to see if file2 is in the current (file1) match list */
  while (scan->dupe_next != NULL && scan->dupe_next != file2) scan = scan->dupe_next;
  if (scan->dupe_next == file2) {
    /* Files are already in the same match list */
    LOUD(fprintf(stderr, "registerpair: files are already in the same match list\n");)
    return NULL;
  }

  /* Match list has no circular references and match isn't already registered */
  if (direction == 1) return start;
  else return scan;
}


/* Register a pair of matching files */
static void registerpair(file_t *file1, file_t *file2)
{
  file_t *list1, *list2;

  /* Pointer sanity checks */
  if (file1 == NULL || file2 == NULL) nullptr("registerpair()");
  LOUD(fprintf(stderr, "registerpair: (%p, %p) '%s', '%s'\n", file1, file2, file1->d_name, file2->d_name);)
  if (file1 == file2) return;

  /* For files with no match lists yet, link the pair immediately */
  if (file1->dupe_prev == NULL && file1->dupe_next == NULL && file2->dupe_prev == NULL && file2->dupe_next == NULL) {
  LOUD(fprintf(stderr, "registerpair: quick register %p(->%p,%p), %p(->%p,%p)\n", file1, file1->dupe_prev, file1->dupe_next, file2, file2->dupe_prev, file2->dupe_next);)
    file1->dupe_next = file2;
    file2->dupe_prev = file1;
  LOUD(fprintf(stderr, "registerpair: after register %p(->%p,%p), %p(->%p,%p)\n", file1, file1->dupe_prev, file1->dupe_next, file2, file2->dupe_prev, file2->dupe_next);)
    return;
  }

  /* Run sanity checks on both match lists, then link them together */
  list1 = match_list_verify(file1, file2, 0);
  if (list1 == NULL) return;
  list2 = match_list_verify(file2, file1, 1);
  if (list2 == NULL) return;
  LOUD(fprintf(stderr, "registerpair: normal register %p, %p for %p, %p\n", list1, list2, file1, file2);)
  list1->dupe_next = list2;
  list2->dupe_prev = list1;
  LOUD(fprintf(stderr, "registerpair: after register: file %p(->%p,%p), %p(->%p,%p), list %p(->%p,%p), %p(->%p,%p)\n",
                          file1, file1->dupe_prev, file1->dupe_next, file2, file2->dupe_prev, file2->dupe_next,
                          list1, list1->dupe_prev, list1->dupe_next, list2, list2->dupe_prev, list2->dupe_next);)

  return;
}


/* Normalize F_DUPE_HEAD and F_HAS_DUPES for all files */
void normalize_match_flags(file_t *file)
{
  file_t *scan;
  LOUD(fprintf(stderr, "normalize_match_flags(%p)\n", file);)

  while (file != NULL) {
    /* Skip files that have already been touched */
    if ISFLAG(file->flags, F_FINALIZED) goto skip_file;

    /* Files with no duplicates linked should be un-flagged */
    if (file->dupe_prev == NULL && file->dupe_next == NULL) {
      SETFLAG(file->flags, F_FINALIZED);
      CLEARFLAG(file->flags, (F_DUPE_HEAD | F_HAS_DUPES));
      goto skip_file;
    } else {
      /* Set flags properly for all duplicate lists */
      scan = file;
      while (scan->dupe_prev != NULL) scan = scan->dupe_prev;  /* rewind */
      SETFLAG(scan->flags, F_FINALIZED | F_DUPE_HEAD | F_HAS_DUPES);
      while (scan->dupe_next != NULL) {
        scan = scan->dupe_next;
        CLEARFLAG(scan->flags, F_DUPE_HEAD);
        SETFLAG(scan->flags, F_FINALIZED | F_HAS_DUPES);
      }
    }

skip_file:
    file = file->next;
  }
  return;
}


static inline void help_text(void)
{
  printf("Usage: jdupes [options] FILES and/or DIRECTORIES...\n\n");

  printf("Duplicate file sets will be printed by default unless a different action\n");
  printf("option is specified (delete, summarize, link, dedupe, etc.)\n");
#ifdef LOUD
  printf(" -@ --loud        \toutput annoying low-level debug info while running\n");
#endif
  printf(" -0 --printnull   \toutput nulls instead of CR/LF (like 'find -print0')\n");
  printf(" -1 --one-file-system \tdo not match files on different filesystems/devices\n");
  printf(" -A --nohidden    \texclude hidden files from consideration\n");
#ifdef ENABLE_DEDUPE
  printf(" -B --dedupe      \tsend matches to filesystem for block-level deduplication\n");
#endif
  printf(" -C --chunksize=# \toverride I/O chunk size (min %d, max %d)\n", MIN_CHUNK_SIZE, MAX_CHUNK_SIZE);
  printf(" -d --delete      \tprompt user for files to preserve and delete all\n");
  printf("                  \tothers; important: under particular circumstances,\n");
  printf("                  \tdata may be lost when using this option together\n");
  printf("                  \twith -s or --symlinks, or when specifying a\n");
  printf("                  \tparticular directory more than once; refer to the\n");
  printf("                  \tdocumentation for additional information\n");
#ifdef DEBUG
  printf(" -D --debug       \toutput debug statistics after completion\n");
#endif
  printf(" -f --omitfirst   \tomit the first file in each set of matches\n");
  printf(" -h --help        \tdisplay this help message\n");
#ifndef NO_HARDLINKS
  printf(" -H --hardlinks   \ttreat any linked files as duplicate files. Normally\n");
  printf("                  \tlinked files are treated as non-duplicates for safety\n");
#endif
  printf(" -i --reverse     \treverse (invert) the match sort order\n");
#ifndef NO_USER_ORDER
  printf(" -I --isolate     \tfiles in the same specified directory won't match\n");
#endif
  printf(" -j --json        \tproduce JSON (machine-readable) output\n");
  printf(" -K --skiphash    \tskip full file hashing (may be faster; 100%% safe)\n");
#ifndef NO_SYMLINKS
  printf(" -l --linksoft    \tmake relative symlinks for duplicates w/o prompting\n");
#endif
#ifndef NO_HARDLINKS
  printf(" -L --linkhard    \thard link all duplicate files without prompting\n");
 #ifdef ON_WINDOWS
  printf("                  \tWindows allows a maximum of 1023 hard links per file\n");
 #endif /* ON_WINDOWS */
#endif /* NO_HARDLINKS */
  printf(" -m --summarize   \tsummarize dupe information\n");
  printf(" -M --printwithsummary\twill print matches and --summarize at the end\n");
  printf(" -N --noprompt    \ttogether with --delete, preserve the first file in\n");
  printf("                  \teach set of duplicates and delete the rest without\n");
  printf("                  \tprompting the user\n");
  printf(" -o --order=BY    \tselect sort order for output, linking and deleting; by\n");
#ifndef NO_USER_ORDER
  printf(" -O --paramorder  \tParameter order is more important than selected -O sort\n");
  printf("                  \tmtime (BY=time) or filename (BY=name, the default)\n");
#endif
#ifndef NO_PERMS
  printf(" -p --permissions \tdon't consider files with different owner/group or\n");
  printf("                  \tpermission bits as duplicates\n");
#endif
  printf(" -P --print=type  \tprint extra info (partial, early, fullhash)\n");
  printf(" -q --quiet       \thide progress indicator\n");
  printf(" -Q --quick       \tskip byte-for-byte confirmation for quick matching\n");
  printf("                  \tWARNING: -Q can result in data loss! Be very careful!\n");
  printf(" -r --recurse     \tfor every directory, process its subdirectories too\n");
  printf(" -R --recurse:    \tfor each directory given after this option follow\n");
  printf("                  \tsubdirectories encountered within (note the ':' at\n");
  printf("                  \tthe end of the option, manpage for more details)\n");
#ifndef NO_SYMLINKS
  printf(" -s --symlinks    \tfollow symlinks\n");
#endif
  printf(" -S --size        \tshow size of duplicate files\n");
  printf(" -t --nochangecheck\tdisable security check for file changes (aka TOCTTOU)\n");
  printf(" -T --partial-only \tmatch based on partial hashes only. WARNING:\n");
  printf("                  \tEXTREMELY DANGEROUS paired with destructive actions!\n");
  printf("                  \t-T must be specified twice to work. Read the manual!\n");
  printf(" -v --version     \tdisplay jdupes version and license information\n");
  printf(" -x --xsize=SIZE  \texclude files of size < SIZE bytes from consideration\n");
  printf("    --xsize=+SIZE \t'+' specified before SIZE, exclude size > SIZE\n");
  printf(" -X --extfilter=spec:x\tfilter files based on specified criteria\n");
  printf("                  \tspecs: size+-=\n");
  printf("                  \tFilters are cumulative: -X spec:ab -X spec:cd\n");
  printf(" -z --zeromatch   \tconsider zero-length files to be duplicates\n");
  printf(" -Z --softabort   \tIf the user aborts (i.e. CTRL-C) act on matches so far\n");
#ifndef ON_WINDOWS
  printf("                  \tYou can send SIGUSR1 to the program to toggle this\n");
#endif
  printf("\nFor sizes, K/M/G/T/P/E[B|iB] suffixes can be used (case-insensitive)\n");
#ifdef OMIT_GETOPT_LONG
  printf("Note: Long options are not supported in this build.\n\n");
#endif
}


#ifdef UNICODE
int wmain(int argc, wchar_t **wargv)
#else
int main(int argc, char **argv)
#endif
{
  static file_t *curfile;
  static char **oldargv;
  static char *xs;
  static int firstrecurse;
  static int opt;
  static int pm = 1;
  static int partialonly_spec = 0;
  static ordertype_t ordertype = ORDER_NAME;
  static long manual_chunk_size = 0;
#ifndef ON_WINDOWS
  static struct proc_cacheinfo pci;
#endif

#ifndef OMIT_GETOPT_LONG
  static const struct option long_options[] =
  {
    { "loud", 0, 0, '@' },
    { "printnull", 0, 0, '0' },
    { "one-file-system", 0, 0, '1' },
    { "nohidden", 0, 0, 'A' },
    { "dedupe", 0, 0, 'B' },
    { "chunksize", 1, 0, 'C' },
    { "delete", 0, 0, 'd' },
    { "debug", 0, 0, 'D' },
    { "omitfirst", 0, 0, 'f' },
    { "help", 0, 0, 'h' },
    { "hardlinks", 0, 0, 'H' },
    { "reverse", 0, 0, 'i' },
    { "isolate", 0, 0, 'I' },
    { "json", 0, 0, 'j' },
    { "skiphash", 0, 0, 'K' },
    { "linksoft", 0, 0, 'l' },
    { "linkhard", 0, 0, 'L' },
    { "summarize", 0, 0, 'm'},
    { "printwithsummary", 0, 0, 'M'},
    { "noempty", 0, 0, 'n' },
    { "noprompt", 0, 0, 'N' },
    { "order", 1, 0, 'o' },
    { "paramorder", 0, 0, 'O' },
    { "permissions", 0, 0, 'p' },
    { "print", 0, 0, 'P' },
    { "quiet", 0, 0, 'q' },
    { "quick", 0, 0, 'Q' },
    { "recurse", 0, 0, 'r' },
    { "recursive", 0, 0, 'r' },
    { "recurse:", 0, 0, 'R' },
    { "recursive:", 0, 0, 'R' },
    { "symlinks", 0, 0, 's' },
    { "size", 0, 0, 'S' },
    { "nochangecheck", 0, 0, 't' },
    { "partial-only", 0, 0, 'T' },
    { "version", 0, 0, 'v' },
    { "xsize", 1, 0, 'x' },
    { "exclude", 1, 0, 'X' },
    { "extfilter", 1, 0, 'X' },
    { "zeromatch", 0, 0, 'z' },
    { "softabort", 0, 0, 'Z' },
    { NULL, 0, 0, 0 }
  };
#define GETOPT getopt_long
#else
#define GETOPT getopt
#endif

/* Windows buffers our stderr output; don't let it do that */
#ifdef ON_WINDOWS
  if (setvbuf(stderr, NULL, _IONBF, 0) != 0)
    fprintf(stderr, "warning: setvbuf() failed\n");
#endif

#ifdef UNICODE
  /* Create a UTF-8 **argv from the wide version */
  static char **argv;
  argv = (char **)string_malloc(sizeof(char *) * argc);
  if (!argv) oom("main() unicode argv");
  widearg_to_argv(argc, wargv, argv);
  /* fix up __argv so getopt etc. don't crash */
  __argv = argv;
  /* Only use UTF-16 for terminal output, else use UTF-8 */
  if (!_isatty(_fileno(stdout))) out_mode = _O_BINARY;
  else out_mode = _O_U16TEXT;
  if (!_isatty(_fileno(stderr))) err_mode = _O_BINARY;
  else err_mode = _O_U16TEXT;
#endif /* UNICODE */

#ifndef ON_WINDOWS
  /* Auto-tune chunk size to be half of L1 data cache if possible */
  get_proc_cacheinfo(&pci);
  if (pci.l1 != 0) auto_chunk_size = (pci.l1 / 2);
  else if (pci.l1d != 0) auto_chunk_size = (pci.l1d / 2);
  /* Must be at least 4096 (4 KiB) and cannot exceed CHUNK_SIZE */
  if (auto_chunk_size < MIN_CHUNK_SIZE || auto_chunk_size > MAX_CHUNK_SIZE) auto_chunk_size = CHUNK_SIZE;
  /* Force to a multiple of 4096 if it isn't already */
  if ((auto_chunk_size & 0x00000fffUL) != 0)
    auto_chunk_size = (auto_chunk_size + 0x00000fffUL) & 0x000ff000;
#endif /* ON_WINDOWS */

  /* Is stderr a terminal? If not, we won't write progress to it */
#ifdef ON_WINDOWS
  if (!_isatty(_fileno(stderr))) SETFLAG(flags, F_HIDEPROGRESS);
#else
  if (!isatty(fileno(stderr))) SETFLAG(flags, F_HIDEPROGRESS);
#endif

  program_name = argv[0];

  oldargv = cloneargs(argc, argv);

  while ((opt = GETOPT(argc, argv,
  "@01ABC:dDfhHiIjKlLmMnNOpP:qQrRsStTvVzZo:x:X:"
#ifndef OMIT_GETOPT_LONG
          , long_options, NULL
#endif
         )) != EOF) {
    if ((uintptr_t)optarg == 0x20) goto error_optarg;
    switch (opt) {
    case '0':
      SETFLAG(flags, F_PRINTNULL);
      break;
    case '1':
      SETFLAG(flags, F_ONEFS);
      break;
    case 'A':
      SETFLAG(flags, F_EXCLUDEHIDDEN);
      break;
    case 'C':
      manual_chunk_size = strtol(optarg, NULL, 10) & 0x0ffff000L;  /* Align to 4K sizes */
      if (manual_chunk_size < MIN_CHUNK_SIZE || manual_chunk_size > MAX_CHUNK_SIZE) {
        fprintf(stderr, "warning: invalid manual chunk size (must be %d-%d); using defaults\n", MIN_CHUNK_SIZE, MAX_CHUNK_SIZE);
        LOUD(fprintf(stderr, "Manual chunk size (failed) was apparently '%s' => %ld\n", optarg, manual_chunk_size));
        manual_chunk_size = 0;
      } else auto_chunk_size = (size_t)manual_chunk_size;
      LOUD(fprintf(stderr, "Manual chunk size is %ld\n", manual_chunk_size));
      break;
    case 'd':
      SETFLAG(flags, F_DELETEFILES);
      break;
    case 'D':
#ifdef DEBUG
      SETFLAG(flags, F_DEBUG);
#endif
      break;
    case 'f':
      SETFLAG(flags, F_OMITFIRST);
      break;
    case 'h':
      help_text();
      string_malloc_destroy();
      exit(EXIT_FAILURE);
#ifndef NO_HARDLINKS
    case 'H':
      SETFLAG(flags, F_CONSIDERHARDLINKS);
      break;
    case 'L':
      SETFLAG(flags, F_HARDLINKFILES);
      break;
#endif
    case 'i':
      SETFLAG(flags, F_REVERSESORT);
      break;
#ifndef NO_USER_ORDER
    case 'I':
      SETFLAG(flags, F_ISOLATE);
      break;
    case 'O':
      SETFLAG(flags, F_USEPARAMORDER);
      break;
#else
    case 'I':
    case 'O':
      fprintf(stderr, "warning: -I and -O are disabled and ignored in this build\n");
      break;
#endif
    case 'j':
      SETFLAG(flags, F_PRINTJSON);
      break;
    case 'K':
      SETFLAG(flags, F_SKIPHASH);
      break;
    case 'm':
      SETFLAG(flags, F_SUMMARIZEMATCHES);
      break;
    case 'M':
      SETFLAG(flags, F_SUMMARIZEMATCHES);
      SETFLAG(flags, F_PRINTMATCHES);
      break;
    case 'n':
      //fprintf(stderr, "note: -n/--noempty is the default behavior now and is deprecated.\n");
      break;
    case 'N':
      SETFLAG(flags, F_NOPROMPT);
      break;
    case 'p':
      SETFLAG(flags, F_PERMISSIONS);
      break;
    case 'P':
      if (strcmp(optarg, "partial") == 0) SETFLAG(p_flags, P_PARTIAL);
      else if (strcmp(optarg, "early") == 0) SETFLAG(p_flags, P_EARLYMATCH);
      else if (strcmp(optarg, "fullhash") == 0) SETFLAG(p_flags, P_FULLHASH);
      else {
        fprintf(stderr, "Option '%s' is not valid for -P\n", optarg);
        exit(EXIT_FAILURE);
      }
      break;
    case 'q':
      SETFLAG(flags, F_HIDEPROGRESS);
      break;
    case 'Q':
      SETFLAG(flags, F_QUICKCOMPARE);
      break;
    case 'r':
      SETFLAG(flags, F_RECURSE);
      break;
    case 'R':
      SETFLAG(flags, F_RECURSEAFTER);
      break;
    case 't':
      SETFLAG(flags, F_NOCHANGECHECK);
      break;
    case 'T':
      if (partialonly_spec == 0)
        partialonly_spec = 1;
      else {
        partialonly_spec = 2;
        SETFLAG(flags, F_PARTIALONLY);
      }
      break;
#ifndef NO_SYMLINKS
    case 'l':
      SETFLAG(flags, F_MAKESYMLINKS);
      break;
    case 's':
      SETFLAG(flags, F_FOLLOWLINKS);
      break;
#endif
    case 'S':
      SETFLAG(flags, F_SHOWSIZE);
      break;
    case 'z':
      SETFLAG(flags, F_INCLUDEEMPTY);
      break;
    case 'Z':
      SETFLAG(flags, F_SOFTABORT);
      break;
    case 'x':
      fprintf(stderr, "-x/--xsize is deprecated; use -X size[+-=]:size[suffix] instead\n");
      xs = string_malloc(8 + strlen(optarg));
      if (xs == NULL) oom("xsize temp string");
      strcpy(xs, "size");
      if (*optarg == '+') {
        strcat(xs, "+:");
        optarg++;
      } else {
        strcat(xs, "-=:");
      }
      strcat(xs, optarg);
      add_extfilter(xs);
      string_free(xs);
      break;
    case 'X':
      add_extfilter(optarg);
      break;
    case '@':
#ifdef LOUD_DEBUG
      SETFLAG(flags, F_DEBUG | F_LOUD | F_HIDEPROGRESS);
#endif
      break;
    case 'v':
    case 'V':
      printf("jdupes %s (%s) ", VER, VERDATE);

      /* Indicate bitness information */
      if (sizeof(uintptr_t) == 8) {
        if (sizeof(long) == 4) printf("64-bit i32\n");
        else if (sizeof(long) == 8) printf("64-bit\n");
      } else if (sizeof(uintptr_t) == 4) {
        if (sizeof(long) == 4) printf("32-bit\n");
        else if (sizeof(long) == 8) printf("32-bit i64\n");
      } else printf("%u-bit i%u\n", (unsigned int)(sizeof(uintptr_t) * 8),
          (unsigned int)(sizeof(long) * 8));

#ifdef BUILD_DATE
#include "build_date.h"
      printf("Built on %s\n", BUILT_ON_DATE);
#endif

      printf("Compile-time extensions:");
      if (*extensions != NULL) {
        int c = 0;
        while (extensions[c] != NULL) {
          printf(" %s", extensions[c]);
          c++;
        }
      } else printf(" none");
      printf("\nCopyright (C) 2015-2020 by Jody Bruchon and contributors\n");
      printf("Forked from fdupes 1.51, (C) 1999-2014 Adrian Lopez and contributors\n");
      printf("\nPermission is hereby granted, free of charge, to any person\n");
      printf("obtaining a copy of this software and associated documentation files\n");
      printf("(the \"Software\"), to deal in the Software without restriction,\n");
      printf("including without limitation the rights to use, copy, modify, merge,\n");
      printf("publish, distribute, sublicense, and/or sell copies of the Software,\n");
      printf("and to permit persons to whom the Software is furnished to do so,\n");
      printf("subject to the following conditions:\n\n");
      printf("The above copyright notice and this permission notice shall be\n");
      printf("included in all copies or substantial portions of the Software.\n\n");
      printf("THE SOFTWARE IS PROVIDED \"AS IS\", WITHOUT WARRANTY OF ANY KIND, EXPRESS\n");
      printf("OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF\n");
      printf("MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT.\n");
      printf("IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY\n");
      printf("CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT,\n");
      printf("TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION WITH THE\n");
      printf("SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.\n");
      printf("\nIf you find this software useful, please consider financially\n");
      printf("supporting its continued developemnt by visiting this URL:\n");
      printf("      https://www.subscribestar.com/JodyBruchon\n");
      exit(EXIT_SUCCESS);
    case 'o':
      if (!strncasecmp("name", optarg, 5)) {
        ordertype = ORDER_NAME;
      } else if (!strncasecmp("time", optarg, 5)) {
        ordertype = ORDER_TIME;
      } else {
        fprintf(stderr, "invalid value for --order: '%s'\n", optarg);
        exit(EXIT_FAILURE);
      }
      break;
    case 'B':
#ifdef ENABLE_DEDUPE
      SETFLAG(flags, F_DEDUPEFILES);
      /* btrfs will do the byte-for-byte check itself */
      SETFLAG(flags, F_QUICKCOMPARE);
      /* It is completely useless to dedupe zero-length extents */
      CLEARFLAG(flags, F_INCLUDEEMPTY);
#else
      fprintf(stderr, "This program was built without btrfs support\n");
      exit(EXIT_FAILURE);
#endif
      break;

    default:
      if (opt != '?') fprintf(stderr, "Option '-%c' is not supported in this build.\n", opt);
      fprintf(stderr, "Try `jdupes --help' for more information.\n");
      string_malloc_destroy();
      exit(EXIT_FAILURE);
    }
  }

  if (optind >= argc) {
    fprintf(stderr, "no files or directories specified (use -h option for help)\n");
    string_malloc_destroy();
    exit(EXIT_FAILURE);
  }

  if (partialonly_spec == 1) {
    fprintf(stderr, "--partial-only specified only once (it's VERY DANGEROUS, read the manual!)\n");
    string_malloc_destroy();
    exit(EXIT_FAILURE);
  }

  if (ISFLAG(flags, F_PARTIALONLY) && ISFLAG(flags, F_QUICKCOMPARE)) {
    fprintf(stderr, "--partial-only overrides --quick and is even more dangerous (read the manual!)\n");
    string_malloc_destroy();
    exit(EXIT_FAILURE);
  }

  if (ISFLAG(flags, F_RECURSE) && ISFLAG(flags, F_RECURSEAFTER)) {
    fprintf(stderr, "options --recurse and --recurse: are not compatible\n");
    string_malloc_destroy();
    exit(EXIT_FAILURE);
  }

  if (ISFLAG(flags, F_SUMMARIZEMATCHES) && ISFLAG(flags, F_DELETEFILES)) {
    fprintf(stderr, "options --summarize and --delete are not compatible\n");
    string_malloc_destroy();
    exit(EXIT_FAILURE);
  }

#ifdef ENABLE_DEDUPE
  if (ISFLAG(flags, F_CONSIDERHARDLINKS) && ISFLAG(flags, F_DEDUPEFILES))
    fprintf(stderr, "warning: option --dedupe overrides the behavior of --hardlinks\n");
#endif

  /* If pm == 0, call printmatches() */
  pm = !!ISFLAG(flags, F_SUMMARIZEMATCHES) +
      !!ISFLAG(flags, F_DELETEFILES) +
      !!ISFLAG(flags, F_HARDLINKFILES) +
      !!ISFLAG(flags, F_MAKESYMLINKS) +
      !!ISFLAG(flags, F_PRINTJSON) +
      !!ISFLAG(flags, F_DEDUPEFILES);

  if (pm > 1) {
      fprintf(stderr, "Only one of --summarize, --printwithsummary, --delete, --linkhard,\n--linksoft, --json, or --dedupe may be used\n");
      string_malloc_destroy();
      exit(EXIT_FAILURE);
  }
  if (pm == 0) SETFLAG(flags, F_PRINTMATCHES);

  if (ISFLAG(flags, F_RECURSEAFTER)) {
    firstrecurse = nonoptafter("--recurse:", argc, oldargv, argv);

    if (firstrecurse == argc)
      firstrecurse = nonoptafter("-R", argc, oldargv, argv);

    if (firstrecurse == argc) {
      fprintf(stderr, "-R option must be isolated from other options\n");
      string_malloc_destroy();
      exit(EXIT_FAILURE);
    }

    /* F_RECURSE is not set for directories before --recurse: */
    for (int x = optind; x < firstrecurse; x++) {
      slash_convert(argv[x]);
      grokdir(argv[x], 0);
      user_item_count++;
    }

    /* Set F_RECURSE for directories after --recurse: */
    SETFLAG(flags, F_RECURSE);

    for (int x = firstrecurse; x < argc; x++) {
      slash_convert(argv[x]);
      grokdir(argv[x], 1);
      user_item_count++;
    }
  } else {
    for (int x = optind; x < argc; x++) {
      slash_convert(argv[x]);
      grokdir(argv[x], ISFLAG(flags, F_RECURSE));
      user_item_count++;
    }
  }

  /* We don't need the double traversal check tree anymore */
  travdone_free(travdone_head);

  if (ISFLAG(flags, F_REVERSESORT)) sort_direction = -1;
  if (!ISFLAG(flags, F_HIDEPROGRESS)) fprintf(stderr, "\n");
  if (filehead == NULL || filehead->next == NULL) {
    fwprint(stderr, "No duplicates found.", 1);
    string_malloc_destroy();
    exit(EXIT_SUCCESS);
  }

  progress = 0;

  /* Catch CTRL-C */
  signal(SIGINT, sighandler);
#ifndef ON_WINDOWS
  /* Catch SIGUSR1 and use it to enable -Z */
  signal(SIGUSR1, sigusr1);
#endif

  curfile = filehead;

  while (curfile) {
    file_t *scanfile;
    FILE *file1;
    FILE *file2;
    int match;

    if (interrupt) {
      fprintf(stderr, "\nStopping file scan due to user abort\n");
      if (!ISFLAG(flags, F_SOFTABORT)) exit(EXIT_FAILURE);
      interrupt = 0;  /* reset interrupt for re-use */
      goto skip_file_scan;
    }

    LOUD(fprintf(stderr, "\nMAIN: current file: %s\n", curfile->d_name));

    scanfile = curfile->next;

    while (scanfile && scanfile != curfile) {
//fprintf(stderr, "cf %p->%p, sf %p->%p\n", curfile, curfile->next, scanfile, scanfile->next);
      LOUD(fprintf(stderr, "MAIN: scanfile: %s = %s\n", curfile->d_name, scanfile->d_name));
      LOUD(fprintf(stderr, "MAIN: scanfile: cur %p->%p, scan %p->%p\n", curfile, curfile->next, scanfile, scanfile->next));
      match = checkmatch(curfile, scanfile);

      LOUD(fprintf(stderr, "MAIN: match = %d\n", match));
      /* Byte-for-byte check that a matched pair are actually matched */
      if (match == 1) {
        LOUD(fprintf(stderr, "MAIN: entering match confirmation\n"));
        /* Quick or partial-only compare will never run confirmmatch()
         * Also skip match confirmation for hard-linked files
         * (This set of comparisons is ugly, but quite efficient) */
        if (ISFLAG(flags, F_QUICKCOMPARE) || ISFLAG(flags, F_PARTIALONLY) ||
             (ISFLAG(flags, F_CONSIDERHARDLINKS) &&
             (curfile->inode == scanfile->inode) &&
             (curfile->device == scanfile->device))
           ) {
          LOUD(fprintf(stderr, "MAIN: notice: hard linked, quick, or partial-only match (-H/-Q/-T)\n"));
          registerpair(curfile, scanfile);
          dupecount++;
          scanfile = scanfile->next;
          continue;
        }

#ifdef UNICODE
        if (!M2W(curfile->d_name, wstr)) file1 = NULL;
        else file1 = _wfopen(wstr, FILE_MODE_RO);
#else
        file1 = fopen(curfile->d_name, FILE_MODE_RO);
#endif
        if (!file1) {
          LOUD(fprintf(stderr, "MAIN: warning: file1 fopen() failed ('%s')\n", curfile->d_name));
          curfile = curfile->next;
          break;
        }

#ifdef UNICODE
        if (!M2W(scanfile->d_name, wstr)) file2 = NULL;
        else file2 = _wfopen(wstr, FILE_MODE_RO);
#else
        file2 = fopen(scanfile->d_name, FILE_MODE_RO);
#endif
        if (!file2) {
          fclose(file1);
          LOUD(fprintf(stderr, "MAIN: warning: file2 fopen() failed ('%s')\n", scanfile->d_name));
          scanfile = scanfile->next;
          continue;
        }

        if (confirmmatch(file1, file2, curfile->size)) {
          LOUD(fprintf(stderr, "MAIN: registering matched file pair\n"));
          registerpair(curfile, scanfile);
          dupecount++;
        } DBG(else hash_fail++;)

        fclose(file1);
        fclose(file2);
      }

      LOUD(fprintf(stderr, "MAIN: scanfile->next\n"));
      scanfile = scanfile->next;
    }   /* scanfile */


    if (!ISFLAG(flags, F_HIDEPROGRESS)) update_progress(NULL, -1);
    progress++;
    curfile = curfile->next;
    LOUD(fprintf(stderr, "MAIN: curfile->next\n"));
  }   /* curfile */

  if (!ISFLAG(flags, F_HIDEPROGRESS)) fprintf(stderr, "\r%60s\r", " ");

skip_file_scan:
  /* Stop catching CTRL+C */
  signal(SIGINT, SIG_DFL);
  normalize_match_flags(filehead);
  if (ISFLAG(flags, F_DELETEFILES)) {
    if (ISFLAG(flags, F_NOPROMPT)) deletefiles(filehead, 0, 0);
    else deletefiles(filehead, 1, stdin);
  }
#ifndef NO_SYMLINKS
  if (ISFLAG(flags, F_MAKESYMLINKS)) linkfiles(filehead, 0);
#endif
#ifndef NO_HARDLINKS
  if (ISFLAG(flags, F_HARDLINKFILES)) linkfiles(filehead, 1);
#endif /* NO_HARDLINKS */
#ifdef ENABLE_DEDUPE
  if (ISFLAG(flags, F_DEDUPEFILES)) dedupefiles(filehead);
#endif /* ENABLE_DEDUPE */
  if (ISFLAG(flags, F_PRINTMATCHES)) printmatches(filehead);
  if (ISFLAG(flags, F_PRINTJSON)) printjson(filehead, argc, argv);
  if (ISFLAG(flags, F_SUMMARIZEMATCHES)) {
    if (ISFLAG(flags, F_PRINTMATCHES)) printf("\n\n");
    summarizematches(filehead);
  }

  string_malloc_destroy();

#ifdef DEBUG
  if (ISFLAG(flags, F_DEBUG)) {
    fprintf(stderr, "\n%d partial (+%d small) -> %d full hash -> %d full (%d partial elim) (%d hash%u fail)\n",
        partial_hash, small_file, full_hash, partial_to_full,
        partial_elim, hash_fail, (unsigned int)sizeof(jdupes_hash_t)*8);
    fprintf(stderr, "%" PRIuMAX " total files, %" PRIuMAX " comparisons\n",
        filecount, comparisons);
    fprintf(stderr, "SMA: allocs %" PRIuMAX ", free %" PRIuMAX " (merge %" PRIuMAX ", repl %" PRIuMAX "), fail %" PRIuMAX ", reuse %" PRIuMAX ", scan %" PRIuMAX ", tails %" PRIuMAX "\n",
        sma_allocs, sma_free_good, sma_free_merged, sma_free_replaced,
        sma_free_ignored, sma_free_reclaimed,
        sma_free_scanned, sma_free_tails);
    if (manual_chunk_size > 0) fprintf(stderr, "I/O chunk size: %ld KiB (manually set)\n", manual_chunk_size >> 10);
    else {
#ifndef ON_WINDOWS
      fprintf(stderr, "I/O chunk size: %" PRIuMAX " KiB (%s)\n", (uintmax_t)(auto_chunk_size >> 10), (pci.l1 + pci.l1d) != 0 ? "dynamically sized" : "default size");
#else
      fprintf(stderr, "I/O chunk size: %" PRIuMAX " KiB (default size)\n", (uintmax_t)(auto_chunk_size >> 10));
#endif
    }
#ifdef ON_WINDOWS
 #ifndef NO_HARDLINKS
    if (ISFLAG(flags, F_HARDLINKFILES))
      fprintf(stderr, "Exclusions based on Windows hard link limit: %u\n", hll_exclude);
 #endif
#endif
  }
#endif /* DEBUG */

  exit(EXIT_SUCCESS);

error_optarg:
  fprintf(stderr, "error: option '%c' requires an argument\n", opt);
  exit(EXIT_FAILURE);
}
