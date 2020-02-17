/* Print matched file sets
 * This file is part of jdupes; see jdupes.c for license information */

#include <stdio.h>
#include <stdint.h>
#include <inttypes.h>
#include "jdupes.h"
#include "jody_win_unicode.h"
#include "act_printmatches.h"

extern void printmatches(file_t *files)
{
  file_t * restrict tmpfile;
  int printed = 0;
  int cr = 1;

  LOUD(fprintf(stderr, "act_printmatches: %p\n", files));

  if (ISFLAG(flags, F_PRINTNULL)) cr = 2;

  while (files != NULL) {
    if (ISFLAG(files->flags, F_DUPE_HEAD)) {
      printed = 1;
      if (!ISFLAG(flags, F_OMITFIRST)) {
        if (ISFLAG(flags, F_SHOWSIZE)) printf("%" PRIdMAX " byte%c each:\n", (intmax_t)files->size,
         (files->size != 1) ? 's' : ' ');
        fwprint(stdout, files->d_name, cr);
      }
      tmpfile = files->dupe_next;
      while (tmpfile != NULL) {
        fwprint(stdout, tmpfile->d_name, cr);
        tmpfile = tmpfile->dupe_next;
      }
      if (files->next != NULL) fwprint(stdout, "", cr);

    }

    files = files->next;
  }

  if (printed == 0) fwprint(stderr, "No duplicates found.", 1);

  return;
}
