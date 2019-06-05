/* jdupes action for printing comprehensive data as JSON to stdout
 * This file is part of jdupes; see jdupes.c for license information */

#ifndef ACT_PRINTJSON_H
#define ACT_PRINTJSON_H

#ifdef __cplusplus
extern "C" {
#endif

#include "jdupes.h"
extern void printjson(file_t * restrict files, const int argc, char ** const restrict argv);

#ifdef __cplusplus
}
#endif

#endif /* ACT_PRINTJSON_H */
