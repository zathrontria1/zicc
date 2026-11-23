#ifndef ZICC_RELAX_H
#define ZICC_RELAX_H
#include <stdio.h>
/* Layout and relax the assembly subset emitted by this backend */
int relax_assembly(FILE *out, const char *assembly, const char *unit, int enabled);
#endif
