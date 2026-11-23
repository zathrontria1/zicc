#ifndef ZICC_PREPROCESS_H
#define ZICC_PREPROCESS_H
#include <stddef.h>
#include <stdio.h>

typedef struct EmbeddedRange {
    size_t begin, end;
    char *resource;
    struct EmbeddedRange *next;
} EmbeddedRange;

char *preprocess_with_embeds(const char *path, const char *include_dir, EmbeddedRange **ranges,
                             int binary64, FILE *dependencies);
char *preprocess(const char *path, const char *include_dir);
#endif
