/* Shared lexical facts; each consumer owns its control-flow and safety proof */
static int assembly_decode(const char *text, size_t length, int *m8, int *x8, const char **op)
{
    *op = NULL;
    if (!strncmp(text, ".a8\n", 4))
        *m8 = 1;
    else if (!strncmp(text, ".a16\n", 5))
        *m8 = 0;
    else if (!strncmp(text, ".i8\n", 4))
        *x8 = 1;
    else if (!strncmp(text, ".i16\n", 5))
        *x8 = 0;

    if (length > 4 && !strncmp(text, "    ", 4) && text[4] != ' ' && text[4] != ';')
        *op = text + 4;
    else if (length && *text != ';' && *text != '.' && *text != ' ' &&
             (text[length - 1] == ':' || (length > 4 && !strncmp(text + length - 4, " = *", 4))))
        return 1;

    return 0;
}

typedef struct {
    const char *name;
    size_t length;
    unsigned line;
} AssemblyLabel;

typedef struct {
    AssemblyLabel *named;
    size_t capacity;
    unsigned *anonymous, count;
} AssemblyLabels;

static AssemblyLabel *assembly_label_slot(const AssemblyLabels *labels, const char *name,
                                          size_t length)
{
    uint32_t hash = 2166136261u;
    size_t i;

    for (i = 0; i < length; ++i) {
        hash = (hash ^ (unsigned char)name[i]) * 16777619u;
    }

    i = hash & (labels->capacity - 1);

    while (labels->named[i].name &&
           (labels->named[i].length != length || memcmp(labels->named[i].name, name, length))) {
        i = (i + 1) & (labels->capacity - 1);
    }

    return &labels->named[i];
}

static void assembly_labels_init(AssemblyLabels *labels, unsigned count)
{
    labels->capacity = 1;
    labels->count = 0;

    while (labels->capacity < 2 * (size_t)count) {
        labels->capacity *= 2;
    }

    labels->named = allocate(labels->capacity * sizeof *labels->named);
    labels->anonymous = allocate((count + 1) * sizeof *labels->anonymous);
}

static void assembly_label_add(AssemblyLabels *labels, const char *text, size_t length,
                               unsigned line)
{
    AssemblyLabel *entry;

    if (length == 1 && text[0] == ':') {
        labels->anonymous[labels->count++] = line;
        return;
    }

    length -= text[length - 1] == ':' ? 1 : 4;
    entry = assembly_label_slot(labels, text, length);

    /* Preserve the first definition, including mixed ':' and ' = *' spellings */
    if (!entry->name)
        *entry = (AssemblyLabel){text, length, line};
}

static int assembly_label_target(const AssemblyLabels *labels, unsigned from, const char *name,
                                 size_t length)
{
    unsigned i, steps;

    if (length > 9 && !strncmp(name, ".loword(", 8) && name[length - 1] == ')') {
        name += 8;
        length -= 9;
    }

    if (length > 1 && name[0] == ':' && (name[1] == '+' || name[1] == '-')) {
        steps = (unsigned)(length - 1);

        for (i = 1; i < length; ++i) {
            if (name[i] != name[1])
                return -1;
        }

        if (name[1] == '+') {
            for (i = 0; i < labels->count; ++i) {
                if (labels->anonymous[i] > from && !--steps)
                    return (int)labels->anonymous[i];
            }
        } else {
            for (i = labels->count; i-- > 0;) {
                if (labels->anonymous[i] < from && !--steps)
                    return (int)labels->anonymous[i];
            }
        }

        return -1;
    }

    {
        const AssemblyLabel *entry = assembly_label_slot(labels, name, length);

        return entry->name ? (int)entry->line : -1;
    }
}

static void assembly_labels_free(AssemblyLabels *labels)
{
    free(labels->named);
    free(labels->anonymous);
}

/* Fixed bytes pushed (positive) or pulled (negative); other effects stay local */
static int assembly_stack_bytes(const char *op, int m8, int x8)
{
    if (op_is(op, "pha"))
        return m8 ? 1 : 2;
    if (op_is(op, "pla"))
        return m8 ? -1 : -2;
    if (op_is(op, "phx") || op_is(op, "phy"))
        return x8 ? 1 : 2;
    if (op_is(op, "plx") || op_is(op, "ply"))
        return x8 ? -1 : -2;
    if (op_is(op, "php") || op_is(op, "phb") || op_is(op, "phk"))
        return 1;
    if (op_is(op, "plp") || op_is(op, "plb"))
        return -1;
    if (op_is(op, "phd") || op_is(op, "pea") || op_is(op, "pei") || op_is(op, "per"))
        return 2;
    if (op_is(op, "pld"))
        return -2;

    return 0;
}
