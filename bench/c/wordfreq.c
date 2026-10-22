// Word frequencies: text built from a vocabulary, split into words, counted in a hash map, and
// the most frequent shown; strings, hashing and sorting. An open-addressing table of its own.
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
typedef struct { char* key; uint32_t len, count; uint64_t hash; } Slot;
static Slot* table; static size_t cap = 1024, size = 0;
static uint64_t fnv(const char* s, size_t n) { uint64_t h = 1469598103934665603ULL; for (size_t i = 0; i < n; i++) { h ^= (unsigned char)s[i]; h *= 1099511628211ULL; } return h; }
static void grow(void) {
  Slot* old = table; size_t oldCap = cap; cap *= 2; table = calloc(cap, sizeof(Slot));
  for (size_t i = 0; i < oldCap; i++) if (old[i].key) { size_t j = old[i].hash & (cap - 1); while (table[j].key) j = (j + 1) & (cap - 1); table[j] = old[i]; }
  free(old);
}
static void add(const char* s, size_t n) {
  if (size * 2 >= cap) grow();
  uint64_t h = fnv(s, n); size_t j = h & (cap - 1);
  while (table[j].key) { if (table[j].hash == h && table[j].len == n && memcmp(table[j].key, s, n) == 0) { table[j].count++; return; } j = (j + 1) & (cap - 1); }
  table[j].key = malloc(n); memcpy(table[j].key, s, n); table[j].len = n; table[j].count = 1; table[j].hash = h; size++;
}
static int cmp(const void* a, const void* b) {
  const Slot *x = a, *y = b;
  if (x->count != y->count) return x->count < y->count ? 1 : -1;
  size_t n = x->len < y->len ? x->len : y->len; int c = memcmp(x->key, y->key, n);
  return c ? c : (int)x->len - (int)y->len;
}
int main(int argc, char** argv) {
  unsigned n = argc > 1 ? atoi(argv[1]) : 1000;
  size_t tcap = 16, tlen = 0; char* text = malloc(tcap);
  uint64_t seed = 42;
  for (unsigned i = 0; i < n; i++) {
    seed = seed * 6364136223846793005ULL + 1442695040888963407ULL;
    char buf[24]; int k = snprintf(buf, sizeof buf, "%sw%llu", i ? " " : "", (unsigned long long)((seed >> 33) % 20000));
    if (tlen + k >= tcap) { while (tlen + k >= tcap) tcap *= 2; text = realloc(text, tcap); }
    memcpy(text + tlen, buf, k); tlen += k;
  }
  table = calloc(cap, sizeof(Slot));
  for (size_t i = 0; i < tlen;) { while (i < tlen && text[i] == ' ') i++; size_t s = i; while (i < tlen && text[i] != ' ') i++; if (i > s) add(text + s, i - s); }
  printf("%zu distinct words\n", size);
  Slot* all = malloc(size * sizeof(Slot)); size_t m = 0;
  for (size_t i = 0; i < cap; i++) if (table[i].key) all[m++] = table[i];
  qsort(all, m, sizeof(Slot), cmp);
  for (int i = 0; i < 10; i++) printf("%.*s %u\n", (int)all[i].len, all[i].key, all[i].count);
}
