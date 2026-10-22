// binary-trees, single-threaded: allocation and freeing of many small trees.
#include <stdio.h>
#include <stdlib.h>
typedef struct Node { struct Node *l, *r; } Node;
static Node* make(int d) { Node* n = malloc(sizeof(Node)); if (d > 0) { n->l = make(d - 1); n->r = make(d - 1); } else { n->l = n->r = NULL; } return n; }
static int check(Node* n) { return 1 + (n->l ? check(n->l) + check(n->r) : 0); }
static void drop(Node* n) { if (n->l) { drop(n->l); drop(n->r); } free(n); }
int main(int argc, char** argv) {
  int n = argc > 1 ? atoi(argv[1]) : 10;
  int max = n < 6 ? 6 : n;
  Node* s = make(max + 1); printf("stretch tree of depth %d\t check: %d\n", max + 1, check(s)); drop(s);
  Node* longLived = make(max);
  for (int d = 4; d <= max; d += 2) {
    int iters = 1 << (max - d + 4), sum = 0;
    for (int i = 0; i < iters; i++) { Node* t = make(d); sum += check(t); drop(t); }
    printf("%d\t trees of depth %d\t check: %d\n", iters, d, sum);
  }
  printf("long lived tree of depth %d\t check: %d\n", max, check(longLived)); drop(longLived);
}
