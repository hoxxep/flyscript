// spectral-norm: the largest eigenvalue of an infinite matrix, by the power method; floating point
// loops over arrays.
#include <math.h>
#include <stdio.h>
#include <stdlib.h>
static double A(int i, int j) { return 1.0 / ((i + j) * (i + j + 1) / 2 + i + 1); }
static void mulAv(int n, const double* v, double* av) { for (int i = 0; i < n; i++) { double s = 0; for (int j = 0; j < n; j++) s += A(i, j) * v[j]; av[i] = s; } }
static void mulAtv(int n, const double* v, double* atv) { for (int i = 0; i < n; i++) { double s = 0; for (int j = 0; j < n; j++) s += A(j, i) * v[j]; atv[i] = s; } }
static void mulAtAv(int n, const double* v, double* out, double* tmp) { mulAv(n, v, tmp); mulAtv(n, tmp, out); }
int main(int argc, char** argv) {
  int n = argc > 1 ? atoi(argv[1]) : 100;
  double *u = malloc(n * sizeof(double)), *v = malloc(n * sizeof(double)), *tmp = malloc(n * sizeof(double));
  for (int i = 0; i < n; i++) u[i] = 1;
  for (int i = 0; i < 10; i++) { mulAtAv(n, u, v, tmp); mulAtAv(n, v, u, tmp); }
  double vBv = 0, vv = 0;
  for (int i = 0; i < n; i++) { vBv += u[i] * v[i]; vv += v[i] * v[i]; }
  printf("%.9f\n", sqrt(vBv / vv));
}
