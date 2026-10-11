// Kourovka 21.130 (Sun): every subset A (|A|=n>2) of a finite abelian group of odd order
// has a cyclic order with all adjacent sums a_i+a_{i+1} (i mod n) distinct.
// Exhaustive over subsets containing 0 (translation normalisation), DFS with node limit.
// usage: sumcycle m1 [m2 ...]  (group = Z_m1 x Z_m2 ...), env KMIN KMAX LIMIT
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
typedef unsigned __int128 u128;
static int N, add[128][128];
static long long LIMIT = 2000000;
static int RESTARTS = 300;
static int A[128], K;
static long long nodes;
static int dfs(int pos, int last, u128 used, u128 sums) {
  if (++nodes > LIMIT) return -1;
  if (pos == K) {
    int s = add[last][A[0]];
    return !((sums >> s) & 1);
  }
  for (int i = 1; i < K; i++) {
    if ((used >> i) & 1) continue;
    int s = add[last][A[i]];
    if ((sums >> s) & 1) continue;
    int r = dfs(pos + 1, A[i], used | ((u128)1 << i), sums | ((u128)1 << s));
    if (r) return r;
  }
  return 0;
}
int main(int argc, char **argv) {
  int mods[8], nm = argc - 1;
  if (nm < 1) return 2;
  N = 1;
  for (int i = 0; i < nm; i++) { mods[i] = atoi(argv[i + 1]); N *= mods[i]; }
  if (N > 40 || N % 2 == 0) { fprintf(stderr, "bad order\n"); return 2; }
  for (int x = 0; x < N; x++) for (int y = 0; y < N; y++) {
    int a = x, b = y, r = 0, mul = 1;
    for (int i = 0; i < nm; i++) {
      int da = a % mods[i], db = b % mods[i]; a /= mods[i]; b /= mods[i];
      r += ((da + db) % mods[i]) * mul; mul *= mods[i];
    }
    add[x][y] = r;
  }
  int kmin = getenv("KMIN") ? atoi(getenv("KMIN")) : 3;
  int kmax = getenv("KMAX") ? atoi(getenv("KMAX")) : N;
  if (getenv("LIMIT")) LIMIT = atoll(getenv("LIMIT"));
  if (getenv("RESTARTS")) RESTARTS = atoi(getenv("RESTARTS"));
  long long total = 0, unknown = 0, fail = 0, maxnodes = 0;
  // subsets containing element 0: bit 0 set
  uint64_t lim = (uint64_t)1 << (N - 1);
  for (uint64_t m = 0; m < lim; m++) {
    uint64_t mask = (m << 1) | 1;
    int k = __builtin_popcountll(mask);
    if (k < kmin || k > kmax) continue;
    K = 0;
    for (int e = 0; e < N; e++) if ((mask >> e) & 1) A[K++] = e;
    total++;
    nodes = 0;
    int r = dfs(1, A[0], 1, 0);
    if (nodes > maxnodes) maxnodes = nodes;
    for (int t = 0; r < 0 && t < RESTARTS; t++) {   // random restarts for hard (near-full) subsets
      for (int i = K - 1; i > 1; i--) { int j = 1 + rand() % i; int x = A[i]; A[i] = A[j]; A[j] = x; }
      nodes = 0; r = dfs(1, A[0], 1, 0);
    }
    if (r == 0) { fail++; printf("FAIL mask=%llx k=%d\n", (unsigned long long)mask, k); }
    else if (r < 0) { unknown++; printf("UNKNOWN mask=%llx k=%d\n", (unsigned long long)mask, k); }
  }
  printf("group");
  for (int i = 0; i < nm; i++) printf(" %d", mods[i]);
  printf(" order=%d k=%d..%d subsets=%lld fail=%lld unknown=%lld maxnodes=%lld limit=%lld\n",
         N, kmin, kmax, total, fail, unknown, maxnodes, LIMIT);
  return fail ? 1 : 0;
}
