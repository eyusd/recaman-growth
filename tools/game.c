/* Exhaustive checks, independent of the Lean development (no proof depends on them).
 *
 *   cc -O2 -o tools/game tools/game.c
 *   tools/game reach L     the reach R(1..L) of the window game
 *   tools/game dial N      max of W for each D, over all words of length <= N and all their prefixes; also the max of
 *                          2F - D, where F counts the up-steps whose witnesses are all at distance >= 8
 *   tools/game rung K      W_K <= D on all words, W_K counting witnesses at distance <= K only (no length limit)
 *   tools/game ratio N     max of a(n)/n for n <= N, and the balance after N steps
 *
 * A walk u steps by +-1. Time s < t witnesses the step after t if u[t] = u[s] + 1 and the sum of u[i] - u[s] over
 * s <= i < t is -1. With A[t] = u[0] + ... + u[t-1] this reads A[t] - A[s] = u[s] (t - s) - 1.
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define MAX 128
static int u[MAX + 1], A[MAX + 1], best, maxW[MAX + 1], max2FD = -MAX;

/* distance to the nearest witness of step t, or 0 if it has none */
static int nearest(int t) {
    for (int s = t - 1; s >= 0; s--)
        if (u[s] == u[t] - 1 && A[t] - A[s] == u[s] * (t - s) - 1) return t - s;
    return 0;
}

static int witnessed(int t) { return nearest(t) > 0; }

static void step(int t, int e) { A[t + 1] = A[t] + u[t]; u[t + 1] = u[t] + e; }

static void reach(int t, int L) {
    if (u[t] > best) best = u[t];
    if (u[t] + (L - t) <= best) return;
    int w = u[t] >= 2 ? witnessed(t) : -1;
    if (w != 0) { step(t, +1); reach(t + 1, L); }
    if (w != 1) { step(t, -1); reach(t + 1, L); }
}

static void dial(int t, int N, int W, int F, int D) {
    if (W > maxW[D]) maxW[D] = W;
    if (2 * F - D > max2FD) max2FD = 2 * F - D;
    if (t == N) return;
    int d = nearest(t);
    step(t, +1); dial(t + 1, N, W + (d > 0), F + (d >= 8), D);
    step(t, -1); dial(t + 1, N, W, F, D + 1);
}

/* A word is a path in the graph whose states are the last K signs; W_K <= D on all words iff no cycle has a positive
 * total weight, where a witnessed up-step weighs +1 and a down-step -1. */
static int rung(int K) {
    size_t n = (size_t)1 << K;
    signed char *wit = calloc(n, 1), *V = calloc(n, 1);
    for (size_t x = 0; x < n; x++)
        for (int d = 1, h = 0, sum = 0; d <= K && !wit[x]; d++) { /* h = u[t-d] - u[t], sum over [t-d, t) of u[i] - u[t] */
            h -= (x >> (d - 1)) & 1 ? 1 : -1;
            sum += h;
            wit[x] = h == -1 && sum - d * h == -1;
        }
    for (int changed = 1; changed;) {
        changed = 0;
        for (size_t x = 0; x < n; x++)
            for (int e = 0; e < 2; e++) {
                size_t y = ((x << 1) | e) & (n - 1);
                int v = V[x] + (e ? wit[x] : -1);
                if (v > V[y]) { V[y] = v; changed = 1; }
                if (v > 100) return 0;
            }
    }
    free(wit); free(V);
    return 1;
}

static void ratio(long long N) {
    long long cap = 1 << 20, a = 0, at = 0, balance = 0;
    unsigned char *seen = calloc(cap, 1);
    double worst = 0;
    seen[0] = 1;
    for (long long n = 1; n <= N; n++) {
        int down = a >= n && !seen[a - n];
        a += down ? -n : n;
        balance += down ? -1 : 1;
        while (a >= cap) { seen = realloc(seen, 2 * cap); memset(seen + cap, 0, cap); cap *= 2; }
        seen[a] = 1;
        if ((double)a / n > worst) { worst = (double)a / n; at = n; }
    }
    printf("max a(n)/n = %.4f, at n = %lld; additions minus subtractions = %lld\n", worst, at, balance);
    free(seen);
}

int main(int argc, char **argv) {
    if (argc != 3) { fprintf(stderr, "usage: game reach L | dial N | rung K | ratio N\n"); return 2; }
    long long n = atoll(argv[2]);
    if (!strcmp(argv[1], "ratio")) { ratio(n); return 0; }
    if (n < 1 || n > MAX) return 2;
    if (!strcmp(argv[1], "reach"))
        for (int L = 1; L <= n; L++) { best = 0; reach(0, L); printf("R(%d) = %d\n", L, best); fflush(stdout); }
    if (!strcmp(argv[1], "dial")) {
        int ok = 1;
        dial(0, (int)n, 0, 0, 0);
        for (int D = 0; D <= n; D++) { ok &= maxW[D] <= D; printf("D = %d: max W = %d\n", D, maxW[D]); }
        printf(ok ? "W <= D on every word of length <= %lld\n" : "W > D occurs (length <= %lld)\n", n);
        printf("max of 2F - D: %d, so %s\n", max2FD, max2FD <= 0 ? "2F <= D everywhere" : "2F > D occurs");
    }
    if (!strcmp(argv[1], "rung") && n <= 30)
        for (int K = 1; K <= n; K++) { printf("rung %d: %s\n", K, rung(K) ? "holds" : "fails"); fflush(stdout); }
    return 0;
}
