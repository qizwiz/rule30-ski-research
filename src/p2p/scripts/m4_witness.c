/* m4_witness.c: Find minimum witness for m=4 SubcaseB at each firing n'.
   Matches Lean's caEvolve semantics:
     caStepList: new[i] = old[i] XOR (old[i+1] OR old[i+2])  (shrinking tape)
     rule30Local(p,q,r) = p XOR (q OR r)
   Compile: cc -O3 -o m4_witness m4_witness.c
   Usage: ./m4_witness [n_start] [n_end] [max_w]
*/
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define MAX_TAPE (2*100001 + 5)

typedef unsigned char byte;

/* Evolve using Lean semantics: new[i] = old[i] ^ (old[i+1] | old[i+2]).
   Tape shrinks by 2 each step. After 'steps' steps returns the single element. */
static int lean_rule30n(const byte *initial, int L, int steps) {
    static byte buf1[MAX_TAPE], buf2[MAX_TAPE];
    byte *cur = buf1, *nxt = buf2;
    memcpy(cur, initial, L);
    int curL = L;
    for (int t = 0; t < steps; t++) {
        int newL = curL - 2;
        for (int i = 0; i < newL; i++)
            nxt[i] = cur[i] ^ (cur[i+1] | cur[i+2]);
        byte *tmp = cur; cur = nxt; nxt = tmp;
        curL = newL;
    }
    return cur[0];
}

/* spikeAtList w n': tape of length 2*(n'+1)+1, single 1 at index w */
static void make_spike(byte *tape, int w, int n_prime) {
    int L = 2*(n_prime+1)+1;
    memset(tape, 0, L);
    if (w >= 0 && w < L) tape[w] = 1;
}

/* Tape with 1s at positions w and m_val (for sensitivity: flipCell(spike(w), m_val)) */
static void make_two_spike(byte *tape, int w, int m_val, int n_prime) {
    int L = 2*(n_prime+1)+1;
    memset(tape, 0, L);
    if (w >= 0 && w < L) tape[w] ^= 1;
    if (m_val >= 0 && m_val < L) tape[m_val] ^= 1;
}

/* Check SubcaseB: spike(m_val) gives center=0, spike(m_val)+spike(last=2*(n'+1)) gives center=1 */
static int subcaseB_fires(int n_prime, int m_val) {
    int L = 2*(n_prime+1)+1;
    byte tape[MAX_TAPE];
    make_spike(tape, m_val, n_prime);
    int f = lean_rule30n(tape, L, n_prime+1);
    if (f) return 0;
    /* twoSpike(m_val, last) = spike at m_val AND spike at 2*(n'+1) */
    memset(tape, 0, L);
    tape[m_val] = 1;
    tape[2*(n_prime+1)] = 1;
    int g = lean_rule30n(tape, L, n_prime+1);
    return g;
}

/* Find minimum even w>=2, w!=m_val, such that spike(w) center != twoSpike(w,m_val) center
   twoSpike(w, m_val) = spike at w AND spike at m_val (flipCell of spike(w) at position m_val) */
static int find_min_witness(int n_prime, int m_val, int max_w) {
    int L = 2*(n_prime+1)+1;
    byte tape[MAX_TAPE];
    for (int w = 2; w <= max_w; w += 2) {
        if (w == m_val) continue;  /* flipping m_val in spike(m_val) gives zero tape */
        make_spike(tape, w, n_prime);
        int fs = lean_rule30n(tape, L, n_prime+1);
        make_two_spike(tape, w, m_val, n_prime);  /* 1s at w and m_val */
        int ft = lean_rule30n(tape, L, n_prime+1);
        if (fs != ft) return w;
    }
    return -1;
}

static int v2(int k) {
    if (k <= 0) return 99;
    int v = 0;
    while (k % 2 == 0) { k /= 2; v++; }
    return v;
}

int main(int argc, char **argv) {
    int n_start = argc > 1 ? atoi(argv[1]) : 3087;
    int n_end   = argc > 2 ? atoi(argv[2]) : 5200;
    int max_w   = argc > 3 ? atoi(argv[3]) : 80;
    int m_val   = 4;

    printf("%8s %6s %5s %6s %7s %8s %7s %5s\n",
           "n'", "j", "mod8", "mod64", "mod512", "mod1024", "v2(n-5)", "min_w");
    printf("%s\n", "------------------------------------------------------------------------");

    int count = 0;
    for (int n = n_start; n <= n_end; n++) {
        if (n % 8 != 5) continue;
        if (!subcaseB_fires(n, m_val)) continue;
        int j = (n - 3093) / 8;
        int w = find_min_witness(n, m_val, max_w);
        int v = v2(n - 5);
        printf("%8d %6d %5d %6d %7d %8d %7d %5d\n",
               n, j, n%8, n%64, n%512, n%1024, v, w);
        fflush(stdout);
        count++;
    }
    fprintf(stderr, "Total firings in [%d,%d]: %d\n", n_start, n_end, count);
    return 0;
}
