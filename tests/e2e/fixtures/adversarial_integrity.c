// SPDX-License-Identifier: MIT
//
// Constant-heavy workload for adversarial binary patch tests. The protected
// build post-link seals self-checksum manifests over native code windows; any
// later code mutation must corrupt this deterministic transcript or stop the
// process.

#include <stdint.h>
#include <stdio.h>

static volatile uint64_t sink;

#if defined(__clang__) || defined(__GNUC__)
#define MOROK_NEUTRAL_CODE_SLED()                                             \
    __asm__ volatile(".rept 256\n"                                             \
                     "nop\n"                                                   \
                     ".endr\n"                                                 \
                     :                                                         \
                     :                                                         \
                     : "memory")
#else
#define MOROK_NEUTRAL_CODE_SLED() ((void)0)
#endif

__attribute__((noinline)) static uint64_t rotl64(uint64_t x, unsigned r) {
    return (x << r) | (x >> (64u - r));
}

__attribute__((noinline)) static uint64_t guarded_round(uint64_t x,
                                                        uint64_t y) {
    MOROK_NEUTRAL_CODE_SLED();
    x ^= 0x9e3779b97f4a7c15ULL;
    x += rotl64(y ^ 0xd1b54a32d192ed03ULL, 17);
    x *= 0x94d049bb133111ebULL;
    x ^= x >> 29;
    x += (y | 0x2545f4914f6cdd1dULL);
    x ^= rotl64(x + 0xbf58476d1ce4e5b9ULL, 31);
    return x;
}

int main(void) {
    uint64_t acc = 0xcbf29ce484222325ULL;
    MOROK_NEUTRAL_CODE_SLED();
    for (uint64_t i = 1; i <= 48; ++i) {
        uint64_t lane = i * 0x100000001b3ULL + 0x6a09e667f3bcc909ULL;
        acc ^= guarded_round(acc + lane, i ^ 0x3c6ef372fe94f82bULL);
        acc = rotl64(acc, (unsigned)((i % 23u) + 5u));
    }
    sink = acc;
    printf("adversarial_integrity=%016llx\n", (unsigned long long)sink);
    return sink == 0 ? 2 : 0;
}
