// SPDX-License-Identifier: MIT
//
// Clean-run regression fixture for jitter-sensitive timing probes.  The local
// clock functions intentionally advance in large jumps to model ordinary
// preemption/load stretching short probe spans.

#include <stdint.h>
#include <stdio.h>
#include <time.h>

static volatile uint64_t fake_now_ns = 1000000000ULL;

__attribute__((noinline)) static uint64_t next_fake_time(void) {
    fake_now_ns += 50000000ULL;
    return fake_now_ns;
}

int clock_gettime(clockid_t clock_id, struct timespec *tp) {
    (void)clock_id;
    uint64_t now = next_fake_time();
    tp->tv_sec = (time_t)(now / 1000000000ULL);
    tp->tv_nsec = (long)(now % 1000000000ULL);
    return 0;
}

#if defined(__APPLE__)
uint64_t mach_absolute_time(void) { return next_fake_time(); }
#endif

#if defined(__APPLE__)
#define MOROK_SEALED_SECTION __attribute__((section("__DATA,.morok.sealed")))
#elif defined(__GNUC__) || defined(__clang__)
#define MOROK_SEALED_SECTION __attribute__((section(".morok.sealed")))
#else
#define MOROK_SEALED_SECTION
#endif

static const unsigned char sealed_payload[8] MOROK_SEALED_SECTION = "seal-ok!";

#if defined(__clang__)
#define MOROK_NOOPT __attribute__((noinline, optnone))
#else
#define MOROK_NOOPT __attribute__((noinline))
#endif

MOROK_NOOPT static uint32_t payload_hash(void) {
    uint32_t h = 0x811c9dc5U;
    h = (h ^ sealed_payload[0]) * 16777619U;
    h = (h ^ sealed_payload[1]) * 16777619U;
    h = (h ^ sealed_payload[2]) * 16777619U;
    h = (h ^ sealed_payload[3]) * 16777619U;
    h = (h ^ sealed_payload[4]) * 16777619U;
    h = (h ^ sealed_payload[5]) * 16777619U;
    h = (h ^ sealed_payload[6]) * 16777619U;
    h = (h ^ sealed_payload[7]) * 16777619U;
    return h;
}

int main(void) {
    uint32_t h = payload_hash();
    printf("timing_seal=%08x\n", h);
    return h == 0xdbe66928U ? 0 : 7;
}
