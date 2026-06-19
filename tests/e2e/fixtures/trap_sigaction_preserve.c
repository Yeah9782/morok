// SPDX-License-Identifier: MIT
#include <signal.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#ifdef MOROK_TRAP_SUPPORT
static volatile sig_atomic_t trap_hits;

static void preinstalled_trap(int sig, siginfo_t *info, void *uctx) {
    (void)info;
    (void)uctx;
    if (sig == SIGTRAP)
        ++trap_hits;
}

__attribute__((constructor)) static void install_trap_handler(void) {
    struct sigaction sa;
    memset(&sa, 0, sizeof(sa));
    sa.sa_sigaction = preinstalled_trap;
    sigemptyset(&sa.sa_mask);
    sigaddset(&sa.sa_mask, SIGUSR1);
    sa.sa_flags = SA_SIGINFO | SA_RESTART;
    if (sigaction(SIGTRAP, &sa, NULL) != 0)
        _Exit(90);
}

void *morok_trap_expected_handler(void) { return (void *)preinstalled_trap; }

int morok_trap_hits(void) { return (int)trap_hits; }
#else
extern void *morok_trap_expected_handler(void);
extern int morok_trap_hits(void);

int main(void) {
    struct sigaction cur;
    if (sigaction(SIGTRAP, NULL, &cur) != 0)
        return 1;

    int failure = 0;
    if ((cur.sa_flags & SA_SIGINFO) == 0)
        failure |= 2;
    if ((void *)cur.sa_sigaction != morok_trap_expected_handler())
        failure |= 4;
    if (sigismember(&cur.sa_mask, SIGUSR1) != 1)
        failure |= 8;
    if (failure != 0) {
        printf("bad:%d\n", failure);
        return failure;
    }

    int before = morok_trap_hits();
    if (raise(SIGTRAP) != 0)
        return 16;
    if (morok_trap_hits() != before + 1)
        return 32;

    printf("ok:%d\n", morok_trap_hits());
    return 0;
}
#endif
