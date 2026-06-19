// SPDX-License-Identifier: MIT
//
// Runtime probe for the Linux DR-sentinel fallback: after anti-debugging
// constructors run, report whether the process is currently traced.

#include <stdio.h>
#include <string.h>

static int tracer_pid(void) {
  FILE *f = fopen("/proc/self/status", "r");
  if (!f)
    return -1;

  char line[128];
  int traced = -1;
  while (fgets(line, sizeof(line), f)) {
    if (strncmp(line, "TracerPid:", 10) != 0)
      continue;
    int pid = 0;
    if (sscanf(line + 10, "%d", &pid) == 1)
      traced = pid > 0;
    break;
  }
  fclose(f);
  return traced;
}

int main(void) {
  int traced = tracer_pid();
  printf("tracer=%d\n", traced > 0 ? 1 : 0);
  return 0;
}
