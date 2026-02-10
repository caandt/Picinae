#define MSG "\n*** cfi abort ***\n"

asm("_start: b abort");

long syscall(long num, long arg1, long arg2, long arg3) {
  register long r7 asm("r7") = num;
  register long r0 asm("r0") = arg1;
  register long r1 asm("r1") = arg2;
  register long r2 asm("r2") = arg3;

  asm volatile (
    "svc #0"
    : "+r"(r0)
    : "r"(r1), "r"(r2), "r"(r7)
    : "memory"
  );

  return r0;
}

void abort() {
  syscall(4, 1, (long)MSG, sizeof(MSG)-1);
  syscall(1, 255, 0, 0);
}
