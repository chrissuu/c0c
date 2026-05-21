#include <limits.h>
#include <signal.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>

__attribute__((noreturn))
void __c0vc_abort(const char *msg) {
  fprintf(stderr, "%s\n", msg);
  fflush(stderr);
  raise(SIGABRT);
  exit(1);
}

__attribute__((noreturn))
void __c0vc_arith_error(const char *msg) {
  fprintf(stderr, "%s\n", msg);
  fflush(stderr);
  raise(SIGFPE);
  exit(1);
}

int __c0vc_checked_div(int lhs, int rhs) {
  if (rhs == 0) {
    __c0vc_arith_error("division by zero");
  }
  if (lhs == INT_MIN && rhs == -1) {
    __c0vc_arith_error("division overflow");
  }
  return lhs / rhs;
}

int __c0vc_checked_mod(int lhs, int rhs) {
  if (rhs == 0) {
    __c0vc_arith_error("modulo by zero");
  }
  if (lhs == INT_MIN && rhs == -1) {
    __c0vc_arith_error("modulo overflow");
  }
  return lhs % rhs;
}

int __c0vc_checked_shr(int lhs, int rhs) {
  if (rhs < 0 || rhs >= 32) {
    __c0vc_arith_error("shift amount out of range");
  }
  return lhs >> rhs;
}

int __c0vc_checked_shl(int lhs, int rhs) {
  if (rhs < 0 || rhs >= 32) {
    __c0vc_arith_error("shift amount out of range");
  }
  return (int)((uint32_t)lhs << rhs);
}
