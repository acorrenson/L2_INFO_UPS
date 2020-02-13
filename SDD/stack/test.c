#include "stack.h"

int main(int argc, char const *argv[]) {
  Stack s = stack_create();
  assert(stack_is_empty(s));
  stack_push(s, 1);
  assert(stack_top(s) == 1);
  stack_pop(s);
  assert(stack_is_empty(s));
  return 0;
}