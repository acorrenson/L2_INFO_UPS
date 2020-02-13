#include "stack.h"

void stack_create(stack_t *s) { s->top = -1; }

bool stack_is_empty(stack_t *s) { return s->top == -1; };

void stack_push(stack_t *s, int e) {
  assert(s->top < MAX_SIZE - 1);
  ++s->top;
  s->stack_data[s->top] = e;
}

void stack_pop(stack_t *s) {
  assert(s->top != -1);
  --s->top;
}

int stack_top(stack_t *s) {
  assert(s->top != -1);
  return s->stack_data[s->top];
}

int main(int argc, char const *argv[]) {
  stack_t s;
  stack_create(&s);
  assert(stack_is_empty(&s));
  stack_push(&s, 1);
  assert(stack_top(&s) == 1);
  stack_pop(&s);
  assert(stack_is_empty(&s));

  return 0;
}
