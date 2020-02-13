#include "stack.h"

struct stack_s {
  int stack_data[MAX_SIZE];
  int top;
};

Stack stack_create() {
  Stack s = malloc(sizeof(struct stack_s));
  s->top = -1;
  return s;
}

bool stack_is_empty(Stack s) { return s->top == -1; };

Stack stack_push(Stack s, int e) {
  assert(s->top < MAX_SIZE - 1);
  ++s->top;
  s->stack_data[s->top] = e;
  return s;
}

Stack stack_pop(Stack s) {
  assert(s->top != -1);
  --s->top;
  return s;
}

int stack_top(Stack s) {
  assert(s->top != -1);
  return s->stack_data[s->top];
}
