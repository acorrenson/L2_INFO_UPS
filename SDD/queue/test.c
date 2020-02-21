#include "queue.h"

int main(int argc, char const *argv[]) {
  Queue q = queue_create();
  queue_push(q, 0);
  queue_push(q, 1);
  queue_push(q, 2);
  assert(queue_top(q) == 0);
  queue_pop(q);
  assert(queue_top(q) == 1);
  queue_pop(q);
  assert(queue_top(q) == 2);
  queue_pop(q);
  assert(queue_is_empty(q));

  return 0;
}
