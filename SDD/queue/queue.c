#include "queue.h"

struct s_queue {
  int queue_data[QUEUE_SIZE];
  int head;
  int tail;
  int size;
};

Queue queue_create() {
  Queue q = malloc(sizeof(struct s_queue));
  q->head = 0;
  q->tail = -1;
  q->size = 0;
  return q;
}

Queue queue_push(Queue q, int e) {
  assert(q->size < QUEUE_SIZE);
  q->tail = (q->tail + 1) % QUEUE_SIZE;
  q->queue_data[q->tail] = e;
  ++q->size;
  return q;
}

bool queue_is_empty(Queue q) { return q->size == 0; }

Queue queue_pop(Queue q) {
  assert(!queue_is_empty(q));
  q->head = (q->head + 1) % QUEUE_SIZE;
  --q->size;
  return q;
}

int queue_top(Queue q) {
  assert(!queue_is_empty(q));
  return q->queue_data[q->head];
}
