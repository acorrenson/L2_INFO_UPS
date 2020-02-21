#include "deque.h"
#include <stdio.h>

typedef struct elem_s {
  int value;
  struct elem_s *prev;
  struct elem_s *next;
} * Elem_t;

struct deque_s {
  Elem_t sentinelle;
  int size;
};

Deque_t deque_create() {
  Deque_t list = malloc(sizeof(struct deque_s));
  list->sentinelle = malloc(sizeof(struct elem_s));
  list->sentinelle->prev = list->sentinelle->next = list->sentinelle;
  list->size = 0;
  return list;
}

Deque_t deque_push_front(Deque_t d, int v) {
  Elem_t e = malloc(sizeof(struct elem_s));
  e->value = v;
  e->next = d->sentinelle->next;
  e->prev = d->sentinelle;
  e->next->prev = e;
  d->sentinelle->next = e;
  ++(d->size);
  return d;
}

Deque_t deque_push_back(Deque_t d, int v) {
  Elem_t e = malloc(sizeof(struct elem_s));
  e->value = v;
  e->prev = d->sentinelle->prev;
  e->next = d->sentinelle;
  e->prev->next = e;
  d->sentinelle->prev = e;
  ++(d->size);
  return d;
}

Deque_t deque_pop_back(Deque_t d) {
  d->sentinelle->prev = d->sentinelle->prev->prev;
  d->size = (d->size > 0 ? d->size - 1 : 0);
  return d;
}

Deque_t deque_insert_at(Deque_t d, int pos, int v) {
  int c = 0;
  Elem_t e = malloc(sizeof(struct elem_s));
  e->value = v;
  Elem_t ptr = d->sentinelle;
  while (c < pos) {
    ptr = ptr->next;
    c++;
  }
  e->next = ptr->next;
  ptr->next = e;
  e->prev = ptr;
  ++(d->size);
  return d;
}

Deque_t deque_map(Deque_t d, SimpleFunctor f) {
  for (Elem_t e = d->sentinelle->next; e != d->sentinelle; e = e->next) {
    e->value = f(e->value);
  }
  return d;
}

void deque_reduce(const Deque_t d, ReduceFunctor f, void *acc) {
  for (Elem_t e = d->sentinelle->next; e != d->sentinelle; e = e->next) {
    f(e->value, acc);
  }
}
