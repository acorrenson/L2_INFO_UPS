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

int print_elem(int v) {
  printf("%d\n", v);
  return v;
}

void sum(int v, void *acc) {
  int *s = (int *)acc;
  *s = *s + v;
}

void prod(int v, void *acc) {
  int *p = (int *)acc;
  *p = *p * v;
}

int main(int argc, char const *argv[]) {
  int s = 0;
  int p = 1;
  Deque_t d = deque_create();
  deque_push_back(d, 1);
  deque_push_back(d, 2);
  deque_push_back(d, 3);
  deque_push_back(d, 4);

  deque_map(d, print_elem);

  deque_reduce(d, sum, &s);
  printf("sum : %d\n", s);

  deque_reduce(d, prod, &p);
  printf("prod : %d\n", p);

  return 0;
}
