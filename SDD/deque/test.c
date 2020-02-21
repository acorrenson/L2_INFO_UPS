#include "deque.h"

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

  deque_insert_at(d, 0, -1);
  deque_map(d, print_elem);
  printf("--\n");
  deque_insert_at(d, 5, -2);
  deque_map(d, print_elem);

  return 0;
}
