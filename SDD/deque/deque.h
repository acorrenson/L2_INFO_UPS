#ifndef DEQUE_H
#define DEQUE_H

#include <stdlib.h>

typedef struct deque_s *Deque_t;

/**
 * @brief Create a doubly linked list.
 *
 * @return Deque_t
 */
Deque_t deque_create();

/**
 * @brief Push an element to the front.
 *
 * @return Deque_t
 */
Deque_t deque_push_front(Deque_t, int);

/**
 * @brief Push an element to the back.
 *
 * @return Deque_t
 */
Deque_t deque_push_back(Deque_t, int);

/**
 * @brief Pop the head element.
 *
 * @return Deque_t
 */
Deque_t deque_pop_front(Deque_t);

/**
 * @brief Pop the tail element.
 *
 * @return Deque_t
 */
Deque_t deque_pop_back(Deque_t);

/**
 * @brief Insert an element
 *
 * @return Deque_t
 */
Deque_t deque_insert_at(Deque_t, int, int);

typedef int (*SimpleFunctor)(int);
typedef void (*ReduceFunctor)(int, void *);

void deque_reduce(const Deque_t, ReduceFunctor, void *);
Deque_t deque_map(Deque_t, SimpleFunctor);

#endif