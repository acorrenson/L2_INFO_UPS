#ifndef STACK_H
#define STACK_H

#include <assert.h>
#include <stdbool.h>

#define MAX_SIZE 256

/**
 * @brief Stack Structure.
 *
 */
typedef struct stack_s {
  int stack_data[MAX_SIZE];
  int top;
} stack_t;

/**
 * @brief Stack constructor stack_create.
 *
 * @semantic default constructor
 *
 */
void stack_create(stack_t *);

/**
 * @brief Stack operator stack_push.
 *
 * @pre
 *  s.top < MAX_SIZE - 1
 * @semantic
 *  default constructor
 *
 */
void stack_push(stack_t *, int);

/**
 * @brief Stack operator stack_create.
 *
 * @semantic
 *  is_empty(create())
 *  ¬is_empty(push(s))
 *
 */
bool stack_is_empty(stack_t *);

/**
 * @brief Stack operator stack_pop
 *
 * @pre
 *  ¬is_empty(s)
 * @semantic
 *  pop(push(s, x)) = s
 *
 */
void stack_pop(stack_t *);

/**
 * @brief Stack operator stack_top
 *
 * @pre
 *  ¬is_empty(s)
 * @semantic
 *  top(push(s, x)) = x
 *
 */
int stack_top(stack_t *);

#endif