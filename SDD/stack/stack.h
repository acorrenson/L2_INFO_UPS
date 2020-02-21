#ifndef STACK_H
#define STACK_H

#include <assert.h>
#include <stdbool.h>
#include <stdlib.h>

#define STACK_SIZE 256

/**
 * @brief Stack Structure.
 *
 */
typedef struct s_stack *Stack;

/**
 * @brief Stack constructor stack_create.
 *
 * @semantic default constructor
 *
 */
Stack stack_create();

/**
 * @brief Stack operator stack_push.
 *
 * @pre
 *  s.top < STACK_SIZE - 1
 * @semantic
 *  default constructor
 *
 */
Stack stack_push(Stack, int);

/**
 * @brief Stack operator stack_create.
 *
 * @semantic
 *  is_empty(create())
 *  ¬is_empty(push(s))
 *
 */
bool stack_is_empty(Stack);

/**
 * @brief Stack operator stack_pop
 *
 * @pre
 *  ¬is_empty(s)
 * @semantic
 *  pop(push(s, x)) = s
 *
 */
Stack stack_pop();

/**
 * @brief Stack operator stack_top
 *
 * @pre
 *  ¬is_empty(s)
 * @semantic
 *  top(push(s, x)) = x
 *
 */
int stack_top(Stack);

#endif