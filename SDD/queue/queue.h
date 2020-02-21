#ifndef QUEUE_H
#define QUEUE_H

#include <assert.h>
#include <stdbool.h>
#include <stdlib.h>

#define QUEUE_SIZE 256

typedef struct s_queue *Queue;

Queue queue_create();
Queue queue_push(Queue, int);
Queue queue_pop();
bool queue_is_empty();
int queue_top();

#endif