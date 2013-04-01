#include <stdlib.h>

/*@
    predicate node(struct node *node, int count) = 
        node == 0 ? 
            count == 0 : 
                (   
                    malloc_block_node(node) 
                        &*& count > 0
                        &*& node->next |-> ?next 
                        &*& node->value |-> ?value
                        &*& node(next, count - 1)
                );
@*/
struct node {
    struct node *next;
    int value;
};

/*@
    predicate stack(struct stack *stack, int count) =
        malloc_block_stack(stack) 
            &*& stack->head |-> ?head
            &*& count >= 0
            &*& node(head, count);
  @*/
struct stack {
    struct node *head;
};

struct stack *create_stack()
    //@ requires true;
    //@ ensures stack(result, 0);
{
    struct stack *stack = (struct stack *)malloc(sizeof(struct stack));
    if (stack == 0) {
        abort();
    }
    stack->head = 0;
    //@ close node(0, 0);
    //@ close stack(stack, 0);
    return stack;
}

bool stack_is_empty(struct stack *stack) 
    //@ requires stack(stack, ?count);
    //@ ensures stack(stack, count) &*& result == (count == 0);
{
    //@ open stack(stack, count);
    struct node *head = stack->head;
    //@ open node(head, count);
    bool result = stack->head == 0;
    //@ close node(head, count);
    //@ close stack(stack, count);
    return result;
}

void stack_push(struct stack *stack, int value)
    //@ requires stack(stack, ?count);
    //@ ensures stack(stack, count + 1);
{
    struct node *node = (struct node *)malloc(sizeof(struct node));
    if (node == 0) {
        abort();
    }
    //@ open stack(stack, count);
    node->next = stack->head;
    node->value = value;
    stack->head = node;
    //@ close node(node, count + 1);
    //@ close stack(stack, count + 1);
}

int stack_pop(struct stack *stack)
    //@ requires stack(stack, ?count) &*& count > 0;
    //@ ensures stack(stack, count - 1);
{
    //@ open stack(stack, count);
    struct node *head = stack->head;
    //@ open node(head, count);
    int result = head->value;
    stack->head = head->next;
    free(head);
    //@ close stack(stack, count - 1);
    return result;
}

void node_dispose(struct node *node)
    //@ requires node(node, _);
    //@ ensures true;
{
    //@ open node(node, _);
    if (node != 0) {    
        node_dispose(node->next);
        free(node);
    }
}

void stack_dispose(struct stack *stack) 
    //@ requires stack(stack, _);
    //@ ensures true;
{
    //@ open stack(stack, _);
    node_dispose(stack->head);
    free(stack);
}

int node_get_sum(struct node *node)
    //@ requires node(node, ?count);
    //@ ensures node(node, count);
{
    int result = 0;
    //@ open node(node, count); 
    if (node != 0) {
          result = node_get_sum(node->next);
          result += node->value;
       }
    //@ close node(node, count);
    return result;
}

int stack_get_sum(struct stack *stack)
    //@ requires stack(stack, ?count);
    //@ ensures stack(stack, count);
{
    //@ open stack(stack, count);
    int result = node_get_sum(stack->head); 
    //@ close stack(stack, count);
    return result;
}

int main()
    //@ requires true;
    //@ ensures true;
{
    struct stack *s = create_stack();
    stack_push(s, 10);
    stack_push(s, 20);
    stack_pop(s);
    stack_pop(s);
    stack_dispose(s);
    return 0;
}