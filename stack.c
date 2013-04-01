#include <stdlib.h>

/*@
    inductive ints = ints_nil | ints_cons(int, ints);
    predicate node(struct node *node, ints values) = 
        node == 0 ? 
            values == ints_nil : 
                (   
                    malloc_block_node(node) 
                        &*& node->next |-> ?next 
                        &*& node->value |-> ?value
                        &*& node(next, ?next_values)
                        &*& values == ints_cons(value, next_values)
                );
@*/
struct node {
    struct node *next;
    int value;
};

/*@
    predicate stack(struct stack *stack, ints values) =
        malloc_block_stack(stack) 
            &*& stack->head |-> ?head
            &*& node(head, values);
  @*/
struct stack {
    struct node *head;
};

struct stack *create_stack()
    //@ requires true;
    //@ ensures stack(result, ints_nil);
{
    struct stack *stack = (struct stack *) malloc(sizeof(struct stack));
    if (stack == 0) {
        abort();
    }
    stack->head = 0;
    //@ close node(0, ints_nil);
    //@ close stack(stack, ints_nil);
    return stack;
}

bool stack_is_empty(struct stack *stack) 
    //@ requires stack(stack, ?values);
    //@ ensures stack(stack, values) &*& result == (values == ints_nil);
{
    //@ open stack(stack, values);
    struct node *head = stack->head;
    //@ open node(head, values);
    bool result = stack->head == 0;
    //@ close node(head, values);
    //@ close stack(stack, values);
    return result;
}

void stack_push(struct stack *stack, int value)
    //@ requires stack(stack, ?values);
    //@ ensures stack(stack, ints_cons(value, values));
{
    struct node *node = (struct node *) malloc(sizeof(struct node));
    if (node == 0) {
        abort();
    }
    //@ open stack(stack, values);
    node->next = stack->head;
    node->value = value;
    stack->head = node;
    //@ close node(node, ints_cons(value, values));
    //@ close stack(stack, ints_cons(value, values));
}

int stack_pop(struct stack *stack)
    //@ requires stack(stack, ints_cons(?value, ?values)); 
    //@ ensures stack(stack, values) &*& result == value;
{
    //@ open stack(stack, ints_cons(value, values)); 
    struct node *head = stack->head; 
    //@ open node(head, ints_cons(value, values));
    int result = head->value; 
    stack->head = head->next;
    free(head);
    //@ close stack(stack, values);
    return result;
}

void stack_dispose(struct stack *stack) 
    //@ requires stack(stack, ints_nil);
    //@ ensures true;
{
    //@ open stack(stack, ints_nil); 
    //@ open node(_, _);
    free(stack);
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