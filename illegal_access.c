#include <stdlib.h>

struct account {
    int balance;
};

int main()
//@ requires true;
//@ ensures true;
{
    struct account *myAccount = (struct account *)malloc(sizeof(struct account));
    if (myAccount == 0) { 
        abort();
    }
    myAccount->balance = 5;
    free(myAccount);
    return 0;
}