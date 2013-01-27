#include <stdlib.h>

struct account {
    int balance;
};

int main()
//@ requires true;
//@ ensures true;
{
    struct account myLocalAccount;
    struct account *myAccount = &myLocalAccount;
    if (myAccount == 0) { 
        abort();
    }
    myAccount->balance = 5;
    free(myAccount);
    return 0;
}