#include <stdlib.h>

struct account {
    int balance;
};

struct account *account_create()
    //@ requires true;
    //@ ensures malloc_block_account(result) &*& result->balance |-> 0;
{
    struct account *result = (struct account *)malloc(sizeof(struct account));
    if (result == 0) { 
        abort();
    }
    result->balance = 0;

    return result;
}

void account_dispose(struct account *account)
    //@ requires malloc_block_account(account) &*& account->balance |-> _;
    //@ ensures true;
{
    free(account);
}

void account_set_balance(struct account *account, int newBalance)
    //@ requires account->balance |-> _;
    //@ ensures account->balance |-> newBalance;
{
    account->balance = newBalance;
}

int main()
    //@ requires true;
    //@ ensures true;
{
    struct account *myAccount = account_create();
    account_set_balance(myAccount, 5);
    account_dispose(myAccount);
    return 0;
}