#include <stdlib.h>
#include <assert.h>

struct account {
    int balance;
    int limit;
};

struct account *account_create(int limit)
    //@ requires true;
    //@ ensures malloc_block_account(result) &*& result->balance |-> 0 &*& result->limit |-> limit;
{
    struct account *result = (struct account *)malloc(sizeof(struct account));
    if (result == 0) { 
        abort();
    }
    result->balance = 0;
    result->limit = limit;

    return result;
}

void account_dispose(struct account *account)
    //@ requires malloc_block_account(account) &*& account->balance |-> _ &*& account->limit |-> _;
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

int account_get_balance(struct account *account)
    //@ requires account->balance |-> ?balance;
    //@ ensures account->balance |-> balance &*& result == balance;
{
    return account->balance;
}

void account_deposit(struct account *account, int amount)
    //@ requires account->balance |-> ?balance;
    //@ ensures account->balance |-> (balance + amount) ;
{
    account->balance += amount;
}

int account_withdraw(struct account* account, int amount)
    //@ requires account->balance |-> ?balance &*& account->limit |-> ?limit;
    //@ ensures account->balance |-> ((balance - amount < limit) ? limit : (balance - amount)) &*& account->limit |-> limit &*& result == ((balance - amount < limit) ? (balance - limit) : amount);
{
    if (account->balance - amount < account->limit) {
        amount = account->balance - account->limit;
    }
    account->balance -= amount;
    return amount;
}

int main()
    //@ requires true;
    //@ ensures true;
{
    struct account *myAccount = account_create(-100);
    account_deposit(myAccount, 200);
    int w1 = account_withdraw(myAccount, 50);
    assert(w1 == 50);
    int b1 = account_get_balance(myAccount);
    assert(b1 == 150);
    int w2 = account_withdraw(myAccount, 300);
    assert(w2 == 250);
    int b2 = account_get_balance(myAccount);
    assert(b2 == -100);
    account_dispose(myAccount);
    return 0;
}