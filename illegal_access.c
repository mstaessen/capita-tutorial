#include <stdlib.h>
#include <assert.h>

/*@
    predicate account_pred(struct account *account, int limit, int balance) =
        malloc_block_account(account) 
            &*& account->balance |-> balance 
            &*& account->limit |-> limit;
  @*/
struct account {
    int balance;
    int limit;
};

struct account *account_create(int limit)
    //@ requires true;
    //@ ensures account_pred(result, limit, 0);
{
    struct account *result = (struct account *)malloc(sizeof(struct account));
    if (result == 0) { 
        abort();
    }
    result->balance = 0;
    result->limit = limit;
    
    //@ close account_pred(result, limit, 0);

    return result;
}

void account_dispose(struct account *account)
    //@ requires account_pred(account, _, _);
    //@ ensures true;
{
    //@ open account_pred(account, _, _);
    free(account);
}

void account_set_balance(struct account *account, int newBalance)
    //@ requires account_pred(account, _, ?balance);
    //@ ensures account_pred(account, _, newBalance);
{
    //@ open account_pred(account, _, balance);
    account->balance = newBalance;
    //@ close account_pred(account, _, newBalance);
}

int account_get_balance(struct account *account)
    //@ requires account_pred(account, _, ?balance);
    //@ ensures account_pred(account, _, balance) &*& result == balance;
{
    //@ open account_pred(account, _, balance);
    return account->balance;
    //@ close account_pred(account, _, balance);
}

void account_deposit(struct account *account, int amount)
    //@ requires account_pred(account, _, ?balance) &*& amount >= 0;
    //@ ensures account_pred(account, _, balance + amount);
{
    //@ open account_pred(account, _, balance);
    account->balance += amount;
    //@ close account_pred(account, _, balance + amount);
}

int account_withdraw(struct account* account, int amount)
    //@ requires account_pred(account, ?limit, ?balance) &*& amount >= 0;
    //@ ensures account_pred(account, limit, balance - result) &*& result == ((balance - amount < limit) ? (balance - limit) : amount);
{
    //@ open account_pred(account, limit, balance);
    if (account->balance - amount < account->limit) {
        amount = account->balance - account->limit;
    }
    account->balance -= amount;
    //@ close account_pred(account, limit, balance - amount);
    return amount;
}

int main()
    //@ requires true;
    //@ ensures true;
{
    struct account *myAccount = account_create(-100);
    account_deposit(myAccount, 200);
    int w1 = account_withdraw(myAccount, 50);
    //assert(w1 == 50);
    int b1 = account_get_balance(myAccount);
    //assert(b1 == 150);
    int w2 = account_withdraw(myAccount, 300);
    //assert(w2 == 250);
    int b2 = account_get_balance(myAccount);
    //assert(b2 == -100);
    account_dispose(myAccount);
    return 0;
}