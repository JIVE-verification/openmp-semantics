// gcc cmplr_tgt1.c -o cmplr_tgt1 -lpthread
// ./cmplr_tgt1

#include <stdio.h>
#include <unistd.h>
#include "threads.h"

lock_t critical_mutex_1; 

// one mutex for each reduction variable in each reduction
lock_t reduction_mutex_1; // for k

typedef struct _par_routine1_data_ty{
    // shared variables
    int* i;
    // reduction variables, should not be accessed by threads in the reduction region directly
    int* k;
} _par_routine1_data_ty;

void * _par_routine1(void* __par_routine1_data){
    // initializing variable environment
    _par_routine1_data_ty * _par_routine1_data = (struct _par_routine1_data_ty*)__par_routine1_data;
    
    int *_i = _par_routine1_data->i; // set up shared variables
    int j; // unintialized accoring to private
    int k=0; // initialized according to reduction

    // original code starts; all accesses to shared variables are transformed to the pointer version
    acquire(&critical_mutex_1); // critical start
    (*_i)++; // increment i
    release(&critical_mutex_1); // critical end
    j = 1;
    k = 1;
    int l=0;

    // do reduction
    acquire(&reduction_mutex_1); // reduction start
    *_par_routine1_data->k = *_par_routine1_data->k + k; // increment k
    release(&reduction_mutex_1); // reduction end

    return NULL;
}


int main() {
    // initialize mutexes
    // can't move to call site of mutex_lock() because initialization should happen only once
    lock_t lock_1 = makelock();
    lock_t lock_2 = makelock();


    int i = 0;
    int j = 0;
    int k = 0;

    /* parallel region start */

    _par_routine1_data_ty __par_routine1_data_1 = {&i, &k};
    _par_routine1_data_ty __par_routine1_data_2 = {&i, &k};
    int t2 = spawn(_par_routine1, (void *)&__par_routine1_data_2);
    
    _par_routine1((void *)&__par_routine1_data_1);

    // wait for threads to finish
    join_thread(t2);
    /* parallel region end */

    printf("i = %d, j = %d, k = %d\n", i, j, k);

    // destroy mutexes
    freelock(lock_1);
    freelock(lock_2);

    return 0;
}

// pass 1: figure out the temp vars that are supposed to be shared, change to locals