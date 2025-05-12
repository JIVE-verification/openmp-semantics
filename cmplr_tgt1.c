// gcc cmplr_tgt1.c -o cmplr_tgt1 -lpthread
// ./cmplr_tgt1

#include <stdio.h>
#include <unistd.h>
#include <pthread.h>

pthread_mutex_t critical_mutex_1; 

// one mutex for each reduction variable in each reduction
pthread_mutex_t reduction_mutex_1; // for k

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
    pthread_mutex_lock(&critical_mutex_1); // critical start
    (*_i)++; // increment i
    pthread_mutex_unlock(&critical_mutex_1); // critical end
    j = 1;
    k = 1;

    // do reduction
    pthread_mutex_lock(&reduction_mutex_1); // reduction start
     ->k = _par_routine1_data->k + k; // increment k
    pthread_mutex_unlock(&reduction_mutex_1); // reduction end

    return NULL;
}


int main() {
    // initialize mutexes
    // can't move to call site of mutex_lock() because initialization should happen only once
    if (pthread_mutex_init(&critical_mutex_1, NULL) != 0) {
        return 1; 
    } 
    if (pthread_mutex_init(&reduction_mutex_1, NULL) != 0) {
        return 1; 
    }


    int i = 0;
    int j = 0;
    int k = 0;

    /* parallel region start */
    pthread_t t1,t2;
    _par_routine1_data_ty __par_routine1_data_1 = {&i, &k};
    pthread_create(&t1, NULL, _par_routine1, (void *)&__par_routine1_data_1);
    _par_routine1_data_ty __par_routine1_data_2 = {&i, &k};
    pthread_create(&t2, NULL, _par_routine1, (void *)&__par_routine1_data_1);
    // wait for threads to finish
    pthread_join(t1, NULL);
    pthread_join(t2, NULL);
    /* parallel region end */

    printf("i = %d, j = %d, k = %d\n", i, j, k);

    // destroy mutexes
    if (pthread_mutex_destroy(&critical_mutex_1) != 0) {
        return 1; 
    }
    if (pthread_mutex_destroy(&reduction_mutex_1) != 0) {
        return 1; 
    }

    return 0;
}