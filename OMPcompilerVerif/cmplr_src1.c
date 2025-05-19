// gcc cmplr_src1.c -o cmplr_src1 -fopenmp -lpthread
// OMP_NESTED=TRUE OMP_NUM_THREADS=2 ./cmplr_src1
// #include <omp.h>
#include <stdio.h>
#include <pthread.h>
// #include <unistd.h>

int main() {
    int i = 0;
    int j = 0;
    int k = 0;
#pragma omp parallel num_threads(2) private(j) reduction(+:k)
    {

        // here
#pragma omp critical
        { i++; }
        j = 1;
        k = 1;
        int l = 0;
    }
    printf("i = %d, j = %d, k = %d\n", i, j, k);
}


typedef struct _par_routine1_data_ty{
    // shared variables
    int* i;
    // reduction variables, should not be accessed by threads in the reduction region directly
    int* k;
} _par_routine1_data_ty;


pthread_mutex_t critical_mutex_1; 

// one mutex for each reduction variable in each reduction
pthread_mutex_t reduction_mutex_1; // for k

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
    _par_routine1_data->k = _par_routine1_data->k + k; // increment k
    pthread_mutex_unlock(&reduction_mutex_1); // reduction end

    return NULL;
}