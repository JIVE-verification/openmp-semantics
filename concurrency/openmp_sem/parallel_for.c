// gcc parallel_for.c -o parallel_for -fopenmp -lpthread
// OMP_NESTED=TRUE OMP_NUM_THREADS=6 ./parallel_for
#include <omp.h>
#include <stdio.h>

int main() {
    
    int count = 0;
    #pragma omp parallel num_threads(3)
    {
        #pragma omp for reduction (+:count)
        for (int i=0; i<6; i+=1) {
            count += 1;

            int *ptr1=&count;
            int *ptr2=&i;
        }
    }
    //printf("count=%d\n", count);
    return 0;
}