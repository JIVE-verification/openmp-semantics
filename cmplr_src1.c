// gcc cmplr_src1.c -o cmplr_src1 -fopenmp -lpthread
// OMP_NESTED=TRUE OMP_NUM_THREADS=2 ./cmplr_src1
#include <omp.h>
#include <stdio.h>
#include <unistd.h>



int main() {
    int i = 0;
    int j = 0;
    int k = 0;
#pragma omp parallel num_threads(2) private(j) reduction(+:k)
    {
#pragma omp critical
        { i++; }
        j = 1;
        k = 1;
    }
    printf("i = %d, j = %d, k = %d\n", i, j, k);
}