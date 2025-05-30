
/*
 * This code was generated by Spiral 8.5.1, www.spiral.net
 */

#include <stdint.h>

void init_nttmpcuda() {
    /* skip */
}

__global__ void ker_code0(uint64_t  *X, uint64_t  *Y, uint64_t *modulus, uint64_t  *twiddles, uint64_t *mu) {
    int a119, a120, a121, a122, a124, a125, a126, b5, 
            c2, i38;
    uint64_t a91, a93, d4, d5, d6, t18, t19;
    uint128_t s28, s29, s30;
    __shared__ uint64_t T1[8];
    a119 = (1024*blockIdx.x);
    a120 = (a119 + threadIdx.x);
    /* Begin of MPModSub 64 */
    /* Begin of MPSubDDD 64 */
    a121 = (2*a120);
    a122 = (a121 + 1);
    d4 = (X[a122] - twiddles[a122]);
    b5 = ((X[a122] < twiddles[a122]));
    d5 = (X[a121] - twiddles[a121]);
    d6 = (d5 - b5);
    /* End of MPSubDDD 64 */
    /* MPAddDDD 64 */
    a91 = modulus[1];
    s28 = (((uint128_t ) d4) + ((uint128_t ) a91));
    t18 = ((uint64_t ) s28);
    c2 = (s28 >> 64);
    a93 = modulus[0];
    s29 = (((uint128_t ) d6) + ((uint128_t ) a93));
    s30 = (((uint128_t ) s29) + ((uint128_t ) c2));
    t19 = ((uint64_t ) s30);
    /* MPLessThan 64 */
    a124 = ((X[a121] < twiddles[a121]));
    a125 = ((X[a121] == twiddles[a121]));
    a126 = ((a125) && (b5));
    i38 = ((a124) || (a126));
    Y[a121] = ((i38) ? (t19) : (d6));
    Y[a122] = ((i38) ? (t18) : (d4));
    /* End of MPModSub 64 */
    __syncthreads();
}

void nttmpcuda(uint64_t  *Y, uint64_t  *X, uint64_t modulus[2], uint64_t  *twiddles, uint64_t mu[2]) {
    dim3 b3(1024, 1, 1), g1(2, 1, 1);
    ker_code0<<<g1, b3>>>(X, Y, modulus, twiddles, mu);
}

void destroy_nttmpcuda() {
    /* skip */
}
