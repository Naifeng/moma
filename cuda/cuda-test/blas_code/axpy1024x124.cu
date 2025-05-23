
/*
 * This code was generated by Spiral 8.5.0, www.spiral.net
 */

#include <stdint.h>

void init_nttmpcuda() {
    /* skip */
}

__global__ void ker_code0(uint64_t  *X, uint64_t  *Y, uint64_t *modulus, uint64_t  *twiddles, uint64_t *mu) {
    int a190, a191, a192, a193, a214, a215, a216, a217, 
            a218, a219, a220, b7, b8, b9, c19, i39, 
            i40;
    uint64_t a198, a199, a200, a201, a202, a207, a208, d10, 
            d11, d12, d13, d14, d15, d16, d17, d18, 
            m4, p3, p4, t40, t41, t44, t45, t58, 
            t59, t60, t61, t62, t63, t64, t65, t66, 
            t67, t68, t69, t70, t71, t72, t73, t74, 
            t75, t76, t77, t78;
    uint128_t a194, a195, a196, a197, a203, a204, a205, a206, 
            a209, a210, a211, c11, c12, c13, c14, c15, 
            c16, c17, c18, s28, s29, s30;
    __shared__ uint64_t T1[8];
    a190 = (1024*blockIdx.x);
    a191 = (a190 + threadIdx.x);
    /* Begin of MPModMul 64 */
    /* Begin of MPMulQDD_Schoolbook_Partial */
    a192 = (2*a191);
    a193 = (a192 + 1);
    a194 = (((uint128_t ) X[a193])*((uint128_t ) twiddles[1]));
    a195 = (((uint128_t ) X[a193])*((uint128_t ) twiddles[0]));
    a196 = (((uint128_t ) X[a192])*((uint128_t ) twiddles[1]));
    a197 = (((uint128_t ) X[a192])*((uint128_t ) twiddles[0]));
    c11 = (((uint128_t ) a195) + ((uint128_t ) a196));
    t58 = (a194 >> 64);
    c12 = (((uint128_t ) c11) + ((uint128_t ) t58));
    t59 = (c12 >> 64);
    c13 = (((uint128_t ) a197) + ((uint128_t ) t59));
    t60 = (c13 >> 64);
    t61 = ((uint64_t ) c13);
    t62 = ((uint64_t ) c12);
    t63 = ((uint64_t ) a194);
    /* End of MPMulQDD_Schoolbook_Partial */
    /* Begin of MPModDQ */
    /* Begin of MPShiftRight3 */
    p3 = (t62 >> 58);
    a198 = ((uint64_t ) 1);
    a199 = (a198 << 58);
    m4 = (a199 - 1);
    p4 = (((t60)&(m4)));
    a200 = (p4 << 6);
    a201 = (t61 >> 58);
    t64 = (((a200)|(a201)));
    a202 = (t61 << 6);
    t65 = (((a202)|(p3)));
    /* End of MPShiftRight3 */
    t40 = mu[0];
    t41 = mu[1];
    /* Begin of MPMulQDD_Schoolbook_Partial */
    a203 = (((uint128_t ) t65)*((uint128_t ) t41));
    a204 = (((uint128_t ) t65)*((uint128_t ) t40));
    a205 = (((uint128_t ) t64)*((uint128_t ) t41));
    a206 = (((uint128_t ) t64)*((uint128_t ) t40));
    c14 = (((uint128_t ) a204) + ((uint128_t ) a205));
    t66 = (a203 >> 64);
    c15 = (((uint128_t ) c14) + ((uint128_t ) t66));
    t67 = (c15 >> 64);
    c16 = (((uint128_t ) a206) + ((uint128_t ) t67));
    t68 = (c16 >> 64);
    t69 = ((uint64_t ) c16);
    /* End of MPMulQDD_Schoolbook_Partial */
    /* Begin of MPShiftRight2 */
    t70 = (t68 >> 1);
    a207 = (t68 << 63);
    a208 = (t69 >> 1);
    t71 = (((a207)|(a208)));
    /* End of MPShiftRight2 */
    t44 = modulus[0];
    t45 = modulus[1];
    /* Begin of MPMulQDD_Schoolbook_Partial */
    a209 = (((uint128_t ) t71)*((uint128_t ) t45));
    a210 = (((uint128_t ) t71)*((uint128_t ) t44));
    a211 = (((uint128_t ) t70)*((uint128_t ) t45));
    c17 = (((uint128_t ) a210) + ((uint128_t ) a211));
    t72 = (a209 >> 64);
    c18 = (((uint128_t ) c17) + ((uint128_t ) t72));
    t73 = ((uint64_t ) c18);
    t74 = ((uint64_t ) a209);
    /* End of MPMulQDD_Schoolbook_Partial */
    /* Begin of MPSubDDD 64 */
    d10 = (t63 - t74);
    b7 = ((t63 < t74));
    d11 = (t62 - t73);
    d12 = (d11 - b7);
    /* End of MPSubDDD 64 */
    /* Begin of MPSubDDD 64 */
    d13 = (d10 - t45);
    b8 = ((d10 < t45));
    d14 = (d12 - t44);
    d15 = (d14 - b8);
    /* End of MPSubDDD 64 */
    /* MPLessThan 64 */
    a214 = ((d12 < t44));
    a215 = ((d12 == t44));
    a216 = ((a215) && (b8));
    i39 = ((a214) || (a216));
    t75 = ((i39) ? (d12) : (d15));
    t76 = ((i39) ? (d10) : (d13));
    /* End of MPModDQ */
    /* End of MPModMul 64 */
    /* Begin of MPModAdd 64 */
    /* MPAddDDD 64 */
    s28 = (((uint128_t ) t76) + ((uint128_t ) twiddles[a193]));
    t77 = ((uint64_t ) s28);
    c19 = (s28 >> 64);
    s29 = (((uint128_t ) t75) + ((uint128_t ) twiddles[a192]));
    s30 = (((uint128_t ) s29) + ((uint128_t ) c19));
    t78 = ((uint64_t ) s30);
    /* Begin of MPModDD */
    /* MPLessThan 64 */
    a217 = ((t44 < t78));
    a218 = ((t44 == t78));
    a219 = ((t45 < t77));
    a220 = ((a218) && (a219));
    i40 = ((a217) || (a220));
    /* Begin of MPSubDDD 64 */
    d16 = (t77 - t45);
    b9 = ((t77 < t45));
    d17 = (t78 - t44);
    d18 = (d17 - b9);
    /* End of MPSubDDD 64 */
    Y[a192] = ((i40) ? (d18) : (t78));
    Y[a193] = ((i40) ? (d16) : (t77));
    /* End of MPModDD */
    /* End of MPModAdd 64 */
    __syncthreads();
}

void nttmpcuda(uint64_t  *Y, uint64_t  *X, uint64_t modulus[2], uint64_t  *twiddles, uint64_t mu[2]) {
    dim3 b3(1024, 1, 1), g1(2, 1, 1);
    ker_code0<<<g1, b3>>>(X, Y, modulus, twiddles, mu);
}

void destroy_nttmpcuda() {
    /* skip */
}
