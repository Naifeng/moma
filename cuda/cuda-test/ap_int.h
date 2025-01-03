#ifndef __AP_INT_H__
#define __AP_INT_H__

// header file for any-precision integer arithmetic, implemented with *arrays*

#include <stdlib.h>
#include <string.h>

typedef unsigned __int128 uint128_t;

// ------------------------------- Algorithm (Theoretic) -------------------------------

#define MBITS 256
typedef uint128_t InInt;
typedef uint128_t DInInt; 

// ------------------------------- System (Actual) -------------------------------
// typedef uint8_t BaseInt;
// typedef uint16_t DBaseInt;

// typedef uint16_t BaseInt;
// typedef uint32_t DBaseInt; 

// typedef uint32_t BaseInt;
// typedef uint64_t DBaseInt; 

typedef uint64_t BaseInt;
typedef uint128_t DBaseInt; 

typedef __int128 QBaseInt; // should be only used for testing

#define BaseSize (int) (sizeof(BaseInt)*8)

// InInt to BaseInt Ratio
// InRatio = 2^recursionLevel
#if (MBITS <= 128)
	#define InRatio ((int) sizeof(InInt)*8 / ((int) sizeof(BaseInt)*8))
#else
	#define InRatio ((MBITS + BaseSize - 1) / BaseSize)
#endif

#include <inttypes.h>

// In: QBaseInt
// Out: binary representation
// recursively print binary bits
static void _apprintb(QBaseInt num) {
    if (num >> 1) {
        _apprintb(num >> 1);
    }
    putc((num & 1) ? '1' : '0', stdout);
}

// In: text, BaseInt*
// Out: decimal representation with description
// static void apprinta(char* str, BaseInt* a, int size) {
// 	// printf("%s", str);
// 	for(int i = 0; i < size; i++)
// 		printf("%s[%d]: %" PRIu64 "\n", str, i, a[i]);
// }

// In: text, BaseInt*
// Out: decimal representation with description
static void apprintb(char* str, BaseInt* a, int size) {
	// printf("%s", str);
	for(int i = 0; i < size; i++){
        printf("%s[%d] in binary: ", str, i);
        _apprintb(a[i]);
        printf("\n");
    }
}

// In: text, QBaseInt
// Out: decimal representation with description
__device__ __host__ void apprint(char* str, QBaseInt a) {
	printf("%s", str);
	printf("%llu", a);
	printf("\n");
}

// In: InInt
// Out: BaseInt[InRatio]
// unpack an InInt into BaseInt[InRatio]
BaseInt* apunpack(InInt a) {
    BaseInt* r = (BaseInt *)malloc(sizeof(BaseInt)*InRatio);
    for (int i = 1; i <= InRatio; i++){
        r[i-1] = (BaseInt) (a >> BaseSize*(InRatio-i));
    }
    return r;
}

// In: BaseInt[InRatio]
// Out: InInt
// pack BaseInt[InRatio] into InInt
__device__ __host__ InInt appack(BaseInt* a) {
    InInt r = 0;
    for (int i = 0; i < InRatio; i++){
        r |= ((InInt) a[i]) << (BaseSize * (InRatio-i-1));
    }
	return r;
}

#endif