#include <inttypes.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/types.h>
#include <sys/stat.h>
#include <fcntl.h>
#include <unistd.h>
#include <time.h>
#include <stdbool.h>
#include <assert.h>
#include "test_helpers.h"

#include <openssl/evp.h>
#include <openssl/ecdsa.h>
#include <openssl/ecdh.h>
#include <openssl/ec.h>

#include "Hacl_P256.h"
#include "Lib_RandomBuffer_System.h"

#include "uECC.h"

uint8_t
prKey[32U] =
  {
    (uint8_t)81U, (uint8_t)155U, (uint8_t)66U, (uint8_t)61U, (uint8_t)113U, (uint8_t)95U,
    (uint8_t)139U, (uint8_t)88U, (uint8_t)31U, (uint8_t)79U, (uint8_t)168U, (uint8_t)238U,
    (uint8_t)89U, (uint8_t)244U, (uint8_t)119U, (uint8_t)26U, (uint8_t)91U, (uint8_t)68U,
    (uint8_t)200U, (uint8_t)19U, (uint8_t)11U, (uint8_t)78U, (uint8_t)62U, (uint8_t)172U,
    (uint8_t)202U, (uint8_t)84U, (uint8_t)165U, (uint8_t)109U, (uint8_t)218U, (uint8_t)114U,
    (uint8_t)180U, (uint8_t)100U
  };

uint8_t
digest[32U] =
  {
    (uint8_t)28U, (uint8_t)203U, (uint8_t)233U, (uint8_t)28U, (uint8_t)7U, (uint8_t)95U,
    (uint8_t)199U, (uint8_t)244U, (uint8_t)240U, (uint8_t)51U, (uint8_t)191U, (uint8_t)162U,
    (uint8_t)72U, (uint8_t)219U, (uint8_t)143U, (uint8_t)204U, (uint8_t)211U, (uint8_t)86U,
    (uint8_t)93U, (uint8_t)233U, (uint8_t)75U, (uint8_t)191U, (uint8_t)177U, (uint8_t)47U,
    (uint8_t)60U, (uint8_t)89U, (uint8_t)255U, (uint8_t)70U, (uint8_t)194U, (uint8_t)113U,
    (uint8_t)191U, (uint8_t)131U
  };

uint8_t
nonce[32U] =
  {
    (uint8_t)148U, (uint8_t)161U, (uint8_t)187U, (uint8_t)177U, (uint8_t)75U, (uint8_t)144U,
    (uint8_t)106U, (uint8_t)97U, (uint8_t)162U, (uint8_t)128U, (uint8_t)242U, (uint8_t)69U,
    (uint8_t)249U, (uint8_t)233U, (uint8_t)60U, (uint8_t)127U, (uint8_t)59U, (uint8_t)74U,
    (uint8_t)98U, (uint8_t)71U, (uint8_t)130U, (uint8_t)79U, (uint8_t)93U, (uint8_t)51U,
    (uint8_t)185U, (uint8_t)103U, (uint8_t)7U, (uint8_t)135U, (uint8_t)100U, (uint8_t)42U,
    (uint8_t)104U, (uint8_t)222U
  };

uint8_t
siggen_vectors_low5[32U] =
  {
    (uint8_t)243U, (uint8_t)172U, (uint8_t)128U, (uint8_t)97U, (uint8_t)181U, (uint8_t)20U,
    (uint8_t)121U, (uint8_t)91U, (uint8_t)136U, (uint8_t)67U, (uint8_t)227U, (uint8_t)214U,
    (uint8_t)98U, (uint8_t)149U, (uint8_t)39U, (uint8_t)237U, (uint8_t)42U, (uint8_t)253U,
    (uint8_t)107U, (uint8_t)31U, (uint8_t)106U, (uint8_t)85U, (uint8_t)90U, (uint8_t)122U,
    (uint8_t)202U, (uint8_t)187U, (uint8_t)94U, (uint8_t)111U, (uint8_t)121U, (uint8_t)200U,
    (uint8_t)194U, (uint8_t)172U
  };

uint8_t
siggen_vectors_low6[32U] =
  {
 	0xcf, 0xa7, 0x40, 0xfe, 0xc7, 0x67, 0x96, 0xd2, 
 	0xe3, 0x92, 0x16, 0xbe, 0x7e, 0xbf, 0x58, 0x0e, 
 	0xa3, 0xc0, 0xef, 0x4b, 0xb0, 0x0a, 0xb2, 0xe7, 
 	0xe4, 0x20, 0x84, 0x34, 0xf4, 0x5f, 0x8c, 0x9c
  };


static uint8_t px0_0[32] = {
0x70, 0x0c, 0x48, 0xf7, 0x7f, 0x56, 0x58, 0x4c, 0x5c, 0xc6, 0x32, 0xca, 0x65, 0x64, 0x0d, 0xb9, 0x1b, 0x6b, 0xac, 0xce, 0x3a, 0x4d, 0xf6, 0xb4, 0x2c, 0xe7, 0xcc, 0x83, 0x88, 0x33, 0xd2, 0x87 

};
static uint8_t py0_0[32] = {
0xdb, 0x71, 0xe5, 0x09, 0xe3, 0xfd, 0x9b, 0x06, 0x0d, 0xdb, 0x20, 0xba, 0x5c, 0x51, 0xdc, 0xc5, 0x94, 0x8d, 0x46, 0xfb, 0xf6, 0x40, 0xdf, 0xe0, 0x44, 0x17, 0x82, 0xca, 0xb8, 0x5f, 0xa4, 0xac 
};

static uint8_t scalar0[32] = {
0x7d, 0x7d, 0xc5, 0xf7, 0x1e, 0xb2, 0x9d, 0xda, 0xf8, 0x0d, 0x62, 0x14, 0x63, 0x2e, 0xea, 0xe0, 0x3d, 0x90, 0x58, 0xaf, 0x1f, 0xb6, 0xd2, 0x2e, 0xd8, 0x0b, 0xad, 0xb6, 0x2b, 0xc1, 0xa5, 0x34 

};


bool print_result(int in_len, uint8_t* comp, uint8_t* exp) {
  return compare_and_print(in_len, comp, exp);
}


#define ROUNDS 5000 //16384
#define SIZE   16384

bool testImplementationHacl()
{
	uint8_t* result = (uint8_t*) malloc (sizeof (uint8_t) * 64);
	bool flag = Hacl_P256_ecdsa_sign_p256_without_hash(result, 32, digest, prKey, nonce);
	bool s0 = compare_and_print(32, result, siggen_vectors_low5);
	bool s1 = compare_and_print(32, result + 32, siggen_vectors_low6);

    uint8_t* pubKey = (uint8_t*) malloc (sizeof (uint8_t) * 64);
    bool s2 = Hacl_P256_ecp256dh_i(pubKey, prKey);
    bool s3 = Hacl_P256_verify_q(pubKey);

    uint8_t* r = (uint8_t*) malloc (sizeof (uint8_t) * 32);
    uint8_t* s = (uint8_t*) malloc (sizeof (uint8_t) * 32);
    memcpy(r, result, 32);
    memcpy(s, result+32, 32);

    bool s4 = Hacl_P256_ecdsa_verif_without_hash(32, digest, pubKey, r, s);
    bool s5 = uECC_verify(pubKey, digest, 32, result, uECC_secp256r1 ());
	return s0 && s1 && s2 && s3 && s4 && s5 && flag;
}

void debug_print_buf(uint8_t* buf, size_t len) {
    for (size_t i = 0; i < len; i++)
        printf("%02x",buf[i]);
    printf("\n");
}

struct Result {
    clock_t clock;
    cycles cycles;
};

struct Result benchmarkP256Verification(cycles a, cycles b, clock_t t1, clock_t t2)
{
    uint8_t* sk = (uint8_t*) malloc (sizeof (uint8_t) * 32);
    memset(sk, 0x00, 32);
    while (!Hacl_P256_is_more_than_zero_less_than_order(sk)) {
        read_random_bytes(32, sk);
    };

    uint8_t* pk = (uint8_t*) malloc (sizeof (uint8_t) * 64);
    assert(Hacl_P256_ecp256dh_i(pk, sk));
    assert(Hacl_P256_verify_q(pk));

    uint8_t* k = (uint8_t*) malloc (sizeof (uint8_t) * 32);
    memset(k,0x00,32);
    while (!Hacl_P256_is_more_than_zero_less_than_order(k)) {
        read_random_bytes(32, k);
    };

    uint8_t* msg = (uint8_t*) malloc (sizeof (uint8_t) * 256);
    read_random_bytes(256, msg);

    uint8_t* sig = (uint8_t*) malloc (sizeof (uint8_t) * 64);
    memset(sig, 0x00, 64);
    assert(Hacl_P256_ecdsa_sign_p256_without_hash(sig, 256, msg, sk, k));

    uint8_t* r = (uint8_t*) malloc (sizeof (uint8_t) * 32);
    uint8_t* s = (uint8_t*) malloc (sizeof (uint8_t) * 32);
    memcpy(r, sig, 32);
    memcpy(s, sig+32, 32);

	t1 = clock();
  	a = cpucycles_begin();
    bool result = Hacl_P256_ecdsa_verif_without_hash(256, msg, pk, r, s);
	b = cpucycles_end();
	t2 = clock();
	clock_t tdiff = t2 - t1;
	cycles cdiff = b - a;

    assert(result);

    free(sk);
    free(pk);
    free(k);
    free(msg);
    free(sig);
    free(r);
    free(s);

    struct Result res = { tdiff, cdiff };
    return res;
}

struct Result benchmarkP256VerificationNoCheck(cycles a, cycles b, clock_t t1, clock_t t2)
{
    uint8_t* sk = (uint8_t*) malloc (sizeof (uint8_t) * 32);
    memset(sk, 0x00, 32);
    while (!Hacl_P256_is_more_than_zero_less_than_order(sk)) {
        read_random_bytes(32, sk);
    };

    uint8_t* pk = (uint8_t*) malloc (sizeof (uint8_t) * 64);
    assert(Hacl_P256_ecp256dh_i(pk, sk));
    assert(Hacl_P256_verify_q(pk));

    uint8_t* k = (uint8_t*) malloc (sizeof (uint8_t) * 32);
    memset(k,0x00,32);
    while (!Hacl_P256_is_more_than_zero_less_than_order(k)) {
        read_random_bytes(32, k);
    };

    uint8_t* msg = (uint8_t*) malloc (sizeof (uint8_t) * 256);
    read_random_bytes(256, msg);

    uint8_t* sig = (uint8_t*) malloc (sizeof (uint8_t) * 64);
    memset(sig, 0x00, 64);
    assert(Hacl_P256_ecdsa_sign_p256_without_hash(sig, 256, msg, sk, k));

    uint8_t* r = (uint8_t*) malloc (sizeof (uint8_t) * 32);
    uint8_t* s = (uint8_t*) malloc (sizeof (uint8_t) * 32);
    memcpy(r, sig, 32);
    memcpy(s, sig+32, 32);

	t1 = clock();
  	a = cpucycles_begin();
    bool result = Hacl_P256_ecdsa_verif_without_hash_no_check(256, msg, pk, r, s);
	b = cpucycles_end();
	t2 = clock();
	clock_t tdiff = t2 - t1;
	cycles cdiff = b - a;

    assert(result);

    free(sk);
    free(pk);
    free(k);
    free(msg);
    free(sig);
    free(r);
    free(s);

    struct Result res = { tdiff, cdiff };
    return res;
}


struct Result benchmarkUeccP256Verification(cycles a, cycles b, clock_t t1, clock_t t2)
{
    uint8_t* sk = (uint8_t*) malloc (sizeof (uint8_t) * 32);
    memset(sk, 0x00, 32);
    while (!Hacl_P256_is_more_than_zero_less_than_order(sk)) {
        read_random_bytes(32, sk);
    };

    uint8_t* pk = (uint8_t*) malloc (sizeof (uint8_t) * 64);
    assert(Hacl_P256_ecp256dh_i(pk, sk));
    assert(Hacl_P256_verify_q(pk));

    uint8_t* k = (uint8_t*) malloc (sizeof (uint8_t) * 32);
    memset(k,0x00,32);
    while (!Hacl_P256_is_more_than_zero_less_than_order(k)) {
        read_random_bytes(32, k);
    };

    uint8_t* msg = (uint8_t*) malloc (sizeof (uint8_t) * 256);
    read_random_bytes(256, msg);

    uint8_t* sig = (uint8_t*) malloc (sizeof (uint8_t) * 64);
    memset(sig, 0x00, 64);
    assert(Hacl_P256_ecdsa_sign_p256_without_hash(sig, 256, msg, sk, k));

	t1 = clock();
  	a = cpucycles_begin();
    int result = uECC_verify(pk, msg, 256, sig, uECC_secp256r1 ());
	b = cpucycles_end();
	t2 = clock();
	clock_t tdiff = t2 - t1;
	cycles cdiff = b - a;

    assert(result == 1);

    free(sk);
    free(pk);
    free(k);
    free(msg);
    free(sig);

    struct Result res = { tdiff, cdiff };
    return res;
}

struct Result benchmarkUeccP256VerificationValidation(cycles a, cycles b, clock_t t1, clock_t t2)
{
    uint8_t* sk = (uint8_t*) malloc (sizeof (uint8_t) * 32);
    memset(sk, 0x00, 32);
    while (!Hacl_P256_is_more_than_zero_less_than_order(sk)) {
        read_random_bytes(32, sk);
    };

    uint8_t* pk = (uint8_t*) malloc (sizeof (uint8_t) * 64);
    assert(Hacl_P256_ecp256dh_i(pk, sk));
    assert(Hacl_P256_verify_q(pk));

    uint8_t* k = (uint8_t*) malloc (sizeof (uint8_t) * 32);
    memset(k,0x00,32);
    while (!Hacl_P256_is_more_than_zero_less_than_order(k)) {
        read_random_bytes(32, k);
    };

    uint8_t* msg = (uint8_t*) malloc (sizeof (uint8_t) * 256);
    read_random_bytes(256, msg);

    uint8_t* sig = (uint8_t*) malloc (sizeof (uint8_t) * 64);
    memset(sig, 0x00, 64);
    assert(Hacl_P256_ecdsa_sign_p256_without_hash(sig, 256, msg, sk, k));

	t1 = clock();
  	a = cpucycles_begin();
    assert(uECC_valid_public_key(pk, uECC_secp256r1 ()) == 1);
    int result = uECC_verify(pk, msg, 256, sig, uECC_secp256r1 ());
	b = cpucycles_end();
	t2 = clock();
	clock_t tdiff = t2 - t1;
	cycles cdiff = b - a;

    assert(result == 1);

    free(sk);
    free(pk);
    free(k);
    free(msg);
    free(sig);

    struct Result res = { tdiff, cdiff };
    return res;
}


void handleErrors()
{
	printf("%s\n", "OpenSSl exception");
}

int main()
{
	if (!testImplementationHacl())
	{
		printf("%s\n", "Test Implementation failed for Hacl* ECDSA");
		return -1;
	}

  	cycles a,b;
	clock_t t1,t2;

    struct Result total_res_hacl = { 0, 0 };

  	for (int j = 0; j < ROUNDS; j++) {
        struct Result res = benchmarkP256Verification(a, b, t1, t2);
        total_res_hacl.clock += res.clock;
        total_res_hacl.cycles += res.cycles;
    }

    struct Result total_res_hacl_no_check = { 0, 0 };

  	for (int j = 0; j < ROUNDS; j++) {
        struct Result res = benchmarkP256VerificationNoCheck(a, b, t1, t2);
        total_res_hacl_no_check.clock += res.clock;
        total_res_hacl_no_check.cycles += res.cycles;
    }

    struct Result total_res_uecc = { 0, 0 };

  	for (int j = 0; j < ROUNDS; j++) {
        struct Result res = benchmarkUeccP256Verification(a, b, t1, t2);
        total_res_uecc.clock += res.clock;
        total_res_uecc.cycles += res.cycles;
    }

    struct Result total_res_uecc_validation = { 0, 0 };

  	for (int j = 0; j < ROUNDS; j++) {
        struct Result res = benchmarkUeccP256VerificationValidation(a, b, t1, t2);
        total_res_uecc_validation.clock += res.clock;
        total_res_uecc_validation.cycles += res.cycles;
    }


	uint8_t* result = (uint8_t*) malloc (sizeof (uint8_t) * 64);

	uint64_t len = SIZE;
	uint8_t plain[SIZE];
	memset(plain,'P',SIZE);

  	for (int j = 0; j < ROUNDS; j++)
		Hacl_P256_ecdsa_sign_p256_without_hash(plain, 32, plain, prKey, nonce);

	t1 = clock();
  	a = cpucycles_begin();

  	for (int j = 0; j < ROUNDS; j++)
		Hacl_P256_ecdsa_sign_p256_without_hash(plain, 32, plain, prKey, nonce);

	b = cpucycles_end();

	t2 = clock();
	clock_t tdiff1 = t2 - t1;
	cycles cdiff1 = b - a;


	uint8_t* pk = (uint8_t*) malloc (sizeof (uint8_t) * 64);
	memcpy(pk, px0_0,  32);
	memcpy(pk+32, py0_0,  32);
	uint64_t res = 0;


	for (int j = 0; j < ROUNDS; j++)
	{
		res ^= scalar0[0] ^ scalar0[31];
	}

	t1 = clock();
	a = cpucycles_begin();

	for (int j = 0; j < ROUNDS; j++)
	{
		Hacl_P256_ecp256dh_r(pk, pk, scalar0);
	    res ^= scalar0[0] ^ scalar0[31];
	}

	b = cpucycles_end();
	t2 = clock();
	clock_t tdiff3 = t2 - t1;
	cycles cdiff3 = b - a;



	uint64_t count = ROUNDS * SIZE;
	printf("Hacl ECDSA (without hashing) PERF: %d\n");
	print_time(count,tdiff1,cdiff1);

	printf("Hacl ECDH PERF: %d\n");
	print_time(count,tdiff3,cdiff3);

    printf("Hacl_P256_ecdsa_verif_without_hash randomized\n");
    print_time(count, total_res_hacl.clock, total_res_hacl.cycles);
    printf("avg time per function call: %" PRIu64 " ms\n", (uint64_t)total_res_hacl.clock/ROUNDS);

    printf("Hacl_P256_ecdsa_verif_without_hash_no_check randomized\n");
    print_time(count, total_res_hacl_no_check.clock, total_res_hacl_no_check.cycles);
    printf("avg time per function call: %" PRIu64 " ms\n", (uint64_t)total_res_hacl_no_check.clock/ROUNDS);

    printf("uECC_verify randomized\n");
    print_time(count, total_res_uecc.clock, total_res_uecc.cycles);
    printf("avg time per function call: %" PRIu64 " ms \n", (uint64_t)total_res_uecc.clock/ROUNDS);

    printf("uECC_verify + validate randomized\n");
    print_time(count, total_res_uecc_validation.clock, total_res_uecc_validation.cycles);
    printf("avg time per function call: %" PRIu64 " ms \n", (uint64_t)total_res_uecc_validation.clock/ROUNDS);

}
