/* Execute the unchanged upstream generator. No SIGIL implementation is linked. */
#include <inttypes.h>
#include <stdio.h>
#include <stdlib.h>
#include "upstream/pcg_basic.h"

int main(int argc, char **argv) {
    if (argc != 4) return 2;
    uint64_t seed = strtoull(argv[1], NULL, 10);
    uint64_t stream = strtoull(argv[2], NULL, 10);
    uint64_t bound = strtoull(argv[3], NULL, 10);
    if (stream > UINT64_MAX / 2 || bound > UINT64_C(4294967296)) return 2;
    pcg32_random_t rng;
    pcg32_srandom_r(&rng, seed, stream);
    printf("%" PRIu64 " %" PRIu64 "\n", rng.state, rng.inc);
    for (int i = 0; i < 12; ++i) {
        uint32_t value = bound == 0 || bound == UINT64_C(4294967296)
            ? pcg32_random_r(&rng)
            : pcg32_boundedrand_r(&rng, (uint32_t)bound);
        printf("%" PRIu32 " %" PRIu64 "\n", value, rng.state);
    }
    return 0;
}
