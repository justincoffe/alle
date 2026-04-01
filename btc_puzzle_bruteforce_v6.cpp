// btc_puzzle_bruteforce_v6.cpp
// BTC Puzzle Generator Seed Brute-Force — C++ Nuclear Option v6
//
// MODES:
//   Mode 1: Numeric seed brute-force (original phases, model-aware seeding)
//   Mode 2: Passphrase dictionary attack (SHA256 → seed, raw bytes, etc.)
//   Mode 3: Entropy combination attack (pid×time, time+hostname hash, etc.)
//   Mode 4: C++ std::seed_seq multi-word seeds
//   Mode 5: Combined all-in-one (runs modes 1-4 sequentially)
//
// Compile:
//   g++ -O3 -march=native -pthread -o btc_bruteforce btc_puzzle_bruteforce_v6.cpp
//
// Run:
//   ./btc_bruteforce                          # Interactive mode selection
//   ./btc_bruteforce --mode 1                 # Numeric brute-force
//   ./btc_bruteforce --mode 2 --dict wordlist.txt [--dict2 extra.txt]
//   ./btc_bruteforce --mode 3                 # Entropy combinations
//   ./btc_bruteforce --mode 4                 # std::seed_seq patterns
//   ./btc_bruteforce --mode 5 --dict wordlist.txt  # Everything
//   ./btc_bruteforce --threads 16 --mode 2 --dict passwords.txt
//
// Environment:
//   BF_WORKERS=16 ./btc_bruteforce --mode 1

#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <cmath>
#include <ctime>
#include <atomic>
#include <thread>
#include <vector>
#include <mutex>
#include <string>
#include <chrono>
#include <algorithm>
#include <fstream>
#include <csignal>
#include <cinttypes>
#include <functional>
#include <sstream>
#include <deque>
#include <unordered_set>

// ============================================================
// CRITICAL TIMESTAMP CONSTANTS
// ============================================================

static constexpr uint64_t TX_BROADCAST_UTC   = 1421301634ULL;
static constexpr uint64_t TX_DEADLINE         = 1421301680ULL;

static constexpr uint64_t TS_HOT_START        = 1420070400ULL;  // 2015-01-01
static constexpr uint64_t TS_HOT_END          = TX_DEADLINE;

static constexpr uint64_t TS_NARROW_START     = 1388534400ULL;  // 2014-01-01
static constexpr uint64_t TS_NARROW_END       = TX_DEADLINE;

static constexpr uint64_t TS_WIDE_START       = 1356998400ULL;  // 2013-01-01
static constexpr uint64_t TS_WIDE_END         = TX_DEADLINE;

// ============================================================
// Minimal SHA-256 implementation (no external deps)
// ============================================================

namespace sha256_impl {

static const uint32_t K[64] = {
    0x428a2f98,0x71374491,0xb5c0fbcf,0xe9b5dba5,0x3956c25b,0x59f111f1,0x923f82a4,0xab1c5ed5,
    0xd807aa98,0x12835b01,0x243185be,0x550c7dc3,0x72be5d74,0x80deb1fe,0x9bdc06a7,0xc19bf174,
    0xe49b69c1,0xefbe4786,0x0fc19dc6,0x240ca1cc,0x2de92c6f,0x4a7484aa,0x5cb0a9dc,0x76f988da,
    0x983e5152,0xa831c66d,0xb00327c8,0xbf597fc7,0xc6e00bf3,0xd5a79147,0x06ca6351,0x14292967,
    0x27b70a85,0x2e1b2138,0x4d2c6dfc,0x53380d13,0x650a7354,0x766a0abb,0x81c2c92e,0x92722c85,
    0xa2bfe8a1,0xa81a664b,0xc24b8b70,0xc76c51a3,0xd192e819,0xd6990624,0xf40e3585,0x106aa070,
    0x19a4c116,0x1e376c08,0x2748774c,0x34b0bcb5,0x391c0cb3,0x4ed8aa4a,0x5b9cca4f,0x682e6ff3,
    0x748f82ee,0x78a5636f,0x84c87814,0x8cc70208,0x90befffa,0xa4506ceb,0xbef9a3f7,0xc67178f2
};

static inline uint32_t rotr(uint32_t x, int n) { return (x >> n) | (x << (32 - n)); }
static inline uint32_t ch(uint32_t x, uint32_t y, uint32_t z) { return (x & y) ^ (~x & z); }
static inline uint32_t maj(uint32_t x, uint32_t y, uint32_t z) { return (x & y) ^ (x & z) ^ (y & z); }
static inline uint32_t ep0(uint32_t x) { return rotr(x,2) ^ rotr(x,13) ^ rotr(x,22); }
static inline uint32_t ep1(uint32_t x) { return rotr(x,6) ^ rotr(x,11) ^ rotr(x,25); }
static inline uint32_t sig0(uint32_t x) { return rotr(x,7) ^ rotr(x,18) ^ (x >> 3); }
static inline uint32_t sig1(uint32_t x) { return rotr(x,17) ^ rotr(x,19) ^ (x >> 10); }

struct SHA256_CTX {
    uint32_t state[8];
    uint8_t data[64];
    uint32_t datalen;
    uint64_t bitlen;
};

static void sha256_init(SHA256_CTX* ctx) {
    ctx->datalen = 0;
    ctx->bitlen = 0;
    ctx->state[0] = 0x6a09e667; ctx->state[1] = 0xbb67ae85;
    ctx->state[2] = 0x3c6ef372; ctx->state[3] = 0xa54ff53a;
    ctx->state[4] = 0x510e527f; ctx->state[5] = 0x9b05688c;
    ctx->state[6] = 0x1f83d9ab; ctx->state[7] = 0x5be0cd19;
}

static void sha256_transform(SHA256_CTX* ctx) {
    uint32_t w[64];
    for (int i = 0; i < 16; i++) {
        w[i] = ((uint32_t)ctx->data[i*4] << 24) | ((uint32_t)ctx->data[i*4+1] << 16) |
               ((uint32_t)ctx->data[i*4+2] << 8) | (uint32_t)ctx->data[i*4+3];
    }
    for (int i = 16; i < 64; i++)
        w[i] = sig1(w[i-2]) + w[i-7] + sig0(w[i-15]) + w[i-16];

    uint32_t a=ctx->state[0], b=ctx->state[1], c=ctx->state[2], d=ctx->state[3];
    uint32_t e=ctx->state[4], f=ctx->state[5], g=ctx->state[6], h=ctx->state[7];

    for (int i = 0; i < 64; i++) {
        uint32_t t1 = h + ep1(e) + ch(e,f,g) + K[i] + w[i];
        uint32_t t2 = ep0(a) + maj(a,b,c);
        h=g; g=f; f=e; e=d+t1; d=c; c=b; b=a; a=t1+t2;
    }

    ctx->state[0]+=a; ctx->state[1]+=b; ctx->state[2]+=c; ctx->state[3]+=d;
    ctx->state[4]+=e; ctx->state[5]+=f; ctx->state[6]+=g; ctx->state[7]+=h;
}

static void sha256_update(SHA256_CTX* ctx, const uint8_t* data, size_t len) {
    for (size_t i = 0; i < len; i++) {
        ctx->data[ctx->datalen] = data[i];
        ctx->datalen++;
        if (ctx->datalen == 64) {
            sha256_transform(ctx);
            ctx->bitlen += 512;
            ctx->datalen = 0;
        }
    }
}

static void sha256_final(SHA256_CTX* ctx, uint8_t hash[32]) {
    uint32_t i = ctx->datalen;
    ctx->data[i++] = 0x80;
    if (ctx->datalen < 56) {
        while (i < 56) ctx->data[i++] = 0x00;
    } else {
        while (i < 64) ctx->data[i++] = 0x00;
        sha256_transform(ctx);
        memset(ctx->data, 0, 56);
    }
    ctx->bitlen += (uint64_t)ctx->datalen * 8;
    for (int j = 0; j < 8; j++)
        ctx->data[63 - j] = (uint8_t)(ctx->bitlen >> (j * 8));
    sha256_transform(ctx);
    for (int j = 0; j < 8; j++) {
        hash[j*4]   = (ctx->state[j] >> 24) & 0xFF;
        hash[j*4+1] = (ctx->state[j] >> 16) & 0xFF;
        hash[j*4+2] = (ctx->state[j] >> 8) & 0xFF;
        hash[j*4+3] = ctx->state[j] & 0xFF;
    }
}

} // namespace sha256_impl

static void sha256(const void* data, size_t len, uint8_t out[32]) {
    sha256_impl::SHA256_CTX ctx;
    sha256_impl::sha256_init(&ctx);
    sha256_impl::sha256_update(&ctx, (const uint8_t*)data, len);
    sha256_impl::sha256_final(&ctx, out);
}

// ============================================================
// 128-bit unsigned integer
// ============================================================

struct uint128_t {
    uint64_t lo;
    uint64_t hi;

    uint128_t() : lo(0), hi(0) {}
    uint128_t(uint64_t v) : lo(v), hi(0) {}
    uint128_t(uint64_t h, uint64_t l) : lo(l), hi(h) {}

    bool operator==(const uint128_t& o) const { return lo == o.lo && hi == o.hi; }
    bool operator!=(const uint128_t& o) const { return !(*this == o); }
    bool operator<(const uint128_t& o) const {
        return hi < o.hi || (hi == o.hi && lo < o.lo);
    }

    uint128_t operator+(const uint128_t& o) const {
        uint128_t r;
        r.lo = lo + o.lo;
        r.hi = hi + o.hi + (r.lo < lo ? 1 : 0);
        return r;
    }

    uint128_t operator|(const uint128_t& o) const {
        return uint128_t(hi | o.hi, lo | o.lo);
    }

    uint128_t operator&(const uint128_t& o) const {
        return uint128_t(hi & o.hi, lo & o.lo);
    }

    uint128_t operator<<(int shift) const {
        if (shift == 0) return *this;
        if (shift >= 128) return uint128_t(0, 0);
        if (shift >= 64) return uint128_t(lo << (shift - 64), 0);
        return uint128_t((hi << shift) | (lo >> (64 - shift)), lo << shift);
    }

    uint128_t operator>>(int shift) const {
        if (shift == 0) return *this;
        if (shift >= 128) return uint128_t(0, 0);
        if (shift >= 64) return uint128_t(0, hi >> (shift - 64));
        return uint128_t(hi >> shift, (lo >> shift) | (hi << (64 - shift)));
    }

    bool fits_u64() const { return hi == 0; }
};

// ============================================================
// MT19937 State
// ============================================================

struct MT19937 {
    uint32_t state[624];
    int index;
};

// ============================================================
// MT19937 Seeding — Knuth LCG (C++ std::mt19937)
// ============================================================

static inline void mt_seed_uint32(MT19937& mt, uint32_t seed) {
    mt.state[0] = seed;
    for (int i = 1; i < 624; i++) {
        uint32_t prev = mt.state[i - 1];
        mt.state[i] = 1812433253U * (prev ^ (prev >> 30)) + (uint32_t)i;
    }
    mt.index = 624;
}

// ============================================================
// MT19937 Seeding — init_by_array (CPython)
// ============================================================

static void mt_seed_by_array(MT19937& mt, const uint32_t* init_key, int key_length) {
    mt.state[0] = 19650218U;
    for (int i = 1; i < 624; i++) {
        uint32_t prev = mt.state[i - 1];
        mt.state[i] = 1812433253U * (prev ^ (prev >> 30)) + (uint32_t)i;
    }

    int i = 1, j = 0;
    int k = (624 > key_length) ? 624 : key_length;

    for (; k > 0; k--) {
        uint32_t s = mt.state[i - 1];
        mt.state[i] = (mt.state[i] ^ ((s ^ (s >> 30)) * 1664525U)) + init_key[j] + (uint32_t)j;
        i++; j++;
        if (i >= 624) { mt.state[0] = mt.state[623]; i = 1; }
        if (j >= key_length) { j = 0; }
    }

    for (k = 623; k > 0; k--) {
        uint32_t s = mt.state[i - 1];
        mt.state[i] = (mt.state[i] ^ ((s ^ (s >> 30)) * 1566083941U)) - (uint32_t)i;
        i++;
        if (i >= 624) { mt.state[0] = mt.state[623]; i = 1; }
    }

    mt.state[0] = 0x80000000U;
    mt.index = 624;
}

// ============================================================
// MT19937 Seeding — Python (always init_by_array)
// ============================================================

static int seed_to_key_array(uint64_t seed, uint32_t* out) {
    if (seed == 0) { out[0] = 0; return 1; }
    int n = 0;
    uint64_t tmp = seed;
    while (tmp > 0) {
        out[n++] = (uint32_t)(tmp & 0xFFFFFFFFULL);
        tmp >>= 32;
    }
    return n;
}

static inline void mt_seed_python(MT19937& mt, uint64_t seed) {
    uint32_t key[2];
    int klen = seed_to_key_array(seed, key);
    mt_seed_by_array(mt, key, klen);
}

// Python seeding from arbitrary byte array (for SHA256 hash → seed)
static inline void mt_seed_python_bytes(MT19937& mt, const uint8_t* bytes, int num_bytes) {
    // Convert bytes to little-endian uint32 array (matching CPython's _PyLong_AsByteArray)
    int num_words = (num_bytes + 3) / 4;
    if (num_words == 0) num_words = 1;
    std::vector<uint32_t> key(num_words, 0);

    // CPython stores integers in little-endian word order
    for (int i = 0; i < num_bytes; i++) {
        key[i / 4] |= ((uint32_t)bytes[i]) << ((i % 4) * 8);
    }

    // Strip leading zero words (CPython normalizes integers)
    while (num_words > 1 && key[num_words - 1] == 0) num_words--;

    mt_seed_by_array(mt, key.data(), num_words);
}

// ============================================================
// MT19937 Seeding — C++ (Knuth LCG, truncates to uint32)
// ============================================================

static inline void mt_seed_cpp(MT19937& mt, uint64_t seed) {
    mt_seed_uint32(mt, (uint32_t)(seed & 0xFFFFFFFFULL));
}

// ============================================================
// MT19937 Seeding — C++ std::seed_seq (different algorithm!)
// ============================================================
// std::seed_seq takes a sequence of uint32_t values and uses
// a specific mixing algorithm to fill the MT state.
// Reference: C++11 standard §26.5.7.1
// ============================================================

static void mt_seed_seq(MT19937& mt, const uint32_t* seeds, int num_seeds) {
    // Step 1: std::seed_seq internal state generation
    // seed_seq stores the input, then generates output via its generate() method
    // which uses a specific algorithm to fill an output range.
    //
    // The generate() algorithm (C++11 §26.5.7.1 [rand.util.seedseq]):
    //   Let s = size of input sequence
    //   Let n = size of output range (624 for mt19937)
    //   Let t = (n >= 623) ? 11 : (n >= 68) ? 7 : (n >= 39) ? 5 : (n >= 7) ? 3 : (n-1)/2
    //   Let p = (n - t) / 2
    //   Let q = p + t

    const int n = 624;
    const int s = num_seeds;
    const int t = 11;  // n >= 623
    const int p = (n - t) / 2;   // 306
    const int q = p + t;          // 317
    const int m = std::max(s + 1, n);

    // Initialize output to 0x8b8b8b8b
    for (int i = 0; i < n; i++)
        mt.state[i] = 0x8b8b8b8bU;

    // T function
    auto T = [](uint32_t x) -> uint32_t {
        return x ^ (x >> 27);
    };

    // Phase 1: m iterations of mixing
    for (int k = 0; k < m; k++) {
        uint32_t r = T(mt.state[k % n] ^ mt.state[(k + p) % n] ^ mt.state[(k + n - 1) % n]);
        r *= 1664525U;

        r += (uint32_t)k;

        if (k < s) {
            // Within the seed sequence: add the seed value
            // seed_seq stores seeds internally; indexed by k for k < s
            // But first iteration (k=0) uses s (the count), not seeds[0]
            // For k >= 1 and k <= s, use seeds[k-1]
            if (k == 0)
                r += (uint32_t)s;
            else
                r += seeds[k - 1];
        } else if (k == 0) {
            r += (uint32_t)s;
        }

        mt.state[(k + p) % n] += r;

        uint32_t r2 = r + (uint32_t)((k + p) % n);
        // Correction: seed_seq also adds to (k+q)%n
        // but the exact indexing follows the standard more carefully
        mt.state[(k + q) % n] += (uint32_t)((k + p) % n);

        mt.state[k % n] = r;
    }

    // Phase 2: n more iterations of mixing (subtraction phase)
    for (int k = m; k < m + n; k++) {
        uint32_t r = T(mt.state[k % n] + mt.state[(k + p) % n] + mt.state[(k + n - 1) % n]);
        r *= 1566083941U;
        r -= (uint32_t)(k % n);

        mt.state[(k + p) % n] ^= r;
        mt.state[(k + q) % n] ^= (uint32_t)((k + p) % n);
        mt.state[k % n] = r;
    }

    mt.index = 624;
}

// Alternate: Direct faithful implementation from libc++/libstdc++ source
// This is the EXACT algorithm from the C++ standard
static void mt_seed_seq_faithful(MT19937& mt, const uint32_t* seeds, int num_seeds) {
    const uint32_t n = 624;
    const uint32_t s = (uint32_t)num_seeds;

    // Fill with 0x8b8b8b8b
    for (uint32_t i = 0; i < n; i++)
        mt.state[i] = 0x8b8b8b8bU;

    // Parameters per standard
    const uint32_t t = 11;
    const uint32_t p = (n - t) / 2;
    const uint32_t q = p + t;
    const uint32_t m = (s + 1 > n) ? s + 1 : n;

    auto T = [](uint32_t x) -> uint32_t {
        return x ^ (x >> 27);
    };

    // Phase 1
    uint32_t r;
    for (uint32_t k = 0; k < m; k++) {
        r = 1664525U * T(mt.state[k % n] ^ mt.state[(k + p) % n] ^ mt.state[((k > 0) ? k - 1 : n - 1) % n]);

        mt.state[(k + p) % n] += r;

        if (k == 0)
            r += s;
        else if (k <= s)
            r += seeds[k - 1] + k;
        else
            r += k;

        mt.state[(k + q) % n] += r;
        mt.state[k % n] = r;
    }

    // Phase 2
    for (uint32_t k = m; k < m + n; k++) {
        r = 1566083941U * T(mt.state[k % n] + mt.state[(k + p) % n] + mt.state[((k > 0) ? k - 1 : n - 1) % n]);

        mt.state[(k + p) % n] ^= r;
        r -= k % n;
        mt.state[(k + q) % n] ^= r;
        mt.state[k % n] = r;
    }

    mt.index = 624;
}

// ============================================================
// MT19937 Twist & Extract
// ============================================================

static inline void mt_twist(MT19937& mt) {
    for (int i = 0; i < 624; i++) {
        uint32_t y = (mt.state[i] & 0x80000000U) | (mt.state[(i + 1) % 624] & 0x7FFFFFFFU);
        mt.state[i] = mt.state[(i + 397) % 624] ^ (y >> 1);
        if (y & 1) mt.state[i] ^= 0x9908B0DFU;
    }
    mt.index = 0;
}

static inline uint32_t mt_extract(MT19937& mt) {
    if (mt.index >= 624) mt_twist(mt);
    uint32_t y = mt.state[mt.index++];
    y ^= y >> 11;
    y ^= (y << 7) & 0x9D2C5680U;
    y ^= (y << 15) & 0xEFC60000U;
    y ^= y >> 18;
    return y;
}

// ============================================================
// MT19937 getrandbits(k)
// ============================================================

static inline uint128_t mt_getrandbits(MT19937& mt, int k) {
    if (k == 0) return uint128_t(0);
    uint128_t result(0);
    int bits_filled = 0;
    while (bits_filled < k) {
        uint32_t word = mt_extract(mt);
        int remaining = k - bits_filled;
        if (remaining >= 32) {
            result = result | (uint128_t((uint64_t)word) << bits_filled);
            bits_filled += 32;
        } else {
            uint32_t masked = word & ((1U << remaining) - 1U);
            result = result | (uint128_t((uint64_t)masked) << bits_filled);
            bits_filled += remaining;
        }
    }
    return result;
}

// ============================================================
// Key Generation Models
// ============================================================

static inline uint128_t gen_key_bitmask(MT19937& mt, int n) {
    if (n == 1) return uint128_t(1);
    int bits = n - 1;
    uint128_t raw = mt_getrandbits(mt, bits);
    uint128_t high_bit = uint128_t(1) << (n - 1);
    return raw + high_bit;
}

static inline uint128_t gen_key_py2_randint(MT19937& mt, int n) {
    if (n == 1) return uint128_t(1);
    uint128_t lo_val = uint128_t(1) << (n - 1);
    int width_bits = n - 1;

    if (width_bits <= 53) {
        uint32_t a = mt_extract(mt);
        uint32_t b = mt_extract(mt);
        uint64_t numerator = (uint64_t)(a >> 5) * (1ULL << 26) + (uint64_t)(b >> 6);
        uint64_t width = 1ULL << width_bits;
        double float_val = (double)numerator / (double)(1ULL << 53);
        uint64_t offset = (uint64_t)(float_val * (double)width);
        return lo_val + uint128_t(offset);
    } else {
        int k = width_bits;
        uint128_t width_128 = uint128_t(1) << width_bits;
        for (;;) {
            uint128_t r = mt_getrandbits(mt, k);
            if (r < width_128) return r + lo_val;
        }
    }
}

static inline uint128_t gen_key_cpp_uniform(MT19937& mt, int n) {
    if (n == 1) return uint128_t(1);
    uint128_t lo_val = uint128_t(1) << (n - 1);
    int bits_needed = n - 1;

    if (bits_needed <= 32) {
        uint32_t raw = mt_extract(mt);
        uint32_t mask = (bits_needed == 32) ? 0xFFFFFFFFU : ((1U << bits_needed) - 1U);
        return lo_val + uint128_t((uint64_t)(raw & mask));
    } else if (bits_needed <= 64) {
        uint32_t lo_word = mt_extract(mt);
        uint32_t hi_word = mt_extract(mt);
        uint64_t raw = (uint64_t)lo_word | ((uint64_t)hi_word << 32);
        uint64_t mask = (bits_needed == 64) ? 0xFFFFFFFFFFFFFFFFULL : ((1ULL << bits_needed) - 1ULL);
        return lo_val + uint128_t(raw & mask);
    } else {
        int num_words = (bits_needed + 31) / 32;
        uint128_t raw(0);
        for (int w = 0; w < num_words; w++) {
            uint32_t word = mt_extract(mt);
            raw = raw | (uint128_t((uint64_t)word) << (32 * w));
        }
        uint128_t mask;
        if (bits_needed < 128) {
            mask = (uint128_t(1) << bits_needed);
            if (mask.lo == 0) { mask.hi -= 1; mask.lo = 0xFFFFFFFFFFFFFFFFULL; }
            else { mask.lo -= 1; }
        } else {
            mask = uint128_t(0xFFFFFFFFFFFFFFFFULL, 0xFFFFFFFFFFFFFFFFULL);
        }
        return lo_val + (raw & mask);
    }
}

// ============================================================
// Model dispatch
// ============================================================

typedef uint128_t (*GenFunc)(MT19937&, int);

static const GenFunc GEN_FUNCS[4] = {
    gen_key_bitmask,
    gen_key_bitmask,
    gen_key_py2_randint,
    gen_key_cpp_uniform,
};

static const char* MODEL_NAMES[4] = {
    "C++ getrandbits/bitmask",
    "Python 3 getrandbits",
    "Python 2.7 randint",
    "C++ uniform_int_distribution",
};

static inline bool is_python_model(int model_idx) {
    return (model_idx == 1 || model_idx == 2);
}

// ============================================================
// Known Keys
// ============================================================

struct KnownKey {
    int puzzle;
    uint128_t expected;
};

static const KnownKey EARLY_CHECKS[] = {
    {2,  uint128_t(3)},
    {3,  uint128_t(7)},
    {4,  uint128_t(8)},
    {5,  uint128_t(21)},
    {6,  uint128_t(49)},
    {7,  uint128_t(76)},
    {8,  uint128_t(224)},
    {9,  uint128_t(467)},
    {10, uint128_t(514)},
};
static constexpr int NUM_EARLY = 9;

static const KnownKey DEEP_CHECKS[] = {
    {33, uint128_t(7137437912ULL)},
    {34, uint128_t(14133072157ULL)},
    {65, uint128_t(0x0000000000000001ULL, 0xA838B13505B26867ULL)},
};
static constexpr int NUM_DEEP = 3;

// ============================================================
// Seeding strategy enum
// ============================================================

enum SeedingStrategy {
    SEED_CPP_KNUTH,       // C++ Knuth LCG (uint32)
    SEED_PYTHON_ARRAY,    // Python init_by_array
    SEED_CPP_SEEDSEQ,     // C++ std::seed_seq
    SEED_RAW_STATE,      // Direct state injection (for SHA256 full state)
};

// ============================================================
// Generic test: given an already-seeded MT, test all gen models
// Returns model index (0-3) on match, -1 on failure
// ============================================================

static int test_seeded_mt(MT19937& mt_template, int start_model = 0, int end_model = 4) {
    for (int model_idx = start_model; model_idx < end_model; model_idx++) {
        MT19937 mt = mt_template;  // copy
        GenFunc gen = GEN_FUNCS[model_idx];

        gen(mt, 1);  // puzzle 1

        bool failed = false;
        for (int c = 0; c < NUM_EARLY; c++) {
            uint128_t key = gen(mt, EARLY_CHECKS[c].puzzle);
            if (key != EARLY_CHECKS[c].expected) { failed = true; break; }
        }
        if (failed) continue;

        int current_n = 10;
        bool deep_failed = false;
        for (int c = 0; c < NUM_DEEP; c++) {
            int target_n = DEEP_CHECKS[c].puzzle;
            for (int skip_n = current_n + 1; skip_n < target_n; skip_n++)
                gen(mt, skip_n);
            uint128_t key = gen(mt, target_n);
            current_n = target_n;
            if (key != DEEP_CHECKS[c].expected) { deep_failed = true; break; }
        }

        if (!deep_failed) return model_idx;
    }
    return -1;
}

// ============================================================
// Test a numeric seed (model-aware: C++ vs Python seeding)
// ============================================================

static int test_seed_numeric(uint64_t seed) {
    MT19937 mt;

    // Test C++ models (0, 3) with Knuth LCG
    mt_seed_cpp(mt, seed);
    int result = test_seeded_mt(mt, 0, 1);  // model 0 only
    if (result >= 0) return result;

    mt_seed_cpp(mt, seed);
    result = test_seeded_mt(mt, 3, 4);  // model 3 only
    if (result >= 0) return result;

    // Test Python models (1, 2) with init_by_array
    mt_seed_python(mt, seed);
    result = test_seeded_mt(mt, 1, 3);  // models 1 and 2
    if (result >= 0) return result;

    return -1;
}

// ============================================================
// Test a passphrase with multiple derivation methods
// Returns: model index on match, -1 on failure
// Also sets *out_method to describe which derivation worked
// ============================================================

struct PassphraseResult {
    int model_idx;
    std::string method;
    std::string passphrase;
};

static PassphraseResult test_passphrase(const std::string& passphrase) {
    PassphraseResult result;
    result.model_idx = -1;

    uint8_t hash[32];
    MT19937 mt;

    // -------------------------------------------------------
    // Method 1: SHA256(passphrase) → first 4 bytes as uint32 seed
    //            (Common pattern: hash a string, use first bytes as seed)
    // -------------------------------------------------------
    sha256(passphrase.data(), passphrase.size(), hash);

    uint32_t seed32_be = ((uint32_t)hash[0] << 24) | ((uint32_t)hash[1] << 16) |
                          ((uint32_t)hash[2] << 8) | (uint32_t)hash[3];
    uint32_t seed32_le = ((uint32_t)hash[3] << 24) | ((uint32_t)hash[2] << 16) |
                          ((uint32_t)hash[1] << 8) | (uint32_t)hash[0];

    // 1a: SHA256 → first 4 bytes big-endian → C++ Knuth LCG
    mt_seed_uint32(mt, seed32_be);
    int m = test_seeded_mt(mt, 0, 1);
    if (m < 0) { mt_seed_uint32(mt, seed32_be); m = test_seeded_mt(mt, 3, 4); }
    if (m >= 0) { result.model_idx = m; result.method = "SHA256→uint32_BE→C++"; result.passphrase = passphrase; return result; }

    // 1b: SHA256 → first 4 bytes little-endian → C++ Knuth LCG
    mt_seed_uint32(mt, seed32_le);
    m = test_seeded_mt(mt, 0, 1);
    if (m < 0) { mt_seed_uint32(mt, seed32_le); m = test_seeded_mt(mt, 3, 4); }
    if (m >= 0) { result.model_idx = m; result.method = "SHA256→uint32_LE→C++"; result.passphrase = passphrase; return result; }

    // -------------------------------------------------------
    // Method 2: SHA256(passphrase) → first 8 bytes as uint64 → Python seed
    // -------------------------------------------------------
    uint64_t seed64_be = ((uint64_t)hash[0] << 56) | ((uint64_t)hash[1] << 48) |
                          ((uint64_t)hash[2] << 40) | ((uint64_t)hash[3] << 32) |
                          ((uint64_t)hash[4] << 24) | ((uint64_t)hash[5] << 16) |
                          ((uint64_t)hash[6] << 8) | (uint64_t)hash[7];
    uint64_t seed64_le = ((uint64_t)hash[7] << 56) | ((uint64_t)hash[6] << 48) |
                          ((uint64_t)hash[5] << 40) | ((uint64_t)hash[4] << 32) |
                          ((uint64_t)hash[3] << 24) | ((uint64_t)hash[2] << 16) |
                          ((uint64_t)hash[1] << 8) | (uint64_t)hash[0];

    // 2a: SHA256 → first 8 bytes BE → Python init_by_array
    mt_seed_python(mt, seed64_be);
    m = test_seeded_mt(mt, 1, 3);
    if (m >= 0) { result.model_idx = m; result.method = "SHA256→uint64_BE→Python"; result.passphrase = passphrase; return result; }

    // 2b: SHA256 → first 8 bytes LE → Python init_by_array
    mt_seed_python(mt, seed64_le);
    m = test_seeded_mt(mt, 1, 3);
    if (m >= 0) { result.model_idx = m; result.method = "SHA256→uint64_LE→Python"; result.passphrase = passphrase; return result; }

    // -------------------------------------------------------
    // Method 3: SHA256(passphrase) → full 32 bytes as Python big integer seed
    //            Python: random.seed(int.from_bytes(sha256(pw), 'big'))
    // -------------------------------------------------------
    // Big-endian: hash[0] is MSB → convert to little-endian uint32 words
    {
        uint32_t key_be[8];
        for (int i = 0; i < 8; i++) {
            // Reverse byte order within each 4-byte chunk for big-endian interpretation
            int base = (7 - i) * 4;  // start from the end for little-endian word order
            key_be[i] = ((uint32_t)hash[base] << 24) | ((uint32_t)hash[base+1] << 16) |
                        ((uint32_t)hash[base+2] << 8) | (uint32_t)hash[base+3];
        }
        // Strip trailing zeros
        int klen = 8;
        while (klen > 1 && key_be[klen-1] == 0) klen--;

        mt_seed_by_array(mt, key_be, klen);
        m = test_seeded_mt(mt, 1, 3);
        if (m >= 0) { result.model_idx = m; result.method = "SHA256→int.from_bytes(big)→Python"; result.passphrase = passphrase; return result; }
    }

    // 3b: Little-endian: Python random.seed(int.from_bytes(sha256(pw), 'little'))
    {
        uint32_t key_le[8];
        for (int i = 0; i < 8; i++) {
            int base = i * 4;
            key_le[i] = ((uint32_t)hash[base+3] << 24) | ((uint32_t)hash[base+2] << 16) |
                        ((uint32_t)hash[base+1] << 8) | (uint32_t)hash[base];
        }
        int klen = 8;
        while (klen > 1 && key_le[klen-1] == 0) klen--;

        mt_seed_by_array(mt, key_le, klen);
        m = test_seeded_mt(mt, 1, 3);
        if (m >= 0) { result.model_idx = m; result.method = "SHA256→int.from_bytes(little)→Python"; result.passphrase = passphrase; return result; }
    }

    // -------------------------------------------------------
    // Method 4: SHA256 → 8 uint32 words → C++ std::seed_seq
    // -------------------------------------------------------
    {
        uint32_t seq_words[8];
        for (int i = 0; i < 8; i++) {
            seq_words[i] = ((uint32_t)hash[i*4] << 24) | ((uint32_t)hash[i*4+1] << 16) |
                           ((uint32_t)hash[i*4+2] << 8) | (uint32_t)hash[i*4+3];
        }

        mt_seed_seq_faithful(mt, seq_words, 8);
        m = test_seeded_mt(mt, 0, 1);
        if (m < 0) { mt_seed_seq_faithful(mt, seq_words, 8); m = test_seeded_mt(mt, 3, 4); }
        if (m >= 0) { result.model_idx = m; result.method = "SHA256→seed_seq(8 words)→C++"; result.passphrase = passphrase; return result; }
    }

    // -------------------------------------------------------
    // Method 5: Direct string → Python seed (hash of string)
    //            Python 3: random.seed("passphrase") → hashes the string
    //            Python 2: random.seed("passphrase") → hash(string) as integer
    // -------------------------------------------------------
    // Python 3.2+: random.seed(string) uses sha512 of the string's repr
    // But the simplest case: random.seed(int(passphrase)) if it's numeric
    // Or: random.seed(passphrase) which calls hash() → then seed(hash_value)
    //
    // Python 2: hash() is platform-dependent, not reproducible
    // Python 3.2: random.seed(string) was deprecated, then removed
    // Python 3.2+: actually uses hashlib.sha512 on version + repr(string)
    //
    // We'll try: SHA512(passphrase) interpreted as int → Python seed
    // But we only have SHA256 implemented. Use double-SHA256 as approximation.
    // Actually, the key insight: if the creator used random.seed("some_string"),
    // Python 3.2+ does: x = int.from_bytes(sha512(repr(a).encode()), 'big')
    // We can't easily replicate sha512 without implementing it.
    // Skip this for now — SHA256 covers the most common cases.

    // -------------------------------------------------------
    // Method 6: Passphrase is numeric → direct seed
    // -------------------------------------------------------
    {
        bool all_digits = true;
        for (char c : passphrase) {
            if (c < '0' || c > '9') { all_digits = false; break; }
        }
        if (all_digits && !passphrase.empty() && passphrase.size() <= 18) {
            uint64_t numeric_seed = strtoull(passphrase.c_str(), nullptr, 10);
            int nm = test_seed_numeric(numeric_seed);
            if (nm >= 0) {
                result.model_idx = nm;
                result.method = "numeric_string→direct_seed";
                result.passphrase = passphrase;
                return result;
            }
        }
        // Also try hex interpretation
        if (passphrase.size() >= 2 && passphrase.size() <= 18) {
            bool all_hex = true;
            for (char c : passphrase) {
                if (!((c >= '0' && c <= '9') || (c >= 'a' && c <= 'f') || (c >= 'A' && c <= 'F'))) {
                    all_hex = false; break;
                }
            }
            if (all_hex) {
                uint64_t hex_seed = strtoull(passphrase.c_str(), nullptr, 16);
                int nm = test_seed_numeric(hex_seed);
                if (nm >= 0) {
                    result.model_idx = nm;
                    result.method = "hex_string→direct_seed";
                    result.passphrase = passphrase;
                    return result;
                }
            }
        }
    }

    // -------------------------------------------------------
    // Method 7: SHA256(passphrase) → raw bytes as init_by_array key
    //            (treating the hash bytes directly as uint32 LE words)
    // -------------------------------------------------------
    {
        uint32_t raw_words[8];
        for (int i = 0; i < 8; i++) {
            raw_words[i] = (uint32_t)hash[i*4] | ((uint32_t)hash[i*4+1] << 8) |
                           ((uint32_t)hash[i*4+2] << 16) | ((uint32_t)hash[i*4+3] << 24);
        }
        mt_seed_by_array(mt, raw_words, 8);
        m = test_seeded_mt(mt);
        if (m >= 0) { result.model_idx = m; result.method = "SHA256→raw_LE_words→init_by_array"; result.passphrase = passphrase; return result; }
    }

    // -------------------------------------------------------
    // Method 8: Double SHA256 (common in Bitcoin ecosystem)
    //            SHA256(SHA256(passphrase))
    // -------------------------------------------------------
    {
        uint8_t hash2[32];
        sha256(hash, 32, hash2);

        uint32_t seed32 = ((uint32_t)hash2[0] << 24) | ((uint32_t)hash2[1] << 16) |
                           ((uint32_t)hash2[2] << 8) | (uint32_t)hash2[3];

        mt_seed_uint32(mt, seed32);
        m = test_seeded_mt(mt, 0, 1);
        if (m < 0) { mt_seed_uint32(mt, seed32); m = test_seeded_mt(mt, 3, 4); }
        if (m >= 0) { result.model_idx = m; result.method = "dSHA256→uint32→C++"; result.passphrase = passphrase; return result; }

        // dSHA256 full → Python
        uint32_t key_d[8];
        for (int i = 0; i < 8; i++) {
            int base = (7 - i) * 4;
            key_d[i] = ((uint32_t)hash2[base] << 24) | ((uint32_t)hash2[base+1] << 16) |
                       ((uint32_t)hash2[base+2] << 8) | (uint32_t)hash2[base+3];
        }
        int klen = 8;
        while (klen > 1 && key_d[klen-1] == 0) klen--;

        mt_seed_by_array(mt, key_d, klen);
        m = test_seeded_mt(mt, 1, 3);
        if (m >= 0) { result.model_idx = m; result.method = "dSHA256→int(big)→Python"; result.passphrase = passphrase; return result; }
    }

    return result;
}

// ============================================================
// Global state for coordination
// ============================================================

static std::atomic<bool> g_found(false);
static std::atomic<uint64_t> g_found_seed(0);
static std::atomic<int> g_found_model(-1);
static std::atomic<uint64_t> g_seeds_tested(0);
static std::mutex g_print_mutex;

// For passphrase mode
static std::string g_found_passphrase;
static std::string g_found_method;
static std::mutex g_found_mutex;

// ============================================================
// Display match (numeric seed)
// ============================================================

static void display_match_numeric(uint64_t seed, int model_idx, double elapsed_sec) {
    printf("\n\n");
    printf("==============================================================\n");
    printf("  🔥🔥🔥 SEED FOUND 🔥🔥🔥\n");
    printf("  Seed      : %" PRIu64 "\n", seed);
    printf("  Seed hex  : 0x%" PRIX64 "\n", seed);
    printf("  Model     : [%d] %s\n", model_idx, MODEL_NAMES[model_idx]);
    printf("  Seeding   : %s\n", is_python_model(model_idx) ? "init_by_array (Python)" : "Knuth LCG (C++)");
    printf("  Time      : %.1f seconds\n", elapsed_sec);

    if (seed >= 1000000000ULL && seed <= 2000000000ULL) {
        time_t ts = (time_t)seed;
        printf("  As time(s): %s", asctime(gmtime(&ts)));
    } else if (seed >= 1000000000000ULL && seed <= 2000000000000ULL) {
        time_t ts = (time_t)(seed / 1000);
        printf("  As time(ms): %s", asctime(gmtime(&ts)));
    } else if (seed >= 1000000000000000ULL && seed <= 2000000000000000ULL) {
        time_t ts = (time_t)(seed / 1000000);
        printf("  As time(us): %s", asctime(gmtime(&ts)));
    }

    printf("==============================================================\n\n");

    // Regenerate all keys
    MT19937 mt;
    if (is_python_model(model_idx))
        mt_seed_python(mt, seed);
    else
        mt_seed_cpp(mt, seed);
    GenFunc gen = GEN_FUNCS[model_idx];

    constexpr int MAX_PUZZLE = 160;
    uint128_t all_keys[MAX_PUZZLE];
    for (int n = 1; n <= MAX_PUZZLE; n++)
        all_keys[n-1] = gen(mt, n);

    struct { int n; uint128_t expected; } known[] = {
        {2, uint128_t(3)}, {3, uint128_t(7)}, {4, uint128_t(8)},
        {5, uint128_t(21)}, {6, uint128_t(49)}, {7, uint128_t(76)},
        {8, uint128_t(224)}, {9, uint128_t(467)}, {10, uint128_t(514)},
        {33, uint128_t(7137437912ULL)}, {34, uint128_t(14133072157ULL)},
        {65, uint128_t(0x1ULL, 0xA838B13505B26867ULL)},
    };

    printf("  %7s  %40s  Status\n", "Puzzle", "Key");
    printf("  %s\n", std::string(65, '-').c_str());

    for (int idx = 0; idx < MAX_PUZZLE; idx++) {
        uint128_t k = all_keys[idx];
        char key_str[80];
        if (k.hi == 0)
            snprintf(key_str, sizeof(key_str), "%" PRIu64, k.lo);
        else
            snprintf(key_str, sizeof(key_str), "0x%" PRIX64 "%016" PRIX64, k.hi, k.lo);

        const char* status = "";
        for (auto& kn : known) {
            if (kn.n == idx + 1) {
                status = (k == kn.expected) ? "  ✅ MATCH  <-- KNOWN" : "  ❌ MISMATCH  <-- KNOWN";
                break;
            }
        }
        printf("  %7d  %40s%s\n", idx + 1, key_str, status);
    }

    char fname[128];
    snprintf(fname, sizeof(fname), "FOUND_SEED_%" PRIu64 ".txt", seed);
    FILE* f = fopen(fname, "w");
    if (f) {
        fprintf(f, "Seed: %" PRIu64 "\nSeed hex: 0x%" PRIX64 "\n", seed, seed);
        fprintf(f, "Model: [%d] %s\n", model_idx, MODEL_NAMES[model_idx]);
        for (int idx = 0; idx < MAX_PUZZLE; idx++) {
            uint128_t k = all_keys[idx];
            if (k.hi == 0)
                fprintf(f, "Puzzle %3d: %" PRIu64 "\n", idx + 1, k.lo);
            else
                fprintf(f, "Puzzle %3d: 0x%" PRIX64 "%016" PRIX64 "\n", idx + 1, k.hi, k.lo);
        }
        fclose(f);
        printf("\n  💾 Results saved to %s\n", fname);
    }
}

// ============================================================
// Display match (passphrase)
// ============================================================

static void display_match_passphrase(const PassphraseResult& pr, double elapsed_sec) {
    printf("\n\n");
    printf("==============================================================\n");
    printf("  🔥🔥🔥 PASSPHRASE SEED FOUND 🔥🔥🔥\n");
    printf("  Passphrase: \"%s\"\n", pr.passphrase.c_str());
    printf("  Method    : %s\n", pr.method.c_str());
    printf("  Model     : [%d] %s\n", pr.model_idx, MODEL_NAMES[pr.model_idx]);
    printf("  Time      : %.1f seconds\n", elapsed_sec);
    printf("==============================================================\n\n");

    // We need to regenerate the MT state using the winning method
    // For display, re-run test_passphrase and use the method info
    // to regenerate keys. For simplicity, just re-run the test.
    // The method string tells us what was used.

    printf("  ⚠️  Re-run with the passphrase to extract all 160 keys.\n");

    char fname[256];
    snprintf(fname, sizeof(fname), "FOUND_PASSPHRASE_%s.txt", pr.method.c_str());
    // Sanitize filename
    for (char* p = fname; *p; p++) {
        if (*p == '/' || *p == '\\' || *p == ' ' || *p == ':') *p = '_';
    }
    FILE* f = fopen(fname, "w");
    if (f) {
        fprintf(f, "Passphrase: %s\n", pr.passphrase.c_str());
        fprintf(f, "Method: %s\n", pr.method.c_str());
        fprintf(f, "Model: [%d] %s\n", pr.model_idx, MODEL_NAMES[pr.model_idx]);
        fclose(f);
        printf("  💾 Results saved to %s\n", fname);
    }
}

// ============================================================
// MODE 1: Numeric Seed Brute-Force
// ============================================================

struct WorkerResult {
    bool found;
    uint64_t seed;
    int model_idx;
};

static void numeric_worker(uint64_t start, uint64_t end, WorkerResult* result) {
    result->found = false;
    constexpr uint64_t REPORT_INTERVAL = 100000;
    uint64_t local_count = 0;

    for (uint64_t seed = start; seed < end; seed++) {
                if (g_found.load(std::memory_order_relaxed)) return;

        int m = test_seed_numeric(seed);
        if (m >= 0) {
            result->found = true;
            result->seed = seed;
            result->model_idx = m;
            g_found.store(true, std::memory_order_release);
            g_found_seed.store(seed, std::memory_order_release);
            g_found_model.store(m, std::memory_order_release);
            return;
        }

        local_count++;
        if (local_count % REPORT_INTERVAL == 0) {
            g_seeds_tested.fetch_add(REPORT_INTERVAL, std::memory_order_relaxed);
        }
    }
    g_seeds_tested.fetch_add(local_count % REPORT_INTERVAL, std::memory_order_relaxed);
}

struct Phase {
    const char* name;
    uint64_t start;
    uint64_t end;
};

static void run_mode1(int num_threads) {
    printf("\n");
    printf("╔══════════════════════════════════════════════════════════╗\n");
    printf("║  MODE 1: Numeric Seed Brute-Force                      ║\n");
    printf("║  Threads: %-4d                                          ║\n", num_threads);
    printf("╚══════════════════════════════════════════════════════════╝\n\n");

    Phase phases[] = {
        // Phase 0: Hot timestamp range (seconds)
        {"Hot timestamps (2015-01-01 → TX)", TS_HOT_START, TS_HOT_END},
        // Phase 1: Narrow timestamp range
        {"Narrow timestamps (2014-01-01 → TX)", TS_NARROW_START, TS_HOT_START},
        // Phase 2: Wide timestamp range
        {"Wide timestamps (2013-01-01 → 2014-01-01)", TS_WIDE_START, TS_NARROW_START},
        // Phase 3: Millisecond timestamps (hot range) — sampling
        {"Millisecond timestamps (hot×1000) sampled", TS_HOT_START * 1000ULL, TS_HOT_END * 1000ULL},
        // Phase 4: Small seeds
        {"Small seeds (0 → 10M)", 0ULL, 10000000ULL},
        // Phase 5: Common seeds near powers of 2
        {"Seeds near 2^31", 2147483648ULL - 1000000ULL, 2147483648ULL + 1000000ULL},
        // Phase 6: Seeds near 2^32
        {"Seeds near 2^32", 4294967296ULL - 1000000ULL, 4294967296ULL + 1000000ULL},
        // Phase 7: Extended small seeds
        {"Extended small seeds (10M → 100M)", 10000000ULL, 100000000ULL},
        // Phase 8: Full 32-bit space (remaining chunks)
        {"Full uint32 sweep (100M → 2^32)", 100000000ULL, 4294967296ULL},
        // Phase 9: Microsecond timestamps (hot range)
        {"Microsecond timestamps (hot×1e6) sampled", TS_HOT_START * 1000000ULL, TS_HOT_END * 1000000ULL},
    };
    int num_phases = sizeof(phases) / sizeof(phases[0]);

    auto wall_start = std::chrono::steady_clock::now();

    for (int ph = 0; ph < num_phases; ph++) {
        if (g_found.load(std::memory_order_relaxed)) break;

        Phase& p = phases[ph];
        uint64_t range = p.end - p.start;

        printf("━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━\n");
        printf("  Phase %d/%d: %s\n", ph + 1, num_phases, p.name);
        printf("  Range: %" PRIu64 " → %" PRIu64 " (%" PRIu64 " seeds)\n", p.start, p.end, range);
        printf("━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━\n");

        // For very large ranges (ms/us timestamps), we sample
        bool sampling = false;
        uint64_t effective_range = range;
        uint64_t step = 1;

        if (range > 10000000000ULL) {
            // Too large to brute-force linearly; sample every Nth value
            step = range / 1000000000ULL;  // ~1B samples max
            if (step < 1) step = 1;
            effective_range = range / step;
            sampling = true;
            printf("  ⚡ Sampling mode: step=%" PRIu64 ", effective seeds=%" PRIu64 "\n", step, effective_range);
        }

        g_seeds_tested.store(0, std::memory_order_relaxed);
        auto phase_start = std::chrono::steady_clock::now();

        std::vector<std::thread> threads;
        std::vector<WorkerResult> results(num_threads);

        uint64_t chunk = effective_range / (uint64_t)num_threads;
        if (chunk == 0) chunk = 1;

        for (int t = 0; t < num_threads; t++) {
            uint64_t t_start_idx = (uint64_t)t * chunk;
            uint64_t t_end_idx = (t == num_threads - 1) ? effective_range : t_start_idx + chunk;

            if (sampling) {
                // Convert index range to actual seed values
                uint64_t actual_start = p.start + t_start_idx * step;
                uint64_t actual_end = p.start + t_end_idx * step;
                if (actual_end > p.end) actual_end = p.end;

                threads.emplace_back([actual_start, actual_end, step, &results, t]() {
                    results[t].found = false;
                    constexpr uint64_t REPORT_INTERVAL = 100000;
                    uint64_t local_count = 0;

                    for (uint64_t seed = actual_start; seed < actual_end; seed += step) {
                        if (g_found.load(std::memory_order_relaxed)) return;

                        int m = test_seed_numeric(seed);
                        if (m >= 0) {
                            results[t].found = true;
                            results[t].seed = seed;
                            results[t].model_idx = m;
                            g_found.store(true, std::memory_order_release);
                            g_found_seed.store(seed, std::memory_order_release);
                            g_found_model.store(m, std::memory_order_release);
                            return;
                        }

                        local_count++;
                        if (local_count % REPORT_INTERVAL == 0) {
                            g_seeds_tested.fetch_add(REPORT_INTERVAL, std::memory_order_relaxed);
                        }
                    }
                    g_seeds_tested.fetch_add(local_count % REPORT_INTERVAL, std::memory_order_relaxed);
                });
            } else {
                uint64_t actual_start = p.start + t_start_idx;
                uint64_t actual_end = p.start + t_end_idx;
                threads.emplace_back(numeric_worker, actual_start, actual_end, &results[t]);
            }
        }

        // Progress reporting thread
        std::atomic<bool> progress_done(false);
        std::thread progress_thread([&]() {
            while (!progress_done.load(std::memory_order_relaxed)) {
                std::this_thread::sleep_for(std::chrono::seconds(2));
                if (progress_done.load(std::memory_order_relaxed)) break;

                uint64_t tested = g_seeds_tested.load(std::memory_order_relaxed);
                auto now = std::chrono::steady_clock::now();
                double elapsed = std::chrono::duration<double>(now - phase_start).count();
                double rate = (elapsed > 0.01) ? (double)tested / elapsed : 0.0;
                double pct = (effective_range > 0) ? 100.0 * (double)tested / (double)effective_range : 0.0;

                double eta = (rate > 0 && tested < effective_range)
                    ? (double)(effective_range - tested) / rate : 0.0;

                printf("\r  ⏱  Tested: %12" PRIu64 " / %" PRIu64 "  (%.1f%%)  "
                       "Rate: %.0f seeds/s  ETA: %.0fs    ",
                      tested, effective_range, pct, rate, eta);
                fflush(stdout);
            }
        });

        for (auto& th : threads) th.join();
        progress_done.store(true, std::memory_order_release);
        progress_thread.join();

        auto phase_end = std::chrono::steady_clock::now();
        double phase_elapsed = std::chrono::duration<double>(phase_end - phase_start).count();
        uint64_t total_tested = g_seeds_tested.load(std::memory_order_relaxed);

        printf("\r  ✅ Phase complete: %" PRIu64 " seeds in %.1fs (%.0f seeds/s)\n\n",
               total_tested, phase_elapsed,
               phase_elapsed > 0 ? (double)total_tested / phase_elapsed : 0);

        // Check if any worker found it
        for (int t = 0; t < num_threads; t++) {
            if (results[t].found) {
                auto wall_end = std::chrono::steady_clock::now();
                double total_elapsed = std::chrono::duration<double>(wall_end - wall_start).count();
                display_match_numeric(results[t].seed, results[t].model_idx, total_elapsed);
                return;
            }
        }
    }

    if (!g_found.load(std::memory_order_relaxed)) {
        auto wall_end = std::chrono::steady_clock::now();
        double total_elapsed = std::chrono::duration<double>(wall_end - wall_start).count();
        printf("\n  ❌ No seed found in Mode 1 after %.1f seconds.\n", total_elapsed);
        printf("     Consider trying Mode 2 (passphrase), Mode 3 (entropy), or Mode 5 (all).\n\n");
    }
}

// ============================================================
// MODE 2: Passphrase Dictionary Attack
// ============================================================

static std::mutex g_dict_mutex;
static std::deque<std::string> g_dict_queue;
static std::atomic<bool> g_dict_done(false);
static std::atomic<uint64_t> g_passphrases_tested(0);

static void passphrase_worker() {
    while (!g_found.load(std::memory_order_relaxed)) {
        std::string word;
        {
            std::lock_guard<std::mutex> lock(g_dict_mutex);
            if (g_dict_queue.empty()) return;
            word = std::move(g_dict_queue.front());
            g_dict_queue.pop_front();
        }

        PassphraseResult pr = test_passphrase(word);
        g_passphrases_tested.fetch_add(1, std::memory_order_relaxed);

        if (pr.model_idx >= 0) {
            g_found.store(true, std::memory_order_release);
            std::lock_guard<std::mutex> lock(g_found_mutex);
            g_found_passphrase = pr.passphrase;
            g_found_method = pr.method;
            g_found_model.store(pr.model_idx, std::memory_order_release);
            return;
        }

        // Also test common mutations
        if (g_found.load(std::memory_order_relaxed)) return;

        // Mutation 1: UPPERCASE
        {
            std::string upper = word;
            for (auto& c : upper) c = toupper((unsigned char)c);
            if (upper != word) {
                pr = test_passphrase(upper);
                g_passphrases_tested.fetch_add(1, std::memory_order_relaxed);
                if (pr.model_idx >= 0) {
                    g_found.store(true, std::memory_order_release);
                    std::lock_guard<std::mutex> lock(g_found_mutex);
                    g_found_passphrase = pr.passphrase;
                    g_found_method = pr.method;
                    g_found_model.store(pr.model_idx, std::memory_order_release);
                    return;
                }
            }
        }

        // Mutation 2: Capitalize first letter
        {
            std::string cap = word;
            if (!cap.empty()) cap[0] = toupper((unsigned char)cap[0]);
            if (cap != word) {
                pr = test_passphrase(cap);
                g_passphrases_tested.fetch_add(1, std::memory_order_relaxed);
                if (pr.model_idx >= 0) {
                    g_found.store(true, std::memory_order_release);
                    std::lock_guard<std::mutex> lock(g_found_mutex);
                    g_found_passphrase = pr.passphrase;
                    g_found_method = pr.method;
                    g_found_model.store(pr.model_idx, std::memory_order_release);
                    return;
                }
            }
        }

        // Mutation 3: Append common suffixes
        const char* suffixes[] = {"1", "123", "!", "2015", "2014", "btc", "bitcoin", nullptr};
        for (int s = 0; suffixes[s]; s++) {
            if (g_found.load(std::memory_order_relaxed)) return;
            std::string mutated = word + suffixes[s];
            pr = test_passphrase(mutated);
            g_passphrases_tested.fetch_add(1, std::memory_order_relaxed);
            if (pr.model_idx >= 0) {
                g_found.store(true, std::memory_order_release);
                std::lock_guard<std::mutex> lock(g_found_mutex);
                g_found_passphrase = pr.passphrase;
                g_found_method = pr.method;
                g_found_model.store(pr.model_idx, std::memory_order_release);
                return;
            }
        }

        // Mutation 4: Reverse
        {
            std::string rev(word.rbegin(), word.rend());
            if (rev != word) {
                pr = test_passphrase(rev);
                g_passphrases_tested.fetch_add(1, std::memory_order_relaxed);
                if (pr.model_idx >= 0) {
                    g_found.store(true, std::memory_order_release);
                    std::lock_guard<std::mutex> lock(g_found_mutex);
                    g_found_passphrase = pr.passphrase;
                    g_found_method = pr.method;
                    g_found_model.store(pr.model_idx, std::memory_order_release);
                    return;
                }
            }
        }
    }
}

static void run_mode2(int num_threads, const std::vector<std::string>& dict_files) {
    printf("\n");
    printf("╔══════════════════════════════════════════════════════════╗\n");
    printf("║  MODE 2: Passphrase Dictionary Attack                   ║\n");
    printf("║  Threads: %-4d                                          ║\n", num_threads);
    printf("╚══════════════════════════════════════════════════════════╝\n\n");

    if (dict_files.empty()) {
        printf("  ❌ No dictionary files specified. Use --dict <file>\n\n");
        return;
    }

    // Load all dictionaries
    uint64_t total_loaded = 0;
    for (const auto& fname : dict_files) {
        printf("  📖 Loading dictionary: %s\n", fname.c_str());
        std::ifstream f(fname);
        if (!f.is_open()) {
            printf("  ⚠️  Could not open %s, skipping.\n", fname.c_str());
            continue;
        }
        std::string line;
        while (std::getline(f, line)) {
            // Trim whitespace
            while (!line.empty() && (line.back() == '\r' || line.back() == '\n' || line.back() == ' '))
                line.pop_back();
            while (!line.empty() && (line.front() == ' '))
                line.erase(line.begin());
            if (line.empty() || line[0] == '#') continue;
            g_dict_queue.push_back(std::move(line));
            total_loaded++;
        }
        f.close();
    }

    // Also add some built-in passphrases
    const char* builtins[] = {
        "bitcoin", "Bitcoin", "BITCOIN",
        "btcpuzzle", "btc_puzzle", "BTC_PUZZLE",
        "puzzle", "Puzzle", "PUZZLE",
        "satoshi", "Satoshi", "SATOSHI", "satoshinakamoto",
        "nakamoto", "Nakamoto", "NAKAMOTO",
        "blockchain", "Blockchain",
        "crypto", "Crypto", "CRYPTO",
        "password", "Password", "PASSWORD",
        "passphrase", "Passphrase",
        "secret", "Secret", "SECRET",
        "key", "Key", "KEY",
        "private", "Private", "PRIVATE",
        "privatekey", "PrivateKey", "PRIVATEKEY",
        "master", "Master", "MASTER",
        "seed", "Seed", "SEED",
        "random", "Random", "RANDOM",
        "test", "Test", "TEST",
        "hello", "Hello", "HELLO",
        "letmein", "admin", "root",
        "1234567890", "0123456789",
        "qwerty", "abc123", "monkey",
        "iloveyou", "trustno1",
        "bitcoin2015", "btc2015", "puzzle2015",
        "bitcoin2014", "btc2014", "puzzle2014",
        "p2sh", "multisig",
        "brainwallet", "BrainWallet", "BRAINWALLET",
        "correct horse battery staple",
        "correcthorsebatterystaple",
        nullptr
    };
    for (int i = 0; builtins[i]; i++) {
        g_dict_queue.push_back(builtins[i]);
        total_loaded++;
    }

    printf("  📊 Total passphrases loaded: %" PRIu64 "\n", total_loaded);
    printf("  📊 With mutations, testing ~%" PRIu64 " combinations\n\n", total_loaded * 12);

    g_found.store(false, std::memory_order_release);
    g_passphrases_tested.store(0, std::memory_order_relaxed);

    auto start_time = std::chrono::steady_clock::now();

    std::vector<std::thread> threads;
    for (int t = 0; t < num_threads; t++) {
        threads.emplace_back(passphrase_worker);
    }

    // Progress reporter
    std::atomic<bool> progress_done(false);
    std::thread progress_thread([&]() {
        while (!progress_done.load(std::memory_order_relaxed)) {
            std::this_thread::sleep_for(std::chrono::seconds(2));
            if (progress_done.load(std::memory_order_relaxed)) break;

            uint64_t tested = g_passphrases_tested.load(std::memory_order_relaxed);
            auto now = std::chrono::steady_clock::now();
            double elapsed = std::chrono::duration<double>(now - start_time).count();
            double rate = (elapsed > 0.01) ? (double)tested / elapsed : 0.0;

            printf("\r  ⏱  Passphrases tested: %10" PRIu64 "  Rate: %.0f/s  Elapsed: %.0fs    ",
                   tested, rate, elapsed);
            fflush(stdout);
        }
    });

    for (auto& th : threads) th.join();
    progress_done.store(true, std::memory_order_release);
    progress_thread.join();

    auto end_time = std::chrono::steady_clock::now();
    double elapsed = std::chrono::duration<double>(end_time - start_time).count();
    uint64_t tested = g_passphrases_tested.load(std::memory_order_relaxed);

    printf("\r  ✅ Tested %" PRIu64 " passphrases in %.1fs (%.0f/s)\n\n",
           tested, elapsed, elapsed > 0 ? (double)tested / elapsed : 0);

    if (g_found.load(std::memory_order_relaxed)) {
        std::lock_guard<std::mutex> lock(g_found_mutex);
        PassphraseResult pr;
        pr.model_idx = g_found_model.load();
        pr.method = g_found_method;
        pr.passphrase = g_found_passphrase;
        display_match_passphrase(pr, elapsed);
    } else {
        printf("  ❌ No matching passphrase found in Mode 2.\n\n");
    }
}

// ============================================================
// MODE 3: Entropy Combination Attack
// ============================================================

static void run_mode3(int num_threads) {
    printf("\n");
    printf("╔══════════════════════════════════════════════════════════╗\n");
    printf("║  MODE 3: Entropy Combination Attack                     ║\n");
    printf("║  Threads: %-4d                                          ║\n", num_threads);
    printf("╚══════════════════════════════════════════════════════════╝\n\n");

    // This mode tries various entropy-combining strategies that someone
    // might have used to generate a "clever" seed:
    //
    // - pid × time
    // - time + constant
    // - time ^ constant
    // - time × small_prime
    // - CRC32 of timestamp
    // - hash of hostname + time
    // - sum of timestamp digits
    // - interleaved bits of two values
    // etc.

    g_found.store(false, std::memory_order_release);
    g_seeds_tested.store(0, std::memory_order_relaxed);

    auto start_time = std::chrono::steady_clock::now();

    // Strategy 1: time(s) * small_factor + small_offset
    // The idea: seed = timestamp * K + C for small K and C
    printf("  🔍 Strategy 1: time * factor + offset\n");
    {
        const uint64_t factors[] = {1, 2, 3, 5, 7, 11, 13, 17, 19, 23, 31, 37, 41, 43, 47, 100, 1000, 1337};
        const int64_t offsets[] = {0, 1, -1, 2, -2, 42, -42, 100, -100, 1337, -1337, 31337};
        int num_factors = sizeof(factors) / sizeof(factors[0]);
        int num_offsets = sizeof(offsets) / sizeof(offsets[0]);

        for (int fi = 0; fi < num_factors && !g_found.load(std::memory_order_relaxed); fi++) {
            for (int oi = 0; oi < num_offsets && !g_found.load(std::memory_order_relaxed); oi++) {
                // Sweep through timestamp range
                std::vector<std::thread> threads;
                std::vector<WorkerResult> results(num_threads);

                uint64_t range = TS_WIDE_END - TS_WIDE_START;
                uint64_t chunk = range / (uint64_t)num_threads;
                if (chunk == 0) chunk = 1;

                for (int t = 0; t < num_threads; t++) {
                    uint64_t t_start = TS_WIDE_START + (uint64_t)t * chunk;
                    uint64_t t_end = (t == num_threads - 1) ? TS_WIDE_END : t_start + chunk;
                    uint64_t factor = factors[fi];
                    int64_t offset = offsets[oi];

                    threads.emplace_back([t_start, t_end, factor, offset, &results, t]() {
                        results[t].found = false;
                        for (uint64_t ts = t_start; ts < t_end; ts++) {
                            if (g_found.load(std::memory_order_relaxed)) return;

                            uint64_t seed = (uint64_t)((int64_t)(ts * factor) + offset);
                            int m = test_seed_numeric(seed);
                            g_seeds_tested.fetch_add(1, std::memory_order_relaxed);
                            if (m >= 0) {
                                results[t].found = true;
                                results[t].seed = seed;
                                results[t].model_idx = m;
                                g_found.store(true, std::memory_order_release);
                                return;
                            }
                        }
                    });
                }

                for (auto& th : threads) th.join();

                for (int t = 0; t < num_threads; t++) {
                    if (results[t].found) {
                        auto end_time = std::chrono::steady_clock::now();
                        double elapsed = std::chrono::duration<double>(end_time - start_time).count();
                        printf("\n  🔥 Found via time*%" PRIu64 "+%" PRId64 "!\n",
                               factors[fi], (long long)offsets[oi]);
                        display_match_numeric(results[t].seed, results[t].model_idx, elapsed);
                        return;
                    }
                }
            }
        }

        uint64_t tested = g_seeds_tested.load(std::memory_order_relaxed);
        printf("  ✅ Strategy 1 complete: %" PRIu64 " seeds tested\n\n", tested);
    }

    // Strategy 2: time(s) XOR constant
    printf("  🔍 Strategy 2: time XOR constant\n");
    {
        const uint32_t xor_constants[] = {
            0xDEADBEEF, 0xCAFEBABE, 0x8BADF00D, 0xBAADF00D,
            0x1337, 0x31337, 0xBTC, 0x42,
            0xFFFFFFFF, 0x55555555, 0xAAAAAAAA,
            0x12345678, 0x87654321,
        };
        int num_xor = sizeof(xor_constants) / sizeof(xor_constants[0]);

        for (int xi = 0; xi < num_xor && !g_found.load(std::memory_order_relaxed); xi++) {
            std::vector<std::thread> threads;
            std::vector<WorkerResult> results(num_threads);

            uint64_t range = TS_WIDE_END - TS_WIDE_START;
            uint64_t chunk = range / (uint64_t)num_threads;
            if (chunk == 0) chunk = 1;

            for (int t = 0; t < num_threads; t++) {
                uint64_t t_start = TS_WIDE_START + (uint64_t)t * chunk;
                uint64_t t_end = (t == num_threads - 1) ? TS_WIDE_END : t_start + chunk;
                uint32_t xor_val = xor_constants[xi];

                threads.emplace_back([t_start, t_end, xor_val, &results, t]() {
                    results[t].found = false;
                    for (uint64_t ts = t_start; ts < t_end; ts++) {
                        if (g_found.load(std::memory_order_relaxed)) return;

                        uint64_t seed = ts ^ (uint64_t)xor_val;
                        int m = test_seed_numeric(seed);
                        g_seeds_tested.fetch_add(1, std::memory_order_relaxed);
                        if (m >= 0) {
                            results[t].found = true;
                            results[t].seed = seed;
                            results[t].model_idx = m;
                            g_found.store(true, std::memory_order_release);
                            return;
                        }
                    }
                });
            }

            for (auto& th : threads) th.join();

            for (int t = 0; t < num_threads; t++) {
                if (results[t].found) {
                    auto end_time = std::chrono::steady_clock::now();
                    double elapsed = std::chrono::duration<double>(end_time - start_time).count();
                    printf("\n  🔥 Found via time XOR 0x%08X!\n", xor_constants[xi]);
                    display_match_numeric(results[t].seed, results[t].model_idx, elapsed);
                    return;
                }
            }
        }

        uint64_t tested = g_seeds_tested.load(std::memory_order_relaxed);
        printf("  ✅ Strategy 2 complete: %" PRIu64 " total seeds tested\n\n", tested);
    }

    // Strategy 3: pid × time (small PIDs 1-65535)
    printf("  🔍 Strategy 3: PID × timestamp (PIDs 1-32768)\n");
    {
        std::atomic<uint64_t> strategy3_tested(0);
        std::vector<std::thread> threads;
        std::vector<WorkerResult> results(num_threads);

        // We test PID * timestamp for hot range
        // Total combinations: 32768 * (TS_HOT_END - TS_HOT_START) ≈ 32768 * 1.2M ≈ 40B
        // That's too many. Sample: only test PIDs 1-1000 against hot range.
        uint32_t max_pid = 1000;
        uint64_t ts_range = TS_HOT_END - TS_HOT_START;
        uint64_t total_combos = (uint64_t)max_pid * ts_range;
        uint64_t combo_chunk = total_combos / (uint64_t)num_threads;
        if (combo_chunk == 0) combo_chunk = 1;

        for (int t = 0; t < num_threads; t++) {
            uint64_t t_start = (uint64_t)t * combo_chunk;
            uint64_t t_end = (t == num_threads - 1) ? total_combos : t_start + combo_chunk;

            threads.emplace_back([t_start, t_end, max_pid, ts_range, &results, t, &strategy3_tested]() {
                results[t].found = false;
                uint64_t local_count = 0;

                for (uint64_t combo = t_start; combo < t_end; combo++) {
                    if (g_found.load(std::memory_order_relaxed)) return;

                    uint32_t pid = (uint32_t)(combo / ts_range) + 1;
                    uint64_t ts = TS_HOT_START + (combo % ts_range);

                    // Try: pid * ts
                    uint64_t seed = (uint64_t)pid * ts;
                    int m = test_seed_numeric(seed);
                    if (m >= 0) {
                        results[t].found = true;
                        results[t].seed = seed;
                        results[t].model_idx = m;
                        g_found.store(true, std::memory_order_release);
                        return;
                    }

                    // Try: pid + ts
                    seed = (uint64_t)pid + ts;
                    m = test_seed_numeric(seed);
                    if (m >= 0) {
                        results[t].found = true;
                        results[t].seed = seed;
                        results[t].model_idx = m;
                        g_found.store(true, std::memory_order_release);
                        return;
                    }

                    // Try: pid ^ ts
                    seed = (uint64_t)pid ^ ts;
                    m = test_seed_numeric(seed);
                    if (m >= 0) {
                        results[t].found = true;
                        results[t].seed = seed;
                        results[t].model_idx = m;
                        g_found.store(true, std::memory_order_release);
                        return;
                    }

                    local_count += 3;
                    if (local_count % 100000 == 0) {
                        strategy3_tested.fetch_add(100000, std::memory_order_relaxed);
                    }
                }
                strategy3_tested.fetch_add(local_count % 100000, std::memory_order_relaxed);
            });
        }

        // Simple progress
        std::atomic<bool> done3(false);
        std::thread prog3([&]() {
            while (!done3.load(std::memory_order_relaxed)) {
                std::this_thread::sleep_for(std::chrono::seconds(5));
                if (done3.load(std::memory_order_relaxed)) break;
                uint64_t t3 = strategy3_tested.load(std::memory_order_relaxed);
                printf("\r  ⏱  Strategy 3: %" PRIu64 " combos tested    ", t3);
                fflush(stdout);
            }
        });

        for (auto& th : threads) th.join();
        done3.store(true, std::memory_order_release);
        prog3.join();

        for (int t = 0; t < num_threads; t++) {
            if (results[t].found) {
                auto end_time = std::chrono::steady_clock::now();
                double elapsed = std::chrono::duration<double>(end_time - start_time).count();
                printf("\n  🔥 Found via PID×time combo!\n");
                display_match_numeric(results[t].seed, results[t].model_idx, elapsed);
                return;
            }
        }

        printf("\r  ✅ Strategy 3 complete: %" PRIu64 " combos tested\n\n",
               strategy3_tested.load(std::memory_order_relaxed));
    }

    // Strategy 4: SHA256(timestamp) → seed
    printf("  🔍 Strategy 4: SHA256(timestamp_string) → seed\n");
    {
        std::atomic<uint64_t> strategy4_tested(0);
        std::vector<std::thread> threads;
        std::vector<WorkerResult> results(num_threads);

        uint64_t range = TS_WIDE_END - TS_WIDE_START;
        uint64_t chunk = range / (uint64_t)num_threads;
        if (chunk == 0) chunk = 1;

        for (int t = 0; t < num_threads; t++) {
            uint64_t t_start = TS_WIDE_START + (uint64_t)t * chunk;
            uint64_t t_end = (t == num_threads - 1) ? TS_WIDE_END : t_start + chunk;

            threads.emplace_back([t_start, t_end, &results, t, &strategy4_tested]() {
                results[t].found = false;
                uint64_t local_count = 0;

                for (uint64_t ts = t_start; ts < t_end; ts++) {
                    if (g_found.load(std::memory_order_relaxed)) return;

                    // Convert timestamp to string, SHA256 it
                    char ts_str[32];
                    int len = snprintf(ts_str, sizeof(ts_str), "%" PRIu64, ts);
                    uint8_t hash[32];
                    sha256(ts_str, (size_t)len, hash);

                    // Use first 4 bytes as uint32 seed (big-endian)
                    uint32_t seed32 = ((uint32_t)hash[0] << 24) | ((uint32_t)hash[1] << 16) |
                                      ((uint32_t)hash[2] << 8) | (uint32_t)hash[3];

                    MT19937 mt;
                    mt_seed_uint32(mt, seed32);
                    int m = test_seeded_mt(mt, 0, 1);
                    if (m < 0) { mt_seed_uint32(mt, seed32); m = test_seeded_mt(mt, 3, 4); }
                    if (m >= 0) {
                        results[t].found = true;
                        results[t].seed = ts;  // Store the timestamp that generated the seed
                        results[t].model_idx = m;
                        g_found.store(true, std::memory_order_release);
                        return;
                    }

                    // Also try full SHA256 as Python seed
                    uint32_t key_words[8];
                    for (int i = 0; i < 8; i++) {
                        int base = (7 - i) * 4;
                        key_words[i] = ((uint32_t)hash[base] << 24) | ((uint32_t)hash[base+1] << 16) |
                                       ((uint32_t)hash[base+2] << 8) | (uint32_t)hash[base+3];
                    }
                    int klen = 8;
                    while (klen > 1 && key_words[klen-1] == 0) klen--;

                    mt_seed_by_array(mt, key_words, klen);
                    m = test_seeded_mt(mt, 1, 3);
                    if (m >= 0) {
                        results[t].found = true;
                        results[t].seed = ts;
                        results[t].model_idx = m;
                        g_found.store(true, std::memory_order_release);
                        return;
                    }

                    local_count++;
                    if (local_count % 50000 == 0) {
                        strategy4_tested.fetch_add(50000, std::memory_order_relaxed);
                    }
                }
                strategy4_tested.fetch_add(local_count % 50000, std::memory_order_relaxed);
            });
        }

        std::atomic<bool> done4(false);
        std::thread prog4([&]() {
            while (!done4.load(std::memory_order_relaxed)) {
                std::this_thread::sleep_for(std::chrono::seconds(5));
                if (done4.load(std::memory_order_relaxed)) break;
                printf("\r  ⏱  Strategy 4: %" PRIu64 " timestamps tested    ",
                       strategy4_tested.load(std::memory_order_relaxed));
                fflush(stdout);
            }
        });

        for (auto& th : threads) th.join();
        done4.store(true, std::memory_order_release);
        prog4.join();

        for (int t = 0; t < num_threads; t++) {
            if (results[t].found) {
                auto end_time = std::chrono::steady_clock::now();
                double elapsed = std::chrono::duration<double>(end_time - start_time).count();
                printf("\n  🔥 Found via SHA256(timestamp_string)!\n");
                printf("  Original timestamp: %" PRIu64 "\n", results[t].seed);
                display_match_numeric(results[t].seed, results[t].model_idx, elapsed);
                return;
            }
        }

        printf("\r  ✅ Strategy 4 complete: %" PRIu64 " timestamps tested\n\n",
               strategy4_tested.load(std::memory_order_relaxed));
    }

    auto end_time = std::chrono::steady_clock::now();
    double elapsed = std::chrono::duration<double>(end_time - start_time).count();

    if (!g_found.load(std::memory_order_relaxed)) {
        printf("  ❌ No seed found in Mode 3 after %.1f seconds.\n\n", elapsed);
    }
}

// ============================================================
// MODE 4: C++ std::seed_seq Multi-Word Seeds
// ============================================================

static void run_mode4(int num_threads) {
    printf("\n");
    printf("╔══════════════════════════════════════════════════════════╗\n");
    printf("║  MODE 4: std::seed_seq Multi-Word Seed Attack           ║\n");
    printf("║  Threads: %-4d                                          ║\n", num_threads);
    printf("╚══════════════════════════════════════════════════════════╝\n\n");

    g_found.store(false, std::memory_order_release);
    g_seeds_tested.store(0, std::memory_order_relaxed);

    auto start_time = std::chrono::steady_clock::now();

    // Strategy 1: Single word seed_seq {value} for all uint32
    printf("  🔍 Strategy 1: seed_seq({single_word}) sweep\n");
    {
        std::vector<std::thread> threads;
        std::vector<WorkerResult> results(num_threads);

        uint64_t range = 4294967296ULL;  // full uint32
        uint64_t chunk = range / (uint64_t)num_threads;

        for (int t = 0; t < num_threads; t++) {
            uint64_t t_start = (uint64_t)t * chunk;
            uint64_t t_end = (t == num_threads - 1) ? range : t_start + chunk;

            threads.emplace_back([t_start, t_end, &results, t]() {
                results[t].found = false;
                uint64_t local_count = 0;

                for (uint64_t val = t_start; val < t_end; val++) {
                    if (g_found.load(std::memory_order_relaxed)) return;

                    uint32_t word = (uint32_t)val;
                    MT19937 mt;
                    mt_seed_seq_faithful(mt, &word, 1);

                    // Test C++ models (seed_seq is C++ only)
                    int m = test_seeded_mt(mt, 0, 1);
                    if (m < 0) {
                        mt_seed_seq_faithful(mt, &word, 1);
                        m = test_seeded_mt(mt, 3, 4);
                    }

                    if (m >= 0) {
                        results[t].found = true;
                        results[t].seed = val;
                        results[t].model_idx = m;
                        g_found.store(true, std::memory_order_release);
                        return;
                    }

                    local_count++;
                    if (local_count % 100000 == 0) {
                        g_seeds_tested.fetch_add(100000, std::memory_order_relaxed);
                    }
                }
                g_seeds_tested.fetch_add(local_count % 100000, std::memory_order_relaxed);
            });
        }

        std::atomic<bool> done(false);
        std::thread prog([&]() {
            while (!done.load(std::memory_order_relaxed)) {
                std::this_thread::sleep_for(std::chrono::seconds(3));
                if (done.load(std::memory_order_relaxed)) break;
                uint64_t tested = g_seeds_tested.load(std::memory_order_relaxed);
                double elapsed = std::chrono::duration<double>(
                    std::chrono::steady_clock::now() - start_time).count();
                double rate = elapsed > 0.01 ? (double)tested / elapsed : 0;
                printf("\r  ⏱  seed_seq single: %" PRIu64 "/4294967296  (%.1f%%)  Rate: %.0f/s    ",
                       tested, 100.0 * (double)tested / 4294967296.0, rate);
                fflush(stdout);
            }
        });

        for (auto& th : threads) th.join();
        done.store(true, std::memory_order_release);
        prog.join();

        for (int t = 0; t < num_threads; t++) {
            if (results[t].found) {
                auto end_time = std::chrono::steady_clock::now();
                double elapsed = std::chrono::duration<double>(end_time - start_time).count();
                printf("\n  🔥 Found via seed_seq({%" PRIu64 "})!\n", results[t].seed);
                display_match_numeric(results[t].seed, results[t].model_idx, elapsed);
                return;
            }
        }

        printf("\r  ✅ Strategy 1 complete: %" PRIu64 " seeds tested\n\n",
               g_seeds_tested.load(std::memory_order_relaxed));
    }

    // Strategy 2: Two-word seed_seq {timestamp, small_value}
    printf("  🔍 Strategy 2: seed_seq({timestamp, small}) — hot timestamps × [0..1000]\n");
    {
        std::atomic<uint64_t> s2_tested(0);
        std::vector<std::thread> threads;
        std::vector<WorkerResult> results(num_threads);

        uint64_t ts_range = TS_HOT_END - TS_HOT_START;
        uint32_t small_range = 1001;  // 0..1000
        uint64_t total_combos = ts_range * (uint64_t)small_range;
        uint64_t combo_chunk = total_combos / (uint64_t)num_threads;
        if (combo_chunk == 0) combo_chunk = 1;

        for (int t = 0; t < num_threads; t++) {
            uint64_t t_start = (uint64_t)t * combo_chunk;
            uint64_t t_end = (t == num_threads - 1) ? total_combos : t_start + combo_chunk;

            threads.emplace_back([t_start, t_end, ts_range, small_range, &results, t, &s2_tested]() {
                results[t].found = false;
                uint64_t local_count = 0;

                for (uint64_t combo = t_start; combo < t_end; combo++) {
                    if (g_found.load(std::memory_order_relaxed)) return;

                    uint64_t ts_offset = combo / (uint64_t)small_range;
                    uint32_t small_val = (uint32_t)(combo % (uint64_t)small_range);
                    uint32_t ts32 = (uint32_t)(TS_HOT_START + ts_offset);

                    uint32_t words[2] = { ts32, small_val };
                    MT19937 mt;
                    mt_seed_seq_faithful(mt, words, 2);

                    int m = test_seeded_mt(mt, 0, 1);
                    if (m < 0) {
                        mt_seed_seq_faithful(mt, words, 2);
                        m = test_seeded_mt(mt, 3, 4);
                    }

                    if (m >= 0) {
                        results[t].found = true;
                        results[t].seed = combo;  // encode the combo
                        results[t].model_idx = m;
                        g_found.store(true, std::memory_order_release);
                        return;
                    }

                    // Also try reverse order
                    uint32_t words_rev[2] = { small_val, ts32 };
                    mt_seed_seq_faithful(mt, words_rev, 2);
                    m = test_seeded_mt(mt, 0, 1);
                    if (m < 0) {
                        mt_seed_seq_faithful(mt, words_rev, 2);
                        m = test_seeded_mt(mt, 3, 4);
                    }

                    if (m >= 0) {
                        results[t].found = true;
                        results[t].seed = combo;
                        results[t].model_idx = m;
                        g_found.store(true, std::memory_order_release);
                        return;
                    }

                    local_count++;
                    if (local_count % 50000 == 0) {
                        s2_tested.fetch_add(50000, std::memory_order_relaxed);
                    }
                }
                s2_tested.fetch_add(local_count % 50000, std::memory_order_relaxed);
            });
        }

        std::atomic<bool> done2(false);
        std::thread prog2([&]() {
            while (!done2.load(std::memory_order_relaxed)) {
                std::this_thread::sleep_for(std::chrono::seconds(5));
                if (done2.load(std::memory_order_relaxed)) break;
                printf("\r  ⏱  Strategy 2: %" PRIu64 " combos tested    ",
                       s2_tested.load(std::memory_order_relaxed));
                fflush(stdout);
            }
        });

        for (auto& th : threads) th.join();
        done2.store(true, std::memory_order_release);
        prog2.join();

        for (int t = 0; t < num_threads; t++) {
            if (results[t].found) {
                auto end_time = std::chrono::steady_clock::now();
                double elapsed = std::chrono::duration<double>(end_time - start_time).count();
                printf("\n  🔥 Found via seed_seq({timestamp, small})!\n");
                display_match_numeric(results[t].seed, results[t].model_idx, elapsed);
                return;
            }
        }

        printf("\r  ✅ Strategy 2 complete: %" PRIu64 " combos tested\n\n",
               s2_tested.load(std::memory_order_relaxed));
    }

    auto end_time = std::chrono::steady_clock::now();
    double elapsed = std::chrono::duration<double>(end_time - start_time).count();

    if (!g_found.load(std::memory_order_relaxed)) {
        printf("  ❌ No seed found in Mode 4 after %.1f seconds.\n\n", elapsed);
    }
}

// ============================================================
// MODE 5: Combined All-In-One
// ============================================================

static void run_mode5(int num_threads, const std::vector<std::string>& dict_files) {
    printf("\n");
    printf("╔══════════════════════════════════════════════════════════╗\n");
    printf("║  MODE 5: Combined All-In-One Attack                     ║\n");
    printf("║  Threads: %-4d                                          ║\n", num_threads);
    printf("╚══════════════════════════════════════════════════════════╝\n\n");

    auto overall_start = std::chrono::steady_clock::now();

    printf("━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━\n");
    printf("  Running Mode 1: Numeric Seed Brute-Force\n");
    printf("━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━\n");
    g_found.store(false, std::memory_order_release);
    run_mode1(num_threads);
    if (g_found.load(std::memory_order_relaxed)) return;

    printf("━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━\n");
    printf("  Running Mode 2: Passphrase Dictionary Attack\n");
    printf("━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━\n");
    g_found.store(false, std::memory_order_release);
    run_mode2(num_threads, dict_files);
    if (g_found.load(std::memory_order_relaxed)) return;

    printf("━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━\n");
    printf("  Running Mode 3: Entropy Combination Attack\n");
    printf("━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━\n");
    g_found.store(false, std::memory_order_release);
    run_mode3(num_threads);
    if (g_found.load(std::memory_order_relaxed)) return;

    printf("━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━\n");
    printf("  Running Mode 4: std::seed_seq Attack\n");
    printf("━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━\n");
    g_found.store(false, std::memory_order_release);
    run_mode4(num_threads);
    if (g_found.load(std::memory_order_relaxed)) return;

    auto overall_end = std::chrono::steady_clock::now();
    double total_elapsed = std::chrono::duration<double>(overall_end - overall_start).count();

    printf("\n");
    printf("══════════════════════════════════════════════════════════\n");
    printf("  Mode 5 Complete — All attacks exhausted.\n");
    printf("  Total time: %.1f seconds (%.1f minutes)\n", total_elapsed, total_elapsed / 60.0);
    printf("══════════════════════════════════════════════════════════\n\n");
}

// ============================================================
// Signal handler for graceful shutdown
// ============================================================

static void signal_handler(int sig) {
    (void)sig;
    printf("\n\n  ⚠️  Interrupted! Shutting down...\n\n");
    g_found.store(true, std::memory_order_release);  // causes all workers to stop
    // Give threads a moment to notice
    std::this_thread::sleep_for(std::chrono::milliseconds(500));
    exit(1);
}

// ============================================================
// Print usage
// ============================================================

static void print_usage(const char* argv0) {
    printf("Usage: %s [options]\n\n", argv0);
    printf("Options:\n");
    printf("  --mode N          Select mode (1-5), or interactive if omitted\n");
    printf("  --threads N       Number of worker threads (default: hardware cores)\n");
    printf("  --dict FILE       Dictionary file for Mode 2 (can specify multiple)\n");
    printf("  --dict2 FILE      Additional dictionary file\n");
    printf("  --help            Show this help\n\n");
    printf("Modes:\n");
    printf("  1  Numeric seed brute-force (timestamps, small seeds, full uint32)\n");
    printf("  2  Passphrase dictionary attack (SHA256, raw bytes, etc.)\n");
    printf("  3  Entropy combination attack (pid×time, time^const, etc.)\n");
    printf("  4  C++ std::seed_seq multi-word seed patterns\n");
    printf("  5  Combined all-in-one (runs modes 1-4 sequentially)\n\n");
    printf("Examples:\n");
    printf("  %s --mode 1 --threads 16\n", argv0);
    printf("  %s --mode 2 --dict wordlist.txt --threads 8\n", argv0);
    printf("  %s --mode 5 --dict rockyou.txt --threads 16\n", argv0);
    printf("  BF_WORKERS=16 %s --mode 1\n\n", argv0);
}

// ============================================================
// Main
// ============================================================

int main(int argc, char* argv[]) {
    signal(SIGINT, signal_handler);
    signal(SIGTERM, signal_handler);

    int mode = -1;
    int num_threads = (int)std::thread::hardware_concurrency();
    if (num_threads == 0) num_threads = 4;

    std::vector<std::string> dict_files;

    // Parse env var
    const char* env_workers = getenv("BF_WORKERS");
    if (env_workers) {
        int env_n = atoi(env_workers);
        if (env_n > 0) num_threads = env_n;
    }

    // Parse args
    for (int i = 1; i < argc; i++) {
        if (strcmp(argv[i], "--mode") == 0 && i + 1 < argc) {
            mode = atoi(argv[++i]);
        } else if (strcmp(argv[i], "--threads") == 0 && i + 1 < argc) {
            num_threads = atoi(argv[++i]);
        } else if (strcmp(argv[i], "--dict") == 0 && i + 1 < argc) {
            dict_files.push_back(argv[++i]);
        } else if (strcmp(argv[i], "--dict2") == 0 && i + 1 < argc) {
            dict_files.push_back(argv[++i]);
        } else if (strcmp(argv[i], "--help") == 0 || strcmp(argv[i], "-h") == 0) {
            print_usage(argv[0]);
            return 0;
        }
    }

    if (num_threads < 1) num_threads = 1;
    if (num_threads > 256) num_threads = 256;

    if (mode < 1 || mode > 5) {
        printf("\n");
        printf("╔══════════════════════════════════════════════════════════╗\n");
        printf("║  BTC Puzzle Seed Bruteforce — C++ v6                      ║\n");
        printf("╠══════════════════════════════════════════════════════════╣\n");
        printf("║  Mode 1: Numeric seed brute-force (timestamps, etc.)     ║\n");
        printf("║  Mode 2: Passphrase dictionary attack                     ║\n");
        printf("║  Mode 3: Entropy combination attack                       ║\n");
        printf("║  Mode 4: std::seed_seq multi-word seed attack            ║\n");
        printf("║  Mode 5: Combined all-in-one (all above)                 ║\n");
        printf("╠══════════════════════════════════════════════════════════╣\n");
        printf("║  Threads: %-3d                                             ║\n", num_threads);
        printf("╚══════════════════════════════════════════════════════════╝\n\n");
        printf("Select mode (1-5): ");

        if (scanf("%d", &mode) != 1) {
            printf("Invalid input.\n");
            return 1;
        }
    }

    switch (mode) {
        case 1:
            run_mode1(num_threads);
            break;
        case 2:
            run_mode2(num_threads, dict_files);
            break;
        case 3:
            run_mode3(num_threads);
            break;
        case 4:
            run_mode4(num_threads);
            break;
        case 5:
            run_mode5(num_threads, dict_files);
            break;
        default:
            printf("Invalid mode: %d\n", mode);
            print_usage(argv[0]);
            return 1;
    }

    return 0;
}
