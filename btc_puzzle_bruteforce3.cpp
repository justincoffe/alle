// btc_puzzle_bruteforce.cpp
// BTC Puzzle Generator Seed Brute-Force — C++ Nuclear Option v5 (FIXED)
//
// FIXES:
//   - Python models now ALWAYS use init_by_array (matching CPython behavior)
//   - Model-aware seeding dispatch in test_seed()
//   - C++ models with >32-bit seeds: truncate to uint32 (std::mt19937 behavior)
//   - Proper handling of seed=0 edge case
//
// OPTIMIZED: Timestamp upper bound locked to TX broadcast:
//   2015-01-15 06:07:14 UTC (unix 1421301634) + 1 min margin = 1421301680
//
// Compile:
//   g++ -O3 -march=native -pthread -o btc_bruteforce btc_puzzle_bruteforce3.cpp
//
// Run:
//   ./btc_bruteforce [num_threads]
//   BF_WORKERS=16 ./btc_bruteforce

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

// ============================================================
// CRITICAL TIMESTAMP CONSTANTS
// ============================================================
//
// The funding TX was broadcast: 2015-01-15 06:07:14 UTC
// Unix epoch: 1421301634
// With 1-minute margin: 1421301680
//
// The seed MUST have been generated BEFORE this moment.
// No point scanning anything after it.
//
// Conservative lower bounds:
//   - Tight:  2014-06-01 (puzzle concept likely emerged mid-2014)
//   - Normal: 2014-01-01
//   - Wide:   2013-01-01 (absolute earliest reasonable)
//
// We also add a "hot zone" for the most likely generation window:
//   2015-01-01 to 2015-01-15 (the 2 weeks before broadcast)
// ============================================================

static constexpr uint64_t TX_BROADCAST_UTC   = 1421301634ULL;  // 2015-01-15 06:07:14 UTC
static constexpr uint64_t TX_DEADLINE         = 1421301680ULL;  // +46s margin (rounded to next minute)

static constexpr uint64_t TS_HOT_START        = 1420070400ULL;  // 2015-01-01 00:00:00 UTC
static constexpr uint64_t TS_HOT_END          = TX_DEADLINE;    // 2015-01-15 06:08:00 UTC

static constexpr uint64_t TS_NARROW_START     = 1388534400ULL;  // 2014-01-01 00:00:00 UTC
static constexpr uint64_t TS_NARROW_END       = TX_DEADLINE;    // hard cutoff

static constexpr uint64_t TS_WIDE_START       = 1356998400ULL;  // 2013-01-01 00:00:00 UTC
static constexpr uint64_t TS_WIDE_END         = TX_DEADLINE;    // hard cutoff

// ============================================================
// 128-bit unsigned integer (minimal, for puzzle 65)
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
    static uint128_t from_u64(uint64_t v) { return uint128_t(0, v); }
};

// ============================================================
// MT19937 State
// ============================================================

struct MT19937 {
    uint32_t state[624];
    int index;
};

// ============================================================
// MT19937 Seeding — uint32 (Knuth LCG, standard C++ std::mt19937)
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
// MT19937 Seeding — init_by_array (matches CPython exactly)
// ============================================================

static void mt_seed_by_array(MT19937& mt, const uint32_t* init_key, int key_length) {
    // Phase 1: Initialize with Knuth LCG using fixed seed 19650218
    mt.state[0] = 19650218U;
    for (int i = 1; i < 624; i++) {
        uint32_t prev = mt.state[i - 1];
        mt.state[i] = 1812433253U * (prev ^ (prev >> 30)) + (uint32_t)i;
    }

    // Phase 2: Mix in the key array
    int i = 1, j = 0;
    int k = (624 > key_length) ? 624 : key_length;

    for (; k > 0; k--) {
        uint32_t s = mt.state[i - 1];
        mt.state[i] = (mt.state[i] ^ ((s ^ (s >> 30)) * 1664525U)) + init_key[j] + (uint32_t)j;
        i++; j++;
        if (i >= 624) { mt.state[0] = mt.state[623]; i = 1; }
        if (j >= key_length) { j = 0; }
    }

    // Phase 3: Additional mixing
    for (k = 623; k > 0; k--) {
        uint32_t s = mt.state[i - 1];
        mt.state[i] = (mt.state[i] ^ ((s ^ (s >> 30)) * 1566083941U)) - (uint32_t)i;
        i++;
        if (i >= 624) { mt.state[0] = mt.state[623]; i = 1; }
    }

    // Sentinel: MSB set to ensure non-zero initial array
    mt.state[0] = 0x80000000U;
    mt.index = 624;
}

// ============================================================
// Convert a uint64_t seed into a little-endian uint32 word array
// Matches CPython's _PyLong_AsByteArray → uint32 conversion
// ============================================================

static int seed_to_key_array(uint64_t seed, uint32_t* out) {
    if (seed == 0) {
        // CPython: int(0) has byte length 0, falls back to key={0}, len=1
        out[0] = 0;
        return 1;
    }
    int n = 0;
    uint64_t tmp = seed;
    while (tmp > 0) {
        out[n++] = (uint32_t)(tmp & 0xFFFFFFFFULL);
        tmp >>= 32;
    }
    return n;
}

// ============================================================
// MT19937 Seeding — Python style (ALWAYS init_by_array)
// CPython's random.seed() converts ANY integer to a uint32
// array and calls init_by_array, regardless of seed size.
// This has been true since Python 2.4 (2004).
// ============================================================

static inline void mt_seed_python(MT19937& mt, uint64_t seed) {
    uint32_t key[2];
    int klen = seed_to_key_array(seed, key);
    mt_seed_by_array(mt, key, klen);
}

// ============================================================
// MT19937 Seeding — C++ style
// std::mt19937 accepts a uint32_t seed via Knuth LCG.
// For seeds > 32-bit, C++ would require std::seed_seq (different
// algorithm entirely). We truncate to uint32 since that's the
// most common C++ usage pattern.
// ============================================================

static inline void mt_seed_cpp(MT19937& mt, uint64_t seed) {
    mt_seed_uint32(mt, (uint32_t)(seed & 0xFFFFFFFFULL));
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

// Model 0: C++ getrandbits/bitmask — getrandbits(n-1) + 2^(n-1)
// Model 1: Python 3 getrandbits — same formula, different seeding
static inline uint128_t gen_key_bitmask(MT19937& mt, int n) {
    if (n == 1) return uint128_t(1);
    int bits = n - 1;
    uint128_t raw = mt_getrandbits(mt, bits);
    uint128_t high_bit = uint128_t(1) << (n - 1);
    return raw + high_bit;
}

// Model 2: Python 2.7 randint (float path for small, getrandbits for large)
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
            if (r < width_128) {
                return r + lo_val;
            }
        }
    }
}

// Model 3: C++ uniform_int_distribution (rejection on 32-bit words)
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
    gen_key_bitmask,       // Model 0: C++ bitmask
    gen_key_bitmask,       // Model 1: Python 3 getrandbits (same gen, different seeding)
    gen_key_py2_randint,   // Model 2: Python 2.7 randint
    gen_key_cpp_uniform,   // Model 3: C++ uniform_int_distribution
};

static const char* MODEL_NAMES[4] = {
    "C++ getrandbits/bitmask",
    "Python 3 getrandbits",
    "Python 2.7 randint",
    "C++ uniform_int_distribution",
};

// ============================================================
// Model seeding classification
// ============================================================
// Models 0 and 3 are C++  → use Knuth LCG (mt_seed_uint32)
// Models 1 and 2 are Python → ALWAYS use init_by_array
// ============================================================

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
// Seed Tester — Model-aware seeding
// ============================================================

static int test_seed(uint64_t seed) {
    MT19937 mt;

    for (int model_idx = 0; model_idx < 4; model_idx++) {
        GenFunc gen = GEN_FUNCS[model_idx];

        // ============================================================
        // CRITICAL FIX: Model-aware seeding
        //
        // Python (models 1, 2): ALWAYS uses init_by_array, even for
        //   small integers like seed=42. This matches CPython's
        //   random.seed() behavior since Python 2.4.
        //
        // C++ (models 0, 3): Uses Knuth LCG (mt_seed_uint32) for
        //   seeds that fit in uint32. For seeds > 32-bit, C++
        //   std::mt19937 only accepts uint32_t natively, so we
        //   truncate. (std::seed_seq is a different algorithm and
        //   not modeled here.)
        // ============================================================

        if (is_python_model(model_idx)) {
            mt_seed_python(mt, seed);
        } else {
            mt_seed_cpp(mt, seed);
        }

        // Puzzle 1 — always 1, consume state
        gen(mt, 1);

        // Early rejection: puzzles 2-10
        bool failed = false;
        for (int c = 0; c < NUM_EARLY; c++) {
            uint128_t key = gen(mt, EARLY_CHECKS[c].puzzle);
            if (key != EARLY_CHECKS[c].expected) {
                failed = true;
                break;
            }
        }
        if (failed) continue;

        // Deep validation: puzzles 33, 34, 65
        int current_n = 10;
        bool deep_failed = false;
        for (int c = 0; c < NUM_DEEP; c++) {
            int target_n = DEEP_CHECKS[c].puzzle;
            for (int skip_n = current_n + 1; skip_n < target_n; skip_n++) {
                gen(mt, skip_n);
            }
            uint128_t key = gen(mt, target_n);
            current_n = target_n;
            if (key != DEEP_CHECKS[c].expected) {
                deep_failed = true;
                break;
            }
        }

        if (!deep_failed) {
            return model_idx;
        }
    }

    return -1;
}

// ============================================================
// Global state for coordination
// ============================================================

static std::atomic<bool> g_found(false);
static std::atomic<uint64_t> g_found_seed(0);
static std::atomic<int> g_found_model(-1);
static std::atomic<uint64_t> g_seeds_tested(0);

// ============================================================
// Thread worker
// ============================================================

struct WorkerResult {
    bool found;
    uint64_t seed;
    int model_idx;
};

static void worker_thread(uint64_t start, uint64_t end, WorkerResult* result)
{
    result->found = false;
    constexpr uint64_t REPORT_INTERVAL = 100000;
    uint64_t local_count = 0;

    for (uint64_t seed = start; seed < end; seed++) {
        if (g_found.load(std::memory_order_relaxed)) return;

        int model = test_seed(seed);
        if (model >= 0) {
            result->found = true;
            result->seed = seed;
            result->model_idx = model;
            g_found.store(true, std::memory_order_relaxed);
            g_found_seed.store(seed, std::memory_order_relaxed);
            g_found_model.store(model, std::memory_order_relaxed);
            return;
        }

        local_count++;
        if (local_count >= REPORT_INTERVAL) {
            g_seeds_tested.fetch_add(local_count, std::memory_order_relaxed);
            local_count = 0;
        }
    }

    g_seeds_tested.fetch_add(local_count, std::memory_order_relaxed);
}

// ============================================================
// Display match — uses correct model-aware seeding for output
// ============================================================

static void display_match(uint64_t seed, int model_idx, double elapsed_sec) {
    printf("\n\n");
    printf("==============================================================\n");
    printf("  🔥🔥🔥 SEED FOUND 🔥🔥🔥\n");
    printf("  Seed      : %" PRIu64 "\n", seed);
    printf("  Seed hex  : 0x%" PRIX64 "\n", seed);
    printf("  Model     : [%d] %s\n", model_idx, MODEL_NAMES[model_idx]);
    printf("  Seeding   : %s\n", is_python_model(model_idx) ? "init_by_array (Python)" : "Knuth LCG (C++)");
    printf("  Time      : %.1f seconds\n", elapsed_sec);

    // Show as timestamp if plausible
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

    // Generate ALL keys 1..160 using correct model-aware seeding
    MT19937 mt;
    if (is_python_model(model_idx)) {
        mt_seed_python(mt, seed);
    } else {
        mt_seed_cpp(mt, seed);
    }
    GenFunc gen = GEN_FUNCS[model_idx];

    constexpr int MAX_PUZZLE = 160;
    struct { int n; uint128_t key; } all_keys[MAX_PUZZLE];
    for (int n = 1; n <= MAX_PUZZLE; n++) {
        all_keys[n-1].n = n;
        all_keys[n-1].key = gen(mt, n);
    }

    // Known keys for validation
    struct { int n; uint128_t expected; } known[] = {
        {2, uint128_t(3)}, {3, uint128_t(7)}, {4, uint128_t(8)},
        {5, uint128_t(21)}, {6, uint128_t(49)}, {7, uint128_t(76)},
        {8, uint128_t(224)}, {9, uint128_t(467)}, {10, uint128_t(514)},
        {33, uint128_t(7137437912ULL)}, {34, uint128_t(14133072157ULL)},
        {65, uint128_t(0x1ULL, 0xA838B13505B26867ULL)},
    };
    int num_known = 12;

    printf("  %7s  %40s  Status\n", "Puzzle", "Key");
    printf("  %s\n", std::string(65, '-').c_str());

    for (int idx = 0; idx < MAX_PUZZLE; idx++) {
        int n = all_keys[idx].n;
        uint128_t k = all_keys[idx].key;

        char key_str[80];
        if (k.hi == 0) {
            snprintf(key_str, sizeof(key_str), "%" PRIu64, k.lo);
        } else {
            snprintf(key_str, sizeof(key_str), "0x%" PRIX64 "%016" PRIX64, k.hi, k.lo);
        }

        const char* status = "";
        for (int ki = 0; ki < num_known; ki++) {
            if (known[ki].n == n) {
                if (k == known[ki].expected)
                    status = "  ✅ MATCH  <-- KNOWN";
                else
                    status = "  ❌ MISMATCH  <-- KNOWN";
                break;
            }
        }

        printf("  %7d  %40s%s\n", n, key_str, status);
    }

    // Save to file
    char fname[128];
    snprintf(fname, sizeof(fname), "FOUND_SEED_%" PRIu64 ".txt", seed);
    FILE* f = fopen(fname, "w");
    if (f) {
        fprintf(f, "Seed: %" PRIu64 "\n", seed);
        fprintf(f, "Seed hex: 0x%" PRIX64 "\n", seed);
        fprintf(f, "Model: [%d] %s\n", model_idx, MODEL_NAMES[model_idx]);
        fprintf(f, "Seeding: %s\n", is_python_model(model_idx) ? "init_by_array (Python)" : "Knuth LCG (C++)");
        fprintf(f, "TX Broadcast: 2015-01-15 06:07:14 UTC (unix 1421301634)\n\n");
        for (int idx = 0; idx < MAX_PUZZLE; idx++) {
            uint128_t k = all_keys[idx].key;
            if (k.hi == 0)
                fprintf(f, "Puzzle %3d: %" PRIu64 "\n", all_keys[idx].n, k.lo);
            else
                fprintf(f, "Puzzle %3d: 0x%" PRIX64 "%016" PRIX64 "\n",
                        all_keys[idx].n, k.hi, k.lo);
        }
        fclose(f);
        printf("\n  💾 Results saved to %s\n", fname);
    }
}

// ============================================================
// Phase Runner
// ============================================================

struct Phase {
    const char* name;
    uint64_t start;
    uint64_t end;
};

static bool run_phase(const Phase& phase, int num_threads) {
    uint64_t total = phase.end - phase.start;
    if (total == 0) return false;

    g_found.store(false, std::memory_order_relaxed);
    g_seeds_tested.store(0, std::memory_order_relaxed);

    uint64_t chunk = (total + (uint64_t)num_threads - 1) / (uint64_t)num_threads;

    // Determine what kind of seeds this phase contains
    bool has_small = (phase.start <= 0xFFFFFFFFULL);
    bool has_large = (phase.end > 0x100000000ULL);
    const char* seed_desc;
    if (has_small && has_large)
        seed_desc = "mixed (C++: Knuth LCG for <=32bit, trunc for >32bit | Python: always init_by_array)";
    else if (has_small)
        seed_desc = "C++: Knuth LCG | Python: init_by_array (all seeds)";
    else
        seed_desc = "C++: truncated to uint32 | Python: init_by_array (all seeds)";

    printf("\n======================================================================\n");
    printf("  PHASE: %s\n", phase.name);
    printf("  Range: %" PRIu64 " -> %" PRIu64 "\n", phase.start, phase.end - 1);
    printf("  Total seeds: %" PRIu64 "\n", total);
    printf("  Threads: %d (chunk ~%" PRIu64 " each)\n", num_threads, chunk);
    printf("  Seeding: %s\n", seed_desc);
    printf("======================================================================\n");
    fflush(stdout);

    auto t_start = std::chrono::steady_clock::now();

    std::vector<std::thread> threads(num_threads);
    std::vector<WorkerResult> results(num_threads);

    for (int t = 0; t < num_threads; t++) {
        uint64_t s = phase.start + (uint64_t)t * chunk;
        uint64_t e = std::min(s + chunk, phase.end);
        if (s >= phase.end) {
            results[t].found = false;
            continue;
        }
        threads[t] = std::thread(worker_thread, s, e, &results[t]);
    }

    // Progress monitor
    while (true) {
        std::this_thread::sleep_for(std::chrono::seconds(10));
        if (g_found.load(std::memory_order_relaxed)) break;

        uint64_t tested = g_seeds_tested.load(std::memory_order_relaxed);
        auto now = std::chrono::steady_clock::now();
        double elapsed = std::chrono::duration<double>(now - t_start).count();
        double rate = (elapsed > 0) ? (double)tested / elapsed : 0;
        double pct = 100.0 * (double)tested / (double)total;
        double remaining = (rate > 0) ? (double)(total - tested) / rate : 0;

        printf("  ⏳ %s: %.2f%% | %" PRIu64 "/%" PRIu64 " seeds | %.0f seeds/s | "
               "ETA: %.2fh | Elapsed: %.2fh\n",
               phase.name, pct, tested, total,
               rate, remaining / 3600.0, elapsed / 3600.0);
        fflush(stdout);

        if (tested >= total) break;
    }

    for (int t = 0; t < num_threads; t++) {
        if (threads[t].joinable()) threads[t].join();
    }

    auto t_end = std::chrono::steady_clock::now();
    double elapsed = std::chrono::duration<double>(t_end - t_start).count();

    for (int t = 0; t < num_threads; t++) {
        if (results[t].found) {
            display_match(results[t].seed, results[t].model_idx, elapsed);
            return true;
        }
    }

    printf("  ✗ Phase '%s' complete — no match. (%.1fs)\n", phase.name, elapsed);
    return false;
}

// ============================================================
// Timestamp helpers
// ============================================================

static void print_ts(uint64_t ts, const char* unit) {
    time_t sec;
    if (strcmp(unit, "ms") == 0) sec = (time_t)(ts / 1000);
    else if (strcmp(unit, "us") == 0) sec = (time_t)(ts / 1000000);
    else sec = (time_t)ts;
    char buf[64];
    struct tm* tm_val = gmtime(&sec);
    strftime(buf, sizeof(buf), "%Y-%m-%d %H:%M:%S UTC", tm_val);
    printf("%s", buf);
}

// ============================================================
// Self-test: verify Python seeding produces expected state[0]
// ============================================================

static bool self_test() {
    printf("Running self-tests...\n");
    bool ok = true;

    // Test 1: Python seed(42) must produce state[0] = 0x80000000
    {
        MT19937 mt;
        mt_seed_python(mt, 42);
        if (mt.state[0] != 0x80000000U) {
            printf("  ✗ FAIL: Python seed(42) state[0] = 0x%08X, expected 0x80000000\n", mt.state[0]);
            ok = false;
        } else {
            printf("  ✓ Python seed(42) state[0] = 0x80000000 (init_by_array sentinel)\n");
        }
    }

    // Test 2: C++ seed(42) must produce state[0] = 42
    {
        MT19937 mt;
        mt_seed_cpp(mt, 42);
        if (mt.state[0] != 42U) {
            printf("  ✗ FAIL: C++ seed(42) state[0] = 0x%08X, expected 42\n", mt.state[0]);
            ok = false;
        } else {
            printf("  ✓ C++ seed(42) state[0] = 42 (Knuth LCG)\n");
        }
    }

    // Test 3: Python and C++ must produce DIFFERENT states for same seed
    {
        MT19937 mt_py, mt_cpp;
        mt_seed_python(mt_py, 42);
        mt_seed_cpp(mt_cpp, 42);

        bool different = false;
        for (int i = 0; i < 624; i++) {
            if (mt_py.state[i] != mt_cpp.state[i]) {
                different = true;
                break;
            }
        }
        if (!different) {
            printf("  ✗ FAIL: Python and C++ seed(42) produced identical states!\n");
            ok = false;
        } else {
            printf("  ✓ Python and C++ seed(42) produce different states (correct)\n");
        }
    }

    // Test 4: Python seed(0) must use init_by_array with key={0}
    {
        MT19937 mt;
        mt_seed_python(mt, 0);
        if (mt.state[0] != 0x80000000U) {
            printf("  ✗ FAIL: Python seed(0) state[0] = 0x%08X, expected 0x80000000\n", mt.state[0]);
            ok = false;
        } else {
            printf("  ✓ Python seed(0) state[0] = 0x80000000 (init_by_array)\n");
        }
    }

    // Test 5: Verify uint128 puzzle-65 constant
    {
        uint128_t val65(0x1ULL, 0xA838B13505B26867ULL);
        if (val65.hi != 0x1ULL || val65.lo != 0xA838B13505B26867ULL) {
            printf("  ✗ FAIL: uint128 puzzle-65 constant corrupted\n");
            ok = false;
        } else {
            printf("  ✓ uint128 puzzle-65: hi=0x%" PRIX64 " lo=0x%" PRIX64 "\n", val65.hi, val65.lo);
        }
    }

    // Test 6: Verify all 4 models can generate without crashing
    {
        for (int model_idx = 0; model_idx < 4; model_idx++) {
            MT19937 mt;
            GenFunc gen = GEN_FUNCS[model_idx];

            // Test with Python seeding
            mt_seed_python(mt, 12345);
            for (int n = 1; n <= 10; n++) gen(mt, n);

            // Test with C++ seeding
            mt_seed_cpp(mt, 12345);
            for (int n = 1; n <= 10; n++) gen(mt, n);

            // Test with large seed (Python)
            mt_seed_python(mt, 1388534400000ULL);
            for (int n = 1; n <= 10; n++) gen(mt, n);

            printf("  ✓ Model %d: %s — all seeding paths OK\n", model_idx, MODEL_NAMES[model_idx]);
        }
    }

    // Test 7: Verify Python seed for large value (>32-bit) uses init_by_array
    {
        MT19937 mt;
        mt_seed_python(mt, 1388534400000ULL); // timestamp in ms
        if (mt.state[0] != 0x80000000U) {
            printf("  ✗ FAIL: Python seed(large) state[0] = 0x%08X, expected 0x80000000\n", mt.state[0]);
            ok = false;
        } else {
            printf("  ✓ Python seed(1388534400000) state[0] = 0x80000000 (init_by_array)\n");
        }
    }

    printf("\n");
    return ok;
}

// ============================================================
// MAIN
// ============================================================

int main(int argc, char** argv) {
    int num_threads = (int)std::thread::hardware_concurrency();
    if (num_threads <= 0) num_threads = 4;

    if (argc > 1) {
        int v = atoi(argv[1]);
        if (v > 0) num_threads = v;
    }

    const char* env_workers = getenv("BF_WORKERS");
    if (env_workers) {
        int w = atoi(env_workers);
        if (w > 0) num_threads = w;
    }

    // =====================================================
    // PHASE DEFINITIONS — optimized with TX deadline
    // =====================================================
    //
    // Priority order:
    //   1. HOT ZONE: seconds in the 2 weeks before broadcast
    //   2. HOT ZONE: milliseconds in the 2 weeks before broadcast
    //   3. Narrow seconds: 2014-01-01 → TX deadline
    //   4. Narrow milliseconds: 2014-01-01 → TX deadline
    //   5. Full 32-bit space (covers all uint32 seeds including timestamps)
    //   6. Wide seconds: 2013-01-01 → 2014-01-01
    //   7. Wide milliseconds: 2013-01-01 → 2014-01-01
    //   8. Narrow microseconds: 2014-01-01 → TX deadline [MASSIVE]
    //   9. Wide microseconds: 2013-01-01 → 2014-01-01 [MASSIVE]
    //
    // NOTE: Seeding is now model-aware inside test_seed().
    //   C++ models (0,3): Knuth LCG for seeds ≤ 32-bit, truncated for larger
    //   Python models (1,2): ALWAYS init_by_array regardless of seed size
    // =====================================================

    Phase phases[] = {
        // --- PRIORITY 1: Hot zone (2 weeks before TX) in seconds ---
        // ~1,231,280 seeds — should complete in seconds
        {
            "HOT ZONE seconds (2015-01-01 → TX broadcast)",
            TS_HOT_START,
            TS_HOT_END,
        },

        // --- PRIORITY 2: Hot zone in milliseconds ---
        // ~1.23 billion seeds
        {
            "HOT ZONE milliseconds (2015-01-01 → TX broadcast)",
            TS_HOT_START * 1000ULL,
            TS_HOT_END * 1000ULL,
        },

        // --- PRIORITY 3: Narrow seconds (2014 → TX) ---
        // ~32.77 million seeds (minus hot zone already tested)
        {
            "Narrow seconds 2014 → 2015-01-01 (before hot zone)",
            TS_NARROW_START,
            TS_HOT_START,
        },

        // --- PRIORITY 4: Narrow milliseconds (2014 → hot zone start) ---
        // ~31.5 billion seeds
        {
            "Narrow milliseconds 2014-01-01 → 2015-01-01 (before hot zone)",
            TS_NARROW_START * 1000ULL,
            TS_HOT_START * 1000ULL,
        },

        // --- PRIORITY 5: Full 32-bit space ---
        // 4.29 billion seeds — covers ALL possible uint32 seeds
        // including any non-timestamp 32-bit value
        {
            "Full 32-bit space",
            0ULL,
            0x100000000ULL,
        },

        // --- PRIORITY 6: Wide milliseconds (2013 → 2014) ---
        // ~31.5 billion seeds
        {
            "Wide milliseconds 2013-01-01 → 2014-01-01",
            TS_WIDE_START * 1000ULL,
            TS_NARROW_START * 1000ULL,
        },

        // --- PRIORITY 7: Narrow microseconds (2014 → TX) ---
        // ~32.77 TRILLION seeds — MASSIVE
        {
            "Narrow microseconds 2014-01-01 → TX broadcast ⚠️ MASSIVE",
            TS_NARROW_START * 1000000ULL,
            TS_HOT_END * 1000000ULL,
        },

        // --- PRIORITY 8: Wide microseconds (2013 → 2014) ---
        // ~31.5 TRILLION seeds — MASSIVE
        {
            "Wide microseconds 2013-01-01 → 2014-01-01 ⚠️ MASSIVE",
            TS_WIDE_START * 1000000ULL,
            TS_NARROW_START * 1000000ULL,
        },
    };
    int num_phases = sizeof(phases) / sizeof(phases[0]);

    // =====================================================
    // BANNER
    // =====================================================

    printf("======================================================================\n");
    printf("  BTC PUZZLE GENERATOR — C++ NUCLEAR OPTION v5 (FIXED)\n");
    printf("  Multi-Phase, Multi-Threaded Seed Brute-Force\n");
    printf("----------------------------------------------------------------------\n");
    printf("  TX Broadcast : 2015-01-15 06:07:14 UTC (unix %" PRIu64 ")\n", TX_BROADCAST_UTC);
    printf("  Hard Deadline: 2015-01-15 06:08:00 UTC (unix %" PRIu64 ")\n", TX_DEADLINE);
    printf("  Seed was generated BEFORE this moment.\n");
    printf("----------------------------------------------------------------------\n");
    printf("  FIX v5: Model-aware seeding\n");
    printf("    C++ models  (0,3): Knuth LCG (mt_seed_uint32)\n");
    printf("    Python models(1,2): init_by_array (ALWAYS, per CPython src)\n");
    printf("======================================================================\n");
    printf("  Threads: %d (pass as arg or set BF_WORKERS env var)\n", num_threads);
    printf("  Models : 4\n");
    for (int i = 0; i < 4; i++)
        printf("    [%d] %-35s  seeding: %s\n", i, MODEL_NAMES[i],
               is_python_model(i) ? "init_by_array" : "Knuth LCG");

    printf("\n  Phases planned: %d\n", num_phases);
    printf("  %-60s %20s\n", "  Phase", "Seeds");
    printf("  %s\n", std::string(82, '-').c_str());

    uint64_t total_all = 0;
    for (int i = 0; i < num_phases; i++) {
        uint64_t sz = phases[i].end - phases[i].start;
        total_all += sz;

        printf("  %d. %-56s %20" PRIu64 "\n", i + 1, phases[i].name, sz);

        // Print time range
        if (phases[i].start >= 1000000000000000ULL) {
            printf("     ");
            print_ts(phases[i].start, "us");
            printf(" → ");
            print_ts(phases[i].end - 1, "us");
            printf("\n");
        } else if (phases[i].start >= 10000000000ULL) {
            printf("     ");
            print_ts(phases[i].start, "ms");
            printf(" → ");
            print_ts(phases[i].end - 1, "ms");
            printf("\n");
        } else if (phases[i].start >= 1000000000ULL && phases[i].start < 10000000000ULL) {
            printf("     ");
            print_ts(phases[i].start, "s");
            printf(" → ");
            print_ts(phases[i].end - 1, "s");
            printf("\n");
        }
    }

    printf("\n  Total seeds across all phases: %" PRIu64 "\n", total_all);
    printf("  Total seed × model tests    : %" PRIu64 "\n", total_all * 4);
    printf("======================================================================\n\n");

    // =====================================================
    // SELF-TESTS
    // =====================================================

    if (!self_test()) {
        printf("❌ SELF-TEST FAILED — aborting.\n");
        return 2;
    }
    printf("✅ All self-tests passed.\n\n");

    // =====================================================
    // RUN PHASES
    // =====================================================

    auto t_global = std::chrono::steady_clock::now();
    bool found = false;

    for (int i = 0; i < num_phases; i++) {
        printf("\n");
        for (int j = 0; j < 70; j++) printf("█");
        printf("\n  Starting Phase %d/%d: %s\n", i + 1, num_phases, phases[i].name);
        for (int j = 0; j < 70; j++) printf("█");
        printf("\n");
        fflush(stdout);

        if (run_phase(phases[i], num_threads)) {
            auto t_end = std::chrono::steady_clock::now();
            double total_elapsed = std::chrono::duration<double>(t_end - t_global).count();
            printf("\n\n");
            printf("==============================================================\n");
            printf("  🏆 VICTORY! 🏆\n");
            printf("  Found in Phase %d: %s\n", i + 1, phases[i].name);
            printf("  Total runtime: %.1fs (%.3fh)\n", total_elapsed, total_elapsed / 3600.0);
            printf("==============================================================\n");
            found = true;
            break;
        }
    }

    if (!found) {
        auto t_end = std::chrono::steady_clock::now();
        double total_elapsed = std::chrono::duration<double>(t_end - t_global).count();
        printf("\n\n======================================================================\n");
        printf("  ALL PHASES COMPLETE — NO MATCH FOUND\n");
        printf("  Total runtime: %.1fs (%.2fh)\n", total_elapsed, total_elapsed / 3600.0);
        printf("  Consider:\n");
        printf("    - Non-MT19937 PRNG (ChaCha20, /dev/urandom, etc.)\n");
        printf("    - Seed derived from passphrase (SHA256, etc.)\n");
        printf("    - Multiple entropy sources combined\n");
        printf("    - Custom or modified PRNG implementation\n");
        printf("    - Seed from hardware RNG (not reproducible)\n");
        printf("    - C++ std::seed_seq with multi-word seeds (different algorithm)\n");
        printf("======================================================================\n");
    }

    return found ? 0 : 1;
}