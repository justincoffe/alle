// btc_puzzle_bruteforce.cpp
// BTC Puzzle Generator Seed Brute-Force — C++ Nuclear Option
//
// Compile:
//   g++ -O3 -march=native -pthread -o btc_bruteforce btc_puzzle_bruteforce.cpp
//   (or with clang++)
//
// Run:
//   ./btc_bruteforce [num_threads]
//   BF_WORKERS=16 ./btc_bruteforce
//
// This faithfully replicates the Python V3 script's logic in optimized C++.

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

static inline uint128_t mul_u128_u64(const uint128_t& a, uint64_t b) {
    __uint128_t full = (__uint128_t)a.lo * b;
    uint64_t r_lo = (uint64_t)full;
    uint64_t r_hi = (uint64_t)(full >> 64);
    r_hi += a.hi * b;
    return uint128_t(r_hi, r_lo);
}

// ============================================================
// MT19937 State
// ============================================================

struct MT19937 {
    uint32_t state[624];
    int index;
};

static inline void mt_seed_uint32(MT19937& mt, uint32_t seed) {
    mt.state[0] = seed;
    for (int i = 1; i < 624; i++) {
        uint32_t prev = mt.state[i - 1];
        mt.state[i] = 1812433253U * (prev ^ (prev >> 30)) + (uint32_t)i;
    }
    mt.index = 624;
}

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
        i++;
        j++;
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

static inline void mt_seed_auto(MT19937& mt, uint64_t seed) {
    if (seed <= 0xFFFFFFFFULL) {
        mt_seed_uint32(mt, (uint32_t)seed);
    } else {
        uint32_t key[2];
        int klen = seed_to_key_array(seed, key);
        mt_seed_by_array(mt, key, klen);
    }
}

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
            if (r < width_128) {
                return r + lo_val;
            }
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
            if (mask.lo == 0) {
                mask.hi -= 1;
                mask.lo = 0xFFFFFFFFFFFFFFFFULL;
            } else {
                mask.lo -= 1;
            }
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
static const int NUM_EARLY = 9;

static const KnownKey DEEP_CHECKS[] = {
    {33, uint128_t(7137437912ULL)},
    {34, uint128_t(14133072157ULL)},
    {65, uint128_t(0x0000000000000001ULL, 0xA838B13505B26867ULL)},
};
static const int NUM_DEEP = 3;

// ============================================================
// Seed Tester
// ============================================================

static int test_seed(uint64_t seed, bool use_uint32_path) {
    MT19937 mt;

    for (int model_idx = 0; model_idx < 4; model_idx++) {
        GenFunc gen = GEN_FUNCS[model_idx];

        if (use_uint32_path) {
            mt_seed_uint32(mt, (uint32_t)seed);
        } else {
            mt_seed_auto(mt, seed);
        }

        gen(mt, 1);

        bool failed = false;
        for (int c = 0; c < NUM_EARLY; c++) {
            uint128_t key = gen(mt, EARLY_CHECKS[c].puzzle);
            if (key != EARLY_CHECKS[c].expected) {
                failed = true;
                break;
            }
        }
        if (failed) continue;

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
// Global state
// ============================================================

static std::atomic<bool> g_found(false);
static std::atomic<uint64_t> g_found_seed(0);
static std::atomic<int> g_found_model(-1);
static std::atomic<uint64_t> g_seeds_tested(0);
static std::mutex g_print_mutex;

struct WorkerResult {
    bool found;
    uint64_t seed;
    int model_idx;
};

static void worker_thread(uint64_t start, uint64_t end, bool use_uint32_path,
                           WorkerResult* result)
{
    result->found = false;
    const uint64_t REPORT_INTERVAL = 100000;
    uint64_t local_count = 0;

    for (uint64_t seed = start; seed < end; seed++) {
        if (g_found.load(std::memory_order_relaxed)) return;

        int model = test_seed(seed, use_uint32_path);
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
// Generate and display all keys for a found seed
// ============================================================

static void display_match(uint64_t seed, int model_idx, double elapsed_sec) {
    printf("\n\n");
    printf("==============================================================\n");
    printf("  SEED FOUND: %lu\n", (unsigned long)seed);
    printf("  Seed hex  : 0x%lX\n", (unsigned long)seed);
    printf("  Model     : [%d] %s\n", model_idx, MODEL_NAMES[model_idx]);
    printf("  Time      : %.1f seconds\n", elapsed_sec);
    printf("==============================================================\n\n");

    MT19937 mt;
    mt_seed_auto(mt, seed);
    GenFunc gen = GEN_FUNCS[model_idx];

    struct { int n; uint128_t key; } all_keys[70];
    for (int n = 1; n <= 70; n++) {
        all_keys[n-1].n = n;
        all_keys[n-1].key = gen(mt, n);
    }

    struct { int n; uint128_t expected; } known[] = {
        {2, uint128_t(3)}, {3, uint128_t(7)}, {4, uint128_t(8)},
        {5, uint128_t(21)}, {6, uint128_t(49)}, {7, uint128_t(76)},
        {8, uint128_t(224)}, {9, uint128_t(467)}, {10, uint128_t(514)},
        {33, uint128_t(7137437912ULL)}, {34, uint128_t(14133072157ULL)},
        {65, uint128_t(0x1ULL, 0xA838B13505B26867ULL)},
    };
    int num_known = 12;

    printf("  %7s  %30s  Status\n", "Puzzle", "Key");
    printf("  -------------------------------------------------------\n");

    for (int idx = 0; idx < 70; idx++) {
        int n = all_keys[idx].n;
        uint128_t k = all_keys[idx].key;

        char key_str[64];
        if (k.hi == 0) {
            snprintf(key_str, sizeof(key_str), "%lu", (unsigned long)k.lo);
        } else {
            snprintf(key_str, sizeof(key_str), "0x%lX%016lX",
                     (unsigned long)k.hi, (unsigned long)k.lo);
        }

        const char* status = "";
        for (int ki = 0; ki < num_known; ki++) {
            if (known[ki].n == n) {
                if (k == known[ki].expected)
                    status = " MATCH  <-- KNOWN";
                else
                    status = " MISMATCH  <-- KNOWN";
                break;
            }
        }

        printf("  %7d  %30s  %s\n", n, key_str, status);
    }

    char fname[128];
    snprintf(fname, sizeof(fname), "FOUND_SEED_%lu.txt", (unsigned long)seed);
    FILE* f = fopen(fname, "w");
    if (f) {
        fprintf(f, "Seed: %lu\n", (unsigned long)seed);
        fprintf(f, "Seed hex: 0x%lX\n", (unsigned long)seed);
        fprintf(f, "Model: [%d] %s\n\n", model_idx, MODEL_NAMES[model_idx]);
        for (int idx = 0; idx < 70; idx++) {
            uint128_t k = all_keys[idx].key;
            if (k.hi == 0)
                fprintf(f, "Puzzle %3d: %lu\n", all_keys[idx].n, (unsigned long)k.lo);
            else
                fprintf(f, "Puzzle %3d: 0x%lX%016lX\n", all_keys[idx].n,
                        (unsigned long)k.hi, (unsigned long)k.lo);
        }
        fclose(f);
        printf("\n  Results saved to %s\n", fname);
    }
}

// ============================================================
// Phase Runner
// ============================================================

struct Phase {
    const char* name;
    uint64_t start;
    uint64_t end;
    bool use_uint32_path;
};

static bool run_phase(const Phase& phase, int num_threads) {
    uint64_t total = phase.end - phase.start;
    if (total == 0) return false;

    g_found.store(false, std::memory_order_relaxed);
    g_seeds_tested.store(0, std::memory_order_relaxed);

    uint64_t chunk = (total + (uint64_t)num_threads - 1) / (uint64_t)num_threads;

    printf("\n======================================================================\n");
    printf("  PHASE: %s\n", phase.name);
    printf("  Range: %lu -> %lu\n", (unsigned long)phase.start,
           (unsigned long)(phase.end - 1));
    printf("  Total seeds: %lu\n", (unsigned long)total);
    printf("  Threads: %d (chunk ~%lu each)\n", num_threads, (unsigned long)chunk);
    printf("  Seeding: %s\n", phase.use_uint32_path ? "uint32 (fast)" : "init_by_array (large)");
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
        threads[t] = std::thread(worker_thread, s, e, phase.use_uint32_path, &results[t]);
    }

    while (true) {
        std::this_thread::sleep_for(std::chrono::seconds(10));
        if (g_found.load(std::memory_order_relaxed)) break;

        bool all_done = true;
        for (int t = 0; t < num_threads; t++) {
            if (threads[t].joinable()) {
                all_done = false;
                break;
            }
        }

        uint64_t tested = g_seeds_tested.load(std::memory_order_relaxed);
        auto now = std::chrono::steady_clock::now();
        double elapsed = std::chrono::duration<double>(now - t_start).count();
        double rate = (elapsed > 0) ? (double)tested / elapsed : 0;
        double pct = 100.0 * (double)tested / (double)total;
        double remaining = (rate > 0) ? (double)(total - tested) / rate : 0;

        printf("  >> %s: %.1f%% | %lu/%lu seeds | %.0f seeds/s | "
               "ETA: %.2fh | Elapsed: %.2fh\n",
               phase.name, pct, (unsigned long)tested, (unsigned long)total,
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

    printf("  X Phase '%s' complete -- no match. (%.1fs)\n", phase.name, elapsed);
    return false;
}

// ============================================================
// Timestamp helpers
// ============================================================

static void print_timestamp(uint64_t ts, const char* unit) {
    time_t sec;
    if (strcmp(unit, "ms") == 0) sec = (time_t)(ts / 1000);
    else if (strcmp(unit, "us") == 0) sec = (time_t)(ts / 1000000);
    else sec = (time_t)ts;
    char buf[64];
    struct tm* tm = gmtime(&sec);
    strftime(buf, sizeof(buf), "%Y-%m-%d %H:%M:%S UTC", tm);
    printf("%s", buf);
}

// ============================================================
// MAIN
// ============================================================

int main(int argc, char** argv) {
    int num_threads = (int)std::thread::hardware_concurrency();
    if (num_threads <= 0) num_threads = 4;

    if (argc > 1) {
        num_threads = atoi(argv[1]);
        if (num_threads <= 0) num_threads = 4;
    }

    const char* env_workers = getenv("BF_WORKERS");
    if (env_workers) {
        int w = atoi(env_workers);
        if (w > 0) num_threads = w;
    }

    const uint64_t TS_START_NARROW = 1388534400ULL;
    const uint64_t TS_END_NARROW   = 1451606400ULL;
    const uint64_t TS_START_WIDE   = 1356998400ULL;
    const uint64_t TS_END_WIDE     = 1483228800ULL;

    Phase phases[] = {
        {
            "UNIX seconds 2014-2015 (narrow)",
            TS_START_NARROW,
            TS_END_NARROW,
            true
        },
        {
            "UNIX milliseconds 2014-2015 (narrow)",
            TS_START_NARROW * 1000ULL,
            TS_END_NARROW * 1000ULL,
            false
        },
        {
            "Full 32-bit space",
            0ULL,
            0x100000000ULL,
            true
        },
        {
            "UNIX milliseconds 2013-2014 (before narrow)",
            TS_START_WIDE * 1000ULL,
            TS_START_NARROW * 1000ULL,
            false
        },
        {
            "UNIX milliseconds 2015-2017 (after narrow)",
            TS_END_NARROW * 1000ULL,
            TS_END_WIDE * 1000ULL,
            false
        },
        {
            "UNIX microseconds 2014-2015 [MASSIVE]",
            TS_START_NARROW * 1000000ULL,
            TS_END_NARROW * 1000000ULL,
            false
        },
    };
    int num_phases = sizeof(phases) / sizeof(phases[0]);

    printf("======================================================================\n");
    printf("  BTC PUZZLE GENERATOR — C++ NUCLEAR OPTION\n");
    printf("  Multi-Phase, Multi-Threaded Seed Brute-Force\n");
    printf("======================================================================\n");
    printf("  Threads: %d (pass as arg or set BF_WORKERS env var)\n", num_threads);
    printf("  Models : 4\n");
    for (int i = 0; i < 4; i++)
        printf("    [%d] %s\n", i, MODEL_NAMES[i]);

    printf("\n  Phases planned: %d\n", num_phases);
    printf("  --------------------------------------------------------\n");

    uint64_t total_all = 0;
    for (int i = 0; i < num_phases; i++) {
        uint64_t sz = phases[i].end - phases[i].start;
        total_all += sz;
        printf("  Phase %d: %s\n", i + 1, phases[i].name);
        printf("           Range: %lu -> %lu\n",
               (unsigned long)phases[i].start, (unsigned long)(phases[i].end - 1));
        printf("           Seeds: %lu\n", (unsigned long)sz);

        if (phases[i].start >= 1000000000000000ULL) {
            printf("           ~ ");
            print_timestamp(phases[i].start, "us");
            printf(" -> ");
            print_timestamp(phases[i].end - 1, "us");
            printf("\n");
        } else if (phases[i].start >= 10000000000ULL) {
            printf("           ~ ");
            print_timestamp(phases[i].start, "ms");
            printf(" -> ");
            print_timestamp(phases[i].end - 1, "ms");
            printf("\n");
        } else if (phases[i].start >= 1000000000ULL) {
            printf("           ~ ");
            print_timestamp(phases[i].start, "s");
            printf(" -> ");
            print_timestamp(phases[i].end - 1, "s");
            printf("\n");
        }
        printf("\n");
    }

    printf("  Total seeds across all phases: %lu\n", (unsigned long)total_all);
    printf("  Total seed x model tests: %lu\n", (unsigned long)(total_all * 4));
    printf("======================================================================\n\n");

    printf("Verifying models...\n");
    for (int model_idx = 0; model_idx < 4; model_idx++) {
        MT19937 mt;
        mt_seed_uint32(mt, 42);
        GenFunc gen = GEN_FUNCS[model_idx];
        for (int n = 1; n <= 10; n++) gen(mt, n);

        mt_seed_auto(mt, 1388534400000ULL);
        for (int n = 1; n <= 10; n++) gen(mt, n);

        printf("  OK Model %d: %s\n", model_idx, MODEL_NAMES[model_idx]);
    }

    {
        uint128_t val65(0x1ULL, 0xA838B13505B26867ULL);
        printf("  OK uint128 puzzle-65 check: hi=0x%lX lo=0x%lX\n",
               (unsigned long)val65.hi, (unsigned long)val65.lo);
    }
    printf("\n");

    auto t_global = std::chrono::steady_clock::now();
    bool found = false;

    for (int i = 0; i < num_phases; i++) {
        printf("\n");
        for (int j = 0; j < 70; j++) printf("#");
        printf("\n  Starting Phase %d/%d: %s\n", i + 1, num_phases, phases[i].name);
        for (int j = 0; j < 70; j++) printf("#");
        printf("\n");
        fflush(stdout);

        if (run_phase(phases[i], num_threads)) {
            auto t_end = std::chrono::steady_clock::now();
            double total_elapsed = std::chrono::duration<double>(t_end - t_global).count();
            printf("\n\n");
            printf("==============================================================\n");
            printf("  VICTORY!\n");
            printf("  Found in Phase %d: %s\n", i + 1, phases[i].name);
            printf("  Total runtime: %.1fs\n", total_elapsed);
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
        printf("======================================================================\n");
    }

    return found ? 0 : 1;
}
