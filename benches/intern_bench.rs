use criterion::{Criterion, criterion_group, criterion_main};
use intern::Interned;
use lasso::{Spur, ThreadedRodeo};
use std::{hint::black_box, thread};

// === Lasso Interner ===
// lasso@0.7: ThreadedRustHen was renamed to RustHen
// Spur has no generic parameters — just `Spur`
type LassoInterner = ThreadedRodeo;

// Common test: 100 unique strings, repeated 1000x
const TEST_STRINGS: &[&str] = &[
    "hello",
    "world",
    "foo",
    "bar",
    "baz",
    "qux",
    "quux",
    "corge",
    "grault",
    "garply",
    "waldo",
    "fred",
    "plugh",
    "xyzzy",
    "thud",
    "apple",
    "banana",
    "cherry",
    "date",
    "elderberry",
    "fig",
    "grape",
    "honeydew",
    "kiwi",
    "lemon",
    "mango",
    "nectarine",
    "orange",
    "papaya",
    "quince",
    "raspberry",
    "strawberry",
    "tangerine",
    "ugli",
    "vanilla",
    "watermelon",
    "xigua",
    "yuzu",
    "zucchini",
    "alpha",
    "beta",
    "gamma",
    "delta",
    "epsilon",
    "zeta",
    "eta",
    "theta",
    "iota",
    "kappa",
    "lambda",
    "mu",
    "nu",
    "xi",
    "omicron",
    "pi",
    "rho",
    "sigma",
    "tau",
    "upsilon",
    "phi",
    "chi",
    "psi",
    "omega",
    "one",
    "two",
    "three",
    "four",
    "five",
    "six",
    "seven",
    "eight",
    "nine",
    "ten",
    "eleven",
    "twelve",
    "thirteen",
    "fourteen",
    "fifteen",
    "sixteen",
    "seventeen",
    "eighteen",
    "nineteen",
    "twenty",
    "hundred",
    "thousand",
    "million",
    "billion",
    "trillion",
    "zero",
];

// Generate 100k entries by cycling through TEST_STRINGS
fn generate_workload() -> Vec<&'static str> {
    let mut workload = Vec::with_capacity(100_000);
    for i in 0..100_000 {
        workload.push(TEST_STRINGS[i % TEST_STRINGS.len()]);
    }
    workload
}

// === Benchmark Group ===
fn intern_benchmark(c: &mut Criterion) {
    let workload = generate_workload();

    // --- First 10k internings ---
    // Both sides start from an empty interner each iteration and keep every handle alive
    // until the iteration ends (for `intern` that is what empties the global interner again).
    c.bench_function("intern/first_10k", |b| {
        b.iter(|| {
            let mut handles = Vec::with_capacity(10_000);
            for &s in &workload[..10_000] {
                let interned = Interned::<str>::from(s);
                black_box(interned.as_inner());
                handles.push(interned);
            }
            black_box(handles);
        })
    });

    c.bench_function("lasso/first_10k_roundtrip", |b| {
        b.iter(|| {
            let interner = LassoInterner::new();
            let mut keys = Vec::with_capacity(10_000);
            for &s in &workload[..10_000] {
                let key = interner.get_or_intern(s);
                black_box(interner.resolve(&key));
                keys.push(key);
            }
            black_box((interner, keys));
        })
    });

    // --- Repeated lookups (hot path) ---
    // For your crate: we can do ptr_eq
    c.bench_function("intern/lookup_100k", |b| {
        let _interns: Vec<Interned<str>> = workload[..10_000].iter().map(|&s| s.into()).collect();
        b.iter(|| {
            for &s in &workload {
                let _interned = Interned::<str>::from(s); // hits cache
                black_box(_interned);
            }
        })
    });

    // --- Repeated lookups (hot path) ---
    // For your crate: we can do ptr_eq
    c.bench_function("lasso/lookup_100k_roundtrip", |b| {
        let interner = LassoInterner::new();
        // Pre-populate
        for &s in &workload[..10_000] {
            interner.get_or_intern(s);
        }
        b.iter(|| {
            for &s in &workload {
                let key = interner.get_or_intern(s);
                let resolved = interner.resolve(&key); // ← critical!
                black_box(resolved);
            }
        })
    });

    // --- Concurrent interning into one shared interner, each thread keeping its handles ---
    c.bench_function("intern/concurrent_10k_threads", |b| {
        b.iter(|| {
            thread::scope(|scope| {
                for _ in 0..10 {
                    scope.spawn(|| {
                        let handles: Vec<Interned<str>> =
                            workload[..10_000].iter().map(|&s| s.into()).collect();
                        black_box(handles);
                    });
                }
            });
        })
    });

    c.bench_function("lasso/concurrent_10k_threads", |b| {
        b.iter(|| {
            let interner = LassoInterner::new();
            thread::scope(|scope| {
                for _ in 0..10 {
                    scope.spawn(|| {
                        let keys: Vec<Spur> = workload[..10_000]
                            .iter()
                            .map(|&s| interner.get_or_intern(s))
                            .collect();
                        black_box(keys);
                    });
                }
            });
            black_box(interner);
        })
    });

    // --- Concurrent lookups against one shared, pre-populated interner (read-heavy) ---
    c.bench_function("intern/concurrent_lookup_100k", |b| {
        let _keep_alive: Vec<Interned<str>> = TEST_STRINGS.iter().map(|&s| s.into()).collect();
        b.iter(|| {
            thread::scope(|scope| {
                for _ in 0..10 {
                    scope.spawn(|| {
                        for &s in &workload {
                            black_box(Interned::<str>::from(s));
                        }
                    });
                }
            });
        })
    });

    c.bench_function("lasso/concurrent_lookup_100k", |b| {
        let interner = LassoInterner::new();
        for &s in TEST_STRINGS {
            interner.get_or_intern(s);
        }
        b.iter(|| {
            thread::scope(|scope| {
                for _ in 0..10 {
                    scope.spawn(|| {
                        for &s in &workload {
                            let key = interner.get_or_intern(s);
                            black_box(interner.resolve(&key));
                        }
                    });
                }
            });
        })
    });
}

// === Memory Usage Comparison ===
fn memory_comparison(c: &mut Criterion) {
    let workload = generate_workload();

    c.bench_function("intern/memory_usage", |b| {
        b.iter(|| {
            let _interns: Vec<_> = workload.iter().map(|&s| Interned::<str>::from(s)).collect();
            black_box(_interns);
        })
    });

    c.bench_function("lasso/memory_usage", |b| {
        b.iter(|| {
            let interner = LassoInterner::new();
            let _spurs: Vec<Spur> = workload
                .iter()
                .map(|&s| interner.get_or_intern(s))
                .collect(); // <-- NO GENERIC!
            black_box(_spurs);
        })
    });
}

criterion_group!(benches, intern_benchmark, memory_comparison);
criterion_main!(benches);
