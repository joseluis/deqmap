// deqmap::benches::deqmap
//
//!
//

use criterion::{
    black_box as bb, criterion_group, criterion_main, BatchSize, BenchmarkId, Criterion,
};
use deqmap::DeqMap;

/* global constants */

/// different loop lengths for calling methods
const LOOPS: [usize; 2] = [100, 10_000];

/// number of values (or keys+values) to fill a deqmap with, before benchmarking
const INITS: [usize; 3] = [0, 100, 10_000];

/* deqmap constructors */

/// New deqmap with `len` values
fn d_v(len: usize) -> DeqMap<usize, usize> {
    DeqMap::from_iter(len..(len * 2))
}

/// New deqmap with `len` keyed values
fn d_kv(len: usize) -> DeqMap<usize, usize> {
    DeqMap::from_iter((len..(len * 2)).map(|v| (v, v)))
}

/* methods benchmarks */

/// benchmark push methods
fn push(c: &mut Criterion) {
    let mut group = c.benchmark_group(format!["push"]);

    macro_rules! bench {
        (single: $row:expr, $constructor:expr, $col:literal, $closure:expr) => {
            let id = BenchmarkId::new($col, $row);
            group.bench_function(id, |b| {
                b.iter_batched_ref(|| $constructor, $closure, BatchSize::SmallInput)
            });
        };
        (multi: $row:expr, $constructor:expr, $($col:literal, $closure:expr),*) => {
            $( bench![single: $row, $constructor, $col, $closure ]; )+
        };

        // for each constructor (row) > for each loop len (row) > bench each function (col)
        ($loops:expr, $( ( $row:expr, $constructor:expr ) ),+ ) => {
            $( for l in $loops {
                    bench![multi: format!["{}: push {} v", $row, l], $constructor,
                    "push_back", |d| { for v in 0..l { bb(d.push_back(v)); } },
                    "push_front", |d| { for v in 0..l { bb(d.push_front(v)); } },
                    "push_at", |d| { for v in 0..l { let _ = bb(d.push_at(v, v)); } },
                    "push_at_unchecked", |d| { for v in 0..l { let _ = bb(d.push_at_unchecked(v, v)); } }
                    ];
            } )+
        };
    }

    for n in INITS {
        bench![
            LOOPS,
            (format!["from {n} v"], d_v(n)),
            (format!["from {n} k,v"], d_kv(n))
        ];
    }

    group.finish();
}

/// benchmark insert methods
fn insert(c: &mut Criterion) {
    let mut group = c.benchmark_group(format!["insert"]);

    macro_rules! bench {
        (single: $row:expr, $constructor:expr, $col:literal, $closure:expr) => {
            let id = BenchmarkId::new($col, $row);
            group.bench_function(id, |b| {
                b.iter_batched_ref(|| $constructor, $closure, BatchSize::SmallInput)
            });
        };
        (multi: $row:expr, $constructor:expr, $($col:literal, $closure:expr),*) => {
            $( bench![single: $row, $constructor, $col, $closure ];)+
        };

        // for each constructor (row) > for each loop len (row) > bench each function (col)
        ($loops:expr, $( ( $row:expr, $constructor:expr ) ),+ ) =>{
            $( for l in $loops {
                bench![multi: format!["{}: insert {} k,v", $row, l], $constructor,
                "insert_back", |d| { for v in 0..l { bb(d.insert_back(v, v)); } },
                "insert_front", |d| { for v in 0..l { bb(d.insert_front(v, v)); } },
                "insert_at", |d| { for v in 0..l { let _ = bb(d.insert_at(v, v, v)); } },
                "insert_at_unchecked", |d| { for v in 0..l { let _ = bb(d.insert_at_unchecked(v, v, v)); } }
                ];
            } )+
        };
    }

    for n in INITS {
        bench![
            LOOPS,
            (format!["from {n} v"], d_v(n)),
            (format!["from {n} k,v"], d_kv(n))
        ];
    }

    group.finish();
}

/// benchmark pop methods
fn pop(c: &mut Criterion) {
    let mut group = c.benchmark_group(format!["pop"]);

    macro_rules! bench {
        (single: $row:expr, $constructor:expr, $col:literal, $closure:expr) => {
            let id = BenchmarkId::new($col, $row);
            group.bench_function(id, |b| {
                b.iter_batched_ref(|| $constructor, $closure, BatchSize::SmallInput)
            });
        };
        (multi: $row:expr, $constructor:expr, $($col:literal, $closure:expr),*) => {
            $( bench![single: $row, $constructor, $col, $closure ];)+
        };

        // for each constructor (row) > for each loop len (row) > bench each function (col)
        ($loops:expr, $init:expr, $( ( $row:expr, $constructor:expr ) ),+ ) =>{
            $( for l in $loops {
                // do not pop more values than we have initialized
                if l <= $init {
                    bench![multi: format!["{}: pop {} v", $row, l], $constructor,
                    "pop_back", |d| { for _ in 0..l { let _ = bb(d.pop_back()); } },
                    "pop_front", |d| { for _ in 0..l { let _ = bb(d.pop_front()); } },
                    "pop_back_with_key", |d| { for _ in 0..l { let _ = bb(d.pop_back_with_key()); } },
                    "pop_front_with_key", |d| { for _ in 0..l { let _ = bb(d.pop_back_with_key()); } }
                    ];
                }
            } )+
        };
    }

    for n in INITS {
        bench![
            LOOPS,
            n,
            (format!["from {n} v"], d_v(n)),
            (format!["from {n} k,v"], d_kv(n))
        ];
    }

    group.finish();
}

/// benchmark get methods
fn get(c: &mut Criterion) {
    let mut group = c.benchmark_group(format!["get"]);

    macro_rules! bench {
        (single: $row:expr, $constructor:expr, $col:literal, $closure:expr) => {
            let id = BenchmarkId::new($col, $row);
            group.bench_function(id, |b| {
                b.iter_batched_ref(|| $constructor, $closure, BatchSize::SmallInput)
            });
        };
        (multi: $row:expr, $constructor:expr, $($col:literal, $closure:expr),*) => {
            $( bench![single: $row, $constructor, $col, $closure ];)+
        };

        // for each constructor (row) > for each loop len (row) > bench each function (col)
        ($loops:expr, $init:expr, $( ( $row:expr, $constructor:expr ) ),+ ) =>{
            $( for l in $loops {
                // do not get more values than we have initialized
                if l <= $init {
                    bench![multi: format!["{}: get {} v", $row, l], $constructor,
                    "get", |d| { for _ in 0..l { let _ = bb(d.get(l)); } },
                    "get_mut", |d| { for _ in 0..l { let _ = bb(d.get_mut(l)); } },
                    "get_with_key", |d| { for _ in 0..l { let _ = bb(d.get_with_key(l)); } },
                    "get_mut_with_key", |d| { for _ in 0..l { let _ = bb(d.get_mut_with_key(l)); } }
                    ];
                }
            } )+
        };
    }

    for n in INITS {
        bench![
            LOOPS,
            n,
            (format!["from {n} v"], d_v(n)),
            (format!["from {n} k,v"], d_kv(n))
        ];
    }

    group.finish();
}

/// benchmark find methods
fn find(c: &mut Criterion) {
    let mut group = c.benchmark_group(format!["find"]);

    macro_rules! bench {
        (single: $row:expr, $constructor:expr, $col:literal, $closure:expr) => {
            let id = BenchmarkId::new($col, $row);
            group.bench_function(id, |b| {
                b.iter_batched_ref(|| $constructor, $closure, BatchSize::SmallInput)
            });
        };
        (multi: $row:expr, $constructor:expr, $($col:literal, $closure:expr),*) => {
            $( bench![single: $row, $constructor, $col, $closure ];)+
        };

        // for each constructor (row) > for each loop len (row) > bench each function (col)
        ($loops:expr, $init:expr, $( ( $row:expr, $constructor:expr ) ),+ ) =>{
            $( for l in $loops {
                // do not find more values than we have initialized
                if l <= $init {
                    bench![multi: format!["{}: find {} v", $row, l], $constructor,
                    "find_key", |d| { for _ in 0..l { let _ = bb(d.find_key(l)); } },
                    "find_key_value", |d| { for _ in 0..l { let _ = bb(d.find_key_value(l)); } },
                    "find_mut_key_value", |d| { for _ in 0..l { let _ = bb(d.find_mut_key_value(l)); } }
                    ];
                }
            } )+
        };
    }

    for n in INITS {
        bench![
            LOOPS,
            n,
            (format!["from {n} v"], d_v(n)),
            (format!["from {n} k,v"], d_kv(n))
        ];
    }

    group.finish();
}

/// benchmark set methods
fn set(c: &mut Criterion) {
    let mut group = c.benchmark_group(format!["set"]);

    macro_rules! bench {
        (single: $row:expr, $constructor:expr, $col:literal, $closure:expr) => {
            let id = BenchmarkId::new($col, $row);
            group.bench_function(id, |b| {
                b.iter_batched_ref(|| $constructor, $closure, BatchSize::SmallInput)
            });
        };
        (multi: $row:expr, $constructor:expr, $($col:literal, $closure:expr),*) => {
            $( bench![single: $row, $constructor, $col, $closure ];)+
        };

        // for each constructor (row) > for each loop len (row) > bench each function (col)
        ($loops:expr, $init:expr, $( ( $row:expr, $constructor:expr ) ),+ ) =>{
            $( for l in $loops {
                // do not set more values than we have initialized
                if l <= $init {
                    bench![multi: format!["{}: set {} v", $row, l], $constructor,
                    "set_key", |d| { for _ in 0..l { let _ = bb(d.set_key(l, l)); } },
                    "reset_key", |d| { for _ in 0..l { let _ = bb(d.reset_key(&($init + l), l)); } }
                    ];
                }
            } )+
        };
    }

    for n in INITS {
        bench![LOOPS, n, (format!["from {n} k,v"], d_kv(n))];
    }

    group.finish();
}

/* criterion config & run */

mod config {
    #![allow(dead_code)]
    use super::Criterion;

    pub fn default() -> Criterion {
        Criterion::default()
    }

    pub fn short_warmup() -> Criterion {
        Criterion::default().warm_up_time(std::time::Duration::new(1, 0))
    }

    // very short, for debugging, also use this:
    // b.iter_batched_ref(|| 0, |_| { }, BatchSize::SmallInput)
    pub fn test_debug() -> Criterion {
        Criterion::default()
            .without_plots()
            .sample_size(10)
            .warm_up_time(std::time::Duration::new(0, 100))
            .measurement_time(std::time::Duration::new(0, 100))
            .nresamples(10)
    }
}

criterion_group!(
    name=short;
    config=config::short_warmup();
    targets=push,insert,pop,get,find,set
);
criterion_main!(short);
