//! Optional Rayon thread-pool wrapper (`-jN`).

pub fn run_with_threads<R: Send>(jobs: usize, f: impl FnOnce() -> R + Send) -> R {
    if jobs <= 1 {
        return f();
    }
    rayon::ThreadPoolBuilder::new()
        .num_threads(jobs)
        .build()
        .expect("rayon thread pool")
        .install(f)
}
