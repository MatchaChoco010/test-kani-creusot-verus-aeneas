use std::sync::Arc;
use std::sync::atomic::{AtomicU32, Ordering};
use std::thread;

fn increment(counter: &AtomicU32) {
    counter.fetch_add(1, Ordering::SeqCst);
}

pub fn count_to_two() -> u32 {
    let counter = Arc::new(AtomicU32::new(0));
    let c1 = Arc::clone(&counter);
    let t1 = thread::spawn(move || increment(&c1));
    let c2 = Arc::clone(&counter);
    let t2 = thread::spawn(move || increment(&c2));
    t1.join().unwrap();
    t2.join().unwrap();
    counter.load(Ordering::SeqCst)
}

// Kani が内部エラーで停止する: thread::spawn に対応していない
// #[cfg(kani)]
// #[kani::proof]
// fn check_count_to_two() {
//     assert_eq!(count_to_two(), 2);
// }

