use std::collections::VecDeque;
use std::sync::{Arc, Condvar, Mutex};
use std::thread;
use std::time::Duration;

const N: usize = 10;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum ImageState {
    None,
    PendingKey,
    HasKey,
    Loaded,
}

#[derive(Debug, Clone, Copy)]
struct Key;

#[derive(Debug)]
struct ImageCache {
    image_states: Vec<ImageState>,
    image_queue: VecDeque<usize>,
    keys_used: usize,
    keys: VecDeque<Key>,
    pending_keys: bool,
}

fn all_images_loaded(cache: &ImageCache) -> bool {
    cache.image_states.iter().all(|&s| s == ImageState::Loaded) && cache.image_queue.is_empty()
}

fn main() {
    let image_cache = ImageCache {
        image_states: vec![ImageState::None; N],
        image_queue: VecDeque::new(),
        keys_used: 0,
        keys: VecDeque::new(),
        pending_keys: false,
    };

    let shared_state = Arc::new((Mutex::new(image_cache), Condvar::new()));
    let mut handles = vec![];

    for thread_id in 0..2 {
        let state_clone = Arc::clone(&shared_state);
        let handle = thread::spawn(move || {
            let (lock, cvar) = &*state_clone;

            loop {
                let mut cache = lock.lock().unwrap();

                if all_images_loaded(&cache) {
                    println!("Thread {}: All images loaded. Exiting.", thread_id);
                    cvar.notify_all();
                    break;
                }

                // StartLoad(i)
                if let Some(i) = cache
                    .image_states
                    .iter()
                    .position(|&s| s == ImageState::None)
                {
                    println!("Thread {}: StartLoad({})", thread_id, i);
                    cache.image_states[i] = ImageState::PendingKey;
                    cache.image_queue.push_back(i);
                    cvar.notify_all();
                    continue;
                }

                // StartKeyGeneration + GenerateKeys (merged, race-free)
                let keys_requested = cache
                    .image_states
                    .iter()
                    .filter(|&&s| s == ImageState::PendingKey)
                    .count();
                let keys_needed = keys_requested.saturating_sub(cache.keys.len());
                if !cache.pending_keys && keys_requested > 0 {
                    if keys_needed > 0 {
                        println!(
                            "Thread {}: StartKeyGeneration+GenerateKeys ({} keys)",
                            thread_id, keys_needed
                        );
                        cache.pending_keys = true;
                        drop(cache); // Release the lock before intensive work
                        thread::sleep(Duration::from_millis(100));
                        let mut cache = lock.lock().unwrap();
                        for _ in 0..keys_needed {
                            cache.keys.push_back(Key);
                        }
                        cache.pending_keys = false;
                        cvar.notify_all();
                        continue;
                    }
                }

                // Actions on the image at the front of the queue
                if let Some(&front_image_idx) = cache.image_queue.front() {
                    let state = cache.image_states[front_image_idx];

                    // SetKey(i)
                    if state == ImageState::PendingKey && !cache.keys.is_empty() {
                        println!("Thread {}: SetKey({})", thread_id, front_image_idx);
                        cache.keys.pop_front();
                        cache.image_states[front_image_idx] = ImageState::HasKey;
                        cache.keys_used += 1;
                        cvar.notify_all();
                        continue;
                    }
                    // FinishLoad(i)
                    if state == ImageState::HasKey {
                        println!("Thread {}: FinishLoad({})", thread_id, front_image_idx);
                        cache.image_states[front_image_idx] = ImageState::Loaded;
                        cvar.notify_all();
                        continue;
                    }
                    // DequeImage(i)
                    if state == ImageState::Loaded {
                        println!("Thread {}: DequeImage({})", thread_id, front_image_idx);
                        cache.image_queue.pop_front();
                        cvar.notify_all();
                        continue;
                    }
                }

                // If no action could be taken, wait for the state to change.
                cache = cvar.wait(cache).unwrap();
            }
        });
        handles.push(handle);
    }

    for handle in handles {
        handle.join().unwrap();
    }

    let final_cache = shared_state.0.lock().unwrap();
    println!("Final keys used: {}", final_cache.keys_used);
    assert!(all_images_loaded(&final_cache));
    assert_eq!(final_cache.keys_used, N);
    assert!(final_cache.image_queue.is_empty());
    assert!(final_cache.keys.is_empty());
    println!("System terminated in a correct state.");
}
