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
    keys_generated: VecDeque<Key>,
    keys_batch: bool,
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
        keys_generated: VecDeque::new(),
        keys_batch: false,
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
                if let Some(i) = cache.image_states.iter().position(|&s| s == ImageState::None) {
                    println!("Thread {}: StartLoad({})", thread_id, i);
                    cache.image_states[i] = ImageState::PendingKey;
                    cache.image_queue.push_back(i);
                    cvar.notify_all();
                    continue;
                }

                // StartGenerateKeys
                let keys_requested = cache.image_states.iter().filter(|&&s| s == ImageState::PendingKey).count();
                if keys_requested > 0 && cache.keys_generated.len() < N * 2 {
                    let keys_needed = keys_requested.saturating_sub(cache.keys.len());
                    if keys_needed > 0 {
                        println!("Thread {}: StartGenerateKeys ({} keys)", thread_id, keys_needed);
                        // Move the compute-intensive work outside the critical section
                        drop(cache); // Release the lock
                        thread::sleep(std::time::Duration::from_millis(100));
                        let mut cache = lock.lock().unwrap(); // Reacquire the lock
                        for _ in 0..keys_needed {
                            cache.keys_generated.push_back(Key);
                        }
                        cache.keys_batch = true; // Set unconditionally here, per spec
                        cvar.notify_all();
                        continue;
                    } else {
                        cache.keys_batch = true; // Set even if no keys are needed
                        cvar.notify_all();
                    }
                }

                // DoneGenerateKeys
                if !cache.keys_generated.is_empty() {
                    println!("Thread {}: DoneGenerateKeys (moving {} keys)", thread_id, cache.keys_generated.len());
                    while let Some(k) = cache.keys_generated.pop_front() {
                        cache.keys.push_back(k);
                    }
                    cvar.notify_all();
                    continue;
                }

                // Actions on the image at the front of the queue
                if let Some(&front_image_idx) = cache.image_queue.front() {
                    let state = cache.image_states[front_image_idx];

                    // SetKey(i)
                    if state == ImageState::PendingKey && !cache.keys.is_empty() && cache.keys_batch {
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
                        cache.keys_batch = false;
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
