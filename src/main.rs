use std::sync::{Arc, Condvar, Mutex};
use std::thread;
use std::time::Duration;

// Corresponds to CONSTANT N in TLA+
const N: usize = 10;

// Newtype pattern for Image
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct Image(usize);

// Corresponds to ImageState == {"None", "PendingKey", "HasKey", "Loaded"}
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum ImageState {
    None,
    PendingKey,
    HasKey,
    Loaded,
}

// Corresponds to keys \in {"Empty", "Generated"}
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum KeysState {
    Empty,
    Generated,
}

// Corresponds to the VARIABLES image_states, keys_used, keys
#[derive(Debug)]
struct ImageCache {
    image_states: Vec<ImageState>,
    keys_used: usize,
    keys: KeysState,
}

// Helper function to check the "Done" condition from the TLA+ spec.
fn all_images_loaded(cache: &ImageCache) -> bool {
    cache.image_states.iter().all(|&s| s == ImageState::Loaded)
}

fn main() {
    // Corresponds to the "Init" predicate in the TLA+ spec.
    let image_cache = ImageCache {
        image_states: vec![ImageState::None; N],
        keys_used: 0,
        keys: KeysState::Empty,
    };

    let shared_state = Arc::new((Mutex::new(image_cache), Condvar::new()));
    let mut handles = vec![];

    println!("Spawning 2 threads to load {} images with non-blocking key generation...", N);

    for thread_id in 0..2 {
        let state_clone = Arc::clone(&shared_state);
        let handle = thread::spawn(move || {
            let (lock, cvar) = &*state_clone;

            // The loop corresponds to the [][Next] part of the spec.
            loop {
                let mut cache = lock.lock().unwrap();

                // Check for the "Done" condition.
                if all_images_loaded(&cache) {
                    println!("Thread {}: All images are loaded. Exiting.", thread_id);
                    break;
                }

                let mut action_taken = false;

                // The following block attempts to perform one of the actions from the "Next" state transition.
                // The order of checks is chosen to prioritize completing in-progress work.

                // Attempt to perform FinishLoad(i)
                if let Some(i) = cache.image_states.iter().position(|&s| s == ImageState::HasKey) {
                    println!("Thread {}: Finishing load for image {}.", thread_id, i);
                    cache.image_states[i] = ImageState::Loaded;
                    action_taken = true;
                }
                // Attempt to perform SetKey(i)
                else if cache.keys == KeysState::Generated {
                    if let Some(i) = cache.image_states.iter().position(|&s| s == ImageState::PendingKey) {
                        println!("Thread {}: Setting key for image {}.", thread_id, i);
                        cache.image_states[i] = ImageState::HasKey;
                        cache.keys = KeysState::Empty;
                        cache.keys_used += 1;
                        action_taken = true;
                    }
                }
                // Attempt to perform GenerateKey
                else if cache.keys == KeysState::Empty && cache.image_states.iter().any(|&s| s == ImageState::PendingKey) {
                    println!("Thread {}: Generating a key.", thread_id);
                    cache.keys = KeysState::Generated;
                    action_taken = true;
                }
                // Attempt to perform StartLoad(i)
                else if !cache.image_states.iter().any(|&s| s == ImageState::PendingKey) {
                    if let Some(i) = cache.image_states.iter().position(|&s| s == ImageState::None) {
                        println!("Thread {}: Starting load for image {}.", thread_id, i);
                        cache.image_states[i] = ImageState::PendingKey;
                        action_taken = true;
                    }
                }

                if action_taken {
                    // An action was taken, so notify other waiting threads.
                    cvar.notify_all();
                } else {
                    // No action could be taken, so wait for the state to change.
                    cache = cvar.wait(cache).unwrap();
                }
                // Mutex is released here.
            }
        });
        handles.push(handle);
    }

    for handle in handles {
        handle.join().unwrap();
    }

    println!("\nAll threads have finished execution.");

    let final_cache = shared_state.0.lock().unwrap();
    println!("Final keys used: {}", final_cache.keys_used);

    // Verify the final state against the spec's "Done" condition.
    assert!(all_images_loaded(&final_cache));
    assert_eq!(final_cache.keys_used, N);
    println!("System terminated in a correct state.");
}
