use std::sync::{Arc, Condvar, Mutex};
use std::thread;

// Corresponds to CONSTANT N in TLA+
const N: usize = 10;

// Newtype pattern for Image, as requested.
// In practice, we use usize indices 0..N-1 to represent images.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct Image(usize);

// Corresponds to ImageState == {"None", "Loaded"}
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum ImageState {
    None,
    Loaded,
}

// Corresponds to the VARIABLES image_states, keys_used
#[derive(Debug)]
struct ImageCache {
    image_states: Vec<ImageState>,
    keys_used: usize,
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
    };

    // The shared state is protected by a Mutex.
    // The Condvar is used to signal state changes between threads.
    let shared_state = Arc::new((Mutex::new(image_cache), Condvar::new()));
    let mut handles = vec![];

    println!("Spawning 2 threads to load {} images...", N);

    // Spawn two threads.
    for thread_id in 0..2 {
        let state_clone = Arc::clone(&shared_state);
        let handle = thread::spawn(move || {
            let (lock, cvar) = &*state_clone;
            
            // The loop corresponds to the [][Next] part of the spec.
            // Each iteration is a "Next" step.
            loop {
                let mut cache = lock.lock().unwrap();

                // Check for the "Done" condition. If all images are loaded, the thread's work is finished.
                if all_images_loaded(&cache) {
                    println!("Thread {}: All images are loaded. Exiting.", thread_id);
                    break;
                }

                // This corresponds to "\E i \in Image: LoadImage(i)"
                // Find an image where the state is "None".
                match cache.image_states.iter().position(|&s| s == ImageState::None) {
                    Some(i) => {
                        // This block implements the "LoadImage(i)" action.
                        println!("Thread {}: Loading image {}.", thread_id, i);
                        cache.image_states[i] = ImageState::Loaded;
                        cache.keys_used += 1;
                        
                        // Notify other threads that the state has changed.
                        // This is important for waking up threads that are waiting.
                        cvar.notify_all();
                    }
                    None => {
                        // No images are in the "None" state, but not all are "Loaded" yet.
                        // This means another thread is currently loading an image.
                        // We wait for a signal that the state has changed.
                        cache = cvar.wait(cache).unwrap();
                    }
                }
                // The mutex lock is released at the end of the scope.
            }
        });
        handles.push(handle);
    }

    // Wait for both threads to complete their execution by joining them.
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
