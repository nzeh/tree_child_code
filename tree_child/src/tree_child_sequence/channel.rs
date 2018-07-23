//! This module implements a channel that can only contain one message at any time.  It maintains
//! whether the thread at the receiving end of the channel is idle or busy and supports sending
//! only to busy or idle threads.

use std::cell::UnsafeCell;
use std::clone::Clone;
use std::sync::Arc;
use std::sync::atomic::{AtomicBool, Ordering};
use std::thread::yield_now;

/// Create a new channel
pub fn channel<T: Clone>() -> (Sender<T>, Receiver<T>) {
    let updating = Arc::new(AtomicBool::new(false));
    let busy     = Arc::new(UnsafeCell::new(false));
    let content  = Arc::new(UnsafeCell::new(None));
    let channel  = Channel { updating, busy, content };
    let sender   = Sender { channel: channel.clone() };
    let receiver = Receiver { channel };
    (sender, receiver)
}

/// The sending end of the channel
#[derive(Clone)]
pub struct Sender<T> {
    channel: Channel<T>
}

impl<T> Sender<T> {

    /// Send an item to the receiver.  This method blocks until the channel is empty and the item
    /// can be sent.
    pub fn _send(&self, item: T) {
        loop {
            let channel = self.channel.lock();
            if channel.content.is_none() {
                *channel.content = Some(item);
                return;
            }
            yield_now();
        }
    }

    /// Send an item to the receiver.  This method does not wait for the channel to be empty and
    /// simply overwrites the contents of the channel.
    pub fn send_overwrite(&self, item: T) {
        let channel = self.channel.lock();
        *channel.content = Some(item);
    }

    /// Send an item to the receiver.  This method does not wait for the channel to be empty and
    /// simply drops the given message if the channel already contains a message.
    pub fn send_drop(&self, item: T) -> Status {
        let channel = self.channel.lock();
        if channel.content.is_none() {
            *channel.content = Some(item);
            Status::Success
        } else {
            Status::FailFull
        }
    }

    /// Send an item to the receiver.  This method does not block.  The send succeeds if the
    /// channel is empty and the thread is currently idle or empty as indicated by the provided
    /// busy-flag.  In this case, the return values is `Status::Success`.  If the send fails
    /// because the channel is full, the return value is `Status::FailFull`.  If the send fails
    /// because the thread is in the wrong state (idle if busy is expected or vice versa), the
    /// return value is `Status::FailState`.
    pub fn send_if<Producer>(&self, item: Producer, busy: bool) -> Status
        where Producer: FnOnce() -> T
    {
        let channel = self.channel.lock();
        if *channel.busy != busy {
            Status::FailState
        } else if channel.content.is_some() {
            Status::FailFull
        } else {
            *channel.content = Some(item());
            Status::Success
        }
    }

    /// Send an item to the receiver.  This method behaves exactly like `send_if` except that it
    /// ignores a full buffer and simply overwrites the buffer contents.  Thus, its only possible
    /// return values are `Status::Success` and `Status::FailState`.
    pub fn _send_overwrite_if<Producer>(&self, item: Producer, busy: bool) -> Status
        where Producer: FnOnce() -> T
    {
        let channel = self.channel.lock();
        if *channel.busy == busy {
            *channel.content = Some(item());
            Status::Success
        } else {
            Status::FailState
        }
    }
}

/// The receiving end of the channel
#[derive(Clone)]
pub struct Receiver<T> {
    channel: Channel<T>
}

impl<T> Receiver<T> {

    /// Wait for an element in the channel, remove it, and return it.
    pub fn recv(&self) -> T {
        loop {
            {
                let channel = self.channel.lock();
                if let Some(item) = channel.content.take() {
                    return item;
                }
            }
            yield_now();
        }
    }

    /// If there's an element currently in the channel, remove it, and return.  Otherwise, leave
    /// the channel unchanged and return `None`.
    pub fn try_recv(&self) -> Option<T> {
        let channel = self.channel.lock();
        channel.content.take()
    }

    /// Change the busy flag of the channel to the given value.
    pub fn set_state(&self, busy: bool) {
        let channel = self.channel.lock();
        *channel.busy = busy;
    }
}

/// The internal representation of the channel
#[derive(Clone)]
struct Channel<T> {

    /// Is the channel being updated?
    updating: Arc<AtomicBool>,

    /// Is the receiving thread busy?
    busy: Arc<UnsafeCell<bool>>,

    /// The content of the channel
    content: Arc<UnsafeCell<Option<T>>>,
}

impl<T> Channel<T> {

    /// Lock the channel
    fn lock(&self) -> LockedChannel<T> {
        while self.updating.fetch_or(true, Ordering::AcqRel) {}
        let busy    = unsafe { &mut *self.busy.get() };
        let content = unsafe { &mut *self.content.get() };
        LockedChannel { channel: self, busy, content }
    }
}

unsafe impl<T> Send for Channel<T> {}

/// A locked channel can be manipulated
struct LockedChannel<'a, T: 'a> {

    /// A reference to the underlying channel
    channel: &'a Channel<T>,

    /// The busy flag of the channel
    busy: &'a mut bool,

    /// The content of the channel
    content: &'a mut Option<T>,
}

impl<'a, T> Drop for LockedChannel<'a, T> {
    fn drop(&mut self) {
        self.channel.updating.store(false, Ordering::Release);
    }
}

/// The status type returned by the various send functions
//#[cfg_attr(test, derive(Debug))]
#[derive(Debug, PartialEq)]
pub enum Status {

    /// The send succeeded
    Success,

    /// The send failed because there is already a message in the channel
    FailFull,

    /// The send failed because the thread is in the wrong state
    FailState,
}

#[cfg(test)]
mod tests {

    use std::thread;

    /// Test sending a message unconditionally
    #[test]
    fn send() {
        let (sender, receiver) = super::channel();
        let producer = thread::spawn(move || {
            sender._send(1);
            sender._send(2);
            sender._send(3);
        });
        let consumer = thread::spawn(move || {
            let x = receiver.recv();
            let y = receiver.recv();
            let z = receiver.recv();
            vec![x, y, z]
        });
        producer.join().unwrap();
        let result = consumer.join().unwrap();
        assert_eq!(result, vec![1, 2, 3]);
    }

    /// Test sending a message only if the worker is busy
    #[test]
    fn send_if() {
        let (sender, receiver) = super::channel();
        assert_eq!(sender.send_if(|| 1, true), super::Status::FailState);
        receiver.set_state(true);
        assert_eq!(sender.send_if(|| 1, true), super::Status::Success);
        assert_eq!(sender.send_if(|| 2, true), super::Status::FailFull);
        assert_eq!(receiver.recv(), 1);
        assert_eq!(sender.send_if(|| 3, true), super::Status::Success);
        assert_eq!(receiver.recv(), 3);
    }

    /// Test sending an overwrite message
    #[test]
    fn send_overwrite() {
        let (sender, receiver) = super::channel();
        sender.send_overwrite(1);
        assert_eq!(receiver.recv(), 1);
        sender.send_overwrite(1);
        sender.send_overwrite(2);
        assert_eq!(receiver.recv(), 2);
    }

    /// Test sending an overwrite message
    #[test]
    fn send_drop() {
        let (sender, receiver) = super::channel();
        sender.send_drop(1);
        assert_eq!(receiver.recv(), 1);
        sender.send_drop(2);
        sender.send_drop(3);
        assert_eq!(receiver.recv(), 2);
    }

    /// Test sending an overwrite message only if the worker is idle
    #[test]
    fn send_overwrite_if() {
        let (sender, receiver) = super::channel();
        receiver.set_state(true);
        assert_eq!(sender._send_overwrite_if(|| 1, false), super::Status::FailState);
        receiver.set_state(false);
        assert_eq!(sender._send_overwrite_if(|| 1, false), super::Status::Success);
        assert_eq!(receiver.recv(), 1);
        assert_eq!(sender._send_overwrite_if(|| 1, false), super::Status::Success);
        assert_eq!(sender._send_overwrite_if(|| 2, false), super::Status::Success);
        assert_eq!(receiver.recv(), 2);
    }

    /// Test try_recv
    #[test]
    fn try_recv() {
        let (sender, receiver) = super::channel();
        assert_eq!(receiver.try_recv(), None);
        sender._send(1);
        assert_eq!(receiver.try_recv(), Some(1));
        assert_eq!(receiver.try_recv(), None);
        sender._send(2);
        assert_eq!(receiver.try_recv(), Some(2));
        assert_eq!(receiver.try_recv(), None);
    }
}
