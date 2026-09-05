//! The actor message envelope (`Message`) and the bounded FIFO mailbox
//! (`MessageQueue`) the host buffers it in.
//!
//! The invariant this file owns: a queue NEVER holds more than `max_len`
//! messages (default `DEFAULT_MAX_MESSAGES` = 65_536; a bound of 0 is
//! clamped to 1). At the bound `push` applies backpressure -- it rejects
//! the message and hands it back as `Err(message)` instead of dropping it
//! silently or growing host memory without bound (availability finding P2);
//! the runtime surfaces the rejection as `RuntimeError::QueueFull`. The
//! in-file tests pin acceptance up to the cap, rejection at it,
//! drain-then-reuse, and the zero-bound clamp.

use std::collections::VecDeque;

use crate::actor::ActorId;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Message {
    pub sender: Option<ActorId>,
    pub receiver: ActorId,
    pub handler: String,
    pub handler_id: u32,
    pub payload: Vec<u8>,
}

/// Default upper bound on the number of undelivered messages a single host
/// buffers. A long-lived host that never fully drains — or a hostile actor
/// that floods `send` — would otherwise grow the queue without bound
/// (availability finding P2). At the bound, `push` applies backpressure:
/// it rejects the message and hands it back to the caller rather than
/// dropping it silently or growing memory. 65_536 is generous for normal
/// actor traffic while still capping worst-case memory.
pub const DEFAULT_MAX_MESSAGES: usize = 65_536;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct MessageQueue {
    queue: VecDeque<Message>,
    max_len: usize,
}

impl Default for MessageQueue {
    fn default() -> Self {
        Self {
            queue: VecDeque::new(),
            max_len: DEFAULT_MAX_MESSAGES,
        }
    }
}

impl Message {
    pub fn system(receiver: ActorId, handler: impl Into<String>, handler_id: u32) -> Self {
        Self {
            sender: None,
            receiver,
            handler: handler.into(),
            handler_id,
            payload: Vec::new(),
        }
    }
}

impl MessageQueue {
    /// Construct a queue with a custom capacity bound. A `max_len` of 0 is
    /// clamped to 1 — a queue must be able to hold at least one message.
    pub fn with_max_len(max_len: usize) -> Self {
        Self {
            queue: VecDeque::new(),
            max_len: max_len.max(1),
        }
    }

    /// Enqueue a message, applying backpressure at the capacity bound.
    /// Returns `Ok(())` when accepted, or `Err(message)` — handing the
    /// rejected message back — when the queue already holds `max_len`
    /// entries. Callers surface the rejection as a runtime error instead
    /// of letting the host's memory grow without bound.
    pub fn push(&mut self, message: Message) -> Result<(), Message> {
        if self.queue.len() >= self.max_len {
            return Err(message);
        }
        self.queue.push_back(message);
        Ok(())
    }

    pub fn pop(&mut self) -> Option<Message> {
        self.queue.pop_front()
    }

    pub fn len(&self) -> usize {
        self.queue.len()
    }

    pub fn is_empty(&self) -> bool {
        self.queue.is_empty()
    }

    /// The capacity bound at which `push` begins rejecting.
    pub fn max_len(&self) -> usize {
        self.max_len
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn msg(to: u64) -> Message {
        Message::system(ActorId(to), "H", 0)
    }

    #[test]
    fn push_accepts_up_to_the_cap() {
        let mut q = MessageQueue::with_max_len(3);
        assert!(q.push(msg(1)).is_ok());
        assert!(q.push(msg(2)).is_ok());
        assert!(q.push(msg(3)).is_ok());
        assert_eq!(q.len(), 3);
    }

    #[test]
    fn push_rejects_at_the_cap_and_returns_the_message() {
        let mut q = MessageQueue::with_max_len(2);
        assert!(q.push(msg(1)).is_ok());
        assert!(q.push(msg(2)).is_ok());
        // Third push exceeds the bound: rejected, memory does not grow,
        // and the caller gets its message back for backpressure handling.
        let rejected = q.push(msg(3));
        assert_eq!(rejected, Err(msg(3)));
        assert_eq!(q.len(), 2, "queue must not grow past its cap");
    }

    #[test]
    fn draining_frees_capacity_again() {
        let mut q = MessageQueue::with_max_len(1);
        assert!(q.push(msg(1)).is_ok());
        assert!(q.push(msg(2)).is_err());
        assert!(q.pop().is_some());
        // After a drain, the slot is available once more.
        assert!(q.push(msg(2)).is_ok());
    }

    #[test]
    fn zero_cap_is_clamped_to_one() {
        let mut q = MessageQueue::with_max_len(0);
        assert_eq!(q.max_len(), 1);
        assert!(q.push(msg(1)).is_ok());
        assert!(q.push(msg(2)).is_err());
    }
}
