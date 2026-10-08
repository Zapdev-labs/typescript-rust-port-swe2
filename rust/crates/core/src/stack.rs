// Ported from tsc/internal/core/stack.go @ ec47d33c23e464a17cdf2475632cba629bee8763

#[derive(Default)]
pub struct Stack<T> {
    data: Vec<T>,
}

impl<T> Stack<T> {
    pub fn push(&mut self, item: T) {
        self.data.push(item);
    }

    pub fn pop(&mut self) -> T {
        if self.data.is_empty() {
            panic!("stack is empty");
        }
        self.data.pop().unwrap()
    }

    // PORT: Go's Peek returns the element by value; Rust borrows it.
    pub fn peek(&self) -> &T {
        if self.data.is_empty() {
            panic!("stack is empty");
        }
        &self.data[self.data.len() - 1]
    }

    pub fn len(&self) -> usize {
        self.data.len()
    }
}
