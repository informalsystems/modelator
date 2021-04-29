
const MAX_NUMBER: u64 = 6;
/// Example system under test (SUT).
/// Allows to modify the two variables, a and b, 
/// if they do not exceed the MAX_NUMBER.
/// Maintains also the sum and product of the variables.
#[allow(missing_docs)]
#[derive(Debug, Clone, Copy, PartialEq)]
pub struct NumberSystem {
    pub a: u64,
    pub b: u64,
    pub sum: u64,
    pub prod: u64,
}

impl Default for NumberSystem {
    fn default() -> Self {
        NumberSystem {
            a: 0,
            b: 0,
            sum: 0,
            prod: 0,
        }
    }
}

#[allow(missing_docs)]
impl NumberSystem {
    pub fn recalculate(&mut self) {
        self.sum = self.a + self.b;
        self.prod = self.a * self.b;
    }
    pub fn increase_a(&mut self, n: u64) -> Result<(), String> { 
        if self.a + n <= MAX_NUMBER {
            self.a = self.a + n;
            self.recalculate();
            Ok(())
        }
        else {
            Err("FAIL".to_string())
        }
    }
    pub fn increase_b(&mut self, n: u64) -> Result<(), String> { 
        if self.b + n <= MAX_NUMBER {
            self.b = self.b + n;
            self.recalculate();
            Ok(())
        }
        else {
            Err("FAIL".to_string())
        }
    }
}
