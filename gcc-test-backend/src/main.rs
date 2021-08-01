trait A {
    fn k(&self, x: i32) -> i32;
}

pub struct O {
}

pub struct P {
}

impl A for O {
    fn k(&self, x: i32) -> i32 {
        x
    }
}

impl A for P {
    fn k(&self, x: i32) -> i32 {
        x
    }
}

pub enum R {
    P(P),
    O(O),
}
impl R {
    pub fn k(&self, x: i32) -> i32 {
        match self {
            &R::P(ref p) => p.k(x),
            &R::O(ref o) => o.k(x),
        }
    }
}
