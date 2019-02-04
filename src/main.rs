type MultiIdx = Vec<i32>;
type Polynomial<T> = Vec<(T, MultiIdx)>;
type Number = f64;

struct Ideal<T>(Vec<Polynomial<T>>);

impl<T> Ideal<T> {
    fn new() -> Self {
        Ideal(Vec::new())
    }

    fn grobner() -> Option<Self> {
        None
    }
}

fn main() {
    println!("Hello, Grobner!");
}
