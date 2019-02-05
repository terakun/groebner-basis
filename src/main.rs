extern crate num_rational;
use std::cmp::Ordering;
use std::fmt;
use std::collections::BTreeMap;

type Rational = num_rational::Ratio<i64>;
#[derive(PartialEq, Eq, Clone, Debug)]
struct MultiIdx {
    idx: Vec<u64>,
}

impl MultiIdx {
    fn hoge() {}
}

impl Ord for MultiIdx {
    fn cmp(&self, other: &Self) -> Ordering {
        self.partial_cmp(other).unwrap()
    }
}

// lexical ordering
impl PartialOrd for MultiIdx {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        for (a, b) in self.idx.iter().zip(&other.idx) {
            if *a != *b {
                return Some(a.cmp(&b));
            }
        }
        Some(Ordering::Equal)
    }
}

impl fmt::Display for MultiIdx {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let mut s: Vec<String> = Vec::new();
        for (i, e) in self.idx.iter().enumerate() {
            if *e != 0 {
                s.push(format!("x_{}^{}", i, e));
            }
        }
        write!(f, "{}", s.join(" "))
    }
}

impl MultiIdx {
    // check self devides other
    fn devisible(&self, other: &MultiIdx) -> bool {
        for (a, b) in self.idx.iter().zip(&other.idx) {
            if a > b {
                return false;
            }
        }
        true
    }
}

#[derive(PartialEq, Eq, Clone, Debug)]
struct Term {
    coeff: Rational,
    mono: MultiIdx,
}

impl From<(MultiIdx, Rational)> for Term {
    fn from(t: (MultiIdx, Rational)) -> Self {
        Term {
            coeff: t.1,
            mono: t.0,
        }
    }
}
impl Term {
    fn devisible(&self, other: &Term) -> bool {
        (other.coeff % self.coeff == Rational::from(0)) && self.mono.devisible(&other.mono)
    }
}

impl std::ops::Mul for Term {
    type Output = Self;
    fn mul(self, other: Self) -> Self {
        let coeff = self.coeff * other.coeff;
        let idx = self.mono
            .idx
            .iter()
            .zip(other.mono.idx)
            .map(|(a, b)| *a + b)
            .collect();
        Term {
            coeff: coeff,
            mono: MultiIdx { idx: idx },
        }
    }
}

#[derive(PartialEq, Eq, Clone, Debug)]
struct Polynomial {
    p: BTreeMap<MultiIdx, Rational>,
    n: usize,
}

impl Polynomial {
    fn new(n: usize) -> Self {
        Polynomial {
            p: BTreeMap::new(),
            n: n,
        }
    }
    // fn leading_term(&self) -> Term {}
    fn from_integer_vec(ivec: Vec<(i64, Vec<u64>)>) -> Self {
        let n = ivec[0].1.len();
        let mut p = BTreeMap::new();
        for t in ivec {
            p.insert(MultiIdx { idx: t.1 }, Rational::from(t.0));
        }
        Polynomial { p: p, n: n }
    }

    fn add_term(&mut self, term: &Term) {
        if let Some(c) = self.p.get_mut(&term.mono) {
            *c += term.coeff;
        } else {
            self.p.insert(term.mono.clone(), term.coeff.clone());
        }
    }
    fn sub_term(&mut self, term: &Term) {
        if let Some(c) = self.p.get_mut(&term.mono) {
            *c -= term.coeff;
        } else {
            self.p.insert(term.mono.clone(), -term.coeff);
        }
    }
}

impl std::ops::Add for Polynomial {
    type Output = Self;

    fn add(self, other: Self) -> Self {
        if self.n != other.n {
            panic!("error");
        }
        let mut p = other.clone();
        for t_self in self.p {
            p.add_term(&Term {
                coeff: t_self.1,
                mono: t_self.0,
            });
        }
        p
    }
}
impl std::ops::Sub for Polynomial {
    type Output = Self;

    fn sub(self, other: Self) -> Self {
        if self.n != other.n {
            panic!("error");
        }
        let mut p = other.clone();
        for t_self in self.p {
            p.sub_term(&Term {
                coeff: t_self.1,
                mono: t_self.0,
            });
        }
        p
    }
}

impl std::ops::Mul for Polynomial {
    type Output = Self;
    fn mul(self, other: Self) -> Self {
        let mut p = Polynomial::new(self.n);
        for t_self in self.p {
            for t_other in &other.p {
                p.add_term(
                    &(Term::from(t_self.clone())
                        * Term::from((t_other.0.clone(), t_other.1.clone()))),
                );
            }
        }
        p
    }
}

struct Ideal(Vec<Polynomial>);

impl Ideal {
    fn new() -> Self {
        Ideal(Vec::new())
    }
    // fn devisible(&self, f: &Polynomial) -> bool {
    //     for g in &self.0 {
    //         if g.p[0].devisible(&f.p[0]) {
    //             return true;
    //         }
    //     }
    //     false
    // }

    // returns (quotient,remainder)
    // fn devide(&self, f: &Polynomial) -> (Vec<Polynomial>, Polynomial) {
    //     let mut quotient = Vec::new();
    //     let mut remainder = Polynomial { p: Vec::new() };
    //     let mut f = f.clone();
    //     while f.is_zero() {
    //         f = if let Some(g) = self.devisible(&f) {
    //             let (q, r) = g.devides(f);
    //             f - g * q
    //         } else {
    //             let lt = f.leading_term();
    //             remainder += lt;
    //             f - lt
    //         }
    //     }
    //
    //     (quotient, Polynomial { p: Vec::new() })
    // }

    fn grobner(&self) -> Option<Self> {
        // let g = self.0;
        None
    }
}

fn s_polynomial() {}

#[test]
fn test_add_term() {
    let mut f1 =
        Polynomial::from_integer_vec(vec![(2, vec![0, 2]), (3, vec![1, 1]), (-4, vec![2, 0])]);
    let f2 = Polynomial::from_integer_vec(vec![
        (0, vec![0, 2]),
        (3, vec![1, 1]),
        (-4, vec![2, 0]),
        (2, vec![1, 0]),
    ]);
    let t1 = Term {
        coeff: Rational::from(-2),
        mono: MultiIdx { idx: vec![0, 2] },
    };
    let t2 = Term {
        coeff: Rational::from(2),
        mono: MultiIdx { idx: vec![1, 0] },
    };
    f1.add_term(&t1);
    f1.add_term(&t2);
    println!("{:?}", f1);
    println!("{:?}", f2);
    assert_eq!(f1, f2);
}

#[test]
fn test_add() {
    let f1 = Polynomial::from_integer_vec(vec![(2, vec![0, 2]), (3, vec![1, 1]), (-4, vec![2, 0])]);
    let f2 = Polynomial::from_integer_vec(vec![(3, vec![1, 2]), (3, vec![1, 1]), (-4, vec![2, 0])]);
    let f3 = Polynomial::from_integer_vec(vec![
        (2, vec![0, 2]),
        (3, vec![1, 2]),
        (6, vec![1, 1]),
        (-8, vec![2, 0]),
    ]);
    assert_eq!(f1 + f2, f3);
}

#[test]
fn test_mul1() {
    let f1 = Polynomial::from_integer_vec(vec![
        (2, vec![2, 0]),
        (3, vec![1, 1]),
        (-4, vec![0, 2]),
        (1, vec![1, 0]),
        (3, vec![0, 1]),
    ]);
    let f2 = Polynomial::from_integer_vec(vec![(1, vec![1, 0]), (2, vec![0, 1]), (5, vec![0, 0])]);
    let f3 = f1 * f2;
    let f4 = Polynomial::from_integer_vec(vec![
        (2, vec![3, 0]),
        (7, vec![2, 1]),
        (11, vec![2, 0]),
        (2, vec![1, 2]),
        (20, vec![1, 1]),
        (5, vec![1, 0]),
        (-8, vec![0, 3]),
        (-14, vec![0, 2]),
        (15, vec![0, 1]),
    ]);
    assert_eq!(f3, f4);
}

#[test]
fn test_mul2() {
    let f1 = Polynomial::from_integer_vec(vec![(2, vec![1, 0]), (3, vec![0, 1])]);
    let f2 = Polynomial::from_integer_vec(vec![(-1, vec![1, 0]), (2, vec![0, 1])]);
    let f3 = f1 * f2;
    let f4 = Polynomial::from_integer_vec(vec![(-2, vec![2, 0]), (1, vec![1, 1]), (6, vec![0, 2])]);
    assert_eq!(f3, f4);
}

fn main() {
    let idx1 = MultiIdx { idx: vec![3, 3] };
    let idx2 = MultiIdx { idx: vec![2, 5] };
    let idx3 = MultiIdx { idx: vec![4, 3] };
    let mut v = vec![idx1, idx2, idx3];
    v.sort();
    println!("{:?}", v);
}
