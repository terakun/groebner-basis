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
    fn is_const(&self) -> bool {
        for i in &self.idx {
            if *i != 0 {
                return false;
            }
        }
        true
    }
    fn lcm(&self, other: &Self) -> Self {
        MultiIdx {
            idx: self.idx
                .iter()
                .zip(&other.idx)
                .map(|(a, b)| *a.max(b))
                .collect(),
        }
    }
}

impl Ord for MultiIdx {
    fn cmp(&self, other: &Self) -> Ordering {
        self.partial_cmp(other).unwrap()
    }
}

// graded lexicographic ordering
impl PartialOrd for MultiIdx {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        let res = (self.idx.iter().sum::<u64>()).cmp(&other.idx.iter().sum());
        if res != std::cmp::Ordering::Equal {
            Some(res)
        } else {
            for (a, b) in self.idx.iter().zip(&other.idx) {
                if *a != *b {
                    return Some(a.cmp(&b));
                }
            }
            Some(Ordering::Equal)
        }
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
        self.mono.devisible(&other.mono)
    }
    fn devide(&self, other: Term) -> Option<Self> {
        if self.devisible(&other) {
            Some(Term {
                coeff: other.coeff / self.coeff,
                mono: MultiIdx {
                    idx: self.mono
                        .idx
                        .iter()
                        .zip(other.mono.idx)
                        .map(|(a, b)| b - *a)
                        .collect(),
                },
            })
        } else {
            None
        }
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
    fn leading_term(&self) -> Term {
        let t = self.p.iter().next_back().unwrap();
        Term::from((t.0.clone(), t.1.clone()))
    }
    fn deg(&self) -> MultiIdx {
        self.leading_term().mono
    }

    fn is_zero(&self) -> bool {
        for (_, c) in self.p.iter() {
            if *c != Rational::from(0) {
                return false;
            }
        }
        true
    }
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
            if *c == Rational::from(0) {
                self.p.remove(&term.mono);
            }
        } else {
            self.p.insert(term.mono.clone(), term.coeff.clone());
        }
    }
    fn sub_term(&mut self, term: &Term) {
        if let Some(c) = self.p.get_mut(&term.mono) {
            *c -= term.coeff;
            if *c == Rational::from(0) {
                self.p.remove(&term.mono);
            }
        } else {
            self.p.insert(term.mono.clone(), -term.coeff);
        }
    }
    fn mul_term(&mut self, term: &Term) {
        let mut p = BTreeMap::new();
        for (mono, coeff) in self.p.iter() {
            let t = Term::from((mono.clone(), coeff.clone()));
            let mul_t = t * term.clone();
            p.insert(mul_t.mono, mul_t.coeff);
        }
        self.p = p;
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
        let mut p = self.clone();
        for t_other in other.p {
            p.sub_term(&Term {
                coeff: t_other.1,
                mono: t_other.0,
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

impl fmt::Display for Polynomial {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let mut s: Vec<String> = Vec::new();
        for (mono, coeff) in self.p.iter() {
            let sign = if *coeff > Rational::from(0) {
                "+".to_string()
            } else {
                "".to_string()
            };
            let coeff_s = if *coeff != Rational::from(1) && *coeff != Rational::from(-1) {
                format!("{}", coeff)
            } else if *coeff == Rational::from(-1) {
                "-".to_string()
            } else {
                "".to_string()
            };
            let mono_s = if mono.is_const()
                && (*coeff == Rational::from(1) || *coeff == Rational::from(-1))
            {
                "1".to_string()
            } else {
                format!("{}", mono)
            };
            s.push(format!("{}{}{}", sign, coeff_s, mono_s));
        }
        write!(f, "{}", s.join(" "))
    }
}

#[derive(Clone)]
struct Ideal(Vec<Polynomial>);

impl Ideal {
    fn devisible(&self, f: &Polynomial) -> Option<usize> {
        for (i, g) in self.0.iter().enumerate() {
            if g.leading_term().devisible(&f.leading_term()) {
                return Some(i);
            }
        }
        None
    }
    // returns (quotient,remainder)
    fn devide(&self, f: &Polynomial) -> (Vec<Polynomial>, Polynomial) {
        let mut quotient = vec![Polynomial::new(self.0[0].n); self.0.len()];
        let mut remainder = Polynomial::new(self.0[0].n);
        let mut f = f.clone();
        while !f.is_zero() {
            if let Some(i) = self.devisible(&f) {
                let q = self.0[i].leading_term().devide(f.leading_term()).unwrap();
                quotient[i].add_term(&q);
                let mut gq = self.0[i].clone();
                gq.mul_term(&q);
                f = f - gq;
            } else {
                let lt = f.leading_term();
                remainder.add_term(&lt);
                f.sub_term(&lt);
            }
        }

        (quotient, remainder)
    }

    fn grobner(&self) -> Option<Self> {
        let mut gs = self.clone();
        loop {
            let gs_old = gs.clone();
            let mut modified = false;

            let n = gs_old.0.len();
            for i in 0..n {
                for j in (i + 1)..n {
                    let s = s_polynomial(&gs_old.0[i], &gs_old.0[j]);
                    let (_, r) = gs_old.devide(&s);
                    if !r.is_zero() {
                        gs.0.push(r);
                        modified = true;
                    }
                }
            }
            if !modified {
                break;
            }
        }

        loop {
            let gs_old = gs.clone();
            for (i, p) in gs_old.0.iter().enumerate() {
                let mut removed = false;
                for q in &gs_old.0 {
                    if *p == *q {
                        continue;
                    }
                    if q.deg().devisible(&p.deg()) {
                        removed = true;
                        break;
                    }
                }
                if removed {
                    gs.0.remove(i);
                    break;
                }
            }
            if gs.0.len() == gs_old.0.len() {
                break;
            }
        }

        Some(gs)
    }
}

fn s_polynomial(f: &Polynomial, g: &Polynomial) -> Polynomial {
    let flt = f.leading_term();
    let glt = g.leading_term();
    let lcm = Term {
        coeff: Rational::from(1),
        mono: flt.mono.lcm(&glt.mono),
    };
    let mut f2 = f.clone();
    let mut g2 = g.clone();
    f2.mul_term(&flt.devide(lcm.clone()).unwrap());
    g2.mul_term(&glt.devide(lcm).unwrap());
    f2 - g2
}

#[test]
fn test_add_term() {
    let mut f1 =
        Polynomial::from_integer_vec(vec![(2, vec![0, 2]), (3, vec![1, 1]), (-4, vec![2, 0])]);
    let f2 = Polynomial::from_integer_vec(vec![(3, vec![1, 1]), (-4, vec![2, 0]), (2, vec![1, 0])]);
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
fn test_sub_term() {
    let mut f1 =
        Polynomial::from_integer_vec(vec![(2, vec![0, 2]), (3, vec![1, 1]), (-4, vec![2, 0])]);
    let f2 = Polynomial::from_integer_vec(vec![(3, vec![1, 1]), (-4, vec![2, 0]), (2, vec![1, 0])]);
    let t1 = Term {
        coeff: Rational::from(2),
        mono: MultiIdx { idx: vec![0, 2] },
    };
    let t2 = Term {
        coeff: Rational::from(-2),
        mono: MultiIdx { idx: vec![1, 0] },
    };
    f1.sub_term(&t1);
    f1.sub_term(&t2);
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
fn test_sub() {
    let f1 = Polynomial::from_integer_vec(vec![(2, vec![0, 2]), (3, vec![1, 1]), (-4, vec![2, 0])]);
    let f2 = Polynomial::from_integer_vec(vec![(3, vec![1, 2]), (3, vec![1, 1]), (-4, vec![2, 0])]);
    let f3 = Polynomial::from_integer_vec(vec![(2, vec![0, 2]), (-3, vec![1, 2])]);
    assert_eq!(f1 - f2, f3);
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

#[test]
fn test_leading_term() {
    let f1 = Polynomial::from_integer_vec(vec![
        (2, vec![2, 0]),
        (3, vec![1, 1]),
        (-4, vec![0, 2]),
        (1, vec![1, 0]),
        (3, vec![0, 1]),
    ]);
    let t = Term {
        coeff: Rational::from(2),
        mono: MultiIdx { idx: vec![2, 0] },
    };
    assert_eq!(f1.leading_term(), t);
}

#[test]
fn test_devides() {
    let t1 = Term {
        coeff: Rational::from(14),
        mono: MultiIdx { idx: vec![3, 2] },
    };
    let t2 = Term {
        coeff: Rational::from(2),
        mono: MultiIdx { idx: vec![2, 0] },
    };
    let t4 = Term {
        coeff: Rational::from(7),
        mono: MultiIdx { idx: vec![2, 3] },
    };
    let t5 = Term {
        coeff: Rational::from(7),
        mono: MultiIdx { idx: vec![1, 2] },
    };

    assert_eq!(t2.devide(t1.clone()), Some(t5));
    assert_eq!(t4.devide(t1.clone()), None);
}

#[test]
fn test_ideal_devide() {
    let f = Polynomial::from_integer_vec(vec![(1, vec![2, 3]), (1, vec![1, 2])]);
    let g1 = Polynomial::from_integer_vec(vec![(1, vec![2, 0]), (1, vec![0, 1])]);
    let g2 = Polynomial::from_integer_vec(vec![(1, vec![1, 2]), (1, vec![0, 1])]);
    let ideal = Ideal(vec![g1, g2]);
    let (qs, r) = ideal.devide(&f);
    let mut f2 = Polynomial::new(2);
    for (q, g) in qs.iter().zip(ideal.0) {
        f2 = f2 + (q.clone() * g.clone());
    }
    f2 = f2 + r;
    assert_eq!(f, f2);
}

fn main() {
    let f1 = Polynomial::from_integer_vec(vec![(1, vec![3, 0]), (-2, vec![1, 1])]);
    let f2 = Polynomial::from_integer_vec(vec![(1, vec![2, 1]), (-2, vec![0, 2]), (1, vec![1, 0])]);
    println!("f1 = {}", f1);
    println!("f2 = {}", f2);

    let ideal = Ideal(vec![f1, f2]);
    let g_ideal = ideal.grobner().unwrap();
    println!("grobner basis");
    for (i, g) in g_ideal.0.iter().enumerate() {
        println!("g_{} = {}", i + 1, g);
    }
}
