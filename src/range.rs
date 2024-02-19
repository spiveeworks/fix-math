// Intervals in which a value might be. Can be used for exact computation on
// approximate measurements, or approximate computation.

use std::ops::{Add, Mul};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Range<T> {
    pub l: T,
    pub r: T,
}

impl<T> Range<T> {
    pub fn new_raw(l: T, r: T) -> Self {
        Range { l, r }
    }
}

impl<T: Clone> Range<T> {
    pub fn exact(x: T) -> Self {
        let y = x.clone();
        Range { l: x, r: y }
    }
}

impl<T: PartialOrd> Range<T> {
    pub fn reorder(self: &mut Range<T>) {
        if self.r < self.l {
            std::mem::swap(&mut self.l, &mut self.r);
        }
    }

    pub fn reordered(mut self: Range<T>) -> Range<T> {
        self.reorder();
        self
    }

    pub fn new(l: T, r: T) -> Range<T> {
        let result = Range::new_raw(l, r);
        result.reordered()
    }
}

#[derive(PartialEq, Eq)]
enum RangeSign {
    ExactZero,
    Negative,
    // NegativeZero,
    NegativePositive,
    // PositiveZero,
    Positive,
}

impl<T: Ord + num_traits::Zero> Range<T> {
    fn sign(self: &Range<T>) -> RangeSign {
        let zero = num_traits::Zero::zero();
        let lord = Ord::cmp(&self.l, &zero);
        let rord = Ord::cmp(&self.r, &zero);

        use std::cmp::Ordering::*;
        match (lord, rord) {
            (Equal, Equal) => RangeSign::ExactZero,
            (Less, Less) => RangeSign::Negative,
            (Equal, Less) => RangeSign::Negative,
            (Less, Greater) => RangeSign::NegativePositive,
            (Equal, Greater) => RangeSign::Positive,
            (Greater, Greater) => RangeSign::Positive,
            // Three additional cases for if r < l
            (Greater, Equal) => RangeSign::Positive,
            (Greater, Less) => RangeSign::NegativePositive,
            (Less, Equal) => RangeSign::Negative,
        }
    }
}

impl<T: Ord + num_traits::Zero> Range<T> {
    pub fn crosses_zero(self: &Range<T>) -> bool {
        self.sign() == RangeSign::NegativePositive
    }

    pub fn touches_zero(self: &Range<T>) -> bool {
        match self.sign() {
            RangeSign::Negative | RangeSign::Positive => false,
            _ => true,
        }
    }
}

// Assumes that inputs are ordered correctly. (Or both incorrectly!)
impl<'a, 'b, T> Add<&'b Range<T>> for &'a Range<T>
  where &'a T: Add<&'b T, Output=T>
{
    type Output = Range<T>;

    fn add(self: &'a Range<T>, other: &'b Range<T>) -> Range<T> {
        Range {
            l: &self.l + &other.l,
            r: &self.r + &other.r,
        }
    }
}

// Assumes that inputs are ordered correctly. (Or both incorrectly!)
impl<'a, 'b, T> Mul<&'b Range<T>> for &'a Range<T>
    where &'a T: Mul<&'b T, Output=T>,
          T: Ord + num_traits::Signed
{
    type Output = Range<T>;

    fn mul(self: &'a Range<T>, other: &'b Range<T>) -> Range<T> {
        match (self.sign(), other.sign()) {
            (RangeSign::NegativePositive, RangeSign::NegativePositive) => {
                let n1 = &self.l * &other.r;
                let n2 = &self.r * &other.l;
                let p1 = &self.l * &other.l;
                let p2 = &self.r * &other.r;
                Range {
                    l: std::cmp::min(n1, n2),
                    r: std::cmp::max(p1, p2),
                }
            },
            (RangeSign::NegativePositive, RangeSign::Positive) => {
                let extremum = std::cmp::max(&other.l, &other.r);
                Range {
                    l: &self.l * extremum,
                    r: &self.r * extremum,
                }
            },
            (RangeSign::NegativePositive, RangeSign::Negative) => {
                // Self is zero, other is negative, so multiply by the lowest
                // possible value of other, then swap sides.
                let extremum = std::cmp::min(&other.l, &other.r);
                Range {
                    l: &self.r * extremum,
                    r: &self.l * extremum,
                }
            },
            (RangeSign::Positive, RangeSign::NegativePositive) => {
                let extremum = std::cmp::max(&self.l, &self.r);
                Range {
                    // We have to multiply extremum by other, since our trait
                    // assumption is &'a T * &'b T
                    l: extremum * &other.l,
                    r: extremum * &other.r,
                }
            },
            (RangeSign::Negative, RangeSign::NegativePositive) => {
                // Other is zero, self is negative, so multiply by the lowest
                // possible value of self, then swap sides.
                let extremum = std::cmp::min(&self.l, &self.r);
                Range {
                    l: extremum * &other.r,
                    r: extremum * &other.l,
                }
            },
            (RangeSign::Negative, RangeSign::Negative) => {
                // Extreme negatives multiply to give extreme positives,
                // so right = left * left.
                Range {
                    l: &self.r * &other.r,
                    r: &self.l * &other.l,
                }
            },
            (RangeSign::Negative, RangeSign::Positive) => {
                // Extreme negative and positive give extreme negative,
                // so left = left * right
                Range {
                    l: &self.l * &other.r,
                    r: &self.r * &other.l,
                }
            },
            (RangeSign::Positive, RangeSign::Negative) => {
                // Extreme positive and negative give extreme negative,
                // so left = right * left
                Range {
                    l: &self.r * &other.l,
                    r: &self.l * &other.r,
                }
            },
            (_, _) => {
                // Both are positive, or at least one is exactly zero, just
                // multiply them in order.
                Range {
                    l: &self.l * &other.l,
                    r: &self.r * &other.r,
                }
            },
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn test_interval_fn<F>(f: F, is: &[Range<i32>], expected: Range<i32>, must_cover_ends: bool)
        -> Result<(), String>
            where F: Fn(&[i32]) -> i32
    {
        let mut xs: Vec<i32> = is.iter().map(|i| i.l).collect();
        let mut l_covered = false;
        let mut r_covered = false;
        loop {
            let actual = f(&xs);
            if actual < expected.l || actual > expected.r {
                return Err(format!("Function applied to {:?} gave {} which is not in the interval {:?}.", xs, actual, expected));
            }
            if actual == expected.l {
                l_covered = true;
            }
            if actual == expected.r {
                r_covered = true;
            }

            let mut was_incremented = false;
            for j in 0..is.len() {
                if xs[j] < is[j].r {
                    xs[j] += 1;
                    was_incremented = true;
                    break;
                } else {
                    xs[j] = is[j].l;
                }
            }
            if !was_incremented {
                break;
            }
        }

        if must_cover_ends {
            if !l_covered && !r_covered && expected.l != expected.r {
                return Err(format!("Function did not cover endpoints {} or {}", expected.l, expected.r));
            }
            if !l_covered {
                return Err(format!("Function did not cover left endpoint {}", expected.l));
            }
            if !r_covered {
                return Err(format!("Function did not cover right endpoint {}", expected.r));
            }
        }

        return Ok(());
    }

    #[test]
    fn test_add() {
        let is = [
            Range { l: 5, r: 10 },
            Range { l: 8, r: 29 },
            Range { l: -3, r: 6 },
        ];
        let expected = &(&is[0] + &is[1]) + &is[2];
        test_interval_fn(
            |xs| xs[0] + xs[1] + xs[2],
            &is,
            expected,
            true
        ).unwrap();
    }

    #[test]
    fn test_mul() {
        let test_pairs = [
            [Range::new(1, 2), Range::new(3, 4)],
            [Range::new(-1, 2), Range::new(3, 4)],
            [Range::new(-1, -2), Range::new(3, 4)],
            [Range::new(1, 2), Range::new(-3, 4)],
            [Range::new(-1, 2), Range::new(-3, 4)],
            [Range::new(0, 2), Range::new(-4, 0)],
        ];
        for is in &test_pairs {
            let expected = &is[0] * &is[1];
            test_interval_fn(
                |xs| xs[0] * xs[1],
                is,
                expected,
                true
            ).unwrap();
        }
    }
}

