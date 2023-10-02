use std::fmt;
use std::str::FromStr;

use crate::*;
use fmt::{Debug, Display, Formatter};
use thiserror::Error;

/// A variable for use in [`Pattern`]s or [`Subst`]s.
///
/// This implements [`FromStr`], and will only parse if it has a
/// leading `?`.
///
/// [`FromStr`]: std::str::FromStr
#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Var(Symbol);

#[derive(Debug, Error)]
pub enum VarParseError {
    #[error("pattern variable {0:?} should have a leading question mark")]
    #[warn(missing_docs)]
    MissingQuestionMark(String),
}

impl FromStr for Var {
    type Err = VarParseError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        use VarParseError::*;

        if s.starts_with('?') && s.len() > 1 {
            Ok(Var(s.into()))
        } else {
            Err(MissingQuestionMark(s.to_owned()))
        }
    }
}

impl Display for Var {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        Display::fmt(&self.0, f)
    }
}

impl Debug for Var {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        Debug::fmt(&self.0, f)
    }
}

#[derive(Default, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
/// A substitition mapping [`Var`]s to eclass [`Id`]s.
///
pub struct Subst {
    /// Internal map of the substitution
    pub vec: smallvec::SmallVec<[(Var, Option<Id>); 3]>,
    /// Default mapping of the substitution
    pub default_val: Id 
}

impl Subst {
    /// Create a `Subst` with the given initial capacity
    pub fn with_capacity(capacity: usize) -> Self {
        Self {
            vec: smallvec::SmallVec::with_capacity(capacity),
            default_val: Id(0),
        }
    }

    /// Insert something, returning the old `Id` if present.
    pub fn insert(&mut self, var: Var, id: Id) -> Option<Id> {
        for pair in &mut self.vec {
            if pair.0 == var {
                match &mut pair.1 {
                    Some(x) => { return Some(std::mem::replace( x, id)) }
                    None => { return None }
                }
            }
        }
        self.vec.push((var, Some(id)));
        None
    }

    /// Set default
    pub fn set_default(&mut self, id: Id) {
        self.default_val = id
    }


    /// Retrieve a `Var`, returning `None` if not present.
    #[inline(never)]
    pub fn get(&self, var: Var) -> Option<&Id> {
        self.vec
            .iter()
            .find_map(|(v, id)| if *v == var { match id {
                Some(id) => { Some(id) }
                None => { None }
            } } else { None })
    }
}

impl std::ops::Index<Var> for Subst {
    type Output = Id;

    fn index(&self, var: Var) -> &Self::Output {
        match self.get(var) {
            Some(id) => id,
            None => &self.default_val,
            // panic!("Var '{}={}' not found in {:?}", var.0, var, self),
        }
    }
}

impl Debug for Subst {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        let len = self.vec.len();
        write!(f, "{{")?;
        for i in 0..len {
            let (var, id) = &self.vec[i];
            write!(f, "{}: {:?}", var, id)?;
            if i < len - 1 {
                write!(f, ", ")?;
            }
        }
        write!(f, "}}")
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn var_parse() {
        assert_eq!(Var::from_str("?a").unwrap().to_string(), "?a");
        assert_eq!(Var::from_str("?abc 123").unwrap().to_string(), "?abc 123");
        assert!(Var::from_str("a").is_err());
        assert!(Var::from_str("a?").is_err());
        assert!(Var::from_str("?").is_err());
    }
}
