//use pattern::apply_pat;
use std::fmt::{self, Debug, Display};
use std::sync::Arc;

use crate::*;

/// A rewrite that searches for the lefthand side and applies the righthand side.
///
/// The [`rewrite!`] is the easiest way to create rewrites.
///
/// A [`Rewrite`] consists principally of a [`Searcher`] (the lefthand
/// side) and an [`Applier`] (the righthand side).
/// It additionally stores a name used to refer to the rewrite and a
/// long name used for debugging.
///
#[derive(Clone)]
#[non_exhaustive]
pub struct Rewrite<L, T, N> {
    /// The name of the rewrite.
    pub name: Symbol,
    /// The searcher (left-hand side) of the rewrite.
    pub searcher: Arc<dyn Searcher<L, T, N> + Sync + Send>,
    /// The applier (right-hand side) of the rewrite.
    pub applier: Arc<dyn Applier<L, T, N> + Sync + Send>,
}

impl<L, T, N> Debug for Rewrite<L, T, N>
where
    L: Language + Display + 'static,
    T: FfnLattice,
    N: Analysis<L,T> + 'static,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut d = f.debug_struct("Rewrite");
        d.field("name", &self.name);

        // if let Some(pat) = Any::downcast_ref::<dyn Pattern<L>>(&self.searcher) {
        if let Some(pat) = self.searcher.get_pattern_ast() {
            d.field("searcher", &DisplayAsDebug(pat));
        } else {
            d.field("searcher", &"<< searcher >>");
        }

        if let Some(pat) = self.applier.get_pattern_ast() {
            d.field("applier", &DisplayAsDebug(pat));
        } else {
            d.field("applier", &"<< applier >>");
        }

        d.finish()
    }
}

impl<L: Language, T: FfnLattice, N: Analysis<L,T>> Rewrite<L, T, N> {
    /// Create a new [`Rewrite`]. You typically want to use the
    /// [`rewrite!`] macro instead.
    ///
    pub fn new(
        name: impl Into<Symbol>,
        searcher: impl Searcher<L, T, N> + Send + Sync + 'static,
        applier: impl Applier<L, T, N> + Send + Sync + 'static,
    ) -> Result<Self, String> {
        let name = name.into();
        let searcher = Arc::new(searcher);
        let applier = Arc::new(applier);

        // let bound_vars = searcher.vars();
        // TODO Locally forget about those vars
        // for v in applier.vars() {
        //     if !bound_vars.contains(&v) {
        //         return Err(format!("Rewrite {} refers to unbound var {}", name, v));
        //     }
        // }

        Ok(Self {
            name,
            searcher,
            applier,
        })
    }

    /// Call [`search`] on the [`Searcher`].
    ///
    /// [`search`]: Searcher::search()
    pub fn search(&self, egraph: &EGraph<L, T, N>) -> Vec<SearchMatches<L, T>> {
        self.searcher.search(egraph)
    }

    /// Call [`apply_matches`] on the [`Applier`].
    ///
    /// [`apply_matches`]: Applier::apply_matches()
    pub fn apply(&self, egraph: &mut EGraph<L, T, N>, matches: &[SearchMatches<L, T>]) -> Vec<Id> {
        self.applier.apply_matches(egraph, matches, self.name)
    }

    /// This `run` is for testing use only. You should use things
    /// from the `egg::run` module
    #[cfg(test)]
    pub(crate) fn run(&self, egraph: &mut EGraph<L, T, N>) -> Vec<Id> {
        let start = crate::util::Instant::now();

        let matches = self.search(egraph);
        log::debug!("Found rewrite {} {} times", self.name, matches.len());

        let ids = self.apply(egraph, &matches);
        let elapsed = start.elapsed();
        log::debug!(
            "Applied rewrite {} {} times in {}.{:03}",
            self.name,
            ids.len(),
            elapsed.as_secs(),
            elapsed.subsec_millis()
        );

        egraph.rebuild();
        ids
    }
}

/// The lefthand side of a [`Rewrite`].
///
/// A [`Searcher`] is something that can search the egraph and find
/// matching substititions.
/// Right now the only significant [`Searcher`] is [`Pattern`].
///
pub trait Searcher<L, T, N>
where
    L: Language,
    T: FfnLattice,
    N: Analysis<L, T>,
{
    /// Search one eclass, returning None if no matches can be found.
    /// This should not return a SearchMatches with no substs.
    fn search_eclass(&self, egraph: &EGraph<L, T, N>, eclass: Id) -> Option<SearchMatches<L, T>>;

    // /// Computes the far-fetchedness of this pattern when instantiated with `subst`
    // fn ffn_of_subst(&self, egraph: &EGraph<L, N>, subst: &Subst) -> Ffn;

    /// Search the whole [`EGraph`], returning a list of all the
    /// [`SearchMatches`] where something was found.
    /// This just calls [`search_eclass`] on each eclass.
    ///
    /// [`search_eclass`]: Searcher::search_eclass
    fn search(&self, egraph: &EGraph<L, T, N>) -> Vec<SearchMatches<L,T>> {
        egraph
            .classes()
            .filter_map(|e| self.search_eclass(egraph, e.id))
            .collect()
    }

    /// Returns the number of matches in the e-graph
    fn n_matches(&self, egraph: &EGraph<L, T, N>) -> usize {
        self.search(egraph).iter().map(|m| m.substs.len()).sum()
    }

    /// For patterns, return the ast directly as a reference
    fn get_pattern_ast(&self) -> Option<&PatternAst<L>> {
        None
    }

    /// Returns a list of the variables bound by this Searcher
    fn vars(&self) -> Vec<Var>;
}

/// The righthand side of a [`Rewrite`].
///
/// An [`Applier`] is anything that can do something with a
/// substitition ([`Subst`]). This allows you to implement rewrites
/// that determine when and how to respond to a match using custom
/// logic, including access to the [`Analysis`] data of an [`EClass`].
///
/// Notably, [`Pattern`] implements [`Applier`], which suffices in
/// most cases.
/// Additionally, `egg` provides [`ConditionalApplier`] to stack
/// [`Condition`]s onto an [`Applier`], which in many cases can save
/// you from having to implement your own applier.
///
/// # Example
/// ```
/// use egg::{rewrite as rw, *};
/// use std::sync::Arc;
///
/// define_language! {
///     enum Math {
///         Num(i32),
///         "+" = Add([Id; 2]),
///         "*" = Mul([Id; 2]),
///         Symbol(Symbol),
///     }
/// }
///
/// type EGraph = egg::EGraph<Math, MinSize>;
///
/// // Our metadata in this case will be size of the smallest
/// // represented expression in the eclass.
/// #[derive(Default)]
/// struct MinSize;
/// impl Analysis<Math> for MinSize {
///     type Data = usize;
///     fn merge(&mut self, to: &mut Self::Data, from: Self::Data) -> DidMerge {
///         merge_min(to, from)
///     }
///     fn make(egraph: &EGraph, enode: &Math) -> Self::Data {
///         let get_size = |i: Id| egraph[i].data;
///         AstSize.cost(enode, get_size)
///     }
/// }
///
/// let rules = &[
///     rw!("commute-add"; "(+ ?a ?b)" => "(+ ?b ?a)"),
///     rw!("commute-mul"; "(* ?a ?b)" => "(* ?b ?a)"),
///     rw!("add-0"; "(+ ?a 0)" => "?a"),
///     rw!("mul-0"; "(* ?a 0)" => "0"),
///     rw!("mul-1"; "(* ?a 1)" => "?a"),
///     // the rewrite macro parses the rhs as a single token tree, so
///     // we wrap it in braces (parens work too).
///     rw!("funky"; "(+ ?a (* ?b ?c))" => { Funky {
///         a: "?a".parse().unwrap(),
///         b: "?b".parse().unwrap(),
///         c: "?c".parse().unwrap(),
///         ast: "(+ (+ ?a 0) (* (+ ?b 0) (+ ?c 0)))".parse().unwrap(),
///     }}),
/// ];
///
/// #[derive(Debug, Clone, PartialEq, Eq)]
/// struct Funky {
///     a: Var,
///     b: Var,
///     c: Var,
///     ast: PatternAst<Math>,
/// }
///
/// impl Applier<Math, MinSize> for Funky {
///
///     fn apply_one(&self, egraph: &mut EGraph, matched_id: Id, subst: &Subst, searcher_pattern: Option<&PatternAst<Math>>, rule_name: Symbol) -> Vec<Id> {
///         let a: Id = subst[self.a];
///         // In a custom Applier, you can inspect the analysis data,
///         // which is powerful combination!
///         let size_of_a = egraph[a].data;
///         if size_of_a > 50 {
///             println!("Too big! Not doing anything");
///             vec![]
///         } else {
///             // we're going to manually add:
///             // (+ (+ ?a 0) (* (+ ?b 0) (+ ?c 0)))
///             // to be unified with the original:
///             // (+    ?a    (*    ?b       ?c   ))
///             let b: Id = subst[self.b];
///             let c: Id = subst[self.c];
///             let zero = egraph.add(Math::Num(0));
///             let a0 = egraph.add(Math::Add([a, zero]));
///             let b0 = egraph.add(Math::Add([b, zero]));
///             let c0 = egraph.add(Math::Add([c, zero]));
///             let b0c0 = egraph.add(Math::Mul([b0, c0]));
///             let a0b0c0 = egraph.add(Math::Add([a0, b0c0]));
///             // Don't forget to union the new node with the matched node!
///             if egraph.union(matched_id, a0b0c0) {
///                 vec![a0b0c0]
///             } else {
///                 vec![]
///             }
///         }
///     }
/// }
///
/// let start = "(+ x (* y z))".parse().unwrap();
/// Runner::default().with_expr(&start).run(rules);
/// ```
pub trait Applier<L, T, N>
where
    L: Language,
    T: FfnLattice,
    N: Analysis<L, T>,
{
    /// Apply many substititions.
    ///
    /// This method should call [`apply_one`] for each match.
    ///
    /// It returns the ids resulting from the calls to [`apply_one`].
    /// The default implementation does this and should suffice for
    /// most use cases.
    ///
    /// [`apply_one`]: Applier::apply_one()
    fn apply_matches(
        &self,
        egraph: &mut EGraph<L, T, N>,
        matches: &[SearchMatches<L, T>],
        rule_name: Symbol
    ) -> Vec<Id> {
        let mut added = vec![];
        for mat in matches {
            let ast = if egraph.are_explanations_enabled() {
                mat.ast.as_ref().map(|cow| cow.as_ref())
            } else {
                None
            };
            for subst in mat.substs.iter(){
                let ids = self.apply_one(egraph, mat.eclass, subst, ast, rule_name);
                added.extend(ids)
            }
        }
        added
    }

    /// For patterns, get the ast directly as a reference.
    fn get_pattern_ast(&self) -> Option<&PatternAst<L>> {
        None
    }

    /// Apply a single substitition.
    ///
    /// An [`Applier`] should add things and union them with `eclass`.
    /// Appliers can also inspect the eclass if necessary using the
    /// `eclass` parameter.
    ///
    /// This should return a list of [`Id`]s of eclasses that
    /// were changed. There can be zero, one, or many.
    /// When explanations mode is enabled, a [`PatternAst`] for
    /// the searcher is provided.
    ///
    /// [`apply_matches`]: Applier::apply_matches()
    fn apply_one(
        &self,
        egraph: &mut EGraph<L, T, N>,
        eclass: Id,
        subst: &Subst<T>,
        searcher_ast: Option<&PatternAst<L>>,
        rule_name: Symbol,
    ) -> Vec<Id>;

    /// Returns a list of variables that this Applier assumes are bound.
    ///
    /// `egg` will check that the corresponding `Searcher` binds those
    /// variables.
    /// By default this return an empty `Vec`, which basically turns off the
    /// checking.
    fn vars(&self) -> Vec<Var> {
        vec![]
    }
}

/// An [`Applier`] that checks a [`Condition`] before applying.
///
/// A [`ConditionalApplier`] simply calls [`check`] on the
/// [`Condition`] before calling [`apply_one`] on the inner
/// [`Applier`].
///
/// See the [`rewrite!`] macro documentation for an example.
///
/// [`apply_one`]: Applier::apply_one()
/// [`check`]: Condition::check()
#[derive(Clone, Debug)]
pub struct ConditionalApplier<C, A> {
    /// The [`Condition`] to [`check`] before calling [`apply_one`] on
    /// `applier`.
    ///
    /// [`apply_one`]: Applier::apply_one()
    /// [`check`]: Condition::check()
    pub condition: C,
    /// The inner [`Applier`] to call once `condition` passes.
    ///
    pub applier: A,
}

impl<C, A, N, T, L> Applier<L, T, N> for ConditionalApplier<C, A>
where
    L: Language,
    C: Condition<L, T, N>,
    A: Applier<L, T, N>,
    T: FfnLattice,
    N: Analysis<L,T>,
{
    fn apply_one(
        &self,
        egraph: &mut EGraph<L, T, N>,
        eclass: Id,
        subst: &Subst<T>,
        searcher_ast: Option<&PatternAst<L>>,
        rule_name: Symbol,
    ) -> Vec<Id> {
        if self.condition.check(egraph, eclass, subst) {
            self.applier
                .apply_one(egraph, eclass, subst, searcher_ast, rule_name)
        } else {
            vec![]
        }
    }

    fn vars(&self) -> Vec<Var> {
        let mut vars = self.applier.vars();
        vars.extend(self.condition.vars());
        vars
    }
}

/// A condition to check in a [`ConditionalApplier`].
///
/// See the [`ConditionalApplier`] docs.
///
/// Notably, any function ([`Fn`]) that doesn't mutate other state
/// and matches the signature of [`check`] implements [`Condition`].
///
/// [`check`]: Condition::check()
/// [`Fn`]: std::ops::Fn
pub trait Condition<L, T, N>
where
    L: Language,
    T: FfnLattice,
    N: Analysis<L,T>,
{
    /// Check a condition.
    ///
    /// `eclass` is the eclass [`Id`] where the match (`subst`) occured.
    /// If this is true, then the [`ConditionalApplier`] will fire.
    ///
    fn check(&self, egraph: &mut EGraph<L, T, N>, eclass: Id, subst: &Subst<T>) -> bool;

    /// Returns a list of variables that this Condition assumes are bound.
    ///
    /// `egg` will check that the corresponding `Searcher` binds those
    /// variables.
    /// By default this return an empty `Vec`, which basically turns off the
    /// checking.
    fn vars(&self) -> Vec<Var> {
        vec![]
    }
}

impl<L, F, T, N> Condition<L, T, N> for F
where
    L: Language,
    T: FfnLattice,
    N: Analysis<L,T>,
    F: Fn(&mut EGraph<L, T, N>, Id, &Subst<T>) -> bool,
{
    fn check(&self, egraph: &mut EGraph<L, T, N>, eclass: Id, subst: &Subst<T>) -> bool {
        self(egraph, eclass, subst)
    }
}

/// A [`Condition`] that checks if two terms are equivalent.
///
/// This condition adds its two [`Pattern`] to the egraph and passes
/// if and only if they are equivalent (in the same eclass).
///
#[derive(Debug)]
pub struct ConditionEqual<L,T: FfnLattice> {
    p1: Pattern<L,T>,
    p2: Pattern<L,T>,
}

impl<L: Language, T: FfnLattice> ConditionEqual<L,T> {
    /// Create a new [`ConditionEqual`] condition given two patterns.
    pub fn new(p1: Pattern<L,T>, p2: Pattern<L,T>) -> Self {
        ConditionEqual { p1, p2 }
    }
}

impl<L: FromOp, T: FfnLattice> ConditionEqual<L,T> {
    /// Create a ConditionEqual by parsing two pattern strings.
    ///
    /// This panics if the parsing fails.
    pub fn parse(a1: &str, a2: &str) -> Self {
        Self {
            p1: a1.parse().unwrap(),
            p2: a2.parse().unwrap(),
        }
    }
}

impl<L, T, N> Condition<L, T, N> for ConditionEqual<L,T>
where
    L: Language,
    T: FfnLattice,
    N: Analysis<L, T>,
{
    fn check(&self, _egraph: &mut EGraph<L, T, N>, _eclass: Id, _subst: &Subst<T>) -> bool {
        panic!("TODO: here we should not use apply_pat, but a variant of apply_pat that does not add new terms");
        /*
        let mut id_buf_1 = vec![0.into(); self.p1.ast.as_ref().len()];
        let mut id_buf_2 = vec![0.into(); self.p2.ast.as_ref().len()];
        let a1 = apply_pat(&mut id_buf_1, self.p1.ast.as_ref(), egraph, subst);
        let a2 = apply_pat(&mut id_buf_2, self.p2.ast.as_ref(), egraph, subst);
        a1 == a2
        */
    }

    fn vars(&self) -> Vec<Var> {
        let mut vars = self.p1.vars();
        vars.extend(self.p2.vars());
        vars
    }
}

#[cfg(test)]
mod tests {

    use crate::{SymbolLang as S, *};
    use std::str::FromStr;

    type EGraph = crate::EGraph<S, i32, ()>;

    #[test]
    fn conditional_rewrite() {
        crate::init_logger();
        let mut egraph = EGraph::default();

        let x = egraph.add(S::leaf("x"));
        let y = egraph.add(S::leaf("2"));
        let mul = egraph.add(S::new("*", vec![x, y]));

        let true_pat = Pattern::from_str("TRUE").unwrap();
        egraph.add(S::leaf("TRUE"));

        let pow2b = Pattern::from_str("(is-power2 ?b)").unwrap();
        let mul_to_shift = rewrite!(
            "mul_to_shift";
            "(* ?a ?b)" => "(>> ?a (log2 ?b))"
            if ConditionEqual::new(pow2b, true_pat)
        );

        println!("rewrite shouldn't do anything yet");
        egraph.rebuild();
        let apps = mul_to_shift.run(&mut egraph);
        assert!(apps.is_empty());

        println!("Add the needed equality");
        egraph.union_instantiations(
            &"(is-power2 2)".parse().unwrap(),
            &"TRUE".parse().unwrap(),
            &Default::default(),
            "direct-union".to_string()
        );

        println!("Should fire now");
        egraph.rebuild();
        let apps = mul_to_shift.run(&mut egraph);
        assert_eq!(apps, vec![egraph.find(mul)]);
    }

    #[test]
    fn fn_rewrite() {
        crate::init_logger();
        let mut egraph = EGraph::default();

        let start = RecExpr::from_str("(+ x y)").unwrap();
        let goal = RecExpr::from_str("xy").unwrap();

        let root = egraph.add_expr(&start);

        fn get(egraph: &EGraph, id: Id) -> Symbol {
            match &egraph[id].nodes[0] {
                SymbolLang::Symb(op, _child) => { return *op; }
                SymbolLang::Num(_x) => { panic!("Should never run"); }
            }
        }

        #[derive(Debug)]
        struct Appender {
            _rhs: PatternAst<S>,
        }

        impl Applier<SymbolLang, ()> for Appender {
            fn apply_one(
                &self,
                egraph: &mut EGraph,
                eclass: Id,
                subst: &Subst,
                searcher_ast: Option<&PatternAst<SymbolLang>>,
                rule_name: Symbol
            ) -> Vec<Id> {
                let a: Var = "?a".parse().unwrap();
                let b: Var = "?b".parse().unwrap();
                let a = get(egraph, subst[a]);
                let b = get(egraph, subst[b]);
                let s = format!("{}{}", a, b);
                if let Some(ast) = searcher_ast {
                    let (id, did_something) = egraph.union_instantiations(
                        ast,
                        &PatternAst::from_str(&s).unwrap(),
                        subst,
                        rule_name
                    );
                    if did_something {
                        vec![id]
                    } else {
                        vec![]
                    }
                } else {
                    let added = egraph.add(S::leaf(&s));
                    if egraph.union(added, eclass) {
                        vec![eclass]
                    } else {
                        vec![]
                    }
                }
            }
        }

        let fold_add = rewrite!(
            "fold_add"; "(+ ?a ?b)" => { Appender { _rhs: "?a".parse().unwrap()}}
        );

        egraph.rebuild();
        fold_add.run(&mut egraph);
        assert_eq!(egraph.equivs(&start, &goal), vec![egraph.find(root)]);
    }
}
