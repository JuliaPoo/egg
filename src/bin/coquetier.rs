/// coquetier (french for egg server)

use egg::{*, rewrite as rw};
use std::io;
use std::time::Instant;
use std::env;
use symbolic_expressions::{Sexp};
// use std::convert::TryInto;
use std::str::FromStr;
use std::fs::File;
use std::io::{BufWriter, Write, BufRead};
// use hashbrown::HashMap;
use std::convert::TryFrom;
use log::*;
use std::{
    fmt::{Debug},
};
use std::cmp::{Ordering, min};


type BuildHasher = fxhash::FxBuildHasher;
type HashMap<K, V> = hashbrown::HashMap<K, V, BuildHasher>;

define_language! {
    enum CoquetierLang {
        "+" = Add([Id; 2]),
        "*" = Mul([Id; 2]),
        "-" = Sub([Id; 2]),
        Num(i64),
        Symb(Symbol, Vec<Id>),
    }
}

/// Cost of terms to control simplification
#[warn(missing_docs)]
pub struct MotivateTrue<'a>{
    /// Number of terms that we are looking for
    pub number_appear: usize,
    /// Symbols we want to make expensive
    pub motivated: &'a HashMap<String, f64>
}
fn pmin(v1: Vec<i64>, v2:Vec<i64>) -> Vec<i64> {
    let mut res = Vec::new();
    for (idx,e) in v1.iter().enumerate() {
        res.push(min(e,&v2[idx]).clone());
    }
    return res;
}

impl CostFunction<CoquetierLang> for MotivateTrue<'_> {
    type Cost = (Vec<i64>, f64);
    fn cost<C>(&mut self, enode: &CoquetierLang, mut costs: C) -> Self::Cost
    where
        C: FnMut(Id) -> Self::Cost
    {
        let op_cost = 
            match &enode {
            CoquetierLang::Num(_) => { &0.0 }
            CoquetierLang::Symb(op,_children) => { self.motivated.get(&op.to_string()).unwrap_or(&4.0) }
            CoquetierLang::Add(_) => { &f64::INFINITY } // Shouldn't appear in our output expressions
            CoquetierLang::Mul(_) => { &f64::INFINITY }
            CoquetierLang::Sub(_) => { &f64::INFINITY }
            };
        let cost_post_mandate = enode.fold(*op_cost, |sum, id| 
                    sum + costs(id).1);
        let repeat1 = vec![1; self.number_appear];
        let cost_vector = enode.fold(repeat1, |sum, id| 
                    pmin(sum, costs(id).0));
        return (cost_vector, cost_post_mandate);

    }
}

// type NodeDataType = ();
#[derive(Default)]
pub struct ConstantFold;
type NodeDataType = ConstantFold;

impl Analysis<CoquetierLang, i32> for NodeDataType {
    type Data = Option<(i64, PatternAst<CoquetierLang>)>;

    fn get_ffn(_map: &Self::Data, _enode: &CoquetierLang) -> i32 { 0 }

    fn make(egraph: &EGraph<CoquetierLang, i32, Self>, enode: &CoquetierLang, _: i32) -> Self::Data {
        let x = |i: &Id| egraph[*i].data.as_ref().map(|d| d.0);
        Some(match enode {
            CoquetierLang::Num(c) => (*c, format!("{}", c).parse().unwrap()),
            CoquetierLang::Add([a, b]) => (
                x(a)? + x(b)?,
                format!("(+ {} {})", x(a)?, x(b)?).parse().unwrap(),
            ),
            CoquetierLang::Mul([a, b]) => (
                x(a)? * x(b)?,
                format!("(* {} {})", x(a)?, x(b)?).parse().unwrap(),
            ),
            CoquetierLang::Sub([a, b]) => (
                x(a)? - x(b)?,
                format!("(- {} {})", x(a)?, x(b)?).parse().unwrap(),
            ),
            _ => return None,
        })
    }

    fn merge(&mut self, a: &mut Self::Data, b: Self::Data) -> DidMerge {
        match (a.as_mut(), &b) {
            (None, None) => DidMerge(false, false),
            (None, Some(_)) => {
                *a = b;
                DidMerge(true, false)
            }
            (Some(_), None) => DidMerge(false, true),
            (Some(_), Some(_)) => DidMerge(false, false),
        }
        // if a.is_none() && b.is_some() {
        //     *a = b
        // }
        // cmp
    }

    fn modify(egraph: &mut EGraph<CoquetierLang, i32, Self>, id: Id) -> bool {
        let class = egraph[id].clone();
        if let Some((c, pat)) = class.data {
            if egraph.are_explanations_enabled() {
                egraph.union_instantiations(
                    &pat,
                    &format!("{}", c).parse().unwrap(),
                    &Default::default(),
                    "%constant_fold%".to_string()
                    // ffn_zero(),
                );
            } else {
                let added = egraph.add(CoquetierLang::Num(c));
                egraph.union(id, added);
            }
            // to not prune, comment this out
            egraph[id].nodes.retain(|n| n.is_leaf());

            #[cfg(debug_assertions)]
            egraph[id].assert_unique_leaves();
            return true;
        }
        false
    }
}



// type NodeDataType = HashMap<CoquetierLang, i32>;
// impl Analysis<CoquetierLang, i32> for NodeDataType {
//     type Data = NodeDataType;

//     fn get_ffn(map : &Self::Data, enode: &CoquetierLang) -> i32 { 
//         let s = map.get(enode);
//         info!("Try to search enode: {:?} ffn: {:?}", enode, s);
//         return *s.unwrap_or(&0);
//         // return 0;
//     }
//     fn make(_egraph: &EGraph<CoquetierLang, i32, Self>, enode: &CoquetierLang, ffn: i32) -> Self::Data {
//         // In the egraph we should keep track of the current ffn level? This is not good enough.
//         // we should pass another value to build the analysis
//         let mut m : Self::Data = Default::default();
//         m.insert(enode.clone(),ffn);
//         return m;
//     }

//     fn merge(&mut self, a: &mut Self::Data, b: Self::Data) -> DidMerge {
//         // Merge is straightforward: key are merged the same way that classes
//         // are merged (enodes are canonicalized), and the values are min-ed together
//         // DidMerge(false, false)
//         let mut change = false;
//         for (key, value) in b {
//             if let Some(v) = a.get(&key) {
//                 if value != *v { change = true; }
//                 a.insert(key, std::cmp::min(value,*v));
//             } else {
//                 a.insert(key, value);
//             }
//         }
//         DidMerge(change, false)
//     }

//     // fn pre_union(egraph: &EGraph<L, Self>, id1: Id, id2: Id) {}
//     fn modify(egraph: &mut EGraph<CoquetierLang, i32, Self>, id: Id) -> bool { 
//         let mut m : Self::Data = Default::default();
//         let mut change = false;
//         for (key, value) in &egraph[id].data {
//             let normalized_key = key.clone().map_children(|i| egraph.find(i));
//             if let Some(v) = m.get(&normalized_key) {
//                 if v != value { change = true; }
//                 m.insert(normalized_key, std::cmp::min(*value,*v));

//             } else {
//                 m.insert(normalized_key, *value);
//             }
//         }
//         egraph[id].data = m;
//         return change;
//     }
// }

/// A utility for implementing [`Analysis::merge`]
/// when the `Data` type has a total ordering.
/// This will take the maximum of the two values.
pub fn merge_max<T: Ord>(to: &mut T, from: T) -> DidMerge {
    let cmp = (*to).cmp(&from);
    match cmp {
        Ordering::Less => {
            *to = from;
            DidMerge(true, false)
        }
        Ordering::Equal => DidMerge(false, false),
        Ordering::Greater => DidMerge(false, true),
    }
}

/// A utility for implementing [`Analysis::merge`]
/// when the `Data` type has a total ordering.
/// This will take the minimum of the two values.
pub fn merge_min<T: Ord>(to: &mut T, from: T) -> DidMerge {
    let cmp = (*to).cmp(&from);
    match cmp {
        Ordering::Less => DidMerge(false, true),
        Ordering::Equal => DidMerge(false, false),
        Ordering::Greater => {
            *to = from;
            DidMerge(true, false)
        }
    }
}



struct Rule {
    rulename: String,
    quantifiers: Vec<String>,
    sideconditions: Vec<Sexp>,
    conclusion_lhs: Sexp,
    conclusion_rhs: Sexp,
    triggers: Vec<Sexp>,
}

impl Rule {
    pub fn new() -> Self {
        Self {
            rulename: Default::default(),
            quantifiers: Default::default(),
            sideconditions: Default::default(),
            conclusion_lhs: Default::default(),
            conclusion_rhs: Default::default(),
            triggers: Default::default(),
        }
    }
    

    pub fn is_eq(&self) -> bool {
        let true_typed : Sexp = Sexp::List(vec![ Sexp::String("annot".to_string()), 
                                        Sexp::String("&True".to_string()),
                                        Sexp::String("&Prop".to_string()),
                                        Sexp::String("0".to_string()),
                                         ]);
        return self.conclusion_lhs != true_typed || (self.rulename == "reify_fundamental".to_string());
    }

    pub fn needs_multipattern(&self) -> bool {
        !self.sideconditions.is_empty() || !self.triggers.is_empty()
    }

    pub fn to_rewrite(&self) -> Rewrite<CoquetierLang, i32, NodeDataType> {
        // if e is (= A B), returns [(name, A); (name, B)]
        // else returns [(name, e)]
        fn multipattern_part(name: &str, e: &Sexp) -> Vec<(Var, PatternAst<CoquetierLang>)> {
            let v = Var::from_str(name).unwrap();
            if e.is_list() && e.list_name().unwrap() == "=" {
                e.list().unwrap()[1..].iter().map(|p| (v, p.to_string().parse().unwrap())).collect()
            } else {
                vec![(v, e.to_string().parse().unwrap())]
            }
        }

        let applier: Pattern<CoquetierLang, i32> = self.conclusion_rhs.to_string().parse().unwrap();
        if self.needs_multipattern() {
            let mut patterns: Vec<(Var, PatternAst<CoquetierLang>)> = Vec::new();
            for (i, p) in self.sideconditions.iter().enumerate() {
                patterns.extend(multipattern_part(&format!("?$hyp{}", i), p))
            }
            for (i, p) in self.triggers.iter().enumerate() {
                patterns.extend(multipattern_part(&format!("?$pat{}", i), p))
            }
            patterns.extend(multipattern_part("?$lhs", &self.conclusion_lhs));
            let searcher: MultiPattern<CoquetierLang,i32> = MultiPattern::new(patterns);
            // println!("{}: {} => {}", self.rulename, searcher, applier);
            Rewrite::new(self.rulename.clone(), searcher, applier).unwrap()
        } else {
            let searcher: Pattern<CoquetierLang, i32> = self.conclusion_lhs.to_string().parse::<Pattern<CoquetierLang,i32>>().unwrap();
            // println!("{}: {} => {}", self.rulename, searcher, applier);
            Rewrite::new(self.rulename.clone(), searcher, applier).unwrap()
        }
    }
}

struct Server {
    verbose : bool,
    infile : String,
    outfile : String,
    rules: Vec<Rule>,
    runner: Runner<CoquetierLang, i32, NodeDataType>, // TODO Analysis: 
    //  ,
    cost: HashMap<String, f64>,
    require_terms : Vec<RecExpr<CoquetierLang>> 
}

impl Server {
    pub fn new(infile: String, outfile:String) -> Self {
    let mut c:HashMap<String, f64> = Default::default();
        c.insert("&True".to_string(),1.0);
        c.insert("&Prop".to_string(),1.0);
        Self { 
            // verbose : true,
            verbose : false,

            infile: infile,
            outfile: outfile,
            rules: Default::default(),
            runner: Runner::default()
                .with_iter_limit(8)
                .with_explanations_enabled()
                .with_node_limit(1000000)
                .with_time_limit(instant::Duration::from_secs(60)),
            cost: c,
            require_terms: Vec::new()
        }
    }

    pub fn verbose(&self) -> bool {
        return self.verbose;
    }

    fn process_line(&mut self, line: Sexp) -> () {
        match line {
            Sexp::List(l) => {
                match &l[0] {
                    Sexp::String(command) => {
                        let c: &str = command;
                        match c {
                            "set-logic" => {/*ignore*/}
                            "set-option" => {/*ignore*/}
                            "declare-sort" => {/*ignore*/}
                            "declare-fun" => {/*ignore*/}
                            "assert" => { self.process_assert(l) }
                            "minimize" => { self.process_minimize(l) }
                            "search" => { self.process_search(l) }
                            "avoid" => { self.process_avoid(l) }
                            "require" => { self.process_require(l) }
                            _ => { panic!("unknown command {}", command); }
                        }
                    }
                    _ => panic!("First element of sexpr is not a command")
                }
            }
            _ => { panic!("Expected an Sexp::List, but got {}", line)}
        }
    }
    fn process_avoid(&mut self, l: Vec<Sexp>) -> () {
        match &l[1] {
            Sexp::String(res) => { self.cost.insert(res.clone(), 10000.); }
            _ => { panic!("assert expects list") }
        }

    }

    fn process_require(&mut self, l: Vec<Sexp>) -> () {
        match &l[1] {
            res => { 
                let expr : RecExpr<CoquetierLang> = res.to_string().parse().unwrap();
                self.runner.add_expr(&expr);
                self.require_terms.push(expr); 
            }
        }
    }


    fn process_assert(&mut self, l: Vec<Sexp>) -> () {
        match &l[1] {
            Sexp::List(ll) => {
                match &ll[0] {
                    Sexp::String(s) => {
                        let kind: &str = s;
                        match kind {
                            "$initial" => { self.process_initial_expr(&ll[1]); }
                            "!" => { self.process_rule(ll); }
                            _ => { panic!("expected $initial or annotation, found {}", kind) }
                        }
                    }
                    _ => { panic!("head of arg to assert must be an atom") }
                }
            }
            _ => { panic!("assert expects list") }
        }

    }

    fn process_initial_expr(&mut self, se: &Sexp) -> () {
        // TODO can we avoid the round-trip?
        let expr: RecExpr<CoquetierLang> = se.to_string().parse().unwrap();
        // TODO can we avoid inlining Runner.with_expr?
        //self.runner = self.runner.with_expr(&sy);
        self.runner.add_expr(&expr);
    }

    // turns sexp ("varname" U) into "varname"
    fn parse_quantifier(s: &Sexp) -> String {
        s.list().unwrap()[0].string().unwrap().clone()
    }

    // r: ["!", formula, ":named", name]
    fn process_rule(&mut self, r: &Vec<Sexp>) -> () {
        self.rules.push(Server::parse_rule(r));
    }

    // r: ["!", formula, ":named", name]
    fn parse_rule(r: &Vec<Sexp>) -> Rule {
        let mut result = Rule::new();
        result.rulename = r[3].string().unwrap().clone();

        // unwrap foralls
        let mut formula: &Sexp = &r[1];
        let mut formula_l = formula.list().unwrap();
        let mut head: &str = &formula_l[0].string().unwrap();
        if head == "forall" {
            // formula_l = ["forall", quantifiers, body]
            result.quantifiers = formula_l[1].list().unwrap().iter().map(Server::parse_quantifier).collect();
            formula = &formula_l[2];
            formula_l = formula.list().unwrap();
            head = &formula_l[0].string().unwrap();
        }

        // unwrap triggers
        if head == "!" {
            // formula_l = ["!", body, ":pattern", patternlist]
            result.triggers = formula_l[3].list().unwrap().to_vec();
            formula = &formula_l[1];
            formula_l = formula.list().unwrap();
            head = &formula_l[0].string().unwrap();
        }

        // unwrap implications
        if head == "=>" {
            // formula_l = ["=>", side1, ..., sideN, conclusion]
            result.sideconditions = formula_l[1..formula_l.len()-1].to_vec();
            formula = formula_l.last().unwrap();
            formula_l = formula.list().unwrap();
            head = &formula_l[0].string().unwrap();
        }

        // unwrap conclusion
        if head == "=" {
            // formula_l = ["=", lhs, rhs]
            result.conclusion_lhs = formula_l[1].clone();
            result.conclusion_rhs = formula_l[2].clone();
        } else {
            panic!("Conclusion is not an equality, but {}", formula)
        }

        result
    }

    /// Indicates whether the conclusion of the rule with `name` is an equality
    fn is_eq(&self, name: &str) -> Option<bool> {
        let o = self.rules.iter().find(|r| r.rulename == name);
        match o {
          Some(r) => { return Some(r.is_eq()); }
          None => { return None; }
        }      
    }

    fn lemma_arity(&self, name: &str) -> usize {
        let r = self.rules.iter().find(|r| r.rulename == name).unwrap();
        let quants : Vec<&String>= r.quantifiers.iter().filter(|s| !s.starts_with("?ffn")).collect();
        quants.len() + r.sideconditions.len()
    }

    fn obtain_rewrites(&mut self) -> Vec<Rewrite<CoquetierLang, i32, NodeDataType>> {
        let mut rewrites: Vec<Rewrite<CoquetierLang, i32, NodeDataType>> = self.rules.iter().map(|r| r.to_rewrite()).collect();
        rewrites.push(
            rw!("%Q_cast_plus%";
                "
                (annot
                    (&Qplus
                        (annot (!Qmake (annot ?a ?c) (annot !xH &positive)) &Q)
                        (annot (!Qmake (annot ?b ?c) (annot !xH &positive)) &Q))
                    &Q)
                "
                =>
                "(annot (!Qmake (annot (+ ?a ?b) ?c) (annot !xH &positive)) &Q)"
            )
        );
        rewrites.push(
            rw!("%Q_cast_mult%";
                "
                (annot
                    (&Qmult
                        (annot (!Qmake (annot ?a ?c) (annot !xH &positive)) &Q)
                        (annot (!Qmake (annot ?b ?c) (annot !xH &positive)) &Q))
                    &Q)
                "
                =>
                "(annot (!Qmake (annot (* ?a ?b) ?c) (annot !xH &positive)) &Q)"
            )
        );
        rewrites.push(
            rw!("%Q_cast_minus%";
                "
                (annot
                    (&Qminus
                        (annot (!Qmake (annot ?a ?c) (annot !xH &positive)) &Q)
                        (annot (!Qmake (annot ?b ?c) (annot !xH &positive)) &Q))
                    &Q)
                "
                =>
                "(annot (!Qmake (annot (- ?a ?b) ?c) (annot !xH &positive)) &Q)"
            )
        );
        rewrites
    }

    fn process_search(&mut self, l: Vec<Sexp>) -> () {
        let expr: Pattern<CoquetierLang, i32> = l[1].to_string().parse().unwrap();
        // let ffn_limit: Ffn = l[2].i().unwrap().try_into().unwrap();
        // self.runner.ffn_limit = ffn_limit;
        let rewrites: Vec<Rewrite<CoquetierLang, i32, NodeDataType>> = self.obtain_rewrites();
        let t = Instant::now();
        self.runner.run_nonchained(rewrites.iter());
        let saturation_time = t.elapsed().as_secs_f64();
        if self.verbose { 
            println!("Saturation took {saturation_time:.3}s");
            self.runner.print_report();
        }
     
        
        let t = Instant::now();
        if self.verbose {
            let dumppath = format!("{}.dump", self.infile); 
            print_eclasses_to_file(&self.runner.egraph, &dumppath);
        }
        let dump_time = t.elapsed().as_secs_f64();
        if self.verbose { println!("Dumping the egraph took {dump_time:.3}s"); }
       

        // We now want to give back the results
        let to_search = [].to_vec();
        let result = expr.search(&self.runner.egraph);
        let extractor = Extractor::new(&self.runner.egraph, MotivateTrue{motivated: &self.cost, number_appear: to_search.len()}, to_search);
        let path = &self.outfile; 
        let f = File::create(path).expect("unable to create file");
        let mut writer = BufWriter::new(f);

        if self.verbose { println!("Start listing potential results"); }
        for search_match in &result {
            if self.verbose { println!("Found evars candidates"); }
            for subst in &search_match.substs {
                writeln!(writer, "(* Substitution suggested *)").expect("failed to write to writer");
                for (var,id) in &subst.vec {
                    let id = id.unwrap();
                    let (_best_cost, best) = extractor.find_best(id);
                    let sbest = format!("{}",best);
                    let sexpbest = symbolic_expressions::parser::parse_str(&sbest).unwrap(); 
                    let processed = holify_aux(&sexpbest);
                    writeln!(writer, "var {}\nval {}",var.to_string(), processed).expect("failed to write to writer");
                }
            }
        } 
        if self.verbose { println!("Wrote proof to {path}"); }
    }

    // l = ["minimize", expr, ffn_limit]
    fn process_minimize(&mut self, l: Vec<Sexp>) -> () {
        let ffn_limit: usize = usize::try_from(l[2].i().unwrap()).unwrap();
        self.runner.set_iter_limit(ffn_limit + 4);
        let expr: RecExpr<CoquetierLang> = l[1].to_string().parse().unwrap();
        // let expr0: RecExpr<CoquetierLang> = "0".to_string().parse().unwrap();
        // let expr1: RecExpr<CoquetierLang> = "1".to_string().parse().unwrap();
        // let expr2: RecExpr<CoquetierLang> = "2".to_string().parse().unwrap();
        // let expr3: RecExpr<CoquetierLang> = "3".to_string().parse().unwrap();
        // let expr4: RecExpr<CoquetierLang> = "4".to_string().parse().unwrap();
        // let expr5: RecExpr<CoquetierLang> = "5".to_string().parse().unwrap();
        // let expr6: RecExpr<CoquetierLang> = "6".to_string().parse().unwrap();
        // self.runner.add_expr(&expr0);
        // self.runner.add_expr(&expr1);
        // self.runner.add_expr(&expr2);
        // self.runner.add_expr(&expr3);
        // self.runner.add_expr(&expr4);
        // self.runner.add_expr(&expr5);
        // self.runner.add_expr(&expr6);

        // for op in ["Qplus", "Qminus", "Qmult"].iter() {
        //     for a in (1..4).into_iter() {
        //         for b in (1..4).into_iter() {
        //             let expr_const: RecExpr<CoquetierLang> = format!("
        //             (annot
        //                 (&{op}
        //                     (annot (!Qmake (annot {a} &Z) (annot !xH &positive)) &Q)
        //                     (annot (!Qmake (annot {b} &Z) (annot !xH &positive)) &Q))
        //                 &Q)
        //             ").parse().unwrap();
        //             self.runner.add_expr(&expr_const);
        //         }
        //     }
        // }

        self.runner.add_expr(&expr);

        let rewrites: Vec<Rewrite<CoquetierLang, i32, NodeDataType>> = self.obtain_rewrites();
        let t = Instant::now();
        self.runner.run_nonchained(rewrites.iter());
        let saturation_time = t.elapsed().as_secs_f64();
        if self.verbose { 
            println!("Saturation took {saturation_time:.3}s"); 
            self.runner.print_report();
        }
        
        let root = *self.runner.roots.last().unwrap();
        let t = Instant::now();
        if self.verbose {
            let dumppath = format!("{}.dump", self.infile); 
            print_eclasses_to_file(&self.runner.egraph, &dumppath);
        }
        let dump_time = t.elapsed().as_secs_f64();
        if self.verbose { println!("Dumping the egraph took {dump_time:.3}s"); }
        let terms = self.require_terms.clone();
        let length = terms.len();
        
        for e in &terms {
            self.runner.add_expr(&e);
        }

        fn kronecker(l: usize, i: usize) -> Vec<i64> {
            let mut res = vec![1; l];
            res[i] = 0;
            return res;
        }


        let to_search : Vec<((Vec<i64>, f64), RecExpr<CoquetierLang>)> = terms.iter().enumerate().map(|(idx,e)| 
                                                    ((kronecker(length ,idx),0.),e.clone())).collect();
        let extractor = Extractor::new(&self.runner.egraph, MotivateTrue{motivated: &self.cost, number_appear: to_search.len()}, to_search);
        let (best_cost, best) = extractor.find_best(root);
        info!("Simplified\n{}\nto\n{}\nwith cost {}", expr, best, best_cost.1);
        let mut ctor_equals = None;

        if best_cost.1 != 6.0 {
            // Only if we failed to simplify to True (only expression of cost equal to one)
            // then check try to find an inconsistency. This allow us to use
            // Coquetier to generate the proof of equality between the two distinct
            // constructor int the environment that is inconsistent
            ctor_equals = find_distinct_ctor_equals(&self.runner.egraph);
        }
        match &ctor_equals {
            Some((t1,t2)) => { 
                let t = Instant::now();
                let exprt1 : RecExpr<CoquetierLang>= t1.parse().unwrap();
                let exprt2 : RecExpr<CoquetierLang>= t2.parse().unwrap();
                
                // println!("Absurd found the following contradiction: {} {}", exprt1, exprt2);
                let mut expl = self.runner.explain_equivalence(&exprt1, &exprt2);
                info!("{}", expl.get_string());
                let explanations = expl.get_flat_sexps();
                let expl_time = t.elapsed().as_secs_f64();
                info!("Absurd found Explanation length: {} (took {:.3}s to generate)", explanations.len(), expl_time);

                let path = &self.outfile; 
                let f = File::create(path).expect("unable to create file");
                let mut writer = BufWriter::new(f);

                let mut explanation = explanations.iter();
                explanation.next();
                writeln!(writer, "(* CONTRADICTION *)").expect("failed to write to writer");
                let st1 = symbolic_expressions::parser::parse_str(&t1).unwrap(); 
                let st2 = symbolic_expressions::parser::parse_str(&t2).unwrap(); 
                let t1 = holify_aux(&st1);
                let t2 = holify_aux(&st2);
                writeln!(writer, "assert ({} = {}) as ABSURDCASE.", t1, t2).expect("failed to write to writer");
                print_equality_proof_to_writer(
                    true,
                    explanation, 
                    &mut writer, 
                    &|name| self.is_eq(name), 
                    &|name| self.lemma_arity(name));
                if self.verbose { println!("Wrote proof to {path}"); }}
            None => {
                let t = Instant::now();
                let mut expl = self.runner.explain_equivalence(&expr, &best);
                info!("{}", expl.get_string());
                let explanations = self.runner.explain_equivalence(&expr, &best).get_flat_sexps();
                let expl_time = t.elapsed().as_secs_f64();
                if self.verbose { println!("Explanation length: {} (took {:.3}s to generate)", explanations.len(), expl_time); }

                let path = &self.outfile; 
                // let path = "./coquetier_proof_output.txt";
                let f = File::create(path).expect("unable to create file");
                let mut writer = BufWriter::new(f);

                let mut explanation = explanations.iter();
                explanation.next();

                writeln!(writer, "(* SIMPLIFICATION *)").expect("failed to write to writer");
                print_equality_proof_to_writer(
                    false,
                    explanation, 
                    &mut writer, 
                    &|name| self.is_eq(name), 
                    &|name| self.lemma_arity(name));
                if self.verbose { println!("Wrote proof to {path}"); }}
        }
    }

    pub fn run_on_reader(&mut self, reader: &mut dyn BufRead) -> () {
        // Add a generic type embedding collapse
        // let sexp = symbolic_expressions::parser::parse_str("(assert(!(forall((?t $U) (?x $U) (?y $U) (?n $U) (?m $U)) (=> (= (annot ?x ?t ?n) (annot ?y ?t ?m)) (= ?x ?y))) :named eggTypeEmbedding))").unwrap();
        // self.process_line(sexp);
        // // Il faut une égalité
        // let sexp = symbolic_expressions::parser::parse_str("(assert(!(forall((?t $U) (?x $U) (?n $U)(?m $U)) (=> (= (annot ?x ?t ?n) (annot ?x ?t ?n)) (= (annot ?x ?t ?m) (annot ?x ?t ?m)) (= (annot ?x ?t ?n) (annot ?x ?t ?m)))) :named eggTypeEmbedding2))").unwrap();
        // let sexp = symbolic_expressions::parser::parse_str("(assert(!(forall((?t $U) (?x $U) (?n $U)(?m $U)) (=> (annot ?x ?t ?n) (annot ?x ?t ?m) (= (annot ?x ?t ?n) (annot ?x ?t ?m)))) :named eggTypeEmbedding2))").unwrap();
        // self.process_line(sexp);
        loop {
            let mut buffer = String::new();
            let bytes_read = reader.read_line(&mut buffer).expect("failed to read line from stdin");
            if bytes_read == 0 { 
                
                break; 
            }
            let sexp = symbolic_expressions::parser::parse_str(&buffer).unwrap();
            self.process_line(sexp);
        }
    }
}

fn main() {
    let args: Vec<String> = env::args().collect();
    let infile = &args[1];
    let outfile = &args[2];
    let t = Instant::now();
    env_logger::init();
    let mut server = Server::new(infile.to_string(), outfile.to_string());
    let use_stdin = false;
    match env::var("EGG_VERBOSE")  {
        Ok(_v) => server.verbose=true,
        Err(_e) => {}
    }

    if use_stdin {
        server.run_on_reader(&mut io::stdin().lock());
    } else {
        let path = infile; 
        let file = File::open(path).unwrap();
        let mut reader = io::BufReader::new(file);
        server.run_on_reader(&mut reader);
    }
    let main_time = t.elapsed().as_secs_f64();
    if server.verbose() { println!("coquetier's main() function took {main_time}s"); }
}
