use egg::*;
use symbolic_expressions::*;
use std::fs::File;
use std::io::{BufWriter, Write};

fn main() {
    env_logger::init();
    run_simplifier(simplify, prove);
    // run_simplifier(simplify);
    // simplify("(wadd x y)");
}

fn holify_aux(e: &Sexp) -> Sexp {
    match e {
        Sexp::String(s) => Sexp::String(s.replace("AT", "@").replace("DOT", ".")),
        Sexp::Empty => Sexp::Empty,
        Sexp::List(l) => {
            if l[0] == Sexp::String("Rewrite=>".to_string()) {
                Sexp::String("hole".to_string())
            } else if l[0] == Sexp::String("Rewrite<=".to_string()) {
                Sexp::String("hole".to_string())
            } else {
                Sexp::List(l.iter().map(holify_aux).collect())
            }
        }
    }
}

fn lemma_arity(s: &str) -> usize {
    match get_lemma_arity(s) {
        Some(a) => { return a; }
        None => { 
            match s.find('O') {
                Some(idx) => {  /* "optimization" */ return idx - 5; }
                None => { return 0; }
            }
        }
    }
}

fn add_arity_th_name(e: &Sexp) -> Sexp {
    match e {
        Sexp::String(s) => {
            // let-bound variables in context like "x := rhs : T"
            // were transformed into are rule named x$def saying "x => rhs", and will
            // now be translated back to (@eq_refl _ x)
            if s.ends_with("$def") {
                Sexp::List(vec![
                    Sexp::String("@eq_refl".to_string()),
                    Sexp::String("_".to_string()),
                    Sexp::String(s[..s.len()-4].to_string()),
                ])
            } else {
                let number = lemma_arity(s);
                if number == 0 {
                    Sexp::String(s.clone().replace("-rev", ""))
                } else {
                    let mut v = vec![e.clone()];
                    let arg_implicit_aux = ["_"].repeat(number);
                    let arg_implicit = arg_implicit_aux
                        .iter()
                        .map(|s| Sexp::String(s.to_string()))
                        .collect::<Vec<_>>();
                    v.extend(arg_implicit);
                    Sexp::List(v.clone())
                }
            }
        }
        _ => {
            panic!("not Sexp::String");
        }
    }
}

fn find_rw(e: &Sexp) -> Option<(bool, String, Sexp, Sexp)> {
    match e {
        Sexp::String(_s) => return None,
        Sexp::Empty => return None,
        Sexp::List(l) => {
            match &l[0] {
                Sexp::String(op) => {
                    if op.starts_with("Rewrite") {
                        let fw1 = op.starts_with("Rewrite=>");
                        match &l[1] {
                            Sexp::String(s) => {
                                let fw2 = !s.contains("-rev");
                                let fw = fw1 ^ fw2;
                                return Some((fw, s.to_string(), add_arity_th_name(&l[1]), l[2].clone()))
                            }
                            _ => { panic!("Expected rule name after Rewrite") }
                        }
                    }
                }
                _ => ()
            }
            // only executed if we have not yet returned:
            for i in l.iter() {
                match find_rw(i) {
                    None => {}
                    Some(a) => {
                        return Some(a);
                    }
                }
            }
            return None;
        }
    }
}

fn holify(e: &Sexp) -> (Sexp, bool, String, Sexp, Sexp) {
    match find_rw(e) {
        None => {
            panic!("There is no rewrite in the sexp")
        }
        Some((fw, name_th, applied_th, new)) => {
            return (holify_aux(e), fw, name_th, applied_th, holify_aux(&new));
        }
    }
}

//  Return two terms that staret with distinct constructors but are in the same eclass
fn find_distinct_ctor_equals<L: Language + std::fmt::Display, N: Analysis<L>>(eg: &EGraph<L, N>) -> Option<(String, String)> {

    let extractor = Extractor::new(eg, AstSize);
    let classes : Vec<&EClass<L, _>> = eg.classes().collect();
    for class in classes {
        let mut last_ctor_seen : Option<(String, String)> = None;
        for node in class.nodes.iter() {
            // The display() method implemented by define_language! macro happens to print only the op name
            // TODO is there a cleaner way to obtain the op name?
            let opname = format!("{}", node);
            let (_arity, is_nonprop_ctor) = symbol_metadata(&opname).unwrap();
            if is_nonprop_ctor {
                match last_ctor_seen.clone() {
                    Some((ctor1, children1)) => { 
                        if !(ctor1 == opname) 
                            {
                                let mut s: String; 
                                s = "".to_string();
                                // Find representant for our children of ctor2
                                for child in node.children().iter() {
                                    let (_best_cost, best) = extractor.find_best(*child);
                                    s.push_str (&format!(" {}", best))
                                }
                                return Some((format!("({} {})", ctor1, children1), format!("({} {})", opname, s)))}
                        }
                    None => { 
                            let mut s: String; 
                            s = "".to_string();
                            // Find representant for our children of ctor2
                            for child in node.children().iter() {
                                let (_best_cost, best) = extractor.find_best(*child);
                                s.push_str (&format!(" {}", best))
                            }
                            last_ctor_seen = Some((opname, s)); }
                }
            }
        }
    }
    return None;
}

struct MotivateTrue;
impl CostFunction<CoqSimpleLanguage> for MotivateTrue{
    type Cost = f64;
    fn cost<C>(&mut self, enode: &CoqSimpleLanguage, mut costs: C) -> Self::Cost
    where
        C: FnMut(Id) -> Self::Cost
    {
    // "&True" = IDTrue([Id; 0]),
        let op_cost = match enode {
            CoqSimpleLanguage::IDTrue(_) => 1.0,
            _ => 2.0
        };
        enode.fold(op_cost, |sum, id| sum + costs(id))
    }
}

impl CostFunction<SymbolLang> for MotivateTrue {
    type Cost = f64;
    fn cost<C>(&mut self, enode: &SymbolLang, mut costs: C) -> Self::Cost
    where
        C: FnMut(Id) -> Self::Cost
    {
        let op_cost = if *enode == SymbolLang::leaf("&True") { 1.0 } else { 2.0 };
        enode.fold(op_cost, |sum, id| sum + costs(id))
    }
}

/// parse an expression, simplify it using egg, and pretty print it back out
#[allow(dead_code, unused_must_use)]
fn simplify(s: &str, extra_s : Vec<&str>) -> () {
    // parse the expression, the type annotation tells it which Language to use
    let expr: RecExpr<CoqSimpleLanguage> = s.parse().unwrap();
    // let expr: RecExpr<SymbolLang> = s.parse().unwrap();

    // let extra_exprs : Vec<RecExpr<SymbolLang>> = extra_s.iter().map(|s| { s.parse::<RecExpr<SymbolLang>>().unwrap()}).collect();
    let extra_exprs : Vec<RecExpr<CoqSimpleLanguage>> = extra_s.iter().map(|s| { s.parse::<RecExpr<CoqSimpleLanguage>>().unwrap()}).collect();
    // simplify the expression using a Runner, which creates an e-graph with
    // the given expression and runs the given rules over it
    let mut runner = Runner::default()
        .with_explanations_enabled()
        .with_node_limit(10000)
        .with_time_limit(instant::Duration::from_secs(10))
        .with_expr(&expr)
        // .with_ffn_limit(ffn_limit)
        .with_exprs(extra_exprs.iter().map(|x| &*x).collect())
        .run(&make_rules());
    // the Runner knows which e-class the expression given with `with_expr` is in
    let root = runner.roots[0];

    print_eclasses_to_file(&runner.egraph, "./coq_eclasses_log.txt");
    runner.print_report();
    let extractor = Extractor::new(&runner.egraph, MotivateTrue);
    let (best_cost, best) = extractor.find_best(root);
    let mut ctor_equals = None;

    if best_cost != 1.0 {
        // Only if we failed to simplify to True (only expression of cost equal to one)
        // then check try to find an inconsistency. This allow us to use
        // Coquetier to generate the proof of equality between the two distinct
        // constructor int the environment that is inconsistent
        ctor_equals = find_distinct_ctor_equals(&runner.egraph);
    }
    match &ctor_equals {
        Some((t1,t2)) => { 
            // t1 t2 are provably equal to eachother when they should not be
            println!("Contradiction: {} {}", t1, t2);
            let path = get_proof_file_path();
            let f = File::create(path).expect("unable to create file");
            let mut writer = BufWriter::new(f);
            writeln!(writer, "(* CONTRADICTION *)");
            writeln!(writer, "assert ({} = {}) as ABSURDCASE.", t1, t2);
            // Now print the proof that those two are equal
            // Figure out exprt1 and exprt2 
            let exprt1 : RecExpr<CoqSimpleLanguage>= t1.parse().unwrap();
            let exprt2 : RecExpr<CoqSimpleLanguage>= t2.parse().unwrap();
            // let exprt1 : RecExpr<SymbolLang>= t1.parse().unwrap();
            // let exprt2 : RecExpr<SymbolLang>= t2.parse().unwrap();
            // TODO cleanup to share this piece of code that is currently copy pasted nxt case.
            let explanations = runner.explain_equivalence(&exprt1, &exprt2).get_flat_sexps();
            println!("Explanation length: {}", explanations.len());
            let mut explanation = explanations.iter();
            explanation.next();
            writeln!(writer, "unshelve (");
            for exp in explanation {
                let (holified, fw, name_th, applied_th, new) = holify(exp);
                let rw_lemma = if fw { "@rew_zoom_fw" } else { "@rew_zoom_bw" };
                let th = if is_eq(&name_th.to_string()).unwrap() { 
                    format!("{applied_th}")
                } else { 
                    format!("(prove_True_eq _ {applied_th})") 
                };
                writeln!(writer, "eapply ({rw_lemma} _ {new} _ {th} (fun hole => {holified} = _));");
            }
            writeln!(writer, "idtac).");
            writer.flush().expect("error flushing");
            println!("Wrote proof to {path}");
        }
        None => {
            // use an Extractor to pick the best element of the root eclass

                

            let explanations = runner.explain_equivalence(&expr, &best).get_flat_sexps();
            println!("Explanation length: {}", explanations.len());

            let path = get_proof_file_path();
            let f = File::create(path).expect("unable to create file");
            let mut writer = BufWriter::new(f);

            let mut explanation = explanations.iter();
            explanation.next();

            writeln!(writer, "(* SIMPLIFICATION *)");
            writeln!(writer, "unshelve (");
            for exp in explanation {
                let (holified, fw, name_th, applied_th, new) = holify(exp);
                let rw_lemma = if fw { "@rew_zoom_fw" } else { "@rew_zoom_bw" };
                let th = if is_eq(&name_th.to_string()).unwrap() { 
                    format!("{applied_th}")
                } else { 
                    format!("(prove_True_eq _ {applied_th})") 
                };
                writeln!(writer, "eapply ({rw_lemma} _ {new} _ {th} (fun hole => {holified}));");
            }
            writeln!(writer, "idtac).");
            writer.flush().expect("error flushing");
            println!("Wrote proof to {path}");

            println!("Simplified\n{}\nto\n{}\nwith cost {}", expr, best, best_cost);
        }
    }
    println!("Stop reason: {:?}", runner.stop_reason);
}

/* too hard to satisfy typechecker
fn write_explanation<W: Write>(&mut writer: &BufWriter<W>, explanations: &Vec<symbolic_expressions::Sexp>) -> () {
    let mut explanation = explanations.iter();
    explanation.next();
    writeln!(writer, "unshelve (");
    for exp in explanation {
        let (holified, fw, name_th, new) = holify(exp);
        let rw_lemma = if fw { "@rew_zoom_fw" } else { "@rew_zoom_bw" };
        writeln!(writer, "(eapply ({rw_lemma} _ {new} _  {name_th} (fun hole => {holified})) || ");
        writeln!(writer, "eapply ({rw_lemma} _ {new} _  (prove_True_eq _ {name_th}) (fun hole => {holified})));");
    }
    writeln!(writer, "idtac).");
}
*/

#[allow(dead_code)]
fn prove(s_l: &str, s_r: &str, extra_exprs: Vec<&str>) -> () {
    // parse the expression, the type annotation tells it which Language to use
    let expr_l: RecExpr<CoqSimpleLanguage> = s_l.parse().unwrap();
    // let expr_l: RecExpr<SymbolLang> = s_l.parse().unwrap();
    let expr_r: RecExpr<CoqSimpleLanguage> = s_r.parse().unwrap();
    // let expr_r: RecExpr<SymbolLang> = s_r.parse().unwrap();

    // let extra_exprs_parsed : Vec<RecExpr<SymbolLang>> = extra_exprs.iter().map(|s| s.parse::<RecExpr<SymbolLang>>().unwrap()).collect();
    // let mut extra_exprs_parsed2 : Vec<&RecExpr<SymbolLang>> = vec![];
    let extra_exprs_parsed : Vec<RecExpr<CoqSimpleLanguage>> = extra_exprs.iter().map(|s| s.parse::<RecExpr<CoqSimpleLanguage>>().unwrap()).collect();
    let mut extra_exprs_parsed2 : Vec<&RecExpr<CoqSimpleLanguage>> = vec![];
    for i in 0..extra_exprs_parsed.len() {
        extra_exprs_parsed2.push(&extra_exprs_parsed[i]);
    }

    // simplify the expression using a Runner, which creates an e-graph with
    // the given expression and runs the given rules over it
    let mut runner = Runner::default()
        .with_explanations_enabled()
        .with_expr(&expr_l)
        .with_exprs(extra_exprs_parsed2)
        .run(&make_rules());
    // the Runner knows which e-class the expression given with `with_expr` is in
    let equivs = runner.egraph.equivs(&expr_l, &expr_r);
    if equivs.is_empty() {
        println!("(NotExplained)");
    } else {
        println!("{}", runner.explain_equivalence(&expr_l, &expr_r));
    }
}
