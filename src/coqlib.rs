use symbolic_expressions::*;
use std::io::{Write, Cursor};
use regex::Regex;
use std::cmp::min;
use log::*;
use crate::*;

/// Remove typer annotations and add "hole" in case of explanations
pub fn holify_aux(e: &Sexp) -> Sexp {
    match e {
        Sexp::String(s) => Sexp::String(s.replace("AT", "@").replace("DOT", ".")),
        Sexp::Empty => Sexp::Empty,
        Sexp::List(l) => {
            if l[0] == Sexp::String("Rewrite=>".to_string()) {
                Sexp::String("hole".to_string())
            } else if l[0] == Sexp::String("Rewrite<=".to_string()) {
                Sexp::String("hole".to_string())
            } else if l[0] == Sexp::String("annot".to_string()) {
                holify_aux(&l[1])
            } else {
                Sexp::List(l.iter().map(holify_aux).collect())
            }
        }
    }
}


fn add_arity_th_name(lemma_arity: &dyn Fn(&str) -> usize, e: &Sexp) -> Sexp {
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
                    let mut arg_implicit_aux = ["_"].repeat(number);
                    if s == "eggTypeEmbedding" {
                        arg_implicit_aux.clear();
                        arg_implicit_aux = vec!["_", "_", "_", "O", "O", "_"];
                    }
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

const SPECIAL_RULES: [&str; 4] = [
    "%Q_cast_plus%",
    "%Q_cast_mult%",
    "%Q_cast_minus%",
    "%constant_fold%",
];

fn find_rw(lemma_arity: &dyn Fn(&str) -> usize, e: &Sexp) -> Option<(bool, String, Sexp, Sexp)> {
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
                                if SPECIAL_RULES.contains(&s.as_str()) {
                                    // (holified, fw, name_th, applied_th, new)
                                    return Some((fw1, s.to_string(), Sexp::Empty, l[2].clone()))
                                }
                                let fw2 = !s.contains("-rev");
                                let fw = fw1 ^ fw2;
                                return Some((fw, s.to_string(), add_arity_th_name(lemma_arity, &l[1]), l[2].clone()))
                            }
                            _ => { panic!("Expected rule name after Rewrite") }
                        }
                    }
                }
                _ => ()
            }
            // only executed if we have not yet returned:
            for i in l.iter() {
                match find_rw(lemma_arity, i) {
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

fn holify(lemma_arity: &dyn Fn(&str) -> usize, e: &Sexp) -> (Sexp, bool, String, Sexp, Sexp) {
    match find_rw(lemma_arity, e) {
        None => {
            panic!("There is no rewrite in the sexp")
        }
        Some((fw, name_th, applied_th, new)) => {
            return (holify_aux(e), fw, name_th, applied_th, holify_aux(&new));
        }
    }
}

///  Return two terms that start with distinct constructors but are in the same eclass
pub fn find_distinct_ctor_equals<L: Language + std::fmt::Display, T: FfnLattice, N: Analysis<L,T>>(eg: &EGraph<L, T, N>) -> Option<(String, String)> {
    let extractor = Extractor::new(eg, AstSize,[].to_vec());
    let classes : Vec<&EClass<L, _>> = eg.classes().collect();
    for class in classes {
        let mut last_ctor_seen : Option<(String, String, String)> = None;
        for node in class.nodes.iter() {
            // The display() method implemented by define_language! macro happens to print only the op name
            // TODO is there a cleaner way to obtain the op name?
            let opname_annote = format!("{}", node);
            if opname_annote == "annot" {
                let ctor_eclass_id  = node.children()[0];
                let ctor_type_eclass_id  = node.children()[1];
                let (_best_cost, ntype) = extractor.find_best(ctor_type_eclass_id);
                let class_ctor = &eg[ctor_eclass_id];
                for node in class_ctor.nodes.iter() {
                    let opname =  format!("{}", node);

                    let is_nonprop_ctor = opname.starts_with("!");
                    if is_nonprop_ctor {
                        match last_ctor_seen.clone() {
                            Some((ctor1, children1, type1)) => { 
                                if !(ctor1 == opname) 
                                    {
                                        let mut s: String; 
                                        s = "".to_string();
                                        // Find representant for our children of ctor2
                                        for child in node.children().iter() {
                                            let (_best_cost, best) = extractor.find_best(*child);
                                            s.push_str (&format!(" {}", best))
                                        }
                                        // TODO fix now that we have ffn internalized
                                        return Some((format!("(annot ({} {}) {})", ctor1, children1, type1), format!("(annot ({} {}) {})", opname, s, ntype)))}
                                }
                            None => { 
                                    let mut s: String; 
                                    s = "".to_string();
                                    // Find representant for our children of ctor2
                                    for child in node.children().iter() {
                                        let (_best_cost, best) = extractor.find_best(*child);
                                        s.push_str (&format!(" {}", best))
                                    }
                                    let stype = format!("{}", ntype);
                                    last_ctor_seen = Some((opname, s, stype)); }
                        }
                    }
                }
                    
            }
        }
    }
    return None;
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

impl CostFunction<SymbolLang> for MotivateTrue<'_> {
    type Cost = (Vec<i64>, f64);
    fn cost<C>(&mut self, enode: &SymbolLang, mut costs: C) -> Self::Cost
    where
        C: FnMut(Id) -> Self::Cost
    {
        
        let op_cost = 
            match &enode {
            SymbolLang::Num(_) => { &0.0 }
            SymbolLang::Symb(op,_children) => { self.motivated.get(&op.to_string()).unwrap_or(&4.0) }
            };
        let cost_post_mandate = enode.fold(*op_cost, |sum, id| 
                    sum + costs(id).1);
        let repeat1 = vec![1; self.number_appear];
        let cost_vector = enode.fold(repeat1, |sum, id| 
                    pmin(sum, costs(id).0));
        return (cost_vector, cost_post_mandate);

    }
}

fn simpl(sexp: &Sexp) -> Sexp {
    match sexp {
        Sexp::List(list) => {
            match &list[0] {
                Sexp::String(op) => {
                    if !"*+-".chars().any(|c| *op == c.to_string()) {
                        return Sexp::List(list.into_iter().map(|e| simpl(e)).collect());
                    }
                    let s = eval(sexp).unwrap();
                    let res = format!("{s}");
                    return Sexp::String(res);
                }
                _ => sexp.clone()
            }
        }
        _ => sexp.clone()
    }
}

fn eval(sexp: &Sexp) -> Result<i64, String> {
    match sexp {
        Sexp::String(s) => Ok(s.parse::<i64>().expect(&format!("{} not a valid i64", s))),
        Sexp::Empty => Err("Empty Sexpr".to_string()),
        Sexp::List(list) => {
            if list.len() != 3 {
                return Err(format!("Expected 3 elements (operator and 2 operands), got {}", list.len()));
            }
            let op = &list[0];
            let a = eval(&list[1])?;
            let b = eval(&list[2])?;

            match op {
                Sexp::String(op_str) => match op_str.as_str() {
                    "+" => Ok(a + b),
                    "-" => Ok(a - b),
                    "*" => Ok(a * b),
                    _ => Err(format!("Unknown operator: {}", op_str)),
                },
                _ => Err("Operator must be a symbol".to_string()),
            }
        }
    }
}

/// Print equality proof as a Coq script with unselve and one eapply per step
#[allow(unused_must_use)]
pub fn print_equality_proof_to_writer<W: Write>(
    is_absurd : bool,
    explanation: std::slice::Iter<symbolic_expressions::Sexp>,
    writer: &mut W,
    is_eq: &dyn Fn(&str) -> Option<bool>,
    lemma_arity: &dyn Fn(&str) -> usize
) -> () {
    let mut buffer = Cursor::new(Vec::new());
    let mut prefix = Cursor::new(Vec::new());
    let re = Regex::new(r" (?P<num>[+-]?\d+) ").unwrap();
    let sanitize = |s: String| {re.replace_all(s.as_str(), " (${num}) ").to_string()};
    writeln!(prefix, "unshelve (");
    for exp in explanation {
        info!("Writing explanation line: {}", exp);
        let (holified, fw, name_th, applied_th, new) = holify(lemma_arity, exp);
        if SPECIAL_RULES.contains(&name_th.as_str()) {
            // if name_th == "%constant_fold%" { continue; }
            // if ["%Q_cast_plus%", "%Q_cast_mult%", "%Q_cast_minus%"].contains(&name_th.as_str()) {
            if name_th == "%constant_fold%" {
                // let folded_expr = new.list().unwrap().get(1).unwrap().list().unwrap();
                // let a = folded_expr.get(1).unwrap().i().unwrap();
                // let b = folded_expr.get(2).unwrap().i().unwrap();
                // let res = a + b;
                // // writeln!(prefix, "assert (special_rule_{special_rule_id} : @eq Q (Qplus (Qmake {a} xH) (Qmake {b} xH)) (Qmake {res} xH)) by reflexivity.");
                // writeln!(prefix, "assert (@eq Q (Qplus (Qmake {a} xH) (Qmake {b} xH)) (Qmake {res} xH)) by reflexivity.");
                // // writeln!(buffer, "eapply (@rew_zoom_fw _ (Qmake {res} xH) _ special_rule_{special_rule_id} (fun hole => {holified}));");
                // writeln!(buffer, "eapply (@rew_zoom_fw _ (Qmake {res} xH) _ _ (fun hole => {holified}));");
                
                // special_rule_id += 1;

                if "*+-".chars().any(|c| holified.to_string().contains(c)) { continue; }
                info!("NEW: {}", new.to_string());

                if !fw {
                    // Constant folding backwards!
                    let new_list = new.list().unwrap();
                    let op = new_list[0].to_string();
                    let a = new_list[1].to_string();
                    let b = new_list[2].to_string();
                    let qop_res = match op.as_str() {
                        "+" => Ok("Qplus"),
                        "-" => Ok("Qminus"),
                        "*" => Ok("Qmult"),
                        _ => Err(format!("Unsupported literal {op}"))
                    };
                    let qop = qop_res.unwrap();
                    let new_str = format!("({qop} (Qmake {a} xH) (Qmake {b} xH))");
                    let holified_str = holified.to_string().replace("(!Qmake hole !xH)", "hole");

                    let res = eval(&new).unwrap();
                    let sanitized1 = sanitize(format!("assert {new}<-{res} by reflexivity."));
                    writeln!(prefix, "{sanitized1}");
                    let sanitized = sanitize(format!("eapply (@rew_zoom_fw _ {new_str} _ _ (fun hole => {holified_str}));"));
                    writeln!(buffer, "{sanitized}");
                    continue;
                }

                // if !new.is_list() {continue;}
                let res = eval(&new).unwrap();

                let sanitized1 = sanitize(format!("assert {new}={res} by reflexivity."));
                writeln!(prefix, "{sanitized1}");
                let sanitized2 = sanitize(format!("eapply (@rew_zoom_fw _ ({res})%Z _ _ (fun hole => {holified}));"));
                writeln!(buffer, "{sanitized2}");
            
            }
            continue;
        }
        // println!("Writing {name_th}");
        let sanitised_holified = simpl(&holified);
        let ref1 = String::from("eggTypeEmbedding");
        let ref2 = String::from("eggTypeEmbedding2");
        if name_th == ref1 || name_th == ref2 { continue; }
        let rw_lemma = if fw { "@rew_zoom_fw" } else { "@rew_zoom_bw" };
        //  let th = format!("{applied_th}") ;
        let th = if is_eq(&name_th.to_string()).unwrap() { 
            format!("{applied_th}")
        } else { 
            format!("(prove_True_eq _ {applied_th})") 
        };
        if is_absurd {
            let sanitized = sanitize(format!("eapply ({rw_lemma} _ {new} _ {th} (fun hole => {sanitised_holified} = _));"));
            writeln!(buffer, "{sanitized}");
        }
        else {
            let sanitized = sanitize(format!("eapply ({rw_lemma} _ {new} _ {th} (fun hole => {sanitised_holified}));"));
            writeln!(buffer, "{sanitized}");
        }
        
    }
    writeln!(buffer, "idtac).");
    
    writer.write_all(&prefix.into_inner());
    writer.write_all(&buffer.into_inner());
    writer.flush().expect("error flushing");
}
