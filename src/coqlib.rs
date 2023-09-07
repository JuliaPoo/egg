use symbolic_expressions::*;
use std::io::{Write};
use std::cmp::min;
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
pub fn find_distinct_ctor_equals<L: Language + std::fmt::Display, N: Analysis<L>>(eg: &EGraph<L, N>) -> Option<(String, String)> {
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


/// Print equality proof as a Coq script with unselve and one eapply per step
#[allow(unused_must_use)]
pub fn print_equality_proof_to_writer<W: Write>(
    is_absurd : bool,
    explanation: std::slice::Iter<symbolic_expressions::Sexp>,
    writer: &mut W,
    is_eq: &dyn Fn(&str) -> Option<bool>,
    lemma_arity: &dyn Fn(&str) -> usize
) -> () {
    writeln!(writer, "unshelve (");
    for exp in explanation {
        let (holified, fw, name_th, applied_th, new) = holify(lemma_arity, exp);
        // if name_th != "eggTypeEmbedding" {
            let rw_lemma = if fw { "@rew_zoom_fw" } else { "@rew_zoom_bw" };
            //  let th = format!("{applied_th}") ;
            let th = if is_eq(&name_th.to_string()).unwrap() { 
                format!("{applied_th}")
            } else { 
                format!("(prove_True_eq _ {applied_th})") 
            };
            if is_absurd {
                writeln!(writer, "eapply ({rw_lemma} _ {new} _ {th} (fun hole => {holified} = _));");
            }
            else {
                writeln!(writer, "eapply ({rw_lemma} _ {new} _ {th} (fun hole => {holified}));");
            }
        // }
    }
    writeln!(writer, "idtac).");
    writer.flush().expect("error flushing");
}
