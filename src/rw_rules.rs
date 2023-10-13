
#![allow(missing_docs,non_camel_case_types)]
use crate ::*;

pub fn get_proof_file_path() -> &'static str {
  "/tmp/egg_proof.txt"
}

define_language! {
  pub enum CoqSimpleLanguage {
    "&Z.div" = IDZDOTdiv([Id; 2]),
    "&wopp" = IDwopp([Id; 1]),
    "&Z.mul" = IDZDOTmul([Id; 2]),
    "&@eq" = IDATeq([Id; 3]),
    "&Z.modulo" = IDZDOTmodulo([Id; 2]),
    "&wsru" = IDwsru([Id; 2]),
    "&@length" = IDATlength([Id; 2]),
    "&Z.of_nat" = IDZDOTof_nat([Id; 1]),
    "&wadd" = IDwadd([Id; 2]),
    "&word" = IDword([Id; 0]),
    "!32" = BANG32([Id; 0]),
    "&Z.le" = IDZDOTle([Id; 2]),
    "&and" = IDand([Id; 2]),
    "&wsub" = IDwsub([Id; 2]),
    "!3" = BANG3([Id; 0]),
    "&x" = IDx([Id; 0]),
    "&x1" = IDx1([Id; 0]),
    "&Z.pow" = IDZDOTpow([Id; 2]),
    "&x2" = IDx2([Id; 0]),
    "!0" = BANG0([Id; 0]),
    "&ZToWord" = IDZToWord([Id; 1]),
    "!4" = BANG4([Id; 0]),
    "!8" = BANG8([Id; 0]),
    "&False" = IDFalse([Id; 0]),
    "&not" = IDnot([Id; 1]),
    "&Z.lt" = IDZDOTlt([Id; 2]),
    "&Z" = IDZ([Id; 0]),
    "&wslu" = IDwslu([Id; 2]),
    "!2" = BANG2([Id; 0]),
    "&unsigned" = IDunsigned([Id; 1]),
    "&True" = IDTrue([Id; 0]),
  }
}

pub fn symbol_metadata(name : &str) -> Option<(usize,bool)> {
  let v = vec![
    ("&Z.div", (2,false)),
    ("&wopp", (1,false)),
    ("&Z.mul", (2,false)),
    ("&@eq", (3,false)),
    ("&Z.modulo", (2,false)),
    ("&wsru", (2,false)),
    ("&@length", (2,false)),
    ("&Z.of_nat", (1,false)),
    ("&wadd", (2,false)),
    ("&word", (0,false)),
    ("!32", (0,true)),
    ("&Z.le", (2,false)),
    ("&and", (2,false)),
    ("&wsub", (2,false)),
    ("!3", (0,true)),
    ("&x", (0,false)),
    ("&x1", (0,false)),
    ("&Z.pow", (2,false)),
    ("&x2", (0,false)),
    ("!0", (0,true)),
    ("&ZToWord", (1,false)),
    ("!4", (0,true)),
    ("!8", (0,true)),
    ("&False", (0,false)),
    ("&not", (1,false)),
    ("&Z.lt", (2,false)),
    ("&Z", (0,false)),
    ("&wslu", (2,false)),
    ("!2", (0,true)),
    ("&unsigned", (1,false)),
    ("&True", (0,false)),
  ];
  let o = v.iter().find(|t| t.0 == name);
  match o {
    Some((_, n)) => { return Some(*n); }
    None => { return None; }
  }
}

pub fn make_rules() -> Vec<Rewrite<CoqSimpleLanguage, i32, ()>> {
  let v  : Vec<Rewrite<CoqSimpleLanguage, i32,()>> = vec![
    rewrite!("wadd_0_l"; "(&wadd(&ZToWord !0)?a)" => "?a"),
    rewrite!("wadd_0_r"; "(&wadd ?a(&ZToWord !0))" => "?a"),
    rewrite!("wadd_comm"; "(&wadd ?a ?b)" => "(&wadd ?b ?a)"),
    rewrite!("wadd_to_left_assoc"; "(&wadd ?a(&wadd ?b ?c))" => "(&wadd(&wadd ?a ?b)?c)"),
    rewrite!("wadd_to_right_assoc"; "(&wadd(&wadd ?a ?b)?c)" => "(&wadd ?a(&wadd ?b ?c))"),
    rewrite!("wadd_opp"; "(&wadd ?a(&wopp ?a))" => "(&ZToWord !0)"),
    rewrite!("wsub_def"; "(&wsub ?a ?b)" => "(&wadd ?a(&wopp ?b))"),
    coq_rewrite!("unsigned_of_Z"; "?$hyp0 = &True = (&and(&Z.le !0 ?a)(&Z.lt ?a(&Z.pow !2 !32))), ?$lhs = (&unsigned(&ZToWord ?a))" => "?a"),
    coq_rewrite!("unsigned_nonneg"; "?$trigger0 = (&unsigned ?x), ?$lhs = &True" => "(&Z.le !0(&unsigned ?x))"),
    coq_rewrite!("unsigned_sru_to_div_pow2"; "?$hyp0 = &True = (&and(&Z.le !0 ?a)(&Z.lt ?a !32)), ?$lhs = (&unsigned(&wsru ?x(&ZToWord ?a)))" => "(&Z.div(&unsigned ?x)(&Z.pow !2 ?a))"),
    coq_rewrite!("unsigned_slu_to_mul_pow2"; "?$hyp0 = &True = (&and(&Z.le !0 ?a)(&Z.lt ?a !32)), ?$lhs = (&unsigned(&wslu ?x(&ZToWord ?a)))" => "(&Z.modulo(&Z.mul(&unsigned ?x)(&Z.pow !2 ?a))(&Z.pow !2 !32))"),
    rewrite!("H"; "(&unsigned(&wsub &x2 &x1))" => "(&Z.mul !8(&Z.of_nat(&@length &word &x)))"),
    rewrite!("H0"; "&True" => "(&not(&@eq &Z(&unsigned(&wsub &x2 &x1))!0))"),
    rewrite!("C1"; "&True" => "(&and(&Z.le !0 !8)(&Z.lt !8(&Z.pow !2 !32)))"),
    rewrite!("C2"; "&True" => "(&and(&Z.le !0 !3)(&Z.lt !3 !32))"),
    rewrite!("C3"; "&True" => "(&and(&Z.le !0 !4)(&Z.lt !4 !32))"),
    rewrite!("C4"; "&True" => "(&Z.le !0(&Z.pow !2 !3))"),
    rewrite!("C5"; "&True" => "(&Z.lt !0(&Z.pow !2 !4))"),
    rewrite!("C6"; "&True" => "(&Z.lt !0(&Z.pow !2 !32))"),
    rewrite!("C7"; "&True" => "(&Z.lt !0(&Z.pow !2 !3))"),
    rewrite!("C8"; "&True" => "(&Z.lt(&Z.pow !2 !3)(&Z.pow !2 !4))"),
    coq_rewrite!("Z_forget_mod_in_lt_l"; "?$hyp0 = &True = (&Z.le !0 ?a), ?$hyp1 = &True = (&Z.lt !0 ?m), ?$hyp2 = &True = (&Z.lt ?a ?b), ?$lhs = &True" => "(&Z.lt(&Z.modulo ?a ?m)?b)"),
    coq_rewrite!("Z_mul_nonneg"; "?$hyp0 = &True = (&Z.le !0 ?e1), ?$hyp1 = &True = (&Z.le !0 ?e2), ?$trigger0 = (&Z.mul ?e1 ?e2), ?$lhs = &True" => "(&Z.le !0(&Z.mul ?e1 ?e2))"),
    coq_rewrite!("Z_div_nonneg"; "?$hyp0 = &True = (&Z.le !0 ?a), ?$hyp1 = &True = (&Z.lt !0 ?b), ?$trigger0 = (&Z.div ?a ?b), ?$lhs = &True" => "(&Z.le !0(&Z.div ?a ?b))"),
    coq_rewrite!("Z_div_mul_lt"; "?$hyp0 = &True = (&Z.lt !0 ?x), ?$hyp1 = &True = (&Z.lt !0 ?d1), ?$hyp2 = &True = (&Z.lt ?d1 ?d2), ?$lhs = &True" => "(&Z.lt(&Z.mul(&Z.div ?x ?d2)?d1)?x)"),
    coq_rewrite!("Z_lt_from_le_and_neq"; "?$hyp0 = &True = (&Z.le ?x ?y), ?$hyp1 = &True = (&not(&@eq &Z ?x ?y)), ?$lhs = &True" => "(&Z.lt ?x ?y)"),
    rewrite!("H_eq_eq_sym"; "(&@eq ?A ?x ?y)" => "(&@eq ?A ?y ?x)"),
  ];
  v
}

pub fn get_lemma_arity(name: &str) -> Option<usize> {
  let v = vec![
    ("wadd_0_l", 1),
    ("wadd_0_r", 1),
    ("wadd_comm", 2),
    ("wadd_to_left_assoc", 3),
    ("wadd_to_right_assoc", 3),
    ("wadd_opp", 1),
    ("wsub_def", 2),
    ("unsigned_of_Z", 2),
    ("unsigned_nonneg", 1),
    ("unsigned_sru_to_div_pow2", 3),
    ("unsigned_slu_to_mul_pow2", 3),
    ("H", 0),
    ("H0", 0),
    ("C1", 0),
    ("C2", 0),
    ("C3", 0),
    ("C4", 0),
    ("C5", 0),
    ("C6", 0),
    ("C7", 0),
    ("C8", 0),
    ("Z_forget_mod_in_lt_l", 6),
    ("Z_mul_nonneg", 4),
    ("Z_div_nonneg", 4),
    ("Z_div_mul_lt", 6),
    ("Z_lt_from_le_and_neq", 4),
    ("H_eq_eq_sym", 3),
  ];
  let o = v.iter().find(|t| t.0 == name);
  match o {
    Some((_, n)) => { return Some(*n); }
    None => { return None; }
  }
}

pub fn is_eq(name: &str) -> Option<bool> {
  let v = vec![
    ("wadd_0_l", true),
    ("wadd_0_r", true),
    ("wadd_comm", true),
    ("wadd_to_left_assoc", true),
    ("wadd_to_right_assoc", true),
    ("wadd_opp", true),
    ("wsub_def", true),
    ("unsigned_of_Z", true),
    ("unsigned_nonneg", false),
    ("unsigned_sru_to_div_pow2", true),
    ("unsigned_slu_to_mul_pow2", true),
    ("H", true),
    ("H0", false),
    ("C1", false),
    ("C2", false),
    ("C3", false),
    ("C4", false),
    ("C5", false),
    ("C6", false),
    ("C7", false),
    ("C8", false),
    ("Z_forget_mod_in_lt_l", false),
    ("Z_mul_nonneg", false),
    ("Z_div_nonneg", false),
    ("Z_div_mul_lt", false),
    ("Z_lt_from_le_and_neq", false),
    ("H_eq_eq_sym", true),
  ];
  let o = v.iter().find(|t| t.0 == name);
  match o {
    Some((_, n)) => { return Some(*n); }
    None => { return None; }
  }
}

#[allow(unused_variables)]
pub fn run_simplifier(f_simplify : fn(&str, Vec<&str>) -> (), f_prove : fn(&str, &str, Vec<&str>) -> ()) {
  let es = vec![
    "(&ZToWord !0)",
    "(&Z.lt !0(&Z.pow !2 !4))",
    "(&not(&@eq &Z(&unsigned(&wsub &x2 &x1))!0))",
    "(&Z.mul !8(&Z.of_nat(&@length &word &x)))",
    "(&Z.lt !0(&Z.pow !2 !3))",
    "(&unsigned(&wsub &x2 &x1))",
    "(&Z.lt !0(&Z.pow !2 !32))",
    "(&and(&Z.le !0 !8)(&Z.lt !8(&Z.pow !2 !32)))",
    "&True",
    "(&and(&Z.le !0 !4)(&Z.lt !4 !32))",
    "(&Z.le !0(&Z.pow !2 !3))",
    "(&and(&Z.le !0 !3)(&Z.lt !3 !32))",
    "(&Z.lt(&Z.pow !2 !3)(&Z.pow !2 !4))",
  ];
  let st : &str = "(&Z.le !0(&Z.mul(&Z.div(&unsigned(&wsub &x2 &x1))(&Z.pow !2 !4))(&Z.pow !2 !3)))";
  f_simplify(st, es);
}
