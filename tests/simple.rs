use egg::*;

define_language! {
    enum SimpleLanguage {
        Num(i32),
        // "+" = Add([Id; 2]),
        // "*" = Mul([Id; 2]),
        "le" = Le([Id; 2]),
        "cast" = Cast([Id; 2]),
        "Some" = Some([Id; 1]),
        "abs" = Abs([Id;1]),
        "id" = Id([Id;1]),
        Symbol(Symbol),
    }
}

fn make_rules() -> Vec<Rewrite<SimpleLanguage, ()>> {
    vec![
        // rewrite!("commute-add"; "(+ ?a ?b)" => "(+ ?b ?a)"),
        // rewrite!("commute-mul"; "(* ?a ?b)" => "(* ?b ?a)"),
        // rewrite!("add-0"; "(+ ?a 0)" => "?a"),
        // rewrite!("mul-0"; "(* ?a 0)" => "0"),
        // rewrite!("mul-1"; "(* ?a 1)" => "?a"),
        // rewrite!("lol-true"; "?a" => "True"),
        rewrite!("le5-true"; "(le 0 5)" => "True"),
        rewrite!("le7-true"; "(le 5 7)" => "True"),
        rewrite!("Somexy"; "(Some x)" => "(Some 7)"),
        rewrite!("id-cast"; "?a" => "(cast ?a ?a)"),
        rewrite!("cast-proj"; "(cast ?a ?a)" => "?a"),
        // rewrite!("id-app-rev"; "(id ?a)" => "?a"),
        // coq_rewrite!("inj-tran"; 
        //              "?s1 = (eq (Some ?a) (Some ?b)) = True, ?foo = (eq ?a ?b)" 
        //               =>
        //               "True"),
        // coq_rewrite!("cong-cast"; 
        //              " ?posx = ?a = ?b, ?foo = (cast ?a ?b)"
        //               =>
        //              "?b"),
        coq_rewrite!("inj-some"; 
                     " ?chenil1 = (Some ?a) = (Some ?b), ?chenil2 = ?a"
                      =>
                     "?b"),
        // coq_rewrite!("le-tran"; 
        //              " ?s1 = (le ?a ?b) = True = (le ?b ?c), ?foo = (le ?a ?c)" 
        //               =>
        //               "True"),
        coq_rewrite!("le-tran"; 
                     " ?s1 = (le ?a ?b) = True = (le ?b ?c), ?foo = True" 
                      =>
                      "(le ?a ?c)"),

        // coq_rewrite!("commute-add"; "(+ ?a ?b)" => "(+ ?b ?a)"),
        coq_rewrite!("remove-abs"; 
                     " ?posx = (le 0 ?yoo) = True, ?foo = (abs ?yoo)" 
                      =>
                      "?yoo"),
        // coq_rewrite!("abs-rev"; 
        //              "?foo = (id ?yoo), ?posx = (le 0 ?yoo) = True" 
        //               =>
        //               "(abs ?yoo)")
    ]
}


/// parse an expression, simplify it using egg, and pretty print it back out
fn simplify(s: &str) -> String {
    // parse the expression, the type annotation tells it which Language to use
    let expr: RecExpr<SimpleLanguage> = s.parse().unwrap();
    let le5: RecExpr<SimpleLanguage> = "(le 0 5)".parse().unwrap();
    let le57: RecExpr<SimpleLanguage> = "(le 5 7)".parse().unwrap();
    // let le07: RecExpr<SimpleLanguage> = "(le 0 7)".parse().unwrap();
    let sx: RecExpr<SimpleLanguage> = "(Some x)".parse().unwrap();
    // let sy: RecExpr<SimpleLanguage> = "(Some y)".parse().unwrap();
    let castx7: RecExpr<SimpleLanguage> = "(cast x 7)".parse().unwrap();

    // simplify the expression using a Runner, which creates an e-graph with
    // the given expression and runs the given rules over it
    let mut runner = Runner::default().with_explanations_enabled().with_expr(&expr).with_expr(&le5).with_expr(&le57).with_expr(&sx).with_expr(&castx7).run(&make_rules());
    // let runner = Runner::default().with_expr(&expr).with_expr(&le5).run(&make_rules());


    // the Runner knows which e-class the expression given with `with_expr` is in
    let root = runner.roots[0];

    // use an Extractor to pick the best element of the root eclass
    let extractor = Extractor::new(&runner.egraph, AstSize, vec![]);
    let (best_cost, best) = extractor.find_best(root);

    let explanations = runner.explain_equivalence(&expr, &best).get_flat_string();
    println!("Simplified {} to {} with cost {}", expr, best, best_cost);
    println!("Explanation {} ", explanations);
    best.to_string()
}


#[test]
fn simple_tests() {
    // simplify("(cast x 7)");
    // simplify("(abs (cast x 7))");
    simplify("(abs  x)");
    // assert_eq!();
    // assert_eq!(simplify("(abs 7)"), "7");
    // assert_eq!(simplify("x"), "y");
    // assert_eq!(simplify("(+ 0 (* 1 foo))"), "foo");
}
