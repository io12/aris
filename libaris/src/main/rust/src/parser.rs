use super::{Expr, USymbol, BSymbol, ASymbol, QSymbol};

fn custom_error<A, B>(a: A, x: u32) -> nom::IResult<A, B> {
    return Err(nom::Err::Error(nom::Context::Code(a, nom::ErrorKind::Custom(x))));
}

fn variable(s: &str) -> nom::IResult<&str, String> {
    let r = variable_(s);
    if let Ok((ref rest, ref var)) = r {
        if let Ok((_, _)) = keyword(&var) {
            return custom_error(rest, 0);
        }
    }
    r
}

named!(space<&str, ()>, do_parse!(many0!(one_of!(" \t")) >> (())));
named!(variable_<&str, String>, do_parse!(x: many1!(one_of!("abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789_")) >> ({let mut y = String::new(); for c in x { y.push(c); }; y})));
named!(keyword<&str, &str>, alt!(tag!("forall") | tag!("exists")));

named!(bottom<&str, Expr>, do_parse!(tag!("_|_") >> (Expr::Bottom)));

named!(notterm<&str, Expr>, do_parse!(tag!("~") >> e: paren_expr >> (Expr::Unop { symbol: USymbol::Not, operand: Box::new(e) })));

named!(predicate<&str, Expr>, alt!(
    do_parse!(space >> name: variable >> space >> tag!("(") >> space >> args: separated_list!(do_parse!(space >> tag!(",") >> space >> (())), variable) >> tag!(")") >> (Expr::Predicate { name, args })) |
    do_parse!(space >> name: variable >> space >> (Expr::Predicate { name, args: vec![]}))
    ));

named!(forallQuantifier<&str, QSymbol>, do_parse!(alt!(tag!("forall ") | tag!("∀")) >> (QSymbol::Forall)));
named!(existsQuantifier<&str, QSymbol>, do_parse!(alt!(tag!("exists ") | tag!("∃")) >> (QSymbol::Exists)));
named!(quantifier<&str, QSymbol>, alt!(forallQuantifier | existsQuantifier));
named!(binder<&str, Expr>, do_parse!(space >> symbol: quantifier >> space >> name: variable >> space >> tag!(",") >> space >> body: paren_expr >> (Expr::Quantifier { symbol, name, body: Box::new(body) })));

named!(binop<&str, BSymbol>, alt!(do_parse!(tag!("->") >> (BSymbol::Implies)) | do_parse!(tag!("+") >> (BSymbol::Plus)) | do_parse!(tag!("*") >> (BSymbol::Mult))));
named!(binopterm<&str, Expr>, do_parse!(left: paren_expr >> space >> symbol: binop >> space >> right: paren_expr >> (Expr::Binop { symbol, left: Box::new(left), right: Box::new(right) })));

named!(andrepr<&str, ASymbol>, do_parse!(alt!(tag!("&") | tag!("∧") | tag!("/\\")) >> (ASymbol::And)));
named!(orrepr<&str, ASymbol>, do_parse!(alt!(tag!("|") | tag!("∨") | tag!("\\/")) >> (ASymbol::Or)));
named!(biconrepr<&str, ASymbol>, do_parse!(alt!(tag!("<->") | tag!("↔")) >> (ASymbol::Bicon)));

named!(assoctermaux<&str, (Vec<Expr>, Vec<ASymbol>)>, alt!(
    do_parse!(space >> e: paren_expr >> space >> sym: alt!(andrepr | orrepr | biconrepr) >> space >> rec: assoctermaux >> ({ let (mut es, mut syms) = rec; es.push(e); syms.push(sym); (es, syms) })) |
    do_parse!(e: paren_expr >> (vec![e], vec![]))
    ));

fn assocterm(s: &str) -> nom::IResult<&str, Expr> {
    let (rest, (mut exprs, syms)) = assoctermaux(s)?;
    assert_eq!(exprs.len(), syms.len()+1);
    if exprs.len() == 1 {
        return custom_error(rest, 0);
    }
    let mut symbol = syms[0].clone();
    if !syms.iter().all(|x| x == &symbol) {
        return custom_error(rest, 0);
    }
    exprs.reverse();
    Ok((rest, Expr::AssocBinop { symbol, exprs }))
}

named!(paren_expr<&str, Expr>, alt!(bottom | predicate | notterm | binder | do_parse!(space >> tag!("(") >> space >> e: expr >> space >> tag!(")") >> space >> (e))));
named!(pub expr<&str, Expr>, alt!(assocterm | binopterm | paren_expr));
named!(pub main<&str, Expr>, do_parse!(e: expr >> tag!("\n") >> (e)));

#[test]
fn test() {
    println!("{:?}", predicate("a(   b, c)"));
    println!("{:?}", expr("a & b & c(x,y)\n"));
    println!("{:?}", expr("forall a, (b & c)\n"));
    println!("{:?}", expr("exists x, (Tet(x) & SameCol(x, b)) -> ~forall x, (Tet(x) -> LeftOf(x, b))\n"));
    named!(f<&str, Vec<&str>>, many1!(tag!("a")));
    println!("{:?}", f("aa\n"));
}
