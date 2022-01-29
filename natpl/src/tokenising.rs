use crate::source_cache::SourceId;
use logos::Logos;

pub type Span = (SourceId, std::ops::Range<usize>);

#[derive(Logos, Debug, Clone, PartialEq)]
pub enum Token<'input> {
    #[token("unit")]
    Unit,

    #[token("conv")]
    Conv,

    #[token(":")]
    Colon,

    #[token("⇒")]
    #[token("=>")]
    DArrowR,

    #[token("?")]
    QuestionMark,

    #[token("=")]
    OpEq,

    #[token("≠")]
    #[token("/=")]
    #[token("!=")]
    #[token("<>")]
    OpNeq,

    #[token(">")]
    OpGt,

    #[token("+")]
    OpAdd,

    #[token("-")]
    OpSub,

    #[token("*")]
    OpMul,

    #[token("/")]
    #[token("÷")]
    OpDiv,

    #[token("to")]
    OpTo,

    #[token("in")]
    OpIn,

    #[token("mod")]
    OpMod,

    #[token("^")]
    OpPow,

    #[token("[")]
    BracketOpen,

    #[token("]")]
    BracketClose,

    #[token("(")]
    ParenOpen,

    #[token(")")]
    ParenClose,

    #[token(",")]
    Comma,

    #[token("\"", parse_string_literal)]
    StringLiteral(String),

    #[regex("(\\p{XID_Start}|_|°)(\\p{XID_Continue}|'|°)*")]
    Identifier(&'input str),

    #[regex("[0-9][_0-9]*")]
    IntegerLit(&'input str),

    #[regex(r"[0-9][_0-9]*\.[0-9][_0-9]*", |lex| {
        let mut parts = lex.slice().split('.');
        let integer = parts.next()?;
        let decimal = parts.next()?;
        Some((integer, decimal))
    })]
    FloatLit((&'input str, &'input str)),

    #[regex(r"[0-9][_0-9]*\.[0-9][_0-9]*x10\^-?[0-9]+", |lex| {
        let mut s = lex.slice().split("x10^");
        let (integer, decimal) = {
            let s = s.next()?;
            let mut parts = s.split('.');
            let integer = parts.next()?;
            let decimal = parts.next()?;
            (integer, decimal)
        };
        let exp = s.next()?.parse().ok()?;
        Some((integer, decimal, exp))
    })]
    ScientificFloatLit((&'input str, &'input str, i64)),

    #[regex(r"[0-9][_0-9]*x10\^(-)?[0-9]+", |lex| {
        let mut s = lex.slice().split("x10^");
        let mantissa = s.next()?;
        let exp = s.next()?.parse().ok()?;
        Some((mantissa, exp))
    })]
    ScientificIntegerLit((&'input str, i64)),

    #[error]
    // skip whitespace
    #[regex(r"[ \t\n\f]+", logos::skip)]
    // line comments
    #[regex(r"#[^\n]*", logos::skip)]
    Error,
}

fn parse_string_literal<'src>(lex: &mut logos::Lexer<'src, Token<'src>>) -> Option<String> {
    let s = lex.remainder();

    let mut buf = String::new();

    let mut escape = false;

    for c in s.chars() {
        if escape {
            match c {
                'n' => buf.push('\n'),
                'r' => buf.push('\r'),
                '\\' => buf.push('\\'),
                '"' => buf.push('"'),
                _ => return None,
            }
            lex.bump(1);
            escape = false;
        } else {
            if c == '"' {
                lex.bump(1);
                return Some(buf);
            }

            if c == '\\' {
                escape = true;
                lex.bump(1);
                continue;
            }

            buf.push(c);
            lex.bump(c.len_utf8());
        }
    }

    None
}

pub fn tokenise(source_id: SourceId, line: &'_ str) -> Vec<(Token<'_>, Span)> {
    Token::lexer(line)
        .spanned()
        .map(|(tok, range)| (tok, (source_id, range)))
        .collect()
}
