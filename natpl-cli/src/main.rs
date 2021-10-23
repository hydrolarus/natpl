use natpl_repl::ReadEvalResult;
use owo_colors::OwoColorize;
use rustyline::error::ReadlineError;
use thiserror::Error;

use natpl::{
    parsing,
    runtime::{self, CallStack, EvalResult, Runtime},
    syntax::HasFC,
    tokenising,
};

#[derive(Debug, Error)]
pub enum LoadFileError {
    #[error("Runtime error: {}", .0)]
    RuntimeError(#[from] runtime::ItemError),
    #[error("Parse error {}", .0)]
    ParseError(String),
}

/// Load a file into the runtime line-by line.
///
/// If `print` is true then printed-expressions are printed to stdout.
pub fn load_file(rt: &mut Runtime, content: &str, print: bool) -> Result<(), LoadFileError> {
    for (line, source) in content.lines().enumerate() {
        let toks = tokenising::tokenise(source);
        let item = match parsing::Parser::parse_line(&toks) {
            Ok(item) => item,
            Err(err) => {
                let msg = format!("on line {}: {}", line, err);
                return Err(LoadFileError::ParseError(msg));
            }
        };

        match rt.eval_line_item(item, &mut CallStack::default())? {
            EvalResult::Empty => {}
            EvalResult::Value(_) => {}
            EvalResult::PrintValue(expr, val) => {
                if print {
                    let range = expr.fc();
                    let input_slice = &source[range.start..range.end];

                    println!(
                        "{} => {:<20} [{}]",
                        input_slice,
                        val.kind.to_string(),
                        val.unit
                    );
                }
            }
            EvalResult::VariableSearchResult { .. } => {}
            EvalResult::UnitSearchResult { .. } => {}
        }
    }
    Ok(())
}

const EXPR_PAD: usize = 12;

pub fn repl(rt: &mut Runtime) -> Result<(), Box<dyn std::error::Error>> {
    let mut rl = rustyline::Editor::<()>::new();

    let prompt = format!("{} ", ">>>".blue());

    loop {
        let readline = rl.readline(&prompt);
        match readline {
            Ok(line) => {
                if line.is_empty() {
                    continue;
                }

                rl.add_history_entry(&line);

                single_expr(rt, &line)?;
            }
            Err(ReadlineError::Interrupted) => break,
            Err(ReadlineError::Eof) => break,
            Err(err) => {
                eprintln!("Error: {}", err);
                break;
            }
        }
    }

    Ok(())
}

#[derive(Clone, Copy)]
enum Marker {
    Success,
    Continuation,
}

fn print_response_line(
    marker: Marker,
    // Name to print along with its width
    name: Option<(&str, usize)>,
    value: impl ToString,
    unit_name: &str,
    expr_pad: usize,
) {
    let marker = match marker {
        Marker::Success => "✔".green().to_string(),
        Marker::Continuation => "⇒".bright_black().to_string(),
    };

    let name_part =
        name.map(|(name, width)| format!("{:width$} {} ", name, "=".bright_black(), width = width));
    let line = format!(
        "{}{:expr_pad$} {}{}{}",
        name_part.unwrap_or_else(String::new),
        value.to_string(),
        "[".bright_black(),
        unit_name.bright_blue(),
        "]".bright_black(),
        expr_pad = expr_pad
    );
    println!("{} {}", marker, line)
}

fn single_expr(rt: &mut Runtime, input: &str) -> Result<(), Box<dyn std::error::Error>> {
    match natpl_repl::read_eval(rt, input) {
        ReadEvalResult::ParseError(err) => {
            eprintln!("{} Parse error: {}", "✘".red(), err);
        }
        ReadEvalResult::ItemError(err) => {
            eprintln!("{} {}", "✘".red(), err);
        }
        ReadEvalResult::Empty => {}
        ReadEvalResult::SilentValue {
            value: _,
            display_candidates,
        } => {
            for (i, (unit, val)) in display_candidates.iter().take(3).enumerate() {
                let marker = if i == 0 {
                    Marker::Success
                } else {
                    Marker::Continuation
                };

                print_response_line(marker, None, &val.to_string(), unit, 12);
            }
        }
        ReadEvalResult::PrintValue {
            expr,
            value: _,
            display_candidates,
        } => {
            let range = expr.fc();
            let input_slice = &input[range.start..range.end];

            let value_part = format!("{} => {}", input_slice, display_candidates[0].1);
            print_response_line(
                Marker::Success,
                None,
                value_part,
                &display_candidates[0].0,
                EXPR_PAD,
            );
        }
        ReadEvalResult::VariableSearchResult {
            unit_aliases: _,
            variables,
            functions: _,
        } => {
            let longest_name = variables.keys().max_by(|a, b| a.len().cmp(&b.len()));
            let name_length = longest_name.map(|s| s.len()).unwrap_or(0);

            for (i, (name, display_candidates)) in variables.into_iter().enumerate() {
                let marker = if i == 0 {
                    Marker::Success
                } else {
                    Marker::Continuation
                };

                let (unit_name, val_kind) = display_candidates[0].clone();

                print_response_line(
                    marker,
                    Some((&name, name_length)),
                    val_kind.to_string(),
                    &unit_name,
                    EXPR_PAD,
                );
            }
        }
        ReadEvalResult::UnitSearchResult {
            unit: _,
            unit_aliases: _,
            variables,
        } => {
            let longest_name = variables.keys().max_by(|a, b| a.len().cmp(&b.len()));
            let name_length = longest_name.map(|s| s.len()).unwrap_or(0);

            for (i, (name, display_candidates)) in variables.into_iter().enumerate() {
                let marker = if i == 0 {
                    Marker::Success
                } else {
                    Marker::Continuation
                };

                let (unit_name, val_kind) = display_candidates[0].clone();
                print_response_line(
                    marker,
                    Some((&name, name_length)),
                    val_kind.to_string(),
                    &unit_name,
                    EXPR_PAD,
                );
            }
        }
    }
    Ok(())
}

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let args = std::env::args().skip(1).collect::<Vec<_>>();

    let mut rt = Runtime::new();

    load_file(&mut rt, include_str!("../../lib/prelude.nat"), false)?;

    if let Some(file_path) = args.first() {
        let path = std::path::Path::new(file_path);

        if path.exists() {
            let content = std::fs::read_to_string(path)?;
            load_file(&mut rt, &content, true)?;
        } else if file_path.ends_with(".nat") {
            println!("File '{}' does not exist", path.display());
        } else {
            let expr = args.join(" ");
            single_expr(&mut rt, &expr)?;
            return Ok(());
        }
    }

    repl(&mut rt)
}
