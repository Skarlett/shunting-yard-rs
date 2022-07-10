use std::ops::Deref;

/// Lexical tokens represent a sequence of characters.
/// The sequence identity is used to determine segments
/// of the source (string) input.
///
/// Given the following example:
///    123+321 *2
///
/// The following tokens would be produced:
///    [INT] [ADD] [INT] [MULITPLY] [INT]
#[derive(Debug)]
struct Token {
  token_type: Lexer,
  start: usize,
  end: usize
}

/// The identity type for lexical tokens.
#[derive(Debug, Clone, Copy)]
enum Lexer {
  ParamOpen,
  ParamClose,
  Add,
  Minus,
  Mul,
  Pow,
  Mod,
  Div,
  Num,
}

/// Operator association.
/// When operators of equal precedence
/// occur next to each other on the operator stack.
#[derive(Debug, Eq, PartialEq, Clone, Copy)]
enum OpAssoc {
  Left,
  Right,
  NonAssoc
}

impl Lexer
{
  /// Check if this token an operator
  fn is_operator(&self) -> bool {
    match self {
      Self::Num
        | Self::ParamOpen
        | Self::ParamClose => false,
      _ => true
    }
  }

  /// Order of operations table.
  /// A table containing the order
  /// of proceedures to perform first.
  ///
  /// Returned values are processed
  /// greatest (first) to least (last).
  ///
  /// parentheses are included as 0 to negate
  /// shunting yard's operator precedence check.
  fn precendence(&self) -> u8 {
    match self {
      Self::Pow => 3,
      Self::Div => 2,
      Self::Mul => 2,
      Self::Mod => 2,
      Self::Add => 1,
      Self::Minus => 1,
      Self::ParamOpen => 0,
      _ => panic!("only operators should see their precendence")
    }
  }

  /// Operator association
  /// is whether the right of the left hand side
  /// of the operation
  /// should be performed first.
  ///
  /// Given the following example:
  ///    1 + 2 + 3
  ///
  ///   (1 + 2)+ 3   (left association)
  ///    1 +(2 + 3) (right association)
  fn assoc(&self) -> OpAssoc {
    match self {
      Self::ParamOpen | Self::ParamClose => OpAssoc::NonAssoc,
      Self::Pow => OpAssoc::Right,
      _ => OpAssoc::Left
    }
  }
}

/// Creates multi-character representation of a number.
fn tokenize_num(prev: Option<&mut Token>) -> Option<Lexer>
{
  match prev {
    None => Some(Lexer::Num),
    Some(last) => {
      // If the last token was a number,
      // and the current token, increment the last
      // token's end length to build a larger digit
      // eg "12"...
      if let Lexer::Num = last.token_type {
        last.end += 1;
        return None;
      }

      return Some(Lexer::Num);
    }
  }
}

/// Detect whether or not the current character
/// is apart of an integer
fn guard_integer(c: char) -> bool {
  return c.is_numeric() || ['.', '_'].contains(&c)
}

/// Creates a lexed stream of tokens.
fn tokenize(mut acc: Vec<Token>, i: usize, c: char) -> Vec<Token>
{
  let token = match c
  {
    ' ' | '\n' | '\t' => None,


    '-' => match acc.last() {
        None => Some(Lexer::Num),
        Some(x) => match x.token_type
        {
          // Is an operator
          Lexer::Num | Lexer::ParamClose => Some(Lexer::Minus),

          // Otherwise its apart of a number.
          _ => Some(Lexer::Num),
        }
    },

    '+' => Some(Lexer::Add),
    '*' => Some(Lexer::Mul),
    '/' => Some(Lexer::Div),
    '^' => Some(Lexer::Pow),
    '%' => Some(Lexer::Mod),

    '(' => Some(Lexer::ParamOpen),
    ')' => Some(Lexer::ParamClose),

    _ if guard_integer(c) => tokenize_num(acc.last_mut()),
    x => panic!("unknown token [{}:{}] '{}'", i, i, x)
  };

  if let Some(token_type) = token {
      acc.push(Token { token_type, start: i, end: i + 1 });
  }

  acc
}

/// Shunting yard algorithm.
/// The parameter `tokens` expects the token stream
/// to be formatted as in-fix notation ("1 + 2").
/// Output is in RPN.
fn parser<'a>(tokens: &'a [Token]) -> Vec<&'a Token>
{
    let mut output = Vec::new();
    let mut op_stack = Vec::new();

    for token in tokens {
        match token.token_type {
            // place into output queue
            Lexer::Num => output.push(token),

            // push onto the operator stack
            Lexer::ParamOpen => op_stack.push(token),

            // while the top of the operator stack
            // is not a left parenthesis,
            // pop out of the operator stack
            // and push into the output queue
            Lexer::ParamClose => {
                while let Some(last) = op_stack.last()
                {
                    if let Lexer::ParamOpen = last.token_type
                    { break }

                    output.push(op_stack.pop().unwrap());
                }

                // remove left parenthesis
                // from operator stack.
                op_stack.pop()
                  .expect("Expected an '(' to be in the operator stack");
            }

            // token as "o1" if "o1" is an operator.
            // ---
            // while there is operator ("o2") other than
            // the left parenthesis at the top of the
            // operator stack.
            //
            // pop out of the operator stack
            // and push into the output queue
            o1 if o1.is_operator() => {
                while let Some(o2) = op_stack.last()
                {
                    let operator = {
                        let o2 = o2.token_type;
                        let po1 = o1.precendence();
                        let po2 = o2.precendence();

                        if po2 > po1
                        { op_stack.pop().unwrap() }

                        else if po2 == po1 && o1.assoc() == OpAssoc::Left
                        { op_stack.pop().unwrap() }

                        else { break }
                    };

                    output.push(operator);
                }

                op_stack.push(token);
            }

            _ => unreachable!(),
        }
    }

    // pop elements from the
    // right side (tail/end)
    // of the collection into the stack
    output.extend(op_stack.drain(..).rev());
    return output;
}

/// Derive the integer value from a token also
/// ignoring underscore ('_') characters.
fn integer(data: &str, tok: &Token) -> f32 {
  data[tok.start..tok.end]
      .chars()
      .filter(|&c| c != '_')
      .collect::<String>()
      .parse::<f32>()
      .expect("Couldn't parse integer")
}

/// Evaluate RPN.
fn eval<T: Deref<Target=Token>>(data: &str, postfix: &[T]) -> f32
{
    let mut stack = Vec::new();

    for tok in postfix.iter() {
        if let Lexer::Num = tok.token_type {
            stack.push(integer(data, tok));
            continue
        }

        let rhs = stack.pop();
        let lhs = stack.pop();

        match (lhs, rhs) {
            (Some(a), Some(b)) => {
                let result = match tok.token_type {
                  Lexer::Add => a + b,
                  Lexer::Minus => a - b,
                  Lexer::Div => a / b,
                  Lexer::Mod => a % b,
                  Lexer::Mul => a * b,
                  Lexer::Pow => a.powf(b),
                  _ => unreachable!()
                };
                stack.push(result);
            },
            (None, Some(b)) => return b,
            (None, None) | (Some(_), None) => unreachable!()
        }
    }

    stack.pop()
      .expect("No integers left in collection")
}

fn main() -> Result<(), Box<dyn std::error::Error>>
{
  use std::io::{Write, stdin, stdout};
  let mut buffer = String::new();
  println!("Try: .22 * 3_000");

  loop {
    stdout().write(b"> ")?;
    stdout().flush()?;
    stdin().read_line(&mut buffer)?;

    if buffer.eq("q\n") { break }

    let tokens: Vec<Token> = buffer.chars()
      .enumerate()
      .fold(Vec::new(), |acc, (i, c)| tokenize(acc, i, c));

    let postfix = parser(&tokens);
    let result = eval(&buffer, &postfix);

    println!("{}", result);
    buffer.clear();
  }

  Ok(())
}


#[cfg(test)]
mod tests {
  use super::*;

  fn run_stage(input: &str) -> f32
  {
    let tokens: Vec<Token> = input.chars()
      .enumerate()
      .fold(Vec::new(), |acc, (i, c)| tokenize(acc, i, c));

    let postfix = parser(&tokens);
    return eval(input, &postfix);
  }

  #[test]
  fn number()
  {
    assert_eq!(run_stage("1000"), 1000.0);
    assert_eq!(run_stage("1_000"), 1000.0);
    assert_eq!(run_stage("1_000_"), 1000.0);
    assert_eq!(run_stage("_1_000_"), 1000.0);
    assert_eq!(run_stage("_1__000_"), 1000.0);
  }

  #[test]
  fn floating_point()
  {
    assert_eq!(run_stage("1.0"), 1.0);
    assert_eq!(run_stage("1._0"), 1.0);
    assert_eq!(run_stage("1.0_"), 1.0);
    assert_eq!(run_stage("1.0_"), 1.0);
    assert_eq!(run_stage("_1.0"), 1.0);
    assert_eq!(run_stage("1.__0"), 1.0);
  }

  #[test]
  fn addition()
  {
    assert_eq!(run_stage("100 + 100"), 100.0 + 100.0);
    assert_eq!(run_stage("1.50 + 1.50"), 1.5 + 1.5);
    assert_eq!(run_stage("1_000 + 1_000"), 1000.0 + 1000.0);
  }

  #[test]
  fn subtraction()
  {
    assert_eq!(run_stage("-1"), -1.0);
    assert_eq!(run_stage("-1 + -1"), -1.0 + -1.0);
    assert_eq!(run_stage("1 + ( -19 + 2 * 20)"), 1.0 + (-19.0 + 2.0 * 20.0));
  }

  #[test]
  fn multiply()
  {
    assert_eq!(run_stage("3 * 0"), 3.0 * 0.0);
    assert_eq!(run_stage("3 * 1"), 3.0 * 1.0);
    assert_eq!(run_stage("3 * 2"), 3.0 * 2.0);
    assert_eq!(run_stage("1.5 * 2"), 1.5 * 2.0);
    assert_eq!(run_stage("-1.5 * -2"), -1.5 * -2.0);
    assert_eq!(run_stage("-1.5 * 2"), -3.0);
  }

  #[test]
  fn divide()
  {
    assert_eq!(run_stage("0 / 1"), 0.0);
    assert_eq!(run_stage("1 / 1"), 1.0 / 1.0);
    assert_eq!(run_stage("1 / 2"), 1.0 / 2.0);
    assert_eq!(run_stage("10 / 2"), 10.0 / 2.0);
    assert_eq!(run_stage("-10 / -2"), 5.0);
    assert_eq!(run_stage("10 / -2"), -5.0);
    assert_eq!(run_stage("1000 / 10 / 10"), 10.0);
  }

  #[test]
  fn modolus()
  {
    assert_eq!(run_stage("2 % 1"), 2.0 % 1.0);
    assert_eq!(run_stage("5 % 2"), 5.0 % 2.0);
    assert_eq!(run_stage("-5 % 2"), -1.0);
    assert_eq!(run_stage("-5 % -2"), -1.0);
    assert_eq!(run_stage("5.5 % 2"), 5.5 % 2.0);
  }

  #[test]
  fn exponential()
  {
    assert_eq!(run_stage("2^1"), 2.0);
    assert_eq!(run_stage("2^3"), 8.0);
    assert_eq!(run_stage("2^3^2"), 512.0);
    assert_eq!(run_stage("2^3^2*2"), 1024.0);
    assert_eq!(run_stage("-1^-1"), -1.0);
    assert_eq!(run_stage("2^-1"), 0.5);
  }

  #[test]
  fn pemdas()
  {
    assert_eq!(run_stage("(1 + 3) * 4"), 16.0);
    assert_eq!(run_stage("1 + 3 * 4"), 13.0);
  }

  #[test]
  fn jasonzou0_pr1()
  {
    assert_eq!(run_stage("-19 + 20"), 1.0);
    assert_eq!(run_stage("1 + (-19 + 2 * 20)"), 22.0);
    assert_eq!(run_stage("-1 - -1"), 0.0);
  }
}
