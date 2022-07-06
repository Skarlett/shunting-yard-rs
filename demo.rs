use std::ops::Deref;

#[derive(Debug, Eq, PartialEq, Clone, Copy)]
enum OpAssoc {
  Left,
  Right,
  NonAssoc
}

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

impl Lexer {
  /// is this token an operator
  fn is_operator(&self) -> bool {
    match self {
      Self::Num
        | Self::ParamOpen
        | Self::ParamClose => false,
      _ => true
    }
  }

  /// order of operations
  fn precendence(&self) -> u8 {
    match self {
      Self::Pow => 3,
      Self::Add => 1,
      Self::Minus => 1,
      Self::Div => 2,
      Self::Mul => 2,
      Self::Mod => 2,
      Self::ParamOpen => 0,
      _ => panic!("only operators should see their precendence")
    }
  }

  /// operator assciotation
  fn assoc(&self) -> OpAssoc {
    match self {
      Self::ParamOpen
        | Self::ParamClose => OpAssoc::NonAssoc,

      Self::Pow => OpAssoc::Right,
      _ => OpAssoc::Left
    }
  }
}

#[derive(Debug)]
struct Token {
  token_type: Lexer,
  start: usize,
  end: usize
}

impl Token {
  fn new(token_type: Lexer, position: usize) -> Self {
    Self {
      token_type,
      start: position,
      end: position + 1
    }
  }
}

fn tokenize_num(acc: &mut Vec<Token>) -> Option<Lexer>
{
  let last = acc.last_mut();

  if let None = last {
    return Some(Lexer::Num)
  }
  // Not None - so unwrap.
  let last = last.unwrap();

  if let Lexer::Num = last.token_type {
    last.end += 1;
    return None;
  }

  Some(Lexer::Num)
}

fn guard_integer(c: char) -> bool
{ c.is_numeric() || ['.', '_'].contains(&c)}

/// Fold function
fn tokenize(mut acc: Vec<Token>, i: usize, c: char) -> Vec<Token>
{
  let token = match c {
    ' ' | '\n' | '\t' => None,

    // operators
    '+' => Some(Lexer::Add),
    '-' => Some(Lexer::Minus),
    '*' => Some(Lexer::Mul),
    '/' => Some(Lexer::Div),
    '^' => Some(Lexer::Pow),
    '%' => Some(Lexer::Mod),

    '(' => Some(Lexer::ParamOpen),
    ')' => Some(Lexer::ParamClose),

    _ if guard_integer(c) => tokenize_num(&mut acc),

    x => panic!("unknown token [{}:{}] '{}'", i, i, x)
  };

  if let Some(tok) = token {
    acc.push(Token::new(tok, i))
  }

  acc
}

/// Shunting yard algorithm
fn parser<'a>(tokens: &'a [Token]) -> Vec<&'a Token>
{
    let mut stack = Vec::new();
    let mut op_stack = Vec::new();

    for token in tokens {
        match token.token_type {
            Lexer::Num => stack.push(token),
            Lexer::ParamOpen => op_stack.push(token),

            Lexer::ParamClose => {
                while let Some(last) = op_stack.last() {
                    if let Lexer::ParamOpen = last.token_type
                    { break }

                    stack.push(op_stack.pop().unwrap());
                }
                op_stack.pop();
            }

            o1 if o1.is_operator() => {
                while let Some(o2) = op_stack.last() {
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

                    stack.push(operator);
                }

                op_stack.push(token);
            }

            _ => unreachable!(),
        }
    }

    // pop elements from the
    // right side (tail/end)
    // of the collection into the stack
    stack.extend(op_stack.drain(..).rev());
    return stack;
}

// slightly confusing function name,
// parses an f32 from a string.
// the string slice may include `_`
fn integer(data: &str, tok: &Token) -> f32 {
  data[tok.start..tok.end]
      .chars()
      .filter(|&c| c != '_')
      .collect::<String>()
      .parse::<f32>()
      .expect("Couldn't parse integer")
}

/// evaluate the postfix expression 
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

            (None, Some(b)) => {
		let result = if let Lexer::Minus = tok.token_type {
		    -b
		} else {
		    b
		};
		stack.push(result)
	    }
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

    if buffer.eq("q") { break }
    
    // create tokens
    let tokens: Vec<Token> = buffer.chars()
      .enumerate()
      .fold(Vec::new(), |acc, (i, c)| tokenize(acc, i, c));
    
    // convert to postfix
    let postfix = parser(&tokens);
    
    // evaluate the answer
    let result = eval(&buffer, &postfix);

    // print
    println!("{}", result);
    buffer.clear();
  }

  Ok(())
}
