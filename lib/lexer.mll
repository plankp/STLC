{
open Parser
}

let ws = [' ' '\t' '\n' '\r']+
let letter = ['a'-'z' 'A'-'Z' '_']
let trail = ['a'-'z' 'A'-'Z' '0'-'9' '_']
let id = letter trail*

rule read = parse
  | ws                  { read lexbuf }
  | "->"                { ARR }
  | "+"                 { INJ }
  | "*"                 { PAIR }
  | "bool"              { BOOL }
  | "\\"                { SLASH }
  | "."                 { DOT }
  | "("                 { LPAREN }
  | ")"                 { RPAREN }
  | "case"              { CASE }
  | "of"                { OF }
  | "|"                 { BAR }
  | "let"               { LET }
  | "="                 { SET }
  | "in"                { IN }
  | ":"                 { COLON }
  | ","                 { COMMA }
  | "fst"               { FST }
  | "snd"               { SND }
  | "inl"               { INL }
  | "inr"               { INR }
  | "true"              { TRUE }
  | "false"             { FALSE }
  | "if"                { IF }
  | "then"              { THEN }
  | "else"              { ELSE }
  | id                  { IDENT (Lexing.lexeme lexbuf) }
  | eof                 { EOF }

