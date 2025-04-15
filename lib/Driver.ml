open Printf

type result =
  | Ok of Typ.tp * Lir.tm
  | SyntaxError of string
  | UndefName of string
  | NeedAnnot
  | WrongType

let drive : Lexing.lexbuf -> result = fun lexbuf ->
  match lexbuf |> Parser.prog Lexer.read |> Ela.elab_infer Lir.Nil (fun _ -> None) with
  | Ela.Ok (Ela.Ev (t, lir)) ->
      Ok (t, lir)
  | Ela.UndefName n -> UndefName (Util.coq_to_ml_str n)
  | Ela.NeedAnnot -> NeedAnnot
  | Ela.WrongType -> WrongType
  | exception Lexer.LexerError n ->
      SyntaxError (sprintf "Unexpected text %s\n" n)
  | exception Parser.Error n ->
      SyntaxError (try ParserMessages.message n with Not_found -> "Unknown syntax error\n")

