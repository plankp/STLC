%{
open Ast
open Typ
open Util
%}

%token <string> IDENT
%token BOOL
%token SLASH DOT ARR
%token LPAREN RPAREN
%token CASE OF BAR
%token LET SET IN
%token COLON
%token COMMA FST SND PAIR
%token INL INR INJ
%token TRUE FALSE
%token IF THEN ELSE
%token EOF

%right ARR
%right INJ
%right PAIR

%start <Ast.ast> prog

%on_error_reduce typ
%on_error_reduce expr

%%

prog:
        | e = expr; EOF                                 { e }
        ;

typ:
        | LPAREN; RPAREN                                { TUnit }
        | LPAREN; t = typ; RPAREN                       { t }
        | BOOL                                          { TInj (TUnit, TUnit) }
        | ta = typ; ARR; tr = typ                       { TArr (ta, tr) }
        | t1 = typ; INJ; t2 = typ                       { TInj (t1, t2) }
        | t1 = typ; PAIR; t2 = typ                      { TPair (t1, t2) }
        ;

expr:
        | n = IDENT                                     { EVar (ml_to_coq_str n) }
        | TRUE                                          { EAnn (EInl EUnit, TInj (TUnit, TUnit)) }
        | FALSE                                         { EAnn (EInr EUnit, TInj (TUnit, TUnit)) }
        | LPAREN; RPAREN                                { EUnit }
        | LPAREN; e = expr; RPAREN                      { e }
        | LPAREN; e = expr; COLON; t = typ; RPAREN      { EAnn (e, t) }
        | LPAREN; e1 = expr; COMMA; e2 = expr; RPAREN   { EPair (e1, e2) }
        | SLASH; xs = lamps; DOT; e = expr              { List.fold_right (fun (x, t) e -> ELam (x, t, e)) xs e }
        | LET; n = IDENT; SET; v = expr; IN; e = expr   { ELet (ml_to_coq_str n, v, e) }
        | FST; e = expr                                 { EFst e }
        | SND; e = expr                                 { ESnd e }
        | f = expr; a = expr                            { EApp (f, a) }
        | INL; e = expr                                 { EInl e }
        | INR; e = expr                                 { EInr e }
        | CASE; e = expr; OF;
          BAR?; INL; nl = IDENT; DOT; el = expr;
          BAR; INR; nr = IDENT; DOT; er = expr          { ECase (e, ml_to_coq_str nl, el, ml_to_coq_str nr, er) }
        | IF; e = expr; THEN; el = expr;
          ELSE; er = expr                               { ECase (EAnn (e, TInj (TUnit, TUnit)), [], el, [], er) }
        ;

lamp:
        | n = IDENT                                     { (ml_to_coq_str n, None) }
        | LPAREN; n = IDENT; COLON; t = typ; RPAREN     { (ml_to_coq_str n, Some t) }
        ;

lamps:
        | x = lamp                                      { x :: [] }
        | x = lamp; xs = lamps                          { x :: xs }
        ;

