From Coq Require Import String.
From STLC Require Import Typ.

Inductive ast : Type :=
  | EVar : string -> ast
  | ELam : string -> option tp -> ast -> ast
  | EApp : ast -> ast -> ast
  | EUnit : ast
  | ELet : string -> ast -> ast -> ast
  | EPair : ast -> ast -> ast
  | EFst : ast -> ast
  | ESnd : ast -> ast
  | EInl : ast -> ast
  | EInr : ast -> ast
  | ECase : ast -> string -> ast -> string -> ast -> ast
  | EAnn : ast -> tp -> ast.

