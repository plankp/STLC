From Coq Require Import ExtrOcamlBasic ExtrOcamlString Extraction String.
From STLC Require Import Ast Typ Ela Lir.

Extract Inlined Constant string_dec => "(=)".

Extraction Library Ast.
Extraction Library Typ.
Extraction Library Ela.
Extraction Library Lir.

