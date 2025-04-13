From STLC Require Import Typ.

Inductive ctx : Type :=
  | Nil
  | Cons : ctx -> tp -> ctx.

Inductive db : ctx -> tp -> Type :=
  | H : forall g t, db (Cons g t) t
  | U : forall g t' t, db g t -> db (Cons g t') t.

Inductive tm : ctx -> tp -> Type :=
  | Var : forall g t, db g t -> tm g t
  | Lam : forall g ta tr, tm (Cons g ta) tr -> tm g (TArr ta tr)
  | App : forall g ta tr, tm g (TArr ta tr) -> tm g ta -> tm g tr
  | Unit : forall g, tm g TUnit
  | Let : forall g ta tr, tm g ta -> tm (Cons g ta) tr -> tm g tr
  | Pair : forall g t1 t2, tm g t1 -> tm g t2 -> tm g (TPair t1 t2)
  | Fst : forall g t1 t2, tm g (TPair t1 t2) -> tm g t1
  | Snd : forall g t1 t2, tm g (TPair t1 t2) -> tm g t2
  | Inl : forall g t1 t2, tm g t1 -> tm g (TInj t1 t2)
  | Inr : forall g t1 t2, tm g t2 -> tm g (TInj t1 t2)
  | Case : forall g t1 t2 tr, tm g (TInj t1 t2) -> tm (Cons g t1) tr -> tm (Cons g t2) tr -> tm g tr.

