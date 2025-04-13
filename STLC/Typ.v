Inductive tp : Type :=
  | TArr : tp -> tp -> tp
  | TUnit : tp
  | TPair : tp -> tp -> tp
  | TInj : tp -> tp -> tp.

Definition tp_eq_dec (a : tp) (b : tp) : {a = b} + {a <> b}.
Proof.
  decide equality.
Defined.

