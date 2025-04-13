From Coq Require Import String Program.Equality.
From STLC Require Import Typ Ast Lir.

Inductive hidden (f : tp -> Type) : Type :=
  | Ev : forall t, f t -> hidden f.

Definition weaken_s (g : ctx) (s : string -> option (hidden (db g))) (n : string) (t : tp) : string -> option (hidden (db (Cons g t))).
Proof.
  intros n'.
  destruct (string_dec n' n).
  + apply (Some (Ev _ t (H _ t))).
  + destruct (s n') as [[t' d']|].
    apply (Some (Ev _ t' (U _ _ _ d'))).
    apply None.
Defined.

Lemma weaken_s_adds_a_new_binding:
  forall g (s : string -> option (hidden (db g))) n t, (weaken_s g s n t) n = Some (Ev _ _ (H _ t)).
Proof.
  intros.
  unfold weaken_s.
  destruct string_dec.
  + reflexivity.
  + contradiction.
Qed.

Lemma weaken_s_preserves_old_ctx1:
  forall g (s : string -> option (hidden (db g))) n t,
  forall n', n <> n' -> s n' = None -> (weaken_s g s n t) n' = None.
Proof.
  intros g s n t.
  intros n' H H0.
  unfold weaken_s.
  destruct string_dec.
  + rewrite e in H.
    contradiction.
  + rewrite H0.
    reflexivity.
Qed.

Lemma weaken_s_preserves_old_ctx2:
  forall g (s : string -> option (hidden (db g))) n t,
  forall n' t' d', n <> n' -> s n' = Some (Ev (db g) t' d') -> (weaken_s g s n t) n' = Some (Ev _ t' (U _ _ _ d')).
Proof.
  intros g s n t.
  intros n' t' d' H0 H1.
  unfold weaken_s.
  destruct string_dec.
  + rewrite e in H0.
    contradiction.
  + rewrite H1.
    reflexivity.
Qed.

Fixpoint elab_infer (g : ctx) (s : string -> option (hidden (db g))) (e : ast) {struct e} : option (hidden (tm g))
  with elab_check (g : ctx) (s : string -> option (hidden (db g))) (e : ast) (t : tp) {struct e} : option (tm g t).
Proof.
  - (* defining elab_infer *)
    destruct e.
    * (* EVar *)
      destruct (s s0) as [[t n]|].
      apply (Some (Ev _ t (Var _ _ n))).
      apply None.
    * (* ELam *)
      destruct o as [ta|].
      + destruct (elab_infer _ (weaken_s _ s s0 ta) e) as [[tr body]|].
        apply (Some (Ev _ (TArr ta tr) (Lam _ _ _ body))).
        apply None.
      + apply None. (* lack of info, give up *)
    * (* EApp *)
      destruct (elab_infer _ s e1) as [[[ta tr| |c1 c2|i1 i2] tm1]|].
      + (* we inferred e1 as ta -> tr *)
        destruct (elab_check _ s e2 ta) as [tm2|].
        apply (Some (Ev _ tr (App _ _ _ tm1 tm2))).
        apply None.
      + apply None. (* a whole bunch of type-mismatch cases *)
      + apply None.
      + apply None.
      + (* we couldn't infer e1 *)
        apply None.
    * (* EUnit *)
      apply (Some (Ev _ TUnit (Unit _))).
    * (* ELet *)
      destruct (elab_infer _ s e1) as [[t1 tm1]|].
      + (* we inferred e1 *)
        destruct (elab_infer _ (weaken_s _ s s0 t1) e2) as [[t2 tm2]|].
        apply (Some (Ev _ t2 (Let _ _ _ tm1 tm2))).
        apply None.
      + (* we couldn't infer e1 *)
        apply None.
    * (* EPair *)
      destruct (elab_infer _ s e1) as [[t1 tm1]|].
      destruct (elab_infer _ s e2) as [[t2 tm2]|].
      apply (Some (Ev _ (TPair t1 t2) (Pair _ _ _ tm1 tm2))).
      apply None.
      apply None.
    * (* EFst *)
      destruct (elab_infer _ s e) as [[[_1 _2| |t1 t2|i1 i2] tm]|].
      apply None.
      apply None.
      apply (Some (Ev _ t1 (Fst _ _ _ tm))).
      apply None.
      apply None.
    * (* ESnd *)
      destruct (elab_infer _ s e) as [[[_1 _2| |t1 t2|i1 i2] tm]|].
      apply None.
      apply None.
      apply (Some (Ev _ t2 (Snd _ _ _ tm))).
      apply None.
      apply None.
    * (* EInl *)
      apply None. (* don't know what type to assign to the other entry. *)
    * (* EInr *)
      apply None.
    * (* ECase *)
      destruct (elab_infer _ s e1) as [[[_1 _2| |c1 c2|i1 i2] tm1]|].
      apply None.
      apply None.
      apply None.
      destruct (elab_infer _ (weaken_s _ s s0 i1) e2) as [[tr tm2]|].
      destruct (elab_check _ (weaken_s _ s s0 i2) e3 tr) as [tm3|].
      apply (Some (Ev _ tr (Case _ _ _ _ tm1 tm2 tm3))).
      apply None.
      apply None.
      apply None.
    * (* EAnn *)
      destruct (elab_check _ s e t).
      apply (Some (Ev _ t t0)).
      apply None.

  - (* defining elab_check *)
    destruct e.
    * (* EVar *)
      destruct (s s0) as [[t0 n]|].
      + (* variable exists *)
        destruct (tp_eq_dec t0 t).
        rewrite <- e. apply (Some (Var _ _ n)).
        apply None.
      + (* variable does not exist *)
        apply None.
    * (* ELam *)
      destruct t as [ta tr| | c1 c2|i1 i2].
      + (* ta -> tr *)
        destruct o as [ta'|].
        ++ destruct (tp_eq_dec ta' ta).
           +++ destruct (elab_check _ (weaken_s _ s s0 ta) e tr) as [body|].
               apply (Some (Lam _ _ _  body)).
               apply None.
           +++ apply None.
        ++ destruct (elab_check _ (weaken_s _ s s0 ta) e tr) as [body|].
           apply (Some (Lam _ _ _  body)).
           apply None.
      + apply None. (* a whole bunch of type-mismatch cases *)
      + apply None.
      + apply None.
    * (* EApp *)
      destruct (elab_infer _ s e1) as [[[ta tr| | c1 c2|i1 i2] tm1]|].
      + (* we inferreed e1 as ta -> tr *)
        destruct (tp_eq_dec tr t).
        ++ destruct (elab_check _ s e2 ta) as [tm2|].
           rewrite <- e. apply (Some (App _ _ _ tm1 tm2)).
           apply None.
        ++ apply None.
      + apply None. (* a whole bunch of type-mismatch cases *)
      + apply None.
      + apply None.
      + apply None.
    * (* EUnit *)
      destruct (tp_eq_dec TUnit t).
      rewrite <- e. apply (Some (Unit _)).
      apply None.
    * (* ELet *)
      destruct (elab_infer _ s e1) as [[t1 tm1]|].
      + (* we inferred e1 *)
        destruct (elab_check _ (weaken_s _ s s0 t1) e2 t) as [tm2|].
        apply (Some (Let _ _ _ tm1 tm2)).
        apply None.
      + (* we couldn't infer e'1 *)
        apply None.
    * (* EPair *)
      destruct t as [_1 _2| |t1 t2|i1 i2].
      + apply None.
      + apply None.
      + (* t1 * t2 *)
        destruct (elab_check _ s e1 t1) as [tm1|].
        destruct (elab_check _ s e2 t2) as [tm2|].
        apply (Some (Pair _ _ _ tm1 tm2)).
        apply None.
        apply None.
      + apply None.
    * (* EFst *)
      destruct (elab_infer _ s e) as [[[_1 _2| |t1 t2|i1 i2] tm]|].
      apply None.
      apply None.
      destruct (tp_eq_dec t1 t).
      rewrite <- e0. apply (Some (Fst _ _ _ tm)).
      apply None.
      apply None.
      apply None.
    * (* ESnd *)
      destruct (elab_infer _ s e) as [[[_1 _2| |t1 t2|i1 i2] tm]|].
      apply None.
      apply None.
      destruct (tp_eq_dec t2 t).
      rewrite <- e0. apply (Some (Snd _ _ _ tm)).
      apply None.
      apply None.
      apply None.
    * (* EInl *)
      destruct t as [ta tr| |c1 c2|i1 i2].
      apply None.
      apply None.
      apply None.
      destruct (elab_check _ s e i1) as [tm|].
      + apply (Some (Inl _ _ _ tm)).
      + apply None.
    * (* EInr *)
      destruct t as [ta tr| |c1 c2|i1 i2].
      apply None.
      apply None.
      apply None.
      destruct (elab_check _ s e i2) as [tm|].
      + apply (Some (Inr _ _ _ tm)).
      + apply None.
    * (* ECase *)
      destruct (elab_infer _ s e1) as [[[_1 _2| |c1 c2|i1 i2] tm1]|].
      apply None.
      apply None.
      apply None.
      destruct (elab_check _ (weaken_s _ s s0 i1) e2 t) as [tm2|].
      destruct (elab_check _ (weaken_s _ s s0 i2) e3 t) as [tm3|].
      apply (Some (Case _ _ _ _ tm1 tm2 tm3)).
      apply None.
      apply None.
      apply None.
    * (* EAnn *)
      destruct (tp_eq_dec t0 t).
      rewrite <- e0. apply (elab_check _ s e t0).
      apply None.
Defined.

