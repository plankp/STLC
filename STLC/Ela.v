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

Inductive elabres (T : Type) : Type :=
  | Ok : T -> elabres T
  | UndefName : string -> elabres T
  | NeedAnnot : elabres T
  | WrongType : elabres T.

Fixpoint elab_infer (g : ctx) (s : string -> option (hidden (db g))) (e : ast) {struct e} : elabres (hidden (tm g))
  with elab_check (g : ctx) (s : string -> option (hidden (db g))) (e : ast) (t : tp) {struct e} : elabres (tm g t).
Proof.
  - (* defining elab_infer *)
    destruct e.
    * (* EVar *)
      destruct (s s0) as [[t n]|].
      apply (Ok _ (Ev _ t (Var _ _ n))).
      apply (UndefName _ s0).
    * (* ELam *)
      destruct o as [ta|].
      destruct (elab_infer _ (weaken_s _ s s0 ta) e) as [[tr body]|err| | ].
      apply (Ok _ (Ev _ (TArr ta tr) (Lam _ _ _ body))).
      apply (UndefName _ err).
      apply NeedAnnot.
      apply WrongType.
      apply NeedAnnot.
    * (* EApp *)
      destruct (elab_infer _ s e1) as [[[ta tr| |c1 c2|i1 i2] tm1]|err| |].
      + (* we inferred e1 as ta -> tr *)
        destruct (elab_check _ s e2 ta) as [tm2|err| |].
        apply (Ok _ (Ev _ tr (App _ _ _ tm1 tm2))).
        apply (UndefName _ err).
        apply NeedAnnot.
        apply WrongType.
      + apply WrongType.
      + apply WrongType.
      + apply WrongType.
      + apply (UndefName _ err).
      + apply NeedAnnot.
      + apply WrongType.
    * (* EUnit *)
      apply (Ok _ (Ev _ TUnit (Unit _))).
    * (* ELet *)
      destruct (elab_infer _ s e1) as [[t1 tm1]|err| | ].
      + (* we inferred e1 *)
        destruct (elab_infer _ (weaken_s _ s s0 t1) e2) as [[t2 tm2]|err| |].
        apply (Ok _ (Ev _ t2 (Let _ _ _ tm1 tm2))).
        apply (UndefName _ err).
        apply NeedAnnot.
        apply WrongType.
      + apply (UndefName _ err).
      + apply NeedAnnot.
      + apply WrongType.
    * (* EPair *)
      destruct (elab_infer _ s e1) as [[t1 tm1]|err| |].
      destruct (elab_infer _ s e2) as [[t2 tm2]|err| |].
      apply (Ok _ (Ev _ (TPair t1 t2) (Pair _ _ _ tm1 tm2))).
      apply (UndefName _ err).
      apply NeedAnnot.
      apply WrongType.
      apply (UndefName _ err).
      apply NeedAnnot.
      apply WrongType.
    * (* EFst *)
      destruct (elab_infer _ s e) as [[[_1 _2| |t1 t2|i1 i2] tm]|err| |].
      apply WrongType.
      apply WrongType.
      apply (Ok _ (Ev _ t1 (Fst _ _ _ tm))).
      apply WrongType.
      apply (UndefName _ err).
      apply NeedAnnot.
      apply WrongType.
    * (* ESnd *)
      destruct (elab_infer _ s e) as [[[_1 _2| |t1 t2|i1 i2] tm]|err| |].
      apply WrongType.
      apply WrongType.
      apply (Ok _ (Ev _ t2 (Snd _ _ _ tm))).
      apply WrongType.
      apply (UndefName _ err).
      apply NeedAnnot.
      apply WrongType.
    * (* EInl *)
      apply NeedAnnot.
    * (* EInr *)
      apply NeedAnnot.
    * (* ECase *)
      destruct (elab_infer _ s e1) as [[[_1 _2| |c1 c2|i1 i2] tm1]|err| |].
      apply WrongType.
      apply WrongType.
      apply WrongType.
      destruct (elab_infer _ (weaken_s _ s s0 i1) e2) as [[tr tm2]|err| |].
      destruct (elab_check _ (weaken_s _ s s0 i2) e3 tr) as [tm3|err| |].
      apply (Ok _ (Ev _ tr (Case _ _ _ _ tm1 tm2 tm3))).
      apply (UndefName _ err).
      apply NeedAnnot.
      apply WrongType.
      apply (UndefName _ err).
      apply NeedAnnot.
      apply WrongType.
      apply (UndefName _ err).
      apply NeedAnnot.
      apply WrongType.
    * (* EAnn *)
      destruct (elab_check _ s e t).
      apply (Ok _ (Ev _ t t0)).
      apply (UndefName _ s0).
      apply NeedAnnot.
      apply WrongType.

  - (* defining elab_check *)
    destruct e.
    * (* EVar *)
      destruct (s s0) as [[t0 n]|].
      + (* variable exists *)
        destruct (tp_eq_dec t0 t).
        rewrite <- e. apply (Ok _ (Var _ _ n)).
        apply WrongType.
      + (* variable does not exist *)
        apply (UndefName _ s0).
    * (* ELam *)
      destruct t as [ta tr| | c1 c2|i1 i2].
      + (* ta -> tr *)
        destruct o as [ta'|].
        ++ destruct (tp_eq_dec ta' ta).
           destruct (elab_check _ (weaken_s _ s s0 ta) e tr) as [body|err| |].
           apply (Ok _ (Lam _ _ _  body)).
           apply (UndefName _ err).
           apply NeedAnnot.
           apply WrongType.
           apply WrongType.
        ++ destruct (elab_check _ (weaken_s _ s s0 ta) e tr) as [body|err| |].
           apply (Ok _ (Lam _ _ _  body)).
           apply (UndefName _ err).
           apply NeedAnnot.
           apply WrongType.
      + apply WrongType. (* a whole bunch of type-mismatch cases *)
      + apply WrongType.
      + apply WrongType.
    * (* EApp *)
      destruct (elab_infer _ s e1) as [[[ta tr| | c1 c2|i1 i2] tm1]|err| |].
      + (* we inferreed e1 as ta -> tr *)
        destruct (tp_eq_dec tr t).
        ++ destruct (elab_check _ s e2 ta) as [tm2|err| |].
           rewrite <- e. apply (Ok _ (App _ _ _ tm1 tm2)).
           apply (UndefName _ err).
           apply NeedAnnot.
           apply WrongType.
        ++ apply WrongType.
      + apply WrongType. (* a whole bunch of type-mismatch cases *)
      + apply WrongType.
      + apply WrongType.
      + apply (UndefName _ err).
      + apply NeedAnnot.
      + apply WrongType.
    * (* EUnit *)
      destruct (tp_eq_dec TUnit t).
      rewrite <- e. apply (Ok _ (Unit _)).
      apply WrongType.
    * (* ELet *)
      destruct (elab_infer _ s e1) as [[t1 tm1]|err| |].
      + (* we inferred e1 *)
        destruct (elab_check _ (weaken_s _ s s0 t1) e2 t) as [tm2|err| |].
        apply (Ok _ (Let _ _ _ tm1 tm2)).
        apply (UndefName _ err).
        apply NeedAnnot.
        apply WrongType.
      + apply (UndefName _ err).
      + apply NeedAnnot.
      + apply WrongType.
    * (* EPair *)
      destruct t as [_1 _2| |t1 t2|i1 i2].
      + apply WrongType.
      + apply WrongType.
      + (* t1 * t2 *)
        destruct (elab_check _ s e1 t1) as [tm1|err| |].
        destruct (elab_check _ s e2 t2) as [tm2|err| |].
        apply (Ok _ (Pair _ _ _ tm1 tm2)).
        apply (UndefName _ err).
        apply NeedAnnot.
        apply WrongType.
        apply (UndefName _ err).
        apply NeedAnnot.
        apply WrongType.
      + apply WrongType.
    * (* EFst *)
      destruct (elab_infer _ s e) as [[[_1 _2| |t1 t2|i1 i2] tm]|err| |].
      apply WrongType.
      apply WrongType.
      destruct (tp_eq_dec t1 t).
      rewrite <- e0. apply (Ok _ (Fst _ _ _ tm)).
      apply WrongType.
      apply WrongType.
      apply (UndefName _ err).
      apply NeedAnnot.
      apply WrongType.
    * (* ESnd *)
      destruct (elab_infer _ s e) as [[[_1 _2| |t1 t2|i1 i2] tm]|err| |].
      apply WrongType.
      apply WrongType.
      destruct (tp_eq_dec t2 t).
      rewrite <- e0. apply (Ok _ (Snd _ _ _ tm)).
      apply WrongType.
      apply WrongType.
      apply (UndefName _ err).
      apply NeedAnnot.
      apply WrongType.
    * (* EInl *)
      destruct t as [ta tr| |c1 c2|i1 i2].
      apply WrongType.
      apply WrongType.
      apply WrongType.
      destruct (elab_check _ s e i1) as [tm|err| |].
      + apply (Ok _ (Inl _ _ _ tm)).
      + apply (UndefName _ err).
      + apply NeedAnnot.
      + apply WrongType.
    * (* EInr *)
      destruct t as [ta tr| |c1 c2|i1 i2].
      apply WrongType.
      apply WrongType.
      apply WrongType.
      destruct (elab_check _ s e i2) as [tm|err| |].
      + apply (Ok _ (Inr _ _ _ tm)).
      + apply (UndefName _ err).
      + apply NeedAnnot.
      + apply WrongType.
    * (* ECase *)
      destruct (elab_infer _ s e1) as [[[_1 _2| |c1 c2|i1 i2] tm1]|err| |].
      apply WrongType.
      apply WrongType.
      apply WrongType.
      destruct (elab_check _ (weaken_s _ s s0 i1) e2 t) as [tm2|err| |].
      destruct (elab_check _ (weaken_s _ s s0 i2) e3 t) as [tm3|err| |].
      apply (Ok _ (Case _ _ _ _ tm1 tm2 tm3)).
      apply (UndefName _ err).
      apply NeedAnnot.
      apply WrongType.
      apply (UndefName _ err).
      apply NeedAnnot.
      apply WrongType.
      apply (UndefName _ err).
      apply NeedAnnot.
      apply WrongType.
    * (* EAnn *)
      destruct (tp_eq_dec t0 t).
      rewrite <- e0. apply (elab_check _ s e t0).
      apply WrongType.
Defined.

