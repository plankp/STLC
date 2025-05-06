From Coq Require Import String Program.Equality.
From STLC Require Import Typ Ast Lir.

Inductive hidden (f : tp -> Type) : Type :=
  | Ev : forall t, f t -> hidden f.

Definition weaken_s (g : ctx) (s : string -> option (hidden (db g))) (n : string) (t : tp) : string -> option (hidden (db (Cons g t))) :=
  fun n' => if string_dec n' n
            then Some (Ev _ t (H _ t))
            else match s n' with
                 | Some (Ev _ t' d') => Some (Ev _ t' (U _ _ _ d'))
                 | _ => None
                 end.

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

Definition bind_elabres {A B} (e : elabres A) (f : A -> elabres B) : elabres B :=
  match e with
  | Ok _ x => f x
  | UndefName _ n => UndefName _ n
  | NeedAnnot _ => NeedAnnot _
  | WrongType _ => WrongType _
  end.

Fixpoint infer'
  (check' : forall g, (string -> option (hidden (db g))) -> ast -> forall t, elabres (tm g t))
  (g : ctx) (s : string -> option (hidden (db g))) (e : ast) {struct e} : elabres (hidden (tm g)) :=
  match e with
  | EVar n =>
      match s n with
      | Some (Ev _ t n) => Ok _ (Ev _ t (Var _ _ n))
      | _ => UndefName _ n
      end
  | EAnn e t =>
      bind_elabres (check' _ s e t) (fun e =>
      Ok _ (Ev _ _ e))
  | EUnit =>
      Ok _ (Ev _ TUnit (Unit _))
  | ELam n (Some ta) m =>
      bind_elabres (infer' check' _ (weaken_s _ s n ta) m) (fun m =>
      match m with
      | Ev _ tr body => Ok _ (Ev _ (TArr ta tr) (Lam _ _ _ body))
      end)
  | EApp e1 e2 =>
      bind_elabres (infer' check' _ s e1) (fun e1 =>
      match e1 with
      | Ev _ (TArr ta tr) e1 =>
          bind_elabres (check' _ s e2 ta) (fun e2 =>
          Ok _ (Ev _ tr (App _ _ _ e1 e2)))
      | _ => WrongType _
      end)
  | EPair e1 e2 =>
      bind_elabres (infer' check' _ s e1) (fun e1 =>
      bind_elabres (infer' check' _ s e2) (fun e2 =>
      match e1, e2 with
      | Ev _ t1 e1, Ev _ t2 e2 => Ok _ (Ev _ (TPair t1 t2) (Pair _ _ _ e1 e2))
      end))
  | EFst e =>
      bind_elabres (infer' check' _ s e) (fun e =>
      match e with
      | Ev _ (TPair t1 t2) e => Ok _ (Ev _ t1 (Fst _ _ _ e))
      | _ => WrongType _
      end)
  | ESnd e =>
      bind_elabres (infer' check' _ s e) (fun e =>
      match e with
      | Ev _ (TPair t1 t2) e => Ok _ (Ev _ t2 (Snd _ _ _ e))
      | _ => WrongType _
      end)
  | ECase e n1 e1 n2 e2 =>
      bind_elabres (infer' check' _ s e) (fun e =>
      match e with
      | Ev _ (TInj t1 t2) e =>
          bind_elabres (infer' check' _ (weaken_s _ s n1 t1) e1) (fun e1 =>
          match e1 with
          | Ev _ tr e1 =>
              bind_elabres (check' _ (weaken_s _ s n2 t2) e2 tr) (fun e2 =>
              Ok _ (Ev _ tr (Case _ _ _ _ e e1 e2)))
          end)
      | _ => WrongType _
      end)
  | ELet n1 e1 e2 =>
      bind_elabres (infer' check' _ s e1) (fun e =>
      match e with
      | Ev _ t1 e1 =>
          bind_elabres (infer' check' _ (weaken_s _ s n1 t1) e2) (fun e2 =>
          match e2 with
          | Ev _ t2 e2 => Ok _ (Ev _ t2 (Let _ _ _ e1 e2))
          end)
      end)
  | _ =>
      NeedAnnot _
  end.

Fixpoint check'
  (g : ctx) (s : string -> option (hidden (db g))) (e : ast) (t : tp) {struct e} : elabres (tm g t) :=
  match e, t with
  | EAnn e t', _ =>
      match tp_eq_dec t' t with
      | left Heq =>
          (* due to Prop erasure, this is actually a tail call to check' *)
          match Heq with eq_refl => check' _ s e t' end
      | _ => WrongType _
      end
  | ELam n None m, TArr ta tr =>
      bind_elabres (check' _ (weaken_s _ s n ta) m tr) (fun m =>
      Ok _ (Lam _ _ _ m))
  | ELam n (Some t') m, TArr ta tr =>
      match tp_eq_dec t' ta with
      | left Heq =>
          bind_elabres (check' _ (weaken_s _ s n t') m tr) (fun m =>
          Ok _ (Lam _ _ _ (match Heq with eq_refl => m end)))
      | _ => WrongType _
      end
  | ELam _ _ _, _ =>
      WrongType _
  | EPair e1 e2, TPair t1 t2 =>
      bind_elabres (check' g s e1 t1) (fun e1 =>
      bind_elabres (check' g s e2 t2) (fun e2 =>
      Ok _ (Pair _ _ _ e1 e2)))
  | EPair _ _, _ =>
      WrongType _
  | EInl e, TInj t1 t2 =>
      bind_elabres (check' g s e t1) (fun e =>
      Ok _ (Inl _ _ _ e))
  | EInl _, _ =>
      WrongType _
  | EInr e, TInj t1 t2 =>
      bind_elabres (check' g s e t2) (fun e =>
      Ok _ (Inr _ _ _ e))
  | EInr _, _ =>
      WrongType _
  | ECase e n1 e1 n2 e2, _ =>
      bind_elabres (infer' check' g s e) (fun e =>
      match e with
      | Ev _ (TInj t1 t2) e =>
          bind_elabres (check' _ (weaken_s _ s n1 t1) e1 t) (fun e1 =>
          bind_elabres (check' _ (weaken_s _ s n2 t2) e2 t) (fun e2 =>
          Ok _ (Case _ _ _ _ e e1 e2)))
      | _ => WrongType _
      end)
  | ELet n1 e1 e, _ =>
      bind_elabres (infer' check' g s e1) (fun e1 =>
      match e1 with
      | Ev _ t1 e1 =>
          bind_elabres (check' _ (weaken_s _ s n1 t1) e t) (fun e =>
          Ok _ (Let _ _ _ e1 e))
      end)
  | _, _ =>
      bind_elabres (infer' check' g s e) (fun e =>
      match e with
      | Ev _ t' e =>
          match tp_eq_dec t' t with
          | left Heq => Ok _ (match Heq with eq_refl => e end)
          | _ => WrongType _
          end
      end)
  end.

Definition elab_infer := infer' check'.
Definition elab_check := check'.

