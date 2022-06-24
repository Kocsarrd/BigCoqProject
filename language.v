From pv Require Export week8.
From stdpp Require Export base.
Import NatMap.

Inductive tag :=
  | IllegalArgumentException : tag.
Definition tag_dec (x y : tag) : {x = y} + {x <> y}.
Proof. decide equality. Qed.
Lemma tag_dec_eq {B} (y1 y2 : B) x :
  (if tag_dec x x then y1 else y2) = y1.
Proof. by destruct (tag_dec x x). Qed.

Inductive bin_op :=
  | PlusOp
  | MinusOp
  | LeOp
  | LtOp
  | EqOp.

Inductive expr :=
  | EVal : val -> expr
  | EVar : string -> expr
  | ELam : string -> expr -> expr
  | ERec : string -> string -> expr -> expr
  | EApp : expr -> expr -> expr
  | EOp : bin_op -> expr -> expr -> expr
  | EPair : expr -> expr -> expr
  | EFst : expr -> expr 
  | ESnd : expr -> expr 
  | EIf : expr -> expr -> expr -> expr
  | ESeq : expr -> expr -> expr
  | EAlloc : expr -> expr
  | ELoad : expr -> expr
  | EStore : expr -> expr -> expr
  | EFree : expr -> expr
  | EThrow : tag -> expr -> expr
  | ECatch : expr -> tag -> expr -> expr
with val :=
  | VClosure : string -> expr -> val
  | VRecClosure : string -> string -> expr -> val
  | VUnit : val
  | VBool : bool -> val
  | VNat : nat -> val
  | VPair : val -> val -> val
  | VRef : loc -> val.

Fixpoint subst (x : string) (w : val) (e : expr) : expr :=
  match e with
  | EVal _ => e
  | EVar y => if String.eq_dec y x then EVal w else EVar y
  | ELam y e => if String.eq_dec y x then ELam y e else ELam y (subst x w e)
  | ERec f y e =>
     if String.eq_dec y x then ERec f y e else
     if String.eq_dec f x then ERec f y e else ERec f y (subst x w e)
  | EApp e1 e2 => EApp (subst x w e1) (subst x w e2)
  | EOp op e1 e2 => EOp op (subst x w e1) (subst x w e2)
  | EPair e1 e2 => EPair (subst x w e1) (subst x w e2)
  | EFst e => EFst (subst x w e)
  | ESnd e => ESnd (subst x w e)
  | EIf e1 e2 e3 => EIf (subst x w e1) (subst x w e2) (subst x w e3)
  | ESeq e1 e2 => ESeq (subst x w e1) (subst x w e2)
  | EAlloc e => EAlloc (subst x w e)
  | EStore e1 e2 => EStore (subst x w e1) (subst x w e2)
  | ELoad e => ELoad (subst x w e)
  | EFree e => EFree (subst x w e)
  | EThrow t e => EThrow t (subst x w e)
  | ECatch e1 t e2 => ECatch (subst x w e1) t (subst x w e2)
  end.

Definition eval_bin_op (op : bin_op) (v1 v2 : val) : option val :=
  match op, v1, v2 with
  | PlusOp, VNat n1, VNat n2 => Some (VNat (n1 + n2))
  | MinusOp, VNat n1, VNat n2 => Some (VNat (n1 - n2))
  | LeOp, VNat n1, VNat n2 => Some (VBool (Nat.leb n1 n2))
  | LtOp, VNat n1, VNat n2 => Some (VBool (Nat.ltb n1 n2))
  | EqOp, VNat n1, VNat n2 => Some (VBool (Nat.eqb n1 n2))
  | EqOp, VBool b1, VBool b2 => Some (VBool (Bool.eqb b1 b2))
  | EqOp, VRef l1, VRef l2 => Some (VBool (Nat.eqb l1 l2))
  | _, _, _ => None
  end.

Notation heap := (natmap val).

Inductive res :=
  | ok : val -> res
  | ex : tag -> val -> res.

Inductive big_step : expr -> heap -> res -> heap -> Prop :=
  | Val_big_step h v :
      big_step (EVal v) h (ok v) h
  | Lam_big_step h y e :
      big_step (ELam y e) h (ok (VClosure y e)) h
  | Rec_big_step h f y e :
      big_step (ERec f y e) h (ok (VRecClosure f y e)) h
  | App_big_step h1 h2 h3 h4 y e1 e1' e2 v2 r :
      big_step e1 h1 (ok (VClosure y e1')) h2 ->
      big_step e2 h2 (ok v2) h3 ->
      big_step (subst y v2 e1') h3 r h4 ->
      big_step (EApp e1 e2) h1 r h4
  | AppRec_big_step h1 h2 h3 h4 f y e1 e1' e2 v2 r :
      big_step e1 h1 (ok (VRecClosure f y e1')) h2 ->
      big_step e2 h2 (ok v2) h3 ->
      big_step (subst y v2 (subst f (VRecClosure f y e1') e1')) h3 r h4 ->
      big_step (EApp e1 e2) h1 r h4
  | App_big_step_ex_l h1 h2 e1 e2 t v1 :
      big_step e1 h1 (ex t v1) h2 ->
      big_step (EApp e1 e2) h1 (ex t v1) h2
  | App_big_step_ex_r h1 h2 h3 e1 e2 t v1 v2 :
      big_step e1 h1 (ok v1) h2 ->
      big_step e2 h2 (ex t v2) h3 ->
      big_step (EApp e1 e2) h1 (ex t v2) h3
  | Op_big_step h1 h2 h3 e1 e2 op v1 v2 v :
      big_step e1 h1 (ok v1) h2 ->
      big_step e2 h2 (ok v2) h3 ->
      eval_bin_op op v1 v2 = Some v ->
      big_step (EOp op e1 e2) h1 (ok v) h3
  | Op_big_step_ex_l h1 h2 e1 e2 op t v1 :
      big_step e1 h1 (ex t v1) h2 ->
      big_step (EOp op e1 e2) h1 (ex t v1) h2
  | Op_big_step_ex_r h1 h2 h3 e1 e2 op t v1 v2 :
      big_step e1 h1 (ok v1) h2 ->
      big_step e2 h2 (ex t v2) h3 ->
      big_step (EOp op e1 e2) h1 (ex t v2) h3
  | Pair_big_step h1 h2 h3 e1 e2 v1 v2 :
      big_step e1 h1 (ok v1) h2 ->
      big_step e2 h2 (ok v2) h3 ->
      big_step (EPair e1 e2) h1 (ok (VPair v1 v2)) h3
  | Pair_big_step_ex_l h1 h2 e1 e2 t v1 :
      big_step e1 h1 (ex t v1) h2 ->
      big_step (EPair e1 e2) h1 (ex t v1) h2
  | Pair_big_step_ex_r h1 h2 h3 e1 e2 t v1 v2 :
      big_step e1 h1 (ok v1) h2 ->
      big_step e2 h2 (ex t v2) h3 ->
      big_step (EPair e1 e2) h1 (ex t v2) h3
  | Fst_big_step h1 h2 e v1 v2 :
      big_step e h1 (ok (VPair v1 v2)) h2 ->
      big_step (EFst e) h1 (ok v1) h2
  | Fst_big_step_ex h1 h2 e t v :
      big_step e h1 (ex t v) h2 ->
      big_step (EFst e) h1 (ex t v) h2
  | Snd_big_step h1 h2 e v1 v2 :
      big_step e h1 (ok (VPair v1 v2)) h2 ->
      big_step (ESnd e) h1 (ok v2) h2
  | Snd_big_step_ex h1 h2 e t v :
      big_step e h1 (ex t v) h2 ->
      big_step (ESnd e) h1 (ex t v) h2
  | If_big_step_true h1 h2 h3 e1 e2 e3 r :
      big_step e1 h1 (ok (VBool true)) h2 ->
      big_step e2 h2 r h3 ->
      big_step (EIf e1 e2 e3) h1 r h3
  | If_big_step_false h1 h2 h3 e1 e2 e3 r :
      big_step e1 h1 (ok (VBool false)) h2 ->
      big_step e3 h2 r h3 ->
      big_step (EIf e1 e2 e3) h1 r h3
  | If_big_step_ex h1 h2 e1 e2 e3 t v1 :
      big_step e1 h1 (ex t v1) h2 ->
      big_step (EIf e1 e2 e3) h1 (ex t v1) h2
  | Seq_big_step h1 h2 h3 e1 e2 v1 r :
      big_step e1 h1 (ok v1) h2 ->
      big_step e2 h2 r h3 ->
      big_step (ESeq e1 e2) h1 r h3
  | Seq_big_step_ex h1 h2 e1 e2 t v1 :
      big_step e1 h1 (ex t v1) h2 ->
      big_step (ESeq e1 e2) h1 (ex t v1) h2
  | Alloc_big_step h1 h2 e v :
      big_step e h1 (ok v) h2 ->
      big_step (EAlloc e) h1 (ok (VRef (fresh h2))) (insert (fresh h2) v h2)
  | Alloc_big_step_ex h1 h2 e t v :
      big_step e h1 (ex t v) h2 ->
      big_step (EAlloc e) h1 (ex t v) h2
  | Load_big_step h1 h2 e l v :
      big_step e h1 (ok (VRef l)) h2 ->
      lookup h2 l = Some v ->
      big_step (ELoad e) h1 (ok v) h2
  | Load_big_step_ex h1 h2 e t v :
      big_step e h1 (ex t v) h2 ->
      big_step (ELoad e) h1 (ex t v) h2
  | Store_big_step h1 h2 h3 e1 e2 l v2 :
      big_step e1 h1 (ok (VRef l)) h2 ->
      big_step e2 h2 (ok v2) h3 ->
      lookup h3 l <> None ->
     big_step (EStore e1 e2) h1 (ok (VRef l)) (insert l v2 h3)
  | Store_big_step_ex_l h1 h2 e1 e2 t v1 :
      big_step e1 h1 (ex t v1) h2 ->
      big_step (EStore e1 e2) h1 (ex t v1) h2
  | Store_big_step_ex_r h1 h2 h3 e1 e2 t v1 v2 :
      big_step e1 h1 (ok v1) h2 ->
      big_step e2 h2 (ex t v2) h3 ->
      big_step (EStore e1 e2) h1 (ex t v2) h3
  | Free_big_step h1 h2 e l v :
      big_step e h1 (ok (VRef l)) h2 ->
      lookup h2 l = Some v ->
      big_step (EFree e) h1 (ok v) (delete l h2)
  | Free_big_step_ex h1 h2 e t v :
      big_step e h1 (ex t v) h2 ->
      big_step (EFree e) h1 (ex t v) h2
  | Throw_big_step h1 h2 t e v :
      big_step e h1 (ok v) h2 ->
      big_step (EThrow t e) h1 (ex t v) h2
  | Throw_big_step_ex h1 h2 e t t' v :
      big_step e h1 (ex t' v) h2 ->
      big_step (EThrow t e) h1 (ex t' v) h2
  | Catch_big_step h1 h2 e1 e2 t v1 :
      big_step e1 h1 (ok v1) h2 ->
      big_step (ECatch e1 t e2) h1 (ok v1) h2
  | Catch_big_step_ex_1 h1 h2 h3 e1 e2 t v1 r :
      big_step e1 h1 (ex t v1) h2 ->
      big_step (EApp e2 (EVal v1)) h2 r h3 ->
      big_step (ECatch e1 t e2) h1 r h3
  | Catch_big_step_ex_2 h1 h2 e1 e2 t t' v1 :
      big_step e1 h1 (ex t' v1) h2 ->
      t <> t' ->
      big_step (ECatch e1 t e2) h1 (ex t' v1) h2.

Inductive ctx : (expr -> expr) -> Prop :=
  | App_l_ctx e2 : ctx (fun x => EApp x e2)
  | App_r_ctx v1 : ctx (EApp (EVal v1))
  | Op_l_ctx op e2 : ctx (fun x => EOp op x e2)
  | Op_r_ctx op v1 : ctx (EOp op (EVal v1))
  | Pair_l_ctx e2 : ctx (fun x => EPair x e2)
  | Pair_r_ctx v1 : ctx (EPair (EVal v1))
  | Fst_ctx : ctx EFst
  | Snd_ctx : ctx ESnd
  | If_ctx e2 e3 : ctx (fun x => EIf x e2 e3)
  | Seq_ctx e2 : ctx (fun x => ESeq x e2)
  | Alloc_ctx : ctx EAlloc
  | Load_ctx : ctx ELoad
  | Store_ctx_l e2 : ctx (fun x => EStore x e2)
  | Store_ctx_r v1 : ctx (EStore (EVal v1))
  | Free_ctx : ctx EFree
  | Id_ctx : ctx (fun x => x)
  | Compose_ctx k1 k2 : ctx k1 -> ctx k2 -> ctx (fun x => k1 (k2 x)).

Notation sepProp := (sepProp val).

Notation "P # Q" := (res_rect (fun _ => sepProp) P Q)
  (at level 10, no associativity).

Definition wp (e : expr) (Phi : val -> sepProp) 
                         (EPhi : tag -> val -> sepProp) : sepProp := fun h =>
  forall hf, disjoint h hf ->
    exists r h',
      disjoint h' hf /\
      big_step e (union h hf) r (union h' hf) /\
      (Phi # EPhi) r h'.

Definition hoare (P : sepProp) (e : expr)
                 (Phi : val -> sepProp) (EPhi : tag -> val -> sepProp) : Prop :=
  P |~ wp e Phi EPhi.

Ltac inv_big :=
  repeat match goal with
  | _ => progress simplify_eq
  | H : big_step (EVal _) _ _ _ |- _ => inv H
  | H : big_step (EVar _) _ _ _ |- _ => inv H
  | H : big_step (ELam _ _) _ _ _ |- _ => inv H
  | H : big_step (ERec _ _ _) _ _ _ |- _ => inv H
  | H : big_step (EApp _ _) _ _ _ |- _ => inv H
  | H : big_step (EOp _ _ _) _ _ _ |- _ => inv H
  | H : big_step (EPair _ _) _ _ _ |- _ => inv H
  | H : big_step (EFst _) _ _ _ |- _ => inv H
  | H : big_step (ESnd _) _ _ _ |- _ => inv H
  | H : big_step (EIf _ _ _) _ _ _ |- _ => inv H
  | H : big_step (ESeq _ _) _ _ _ |- _ => inv H
  | H : big_step (EAlloc _) _ _ _ |- _ => inv H
  | H : big_step (ELoad _) _ _ _ |- _ => inv H
  | H : big_step (EStore _ _) _ _ _ |- _ => inv H
  | H : big_step (EFree _) _ _ _ |- _ => inv H
  | H : big_step (EThrow _ _) _ _ _ |- _ => inv H
  | H : big_step (ECatch _ _ _) _ _ _ |- _ => inv H
  end.

Class TCSimpl {A} (x x' : A) := tc_simpl : x = x'.

Global Hint Extern 0 (TCSimpl _ _) =>
  simpl; reflexivity : typeclass_instances.

Global Hint Extern 0 (TCEq _ _) =>
  apply TCEq_eq; eassumption : typeclass_instances.

Global Hint Extern 0 (disjoint _ _) =>
  apply disjoint_comm; assumption : core.

Lemma big_step_ctx_ok k e v3 h1 h3 :
  ctx k ->
  big_step (k e) h1 (ok v3) h3 <->
    exists v2 h2,
      big_step e h1 (ok v2) h2 /\
      big_step (k (EVal v2)) h2 (ok v3) h3.
Proof.
  intros Hk; revert e v3 h1 h3; induction Hk; intros e v3 h1 h3;
    (split; [intros H3 | intros (v2 & h2 & H1 & H2)]);
    inv_big; eauto using big_step.
  - apply IHHk1 in H3 as (v2' & h2' & H2 & H3).
    apply IHHk2 in H2 as (v2 & h2 & H1 & H2).
    do 2 eexists; split; [done |]. apply IHHk1. eauto.
  - apply IHHk1. apply IHHk1 in H2 as (v2' & h2' & H2 & H3).
    do 2 eexists; split; [| done]. apply IHHk2. eauto.
Qed.

Lemma big_step_ctx_ex k e t v3 h1 h3 :
  ctx k ->
  big_step (k e) h1 (ex t v3) h3 <->
    big_step e h1 (ex t v3) h3 \/
    exists v2 h2,
      big_step e h1 (ok v2) h2 /\
      big_step (k (EVal v2)) h2 (ex t v3) h3.
Proof.
  intros Hk; revert e v3 h1 h3; induction Hk; intros e v3 h1 h3;
    (split; [intros H3 | intros [H | (v2 & h2 & H1 & H2)]]);
    inv_big; eauto 6 using big_step.
  - apply IHHk1 in H3 as [H2 | (v2' & h2' & H2 & H3)].
    + apply IHHk2 in H2 as [H1 | (v2 & h2 & H1 & H2)]; [by left |].
      right; do 2 eexists; split; [done |]. apply IHHk1. by left.
    + apply big_step_ctx_ok in H2 as (v2 & h2 & H1 & H2); [| done].
      right; do 2 eexists; split; [done |]. apply IHHk1. eauto.
  - apply IHHk1. left. apply IHHk2. by left.
  - apply IHHk1. apply IHHk1 in H2 as [H2 | (v2' & h2' & H2 & H3)].
    + left. apply IHHk2. eauto.
    + right; do 2 eexists; split; [| done]. apply big_step_ctx_ok; eauto.
Qed.

Lemma wp_mono Phi Psi EPhi EPsi e :
  (forall v, Phi v |~ Psi v) ->
  (forall t v, EPhi t v |~ EPsi t v) ->
  wp e Phi EPhi |~ wp e Psi EPsi.
Proof.
  intros H1 H2 h He hf Hdisj.
  edestruct He as (r & h' & Hdisj' & Hbig & Hr); [done |].
  exists r, h'; repeat split; [done .. |].
  destruct r as [v | t v]; simpl in *; [by apply H1 | by apply H2].
Qed.

Lemma wp_frame Phi EPhi e R :
  wp e Phi EPhi ** R |~ wp e (fun v => Phi v ** R) (fun t v => EPhi t v ** R).
Proof.
  intros h (h1 & h2 & -> & Hdisj & He & HR) hf Hdisj'.
  apply disjoint_union in Hdisj' as [??].
  destruct (He (union h2 hf)) as (r & h1' & Hdisj' & Hbig & Hr).
  { by apply disjoint_comm, disjoint_union. }
  apply disjoint_comm, disjoint_union in Hdisj' as [??].
  exists r, (union h1' h2); repeat split.
  { by apply disjoint_union. }
  { by rewrite <-!union_assoc. }
  destruct r as [v | t v]; simpl in *; by exists h1', h2.
Qed.

Lemma wp_ctx k Phi EPhi e :
  ctx k ->
  wp e (fun vret => wp (k (EVal vret)) Phi EPhi) EPhi |~ wp (k e) Phi EPhi.
Proof.
  intros Hk h1 He hf Hdisj1.
  edestruct He as (r2 & h2 & Hdisj2 & Hbig2 & Hr2); [done |].
  destruct r2 as [v2 | t v2]; simpl in Hr2.
  - edestruct Hr2 as (r3 & h3 & Hdisj3 & Hbig3 & Hr3); [done |].
    exists r3, h3; repeat split; [done | | done].
    destruct r3 as [v3 | v3].
    + apply big_step_ctx_ok; eauto.
    + apply big_step_ctx_ex; eauto.
  - exists (ex t v2), h2; repeat split; [done | | done].
    apply big_step_ctx_ex; eauto.
Qed.

Lemma Val_wp Phi EPhi v :
  Phi v |~ wp (EVal v) Phi EPhi.
Proof.
  intros h HPhi hf Hdisj. eauto using big_step.
Qed.

Lemma Lam_wp Phi EPhi x e :
  Phi (VClosure x e) |~ wp (ELam x e) Phi EPhi.
Proof.
  intros ???; eauto using big_step.
Qed.

Lemma Rec_wp Phi EPhi f x e :
  Phi (VRecClosure f x e) |~ wp (ERec f x e) Phi EPhi.
Proof.
  intros ???; eauto using big_step.
Qed.

Lemma App_wp Phi EPhi x e v e' :
  TCSimpl (subst x v e) e' ->
  wp e' Phi EPhi |~ wp (EApp (EVal (VClosure x e)) (EVal v)) Phi EPhi.
Proof.
  intros <- h Hwp hf Hdisj.
  edestruct Hwp as (vret & h' & Hdisj' & Hbig & HPost); [done|].
  eauto 6 using big_step.
Qed.

Lemma AppRec_wp Phi EPhi rec f x e v e' :
  TCEq rec (VRecClosure f x e) ->
  TCSimpl (subst x v (subst f rec e)) e' ->
  wp e' Phi EPhi |~ wp (EApp (EVal rec) (EVal v)) Phi EPhi.
Proof.
  intros -> <- h Hwp hf Hdisj.
  edestruct Hwp as (vret & h' & Hdisj' & Hbig & HPost); [done |].
  eauto 6 using big_step.
Qed.

Lemma Op_wp Phi EPhi op v1 v2 v :
  TCEq (eval_bin_op op v1 v2) (Some v) ->
  Phi v |~ wp (EOp op (EVal v1) (EVal v2)) Phi EPhi.
Proof.
  intros Hop%TCEq_eq h HPhi hf Hdisj.
  eauto 6 using big_step.
Qed.

Lemma Pair_wp Phi EPhi v1 v2 :
  Phi (VPair v1 v2) |~ wp (EPair (EVal v1) (EVal v2)) Phi EPhi.
Proof.
  intros ???; eauto 6 using big_step.
Qed.

Lemma Fst_wp Phi EPhi v1 v2 :
  Phi v1 |~ wp (EFst (EVal (VPair v1 v2))) Phi EPhi.
Proof.
  intros ???; eauto 6 using big_step.
Qed.

Lemma Snd_wp Phi EPhi v1 v2 :
  Phi v2 |~ wp (ESnd (EVal (VPair v1 v2))) Phi EPhi.
Proof.
  intros ???; eauto 6 using big_step.
Qed.

Lemma If_true_wp Phi EPhi e2 e3 :
  wp e2 Phi EPhi |~ wp (EIf (EVal (VBool true)) e2 e3) Phi EPhi.
Proof.  
  intros h Hwp hf Hdisj.
  edestruct Hwp as (?&?&?&?&?); eauto 6 using big_step.
Qed.

Lemma If_false_wp Phi EPhi e2 e3 :
  wp e3 Phi EPhi |~ wp (EIf (EVal (VBool false)) e2 e3) Phi EPhi.
Proof.
  intros h Hwp hf Hdisj.
  edestruct Hwp as (?&?&?&?&?); eauto 6 using big_step.
Qed.

Lemma Seq_wp Phi EPhi e1 e2 :
  wp e1 (fun _ => wp e2 Phi EPhi) EPhi |~ wp (ESeq e1 e2) Phi EPhi.
Proof.
  intros h He1 hf Hdisj.
  edestruct He1 as (r1 & h1 & Hdisj1 & Hbig1 & Hr1); [done |].
  destruct r1 as [v1 | t v1]; simpl in Hr1.
  - edestruct Hr1 as (r2 & h2 & Hdisj2 & Hbig2 & Hr2); [done |].
    eauto 6 using big_step.
  - eauto 6 using big_step.
Qed.

Lemma Alloc_wp Phi EPhi v :
  (All l, l ~> v -** Phi (VRef l)) |~ wp (EAlloc (EVal v)) Phi EPhi.
Proof.
  intros h H hf Hdisj. set (l := fresh (union h hf)).
  exists (ok (VRef l)), (union (singleton l v) h); repeat split.
  - rewrite disjoint_union, disjoint_singleton. split; [subst l | done].
    rewrite disjoint_union_comm; [| done].
    apply lookup_fresh_incl, incl_union_l.
  - replace (union (union (singleton l v) h) hf) with (insert l v (union h hf))
         by map_solver. eauto using big_step.
  - apply H; [| done]. rewrite disjoint_singleton; subst l.
    apply lookup_fresh_incl, incl_union_l.
Qed.

Lemma Load_wp Phi EPhi l v :
  l ~> v ** (l ~> v -** Phi v) |~ wp (ELoad (EVal (VRef l))) Phi EPhi.
Proof.
  intros h (h1 & h2 & -> & Hdisj & -> & Hwand) hf Hdisj'.
  apply disjoint_singleton in Hdisj.
  apply disjoint_union in Hdisj' as [??].
  apply disjoint_singleton in H.
  exists (ok v), (union (singleton l v) h2); split.
  { apply disjoint_union; split; [|done]. by apply disjoint_singleton. }
  split.
  { eapply Load_big_step; eauto using big_step. map_solver. }
  apply Hwand; [|done]. by apply disjoint_singleton.
Qed.

Lemma Store_wp Phi EPhi l v w :
  l ~> v ** (l ~> w -** Phi (VRef l)) |~
  wp (EStore (EVal (VRef l)) (EVal w)) Phi EPhi.
Proof.
  intros h (h1 & h2 & -> & Hdisj & -> & Hwand) hf Hdisj'.
  apply disjoint_singleton in Hdisj.
  apply disjoint_union in Hdisj' as [??].
  apply disjoint_singleton in H.
  exists (ok (VRef l)), (union (singleton l w) h2); split.
  { apply disjoint_union; split; [|done]; by apply disjoint_singleton. }
  split.
  { replace (union (union (singleton l w) h2) hf) 
      with (insert l w (insert l v (union h2 hf))) by map_solver.
    rewrite <- union_assoc, union_singleton_l. 
    eapply Store_big_step; eauto using big_step.
    map_solver.
  }
  apply Hwand; [|done]. by apply disjoint_singleton.
Qed.

Lemma Free_wp Phi EPhi l v :
  l ~> v ** Phi v |~ wp (EFree (EVal (VRef l))) Phi EPhi.
Proof.
  intros h (h1 & h2 & -> & Hdisj & -> & HPhi) hf Hdisj'.
  apply disjoint_singleton in Hdisj.
  apply disjoint_union in Hdisj' as [?%disjoint_singleton ?].
  exists (ok v), h2; repeat split; [done | | done].
  replace (union h2 hf) with (delete l (union (union (singleton l v) h2) hf))
       by map_solver.
  apply Free_big_step; [apply Val_big_step | map_solver].
Qed.

Lemma Throw_wp Phi EPhi t e :
  wp e (EPhi t) EPhi |~ wp (EThrow t e) Phi EPhi.
Proof.
  intros h He hf Hdisj.
  edestruct He as (r & h' & Hdisj' & Hbig & Hr); [done |].
  destruct r as [v | t' v].
  - exists (ex t v), h'. eauto using big_step.
  - exists (ex t' v), h'. eauto using big_step.
Qed.

Lemma Catch_wp Phi EPhi e1 t e2 :
  wp e1 Phi (fun t' v1 => if tag_dec t t'
                            then wp (EApp e2 (EVal v1)) Phi EPhi
                            else EPhi t' v1) |~
  wp (ECatch e1 t e2) Phi EPhi.
Proof.
  intros h He1 hf Hdisj.
  edestruct He1 as (r1 & h1 & Hdisj1 & Hbig & Hr1); [done |].
  destruct r1 as [v1 | t' v1]; simpl in Hr1.
  - exists (ok v1), h1. eauto using big_step.
  - destruct (tag_dec t t') as [<- | Ht].
    + edestruct Hr1 as (r2 & h2 & Hdisj2 & Hbig2 & Hr2); [done |].
      exists r2, h2. eauto using big_step.
    + exists (ex t' v1), h1. eauto using big_step.
Qed.
