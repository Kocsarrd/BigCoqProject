From pv Require Export library.
From pv Require Export week8.

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
  | EThrow : expr -> expr
  | ECatch : expr -> expr -> expr
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
  | EThrow e => EThrow (subst x w e)
  | ECatch e t => ECatch (subst x w e) (subst x w t)  
  end.

Definition eval_bin_op (op : bin_op) (v1 v2 : val) : option val :=
  match op, v1, v2 with
  | PlusOp, VNat n1, VNat n2 => Some (VNat (n1 + n2))
  | MinusOp, VNat n1, VNat n2 => Some (VNat (n1 - n2))
  | LeOp, VNat n1, VNat n2 => Some (VBool (Nat.leb n1 n2))
  | LtOp, VNat n1, VNat n2 => Some (VBool (Nat.ltb n1 n2))
  | EqOp, VNat n1, VNat n2 => Some (VBool (Nat.eqb n1 n2))
  | EqOp, VBool n1, VBool n2 => Some (VBool (Bool.eqb n1 n2))
  | EqOp, VRef l1, VRef l2 => Some (VBool (Nat.eqb l1 l2))
  | _, _, _ => None
  end.

Notation heap := (natmap val).
Import NatMap.

Inductive big_step : expr -> heap -> val -> heap -> Prop :=
  | Val_big_step h v :
     big_step (EVal v) h v h
  | Lam_big_step h y e :
     big_step (ELam y e) h (VClosure y e) h
  | Rec_big_step h f y e :
     big_step (ERec f y e) h (VRecClosure f y e) h
  | App_big_step h1 h2 h3 h4 y e1 e1' e2 v2 v :
     big_step e1 h1 (VClosure y e1') h2 ->
     big_step e2 h2 v2 h3 ->
     big_step (subst y v2 e1') h3 v h4 ->
     big_step (EApp e1 e2) h1 v h4
  | AppRec_big_step h1 h2 h3 h4 f y e1 e1' e2 v2 v :
     big_step e1 h1 (VRecClosure f y e1') h2 ->
     big_step e2 h2 v2 h3 ->
     big_step (subst y v2 (subst f (VRecClosure f y e1') e1')) h3 v h4 ->
     big_step (EApp e1 e2) h1 v h4
  | Op_big_step h1 h2 h3 e1 e2 op v1 v2 v :
     big_step e1 h1 v1 h2 ->
     big_step e2 h2 v2 h3 ->
     eval_bin_op op v1 v2 = Some v ->
     big_step (EOp op e1 e2) h1 v h3
  | Pair_big_step h1 h2 h3 e1 e2 v1 v2 :
     big_step e1 h1 v1 h2 ->
     big_step e2 h2 v2 h3 ->
     big_step (EPair e1 e2) h1 (VPair v1 v2) h3
  | Fst_big_step h1 h2 e v1 v2 :
     big_step e h1 (VPair v1 v2) h2 ->
     big_step (EFst e) h1 v1 h2
  | Snd_big_step h1 h2 e v1 v2 :
     big_step e h1 (VPair v1 v2) h2 ->
     big_step (ESnd e) h1 v2 h2
  | If_big_step_true h1 h2 h3 e1 e2 e3 v :
     big_step e1 h1 (VBool true) h2 ->
     big_step e2 h2 v h3 ->
     big_step (EIf e1 e2 e3) h1 v h3
  | If_big_step_false h1 h2 h3 e1 e2 e3 v :
     big_step e1 h1 (VBool false) h2 ->
     big_step e3 h2 v h3 ->
     big_step (EIf e1 e2 e3) h1 v h3
  | Seq_big_step h1 h2 h3 e1 e2 v1 v2 :
     big_step e1 h1 v1 h2 ->
     big_step e2 h2 v2 h3 ->
     big_step (ESeq e1 e2) h1 v2 h3
  | Alloc_big_step h1 h2 e v :
     big_step e h1 v h2 ->
     big_step (EAlloc e) h1 (VRef (fresh h2)) (insert (fresh h2) v h2)
  | Load_big_step h1 h2 e l v :
     big_step e h1 (VRef l) h2 ->
     lookup h2 l = Some v ->
     big_step (ELoad e) h1 v h2
  | Store_big_step h1 h2 h3 e1 e2 l v :
     big_step e1 h1 (VRef l) h2 ->
     big_step e2 h2 v h3 ->
     lookup h3 l <> None ->
     big_step (EStore e1 e2) h1 (VRef l) (insert l v h3)
  | Free_big_step h1 h2 e l v :
     big_step e h1 (VRef l) h2 ->
     lookup h2 l = Some v ->
     big_step (EFree e) h1 v (delete l h2)
  | Catch_big_step_l h1 h2 e1 e2 v :
     big_step e1 h1 v h2 ->
     big_step (ECatch e1 e2) h1 v h2
  | Catch_big_step_r h1 h2 h3 e1 e2 v1 v2 :
     big_step_error e1 h1 v1 h2 ->
     big_step (EApp e2 (EVal v1)) h2 v2 h3 ->
     big_step (ECatch e1 e2) h1 v2 h3
with big_step_error : expr -> heap -> val -> heap -> Prop :=
  | Throw_big_step_error h1 h2 e v :
     big_step e h1 v h2 -> 
     big_step_error (EThrow e) h1 v h2
  | Throw_big_step_error_arg h1 h2 e v :
     big_step_error e h1 v h2 ->
     big_step_error (EThrow e) h1 v h2
  | App_big_step_error_l h1 h2 e1 e2 v :
     big_step_error e1 h1 v h2 ->
     big_step_error (EApp e1 e2) h1 v h2
  | App_big_step_error_r h1 h2 h3 e1 e2 v1 v2 :
     big_step e1 h1 v1 h2 ->
     big_step_error e2 h2 v2 h3 ->
     big_step_error (EApp e1 e2) h1 v2 h3
  | App_big_step_error_subst h1 h2 h3 h4 y e1 e1' e2 v2 v3 :
     big_step e1 h1 (VClosure y e1') h2 ->
     big_step e2 h2 v2 h3 ->
     big_step_error (subst y v2 e1') h3 v3 h4 ->
     big_step_error (EApp e1 e2) h1 v3 h4
  | AppRec_big_step_error_subst h1 h2 h3 h4 f y e1 e1' e2 v2 v3 :
     big_step e1 h1 (VRecClosure f y e1') h2 ->
     big_step e2 h2 v2 h3 ->
     big_step_error (subst y v2 (subst f (VRecClosure f y e1') e1')) h3 v3 h4 ->
     big_step_error (EApp e1 e2) h1 v3 h4
  | Op_big_step_error_l h1 h2 e1 e2 op v1 :
     big_step_error e1 h1 v1 h2 ->
     big_step_error (EOp op e1 e2) h1 v1 h2
  | Op_big_step_error_r h1 h2 h3 e1 e2 op v1 v2 :
     big_step e1 h1 v1 h2 ->
     big_step_error e2 h2 v2 h3 ->
     big_step_error (EOp op e1 e2) h1 v2 h3
  | Pair_big_step_error_l h1 h2 e1 e2 v1:
     big_step_error e1 h1 v1 h2 ->
     big_step_error (EPair e1 e2) h1 v1 h2
  | Pair_big_step_error_r h1 h2 h3 e1 e2 v1 v2 :
     big_step e1 h1 v1 h2 ->
     big_step_error e2 h2 v2 h3 ->
     big_step_error (EPair e1 e2) h1 v2 h3
  | Fst_big_step_error h1 h2 e v :
     big_step_error e h1 v h2 ->
     big_step_error (EFst e) h1 v h2
  | Snd_big_step_error h1 h2 e v :
     big_step_error e h1 v h2 ->
     big_step_error (ESnd e) h1 v h2
  | If_big_step_error_cond h1 h2 e e1 e2 v :
     big_step_error e h1 v h2 ->
     big_step_error (EIf e e1 e2) h1 v h2
  | If_big_step_error_true h1 h2 h3 e1 e2 e3 v :
     big_step e1 h1 (VBool true) h2 ->
     big_step_error e2 h2 v h3 ->
     big_step_error (EIf e1 e2 e3) h1 v h3
  | If_big_step_error_false h1 h2 h3 e1 e2 e3 v :
     big_step e1 h1 (VBool false) h2 ->
     big_step_error e3 h2 v h3 ->
     big_step_error (EIf e1 e2 e3) h1 v h3
  | Seq_big_step_error_l h1 h2 e1 e2 v1 :
     big_step_error e1 h1 v1 h2 ->
     big_step_error (ESeq e1 e2) h1 v1 h2
  | Seq_big_step_error_r h1 h2 h3 e1 e2 v1 v2 :
     big_step e1 h1 v1 h2 ->
     big_step_error e2 h2 v2 h3 ->
     big_step_error (ESeq e1 e2) h1 v2 h3
  | Alloc_big_step_error h1 h2 e v :
     big_step_error e h1 v h2 ->
     big_step_error (EAlloc e) h1 v h2
  | Load_big_step_error h1 h2 e v :
     big_step_error e h1 v h2 ->
     big_step_error (ELoad e) h1 v h2
  | Store_big_step_error_l h1 h2 e1 e2 v :
     big_step_error e1 h1 v h2 ->
     big_step_error (EStore e1 e2) h1 v h2
  | Store_big_step_error_r h1 h2 h3 e1 e2 v1 v :
     big_step e1 h1 v1 h2 ->
     big_step_error e2 h2 v h3 ->
     big_step_error (EStore e1 e2) h1 v h3
  | Free_big_step_error h1 h2 e v :
     big_step_error e h1 v h2 ->
     big_step_error (EFree e) h1 v h2
  | Catch_big_step_error h1 h2 h3 e1 e2 v1 v2 :
     big_step_error e1 h1 v1 h2 ->
     big_step_error (EApp e2 (EVal v1)) h2 v2 h3 ->
     big_step_error (ECatch e1 e2) h1 v2 h3.

Notation sepProp := (sepProp val).

Definition wp (e : expr) (Phi EPhi : val -> sepProp) : sepProp := fun h =>
  forall hf, disjoint h hf ->
    (exists vret h',
      disjoint h' hf /\
      big_step e (union h hf) vret (union h' hf) /\
      Phi vret h') \/
    (exists vexcept h',
      disjoint h' hf /\
      big_step_error e (union h hf) vexcept (union h' hf) /\
      EPhi vexcept h').



Inductive ctx : (expr -> expr) -> Prop :=
  | Alloc_ctx : ctx EAlloc
  | Load_ctx : ctx ELoad
  | Store_ctx_l e : ctx (fun x => EStore x e)
  | Store_ctx_r v : ctx (EStore (EVal v))
  | Free_ctx : ctx EFree
  | App_l_ctx e : ctx (fun x => EApp x e)
  | App_r_ctx v : ctx (EApp (EVal v))
  | Op_l_ctx op e : ctx (fun x => EOp op x e)
  | Op_r_ctx op v : ctx (EOp op (EVal v))
  | Pair_l_ctx e : ctx (fun x => EPair x e)
  | Pair_r_ctx v : ctx (EPair (EVal v))
  | Fst_ctx : ctx EFst
  | Snd_ctx : ctx ESnd
  | If_ctx e2 e3 : ctx (fun x => EIf x e2 e3)
  | Id_ctx : ctx (fun x => x)
  | Compose_ctx k1 k2 : ctx k1 -> ctx k2 -> ctx (fun x => k1 (k2 x)).

Ltac inv_big :=
  repeat match goal with
  | _ => progress simplify_eq
  | H : big_step (EAlloc _) _ _ _ |- _ => inv H
  | H : big_step (ELoad _) _ _ _ |- _ => inv H
  | H : big_step (EStore _ _) _ _ _ |- _ => inv H
  | H : big_step (EFree _) _ _ _ |- _ => inv H
  | H : big_step (EVal _) _ _ _ |- _ => inv H
  | H : big_step (ELam _ _) _ _ _ |- _ => inv H
  | H : big_step (EApp _ _) _ _ _ |- _ => inv H
  | H : big_step (EOp _ _ _) _ _ _ |- _ => inv H
  | H : big_step (EPair _ _) _ _ _ |- _ => inv H
  | H : big_step (EFst _) _ _ _ |- _ => inv H
  | H : big_step (ESnd _) _ _ _ |- _ => inv H
  | H : big_step (EIf _ _ _) _ _ _ |- _ => inv H
  | H : big_step (ESeq _ _) _ _ _ |- _ => inv H
  | H : big_step (EThrow _) _ _ _ |- _ => inv H
  | H : big_step (ECatch _ _) _ _ _ |- _ => inv H
  | H : big_step_error (EAlloc _) _ _ _ |- _ => inv H
  | H : big_step_error (ELoad _) _ _ _ |- _ => inv H
  | H : big_step_error (EStore _ _) _ _ _ |- _ => inv H
  | H : big_step_error (EFree _) _ _ _ |- _ => inv H
  | H : big_step_error (EVal _) _ _ _ |- _ => inv H
  | H : big_step_error (ELam _ _) _ _ _ |- _ => inv H
  | H : big_step_error (EApp _ _) _ _ _ |- _ => inv H
  | H : big_step_error (EOp _ _ _) _ _ _ |- _ => inv H
  | H : big_step_error (EPair _ _) _ _ _ |- _ => inv H
  | H : big_step_error (EFst _) _ _ _ |- _ => inv H
  | H : big_step_error (ESnd _) _ _ _ |- _ => inv H
  | H : big_step_error (EIf _ _ _) _ _ _ |- _ => inv H
  end.

Lemma big_step_ctx k e v3 h1 h3 :
  ctx k ->
  big_step (k e) h1 v3 h3 <->
  exists v2 h2,
    big_step e h1 v2 h2 /\
    big_step (k (EVal v2)) h2 v3 h3.
Proof.
  intros Hk. revert e v3 h1 h3.
  induction Hk; intros e' v3 h1 h3;
    (split; [intros ?|intros (?&?&?&?)]); inv_big; eauto using big_step.
  - apply IHHk1 in H as (?&?&?&?). apply IHHk2 in H as (?&?&?&?).
    eexists _, _; split; [done|]. apply IHHk1. eauto.
  - apply IHHk1 in H0 as (?&?&?&alma).
    apply IHHk1. eexists _, _; split; [apply IHHk2|]; eauto.
Qed.

Lemma big_step_error_ctx k e v3 h1 h3 :
  ctx k ->
  big_step_error (k e) h1 v3 h3 <->
  (exists v2 h2,
    big_step e h1 v2 h2 /\
    big_step_error (k (EVal v2)) h2 v3 h3) \/
  big_step_error e h1 v3 h3.
Proof.
intros Hk. revert e v3 h1 h3.
induction Hk;intros e' v3 h1 h3;
  (split; [intros ? | intros [(?&?&?&?)|?]]);
  inv_big;eauto 100 using big_step,big_step_error.
+ apply IHHk1 in H as [(?&?&?&?)|?]; admit.
+ 

Lemma Val_wp Phi EPhi v :
  Phi v |~ wp (EVal v) Phi EPhi.
Proof.
intros h Hphi hf Hh. left. exists v,h. eauto using big_step.
Qed.


Lemma Throw_wp Phi EPhi e :
  wp e EPhi EPhi |~ wp (EThrow e) Phi EPhi.
Proof.
intros h He hf Hhf. 
edestruct He 
  as [ (v & h' & Hh' & Hbs & HPhi) | (v & h' & Hh' & Hbs & HPhi) ];eauto;
right; repeat eexists;eauto using big_step_error.
Qed.

Lemma Catch_wp Phi EPhi e1 e2 :
  wp e1 Phi (fun w => wp (EApp e2 (EVal w)) Phi EPhi)
  |~ wp (ECatch e1 e2) Phi EPhi.
Proof.
intros h He1 hf Hhf.
edestruct He1 
  as [(vret & h' & Hh' & Hbs & Hphi) | (vexcept & h' & Hh' & Hbs & Hephi)];eauto.
+ left. repeat eexists;eauto using big_step.
+ edestruct Hephi 
  as [(vret0 & h0' & Hh0' & Hbs0 & Hphi0) | (vexcept0 & h0' & Hh0' & Hbs0 & Hephi0)];
  eauto.
  - left. repeat eexists;eauto using big_step.
  - right. repeat eexists;eauto using big_step_error.
Qed.

Lemma wp_frame Phi EPhi R e :
  wp e Phi EPhi ** R |~ wp e (fun vret => Phi vret ** R) 
                             (fun vexcept => EPhi vexcept ** R).
Proof.
intros h (h1 & h2 & -> & Hdisj & Hwp & Hh2) hf Hh.
apply disjoint_union in Hh as [??].
edestruct (Hwp (union h2 hf)) 
  as [(vret & h' & Hh' & Hbs & Hphi) | (vexcept & h' & Hh' & Hbs & Hephi)];eauto.
{ apply disjoint_comm. apply disjoint_union. split;by apply disjoint_comm.  }
+ left. apply disjoint_comm, disjoint_union in Hh' as [??]. 
  exists vret, (union h' h2);split.
  { apply disjoint_union;split;[|done]. by apply disjoint_comm. }
  do 2 rewrite <- union_assoc;split;[done|].
  unfold "**". repeat eexists;eauto. by apply disjoint_comm.
+ right. apply disjoint_comm, disjoint_union in Hh' as [??].
  exists vexcept, (union h' h2);split.
  { apply disjoint_union;split;[|done]. by apply disjoint_comm. }
  do 2 rewrite <- union_assoc;split;[done|].
  repeat eexists;eauto. by apply disjoint_comm.
Qed.

Lemma Op_wp Phi EPhi op v1 v2 v :
  eval_bin_op op v1 v2 = Some v ->
  Phi v |~ wp (EOp op (EVal v1) (EVal v2)) Phi EPhi.
Proof.
intros Hop h Hphi hf Hh. left. exists v,h. eauto using big_step.
Qed.

Lemma wp_mono Phi EPhi Psi EPsi e :
  (forall vret, Phi vret |~ Psi vret) ->
  (forall vret, EPhi vret |~ EPsi vret) ->
  wp e Phi EPhi |~ wp e Psi EPsi.
Proof.
intros Hret Hexcept hf He hf' Hdisj.
destruct (He hf') 
  as [(vret & h' & Hh' & Hbs & Hvret)|(vexcept & h' & Hh' & Hbs & Hvexcept)];eauto.
+ left;repeat eexists;eauto. by apply Hret.
+ right;repeat eexists;eauto. by apply Hexcept.
Qed.

Lemma Seq_wp Phi EPhi EPhi' e1 e2 :
  wp e1 (fun _ => wp e2 Phi EPhi') EPhi |~ 
    wp (ESeq e1 e2) Phi (fun h => EPhi h \// EPhi' h).
Proof.
intros h He1 hf Hdisj.
edestruct He1 as 
  [(vret & h' & Hh' & Hbs & Hvret)|(vexcept & h' & Hh' & Hbs & Hvexcept)];eauto.
+ edestruct Hvret as
  [(vret0 & h0' & Hh0' & Hbs0 & Hvret0)|(vexcept0 & h0' & Hh0' & Hbs0 & Hvexcept0)];
  eauto.
  - left. repeat eexists;eauto using big_step.
  - right. repeat eexists; eauto using big_step_error. by right.
+ right. repeat eexists;eauto using big_step_error. by left.
Qed.

Lemma App_wp Phi EPhi x e v :
  wp (subst x v e) Phi EPhi |~ wp (EApp (EVal (VClosure x e)) (EVal v)) Phi EPhi.
Proof.
intros h Hwp hf Hdisj. 
edestruct Hwp as 
  [(vret & h' & Hh' & Hbs & Hvret)|(vexcept & h' & Hh' & Hbs & Hvexcept)];eauto.
+ left. repeat eexists;eauto using big_step.
+ right. repeat eexists;eauto. eapply App_big_step_error_l;eauto using big_step.
Qed.

Lemma Lam_wp Phi EPhi x e :
  Phi (VClosure x e) |~ wp (ELam x e) Phi EPhi.
Proof.
intros h Hphi hf Hdisj. left. eauto using big_step.
Qed.

Lemma Pair_wp Phi EPhi v1 v2 :
  Phi (VPair v1 v2) |~ wp (EPair (EVal v1) (EVal v2)) Phi EPhi.
Proof.
intros h Hphi hf Hdisj. left. repeat eexists;eauto using big_step.
Qed.

Lemma Fst_wp Phi EPhi v1 v2 :
  Phi v1 |~ wp (EFst (EVal (VPair v1 v2))) Phi EPhi.
Proof.
intros h Hphi hf Hdisj. left. repeat eexists;eauto using big_step.
Qed.

Lemma Snd_wp Phi EPhi v1 v2 :
  Phi v2 |~ wp (ESnd (EVal (VPair v1 v2))) Phi EPhi.
Proof.
intros h Hphi hf Hdisj. left. repeat eexists;eauto using big_step.
Qed.

Lemma If_true_wp Phi EPhi e2 e3 :
  wp e2 Phi EPhi |~ wp (EIf (EVal (VBool true)) e2 e3) Phi EPhi.
Proof.
intros h He2 hf Hdisj. edestruct He2 as 
  [(vret & h' & Hh' & Hbs & Hvret)|(vexcept & h' & Hh' & Hbs & Hvexcept)];eauto.
+ left. repeat eexists;eauto using big_step.
+ right. repeat eexists;eauto. 
  eapply If_big_step_error_true;eauto using big_step.
Qed.  

Lemma If_false_wp Phi EPhi e2 e3 :
  wp e3 Phi EPhi |~ wp (EIf (EVal (VBool false)) e2 e3) Phi EPhi.
Proof.
intros h He2 hf Hdisj. edestruct He2 as 
  [(vret & h' & Hh' & Hbs & Hvret)|(vexcept & h' & Hh' & Hbs & Hvexcept)];eauto.
+ left. repeat eexists;eauto using big_step.
+ right. repeat eexists;eauto. 
  eapply If_big_step_error_false; eauto using big_step.
Qed.

Lemma Store_wp Phi EPhi l v w :
  l ~> v ** (l ~> w -** Phi (VRef l)) |~ wp (EStore (EVal (VRef l)) (EVal w)) Phi EPhi.
Proof.
intros h (h1 & h2 & -> & Hdisj & Hl & Hwand) hf Hhf. unfold "~>" in Hl;subst.
apply disjoint_union in Hhf as [?%disjoint_singleton ?].
apply disjoint_singleton in Hdisj.
left.
exists (VRef l), (union (singleton l w) h2). split.
{ apply disjoint_union. by rewrite disjoint_singleton. } split.
{ replace (union (union (singleton l w) h2) hf) with
      (insert l w (union (union (singleton l v) h2) hf)) by map_solver.
  eapply Store_big_step;eauto using big_step.
  by rewrite <- union_assoc, lookup_union, lookup_singleton, Nat.eq_dec_eq. 
}
apply Hwand;[|done]. by rewrite disjoint_singleton.
Qed.

Lemma Load_wp Phi EPhi l v :
  l ~> v ** (l ~> v -** Phi v) |~ wp (ELoad (EVal (VRef l))) Phi EPhi.
Proof.
intros h (h1 & h2 & -> & Hdisj & Hl & Hwand) hf Hhf. unfold "~>" in Hl;subst.
apply disjoint_union in Hhf as [?%disjoint_singleton ?].
apply disjoint_singleton in Hdisj.
left.
exists v, (union (singleton l v) h2). split.
{ apply disjoint_union. by rewrite disjoint_singleton. } split.
{ replace (union (union (singleton l v) h2) hf) with
      (insert l v (union (union (singleton l v) h2) hf)) by map_solver.
  eapply Load_big_step;eauto using big_step. map_solver.
}
apply Hwand;[|done]. by apply disjoint_singleton.
Qed.

Lemma Alloc_wp Phi EPhi v :
  (All l, l ~> v -** Phi (VRef l)) |~ wp (EAlloc (EVal v)) Phi EPhi.
Proof.
intros h H hf Hdisj. left. unfold "-**", "~>" in H.
Check Alloc_big_step. 
exists (VRef (fresh (union hf h))), (union (singleton (fresh (union hf h)) v) h). 
split.
{ apply disjoint_union;split;[|done]. rewrite disjoint_singleton.
  apply lookup_fresh_incl, incl_union_l. } split.
{ replace (union (union (singleton (fresh (union hf h)) v) h) hf) 
    with (insert (fresh (union hf h)) v (union h hf)) by map_solver.
  replace (union hf h) with (union h hf);[|by apply disjoint_union_comm].
  eauto using big_step. }
apply H;[|done]. apply disjoint_singleton. apply lookup_fresh_incl.
rewrite disjoint_union_comm;[apply incl_union_l|by apply disjoint_comm].
Qed.

Lemma Free_wp Phi EPhi l v :
  l ~> v ** Phi v |~ wp (EFree (EVal (VRef l))) Phi EPhi.
Proof.
intros h (h1 & h2 & -> & Hdisj & H & Hphi) hf Hhf. unfold "~>" in H;subst.
apply disjoint_union in Hhf as [?%disjoint_singleton ?].
apply disjoint_singleton in Hdisj. left. Check Free_big_step.
exists v, h2. split;[done|]. split;[|done]. Check insert.
replace (union h2 hf) with (delete l (insert l v (union h2 hf))) by map_solver.
eapply Free_big_step;[|map_solver].
rewrite insert_union_l, union_singleton_l. 
apply Val_big_step.
Qed.

Lemma wp_ctx Phi EPhi EPhi' k e :
  ctx k ->
  wp e (fun vret => wp (k (EVal vret)) Phi EPhi') EPhi |~ 
    wp (k e) Phi (fun h => EPhi h \// EPhi' h).
Proof.
intros Hk h He hf Hdisj.
edestruct He as [(?&?&?&?&?)|(?&?&?&?&?)];eauto.
+ edestruct H1 as [(?&?&?&?&?)|(?&?&?&?&?)];eauto.
  - left. exists x1,x2;repeat split;eauto.
    apply big_step_ctx;[done|].
    exists x,(union x0 hf);eauto.
  - right. exists x1,x2;repeat split;eauto;[|by right].
    apply big_step_error_ctx;[done|]. left; eauto.
+ right. exists x, x0;repeat split;eauto;[|by left].
  apply big_step_error_ctx;[done|]. by right.
Qed. 