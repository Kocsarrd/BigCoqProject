From pv Require Import proofmode.

Definition TEx (t : tag) (v : val) : sepProp := Ex n, @[ v = VNat n ].

Definition ty := val -> sepProp.

Definition TUnit : ty := fun v => @[ v = VUnit ].
Definition TNat : ty := fun v => Ex n, @[ v = VNat n ].
Definition TBool : ty := fun v => Ex b, @[ v = VBool b ].
Definition TMoved : ty := fun v => EMP.

Definition TRef (A : ty) : ty := fun v =>
  Ex l w, @[ v = VRef l ] ** l ~> w ** A w.

Definition TProd (A1 A2 : ty) : ty := fun v =>
  Ex w1 w2, @[ v = VPair w1 w2 ] ** A1 w1 ** A2 w2.
Definition TSum (A1 A2 : ty) : ty := fun v =>
  Ex w, (@[ v = VInjL w ] ** A1 w) \// (@[ v = VInjR w] ** A2 w).

Definition TFun (A1 A2 : ty) : ty := fun v =>
  @[ forall w, A1 w |~ wp (EApp (EVal v) (EVal w)) (abs1 A2) (abs2 TEx) ].
Definition TFunOnce (A1 A2 : ty) : ty := fun v =>
  All w, A1 w -** wp (EApp (EVal v) (EVal w)) (abs1 A2) (abs2 TEx).

Notation ty_ctx := (list (string * ty)).

Definition ctx_dom : ty_ctx -> list string := map fst.

Fixpoint ctx_typed (Gamma : ty_ctx) (vs : stringmap val) : sepProp :=
  match Gamma with
  | [] => EMP
  | (x, A) :: Gamma =>
      (Ex v, @[ StringMap.lookup vs x = Some v ] ** A v) **
      ctx_typed Gamma vs
  end.

Fixpoint subst_map (vs : stringmap val) (e : expr) : expr :=
  match e with
  | EVal _ => e
  | EVar x =>
      match StringMap.lookup vs x with
      | Some v => EVal v
      | None => e
      end
  | ELam x e => ELam x (subst_map (StringMap.delete x vs) e)
  | ERec f x e =>
      ERec f x (subst_map (StringMap.delete x (StringMap.delete f vs)) e)
  | EApp e1 e2 => EApp (subst_map vs e1) (subst_map vs e2)
  | EOp op e1 e2 => EOp op (subst_map vs e1) (subst_map vs e2)
  | EPair e1 e2 => EPair (subst_map vs e1) (subst_map vs e2)
  | EFst e => EFst (subst_map vs e)
  | ESnd e => ESnd (subst_map vs e)
  | EIf e1 e2 e3 => EIf (subst_map vs e1) (subst_map vs e2) (subst_map vs e3)
  | ESeq e1 e2 => ESeq (subst_map vs e1) (subst_map vs e2)
  | EAlloc e => EAlloc (subst_map vs e)
  | ELoad e => ELoad (subst_map vs e)
  | EStore e1 e2 => EStore (subst_map vs e1) (subst_map vs e2)
  | EFree e => EFree (subst_map vs e)
  | EThrow t e => EThrow t (subst_map vs e)
  | ECatch e1 t e2 => ECatch (subst_map vs e1) t (subst_map vs e2)
  end.

Definition val_typed (v : val) (A : ty) : Prop :=
  EMP |~ A v.

Definition typed (Gamma : ty_ctx) (e : expr) (A : ty) : Prop :=
  forall vs, ctx_typed Gamma vs |~ wp (subst_map vs e) (abs1 A) (abs2 TEx).

Definition copy (A : ty) : Prop :=
  forall v, A v |~ @[ EMP |~ A v ].

Definition subty (A1 A2 : ty) : Prop :=
  forall v, A1 v |~ A2 v.

Definition subctx (Gamma1 Gamma2 : ty_ctx) : Prop :=
  forall vs, ctx_typed Gamma1 vs |~ ctx_typed Gamma2 vs.

(* ########################################################################## *)
(** * Helper lemmas *)
(* ########################################################################## *)

Lemma subst_map_empty e :
  subst_map StringMap.empty e = e.
Proof. induction e; simpl; by f_equal. Qed.

Lemma subst_map_insert x v vs e :
  subst_map (StringMap.insert x v vs) e
  = subst x v (subst_map (StringMap.delete x vs) e).
Proof.
  revert vs. induction e; intros vs; simpl; try (by f_equal).
  - (** Case var *)
    rewrite StringMap.lookup_delete, StringMap.lookup_insert.
    destruct (String.eq_dec _ _); simplify_eq.
    + by destruct (String.eq_dec _ _).
    + destruct (StringMap.lookup vs s) eqn:E; simpl; eauto.
      by destruct (String.eq_dec _ _).
  - (** Case lam *)
    destruct (String.eq_dec _ _); simplify_eq.
    + f_equal. f_equal. StringMap.map_solver.
    + f_equal. rewrite StringMap.delete_delete.
      destruct (String.eq_dec _ _); [done|].
      rewrite <-IHe. f_equal. StringMap.map_solver.
  - (** Case rec *)
    destruct (String.eq_dec _ _); simplify_eq.
    { do 2 f_equal. StringMap.map_solver. }
    destruct (String.eq_dec _ _); simplify_eq.
    { do 2 f_equal. StringMap.map_solver. }
    do 2 f_equal.
    do 2 rewrite StringMap.delete_insert, String.eq_dec_neq by congruence.
    rewrite IHe. do 2 f_equal. StringMap.map_solver.
Qed.

Lemma subst_map_singleton x v e :
  subst_map (StringMap.singleton x v) e = subst x v e.
Proof.
  rewrite <-StringMap.insert_empty, subst_map_insert.
  by rewrite StringMap.delete_empty, subst_map_empty.
Qed.

(* ########################################################################## *)
(** * Semantic typing rules *)
(* ########################################################################## *)

Lemma ctx_typed_app Gamma1 Gamma2 vs :
  ctx_typed (Gamma1 ++ Gamma2) vs |~
  ctx_typed Gamma1 vs ** ctx_typed Gamma2 vs.
Proof.
  iIntros "Hctx". iInduction Gamma1 as [|[x A] Gamma] "IH"; simpl.
  { by iFrame. }
  iDestruct "Hctx" as "[$ Hctx]". by iApply "IH".
Qed.

Lemma ctx_typed_insert Gamma vs x v :
  ~In x (ctx_dom Gamma) ->
  ctx_typed Gamma vs |~ ctx_typed Gamma (StringMap.insert x v vs).
Proof.
  iIntros (Hfresh) "Hctx".
  iInduction Gamma as [|[y A] Gamma] "IH"; simpl in *; [done|].
  iDestruct "Hctx" as "[(%w & %Hlookup & HA) Hctx]". iSplitL "HA".
  - iExists w. iFrame "HA". iPureIntro.
    rewrite StringMap.lookup_insert.
    destruct (String.eq_dec _ _) as [->|]; [|done].
    destruct Hfresh; auto.
  - iApply ("IH" with "[%] Hctx"). tauto.
Qed.

Ltac ex_done := iSplit; [| iIntros (??) "[??]"; by iFrame].
Tactic Notation "wp_absorb" constr(spat) :=
  iApply (absorb with spat);
    [apply wp_absorbing; intros; apply abs_absorbing | done |].

Lemma Unit_typed :
  val_typed VUnit TUnit.
Proof.
  by iIntros "_".
Qed.

Lemma Nat_typed n :
  val_typed (VNat n) TNat.
Proof.
  iIntros "_"; by iExists n.
Qed.

Lemma Bool_typed b :
  val_typed (VBool b) TBool.
Proof.
  iIntros "_"; by iExists b.
Qed.

Lemma Closure_typed x e A1 A2 :
  typed [(x, A1)] e A2 ->
  val_typed (VClosure x e) (TFun A1 A2).
Proof.
  iIntros (He) "_ !% %v Hv".
  iApply App_wp. rewrite <-subst_map_singleton.
  iApply He; simpl. iSplitL; [| done].
  iExists v; iFrame; StringMap.map_solver.
Qed.

Lemma Lam_typed Gamma x e A1 A2 :
  ~In x (ctx_dom Gamma) ->
  typed ((x, A1) :: Gamma) e A2 ->
  typed Gamma (ELam x e) (TFunOnce A1 A2).
Proof.
  iIntros (Hdom He vs) "Hvs"; simpl.
  iApply Lam_wp. iSplitL; [| done]. iIntros (v) "Hv".
  iApply App_wp. rewrite <-subst_map_insert.
  iApply He; simpl. iSplitL "Hv".
  { iExists v; iFrame; StringMap.map_solver. }
  by iApply ctx_typed_insert.
Qed.

Lemma App_typed Gamma1 Gamma2 e1 e2 A1 A2 :
  typed Gamma1 e1 (TFunOnce A1 A2) ->
  typed Gamma2 e2 A1 ->
  typed (Gamma1 ++ Gamma2) (EApp e1 e2) A2.
Proof.
  iIntros (He1 He2 vs) "Hvs"; simpl.
  iDestruct (ctx_typed_app with "Hvs") as "[Hvs1 Hvs2]".
  iApply (He1 with "Hvs1"); ex_done; iIntros (v1) "[Hv1 ?]".
  iApply (He2 with "Hvs2"); ex_done; iIntros (v2) "[Hv2 ?]".
  wp_absorb "[- Hv1 Hv2]". iApply ("Hv1" with "Hv2").
Qed.
