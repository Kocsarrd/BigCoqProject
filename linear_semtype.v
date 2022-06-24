From pv Require Import proofmode.

Definition TEx (t : tag) (v : val) : sepProp := Ex n, @[ v = VNat n ].

Definition ty := val -> sepProp.

Definition TMoved : ty := fun v => EMP.
Definition TUnit : ty := fun v => @[ v = VUnit ].
Definition TNat : ty := fun v => Ex n, @[ v = VNat n ].
Definition TBool : ty := fun v => Ex b, @[ v = VBool b ].

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

Definition bin_op_typed (op : bin_op) (A1 A2 B : ty) : Prop :=
  forall v1 v2,
    A1 v1 ** A2 v2 |~ Ex v, @[ eval_bin_op op v1 v2 = Some v ] ** B v.

(* ########################################################################## *)
(** * Helper lemmas and tactics *)
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

Lemma PlusOp_typed :
  bin_op_typed PlusOp TNat TNat TNat.
Proof.
  iIntros (v1 v2) "[[%n1 ->] [%n2 ->]]"; simpl; eauto.
Qed.

Lemma MinusOp_typed :
  bin_op_typed MinusOp TNat TNat TNat.
Proof.
  iIntros (v1 v2) "[[%n1 ->] [%n2 ->]]"; simpl; eauto.
Qed.

Lemma LeOp_typed :
  bin_op_typed LeOp TNat TNat TBool.
Proof.
  iIntros (v1 v2) "[[%n1 ->] [%n2 ->]]"; simpl; eauto.
Qed.

Lemma LtOp_typed :
  bin_op_typed LtOp TNat TNat TBool.
Proof.
  iIntros (v1 v2) "[[%n1 ->] [%n2 ->]]"; simpl; eauto.
Qed.

Lemma EqOp_Nat_typed :
  bin_op_typed EqOp TNat TNat TBool.
Proof.
  iIntros (v1 v2) "[[%n1 ->] [%n2 ->]]"; simpl; eauto.
Qed.

Lemma EqOp_Bool_typed :
  bin_op_typed EqOp TBool TBool TBool.
Proof.
  iIntros (v1 v2) "[[%b1 ->] [%b2 ->]]"; simpl; eauto.
Qed.

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

(* ########################################################################## *)
(** * Semantic typing rules *)
(* ########################################################################## *)

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

Lemma Val_typed Gamma v A :
  val_typed v A ->
  typed Gamma (EVal v) A.
Proof.
  iIntros (Hv vs) "Hvs"; simpl.
  iApply Val_wp. iSplitR; [| done]. by iApply Hv.
Qed.

Lemma Var_typed Gamma x A :
  In (x, A) Gamma ->
  typed Gamma (EVar x) A.
Proof.
  iIntros (HIn vs) "Hvs".
  iInduction Gamma as [| [y B] Gamma] "IH" forall (vs); simpl in *; [done |].
  destruct HIn as [? | HIn]; simplify_eq.
  - iDestruct "Hvs" as "[(%v & -> & Hv) Hvs]".
    iApply Val_wp. by iSplitL "Hv".
  - iDestruct "Hvs" as "[? Hvs]".
    wp_absorb "[- Hvs]". by iApply "IH".
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

Lemma Op_typed Gamma1 Gamma2 op e1 e2 A1 A2 B :
  bin_op_typed op A1 A2 B ->
  typed Gamma1 e1 A1 ->
  typed Gamma2 e2 A2 ->
  typed (Gamma1 ++ Gamma2) (EOp op e1 e2) B.
Proof.
  iIntros (Hop He1 He2 vs) "Hvs"; simpl.
  iDestruct (ctx_typed_app with "Hvs") as "[Hvs1 Hvs2]".
  iApply (He1 with "Hvs1"); ex_done; iIntros (v1) "[Hv1 ?]".
  iApply (He2 with "Hvs2"); ex_done; iIntros (v2) "[Hv2 ?]".
  iDestruct (Hop with "[$Hv1 $Hv2]") as (v Heval) "Hv".
  iApply Op_wp. iFrame.
Qed.

Lemma Pair_typed Gamma1 Gamma2 e1 e2 A1 A2 :
  typed Gamma1 e1 A1 ->
  typed Gamma2 e2 A2 ->
  typed (Gamma1 ++ Gamma2) (EPair e1 e2) (TProd A1 A2).
Proof.
  iIntros (He1 He2 vs) "Hvs"; simpl.
  iDestruct (ctx_typed_app with "Hvs") as "[Hvs1 Hvs2]".
  iApply (He1 with "Hvs1"); ex_done; iIntros (v1) "[Hv1 ?]".
  iApply (He2 with "Hvs2"); ex_done; iIntros (v2) "[Hv2 ?]".
  iApply Pair_wp. iSplitL "Hv1 Hv2"; [| done]. iExists v1, v2. by iFrame.
Qed.

Lemma LetPair_typed Gamma1 Gamma2 x1 x2 e1 e2 A1 A2 B :
  ~In x1 (ctx_dom Gamma2) ->
  ~In x2 (ctx_dom Gamma2) ->
  x1 <> x2 ->
  typed Gamma1 e1 (TProd A1 A2) ->
  typed ((x1, A1) :: (x2, A2) :: Gamma2) e2 B ->
  typed (Gamma1 ++ Gamma2) (ELetPair x1 x2 e1 e2) B.
Proof. Admitted.

Lemma If_typed Gamma1 Gamma2 e1 e2 e3 A :
  typed Gamma1 e1 TBool ->
  typed Gamma2 e2 A ->
  typed Gamma2 e3 A ->
  typed (Gamma1 ++ Gamma2) (EIf e1 e2 e3) A.
Proof.
  iIntros (He1 He2 He3 vs) "Hvs"; simpl.
  iDestruct (ctx_typed_app with "Hvs") as "[Hvs1 Hvs2]".
  iApply (He1 with "Hvs1"); ex_done; iIntros (v1) "[[%b ->] ?]". destruct b.
  - iApply If_true_wp. wp_absorb "[- Hvs2]". by iApply He2.
  - iApply If_false_wp. wp_absorb "[- Hvs2]". by iApply He3.
Qed.

Lemma Seq_typed Gamma1 Gamma2 e1 e2 A B :
  typed Gamma1 e1 A ->
  typed Gamma2 e2 B ->
  typed (Gamma1 ++ Gamma2) (ESeq e1 e2) B.
Proof.
  iIntros (He1 He2 vs) "Hvs"; simpl.
  iDestruct (ctx_typed_app with "Hvs") as "[Hvs1 Hvs2]".
  iApply Seq_wp. iApply (He1 with "Hvs1"); ex_done; iIntros (v1) "[??]".
  wp_absorb "[- Hvs2]". iApply (He2 with "Hvs2").
Qed.

Lemma Alloc_typed Gamma e A :
  typed Gamma e A ->
  typed Gamma (EAlloc e) (TRef A).
Proof. Admitted.

Lemma LinLoad_typed Gamma e A :
  typed Gamma e (TRef A) ->
  typed Gamma (ELinLoad e) (TProd (TRef TMoved) A).
Proof. Admitted.

Lemma LinLoad_copy_typed Gamma e A :
  copy A ->
  typed Gamma e (TRef A) ->
  typed Gamma (ELinLoad e) (TProd (TRef A) A).
Proof. Admitted.

Lemma Store_typed Gamma1 Gamma2 e1 e2 A :
  typed Gamma1 e1 (TRef A) ->
  typed Gamma2 e2 A ->
  typed (Gamma1 ++ Gamma2) (EStore e1 e2) (TRef A).
Proof. Admitted.

Lemma Free_typed Gamma e A :
  typed Gamma e (TRef A) ->
  typed Gamma (EFree e) A.
Proof. Admitted.

Lemma Throw_typed Gamma t e A :
  typed Gamma e TNat ->
  typed Gamma (EThrow t e) A.
Proof. Admitted.

Lemma Catch_typed Gamma1 Gamma2 e1 t e2 A :
  typed Gamma1 e1 A ->
  typed Gamma2 e2 (TFunOnce TNat A) ->
  typed (Gamma1 ++ Gamma2) (ECatch e1 t e2) A.
Proof. Admitted.

Lemma Let_typed Gamma1 Gamma2 x e1 e2 A B :
  ~In x (ctx_dom Gamma2) ->
  typed Gamma1 e1 A ->
  typed ((x, A) :: Gamma2) e2 B ->
  typed (Gamma1 ++ Gamma2) (ELet x e1 e2) B.
Proof. Admitted.

Lemma InjL_typed Gamma e A1 A2 :
  typed Gamma e A1 ->
  typed Gamma (EInjL e) (TSum A1 A2).
Proof. Admitted.

Lemma InjR_typed Gamma e A1 A2 :
  typed Gamma e A2 ->
  typed Gamma (EInjR e) (TSum A1 A2).
Proof. Admitted.

Lemma Match_typed Gamma1 Gamma2 e x1 e1 x2 e2 A1 A2 B :
  ~In x1 (ctx_dom Gamma2) ->
  ~In x2 (ctx_dom Gamma2) ->
  typed Gamma1 e (TSum A1 A2) ->
  typed ((x1, A1) :: Gamma2) e1 B ->
  typed ((x2, A2) :: Gamma2) e2 B ->
  typed (Gamma1 ++ Gamma2) (EMatch e x1 e1 x2 e2) B.
Proof. Admitted.

Lemma copy_emp A v :
  copy A ->
  A v |~ EMP.
Proof.
  iIntros (HA) "Hv".
  by iDestruct (HA with "Hv") as "Hv".
Qed.

Lemma copy_dup A v :
  copy A ->
  A v |~ A v ** A v.
Proof.
  iIntros (HA) "Hv".
  iDestruct (HA with "Hv") as %Hv. iFrame "Hv". by iApply Hv.
Qed.

Lemma Moved_copy :
  copy TMoved.
Proof.
  by iIntros (v) "_ !% _".
Qed.

Lemma Unit_copy :
  copy TUnit.
Proof.
  by iIntros (v) "-> !% _".
Qed.

Lemma Nat_copy :
  copy TNat.
Proof.
  iIntros (v) "[%n ->] !% _"; eauto.
Qed.

Lemma Bool_copy :
  copy TBool.
Proof.
  iIntros (v) "[%b ->] !% _"; eauto.
Qed.

Lemma Prod_copy A1 A2 :
  copy A1 ->
  copy A2 ->
  copy (TProd A1 A2).
Proof.
  iIntros (HA1 HA2 v) "(%w1 & %w2 & % & Hw1 & Hw2)".
  iDestruct (HA1 with "Hw1") as "Hw1"; iDestruct "Hw1" as %Hw1.
  iDestruct (HA2 with "Hw2") as "Hw2"; iDestruct "Hw2" as %Hw2.
  iIntros "!% _"; iExists w1, w2. iSplitR; [done |].
  iSplitR; [by iApply Hw1 | by iApply Hw2].
Qed.

Lemma Sum_copy A1 A2 :
  copy A1 ->
  copy A2 ->
  copy (TSum A1 A2).
Proof.
  iIntros (HA1 HA2 v) "[%w [[% Hw] | [% Hw]]]".
  - iDestruct (HA1 with "Hw") as "Hw"; iDestruct "Hw" as %Hw.
    iIntros "!% _"; iExists w. iLeft; iSplitR; [done |]. by iApply Hw.
  - iDestruct (HA2 with "Hw") as "Hw"; iDestruct "Hw" as %Hw.
    iIntros "!% _"; iExists w. iRight; iSplitR; [done |]. by iApply Hw.
Qed.

Lemma Fun_copy A1 A2 :
  copy (TFun A1 A2).
Proof.
  by iStartProof; iIntros (v) "%Hfun !% _".
Qed.

Lemma subty_refl A :
  subty A A.
Proof.
  iIntros (v) "HA //".
Qed.

Lemma subty_trans A1 A2 A3 :
  subty A1 A2 ->
  subty A2 A3 ->
  subty A1 A3.
Proof.
  iIntros (HA12 HA23 v) "HA1". iApply HA23. by iApply HA12.
Qed.

Lemma subty_copy A :
  copy A ->
  subty A TMoved.
Proof.
  iIntros (HA v) "Hv". by iApply copy_emp.
Qed.

Lemma Fun_to_FunOnce_subty A1 A2 :
  subty (TFun A1 A2) (TFunOnce A1 A2).
Proof.
  iStartProof; iIntros (v Hfun w) "Hw". by iApply Hfun.
Qed.

Lemma Ref_subty A1 A2 :
  subty A1 A2 ->
  subty (TRef A1) (TRef A2).
Proof.
  iIntros (HA v) "(%l & %w & % & Hl & Hv)".
  iExists l, w. iSplitR; [done |]; iFrame. by iApply HA.
Qed.

Lemma Prod_subty A1 A2 B1 B2 :
  subty A1 A2 ->
  subty B1 B2 ->
  subty (TProd A1 B1) (TProd A2 B2).
Proof.
  iIntros (HA HB v) "(%w1 & %w2 & % & Hw1 & Hw2)".
  iExists w1, w2. iSplitR; [done |].
  iSplitL "Hw1"; [by iApply HA | by iApply HB].
Qed.

Lemma Sum_subty A1 A2 B1 B2 :
  subty A1 A2 ->
  subty B1 B2 ->
  subty (TSum A1 B1) (TSum A2 B2).
Proof.
  iIntros (HA HB v) "[%w [[% Hw] | [% Hw]]]".
  - iExists w. iLeft; iSplitR; [done |]. by iApply HA.
  - iExists w. iRight; iSplitR; [done |]. by iApply HB.
Qed.

Lemma Fun_subty A1 A2 B1 B2 :
  subty A2 A1 ->
  subty B1 B2 ->
  subty (TFun A1 B1) (TFun A2 B2).
Proof. Admitted.

Lemma FunOnce_subty A1 A2 B1 B2 :
  subty A2 A1 ->
  subty B1 B2 ->
  subty (TFunOnce A1 B1) (TFunOnce A2 B2).
Proof. Admitted.

Lemma subctx_refl Gamma :
  subctx Gamma Gamma.
Proof.
  iIntros (vs) "Hvs //".
Qed.

Lemma subctx_trans Gamma1 Gamma2 Gamma3 :
  subctx Gamma1 Gamma2 ->
  subctx Gamma2 Gamma3 ->
  subctx Gamma1 Gamma3.
Proof.
  iIntros (HGamma12 HGamma23 vs) "Hvs". iApply HGamma23. by iApply HGamma12.
Qed. 

Lemma subctx_cons Gamma1 Gamma2 x A1 A2 :
  subty A1 A2 ->
  subctx Gamma1 Gamma2 ->
  subctx ((x, A1) :: Gamma1) ((x, A2) :: Gamma2).
Proof.
  iIntros (HA HGamma vs) "Hvs"; simpl.
  iDestruct "Hvs" as "[(%v & % & Hv) Hvs]".
  iSplitR "Hvs"; [| by iApply HGamma].
  iExists v; iSplitR; [done |]. by iApply HA.
Qed.

Lemma subctx_swap Gamma x1 x2 A1 A2 :
  subctx ((x1, A1) :: (x2, A2) :: Gamma) ((x2, A2) :: (x1, A1) :: Gamma).
Proof.
  iIntros (vs) "Hvs"; simpl.
  iDestruct "Hvs" as "((%v1 & % & Hv1) & (%v2 & % & Hv2) & Hvs)".
  iFrame; iSplitL "Hv2"; eauto.
Qed.

Lemma subctx_copy_weakening Gamma x A :
  copy A ->
  subctx ((x, A) :: Gamma) Gamma.
Proof.
  iIntros (HA vs) "Hvs"; simpl.
  iDestruct "Hvs" as "[(%v & _ & Hv) Hvs]".
  iFrame. by iApply copy_emp.
Qed.

Lemma subctx_copy_contraction Gamma x A :
  copy A ->
  subctx ((x, A) :: Gamma) ((x, A) :: (x, A) :: Gamma).
Proof.
  iIntros (HA vs) "Hvs"; simpl.
  iDestruct "Hvs" as "[(%v & % & Hv) Hvs]". iFrame.
  iDestruct (copy_dup with "Hv") as "[Hv1 Hv2]"; [done |].
  iSplitL "Hv1"; iExists v; by iFrame.
Qed.

Lemma val_subsumption v A1 A2 :
  subty A1 A2 ->
  val_typed v A1 ->
  val_typed v A2.
Proof.
  iIntros (HA Hv) "_". iApply HA. by iApply Hv.
Qed.

Lemma subsumption Gamma1 Gamma2 e A1 A2 :
  subctx Gamma2 Gamma1 ->
  subty A1 A2 ->
  typed Gamma1 e A1 ->
  typed Gamma2 e A2.
Proof.
  iIntros (HGamma HA He vs) "Hvs".
  iApply (He with "[Hvs]"); [by iApply HGamma |]; ex_done.
  iIntros (v) "[Hv1 ?]". iSplitL "Hv1"; [| done]. by iApply HA.
Qed.

Definition terminates (e : expr) :Prop :=
  exists r h, big_step e NatMap.empty r h.

Section wp_adequacy.
  Transparent sepEntails.

  Lemma wp_adequacy Phi EPhi e :
    (EMP |~ wp e Phi EPhi) ->
    exists r h, big_step e NatMap.empty r h /\ (Phi # EPhi) r h.
  Proof.
    unfold sepEntails, wp; intros H.
    edestruct H as (r & h & _ & Hbig & HPost).
    { done. }
    { apply (NatMap.disjoint_empty NatMap.empty). }
    rewrite !NatMap.union_empty_r in Hbig. eauto.
  Qed.
End wp_adequacy.

Lemma type_soundness e A :
  typed [] e A ->
  terminates e.
Proof.
  unfold typed, terminates; simpl; intros He.
  specialize (He StringMap.empty). rewrite subst_map_empty in He.
  apply wp_adequacy in He as (r & h & Hbig & _). eauto.
Qed.
