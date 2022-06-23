From pv Require Import proofmode.

Print ty.

Definition TExcept : tag -> val -> sepProp := fun _ v =>
  (Ex n, @[ v = VNat n ]) ** TRUE.

Fixpoint sem (A : ty) (v : val) : sepProp :=
  match A with
  | TUnit => @[ v = VUnit ]
  | TNat => Ex n, @[ v = VNat n ]
  | TBool => Ex b, @[ v = VBool b ]
  | TMoved => EMP
  | TRef A => Ex l w, @[ v = VRef l ] ** l ~> w ** sem A w
  | TProd A1 A2 => Ex w1 w2, @[ v = VPair w1 w2 ] ** sem A1 w1 ** sem A2 w2
  | TSum A1 A2 => (Ex w : val, @[v = VInjL w] ** sem A1 w) \//
                  (Ex w : val, @[v = VInjR w] ** sem A2 w)
  | TFun A1 A2 => 
      @[ forall w, sem A1 w |~ 
          wp (EApp (EVal v) (EVal w)) (fun v => sem A2 v ** TRUE) TExcept ]
  | TFunOnce A1 A2 => 
      All w, sem A1 w -** wp (EApp (EVal v) (EVal w)) (fun v => sem A2 v ** TRUE) TExcept
  end.

(** Intuitively, contexts are multisets of bindings (since variables can occur
multiple times). We formalize contexts in Coq as lists. The lemma [subctx_swap]
below shows that the order does not matter. *)

Notation ty_ctx := (list (string * ty)).

(** The domain of the context. *)

Definition ctx_dom : ty_ctx -> list string := map fst.

(** Similar to week 6, we define semantic typing for contexts,
[ctx_typed Gamma vs] to say that all the variables in an environment [vs] have
types given by the type context [Gamma]. Since our types are predicates in
separation logic, [ctx_typed] is a [sepProp]. We use the separating conjunction
to ensure the ownership of all variables in the context is separate. *)

Fixpoint ctx_typed (Gamma : ty_ctx) (vs : stringmap val) : sepProp :=
  match Gamma with
  | [] => EMP
  | (x,A) :: Gamma =>
     (Ex v, @[ StringMap.lookup vs x = Some v ] ** sem A v) **
     ctx_typed Gamma vs
  end.

(** The semantic typing judgments are defined similarly to the ones from week 6,
but using separation logic entailment [|~] instead of a Coq implication. *)

Definition val_typed (v : val) (A : ty) : Prop :=
  TRUE |~ sem A v ** TRUE.

Definition typed (Gamma : ty_ctx) (e : expr) (A : ty) : Prop :=
  forall vs,
    ctx_typed Gamma vs |~ 
      wp (subst_map vs e) (fun v => sem A v ** TRUE) TExcept.

Definition copy (A : ty) : Prop :=
  forall v, sem A v |~ @[ EMP |~ sem A v ].

Definition subty (A1 A2 : ty) : Prop :=
  forall v, sem A1 v |~ sem A2 v.

(** We lift subtyping to contexts. This allows us to:

1. Have a stronger subsumption rule that also allows subtyping of the variable
   context, see [subsumption].
2. Formalize that the list is in fact a set (i.e., the order is not relevant),
   see [subctx_swap].
3. Lift the weakening and contraction rules to context subtyping, see
   [subctx_copy_weakening] and [subctx_copy_contraction]. *)

Definition subctx (Gamma1 Gamma2 : ty_ctx) : Prop :=
  forall vs, ctx_typed Gamma1 vs |~ ctx_typed Gamma2 vs.

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

(** We can extend the environment [vs] with a new binding, as long as it is
fresh. *)

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

Lemma Closure_typed x e A1 A2 :
  typed [(x,A1)] e A2 ->
  val_typed (VClosure x e) (TFun A1 A2).
Proof. 
  iIntros "%Htyped Htrue". iSplitR;[|done].
  iIntros "!% %w Hw". iApply App_wp. 
  rewrite <- subst_map_singleton.
  iApply Htyped. unfold ctx_typed;iSplitL;[|done].
  iExists w. iFrame. iPureIntro;StringMap.map_solver.
Qed. 

Lemma App_typed Gamma1 Gamma2 e1 e2 A B :
  typed Gamma1 e1 (TFunOnce A B) ->
  typed Gamma2 e2 A ->
  typed (Gamma1 ++ Gamma2) (EApp e1 e2) B.
Proof.
  iIntros "%He1 %He2 %vs Hctx" .
  iDestruct (ctx_typed_app with "Hctx") as "[Hctx1 Hctx2]";simpl.
  iApply (He1 with "Hctx1"). iSplit.
  { iIntros (v1) "[Hv1 Htrue]". iApply (He2 with "Hctx2"). iSplit.
    + iIntros (v2) "[Hv2 Htrue2]";simpl.

Qed.

Lemma Lam_typed Gamma e x A1 A2 :
  ~In x (ctx_dom Gamma) ->
  typed ((x,A1) :: Gamma) e A2 ->
  typed Gamma (ELam x e) (TFunOnce A1 A2).
Proof.
  unfold typed. iIntros (? He vs) "Hctx". simpl.
  iApply Lam_wp. iIntros (w) "HA". iApply App_wp.
  (** We need to turn the [subst] into a [substmap] so that we can [iApply]
  the hypothesis [He]. *)
  rewrite <-subst_map_insert.

  iApply He; simpl. iSplitL "HA".
  { iExists w. iFrame. iPureIntro. StringMap.map_solver. }
  by iApply ctx_typed_insert.
Qed.

Lemma If_typed Gamma1 Gamma2 e1 e2 e3 B :
  typed Gamma1 e1 TBool ->
  typed Gamma2 e2 B ->
  typed Gamma2 e3 B ->
  typed (Gamma1 ++ Gamma2) (EIf e1 e2 e3) B.
Proof.
  unfold typed. iIntros (He1 He2 He3 vs) "Hctx". simpl.
  iDestruct (ctx_typed_app with "Hctx") as "[Hctx1 Hctx2]".
  iApply (He1 with "Hctx1"). iIntros (v1) "[%b ->]". destruct b.
  - iApply If_true_wp. by iApply He2.
  - iApply If_false_wp. by iApply He3.
Qed.

Lemma Seq_typed Gamma1 Gamma2 e1 e2 A B :
  copy A ->
  typed Gamma1 e1 A ->
  typed Gamma2 e2 B ->
  typed (Gamma1 ++ Gamma2) (ESeq e1 e2) B.
Proof.
  unfold typed. iIntros (HcopyA He1 He2 vs) "Hctx". simpl.
  iDestruct (ctx_typed_app with "Hctx") as "[Hctx1 Hctx2]".
  iApply Seq_wp.
  iApply (He1 with "Hctx1"); iIntros (v1) "HA".
  iDestruct (HcopyA with "HA") as "_".
  iApply (He2 with "Hctx2").
Qed.



