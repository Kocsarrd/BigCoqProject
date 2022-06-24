From pv Require Import proofmode.

Definition EPhi (t : tag) (v : val) : sepProp :=
  (Ex n, @[ v = VNat n ]) ** TRUE.

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
  @[ forall w, A1 w |~ wp (EApp (EVal v) (EVal w)) A2 EPhi ].
Definition TFunOnce (A1 A2 : ty) : ty := fun v =>
  All w, A1 w -** wp (EApp (EVal v) (EVal w)) A2 EPhi.

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
  | (x, A) :: Gamma =>
      (Ex v, @[ StringMap.lookup vs x = Some v ] ** A v) **
      ctx_typed Gamma vs
  end.

(** The semantic typing judgments are defined similarly to the ones from week 6,
but using separation logic entailment [|~] instead of a Coq implication. *)

Definition val_typed (v : val) (A : ty) : Prop :=
  TRUE |~ A v ** TRUE.

Definition typed (Gamma : ty_ctx) (e : expr) (A : ty) : Prop :=
  forall vs,
    ctx_typed Gamma vs |~
      wp (subst_map vs e) (fun v => A v ** TRUE) EPhi.

Definition copy (A : ty) : Prop :=
  forall v, A v |~ @[ EMP |~ A v ].

Definition subty (A1 A2 : ty) : Prop :=
  forall v, A1 v |~ A2 v.

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
