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

Fixpoint subst_map (vs : stringmap val) (e : expr) : expr :=
  match e with
  | EVal _ => e
  | EVar y =>
     match StringMap.lookup vs y with
     | Some v => EVal v
     | None => e
     end
  | ELam y e => ELam y (subst_map (StringMap.delete y vs) e)
  | ERec f y e =>
     ERec f y (subst_map (StringMap.delete y (StringMap.delete f vs)) e)
  | EApp e1 e2 => EApp (subst_map vs e1) (subst_map vs e2)
  | EOp op e1 e2 => EOp op (subst_map vs e1) (subst_map vs e2)
  | EPair e1 e2 => EPair (subst_map vs e1) (subst_map vs e2)
  | EFst e => EFst (subst_map vs e)
  | ESnd e => ESnd (subst_map vs e)
  | EIf e1 e2 e3 => EIf (subst_map vs e1) (subst_map vs e2) (subst_map vs e3)
  | ESeq e1 e2 => ESeq (subst_map vs e1) (subst_map vs e2)
  | EAlloc e => EAlloc (subst_map vs e)
  | EStore e1 e2 => EStore (subst_map vs e1) (subst_map vs e2)
  | ELoad e => ELoad (subst_map vs e)
  | EFree e => EFree (subst_map vs e)
  | EThrow t e => EThrow t (subst_map vs e)
  | ECatch e1 t e2 => ECatch (subst_map vs e1) t (subst_map vs e2)
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
