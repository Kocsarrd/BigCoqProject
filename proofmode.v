From iris.proofmode Require Export tactics.
From pv Require Export language.

(* ########################################################################## *)
(** Make the proof mode work *)
(* ########################################################################## *)

(** Iris needs a version of pure that is absorbing, whereas ours is affine. We
thus wrap it. Iris also needs a persistence modality. Since we do not have
persistent resources in our logic, we define it to forget all resources.
Semantically, our definition is equivalent to [fun h => P NatMap.empty]. *)

Definition sepPure' (p : Prop) : sepProp := @[ p ] ** sepTrue.
Definition sepPersistently (P : sepProp) : sepProp := sepPure' (EMP |~ P).

Lemma sepPure'_intro (p : Prop) (P : sepProp) : p -> P |~ sepPure' p.
Proof.
  intros. eapply sepEntails_trans; [apply sepSep_emp_l|apply sepSep_mono].
  - by apply sepPure_intro.
  - apply sepTrue_intro.
Qed.
Lemma sepPure'_elim (p : Prop) (P : sepProp) :
  (p -> sepPure' True |~ P) -> sepPure' p |~ P.
Proof.
  unfold sepPure'. intros HP. apply sepPure_elim; intros.
  eapply sepEntails_trans; [|by apply HP].
  eapply sepEntails_trans; [apply sepSep_emp_l|].
  by apply sepSep_mono_l, sepPure_intro.
Qed.

Lemma sepAnd_mono (P1 P2 Q1 Q2 : sepProp) :
  (P1 |~ P2) -> (Q1 |~ Q2) -> P1 /\\ Q1 |~ P2 /\\ Q2.
Proof.
  intros. apply sepAnd_intro;
    eauto 2 using sepAnd_elim_l, sepAnd_elim_r, sepEntails_trans.
Qed.
Lemma sepOr_mono (P1 P2 Q1 Q2 : sepProp) :
  (P1 |~ P2) -> (Q1 |~ Q2) -> P1 \// Q1 |~ P2 \// Q2.
Proof.
  intros. apply sepOr_elim;
    eauto 2 using sepOr_intro_l, sepOr_intro_r, sepEntails_trans.
Qed.
Lemma sepImpl_mono (P1 P2 Q1 Q2 : sepProp) :
  (P2 |~ P1) -> (Q1 |~ Q2) -> (P1 ->> Q1) |~ (P2 ->> Q2).
Proof.
  intros. apply sepImpl_intro. apply sepEntails_trans with Q1; [|done].
  eapply sepEntails_trans; [|apply sepImpl_elim].
  by apply sepAnd_mono, sepEntails_refl.
Qed.
Lemma sepWand_mono (P1 P2 Q1 Q2 : sepProp) :
  (P2 |~ P1) -> (Q1 |~ Q2) -> (P1 -** Q1) |~ (P2 -** Q2).
Proof.
  intros. apply sepWand_intro. apply sepEntails_trans with Q1; [|done].
  eapply sepEntails_trans; [|apply sepWand_elim].
  by apply sepSep_mono, sepEntails_refl.
Qed.
Lemma sepImpl_revert (P1 P2 Q : sepProp) :
  (P1 |~ P2 ->> Q) -> (P1 /\\ P2 |~ Q).
Proof.
  intros H. eapply sepEntails_trans; [|apply sepImpl_elim].
  apply sepAnd_intro; [apply sepAnd_elim_r|].
  by eapply sepEntails_trans; [apply sepAnd_elim_l|].
Qed.

Lemma sepEntails_emp_exist {A} (Phi : A -> sepProp) :
  (EMP |~ Ex x, Phi x) -> (exists x, EMP |~ Phi x).
Proof.
  intros HPhi. destruct (HPhi NatMap.empty) as [x ?]; [done|].
  exists x. by intros h ->.
Qed.

(** Define setoid equality and bi-entailment. *)

Global Instance sepProp_equiv : Equiv sepProp := fun P Q => (P |~ Q) /\ (Q |~ P).
Global Instance sepProp_equivalence : Equivalence (@equiv sepProp _).
Proof.
  unfold equiv, sepProp_equiv.
  split; red; intuition eauto using sepEntails_refl, sepEntails_trans.
Qed.

Canonical Structure sepPropO := discreteO sepProp.

(** Now we show that our separation logic is an instance of Iris's BI
interface. This proof is a bit clunky because 1.) some of our proof rules
slightly differently (TODO: make consistent in future years), 2.) we need to
prove all the [NonExpansive] properties, which are uninteresting in our logic
because we do not have step-indexing (TODO: add smart constructor to Iris). *)

Definition sepProp_bi_mixin :
  BiMixin
    sepEntails sepEmp sepPure' sepAnd sepOr sepImpl
    (@sepForall val) (@sepExists val) sepSep sepWand sepPersistently.
Proof.
  split.
  - split.
    + intros P. apply sepEntails_refl.
    + intros P Q R. by eapply sepEntails_trans.
  - done.
  - intros ? φ φ' [??]; split; apply sepPure'_elim; intros ?;
      apply sepPure'_intro; auto.
  - intros ? P P' [??] Q Q' [??]; split; by apply sepAnd_mono.
  - intros ? P P' [??] Q Q' [??]; split; by apply sepOr_mono.
  - intros ? P P' [??] Q Q' [??]; split; by apply sepImpl_mono.
  - intros A ? Φ Φ' HΦ; split; apply sepForall_intro; intros x;
      eapply sepForall_elim_alt, HΦ.
  - intros A ? Φ Φ' HΦ; split; apply sepExist_elim; intros x;
      eapply sepExist_intro_alt, HΦ.
  - intros ? P P' [??] Q Q' [??]; split; by apply sepSep_mono.
  - intros ? P P' [??] Q Q' [??]; split; by apply sepWand_mono.
  - intros ? P P' [??]; split; apply sepPure'_elim; intros;
      by eapply sepPure'_intro, sepEntails_trans.
  - intros φ P. apply sepPure'_intro.
  - intros φ P. apply sepPure'_elim.
  - intros P Q. apply sepAnd_elim_l.
  - intros P Q. apply sepAnd_elim_r.
  - intros P Q R. apply sepAnd_intro.
  - intros P Q. apply sepOr_intro_l.
  - intros P Q. apply sepOr_intro_r.
  - intros P Q R. apply sepOr_elim.
  - intros P Q R ?. eapply sepImpl_intro, sepEntails_trans; [|done].
    apply sepAnd_intro; auto using sepAnd_elim_l, sepAnd_elim_r.
  - intros P Q R ?. eapply sepEntails_trans; [|apply (sepImpl_elim Q)].
    apply sepAnd_intro; [by apply sepAnd_elim_r|].
    by eapply sepEntails_trans; [apply sepAnd_elim_l|].
  - intros A P Φ. apply sepForall_intro.
  - intros A Φ x. apply sepForall_elim.
  - intros A Φ x. apply sepExist_intro.
  - intros A Φ Q. apply sepExist_elim.
  - intros P P' Q Q'. apply sepSep_mono.
  - intros P. apply sepSep_emp_l.
  - intros P. apply sepSep_emp_l_inv.
  - intros P Q. apply sepSep_comm.
  - intros P Q R. apply sepSep_assoc'.
  - intros P Q R ?. apply sepWand_intro.
    by eapply sepEntails_trans; [apply sepSep_comm|].
  - intros. eapply sepEntails_trans; [apply sepSep_comm|].
    eapply sepEntails_trans; [by apply sepSep_mono_r|]. apply sepWand_elim.
  - intros P Q ?. apply sepPure'_elim; intros.
    by eapply sepPure'_intro, sepEntails_trans.
  - intros P. apply sepPure'_elim; intros.
    by apply sepPure'_intro, sepPure'_intro.
  - apply sepPure'_intro, sepEntails_refl.
  - intros P Q. apply sepImpl_revert, sepPure'_elim; intros.
    eapply sepImpl_intro, sepEntails_trans; [apply sepAnd_elim_l|].
    apply sepPure'_elim; intros. by apply sepPure'_intro, sepAnd_intro.
  - intros A Φ. apply sepPure'_elim; intros [x ?]%sepEntails_emp_exist.
    apply sepExist_intro_alt with x. by apply sepPure'_intro.
  - intros P Q. eapply sepEntails_trans; [apply sepSep_assoc'|].
    apply sepSep_mono_r, sepTrue_intro.
  - intros P Q. apply sepImpl_revert, sepPure'_elim; intros.
    eapply sepImpl_intro, sepEntails_trans; [apply sepAnd_elim_l|].
    eapply sepEntails_trans; [apply sepSep_emp_l|]. by apply sepSep_mono_l.
Qed.

Definition sepProp_bi_later_mixin :
  BiLaterMixin
    sepEntails sepPure' sepOr sepImpl
    (@sepForall val) (@sepExists val) sepSep sepPersistently id.
Proof. by eapply bi_later_mixin_id, sepProp_bi_mixin. Qed.

Canonical Structure sepPropI : bi :=
  {| bi_ofe_mixin := ofe_mixin_of sepProp;
     bi_bi_mixin := sepProp_bi_mixin;
     bi_bi_later_mixin := sepProp_bi_later_mixin |}.

(** Define a bunch of instances so that the Iris Proof Mode understands our
(affine) version of pure, as well as our [sepTrue] and [sepFalse] connectives
(which are instances of pure in Iris). *)

Global Instance sepPure_affine p : Affine (@[ p ] : sepProp).
Proof.
  rewrite /Affine -(right_id emp%I bi_sep (@[ p ])).
  by apply sepPure_elim.
Qed.
Global Instance sepPure_persistent p : Persistent (@[ p ] : sepProp).
Proof.
  rewrite /Persistent -(right_id emp%I bi_sep (@[ p ])).
  apply sepPure_elim; intros. apply sepPure'_intro. rewrite right_id.
  by apply sepPure_intro.
Qed.

Global Instance sepTrue_absorbing : Absorbing (sepTrue : sepProp).
Proof. rewrite /Absorbing. apply sepTrue_intro. Qed.
Global Instance sepTrue_persistent : Persistent (sepTrue : sepProp).
Proof. rewrite /Persistent. apply sepPure'_intro, sepTrue_intro. Qed.

Global Instance sepFalse_affine : Affine (sepFalse : sepProp).
Proof. rewrite /Affine. apply sepFalse_elim. Qed.
Global Instance sepFalse_absorbing : Absorbing (sepFalse : sepProp).
Proof. rewrite /Absorbing. apply bi.wand_elim_r', sepFalse_elim. Qed.
Global Instance sepFalse_persistent : Persistent (sepFalse : sepProp).
Proof. rewrite /Persistent. apply sepFalse_elim. Qed.

Global Instance sepPure_into_pure p : IntoPure (@[ p ] : sepProp) p.
Proof.
  rewrite /IntoPure /bi_pure /= -{1}(right_id emp%I bi_sep (@[ p ])).
  apply sepPure_elim, sepPure'_intro.
Qed.
Global Instance sepTrue_into_pure : IntoPure (sepTrue : sepProp) True.
Proof. rewrite /IntoPure. apply bi.True_intro. Qed.
Global Instance sepFalse_into_pure : IntoPure (sepFalse : sepProp) False.
Proof. rewrite /IntoPure. apply sepFalse_elim. Qed.

Global Instance sepPure_from_pure p : FromPure true (@[ p ] : sepProp) p.
Proof.
  rewrite /FromPure /= /bi_pure /bi_affinely /= comm.
  apply sepImpl_revert. apply sepPure_elim; intros.
  apply sepImpl_intro. rewrite bi.and_elim_l. by apply sepPure_intro.
Qed.
Global Instance sepTrue_from_pure : FromPure false (sepTrue : sepProp) True.
Proof. rewrite /FromPure. apply sepTrue_intro. Qed.
Global Instance sepFalse_from_pure : FromPure false (sepFalse : sepProp) False.
Proof. rewrite /FromPure /=. apply bi.False_elim. Qed.

(** Make sure that [auto] understands our connectives. *)

Global Hint Extern 1 (environments.envs_entails _ (_ /\\ _)) => iSplit : core.
Global Hint Extern 1 (environments.envs_entails _ (_ ** _)) => iSplit : core.
Global Hint Extern 1 (environments.envs_entails _ (Ex _, _)) => iExists _ : core.
Global Hint Extern 1 (environments.envs_entails _ (_ \// _)) => iLeft : core.
Global Hint Extern 1 (environments.envs_entails _ (_ \// _)) => iRight : core.
Global Hint Extern 2 (environments.envs_entails _ (_ ** _)) => progress iFrame : iFrame.

(** When importing lemmas into the proof mode, Iris unfolds definitions too
eagerly, and unfolds our entailment relation [|~]. This happens even if we
make entailment opaque due to Coq bug https://github.com/coq/coq/issues/9135.
In Iris-based logics this problem does not occur because entailment (and all
logical operators) are sealed. Our logic is not sealed (because we want easy
access to its model in the lectures of week 8 and 9). We thus patch up Iris to
give our entailement [|~] precedence so it is not unfolded. *)

Opaque sepEntails.

Ltac iIntoEmpValid_go ::=
  first
    [(* Case [|~] *)
     notypeclasses refine (coq_tactics.into_emp_valid_here (_ |~ _) _ _)
    |(* Case [φ -> ψ] *)
     notypeclasses refine (coq_tactics.into_emp_valid_impl _ _ _ _ _);
       [(*goal for [φ] *)|iIntoEmpValid_go]
    |(* Case [∀ x : A, φ] *)
     notypeclasses refine (coq_tactics.into_emp_valid_forall _ _ _ _); iIntoEmpValid_go
    |(* Case [∀.. x : TT, φ] *)
     notypeclasses refine (coq_tactics.into_emp_valid_tforall _ _ _ _); iIntoEmpValid_go
    |(*| Case [P ⊢ Q], [P ⊣⊢ Q], [⊢ P] *)
     notypeclasses refine (coq_tactics.into_emp_valid_here _ _ _)].

Global Instance into_wand_impl_pure (Q : sepProp) φ :
  IntoWand true false (⌜ φ ⌝ → Q) (@[ φ ]) Q.
Proof.
  rewrite /IntoWand /= bi.intuitionistically_elim.
  rewrite (bi.intuitionistic (@[ _ ])) -bi.impl_wand_intuitionistically.
  apply bi.impl_mono; [|done]. rewrite bi.persistently_into_absorbingly.
  rewrite /bi_absorbingly comm. apply bi.sep_mono; [done|]. apply sepTrue_intro.
Qed.

(* ########################################################################## *)
(** Automation for our program logic *)
(* ########################################################################## *)

(** We extend Iris's [iApply] to become smarter when applying WP lemmas. We
let it 1.) automatically perform the context rule 2.) automatically performing
framing + monotonicity, i.e., let is generate a wand if the postconditions do
not match. *)

(** We first need some automation to decompose an expression into an evaluation
context and a subexpression. This works better for our "functional evaluation
contexts" than Iris's [reshape_expr] tactic. *)

Class IntoCtx (e : expr) (k : expr -> expr) (e' : expr) := {
  into_ctx_ctx : ctx k;
  into_ctx_eq : e = k e';
}.
Global Hint Mode IntoCtx ! - ! : typeclass_instances.

Global Instance into_ctx_id e : IntoCtx e (fun x => x) e.
Proof. split; eauto using ctx. Qed.
Global Instance into_ctx_app_l k e1 e2 e :
  IntoCtx e1 k e ->
  IntoCtx (EApp e1 e2) (fun x => EApp (k x) e2) e.
Proof.
  intros [? ->]; split; [|done].
  apply (Compose_ctx (λ x, EApp x _)); auto using ctx.
Qed.
Global Instance into_ctx_app_r k v1 e2 e :
  IntoCtx e2 k e ->
  IntoCtx (EApp (EVal v1) e2) (fun x => EApp (EVal v1) (k x)) e.
Proof. intros [? ->]; split; eauto using ctx. Qed.
Global Instance into_ctx_op_l k op e1 e2 e :
  IntoCtx e1 k e ->
  IntoCtx (EOp op e1 e2) (fun x => EOp op (k x) e2) e.
Proof.
  intros [? ->]; split; [|done].
  apply (Compose_ctx (λ x, EOp op x _)); auto using ctx.
Qed.
Global Instance into_ctx_op_r k op v1 e2 e :
  IntoCtx e2 k e ->
  IntoCtx (EOp op (EVal v1) e2) (fun x => EOp op (EVal v1) (k x)) e.
Proof. intros [? ->]; split; eauto using ctx. Qed.
Global Instance into_ctx_pair_l k e1 e2 e :
  IntoCtx e1 k e ->
  IntoCtx (EPair e1 e2) (fun x => EPair (k x) e2) e.
Proof.
  intros [? ->]; split; [|done].
  apply (Compose_ctx (λ x, EPair x _)); auto using ctx.
Qed.
Global Instance into_ctx_pair_r k v1 e2 e :
  IntoCtx e2 k e ->
  IntoCtx (EPair (EVal v1) e2) (fun x => EPair (EVal v1) (k x)) e.
Proof. intros [? ->]; split; eauto using ctx. Qed.
Global Instance into_ctx_fst k e e' :
  IntoCtx e k e' ->
  IntoCtx (EFst e) (fun x => EFst (k x)) e'.
Proof. intros [? ->]; split; eauto using ctx. Qed.
Global Instance into_ctx_snd k e e' :
  IntoCtx e k e' ->
  IntoCtx (ESnd e) (fun x => ESnd (k x)) e'.
Proof. intros [? ->]; split; eauto using ctx. Qed.
Global Instance into_ctx_if k e e1 e2 e' :
  IntoCtx e k e' ->
  IntoCtx (EIf e e1 e2) (fun x => EIf (k x) e1 e2) e'.
Proof.
  intros [? ->]; split; [|done].
  apply (Compose_ctx (λ x, EIf x _ _)); auto using ctx.
Qed.
Global Instance into_ctx_seq k e1 e2 e :
  IntoCtx e1 k e ->
  IntoCtx (ESeq e1 e2) (fun x => ESeq (k x) e2) e.
Proof.
  intros [? ->]; split; [|done].
  apply (Compose_ctx (λ x, ESeq x _)); auto using ctx.
Qed.
Global Instance into_ctx_alloc k e e' :
  IntoCtx e k e' ->
  IntoCtx (EAlloc e) (fun x => EAlloc (k x)) e'.
Proof. intros [? ->]; split; eauto using ctx. Qed.
Global Instance into_ctx_load k e e' :
  IntoCtx e k e' ->
  IntoCtx (ELoad e) (fun x => ELoad (k x)) e'.
Proof. intros [? ->]; split; eauto using ctx. Qed.
Global Instance into_ctx_store_l k e1 e2 e :
  IntoCtx e1 k e ->
  IntoCtx (EStore e1 e2) (fun x => EStore (k x) e2) e.
Proof.
  intros [? ->]; split; [|done].
  apply (Compose_ctx (λ x, EStore x _)); auto using ctx.
Qed.
Global Instance into_ctx_store_r k v1 e2 e :
  IntoCtx e2 k e ->
  IntoCtx (EStore (EVal v1) e2) (fun x => EStore (EVal v1) (k x)) e.
Proof. intros [? ->]; split; eauto using ctx. Qed.
Global Instance into_ctx_free k e e' :
  IntoCtx e k e' ->
  IntoCtx (EFree e) (fun x => EFree (k x)) e'.
Proof. intros [? ->]; split; eauto using ctx. Qed.

(** We now extend [iApply] and [iAssumption]. *)

Global Instance from_assumption_wp p k e e' Phi EPhi :
  IntoCtx e k e' ->
  FromAssumption p (wp e' (fun vret => wp (k (EVal vret)) Phi EPhi) EPhi)
    (wp e Phi EPhi) | 2.
Proof.
  intros [? ->]. rewrite /FromAssumption bi.intuitionistically_if_elim.
  by apply wp_ctx.
Qed.

Global Instance into_wand_wp p k e e' Phi EPhi Psi EPsi Psi' :
  IntoCtx e k e' ->
  TCIf (TCEq k id) (TCEq Psi' Psi)
    (TCEq Psi' (fun vret => wp (k (EVal vret)) Psi EPsi)) ->
  IntoWand p false (wp e' Phi EPhi)
                   ((All vret, Phi vret -** Psi' vret) /\\
                    (All t ve, EPhi t ve -** EPsi t ve)) (wp e Psi EPsi).
Proof.
  intros [? ->] HPsi. rewrite /IntoWand /= bi.intuitionistically_if_elim.
  apply sepWand_intro. rewrite -wp_ctx // comm wp_frame.
  apply wp_mono; [intros vret | intros t ve].
  - rewrite bi.and_elim_l (bi.forall_elim vret) bi.wand_elim_r.
    destruct HPsi as [-> ->| ->]; [apply Val_wp|done].
  - by rewrite bi.and_elim_r (bi.forall_elim t) (bi.forall_elim ve)
               bi.wand_elim_r.
Qed.

(** This instance should not be needed, but is a workaround for
https://gitlab.mpi-sws.org/iris/iris/-/issues/459 *)

Global Instance into_wand_wand_wp p q k e e' P P' Phi EPhi :
  IntoCtx e k e' ->
  FromAssumption q P P' ->
  IntoWand p q (P' -∗ wp e' (fun vret => wp (k (EVal vret)) Phi EPhi) EPhi)
    P (wp e Phi EPhi).
Proof.
  rewrite /FromAssumption /IntoWand. intros [? ->] ->; simpl.
  rewrite bi.intuitionistically_if_elim.
  apply bi.wand_mono; [done|]. by apply wp_ctx.
Qed.

Lemma wp_ctx' e k e' Phi EPhi :
  IntoCtx e k e' ->
  wp e' (fun vret => wp (k (EVal vret)) Phi EPhi) EPhi |~ wp e Phi EPhi.
Proof. intros [? ->]. by apply wp_ctx. Qed.


(* ########################################################################## *)
(** Disable ssreflect rewrite *)
(* ########################################################################## *)

(** Iris uses ssreflect's [rewrite] tactic. We do not want to use that in this
course, so we disable it. *)

Global Unset SsrRewrite.


(* ########################################################################## *)
(** Separation logic notations *)
(* ########################################################################## *)

Notation "'TRUE'" := sepTrue.
Notation "'FALSE'" := sepFalse.

(* ########################################################################## *)
(** Substitution *)
(* ########################################################################## *)

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

Lemma subst_subst_eq x v1 v2 e :
  subst x v1 (subst x v2 e) = subst x v2 e.
Proof.
  induction e; simpl;
    repeat (destruct (String.eq_dec _ _); simplify_eq);
    f_equal; by auto.
Qed.

Lemma subst_subst_neq x1 x2 v1 v2 e :
  x1 <> x2 ->
  subst x1 v1 (subst x2 v2 e) = subst x2 v2 (subst x1 v1 e).
Proof.
  intros. induction e; simpl;
    repeat (destruct (String.eq_dec _ _); simplify_eq);
    f_equal; by auto.
Qed.

(* ########################################################################## *)
(** Helper lemmas for wp logic *)
(* ########################################################################## *)

Opaque wp.

Lemma Seq_Val_wp Phi EPhi v1 e2 :
  wp e2 Phi EPhi |~ wp (ESeq (EVal v1) e2) Phi EPhi.
Proof.
  iIntros "He2". iApply Seq_wp. by iApply Val_wp.
Qed.

Lemma Throw_Val_wp Phi EPhi t v :
  EPhi t v |~ wp (EThrow t (EVal v)) Phi EPhi.
Proof.
  iIntros "HEPhi". iApply Throw_wp. by iApply Val_wp.
Qed.

Lemma Catch_Lam_wp Phi EPhi e1 t x e2 EPhi' :
  TCSimpl (fun t' v1 => if tag_dec t t'
                          then wp (subst x v1 e2) Phi EPhi
                          else EPhi t' v1) EPhi' ->
  wp e1 Phi EPhi' |~ wp (ECatch e1 t (ELam x e2)) Phi EPhi.
Proof.
  iIntros (<-) "He1". iApply Catch_wp.
  iApply wp_mono; [done | | done]; iIntros (t' v1) "Hwp"; simpl.
  destruct (tag_dec t t') as [<- | ?]; [| done].
  iApply Lam_wp. by iApply App_wp.
Qed.

(* ########################################################################## *)
(** Defined language constructs: let, sum, pair let, linear load *)
(* ########################################################################## *)

Notation ELet x e1 e2 := (EApp (ELam x e2) e1) (only parsing).

Notation EInjL e := (EPair (EVal (VBool true)) e).
Notation EInjR e := (EPair (EVal (VBool false)) e).

Notation VInjL v := (VPair (VBool true) v).
Notation VInjR v := (VPair (VBool false) v).

Definition sum_case :=
  VClosure "x" (ELam "f1" (ELam "f2"
    (EIf (EFst (EVar "x"))
         (EApp (EVar "f1") (ESnd (EVar "x")))
         (EApp (EVar "f2") (ESnd (EVar "x")))))).
Notation EMatch e x1 e1 x2 e2 :=
  (EApp (EApp (EApp (EVal sum_case) e) (ELam x1 e1)) (ELam x2 e2))
  (only parsing).

Definition pair_elim :=
  VClosure "x" (ELam "f"
    (EApp (EApp (EVar "f") (EFst (EVar "x"))) (ESnd (EVar "x")))).
Notation ELetPair x1 x2 e1 e2 :=
  (EApp (EApp (EVal pair_elim) e1) (ELam x1 (ELam x2 e2))) (only parsing).

Definition lin_load :=
  VClosure "l" (EPair (EVar "l") (ELoad (EVar "l"))).
Notation ELinLoad e := (EApp (EVal lin_load) e) (only parsing).

Lemma Let_wp Phi EPhi x e1 e2 Phi' :
  TCSimpl (fun v1 => wp (subst x v1 e2) Phi EPhi) Phi' ->
  wp e1 Phi' EPhi |~ wp (ELet x e1 e2) Phi EPhi.
Proof.
  iIntros (<-) "Hwp". iApply Lam_wp.
  iApply (wp_ctx (EApp _)); [constructor |].
  iApply wp_mono; [| done ..].
  iIntros (v) "Hwp". by iApply App_wp.
Qed.

Lemma Let_Val_wp Phi EPhi x v1 e2 e' :
  TCSimpl (subst x v1 e2) e' ->
  wp e' Phi EPhi |~ wp (ELet x (EVal v1) e2) Phi EPhi.
Proof.
  iIntros (<-) "Hwp". iApply Let_wp. by iApply Val_wp.
Qed.

Lemma InjL_wp Phi EPhi v :
  Phi (VInjL v) |~ wp (EInjL (EVal v)) Phi EPhi.
Proof.
  iIntros "HPhi". by iApply Pair_wp.
Qed.

Lemma InjR_wp Phi EPhi v :
  Phi (VInjR v) |~ wp (EInjR (EVal v)) Phi EPhi.
Proof.
  iIntros "HPhi". by iApply Pair_wp.
Qed.

Lemma Match_InjL_wp Phi EPhi v x1 e1 x2 e2 e' :
  TCSimpl (subst x1 v e1) e' ->
  wp e' Phi EPhi |~ wp (EMatch (EVal (VInjL v)) x1 e1 x2 e2) Phi EPhi.
Proof.
  iIntros (<-) "Hwp".
  iApply App_wp. iApply Lam_wp. iApply Lam_wp.
  iApply App_wp. iApply Lam_wp. iApply Lam_wp.
  iApply App_wp. iApply Fst_wp. iApply If_true_wp.
  iApply Snd_wp. by iApply App_wp. 
Qed.
 
Lemma Match_InjR_wp Phi EPhi v x1 e1 x2 e2 e' :
  TCSimpl (subst x2 v e2) e' ->
  wp e' Phi EPhi |~ wp (EMatch (EVal (VInjR v)) x1 e1 x2 e2) Phi EPhi.
Proof.
  iIntros (<-) "Hwp".
  iApply App_wp. iApply Lam_wp. iApply Lam_wp.
  iApply App_wp. iApply Lam_wp. iApply Lam_wp.
  iApply App_wp. iApply Fst_wp. iApply If_false_wp.
  iApply Snd_wp. by iApply App_wp.
Qed.

Lemma LetPair_wp Phi EPhi x1 x2 v1 v2 e2 e' :
  TCSimpl (subst x1 v1 (subst x2 v2 e2)) e' ->
  wp e' Phi EPhi |~ wp (ELetPair x1 x2 (EVal (VPair v1 v2)) e2) Phi EPhi.
Proof.
  iIntros (<-) "Hwp".
  iApply App_wp. iApply Lam_wp. iApply Lam_wp.
  iApply App_wp. iApply Fst_wp. iApply App_wp.
  destruct (String.eq_dec x2 x1) as [->|?].
  - iApply Lam_wp. iApply Snd_wp. iApply App_wp. 
    by rewrite subst_subst_eq.
  - iApply Lam_wp. iApply Snd_wp. iApply App_wp.
    by rewrite subst_subst_neq by congruence.
Qed.

Lemma LinLoad_wp Phi EPhi l v :
  l ~> v ** (l ~> v -** Phi (VPair (VRef l) v)) |~
  wp (ELinLoad (EVal (VRef l))) Phi EPhi.
Proof.
  iIntros "[Hl Hwand]".
  iApply App_wp. iApply Load_wp. iIntros "{$Hl} Hl".
  iApply Pair_wp. by iApply "Hwand".
Qed.

(* ########################################################################## *)
(** Notations *)
(* ########################################################################## *)

Module language_notation.
  Coercion VNat : nat >-> val.
  Coercion VBool : bool >-> val.

  Coercion EVar : string >-> expr.
  Coercion EVal : val >-> expr.
  Coercion EApp : expr >-> Funclass.

  Notation "()" := VUnit.
  Notation "( e1 , e2 , .. , en )" := (EPair .. (EPair e1 e2) .. en).
  Notation "(% v1 , v2 , .. , vn %)" := (VPair .. (VPair v1 v2) .. vn)
    (format "'[' (%  v1 ,  v2 ,  .. ,  vn  %) ']'").
  Notation "'fst' e" := (EFst e) (at level 10).
  Notation "'snd' e" := (ESnd e) (at level 10).

  Notation "'let:' x := e1 'in' e2" := (ELet x e1 e2)
    (at level 200, x at level 1, e1, e2 at level 200,
     format "'[' 'let:'  x  :=  '[' e1 ']'  'in'  '/' e2 ']'").
  Notation "e1 ;; e2" := (ESeq e1 e2)
    (at level 100, e2 at level 200,
     format "'[' '[hv' '[' e1 ']' ;;  ']' '/' e2 ']'").
  Notation "'alloc' e" := (EAlloc e) (at level 10).
  Notation "! e" := (ELoad e) (at level 9, right associativity, format "! e").
  Notation "e1 <- e2" := (EStore e1 e2) (at level 80).
  Notation "'free' e" := (EFree e) (at level 10).
  Notation "'if:' e1 'then' e2 'else' e3" := (EIf e1 e2 e3)
    (at level 200, e1, e2, e3 at level 200).

  Notation "'match:' e 'with' | 'InjL' x1 => e1 | 'InjR' x2 => e2 'end'" :=
    (EMatch e x1 e1 x2 e2)
    (e, x1, e1, x2, e2 at level 200,
     format "'[hv' 'match:'  e  'with'  '/  ' '[' |  'InjL'  x1  =>  '/  ' e1 ']'  '/' '[' |  'InjR'  x2  =>  '/  ' e2 ']'  '/' 'end' ']'").
  Notation "'match:' e 'with' | 'InjR' x1 => e1 | 'InjL' x2 => e2 'end'" :=
    (EMatch e x2 e2 x1 e1)
    (e, x1, e1, x2, e2 at level 200, only parsing).

  Notation "fun: x => e" := (ELam x e)
    (at level 200, x at level 1, e at level 200,
     format "'[' 'fun:'  x  =>  '/  ' e ']'").
  Notation "fun: x y .. z => e" := (ELam x (ELam y .. (ELam z e) ..))
    (at level 200, x, y, z at level 1, e at level 200,
     format "'[' 'fun:'  x  y  ..  z  =>  '/  ' e ']'").
  Notation "closure: x => e" := (VClosure x e)
    (at level 200, x at level 1, e at level 200,
     format "'[' 'closure:'  x  =>  '/  ' e ']'").
  Notation "closure: x y .. z => e" := (VClosure x (ELam y .. (ELam z e) ..))
    (at level 200, x, y, z at level 1, e at level 200,
     format "'[' 'closure:'  x  y  ..  z  =>  '/  ' e ']'").

  Notation "'rec:' f x => e" := (ERec f x e)
    (at level 200, f at level 1, x at level 1, e at level 200,
     format "'[' 'rec:'  f  x  =>  '/  ' e ']'").
  Notation "'rec:' f x y .. z => e" := (ERec f x (ELam y .. (ELam z e) ..))
    (at level 200, f, x, y, z at level 1, e at level 200,
     format "'[' 'rec:'  f  x  y  ..  z  =>  '/  ' e ']'").
  Notation "'recclosure:' f x => e" := (VRecClosure f x e)
    (at level 200, f at level 1, x at level 1, e at level 200,
     format "'[' 'recclosure:'  f  x  =>  '/  ' e ']'").
  Notation "'recclosure:' f x y .. z => e" :=
    (VRecClosure f x (ELam y .. (ELam z e) ..))
    (at level 200, f, x, y, z at level 1, e at level 200,
     format "'[' 'recclosure:'  f  x  y  ..  z  =>  '/  ' e ']'").

  Notation "e1 +: e2" := (EOp PlusOp e1 e2) (at level 50, left associativity).
  Notation "e1 -: e2" := (EOp MinusOp e1 e2) (at level 50, left associativity).
  Notation "e1 =: e2" := (EOp EqOp e1 e2) (at level 70, no associativity).
  Notation "e1 <=: e2" := (EOp LeOp e1 e2) (at level 70, no associativity).
  Notation "e1 <: e2" := (EOp LtOp e1 e2) (at level 70, no associativity).

  Notation "'throw' t e" := (EThrow t e)
    (at level 10, t at level 1).
  Notation "e1 'catch:' t x => e2" := (ECatch e1 t (ELam x e2))
    (at level 90, t, x at level 1, left associativity,
     format "'[hv' e1  '/  ' 'catch:'  t  x  =>  '/  ' e2 ']'").

  Notation "'let:' ( x1 , x2 ) := e1 'in' e2" := (ELetPair x1 x2 e1 e2)
    (at level 200, x1, x2 at level 1, e1, e2 at level 200,
     format "'[' 'let:'  ( x1 ,  x2 )  :=  '[' e1 ']'  'in'  '/' e2 ']'").
  Notation "!! e" := (ELinLoad e)
    (at level 9, right associativity, format "!! e").

  Notation NONE := (EInjL (EVal VUnit)) (only parsing).
  Notation NONEV := (VInjL VUnit) (only parsing).
  Notation SOME e := (EInjR e) (only parsing).
  Notation SOMEV v := (VInjR v) (only parsing).

  Notation "'match:' e 'with' | 'NONE' => e1 | 'SOME' x => e2 'end'" :=
    (EMatch e "_" e1 x e2) (e, e1, x, e2 at level 200, only parsing).
  Notation "'match:' e 'with' | 'SOME' x => e1 | 'NONE' => e2 'end'" :=
    (EMatch e "_" e2 x e1) (e, e1, x, e2 at level 200, only parsing).
End language_notation.

Module hoare_notation.
  Notation "'WP' e {{ v , Q }} {{ t w , R }}" :=
    (wp e (fun v => Q) (fun t w => R))
    (at level 20, e, Q, R at level 200, v name, t name, w name,
     format "'[hv' 'WP'  e  '/' {{  '[' v ,  '/' Q  ']' }}  '/' {{  '[' t  w ,  '/' R  ']' }} ']'").

  Notation "{{ P }} e {{ v , Q }} {{ t w , R }}" :=
    (hoare P e (fun v => Q) (fun t w => R))
    (at level 20, P, e, Q, R at level 200, v name, t name, w name,
     format "'[hv' {{  P  }} ']' '/  '  '[' e ']'  '/' '[' {{  v ,  Q  }} ']'  '/' '[' {{  t  w ,  R  }} ']'").
End hoare_notation.
