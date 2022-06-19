(** * Lecture 8: The propositions of separation logic *)
From pv Require Export library.

(* REMINDER:

          #####################################################
          ###  PLEASE DO NOT DISTRIBUTE SOLUTIONS PUBLICLY  ###
          #####################################################

*)

(* ########################################################################## *)
(** * Introduction *)
(* ########################################################################## *)

(** See the file week8.md in the repository for the theoretical background
of this lecture. *)


(* ########################################################################## *)
(** * A shallow embedding of separation logic *)
(* ########################################################################## *)

(** We model the propositions of separation logic using a _shallow embedding_ in
terms of predicates over heaps. Since we want to keep our development abstract
from the language that is being used, we abstract over the type of values [V].
That is, we make [sepProp] polymorphic in [V] and use [natmap V] to represent
heaps. *)

Import NatMap.

Definition sepProp (V : Type) : Type := natmap V -> Prop.

(** We start with the separating conjunction [**]. Recall the informal
description of [P ** Q]: the heap can be split into two _disjoint_ parts, so
that the first satisfies [P] and the second satisfies [Q].

Recall that predicates are functions. So, to construct an element of type
[sepProp] (i.e., [natmap V -> Prop]) we use a lambda abstraction. *)

Definition sepSep {V} (P Q : sepProp V) : sepProp V := fun h =>
  exists h1 h2, h = union h1 h2 /\ disjoint h1 h2 /\ P h1 /\ Q h2.

(** For convenience's sake, we declare nice notation. Note that we cannot use a
single [*] as that symbol is already used for multiplication of natural
numbers. *)

Notation "P ** Q" := (sepSep P Q) (at level 80, right associativity).

(** In the same spirit as separating conjunction, we now formalize empty heap
connective the points-to connective. *)

Definition sepEmp {V} : sepProp V := fun h => h = empty.
Notation "'EMP'" := sepEmp.

Notation loc := nat (only parsing).

Definition points_to {V} (l : loc) (v : V) : sepProp V := fun h =>
  h = singleton l v.
Notation "l ~> v" := (points_to l v) (at level 20).

(** All of the logical connectives (truth, falsum, conjunction, disjunction,
implication are defined by lifting those of Coq to heap predicates. *)

Definition sepTrue {V} : sepProp V := fun _ => True.

Definition sepFalse {V} : sepProp V := fun _ => False.

Definition sepAnd {V} (P Q : sepProp V) : sepProp V := fun h =>
  P h /\ Q h.

(** Note that we cannot use the notation [P /\ Q]. That notation is already in
use for Coq's conjunction. We use the notation [P /\\ Q] to disambiguate. *)

Notation "P /\\ Q" := (sepAnd P Q) (at level 80).

Definition sepOr {V} (P Q : sepProp V) : sepProp V := fun h =>
  P h \/ Q h.

(** Again, we slightly modify the notation to avoid ambiguity. *)

Notation "P \// Q" := (sepOr P Q) (at level 85).

Definition sepImpl {V} (P Q : sepProp V) : sepProp V := fun h =>
  P h -> Q h.

Notation "P ->> Q" := (sepImpl P Q) (at level 100, Q at level 200).

(** In the same way that implication is the adjoint of conjunction, we define
the "magic wand" or "separating implication", which is the adjoint of separating
conjunction. That is, we have [P ⊢ Q -** R] iff [P ** Q ⊢ R], similar to
[P ⊢ Q ->> R] iff [P /\\ Q ⊢ R]. Semantically, you can think of [P -** Q] as
being that [Q] holds under the assumption of additional resources described by
[P]. *)

Definition sepWand {V} (P Q : sepProp V) : sepProp V := fun h =>
  forall h', disjoint h' h -> P h' -> Q (union h' h).

Notation "P -** Q" := (sepWand P Q) (at level 100, Q at level 200).

(** Finally, we lift the quantifiers [∀ x. P] and [∃ x. P] of Coq into
separation logic. These definitions are a bit more subtle, since we have to deal
with the binder [x] in [P]. As such, we represent the argument of the
quantifiers as a predicate [Phi : A -> sepProp]. *)

Definition sepForall {V A} (Phi : A -> sepProp V) : sepProp V := fun h =>
  forall x, Phi x h.

Definition sepExists {V A} (Phi : A -> sepProp V) : sepProp V := fun h =>
  exists x, Phi x h.

(** Now, to write down a quantifiers [∀ x. P] and [∃ x. P] in separation logic,
we use [sepForall (fun x => P)] and [sepExists (fun x => P)], respectively. For
convenience, we wrap these into notations [All x. P] and [Ex x. P]. These
notations make it possible for us to nest binders, e.g., to write
[All (x : nat) (y : list nat), ...]. *)

Notation "'All' x1 .. xn , P" :=
  (sepForall (fun x1 => .. (sepForall (fun xn => P)) ..))
  (at level 200, x1 binder, xn binder, right associativity).

Notation "'Ex' x1 .. xn , P" :=
  (sepExists (fun x1 => .. (sepExists (fun xn => P)) ..))
  (at level 200, x1 binder, xn binder, right associativity).

(** In order to express mathematical statements in our separation logic (e.g.,
equality, or that a number is even, ...), we will define an embedding of Coq
propositions (type [Prop]) into the propositions of our separation logic (type
[sepProp]). *)

Definition sepPure {V} (p : Prop) : sepProp V := fun h =>
  p /\ h = empty.
Notation "@[ p ]" := (sepPure p)
  (at level 20, p at level 200, format "@[  p  ]").

(** The entailment [P |~ Q] expresses that [P] implies [Q] for any heap [h]. *)

Definition sepEntails {V} (P Q : sepProp V) : Prop :=
  forall h, P h -> Q h.
Notation "P |~ Q" := (sepEntails P Q) (at level 99, Q at level 200).

(** Sometimes we need to be explicit about the type of values because the lemma
statement would otherwise be ambiguous. We introduce the [P |~@{V} Q] notation
for that. *)

Notation "P |~@{ V } Q" := (@sepEntails V P Q)
  (at level 99, Q at level 200, only parsing).


(* ########################################################################## *)
(** * The primitive proof rules of separation logic *)
(* ########################################################################## *)

(** Since all lemmas we are going to prove will be polymorphic in the type of
values [V], we use Coq's section mechanism to make all lemmas will be implicitly
polymorphic. Let use take a brief look at a simple example. *)

(** Using [Section name] we open a new section. The name is only relevant for
closing the section using [End name]. *)

Section section_example.
  (** Using [Context vars] we express that all definitions and lemmas in the
  section will be extended with [vars]. *)

  Context {A : Type}.

  (** Now we do not need to mention [{A}] in the definition, we get that from
  the [Context]. *)

  Definition my_test_def (x : A) : A := x.

  (** We can use multiple [Context] commands. Also, we can use the syntax
  [{ ..}] (as above) for implicit variables and [(..)] not explicit variables
  (as below) *)

  Context (x : A).

  Lemma my_test_lemma : my_test_def x = x.
  Proof. done. Qed.

(** After closing a [Section], all definitions and lemmas in the section will
automatically be generalized over their [Context]s. *)

End section_example.

About my_test_def. (* [A] added as an explicit argument. *)
About my_test_lemma. (* [A] and [x] added as an explicit argument. *)

(** Now we use [Section] for real to generalize all our lemmas over [V]. *)

Section sep_logic.
  Context {V : Type}.

  (** Using [Implicit Types] we tell Coq that variables starting with a certain
  prefix (followed by a number) should always be type checked with a certain
  type. We use the convention to use uppercase letters [P], [Q] and [R] (and
  thus [P1], [Q1], [R1], [P2], etc) for separation logic propositions, and
  lowercase letters [p] and [q] for Coq propositions. *)

  Implicit Types P Q R : sepProp V.
  Implicit Types p q : Prop.

  (** Let us first prove that entailment [|~] is a pre-order, i.e., it is
  reflexive and transitive. These properties are crucial to compose proofs. *)

  Lemma sepEntails_refl P :
    P |~ P.
  Proof.
    unfold sepEntails.
    intros h Hh.
    done.
  Qed.

  Lemma sepEntails_trans P Q R :
    (P |~ Q) ->
    (Q |~ R) ->
    P |~ R.
  Proof.
    (** Note that we do not have to unfold [sepEntails]: the [intros] tactic
    will do that automatically for us. *)
    intros HPQ HQR h HP. apply HQR. by apply HPQ.
  Qed.

  (** We now prove the key rules of separating conjunction:

  - Monotonicity: [(P1 |~ P2) -> (P1 ** Q |~ P2 ** Q)]
  - Commutativity: [P ** Q |~ Q ** P]
  - Associativity: [P ** (Q ** R) |~ (P ** Q) ** R]
  - The identity rules: [P |~ EMP ** P] and [EMP ** P |~ P].

  We will prove the first rules together and leave the others as exercises. *)

  Lemma sepSep_mono_l P1 P2 Q :
    (P1 |~ P2) ->
    (P1 ** Q |~ P2 ** Q).
  Proof.
    intros HP h Hh.
    unfold sepSep in Hh.
    destruct Hh as [h1 Hh].
    destruct Hh as [h2 Hh].
    destruct Hh as [Heq Hh].
    destruct Hh as [Hdisj Hh].
    destruct Hh as [HPh1 HQh2].
    (** As we have just seen, writing down this sequence of existential and
    conjunction eliminations becomes pretty tedious. It requires to invoke many
    tactics, and we have to name all the auxiliary results. Recall from week 2
    that Coq allows us to nest these [destruct]s using introduction patterns. *)
  Restart.
    intros HP h Hh.
    unfold sepSep in Hh.
    destruct Hh as [h1 [h2 [Heq [Hdisj [HPh1 HQh2]]]]].
    (** This is much shorter, but still results in a lot of brackets. Coq
    provides yet another syntax to make this more concise. *)
  Restart.
    intros HP h Hh.
    unfold sepSep in Hh.
    destruct Hh as (h1 & h2 & Heq & Hdisj & HPh1 & HQh2).
    (** Recall from week 2 that the syntax [ (x1 & x2 & ... & xn) ] is just
    sugar for [x1 [x2 [... [xn-1 xn]]]].

    And finally, recall that we can even perform the eliminations directly
    through the [intros] tactic: *)
  Restart.
    intros HP h (h1 & h2 & -> & Hdisj & HP1 & HQ).
    unfold sepSep.
    exists h1, h2.
    do 2 (split; [done|]).
    split.
    - by apply HP.
    - done.
  Restart.
    (** To make the proof even shorter, we can use [eauto], which uses all
    hypotheses (including implications, like the entailment) to perform a
    depth-first proof search. *)
    intros HP h (h1 & h2 & -> & Hdisj & HPh1 & HQh2).
    unfold sepSep. eauto 10.
  Qed.

  Lemma sepSep_comm P Q :
    P ** Q |~ Q ** P.
  Proof.
    intros h (h1 & h2 & -> & Hdisj & HP & HQ).
    exists h2, h1.
    rewrite <-(disjoint_union_comm h1) by done.
    rewrite disjoint_comm. auto.
  Qed.

  (** We will now prove the introduction and elimination rules for some of the
  ordinary logical connectives (truth, conjunction, universal quantification).

  Note that resemblance between these rules and the rules of first-order
  propositional that you might recall from your logic course. *)

  (** The introduction rule for truth *)

  Lemma sepTrue_intro P :
    P |~ sepTrue.
  Proof.
    intros h HP. unfold sepTrue.
    (** After unfolding the definition of [sepTrue], we can just use
    introduction of Truth in Coq (do [Print True] to see that the constructor
    of [True] is called [I]). *)
    apply I.
  Qed.

  (** The introduction and elimination rules for conjunction *)

  Lemma sepAnd_intro R P Q :
    (R |~ P) ->
    (R |~ Q) ->
    R |~ P /\\ Q.
  Proof.
    intros HP HQ h HR.
    unfold sepAnd.
    (** Use introduction of conjunction in Coq *)
    split.
    - (** case [P h]. *) by apply HP.
    - (** case [Q h]. *) by apply HQ.
  Qed.

  (** The introduction and elimination rules for universal quantification. *)

  Lemma sepForall_intro {A} P (Psi : A -> sepProp V) :
    (forall x, P |~ Psi x) ->
    (P |~ All x, Psi x).
  Proof.
    intros H h HP x. by apply H.
  Qed.

  Lemma sepForall_elim {A} (Phi : A -> sepProp V) x :
    (All z, Phi z) |~ Phi x.
  Proof.
    intros h HPhi. apply HPhi.
  Qed.


(* ########################################################################## *)
(** * Exercise: Primitive proof rules of separation logic *)
(* ########################################################################## *)

  (** Prove the commutativity, associativity, and identity rules of separating
  conjunction. To make your job more comfortable, it is a good idea to get
  comfortable with the introduction pattern syntax (if you are not already):

    intros (... & ... & ... & ...)

  Note that you can also nest this syntax. For example:

    intros (... & ... & (... & ... & ... & ...) & ...)

  This nesting may come in handy in some of the exercises (but is not required).
  See week 2 and the Coq cheat sheet for more information on introduction
  patterns. *)

  (** Prove the elimination rule for Falsum. You will have to unfold the
  definitions again, and use elimination of [False] in Coq. *)

  Lemma sepSep_assoc P Q R :
    P ** (Q ** R) |~ (P ** Q) ** R.
  Proof.
    intros h (h1 & h2 & -> & Hdisj1 & HP & h3 & h4 & -> & Hdisj2 & HQ & HR).
    rewrite union_assoc.
    rewrite disjoint_comm, disjoint_union in Hdisj1.
    rewrite (disjoint_comm h3), (disjoint_comm h4) in Hdisj1.
    destruct Hdisj1 as [Hdisj3 Hdisj4].
    exists (union h1 h3), h4. repeat split; [.. | done].
    - by rewrite disjoint_union.
    - unfold sepSep; eauto 6.
  Qed.

  Lemma sepSep_emp_l P :
    P |~ EMP ** P.
  Proof.
    intros h HP. exists empty, h. repeat split; [.. | done].
    - by rewrite union_empty_l.
    - apply disjoint_empty.
  Qed.

  Lemma sepSep_emp_l_inv P :
    EMP ** P |~ P.
  Proof.
    intros h (h1 & h2 & -> & Hdisj & -> & HP).
    by rewrite union_empty_l.
  Qed.

  Lemma points_to_unique l v1 v2 :
    l ~> v1 ** l ~> v2 |~@{V} sepFalse.
  Proof.
    intros h (h1 & h2 & Heq & Hdisj & -> & ->).
    rewrite disjoint_singleton, lookup_singleton in Hdisj. map_solver.
  Qed.

  Lemma sepFalse_elim P :
    sepFalse |~ P.
  Proof. by intros h H. Qed.

  (** Prove the elimination rules for conjunction. You will need to make
  use of elimination of conjunction in Coq. *)

  Lemma sepAnd_elim_l P Q :
    P /\\ Q |~ P.
  Proof. by intros h [HP HQ]. Qed.

  Lemma sepAnd_elim_r P Q :
    P /\\ Q |~ Q.
  Proof. by intros h [HP HQ]. Qed.

  (** Prove the introduction and elimination rules for disjunction. *)

  Lemma sepOr_intro_l P Q :
    P |~ P \// Q.
  Proof. intros h Hh; by left. Qed.

  Lemma sepOr_intro_r P Q :
    Q |~ P \// Q.
  Proof. intros h Hh; by right. Qed.

  Lemma sepOr_elim R P Q :
    (P |~ R) ->
    (Q |~ R) ->
    P \// Q |~ R.
  Proof. intros H1 H2 h [HP | HQ]; eauto. Qed.

  (** Prove the introduction and elimination rules for implication. *)

  Lemma sepImpl_intro P Q R :
    (P /\\ R |~ Q) ->
    R |~ P ->> Q.
  Proof. intros H h HR HP; by apply H. Qed.

  Lemma sepImpl_elim P Q :
    P /\\ (P ->> Q) |~ Q.
  Proof. intros h [HP H]; eauto. Qed.

  (** Prove the introduction and elimination rules for magic wand (note the
  similarity to those for implication above). *)

  Lemma sepWand_intro P Q R :
    (P ** R |~ Q) ->
    R |~ P -** Q.
  Proof. intros H h HR h' Hdisj HP. apply H; unfold sepSep; eauto 6. Qed.

  Lemma sepWand_elim P Q :
    P ** (P -** Q) |~ Q.
  Proof. intros h (h1 & h2 & -> & Hdisj & HP & H). by apply H. Qed.

  (* Prove the introduction and elimination rules for existential
  quantification *)

  Lemma sepExist_intro {A} (Phi : A -> sepProp V) x :
    Phi x |~ Ex z, Phi z.
  Proof. intros h HPhi; by eexists. Qed.

  Lemma sepExist_elim {A} (Phi : A -> sepProp V) Q :
    (forall x, Phi x |~ Q) ->
    (Ex z, Phi z) |~ Q.
  Proof. intros H h [z HPhi]; by apply (H z). Qed.

  (** Prove the introduction and elimination rules for pure propositions. *)

  Lemma sepPure_intro p :
    p ->
    EMP |~@{V} @[ p ].
  Proof. intros Hp h ->; by split. Qed.

  Lemma sepPure_elim p P Q :
    (p -> P |~ Q) ->
    @[ p ] ** P |~ Q.
  Proof.
    intros H h (h1 & h2 & -> & Hdisj & [Hp ->] & HP).
    rewrite union_empty_l. by apply H.
  Qed.


(* ########################################################################## *)
(** * Derived proof rules of separation logic *)
(* ########################################################################## *)

  (** So far, we have proved a number of rules for separation logic by unfolding
  the definition of the separation logic connectives and entailment. However, it
  turns out that many additional rules can be _derived_ from the rules we have
  already proved.

  Most of these rules are proven by making use of transitivity of entailment to
  combine previously derived rules. For example: *)

  (** Using the [Opaque] keyword we prohibit Coq from unfolding the given
  definitions. This prohibits both explicit unfolding (through the [unfold]
  tactic] and implicit unfolding (through tactics like [reflexivity], [intros],
  and [destruct]). We make all separation logic connectives (and the entailment)
  opaque to ensure we do not accidentally unfold them in our proofs. *)

  Opaque sepSep points_to sepEmp sepTrue sepFalse sepAnd sepOr sepImpl sepWand
    sepForall sepExists sepPure sepEntails.

  Lemma sepSep_emp_r P :
    P |~ P ** EMP.
  Proof.
    apply sepEntails_trans with (EMP ** P).
    (** Now we get two goals *)
    - (** [P |~ EMP ** P] *)
      apply sepSep_emp_l.
    - (** [EMP ** P |~ P ** EMP] *)
      apply sepSep_comm.
  Qed.

  (** Often it is needed to use transitivity multiple times. *)

  Lemma sepSep_mono_r P Q1 Q2 :
    (Q1 |~ Q2) ->
    P ** Q1 |~ P ** Q2.
  Proof.
    intros HQ. apply sepEntails_trans with (Q1 ** P).
    { apply sepSep_comm. }
    (** [Q1 ** P |~ P ** Q2] *)
    apply sepEntails_trans with (Q2 ** P).
    { apply sepSep_mono_l. done. }
    (** [Q2 ** P |~ P ** Q2] *)
    apply sepSep_comm.
  Qed.


(* ########################################################################## *)
(** * Exercise: Derived proof rules of separation logic *)
(* ########################################################################## *)

  (** Prove the following derived rules. Make sure to not unfold the definitions
  of the separation logic connectives, but only use the rules we have already
  proved. *)

  Lemma sepSep_emp_r_inv P :
    P ** EMP |~ P.
  Proof.
    apply sepEntails_trans with (EMP ** P).
    - apply sepSep_comm.
    - apply sepSep_emp_l_inv.
  Qed.

  Lemma sepSep_mono P1 P2 Q1 Q2 :
    (P1 |~ P2) ->
    (Q1 |~ Q2) -> 
    P1 ** Q1 |~ P2 ** Q2.
  Proof.
    intros HP HQ. apply sepEntails_trans with (P2 ** Q1).
    - by apply sepSep_mono_l.
    - by apply sepSep_mono_r.
  Qed.

  Lemma sepExist_intro_alt {A} P (Psi : A -> sepProp V) x :
    (P |~ Psi x) ->
    P |~ (Ex z, Psi z).
  Proof.
    intros H. apply sepEntails_trans with (Psi x); [done |].
    apply sepExist_intro.
  Qed.

  Lemma sepForall_elim_alt {A} (Phi : A -> sepProp V) Q x :
    (Phi x |~ Q) ->
    (All z, Phi z) |~ Q.
  Proof.
    intros H. apply sepEntails_trans with (Phi x); [| done].
    apply sepForall_elim.
  Qed.

  Lemma sepSep_pure_intro p P Q :
    p ->
    (P |~ Q) ->
    P |~ @[ p ] ** Q.
  Proof.
    intros Hp H. apply sepEntails_trans with (EMP ** P).
    { apply sepSep_emp_l. }
    apply sepSep_mono; [| done]. by apply sepPure_intro.
  Qed.

  Lemma sepWand_pure_intro p P Q :
    (p -> P |~ Q) ->
    P |~ @[ p ] -** Q.
  Proof. intros H. apply sepWand_intro. by apply sepPure_elim. Qed.

  Lemma sepWand_pure_elim p Q :
    p ->
    (@[ p ] -** Q) |~ Q.
  Proof.
    intros Hp. apply sepEntails_trans with (@[ p ] ** (@[ p ] -** Q)).
    - apply sepSep_pure_intro; [done |]. apply sepEntails_refl.
    - apply sepWand_elim.
  Qed.


(* ########################################################################## *)
(** * Challenge: More derived rules *)
(* ########################################################################## *)

  (** This lemma is quite subtle: you need to combine the rules for
  commutativity and associativity, and possibly (but not necessarily)
  monotonicity. It is best to first work out a proof on paper, and then do it in
  Coq. *)

  Lemma sepSep_assoc' P Q R :
    (P ** Q) ** R |~ P ** (Q ** R).
  Proof.
    apply sepEntails_trans with (R ** (P ** Q)).
    { apply sepSep_comm. }
    apply sepEntails_trans with ((R ** P) ** Q).
    { apply sepSep_assoc. }
    apply sepEntails_trans with (Q ** (R ** P)).
    { apply sepSep_comm. }
    apply sepEntails_trans with ((Q ** R) ** P).
    { apply sepSep_assoc. }
    apply sepSep_comm.
  Qed.

  (** Prove that existential quantification and separating conjunction are
  distributive. One direction is easy the other is surprisingly subtle (though,
  our answer is only 4 lines of Coq). *)

  Lemma sepExists_sep {A} P (Psi : A -> sepProp V) :
    (Ex x, P ** Psi x) |~ P ** (Ex x, Psi x).
  Proof.
    apply sepExist_elim; intros x.
    apply sepSep_mono_r. apply sepExist_intro.
  Qed.

  Lemma sepSep_exists {A} P (Psi : A -> sepProp V) :
    P ** (Ex x, Psi x) |~ (Ex x, P ** Psi x).
  Proof.
    apply sepEntails_trans with (P ** (P -** Ex x, P ** Psi x)).
    - apply sepSep_mono_r. apply sepExist_elim; intro x.
      apply sepWand_intro. apply (sepExist_intro (fun x => P ** Psi x)).
    - apply sepWand_elim.
  Qed.


(* ########################################################################## *)
(** * Challenge: Fixpoints in separation logic *)
(* ########################################################################## *)

  (** In this exercise we study fixpoint combinators for least and greatest
  fixpoints in separation logic. These fixpoint combinators generalize Church
  encodings, or if you are more mathematically inclined, the Knaster-Tarski
  fixpoint theorem. *)

  (** Let us first recap basic Church encodings. To define recursive types in
  Coq, one can use Church encodings. For example, the type of natural numbers
  can be defined as: *)

  Definition cnat_v1 := forall A : Type, (A -> A) -> A -> A.

  Definition O_v1 : cnat_v1 := fun A f a => a.
  Definition S_v1 (x : cnat_v1) : cnat_v1 := fun A f a => f (x A f a).

  (** This idea can be generalized to any functor [F]. For the case of natural
  numbers, [F] will be [F X := X + 1]. *)

  Definition church_least_fixpoint (F : Type -> Type) : Type :=
    forall A : Type, (F A -> A) -> A.

  Definition cnat_v2 := church_least_fixpoint (fun X => sum X unit).
  Definition O_v2 : cnat_v2 := fun A f => f (inr tt).
  Definition S_v2 (x : cnat_v2) : cnat_v2 := fun A f => f (inl (x A f)).

  (** In a similar way, we can define inductive predicates, but instead of
  quantifying over a type [A : Type], we quantify over a predicate
  [phi : nat -> Prop]. (To compare with Knaster-Tarski, think of [A -> Prop]
  as being sets with elements [A].) *)

  Definition ceven_v1 (x : nat) : Prop :=
    forall phi : nat -> Prop,
      phi 0 -> (forall y, phi y -> phi (S (S y))) -> phi x.
  Lemma ceven_v1_0 : ceven_v1 0.
  Proof. intros phi H0 HSS. apply H0. Qed.
  Lemma ceven_v1_SS n : ceven_v1 n -> ceven_v1 (S (S n)).
  Proof. intros Heven phi H0 HSS. apply HSS. by apply Heven. Qed.

  (** We can generalize this to any functor [F]. For the case of even numbers,
  [F] will be [F phi x := x = 0 \/ exists x', x = S (S x') /\ phi x']. *)

  Definition church_least_predicate {A}
      (F : (A -> Prop) -> (A -> Prop)) (x : A) : Prop :=
    forall phi : A -> Prop,
      (forall y, F phi y -> phi y) -> phi x.
  Definition ceven_v2 : nat -> Prop :=
    church_least_predicate (fun phi x =>
      x = 0 \/ exists x', x = S (S x') /\ phi x').
  Lemma ceven_v2_0 : ceven_v2 0.
  Proof. intros phi H. apply H. by left. Qed.
  Lemma ceven_v2_SS n : ceven_v2 n -> ceven_v2 (S (S n)).
  Proof.
    intros Heven phi H. apply H. right. exists n; split; [done|].
    by apply Heven.
  Qed.

  (** We now generalize [church_least_predicate] to construct predicates in
  separation logic, i.e., [A -> sepProp V]. *)

  Section fixpoints.
    Context {A} (F : (A -> sepProp V) -> (A -> sepProp V)).

    (** We need monotonicy in the proofs. This is standard for Church encodings
    and Knaster-Tarski-like theorems. *)

    Context (F_mono : forall (Psi1 Psi2 : A -> sepProp V),
      (forall x, Psi1 x |~ Psi2 x) ->
      forall x, F Psi1 x |~ F Psi2 x).

    Definition least_fixpoint (x : A) : sepProp V :=
      All Psi : A -> sepProp V,
        @[ forall x, F Psi x |~ Psi x ] -** Psi x.

    (** Prove that [least_fixpoint] is actually a fixpoint. That means,
    [F least_fixpoint] is the same as [least_fixpoint]. We express this using
    entailments in both directions. *)

    (** Hint: Make sure to use the derived proof rules of separation logic.
    Especially [sepForall_elim_alt], [sepWand_pure_intro], [sepWand_pure_elim]
    might come in handy. (You can do without, but then you likely have to use
    transitivity of entailment many times.) *)

    Lemma least_fixpoint_unfold_2 x :
      F least_fixpoint x |~ least_fixpoint x.
    Proof.
      apply sepForall_intro; intros Psi.
      apply sepWand_pure_intro; intros HF.
      apply sepEntails_trans with (F Psi x); [| apply HF].
      apply F_mono; intros y.
      apply sepForall_elim_alt with Psi.
      by apply sepWand_pure_elim.
    Qed.

    (** Hint: The key step is to instantiate the [All Psi : A -> sepProp V] in
    the right way. The lemma [least_fixpoint_unfold_2] might come in handy
    in this proof. *)

    Lemma least_fixpoint_unfold_1 x :
      least_fixpoint x |~ F least_fixpoint x.
    Proof.
      apply sepForall_elim_alt with (F least_fixpoint).
      apply sepWand_pure_elim; intros y.
      apply F_mono, least_fixpoint_unfold_2.
    Qed.

    (** The basic induction principle for least fixpoints: as inductive
    hypothesis, it allows to assume the statement to prove below exactly one
    application of [F]. *)

    Lemma least_fixpoint_iter (Psi : A -> sepProp V) :
      (forall y, F Psi y |~ Psi y) ->
      forall x, least_fixpoint x |~ Psi x.
    Proof.
      intros HF x.
      apply sepForall_elim_alt with Psi.
      by apply sepWand_pure_elim.
    Qed.

    (** Dually, we can also define the greatest fixpoint of [F]. *)

    Definition greatest_fixpoint (x : A) : sepProp V :=
      Ex Psi : A -> sepProp V,
        @[ forall x, Psi x |~ F Psi x ] ** Psi x.

    (** Now prove that the greatest fixpoint is in fact a fixpoint. The
    following proofs are essentially dual to those for least fixpoints
    (since [All]/[Ex] and [-**] and [**] are swapped. *)

    Lemma greatest_fixpoint_unfold_1 x :
      greatest_fixpoint x |~ F greatest_fixpoint x.
    Proof.
      apply sepExist_elim; intros Psi.
      apply sepPure_elim; intros HF.
      apply sepEntails_trans with (F Psi x); [apply HF |].
      apply F_mono; intros y.
      apply sepExist_intro_alt with Psi.
      apply sepSep_pure_intro; [done | apply sepEntails_refl].
    Qed.

    Lemma greatest_fixpoint_unfold_2 x :
      F greatest_fixpoint x |~ greatest_fixpoint x.
    Proof.
      apply sepExist_intro_alt with (F greatest_fixpoint).
      apply sepSep_pure_intro; [| apply sepEntails_refl]; intros y.
      apply F_mono, greatest_fixpoint_unfold_1.
    Qed.

    (** The following lemma provides basic coinduction capabilities, by
    requiring to reestablish the coinduction hypothesis after exactly one
    step. *)

    Lemma greatest_fixpoint_coiter (Psi : A -> sepProp V) :
      (forall y, Psi y |~ F Psi y) ->
      forall x, Psi x |~ greatest_fixpoint x.
    Proof.
      intros HF x.
      apply sepExist_intro_alt with Psi.
      apply sepSep_pure_intro; [done | apply sepEntails_refl].
    Qed.
  End fixpoints.
End sep_logic.
