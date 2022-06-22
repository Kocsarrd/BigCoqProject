From pv Require Import language.
From pv Require Import proofmode.
Import language_notation hoare_notation.

Definition dec_list : val :=
  recclosure: "dec_list" "l" =>
    match: "l" with
    | NONE => VUnit
    | SOME "p" =>
        let: "x" := EFst !"p" in
        let: "l" := ESnd !"p" in
        if: "x" =: 0
          then EThrow tt ()
          else "p" <- ("x" -: 1, "l");;
               "dec_list" "l"
    end.

Fixpoint is_list (l : list nat) (v : val) : sepProp :=
  match l with
  | [] => @[ v = NONEV ]
  | n :: l' => Ex p v',
      @[ v = SOMEV (VRef p) ] **
      p ~> (% VNat n, v' %) **
      is_list l' v'
  end.

Lemma dec_list_spec l v :
  {{ is_list l v }}
    dec_list v
  {{ vret, @[ vret = () ] ** is_list (map pred l) v }}
  {{ t vex, @[ t = tt /\ vex = () ] **
            Ex l1 l2, @[ l = l1 ++ l2 ] **
                      is_list (map pred l1 ++ l2) v }}.
Proof.
  iIntros "Hv".
  iInduction l as [| n l'] "IH" forall (v); simpl; iApply AppRec_wp.
  - iDestruct "Hv" as %->. iApply Match_InjL_wp. by iApply Val_wp.
  - iDestruct "Hv" as (p v' ->) "(Hp & Hv')".
    iApply Match_InjR_wp.
    iApply Let_wp. iApply Load_wp; iIntros "{$Hp} Hp". iApply Fst_wp.
    iApply Let_wp. iApply Load_wp; iIntros "{$Hp} Hp". iApply Snd_wp.
    iApply Op_wp. destruct (n =? 0) eqn: Hn.
    + iApply If_true_wp. iApply Throw_Val_wp. iSplit; [done |].
      iExists [], (n :: l'); simpl; eauto 6 with iFrame.
    + iApply If_false_wp. iApply Seq_wp.
      iApply Op_wp. iApply Pair_wp. iApply Store_wp; iIntros "{$Hp} Hp".
      iApply ("IH" with "Hv'"); iSplit.
      * iIntros (v) "[% Hv']".
        replace (pred n) with (n - 1) by lia.
        eauto with iFrame.
      * iIntros (t v) "(% & %l1 & %l2 & -> & Hv')". iSplit; [done |].
        iExists (n :: l1), l2; simpl.
        replace (pred n) with (n - 1) by lia.
        eauto 6 with iFrame.
Qed.
