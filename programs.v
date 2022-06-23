From pv Require Import language.
From pv Require Import proofmode.
Import language_notation hoare_notation.

Fixpoint alloc_list (l : list nat) : val :=
  closure: "_" =>
    match l with
    | [] => NONE
    | n :: l' =>
        let: "l'" := alloc_list l' () in
        let: "l" := alloc (n, "l'") in
        SOME "l"
    end.

Definition dec_list : val :=
  recclosure: "dec_list" "l" =>
    match: "l" with
    | NONE => ()
    | SOME "p" =>
        let: "x" := fst !"p" in
        let: "l" := snd !"p" in
        if: "x" =: 0
          then throw tt ()
          else "p" <- ("x" -: 1, "l");;
               "dec_list" "l"
    end.

Definition main (l : list nat) : val :=
  closure: "_" =>
    let: "l" := alloc_list l () in
    (dec_list "l";; "l")
      catch: tt "_" => "l".

Fixpoint is_list (l : list nat) (v : val) : sepProp :=
  match l with
  | [] => @[ v = NONEV ]
  | n :: l' => Ex p v',
      @[ v = SOMEV (VRef p) ] **
      p ~> (% VNat n, v' %) **
      is_list l' v'
  end.

Lemma alloc_list_spec l :
  {{ EMP }}
    alloc_list l ()
  {{ v, is_list l v }}
  {{ _ _, FALSE }}.
Proof.
  iIntros "_".
  iInduction l as [| n l'] "IH"; simpl; iApply App_wp.
  - by iApply InjL_wp.
  - iApply Let_wp. iApply "IH"; iSplit.
    + iIntros (v') "Hv'". iApply Let_wp.
      iApply Pair_wp. iApply Alloc_wp; iIntros (p) "Hp".
      iApply InjR_wp. eauto with iFrame.
    + by iIntros (??) "?".
Qed.

Local Notation positive := (fun x => x ≠ 0).

Lemma dec_list_spec l v :
  {{ is_list l v }}
    dec_list v
  {{ vret, @[ vret = () ] **
           @[ Forall positive l ] **
           is_list (map pred l) v }}
  {{ t vex, @[ t = tt ] ** @[ vex = () ] **
            Ex l1 l2, @[ l = l1 ++ 0 :: l2 ] **
                      @[ Forall positive l1 ] **
                      is_list (map pred l1 ++ 0 :: l2) v }}.
Proof.
  iIntros "Hv".
  iInduction l as [| n l'] "IH" forall (v); simpl; iApply AppRec_wp.
  - iDestruct "Hv" as %->. iApply Match_InjL_wp. by iApply Val_wp.
  - iDestruct "Hv" as (p v' ->) "(Hp & Hv')".
    iApply Match_InjR_wp.
    iApply Let_wp. iApply Load_wp; iIntros "{$Hp} Hp". iApply Fst_wp.
    iApply Let_wp. iApply Load_wp; iIntros "{$Hp} Hp". iApply Snd_wp.
    iApply Op_wp. destruct (n =? 0) eqn: Hn.
    + apply beq_nat_true in Hn as ->.
      iApply If_true_wp. iApply Throw_Val_wp. do 2 (iSplit; [done |]).
      iExists [], l'; simpl; eauto 6 with iFrame.
    + apply beq_nat_false in Hn.
      iApply If_false_wp. iApply Seq_wp.
      iApply Op_wp. iApply Pair_wp. iApply Store_wp; iIntros "{$Hp} Hp".
      iApply ("IH" with "Hv'"); iSplit.
      * iIntros (vret) "(% & %Hl' & Hv')".
        replace (pred n) with (n - 1) by lia.
        eauto 8 with iFrame.
      * iIntros (t vex) "(% & % & %l1 & %l2 & -> & %Hl1 & Hv')";
          do 2 (iSplit; [done |]).
        iExists (n :: l1), l2; simpl.
        replace (pred n) with (n - 1) by lia.
        eauto 8 with iFrame.
Qed.

Lemma main_spec l :
  {{ EMP }}
    main l ()
  {{ v, @[ Forall positive l ] ** is_list (map pred l) v \//
        Ex l1 l2, @[ l = l1 ++ 0 :: l2 ] **
          is_list (map pred l1 ++ 0 :: l2) v }}
  {{ _ _, FALSE }}.
Proof.
  iIntros "_". iApply App_wp. iApply Let_wp.
  iApply (alloc_list_spec with "[//]"); iSplit.
  - iIntros (v) "Hv". iApply Catch_wp. iApply Seq_wp.
    iApply (dec_list_spec with "Hv"); iSplit.
    + iIntros (?) "(% & %Hl & Hv)". iApply Val_wp. eauto with iFrame.
    + iIntros (t ?) "(-> & % & %l1 & %l2 & -> & %Hl1 & Hv)".
      rewrite tag_dec_eq. iApply Let_Val_wp. iApply Val_wp. eauto with iFrame.
  - by iIntros (??) "?".
Qed.

Lemma main_spec' l :
  {{ @[ Forall positive l ] }}
    main l ()
  {{ v, is_list (map pred l) v }}
  {{ _ _, FALSE }}.
Proof.
  iStartProof; iIntros (Hl).
  iApply (main_spec with "[//]"); iSplit.
  - iIntros (v) "[[_ Hv] | (%l1 & %l2 & -> & ?)]"; [done |].
    apply Forall_app in Hl as [Hl1 Hl2]. by inv Hl2.
  - by iIntros (??) "?".
Qed.
