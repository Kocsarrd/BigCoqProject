From pv Require Import language.
From pv Require Import proofmode.
Import language_notation hoare_notation.

Definition dec_list : val :=
  recclosure: "dec_list" "l" =>
    match: "l" with
    | NONE => VUnit
    | SOME "p" =>
        let: "x" := EFst "p" in
        let: "l" := !(ESnd "p") in
        if: "x" =: 0
          then EThrow tt 0
          else "x" <- !"x" -: 1;;
               "dec_list" "l"
    end.

Fixpoint is_list (v : val) (l : list nat) : sepProp :=
  match l with
  | [] => @[ v = NONEV ]
  | n :: l' => Ex p v',
      @[ v = SOMEV (VRef p, v') ] **
      p ~> VNat n **
      is_list v' l'
  end.
