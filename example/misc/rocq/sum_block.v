(** Sum a one-word block by the index [base + i] inside a [while]. *)
From iris.proofmode Require Import proofmode.
From cjr Require Import notation primitive_laws.
From iris.prelude Require Import options.
From Coq Require Import Lia.
Open Scope expr_scope.

Definition sum_at (p : Z) : expr :=
  VarBind "i" (Val (LitV (LitInt 0)))
    (VarBind "s" (Val (LitV (LitInt 0)))
      (Seq
        (While
          (Var "i" ≤ Val (LitV (LitInt 0)))
          (Seq
            (Assign "s"
              (Var "s" + Load (Offset (Val (LitV (LitPtr p))) (Var "i"))))
            (Assign "i" (Var "i" + Val (LitV (LitInt 1))))))
        (Var "s"))).

Lemma sum_at_wp `{!cjrGS Σ} `{!invGS_gen HasLc Σ} (p : Z) :
  RawId p ↦ᵣ LitV (LitInt 4) -∗ RawId p ↦ᵦ 1 -∗
  WP sum_at p {{ v, ⌜ v = LitV (LitInt 4) ⌝ ∗
                   RawId p ↦ᵣ LitV (LitInt 4) ∗ RawId p ↦ᵦ 1 }}.
Proof.
  iIntros "Hp Hblk".
  iApply wp_var_bind. iIntros (li) "Hi".
  iApply wp_var_bind. iIntros (ls) "Hs".
  simpl.
  set (loadi := StackLoad (Val (LitV (LitStack li)))).
  set (loads := StackLoad (Val (LitV (LitStack ls)))).
  set (cond := loadi ≤ Val (LitV (LitInt 0))).
  set (idx := Offset (Val (LitV (LitPtr p))) loadi).
  set (steps := StackAssign (Val (LitV (LitStack ls))) (loads + Load idx)).
  set (stepi := StackAssign (Val (LitV (LitStack li))) (loadi + Val (LitV (LitInt 1)))).
  set (body := Seq steps stepi).
  iApply (wp_bind [SeqCtx loads]).
  iApply wp_while.
  iApply (wp_bind [IfCtx (Seq body (While cond body)) (Val (LitV LitUnit))]).
  iApply (wp_bind [BinOpLCtx LeOp (Val (LitV (LitInt 0)))]).
  iApply (wp_stack_load (StackId li) with "Hi").
  iIntros "!> _ Hi".
  iApply wp_binop; [by vm_compute|].
  iIntros "!> _".
  iApply wp_if_true.
  iApply (wp_bind [SeqCtx (While cond body)]).
  iApply (wp_bind [SeqCtx stepi]).
  iApply (wp_bind [StackAssignRCtx (LitV (LitStack ls))]).
  iApply (wp_bind [BinOpLCtx PlusOp (Load idx)]).
  iApply (wp_stack_load (StackId ls) with "Hs").
  iIntros "!> _ Hs".
  iApply (wp_bind [BinOpRCtx PlusOp (LitV (LitInt 0))]).
  iApply (wp_bind [LoadCtx]).
  iApply (wp_bind [OffsetRCtx (LitV (LitPtr p))]).
  iApply (wp_stack_load (StackId li) with "Hi").
  iIntros "!> _ Hi".
  iApply wp_offset.
  iIntros "!> _".
  assert ((p + 0)%Z = p) as -> by lia.
  iApply (wp_load with "Hp").
  iIntros "!> _ Hp".
  iApply wp_binop; [by vm_compute|].
  iIntros "!> _".
  iApply (wp_stack_assign with "Hs").
  iIntros "!> _ Hs".
  iApply wp_seq.
  iApply (wp_bind [StackAssignRCtx (LitV (LitStack li))]).
  iApply (wp_bind [BinOpLCtx PlusOp (Val (LitV (LitInt 1)))]).
  iApply (wp_stack_load (StackId li) with "Hi").
  iIntros "!> _ Hi".
  iApply wp_binop; [by vm_compute|].
  iIntros "!> _".
  iApply (wp_stack_assign with "Hi").
  iIntros "!> _ Hi".
  iApply wp_seq.
  iApply wp_while.
  iApply (wp_bind [IfCtx (Seq body (While cond body)) (Val (LitV LitUnit))]).
  iApply (wp_bind [BinOpLCtx LeOp (Val (LitV (LitInt 0)))]).
  iApply (wp_stack_load (StackId li) with "Hi").
  iIntros "!> _ Hi".
  iApply wp_binop; [by vm_compute|].
  iIntros "!> _".
  iApply wp_if_false.
  iApply wp_value'.
  iApply wp_seq.
  iApply (wp_stack_load (StackId ls) with "Hs").
  iIntros "!> _ Hs".
  iExists (LitV (LitInt 4)). iFrame "Hs".
  iExists (LitV (LitInt 1)). iFrame "Hi".
  iSplit; [done|]. iFrame.
Qed.
