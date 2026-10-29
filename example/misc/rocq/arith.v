(** Sum [1] with a [while] over two [var] locals. No heap. *)
From iris.proofmode Require Import proofmode.
From cjr Require Import notation primitive_laws adequacy.
From iris.prelude Require Import options.
Open Scope expr_scope.

Definition sum_one : expr :=
  VarBind "n" (Val (LitV (LitInt 1)))
    (VarBind "s" (Val (LitV (LitInt 0)))
      (Seq
        (While
          (BinOp LeOp (Val (LitV (LitInt 1))) (Var "n"))
          (Seq
            (Assign "s" (BinOp PlusOp (Var "s") (Val (LitV (LitInt 1)))))
            (Assign "n" (BinOp MinusOp (Var "n") (Val (LitV (LitInt 1)))))))
        (Var "s"))).

Lemma sum_one_wp `{!cjrGS Σ} `{!invGS_gen HasLc Σ} :
  ⊢ WP sum_one {{ v, ⌜ v = LitV (LitInt 1) ⌝ }}.
Proof.
  iApply wp_var_bind. iIntros (ln) "Hn".
  iApply wp_var_bind. iIntros (ls) "Hs".
  simpl.
  set (loadn := StackLoad (Val (LitV (LitStack ln)))).
  set (loads := StackLoad (Val (LitV (LitStack ls)))).
  set (cond := Val (LitV (LitInt 1)) ≤ loadn).
  set (steps := StackAssign (Val (LitV (LitStack ls))) (loads + Val (LitV (LitInt 1)))).
  set (stepn := StackAssign (Val (LitV (LitStack ln))) (loadn - Val (LitV (LitInt 1)))).
  set (body := Seq steps stepn).
  iApply (wp_bind [SeqCtx loads]).
  iApply wp_while.
  iApply (wp_bind [IfCtx (Seq body (While cond body)) (Val (LitV LitUnit))]).
  iApply (wp_bind [BinOpRCtx LeOp (LitV (LitInt 1))]).
  iApply (wp_stack_load (StackId ln) with "Hn").
  iIntros "!> _ Hn".
  iApply wp_binop; [by vm_compute|].
  iIntros "!> _".
  iApply wp_if_true.
  iApply (wp_bind [SeqCtx (While cond body)]).
  iApply (wp_bind [SeqCtx stepn]).
  iApply (wp_bind [StackAssignRCtx (LitV (LitStack ls))]).
  iApply (wp_bind [BinOpLCtx PlusOp (Val (LitV (LitInt 1)))]).
  iApply (wp_stack_load (StackId ls) with "Hs").
  iIntros "!> _ Hs".
  iApply wp_binop; [by vm_compute|].
  iIntros "!> _".
  iApply (wp_stack_assign with "Hs").
  iIntros "!> _ Hs".
  iApply wp_seq.
  iApply (wp_bind [StackAssignRCtx (LitV (LitStack ln))]).
  iApply (wp_bind [BinOpLCtx MinusOp (Val (LitV (LitInt 1)))]).
  iApply (wp_stack_load (StackId ln) with "Hn").
  iIntros "!> _ Hn".
  iApply wp_binop; [by vm_compute|].
  iIntros "!> _".
  iApply (wp_stack_assign with "Hn").
  iIntros "!> _ Hn".
  iApply wp_seq.
  iApply wp_while.
  iApply (wp_bind [IfCtx (Seq body (While cond body)) (Val (LitV LitUnit))]).
  iApply (wp_bind [BinOpRCtx LeOp (LitV (LitInt 1))]).
  iApply (wp_stack_load (StackId ln) with "Hn").
  iIntros "!> _ Hn".
  iApply wp_binop; [by vm_compute|].
  iIntros "!> _".
  iApply wp_if_false.
  iApply wp_value'.
  iApply wp_seq.
  iApply (wp_stack_load (StackId ls) with "Hs").
  iIntros "!> _ Hs".
  iExists (LitV (LitInt 1)). iFrame "Hs".
  iExists (LitV (LitInt 0)). iFrame "Hn".
  done.
Qed.

Lemma sum_one_adequate Σ `{!cjrGpreS Σ} :
  adequate NotStuck sum_one state_init (λ v _, v = LitV (LitInt 1)).
Proof. eapply (cjr_adequacy Σ). intros ??. eapply sum_one_wp. Qed.

(** Regression checks for signed remainder and its partial domain. *)
Example remainder_signs :
  bin_op_eval RemOp (LitV (LitInt 7)) (LitV (LitInt 3)) = Some (LitV (LitInt 1)) ∧
  bin_op_eval RemOp (LitV (LitInt (-7))) (LitV (LitInt 3)) = Some (LitV (LitInt (-1))) ∧
  bin_op_eval RemOp (LitV (LitInt 7)) (LitV (LitInt (-3))) = Some (LitV (LitInt 1)) ∧
  bin_op_eval RemOp (LitV (LitInt (-7))) (LitV (LitInt (-3))) = Some (LitV (LitInt (-1))).
Proof. vm_compute. repeat split; reflexivity. Qed.

Example remainder_zero_divisor n :
  bin_op_eval RemOp (LitV (LitInt n)) (LitV (LitInt 0)) = None.
Proof. reflexivity. Qed.

Example remainder_noninteger :
  bin_op_eval RemOp (LitV (LitBool true)) (LitV (LitInt 3)) = None.
Proof. reflexivity. Qed.

(** Bitwise operations retain the ordinary signed two's-complement laws. *)
Example bitwise_signed_cases :
  bin_op_eval BitXorOp (LitV (LitInt (-1))) (LitV (LitInt 85)) = Some (LitV (LitInt (-86))) ∧
  bin_op_eval BitAndOp (LitV (LitInt (-1))) (LitV (LitInt 255)) = Some (LitV (LitInt 255)) ∧
  bin_op_eval BitXorOp (LitV (LitInt 128)) (LitV (LitInt 255)) = Some (LitV (LitInt 127)).
Proof. vm_compute. repeat split; reflexivity. Qed.
Example bitwise_noninteger :
  bin_op_eval BitXorOp (LitV (LitBool true)) (LitV (LitInt 3)) = None ∧
  bin_op_eval BitAndOp (LitV (LitInt 3)) (LitV (LitBool true)) = None.
Proof. split; reflexivity. Qed.

(** Multiplication is signed and unbounded in the model. *)
Definition multiply_body : expr :=
  Let (Some "a") (StructLoad (Var "args") 0)
    (Let (Some "b") (StructLoad (Var "args") 1)
      (Var "a" * Var "b")).

Example multiplication_cases :
  bin_op_eval MulOp (LitV (LitInt (-7))) (LitV (LitInt 6)) = Some (LitV (LitInt (-42))) ∧
  bin_op_eval MulOp (LitV (LitInt (-7))) (LitV (LitInt (-6))) = Some (LitV (LitInt 42)) ∧
  bin_op_eval MulOp (LitV (LitInt 0)) (LitV (LitInt 42)) = Some (LitV (LitInt 0)) ∧
  bin_op_eval MulOp (LitV (LitInt 9223372036854775807)) (LitV (LitInt 2)) =
    Some (LitV (LitInt 18446744073709551614)).
Proof. vm_compute. repeat split; reflexivity. Qed.

Example multiplication_noninteger :
  bin_op_eval MulOp (LitV (LitBool true)) (LitV (LitInt 3)) = None ∧
  bin_op_eval MulOp (LitV (LitInt 3)) (LitV (LitFloat 2)) = None.
Proof. split; reflexivity. Qed.

(** Division follows Cangjie's truncation toward zero, not floor division. *)
Example division_signs :
  bin_op_eval DivOp (LitV (LitInt 7)) (LitV (LitInt 3)) = Some (LitV (LitInt 2)) ∧
  bin_op_eval DivOp (LitV (LitInt (-7))) (LitV (LitInt 3)) = Some (LitV (LitInt (-2))) ∧
  bin_op_eval DivOp (LitV (LitInt 7)) (LitV (LitInt (-3))) = Some (LitV (LitInt (-2))) ∧
  bin_op_eval DivOp (LitV (LitInt (-7))) (LitV (LitInt (-3))) = Some (LitV (LitInt 2)).
Proof. vm_compute. repeat split; reflexivity. Qed.
Example division_zero n :
  bin_op_eval DivOp (LitV (LitInt n)) (LitV (LitInt 0)) = None.
Proof. reflexivity. Qed.
Example division_noninteger :
  bin_op_eval DivOp (LitV (LitBool true)) (LitV (LitInt 2)) = None.
Proof. reflexivity. Qed.
Definition divide_body : expr :=
  Let (Some "a") (StructLoad (Var "args") 0)
    (Let (Some "b") (StructLoad (Var "args") 1)
      (BinOp DivOp (Var "a") (Var "b"))).
