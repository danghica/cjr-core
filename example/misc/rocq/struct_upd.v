(** In-place update of a [var] struct field. The raw heap is framed. *)
From iris.proofmode Require Import proofmode.
From cjr Require Import notation primitive_laws adequacy.
From iris.prelude Require Import options.
Open Scope expr_scope.

Definition bump : expr :=
  VarBind "p" (Val (StructV [LitV (LitInt 0)]))
    (Seq
      (StructStore "p" 0 (Val (LitV (LitInt 1))))
      (StructLoad (Var "p") 0)).

Lemma bump_wp `{!cjrGS Σ} `{!invGS_gen HasLc Σ} l v :
  RawId l ↦ᵣ v -∗
  WP bump {{ w, ⌜ w = LitV (LitInt 1) ⌝ ∗ RawId l ↦ᵣ v }}.
Proof.
  iIntros "Hr".
  iApply wp_var_bind. iIntros (lp) "Hp". simpl.
  set (rd := StructLoad (StackLoad (Val (LitV (LitStack lp)))) 0).
  iApply (wp_bind [SeqCtx rd]).
  iApply (wp_stack_field (StackId lp) [LitV (LitInt 0)] 0
            (LitV (LitInt 0)) (LitV (LitInt 1)) with "Hp").
  { done. }
  iIntros "!> _ Hp".
  iApply wp_seq.
  iApply (wp_bind [StructLoadCtx 0]).
  iApply (wp_stack_load (StackId lp) with "Hp").
  iIntros "!> _ Hp".
  iApply (wp_struct_load [LitV (LitInt 1)] 0 (LitV (LitInt 1))).
  { done. }
  iIntros "!> _".
  iExists (StructV [LitV (LitInt 1)]). iFrame "Hp Hr".
  done.
Qed.

Definition bump_keep : expr :=
  Let (Some "r") (Alloc (Val (LitV (LitInt 1))))
    (Seq bump (Load (Var "r"))).

Lemma bump_keep_wp `{!cjrGS Σ} `{!invGS_gen HasLc Σ} :
  ⊢ WP bump_keep {{ v, ⌜ v = LitV (LitInt 0) ⌝ }}.
Proof.
  iApply (wp_bind [LetCtx (Some "r") (Seq bump (Load (Var "r")))]).
  iApply wp_alloc_one. iIntros (l) "Hl _".
  iApply wp_let. simpl.
  iApply (wp_bind [SeqCtx (Load (Val (LitV (LitPtr l))))]).
  iApply (wp_wand with "[Hl]").
  { iApply (bump_wp with "Hl"). }
  iIntros (w) "[%Hw Hr]".
  iApply wp_seq.
  iApply (wp_load with "Hr").
  iIntros "!> _ _". iPureIntro. done.
Qed.

Lemma bump_adequate Σ `{!cjrGpreS Σ} :
  adequate NotStuck bump_keep state_init (λ v _, v = LitV (LitInt 0)).
Proof. eapply (cjr_adequacy Σ). intros ??. apply bump_keep_wp. Qed.
