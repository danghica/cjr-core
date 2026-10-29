(** Allocate a final class, write a field, and read it back.
A raw cell is framed across the object update. *)
From iris.proofmode Require Import proofmode.
From cjr Require Import notation primitive_laws adequacy.
From iris.prelude Require Import options.
Open Scope expr_scope.

Definition class_bump : expr :=
  Let (Some "r") (Alloc (Val (LitV (LitInt 1))))
    (Let (Some "o") (New [LitV (LitInt 0)] [])
      (Seq
        (FieldStore (Var "o") 0 (Val (LitV (LitInt 5))))
        (Seq (FieldLoad (Var "o") 0) (Load (Var "r"))))).

Lemma class_bump_wp `{!cjrGS Σ} `{!invGS_gen HasLc Σ} :
  ⊢ WP class_bump {{ v, ⌜ v = LitV (LitInt 0) ⌝ }}.
Proof.
  iApply (wp_bind [LetCtx (Some "r")
    (Let (Some "o") (New [LitV (LitInt 0)] [])
      (Seq (FieldStore (Var "o") 0 (Val (LitV (LitInt 5))))
        (Seq (FieldLoad (Var "o") 0) (Load (Var "r")))))]).
  iApply wp_alloc_one. iIntros (l) "Hl _".
  iApply wp_let. simpl.
  iApply (wp_bind [LetCtx (Some "o")
    (Seq (FieldStore (Var "o") 0 (Val (LitV (LitInt 5))))
      (Seq (FieldLoad (Var "o") 0) (Load (Val (LitV (LitPtr l))))))]).
  iApply wp_new. iIntros (o) "Ho".
  iDestruct "Ho" as "[Ho _]".
  iApply wp_let. simpl.
  iApply (wp_bind [SeqCtx
    (Seq (FieldLoad (Val (LitV (LitObj o))) 0) (Load (Val (LitV (LitPtr l)))))]).
  iApply (wp_field_store with "Ho").
  iIntros "!> _ Ho".
  iApply wp_seq.
  iApply (wp_bind [SeqCtx (Load (Val (LitV (LitPtr l))))]).
  iApply (wp_field_load with "Ho").
  iIntros "!> _ _".
  iApply wp_seq.
  iApply (wp_load with "Hl").
  iIntros "!> _ _". done.
Qed.

Lemma class_bump_adequate Σ `{!cjrGpreS Σ} :
  adequate NotStuck class_bump state_init (λ v _, v = LitV (LitInt 0)).
Proof. eapply (cjr_adequacy Σ). intros ??. apply class_bump_wp. Qed.
