(** Allocate, store, load, and free one raw word. *)
From iris.proofmode Require Import proofmode.
From cjr Require Import notation primitive_laws adequacy.
From iris.prelude Require Import options.
Open Scope expr_scope.

Definition cell : expr :=
  Let (Some "p") (Alloc (Val (LitV (LitInt 1))))
    (Seq
      (Store (Var "p") (Val (LitV (LitInt 7))))
      (Seq (Load (Var "p")) (Free (Var "p")))).

Lemma cell_wp `{!cjrGS Σ} `{!invGS_gen HasLc Σ} :
  ⊢ WP cell {{ v, ⌜ v = LitV LitUnit ⌝ }}.
Proof.
  iApply (wp_bind [LetCtx (Some "p")
    (Seq (Store (Var "p") (Val (LitV (LitInt 7))))
      (Seq (Load (Var "p")) (Free (Var "p"))))]).
  iApply wp_alloc_one. iIntros (l) "Hl Hblk".
  iApply wp_let. simpl.
  iApply (wp_bind [SeqCtx (Seq (Load (Val (LitV (LitPtr l)))) (Free (Val (LitV (LitPtr l)))))]).
  iApply (wp_store with "Hl").
  iIntros "!> _ Hl".
  iApply wp_seq.
  iApply (wp_bind [SeqCtx (Free (Val (LitV (LitPtr l))))]).
  iApply (wp_load with "Hl").
  iIntros "!> _ Hl".
  iApply wp_seq.
  iApply (wp_free_one with "Hl Hblk").
  iIntros "!> _". done.
Qed.

Lemma cell_adequate Σ `{!cjrGpreS Σ} :
  adequate NotStuck cell state_init (λ v _, v = LitV LitUnit).
Proof. eapply (cjr_adequacy Σ). intros ??. apply cell_wp. Qed.
