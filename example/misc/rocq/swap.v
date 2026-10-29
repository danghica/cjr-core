(** In-place swap of two disjoint raw words.
Aliasing the two addresses contradicts the precondition. *)
From iris.proofmode Require Import proofmode.
From cjr Require Import notation primitive_laws.
From iris.prelude Require Import options.
Open Scope expr_scope.

Definition swap_at (l1 l2 : Z) : expr :=
  Let (Some "t") (Load (Val (LitV (LitPtr l1))))
    (Seq
      (Store (Val (LitV (LitPtr l1))) (Load (Val (LitV (LitPtr l2)))))
      (Store (Val (LitV (LitPtr l2))) (Var "t"))).

Lemma swap_wp `{!cjrGS Σ} `{!invGS_gen HasLc Σ} (l1 l2 : Z) v1 v2 :
  RawId l1 ↦ᵣ v1 -∗ RawId l2 ↦ᵣ v2 -∗
  WP swap_at l1 l2 {{ _, RawId l1 ↦ᵣ v2 ∗ RawId l2 ↦ᵣ v1 }}.
Proof.
  iIntros "H1 H2".
  iApply (wp_bind [LetCtx (Some "t")
    (Seq
      (Store (Val (LitV (LitPtr l1))) (Load (Val (LitV (LitPtr l2)))))
      (Store (Val (LitV (LitPtr l2))) (Var "t")))]).
  iApply (wp_load with "H1").
  iIntros "!> _ H1".
  iApply wp_let. simpl.
  iApply (wp_bind [SeqCtx (Store (Val (LitV (LitPtr l2))) (Val v1))]).
  iApply (wp_bind [StoreRCtx (LitV (LitPtr l1))]).
  iApply (wp_load with "H2").
  iIntros "!> _ H2".
  iApply (wp_store with "H1").
  iIntros "!> _ H1".
  iApply wp_seq.
  iApply (wp_store with "H2").
  iIntros "!> _ H2".
  iFrame.
Qed.

Lemma swap_aliased `{!cjrGS Σ} (l : raw_id) v1 v2 :
  l ↦ᵣ v1 -∗ l ↦ᵣ v2 -∗ False.
Proof. apply raw_mapsto_exclusive. Qed.
