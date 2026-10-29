(** Derived initialized storage: no new runtime primitive or logical axiom. *)
From iris.proofmode Require Import proofmode.
From cjr Require Import buffer generic_laws primitive_laws.
From iris.prelude Require Import options.
From Coq Require Import Lia.

Section buffer_logic.
  Context `{!cjrGS Σ} `{!invGS_gen HasLc Σ}.

  Definition buffer_cells (base : Z) (xs : list val) : iProp Σ :=
    [∗ list] i ↦ v ∈ xs, RawId (base + Z.of_nat i)%Z ↦ᵣ v.

  Lemma buffer_zero_cells base n :
    ([∗ list] i ∈ seq 0 n, RawId (base + Z.of_nat i)%Z ↦ᵣ LitV (LitInt 0)) ⊢
    buffer_cells base (replicate n (LitV (LitInt 0))).
  Proof.
    revert base. induction n as [|n IH]; intros base.
    - by rewrite big_sepL_nil.
    - rewrite seq_S big_sepL_snoc replicate_S_end.
      rewrite /buffer_cells big_sepL_app big_sepL_singleton.
      rewrite length_replicate Nat.add_0_r.
      apply bi.sep_mono; [apply IH|done].
  Qed.

  Lemma wp_buffer_fill base n seed : closed_val seed →
    buffer_cells base (replicate n (LitV (LitInt 0))) -∗
    WP App (Val buffer_fill_val)
      (Val (StructV [LitV (LitPtr base); LitV (LitInt (Z.of_nat n)); seed]))
      {{ v, ⌜v = LitV LitUnit⌝ ∗ buffer_cells base (replicate n seed) }}.
  Proof.
    intros Hclosed. induction n as [|n IH]; iIntros "Hcells";
      iApply wp_app; simpl; rewrite ?Hclosed.
    all: iApply (wp_bind [LetCtx _ _]); iApply wp_struct_load; [done|];
      iIntros "!> _"; iApply wp_let; simpl; rewrite ?Hclosed.
    all: iApply (wp_bind [LetCtx _ _]); iApply wp_struct_load; [done|];
      iIntros "!> _"; iApply wp_let; simpl; rewrite ?Hclosed.
    all: iApply (wp_bind [LetCtx _ _]); iApply wp_struct_load; [done|];
      iIntros "!> _"; iApply wp_let; simpl; rewrite ?Hclosed.
    - iApply (wp_bind [IfCtx _ _]). iApply wp_binop; [done|].
      iIntros "!> _". iApply wp_if_true.
      iApply wp_value'. iSplit; done.
    - iApply (wp_bind [IfCtx _ _]). iApply (wp_binop _ _ _ (LitV (LitBool false))).
      { cbn [bin_op_eval]. rewrite bool_decide_false; [done|lia]. }
      iIntros "!> _". iApply wp_if_false.
      iApply (wp_bind [LetCtx _ _]). iApply wp_binop; [done|].
      iIntros "!> _". iApply wp_let. simpl. rewrite ?Hclosed.
      replace (Z.of_nat (S n) - 1)%Z with (Z.of_nat n) by lia.
      iAssert (buffer_cells base (replicate (S n) (LitV (LitInt 0)))) with "[Hcells]" as "Hcells"; [iExact "Hcells"|].
      iEval (rewrite replicate_S_end /buffer_cells big_sepL_app
        big_sepL_singleton length_replicate Nat.add_0_r) in "Hcells".
      iDestruct "Hcells" as "[Hprefix Hlast]".
      iApply (wp_bind [StoreLCtx _; LetCtx _ _]). iApply wp_offset.
      iIntros "!> _". iApply (wp_bind [LetCtx _ _]).
      iApply (wp_store with "Hlast"). iIntros "!> _ Hlast".
      iApply wp_let. simpl. rewrite ?Hclosed.
      iApply (wp_bind [AppRCtx buffer_fill_val]).
      iApply (wp_generic_pack_acc [] [LitV (LitPtr base); LitV (LitInt (Z.of_nat n)); seed]).
      simpl app. iApply (wp_wand with "[Hprefix]").
      { iApply (IH with "Hprefix"). }
      iIntros (v) "[%Hv Hprefix]". iSplit; [done|].
      iAssert (buffer_cells base (replicate (S n) seed)) with "[Hprefix Hlast]" as "H"; [|iExact "H"].
      rewrite replicate_S_end /buffer_cells big_sepL_app big_sepL_singleton
        length_replicate Nat.add_0_r. iFrame.
  Qed.

  Lemma wp_buffer_make n seed : (0 < n)%nat → closed_val seed →
    ⊢ WP App (Val buffer_make_val)
      (Val (StructV [LitV (LitInt (Z.of_nat n)); seed]))
      {{ v, ∃ base, ⌜v = LitV (LitPtr base)⌝ ∗ RawId base ↦ᵦ n ∗
        buffer_cells base (replicate n seed) }}.
  Proof.
    intros Hn Hclosed. iApply wp_app. simpl. rewrite ?Hclosed.
    iApply (wp_bind [LetCtx _ _]); iApply wp_struct_load; [done|].
    iIntros "!> _". iApply wp_let. simpl.
    rewrite ?Hclosed ?buffer_fill_closed.
    iApply (wp_bind [LetCtx _ _]); iApply wp_struct_load; [done|].
    iIntros "!> _". iApply wp_let. simpl.
    rewrite ?Hclosed ?buffer_fill_closed.
    iApply (wp_bind [LetCtx _ _]). iApply wp_alloc; [lia|].
    iIntros (base) "Hcells Hblock".
    iEval (rewrite Nat2Z.id) in "Hcells Hblock".
    iDestruct (buffer_zero_cells with "Hcells") as "Hcells".
    iApply wp_let. simpl. rewrite ?Hclosed ?buffer_fill_closed.
    iApply (wp_bind [AppRCtx buffer_fill_val; LetCtx _ _]).
    iApply (wp_generic_pack_acc [] [LitV (LitPtr base); LitV (LitInt (Z.of_nat n)); seed]).
    simpl app. iApply (wp_bind [LetCtx _ _]).
    iApply (wp_wand with "[Hcells]").
    { iApply (wp_buffer_fill with "Hcells"). exact Hclosed. }
    iIntros (v) "[%Hv Hcells]". iApply wp_let. simpl.
    iApply wp_value'. iExists base. iSplit; [done|]. iFrame.
  Qed.
End buffer_logic.
