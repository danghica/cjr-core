(** Iris reasoning for generics is reasoning about their erased programs. *)
From iris.proofmode Require Import proofmode.
From cjr Require Export generics adequacy.
From iris.prelude Require Import options.

Section generic_logic.
  Context `{!cjrGS Σ} `{!invGS_gen HasLc Σ}.

  Definition generic_wp ds fs e (Φ : val → iProp Σ) : iProp Σ :=
    WP erase ds fs e {{ Φ }}.

  Lemma generic_wp_instantiate ds fs e s Φ : nominal_owners e = true →
    generic_wp ds fs (ginstantiate s e) Φ ⊣⊢ generic_wp ds fs e Φ.
  Proof. intros H. unfold generic_wp. rewrite (erase_instantiate ds fs e s H). done. Qed.

  Lemma generic_wp_legacy ds fs e Φ :
    generic_wp ds fs (GECore e) Φ ⊣⊢ WP e {{ Φ }}.
  Proof. done. Qed.

  Lemma wp_generic_struct_step vs v es Φ :
    WP Struct (vs ++ [v]) es {{ Φ }} ⊢ WP Struct vs (Val v :: es) {{ Φ }}.
  Proof.
    iIntros "H". iApply wp_pure_step; [done| | |].
    { intros σ. eexists [], _, σ, []. apply StructStepS. }
    { intros ????? Hstep. inversion Hstep; simplify_eq; auto. }
    iIntros "!> _". iExact "H".
  Qed.

  Lemma wp_generic_new_step vs v es Φ :
    WP New (vs ++ [v]) es {{ Φ }} ⊢ WP New vs (Val v :: es) {{ Φ }}.
  Proof.
    iIntros "H". iApply wp_pure_step; [done| | |].
    { intros σ. eexists [], _, σ, []. apply NewStepS. }
    { intros ????? Hstep. inversion Hstep; simplify_eq; auto. }
    iIntros "!> _". iExact "H".
  Qed.

  Lemma wp_generic_pack_acc acc vs Φ :
    Φ (StructV (acc ++ vs)) ⊢ WP Struct acc (map Val vs) {{ Φ }}.
  Proof.
    revert acc. induction vs as [|v vs IH]; intros acc; simpl.
    - rewrite app_nil_r. iIntros "H". iApply wp_struct_done. iIntros "!> _". iExact "H".
    - iIntros "H". iApply wp_generic_struct_step. iApply IH.
      rewrite <- app_assoc. simpl. iExact "H".
  Qed.

  Lemma wp_generic_call_args fs name f vs Φ :
    glookup name fs = Some f →
    WP App (resolve fs name) (Val (StructV vs)) {{ Φ }} ⊢
    WP App (resolve fs name) (gpack (map Val vs)) {{ Φ }}.
  Proof.
    intros Hf. unfold resolve. rewrite Hf.
    iIntros "H". iApply (wp_bind [AppRCtx f]).
    iApply wp_generic_pack_acc. simpl. iExact "H".
  Qed.
End generic_logic.

Lemma generic_adequacy Σ `{!cjrGpreS Σ} p φ :
  (∀ `{!cjrGS Σ} `{!invGS_gen HasLc Σ},
    ⊢ generic_wp (gp_layouts p)
      (link_functions (gp_layouts p) [] (gp_functions p)) (gp_main p)
      (λ v, ⌜φ v⌝)) →
  adequate NotStuck (erase_program p) state_init (λ v _, φ v).
Proof. intros H. apply (cjr_adequacy Σ). exact H. Qed.
