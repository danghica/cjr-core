From iris.proofmode Require Import proofmode.
From iris.program_logic Require Export weakestpre.
From iris.program_logic Require Import ectx_lifting.
From cjr Require Import lang.
From iris.prelude Require Import options.

Section lifting.
  Context `{!irisGS_gen hlc cjr_lang Σ}.
  Implicit Types Φ : val → iProp Σ.

  Lemma wp_lift_pure_step E Φ e1 e2 :
    to_val e1 = None →
    (∀ σ, base_reducible e1 σ) →
    (∀ σ1 κ e2' σ2 efs,
       base_step e1 σ1 κ e2' σ2 efs → κ = [] ∧ σ2 = σ1 ∧ e2' = e2 ∧ efs = []) →
    ▷ (£ 1 -∗ WP e2 @ E {{ Φ }}) ⊢ WP e1 @ E {{ Φ }}.
  Proof.
    iIntros (???) "H".
    iApply wp_lift_pure_det_base_step_no_fork'; [done|done|done|].
    iExact "H".
  Qed.
End lifting.
