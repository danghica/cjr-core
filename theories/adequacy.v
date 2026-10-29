From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import ghost_map invariants.
From iris.program_logic Require Import adequacy.
From cjr Require Export lang primitive_laws.
From iris.prelude Require Import options.

Class cjrGpreS Σ := CjrGpreS {
  #[global] cjrGpreS_inv :: invGpreS Σ;
  #[global] cjrGpreS_stack :: ghost_mapG Σ stack_id val_cjr;
  #[global] cjrGpreS_raw :: ghost_mapG Σ raw_id val_cjr;
  #[global] cjrGpreS_block :: ghost_mapG Σ raw_id nat;
  #[global] cjrGpreS_obj :: ghost_mapG Σ (obj_id * nat) val_cjr
}.

Definition cjrΣ : gFunctors :=
  #[ invΣ;
     ghost_mapΣ stack_id val_cjr;
     ghost_mapΣ raw_id val_cjr;
     ghost_mapΣ raw_id nat;
     ghost_mapΣ (obj_id * nat) val_cjr ].

Global Instance subG_cjrGpreS {Σ} : subG cjrΣ Σ → cjrGpreS Σ.
Proof. solve_inG. Qed.

Lemma cjr_adequacy Σ `{!cjrGpreS Σ} e φ :
  (∀ `{!cjrGS Σ} `{!invGS_gen HasLc Σ}, ⊢ WP e {{ v, ⌜ φ v ⌝ }}) →
  adequate NotStuck e state_init (λ v _, φ v).
Proof.
  intros Hwp. eapply (wp_adequacy Σ cjr_lang).
  iIntros (Hinv κs).
  iMod (ghost_map_alloc_empty (K:=stack_id) (V:=val_cjr)) as (γs) "Hs".
  iMod (ghost_map_alloc_empty (K:=raw_id) (V:=val_cjr)) as (γr) "Hr".
  iMod (ghost_map_alloc_empty (K:=raw_id) (V:=nat)) as (γb) "Hb".
  iMod (ghost_map_alloc_empty (K:=obj_id * nat) (V:=val_cjr)) as (γo) "Ho".
  pose (Hg := @CjrGS Σ _ _ _ _ γs γr γb γo).
  iModIntro.
  iExists (λ σ _, cjr_state_interp σ), (λ _, True)%I.
  iSplitL "Hs Hr Hb Ho".
  { unfold cjr_state_interp. simpl. iFrame. iPureIntro. apply state_init_wf. }
  iApply Hwp.
Qed.
