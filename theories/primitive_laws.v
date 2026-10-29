From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import ghost_map.
From iris.program_logic Require Export weakestpre adequacy.
From iris.program_logic Require Import ectx_lifting.
From cjr Require Export lang.
From iris.prelude Require Import options.

Class cjrGS Σ := CjrGS {
  cjr_stackG :: ghost_mapG Σ stack_id val_cjr;
  cjr_rawG :: ghost_mapG Σ raw_id val_cjr;
  cjr_blockG :: ghost_mapG Σ raw_id nat;
  cjr_objG :: ghost_mapG Σ (obj_id * nat) val_cjr;
  cjr_stack_name : gname;
  cjr_raw_name : gname;
  cjr_block_name : gname;
  cjr_obj_name : gname
}.

Section defs.
  Context `{!cjrGS Σ}.

  Definition stack_mapsto (l : stack_id) (v : val_cjr) : iProp Σ :=
    ghost_map_elem cjr_stack_name l (DfracOwn 1) v.
  Definition raw_mapsto (l : raw_id) (v : val_cjr) : iProp Σ :=
    ghost_map_elem cjr_raw_name l (DfracOwn 1) v.
  Definition block_mapsto (l : raw_id) (n : nat) : iProp Σ :=
    ghost_map_elem cjr_block_name l (DfracOwn 1) n.
  Definition obj_mapsto (o : obj_id) (i : nat) (v : val_cjr) : iProp Σ :=
    ghost_map_elem cjr_obj_name (o, i) (DfracOwn 1) v.

  Definition cjr_state_interp (σ : state_cjr) : iProp Σ :=
    ghost_map_auth cjr_stack_name 1 (cjr_stack σ) ∗
    ghost_map_auth cjr_raw_name 1 (cjr_raw σ) ∗
    ghost_map_auth cjr_block_name 1 (cjr_blocks σ) ∗
    ghost_map_auth cjr_obj_name 1 (cjr_obj σ) ∗
    ⌜state_wf σ⌝.
End defs.

Notation "l ↦ₛ v" := (stack_mapsto l v)
  (at level 20, format "l  ↦ₛ  v") : bi_scope.
Notation "l ↦ᵣ v" := (raw_mapsto l v)
  (at level 20, format "l  ↦ᵣ  v") : bi_scope.
Notation "l ↦ᵦ n" := (block_mapsto l n)
  (at level 20, format "l  ↦ᵦ  n") : bi_scope.
Notation "o ↦ₒ[ i ] v" := (obj_mapsto o i v)
  (at level 20, format "o  ↦ₒ[ i ]  v") : bi_scope.

Global Instance cjr_irisGS `{!cjrGS Σ} `{Hinv : !invGS_gen HasLc Σ} :
  irisGS cjr_lang Σ :=
  IrisG Hinv (λ σ _ κs _, cjr_state_interp σ) (λ _, True%I)
        (λ _, 0) (λ _ _ _ _, fupd_intro _ _).

Section laws.
  Context `{!cjrGS Σ} `{!invGS_gen HasLc Σ}.
  Implicit Types Φ : val_cjr → iProp Σ.

  Lemma stack_mapsto_exclusive l v1 v2 :
    l ↦ₛ v1 -∗ l ↦ₛ v2 -∗ False.
  Proof.
    iIntros "H1 H2".
    iDestruct (ghost_map_elem_valid_2 with "H1 H2") as %[Hval _].
    by apply dfrac_valid_own_r in Hval.
  Qed.

  Lemma raw_mapsto_exclusive l v1 v2 :
    l ↦ᵣ v1 -∗ l ↦ᵣ v2 -∗ False.
  Proof.
    iIntros "H1 H2".
    iDestruct (ghost_map_elem_valid_2 with "H1 H2") as %[Hval _].
    by apply dfrac_valid_own_r in Hval.
  Qed.

  Lemma wp_bind K `{!LanguageCtx (fill K)} e Φ :
    WP e {{ v, WP fill K (Val v) {{ Φ }} }} ⊢ WP fill K e {{ Φ }}.
  Proof. iIntros "H". iApply (wp_bind (fill K) with "H"). Qed.

  Lemma wp_pure_step E e1 e2 Φ :
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

  Local Ltac pure_reducible :=
    intros σ; eexists [], _, σ, []; repeat (econstructor; eauto).
  Local Ltac pure_det :=
    intros ????? Hstep; inversion Hstep; simplify_eq; auto.

  Lemma wp_rec f x e E Φ :
    ▷ (£ 1 -∗ Φ (RecV f x e)) ⊢ WP Rec f x e @ E {{ Φ }}.
  Proof.
    iIntros "H".
    iApply wp_pure_step; [done|pure_reducible|pure_det|].
    iIntros "!> Hcred". iApply wp_value'. iApply ("H" with "Hcred").
  Qed.

  Lemma wp_app f x e v E Φ :
    WP subst_binder x v (subst_binder f (RecV f x e) e) @ E {{ Φ }} ⊢
    WP App (Val (RecV f x e)) (Val v) @ E {{ Φ }}.
  Proof.
    iIntros "H".
    iApply wp_pure_step; [done|pure_reducible|pure_det|].
    iIntros "!> _". iApply "H".
  Qed.

  Lemma wp_let x v e E Φ :
    WP subst_binder x v e @ E {{ Φ }} ⊢ WP Let x (Val v) e @ E {{ Φ }}.
  Proof.
    iIntros "H".
    iApply wp_pure_step; [done|pure_reducible|pure_det|].
    iIntros "!> _". iApply "H".
  Qed.

  Lemma wp_if_true e1 e2 E Φ :
    WP e1 @ E {{ Φ }} ⊢ WP If (Val (LitV (LitBool true))) e1 e2 @ E {{ Φ }}.
  Proof.
    iIntros "H".
    iApply wp_pure_step; [done|pure_reducible|pure_det|].
    iIntros "!> _". iApply "H".
  Qed.

  Lemma wp_if_false e1 e2 E Φ :
    WP e2 @ E {{ Φ }} ⊢ WP If (Val (LitV (LitBool false))) e1 e2 @ E {{ Φ }}.
  Proof.
    iIntros "H".
    iApply wp_pure_step; [done|pure_reducible|pure_det|].
    iIntros "!> _". iApply "H".
  Qed.

  Lemma wp_while e1 e2 E Φ :
    WP If e1 (Seq e2 (While e1 e2)) (Val (LitV LitUnit)) @ E {{ Φ }} ⊢
    WP While e1 e2 @ E {{ Φ }}.
  Proof.
    iIntros "H".
    iApply wp_pure_step; [done|pure_reducible|pure_det|].
    iIntros "!> _". iApply "H".
  Qed.

  Lemma wp_seq v e E Φ :
    WP e @ E {{ Φ }} ⊢ WP Seq (Val v) e @ E {{ Φ }}.
  Proof.
    iIntros "H".
    iApply wp_pure_step; [done|pure_reducible|pure_det|].
    iIntros "!> _". iApply "H".
  Qed.

  Lemma wp_binop op v1 v2 v E Φ :
    bin_op_eval op v1 v2 = Some v →
    ▷ (£ 1 -∗ Φ v) ⊢ WP BinOp op (Val v1) (Val v2) @ E {{ Φ }}.
  Proof.
    iIntros (Heval) "H".
    iApply wp_pure_step; [done| | |].
    - intros σ. eexists [], (Val v), σ, []. by econstructor.
    - pure_det.
    - iIntros "!> Hcred". iApply wp_value'. iApply ("H" with "Hcred").
  Qed.

  (** Multiplication uses unbounded integers, like addition and subtraction. *)
  Lemma wp_mul (a b : Z) E Φ :
    ▷ (£ 1 -∗ Φ (LitV (LitInt (a * b)))) ⊢
    WP BinOp MulOp (Val (LitV (LitInt a))) (Val (LitV (LitInt b))) @ E {{ Φ }}.
  Proof. apply wp_binop. reflexivity. Qed.

  (** Signed division truncates toward zero; its divisor must be nonzero. *)
  Lemma wp_div (n d : Z) E Φ :
    d ≠ 0%Z →
    ▷ (£ 1 -∗ Φ (LitV (LitInt (Z.quot n d)))) ⊢
    WP BinOp DivOp (Val (LitV (LitInt n))) (Val (LitV (LitInt d))) @ E {{ Φ }}.
  Proof.
    intros Hd. apply wp_binop. simpl.
    destruct (decide (d = 0)%Z); [contradiction|reflexivity].
  Qed.

  (** Signed remainder is defined only for a nonzero divisor. *)
  Lemma wp_rem (n d : Z) E Φ :
    d ≠ 0%Z →
    ▷ (£ 1 -∗ Φ (LitV (LitInt (Z.rem n d)))) ⊢
    WP BinOp RemOp (Val (LitV (LitInt n))) (Val (LitV (LitInt d))) @ E {{ Φ }}.
  Proof.
    intros Hd. apply wp_binop. simpl.
    destruct (decide (d = 0)%Z); [contradiction|reflexivity].
  Qed.

  (** Integer bitwise operations; Boolean conjunction remains [AndOp]. *)
  Lemma wp_bitxor (a b : Z) E Φ :
    ▷ (£ 1 -∗ Φ (LitV (LitInt (Z.lxor a b)))) ⊢
    WP BinOp BitXorOp (Val (LitV (LitInt a))) (Val (LitV (LitInt b))) @ E {{ Φ }}.
  Proof. apply wp_binop. reflexivity. Qed.

  Lemma wp_bitand (a b : Z) E Φ :
    ▷ (£ 1 -∗ Φ (LitV (LitInt (Z.land a b)))) ⊢
    WP BinOp BitAndOp (Val (LitV (LitInt a))) (Val (LitV (LitInt b))) @ E {{ Φ }}.
  Proof. apply wp_binop. reflexivity. Qed.

  Lemma wp_offset (l i : Z) E Φ :
    ▷ (£ 1 -∗ Φ (LitV (LitPtr (l + i)%Z))) ⊢
    WP Offset (Val (LitV (LitPtr l))) (Val (LitV (LitInt i))) @ E {{ Φ }}.
  Proof.
    iIntros "H".
    iApply wp_pure_step; [done|pure_reducible|pure_det|].
    iIntros "!> Hcred". iApply wp_value'. iApply ("H" with "Hcred").
  Qed.

  Lemma wp_struct_done vs E Φ :
    ▷ (£ 1 -∗ Φ (StructV vs)) ⊢ WP Struct vs [] @ E {{ Φ }}.
  Proof.
    iIntros "H".
    iApply wp_pure_step; [done|pure_reducible|pure_det|].
    iIntros "!> Hcred". iApply wp_value'. iApply ("H" with "Hcred").
  Qed.

  Lemma wp_struct_load vs i v E Φ :
    vs !! i = Some v →
    ▷ (£ 1 -∗ Φ v) ⊢ WP StructLoad (Val (StructV vs)) i @ E {{ Φ }}.
  Proof.
    iIntros (Hlook) "H".
    iApply wp_pure_step; [done| | |].
    - intros σ. eexists [], (Val v), σ, []. by econstructor.
    - intros ????? Hstep. inversion Hstep; simplify_eq; auto.
    - iIntros "!> Hcred". iApply wp_value'. iApply ("H" with "Hcred").
  Qed.

  Lemma wp_var_bind x v e Φ :
    (∀ l, StackId l ↦ₛ v -∗
       WP subst_var x l e {{ w, ∃ v', StackId l ↦ₛ v' ∗ Φ w }}) -∗
    WP VarBind x (Val v) e {{ Φ }}.
  Proof.
    iIntros "Hbody".
    iApply wp_lift_base_step; [done|].
    iIntros (σ ns κ κs nt) "(Hs & Hr & Hb & Ho & %Hwf)".
    iApply fupd_mask_intro; [set_solver|]. iIntros "Hclose".
    iSplit.
    { iPureIntro. eexists [], _, _, []. eapply (VarBindS x v e σ). }
    iIntros "!>" (e2 σ2 efs Hstep) "Hcred".
    iMod "Hclose" as "_".
    inversion Hstep; simplify_eq.
    iMod (ghost_map_insert (StackId (cjr_next σ)) v with "Hs") as "[Hs Hl]".
    { by eapply stack_fresh. }
    iModIntro.
    iSplitL "Hs Hr Hb Ho".
    { iFrame. iPureIntro. by apply wf_stack_alloc. }
    iSpecialize ("Hbody" $! l with "Hl").
    iSplitL "Hbody".
    { iApply (wp_bind [PopCtx (StackId l)]).
      iApply (wp_wand with "Hbody").
      iIntros (w) "Hrest".
      iApply wp_lift_atomic_base_step_no_fork; [done|].
    iIntros (σ' ns' κ' κs' nt') "(Hs' & Hr' & Hb' & Ho' & %Hwf')".
    iModIntro. iSplit.
    { iPureIntro. eexists [], (Val w), _, []. econstructor. }
    iIntros "!>" (e3 σ3 efs3 Hstep3) "_".
    inversion Hstep3; simplify_eq.
    iDestruct "Hrest" as (v') "[Hl HΦ]".
    iMod (ghost_map_delete with "Hs' Hl") as "Hs'".
    iModIntro. iSplit; [done|]. iSplitL "Hs' Hr' Hb' Ho'".
    { iFrame. iPureIntro. by apply wf_stack_delete. }
    iApply "HΦ". }
    done.
  Qed.

  Lemma wp_stack_load l v E Φ :
    l ↦ₛ v -∗ ▷ (£ 1 -∗ l ↦ₛ v -∗ Φ v) -∗
    WP StackLoad (Val (LitV (LitStack (match l with StackId z => z end)))) @ E {{ Φ }}.
  Proof.
    iIntros "Hl HΦ".
    iApply wp_lift_atomic_base_step_no_fork; [done|].
    iIntros (σ ns κ κs nt) "(Hs & Hr & Hb & Ho & %Hwf)".
    iDestruct (ghost_map_lookup with "Hs Hl") as %Hlook.
    iModIntro. iSplit.
    { iPureIntro. eexists [], (Val v), σ, []. by econstructor. }
    iIntros "!>" (e2 σ2 efs Hstep) "Hcred".
    assert (base_step (StackLoad (Val (LitV (LitStack (match l with StackId z => z end))))) σ [] (Val v) σ []) as Hgood.
    { econstructor. exact Hlook. }
    destruct (base_step_det _ _ _ _ _ _ _ _ _ _ Hstep Hgood) as (-> & -> & -> & ->).
    iModIntro. iSplit; [done|]. iSplitL "Hs Hr Hb Ho".
    { iFrame. done. }
    iApply ("HΦ" with "Hcred Hl").
  Qed.

  Lemma wp_stack_assign l v w E Φ :
    l ↦ₛ v -∗ ▷ (£ 1 -∗ l ↦ₛ w -∗ Φ (LitV LitUnit)) -∗
    WP StackAssign (Val (LitV (LitStack (match l with StackId z => z end)))) (Val w) @ E {{ Φ }}.
  Proof.
    destruct l as [z].
    iIntros "Hl HΦ".
    iApply wp_lift_atomic_base_step_no_fork; [done|].
    iIntros (σ ns κ κs nt) "(Hs & Hr & Hb & Ho & %Hwf)".
    iDestruct (ghost_map_lookup with "Hs Hl") as %Hlook.
    iModIntro. iSplit.
    { iPureIntro. eexists [], (Val (LitV LitUnit)), _, []. eapply StackAssignS. by eauto. }
    iIntros "!>" (e2 σ2 efs Hstep) "Hcred".
    assert (base_step (StackAssign (Val (LitV (LitStack z))) (Val w)) σ []
              (Val (LitV LitUnit)) (set_stack (<[StackId z := w]> (cjr_stack σ)) σ) []) as Hgood.
    { eapply StackAssignS. by eauto. }
    destruct (base_step_det _ _ _ _ _ _ _ _ _ _ Hstep Hgood) as (-> & -> & -> & ->).
    iMod (ghost_map_update w with "Hs Hl") as "[Hs Hl]".
    iModIntro. iSplit; [done|]. iSplitL "Hs Hr Hb Ho".
    { iFrame. iPureIntro. apply wf_stack_upd; [|done]. by eauto. }
    iApply ("HΦ" with "Hcred Hl").
  Qed.

  Lemma wp_stack_field l vs i w v E Φ :
    vs !! i = Some w →
    l ↦ₛ StructV vs -∗
    ▷ (£ 1 -∗ l ↦ₛ StructV (set_nth i v vs) -∗ Φ (LitV LitUnit)) -∗
    WP StackFieldStore (Val (LitV (LitStack (match l with StackId z => z end)))) i (Val v) @ E {{ Φ }}.
  Proof.
    destruct l as [z].
    iIntros (Hidx) "Hl HΦ".
    iApply wp_lift_atomic_base_step_no_fork; [done|].
    iIntros (σ ns κ κs nt) "(Hs & Hr & Hb & Ho & %Hwf)".
    iDestruct (ghost_map_lookup with "Hs Hl") as %Hlook.
    iModIntro. iSplit.
    { iPureIntro. eexists [], (Val (LitV LitUnit)), _, [].
      eapply (StackFieldS z i vs v σ w); [exact Hlook|exact Hidx]. }
    iIntros "!>" (e2 σ2 efs Hstep) "Hcred".
    assert (base_step (StackFieldStore (Val (LitV (LitStack z))) i (Val v)) σ []
              (Val (LitV LitUnit))
              (set_stack (<[StackId z := StructV (set_nth i v vs)]> (cjr_stack σ)) σ) []) as Hgood.
    { eapply (StackFieldS z i vs v σ w); [exact Hlook|exact Hidx]. }
    destruct (base_step_det _ _ _ _ _ _ _ _ _ _ Hstep Hgood) as (-> & -> & -> & ->).
    iMod (ghost_map_update (StructV (set_nth i v vs)) with "Hs Hl") as "[Hs Hl]".
    iModIntro. iSplit; [done|]. iSplitL "Hs Hr Hb Ho".
    { iFrame. iPureIntro. apply wf_stack_upd; [|done]. rewrite Hlook. by eauto. }
    iApply ("HΦ" with "Hcred Hl").
  Qed.

  Lemma wp_alloc_one E Φ :
    (∀ l, RawId l ↦ᵣ LitV (LitInt 0) -∗ RawId l ↦ᵦ 1 -∗ Φ (LitV (LitPtr l))) -∗
    WP Alloc (Val (LitV (LitInt 1))) @ E {{ Φ }}.
  Proof.
    iIntros "HΦ".
    iApply wp_lift_atomic_base_step_no_fork; [done|].
    iIntros (σ ns κ κs nt) "(Hs & Hr & Hb & Ho & %Hwf)".
    iModIntro. iSplit.
    { iPureIntro. eexists [], _, _, []. eapply (AllocS 1). lia. }
    iIntros "!>" (e2 σ2 efs Hstep) "Hcred".
    set (base := cjr_next σ).
    assert (base_step (Alloc (Val (LitV (LitInt 1)))) σ []
              (Val (LitV (LitPtr base)))
              (set_next (base + 1)%Z
                 (set_blocks (<[RawId base := 1%nat]> (cjr_blocks σ))
                    (set_raw (init_cells base 1 ∪ cjr_raw σ) σ))) []) as Hgood.
    { eapply (AllocS 1). lia. }
    destruct (base_step_det _ _ _ _ _ _ _ _ _ _ Hstep Hgood) as (-> & -> & -> & ->).
    rewrite init_cells_one.
    iMod (ghost_map_insert (RawId base) (LitV (LitInt 0)) with "Hr") as "[Hr Hl]".
    { by eapply raw_fresh. }
    iMod (ghost_map_insert (RawId base) 1%nat with "Hb") as "[Hb Hblk]".
    { by eapply block_fresh. }
    iModIntro. iSplit; [done|]. iSplitL "Hs Hr Hb Ho".
    { replace ({[RawId base := LitV (LitInt 0)]} ∪ cjr_raw σ)
        with (<[RawId base := LitV (LitInt 0)]> (cjr_raw σ))
        by (by rewrite insert_union_singleton_l).
      iFrame. iPureIntro. by apply wf_alloc_one_insert. }
    iApply ("HΦ" with "Hl Hblk").
  Qed.

  Lemma init_cells_sep base n :
    ([∗ map] k ↦ v ∈ init_cells base n,
       ghost_map_elem cjr_raw_name k (DfracOwn 1) v) ⊢
    [∗ list] k ↦ i ∈ seq 0 n, RawId (base + Z.of_nat i)%Z ↦ᵣ LitV (LitInt 0).
  Proof.
    revert base. induction n as [|n IH]; intros base.
    - cbn. rewrite big_sepM_empty. done.
    - cbn [init_cells].
      rewrite big_sepM_insert; last by (apply init_cells_high; lia).
      rewrite seq_S big_sepL_snoc.
      iIntros "[Hlast Hpre]".
      iSplitL "Hpre".
      + iApply (IH with "Hpre").
      + iFrame.
  Qed.

  Lemma wp_alloc (n : Z) E Φ :
    (0 < n)%Z →
    (∀ l, ([∗ list] i ∈ seq 0 (Z.to_nat n),
             RawId (l + Z.of_nat i)%Z ↦ᵣ LitV (LitInt 0)) -∗
           RawId l ↦ᵦ Z.to_nat n -∗ Φ (LitV (LitPtr l))) -∗
    WP Alloc (Val (LitV (LitInt n))) @ E {{ Φ }}.
  Proof.
    iIntros (Hn) "HΦ".
    iApply wp_lift_atomic_base_step_no_fork; [done|].
    iIntros (σ ns κ κs nt) "(Hs & Hr & Hb & Ho & %Hwf)".
    iModIntro. iSplit.
    { iPureIntro. eexists [], _, _, []. eapply (AllocS n). lia. }
    iIntros "!>" (e2 σ2 efs Hstep) "_".
    set (base := cjr_next σ).
    set (len := Z.to_nat n).
    assert (base_step (Alloc (Val (LitV (LitInt n)))) σ []
              (Val (LitV (LitPtr base)))
              (set_next (base + n)%Z
                 (set_blocks (<[RawId base := len]> (cjr_blocks σ))
                    (set_raw (init_cells base len ∪ cjr_raw σ) σ))) []) as Hgood.
    { eapply (AllocS n). lia. }
    destruct (base_step_det _ _ _ _ _ _ _ _ _ _ Hstep Hgood) as (-> & -> & -> & ->).
    iMod (ghost_map_insert_big (init_cells base len) with "Hr") as "[Hr Hcells]".
    { by apply init_cells_fresh. }
    iMod (ghost_map_insert (RawId base) len with "Hb") as "[Hb Hblk]".
    { by eapply block_fresh. }
    iModIntro. iSplit; [done|]. iSplitL "Hs Hr Hb Ho".
    { iFrame. iPureIntro. by apply wf_alloc. }
    iApply ("HΦ" with "[Hcells] Hblk").
    by iApply (init_cells_sep with "Hcells").
  Qed.

  Lemma wp_free_one l v E Φ :
    RawId l ↦ᵣ v -∗ RawId l ↦ᵦ 1 -∗ ▷ (£ 1 -∗ Φ (LitV LitUnit)) -∗
    WP Free (Val (LitV (LitPtr l))) @ E {{ Φ }}.
  Proof.
    iIntros "Hl Hblk HΦ".
    iApply wp_lift_atomic_base_step_no_fork; [done|].
    iIntros (σ ns κ κs nt) "(Hs & Hr & Hb & Ho & %Hwf)".
    iDestruct (ghost_map_lookup with "Hb Hblk") as %Hlen.
    iModIntro. iSplit.
    { iPureIntro. eexists [], (Val (LitV LitUnit)), _, []. eapply (FreeS l 1). exact Hlen. }
    iIntros "!>" (e2 σ2 efs Hstep) "Hcred".
    assert (base_step (Free (Val (LitV (LitPtr l)))) σ [] (Val (LitV LitUnit))
              (set_blocks (delete (RawId l) (cjr_blocks σ))
                 (set_raw (free_cells l 1 (cjr_raw σ)) σ)) []) as Hgood.
    { eapply (FreeS l 1). exact Hlen. }
    destruct (base_step_det _ _ _ _ _ _ _ _ _ _ Hstep Hgood) as (-> & -> & -> & ->).
    rewrite free_cells_one.
    iMod (ghost_map_delete with "Hr Hl") as "Hr".
    iMod (ghost_map_delete with "Hb Hblk") as "Hb".
    iModIntro. iSplit; [done|]. iSplitL "Hs Hr Hb Ho".
    { iFrame. iPureIntro. by eapply wf_free_one. }
    iApply ("HΦ" with "Hcred").
  Qed.

  Lemma wp_load l v E Φ :
    RawId l ↦ᵣ v -∗ ▷ (£ 1 -∗ RawId l ↦ᵣ v -∗ Φ v) -∗
    WP Load (Val (LitV (LitPtr l))) @ E {{ Φ }}.
  Proof.
    iIntros "Hl HΦ".
    iApply wp_lift_atomic_base_step_no_fork; [done|].
    iIntros (σ ns κ κs nt) "(Hs & Hr & Hb & Ho & %Hwf)".
    iDestruct (ghost_map_lookup with "Hr Hl") as %Hlook.
    iModIntro. iSplit.
    { iPureIntro. eexists [], (Val v), σ, []. by eapply (LoadS l v). }
    iIntros "!>" (e2 σ2 efs Hstep) "Hcred".
    assert (base_step (Load (Val (LitV (LitPtr l)))) σ [] (Val v) σ []) as Hgood.
    { by eapply (LoadS l v). }
    destruct (base_step_det _ _ _ _ _ _ _ _ _ _ Hstep Hgood) as (-> & -> & -> & ->).
    iModIntro. iSplit; [done|]. iSplitL "Hs Hr Hb Ho".
    { iFrame. done. }
    iApply ("HΦ" with "Hcred Hl").
  Qed.

  Lemma wp_store l v w E Φ :
    RawId l ↦ᵣ v -∗ ▷ (£ 1 -∗ RawId l ↦ᵣ w -∗ Φ (LitV LitUnit)) -∗
    WP Store (Val (LitV (LitPtr l))) (Val w) @ E {{ Φ }}.
  Proof.
    iIntros "Hl HΦ".
    iApply wp_lift_atomic_base_step_no_fork; [done|].
    iIntros (σ ns κ κs nt) "(Hs & Hr & Hb & Ho & %Hwf)".
    iDestruct (ghost_map_lookup with "Hr Hl") as %Hlook.
    iModIntro. iSplit.
    { iPureIntro. eexists [], (Val (LitV LitUnit)), _, []. eapply StoreS. by eauto. }
    iIntros "!>" (e2 σ2 efs Hstep) "Hcred".
    assert (base_step (Store (Val (LitV (LitPtr l))) (Val w)) σ []
              (Val (LitV LitUnit)) (set_raw (<[RawId l := w]> (cjr_raw σ)) σ) []) as Hgood.
    { eapply StoreS. by eauto. }
    destruct (base_step_det _ _ _ _ _ _ _ _ _ _ Hstep Hgood) as (-> & -> & -> & ->).
    iMod (ghost_map_update w with "Hr Hl") as "[Hr Hl]".
    iModIntro. iSplit; [done|]. iSplitL "Hs Hr Hb Ho".
    { iFrame. iPureIntro. apply wf_raw_store; [|done]. by eauto. }
    iApply ("HΦ" with "Hcred Hl").
  Qed.

  Lemma init_fields_sep o vs i :
    ([∗ map] k ↦ v ∈ init_fields o vs i,
       ghost_map_elem cjr_obj_name k (DfracOwn 1) v) ⊢
    [∗ list] k ↦ v ∈ vs, ObjId o ↦ₒ[(i + k)%nat] v.
  Proof.
    revert i. induction vs as [|v vs IH]; intros i; simpl.
    - by rewrite big_sepM_empty.
    - rewrite big_sepM_insert; last (by rewrite init_fields_low; [|lia]).
      rewrite (IH (S i)) Nat.add_0_r.
      apply bi.sep_mono_r, big_sepL_mono. intros k w _.
      by rewrite Nat.add_succ_r Nat.add_succ_l.
  Qed.

  Lemma wp_new vs E Φ :
    (∀ o, ([∗ list] i ↦ v ∈ vs, ObjId o ↦ₒ[i] v) -∗ Φ (LitV (LitObj o))) -∗
    WP New vs [] @ E {{ Φ }}.
  Proof.
    iIntros "HΦ".
    iApply wp_lift_atomic_base_step_no_fork; [done|].
    iIntros (σ ns κ κs nt) "(Hs & Hr & Hb & Ho & %Hwf)".
    iModIntro. iSplit.
    { iPureIntro. eexists [], (Val (LitV (LitObj (cjr_next σ)))), _, [].
      exact (NewDoneS vs σ). }
    iIntros "!>" (e2 σ2 efs Hstep) "_".
    set (o := cjr_next σ).
    assert (base_step (New vs []) σ [] (Val (LitV (LitObj o)))
              (set_next (o + 1) (set_obj (init_fields o vs 0 ∪ cjr_obj σ) σ)) []) as Hgood.
    { apply NewDoneS. }
    destruct (base_step_det _ _ _ _ _ _ _ _ _ _ Hstep Hgood) as (-> & -> & -> & ->).
    iMod (ghost_map_insert_big (init_fields o vs 0) with "Ho") as "[Ho Hfields]";
      first by apply init_fields_fresh.
    iModIntro. iSplit; [done|]. iSplitL "Hs Hr Hb Ho".
    { iFrame. iPureIntro. by apply wf_new. }
    iDestruct (init_fields_sep o vs 0 with "Hfields") as "Hfields".
    iApply "HΦ". iApply (big_sepL_mono with "Hfields").
    iIntros (k v _) "Hk". by rewrite Nat.add_0_l.
  Qed.

  Lemma wp_field_load o i v E Φ :
    ObjId o ↦ₒ[i] v -∗ ▷ (£ 1 -∗ ObjId o ↦ₒ[i] v -∗ Φ v) -∗
    WP FieldLoad (Val (LitV (LitObj o))) i @ E {{ Φ }}.
  Proof.
    iIntros "Hl HΦ".
    iApply wp_lift_atomic_base_step_no_fork; [done|].
    iIntros (σ ns κ κs nt) "(Hs & Hr & Hb & Ho & %Hwf)".
    iDestruct (ghost_map_lookup with "Ho Hl") as %Hlook.
    iModIntro. iSplit.
    { iPureIntro. eexists [], (Val v), σ, []. by eapply (FieldLoadS o i v). }
    iIntros "!>" (e2 σ2 efs Hstep) "Hcred".
    assert (base_step (FieldLoad (Val (LitV (LitObj o))) i) σ [] (Val v) σ []) as Hgood.
    { by eapply (FieldLoadS o i v). }
    destruct (base_step_det _ _ _ _ _ _ _ _ _ _ Hstep Hgood) as (-> & -> & -> & ->).
    iModIntro. iSplit; [done|]. iSplitL "Hs Hr Hb Ho".
    { iFrame. done. }
    iApply ("HΦ" with "Hcred Hl").
  Qed.

  Lemma wp_field_store o i v w E Φ :
    ObjId o ↦ₒ[i] v -∗
    ▷ (£ 1 -∗ ObjId o ↦ₒ[i] w -∗ Φ (LitV LitUnit)) -∗
    WP FieldStore (Val (LitV (LitObj o))) i (Val w) @ E {{ Φ }}.
  Proof.
    iIntros "Hl HΦ".
    iApply wp_lift_atomic_base_step_no_fork; [done|].
    iIntros (σ ns κ κs nt) "(Hs & Hr & Hb & Ho & %Hwf)".
    iDestruct (ghost_map_lookup with "Ho Hl") as %Hlook.
    iModIntro. iSplit.
    { iPureIntro. eexists [], (Val (LitV LitUnit)), _, []. eapply FieldStoreS. by eauto. }
    iIntros "!>" (e2 σ2 efs Hstep) "Hcred".
    assert (base_step (FieldStore (Val (LitV (LitObj o))) i (Val w)) σ []
              (Val (LitV LitUnit))
              (set_obj (<[(ObjId o, i) := w]> (cjr_obj σ)) σ) []) as Hgood.
    { eapply FieldStoreS. by eauto. }
    destruct (base_step_det _ _ _ _ _ _ _ _ _ _ Hstep Hgood) as (-> & -> & -> & ->).
    iMod (ghost_map_update w with "Ho Hl") as "[Ho Hl]".
    iModIntro. iSplit; [done|]. iSplitL "Hs Hr Hb Ho".
    { iFrame. iPureIntro. apply wf_field_store; [|done]. by eauto. }
    iApply ("HΦ" with "Hcred Hl").
  Qed.
End laws.
