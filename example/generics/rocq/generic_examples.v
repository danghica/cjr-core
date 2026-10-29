(** One source for verification and extraction: no hand-written generic bodies
    are substituted by the printer. *)
From iris.proofmode Require Import proofmode.
From cjr Require Import generic_laws.
From cjr.examples Require Import generic_print.
From iris.prelude Require Import options.
Import ListNotations.
Local Open Scope string_scope.

Definition tA := GTVar "A".
Definition tB := GTVar "B".
Definition tT := GTVar "T".
Definition tU := GTVar "U".
Definition pair_ty a b := GTNamed "Pair" [a; b].
Definition box_ty t := GTNamed "Box" [t].
Definition pair_layout := GLayout "Pair" GStruct ["A"; "B"] [("first", tA); ("second", tB)].
Definition box_layout := GLayout "Box" GClass ["T"] [("value", tT)].
Definition other_pair_layout := GLayout "OtherPair" GStruct ["A"; "B"] [("left", tA); ("right", tB)].
Definition other_box_layout := GLayout "OtherBox" GClass ["T"] [("item", tT)].
Definition generic_layouts := [pair_layout; box_layout; other_pair_layout; other_box_layout].

Definition identity_body := GEVar "x".
Definition identity_fn := GFunction "genericId" None ["T"] [("x", tT)] tT identity_body.
Definition identity_again_fn := GFunction "genericIdAgain" None ["T"] [("x", tT)] tT identity_body.
Definition first_body := GEField (pair_ty tA tB) (GEVar "p") 0.
Definition second_body := GEField (pair_ty tA tB) (GEVar "p") 1.
Definition first_fn := GFunction "firstOf" None ["A"; "B"] [("p", pair_ty tA tB)] tA first_body.
Definition second_fn := GFunction "secondOf" None ["A"; "B"] [("p", pair_ty tA tB)] tB second_body.
Definition box_get_body := GEField (box_ty tT) (GEVar "self") 0.
Definition box_get_fn := GFunction "get" (Some "Box") [] [("self", box_ty tT)] tT box_get_body.
Definition box_map_body :=
  GEConstruct (box_ty tU)
    [GEApp (GEVar "f") (GEField (box_ty tT) (GEVar "self") 0)].
Definition box_map_fn := GFunction "map" (Some "Box") ["U"]
  [("self", box_ty tT); ("f", GTArrow tT tU)] (box_ty tU) box_map_body.
Definition recursive_body :=
  GEIf (GEBinOp LeOp (GEVar "n") (GEVal (LitV (LitInt 0)))) (GEVar "x")
    (GECall "repeatIdentity" [tT]
      [GEVar "x"; GEBinOp MinusOp (GEVar "n") (GEVal (LitV (LitInt 1)))]).
Definition recursive_fn := GFunction "repeatIdentity" None ["T"]
  [("x", tT); ("n", GTInt)] tT recursive_body.
Definition make_pair_body := GEConstruct (pair_ty tA tB) [GEVar "a"; GEVar "b"].
Definition make_pair_fn := GFunction "makePair" None ["A"; "B"]
  [("a", tA); ("b", tB)] (pair_ty tA tB) make_pair_body.
Definition make_box_fn := GFunction "makeBox" None ["T"] [("x", tT)] (box_ty tT)
  (GEConstruct (box_ty tT) [GEVar "x"]).
Definition positive_box_body :=
  GELet (Some "b") (GEConstruct (box_ty GTInt) [GEVar "n"])
    (GEMethod (box_ty GTBool)
      (GEMethod (box_ty GTInt) (GEVar "b") "map" [GTBool]
        [GELam "x" GTInt GTBool (GEBinOp LeOp (GEVal (LitV (LitInt 0))) (GEVar "x"))])
      "get" [] []).
Definition positive_box_fn := GFunction "positiveBox" None [] [("n", GTInt)] GTBool positive_box_body.
Definition strict_and_fn := GFunction "strictAnd" None [] [("f", GTArrow GTUnit GTBool)] GTBool
  (GEBinOp AndOp (GEVal (LitV (LitBool false))) (GEApp (GEVar "f") (GEVal (LitV LitUnit)))).
Definition generic_functions :=
  [identity_fn; identity_again_fn; first_fn; second_fn; box_get_fn; box_map_fn; recursive_fn; make_pair_fn; make_box_fn; positive_box_fn; strict_and_fn].
Definition generic_main := GECall "genericId" [GTInt] [GEVal (LitV (LitInt 42))].
Definition generic_program := GProgram generic_layouts generic_functions generic_main.
Definition generic_runtime := link_functions generic_layouts [] generic_functions.

Example generic_program_valid : check_program generic_program = [].
Proof. vm_compute. reflexivity. Qed.

Section proofs.
  Context `{!cjrGS Σ} `{!invGS_gen HasLc Σ}.

  (** An element representation can own resources. No persistence or
      duplicability is assumed. *)
  Definition pair_rep (R S : val → iProp Σ) (p : val) : iProp Σ :=
    ∃ a b, ⌜p = StructV [a; b]⌝ ∗ R a ∗ S b.
  Definition box_rep (R : val → iProp Σ) (p : val) : iProp Σ :=
    ∃ o v, ⌜p = LitV (LitObj o)⌝ ∗ ObjId o ↦ₒ[0] v ∗ R v.

  Lemma identity_spec (R : val → iProp Σ) t v :
    R v -∗ generic_wp generic_layouts generic_runtime
      (GECall "genericId" [t] [GEVal v]) (λ w, ⌜w = v⌝ ∗ R w).
  Proof.
    iIntros "HR". unfold generic_wp. simpl.
    iApply (wp_bind [AppRCtx _]). iApply (wp_generic_pack_acc [] [v]). simpl.
    iApply wp_app. simpl.
    iApply (wp_bind [LetCtx (Some "x") (Var "x")]).
    iApply wp_struct_load; [done|]. iIntros "!> _".
    iApply wp_let. simpl. iApply wp_value'. iFrame. done.
  Qed.

  Lemma pair_construct_spec (R S : val → iProp Σ) ta tb a b :
    R a -∗ S b -∗ generic_wp generic_layouts generic_runtime
      (GEConstruct (pair_ty ta tb) [GEVal a; GEVal b]) (pair_rep R S).
  Proof.
    iIntros "Ha Hb". unfold generic_wp. simpl.
    iApply (wp_generic_pack_acc [] [a; b]). simpl. iExists a, b. iFrame. done.
  Qed.

  (** Projection returns the selected value and preserves both resources;
      it does not create a second copy of the selected resource. *)
  Lemma pair_first_spec (R S : val → iProp Σ) ta tb p :
    pair_rep R S p -∗ generic_wp generic_layouts generic_runtime
      (GECall "firstOf" [ta; tb] [GEVal p])
      (λ w, ∃ b, ⌜p = StructV [w; b]⌝ ∗ R w ∗ S b).
  Proof.
    iIntros "Hp". iDestruct "Hp" as (a b ->) "[Ha Hb]".
    unfold generic_wp. simpl. iApply (wp_bind [AppRCtx _]).
    iApply (wp_generic_pack_acc [] [StructV [a; b]]). simpl. iApply wp_app. simpl.
    iApply (wp_bind [LetCtx (Some "p") (StructLoad (Var "p") 0)]).
    iApply wp_struct_load; [done|]. iIntros "!> _".
    iApply wp_let. simpl. iApply wp_struct_load; [done|].
    iIntros "!> _". iExists b. iFrame. done.
  Qed.

  Lemma pair_second_spec (R S : val → iProp Σ) ta tb p :
    pair_rep R S p -∗ generic_wp generic_layouts generic_runtime
      (GECall "secondOf" [ta; tb] [GEVal p])
      (λ w, ∃ a, ⌜p = StructV [a; w]⌝ ∗ R a ∗ S w).
  Proof.
    iIntros "Hp". iDestruct "Hp" as (a b ->) "[Ha Hb]".
    unfold generic_wp. simpl. iApply (wp_bind [AppRCtx _]).
    iApply (wp_generic_pack_acc [] [StructV [a; b]]). simpl. iApply wp_app. simpl.
    iApply (wp_bind [LetCtx (Some "p") (StructLoad (Var "p") 1)]).
    iApply wp_struct_load; [done|]. iIntros "!> _".
    iApply wp_let. simpl. iApply wp_struct_load; [done|].
    iIntros "!> _". iExists a. iFrame. done.
  Qed.

  Lemma box_construct_spec (R : val → iProp Σ) t v :
    R v -∗ generic_wp generic_layouts generic_runtime
      (GEConstruct (box_ty t) [GEVal v]) (box_rep R).
  Proof.
    iIntros "HR". unfold generic_wp. simpl. iApply wp_generic_new_step. simpl.
    iApply wp_new. iIntros (o) "[Ho _]". iExists o, v. iFrame. done.
  Qed.

  Lemma box_get_spec (R : val → iProp Σ) t p :
    box_rep R p -∗ generic_wp generic_layouts generic_runtime
      (GEMethod (box_ty t) (GEVal p) "get" [] [])
      (λ w, ∃ o, ⌜p = LitV (LitObj o)⌝ ∗ ObjId o ↦ₒ[0] w ∗ R w).
  Proof.
    iIntros "Hp". iDestruct "Hp" as (o v ->) "[Ho HR]".
    unfold generic_wp. simpl. iApply (wp_bind [AppRCtx _]).
    iApply (wp_generic_pack_acc [] [LitV (LitObj o)]). simpl. iApply wp_app. simpl.
    iApply (wp_bind [LetCtx (Some "self") (FieldLoad (Var "self") 0)]).
    iApply wp_struct_load; [done|]. iIntros "!> _".
    iApply wp_let. simpl. iApply (wp_field_load with "Ho").
    iIntros "!> _ Ho". iExists o. iFrame. done.
  Qed.

  (** The callback consumes R and produces S. The old object's raw field is
      framed, but its R resource moves to the callback, not copied. A closed
      callback is stable under the source function's parameter substitutions. *)
  Lemma box_map_spec (R S : val → iProp Σ) t u o v f :
    (∀ x w, subst_val x w f = f) →
    ObjId o ↦ₒ[0] v -∗ R v -∗
    (∀ a, R a -∗ WP App (Val f) (Val a) {{ S }}) -∗
    generic_wp generic_layouts generic_runtime
      (GEMethod (box_ty t) (GEVal (LitV (LitObj o))) "map" [u] [GEVal f])
      (λ p, ObjId o ↦ₒ[0] v ∗ box_rep S p).
  Proof.
    intros Hclosed. iIntros "Ho HR Hf". unfold generic_wp. simpl.
    iApply (wp_bind [AppRCtx _]). iApply (wp_generic_pack_acc [] [LitV (LitObj o); f]). simpl.
    iApply wp_app. simpl.
    repeat rewrite Hclosed.
    iApply (wp_bind [LetCtx (Some "self")
      (Let (Some "f") (StructLoad (Val (StructV [LitV (LitObj o); f])) 1)
        (New [] [App (Var "f") (FieldLoad (Var "self") 0)]))]).
    iApply wp_struct_load; [done|]. iIntros "!> _".
    iApply wp_let. simpl. repeat rewrite Hclosed.
    iApply (wp_bind [LetCtx (Some "f")
      (New [] [App (Var "f") (FieldLoad (Val (LitV (LitObj o))) 0)])]).
    iApply wp_struct_load; [done|]. iIntros "!> _".
    iApply wp_let. simpl.
    iApply (wp_bind [AppRCtx f; NewCtx [] []]).
    iApply (wp_field_load with "Ho"). iIntros "!> _ Ho".
    iApply (wp_bind [NewCtx [] []]).
    iApply (wp_wand with "[HR Hf]").
    { iApply ("Hf" with "HR"). }
    iIntros (w) "HS". iApply wp_generic_new_step. simpl.
    iApply wp_new. iIntros (o') "[Ho' _]". iFrame "Ho".
    iExists o', w. iFrame. done.
  Qed.

  Lemma generic_main_wp :
    ⊢ generic_wp generic_layouts generic_runtime generic_main
      (λ v, ⌜v = LitV (LitInt 42)⌝).
  Proof.
    iApply (wp_wand with "[]").
    { iApply (identity_spec (λ _, True)%I). done. }
    iIntros (v) "[H _]". iExact "H".
  Qed.
End proofs.

Lemma generic_main_adequate Σ `{!cjrGpreS Σ} :
  adequate NotStuck (erase_program generic_program) state_init
    (λ v _, v = LitV (LitInt 42)).
Proof. apply (generic_adequacy Σ). intros ??. apply generic_main_wp. Qed.
