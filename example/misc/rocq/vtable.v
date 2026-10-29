(** A struct holds a function pointer. Calling it increments a class field. *)
From iris.proofmode Require Import proofmode.
From cjr Require Import notation primitive_laws adequacy.
From iris.prelude Require Import options.
Open Scope expr_scope.

Definition inc_body : expr :=
  FieldStore (Var "this") 0
    (FieldLoad (Var "this") 0 + Val (LitV (LitInt 1))).

Definition vtable_prog : expr :=
  Let (Some "inc") (Rec None (Some "this") inc_body)
    (Let (Some "box") (Struct [] [Var "inc"])
      (Let (Some "o") (New [LitV (LitInt 0)] [])
        (Seq
          (App (StructLoad (Var "box") 0) (Var "o"))
          (FieldLoad (Var "o") 0)))).

Lemma vtable_prog_wp `{!cjrGS Σ} `{!invGS_gen HasLc Σ} :
  ⊢ WP vtable_prog {{ v, ⌜ v = LitV (LitInt 1) ⌝ }}.
Proof.
  iApply (wp_bind [LetCtx (Some "inc")
    (Let (Some "box") (Struct [] [Var "inc"])
      (Let (Some "o") (New [LitV (LitInt 0)] [])
        (Seq (App (StructLoad (Var "box") 0) (Var "o"))
             (FieldLoad (Var "o") 0))))]).
  iApply wp_rec. iIntros "!> _".
  iApply wp_let. simpl.
  set (inc := RecV None (Some "this") inc_body).
  iApply (wp_bind [LetCtx (Some "box")
    (Let (Some "o") (New [LitV (LitInt 0)] [])
      (Seq (App (StructLoad (Var "box") 0) (Var "o"))
           (FieldLoad (Var "o") 0)))]).
  iApply (wp_bind [StructCtx [] []]).
  iApply wp_value'.
  iApply wp_pure_step; [done| | |].
  { intros σ. eexists [], (Struct [inc] []), σ, []. constructor. }
  { intros ????? Hstep. inversion Hstep; simplify_eq; auto. }
  iIntros "!> _".
  iApply wp_struct_done.
  iIntros "!> _".
  iApply wp_let. simpl.
  iApply (wp_bind [LetCtx (Some "o")
    (Seq (App (StructLoad (Val (StructV [inc])) 0) (Var "o"))
         (FieldLoad (Var "o") 0))]).
  iApply wp_new. iIntros (o) "Ho".
  iDestruct "Ho" as "[Ho _]".
  iApply wp_let. simpl.
  iApply (wp_bind [SeqCtx (FieldLoad (Val (LitV (LitObj o))) 0)]).
  iApply (wp_bind [AppLCtx (Val (LitV (LitObj o)))]).
  iApply (wp_struct_load [inc] 0 inc).
  { done. }
  iIntros "!> _".
  iApply wp_app. simpl.
  iApply (wp_bind [FieldStoreRCtx (LitV (LitObj o)) 0]).
  iApply (wp_bind [BinOpLCtx PlusOp (Val (LitV (LitInt 1)))]).
  iApply (wp_field_load with "Ho").
  iIntros "!> _ Ho".
  iApply wp_binop; [by vm_compute|].
  iIntros "!> _".
  iApply (wp_field_store with "Ho").
  iIntros "!> _ Ho".
  iApply wp_seq.
  iApply (wp_field_load with "Ho").
  iIntros "!> _ _". done.
Qed.

Lemma vtable_adequate Σ `{!cjrGpreS Σ} :
  adequate NotStuck vtable_prog state_init (λ v _, v = LitV (LitInt 1)).
Proof. eapply (cjr_adequacy Σ). intros ??. apply vtable_prog_wp. Qed.
