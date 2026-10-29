(** A call stores through one pointer. A second pointer is framed. *)
From iris.proofmode Require Import proofmode.
From cjr Require Import notation primitive_laws.
From iris.prelude Require Import options.
Open Scope expr_scope.

Definition write_call (p q : Z) : expr :=
  Let (Some "f")
    (Rec None (Some "x") (Store (Var "x") (Val (LitV (LitInt 9)))))
    (Seq
      (App (Var "f") (Val (LitV (LitPtr p))))
      (Load (Val (LitV (LitPtr q))))).

Lemma write_call_wp `{!cjrGS Σ} `{!invGS_gen HasLc Σ} (p q : Z) v :
  RawId p ↦ᵣ v -∗ RawId q ↦ᵣ LitV (LitInt 3) -∗
  WP write_call p q {{ w, ⌜ w = LitV (LitInt 3) ⌝ ∗
                         RawId p ↦ᵣ LitV (LitInt 9) ∗
                         RawId q ↦ᵣ LitV (LitInt 3) }}.
Proof.
  iIntros "Hp Hq".
  iApply (wp_bind [LetCtx (Some "f")
    (Seq (App (Var "f") (Val (LitV (LitPtr p))))
         (Load (Val (LitV (LitPtr q)))))]).
  iApply wp_rec.
  iIntros "!> _".
  iApply wp_let. simpl.
  set (f := RecV None (Some "x") (Store (Var "x") (Val (LitV (LitInt 9))))).
  iApply (wp_bind [SeqCtx (Load (Val (LitV (LitPtr q))))]).
  iApply wp_app.
  simpl.
  iApply (wp_store with "Hp").
  iIntros "!> _ Hp".
  iApply wp_seq.
  iApply (wp_load with "Hq").
  iIntros "!> _ Hq".
  iFrame. done.
Qed.
