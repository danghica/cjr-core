(** Initialized generic storage, derived entirely from the existing core.
    One modeled word holds one CJR value; native byte layout is not assumed. *)
From Coq Require Import String List.
From cjr Require Export lang.
Import ListNotations.
Local Open Scope string_scope.

Definition closed_val (v : val) : Prop := ∀ x w, subst_val x w v = v.

Definition buffer_fill_body : expr :=
  Let (Some "$p") (StructLoad (Var "$fillArgs") 0)
  (Let (Some "$n") (StructLoad (Var "$fillArgs") 1)
  (Let (Some "$seed") (StructLoad (Var "$fillArgs") 2)
    (If (BinOp LeOp (Var "$n") (Val (LitV (LitInt 0))))
      (Val (LitV LitUnit))
      (Let (Some "$k") (BinOp MinusOp (Var "$n") (Val (LitV (LitInt 1))))
      (Let None (Store (Offset (Var "$p") (Var "$k")) (Var "$seed"))
        (App (Var "$fill") (Struct [] [Var "$p"; Var "$k"; Var "$seed"]))))))).
Definition buffer_fill_val : val :=
  RecV (Some "$fill") (Some "$fillArgs") buffer_fill_body.

Definition buffer_make_body : expr :=
  Let (Some "$size") (StructLoad (Var "$makeArgs") 0)
  (Let (Some "$seed") (StructLoad (Var "$makeArgs") 1)
  (Let (Some "$base") (Alloc (Var "$size"))
  (Let None (App (Val buffer_fill_val)
     (Struct [] [Var "$base"; Var "$size"; Var "$seed"]))
     (Var "$base")))).
Definition buffer_make_val : val := RecV None (Some "$makeArgs") buffer_make_body.

Lemma buffer_fill_closed : closed_val buffer_fill_val.
Proof.
  intros x w. unfold buffer_fill_val, buffer_fill_body.
  simpl. repeat case_bool_decide; simplify_eq; simpl; done.
Qed.
Lemma buffer_make_closed : closed_val buffer_make_val.
Proof.
  intros x w. unfold buffer_make_val, buffer_make_body.
  cbn -[buffer_fill_val].
  repeat case_bool_decide; simplify_eq; cbn -[buffer_fill_val];
    rewrite ?buffer_fill_closed; done.
Qed.

Lemma closed_lit l : closed_val (LitV l).
Proof. done. Qed.
