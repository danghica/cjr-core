(** Kernel-checked regressions for generic source scope and extraction. *)
From Coq Require Import String List.
From cjr Require Import generics.
From cjr.examples Require Import generic_print generic_examples.
Import ListNotations.
Local Open Scope string_scope.

Definition expression_errors e := check_expr generic_layouts generic_functions [] [] e.
Definition rejected p := match print_generic_program p with Rejected _ => true | _ => false end.

Example nested_type_substitution :
  gty_subst [("T", GTBool)] (box_ty (pair_ty tT (box_ty tT))) =
  box_ty (pair_ty GTBool (box_ty GTBool)).
Proof. reflexivity. Qed.
Example simultaneous_type_substitution :
  gty_subst [("T", tU); ("U", GTInt)] tT = tU.
Proof. reflexivity. Qed.
Example nested_type_well_formed :
  gty_wf generic_layouts [] (box_ty (pair_ty GTInt GTBool)) = true.
Proof. reflexivity. Qed.
Example unbound_type_rejected :
  expression_errors (GECall "genericId" [tT] [GEVal (LitV (LitInt 1))]) =
  ["unbound type variable, unknown type, or wrong type arity"].
Proof. reflexivity. Qed.
Example wrong_type_arity_rejected :
  expression_errors (GECall "genericId" [] [GEVal (LitV (LitInt 1))]) =
  ["wrong type arity: genericId"].
Proof. reflexivity. Qed.
Example wrong_value_arity_rejected :
  expression_errors (GECall "genericId" [GTInt] []) = ["wrong argument arity: genericId"].
Proof. reflexivity. Qed.
Example unknown_reference_rejected :
  expression_errors (GECall "missing" [] []) =
  ["unresolved function (declare dependencies first): missing"].
Proof. reflexivity. Qed.
Example invalid_method_type_arity_rejected :
  check_expr generic_layouts generic_functions [] ["b"; "f"]
    (GEMethod (box_ty GTInt) (GEVar "b") "map" [] [GEVar "f"]) =
  ["wrong method type arity: map"].
Proof. reflexivity. Qed.
Example invalid_constructor_arity_rejected :
  expression_errors (GEConstruct (box_ty GTBool) []) = ["wrong constructor arity: Box"].
Proof. reflexivity. Qed.
Example invalid_field_rejected :
  check_expr generic_layouts generic_functions [] ["b"] (GEField (box_ty GTInt) (GEVar "b") 1) =
  ["field index out of range: Box"].
Proof. reflexivity. Qed.
Example nominal_type_arity_rejected :
  gty_wf generic_layouts [] (GTNamed "Pair" [GTInt]) = false.
Proof. reflexivity. Qed.
Example method_parameter_shadowing_rejected :
  rejected (GProgram generic_layouts
    [GFunction "bad" (Some "Box") ["T"] [("self", box_ty tT)] tT box_get_body]
    (GEVal (LitV LitUnit))) = true.
Proof. vm_compute. reflexivity. Qed.
Example internal_binder_rejected :
  rejected (GProgram [] [GFunction "bad" None [] [("$args", GTInt)] GTInt (GEVar "$args")]
    (GEVal (LitV LitUnit))) = true.
Proof. vm_compute. reflexivity. Qed.
Example duplicate_declaration_rejected :
  rejected (GProgram [] [identity_fn; identity_fn] (GEVal (LitV LitUnit))) = true.
Proof. vm_compute. reflexivity. Qed.
Example legacy_embedding_rejected_by_generic_printer :
  rejected (GProgram [] [] (GECore (Val (LitV LitUnit)))) = true.
Proof. reflexivity. Qed.
Example unbound_local_rejected : expression_errors (GEVar "x") = ["unbound local: x"].
Proof. reflexivity. Qed.
Example identical_bodies_have_distinct_references :
  print_expr generic_layouts (GECall "genericId" [GTBool] [GEVal (LitV (LitBool true))]) = "genericId<Bool>(true)" ∧
  print_expr generic_layouts (GECall "genericIdAgain" [GTBool] [GEVal (LitV (LitBool true))]) = "genericIdAgain<Bool>(true)".
Proof. split; reflexivity. Qed.
Example identical_layout_sizes_have_distinct_names :
  print_expr generic_layouts (GEConstruct (GTNamed "OtherBox" [GTInt]) [GEVal (LitV (LitInt 3))]) = "OtherBox<Int64>(3)" ∧
  print_expr generic_layouts (GEField (GTNamed "OtherPair" [GTInt; GTBool]) (GEVar "p") 1) = "(({ cjrTypedValue: OtherPair<Int64, Bool> => cjrTypedValue })(p)).right" ∧
  print_expr generic_layouts (GEField (pair_ty GTInt GTBool) (GEVar "p") 1) = "(({ cjrTypedValue: Pair<Int64, Bool> => cjrTypedValue })(p)).second".
Proof. repeat split; reflexivity. Qed.
Example source_substitution_respects_shadowing :
  gsubst "x" (LitV (LitInt 3)) (GELet (Some "x") (GEVar "x") (GEVar "x")) =
    GELet (Some "x") (GEVal (LitV (LitInt 3))) (GEVar "x").
Proof. reflexivity. Qed.
Example map_erasure_uniform s :
  erase generic_layouts generic_runtime (ginstantiate s box_map_body) =
  erase generic_layouts generic_runtime box_map_body.
Proof. apply erase_instantiate. reflexivity. Qed.
Example recursive_reference_is_bound :
  erase generic_layouts [] (GECall "repeatIdentity" [GTInt]
    [GEVar "x"; GEVar "n"]) =
  App (Var "repeatIdentity") (Struct [] [Var "x"; Var "n"]).
Proof. reflexivity. Qed.
Example forward_reference_rejected :
  rejected (GProgram []
    [GFunction "first" None [] [] GTInt (GECall "later" [] []);
     GFunction "later" None [] [] GTInt (GEVal (LitV (LitInt 0)))]
    (GEVal (LitV LitUnit))) = true.
Proof. vm_compute. reflexivity. Qed.

Example declaration_shadowing_rejected :
  rejected (GProgram generic_layouts generic_functions
    (GELet (Some "genericId") (GELam "z" GTInt GTInt (GEVar "z"))
      (GECall "genericId" [GTInt] [GEVal (LitV (LitInt 1))]))) = true.
Proof. vm_compute. reflexivity. Qed.
