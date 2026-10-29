From Coq Require Import String ZArith List.
From cjr Require Import lang.
From cjr.examples Require Import cj_print generic_print.
Import ListNotations.
Local Open Scope string_scope.
From cjr.examples Require arith struct_upd cell swap sum_block class_upd frame_call vtable.
From cjr.examples Require Import generic_examples.
Definition int (n : Z) : expr := Val (LitV (LitInt n)).
Definition unit_e : expr := Val (LitV LitUnit).

Definition t_int := "Int64".
Definition t_ptr := "CPointer<Int64>".

(** * Layouts *)

Definition cell_s := Decl "Cell" [("x", t_int)].
Definition box_c := Decl "Box" [("value", t_int)].
Definition counter_c := Decl "Counter" [("value", t_int)].
Definition vtable_s := Decl "VTable" [("inc", "(Counter) -> Unit")].
Definition node_c := Decl "Node" [("isCons", "Bool"); ("value", t_int); ("next", "Node")].
Definition array_c := Decl "Array" [("len", t_int); ("data", t_ptr)].
Definition array_list_c :=
  Decl "ArrayList" [("myData", "Array"); ("mySize", t_int); ("myVersion", t_int)].
Definition hash_map_c :=
  Decl "HashMap" [("mySize", t_int); ("tags", "Array"); ("keys", "Array"); ("vals", "Array")].
Definition probe_result_s :=
  Decl "ProbeResult" [("found", "Bool"); ("index", t_int); ("value", t_int)].
Definition int64_opt_c :=
  Decl "Int64Option" [("ok", "Bool"); ("value", t_int)].

(** * Straight-line examples *)

Definition sum_one_fn := Fn "sumOne" None None arith.sum_one [] t_int.
Definition p_arith := Prog [] [] [sum_one_fn; Fn "multiply" None (Some "args") arith.multiply_body [t_int; t_int] t_int; Fn "divide" None (Some "args") arith.divide_body [t_int; t_int] t_int] arith.sum_one.

Definition p_struct_upd :=
  Prog [] [cell_s]
    [Fn "bump" None None struct_upd.bump [] t_int;
     Fn "bumpKeep" None None struct_upd.bump_keep [] t_int]
    struct_upd.bump_keep.

Definition p_cell := Prog [] [] [Fn "cell" None None cell.cell [] "Unit"] cell.cell.

Definition p_class_upd :=
  Prog [box_c] [] [Fn "classBump" None None class_upd.class_bump [] t_int]
    class_upd.class_bump.

Definition p_vtable :=
  Prog [counter_c] [vtable_s]
    [Fn "inc" None (Some "this") vtable.inc_body ["Counter"] "Unit";
     Fn "run" None None vtable.vtable_prog [] t_int]
    vtable.vtable_prog.

(** * Examples over raw addresses

The placeholder pointers are renamed back to the parameters they stand for. *)

Definition swap_body : expr :=
  Let (Some "l1") (StructLoad (Var "args") 0)
    (Let (Some "l2") (StructLoad (Var "args") 1)
      (rename_ptr 0 "l1" (rename_ptr 1 "l2" (swap.swap_at 0 1)))).

Definition p_swap :=
  Prog [] [] [Fn "swap" None (Some "args") swap_body [t_ptr; t_ptr] "Unit"]
    (Let (Some "l1") (Alloc (int 1))
      (Let (Some "l2") (Alloc (int 1))
        (Seq (Store (Var "l1") (int 1))
          (Seq (Store (Var "l2") (int 2))
            (App (Rec None (Some "args") swap_body)
              (Struct [] [Var "l1"; Var "l2"])))))).

Definition sum_at_body : expr := rename_ptr 0 "p" (sum_block.sum_at 0).

Definition p_sum_block :=
  Prog [] [] [Fn "sumAt" None (Some "p") sum_at_body [t_ptr] t_int]
    (Let (Some "p") (Alloc (int 1))
      (Seq (Store (Var "p") (int 4))
        (App (Rec None (Some "p") sum_at_body) (Var "p")))).

Definition write_body : expr :=
  match frame_call.write_call 0 1 with
  | Let _ (Rec _ _ b) _ => b
  | _ => unit_e
  end.

Definition frame_body : expr :=
  Let (Some "p") (StructLoad (Var "args") 0)
    (Let (Some "q") (StructLoad (Var "args") 1)
      (rename_ptr 0 "p" (rename_ptr 1 "q" (frame_call.write_call 0 1)))).

Definition p_frame_call :=
  Prog [] []
    [Fn "write" None (Some "x") write_body [t_ptr] "Unit";
     Fn "frameCall" None (Some "args") frame_body [t_ptr; t_ptr] t_int]
    (Let (Some "p") (Alloc (int 1))
      (Let (Some "q") (Alloc (int 1))
        (Seq (Store (Var "q") (int 3))
          (App (Rec None (Some "args") frame_body)
            (Struct [] [Var "p"; Var "q"]))))).

Definition cj_files : list (string * prog) :=
[("arith", p_arith); ("struct_upd", p_struct_upd); ("cell", p_cell);
 ("swap", p_swap); ("sum_block", p_sum_block); ("class_upd", p_class_upd);
 ("frame_call", p_frame_call); ("vtable", p_vtable)].
Definition cj_bundle : string := cat_all (map (fun '(n,p) => "@@FILE " ++ n ++ nl ++ print_prog p) cj_files) ++ "@@FILE generics" ++ nl ++ generic_source generic_program.
