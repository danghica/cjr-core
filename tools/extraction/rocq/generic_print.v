(** Checked, explicitly named extraction of the generic source language.
    This is a scope/layout/arity checker, not a proved static type system. *)
From Coq Require Import String Ascii List Bool.
From cjr Require Import generics.
From cjr.examples Require Import cj_print.
Import ListNotations.
Local Open Scope string_scope.

Fixpoint gty_beq (a b : gty) : bool :=
  match a, b with
  | GTInt, GTInt | GTBool, GTBool | GTUnit, GTUnit => true
  | GTVar x, GTVar y => String.eqb x y
  | GTNamed n ts, GTNamed m us => String.eqb n m &&
      (fix go ts us := match ts, us with
       | [], [] => true | t :: ts, u :: us => gty_beq t u && go ts us | _, _ => false end) ts us
  | GTArrow a b, GTArrow c d => gty_beq a c && gty_beq b d
  | GTBuffer a, GTBuffer b => gty_beq a b
  | _, _ => false
  end.

Definition member (n : string) (ns : list string) := existsb (String.eqb n) ns.
Fixpoint distinct (ns : list string) : bool :=
  match ns with [] => true | n :: ns => negb (member n ns) && distinct ns end.
Definition letter (c : ascii) :=
  let n := nat_of_ascii c in
  ((Nat.leb 65 n) && (Nat.leb n 90)) || ((Nat.leb 97 n) && (Nat.leb n 122)) || (Nat.eqb n 95).
Definition digit (c : ascii) := let n := nat_of_ascii c in (Nat.leb 48 n) && (Nat.leb n 57).
Fixpoint identifier_tail (n : string) : bool :=
  match n with EmptyString => true | String c s => (letter c || digit c) && identifier_tail s end.
Definition identifier (n : string) :=
  match n with EmptyString => false | String c s => letter c && identifier_tail s &&
    negb (member n (keywords ++ ["Int64"; "Bool"; "Unit"; "CjrBuffer"; "public"; "private"; "static"; "return"])) end.
Definition require (b : bool) (message : string) : list string := if b then [] else [message].
Definition type_errors ds scope t :=
  require (gty_wf ds scope t) "unbound type variable, unknown type, or wrong type arity".
Definition function_env (fs : list gfunction) := map (fun f => (function_key f, f)) fs.
Definition type_args (t : gty) := match t with GTNamed _ ts => ts | _ => [] end.

(** Explicit references must not be captured by native local bindings. *)
Definition local_identifier (ds : list glayout) (fs : list gfunction) scope n :=
  identifier n && negb (member n (map gl_name ds ++ map gf_name fs ++ scope)).

Fixpoint check_expr (ds : list glayout) (fs : list gfunction)
    (scope locals : list string) (e : gexpr) : list string :=
  match e with
  | GECore _ => ["legacy core embedding: use the legacy printer"]
  | GEVal (LitV (LitInt _)) | GEVal (LitV (LitBool _)) | GEVal (LitV LitUnit) => []
  | GEVal _ => ["runtime value has no generic source literal"]
  | GEVar x => require (member x locals) ("unbound local: " ++ x)
  | GERef _ _ => ["bare named function reference: pass an explicitly typed lambda instead"]
  | GELam x a b e =>
      require (local_identifier ds fs scope x) ("invalid or shadowing lambda parameter: " ++ x) ++
      type_errors ds scope a ++ type_errors ds scope b ++ check_expr ds fs scope (x :: locals) e
  | GEApp a b => check_expr ds fs scope locals a ++ check_expr ds fs scope locals b
  | GECall n ts es =>
      (match glookup n (function_env fs) with
       | None => ["unresolved function (declare dependencies first): " ++ n]
       | Some f => require (match gf_owner f with None => true | _ => false end)
           ((if gf_static f then "static method requires a type-qualified call: "
             else "method requires a receiver: ") ++ n) ++
           require (Nat.eqb (length ts) (length (gf_tparams f))) ("wrong type arity: " ++ n) ++
           require (Nat.eqb (length es) (length (gf_params f))) ("wrong argument arity: " ++ n)
       end) ++ flat_map (type_errors ds scope) ts ++
       flat_map (check_expr ds fs scope locals) es
  | GEMethod t r n ts es =>
      require (nominal t) "method receiver needs a named type" ++ type_errors ds scope t ++
      (match glookup (method_key (owner_name t) n) (function_env fs) with
       | None => ["unresolved method: " ++ method_key (owner_name t) n]
       | Some f => require (negb (gf_static f)) ("static method requires a type-qualified call: " ++ n) ++
          require (Nat.eqb (length ts) (length (gf_tparams f))) ("wrong method type arity: " ++ n) ++
          require (Nat.eqb (S (length es)) (length (gf_params f))) ("wrong method argument arity: " ++ n)
       end) ++ flat_map (type_errors ds scope) ts ++ check_expr ds fs scope locals r ++
       flat_map (check_expr ds fs scope locals) es
  | GEStaticCall t n ts es =>
      require (nominal t) "static method owner needs a named type" ++ type_errors ds scope t ++
      (match glookup (method_key (owner_name t) n) (function_env fs) with
       | None => ["unresolved static method: " ++ method_key (owner_name t) n]
       | Some f => require (gf_static f) ("instance method requires a receiver: " ++ n) ++
          require (Nat.eqb (length ts) (length (gf_tparams f))) ("wrong static method type arity: " ++ n) ++
          require (Nat.eqb (length es) (length (gf_params f))) ("wrong static method argument arity: " ++ n)
       end) ++ flat_map (type_errors ds scope) ts ++
       flat_map (check_expr ds fs scope locals) es
  | GEConstruct t es =>
      require (nominal t) "constructor needs a named type" ++ type_errors ds scope t ++
      (match glookup (owner_name t) (layout_env ds) with
       | None => ["unresolved constructor: " ++ owner_name t]
       | Some d => require (Nat.eqb (length es) (length (gl_fields d)))
           ("wrong constructor arity: " ++ owner_name t)
       end) ++ flat_map (check_expr ds fs scope locals) es
  | GEField t r i =>
      require (nominal t) "field receiver needs a named type" ++ type_errors ds scope t ++
      (match glookup (owner_name t) (layout_env ds) with
       | None => ["unresolved field owner: " ++ owner_name t]
       | Some d => require (Nat.ltb i (length (gl_fields d))) ("field index out of range: " ++ owner_name t)
       end) ++ check_expr ds fs scope locals r
  | GELet x a b => check_expr ds fs scope locals a ++
      (match x with
       | None => check_expr ds fs scope locals b
       | Some x => require (local_identifier ds fs scope x) ("invalid or shadowing local: " ++ x) ++ check_expr ds fs scope (x :: locals) b
       end)
  | GEIf c a b => check_expr ds fs scope locals c ++ check_expr ds fs scope locals a ++ check_expr ds fs scope locals b
  | GEBinOp _ a b => check_expr ds fs scope locals a ++ check_expr ds fs scope locals b
  | GEBufferMake t a b | GEBufferGet t a b =>
      type_errors ds scope t ++ check_expr ds fs scope locals a ++ check_expr ds fs scope locals b
  | GEBufferSet t a b c => type_errors ds scope t ++ check_expr ds fs scope locals a ++
      check_expr ds fs scope locals b ++ check_expr ds fs scope locals c
  end.

Definition owner_parameters ds f : list string :=
  match gf_owner f with
  | None => []
  | Some o => match glookup o (layout_env ds) with Some d => gl_tparams d | None => [] end
  end.
Definition check_layout ds d : list string :=
  require (identifier (gl_name d)) ("invalid type name: " ++ gl_name d) ++
  require (distinct (gl_tparams d) && forallb identifier (gl_tparams d)) "invalid or duplicate type parameters" ++
  require (distinct (map fst (gl_fields d)) && forallb identifier (map fst (gl_fields d))) "invalid or duplicate fields" ++
  flat_map (fun '(_, t) => type_errors ds (gl_tparams d) t) (gl_fields d).

Definition check_function ds previous f : list string :=
  let scope := (owner_parameters ds f ++ gf_tparams f)%list in
  require (identifier (gf_name f)) ("invalid function name: " ++ gf_name f) ++
  require (distinct scope && forallb identifier scope) "invalid, shadowed, or duplicate type parameters" ++
  require (distinct (map fst (gf_params f)) && forallb (local_identifier ds (f :: previous) scope) (map fst (gf_params f))) "invalid or duplicate parameters" ++
  (match gf_owner f with
   | None => require (negb (gf_static f)) "static method needs an owner"
   | Some o =>
       match glookup o (layout_env ds) with
       | Some d =>
           (if gf_static f then [] else
            match gf_params f with
            | (_, receiver) :: _ =>
                require (gty_beq receiver (GTNamed o (map GTVar (gl_tparams d))))
                  "method first parameter must be its owning type with its type parameters"
            | [] => ["unknown method owner or missing receiver"]
            end) ++
           require (negb (member (gf_name f) (map fst (gl_fields d)))) "method conflicts with a field"
       | None => ["unknown method owner or missing receiver"]
       end
   end) ++
  flat_map (fun '(_, t) => type_errors ds scope t) (gf_params f) ++ type_errors ds scope (gf_ret f) ++
  check_expr ds (f :: previous) scope (map fst (gf_params f)) (gf_body f).

Fixpoint check_functions ds previous fs : list string :=
  match fs with
  | [] => []
  | f :: fs => check_function ds previous f ++ check_functions ds (f :: previous) fs
  end.
Definition check_program p : list string :=
  let ds := gp_layouts p in let fs := gp_functions p in
  require (distinct (map gl_name ds)) "duplicate type names" ++
  require (distinct (map function_key fs)) "duplicate function or method names" ++
  require (forallb (fun f => match gf_owner f with
           | Some _ => true | None => negb (member (gf_name f) (map gl_name ds)) end) fs)
          "function conflicts with a type name" ++
  flat_map (check_layout ds) ds ++ check_functions ds [] fs ++
  check_expr ds fs [] [] (gp_main p).

Fixpoint print_type (t : gty) : string :=
  match t with
  | GTInt => "Int64" | GTBool => "Bool" | GTUnit => "Unit"
  | GTVar n => n
  | GTNamed n ts => n ++ match ts with [] => "" | _ => "<" ++ comma (map print_type ts) ++ ">" end
  | GTArrow a b => "(" ++ print_type a ++ ") -> " ++ print_type b
  | GTBuffer a => "CjrBuffer<" ++ print_type a ++ ">"
  end.
Definition print_types ts := match ts with [] => "" | _ => "<" ++ comma (map print_type ts) ++ ">" end.
Definition print_parameters ts := match ts with [] => "" | _ => "<" ++ comma ts ++ ">" end.
Definition print_field_name ds t i :=
  match glookup (owner_name t) (layout_env ds) with
  | Some d => match nth_error (gl_fields d) i with Some (n, _) => n | None => "INVALID_FIELD" end
  | None => "INVALID_OWNER"
  end.

(** Force the native compiler to check receiver annotations. Without this,
    two unrelated layouts sharing field names could silently select different
    indices in CJR and Cangjie. The identity lambda does not enclose user code. *)
Definition typed_receiver t source :=
  "({ cjrTypedValue: " ++ print_type t ++ " => cjrTypedValue })(" ++ source ++ ")".

(** Every compound expression stays an expression. In particular, let uses an
    immediately invoked lambda, preserving the core's left-to-right order. *)
Fixpoint print_expr ds (e : gexpr) : string :=
  match e with
  | GECore _ | GEVal _ => match e with GEVal (LitV l) => lit l | _ => "INVALID_LITERAL" end
  | GEVar n => n
  | GERef n ts => n ++ print_types ts
  | GELam x t ret b => "{ " ++ x ++ ": " ++ print_type t ++ " => " ++ typed_receiver ret (print_expr ds b) ++ " }"
  | GEApp f a => "(" ++ print_expr ds f ++ ")(" ++ print_expr ds a ++ ")"
  | GECall n ts es => n ++ print_types ts ++ "(" ++ comma (map (print_expr ds) es) ++ ")"
  | GEMethod t r n ts es => "(" ++ typed_receiver t (print_expr ds r) ++ ")." ++ n ++ print_types ts ++
      "(" ++ comma (map (print_expr ds) es) ++ ")"
  | GEStaticCall t n ts es => print_type t ++ "." ++ n ++ print_types ts ++
      "(" ++ comma (map (print_expr ds) es) ++ ")"
  | GEConstruct t es => print_type t ++ "(" ++ comma (map (print_expr ds) es) ++ ")"
  | GEField t r i => "(" ++ typed_receiver t (print_expr ds r) ++ ")." ++ print_field_name ds t i
  | GELet x a b => "({ => " ++ nl ++
      (match x with Some n => "let " ++ n ++ " = " | None => "" end) ++ print_expr ds a ++ nl ++
      print_expr ds b ++ nl ++ "})()"
  | GEIf c a b => "if (" ++ print_expr ds c ++ ") { " ++ print_expr ds a ++
      " } else { " ++ print_expr ds b ++ " }"
  | GEBinOp AndOp a b => "({ cjrLeft: Bool, cjrRight: Bool => cjrLeft && cjrRight })(" ++
      print_expr ds a ++ ", " ++ print_expr ds b ++ ")"
  | GEBinOp op a b => "(" ++ print_expr ds a ++ " " ++ sym op ++ " " ++ print_expr ds b ++ ")"
  | GEBufferMake t n v => print_type (GTBuffer t) ++ "(" ++ print_expr ds n ++ ", repeat: " ++ print_expr ds v ++ ")"
  | GEBufferGet t b i => "(" ++ typed_receiver (GTBuffer t) (print_expr ds b) ++ ")[" ++ print_expr ds i ++ "]"
  | GEBufferSet t b i v => "({ cjrBuf: " ++ print_type (GTBuffer t) ++ ", cjrIndex: Int64, cjrValue: " ++ print_type t ++
      " => cjrBuf[cjrIndex] = cjrValue; () })(" ++ print_expr ds b ++ ", " ++ print_expr ds i ++ ", " ++ print_expr ds v ++ ")"
  end.
Definition print_parameter (p : string * gty) := fst p ++ ": " ++ print_type (snd p).
Definition print_function ds f :=
  let '(ps, prefix) := if gf_static f then (gf_params f, "") else match gf_owner f, gf_params f with
    | Some _, (x, _) :: ps => (ps, "let " ++ x ++ " = this" ++ nl)
    | _, ps => (ps, "") end in
  (if gf_static f then "public static func " else "public func ") ++ gf_name f ++ print_parameters (gf_tparams f) ++
  "(" ++ comma (map print_parameter ps) ++ "): " ++ print_type (gf_ret f) ++ " {" ++ nl ++
  prefix ++ "return " ++ print_expr ds (gf_body f) ++ nl ++ "}" ++ nl.
Definition print_layout ds fs d :=
  (match gl_kind d with GClass => "public class " | GStruct => "public struct " end) ++ gl_name d ++
  print_parameters (gl_tparams d) ++ " {" ++ nl ++
  cat_all (map (fun '(n,t) => "public let " ++ n ++ ": " ++ print_type t ++ nl) (gl_fields d)) ++
  "public init(" ++ comma (map print_parameter (gl_fields d)) ++ ") {" ++ nl ++
  cat_all (map (fun '(n,_) => "this." ++ n ++ " = " ++ n ++ nl) (gl_fields d)) ++ "}" ++ nl ++
  cat_all (map (print_function ds) (List.filter (fun f =>
    match gf_owner f with Some o => String.eqb o (gl_name d) | None => false end) fs)) ++
  "}" ++ nl.

Inductive extraction_result := Extracted (source : string) | Rejected (errors : list string).
Definition print_generic_program p : extraction_result :=
  match check_program p with
  | [] => Extracted (
      "// Generated from checked CJR generic source; do not edit." ++ nl ++
      "import std.core.Array as CjrBuffer" ++ nl ++
      cat_all (map (print_layout (gp_layouts p) (gp_functions p)) (gp_layouts p)) ++
      cat_all (map (print_function (gp_layouts p)) (List.filter (fun f =>
        match gf_owner f with None => true | _ => false end) (gp_functions p))) ++
      "main() {" ++ nl ++ print_expr (gp_layouts p) (gp_main p) ++ nl ++ "0" ++ nl ++ "}" ++ nl)
  | errors => Rejected errors
  end.
Definition generic_source p :=
  match print_generic_program p with
  | Extracted source => source
  | Rejected errors => "unsupported generic program: " ++ comma errors
  end.

Lemma extracted_program_checked p source :
  print_generic_program p = Extracted source → check_program p = [].
Proof. unfold print_generic_program. destruct (check_program p); congruence. Qed.
