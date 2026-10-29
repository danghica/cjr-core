(** Explicit rank-one generic source language. The existing CJR language and
    Iris instance are unchanged. Types are erased, never inspected at runtime. *)
From Coq Require Import String List Bool.
From cjr Require Export buffer.
Import ListNotations.
Local Open Scope string_scope.

Inductive gty :=
| GTInt | GTBool | GTUnit
| GTVar (name : string)
| GTNamed (name : string) (args : list gty)
| GTArrow (arg ret : gty)
| GTBuffer (element : gty).

Fixpoint glookup {A} (name : string) (xs : list (string * A)) : option A :=
  match xs with
  | [] => None
  | (n, a) :: xs => if String.eqb name n then Some a else glookup name xs
  end.

Fixpoint gty_subst (s : list (string * gty)) (t : gty) : gty :=
  match t with
  | GTVar n => match glookup n s with Some t => t | None => GTVar n end
  | GTNamed n ts => GTNamed n (map (gty_subst s) ts)
  | GTArrow a b => GTArrow (gty_subst s a) (gty_subst s b)
  | GTBuffer a => GTBuffer (gty_subst s a)
  | _ => t
  end.

Inductive gkind := GClass | GStruct.
Record glayout := GLayout {
  gl_name : string;
  gl_kind : gkind;
  gl_tparams : list string;
  gl_fields : list (string * gty)
}.
Definition layout_env (ds : list glayout) := map (fun d => (gl_name d, d)) ds.

Fixpoint gty_wf (ds : list glayout) (scope : list string) (t : gty) : bool :=
  match t with
  | GTInt | GTBool | GTUnit => true
  | GTVar n => existsb (String.eqb n) scope
  | GTNamed n ts =>
      match glookup n (layout_env ds) with
      | None => false
      | Some d => Nat.eqb (length ts) (length (gl_tparams d)) &&
                  forallb (gty_wf ds scope) ts
      end
  | GTArrow a b => gty_wf ds scope a && gty_wf ds scope b
  | GTBuffer a => gty_wf ds scope a
  end.

(** [GECore] embeds old CJR programs without changing their meaning. It is
    intentionally rejected by the generic printer: use the legacy printer for
    legacy programs. [GEVal] also supports semantic substitutions in proofs;
    only printable literals are admitted in extracted source. *)
Inductive gexpr :=
| GECore (e : expr)
| GEVal (v : val)
| GEVar (x : string)
| GERef (name : string) (types : list gty)
| GELam (x : string) (arg ret : gty) (body : gexpr)
| GEApp (f arg : gexpr)
| GECall (name : string) (types : list gty) (args : list gexpr)
| GEMethod (owner : gty) (receiver : gexpr) (name : string)
           (types : list gty) (args : list gexpr)
| GEStaticCall (owner : gty) (name : string) (types : list gty) (args : list gexpr)
| GEConstruct (owner : gty) (args : list gexpr)
| GEField (owner : gty) (receiver : gexpr) (index : nat)
| GELet (x : binder) (value body : gexpr)
| GEIf (cond yes no : gexpr)
| GEBinOp (op : bin_op) (left right : gexpr)
(** Managed native buffers use existing core allocation/load/store after erasure.
    They carry values, not an assumed native byte width for their element type. *)
| GEBufferMake (element : gty) (size seed : gexpr)
| GEBufferGet (element : gty) (buffer index : gexpr)
| GEBufferSet (element : gty) (buffer index value : gexpr).

Definition owner_name (t : gty) : string :=
  match t with GTNamed n _ => n | _ => "" end.
Definition method_key (owner name : string) := owner ++ "." ++ name.
Definition is_class (ds : list glayout) (n : string) : bool :=
  match glookup n (layout_env ds) with
  | Some d => match gl_kind d with GClass => true | GStruct => false end
  | None => false
  end.
Definition resolve (fs : list (string * val)) (n : string) : expr :=
  match glookup n fs with Some v => Val v | None => Var n end.
Definition gpack (es : list expr) := Struct [] es.

Fixpoint erase (ds : list glayout) (fs : list (string * val)) (e : gexpr) : expr :=
  match e with
  | GECore e => e
  | GEVal v => Val v
  | GEVar x => Var x
  | GERef n _ => resolve fs n
  | GELam x _ _ b => Rec None (Some x) (erase ds fs b)
  | GEApp f a => App (erase ds fs f) (erase ds fs a)
  | GECall n _ args => App (resolve fs n) (gpack (map (erase ds fs) args))
  | GEMethod t r n _ args =>
      App (resolve fs (method_key (owner_name t) n))
          (gpack (erase ds fs r :: map (erase ds fs) args))
  | GEStaticCall t n _ args =>
      App (resolve fs (method_key (owner_name t) n)) (gpack (map (erase ds fs) args))
  | GEConstruct t args =>
      if is_class ds (owner_name t) then New [] (map (erase ds fs) args)
      else Struct [] (map (erase ds fs) args)
  | GEField t r i =>
      if is_class ds (owner_name t) then FieldLoad (erase ds fs r) i
      else StructLoad (erase ds fs r) i
  | GELet x a b => Let x (erase ds fs a) (erase ds fs b)
  | GEIf c a b => If (erase ds fs c) (erase ds fs a) (erase ds fs b)
  | GEBinOp op a b => BinOp op (erase ds fs a) (erase ds fs b)
  | GEBufferMake _ n v => App (Val buffer_make_val) (Struct [] [erase ds fs n; erase ds fs v])
  | GEBufferGet _ b i => Load (Offset (erase ds fs b) (erase ds fs i))
  | GEBufferSet _ b i v => Store (Offset (erase ds fs b) (erase ds fs i)) (erase ds fs v)
  end.

Fixpoint ginstantiate (s : list (string * gty)) (e : gexpr) : gexpr :=
  match e with
  | GECore _ | GEVal _ | GEVar _ => e
  | GERef n ts => GERef n (map (gty_subst s) ts)
  | GELam x a b e => GELam x (gty_subst s a) (gty_subst s b) (ginstantiate s e)
  | GEApp f a => GEApp (ginstantiate s f) (ginstantiate s a)
  | GECall n ts es => GECall n (map (gty_subst s) ts) (map (ginstantiate s) es)
  | GEMethod t r n ts es => GEMethod (gty_subst s t) (ginstantiate s r) n
      (map (gty_subst s) ts) (map (ginstantiate s) es)
  | GEStaticCall t n ts es => GEStaticCall (gty_subst s t) n
      (map (gty_subst s) ts) (map (ginstantiate s) es)
  | GEConstruct t es => GEConstruct (gty_subst s t) (map (ginstantiate s) es)
  | GEField t r i => GEField (gty_subst s t) (ginstantiate s r) i
  | GELet x a b => GELet x (ginstantiate s a) (ginstantiate s b)
  | GEIf c a b => GEIf (ginstantiate s c) (ginstantiate s a) (ginstantiate s b)
  | GEBinOp op a b => GEBinOp op (ginstantiate s a) (ginstantiate s b)
  | GEBufferMake t n v => GEBufferMake (gty_subst s t) (ginstantiate s n) (ginstantiate s v)
  | GEBufferGet t b i => GEBufferGet (gty_subst s t) (ginstantiate s b) (ginstantiate s i)
  | GEBufferSet t b i v => GEBufferSet (gty_subst s t) (ginstantiate s b) (ginstantiate s i) (ginstantiate s v)
  end.

(** Receiver and constructor annotations must name a layout, not a bare type
    variable. This prevents instantiation from changing runtime layout kind. *)
Definition nominal (t : gty) : bool :=
  match t with GTNamed _ _ => true | _ => false end.
Fixpoint nominal_owners (e : gexpr) : bool :=
  match e with
  | GELam _ _ _ b => nominal_owners b
  | GEApp a b | GELet _ a b | GEBinOp _ a b | GEBufferMake _ a b | GEBufferGet _ a b => nominal_owners a && nominal_owners b
  | GECall _ _ es => forallb nominal_owners es
  | GEMethod t r _ _ es => nominal t && nominal_owners r && forallb nominal_owners es
  | GEStaticCall t _ _ es => nominal t && forallb nominal_owners es
  | GEConstruct t es => nominal t && forallb nominal_owners es
  | GEField t r _ => nominal t && nominal_owners r
  | GEIf c a b | GEBufferSet _ c a b => nominal_owners c && nominal_owners a && nominal_owners b
  | _ => true
  end.

Lemma owner_subst s t : nominal t = true → owner_name (gty_subst s t) = owner_name t.
Proof. destruct t; simpl; try discriminate; reflexivity. Qed.

Lemma erase_instantiate ds fs e s : nominal_owners e = true →
  erase ds fs (ginstantiate s e) = erase ds fs e.
Proof.
  revert e. fix IH 1. intros e H. destruct e; simpl in *;
    repeat match goal with H : _ && _ = true |- _ => apply andb_true_iff in H as [? ?] end;
    try reflexivity.
  - f_equal. auto.
  - f_equal; auto.
  - f_equal. unfold gpack. f_equal. rewrite map_map.
    induction args; simpl in *; [done|].
    apply andb_true_iff in H as [Ha Hs]. f_equal; auto.
  - rewrite (owner_subst s owner ltac:(assumption)). f_equal. unfold gpack. f_equal.
    f_equal; [auto|]. rewrite map_map. induction args; simpl in *; [done|].
    repeat match goal with H : _ && _ = true |- _ => apply andb_true_iff in H as [? ?] end.
    f_equal; auto.
  - rewrite (owner_subst s owner ltac:(assumption)).
    f_equal. unfold gpack. f_equal. rewrite map_map.
    induction args; simpl in *; [done|].
    repeat match goal with H : _ && _ = true |- _ => apply andb_true_iff in H as [? ?] end.
    f_equal; auto.
  - rewrite (owner_subst s owner ltac:(assumption)).
    destruct (is_class ds (owner_name owner)); f_equal; rewrite map_map;
      induction args; simpl in *; try reflexivity;
      repeat match goal with H : _ && _ = true |- _ => apply andb_true_iff in H as [? ?] end;
      f_equal; auto.
  - rewrite (owner_subst s owner ltac:(assumption)).
    destruct (is_class ds (owner_name owner)); f_equal; auto.
  - f_equal; auto.
  - f_equal; auto.
  - f_equal; auto.
  - rewrite (IH e1 ltac:(assumption)) (IH e2 ltac:(assumption)). done.
  - rewrite (IH e1 ltac:(assumption)) (IH e2 ltac:(assumption)). done.
  - rewrite (IH e1 ltac:(assumption)) (IH e2 ltac:(assumption)) (IH e3 ltac:(assumption)). done.
Qed.

Fixpoint gsubst (x : string) (v : val) (e : gexpr) : gexpr :=
  match e with
  | GECore e => GECore (subst x v e)
  | GEVal w => GEVal (subst_val x v w)
  | GEVar y => if String.eqb x y then GEVal v else GEVar y
  | GERef _ _ => e
  | GELam y a b e => GELam y a b (if String.eqb x y then e else gsubst x v e)
  | GEApp a b => GEApp (gsubst x v a) (gsubst x v b)
  | GECall n ts es => GECall n ts (map (gsubst x v) es)
  | GEMethod t r n ts es => GEMethod t (gsubst x v r) n ts (map (gsubst x v) es)
  | GEStaticCall t n ts es => GEStaticCall t n ts (map (gsubst x v) es)
  | GEConstruct t es => GEConstruct t (map (gsubst x v) es)
  | GEField t r i => GEField t (gsubst x v r) i
  | GELet b a e => GELet b (gsubst x v a) (if binds x b then e else gsubst x v e)
  | GEIf c a b => GEIf (gsubst x v c) (gsubst x v a) (gsubst x v b)
  | GEBinOp op a b => GEBinOp op (gsubst x v a) (gsubst x v b)
  | GEBufferMake t n a => GEBufferMake t (gsubst x v n) (gsubst x v a)
  | GEBufferGet t b i => GEBufferGet t (gsubst x v b) (gsubst x v i)
  | GEBufferSet t b i a => GEBufferSet t (gsubst x v b) (gsubst x v i) (gsubst x v a)
  end.

Fixpoint referenced_names (e : gexpr) : list string :=
  match e with
  | GERef n _ => [n]
  | GELam _ _ _ b => referenced_names b
  | GEApp a b | GELet _ a b | GEBinOp _ a b | GEBufferMake _ a b | GEBufferGet _ a b => referenced_names a ++ referenced_names b
  | GECall n _ es => n :: flat_map referenced_names es
  | GEMethod t r n _ es => method_key (owner_name t) n ::
      (referenced_names r ++ flat_map referenced_names es)
  | GEStaticCall t n _ es => method_key (owner_name t) n :: flat_map referenced_names es
  | GEConstruct _ es => flat_map referenced_names es
  | GEField _ r _ => referenced_names r
  | GEIf c a b | GEBufferSet _ c a b => referenced_names c ++ referenced_names a ++ referenced_names b
  | _ => []
  end.

Lemma string_eqb_decide x y : String.eqb x y = bool_decide (x = y).
Proof. destruct (String.eqb_spec x y); repeat case_bool_decide; congruence. Qed.

(** Named declarations are closed with respect to the substituted local
    variable. This is necessary: global function references are not locals. *)
Lemma erase_subst ds fs e x v :
  (∀ n, In n (referenced_names e) → subst x v (resolve fs n) = resolve fs n) →
  erase ds fs (gsubst x v e) = subst x v (erase ds fs e).
Proof.
  revert e. fix IH 1. intros e H. destruct e; simpl in *;
    try reflexivity.
  - rewrite string_eqb_decide. destruct (bool_decide (x = x0)); reflexivity.
  - symmetry. apply H. auto.
  - unfold binds. rewrite string_eqb_decide. destruct (bool_decide (x = x0)); simpl;
      [reflexivity|]. f_equal. apply IH. exact H.
  - f_equal; apply IH; intros; apply H; apply in_or_app; auto.
  - rewrite (H _ ltac:(auto)). f_equal. f_equal. rewrite map_map.
    induction args as [|a es IHL]; simpl; [done|]. f_equal.
    + apply IH. intros n Hn. apply H. right. apply in_or_app. auto.
    + apply IHL. intros n Hn. apply H. destruct Hn as [->|Hn]; auto.
      right. apply in_or_app. auto.
  - rewrite (H _ ltac:(auto)). f_equal. f_equal. f_equal.
    + apply IH. intros n Hn. apply H. right. apply in_or_app. auto.
    + rewrite map_map. induction args as [|a es IHL]; simpl; [done|]. f_equal.
      * apply IH. intros n Hn. apply H. right. apply in_or_app. right.
        apply in_or_app. auto.
      * apply IHL. intros n Hn. apply H. destruct Hn as [->|Hn]; auto.
        right. apply in_app_or in Hn as [Hn|Hn]; apply in_or_app; auto.
        right. apply in_or_app. auto.
  - rewrite (H _ ltac:(auto)). f_equal. f_equal. rewrite map_map.
    induction args as [|a es IHL]; simpl; [done|]. f_equal.
    + apply IH. intros n Hn. apply H. right. apply in_or_app. auto.
    + apply IHL. intros n Hn. apply H. destruct Hn as [->|Hn]; auto.
      right. apply in_or_app. auto.
  - destruct (is_class ds (owner_name owner)); simpl; f_equal;
      rewrite map_map; induction args as [|a es IHL]; simpl; [done| |done|]; f_equal;
      try (apply IH; intros n Hn; apply H; apply in_or_app; auto);
      apply IHL; intros n Hn; apply H; apply in_or_app; auto.
  - destruct (is_class ds (owner_name owner)); simpl; f_equal; apply IH; exact H.
  - f_equal.
    + apply IH. intros n Hn. apply H. apply in_or_app. auto.
    + destruct (binds x x0); [done|]. apply IH. intros n Hn. apply H. apply in_or_app. auto.
  - f_equal; apply IH; intros n Hn; apply H; repeat (apply in_or_app; first [left; exact Hn|right]); exact Hn.
  - f_equal; apply IH; intros; apply H; apply in_or_app; auto.
  - change ((App (Val buffer_make_val) (Struct [] [erase ds fs (gsubst x v e1); erase ds fs (gsubst x v e2)])) =
      (App (Val (subst_val x v buffer_make_val)) (Struct [] [subst x v (erase ds fs e1); subst x v (erase ds fs e2)]))).
    rewrite buffer_make_closed.
    rewrite (IH e1 ltac:(intros; apply H; apply in_or_app; auto))
      (IH e2 ltac:(intros; apply H; apply in_or_app; auto)). done.
  - rewrite (IH e1 ltac:(intros; apply H; apply in_or_app; auto))
      (IH e2 ltac:(intros; apply H; apply in_or_app; auto)). done.
  - rewrite (IH e1 ltac:(intros n Hn; apply H; apply in_or_app; auto))
      (IH e2 ltac:(intros n Hn; apply H; apply in_or_app; right; apply in_or_app; auto))
      (IH e3 ltac:(intros n Hn; apply H; apply in_or_app; right; apply in_or_app; auto)). done.
Qed.

Record gfunction := GFunctionDecl {
  gf_name : string;
  gf_owner : option string;
  gf_static : bool;
  gf_tparams : list string;
  gf_params : list (string * gty);
  gf_ret : gty;
  gf_body : gexpr
}.
(** Preserve the existing declaration interface. Static methods have an
    explicit owner but no receiver in their argument tuple. *)
Definition GFunction name owner tparams params ret body :=
  GFunctionDecl name owner false tparams params ret body.
Definition GStaticFunction name owner tparams params ret body :=
  GFunctionDecl name (Some owner) true tparams params ret body.
Definition function_key (f : gfunction) :=
  match gf_owner f with None => gf_name f | Some o => method_key o (gf_name f) end.

(** A method's explicit first parameter is its receiver. Argument tuples are
    an internal calling convention; native Cangjie uses ordinary parameters. *)
Fixpoint bind_parameters (ps : list (string * gty)) (i : nat) (body : expr) : expr :=
  match ps with
  | [] => body
  | (x, _) :: ps => Let (Some x) (StructLoad (Var "$args") i)
      (bind_parameters ps (S i) body)
  end.
Definition erase_function ds fs f : val :=
  RecV (Some (function_key f)) (Some "$args")
    (bind_parameters (gf_params f) 0 (erase ds fs (gf_body f))).
Fixpoint link_functions ds (fs : list (string * val)) (decls : list gfunction)
    : list (string * val) :=
  match decls with
  | [] => fs
  | f :: decls => link_functions ds
      ((function_key f, erase_function ds fs f) :: fs) decls
  end.
Record gprogram := GProgram {
  gp_layouts : list glayout;
  gp_functions : list gfunction;
  gp_main : gexpr
}.
Definition erase_program p :=
  erase (gp_layouts p) (link_functions (gp_layouts p) [] (gp_functions p)) (gp_main p).

Lemma erase_legacy ds fs e : erase ds fs (GECore e) = e.
Proof. reflexivity. Qed.
