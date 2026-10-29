(** cjr: syntax and small-step semantics.

Mutable [var] bindings are stack slots. Immutable [let] is substitution.
[CPointer] cells live on a raw word heap, grouped into blocks.
Final class fields live on a separate object heap.
*)
From stdpp Require Import countable gmap strings.
From iris.program_logic Require Export language ectx_language ectxi_language.
From iris.prelude Require Import options.
From Coq Require Import Lia.

Definition loc : Type := Z.

Inductive stack_id := StackId (z : Z).
Inductive raw_id := RawId (z : Z).
Inductive obj_id := ObjId (z : Z).

Global Instance stack_id_eq_dec : EqDecision stack_id.
Proof. solve_decision. Defined.
Global Instance stack_id_countable : Countable stack_id.
Proof. refine (inj_countable' (λ '(StackId z), z) StackId _); by intros []. Defined.
Global Instance raw_id_eq_dec : EqDecision raw_id.
Proof. solve_decision. Defined.
Global Instance raw_id_countable : Countable raw_id.
Proof. refine (inj_countable' (λ '(RawId z), z) RawId _); by intros []. Defined.
Global Instance raw_id_inj : Inj (=) (=) RawId.
Proof. intros z1 z2. by inversion 1. Qed.
Global Instance stack_id_inj : Inj (=) (=) StackId.
Proof. intros z1 z2. by inversion 1. Qed.
Global Instance obj_id_inj : Inj (=) (=) ObjId.
Proof. intros z1 z2. by inversion 1. Qed.
Global Instance obj_id_eq_dec : EqDecision obj_id.
Proof. solve_decision. Defined.
Global Instance obj_id_countable : Countable obj_id.
Proof. refine (inj_countable' (λ '(ObjId z), z) ObjId _); by intros []. Defined.

(** Intended monomorphic types. The operational semantics is untyped;
safety of specified programs is the adequacy theorem. *)
Inductive ty :=
  | TyInt | TyFloat | TyBool | TyUnit
  | TyStruct (τs : list ty)
  | TyPtr (τ : ty)
  | TyObj (nfields : nat)
  | TyFun (τ1 τ2 : ty).

Definition binder := option string.

Inductive base_lit :=
  | LitInt (n : Z)
  | LitFloat (n : Z)
  | LitBool (b : bool)
  | LitUnit
  | LitPtr (l : loc)
  | LitNull
  | LitObj (o : loc)
  | LitStack (l : loc).

Inductive bin_op := PlusOp | MinusOp | MulOp | DivOp | RemOp | LeOp | EqOp | AndOp | BitXorOp | BitAndOp.

Inductive val :=
  | LitV (l : base_lit)
  | RecV (f x : binder) (e : expr)
  | StructV (vs : list val)
with expr :=
  | Val (v : val)
  | Var (x : string)
  | Rec (f x : binder) (e : expr)
  | App (e1 e2 : expr)
  | Let (x : binder) (e1 e2 : expr)
  | VarBind (x : string) (e1 e2 : expr)
  | Assign (x : string) (e : expr)
  | Pop (l : stack_id) (e : expr)
  | StackLoad (e : expr)
  | StackAssign (e1 e2 : expr)
  | StackFieldStore (e1 : expr) (i : nat) (e2 : expr)
  | If (e0 e1 e2 : expr)
  | While (e1 e2 : expr)
  | Seq (e1 e2 : expr)
  | BinOp (op : bin_op) (e1 e2 : expr)
  | Alloc (e : expr)
  | Free (e : expr)
  | Load (e : expr)
  | Store (e1 e2 : expr)
  | Offset (e1 e2 : expr)
  | Struct (vs : list val) (es : list expr)
  | StructLoad (e : expr) (i : nat)
  | StructStore (x : string) (i : nat) (e : expr)
  | New (vs : list val) (es : list expr)
  | FieldLoad (e : expr) (i : nat)
  | FieldStore (e1 : expr) (i : nat) (e2 : expr).

Notation val_cjr := val (only parsing).
Notation expr_cjr := expr (only parsing).
Global Instance val_inhabited : Inhabited val := populate (LitV LitUnit).
Global Instance expr_inhabited : Inhabited expr := populate (Val (LitV LitUnit)).

Definition binds (x : string) (b : binder) : bool :=
  match b with
  | None => false
  | Some y => bool_decide (x = y)
  end.

Fixpoint subst (x : string) (v : val) (e : expr) {struct e} : expr :=
  match e with
  | Val w => Val (subst_val x v w)
  | Var y => if bool_decide (x = y) then Val v else Var y
  | Rec f y e1 =>
      Rec f y (if binds x f || binds x y then e1 else subst x v e1)
  | App e1 e2 => App (subst x v e1) (subst x v e2)
  | Let b e1 e2 =>
      Let b (subst x v e1) (if binds x b then e2 else subst x v e2)
  | VarBind y e1 e2 =>
      VarBind y (subst x v e1) (if bool_decide (x = y) then e2 else subst x v e2)
  | Assign y e1 => Assign y (subst x v e1)
  | Pop l e1 => Pop l (subst x v e1)
  | StackLoad e1 => StackLoad (subst x v e1)
  | StackAssign e1 e2 => StackAssign (subst x v e1) (subst x v e2)
  | StackFieldStore e1 i e2 => StackFieldStore (subst x v e1) i (subst x v e2)
  | If e0 e1 e2 => If (subst x v e0) (subst x v e1) (subst x v e2)
  | While e1 e2 => While (subst x v e1) (subst x v e2)
  | Seq e1 e2 => Seq (subst x v e1) (subst x v e2)
  | BinOp op e1 e2 => BinOp op (subst x v e1) (subst x v e2)
  | Alloc e1 => Alloc (subst x v e1)
  | Free e1 => Free (subst x v e1)
  | Load e1 => Load (subst x v e1)
  | Store e1 e2 => Store (subst x v e1) (subst x v e2)
  | Offset e1 e2 => Offset (subst x v e1) (subst x v e2)
  | Struct vs es =>
      Struct
        ((fix go vs := match vs with [] => [] | w :: vs => subst_val x v w :: go vs end) vs)
        ((fix go es := match es with [] => [] | e :: es => subst x v e :: go es end) es)
  | StructLoad e1 i => StructLoad (subst x v e1) i
  | StructStore y i e1 => StructStore y i (subst x v e1)
  | New vs es =>
      New
        ((fix go vs := match vs with [] => [] | w :: vs => subst_val x v w :: go vs end) vs)
        ((fix go es := match es with [] => [] | e :: es => subst x v e :: go es end) es)
  | FieldLoad e1 i => FieldLoad (subst x v e1) i
  | FieldStore e1 i e2 => FieldStore (subst x v e1) i (subst x v e2)
  end
with subst_val (x : string) (v w : val) {struct w} : val :=
  match w with
  | LitV _ => w
  | RecV f y e =>
      RecV f y (if binds x f || binds x y then e else subst x v e)
  | StructV vs =>
      StructV ((fix go vs := match vs with [] => [] | w :: vs => subst_val x v w :: go vs end) vs)
  end.

Definition subst_binder (b : binder) (v : val) (e : expr) : expr :=
  match b with
  | None => e
  | Some x => subst x v e
  end.

(** Replace mutable mentions of [x] by operations on stack slot [l]. *)
Fixpoint subst_var (x : string) (l : loc) (e : expr) {struct e} : expr :=
  let slot := Val (LitV (LitStack l)) in
  match e with
  | Val w => Val (subst_var_val x l w)
  | Var y => if bool_decide (x = y) then StackLoad slot else Var y
  | Rec f y e1 =>
      Rec f y (if binds x f || binds x y then e1 else subst_var x l e1)
  | App e1 e2 => App (subst_var x l e1) (subst_var x l e2)
  | Let b e1 e2 =>
      Let b (subst_var x l e1) (if binds x b then e2 else subst_var x l e2)
  | VarBind y e1 e2 =>
      VarBind y (subst_var x l e1)
        (if bool_decide (x = y) then e2 else subst_var x l e2)
  | Assign y e1 =>
      if bool_decide (x = y) then StackAssign slot (subst_var x l e1)
      else Assign y (subst_var x l e1)
  | Pop l' e1 => Pop l' (subst_var x l e1)
  | StackLoad e1 => StackLoad (subst_var x l e1)
  | StackAssign e1 e2 => StackAssign (subst_var x l e1) (subst_var x l e2)
  | StackFieldStore e1 i e2 =>
      StackFieldStore (subst_var x l e1) i (subst_var x l e2)
  | If e0 e1 e2 => If (subst_var x l e0) (subst_var x l e1) (subst_var x l e2)
  | While e1 e2 => While (subst_var x l e1) (subst_var x l e2)
  | Seq e1 e2 => Seq (subst_var x l e1) (subst_var x l e2)
  | BinOp op e1 e2 => BinOp op (subst_var x l e1) (subst_var x l e2)
  | Alloc e1 => Alloc (subst_var x l e1)
  | Free e1 => Free (subst_var x l e1)
  | Load e1 => Load (subst_var x l e1)
  | Store e1 e2 => Store (subst_var x l e1) (subst_var x l e2)
  | Offset e1 e2 => Offset (subst_var x l e1) (subst_var x l e2)
  | Struct vs es =>
      Struct
        ((fix go vs := match vs with [] => [] | w :: vs => subst_var_val x l w :: go vs end) vs)
        ((fix go es := match es with [] => [] | e :: es => subst_var x l e :: go es end) es)
  | StructLoad e1 i => StructLoad (subst_var x l e1) i
  | StructStore y i e1 =>
      if bool_decide (x = y) then StackFieldStore slot i (subst_var x l e1)
      else StructStore y i (subst_var x l e1)
  | New vs es =>
      New
        ((fix go vs := match vs with [] => [] | w :: vs => subst_var_val x l w :: go vs end) vs)
        ((fix go es := match es with [] => [] | e :: es => subst_var x l e :: go es end) es)
  | FieldLoad e1 i => FieldLoad (subst_var x l e1) i
  | FieldStore e1 i e2 => FieldStore (subst_var x l e1) i (subst_var x l e2)
  end
with subst_var_val (x : string) (l : loc) (w : val) {struct w} : val :=
  match w with
  | LitV _ => w
  | RecV f y e =>
      RecV f y (if binds x f || binds x y then e else subst_var x l e)
  | StructV vs =>
      StructV ((fix go vs := match vs with [] => [] | w :: vs => subst_var_val x l w :: go vs end) vs)
  end.

Definition of_val (v : val) : expr := Val v.
Definition to_val (e : expr) : option val :=
  match e with
  | Val v => Some v
  | _ => None
  end.

Lemma to_of_val v : to_val (of_val v) = Some v.
Proof. by destruct v. Qed.
Lemma of_to_val e v : to_val e = Some v → of_val v = e.
Proof. destruct e; simpl; intros ?; by simplify_eq. Qed.

Definition bin_op_eval (op : bin_op) (v1 v2 : val) : option val :=
  match op, v1, v2 with
  | PlusOp, LitV (LitInt n1), LitV (LitInt n2) => Some (LitV (LitInt (n1 + n2)))
  | MinusOp, LitV (LitInt n1), LitV (LitInt n2) => Some (LitV (LitInt (n1 - n2)))
  | MulOp, LitV (LitInt n1), LitV (LitInt n2) => Some (LitV (LitInt (n1 * n2)))
  (* Cangjie division and remainder truncate toward zero. *)
  | DivOp, LitV (LitInt n1), LitV (LitInt n2) =>
      if decide (n2 = 0)%Z then None else Some (LitV (LitInt (Z.quot n1 n2)))
  | RemOp, LitV (LitInt n1), LitV (LitInt n2) =>
      if decide (n2 = 0)%Z then None else Some (LitV (LitInt (Z.rem n1 n2)))
  | BitXorOp, LitV (LitInt n1), LitV (LitInt n2) => Some (LitV (LitInt (Z.lxor n1 n2)))
  | BitAndOp, LitV (LitInt n1), LitV (LitInt n2) => Some (LitV (LitInt (Z.land n1 n2)))
  | LeOp, LitV (LitInt n1), LitV (LitInt n2) => Some (LitV (LitBool (bool_decide (n1 ≤ n2)%Z)))
  | EqOp, LitV (LitInt n1), LitV (LitInt n2) => Some (LitV (LitBool (bool_decide (n1 = n2))))
  | AndOp, LitV (LitBool b1), LitV (LitBool b2) => Some (LitV (LitBool (b1 && b2)))
  | _, _, _ => None
  end.

Record state := MkState {
  cjr_stack : gmap stack_id val;
  cjr_raw : gmap raw_id val;
  cjr_blocks : gmap raw_id nat;
  cjr_obj : gmap (obj_id * nat) val;
  cjr_next : Z
}.

Notation state_cjr := state (only parsing).
Global Instance state_inhabited : Inhabited state :=
  populate (MkState ∅ ∅ ∅ ∅ 0).

Definition state_init : state := inhabitant.

Definition set_stack (m : gmap stack_id val) (σ : state) : state :=
  MkState m (cjr_raw σ) (cjr_blocks σ) (cjr_obj σ) (cjr_next σ).
Definition set_raw (m : gmap raw_id val) (σ : state) : state :=
  MkState (cjr_stack σ) m (cjr_blocks σ) (cjr_obj σ) (cjr_next σ).
Definition set_blocks (m : gmap raw_id nat) (σ : state) : state :=
  MkState (cjr_stack σ) (cjr_raw σ) m (cjr_obj σ) (cjr_next σ).
Definition set_obj (m : gmap (obj_id * nat) val) (σ : state) : state :=
  MkState (cjr_stack σ) (cjr_raw σ) (cjr_blocks σ) m (cjr_next σ).
Definition set_next (n : Z) (σ : state) : state :=
  MkState (cjr_stack σ) (cjr_raw σ) (cjr_blocks σ) (cjr_obj σ) n.

Fixpoint set_nth {A} (i : nat) (a : A) (xs : list A) : list A :=
  match i, xs with
  | O, _ :: xs => a :: xs
  | S i, x :: xs => x :: set_nth i a xs
  | _, [] => []
  end.

Fixpoint init_cells (base : loc) (n : nat) : gmap raw_id val :=
  match n with
  | O => ∅
  | S n => <[RawId (base + Z.of_nat n) := LitV (LitInt 0)]> (init_cells base n)
  end.

Fixpoint free_cells (base : loc) (n : nat) (m : gmap raw_id val) : gmap raw_id val :=
  match n with
  | O => m
  | S n => delete (RawId (base + Z.of_nat n)) (free_cells base n m)
  end.

Fixpoint init_fields (o : loc) (vs : list val) (i : nat) : gmap (obj_id * nat) val :=
  match vs with
  | [] => ∅
  | v :: vs => <[(ObjId o, i) := v]> (init_fields o vs (S i))
  end.

Definition stack_below (m : gmap stack_id val) (n : Z) : Prop :=
  ∀ l, StackId l ∈ dom m → (l < n)%Z.
Definition raw_below (m : gmap raw_id val) (n : Z) : Prop :=
  ∀ l, RawId l ∈ dom m → (l < n)%Z.
Definition block_below (m : gmap raw_id nat) (n : Z) : Prop :=
  ∀ l, RawId l ∈ dom m → (l < n)%Z.
Definition obj_below (m : gmap (obj_id * nat) val) (n : Z) : Prop :=
  ∀ l i, (ObjId l, i) ∈ dom m → (l < n)%Z.

Definition block_cover (blocks : gmap raw_id nat) (raw : gmap raw_id val) (next : Z) : Prop :=
  ∀ l n, blocks !! RawId l = Some n →
    (l + Z.of_nat n ≤ next)%Z ∧
    ∀ i, i < n → is_Some (raw !! RawId (l + Z.of_nat i)).

Definition blocks_disjoint (blocks : gmap raw_id nat) : Prop :=
  ∀ l1 n1 l2 n2,
    blocks !! RawId l1 = Some n1 → blocks !! RawId l2 = Some n2 →
    l1 ≠ l2 → (l1 + Z.of_nat n1 ≤ l2 ∨ l2 + Z.of_nat n2 ≤ l1)%Z.

Record state_wf (σ : state) : Prop := {
  wf_stack : stack_below (cjr_stack σ) (cjr_next σ);
  wf_raw : raw_below (cjr_raw σ) (cjr_next σ);
  wf_block : block_below (cjr_blocks σ) (cjr_next σ);
  wf_obj : obj_below (cjr_obj σ) (cjr_next σ);
  wf_cover : block_cover (cjr_blocks σ) (cjr_raw σ) (cjr_next σ);
  wf_disj : blocks_disjoint (cjr_blocks σ)
}.

Lemma state_init_wf : state_wf state_init.
Proof. split; try (intros ?; set_solver); intros ??????; set_solver. Qed.

Inductive ectx_item :=
  | LetCtx (x : binder) (e2 : expr)
  | VarBindCtx (x : string) (e2 : expr)
  | PopCtx (l : stack_id)
  | AssignCtx (x : string)
  | StackLoadCtx
  | StackAssignLCtx (e2 : expr)
  | StackAssignRCtx (v1 : val)
  | StackFieldLCtx (i : nat) (e2 : expr)
  | StackFieldRCtx (v1 : val) (i : nat)
  | AppLCtx (e2 : expr)
  | AppRCtx (v1 : val)
  | IfCtx (e1 e2 : expr)
  | SeqCtx (e2 : expr)
  | BinOpLCtx (op : bin_op) (e2 : expr)
  | BinOpRCtx (op : bin_op) (v1 : val)
  | AllocCtx
  | FreeCtx
  | LoadCtx
  | StoreLCtx (e2 : expr)
  | StoreRCtx (v1 : val)
  | OffsetLCtx (e2 : expr)
  | OffsetRCtx (v1 : val)
  | StructCtx (vs : list val) (es : list expr)
  | StructLoadCtx (i : nat)
  | StructStoreCtx (x : string) (i : nat)
  | NewCtx (vs : list val) (es : list expr)
  | FieldLoadCtx (i : nat)
  | FieldStoreLCtx (i : nat) (e2 : expr)
  | FieldStoreRCtx (v1 : val) (i : nat).

Definition fill_item (Ki : ectx_item) (e : expr) : expr :=
  match Ki with
  | LetCtx x e2 => Let x e e2
  | VarBindCtx x e2 => VarBind x e e2
  | PopCtx l => Pop l e
  | AssignCtx x => Assign x e
  | StackLoadCtx => StackLoad e
  | StackAssignLCtx e2 => StackAssign e e2
  | StackAssignRCtx v1 => StackAssign (Val v1) e
  | StackFieldLCtx i e2 => StackFieldStore e i e2
  | StackFieldRCtx v1 i => StackFieldStore (Val v1) i e
  | AppLCtx e2 => App e e2
  | AppRCtx v1 => App (Val v1) e
  | IfCtx e1 e2 => If e e1 e2
  | SeqCtx e2 => Seq e e2
  | BinOpLCtx op e2 => BinOp op e e2
  | BinOpRCtx op v1 => BinOp op (Val v1) e
  | AllocCtx => Alloc e
  | FreeCtx => Free e
  | LoadCtx => Load e
  | StoreLCtx e2 => Store e e2
  | StoreRCtx v1 => Store (Val v1) e
  | OffsetLCtx e2 => Offset e e2
  | OffsetRCtx v1 => Offset (Val v1) e
  | StructCtx vs es => Struct vs (e :: es)
  | StructLoadCtx i => StructLoad e i
  | StructStoreCtx x i => StructStore x i e
  | NewCtx vs es => New vs (e :: es)
  | FieldLoadCtx i => FieldLoad e i
  | FieldStoreLCtx i e2 => FieldStore e i e2
  | FieldStoreRCtx v i => FieldStore (Val v) i e
  end.

Definition observation := Empty_set.

Inductive base_step : expr → state → list observation → expr → state → list expr → Prop :=
  | RecS f x e σ :
      base_step (Rec f x e) σ [] (Val (RecV f x e)) σ []
  | AppS f x e v σ :
      base_step (App (Val (RecV f x e)) (Val v)) σ []
        (subst_binder x v (subst_binder f (RecV f x e) e)) σ []
  | LetS x v e2 σ :
      base_step (Let x (Val v) e2) σ [] (subst_binder x v e2) σ []
  | VarBindS x v e2 σ :
      let l := cjr_next σ in
      base_step (VarBind x (Val v) e2) σ []
        (Pop (StackId l) (subst_var x l e2))
        (set_next (l + 1) (set_stack (<[StackId l := v]> (cjr_stack σ)) σ)) []
  | PopS l v σ :
      base_step (Pop l (Val v)) σ [] (Val v) (set_stack (delete l (cjr_stack σ)) σ) []
  | StackLoadS (z : loc) v σ :
      cjr_stack σ !! StackId z = Some v →
      base_step (StackLoad (Val (LitV (LitStack z)))) σ [] (Val v) σ []
  | StackAssignS (z : loc) v σ :
      is_Some (cjr_stack σ !! StackId z) →
      base_step (StackAssign (Val (LitV (LitStack z))) (Val v)) σ []
        (Val (LitV LitUnit)) (set_stack (<[StackId z := v]> (cjr_stack σ)) σ) []
  | StackFieldS (z : loc) i vs v σ w :
      cjr_stack σ !! StackId z = Some (StructV vs) →
      vs !! i = Some w →
      base_step (StackFieldStore (Val (LitV (LitStack z))) i (Val v)) σ []
        (Val (LitV LitUnit))
        (set_stack (<[StackId z := StructV (set_nth i v vs)]> (cjr_stack σ)) σ) []
  | IfTrueS e1 e2 σ :
      base_step (If (Val (LitV (LitBool true))) e1 e2) σ [] e1 σ []
  | IfFalseS e1 e2 σ :
      base_step (If (Val (LitV (LitBool false))) e1 e2) σ [] e2 σ []
  | WhileS e1 e2 σ :
      base_step (While e1 e2) σ []
        (If e1 (Seq e2 (While e1 e2)) (Val (LitV LitUnit))) σ []
  | SeqS v e2 σ :
      base_step (Seq (Val v) e2) σ [] e2 σ []
  | BinOpS op v1 v2 v σ :
      bin_op_eval op v1 v2 = Some v →
      base_step (BinOp op (Val v1) (Val v2)) σ [] (Val v) σ []
  | StructStepS vs v es σ :
      base_step (Struct vs (Val v :: es)) σ [] (Struct (vs ++ [v]) es) σ []
  | StructDoneS vs σ :
      base_step (Struct vs []) σ [] (Val (StructV vs)) σ []
  | StructLoadS vs i v σ :
      vs !! i = Some v →
      base_step (StructLoad (Val (StructV vs)) i) σ [] (Val v) σ []
  | AllocS (n : Z) σ :
      (0 < n)%Z →
      let base := cjr_next σ in
      let len := Z.to_nat n in
      base_step (Alloc (Val (LitV (LitInt n)))) σ []
        (Val (LitV (LitPtr base)))
        (set_next (base + n)
          (set_blocks (<[RawId base := len]> (cjr_blocks σ))
            (set_raw (init_cells base len ∪ cjr_raw σ) σ))) []
  | FreeS l len σ :
      cjr_blocks σ !! RawId l = Some len →
      base_step (Free (Val (LitV (LitPtr l)))) σ []
        (Val (LitV LitUnit))
        (set_blocks (delete (RawId l) (cjr_blocks σ))
          (set_raw (free_cells l len (cjr_raw σ)) σ)) []
  | LoadS l v σ :
      cjr_raw σ !! RawId l = Some v →
      base_step (Load (Val (LitV (LitPtr l)))) σ [] (Val v) σ []
  | StoreS l v σ :
      is_Some (cjr_raw σ !! RawId l) →
      base_step (Store (Val (LitV (LitPtr l))) (Val v)) σ []
        (Val (LitV LitUnit)) (set_raw (<[RawId l := v]> (cjr_raw σ)) σ) []
  | OffsetS l (i : Z) σ :
      base_step (Offset (Val (LitV (LitPtr l))) (Val (LitV (LitInt i)))) σ []
        (Val (LitV (LitPtr (l + i)%Z))) σ []
  | NewStepS vs v es σ :
      base_step (New vs (Val v :: es)) σ [] (New (vs ++ [v]) es) σ []
  | NewDoneS vs σ :
      let o := cjr_next σ in
      base_step (New vs []) σ []
        (Val (LitV (LitObj o)))
        (set_next (o + 1) (set_obj (init_fields o vs 0 ∪ cjr_obj σ) σ)) []
  | FieldLoadS o i v σ :
      cjr_obj σ !! (ObjId o, i) = Some v →
      base_step (FieldLoad (Val (LitV (LitObj o))) i) σ [] (Val v) σ []
  | FieldStoreS o i v σ :
      is_Some (cjr_obj σ !! (ObjId o, i)) →
      base_step (FieldStore (Val (LitV (LitObj o))) i (Val v)) σ []
        (Val (LitV LitUnit))
        (set_obj (<[(ObjId o, i) := v]> (cjr_obj σ)) σ) [].

Lemma fill_item_val Ki e :
  is_Some (to_val (fill_item Ki e)) → is_Some (to_val e).
Proof. destruct Ki; simpl; intros [? ?]; discriminate. Qed.

Lemma fill_item_not_val Ki e : to_val (fill_item Ki e) = None.
Proof. by destruct Ki. Qed.

Lemma base_step_fill_item Ki e σ κ e' σ' efs :
  base_step (fill_item Ki e) σ κ e' σ' efs → is_Some (to_val e).
Proof.
  intros Hstep. destruct Ki; simpl in Hstep; inversion Hstep; simplify_eq; by eauto.
Qed.

Lemma fill_item_inj Ki : Inj (=) (=) (fill_item Ki).
Proof. intros e1 e2. destruct Ki; inversion 1; auto. Qed.

Lemma fill_item_eq_no_val Ki1 e1 Ki2 e2 :
  fill_item Ki1 e1 = fill_item Ki2 e2 →
  to_val e1 = None → to_val e2 = None →
  Ki1 = Ki2 ∧ e1 = e2.
Proof.
  destruct Ki1, Ki2; simpl; intros Heq Hv1 Hv2;
    inversion Heq; subst; try discriminate; auto.
Qed.

Lemma val_base_stuck e1 σ1 κ e2 σ2 efs :
  base_step e1 σ1 κ e2 σ2 efs → to_val e1 = None.
Proof. inversion 1; done. Qed.

Lemma cjr_ectxi_mixin : EctxiLanguageMixin of_val to_val fill_item base_step.
Proof.
  split.
  - apply to_of_val.
  - apply of_to_val.
  - apply val_base_stuck.
  - apply fill_item_val.
  - apply fill_item_inj.
  - intros Ki1 Ki2 e1 e2 H1 H2 Heq.
    by destruct (fill_item_eq_no_val Ki1 e1 Ki2 e2 Heq H1 H2) as [-> _].
  - apply base_step_fill_item.
Qed.

Canonical Structure cjr_ectxi_lang : ectxiLanguage := EctxiLanguage cjr_ectxi_mixin.
Canonical Structure cjr_ectx_lang : ectxLanguage := EctxLanguageOfEctxi cjr_ectxi_lang.
Canonical Structure cjr_lang : language := LanguageOfEctx cjr_ectx_lang.

Lemma base_step_det e σ κ e' σ' efs κ2 e2 σ2 efs2 :
  base_step e σ κ e' σ' efs →
  base_step e σ κ2 e2 σ2 efs2 →
  κ = κ2 ∧ e' = e2 ∧ σ' = σ2 ∧ efs = efs2.
Proof.
  intros H1 H2. destruct H1; inversion H2; simplify_eq/=.
  all: repeat match goal with
    | H1 : ?m !! ?i = Some ?a, H2 : ?m !! ?i = Some ?b |- _ =>
        rewrite H1 in H2; inversion H2; clear H2; subst
    | H1 : bin_op_eval ?op ?v1 ?v2 = Some ?a,
        H2 : bin_op_eval ?op ?v1 ?v2 = Some ?b |- _ =>
        rewrite H1 in H2; inversion H2; clear H2; subst
    end.
  all: done.
Qed.

Lemma stack_fresh σ : state_wf σ → cjr_stack σ !! StackId (cjr_next σ) = None.
Proof.
  intros Hwf. destruct (cjr_stack σ !! StackId (cjr_next σ)) eqn:Heq; last done.
  apply elem_of_dom_2 in Heq. pose proof (wf_stack _ Hwf _ Heq). lia.
Qed.

Lemma raw_fresh σ : state_wf σ → cjr_raw σ !! RawId (cjr_next σ) = None.
Proof.
  intros Hwf. destruct (cjr_raw σ !! RawId (cjr_next σ)) eqn:Heq; last done.
  apply elem_of_dom_2 in Heq. pose proof (wf_raw _ Hwf _ Heq). lia.
Qed.

Lemma block_fresh σ : state_wf σ → cjr_blocks σ !! RawId (cjr_next σ) = None.
Proof.
  intros Hwf. destruct (cjr_blocks σ !! RawId (cjr_next σ)) eqn:Heq; last done.
  apply elem_of_dom_2 in Heq. pose proof (wf_block _ Hwf _ Heq). lia.
Qed.

Lemma obj_fresh σ i : state_wf σ → cjr_obj σ !! (ObjId (cjr_next σ), i) = None.
Proof.
  intros Hwf. destruct (cjr_obj σ !! (ObjId (cjr_next σ), i)) eqn:Heq; last done.
  apply elem_of_dom_2 in Heq. pose proof (wf_obj _ Hwf _ _ Heq). lia.
Qed.

Lemma init_cells_one base :
  init_cells base 1 = {[RawId base := LitV (LitInt 0)]}.
Proof. simpl. by rewrite Z.add_0_r. Qed.

Lemma free_cells_one l m : free_cells l 1 m = delete (RawId l) m.
Proof. simpl. by rewrite Z.add_0_r. Qed.

Lemma wf_stack_alloc σ v :
  state_wf σ →
  let l := cjr_next σ in
  state_wf (set_next (l + 1)%Z (set_stack (<[StackId l := v]> (cjr_stack σ)) σ)).
Proof.
  intros Hwf l. destruct Hwf as [Hs Hr Hb Ho Hc Hd]. split; simpl.
  - intros z Hz. rewrite dom_insert elem_of_union elem_of_singleton in Hz.
    destruct Hz as [Hz|Hz].
    + injection Hz as ->. lia.
    + pose proof (Hs z Hz). lia.
  - intros z Hz. pose proof (Hr z Hz). lia.
  - intros z Hz. pose proof (Hb z Hz). lia.
  - intros z i Hz. pose proof (Ho z i Hz). lia.
  - intros z n Hn. destruct (Hc z n Hn) as [Hle Hcell]. split; [lia|done].
  - done.
Qed.

Lemma wf_stack_delete σ l :
  state_wf σ → state_wf (set_stack (delete l (cjr_stack σ)) σ).
Proof.
  intros [Hs Hr Hb Ho Hc Hd]. split; simpl; try done.
  intros z Hz. apply Hs. rewrite dom_delete in Hz. set_solver.
Qed.

Lemma wf_stack_upd σ z v :
  is_Some (cjr_stack σ !! StackId z) → state_wf σ →
  state_wf (set_stack (<[StackId z := v]> (cjr_stack σ)) σ).
Proof.
  intros Hsome [Hs Hr Hb Ho Hc Hd]. split; simpl; try done.
  intros z' Hz. rewrite dom_insert elem_of_union elem_of_singleton in Hz.
  destruct Hz as [Hz|Hz]; [|by apply Hs].
  injection Hz as ->. apply elem_of_dom in Hsome. by apply Hs.
Qed.

Lemma wf_raw_store σ l v :
  is_Some (cjr_raw σ !! RawId l) → state_wf σ →
  state_wf (set_raw (<[RawId l := v]> (cjr_raw σ)) σ).
Proof.
  intros Hsome [Hs Hr Hb Ho Hc Hd]. split; simpl; try done.
  - intros z Hz. rewrite dom_insert elem_of_union elem_of_singleton in Hz.
    destruct Hz as [Hz|Hz]; [|by apply Hr].
    injection Hz as ->. apply elem_of_dom in Hsome. by apply Hr.
  - intros z n Hn. destruct (Hc z n Hn) as [Hle Hcell]. split; [done|].
    intros i Hi. destruct (Hcell i Hi) as [w Hw].
    destruct (decide (RawId (z + Z.of_nat i)%Z = RawId l)) as [Heq|Hne];
      [rewrite Heq lookup_insert; by eauto|rewrite lookup_insert_ne //; eauto].
Qed.

Lemma wf_field_store σ o i v :
  is_Some (cjr_obj σ !! (ObjId o, i)) → state_wf σ →
  state_wf (set_obj (<[(ObjId o, i) := v]> (cjr_obj σ)) σ).
Proof.
  intros Hsome [Hs Hr Hb Ho Hc Hd]. split; simpl; try done.
  intros z j Hz. eapply Ho.
  rewrite dom_insert elem_of_union elem_of_singleton in Hz.
  destruct Hz as [Hz|Hz]; [injection Hz as -> ->; apply elem_of_dom; done|done].
Qed.

Lemma wf_alloc_one σ :
  state_wf σ →
  let base := cjr_next σ in
  state_wf
    (set_next (base + 1)%Z
       (set_blocks (<[RawId base := 1%nat]> (cjr_blocks σ))
          (set_raw ({[RawId base := LitV (LitInt 0)]} ∪ cjr_raw σ) σ))).
Proof.
  intros [Hs Hr Hb Ho Hc Hd] base. split; simpl.
  - intros z Hz. pose proof (Hs z Hz). lia.
  - intros z Hz. rewrite dom_union_L elem_of_union dom_singleton_L elem_of_singleton in Hz.
    destruct Hz as [Hz|Hz]; [apply (inj RawId) in Hz; subst; lia|pose proof (Hr z Hz); lia].
  - intros z Hz. rewrite dom_insert elem_of_union elem_of_singleton in Hz.
    destruct Hz as [Hz|Hz]; [apply (inj RawId) in Hz; subst; lia|pose proof (Hb z Hz); lia].
  - intros z i Hz. pose proof (Ho z i Hz). lia.
  - intros z n Hn.
    destruct (decide (RawId z = RawId base)) as [Heq|Hne].
    + apply (inj RawId) in Heq. subst. rewrite lookup_insert in Hn. injection Hn as <-.
      split; [lia|]. intros i Hi. replace i with 0%nat by lia.
      rewrite Z.add_0_r. exists (LitV (LitInt 0)).
      apply lookup_union_Some_l. by rewrite lookup_singleton.
    + rewrite lookup_insert_ne in Hn; last done.
      destruct (Hc z n Hn) as [Hle Hcell]. split; [lia|].
      intros i Hi. destruct (Hcell i Hi) as [w Hw].
      rewrite lookup_union_r; first by eauto.
      rewrite lookup_singleton_ne //.
      intros Heq. injection Heq as Heq. lia.
  - intros l1 n1 l2 n2 H1 H2 Hneq.
    destruct (decide (RawId l1 = RawId base)) as [E1|N1];
    destruct (decide (RawId l2 = RawId base)) as [E2|N2].
    + apply (inj RawId) in E1, E2. subst. done.
    + apply (inj RawId) in E1. subst. rewrite lookup_insert in H1. injection H1 as <-.
      rewrite lookup_insert_ne in H2; last done.
      destruct (Hc l2 n2 H2) as [Hle _]. lia.
    + apply (inj RawId) in E2. subst. rewrite lookup_insert in H2. injection H2 as <-.
      rewrite lookup_insert_ne in H1; last done.
      destruct (Hc l1 n1 H1) as [Hle _]. lia.
    + rewrite lookup_insert_ne in H1; last done.
      rewrite lookup_insert_ne in H2; last done.
      eapply Hd; eauto.
Qed.

Lemma wf_alloc_one_insert σ :
  state_wf σ →
  let base := cjr_next σ in
  state_wf
    (set_next (base + 1)%Z
       (set_blocks (<[RawId base := 1%nat]> (cjr_blocks σ))
          (set_raw (<[RawId base := LitV (LitInt 0)]> (cjr_raw σ)) σ))).
Proof.
  intros Hwf base.
  rewrite (insert_union_singleton_l (cjr_raw σ) (RawId base) (LitV (LitInt 0))).
  by apply wf_alloc_one.
Qed.

Lemma wf_free_one σ l :
  cjr_blocks σ !! RawId l = Some 1%nat →
  state_wf σ →
  state_wf (set_blocks (delete (RawId l) (cjr_blocks σ))
             (set_raw (delete (RawId l) (cjr_raw σ)) σ)).
Proof.
  intros Hlen [Hs Hr Hb Ho Hc Hd]. split; simpl; try done.
  - intros z Hz. rewrite dom_delete in Hz. eapply Hr. set_solver.
  - intros z Hz. rewrite dom_delete in Hz. eapply Hb. set_solver.
  - intros z n Hn.
    destruct (decide (z = l)) as [->|Hne].
    + rewrite lookup_delete in Hn. discriminate.
    + rewrite lookup_delete_ne in Hn; last (intros Heq; apply (inj RawId) in Heq; done).
      destruct (Hc z n Hn) as [Hle Hcell]. split.
      { done. }
      { intros i Hi. destruct (Hcell i Hi) as [w Hw].
        destruct (decide ((z + Z.of_nat i)%Z = l)) as [Heq|Hi'].
        - destruct (Hd l 1%nat z n Hlen Hn) as [Hdis|Hdis]; lia.
        - rewrite lookup_delete_ne; last (intros Heq'; apply (inj RawId) in Heq'; done). eauto. }
  - intros l1 n1 l2 n2 H1 H2 Hneq.
    destruct (decide (l1 = l)) as [->|Hn1].
    + rewrite lookup_delete in H1. discriminate.
    + destruct (decide (l2 = l)) as [->|Hn2].
      * rewrite lookup_delete in H2. discriminate.
      * rewrite lookup_delete_ne in H1; last (intros Heq; apply (inj RawId) in Heq; done).
        rewrite lookup_delete_ne in H2; last (intros Heq; apply (inj RawId) in Heq; done).
        eapply Hd; eauto.
Qed.

Lemma init_fields_carrier o vs i l j w :
  init_fields o vs i !! (ObjId l, j) = Some w → l = o.
Proof.
  revert i. induction vs as [|v vs IH]; intros i; simpl; [discriminate|].
  destruct (decide ((ObjId l, j) = (ObjId o, i))) as [Heq|Hne].
  - injection Heq as ->. done.
  - rewrite lookup_insert_ne //. eauto.
Qed.

Lemma init_fields_shift o vs i k :
  init_fields o vs i !! (ObjId o, i + k) = vs !! k.
Proof.
  revert i k. induction vs as [|v vs IH]; intros i k; simpl; [done|].
  destruct k as [|k].
  - rewrite Nat.add_0_r lookup_insert //.
  - rewrite lookup_insert_ne.
    { assert ((i + S k)%nat = (S i + k)%nat) as -> by lia. by rewrite IH. }
    { intros Heq. apply (f_equal snd) in Heq. simpl in Heq. lia. }
Qed.

Lemma wf_new σ vs :
  state_wf σ →
  let o := cjr_next σ in
  state_wf (set_next (o + 1)%Z (set_obj (init_fields o vs 0 ∪ cjr_obj σ) σ)).
Proof.
  intros [Hs Hr Hb Ho Hc Hd] o. split; simpl.
  - intros z Hz. pose proof (Hs z Hz). lia.
  - intros z Hz. pose proof (Hr z Hz). lia.
  - intros z Hz. pose proof (Hb z Hz). lia.
  - intros z j Hz. rewrite dom_union_L elem_of_union in Hz. destruct Hz as [Hz|Hz].
    + apply elem_of_dom in Hz as [w Hw].
      assert (z = o) as -> by (eapply init_fields_carrier; exact Hw). lia.
    + pose proof (Ho z j Hz). lia.
  - intros z n Hn. destruct (Hc z n Hn) as [Hle Hcell]. split; [lia|done].
  - done.
Qed.

Lemma init_fields_low o vs i j :
  (j < i)%nat → init_fields o vs i !! (ObjId o, j) = None.
Proof.
  revert i j. induction vs as [|v vs IH]; intros i j Hj; simpl; [done|].
  rewrite lookup_insert_ne.
  - apply IH. lia.
  - intros Heq. apply (f_equal snd) in Heq. simpl in Heq. lia.
Qed.

Lemma init_fields_fresh σ vs :
  state_wf σ →
  init_fields (cjr_next σ) vs 0 ##ₘ cjr_obj σ.
Proof.
  intros Hwf. apply map_disjoint_spec. intros [[l] j] v1 v2 H1 H2.
  assert (l = cjr_next σ) as -> by (eapply init_fields_carrier; exact H1).
  rewrite (obj_fresh _ j Hwf) in H2. discriminate.
Qed.

Lemma init_cells_lookup base n i :
  (i < n)%nat →
  init_cells base n !! RawId (base + Z.of_nat i)%Z = Some (LitV (LitInt 0)).
Proof.
  revert i. induction n as [|n IH]; intros i Hi; [lia|].
  simpl.
  destruct (decide (i = n)) as [->|Hne].
  - by rewrite lookup_insert.
  - rewrite lookup_insert_ne; last first.
    { intros Heq. apply (inj RawId) in Heq. lia. }
    apply IH. lia.
Qed.

Lemma init_cells_addr base n l v :
  init_cells base n !! RawId l = Some v →
  (base ≤ l < base + Z.of_nat n)%Z.
Proof.
  revert l v. induction n as [|n IH]; intros l v; simpl; [discriminate|].
  destruct (decide (RawId l = RawId (base + Z.of_nat n)%Z)) as [Heq|Hne].
  - rewrite Heq lookup_insert. intros [= <-].
    apply (inj RawId) in Heq. lia.
  - rewrite lookup_insert_ne //. intros Hlook.
    specialize (IH l v Hlook). lia.
Qed.

Lemma init_cells_below base n z :
  (z < base)%Z → init_cells base n !! RawId z = None.
Proof.
  intros Hz. destruct (init_cells base n !! RawId z) as [v|] eqn:Hlook; [|done].
  apply init_cells_addr in Hlook. lia.
Qed.

Lemma init_cells_high base n z :
  (base + Z.of_nat n ≤ z)%Z → init_cells base n !! RawId z = None.
Proof.
  intros Hz. destruct (init_cells base n !! RawId z) as [v|] eqn:Hlook; [|done].
  apply init_cells_addr in Hlook. lia.
Qed.

Lemma init_cells_fresh σ n :
  state_wf σ →
  init_cells (cjr_next σ) n ##ₘ cjr_raw σ.
Proof.
  intros Hwf. apply map_disjoint_spec. intros [l] v1 v2 H1 H2.
  apply init_cells_addr in H1.
  apply elem_of_dom_2 in H2.
  pose proof (wf_raw _ Hwf _ H2). lia.
Qed.

Lemma wf_alloc σ (n : Z) :
  (0 < n)%Z → state_wf σ →
  let base := cjr_next σ in
  let len := Z.to_nat n in
  state_wf
    (set_next (base + n)%Z
       (set_blocks (<[RawId base := len]> (cjr_blocks σ))
          (set_raw (init_cells base len ∪ cjr_raw σ) σ))).
Proof.
  intros Hn Hwf.
  cbv zeta.
  set (base := cjr_next σ).
  set (len := Z.to_nat n).
  destruct Hwf as [Hs Hr Hb Ho Hc Hd].
  assert (Z.of_nat len = n) as HlenZ by (unfold len; lia).
  split; simpl.
  - intros z Hz. pose proof (Hs z Hz). lia.
  - intros z Hz. rewrite dom_union_L elem_of_union in Hz.
    destruct Hz as [Hz|Hz].
    + apply elem_of_dom in Hz as [v Hv]. apply init_cells_addr in Hv. lia.
    + pose proof (Hr z Hz). lia.
  - intros z Hz. rewrite dom_insert elem_of_union elem_of_singleton in Hz.
    destruct Hz as [Hz|Hz].
    + apply (inj RawId) in Hz. rewrite Hz. lia.
    + pose proof (Hb z Hz). lia.
  - intros z i Hz. pose proof (Ho z i Hz). lia.
  - intros z k Hk. simpl in Hk.
    destruct (decide (RawId z = RawId base)) as [Heq|Hne].
    + apply (inj RawId) in Heq. rewrite Heq in Hk. rewrite Heq.
      rewrite lookup_insert in Hk.
      assert (k = len) as Hklen by congruence.
      rewrite Hklen. split; [lia|]. intros i Hi.
      eexists. apply lookup_union_Some_l. by apply init_cells_lookup.
    + rewrite lookup_insert_ne // in Hk.
      destruct (Hc z k Hk) as [Hle Hcell]. split; [lia|].
      intros i Hi. destruct (Hcell i Hi) as [w Hw].
      rewrite lookup_union_r; [by eauto|].
      apply init_cells_below. lia.
  - intros l1 n1 l2 n2 H1 H2 Hneq. simpl in H1, H2.
    destruct (decide (RawId l1 = RawId base)) as [E1|N1];
    destruct (decide (RawId l2 = RawId base)) as [E2|N2].
    + apply (inj RawId) in E1, E2. rewrite E1 in Hneq. rewrite E2 in Hneq. done.
    + apply (inj RawId) in E1. rewrite E1 in H1.
      rewrite lookup_insert in H1.
      assert (n1 = len) as -> by congruence.
      rewrite lookup_insert_ne // in H2.
      destruct (Hc l2 n2 H2) as [Hend _]. lia.
    + apply (inj RawId) in E2. rewrite E2 in H2.
      rewrite lookup_insert in H2.
      assert (n2 = len) as -> by congruence.
      rewrite lookup_insert_ne // in H1.
      destruct (Hc l1 n1 H1) as [Hend _]. lia.
    + rewrite lookup_insert_ne // in H1.
      rewrite lookup_insert_ne // in H2.
      eapply Hd; eauto.
Qed.
