From cjr Require Export lang.
From iris.prelude Require Import options.

(** Surface forms used by the examples. Literals stay explicit [LitV] values. *)
Notation "e1 + e2" := (BinOp PlusOp e1%E e2%E) : expr_scope.
Notation "e1 - e2" := (BinOp MinusOp e1%E e2%E) : expr_scope.
Notation "e1 * e2" := (BinOp MulOp e1%E e2%E) : expr_scope.
Notation "e1 / e2" := (BinOp DivOp e1%E e2%E) (at level 40, left associativity) : expr_scope.
Notation "e1 % e2" := (BinOp RemOp e1%E e2%E) (at level 40, left associativity) : expr_scope.
Notation "e1 ≤ e2" := (BinOp LeOp e1%E e2%E) : expr_scope.

Bind Scope expr_scope with expr.

Notation "e1 .^ e2" := (BinOp BitXorOp e1%E e2%E) (at level 40, left associativity) : expr_scope.
Notation "e1 .& e2" := (BinOp BitAndOp e1%E e2%E) (at level 40, left associativity) : expr_scope.
