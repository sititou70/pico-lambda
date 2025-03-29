Require Import Nat.
Require Import Ensembles.
Require Import Relation_Operators.

Inductive type: Type :=
  | type_arrow: type -> type -> type
  | type_nat: type.

Inductive term: Type :=
  | term_var: nat -> term
  | term_app: term -> term -> term
  | term_abs: nat -> type -> term -> term.

Inductive value: term -> Prop :=
  | value_abs:
    forall x T t,
    value (term_abs x T t).

Fixpoint freash_variable (t: term): nat :=
  match t with
  | term_var x => x + 1
  | term_abs x T t1 => x + (freash_variable t1)
  | term_app t1 t2 => (freash_variable t1) + (freash_variable t2)
  end.

Fixpoint alpha_conversion_body (t: term) (from: nat) (to: nat): term :=
  match t with
  | term_var x => if Nat.eqb x from then term_var to else term_var x
  | term_abs x T t1 => if Nat.eqb x from then term_abs x T t1 else term_abs x T (alpha_conversion_body t1 from to)
  | term_app t1 t2 => term_app (alpha_conversion_body t1 from to) (alpha_conversion_body t2 from to)
  end.
Definition alpha_conversion (x: nat) (T: type) (t1: term) (to : nat): term :=
  term_abs to T (alpha_conversion_body t1 x to).

Fixpoint assign (t: term) (from: nat) (to: term): term :=
  match t with
  | term_var x => if Nat.eqb x from then to else t
  | term_abs x T t1 => alpha_conversion x T t1 ((freash_variable to) + from)
  | term_app t1 t2 => term_app (assign t1 from to) (assign t2 from to)
  end.

Inductive eval1: term -> term -> Prop :=
  | E_App1:
    forall t1 t1' t2,
    eval1 t1 t1' ->
    eval1 (term_app t1 t2) (term_app t1' t2)
  | E_App2:
    forall t2 t2' v1,
    value v1 ->
    eval1 t2 t2' ->
    eval1 (term_app v1 t2) (term_app v1 t2')
  | E_AppAbs:
    forall x T11 t12 v2,
    value v2 ->
    eval1 (term_app (term_abs x T11 t12) v2) (assign t12 x v2).

Definition eval := clos_trans_n1 term eval1.
(* Inductive typed: context → tm → ty → Prop :=
| T_Var : ∀ Γ x T,
    Γ x = Some T →
    has_type Γ (tm_var x) T
| T_Abs : ∀ Γ x T11 T12 t12,
    has_type (extend Γ x T11) t12 T12 →
    has_type Γ (tm_abs x T11 t12) (ty_arrow T11 T12)
| T_App : ∀ T11 T12 Γ t1 t2,
    has_type Γ t1 (ty_arrow T11 T12) →
    has_type Γ t2 T11 →
    has_type Γ (term_app t1 t2) T12
| T_True : ∀ Γ,
      has_type Γ tm_true ty_Bool
| T_False : ∀ Γ,
      has_type Γ tm_false ty_Bool
| T_If : ∀ t1 t2 t3 T Γ,
      has_type Γ t1 ty_Bool →
      has_type Γ t2 T →
      has_type Γ t3 T →
      has_type Γ (tm_if t1 t2 t3) T. *)
