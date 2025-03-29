Require Import Lia.
Require Import Nat.
Require Import Relation_Operators.
Require Import FunInd.
Require Import Recdef.
Require Import PeanoNat.

Inductive type: Type :=
  | type_arrow: type -> type -> type
  | type_nat: type.

Inductive term: Type :=
  | term_var: nat -> term
  | term_abs: nat -> type -> term -> term
  | term_app: term -> term -> term.

Inductive value: term -> Prop :=
  | value_abs:
    forall x T t,
    value (term_abs x T t).

Fixpoint fresh_variable (t: term): nat :=
  match t with
  | term_var x => x + 1
  | term_abs x T t1 => x + (fresh_variable t1) + 1
  | term_app t1 t2 => (fresh_variable t1) + (fresh_variable t2) + 1
  end.

Fixpoint replace_free_variable (t: term) (from: nat) (to: nat): term :=
  match t with
  | term_var x => if Nat.eqb x from then term_var to else term_var x
  | term_abs x T t1 => if Nat.eqb x from then term_abs x T t1 else term_abs x T (replace_free_variable t1 from to)
  | term_app t1 t2 => term_app (replace_free_variable t1 from to) (replace_free_variable t2 from to)
  end.

Fixpoint term_size (t: term): nat :=
  match t with
  | term_var x => 1
  | term_abs x T t1 => 1 + term_size t1
  | term_app t1 t2 => (term_size t1) + (term_size t2)
  end.  
Function assign (t: term) (from: nat) (to: term) {measure term_size t}: term :=
  match t with
  | term_var x => if Nat.eqb x from then to else t
  | term_abs x T t1 =>
    let fresh_var := (fresh_variable to) + from + (fresh_variable t1) in
    let fresh_body := (replace_free_variable t1 x fresh_var) in
    term_abs fresh_var T (assign fresh_body from to)
  | term_app t1 t2 => term_app (assign t1 from to) (assign t2 from to)
  end.
Proof.
Admitted.

Inductive eval: term -> term -> Prop :=
  | E_App1:
    forall t1 t1' t2,
    eval t1 t1' ->
    eval (term_app t1 t2) (term_app t1' t2)
  | E_App2:
    forall t2 t2' v1,
    value v1 ->
    eval t2 t2' ->
    eval (term_app v1 t2) (term_app v1 t2')
  | E_AppAbs:
    forall x T11 t12 v2,
    value v2 ->
    eval (term_app (term_abs x T11 t12) v2) (assign t12 x v2).

Definition evalmany := clos_trans_n1 term eval.

Definition context := nat -> option type.
Definition empty_context: context := (fun _ => None).
Definition extend_context (ctx : context) (x: nat) (T: type) :=
  fun x' => if Nat.eqb x' x then Some T else ctx x'.

Inductive typed: context -> term -> type -> Prop :=
  | T_Var:
    forall ctx x T,
    ctx x = Some T ->
    typed ctx (term_var x) T
  | T_Abs:
    forall ctx x T1 t2 T2,
    typed (extend_context ctx x T1) t2 T2 ->
    typed ctx (term_abs x T1 t2) (type_arrow T1 T2)
  | T_App:
    forall ctx t1 T11 T12 t2,
    typed ctx t1 (type_arrow T11 T12) ->
    typed ctx t2 T11 ->
    typed ctx (term_app t1 t2) T12.

Theorem progress:
  forall t T,
  typed empty_context t T ->
  value t \/ exists t', eval t t'.
Proof.
  intros t T Htyped.
  remember empty_context as ctx.
  induction Htyped.

    (* T_Var *)
    +
    subst.
    inversion H.

    (* T_Abs *)
    +
    left.
    auto using value.

    (* T_App *)
    +
    right.
    destruct IHHtyped1; auto.

      (* t1 is value *)
      ++
      destruct IHHtyped2; auto.

        (* t2 is value *)
        +++
        inversion H.
        eauto using eval.

        (* t2 eval *)
        +++
        inversion H0 as [t2'].
        exists (term_app t1 t2').
        eauto using eval.

      (* t1 eval *)
      ++
      inversion H as [t1'].
      eauto using eval.
Qed.

Lemma assignation_preserves_type:
  forall ctx x S t T s,
  typed (extend_context ctx x S) t T ->
  typed ctx s S ->
  typed ctx (assign t x s) T.
Proof.
  intros ctx x S t T s.
  generalize dependent ctx.
  generalize dependent T.
  induction t; intros T ctx Httyped Hstyped.

    (* term_var *)
    +
    unfold extend_context in *.
    inversion Httyped; subst.
    rewrite assign_equation.
    
    destruct (Nat.eqb n x).

      (* n = x *)
      ++
      inversion H1.
      subst.
      auto.

      (* n <> x *)
      ++
      eauto using typed.
    
    (* term_abs *)
    +
    rename n into t1_x.
    rename t into T1.
    rename t0 into t2.
    inversion Httyped; subst.
    rewrite assign_equation.
    remember (fresh_variable s + x + fresh_variable t2) as fresh_var.
    constructor.
    admit.

    (* term_app *)
    +
    inversion Httyped; subst.
    rename T into T12.
    rewrite assign_equation.
    eauto using typed.
Admitted.

Theorem preservation:
  forall ctx t T t',
  typed ctx t T ->
  eval t t' ->
  typed ctx t' T.
Proof.
  intros ctx t T t' Htyped Heval.
  generalize dependent t'.
  induction Htyped; intros t' Heval.

    (* T_Var *)
    +
    inversion Heval.

    (* T_Abs *)
    +
    inversion Heval.

    (* T_App *)
    +
    inversion Heval; eauto using typed.

      (* E_AppAbs *)
      ++
      subst.
      inversion Htyped1.
      subst.
      eauto using assignation_preserves_type.
Qed.
