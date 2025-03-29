Require Import Lia.
Require Import List.
Import ListNotations.

Inductive type: Type :=
  | type_arrow: type -> type -> type
  | type_nat: type.

Inductive term: Type :=
  | term_var: nat -> term
  | term_abs: nat -> type -> term -> term
  | term_app: term -> term -> term.

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

Fixpoint max (l: list nat): nat :=
  match l with
    | [] => 0
    | n :: cdr => if (Nat.ltb n (max cdr)) then (max cdr) else n
  end.

Lemma existance_of_fresh_x:
  forall (l: list nat),
  exists x, not (In x l).
Proof.
Admitted.

Fixpoint replace_free_variable (t: term) (from_x: nat) (to_x: nat): term :=
  match t with
  | term_var x => if Nat.eqb x from_x then term_var to_x else t
  | term_abs x T t2 => if Nat.eqb x from_x then t else term_abs x T (replace_free_variable t2 from_x to_x)
  | term_app t1 t2 => term_app (replace_free_variable t1 from_x to_x) (replace_free_variable t2 from_x to_x)
  end.

Fixpoint variables (t: term): list nat :=
  match t with
    | term_var x => [x]
    | term_abs x T t2 => x :: (variables t2)
    | term_app t1 t2 => concat [variables t1; variables t2]
  end.

Lemma replace_free_variable_preserves_type:
  forall ctx x TX t T x',
  typed (extend_context ctx x TX) t T ->
  not (In x' (variables t)) ->
  typed (extend_context ctx x' TX) (replace_free_variable t x x') T.
Proof.
  intros ctx x TX t T x' Htyped Hfresh.

  remember (extend_context ctx x TX) as ctx'.
  induction Htyped.

    +
    rename x0 into t_x.
    unfold variables in *.
    unfold In in *.
    assert (Hfresh': t_x <> x') by lia.
    unfold replace_free_variable.
    assert (tmp: t_x = x \/ t_x <> x) by lia; destruct tmp.

      ++
      subst.
      unfold extend_context in *.
      rewrite (PeanoNat.Nat.eqb_refl) in *.
      constructor.
      rewrite (PeanoNat.Nat.eqb_refl) in *.
      auto.

      ++
      rewrite (proj2 (PeanoNat.Nat.eqb_neq _ _)); auto.
      constructor.
      unfold extend_context in *.
      rewrite (proj2 (PeanoNat.Nat.eqb_neq _ _)); auto.
      subst.
      rewrite (proj2 (PeanoNat.Nat.eqb_neq _ _)) in *; auto.
    
    +
    rename x0 into t_x.
    rename T1 into t_T1.
    rename t2 into t_t2.

    assert (Hfresh': t_x <> x').
    {
      unfold variables in Hfresh.
      unfold In in Hfresh.
      lia.
    }

    assert (tmp: t_x = x \/ t_x <> x) by lia; destruct tmp.

      ++
      unfold replace_free_variable.
      fold replace_free_variable.
      subst.
      rewrite (PeanoNat.Nat.eqb_refl).
      constructor.
      admit.

      ++
      unfold replace_free_variable.
      fold replace_free_variable.
      subst.
      rewrite (proj2 (PeanoNat.Nat.eqb_neq _ _)); auto.
      constructor.
    
    Search (Nat.eqb).
Admitted.

Definition alpha_conversion (x: nat) (T1: type) (t2: term): nat * type * term :=
  let fresh_x := max (x :: (variables t2)) + 1 in
  let fresh_t2 := replace_free_variable t2 x fresh_x in
  (fresh_x, T1, fresh_t2).

Theorem alpha_conversion_preserves_type:
  forall ctx x T1 t2 T,
  typed ctx (term_abs x T1 t2) T ->
  let '(x', T1', t2') := alpha_conversion x T1 t2 in
  typed ctx (term_abs x' T1' t2') T.
Proof.
  intros ctx x T1 t2 T Htyped.

  (* intro let *)
  remember (alpha_conversion x T1 t2) as converted.
  destruct converted as [tuple t2'].
  destruct tuple as [x' T1'].

  (* unfold alpha_conversion *)
  unfold alpha_conversion in *.
  inversion Heqconverted; subst; clear Heqconverted.
  remember ((if Nat.ltb x (max (variables t2)) then max (variables t2) else x) + 1) as x'.

  (* inversion T *)
  inversion Htyped; subst.
  remember ((if Nat.ltb x (max (variables t2)) then max (variables t2) else x) + 1) as x'.
  rename H4 into Ht2typed.

  apply T_Abs.

  (* rename *)
  clear Htyped.
  rename t2 into t.
  rename T2 into T.
  rename T1 into TX.
  rename Ht2typed into Htyped.
Admitted.
