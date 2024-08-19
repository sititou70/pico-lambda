Require Import commons.

(* 型 *)
Inductive ty : Type :=
  | ty_arrow : ty -> ty -> ty
  | ty_nat : ty.

(* 項 *)
Inductive tm : Type :=
  | tm_var : nat -> tm
  | tm_abs : nat -> ty -> tm -> tm
  | tm_app : tm -> tm -> tm
  | tm_zero : tm
  | tm_succ : tm -> tm
  | tm_let : nat -> tm -> tm -> tm.

(* 値 *)
Inductive value : tm -> Prop :=
  | value_abs :
    forall x T t,
    value (tm_abs x T t)
  | value_zero : value tm_zero
  | value_succ :
    forall t,
    t = tm_zero \/ (exists t', t = tm_succ t') ->
    value (tm_succ t).

(* 代入 *)
(*
  sは閉じた項であると仮定する。したがって、x \notin FV(s)の前提は自明に満たされるため省略できる。
*)
Fixpoint subst (x : nat) (s : tm) (t : tm) : tm :=
  match t with
  | tm_var x' =>
    if Nat.eqb x x' then s else t
  | tm_abs x' T t1 =>
    tm_abs x' T (if PeanoNat.Nat.eqb x x' then t1 else (subst x s t1))
  | tm_app t1 t2 =>
    tm_app (subst x s t1) (subst x s t2)
  | tm_zero =>
    tm_zero
  | tm_succ t1 =>
    tm_succ (subst x s t1)
  | tm_let x' t1 t2 =>
    (
      if
        PeanoNat.Nat.eqb x x'
      then
        tm_let x' (subst x s t1) t2
      else
        tm_let x' (subst x s t1) (subst x s t2)
    )
  end.

(* 評価規則 *)
Reserved Notation "t1 '==>' t2" (at level 40).
Inductive eval1 : tm -> tm -> Prop :=
  | E_App1 :
    forall t1 t1' t2,
    t1 ==> t1' ->
    tm_app t1 t2 ==> tm_app t1' t2
  | E_App2 :
    forall v1 t2 t2',
    value v1 ->
    t2 ==> t2' ->
    tm_app v1 t2 ==> tm_app v1 t2'
  | E_AppAbs :
    forall x T11 t12 v2,
    value v2 ->
    (tm_app (tm_abs x T11 t12) v2) ==> (subst x v2 t12)
  | E_Succ :
    forall t1 t1',
    t1 ==> t1' ->
    tm_succ t1 ==> tm_succ t1'
  | E_Let :
    forall x t1 t1' t2,
    t1 ==> t1' ->
    tm_let x t1 t2 ==> tm_let x t1' t2
  | E_LetV :
    forall x v1 t2,
    value v1 ->
    tm_let x v1 t2 ==> (subst x v1 t2)
where "t1 '==>' t2" := (eval1 t1 t2).

Definition relation (X : Type) := X -> X -> Prop.
Inductive refl_trans_closure {X : Type} (R: relation X): X -> X -> Prop :=
  | rsc_refl :
    forall (x : X),
    refl_trans_closure R x x
  | rsc_trans :
    forall (x y z : X),
    R x y ->
    refl_trans_closure R y z ->
    refl_trans_closure R x z.
Notation evalmany := (refl_trans_closure eval1).
Notation "t1 '==>*' t2" := (evalmany t1 t2) (at level 40).

(* 文脈 *)
Definition partial_map (A : Type) := nat -> option A.
Definition ctx := partial_map ty.

Definition empty_ctx {A : Type} : partial_map A :=
  (fun _ => None).

Definition bind_ctx {A : Type} (ctx : partial_map A) (x : nat) (T : A) :=
  fun x' => if Nat.eqb x x' then Some T else ctx x'.

(* 型付け規則 *)
Inductive typed : ctx -> tm -> ty -> Prop :=
  | T_Var :
    forall ctx x T,
    ctx x = Some T ->
    typed ctx (tm_var x) T
  | T_Abs :
    forall ctx x T1 t2 T2,
    typed (bind_ctx ctx x T1) t2 T2 ->
    typed ctx (tm_abs x T1 t2) (ty_arrow T1 T2)
  | T_App :
    forall ctx t1 T11 T12 t2,
    typed ctx t1 (ty_arrow T11 T12) ->
    typed ctx t2 T11 ->
    typed ctx (tm_app t1 t2) T12
  | T_Zero :
    forall ctx,
    typed ctx tm_zero ty_nat
  | T_Succ :
    forall ctx t1,
    typed ctx t1 ty_nat ->
    typed ctx (tm_succ t1) ty_nat
  | T_Let :
    forall ctx t1 T1 t2 T2 x,
    typed ctx t1 T1 ->
    typed (bind_ctx ctx x T1) t2 T2 ->
    typed ctx (tm_let x t1 t2) T2.

(* 自由な出現 *)
Inductive appears_free_in : nat -> tm -> Prop :=
  | afi_var :
    forall x,
    appears_free_in x (tm_var x)
  | afi_abs :
    forall x y T11 t12,
    x <> y ->
    appears_free_in x t12 ->
    appears_free_in x (tm_abs y T11 t12)
  | afi_app1 :
    forall x t1 t2,
    appears_free_in x t1 -> appears_free_in x (tm_app t1 t2)
  | afi_app2 :
    forall x t1 t2,
    appears_free_in x t2 -> appears_free_in x (tm_app t1 t2)
  | afi_succ :
    forall x t1,
    appears_free_in x t1 ->
    appears_free_in x (tm_succ t1)
  | afi_let1 :
    forall x y t1 t2,
    x <> y ->
    appears_free_in x t2 ->
    appears_free_in x (tm_let y t1 t2)
  | afi_let2 :
    forall x y t1 t2,
    appears_free_in x t1 ->
    appears_free_in x (tm_let y t1 t2).

(* utils *)
Tactic Notation "tm_cases" tactic(first) ident(c) :=
  first;
  [ 
      Case_aux c "tm_var"
    | Case_aux c "tm_abs"
    | Case_aux c "tm_app"
    | Case_aux c "tm_zero"
    | Case_aux c "tm_succ"
    | Case_aux c "tm_let"
  ].

Tactic Notation "eval1_cases" tactic(first) ident(c) :=
  first;
  [
      Case_aux c "E_App1"
    | Case_aux c "E_App2"
    | Case_aux c "E_AppAbs"
    | Case_aux c "E_Succ"
    | Case_aux c "E_Let"
    | Case_aux c "E_LetV"
  ].

Tactic Notation "typed_cases" tactic(first) ident(c) :=
  first;
  [
      Case_aux c "T_Var"
    | Case_aux c "T_Abs"
    | Case_aux c "T_App"
    | Case_aux c "T_Zero"
    | Case_aux c "T_Succ"
    | Case_aux c "T_Let"
  ].

Tactic Notation "afi_cases" tactic(first) ident(c) :=
  first;
  [
      Case_aux c "afi_var"
    | Case_aux c "afi_abs"
    | Case_aux c "afi_app1"
    | Case_aux c "afi_app2"
    | Case_aux c "afi_succ"
    | Case_aux c "afi_let1"
    | Case_aux c "afi_let2"
].
