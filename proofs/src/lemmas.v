Require Import commons.
Require Import definitions.

(* 逆転 *)
Lemma inversion__T_Var :
  forall ctx n R,
  typed ctx (tm_var n) R ->
  ctx n = Some R.
Proof.
  intros.
  inversion H.
  assumption.
Qed.

Lemma inversion__T_Abs :
  forall ctx n T1 t2 R,
  typed ctx (tm_abs n T1 t2) R ->
  (
    exists R2,
    typed (bind_ctx ctx n T1) t2 R2 /\ R = ty_arrow T1 R2
  ).
Proof.
  intros.
  inversion H.
  exists T2.
  auto.
Qed.

Lemma inversion__T_App :
  forall ctx t1 t2 R,
  typed ctx (tm_app t1 t2) R ->
  (
    exists T11,
    typed ctx t1 (ty_arrow T11 R) /\ typed ctx t2 T11
  ).
Proof.
  intros.
  inversion H.
  exists T11.
  auto.
Qed.

Lemma inversion__T_Zero :
  forall ctx R,
  typed ctx tm_zero R ->
  R = ty_nat.
Proof.
  intros.
  inversion H.
  reflexivity.
Qed.

Lemma inversion__T_Succ :
  forall ctx t1 R,
  typed ctx (tm_succ t1) R ->
  R = ty_nat /\ typed ctx t1 ty_nat.
Proof.
  intros.
  inversion H.
  auto.
Qed.

Lemma inversion__T_Let :
  forall ctx n t1 t2 R,
  typed ctx (tm_let n t1 t2) R ->
  (
    exists T1,
    typed ctx t1 T1 /\ typed (bind_ctx ctx n T1) t2 R
  ).
Proof.
  intros.
  inversion H.
  subst.
  exists T1.
  auto.
Qed.

(* 標準形 *)
Lemma canonical_forms__arrow :
  forall ctx v T1 T2,
  value v ->
  typed ctx v (ty_arrow T1 T2) ->
  (
    exists n t2,
    v = tm_abs n T1 t2
  ).
Proof.
  intros ctx v T1 T2 Hvalue Htyped.
  destruct Hvalue.

    Case "v: value_abs".
    exists x.
    exists t.
    apply inversion__T_Abs in Htyped.
    inversion Htyped.
    inversion H.
    inversion H1.
    reflexivity.

    Case "v: value_zero".
    apply inversion__T_Zero in Htyped.
    inversion Htyped.

    Case "v: value_succ".
    apply inversion__T_Succ in Htyped.
    inversion Htyped.
    inversion H0.
Qed.

Lemma canonical_forms__nat :
  forall ctx v,
  value v ->
  typed ctx v ty_nat ->
  v = tm_zero \/ exists t, v = tm_succ t.
Proof.
  intros ctx v Hvalue Htyped.
  destruct Hvalue.

    Case "v: value_abs".
    apply inversion__T_Abs in Htyped.
    inversion Htyped.
    inversion H.
    inversion H1.

    Case "v: value_zero".
    left.
    reflexivity.

    Case "v: value_succ".
    right.
    exists t.
    reflexivity.
Qed.

(* 並び替え *)
Lemma ctx_permutation :
  forall ctx1 ctx2 t T,
  (forall x, ctx1 x = ctx2 x) ->
  typed ctx1 t T ->
  typed ctx2 t T.
Proof with eauto using typed.
  intros ctx1 ctx2 t T Heq Htyped.
  generalize dependent ctx2.
  typed_cases (induction Htyped as [ctx1 | ctx1 x' T1 t2 | | | | ctx1 t1 T1 t2 T2 x']) Case; intros;
    try solve [
      eauto using typed
    ].

    Case "T_Var".
    apply T_Var.
    rewrite (Heq x) in H.
    assumption.

    Case "T_Abs".
    apply T_Abs.
    apply IHHtyped.
    intros.
    unfold bind_ctx.
    destruct (PeanoNat.Nat.eq_dec x' x) as [x'x | x'x].

      SCase "x' = x".
      subst.
      rewrite (PeanoNat.Nat.eqb_refl x).
      reflexivity.

      SCase "x' <> x".
      apply (PeanoNat.Nat.eqb_neq x' x) in x'x.
      rewrite x'x.
      apply (Heq x).

    Case "T_Let".
    apply (T_Let _ t1 T1 t2 T2 _)...
    apply IHHtyped2.
    intros.
    unfold bind_ctx.
    destruct (PeanoNat.Nat.eq_dec x' x) as [x'x | x'x].

      SCase "x' = x".
      subst.
      rewrite (PeanoNat.Nat.eqb_refl x).
      reflexivity.

      SCase "x' <> x".
      apply (PeanoNat.Nat.eqb_neq x' x) in x'x.
      rewrite x'x.
      apply (Heq x).
Qed.

Lemma ctx_swapping :
  forall ctx x X y Y t T,
  typed (bind_ctx (bind_ctx ctx x X) y Y) t T ->
  ~ (x = y) ->
  typed (bind_ctx (bind_ctx ctx y Y) x X) t T.
Proof.
  intros ctx x X y Y t T Htyped Hneq.
  apply (ctx_permutation (bind_ctx (bind_ctx ctx x X) y Y) (bind_ctx (bind_ctx ctx y Y) x X)).

  intros x'.
  unfold bind_ctx.
  destruct (PeanoNat.Nat.eq_dec x' x) as [x'x | x'x].

    Case "x' = x".
    destruct (PeanoNat.Nat.eq_dec x' y) as [x'y | x'y].

      SCase "x' = y".
      subst.
      destruct Hneq.
      reflexivity.

      SCase "x' <> y".
      subst.
      rewrite (PeanoNat.Nat.eqb_refl x).
      apply (PeanoNat.Nat.eqb_neq x y) in Hneq.
      rewrite (PeanoNat.Nat.eqb_sym x y) in Hneq.
      rewrite Hneq.
      reflexivity.

    Case "x' <> x".
    apply (PeanoNat.Nat.eqb_neq x' x) in x'x.
    rewrite (PeanoNat.Nat.eqb_sym x' x) in x'x.
    rewrite x'x.
    reflexivity.
  
  assumption.
Qed.

Lemma ctx_invariance :
  forall ctx1 t T ctx2,
  typed ctx1 t T ->
  (forall x, appears_free_in x t -> ctx1 x = ctx2 x) ->
  typed ctx2 t T.
Proof with eauto using appears_free_in.
  intros ctx1 t T ctx2 Htyped Hafi.
  generalize dependent ctx2.
  typed_cases (induction Htyped as [ctx1 x' | ctx1 x' | ctx1 | | | ctx1 t1 T1 t2 T2 x']) Case; intros;
    try solve [
      eauto using typed, appears_free_in
    ].

    Case "T_Var".
    apply T_Var.
    specialize (Hafi x' (afi_var x')) as ctx1_eq_ctx2_for_x'.
    rewrite ctx1_eq_ctx2_for_x' in H.
    assumption.

    Case "T_Abs".
    apply T_Abs.
    apply IHHtyped.
    intros.
    destruct (PeanoNat.Nat.eq_dec x x') as [xx' | xx'].

      SCase "x' = x".
      subst.
      unfold bind_ctx.
      rewrite (PeanoNat.Nat.eqb_refl x').
      reflexivity.

      SCase "x' <> x".
      specialize xx' as x_noteq_x'.
      unfold bind_ctx.
      apply (PeanoNat.Nat.eqb_neq x x') in xx'.
      rewrite (PeanoNat.Nat.eqb_sym x x') in xx'.
      rewrite xx'.
      apply Hafi.
      apply afi_abs...

    Case "T_App".
    apply (T_App _ _ T11 _ _)...

    Case "T_Let".
    apply (T_Let _ _ T1 _ _ _)...
    apply IHHtyped2.
    intros x Hafit2.
    destruct (PeanoNat.Nat.eq_dec x x') as [xx' | xx'].

      SCase "x = x'".
      subst.
      unfold bind_ctx.
      rewrite (PeanoNat.Nat.eqb_refl x').
      reflexivity.

      SCase "x <> x'".
      specialize xx' as x_noteq_x'.
      unfold bind_ctx.
      apply (PeanoNat.Nat.eqb_neq x x') in xx'.
      rewrite (PeanoNat.Nat.eqb_sym x x') in xx'.
      rewrite xx'...
Qed.

Lemma free_in_ctx :
  forall x ctx t T,
  appears_free_in x t ->
  typed ctx t T ->
  ∃ T', ctx x = Some T'.
Proof.
  intros x ctx t T Hafi Htyped.
  generalize dependent ctx.
  generalize dependent T.
  afi_cases (induction Hafi) Case; intros;
    try solve [
      inversion Htyped;
      eauto
    ].

    Case "afi_abs".
    inversion Htyped. subst.
    apply IHHafi in H5.
    apply (PeanoNat.Nat.eqb_neq x y) in H.
    rewrite (PeanoNat.Nat.eqb_sym x y) in H.
    unfold bind_ctx in H5.
    rewrite H in H5.
    assumption.

    Case "afi_let1".
    inversion Htyped. subst.
    apply IHHafi in H6.
    apply (PeanoNat.Nat.eqb_neq x y) in H.
    rewrite (PeanoNat.Nat.eqb_sym x y) in H.
    unfold bind_ctx in H6.
    rewrite H in H6.
    assumption.
Qed.

Lemma ctx_bind_fresh :
  forall {T : Type} ctx x' X' x,
  @bind_ctx T ctx x' X' x = None ->
  ctx x = None.
Proof.
  intros.
  destruct (PeanoNat.Nat.eq_dec x x') as [xx' | xx'].

    Case "x = x'".
    subst.
    unfold bind_ctx in H.
    rewrite (PeanoNat.Nat.eqb_refl x') in H.
    inversion H.

    Case "x <> x'".
    unfold bind_ctx in H.
    apply (PeanoNat.Nat.eqb_neq x x') in xx'.
    rewrite (PeanoNat.Nat.eqb_sym x x') in xx'.
    rewrite xx' in H.
    assumption.
Qed.

Lemma ctx_fresh_notin :
  forall {T : Type} ctx x' X' x,
  @bind_ctx T ctx x' X' x = None ->
  ~ (x' = x).
Proof.
  intros.
  destruct (PeanoNat.Nat.eq_dec x x') as [xx' | xx'].

    Case "x = x'".
    subst.
    unfold bind_ctx in H.
    rewrite (PeanoNat.Nat.eqb_refl x') in H.
    inversion H.

    Case "x <> x'".
    rewrite PeanoNat.Nat.eq_sym_iff in xx'.
    assumption.
Qed.

Lemma ctx_ignore_same_variable :
  forall ctx x X1 X2 t T,
  typed (bind_ctx (bind_ctx ctx x X1) x X2) t T ->
  typed (bind_ctx ctx x X2) t T.
Proof.
  intros ctx x X1 X2 t T Htyped.
  apply (ctx_invariance (bind_ctx (bind_ctx ctx x X1) x X2) _ _ (bind_ctx ctx x X2)).
  assumption.
  intros x' Hafi.
  destruct (PeanoNat.Nat.eq_dec x x') as [xx' | xx'].

    Case "x = x'".
    subst.
    unfold bind_ctx.
    rewrite (PeanoNat.Nat.eqb_refl x').
    reflexivity.

    Case "x <> x'".
    apply (PeanoNat.Nat.eqb_neq x x') in xx'.
    unfold bind_ctx.
    rewrite xx'.
    reflexivity.
Qed.

(* 代入 *)
Lemma preservation_of_types_under_substitution :
  forall ctx x S t T s,
  typed (bind_ctx ctx x S) t T ->
  typed empty_ctx s S ->
  typed ctx (subst x s t) T.
Proof with eauto using typed.
  intros ctx x S t T s Htypedt Htypeds.
  generalize dependent ctx.
  generalize dependent T.
  tm_cases (induction t as [x' | x' T1 t2 | | | | x']) Case; intros;
    try solve [
      inversion Htypedt;
      eauto using typed
    ].

    Case "tm_var".
    simpl.
    destruct (PeanoNat.Nat.eq_dec x x') as [xx' | xx'].

      SCase "x = x'".
      subst.
      rewrite (PeanoNat.Nat.eqb_refl x').
      inversion Htypedt. subst.
      unfold bind_ctx in H1.
      rewrite (PeanoNat.Nat.eqb_refl x') in H1.
      inversion H1. subst. clear H1.
      apply (ctx_invariance empty_ctx _ _ ctx).
      assumption.
      intros x afi_xs.
      specialize (free_in_ctx _ _ _ _ afi_xs Htypeds) as exists_T'.
      inversion exists_T'.
      inversion H.

      SCase "x <> x'".
      rewrite <- (PeanoNat.Nat.eqb_neq x x') in xx'.
      rewrite xx'.
      inversion Htypedt. subst.
      unfold bind_ctx in H1.
      rewrite xx' in H1.
      apply T_Var.
      assumption.

    Case "tm_abs".
    simpl.
    inversion Htypedt. subst.
    destruct (PeanoNat.Nat.eq_dec x x') as [xx' | xx'].

      SCase "x = x'".
      subst.
      rewrite (PeanoNat.Nat.eqb_refl x').
      apply T_Abs.
      apply (ctx_ignore_same_variable _ _ S)...

      SCase "x <> x'".
      specialize xx' as x_neq_x'.
      rewrite <- (PeanoNat.Nat.eqb_neq x x') in xx'.
      rewrite xx'.
      apply T_Abs.
      apply IHt2.
      apply ctx_swapping...

    Case "tm_let".
    simpl.
    inversion Htypedt. subst.
    destruct (PeanoNat.Nat.eq_dec x x') as [xx' | xx'].

      SCase "x = x'".
      subst.
      rewrite (PeanoNat.Nat.eqb_refl x').
      apply (T_Let _ _ T1)...
      apply (ctx_ignore_same_variable _ _ S)...

      SCase "x <> x'".
      specialize xx' as x_neq_x'.
      rewrite <- (PeanoNat.Nat.eqb_neq x x') in xx'.
      rewrite xx'.
      apply (T_Let _ _ T1)...
      apply IHt2.
      apply ctx_swapping...
Qed.
