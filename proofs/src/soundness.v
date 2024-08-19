Require Import commons.
Require Import definitions.
Require Import lemmas.

Theorem progress :
  forall t T,
  typed empty_ctx t T ->
  value t \/ exists t', t ==> t'.
Proof.
  intros t T Htyped.
  remember empty_ctx as ctx.
  typed_cases (induction Htyped) Case;
    try solve [
      eauto using value
    ].

    Case "T_Var".
    subst ctx.
    inversion H.

    Case "T_App".
    right.
    specialize Heqctx as IHt1.
    apply IHHtyped1 in IHt1.
    specialize Heqctx as IHt2.
    apply IHHtyped2 in IHt2.
    destruct IHt1 as [IHt1 | IHt1].

      SCase "t1 is a value".
      destruct IHt2 as [IHt2 | IHt2].

        SSCase "t2 is a value".
        apply (canonical_forms__arrow _ _ _ _ IHt1) in Htyped1.
        inversion Htyped1 as [x t1_form'].
        inversion t1_form' as [t12 t1_form].
        exists (subst x t2 t12).
        rewrite t1_form.
        apply (E_AppAbs _ _ _ _ IHt2).

        SSCase "t2 ==> t2'".
        inversion IHt2 as [t2'].
        exists (tm_app t1 t2').
        apply (E_App2 _ _ _ IHt1 H).

      SCase "t1 ==> t1'".
      inversion IHt1 as [t1'].
      exists (tm_app t1' t2).
      apply (E_App1 _ _ _ H).

    Case "T_Succ".
    specialize Heqctx as IHt1.
    apply IHHtyped in IHt1.
    destruct IHt1 as [IHt1 | IHt1].

      SCase "t1 is a value".
      left.
      apply (canonical_forms__nat _ _ IHt1) in Htyped.
      destruct Htyped as [Htyped | Htyped].

        SSCase "t1 = tm_zero".
        apply value_succ.
        left.
        apply Htyped.

        SSCase "t1 = tm_succ t1'".
        apply value_succ.
        right.
        apply Htyped.

      SCase "t1 ==> t1'".
      right.
      inversion IHt1 as [t1'].
      exists (tm_succ t1').
      apply (E_Succ _ _ H).

    Case "T_Let".
    right.
    specialize Heqctx as IHt1.
    apply IHHtyped1 in IHt1.
    destruct IHt1 as [IHt1 | IHt1].

      SCase "t1 is a value".
      exists (subst x t1 t2).
      apply (E_LetV _ _ _ IHt1).

      SCase "t1 ==> t1'".
      inversion IHt1 as [t1'].
      exists (tm_let x t1' t2).
      apply (E_Let _ _ _ _ H).
Qed.

Theorem preservation :
  forall t T t',
  typed empty_ctx t T ->
  t ==> t' ->
  typed empty_ctx t' T.
Proof with eauto using typed.
  intros t T t' Htyped Heval1.
  generalize dependent t'.
  remember (@empty_ctx ty) as ctx.
  typed_cases (induction Htyped) Case; intros;
    try solve
      [
        intros;
        inversion Heval1;
        eauto using typed
      ].
  
    Case "T_App".
    inversion Heval1 as [| | x T11' | | |]; subst...

      SCase "eval1 t by E_AppAbs".
      apply inversion__T_Abs in Htyped1.
      inversion Htyped1 as [R12 Hinv].
      inversion Hinv as [Hinv1 Hinv2]. clear Hinv.
      inversion Hinv2 as [T11eq]. subst.
      apply (preservation_of_types_under_substitution _ _ _ _ _ _ Hinv1 Htyped2).

    Case "T_Let".
    inversion Heval1 as [| | | | |]; subst...

      SCase "eval1 t1 by E_LetV".
      apply (preservation_of_types_under_substitution _ _ _ _ _ _ Htyped2 Htyped1).
Qed.

Theorem soundness :
  forall t T t',
  typed empty_ctx t T ->
  t ==>* t' ->
  ~ (exists t'', t' ==> t'') ->
  value t'.
Proof.
  intros t T t' Htyped Hevalmany Hcannoteval1.
  induction Hevalmany as [t | t u t'].

    Case "rsc_refl".
    specialize (progress _ _ Htyped) as prog.
    destruct prog.

      SCase "x is a value".
      assumption.

      SCase "x ==> x'".
      destruct Hcannoteval1.
      assumption.

    Case "rsc_trans".
    specialize (preservation _ _ _ Htyped H) as preserv.
    apply (IHHevalmany preserv Hcannoteval1).
Qed.
