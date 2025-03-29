Require Import main.
Require Import Lia.
Require Import Relation_Operators.

Example freash_variable_case1:
  let term := term_var 0 in
  let actual := freash_variable term in
  not (actual = 0).
Proof.
  compute.
  lia.
Qed.
Example freash_variable_case2:
  let term :=
    term_app
      (term_abs
        0
        (type_arrow
          (type_arrow type_nat type_nat)
          (type_arrow type_nat type_nat)
        )
        (term_var 0)
      )
      (term_abs
        1
        (type_arrow type_nat type_nat)
        (term_var 1)
      )
  in
  let actual := freash_variable term in
  not (actual = 0) /\
  not (actual = 1) /\
  not (actual = 1).
Proof.
  compute.
  lia.
Qed.

Example alpha_conversion_case1:
  let actual :=
    alpha_conversion
      0
      type_nat
      (term_app
        (term_abs 0 type_nat (term_var 0))
        (term_var 0)
      )
      1
  in
  let expected :=
    term_abs
      1
      type_nat
      (term_app
        (term_abs 0 type_nat (term_var 0))
        (term_var 1)
      )
  in
  actual = expected.
Proof.
  compute.
  auto.
Qed.

Example freash_eval_case1:
  let term :=
    term_app
      (term_abs
        0
        (type_arrow
          (type_arrow type_nat type_nat)
          (type_arrow type_nat type_nat)
        )
        (term_var 0)
      )
      (term_app
        (term_abs
          1
          (type_arrow
            (type_arrow type_nat type_nat)
            (type_arrow type_nat type_nat)
          )
          (term_var 1)
        )
        (term_abs
          2
          (type_arrow type_nat type_nat)
          (term_var 2)
        )
      )
  in
  let evaluated :=
    (term_abs
      2
      (type_arrow type_nat type_nat)
      (term_var 2)
    )
  in
  eval term evaluated.
Proof with eauto using clos_trans_n1, eval1, value.
  eapply tn1_trans...
  simpl...
Qed.
