Require Import msl.msl_classical.

Ltac equate_age a1 a2 :=
  let Heq := fresh "Heq" in
  let Heq1 := fresh "Heq1" in
  let Heq2 := fresh "Heq2" in
  match goal with
    | [H1: age ?X a1, H2: age ?X a2 |- _] =>
      assert (Heq1: age1 X = Some a1) by auto; assert (Heq2: age1 X = Some a2) by auto;
      rewrite Heq2 in Heq1; injection Heq1; intro Heq; rewrite Heq in *; clear Heq1 Heq2 H2 Heq
  end.

Ltac try_join h1 h2 h1h2 :=
  let helper m1 m2 m1m2 :=
      match goal with
        | [H1: join _ m1 ?X, H2: join ?X m2 _ |- _] => destruct (join_assoc H1 H2) as [m1m2 [? ?]]
        | [H1: join m1 _ ?X, H2: join ?X m2 _ |- _] => destruct (join_assoc (join_comm H1) H2) as [m1m2 [? ?]]
        | [H1: join _ m1 ?X, H2: join m2 ?X _ |- _] => destruct (join_assoc H1 (join_comm H2)) as [m1m2 [? ?]]
        | [H1: join m1 _ ?X, H2: join m2 ?X _ |- _] => destruct (join_assoc (join_comm H1) (join_comm H2)) as [m1m2 [? ?]]
      end
  in helper h1 h2 h1h2 || helper h2 h1 h1h2.

Ltac try_join_through X h1 h2 h1h2 :=
  let helper m1 m2 m1m2 :=
      match goal with
        | [H1: join _ m1 X, H2: join X m2 _ |- _] => destruct (join_assoc H1 H2) as [m1m2 [? ?]]
        | [H1: join m1 _ X, H2: join X m2 _ |- _] => destruct (join_assoc (join_comm H1) H2) as [m1m2 [? ?]]
        | [H1: join _ m1 X, H2: join m2 X _ |- _] => destruct (join_assoc H1 (join_comm H2)) as [m1m2 [? ?]]
        | [H1: join m1 _ X, H2: join m2 X _ |- _] => destruct (join_assoc (join_comm H1) (join_comm H2)) as [m1m2 [? ?]]
      end
  in helper h1 h2 h1h2 || helper h2 h1 h1h2.

Ltac equate_join x1 x2 :=
  let Heq := fresh "Heq" in
  match goal with
    |[H1: join ?a ?b x1, H2: join ?b ?a x2 |- _] => apply join_comm in H2
    | _ => idtac
  end;
  match goal with
    |[H1: join ?a ?b x1, H2: join ?a ?b x2 |- _] =>
     generalize (join_eq H2 H1); intro Heq;
     rewrite Heq in *; clear H2 Heq x2
  end.

Ltac assertSub a c Hsub :=
  match goal with
    | [_: join a ?b c |- _] => assert (Hsub: join_sub a c) by (exists b; auto)
    | [H: join ?b a c |- _] => assert (Hsub: join_sub a c) by (exists b; apply join_comm; auto)
  end.

Ltac equate_precise x1 x2 :=
  let Sub1 := fresh "Sub1" in
  let Sub2 := fresh "Sub2" in
  let Heq := fresh "Heq" in
  match goal with
    | [_ : join x1 _ ?c, _: join x2 _ ?c |- _] => assertSub x1 c Sub1; assertSub x2 c Sub2
    | [_ : join _ x1 ?c, _: join x2 _ ?c |- _] => assertSub x1 c Sub1; assertSub x2 c Sub2
    | [_ : join x1 _ ?c, _: join _ x2 ?c |- _] => assertSub x1 c Sub1; assertSub x2 c Sub2
    | [_ : join _ x1 ?c, _: join _ x2 ?c |- _] => assertSub x1 c Sub1; assertSub x2 c Sub2
  end;
  match goal with
    | [H1: precise _, H2: ?P x1, H3: ?P x2, H4: join_sub x1 ?w, H5: join_sub x2 ?w |- _] =>
      generalize (H1 w x2 x1 H3 H2 H5 H4); intro Heq;
      rewrite Heq in *; clear H3 H4 H5 Heq x2
  end.

Ltac equate_canc x1 x2 :=
  let Heq := fresh "Heq" in
  let helper M1 M2 M3 := generalize (join_canc M2 M1); intro Heq; rewrite Heq in *; clear M3 Heq x2 in
    match goal with
      | [H1: join x1 ?b ?c, H2: join x2 ?b ?c |- _] => helper H1 H2 H2
      | [H1: join ?b x1 ?c, H2: join x2 ?b ?c |- _] => helper (join_comm H1) H2 H2
      | [H1: join x1 ?b ?c, H2: join ?b x2 ?c |- _] => helper H1 (join_comm H2) H2
      | [H1: join ?b x1 ?c, H2: join ?b x2 ?c |- _] => helper (join_comm H1) (join_comm H2) H2
    end.
