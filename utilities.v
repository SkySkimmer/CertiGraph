Require Import List.
Require Import Omega.

Definition Sublist {A} (L1 L2 : list A) : Prop := forall a, In a L1 -> In a L2.

Lemma Sublist_refl: forall A (L : list A), Sublist L L. Proof. repeat intro; auto. Qed.

Lemma Sublist_trans: forall A (L1 L2 L3 : list A), Sublist L1 L2 -> Sublist L2 L3 -> Sublist L1 L3.
Proof. repeat intro; apply H0; apply H; trivial. Qed.

Add Parametric Relation {A} : (list A) Sublist
    reflexivity proved by (@Sublist_refl A)
    transitivity proved by (@Sublist_trans A) as Sublist_rel.

Lemma Sublist_nil: forall A (L : list A), Sublist nil L. Proof. repeat intro; inversion H. Qed.

Lemma Sublist_cons: forall A (a : A) L, Sublist L (a :: L). Proof. repeat intro; simpl; auto. Qed.

Lemma Sublist_app: forall A (L1 L2 L3 L4: list A), Sublist L1 L2 -> Sublist L3 L4 -> Sublist (L1 ++ L3) (L2 ++ L4).
Proof. repeat intro; apply in_app_or in H1; apply in_or_app; destruct H1; [left; apply H | right; apply H0]; trivial. Qed.

Lemma In_tail: forall A (a : A) L, In a (tl L) -> In a L.
Proof. induction L; simpl; auto. Qed.

Definition eq_as_set {A} (L1 L2 : list A) : Prop := Sublist L1 L2 /\ Sublist L2 L1.

Notation "a '~=' b" := (eq_as_set a b) (at level 1).

Lemma eq_as_set_refl: forall A (L : list A), L ~= L. Proof. intros; split; apply Sublist_refl. Qed.

Lemma eq_as_set_sym: forall A (L1 L2 : list A), L1 ~= L2 -> L2 ~= L1. Proof. intros; hnf in *; firstorder. Qed.

Lemma eq_as_set_trans: forall A (L1 L2 L3 : list A), L1 ~= L2 -> L2 ~= L3 -> L1 ~= L3.
Proof. intros; hnf in *; intuition; transitivity L2; trivial. Qed.

Add Parametric Relation {A} : (list A) eq_as_set
    reflexivity proved by (eq_as_set_refl A)
    symmetry proved by (eq_as_set_sym A)
    transitivity proved by (eq_as_set_trans A) as eq_as_set_rel.

Lemma eq_as_set_app: forall A (L1 L2 L3 L4: list A), L1 ~= L2 -> L3 ~= L4 -> (L1 ++ L3) ~= (L2 ++ L4).
Proof. intros; hnf in *; intuition; apply Sublist_app; trivial. Qed.

Lemma Forall_tl: forall {A : Type} (P : A -> Prop) (x : A) (l : list A), Forall P (x :: l) -> Forall P l.
Proof. intros; rewrite Forall_forall in *; intros. apply H, in_cons; auto. Qed.

Lemma Forall_app: forall {A : Type} (P : A -> Prop) (l1 l2 : list A), Forall P l1 -> Forall P l2 -> Forall P (l1 ++ l2).
Proof.
  induction l1; intros. rewrite app_nil_l; auto. generalize (Forall_inv H); intros.
  rewrite <- app_comm_cons. apply Forall_cons; auto. apply IHl1; auto. apply Forall_tl with a; auto.
Qed.

Lemma Forall_sublist: forall {A : Type} (P : A -> Prop) (l1 l2 : list A), Sublist l1 l2 -> Forall P l2 -> Forall P l1.
Proof. intros; hnf in *. rewrite Forall_forall in *; intro y; intros. apply H0, H; auto. Qed.

Lemma sublist_reverse: forall {A : Type} (eq_dec : forall x y : A, {x = y} + {x <> y}) (l1 l2 : list A),
                         NoDup l1 -> length l1 = length l2 -> Sublist l1 l2 -> Sublist l2 l1.
Proof.
  induction l1; intros. destruct l2; auto. simpl in H0; inversion H0.
  generalize (H1 a); intros. assert (In a (a :: l1)) as S by apply in_eq; specialize (H2 S); clear S.
  generalize (in_split a l2 H2); intro S; clear H2; destruct S as [l3 [l4 ?]].
  intro y; intros. destruct (eq_dec y a). subst. apply in_eq. apply in_cons. subst. apply in_app_or in H3.
  assert (In y l3 \/ In y l4). destruct H3; [left; auto | right]. apply in_inv in H2. destruct H2; [exfalso | ]; auto.
  clear H3. apply in_or_app in H2. unfold Sublist in IHl1 at 2. apply IHl1 with (l3 ++ l4).
  rewrite <- app_nil_l in H. apply NoDup_remove_1 in H. rewrite app_nil_l in H. apply H.
  rewrite app_length in *. simpl in H0. omega. intro z; intros. clear H2 n y H0. specialize (H1 z).
  generalize (in_cons a z l1 H3); intro S; specialize (H1 S); clear S. apply in_app_or in H1. apply in_or_app.
  destruct H1. left; auto. apply in_inv in H0. right; destruct H0. subst. rewrite <- app_nil_l in H.
  apply NoDup_remove_2 in H. rewrite app_nil_l in H. exfalso; intuition. auto. auto.
Qed.