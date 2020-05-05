Require Import VST.floyd.proofauto.
Require Import RamifyCoq.sample_mark.dijk_pq_arr_macros.
Require Import RamifyCoq.sample_mark.priorityqueue.
Require Import RamifyCoq.sample_mark.priq_utils.
Require Import RamifyCoq.sample_mark.dijk_pq_arr_spec.
Require Import VST.floyd.sublist.

(* We must use the CompSpecs and Vprog that were
   centrally defined in dijksta's environment. 
   This lets us be consistent and call PQ functions in Dijkstra. 
 *)

Local Definition CompSpecs := env_dijkstra_arr.CompSpecs.
Local Definition Vprog := env_dijkstra_arr.Vprog.

Lemma inf_eq2: Int.sub (Int.repr 2147483647)
                       (Int.divs (Int.repr 2147483647)
                                 (Int.repr SIZE)) = Int.repr inf.
Proof. compute. trivial. Qed.

Lemma body_push: semax_body Vprog Gprog f_push push_spec.
Proof. start_function. forward. entailer!. Qed.

Lemma body_pq_emp: semax_body Vprog Gprog f_pq_emp pq_emp_spec.
Proof.
  start_function.
  forward_for_simple_bound
    SIZE
    (EX i : Z,
     PROP (isEmpty_Prop (sublist 0 i priq_contents))
     LOCAL (temp _pq pq)
     SEP (data_at Tsh (tarray tint SIZE) (map Vint (map Int.repr priq_contents)) pq)).
  - unfold SIZE; rep_lia.
  - unfold SIZE; rep_lia.
  - entailer!. 
  - simpl.
    assert_PROP (Zlength priq_contents = SIZE). {
      entailer!. repeat rewrite Zlength_map in H3; auto.
    }
    forward; forward_if; forward; entailer!.
    + rewrite (isEmpty_in priq_contents (Znth i priq_contents)).
      trivial.
      apply Znth_In; lia.
      rewrite <- H1 in H0.
      pose proof (Forall_Znth _ _ i H0 H).
      rewrite Int.signed_repr in H3.
      apply (Z.lt_stepr _ _ _ H3). compute; trivial.
      simpl in H7. rep_lia.
    + rewrite (sublist_split 0 i (i+1)); try lia.
      unfold isEmpty_Prop.
      rewrite fold_right_app.
      rewrite sublist_one; try lia. simpl.
      destruct (Z_lt_dec (Znth i priq_contents) inf).
      2: unfold isEmpty_Prop in H2; trivial.
      exfalso.
      replace 8 with SIZE in H3 by (unfold SIZE; trivial).
      rewrite inf_eq2 in H3.
      do 2 rewrite Int.signed_repr in H3.
      rep_lia.
      1: compute; split; inversion 1.
      1,2: rewrite <- H1 in H0; apply (Forall_Znth _ _ i H0) in H; simpl in H; rep_lia.
  - forward. entailer!.
    rewrite sublist_same in H0; trivial.
    2: { symmetry; repeat rewrite Zlength_map in H2.
         unfold SIZE. simpl in H2. lia. }
    replace (Vint (Int.repr 1)) with Vone by now unfold Vone, Int.one.
    symmetry. apply isEmpty_prop_val; trivial.
Qed.

Lemma body_adjustWeight: semax_body Vprog Gprog f_adjustWeight adjustWeight_spec.
Proof. start_function. forward. entailer!. Qed.

Lemma body_popMin: semax_body Vprog Gprog f_popMin popMin_spec.
Proof.
  start_function.
  assert_PROP (Zlength priq_contents = SIZE). {
    entailer!. repeat rewrite Zlength_map in H2; auto.
  }
  assert (0 <= 0 < Zlength (map Int.repr priq_contents)) by
      (rewrite Zlength_map; rewrite H1; unfold SIZE; lia).
  assert (0 <= 0 < Zlength priq_contents) by
      (rewrite H1; unfold SIZE; lia).
  forward. forward.
  forward_for_simple_bound
    SIZE
    (EX i : Z,
     PROP ()
     LOCAL (temp _minWeight (Vint (Int.repr (fold_right Z.min (Znth 0 priq_contents) (sublist 0 i priq_contents))));
                        temp _minVertex (Vint (Int.repr (find priq_contents (fold_right Z.min (Znth 0 priq_contents) (sublist 0 i priq_contents)) 0)));
                        temp _pq pq)
                 SEP (data_at Tsh (tarray tint SIZE) (map Vint (map Int.repr priq_contents)) pq)).
  - unfold SIZE; rep_lia.
  - entailer!. simpl. rewrite find_index.
    trivial. lia. simpl. unfold not. lia.
  - forward.
    assert (0 <= i < Zlength priq_contents) by lia.
    assert (Int.min_signed <=
            fold_right Z.min (Znth 0 priq_contents) (sublist 0 i priq_contents) <= Int.max_signed).
    { apply Forall_fold_min. apply Forall_Znth. lia.
      rewrite Forall_forall. intros. rewrite In_Znth_iff in H6.
      destruct H6 as [? [? ?]]. rewrite <- H7.
      pose proof (Forall_Znth _ _ x0 H6 H).
      simpl in H8. rep_lia.
      rewrite Forall_forall. intros. rewrite In_Znth_iff in H6.
      destruct H6 as [? [? ?]]. rewrite <- H7.
      apply (Forall_sublist _ 0 i _) in H.
      apply (Forall_Znth _ _ _ H6) in H.
      simpl in H. rep_lia.
    }
    assert (Int.min_signed <= Znth i priq_contents <= Int.max_signed). {
      apply (Forall_Znth _ _ _ H5) in H; simpl in H; rep_lia. }
    forward_if.
    + forward. forward. entailer!.
      rewrite (sublist_split 0 i (i+1)) by lia.
      rewrite (sublist_one i (i+1) priq_contents) by lia.
      rewrite fold_min_another.
      rewrite Z.min_r; [|lia].
      split; trivial. f_equal.
      rewrite find_index; trivial.
      apply min_not_in_prev; trivial.
    + forward. entailer!.
      rewrite (sublist_split 0 i (i+1)) by lia.
      rewrite (sublist_one i (i+1) priq_contents) by lia.
      rewrite fold_min_another.
      rewrite Z.min_l; [|lia]. split; trivial.
  - forward.
    + entailer!. rewrite <- H1.
      apply find_range.
      rewrite sublist_same; [|lia..].
      apply min_in_list; [apply incl_refl | apply Znth_In; lia].
    + forward.
      Exists (find priq_contents (fold_right Z.min (hd 0 priq_contents) (sublist 0 SIZE priq_contents)) 0).
      rewrite sublist_same by lia. entailer!.
      destruct priq_contents; simpl; auto.
Qed.