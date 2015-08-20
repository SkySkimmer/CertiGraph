Require Import Coq.Sets.Ensembles.
Require Import Coq.Sets.Finite_sets.
Require Import RamifyCoq.Coqlib.
Require Import RamifyCoq.sample_mark.env_mark_bi.
Require Import RamifyCoq.graph.graph_model.
Require RamifyCoq.graph.marked_graph. Import RamifyCoq.graph.marked_graph.MarkGraph.
Require Import RamifyCoq.graph.path_lemmas.
Require Import RamifyCoq.graph.subgraph2.
Require Import RamifyCoq.graph.reachable_computable.
Require Import RamifyCoq.data_structure.general_spatial_graph.
Require Import RamifyCoq.data_structure.spatial_graph_bi.
Require Import RamifyCoq.data_structure.spatial_graph_mark_bi.
Require Import RamifyCoq.data_structure.spatial_graph_aligned_bi_VST.

Local Open Scope logic.

Notation graph sh x g := (@graph _ _ _ _ _ _ (@SGP pSGG_VST (sSGG_VST sh)) _ x g).
Existing Instances MGS biGraph maGraph finGraph RGF.

Definition mark_spec :=
 DECLARE _mark
  WITH sh: share, g: Graph, x: pointer_val
  PRE [ _x OF (tptr (Tstruct _Node noattr))]
          PROP  (writable_share sh; weak_valid g x)
          LOCAL (temp _x (pointer_val_val x))
          SEP   (`(graph sh x g))
  POST [ Tvoid ]
        PROP ()
        LOCAL()
        SEP (`(EX g': Graph, !! mark g x g' && graph sh x g')).

Definition main_spec :=
 DECLARE _main
  WITH u : unit
  PRE  [] main_pre prog u
  POST [ tint ] main_post prog u.

Definition Vprog : varspecs := (_hd, tptr (Tstruct _Node noattr))::(_n, (Tstruct _Node noattr))::nil.

Definition Gprog : funspecs := mark_spec :: main_spec::nil.

Ltac revert_exp_left_tac x :=
  match goal with
  | |- ?P |-- _ =>
      let P0 := fresh "P" in
      set (P0 := P);
      pattern x in P0;
      subst P0;
      apply (revert_exists_left x); try clear x
  end.

Lemma body_mark: semax_body Vprog Gprog f_mark mark_spec.
Proof.
  start_function.
  remember (vgamma g x) as dlr eqn:?H.
  destruct dlr as [[d l] r].
  rename H0 into H_GAMMA_g; symmetry in H_GAMMA_g.
  rename H into H_weak_valid.

  forward_if_tac  (* if (x == 0) *)
    (PROP  (pointer_val_val x <> nullval)
     LOCAL (temp _x (pointer_val_val x))
     SEP   (`(graph sh x g))).
  admit. (* type checking for pointer comparable. *)
  Focus 1. { (* if-then branch *)
    destruct_pointer_val x.
    forward. (* return *)
    pose proof mark_invalid_refl g NullPointer.
    spec H0;
    [pose proof valid_not_null g NullPointer; rewrite is_null_def in H1; intro; apply H1; auto; congruence |].
    apply (exp_right g); entailer!.
  } Unfocus.
  Focus 1. { (* if-else branch *)
    forward. (* skip; *)
    entailer!.
  } Unfocus.
  normalize.
  assert (vvalid g x) as gx_vvalid.
  Focus 1. {
    destruct H_weak_valid; [| auto].
    rewrite is_null_def in H0; subst x.
    exfalso.
    apply H. auto.
  } Unfocus.
  destruct_pointer_val x. clear H0 H_weak_valid.
  assert (gl_weak_valid: weak_valid g l) by (eapply gamma_left_weak_valid; eauto).
  assert (gr_weak_valid: weak_valid g r) by (eapply gamma_right_weak_valid; eauto).

  localize
   (PROP  ()
    LOCAL (temp _x (pointer_val_val x))
    SEP   (`(data_at sh node_type (Vint (Int.repr (if d then 1 else 0)), (pointer_val_val l, pointer_val_val r))
              (pointer_val_val x)))).
  (* localize *)

  apply -> ram_seq_assoc. 
  eapply semax_ram_seq;
    [ repeat apply eexists_add_stats_cons; constructor
    | new_load_tac 
    | abbreviate_semax_ram].
  apply ram_extract_exists_pre.
  intro root_mark_old; autorewrite with subst; clear root_mark_old.
  (* root_mark = x -> m; *)

  unlocalize (PROP ()  LOCAL  (temp _root_mark (Vint (Int.repr (if d then 1 else 0))); temp _x (pointer_val_val x))  SEP  (`(graph sh x g))).
  Grab Existential Variables.
  Focus 6. { solve_split_by_closed. } Unfocus.
  Focus 2. { entailer!. } Unfocus.
  Focus 3. { entailer!. } Unfocus.
  Focus 3. { repeat constructor; auto with closed. } Unfocus.
  Focus 2. {
    entailer!. rewrite (update_self g x (d, l, r)) at 2 by auto.
    pose proof (@graph_ramify_aux0 _ _ _ _ _ _ _ (SGA_VST sh) g _ x (d, l, r) (d, l, r)).
    simpl in H1; auto.
  } Unfocus.
  (* unlocalize *)

  unfold semax_ram.
  forward_if_tac  (* if (root_mark == 1) *)
    (PROP   (d = false)
      LOCAL (temp _x (pointer_val_val x))
      SEP   (`(graph sh x g))).
  Focus 1. { (* if-then branch *)
    forward. (* return *)
    apply (exp_right g).
    assert (mark g (ValidPointer b i) g).
    Focus 1. {
      apply mark_marked_root_refl.
      simpl.
      inversion H_GAMMA_g.
      destruct d; [auto | inversion H0].
    } Unfocus.
    normalize.
  } Unfocus.
  Focus 1. { (* if-else branch *)
    forward. (* skip; *)
    entailer!.
    destruct d; congruence.
  } Unfocus.

  normalize.
  subst d.
  localize
   (PROP  ()
    LOCAL (temp _x (pointer_val_val x))
    SEP   (`(data_at sh node_type (Vint (Int.repr 0), (pointer_val_val l, pointer_val_val r))
              (pointer_val_val x)))).
  (* localize *)

  apply -> ram_seq_assoc. 
  eapply semax_ram_seq;
    [ repeat apply eexists_add_stats_cons; constructor
    | new_load_tac 
    | abbreviate_semax_ram].
  apply ram_extract_exists_pre.
  intro l_old; autorewrite with subst; clear l_old.
  (* l = x -> l; *)

  apply -> ram_seq_assoc.
  eapply semax_ram_seq;
    [ repeat apply eexists_add_stats_cons; constructor
    | new_load_tac 
    | abbreviate_semax_ram].
  apply ram_extract_exists_pre.
  intro r_old; autorewrite with subst; clear r_old.
  (* r = x -> r; *)

  apply -> ram_seq_assoc.
  eapply semax_ram_seq;
    [ repeat apply eexists_add_stats_cons; constructor
    | new_store_tac
    | abbreviate_semax_ram].
  cbv beta zeta iota delta [replace_nth].
  change (@field_at CompSpecs CS_legal sh node_type []
           (Vint (Int.repr 1), (pointer_val_val l, pointer_val_val r))) with
         (@data_at CompSpecs CS_legal sh node_type
           (Vint (Int.repr 1), (pointer_val_val l, pointer_val_val r))).
  (* x -> d = 1; *)

  unlocalize
   (PROP  ()
    LOCAL (temp _r (pointer_val_val r);
           temp _l (pointer_val_val l);
           temp _x (pointer_val_val x))
    SEP (`(graph sh x (Graph_gen g x true)))).
  Grab Existential Variables.
  Focus 6. { solve_split_by_closed. } Unfocus.
  Focus 2. { entailer!. } Unfocus.
  Focus 3. { entailer!. } Unfocus.
  Focus 3. { repeat constructor; auto with closed. } Unfocus.
  Focus 2. {
    entailer!.
    rewrite Graph_gen_spatial_spec by eauto.
    pose proof (@graph_ramify_aux0 _ _ _ _ _ _ _ (SGA_VST sh) g _ x (false, l, r) (true, l, r)).
    simpl in H1; auto.
  } Unfocus.
  (* unlocalize *)

  unfold semax_ram. (* should not need this *)

  pose proof Graph_gen_true_mark1 g x _ _ H_GAMMA_g gx_vvalid.
  assert (H_GAMMA_g1: vgamma (Graph_gen g x true) x = (true, l, r)) by
   (rewrite (proj1 (proj2 (Graph_gen_spatial_spec g x _ true _ _ H_GAMMA_g))) by assumption;
    apply spacialgraph_gen_vgamma).
  forget (Graph_gen g x true) as g1.  
  assert (g1x_valid: vvalid g1 x) by (apply (proj1 (proj1 H0)); auto).
  assert (g1l_weak_valid: weak_valid g1 l) by (apply (weak_valid_si g g1 _ (proj1 H0)); auto).
  assert (g1r_weak_valid: weak_valid g1 r) by (apply (weak_valid_si g g1 _ (proj1 H0)); auto).

  localize
   (PROP  ()
    LOCAL (temp _l (pointer_val_val l))
    SEP   (`(graph sh l g1))).
  (* localize *)
  
  rewrite <- ram_seq_assoc.
  eapply semax_ram_seq;
  [ repeat apply eexists_add_stats_cons; constructor
  | forward_call' (sh, g1, l); apply derives_refl
  | abbreviate_semax_ram].

  unlocalize
   (PROP  ()
    LOCAL (temp _r (pointer_val_val r);
           temp _l (pointer_val_val l);
           temp _x (pointer_val_val x))
    SEP (`((EX g2: Graph, !! mark g1 l g2 && graph sh x g2)))).
  Grab Existential Variables.
  Focus 6. { solve_split_by_closed. } Unfocus.
  Focus 2. { entailer!. } Unfocus.
  Focus 3. { entailer!. } Unfocus.
  Focus 3. { repeat constructor; auto with closed. } Unfocus.
  Focus 2. {
    entailer.
    rewrite !exp_emp.
    eapply (@graph_ramify_aux1_left _ (sSGG_VST sh) g1); eauto.
  } Unfocus.
  (* unlocalize *)

  unfold semax_ram. (* should not need this *)
  normalize; intros g2; normalize.
  assert (g2x_valid: vvalid g2 x) by (apply (proj1 (proj1 H2)); auto).
  assert (g2r_weak_valid: weak_valid g2 r) by (apply (weak_valid_si g1 g2 _ (proj1 H2)); auto).

  localize
   (PROP  ()
    LOCAL (temp _r (pointer_val_val r))
    SEP   (`(graph sh r g2))).
  (* localize *)
  
  eapply semax_ram_seq;
  [ repeat apply eexists_add_stats_cons; constructor
  | forward_call' (sh, g2, r); apply derives_refl
  | abbreviate_semax_ram].
  (* mark(r); *)

  unlocalize
   (PROP  ()
    LOCAL (temp _r (pointer_val_val r);
           temp _l (pointer_val_val l);
           temp _x (pointer_val_val x))
    SEP (`(EX g3: Graph, !!mark g2 r g3 && graph sh x g3))).
  Grab Existential Variables.
  Focus 6. { solve_split_by_closed. } Unfocus.
  Focus 2. { entailer!. } Unfocus.
  Focus 3. { entailer!. } Unfocus.
  Focus 3. { repeat constructor; auto with closed. } Unfocus.
  Focus 2. {
    entailer!.
    rewrite !exp_emp.
    eapply (@graph_ramify_aux1_right _ (sSGG_VST sh) g2); eauto.
    eapply gamme_true_mark; eauto.
    apply weak_valid_vvalid_dec; auto.
  } Unfocus.
  (* Unlocalize *)

  unfold semax_ram.
  forward. (* ( return; ) *)
  apply (exp_right g3); entailer!.
  apply (mark1_mark_left_mark_right g g1 g2 g3 (ValidPointer b i) l r); auto.
  eapply gamme_true_mark; eauto.
  apply weak_valid_vvalid_dec; auto.
Time Qed. (* Takes 30 minuts. *)