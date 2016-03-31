Require Import VST.msl.seplog.
Require Import VST.msl.log_normalize.
Require Import RamifyCoq.lib.Coqlib.
Require Import RamifyCoq.lib.Ensembles_ext.
Require Import RamifyCoq.lib.EquivDec_ext.
Require Import RamifyCoq.lib.List_ext.
Require Import RamifyCoq.lib.relation_list.
Require Import RamifyCoq.msl_ext.abs_addr.
Require Import RamifyCoq.msl_ext.seplog.
Require Import RamifyCoq.msl_ext.log_normalize.
Require Import RamifyCoq.msl_ext.iter_sepcon.
Require Import RamifyCoq.msl_ext.ramification_lemmas.
Require Import RamifyCoq.graph.graph_model.
Require Import RamifyCoq.graph.path_lemmas.
Require Import RamifyCoq.graph.reachable_computable.
Require Import RamifyCoq.graph.reachable_ind.
Require Import RamifyCoq.graph.subgraph2.
Require Import RamifyCoq.graph.graph_gen.
Require Import RamifyCoq.graph.dag.
Require Import RamifyCoq.graph.weak_mark_lemmas.
Require Import RamifyCoq.msl_application.Graph.
Require Import Coq.Logic.Classical.
Import RamifyCoq.msl_ext.seplog.OconNotation.

Local Open Scope logic.

Section SpatialGraph_Mark.

Context {V E: Type}.
Context {DV DE: Type}.
Context {GV GE Pred: Type}.
Context {SGBA: SpatialGraphBasicAssum V E}.
Context {SGC: SpatialGraphConstructor V E DV DE GV GE}.
Context {L_SGC: Local_SpatialGraphConstructor V E DV DE GV GE}.
Context {SGP: SpatialGraphPred V E GV GE Pred}.
Context {SGA: SpatialGraphAssum SGP}.
Context {MGS: WeakMarkGraph.MarkGraphSetting DV}.

Notation Graph := (LabeledGraph V E DV DE).
Notation SGraph := (SpatialGraph V E GV GE).

Local Coercion pg_lg: LabeledGraph >-> PreGraph.

Definition mark1 x (G1: Graph) (G2: Graph) := WeakMarkGraph.mark1 x G1 G2.
Definition mark x (G1: Graph) (G2: Graph) := WeakMarkGraph.mark x G1 G2 /\ G1 ~=~ G2.

Definition mark_list xs g1 g2 := relation_list (map mark xs) g1 g2.

Lemma mark_invalid_refl: forall (g: Graph) root, ~ vvalid g root -> mark root g g.
Proof.
  intros.
  split.
  + apply WeakMarkGraph.mark_invalid_refl; auto.
  + reflexivity.
Qed.

Lemma mark_marked_root_refl: forall (g: Graph) root, WeakMarkGraph.marked g root -> mark root g g.
Proof.
  intros.
  split.
  + apply WeakMarkGraph.mark_marked_root_refl; auto.
  + reflexivity.
Qed.

Lemma mark_list_eq: forall root xs g1 g2,
  mark_list xs g1 g2 ->
  WeakMarkGraph.componded_mark_list root xs g1 g2 /\ g1 ~=~ g2.
Proof.
  intros.
  change (mark_list xs g1 g2) with
    (relation_list (map (fun x => relation_conjunction (WeakMarkGraph.mark x) (respectful_relation pg_lg structurally_identical)) xs) g1 g2) in H.
  eapply relation_list_conjunction in H.
  rewrite relation_conjunction_iff in H.
  split.
  + destruct H as [? _].
    eapply relation_list_inclusion; [| exact H].
    intros ? _.
    clear.
    intros g1 g2 ?.
    exists g2; [| apply WeakMarkGraph.eq_do_nothing; auto].
    exists g1; [apply WeakMarkGraph.eq_do_nothing; auto |].
    auto.
  + eapply si_list.
    exact (proj2 H).
Qed.

Lemma mark1_mark_list_mark: forall root l (g g': Graph),
  vvalid g root ->
  (WeakMarkGraph.unmarked g) root ->
  step_list g root l ->
  relation_list (mark1 root :: mark_list l :: nil) g g' ->
  mark root g g'.
Proof.
  intros.
  destruct_relation_list g0 in H2.
  eapply (mark_list_eq root) in H2.
  destruct H2; simpl in H2.
  split.
  + eapply WeakMarkGraph.mark1_componded_mark_list_mark; eauto.
    split_relation_list (g :: g0 :: g0 :: g' :: nil); auto;
    apply WeakMarkGraph.eq_do_nothing; auto.
  + destruct H3 as [? _].
    rewrite H3; auto.
Qed.

Lemma vertex_update_ramify: forall (g: Graph) (x: V) (lx: DV) (gx: GV),
  vvalid g x ->
  gx = vgamma (Graph_SpatialGraph (labeledgraph_vgen g x lx)) x ->
  @derives Pred _
    (graph x (Graph_SpatialGraph g))
    (vertex_at x (vgamma (Graph_SpatialGraph g) x) *
      (vertex_at x gx -* graph x (Graph_SpatialGraph (labeledgraph_vgen g x lx)))).
Proof.
  intros.

  rewrite GSG_VGenPreserve by eassumption.

  apply vertices_at_ramify1; auto.
  apply reachable_refl.
  simpl; auto.
Qed.

Lemma exp_mark1: forall (g: Graph) (x: V) (lx: DV),
  WeakMarkGraph.label_marked lx ->
  @derives Pred _ (graph x (Graph_SpatialGraph (labeledgraph_vgen g x lx))) (EX g': Graph, !! (mark1 x g g') && graph x (Graph_SpatialGraph g')).
Proof.
  intros.
  apply (exp_right (labeledgraph_vgen g x lx)).
  apply andp_right; [apply prop_right | auto].
  apply WeakMarkGraph.vertex_update_mark1; auto.
Qed.

Lemma mark_list_mark_ramify: forall {A} (g1 g2: Graph) (g3: A -> Graph) x l y l',
  (forall (g: Graph) x y, reachable g x y \/ ~ reachable g x y) ->
  vvalid g1 x ->
  step_list g1 x (l ++ y :: l') ->
  relation_list (mark1 x :: mark_list l :: nil) g1 g2 ->
  @derives Pred _
    (graph x (Graph_SpatialGraph g2))
    (graph y (Graph_SpatialGraph g2) *
      (ALL a: A, !! mark y g2 (g3 a) -->
        (graph y (Graph_SpatialGraph (g3 a)) -*
         graph x (Graph_SpatialGraph (g3 a))))).
Proof.
  intros.
  assert (Included (reachable g1 y) (reachable g1 x)).
  Focus 1. {
    hnf; unfold Ensembles.In; intros.
    apply step_reachable with y; auto.
    clear H3 x0.
    apply H1; clear H1.
    rewrite in_app_iff.
    simpl; auto.
  } Unfocus.
  destruct_relation_list g1' in H2.
  destruct H4 as [? _].
  apply (mark_list_eq x) in H2.
  destruct H2 as [_ ?].
  rewrite <- H4 in H2; clear g1' H4.
  apply pred_sepcon_ramify_pred_Q with
    (PF := Intersection _
            (reachable g2 x)
            (Complement _ (reachable g2 y))); auto.
  + apply Ensemble_join_Intersection_Complement; auto.
    rewrite <- !H2.
    auto.
  + intros.
    destruct H4 as [_ ?].
    rewrite <- H4; clear H4.
    apply Ensemble_join_Intersection_Complement; auto.
    rewrite <- H2; auto.
  + intros.
    unfold graph_vcell.
    f_equal.
    simpl.
    destruct H5; unfold Ensembles.In in *.
    apply compute_vgamma_local.
    reflexivity.
Qed.

End SpatialGraph_Mark.

