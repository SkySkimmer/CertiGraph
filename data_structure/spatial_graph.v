Require Import VST.msl.seplog.
Require Import VST.msl.log_normalize.
Require Import RamifyCoq.Coqlib.
Require Import RamifyCoq.msl_ext.abs_addr.
Require Import RamifyCoq.msl_ext.seplog.
Require Import RamifyCoq.msl_ext.log_normalize.
Require Import RamifyCoq.msl_ext.iter_sepcon.
Require Import RamifyCoq.graph.graph.
Require Import RamifyCoq.graph.graph_reachable.
Require Import Coq.Logic.Classical.
Import RamifyCoq.msl_ext.seplog.OconNotation.

Class SpatialGraphSetting: Type := {
  Data: Type;
  addr: Type;
  null: addr;
  addr_eq_dec: forall x y: addr, {x = y} + {x <> y};
  addr_eqb: addr -> addr -> bool := fun x y => if addr_eq_dec x y then true else false
}.

Instance AV_SGraph `{SpatialGraphSetting} : AbsAddr.
  apply (mkAbsAddr addr (Data * addr * addr) (fun x y => addr_eqb x y)); simpl; intros.
  + unfold addr_eqb.
    destruct (addr_eq_dec p1 p2), (addr_eq_dec p2 p1); try congruence.
  + unfold addr_eqb in H0.
    destruct (addr_eq_dec p1 p1); congruence.
Defined.

Instance AddrDec `{SpatialGraphSetting}: EqDec Addr. apply Build_EqDec. intros. apply (addr_eq_dec t1 t2). Defined.
Opaque AddrDec.

Class SpatialGraphAssum: Type := {
  SGA_Pred: Type;
  SGA_ND: NatDed SGA_Pred;
  SGA_SL : SepLog SGA_Pred;
  SGA_ClSL: ClassicalSep SGA_Pred;
  SGA_PSL : PreciseSepLog SGA_Pred;
  SGA_CoSL: CorableSepLog SGA_Pred;
  SGA_OSL: OverlapSepLog SGA_Pred;
  SGA_DSL : DisjointedSepLog SGA_Pred;
  SGA_COSL: CorableOverlapSepLog SGA_Pred;

  SG_Setting: SpatialGraphSetting;
  trinode : Addr -> Val -> SGA_Pred;
  SGA_MSL: MapstoSepLog AV_SGraph trinode;
  SGA_sMSL: StaticMapstoSepLog AV_SGraph trinode;
  SGA_nMSL: NormalMapstoSepLog AV_SGraph trinode
}.

Global Existing Instances SGA_ND SGA_SL SGA_ClSL SGA_PSL SGA_CoSL SGA_OSL SGA_DSL SGA_COSL SG_Setting SGA_MSL SGA_sMSL SGA_nMSL.

Hint Resolve SGA_ND SGA_SL SGA_ClSL SGA_PSL SGA_CoSL SGA_OSL SGA_DSL SGA_COSL SG_Setting SGA_MSL SGA_sMSL SGA_nMSL.

Local Open Scope logic.

Section SpatialGraph.

  Context {SGA : SpatialGraphAssum}.

  Definition graph_cell (bi : BiGraph Addr Data) (v : Addr) : SGA_Pred := trinode v (gamma bi v).

  Lemma precise_graph_cell: forall bi v, precise (graph_cell bi v).
  Proof. intros. unfold graph_cell. destruct (gamma bi v) as [[? ?] ?]. apply mapsto_precise. Qed.

  Lemma sepcon_unique_graph_cell: forall bi, sepcon_unique (graph_cell bi).
  Proof.
    repeat intro. unfold graph_cell. destruct (gamma bi x) as [[? ?] ?]. apply mapsto_conflict.
    simpl. unfold addr_eqb. destruct (addr_eq_dec x x); auto.
  Qed.

  Lemma joinable_graph_cell : forall bi, joinable (graph_cell bi).
  Proof.
    intros. unfold joinable; intros. unfold graph_cell. apply disj_mapsto.
    simpl. unfold addr_eqb. destruct (addr_eq_dec x y); tauto.
  Qed.

  Definition graph (x : Addr) (bimg : BiMathGraph Addr Data null): SGA_Pred :=
    !!(x = null \/ valid x) && EX l : list Addr, !!reachable_list b_pg x l && iter_sepcon l (graph_cell bm_bi).

  Lemma graph_unfold_null: forall bimg, graph null bimg = emp.
  Proof.
    intros. apply pred_ext; unfold graph.
    + apply andp_left2, exp_left. intros. apply derives_extract_prop. intro. destruct x.
      - simpl. apply derives_refl.
      - exfalso. assert (In a (a :: x)). apply in_eq. rewrite (H a) in H0. apply reachable_head_valid in H0.
        rewrite <- pg_the_same in H0.
        apply valid_not_null in H0. auto.
    + apply andp_right.
      - apply prop_right. left; auto.
      - apply (exp_right nil). simpl. apply andp_right.
        * apply prop_right. intro. split; intro. inversion H. apply reachable_head_valid in H.
          rewrite <- pg_the_same in H. apply valid_not_null in H. exfalso; auto.
        * apply derives_refl.
  Qed.

  Lemma graph_unfold_valid:
    forall x bimg d l r, valid x -> gamma bm_bi x = (d, l, r) ->
                         graph x bimg = trinode x (d, l, r) ⊗ graph l bimg ⊗ graph r bimg.
  Proof.
    intros. assert (TRI: trinode x (d, l, r) = iter_sepcon (x :: nil) (graph_cell bm_bi)). {
      unfold iter_sepcon. rewrite sepcon_comm, emp_sepcon. unfold graph_cell. rewrite H0. auto.
    } apply pred_ext.
    + unfold graph. apply andp_left2, exp_left. intro li.
      rewrite (add_andp _ _ (iter_sepcon_unique_nodup li (sepcon_unique_graph_cell bm_bi))). normalize_overlap.
      rename H2 into NODUPLi.
      unfold gamma in H0. unfold biEdge in H0. destruct (only_two_neighbours x) as [v1 [v2 ?]].
      inversion H0; subst. clear H0. rewrite <- pg_the_same in H, H1.
      assert (In l (edge_func x)). rewrite e. apply in_eq. rewrite <- pg_the_same in H0.
      destruct (compute_neighbor bm_ma x li H H1 l H0) as [leftL [? ?]].
      assert (In r (edge_func x)). rewrite e. apply in_cons, in_eq. rewrite <- pg_the_same in H4.
      destruct (compute_neighbor bm_ma x li H H1 r H4) as [rightL [? ?]].
      apply (exp_right rightL). normalize_overlap. apply (exp_right leftL). normalize_overlap. apply andp_right.
      - rewrite <- !prop_and. apply prop_right. rewrite <- pg_the_same in *. do 2 (split; auto).
        split; apply (valid_graph x); auto.
      - rewrite TRI, ocon_assoc.
        rewrite !(iter_sepcon_ocon t_eq_dec); auto.
        2: repeat constructor; simpl; tauto.
        2: apply remove_dup_nodup.
        2: apply precise_graph_cell.
        2: apply joinable_graph_cell.
        2: apply precise_graph_cell.
        2: apply joinable_graph_cell.
        rewrite iter_sepcon_permutation with (l2 := remove_dup t_eq_dec ((x :: nil) ++ remove_dup t_eq_dec (leftL ++ rightL))).
        * apply derives_refl.
        * apply (eq_as_set_permutation t_eq_dec); auto.
          apply remove_dup_nodup. apply eq_as_set_spec. intro y.
          rewrite <- remove_dup_in_inv. simpl.
          rewrite <- remove_dup_in_inv.
          rewrite in_app_iff. rewrite (H1 y).
          apply (reachable_list_bigraph_in l r); auto. rewrite pg_the_same; auto.
    + unfold graph. normalize_overlap. intro rightL. normalize_overlap. intro leftL. normalize_overlap.
      apply (exp_right (remove_dup t_eq_dec ((x :: nil) ++ remove_dup t_eq_dec (leftL ++ rightL)))). rewrite <- andp_assoc.
      rewrite <- prop_and. rewrite TRI.
      rewrite (add_andp _ _ (iter_sepcon_unique_nodup leftL (sepcon_unique_graph_cell bm_bi))).
      rewrite (add_andp _ _ (iter_sepcon_unique_nodup rightL (sepcon_unique_graph_cell bm_bi))).
      normalize_overlap. apply andp_right.
      - apply prop_right. split. right; auto. intro.
        rewrite <- remove_dup_in_inv. simpl. rewrite <- remove_dup_in_inv.
        rewrite in_app_iff. symmetry. apply (reachable_list_bigraph_in l r); auto.
        unfold gamma in H0. unfold biEdge in H0. destruct (only_two_neighbours x) as [? [? ?]]. inversion H0. subst. auto.
      - rewrite ocon_assoc. rewrite !(iter_sepcon_ocon t_eq_dec); auto.
        * repeat constructor; simpl; tauto.
        * apply remove_dup_nodup.
        * apply precise_graph_cell.
        * apply joinable_graph_cell.
        * apply precise_graph_cell.
        * apply joinable_graph_cell.
  Qed.

  Lemma graph_root_nv: forall x bimg, graph x bimg |-- !!(x = null \/ valid x).
  Proof. intros. unfold graph. apply andp_left1, prop_left. intros. apply TT_prop_right; auto. Qed.

  Lemma graph_unfold':
    forall x bimg, graph x bimg = (!!(x = null) && emp) ||
                                  EX d:Data, EX l:Addr, EX r:Addr, !!(gamma bm_bi x = (d, l, r) /\ valid x) &&
                                                                     (trinode x (d, l, r) ⊗ graph l bimg ⊗ graph r bimg).
  Proof.
    intros. apply pred_ext.
    + destruct (t_eq_dec x null).
      - subst. apply orp_right1. rewrite graph_unfold_null. normalize.
      - apply orp_right2. destruct (gamma bm_bi x) as [[dd ll] rr] eqn:? .
        apply (exp_right dd), (exp_right ll), (exp_right rr).
        rewrite (add_andp _ _ (graph_root_nv x bimg)). apply andp_right.
        * apply andp_left2, prop_left; intros. apply TT_prop_right. destruct H. tauto. split; auto.
        * normalize. destruct H; [tauto | rewrite (graph_unfold_valid _ _ dd ll rr); auto].
    + apply orp_left.
      - normalize. rewrite graph_unfold_null. auto.
      - normalize. intros d l r [? ?]. rewrite <- (graph_unfold_valid _ _ d l r); auto.
  Qed.

  Lemma graph_unfold:
    forall x bimg d l r, gamma bm_bi x = (d, l, r) ->
                         graph x bimg = !!(x = null) && emp ||
                                        !!(valid x) && (trinode x (d, l, r) ⊗ graph l bimg ⊗ graph r bimg).
  Proof.
    intros. apply pred_ext.
    + rewrite (add_andp _ _ (graph_root_nv x bimg)). normalize. destruct H0.
      - subst. rewrite graph_unfold_null. apply orp_right1. normalize.
      - apply orp_right2. rewrite (graph_unfold_valid _ _ d l r H0 H). normalize.
    + apply orp_left.
      - normalize. rewrite graph_unfold_null. auto.
      - normalize. rewrite (graph_unfold_valid _ _ d l r H0 H). auto.
  Qed.

  Lemma precise_graph: forall x bimg, precise (graph x bimg).
  Proof.
    intros. apply precise_andp_right. apply precise_exp_iter_sepcon.
    + apply sepcon_unique_graph_cell.
    + apply classic.
    + apply precise_graph_cell.
    + apply reachable_list_permutation.
  Qed.

  Fixpoint graphs (l : list Addr) bimg :=
    match l with
      | nil => emp
      | v :: l' => graph v bimg ⊗ graphs l' bimg
    end.

  Lemma precise_graphs: forall S bimg, precise (graphs S bimg).
  Proof. intros; induction S; simpl. apply precise_emp. apply precise_ocon. apply precise_graph. apply IHS. Qed.

  Lemma graphs_list_well_defined: forall S bimg, graphs S bimg |-- !!well_defined_list bm_ma S.
  Proof.
    induction S; intros; unfold well_defined_list in *; simpl.
    + apply prop_right. intros; tauto.
    + unfold graph.
      rewrite (add_andp _ _ (IHS _)).
      normalize_overlap.
      apply prop_right.
      intro y; intros. destruct H1.
      - subst. rewrite pg_the_same; auto.
      - specialize (H0 _ H1). apply H0.
  Qed.

  Lemma graphs_unfold: forall S bimg, graphs S bimg =
                                      !!(well_defined_list bm_ma S) &&
                                      EX l: list Addr, !!reachable_set_list b_pg S l &&
                                                       iter_sepcon l (graph_cell bm_bi).
  Proof.
    induction S; intros.
    + unfold graphs. apply pred_ext.
      - apply andp_right.
        * apply prop_right. hnf. intros. inversion H.
        * apply (exp_right nil). simpl. apply andp_right; auto. apply prop_right. hnf.
          intros. split; intros. unfold reachable_through_set in H. destruct H as [s [? _]]. inversion H. inversion H.
      - normalize. destruct l. simpl; auto. hnf in H0. specialize (H0 a).
        assert (In a (a :: l)) by apply in_eq.
        rewrite <- H0 in H1. unfold reachable_through_set in H1. destruct H1 as [? [? _]]. inversion H1.
    + unfold graphs. fold graphs. rewrite IHS. unfold graph. apply pred_ext. clear IHS.
      - normalize_overlap. rename x into la.
        normalize_overlap. rename x into lS.
        normalize_overlap.
        rewrite (add_andp _ _ (iter_sepcon_unique_nodup la (sepcon_unique_graph_cell bm_bi))).
        rewrite (add_andp _ _ (iter_sepcon_unique_nodup lS (sepcon_unique_graph_cell bm_bi))).
        normalize_overlap.
        rewrite (iter_sepcon_ocon t_eq_dec); auto. apply (exp_right (remove_dup t_eq_dec (la ++ lS))).
        rewrite <- andp_assoc, <- prop_and. apply andp_right.
        * apply prop_right. split.
          Focus 1. {
            unfold well_defined_list in *. intros. simpl in H5.
            destruct H5; [subst; rewrite pg_the_same | apply H0]; auto. } Unfocus.
          Focus 1. {
            unfold reachable_set_list in *.
            unfold reachable_list in *. intros.
            rewrite <- remove_dup_in_inv.
            rewrite reachable_through_set_eq.
            specialize (H1 x). specialize (H2 x).
            split; intro; [apply in_or_app | apply in_app_or in H5];
            destruct H5; [left | right | left | right]; tauto.
          } Unfocus.
        * auto.
        * apply precise_graph_cell.
        * apply joinable_graph_cell.
      - normalize.
        assert (In a (a :: S)) by apply in_eq.
        assert (a = null \/ valid a) by (rewrite <- pg_the_same; unfold well_defined_list in H; apply (H a); auto).
        rewrite <- pg_the_same in H0, H2.
        destruct (reachable_through_single_reachable bm_ma _ _ H0 a H1 H2) as [la [? ?]].
        normalize_overlap. apply (exp_right la).
        assert (Sublist S (a :: S)) by (intro s; intros; apply in_cons; auto).
        assert (well_defined_list bm_ma S) by (unfold well_defined_list in *; intros; apply H; apply in_cons; auto).
        destruct (reachable_through_sublist_reachable _ _ _ H0 _ H5 H6) as [lS [? ?]].
        normalize_overlap. apply (exp_right lS). normalize_overlap.
        rewrite <- !prop_and. apply andp_right.
        * rewrite <- pg_the_same in *. apply prop_right. auto.
        * rewrite (add_andp _ _ (iter_sepcon_unique_nodup l (sepcon_unique_graph_cell bm_bi))).
          normalize.
          rewrite (iter_sepcon_ocon t_eq_dec); auto.
          2: apply precise_graph_cell.
          2: apply joinable_graph_cell.
          rewrite iter_sepcon_permutation with (l2 := remove_dup t_eq_dec (la ++ lS)); auto.
          apply NoDup_Permutation; auto. apply remove_dup_nodup.
          intros. rewrite <- remove_dup_in_inv. clear -H7 H3 H0.
          specialize (H0 x). specialize (H7 x). specialize (H3 x). rewrite <- H0.
          rewrite reachable_through_set_eq. rewrite in_app_iff. tauto.
  Qed.

End SpatialGraph.
