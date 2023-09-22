(* -*- mode: coq; coq-prog-args: ("-emacs" "-w" "-overriding-logical-loadpath" "-w" "-deprecated-native-compiler-option,-native-compiler-disabled" "-native-compiler" "ondemand" "-Q" "/github/workspace/cwd" "Top" "-Q" "/github/workspace/CertiGraph/lib" "CertiGraph.lib" "-Q" "/github/workspace/CertiGraph/msl_ext" "CertiGraph.msl_ext" "-Q" "/github/workspace/CertiGraph/msl_application" "CertiGraph.msl_application" "-Q" "/github/workspace/CertiGraph/graph" "CertiGraph.graph" "-Q" "/github/workspace/CertiGraph/heap_model_direct" "CertiGraph.heap_model_direct" "-Q" "/github/workspace/CertiGraph" "CertiGraph" "-Q" "/home/coq/.opam/4.13.1+flambda/lib/coq/user-contrib/VST" "VST" "-Q" "/home/coq/.opam/4.13.1+flambda/lib/coq/user-contrib/compcert" "compcert" "-Q" "/home/coq/.opam/4.13.1+flambda/lib/coq/user-contrib/Bignums" "Bignums" "-Q" "/home/coq/.opam/4.13.1+flambda/lib/coq/user-contrib/Flocq" "Flocq" "-Q" "/home/coq/.opam/4.13.1+flambda/lib/coq/user-contrib/Ltac2" "Ltac2" "-Q" "/home/coq/.opam/4.13.1+flambda/lib/coq/user-contrib/MenhirLib" "MenhirLib" "-top" "CertiGraph.CertiGC.refine_bug") -*- *)
(* File reduced by coq-bug-minimizer from original input, then from 248 lines to 293 lines, then from 306 lines to 1139 lines, then from 1144 lines to 745 lines, then from 758 lines to 2718 lines, then from 2722 lines to 1108 lines, then from 1120 lines to 836 lines, then from 849 lines to 1155 lines, then from 1160 lines to 909 lines, then from 727 lines to 139 lines, then from 152 lines to 655 lines, then from 657 lines to 144 lines, then from 157 lines to 1418 lines, then from 1420 lines to 199 lines, then from 212 lines to 2324 lines, then from 2327 lines to 228 lines, then from 241 lines to 2815 lines, then from 2818 lines to 249 lines, then from 262 lines to 6396 lines, then from 6401 lines to 363 lines, then from 376 lines to 1830 lines, then from 1830 lines to 363 lines, then from 376 lines to 981 lines, then from 985 lines to 364 lines, then from 377 lines to 3092 lines, then from 3076 lines to 366 lines, then from 379 lines to 3551 lines, then from 3552 lines to 375 lines, then from 388 lines to 692 lines, then from 696 lines to 375 lines, then from 388 lines to 849 lines, then from 853 lines to 387 lines, then from 400 lines to 866 lines, then from 871 lines to 385 lines, then from 398 lines to 3832 lines, then from 3835 lines to 504 lines, then from 517 lines to 3129 lines, then from 3133 lines to 2318 lines *)
(* coqc version 8.17.1 compiled with OCaml 4.13.1
   coqtop version 8.17.1
   Expected coqc runtime on this file: 2.652 sec *)
Require Coq.Init.Ltac.
Require Coq.Logic.ProofIrrelevance.
Require Coq.Setoids.Setoid.
Require Coq.Classes.Morphisms.
Require Coq.Classes.Equivalence.
Require Coq.Sets.Ensembles.
Require Coq.Sets.Constructive_sets.
Require Coq.Relations.Relation_Definitions.
Require Coq.Lists.List.
Require Coq.Program.Basics.
Require CertiGraph.lib.Coqlib.
Require Coq.Classes.EquivDec.
Require CertiGraph.lib.EquivDec_ext.
Require CertiGraph.lib.Ensembles_ext.
Require Coq.micromega.Lia.
Require Coq.Sorting.Permutation.
Require Coq.ZArith.ZArith_base.
Require Coq.ZArith.Zcomplements.
Require Coq.Logic.FunctionalExtensionality.
Require Coq.ZArith.ZArith.
Require Coq.ZArith.Znumtheory.
Require VST.zlist.sublist.
Require Coq.Logic.PropExtensionality.
Require VST.zlist.Zlength_solver.
Require Coq.Sorting.Sorted.
Require VST.zlist.list_solver.
Require CertiGraph.lib.List_ext.
Require CertiGraph.lib.Relation_ext.
Require CertiGraph.lib.Equivalence_ext.
Require CertiGraph.lib.List_Func_ext.
Require CertiGraph.lib.relation_list.
Require CertiGraph.graph.graph_model.
Require Coq.Arith.Arith.
Require Coq.Arith.EqNat.
Require Coq.Arith.Max.
Require Coq.Bool.Bool.
Require Coq.Classes.RelationClasses.
Require Coq.Lists.ListSet.
Require Coq.Logic.ClassicalFacts.
Require Coq.Logic.ConstructiveEpsilon.
Require Coq.Logic.Eqdep.
Require Coq.Logic.EqdepFacts.
Require Coq.Logic.Eqdep_dec.
Require Coq.Logic.JMeq.
Require Coq.Numbers.Natural.Peano.NPeano.
Require Coq.Reals.Rdefinitions.
Require Coq.Relations.Relations.
Require Coq.Sorting.Sorting.
Require Coq.Strings.Ascii.
Require Coq.Strings.String.
Require Coq.Structures.GenericMinMax.
Require Coq.Structures.Orders.
Require Coq.Wellfounded.Wellfounded.
Require Coq.funind.FunInd.
Require Coq.funind.Recdef.
Require VST.msl.simple_CCC.
Require VST.veric.lift.
Require compcert.cfrontend.Clight.
Require compcert.cfrontend.Cop.
Require compcert.cfrontend.Ctypes.
Require compcert.common.AST.
Require compcert.common.Events.
Require compcert.common.Globalenvs.
Require compcert.common.Memdata.
Require compcert.common.Memory.
Require compcert.common.Memtype.
Require compcert.common.Values.
Require compcert.export.Clightdefs.
Require compcert.lib.Axioms.
Require compcert.lib.Coqlib.
Require compcert.lib.Floats.
Require compcert.lib.Integers.
Require compcert.lib.Maps.
Require VST.floyd.find_nth_tactic.
Require VST.msl.Axioms.
Require VST.msl.Extensionality.
Require VST.msl.sepalg.
Require VST.msl.seplog.
Require VST.msl.ghost.
Require VST.sepcomp.extspec.
Require VST.floyd.jmeq_lemmas.
Require VST.msl.base.
Require VST.msl.eq_dec.
Require VST.msl.functors.
Require VST.msl.ghost_seplog.
Require VST.msl.sig_isomorphism.
Require VST.msl.Coqlib2.
Require VST.msl.cjoins.
Require VST.msl.sepalg_generators.
Require VST.msl.ageable.
Require VST.msl.boolean_alg.
Require VST.msl.psepalg.
Require VST.msl.sepalg_functors.
Require VST.msl.combiner_sa.
Require VST.msl.predicates_hered.
Require VST.msl.age_sepalg.
Require VST.msl.cross_split.
Require VST.msl.knot.
Require VST.msl.subtypes.
Require VST.msl.predicates_rec.
Require VST.sepcomp.Address.
Require VST.veric.val_lemmas.
Require VST.msl.knot_full_variant.
Require VST.msl.age_to.
Require VST.msl.tree_shares.
Require VST.veric.coqlib4.
Require VST.msl.knot_shims.
Require VST.msl.shares.
Require VST.floyd.coqlib3.
Require VST.msl.predicates_sl.
Require VST.msl.pshares.
Require VST.sepcomp.mem_lemmas.
Require VST.msl.corable.
Require VST.sepcomp.semantics.
Require VST.veric.Memory.
Require VST.msl.subtypes_sl.
Require VST.sepcomp.semantics_lemmas.
Require VST.msl.contractive.
Require VST.sepcomp.event_semantics.
Require VST.msl.knot_full_sa.
Require VST.veric.base.
Require VST.sepcomp.step_lemmas.
Require VST.veric.type_induction.
Require VST.veric.Cop2.
Require VST.veric.composite_compute.
Require VST.veric.address_conflict.
Require VST.floyd.functional_base.
Require VST.veric.align_mem.
Require VST.veric.compspecs.
Require VST.veric.Clight_base.
Require VST.veric.Clight_lemmas.
Require VST.veric.Clight_core.
Require VST.msl.msl_standard.
Require VST.msl.normalize.
Require VST.msl.alg_seplog.
Require VST.msl.sepalg_list.
Require VST.veric.shares.
Require VST.msl.log_normalize.
Require VST.msl.wand_frame.
Require VST.msl.wandQ_frame.
Require VST.msl.iter_sepcon.
Require VST.msl.ramification_lemmas.
Require VST.veric.local.
Require VST.veric.rmaps.
Require VST.veric.rmaps_lemmas.
Require VST.veric.compcert_rmaps.
Require VST.veric.juicy_base.
Require VST.veric.age_to_resource_at.
Require VST.veric.juicy_mem.
Require VST.veric.mpred.
Require VST.veric.juicy_safety.
Require VST.veric.res_predicates.
Require VST.veric.own.
Require VST.veric.slice.
Require VST.veric.juicy_mem_lemmas.
Require VST.veric.juicy_mem_ops.
Require VST.veric.mapsto_memory_block.
Require VST.veric.mem_lessdef.
Require VST.veric.ghosts.
Require VST.veric.ghost_PCM.
Require VST.veric.invariants.
Require VST.veric.Clight_mem_lessdef.
Require VST.veric.fupd.
Require VST.veric.seplog.
Require VST.veric.assert_lemmas.
Require VST.veric.tycontext.
Require VST.veric.Clight_Cop2.
Require VST.veric.Clight_evsem.
Require VST.veric.expr.
Require VST.veric.change_compspecs.
Require VST.veric.expr2.
Require VST.veric.binop_lemmas2.
Require VST.veric.environ_lemmas.
Require VST.veric.expr_lemmas2.
Require VST.veric.binop_lemmas3.
Require VST.veric.binop_lemmas4.
Require VST.veric.binop_lemmas5.
Require VST.veric.binop_lemmas6.
Require VST.veric.expr_lemmas3.
Require VST.veric.Clight_mapsto_memory_block.
Require VST.veric.binop_lemmas.
Require VST.veric.Clight_seplog.
Require VST.veric.juicy_extspec.
Require VST.veric.expr_lemmas4.
Require VST.veric.expr_lemmas.
Require VST.veric.extend_tc.
Require VST.veric.initial_world.
Require VST.veric.valid_pointer.
Require VST.veric.Clight_assert_lemmas.
Require VST.veric.Clight_initial_world.
Require VST.veric.semax.
Require VST.veric.semax_lemmas.
Require VST.veric.semax_call.
Require VST.veric.semax_conseq.
Require VST.veric.semax_switch.
Require VST.veric.initialize.
Require VST.veric.semax_loop.
Require VST.veric.semax_straight.
Require VST.veric.semax_ext.
Require VST.veric.semax_prog.
Require VST.veric.SeparationLogic.
Require VST.veric.SeparationLogicSoundness.
Require VST.veric.SequentialClight2.
Require VST.floyd.val_lemmas.
Require VST.veric.NullExtension.
Require VST.floyd.assert_lemmas.

Module Export AdmitTactic.
Module Import LocalFalse.
Inductive False : Prop := .
End LocalFalse.
Axiom proof_admitted : False.
Import Coq.Init.Ltac.
Tactic Notation "admit" := abstract case proof_admitted.
End AdmitTactic.

Module Export VST_DOT_floyd_DOT_SeparationLogicFacts_WRAPPED.
Module Export SeparationLogicFacts.
Export compcert.export.Clightdefs.
Export VST.veric.SeparationLogic.
Export VST.msl.Extensionality.
Export compcert.lib.Coqlib.
Export VST.msl.Coqlib2.
Export VST.veric.coqlib4.
Export VST.floyd.coqlib3.
Export VST.floyd.jmeq_lemmas.
Export VST.floyd.find_nth_tactic.
Export VST.veric.juicy_extspec.
Import VST.veric.NullExtension.
Import VST.floyd.assert_lemmas.
Import LiftNotation.
Import compcert.lib.Maps.

Local Open Scope logic.

 
Lemma exp_derives:
       forall {A: Type}  {NA: NatDed A} (B: Type) (P Q: B -> A),
               (forall x:B, P x |-- Q x) -> (exp P |-- exp Q).
Admitted.

 

Lemma closed_wrt_subst:
  forall {A} id e (P: environ -> A), closed_wrt_vars (eq id) P -> subst id e P = P.
Admitted.

 

Lemma subst_self: forall {A: Type} (P: environ -> A) t id v Delta rho,
  (temp_types Delta) ! id = Some t ->
  tc_environ Delta rho ->
  v rho = eval_id id rho ->
  subst id v P rho = P rho.
Admitted.
Definition obox (Delta: tycontext) (i: ident) (P: environ -> mpred): environ -> mpred. exact (ALL v: _,
    match ((temp_types Delta) ! i) with
    | Some t => !! (tc_val' t v) --> subst i (`v) P
    | _ => TT
    end). Defined.
Definition odia (Delta: tycontext) (i: ident) (P: environ -> mpred): environ -> mpred. exact (EX v: _,
    match ((temp_types Delta) ! i) with
    | Some t => !! (tc_val' t v) && subst i (`v) P
    | _ => FF
    end). Defined.

Lemma obox_closed_wrt: forall Delta id P, closed_wrt_vars (eq id) (obox Delta id P).
Admitted.

Lemma odia_closed_wrt: forall Delta id P, closed_wrt_vars (eq id) (odia Delta id P).
Admitted.

Lemma subst_obox: forall Delta id v (P: environ -> mpred), subst id (`v) (obox Delta id P) = obox Delta id P.
Admitted.

Lemma subst_odia: forall Delta id v (P: environ -> mpred), subst id (`v) (odia Delta id P) = odia Delta id P.
Admitted.
Definition temp_guard (Delta : tycontext) (i: ident): Prop. exact ((temp_types Delta) ! i <> None). Defined.

Lemma obox_closed: forall Delta i P, temp_guard Delta i -> closed_wrt_vars (eq i) P -> obox Delta i P = P.
Admitted.

Lemma obox_odia: forall Delta i P, temp_guard Delta i -> obox Delta i (odia Delta i P) = odia Delta i P.
Admitted.

Lemma obox_K: forall Delta i P Q, (P |-- Q) -> obox Delta i P |-- obox Delta i Q.
Admitted.

Lemma obox_T: forall Delta i (P: environ -> mpred),
  temp_guard Delta i ->
  local (tc_environ Delta) && obox Delta i P |-- P.
Admitted.

Lemma odia_D: forall Delta i (P: environ -> mpred),
  temp_guard Delta i ->
  local (tc_environ Delta) && P |-- odia Delta i P.
Admitted.

Lemma odia_derives_EX_subst: forall Delta i P,
  odia Delta i P |-- EX v : val, subst i (` v) P.
Admitted.

Lemma obox_left2: forall Delta i P Q,
  temp_guard Delta i ->
  (local (tc_environ Delta) && P |-- Q) ->
  local (tc_environ Delta) && obox Delta i P |-- obox Delta i Q.
Admitted.

Lemma obox_left2': forall Delta i P Q,
  temp_guard Delta i ->
  (local (tc_environ Delta) && (allp_fun_id Delta && P) |-- Q) ->
  local (tc_environ Delta) && (allp_fun_id Delta && obox Delta i P) |-- obox Delta i Q.
Admitted.

Lemma obox_sepcon: forall Delta i P Q,
  obox Delta i P * obox Delta i Q |-- obox Delta i (P * Q).
Admitted.

Definition oboxopt Delta ret P :=
  match ret with
  | Some id => obox Delta id P
  | _ => P
  end.

Definition odiaopt Delta ret P :=
  match ret with
  | Some id => odia Delta id P
  | _ => P
  end.
Definition temp_guard_opt (Delta : tycontext) (i: option ident): Prop. exact (match i with
  | Some i => temp_guard Delta i
  | None => True
  end). Defined.

Lemma substopt_oboxopt: forall Delta id v (P: environ -> mpred), substopt id (`v) (oboxopt Delta id P) = oboxopt Delta id P.
Admitted.

Lemma oboxopt_closed: forall Delta i P,
  temp_guard_opt Delta i ->
  closed_wrt_vars (fun id => isSome (match i with Some i' => insert_idset i' idset0 | None => idset0 end) ! id) P ->
  oboxopt Delta i P = P.
Admitted.

Lemma oboxopt_T: forall Delta i (P: environ -> mpred),
  temp_guard_opt Delta i ->
  local (tc_environ Delta) && oboxopt Delta i P |-- P.
Admitted.

Lemma odiaopt_D: forall Delta i (P: environ -> mpred),
  temp_guard_opt Delta i ->
  local (tc_environ Delta) && P |-- odiaopt Delta i P.
Admitted.

Lemma oboxopt_odiaopt: forall Delta i P, temp_guard_opt Delta i -> oboxopt Delta i (odiaopt Delta i P) = odiaopt Delta i P.
Admitted.

Lemma oboxopt_K: forall Delta i P Q, (P |-- Q) -> oboxopt Delta i P |-- oboxopt Delta i Q.
Admitted.

Lemma odiaopt_derives_EX_substopt: forall Delta i P,
  odiaopt Delta i P |-- EX v : val, substopt i (` v) P.
Admitted.

Lemma oboxopt_left2: forall Delta i P Q,
  temp_guard_opt Delta i ->
  (local (tc_environ Delta) && P |-- Q) ->
  local (tc_environ Delta) && oboxopt Delta i P |-- oboxopt Delta i Q.
Admitted.

Lemma oboxopt_left2': forall Delta i P Q,
  temp_guard_opt Delta i ->
  (local (tc_environ Delta) && (allp_fun_id Delta && P) |-- Q) ->
  local (tc_environ Delta) && (allp_fun_id Delta && oboxopt Delta i P) |-- oboxopt Delta i Q.
Admitted.

Lemma oboxopt_sepcon: forall Delta i P Q,
  oboxopt Delta i P * oboxopt Delta i Q |-- oboxopt Delta i (P * Q).
Admitted.

Module Type CLIGHT_SEPARATION_HOARE_LOGIC_COMPLETE_CONSEQUENCE.

Declare Module CSHL_Def: CLIGHT_SEPARATION_HOARE_LOGIC_DEF.

Import CSHL_Def.

Axiom semax_conseq:
  forall {CS: compspecs} {Espec: OracleKind} (Delta: tycontext),
  forall P' (R': ret_assert) P c (R: ret_assert) ,
    (local (tc_environ Delta) && ((allp_fun_id Delta) && P) |-- (|={Ensembles.Full_set}=> P')) ->
    (local (tc_environ Delta) && ((allp_fun_id Delta) && RA_normal R') |-- (|={Ensembles.Full_set}=> RA_normal R)) ->
    (local (tc_environ Delta) && ((allp_fun_id Delta) && RA_break R') |-- (|={Ensembles.Full_set}=> RA_break R)) ->
    (local (tc_environ Delta) && ((allp_fun_id Delta) && RA_continue R') |-- (|={Ensembles.Full_set}=> RA_continue R)) ->
    (forall vl, local (tc_environ Delta) && ((allp_fun_id Delta) && RA_return R' vl) |-- (RA_return R vl)) ->
   @semax CS Espec Delta P' c R' -> @semax CS Espec Delta P c R.

End CLIGHT_SEPARATION_HOARE_LOGIC_COMPLETE_CONSEQUENCE.

Module GenCConseqFacts
       (Def: CLIGHT_SEPARATION_HOARE_LOGIC_DEF)
       (CConseq: CLIGHT_SEPARATION_HOARE_LOGIC_COMPLETE_CONSEQUENCE with Module CSHL_Def := Def).

Import Def.
Import CConseq.

Lemma semax_pre_post_indexed_fupd:
  forall {CS: compspecs} {Espec: OracleKind} (Delta: tycontext),
 forall P' (R': ret_assert) P c (R: ret_assert) ,
    (local (tc_environ Delta) && P |-- (|={Ensembles.Full_set}=> P')) ->
    (local (tc_environ Delta) && RA_normal R' |-- (|={Ensembles.Full_set}=> RA_normal R)) ->
    (local (tc_environ Delta) && RA_break R' |-- (|={Ensembles.Full_set}=> RA_break R)) ->
    (local (tc_environ Delta) && RA_continue R' |-- (|={Ensembles.Full_set}=> RA_continue R)) ->
    (forall vl, local (tc_environ Delta) && RA_return R' vl |-- (RA_return R vl)) ->
   @semax CS Espec Delta P' c R' -> @semax CS Espec Delta P c R.
Admitted.

Lemma semax_pre_post_fupd:
  forall {CS: compspecs} {Espec: OracleKind} (Delta: tycontext),
 forall P' (R': ret_assert) P c (R: ret_assert) ,
    (local (tc_environ Delta) && P |-- (|={Ensembles.Full_set}=> P')) ->
    (local (tc_environ Delta) && RA_normal R' |-- (|={Ensembles.Full_set}=> RA_normal R)) ->
    (local (tc_environ Delta) && RA_break R' |-- (|={Ensembles.Full_set}=> RA_break R)) ->
    (local (tc_environ Delta) && RA_continue R' |-- (|={Ensembles.Full_set}=> RA_continue R)) ->
    (forall vl, local (tc_environ Delta) && RA_return R' vl |-- (RA_return R vl)) ->
   @semax CS Espec Delta P' c R' -> @semax CS Espec Delta P c R.
Admitted.

Lemma semax_pre_indexed_fupd:
 forall P' Espec {cs: compspecs} Delta P c R,
     (local (tc_environ Delta) && P |-- (|={Ensembles.Full_set}=> P')) ->
     @semax cs Espec Delta P' c R  -> @semax cs Espec Delta P c R.
Admitted.

Lemma semax_post_indexed_fupd:
 forall (R': ret_assert) Espec {cs: compspecs} Delta (R: ret_assert) P c,
   (local (tc_environ Delta) && RA_normal R' |-- (|={Ensembles.Full_set}=> RA_normal R)) ->
   (local (tc_environ Delta) && RA_break R' |-- (|={Ensembles.Full_set}=> RA_break R)) ->
   (local (tc_environ Delta) && RA_continue R' |-- (|={Ensembles.Full_set}=> RA_continue R)) ->
   (forall vl, local (tc_environ Delta) && RA_return R' vl |-- (RA_return R vl)) ->
   @semax cs Espec Delta P c R' ->  @semax cs Espec Delta P c R.
Admitted.

Lemma semax_post''_indexed_fupd: forall R' Espec {cs: compspecs} Delta R P c,
           (local (tc_environ Delta) && R' |-- (|={Ensembles.Full_set}=> RA_normal R)) ->
      @semax cs Espec Delta P c (normal_ret_assert R') ->
      @semax cs Espec Delta P c R.
Admitted.

Lemma semax_pre_fupd:
 forall P' Espec {cs: compspecs} Delta P c R,
     (local (tc_environ Delta) && P |-- (|={Ensembles.Full_set}=> P')) ->
     @semax cs Espec Delta P' c R  -> @semax cs Espec Delta P c R.
Admitted.

Lemma semax_post_fupd:
 forall (R': ret_assert) Espec {cs: compspecs} Delta (R: ret_assert) P c,
   (local (tc_environ Delta) && RA_normal R' |-- (|={Ensembles.Full_set}=> RA_normal R)) ->
   (local (tc_environ Delta) && RA_break R' |-- (|={Ensembles.Full_set}=> RA_break R)) ->
   (local (tc_environ Delta) && RA_continue R' |-- (|={Ensembles.Full_set}=> RA_continue R)) ->
   (forall vl, local (tc_environ Delta) && RA_return R' vl |-- (RA_return R vl)) ->
   @semax cs Espec Delta P c R' ->  @semax cs Espec Delta P c R.
Admitted.

Lemma semax_post'_fupd: forall R' Espec {cs: compspecs} Delta R P c,
           (local (tc_environ Delta) && R' |-- (|={Ensembles.Full_set}=> R)) ->
      @semax cs Espec Delta P c (normal_ret_assert R') ->
      @semax cs Espec Delta P c (normal_ret_assert R).
Admitted.

Lemma semax_post''_fupd: forall R' Espec {cs: compspecs} Delta R P c,
           (local (tc_environ Delta) && R' |-- (|={Ensembles.Full_set}=> RA_normal R)) ->
      @semax cs Espec Delta P c (normal_ret_assert R') ->
      @semax cs Espec Delta P c R.
Admitted.

Lemma semax_pre_post'_fupd: forall P' R' Espec {cs: compspecs} Delta R P c,
      (local (tc_environ Delta) && P |-- (|={Ensembles.Full_set}=> P')) ->
      (local (tc_environ Delta) && R' |-- (|={Ensembles.Full_set}=> R)) ->
      @semax cs Espec Delta P' c (normal_ret_assert R') ->
      @semax cs Espec Delta P c (normal_ret_assert R).
Admitted.

Lemma semax_pre_post''_fupd: forall P' R' Espec {cs: compspecs} Delta R P c,
      (local (tc_environ Delta) && P |-- (|={Ensembles.Full_set}=> P')) ->
      (local (tc_environ Delta) && R' |-- (|={Ensembles.Full_set}=> RA_normal R)) ->
      @semax cs Espec Delta P' c (normal_ret_assert R') ->
      @semax cs Espec Delta P c R.
Admitted.

End GenCConseqFacts.

Module Type CLIGHT_SEPARATION_HOARE_LOGIC_CONSEQUENCE.

Declare Module CSHL_Def: CLIGHT_SEPARATION_HOARE_LOGIC_DEF.

Import CSHL_Def.

Axiom semax_pre_post : forall {Espec: OracleKind}{CS: compspecs},
 forall P' (R': ret_assert) Delta P c (R: ret_assert) ,
    (local (tc_environ Delta) && P |-- P') ->
    (local (tc_environ Delta) && RA_normal R' |-- RA_normal R) ->
    (local (tc_environ Delta) && RA_break R' |-- RA_break R) ->
    (local (tc_environ Delta) && RA_continue R' |-- RA_continue R) ->
    (forall vl, local (tc_environ Delta) && RA_return R' vl |-- RA_return R vl) ->
   @semax CS Espec Delta P' c R' -> @semax CS Espec Delta P c R.

End CLIGHT_SEPARATION_HOARE_LOGIC_CONSEQUENCE.

Module GenConseq
       (Def: CLIGHT_SEPARATION_HOARE_LOGIC_DEF)
       (CConseq: CLIGHT_SEPARATION_HOARE_LOGIC_COMPLETE_CONSEQUENCE with Module CSHL_Def := Def): CLIGHT_SEPARATION_HOARE_LOGIC_CONSEQUENCE with Module CSHL_Def := Def.

Module CSHL_Def := Def.
Module CConseqFacts := GenCConseqFacts (Def) (CConseq).
Import CSHL_Def.
Import CConseq.
Import CConseqFacts.

Lemma semax_pre_post : forall {Espec: OracleKind}{CS: compspecs},
 forall P' (R': ret_assert) Delta P c (R: ret_assert) ,
    (local (tc_environ Delta) && P |-- P') ->
    (local (tc_environ Delta) && RA_normal R' |-- RA_normal R) ->
    (local (tc_environ Delta) && RA_break R' |-- RA_break R) ->
    (local (tc_environ Delta) && RA_continue R' |-- RA_continue R) ->
    (forall vl, local (tc_environ Delta) && RA_return R' vl |-- RA_return R vl) ->
   @semax CS Espec Delta P' c R' -> @semax CS Espec Delta P c R.
Admitted.

End GenConseq.

Module GenConseqFacts
       (Def: CLIGHT_SEPARATION_HOARE_LOGIC_DEF)
       (Conseq: CLIGHT_SEPARATION_HOARE_LOGIC_CONSEQUENCE with Module CSHL_Def := Def).

Import Def.
Import Conseq.

 

Lemma semax_pre: forall {Espec: OracleKind}{cs: compspecs},
 forall P' Delta P c R,
     (local (tc_environ Delta) && P |-- P') ->
     @semax cs Espec Delta P' c R  -> @semax cs Espec Delta P c R.
Admitted.

Lemma semax_pre_simple: forall {Espec: OracleKind}{cs: compspecs},
 forall P' Delta P c R,
     (P |-- P') ->
     @semax cs Espec Delta P' c R  -> @semax cs Espec Delta P c R.
Admitted.

Lemma semax_post:
 forall (R': ret_assert) Espec {cs: compspecs} Delta (R: ret_assert) P c,
   (local (tc_environ Delta) && RA_normal R' |-- RA_normal R) ->
   (local (tc_environ Delta) && RA_break R' |-- RA_break R) ->
   (local (tc_environ Delta) && RA_continue R' |-- RA_continue R) ->
   (forall vl, local (tc_environ Delta) && RA_return R' vl |-- RA_return R vl) ->
   @semax cs Espec Delta P c R' ->  @semax cs Espec Delta P c R.
Admitted.

Lemma semax_post_simple:
 forall (R': ret_assert) Espec {cs: compspecs} Delta (R: ret_assert) P c,
   (RA_normal R' |-- RA_normal R) ->
   (RA_break R' |-- RA_break R) ->
   (RA_continue R' |-- RA_continue R) ->
   (forall vl, RA_return R' vl |-- RA_return R vl) ->
   @semax cs Espec Delta P c R' ->  @semax cs Espec Delta P c R.
Admitted.

Lemma semax_post': forall R' Espec {cs: compspecs} Delta R P c,
           (local (tc_environ Delta) && R' |-- R) ->
      @semax cs Espec Delta P c (normal_ret_assert R') ->
      @semax cs Espec Delta P c (normal_ret_assert R).
Admitted.

Lemma semax_pre_post': forall P' R' Espec {cs: compspecs} Delta R P c,
      (local (tc_environ Delta) && P |-- P') ->
      (local (tc_environ Delta) && R' |-- R) ->
      @semax cs Espec Delta P' c (normal_ret_assert R') ->
      @semax cs Espec Delta P c (normal_ret_assert R).
Admitted.

 

Lemma semax_post'': forall R' Espec {cs: compspecs} Delta R P c,
           (local (tc_environ Delta) && R' |-- RA_normal R) ->
      @semax cs Espec Delta P c (normal_ret_assert R') ->
      @semax cs Espec Delta P c R.
Admitted.

Lemma semax_pre_post'': forall P' R' Espec {cs: compspecs} Delta R P c,
      (local (tc_environ Delta) && P |-- P') ->
      (local (tc_environ Delta) && R' |-- RA_normal R) ->
      @semax cs Espec Delta P' c (normal_ret_assert R') ->
      @semax cs Espec Delta P c R.
Admitted.

End GenConseqFacts.

Module Type CLIGHT_SEPARATION_HOARE_LOGIC_EXTRACTION.

Declare Module CSHL_Def: CLIGHT_SEPARATION_HOARE_LOGIC_DEF.

Import CSHL_Def.

End CLIGHT_SEPARATION_HOARE_LOGIC_EXTRACTION.

Module GenExtrFacts
       (Def: CLIGHT_SEPARATION_HOARE_LOGIC_DEF)
       (Conseq: CLIGHT_SEPARATION_HOARE_LOGIC_CONSEQUENCE with Module CSHL_Def := Def)
       (Extr: CLIGHT_SEPARATION_HOARE_LOGIC_EXTRACTION with Module CSHL_Def := Def).

Module ConseqFacts := GenConseqFacts (Def) (Conseq).
Import Def.
Import Conseq.
Import ConseqFacts.
Import Extr.

Lemma semax_extract_prop:
  forall {CS: compspecs} {Espec: OracleKind},
  forall Delta (PP: Prop) P c Q,
           (PP -> @semax CS Espec Delta P c Q) ->
           @semax CS Espec Delta (!!PP && P) c Q.
Admitted.

Lemma semax_orp:
  forall {CS: compspecs} {Espec: OracleKind},
  forall Delta P1 P2 c Q,
           @semax CS Espec Delta P1 c Q ->
           @semax CS Espec Delta P2 c Q ->
           @semax CS Espec Delta (P1 || P2) c Q.
Admitted.

End GenExtrFacts.

Module GenIExtrFacts
       (Def: CLIGHT_SEPARATION_HOARE_LOGIC_DEF)
       (CConseq: CLIGHT_SEPARATION_HOARE_LOGIC_COMPLETE_CONSEQUENCE with Module CSHL_Def := Def)
       (Extr: CLIGHT_SEPARATION_HOARE_LOGIC_EXTRACTION with Module CSHL_Def := Def).

Module Conseq := GenConseq (Def) (CConseq).
Module CConseqFacts := GenCConseqFacts (Def) (CConseq).
Module ExtrFacts := GenExtrFacts (Def) (Conseq) (Extr).
Import Def.
Import CConseq.
Import CConseqFacts.
Import Extr.
Import ExtrFacts.

Lemma semax_extract_later_prop:
  forall {CS: compspecs} {Espec: OracleKind},
  forall Delta (PP: Prop) P c Q,
           (PP -> @semax CS Espec Delta P c Q) ->
           @semax CS Espec Delta ((|> !!PP) && P) c Q.
Admitted.

End GenIExtrFacts.

Module Type CLIGHT_SEPARATION_HOARE_LOGIC_STORE_FORWARD.

Declare Module CSHL_Def: CLIGHT_SEPARATION_HOARE_LOGIC_DEF.

Import CSHL_Def.

Axiom semax_store_forward:
  forall {CS: compspecs} {Espec: OracleKind} (Delta: tycontext),
 forall e1 e2 sh P,
   writable_share sh ->
   @semax CS Espec Delta
          (|> ( (tc_lvalue Delta e1) &&  (tc_expr Delta (Ecast e2 (typeof e1)))  &&
             (`(mapsto_ sh (typeof e1)) (eval_lvalue e1) * P)))
          (Sassign e1 e2)
          (normal_ret_assert
             (`(mapsto sh (typeof e1)) (eval_lvalue e1) (`force_val (`(sem_cast (typeof e2) (typeof e1)) (eval_expr e2))) * P)).

End CLIGHT_SEPARATION_HOARE_LOGIC_STORE_FORWARD.

Module Type CLIGHT_SEPARATION_HOARE_LOGIC_STORE_BACKWARD.

Declare Module CSHL_Def: CLIGHT_SEPARATION_HOARE_LOGIC_DEF.

Import CSHL_Def.

Axiom semax_store_backward: forall {CS: compspecs} {Espec: OracleKind} (Delta: tycontext) e1 e2 P,
   @semax CS Espec Delta
          (EX sh: share, !! writable_share sh && |> ( (tc_lvalue Delta e1) &&  (tc_expr Delta (Ecast e2 (typeof e1)))  &&
             ((`(mapsto_ sh (typeof e1)) (eval_lvalue e1)) * (`(mapsto sh (typeof e1)) (eval_lvalue e1) (`force_val (`(sem_cast (typeof e2) (typeof e1)) (eval_expr e2))) -* P))))
          (Sassign e1 e2)
          (normal_ret_assert P).

End CLIGHT_SEPARATION_HOARE_LOGIC_STORE_BACKWARD.

Module StoreF2B
       (Def: CLIGHT_SEPARATION_HOARE_LOGIC_DEF)
       (Conseq: CLIGHT_SEPARATION_HOARE_LOGIC_CONSEQUENCE with Module CSHL_Def := Def)
       (Extr: CLIGHT_SEPARATION_HOARE_LOGIC_EXTRACTION with Module CSHL_Def := Def)
       (StoreF: CLIGHT_SEPARATION_HOARE_LOGIC_STORE_FORWARD with Module CSHL_Def := Def):
       CLIGHT_SEPARATION_HOARE_LOGIC_STORE_BACKWARD with Module CSHL_Def := Def.

Module CSHL_Def := Def.
Module ConseqFacts := GenConseqFacts (Def) (Conseq).
Module ExtrFacts := GenExtrFacts (Def) (Conseq) (Extr).
Import Def.
Import Conseq.
Import ConseqFacts.
Import Extr.
Import ExtrFacts.
Import StoreF.

Theorem semax_store_backward: forall {CS: compspecs} {Espec: OracleKind} (Delta: tycontext) e1 e2 P,
   @semax CS Espec Delta
          (EX sh: share, !! writable_share sh && |> ( (tc_lvalue Delta e1) &&  (tc_expr Delta (Ecast e2 (typeof e1)))  &&
             ((`(mapsto_ sh (typeof e1)) (eval_lvalue e1)) * (`(mapsto sh (typeof e1)) (eval_lvalue e1) (`force_val (`(sem_cast (typeof e2) (typeof e1)) (eval_expr e2))) -* P))))
          (Sassign e1 e2)
          (normal_ret_assert P).
Admitted.

End StoreF2B.

Module StoreB2F
       (Def: CLIGHT_SEPARATION_HOARE_LOGIC_DEF)
       (Conseq: CLIGHT_SEPARATION_HOARE_LOGIC_CONSEQUENCE with Module CSHL_Def := Def)
       (StoreB: CLIGHT_SEPARATION_HOARE_LOGIC_STORE_BACKWARD with Module CSHL_Def := Def):
       CLIGHT_SEPARATION_HOARE_LOGIC_STORE_FORWARD with Module CSHL_Def := Def.

Module CSHL_Def := Def.
Module ConseqFacts := GenConseqFacts (Def) (Conseq).
Import Def.
Import Conseq.
Import ConseqFacts.
Import StoreB.

Theorem semax_store_forward:
  forall {CS: compspecs} {Espec: OracleKind} (Delta: tycontext),
 forall e1 e2 sh P,
   writable_share sh ->
   @semax CS Espec Delta
          (|> ( (tc_lvalue Delta e1) &&  (tc_expr Delta (Ecast e2 (typeof e1)))  &&
             (`(mapsto_ sh (typeof e1)) (eval_lvalue e1) * P)))
          (Sassign e1 e2)
          (normal_ret_assert
             (`(mapsto sh (typeof e1)) (eval_lvalue e1) (`force_val (`(sem_cast (typeof e2) (typeof e1)) (eval_expr e2))) * P)).
Admitted.

End StoreB2F.

Module Type CLIGHT_SEPARATION_HOARE_LOGIC_STORE_UNION_HACK_FORWARD.

Declare Module CSHL_Def: CLIGHT_SEPARATION_HOARE_LOGIC_DEF.

Import CSHL_Def.

Axiom semax_store_union_hack_forward:
  forall {CS: compspecs} {Espec: OracleKind} (Delta: tycontext),
 forall (e1 e2 : expr) (t2: type) (ch ch' : memory_chunk) (sh : share) (P : LiftEnviron mpred),
       (numeric_type (typeof e1) && numeric_type t2)%bool = true ->
       access_mode (typeof e1) = By_value ch ->
       access_mode t2 = By_value ch' ->
       decode_encode_val_ok ch ch' ->
       writable_share sh ->
       semax Delta
         (|> (tc_lvalue Delta e1 && tc_expr Delta (Ecast e2 (typeof e1)) &&
              ((`(mapsto_ sh (typeof e1)) (eval_lvalue e1)
                && `(mapsto_ sh t2) (eval_lvalue e1))
               * P)))
         (Sassign e1 e2)
         (normal_ret_assert
            (EX v':val,
              andp (local  ((`decode_encode_val )
                         ((` force_val) ((`(sem_cast (typeof e2) (typeof e1))) (eval_expr e2))) (`ch) (`ch') (`v') ))
              ((` (mapsto sh t2)) (eval_lvalue e1) (`v') * P))).

End CLIGHT_SEPARATION_HOARE_LOGIC_STORE_UNION_HACK_FORWARD.

Module Type CLIGHT_SEPARATION_HOARE_LOGIC_STORE_UNION_HACK_BACKWARD.

Declare Module CSHL_Def: CLIGHT_SEPARATION_HOARE_LOGIC_DEF.

Import CSHL_Def.

Axiom semax_store_union_hack_backward:
 forall {CS: compspecs} {Espec: OracleKind} (Delta: tycontext) e1 e2 P,
   @semax CS Espec Delta
          (EX (t2:type) (ch ch': memory_chunk) (sh: share),
             !! ((numeric_type (typeof e1) && numeric_type t2)%bool = true /\
                 access_mode (typeof e1) = By_value ch /\
                 access_mode t2 = By_value ch' /\
                 decode_encode_val_ok ch ch' /\
                 writable_share sh) &&
             |> ( (tc_lvalue Delta e1) &&  (tc_expr Delta (Ecast e2 (typeof e1)))  &&
             ((`(mapsto_ sh (typeof e1)) (eval_lvalue e1)
                      && `(mapsto_ sh t2) (eval_lvalue e1)) *
              (ALL v': val,
                 `(mapsto sh t2) (eval_lvalue e1) (`v') -*
                  imp (local  ((`decode_encode_val )
                         ((` force_val) ((`(sem_cast (typeof e2) (typeof e1))) (eval_expr e2))) (`ch) (`ch') (`v') ))
                      (  P)))))
          (Sassign e1 e2)
          (normal_ret_assert P).

End CLIGHT_SEPARATION_HOARE_LOGIC_STORE_UNION_HACK_BACKWARD.

Module StoreUnionHackF2B
       (Def: CLIGHT_SEPARATION_HOARE_LOGIC_DEF)
       (Conseq: CLIGHT_SEPARATION_HOARE_LOGIC_CONSEQUENCE with Module CSHL_Def := Def)
       (Extr: CLIGHT_SEPARATION_HOARE_LOGIC_EXTRACTION with Module CSHL_Def := Def)
       (StoreUnionHackF: CLIGHT_SEPARATION_HOARE_LOGIC_STORE_UNION_HACK_FORWARD with Module CSHL_Def := Def):
       CLIGHT_SEPARATION_HOARE_LOGIC_STORE_UNION_HACK_BACKWARD with Module CSHL_Def := Def.

Module CSHL_Def := Def.
Module ConseqFacts := GenConseqFacts (Def) (Conseq).
Module ExtrFacts := GenExtrFacts (Def) (Conseq) (Extr).
Import Def.
Import Conseq.
Import ConseqFacts.
Import Extr.
Import ExtrFacts.
Import StoreUnionHackF.

Theorem semax_store_union_hack_backward:
 forall {CS: compspecs} {Espec: OracleKind} (Delta: tycontext) e1 e2 P,
   @semax CS Espec Delta
          (EX (t2:type) (ch ch': memory_chunk) (sh: share),
             !! ((numeric_type (typeof e1) && numeric_type t2)%bool = true /\
                 access_mode (typeof e1) = By_value ch /\
                 access_mode t2 = By_value ch' /\
                 decode_encode_val_ok ch ch' /\
                 writable_share sh) &&
             |> ( (tc_lvalue Delta e1) &&  (tc_expr Delta (Ecast e2 (typeof e1)))  &&
             ((`(mapsto_ sh (typeof e1)) (eval_lvalue e1)
                      && `(mapsto_ sh t2) (eval_lvalue e1)) *
              (ALL v': val,
                 `(mapsto sh t2) (eval_lvalue e1) (`v') -*
                    imp (local  ((`decode_encode_val )
                         ((` force_val) ((`(sem_cast (typeof e2) (typeof e1))) (eval_expr e2))) (`ch) (`ch') (`v') ))
                      (P)))))
          (Sassign e1 e2)
          (normal_ret_assert P).
Admitted.

End StoreUnionHackF2B.

Module StoreUnionHackB2F
       (Def: CLIGHT_SEPARATION_HOARE_LOGIC_DEF)
       (Conseq: CLIGHT_SEPARATION_HOARE_LOGIC_CONSEQUENCE with Module CSHL_Def := Def)
       (StoreUnionHackB: CLIGHT_SEPARATION_HOARE_LOGIC_STORE_UNION_HACK_BACKWARD with Module CSHL_Def := Def):
       CLIGHT_SEPARATION_HOARE_LOGIC_STORE_UNION_HACK_FORWARD with Module CSHL_Def := Def.

Module CSHL_Def := Def.
Module ConseqFacts := GenConseqFacts (Def) (Conseq).
Import Def.
Import Conseq.
Import ConseqFacts.
Import StoreUnionHackB.

Theorem semax_store_union_hack_forward:
  forall {CS: compspecs} {Espec: OracleKind} (Delta: tycontext),
 forall (e1 e2 : expr) (t2: type) (ch ch' : memory_chunk) (sh : share) (P : LiftEnviron mpred),
       (numeric_type (typeof e1) && numeric_type t2)%bool = true ->
       access_mode (typeof e1) = By_value ch ->
       access_mode t2 = By_value ch' ->
       decode_encode_val_ok ch ch' ->
       writable_share sh ->
       semax Delta
         (|> (tc_lvalue Delta e1 && tc_expr Delta (Ecast e2 (typeof e1)) &&
              ((`(mapsto_ sh (typeof e1)) (eval_lvalue e1)
                && `(mapsto_ sh t2) (eval_lvalue e1))
               * P)))
         (Sassign e1 e2)
         (normal_ret_assert
            (EX v':val,
              andp (local  ((`decode_encode_val )
                         ((` force_val) ((`(sem_cast (typeof e2) (typeof e1))) (eval_expr e2))) (`ch) (`ch') (`v') ))
              ((` (mapsto sh t2)) (eval_lvalue e1) (`v') * P))).
Admitted.

End StoreUnionHackB2F.

Module Type CLIGHT_SEPARATION_HOARE_LOGIC_SASSIGN_BACKWARD.

Declare Module CSHL_Def: CLIGHT_SEPARATION_HOARE_LOGIC_DEF.

Import CSHL_Def.

Axiom semax_store_store_union_hack_backward: forall {CS: compspecs} {Espec: OracleKind} (Delta: tycontext),
  forall (P: environ->mpred) e1 e2,
    @semax CS Espec Delta
       ((EX sh: share, !! writable_share sh &&
             |> ( (tc_lvalue Delta e1) &&  (tc_expr Delta (Ecast e2 (typeof e1)))  &&
             ((`(mapsto_ sh (typeof e1)) (eval_lvalue e1)) *
              (`(mapsto sh (typeof e1)) (eval_lvalue e1) (`force_val (`(sem_cast (typeof e2) (typeof e1)) (eval_expr e2))) -* P))))
          || (EX (t2:type) (ch ch': memory_chunk) (sh: share),
             !! ((numeric_type (typeof e1) && numeric_type t2)%bool = true /\
                 access_mode (typeof e1) = By_value ch /\
                 access_mode t2 = By_value ch' /\
                 decode_encode_val_ok ch ch' /\
                 writable_share sh) &&
             |> ( (tc_lvalue Delta e1) &&  (tc_expr Delta (Ecast e2 (typeof e1)))  &&
             ((`(mapsto_ sh (typeof e1)) (eval_lvalue e1)
                      && `(mapsto_ sh t2) (eval_lvalue e1)) *
              (ALL v': val,
                 `(mapsto sh t2) (eval_lvalue e1) (`v') -*
                    imp (local  ((`decode_encode_val )
                         ((` force_val) ((`(sem_cast (typeof e2) (typeof e1))) (eval_expr e2))) (`ch) (`ch') (`v') ))
                      (P)))))
       )
        (Sassign e1 e2) (normal_ret_assert P).

End CLIGHT_SEPARATION_HOARE_LOGIC_SASSIGN_BACKWARD.

Module ToSassign
       (Def: CLIGHT_SEPARATION_HOARE_LOGIC_DEF)
       (Conseq: CLIGHT_SEPARATION_HOARE_LOGIC_CONSEQUENCE with Module CSHL_Def := Def)
       (Extr: CLIGHT_SEPARATION_HOARE_LOGIC_EXTRACTION with Module CSHL_Def := Def)
       (StoreB: CLIGHT_SEPARATION_HOARE_LOGIC_STORE_BACKWARD with Module CSHL_Def := Def)
       (StoreUnionHackB: CLIGHT_SEPARATION_HOARE_LOGIC_STORE_UNION_HACK_BACKWARD with Module CSHL_Def := Def):
       CLIGHT_SEPARATION_HOARE_LOGIC_SASSIGN_BACKWARD with Module CSHL_Def := Def.

Module CSHL_Def := Def.
Module ConseqFacts := GenConseqFacts (Def) (Conseq).
Module ExtrFacts := GenExtrFacts (Def) (Conseq) (Extr).

Import Def.
Import Conseq.
Import ConseqFacts.
Import StoreB.
Import StoreUnionHackB.
Import ExtrFacts.

Theorem semax_store_store_union_hack_backward: forall {CS: compspecs} {Espec: OracleKind} (Delta: tycontext),
  forall (P: environ->mpred) e1 e2,
    @semax CS Espec Delta
       ((EX sh: share, !! writable_share sh &&
             |> ( (tc_lvalue Delta e1) &&  (tc_expr Delta (Ecast e2 (typeof e1)))  &&
             ((`(mapsto_ sh (typeof e1)) (eval_lvalue e1)) *
              (`(mapsto sh (typeof e1)) (eval_lvalue e1) (`force_val (`(sem_cast (typeof e2) (typeof e1)) (eval_expr e2))) -* P))))
          || (EX (t2:type) (ch ch': memory_chunk) (sh: share),
             !! ((numeric_type (typeof e1) && numeric_type t2)%bool = true /\
                 access_mode (typeof e1) = By_value ch /\
                 access_mode t2 = By_value ch' /\
                 decode_encode_val_ok ch ch' /\
                 writable_share sh) &&
             |> ( (tc_lvalue Delta e1) &&  (tc_expr Delta (Ecast e2 (typeof e1)))  &&
             ((`(mapsto_ sh (typeof e1)) (eval_lvalue e1)
                      && `(mapsto_ sh t2) (eval_lvalue e1)) *
              (ALL v': val,
                 `(mapsto sh t2) (eval_lvalue e1) (`v') -*
                    imp (local  ((`decode_encode_val )
                         ((` force_val) ((`(sem_cast (typeof e2) (typeof e1))) (eval_expr e2))) (`ch) (`ch') (`v') ))
                      (P)))))
       )
        (Sassign e1 e2) (normal_ret_assert P).
Admitted.

End ToSassign.

Module Sassign2Store
       (Def: CLIGHT_SEPARATION_HOARE_LOGIC_DEF)
       (Conseq: CLIGHT_SEPARATION_HOARE_LOGIC_CONSEQUENCE with Module CSHL_Def := Def)
       (Sassign: CLIGHT_SEPARATION_HOARE_LOGIC_SASSIGN_BACKWARD with Module CSHL_Def := Def):
       CLIGHT_SEPARATION_HOARE_LOGIC_STORE_BACKWARD with Module CSHL_Def := Def.

Module CSHL_Def := Def.
Module ConseqFacts := GenConseqFacts (Def) (Conseq).

Import Def.
Import Conseq.
Import ConseqFacts.
Import Sassign.

Theorem semax_store_backward: forall {CS: compspecs} {Espec: OracleKind} (Delta: tycontext) e1 e2 P,
   @semax CS Espec Delta
          (EX sh: share, !! writable_share sh && |> ( (tc_lvalue Delta e1) &&  (tc_expr Delta (Ecast e2 (typeof e1)))  &&
             ((`(mapsto_ sh (typeof e1)) (eval_lvalue e1)) * (`(mapsto sh (typeof e1)) (eval_lvalue e1) (`force_val (`(sem_cast (typeof e2) (typeof e1)) (eval_expr e2))) -* P))))
          (Sassign e1 e2)
          (normal_ret_assert P).
Admitted.

End Sassign2Store.

Module Sassign2StoreUnionHack
       (Def: CLIGHT_SEPARATION_HOARE_LOGIC_DEF)
       (Conseq: CLIGHT_SEPARATION_HOARE_LOGIC_CONSEQUENCE with Module CSHL_Def := Def)
       (Sassign: CLIGHT_SEPARATION_HOARE_LOGIC_SASSIGN_BACKWARD with Module CSHL_Def := Def):
       CLIGHT_SEPARATION_HOARE_LOGIC_STORE_UNION_HACK_BACKWARD with Module CSHL_Def := Def.

Module CSHL_Def := Def.
Module ConseqFacts := GenConseqFacts (Def) (Conseq).

Import Def.
Import Conseq.
Import ConseqFacts.
Import Sassign.

Theorem semax_store_union_hack_backward:
 forall {CS: compspecs} {Espec: OracleKind} (Delta: tycontext) e1 e2 P,
   @semax CS Espec Delta
          (EX (t2:type) (ch ch': memory_chunk) (sh: share),
             !! ((numeric_type (typeof e1) && numeric_type t2)%bool = true /\
                 access_mode (typeof e1) = By_value ch /\
                 access_mode t2 = By_value ch' /\
                 decode_encode_val_ok ch ch' /\
                 writable_share sh) &&
             |> ( (tc_lvalue Delta e1) &&  (tc_expr Delta (Ecast e2 (typeof e1)))  &&
             ((`(mapsto_ sh (typeof e1)) (eval_lvalue e1)
                      && `(mapsto_ sh t2) (eval_lvalue e1)) *
              (ALL v': val,
                 `(mapsto sh t2) (eval_lvalue e1) (`v') -*
                    imp (local  ((`decode_encode_val )
                         ((` force_val) ((`(sem_cast (typeof e2) (typeof e1))) (eval_expr e2))) (`ch) (`ch') (`v') ))
                      (P)))))
          (Sassign e1 e2)
          (normal_ret_assert P).
Admitted.

End Sassign2StoreUnionHack.

Module Type CLIGHT_SEPARATION_HOARE_LOGIC_CALL_FORWARD.

Declare Module CSHL_Def: CLIGHT_SEPARATION_HOARE_LOGIC_DEF.

Import CSHL_Def.

Axiom semax_call_forward: forall {CS: compspecs} {Espec: OracleKind} (Delta: tycontext),
    forall A P Q NEP NEQ ts x (F: environ -> mpred) ret argsig retsig cc a bl,
           Cop.classify_fun (typeof a) =
           Cop.fun_case_f (typelist_of_type_list argsig) retsig cc ->
           (retsig = Ctypes.Tvoid -> ret = None) ->
          tc_fn_return Delta ret retsig ->
  @semax CS Espec Delta
          (( ((tc_expr Delta a) && (tc_exprlist Delta argsig bl)))  &&
         (`(func_ptr (mk_funspec  (argsig,retsig) cc A P Q NEP NEQ)) (eval_expr a) &&
          (|> (F * (fun rho => P ts x (ge_of rho, eval_exprlist argsig bl rho))))))
         (Scall ret a bl)
         (normal_ret_assert
            (EX old:val, substopt ret (`old) F * maybe_retval (Q ts x) retsig ret)).

End CLIGHT_SEPARATION_HOARE_LOGIC_CALL_FORWARD.

Module Type CLIGHT_SEPARATION_HOARE_LOGIC_CALL_BACKWARD.

Declare Module CSHL_Def: CLIGHT_SEPARATION_HOARE_LOGIC_DEF.

Import CSHL_Def.

Axiom semax_call_backward: forall {CS: compspecs} {Espec: OracleKind} (Delta: tycontext),
    forall ret a bl R,
  @semax CS Espec Delta
         (EX argsig: _, EX retsig: _, EX cc: _,
          EX A: _, EX P: _, EX Q: _, EX NEP: _, EX NEQ: _, EX ts: _, EX x: _,
         !! (Cop.classify_fun (typeof a) =
             Cop.fun_case_f (typelist_of_type_list argsig) retsig cc /\
             (retsig = Ctypes.Tvoid -> ret = None) /\
             tc_fn_return Delta ret retsig) &&
          ( ((tc_expr Delta a) && (tc_exprlist Delta argsig bl)))  &&
         `(func_ptr (mk_funspec  (argsig,retsig) cc A P Q NEP NEQ)) (eval_expr a) &&
          |>((fun rho => (P ts x (ge_of rho, eval_exprlist argsig bl rho))) * oboxopt Delta ret (maybe_retval (Q ts x) retsig ret -* R)))
         (Scall ret a bl)
         (normal_ret_assert R).

End CLIGHT_SEPARATION_HOARE_LOGIC_CALL_BACKWARD.

Module CallF2B
       (Def: CLIGHT_SEPARATION_HOARE_LOGIC_DEF)
       (Conseq: CLIGHT_SEPARATION_HOARE_LOGIC_CONSEQUENCE with Module CSHL_Def := Def)
       (Extr: CLIGHT_SEPARATION_HOARE_LOGIC_EXTRACTION with Module CSHL_Def := Def)
       (CallF: CLIGHT_SEPARATION_HOARE_LOGIC_CALL_FORWARD with Module CSHL_Def := Def):
       CLIGHT_SEPARATION_HOARE_LOGIC_CALL_BACKWARD with Module CSHL_Def := Def.

Module CSHL_Def := Def.
Module ConseqFacts := GenConseqFacts (Def) (Conseq).
Module ExtrFacts := GenExtrFacts (Def) (Conseq) (Extr).
Import Def.
Import Conseq.
Import ConseqFacts.
Import Extr.
Import ExtrFacts.
Import CallF.

Theorem semax_call_backward: forall {CS: compspecs} {Espec: OracleKind} (Delta: tycontext),
    forall ret a bl R,
  @semax CS Espec Delta
         (EX argsig: _, EX retsig: _, EX cc: _,
          EX A: _, EX P: _, EX Q: _, EX NEP: _, EX NEQ: _, EX ts: _, EX x: _,
         !! (Cop.classify_fun (typeof a) =
             Cop.fun_case_f (typelist_of_type_list argsig) retsig cc /\
             (retsig = Ctypes.Tvoid -> ret = None) /\
             tc_fn_return Delta ret retsig) &&
          ( ((tc_expr Delta a) && (tc_exprlist Delta argsig bl)))  &&
         `(func_ptr (mk_funspec  (argsig,retsig) cc A P Q NEP NEQ)) (eval_expr a) &&
          |>((fun rho => P ts x (ge_of rho, eval_exprlist argsig bl rho)) * oboxopt Delta ret (maybe_retval (Q ts x) retsig ret -* R)))
         (Scall ret a bl)
         (normal_ret_assert R).
Admitted.

End CallF2B.

Module CallB2F
       (Def: CLIGHT_SEPARATION_HOARE_LOGIC_DEF)
       (Conseq: CLIGHT_SEPARATION_HOARE_LOGIC_CONSEQUENCE with Module CSHL_Def := Def)
       (CallB: CLIGHT_SEPARATION_HOARE_LOGIC_CALL_BACKWARD with Module CSHL_Def := Def):
       CLIGHT_SEPARATION_HOARE_LOGIC_CALL_FORWARD with Module CSHL_Def := Def.

Module CSHL_Def := Def.
Module ConseqFacts := GenConseqFacts (Def) (Conseq).
Import Def.
Import Conseq.
Import ConseqFacts.
Import CallB.
 
Theorem semax_call_forward: forall {CS: compspecs} {Espec: OracleKind} (Delta: tycontext),
    forall A P Q NEP NEQ ts x (F: environ -> mpred) ret argsig retsig cc a bl,
           Cop.classify_fun (typeof a) =
             Cop.fun_case_f (typelist_of_type_list argsig) retsig cc ->
           (retsig = Ctypes.Tvoid -> ret = None) ->
          tc_fn_return Delta ret retsig ->
  @semax CS Espec Delta
          (( ((tc_expr Delta a) && (tc_exprlist Delta argsig bl)))  &&
         (`(func_ptr (mk_funspec  (argsig,retsig) cc A P Q NEP NEQ)) (eval_expr a) &&
          |>(F * (fun rho => P ts x (ge_of rho, eval_exprlist argsig bl rho)))))
         (Scall ret a bl)
         (normal_ret_assert
            (EX old:val, substopt ret (`old) F * maybe_retval (Q ts x) retsig ret)).
Admitted.

End CallB2F.

Module Type CLIGHT_SEPARATION_HOARE_LOGIC_SET_FORWARD.

Declare Module CSHL_Def: CLIGHT_SEPARATION_HOARE_LOGIC_DEF.

Import CSHL_Def.

Axiom semax_set_forward: forall {CS: compspecs} {Espec: OracleKind} (Delta: tycontext),
  forall (P: environ->mpred) id e,
    @semax CS Espec Delta
        (|> ( (tc_expr Delta e) &&
             (tc_temp_id id (typeof e) Delta e) &&
          P))
          (Sset id e)
        (normal_ret_assert
          (EX old:val, local (`eq (eval_id id) (subst id (`old) (eval_expr e))) &&
                            subst id (`old) P)).

End CLIGHT_SEPARATION_HOARE_LOGIC_SET_FORWARD.

Module Type CLIGHT_SEPARATION_HOARE_LOGIC_SET_BACKWARD.

Declare Module CSHL_Def: CLIGHT_SEPARATION_HOARE_LOGIC_DEF.

Import CSHL_Def.

Axiom semax_set_backward: forall {CS: compspecs} {Espec: OracleKind} (Delta: tycontext),
  forall (P: environ->mpred) id e,
    @semax CS Espec Delta
        (|> ( (tc_expr Delta e) &&
             (tc_temp_id id (typeof e) Delta e) &&
             subst id (eval_expr e) P))
          (Sset id e) (normal_ret_assert P).

End CLIGHT_SEPARATION_HOARE_LOGIC_SET_BACKWARD.

Module Type CLIGHT_SEPARATION_HOARE_LOGIC_LOAD_FORWARD.

Declare Module CSHL_Def: CLIGHT_SEPARATION_HOARE_LOGIC_DEF.

Import CSHL_Def.

Axiom semax_load_forward: forall {CS: compspecs} {Espec: OracleKind} (Delta: tycontext),
  forall  sh id P e1 t2 (v2: val),
    typeof_temp Delta id = Some t2 ->
    is_neutral_cast (typeof e1) t2 = true ->
    readable_share sh ->
    (local (tc_environ Delta) && P |-- `(mapsto sh (typeof e1)) (eval_lvalue e1) (` v2) * TT) ->
    @semax CS Espec Delta
       (|> ( (tc_lvalue Delta e1) &&
       local (`(tc_val (typeof e1) v2)) &&
          P))
       (Sset id e1)
       (normal_ret_assert (EX old:val, local (`eq (eval_id id) (` v2)) &&
                                          (subst id (`old) P))).

End CLIGHT_SEPARATION_HOARE_LOGIC_LOAD_FORWARD.

Module Type CLIGHT_SEPARATION_HOARE_LOGIC_LOAD_BACKWARD.

Declare Module CSHL_Def: CLIGHT_SEPARATION_HOARE_LOGIC_DEF.

Import CSHL_Def.

Axiom semax_load_backward: forall {CS: compspecs} {Espec: OracleKind} (Delta: tycontext),
  forall (P: environ->mpred) id e1,
    @semax CS Espec Delta
        (EX sh: share, EX t2: type, EX v2: val,
              !! (typeof_temp Delta id = Some t2 /\
                  is_neutral_cast (typeof e1) t2 = true /\
                  readable_share sh) &&
         |> ( (tc_lvalue Delta e1) &&
              local (`(tc_val (typeof e1) v2)) &&
              (`(mapsto sh (typeof e1)) (eval_lvalue e1) (`v2) * TT) &&
              subst id (`v2) P))
        (Sset id e1) (normal_ret_assert P).

End CLIGHT_SEPARATION_HOARE_LOGIC_LOAD_BACKWARD.

Module Type CLIGHT_SEPARATION_HOARE_LOGIC_CAST_LOAD_FORWARD.

Declare Module CSHL_Def: CLIGHT_SEPARATION_HOARE_LOGIC_DEF.

Import CSHL_Def.

Axiom semax_cast_load_forward: forall {CS: compspecs} {Espec: OracleKind} (Delta: tycontext),
  forall sh id P e1 t1 (v2: val),
    typeof_temp Delta id = Some t1 ->
   cast_pointer_to_bool (typeof e1) t1 = false ->
    readable_share sh ->
    (local (tc_environ Delta) && P |-- `(mapsto sh (typeof e1)) (eval_lvalue e1) (`v2) * TT) ->
    @semax CS Espec Delta
       (|> ( (tc_lvalue Delta e1) &&
       local (`(tc_val t1) (`(eval_cast (typeof e1) t1 v2))) &&
          P))
       (Sset id (Ecast e1 t1))
       (normal_ret_assert (EX old:val, local (`eq (eval_id id) (subst id (`old) (`(eval_cast (typeof e1) t1 v2)))) &&
                                          (subst id (`old) P))).

End CLIGHT_SEPARATION_HOARE_LOGIC_CAST_LOAD_FORWARD.

Module Type CLIGHT_SEPARATION_HOARE_LOGIC_CAST_LOAD_BACKWARD.

Declare Module CSHL_Def: CLIGHT_SEPARATION_HOARE_LOGIC_DEF.

Import CSHL_Def.

Axiom semax_cast_load_backward: forall {CS: compspecs} {Espec: OracleKind} (Delta: tycontext),
  forall (P: environ->mpred) id e,
    @semax CS Espec Delta
        (EX sh: share, EX e1: expr, EX t1: type, EX v2: val,
              !! (e = Ecast e1 t1 /\
                  typeof_temp Delta id = Some t1 /\
                  cast_pointer_to_bool (typeof e1) t1 = false /\
                  readable_share sh) &&
         |> ( (tc_lvalue Delta e1) &&
              local (`(tc_val t1) (`(eval_cast (typeof e1) t1 v2))) &&
              (`(mapsto sh (typeof e1)) (eval_lvalue e1) (`v2) * TT) &&
              subst id (`(force_val (sem_cast (typeof e1) t1 v2))) P))
        (Sset id e) (normal_ret_assert P).

End CLIGHT_SEPARATION_HOARE_LOGIC_CAST_LOAD_BACKWARD.

Module LoadF2B
       (Def: CLIGHT_SEPARATION_HOARE_LOGIC_DEF)
       (Conseq: CLIGHT_SEPARATION_HOARE_LOGIC_CONSEQUENCE with Module CSHL_Def := Def)
       (Extr: CLIGHT_SEPARATION_HOARE_LOGIC_EXTRACTION with Module CSHL_Def := Def)
       (LoadF: CLIGHT_SEPARATION_HOARE_LOGIC_LOAD_FORWARD with Module CSHL_Def := Def):
       CLIGHT_SEPARATION_HOARE_LOGIC_LOAD_BACKWARD with Module CSHL_Def := Def.

Module CSHL_Def := Def.
Module ConseqFacts := GenConseqFacts (Def) (Conseq).
Module ExtrFacts := GenExtrFacts (Def) (Conseq) (Extr).
Import Def.
Import Conseq.
Import ConseqFacts.
Import Extr.
Import ExtrFacts.
Import LoadF.

Theorem semax_load_backward: forall {CS: compspecs} {Espec: OracleKind} (Delta: tycontext),
  forall (P: environ->mpred) id e1,
    @semax CS Espec Delta
        (EX sh: share, EX t2: type, EX v2: val,
              !! (typeof_temp Delta id = Some t2 /\
                  is_neutral_cast (typeof e1) t2 = true /\
                  readable_share sh) &&
         |> ( (tc_lvalue Delta e1) &&
              local (`(tc_val (typeof e1) v2)) &&
              (`(mapsto sh (typeof e1)) (eval_lvalue e1) (`v2) * TT) &&
              subst id (`v2) P))
        (Sset id e1) (normal_ret_assert P).
Admitted.

End LoadF2B.

Module LoadB2F
       (Def: CLIGHT_SEPARATION_HOARE_LOGIC_DEF)
       (Conseq: CLIGHT_SEPARATION_HOARE_LOGIC_CONSEQUENCE with Module CSHL_Def := Def)
       (LoadB: CLIGHT_SEPARATION_HOARE_LOGIC_LOAD_BACKWARD with Module CSHL_Def := Def):
       CLIGHT_SEPARATION_HOARE_LOGIC_LOAD_FORWARD with Module CSHL_Def := Def.

Module CSHL_Def := Def.
Module ConseqFacts := GenConseqFacts (Def) (Conseq).
Import Def.
Import Conseq.
Import ConseqFacts.
Import LoadB.

Theorem semax_load_forward: forall {CS: compspecs} {Espec: OracleKind} (Delta: tycontext),
  forall  sh id P e1 t2 (v2: val),
    typeof_temp Delta id = Some t2 ->
    is_neutral_cast (typeof e1) t2 = true ->
    readable_share sh ->
    (local (tc_environ Delta) && P |-- `(mapsto sh (typeof e1)) (eval_lvalue e1) (` v2) * TT) ->
    @semax CS Espec Delta
       (|> ( (tc_lvalue Delta e1) &&
       local (`(tc_val (typeof e1) v2)) &&
          P))
       (Sset id e1)
       (normal_ret_assert (EX old:val, local (`eq (eval_id id) (` v2)) &&
                                          (subst id (`old) P))).
Admitted.

End LoadB2F.

Module CastLoadF2B
       (Def: CLIGHT_SEPARATION_HOARE_LOGIC_DEF)
       (Conseq: CLIGHT_SEPARATION_HOARE_LOGIC_CONSEQUENCE with Module CSHL_Def := Def)
       (Extr: CLIGHT_SEPARATION_HOARE_LOGIC_EXTRACTION with Module CSHL_Def := Def)
       (CastLoadF: CLIGHT_SEPARATION_HOARE_LOGIC_CAST_LOAD_FORWARD with Module CSHL_Def := Def):
       CLIGHT_SEPARATION_HOARE_LOGIC_CAST_LOAD_BACKWARD with Module CSHL_Def := Def.

Module CSHL_Def := Def.
Module ConseqFacts := GenConseqFacts (Def) (Conseq).
Module ExtrFacts := GenExtrFacts (Def) (Conseq) (Extr).
Import Def.
Import Conseq.
Import ConseqFacts.
Import Extr.
Import ExtrFacts.
Import CastLoadF.

Theorem semax_cast_load_backward: forall {CS: compspecs} {Espec: OracleKind} (Delta: tycontext),
  forall (P: environ->mpred) id e,
    @semax CS Espec Delta
        (EX sh: share, EX e1: expr, EX t1: type, EX v2: val,
              !! (e = Ecast e1 t1 /\
                  typeof_temp Delta id = Some t1 /\
                  cast_pointer_to_bool (typeof e1) t1 = false /\
                  readable_share sh) &&
         |> ( (tc_lvalue Delta e1) &&
              local (`(tc_val t1) (`(eval_cast (typeof e1) t1 v2))) &&
              (`(mapsto sh (typeof e1)) (eval_lvalue e1) (`v2) * TT) &&
              subst id (`(force_val (sem_cast (typeof e1) t1 v2))) P))
        (Sset id e) (normal_ret_assert P).
Admitted.

End CastLoadF2B.

Module CastLoadB2F
       (Def: CLIGHT_SEPARATION_HOARE_LOGIC_DEF)
       (Conseq: CLIGHT_SEPARATION_HOARE_LOGIC_CONSEQUENCE with Module CSHL_Def := Def)
       (CastLoadB: CLIGHT_SEPARATION_HOARE_LOGIC_CAST_LOAD_BACKWARD with Module CSHL_Def := Def):
       CLIGHT_SEPARATION_HOARE_LOGIC_CAST_LOAD_FORWARD with Module CSHL_Def := Def.

Module CSHL_Def := Def.
Module ConseqFacts := GenConseqFacts (Def) (Conseq).
Import Def.
Import Conseq.
Import ConseqFacts.
Import CastLoadB.

Theorem semax_cast_load_forward: forall {CS: compspecs} {Espec: OracleKind} (Delta: tycontext),
  forall sh id P e1 t1 (v2: val),
    typeof_temp Delta id = Some t1 ->
   cast_pointer_to_bool (typeof e1) t1 = false ->
    readable_share sh ->
    (local (tc_environ Delta) && P |-- `(mapsto sh (typeof e1)) (eval_lvalue e1) (`v2) * TT) ->
    @semax CS Espec Delta
       (|> ( (tc_lvalue Delta e1) &&
       local (`(tc_val t1) (`(eval_cast (typeof e1) t1 v2))) &&
          P))
       (Sset id (Ecast e1 t1))
       (normal_ret_assert (EX old:val, local (`eq (eval_id id) (subst id (`old) (`(eval_cast (typeof e1) t1 v2)))) &&
                                          (subst id (`old) P))).
Admitted.

End CastLoadB2F.

Module SetF2B
       (Def: CLIGHT_SEPARATION_HOARE_LOGIC_DEF)
       (Conseq: CLIGHT_SEPARATION_HOARE_LOGIC_CONSEQUENCE with Module CSHL_Def := Def)
       (Extr: CLIGHT_SEPARATION_HOARE_LOGIC_EXTRACTION with Module CSHL_Def := Def)
       (SetF: CLIGHT_SEPARATION_HOARE_LOGIC_SET_FORWARD with Module CSHL_Def := Def):
       CLIGHT_SEPARATION_HOARE_LOGIC_SET_BACKWARD with Module CSHL_Def := Def.

Module CSHL_Def := Def.
Module ConseqFacts := GenConseqFacts (Def) (Conseq).
Module ExtrFacts := GenExtrFacts (Def) (Conseq) (Extr).
Import Def.
Import Conseq.
Import ConseqFacts.
Import Extr.
Import ExtrFacts.
Import SetF.

Theorem semax_set_backward: forall {CS: compspecs} {Espec: OracleKind} (Delta: tycontext),
  forall (P: environ->mpred) id e,
    @semax CS Espec Delta
        (|> ( (tc_expr Delta e) &&
             (tc_temp_id id (typeof e) Delta e) &&
             subst id (eval_expr e) P))
          (Sset id e) (normal_ret_assert P).
Admitted.

End SetF2B.

Module SetB2F
       (Def: CLIGHT_SEPARATION_HOARE_LOGIC_DEF)
       (Conseq: CLIGHT_SEPARATION_HOARE_LOGIC_CONSEQUENCE with Module CSHL_Def := Def)
       (SetB: CLIGHT_SEPARATION_HOARE_LOGIC_SET_BACKWARD with Module CSHL_Def := Def):
       CLIGHT_SEPARATION_HOARE_LOGIC_SET_FORWARD with Module CSHL_Def := Def.

Module CSHL_Def := Def.
Module ConseqFacts := GenConseqFacts (Def) (Conseq).
Import Def.
Import Conseq.
Import ConseqFacts.
Import SetB.

Theorem semax_set_forward: forall {CS: compspecs} {Espec: OracleKind} (Delta: tycontext),
  forall (P: environ->mpred) id e,
    @semax CS Espec Delta
        (|> ( (tc_expr Delta e) &&
             (tc_temp_id id (typeof e) Delta e) &&
          P))
          (Sset id e)
        (normal_ret_assert
          (EX old:val, local (`eq (eval_id id) (subst id (`old) (eval_expr e))) &&
                            subst id (`old) P)).
Admitted.

End SetB2F.

Module Type CLIGHT_SEPARATION_HOARE_LOGIC_PTR_CMP_FORWARD.

Declare Module CSHL_Def: CLIGHT_SEPARATION_HOARE_LOGIC_DEF.

Import CSHL_Def.

Axiom semax_ptr_compare_forward: forall {CS: compspecs} {Espec: OracleKind} (Delta: tycontext),
  forall P id cmp e1 e2 ty sh1 sh2,
    sepalg.nonidentity sh1 -> sepalg.nonidentity sh2 ->
   is_comparison cmp = true  ->
   eqb_type (typeof e1) int_or_ptr_type = false ->
   eqb_type (typeof e2) int_or_ptr_type = false ->
   typecheck_tid_ptr_compare Delta id = true ->
   @semax CS Espec Delta
        ( |> ( (tc_expr Delta e1) &&
              (tc_expr Delta e2)  &&

          local (`(blocks_match cmp) (eval_expr e1) (eval_expr e2)) &&
          (`(mapsto_ sh1 (typeof e1)) (eval_expr e1) * TT) &&
          (`(mapsto_ sh2 (typeof e2)) (eval_expr e2) * TT) &&
          P))
          (Sset id (Ebinop cmp e1 e2 ty))
        (normal_ret_assert
          (EX old:val,
                 local (`eq (eval_id id)  (subst id `(old)
                     (eval_expr (Ebinop cmp e1 e2 ty)))) &&
                       subst id `(old) P)).

End CLIGHT_SEPARATION_HOARE_LOGIC_PTR_CMP_FORWARD.

Module Type CLIGHT_SEPARATION_HOARE_LOGIC_PTR_CMP_BACKWARD.

Declare Module CSHL_Def: CLIGHT_SEPARATION_HOARE_LOGIC_DEF.

Import CSHL_Def.

Axiom semax_ptr_compare_backward: forall {CS: compspecs} {Espec: OracleKind} (Delta: tycontext),
  forall P id e,
   @semax CS Espec Delta
        (EX cmp: Cop.binary_operation, EX e1: expr, EX e2: expr,
         EX ty: type, EX sh1: share, EX sh2: share,
          !! (e = Ebinop cmp e1 e2 ty /\
              sepalg.nonidentity sh1 /\ sepalg.nonidentity sh2 /\
              is_comparison cmp = true /\
              eqb_type (typeof e1) int_or_ptr_type = false /\
              eqb_type (typeof e2) int_or_ptr_type = false /\
              typecheck_tid_ptr_compare Delta id = true) &&
            ( |> ( (tc_expr Delta e1) &&
              (tc_expr Delta e2)  &&
          local (`(blocks_match cmp) (eval_expr e1) (eval_expr e2)) &&
          (`(mapsto_ sh1 (typeof e1)) (eval_expr e1) * TT) &&
          (`(mapsto_ sh2 (typeof e2)) (eval_expr e2) * TT) &&
          subst id (eval_expr (Ebinop cmp e1 e2 ty)) P)))
          (Sset id e)
        (normal_ret_assert P).

End CLIGHT_SEPARATION_HOARE_LOGIC_PTR_CMP_BACKWARD.

Module PtrCmpF2B
       (Def: CLIGHT_SEPARATION_HOARE_LOGIC_DEF)
       (Conseq: CLIGHT_SEPARATION_HOARE_LOGIC_CONSEQUENCE with Module CSHL_Def := Def)
       (Extr: CLIGHT_SEPARATION_HOARE_LOGIC_EXTRACTION with Module CSHL_Def := Def)
       (PtrCmpF: CLIGHT_SEPARATION_HOARE_LOGIC_PTR_CMP_FORWARD with Module CSHL_Def := Def):
       CLIGHT_SEPARATION_HOARE_LOGIC_PTR_CMP_BACKWARD with Module CSHL_Def := Def.

Module CSHL_Def := Def.
Module ConseqFacts := GenConseqFacts (Def) (Conseq).
Module ExtrFacts := GenExtrFacts (Def) (Conseq) (Extr).
Import Def.
Import Conseq.
Import ConseqFacts.
Import Extr.
Import ExtrFacts.
Import PtrCmpF.

Theorem semax_ptr_compare_backward: forall {CS: compspecs} {Espec: OracleKind} (Delta: tycontext),
  forall P id e,
   @semax CS Espec Delta
        (EX cmp: Cop.binary_operation, EX e1: expr, EX e2: expr,
         EX ty: type, EX sh1: share, EX sh2: share,
          !! (e = Ebinop cmp e1 e2 ty /\
              sepalg.nonidentity sh1 /\ sepalg.nonidentity sh2 /\
              is_comparison cmp = true /\
              eqb_type (typeof e1) int_or_ptr_type = false /\
              eqb_type (typeof e2) int_or_ptr_type = false /\
              typecheck_tid_ptr_compare Delta id = true) &&
            ( |> ( (tc_expr Delta e1) &&
              (tc_expr Delta e2)  &&
          local (`(blocks_match cmp) (eval_expr e1) (eval_expr e2)) &&
          (`(mapsto_ sh1 (typeof e1)) (eval_expr e1) * TT) &&
          (`(mapsto_ sh2 (typeof e2)) (eval_expr e2) * TT) &&
          subst id (eval_expr (Ebinop cmp e1 e2 ty)) P)))
          (Sset id e)
          (normal_ret_assert P).
Admitted.

End PtrCmpF2B.

Module PtrCmpB2F
       (Def: CLIGHT_SEPARATION_HOARE_LOGIC_DEF)
       (Conseq: CLIGHT_SEPARATION_HOARE_LOGIC_CONSEQUENCE with Module CSHL_Def := Def)
       (PtrCmpB: CLIGHT_SEPARATION_HOARE_LOGIC_PTR_CMP_BACKWARD with Module CSHL_Def := Def):
       CLIGHT_SEPARATION_HOARE_LOGIC_PTR_CMP_FORWARD with Module CSHL_Def := Def.

Module CSHL_Def := Def.
Module ConseqFacts := GenConseqFacts (Def) (Conseq).
Import Def.
Import Conseq.
Import ConseqFacts.
Import PtrCmpB.

Theorem semax_ptr_compare_forward: forall {CS: compspecs} {Espec: OracleKind} (Delta: tycontext),
  forall P id cmp e1 e2 ty sh1 sh2,
    sepalg.nonidentity sh1 -> sepalg.nonidentity sh2 ->
   is_comparison cmp = true  ->
   eqb_type (typeof e1) int_or_ptr_type = false ->
   eqb_type (typeof e2) int_or_ptr_type = false ->
   typecheck_tid_ptr_compare Delta id = true ->
   @semax CS Espec Delta
        ( |> ( (tc_expr Delta e1) &&
              (tc_expr Delta e2)  &&

          local (`(blocks_match cmp) (eval_expr e1) (eval_expr e2)) &&
          (`(mapsto_ sh1 (typeof e1)) (eval_expr e1) * TT) &&
          (`(mapsto_ sh2 (typeof e2)) (eval_expr e2) * TT) &&
          P))
          (Sset id (Ebinop cmp e1 e2 ty))
        (normal_ret_assert
          (EX old:val,
                 local (`eq (eval_id id)  (subst id `(old)
                     (eval_expr (Ebinop cmp e1 e2 ty)))) &&
                       subst id `(old) P)).
Admitted.

End PtrCmpB2F.

Module Type CLIGHT_SEPARATION_HOARE_LOGIC_SSET_BACKWARD.

Declare Module CSHL_Def: CLIGHT_SEPARATION_HOARE_LOGIC_DEF.

Import CSHL_Def.

Axiom semax_set_ptr_compare_load_cast_load_backward: forall {CS: compspecs} {Espec: OracleKind} (Delta: tycontext),
  forall (P: environ->mpred) id e,
    @semax CS Espec Delta
       ((|> ( (tc_expr Delta e) &&
             (tc_temp_id id (typeof e) Delta e) &&
             subst id (eval_expr e) P)) ||
        (EX cmp: Cop.binary_operation, EX e1: expr, EX e2: expr,
         EX ty: type, EX sh1: share, EX sh2: share,
          !! (e = Ebinop cmp e1 e2 ty /\
              sepalg.nonidentity sh1 /\ sepalg.nonidentity sh2 /\
              is_comparison cmp = true /\
              eqb_type (typeof e1) int_or_ptr_type = false /\
              eqb_type (typeof e2) int_or_ptr_type = false /\
              typecheck_tid_ptr_compare Delta id = true) &&
            ( |> ( (tc_expr Delta e1) &&
              (tc_expr Delta e2)  &&
          local (`(blocks_match cmp) (eval_expr e1) (eval_expr e2)) &&
          (`(mapsto_ sh1 (typeof e1)) (eval_expr e1) * TT) &&
          (`(mapsto_ sh2 (typeof e2)) (eval_expr e2) * TT) &&
          subst id (eval_expr (Ebinop cmp e1 e2 ty)) P))) ||
        (EX sh: share, EX t2: type, EX v2: val,
              !! (typeof_temp Delta id = Some t2 /\
                  is_neutral_cast (typeof e) t2 = true /\
                  readable_share sh) &&
         |> ( (tc_lvalue Delta e) &&
              local (`(tc_val (typeof e) v2)) &&
              (`(mapsto sh (typeof e)) (eval_lvalue e) (`v2) * TT) &&
              subst id (`v2) P)) ||
        (EX sh: share, EX e1: expr, EX t1: type, EX v2: val,
              !! (e = Ecast e1 t1 /\
                  typeof_temp Delta id = Some t1 /\
                  cast_pointer_to_bool (typeof e1) t1 = false /\
                  readable_share sh) &&
         |> ( (tc_lvalue Delta e1) &&
              local (`(tc_val t1) (`(eval_cast (typeof e1) t1 v2))) &&
              (`(mapsto sh (typeof e1)) (eval_lvalue e1) (`v2) * TT) &&
              subst id (`(force_val (sem_cast (typeof e1) t1 v2))) P)))
        (Sset id e) (normal_ret_assert P).

End CLIGHT_SEPARATION_HOARE_LOGIC_SSET_BACKWARD.

Module ToSset
       (Def: CLIGHT_SEPARATION_HOARE_LOGIC_DEF)
       (Conseq: CLIGHT_SEPARATION_HOARE_LOGIC_CONSEQUENCE with Module CSHL_Def := Def)
       (Extr: CLIGHT_SEPARATION_HOARE_LOGIC_EXTRACTION with Module CSHL_Def := Def)
       (SetB: CLIGHT_SEPARATION_HOARE_LOGIC_SET_BACKWARD with Module CSHL_Def := Def)
       (PtrCmpB: CLIGHT_SEPARATION_HOARE_LOGIC_PTR_CMP_BACKWARD with Module CSHL_Def := Def)
       (LoadB: CLIGHT_SEPARATION_HOARE_LOGIC_LOAD_BACKWARD with Module CSHL_Def := Def)
       (CastLoadB: CLIGHT_SEPARATION_HOARE_LOGIC_CAST_LOAD_BACKWARD with Module CSHL_Def := Def):
       CLIGHT_SEPARATION_HOARE_LOGIC_SSET_BACKWARD with Module CSHL_Def := Def.

Module CSHL_Def := Def.
Module ConseqFacts := GenConseqFacts (Def) (Conseq).
Module ExtrFacts := GenExtrFacts (Def) (Conseq) (Extr).

Import Def.
Import Conseq.
Import ConseqFacts.
Import SetB.
Import PtrCmpB.
Import LoadB.
Import CastLoadB.
Import ExtrFacts.

Theorem semax_set_ptr_compare_load_cast_load_backward: forall {CS: compspecs} {Espec: OracleKind} (Delta: tycontext),
  forall (P: environ->mpred) id e,
    @semax CS Espec Delta
       ((|> ( (tc_expr Delta e) &&
             (tc_temp_id id (typeof e) Delta e) &&
             subst id (eval_expr e) P)) ||
        (EX cmp: Cop.binary_operation, EX e1: expr, EX e2: expr,
         EX ty: type, EX sh1: share, EX sh2: share,
          !! (e = Ebinop cmp e1 e2 ty /\
              sepalg.nonidentity sh1 /\ sepalg.nonidentity sh2 /\
              is_comparison cmp = true /\
              eqb_type (typeof e1) int_or_ptr_type = false /\
              eqb_type (typeof e2) int_or_ptr_type = false /\
              typecheck_tid_ptr_compare Delta id = true) &&
            ( |> ( (tc_expr Delta e1) &&
              (tc_expr Delta e2)  &&
          local (`(blocks_match cmp) (eval_expr e1) (eval_expr e2)) &&
          (`(mapsto_ sh1 (typeof e1)) (eval_expr e1) * TT) &&
          (`(mapsto_ sh2 (typeof e2)) (eval_expr e2) * TT) &&
          subst id (eval_expr (Ebinop cmp e1 e2 ty)) P))) ||
        (EX sh: share, EX t2: type, EX v2: val,
              !! (typeof_temp Delta id = Some t2 /\
                  is_neutral_cast (typeof e) t2 = true /\
                  readable_share sh) &&
         |> ( (tc_lvalue Delta e) &&
              local (`(tc_val (typeof e) v2)) &&
              (`(mapsto sh (typeof e)) (eval_lvalue e) (`v2) * TT) &&
              subst id (`v2) P)) ||
        (EX sh: share, EX e1: expr, EX t1: type, EX v2: val,
              !! (e = Ecast e1 t1 /\
                  typeof_temp Delta id = Some t1 /\
                  cast_pointer_to_bool (typeof e1) t1 = false /\
                  readable_share sh) &&
         |> ( (tc_lvalue Delta e1) &&
              local (`(tc_val t1) (`(eval_cast (typeof e1) t1 v2))) &&
              (`(mapsto sh (typeof e1)) (eval_lvalue e1) (`v2) * TT) &&
              subst id (`(force_val (sem_cast (typeof e1) t1 v2))) P)))
        (Sset id e) (normal_ret_assert P).
Admitted.

End ToSset.

Module Sset2Set
       (Def: CLIGHT_SEPARATION_HOARE_LOGIC_DEF)
       (Conseq: CLIGHT_SEPARATION_HOARE_LOGIC_CONSEQUENCE with Module CSHL_Def := Def)
       (Sset: CLIGHT_SEPARATION_HOARE_LOGIC_SSET_BACKWARD with Module CSHL_Def := Def):
       CLIGHT_SEPARATION_HOARE_LOGIC_SET_BACKWARD with Module CSHL_Def := Def.

Module CSHL_Def := Def.
Module ConseqFacts := GenConseqFacts (Def) (Conseq).

Import Def.
Import Conseq.
Import ConseqFacts.
Import Sset.

Theorem semax_set_backward: forall {CS: compspecs} {Espec: OracleKind} (Delta: tycontext),
  forall (P: environ->mpred) id e,
    @semax CS Espec Delta
        (|> ( (tc_expr Delta e) &&
             (tc_temp_id id (typeof e) Delta e) &&
             subst id (eval_expr e) P))
          (Sset id e) (normal_ret_assert P).
Admitted.

End Sset2Set.

Module Sset2PtrCmp
       (Def: CLIGHT_SEPARATION_HOARE_LOGIC_DEF)
       (Conseq: CLIGHT_SEPARATION_HOARE_LOGIC_CONSEQUENCE with Module CSHL_Def := Def)
       (Sset: CLIGHT_SEPARATION_HOARE_LOGIC_SSET_BACKWARD with Module CSHL_Def := Def):
       CLIGHT_SEPARATION_HOARE_LOGIC_PTR_CMP_BACKWARD with Module CSHL_Def := Def.

Module CSHL_Def := Def.
Module ConseqFacts := GenConseqFacts (Def) (Conseq).

Import Def.
Import Conseq.
Import ConseqFacts.
Import Sset.

Theorem semax_ptr_compare_backward: forall {CS: compspecs} {Espec: OracleKind} (Delta: tycontext),
  forall P id e,
   @semax CS Espec Delta
        (EX cmp: Cop.binary_operation, EX e1: expr, EX e2: expr,
         EX ty: type, EX sh1: share, EX sh2: share,
          !! (e = Ebinop cmp e1 e2 ty /\
              sepalg.nonidentity sh1 /\ sepalg.nonidentity sh2 /\
              is_comparison cmp = true /\
              eqb_type (typeof e1) int_or_ptr_type = false /\
              eqb_type (typeof e2) int_or_ptr_type = false /\
              typecheck_tid_ptr_compare Delta id = true) &&
            ( |> ( (tc_expr Delta e1) &&
              (tc_expr Delta e2)  &&
          local (`(blocks_match cmp) (eval_expr e1) (eval_expr e2)) &&
          (`(mapsto_ sh1 (typeof e1)) (eval_expr e1) * TT) &&
          (`(mapsto_ sh2 (typeof e2)) (eval_expr e2) * TT) &&
          subst id (eval_expr (Ebinop cmp e1 e2 ty)) P)))
          (Sset id e)
        (normal_ret_assert P).
Admitted.

End Sset2PtrCmp.

Module Sset2Load
       (Def: CLIGHT_SEPARATION_HOARE_LOGIC_DEF)
       (Conseq: CLIGHT_SEPARATION_HOARE_LOGIC_CONSEQUENCE with Module CSHL_Def := Def)
       (Sset: CLIGHT_SEPARATION_HOARE_LOGIC_SSET_BACKWARD with Module CSHL_Def := Def):
       CLIGHT_SEPARATION_HOARE_LOGIC_LOAD_BACKWARD with Module CSHL_Def := Def.

Module CSHL_Def := Def.
Module ConseqFacts := GenConseqFacts (Def) (Conseq).

Import Def.
Import Conseq.
Import ConseqFacts.
Import Sset.

Theorem semax_load_backward: forall {CS: compspecs} {Espec: OracleKind} (Delta: tycontext),
  forall (P: environ->mpred) id e1,
    @semax CS Espec Delta
        (EX sh: share, EX t2: type, EX v2: val,
              !! (typeof_temp Delta id = Some t2 /\
                  is_neutral_cast (typeof e1) t2 = true /\
                  readable_share sh) &&
         |> ( (tc_lvalue Delta e1) &&
              local (`(tc_val (typeof e1) v2)) &&
              (`(mapsto sh (typeof e1)) (eval_lvalue e1) (`v2) * TT) &&
              subst id (`v2) P))
        (Sset id e1) (normal_ret_assert P).
Admitted.

End Sset2Load.

Module Sset2CastLoad
       (Def: CLIGHT_SEPARATION_HOARE_LOGIC_DEF)
       (Conseq: CLIGHT_SEPARATION_HOARE_LOGIC_CONSEQUENCE with Module CSHL_Def := Def)
       (Sset: CLIGHT_SEPARATION_HOARE_LOGIC_SSET_BACKWARD with Module CSHL_Def := Def):
       CLIGHT_SEPARATION_HOARE_LOGIC_CAST_LOAD_BACKWARD with Module CSHL_Def := Def.

Module CSHL_Def := Def.
Module ConseqFacts := GenConseqFacts (Def) (Conseq).

Import Def.
Import Conseq.
Import ConseqFacts.
Import Sset.

Theorem semax_cast_load_backward: forall {CS: compspecs} {Espec: OracleKind} (Delta: tycontext),
  forall (P: environ->mpred) id e,
    @semax CS Espec Delta
        (EX sh: share, EX e1: expr, EX t1: type, EX v2: val,
              !! (e = Ecast e1 t1 /\
                  typeof_temp Delta id = Some t1 /\
                  cast_pointer_to_bool (typeof e1) t1 = false /\
                  readable_share sh) &&
         |> ( (tc_lvalue Delta e1) &&
              local (`(tc_val t1) (`(eval_cast (typeof e1) t1 v2))) &&
              (`(mapsto sh (typeof e1)) (eval_lvalue e1) (`v2) * TT) &&
              subst id (`(force_val (sem_cast (typeof e1) t1 v2))) P))
        (Sset id e) (normal_ret_assert P).
Admitted.

End Sset2CastLoad.

End SeparationLogicFacts.

End VST_DOT_floyd_DOT_SeparationLogicFacts_WRAPPED.
Module Export VST_DOT_floyd_DOT_SeparationLogicFacts.
Module Export VST.
Module Export floyd.
Module Export SeparationLogicFacts.
Include VST_DOT_floyd_DOT_SeparationLogicFacts_WRAPPED.SeparationLogicFacts.
End SeparationLogicFacts.

End floyd.

End VST.

End VST_DOT_floyd_DOT_SeparationLogicFacts.
Import VST.floyd.SeparationLogicFacts.
Import LiftNotation.
Import compcert.cfrontend.Ctypes.
Local Open Scope logic.

Inductive semax {CS: compspecs} {Espec: OracleKind} (Delta: tycontext): (environ -> mpred) -> statement -> ret_assert -> Prop :=
| semax_ifthenelse :
   forall P (b: expr) c d R,
     @semax CS Espec Delta (P && local (`(typed_true (typeof b)) (eval_expr b))) c R ->
     @semax CS Espec Delta (P && local (`(typed_false (typeof b)) (eval_expr b))) d R ->
     @semax CS Espec Delta (!! (bool_type (typeof b) = true) && |> (tc_expr Delta (Eunop Cop.Onotbool b (Tint I32 Signed noattr)) && P)) (Sifthenelse b c d) R
| semax_seq:
  forall R P Q h t,
    @semax CS Espec Delta P h (overridePost Q R) ->
    @semax CS Espec Delta Q t R ->
    @semax CS Espec Delta P (Ssequence h t) R
| semax_break: forall Q,
    @semax CS Espec Delta (RA_break Q) Sbreak Q
| semax_continue: forall Q,
    @semax CS Espec Delta (RA_continue Q) Scontinue Q
| semax_loop: forall Q Q' incr body R,
     @semax CS Espec Delta  Q body (loop1_ret_assert Q' R) ->
     @semax CS Espec Delta Q' incr (loop2_ret_assert Q R) ->
     @semax CS Espec Delta Q (Sloop body incr) R
| semax_switch: forall (Q: environ->mpred) a sl R,
     (forall rho, Q rho |-- tc_expr Delta a rho) ->
     (forall n,
     @semax CS Espec Delta
               (local (`eq (eval_expr a) `(Vint n)) &&  Q)
               (seq_of_labeled_statement (select_switch (Int.unsigned n) sl))
               (switch_ret_assert R)) ->
     @semax CS Espec Delta (!! (is_int_type (typeof a) = true) && Q) (Sswitch a sl) R

| semax_call_backward: forall ret a bl R,
     @semax CS Espec Delta
         (EX argsig: _, EX retsig: _, EX cc: _,
          EX A: _, EX P: _, EX Q: _, EX NEP: _, EX NEQ: _, EX ts: _, EX x: _,
         !! (Cop.classify_fun (typeof a) =
             Cop.fun_case_f (typelist_of_type_list argsig) retsig cc /\
             (retsig = Tvoid -> ret = None) /\
             tc_fn_return Delta ret retsig) &&
          (((tc_expr Delta a) && (tc_exprlist Delta argsig bl)))  &&
         `(func_ptr (mk_funspec  (argsig,retsig) cc A P Q NEP NEQ)) (eval_expr a) &&
          |>((fun rho => P ts x (ge_of rho, eval_exprlist argsig bl rho)) * oboxopt Delta ret (maybe_retval (Q ts x) retsig ret -* R)))
         (Scall ret a bl)
         (normal_ret_assert R)
| semax_return: forall (R: ret_assert) ret ,
      @semax CS Espec Delta
                ( (tc_expropt Delta ret (ret_type Delta)) &&
                `(RA_return R : option val -> environ -> mpred) (cast_expropt ret (ret_type Delta)) (@id environ))
                (Sreturn ret)
                R
| semax_set_ptr_compare_load_cast_load_backward: forall (P: environ->mpred) id e,
    @semax CS Espec Delta
       ((|> ( (tc_expr Delta e) &&
             (tc_temp_id id (typeof e) Delta e) &&
             subst id (eval_expr e) P)) ||
        (EX cmp: Cop.binary_operation, EX e1: expr, EX e2: expr,
         EX ty: type, EX sh1: share, EX sh2: share,
          !! (e = Ebinop cmp e1 e2 ty /\
              sepalg.nonidentity sh1 /\ sepalg.nonidentity sh2 /\
              is_comparison cmp = true /\
              eqb_type (typeof e1) int_or_ptr_type = false /\
              eqb_type (typeof e2) int_or_ptr_type = false /\
              typecheck_tid_ptr_compare Delta id = true) &&
            ( |> ( (tc_expr Delta e1) &&
              (tc_expr Delta e2)  &&
          local (`(blocks_match cmp) (eval_expr e1) (eval_expr e2)) &&
          (`(mapsto_ sh1 (typeof e1)) (eval_expr e1) * TT) &&
          (`(mapsto_ sh2 (typeof e2)) (eval_expr e2) * TT) &&
          subst id (eval_expr (Ebinop cmp e1 e2 ty)) P))) ||
        (EX sh: share, EX t2: type, EX v2: val,
              !! (typeof_temp Delta id = Some t2 /\
                  is_neutral_cast (typeof e) t2 = true /\
                  readable_share sh) &&
         |> ( (tc_lvalue Delta e) &&
              local (`(tc_val (typeof e) v2)) &&
              (`(mapsto sh (typeof e)) (eval_lvalue e) (`v2) * TT) &&
              subst id (`v2) P)) ||
        (EX sh: share, EX e1: expr, EX t1: type, EX v2: val,
              !! (e = Ecast e1 t1 /\
                  typeof_temp Delta id = Some t1 /\
                  cast_pointer_to_bool (typeof e1) t1 = false /\
                  readable_share sh) &&
         |> ( (tc_lvalue Delta e1) &&
              local (`(tc_val t1) (`(eval_cast (typeof e1) t1 v2))) &&
              (`(mapsto sh (typeof e1)) (eval_lvalue e1) (`v2) * TT) &&
              subst id (`(force_val (sem_cast (typeof e1) t1 v2))) P)))
        (Sset id e) (normal_ret_assert P)
| semax_store_store_union_hack_backward: forall (P: environ->mpred) e1 e2,
    @semax CS Espec Delta
       ((EX sh: share, !! writable_share sh &&
             |> ( (tc_lvalue Delta e1) &&  (tc_expr Delta (Ecast e2 (typeof e1)))  &&
             ((`(mapsto_ sh (typeof e1)) (eval_lvalue e1)) *
              (`(mapsto sh (typeof e1)) (eval_lvalue e1) (`force_val (`(sem_cast (typeof e2) (typeof e1)) (eval_expr e2))) -* P))))
          || (EX (t2:type) (ch ch': memory_chunk) (sh: share),
             !! ((numeric_type (typeof e1) && numeric_type t2)%bool = true /\
                 access_mode (typeof e1) = By_value ch /\
                 access_mode t2 = By_value ch' /\
                 decode_encode_val_ok ch ch' /\
                 writable_share sh) &&
             |> ( (tc_lvalue Delta e1) &&  (tc_expr Delta (Ecast e2 (typeof e1)))  &&
             ((`(mapsto_ sh (typeof e1)) (eval_lvalue e1)
                      && `(mapsto_ sh t2) (eval_lvalue e1)) *
              (ALL v': val,
                 `(mapsto sh t2) (eval_lvalue e1) (`v') -*
                    imp (local  ((`decode_encode_val )
                         ((` force_val) ((`(sem_cast (typeof e2) (typeof e1))) (eval_expr e2))) (`ch) (`ch') (`v') ))
                      (P)))))
       )
        (Sassign e1 e2) (normal_ret_assert P)
| semax_skip: forall P, @semax CS Espec Delta P Sskip (normal_ret_assert P)
| semax_builtin: forall P opt ext tl el, @semax CS Espec Delta FF (Sbuiltin opt ext tl el) P
| semax_label: forall (P:environ -> mpred) (c:statement) (Q:ret_assert) l,
    @semax CS Espec Delta P c Q -> @semax CS Espec Delta P (Slabel l c) Q
| semax_goto: forall P l, @semax CS Espec Delta FF (Sgoto l) P
| semax_conseq: forall P' (R': ret_assert) P c (R: ret_assert) ,
    (local (tc_environ Delta) && ((allp_fun_id Delta) && P) |-- (|={Ensembles.Full_set}=> P')) ->
    (local (tc_environ Delta) && ((allp_fun_id Delta) && RA_normal R') |-- (|={Ensembles.Full_set}=> RA_normal R)) ->
    (local (tc_environ Delta) && ((allp_fun_id Delta) && RA_break R') |-- (|={Ensembles.Full_set}=> RA_break R)) ->
    (local (tc_environ Delta) && ((allp_fun_id Delta) && RA_continue R') |-- (|={Ensembles.Full_set}=> RA_continue R)) ->
    (forall vl, local (tc_environ Delta) && ((allp_fun_id Delta) && RA_return R' vl) |-- (RA_return R vl)) ->
    @semax CS Espec Delta P' c R' -> @semax CS Espec Delta P c R.

Fixpoint fold_right_sepcon (l: list mpred) : mpred.
exact (match l with
 | nil => emp
 | b::r => b * fold_right_sepcon r
 end).
Defined.

Inductive localdef : Type :=
 | temp: ident -> val -> localdef
 | lvar: ident -> type -> val -> localdef
 | gvars: globals -> localdef.
Definition PROPx {A} (P: list Prop): forall (Q: A->mpred), A->mpred.
Admitted.
Definition LOCALx (Q: list localdef) : forall (R: environ->mpred), environ->mpred.
Admitted.
Definition SEPx {A} (R: list mpred) : A->mpred.
Admitted.

Definition abbreviate {A:Type} (x:A) := x.
Definition reptype_gen {cs: compspecs} : type -> (sigT (fun x => x)).
Admitted.

Definition reptype {cs: compspecs} t: Type := match reptype_gen t with existT t _ => t end.

Import CertiGraph.graph.graph_model.
Definition MAX_SPACES: Z.
Admitted.
Definition MAX_ARGS: Z.
Admitted.

Definition WORD_SIZE: Z := Eval cbv [Archi.ptr64] in if Archi.ptr64 then 8 else 4.

Definition MAX_UINT: Z := Eval cbv [Archi.ptr64] in
      if Archi.ptr64 then Int64.max_unsigned else Int.max_unsigned.

Definition MAX_SPACE_SIZE: Z := Eval cbv [Archi.ptr64] in
      if Archi.ptr64 then Z.shiftl 1 40 else Z.shiftl 1 29.
Definition NO_SCAN_TAG: Z.
Admitted.

Definition VType: Type := nat * nat.
Definition EType: Type := VType * nat.

Inductive GC_Pointer := | GCPtr: block -> ptrofs -> GC_Pointer.
Definition raw_field: Type.
exact (option (Z + GC_Pointer)).
Defined.

Definition Z2val (x: Z) : val :=
  Eval cbv delta [Archi.ptr64] match
         in if Archi.ptr64 then Vlong (Int64.repr x) else Vint (Int.repr x).

Record raw_vertex_block : Type :=
  {
    raw_mark: bool;
    copied_vertex: VType;
    raw_fields: list raw_field;
    raw_color: Z;
    raw_tag: Z;
    raw_tag_range: 0 <= raw_tag < 256;
    raw_color_range: 0 <= raw_color < 4;
    raw_fields_range: 0 < Zlength raw_fields < two_p (WORD_SIZE * 8 - 10);
    tag_no_scan: NO_SCAN_TAG <= raw_tag -> ~ In None raw_fields;

  }.

Record generation_info: Type :=
  {
    start_address: val;
    number_of_vertices: nat;
    generation_sh: share;
    start_isptr: isptr start_address;
    generation_share_writable: writable_share generation_sh;
  }.

Record graph_info : Type :=
  {
    g_gen: list generation_info;
    g_gen_not_nil: g_gen <> nil;
  }.

Definition LGraph := LabeledGraph VType EType raw_vertex_block unit graph_info.

Record space: Type :=
  {
    space_start: val;
    used_space: Z;
    total_space: Z;
    space_sh: share;
    space_order: 0 <= used_space <= total_space;
    space_upper_bound: total_space < MAX_SPACE_SIZE;
  }.

Record heap: Type :=
  {
    spaces: list space;
    spaces_size: Zlength spaces = MAX_SPACES;
  }.

Record thread_info: Type :=
  {
    ti_heap_p: val;
    ti_heap: heap;
    ti_args: list val;
    arg_size: Zlength ti_args = MAX_ARGS;
  }.

Record fun_info : Type :=
  {
    fun_word_size: Z;
    live_roots_indices: list Z;
    fi_index_range: forall i, In i live_roots_indices -> (0 <= i < MAX_ARGS)%Z;
    lri_range: (Zlength (live_roots_indices) <= MAX_UINT - 2)%Z;
    word_size_range: (0 <= fun_word_size <= MAX_UINT)%Z;
  }.
Definition nth_gen (g: LGraph) (gen: nat): generation_info.
Admitted.
Definition graph_has_v (g: LGraph) (v: VType): Prop.
Admitted.
Definition gen_start (g: LGraph) (gen: nat): val.
Admitted.
Definition vertex_address (g: LGraph) (v: VType): val.
Admitted.
Definition roots_t: Type.
Admitted.
Definition outlier_t: Type.
Admitted.
Definition make_header (g: LGraph) (v: VType): Z.
Admitted.
Definition nth_space (t_info: thread_info) (n: nat): space.
Admitted.

Definition gen_size t_info n := total_space (nth_space t_info n).

Definition nth_sh g gen := generation_sh (nth_gen g gen).
Definition _forward : ident.
Admitted.
Definition _from_limit : ident.
Admitted.
Definition _from_start : ident.
Admitted.
Definition _hd : ident.
Admitted.
Definition _j : ident.
Admitted.
Definition _next : ident.
Admitted.
Definition _s : ident.
Admitted.
Definition _spaces : ident.
Admitted.
Definition _sz : ident.
Admitted.
Definition _tag : ident.
Admitted.
Definition _t'1 : ident.
Admitted.

Inductive gfield : Type :=
  | ArraySubsc : forall i: Z, gfield
  | StructField : forall i: ident, gfield
  | UnionField : forall i: ident, gfield.

Section COMPOSITE_ENV.

Context {cs: compspecs}.
Definition nested_field_offset (t: type) (gfs: list gfield) : Z.
Admitted.
Fixpoint legal_nested_field (t: type) (gfs: list gfield) : Prop.
Admitted.

Definition field_compatible t gfs p :=
  isptr p /\
  complete_legal_cosu_type t = true /\
  size_compatible t p /\
  align_compatible t p /\
  legal_nested_field t gfs.

Lemma field_compatible_dec: forall t gfs p,
  {field_compatible t gfs p} + {~ field_compatible t gfs p}.
Admitted.

Definition field_address t gfs p :=
  if (field_compatible_dec t gfs p)
  then offset_val (nested_field_offset t gfs) p
  else Vundef.

End COMPOSITE_ENV.
Export ListNotations.

Module Type FREEZER.
Parameter FRZ : mpred -> mpred.

Parameter FRZL : list mpred -> mpred.

Parameter FRZRw : list mpred -> list mpred -> Type.
Parameter FRZRw_constr : forall {L1 G1: list mpred} {F: mpred},
    ((fold_right sepcon emp G1) |-- fold_right sepcon emp L1 * F) -> FRZRw L1 G1.
Parameter FRZR : forall L1 G1 {w: FRZRw L1 G1}, mpred.

End FREEZER.

Module Freezer : FREEZER.
Definition FRZ (p: mpred) := p.
Definition FRZL (ps:list mpred): mpred.
Admitted.

Inductive FRZRw' (L1 G1: list mpred): Type :=
| FRZRw'_constr: forall F: mpred,
    ((fold_right sepcon emp G1) |-- fold_right sepcon emp L1 * F) -> FRZRw' L1 G1.

Definition FRZRw := FRZRw'.
Definition FRZRw_constr:= FRZRw'_constr.
Definition FRZR (L1 G1: list mpred) {w: FRZRw L1 G1}: mpred.
Admitted.

End Freezer.

Notation FRZ := Freezer.FRZ.
Notation FRZL := Freezer.FRZL.
Notation FRZR := Freezer.FRZR.

Inductive split_FRZ_in_SEP: list mpred -> list mpred -> list mpred -> Prop :=
| split_FRZ_in_SEP_nil: split_FRZ_in_SEP nil nil nil
| split_FRZ_in_SEP_FRZ: forall R R' RF F, split_FRZ_in_SEP R R' RF -> split_FRZ_in_SEP (FRZ F :: R) R' (FRZ F :: RF)
| split_FRZ_in_SEP_FRZL: forall R R' RF F, split_FRZ_in_SEP R R' RF -> split_FRZ_in_SEP (FRZL F :: R) R' (FRZL F :: RF)
| split_FRZ_in_SEP_FRZR: forall R R' RF L G w, split_FRZ_in_SEP R R' RF -> split_FRZ_in_SEP (@FRZR L G w :: R) R' (@FRZR L G w :: RF)
| split_FRZ_in_SEP_other: forall R R' RF R0, split_FRZ_in_SEP R R' RF -> split_FRZ_in_SEP (R0 :: R) (R0 :: R') RF.

Ltac prove_split_FRZ_in_SEP :=
  solve [
    repeat first
    [ simple apply split_FRZ_in_SEP_nil
    | simple apply split_FRZ_in_SEP_FRZ
    | simple apply split_FRZ_in_SEP_FRZL
    | simple apply split_FRZ_in_SEP_FRZR
    | simple apply split_FRZ_in_SEP_other]].

Lemma unlocalize_triple: forall R_G2 Espec {cs: compspecs} Delta P Q R R_FR R_L1 R_G1 R_L2 c Post w,
  split_FRZ_in_SEP R R_L2 (@FRZR R_L1 R_G1 w :: R_FR) ->
  (exists (H: fold_right_sepcon R_G1 |-- fold_right_sepcon R_L1 * (fold_right_sepcon R_L2 -* fold_right_sepcon R_G2)), w = @Freezer.FRZRw_constr _ _ _ H) ->
  (@abbreviate _ (fun _ _ => True) R_L1 R_G1 -> @semax cs Espec Delta (PROPx P (LOCALx Q (SEPx (R_G2 ++ R_FR)))) c Post) ->
  @semax cs Espec Delta (PROPx P (LOCALx Q (SEPx R))) c Post.
Admitted.
Export compcert.cfrontend.Cop.

#[export] Instance CompSpecs : compspecs.
Admitted.
Definition space_type : type.
Admitted.
Definition heap_type: type.
Admitted.
Definition vertex_rep (sh: share) (g: LGraph) (v: VType): mpred.
Admitted.
Definition graph_rep (g: LGraph): mpred.
Admitted.

Definition limit_address g t_info from :=
  offset_val (WORD_SIZE * gen_size t_info from) (gen_start g from).

Lemma foo: True.
Proof.
  eassert (
  forall (Espec : OracleKind) (rsh sh : share) (gv : globals) (fi ti : val)
         (_ : LGraph) (_ : thread_info) (f_info : fun_info) (_ : roots_t) (outlier : outlier_t)
         (from to _ : nat) (Delta_specs : Maps.PTree.t funspec) (Delta : tycontext)
         (g' : LGraph) (t_info' : thread_info) (index : nat) (sp_to : space)
         (l : list (@reptype CompSpecs space_type)) (used_offset index_offset : Z)
         (FR : list mpred) (_ : graph_has_v g' (@pair nat nat to index)) (RamL RamG : list mpred)
         (POSTCONDITION : ret_assert) (MORE_COMMANDS : statement),
    @semax CompSpecs Espec Delta
      (@PROPx environ (@nil Prop)
         (LOCALx
            (@cons localdef (temp _hd (Z2val (make_header g' (@pair nat nat to index))))
               (@cons localdef (temp _t'1 (offset_val used_offset (space_start sp_to)))
                  (@cons localdef
                     (temp _s
                        (offset_val (Z.opp WORD_SIZE) (vertex_address g' (@pair nat nat to index))))
                     (@cons localdef (temp _from_start (gen_start g' from))
                        (@cons localdef (temp _from_limit (limit_address g' t_info' from))
                           (@cons localdef
                              (temp _next
                                 (@field_address CompSpecs heap_type
                                    (@cons gfield (StructField _next)
                                       (@cons gfield (ArraySubsc (Z.of_nat to))
                                          (@cons gfield (StructField _spaces) (@nil gfield))))
                                    (ti_heap_p t_info'))) (@nil localdef)))))))
            (@SEPx environ
               (@cons mpred (vertex_rep (nth_sh g' to) g' (@pair nat nat to index))
                  (@cons mpred (@Freezer.FRZR RamL RamG _)
                     (@cons mpred (Freezer.FRZL FR) (@nil mpred)))))))
      (Ssequence
         (Ssequence
            (Sset _sz
               (Ecast
                  (Ebinop Oshr (Etempvar _hd tulong)
                     (Econst_int (Int.repr (Zpos (xO (xI (xO xH))))) tint) tulong) tulong))
            (Ssequence
               (Sset _tag
                  (Ecast
                     (Ebinop Oand (Etempvar _hd tulong)
                        (Econst_int (Int.repr (Zpos (xI (xI (xI (xI (xI (xI (xI xH))))))))) tint)
                        tulong) tuint))
               (Ssequence
                  (Sifthenelse
                     (Eunop Onotbool
                        (Ebinop Oge (Etempvar _tag tint)
                           (Econst_int (Int.repr (Zpos (xI (xI (xO (xI (xI (xI (xI xH))))))))) tint)
                           tint) tint)
                     (Sfor (Sset _j (Ecast (Econst_int (Int.repr (Zpos xH)) tint) tlong))
                        (Ebinop Ole (Etempvar _j tlong) (Etempvar _sz tulong) tint)
                        (Scall (@None ident)
                           (Evar _forward
                              (Tfunction
                                 (Tcons
                                    (tptr (Tpointer tvoid (mk_attr false (@Some N (Npos (xI xH))))))
                                    (Tcons
                                       (tptr (Tpointer tvoid (mk_attr false (@Some N (Npos (xI xH))))))
                                       (Tcons
                                          (tptr
                                             (tptr
                                                (Tpointer tvoid
                                                   (mk_attr false (@Some N (Npos (xI xH)))))))
                                          (Tcons
                                             (tptr
                                                (Tpointer tvoid
                                                   (mk_attr false (@Some N (Npos (xI xH))))))
                                             (Tcons tint Tnil))))) tvoid cc_default))
                           (@cons expr
                              (Etempvar _from_start
                                 (tptr (Tpointer tvoid (mk_attr false (@Some N (Npos (xI xH)))))))
                              (@cons expr
                                 (Etempvar _from_limit
                                    (tptr (Tpointer tvoid (mk_attr false (@Some N (Npos (xI xH)))))))
                                 (@cons expr
                                    (Etempvar _next
                                       (tptr
                                          (tptr
                                             (Tpointer tvoid (mk_attr false (@Some N (Npos (xI xH))))))))
                                    (@cons expr
                                       (Ebinop Oadd
                                          (Ecast
                                             (Etempvar _s
                                                (tptr
                                                   (Tpointer tvoid
                                                      (mk_attr false (@Some N (Npos (xI xH)))))))
                                             (tptr
                                                (Tpointer tvoid
                                                   (mk_attr false (@Some N (Npos (xI xH)))))))
                                          (Etempvar _j tlong)
                                          (tptr
                                             (Tpointer tvoid (mk_attr false (@Some N (Npos (xI xH)))))))
                                       (@cons expr (Econst_int (Int.repr Z0) tint) (@nil expr)))))))
                        (Sset _j
                           (Ebinop Oadd (Etempvar _j tlong) (Econst_int (Int.repr (Zpos xH)) tint)
                              tlong))) Sskip)
                  (Sset _s
                     (Ebinop Oadd
                        (Etempvar _s (tptr (Tpointer tvoid (mk_attr false (@Some N (Npos (xI xH)))))))
                        (Ebinop Oadd (Econst_int (Int.repr (Zpos xH)) tint)
                           (Etempvar _sz tulong) tulong)
                        (tptr (Tpointer tvoid (mk_attr false (@Some N (Npos (xI xH)))))))))))
         MORE_COMMANDS) POSTCONDITION).
  2:give_up.
  intros Espec rsh sh gv fi ti g t_info f_info roots outlier from to to_index Delta_specs Delta g' t_info' index sp_to l used_offset index_offset FR H23 RamL RamG POSTCONDITION MORE_COMMANDS.

eapply (unlocalize_triple [graph_rep g']); [ prove_split_FRZ_in_SEP | | ].
{

set (J := fst (RamG, H23)).
change RamG with J.
clear.

refine (ex_intro _ _ eq_refl).

Check J.
