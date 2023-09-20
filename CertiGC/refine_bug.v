(* -*- mode: coq; coq-prog-args: ("-emacs" "-w" "-overriding-logical-loadpath" "-w" "-deprecated-native-compiler-option,-native-compiler-disabled" "-native-compiler" "ondemand" "-Q" "/github/workspace/cwd" "Top" "-Q" "/github/workspace/CertiGraph/lib" "CertiGraph.lib" "-Q" "/github/workspace/CertiGraph/msl_ext" "CertiGraph.msl_ext" "-Q" "/github/workspace/CertiGraph/msl_application" "CertiGraph.msl_application" "-Q" "/github/workspace/CertiGraph/graph" "CertiGraph.graph" "-Q" "/github/workspace/CertiGraph/heap_model_direct" "CertiGraph.heap_model_direct" "-Q" "/github/workspace/CertiGraph" "CertiGraph" "-Q" "/home/coq/.opam/4.13.1+flambda/lib/coq/user-contrib/VST" "VST" "-Q" "/home/coq/.opam/4.13.1+flambda/lib/coq/user-contrib/compcert" "compcert" "-Q" "/home/coq/.opam/4.13.1+flambda/lib/coq/user-contrib/Bignums" "Bignums" "-Q" "/home/coq/.opam/4.13.1+flambda/lib/coq/user-contrib/Flocq" "Flocq" "-Q" "/home/coq/.opam/4.13.1+flambda/lib/coq/user-contrib/Ltac2" "Ltac2" "-Q" "/home/coq/.opam/4.13.1+flambda/lib/coq/user-contrib/MenhirLib" "MenhirLib" "-top" "CertiGraph.CertiGC.refine_bug") -*- *)
(* File reduced by coq-bug-minimizer from original input, then from 248 lines to 293 lines, then from 306 lines to 1139 lines, then from 1144 lines to 745 lines, then from 758 lines to 2718 lines, then from 2722 lines to 1108 lines *)
(* coqc version 8.17.1 compiled with OCaml 4.13.1
   coqtop version 8.17.1
   Expected coqc runtime on this file: 16.406 sec *)
Require Coq.Init.Ltac.
Require CertiGraph.msl_ext.abs_addr.
Require Coq.Arith.Arith.
Require Coq.Arith.EqNat.
Require Coq.Arith.Max.
Require Coq.Bool.Bool.
Require Coq.Classes.EquivDec.
Require Coq.Classes.Equivalence.
Require Coq.Classes.Morphisms.
Require Coq.Classes.RelationClasses.
Require Coq.Lists.List.
Require Coq.Lists.ListDec.
Require Coq.Lists.ListSet.
Require Coq.Logic.ClassicalFacts.
Require Coq.Logic.ConstructiveEpsilon.
Require Coq.Logic.Eqdep.
Require Coq.Logic.EqdepFacts.
Require Coq.Logic.Eqdep_dec.
Require Coq.Logic.FunctionalExtensionality.
Require Coq.Logic.JMeq.
Require Coq.Logic.ProofIrrelevance.
Require Coq.Logic.PropExtensionality.
Require Coq.Numbers.Natural.Peano.NPeano.
Require Coq.Program.Basics.
Require Coq.Reals.Rdefinitions.
Require Coq.Relations.Relation_Definitions.
Require Coq.Relations.Relations.
Require Coq.Setoids.Setoid.
Require Coq.Sets.Constructive_sets.
Require Coq.Sets.Ensembles.
Require Coq.Sets.Finite_sets.
Require Coq.Sorting.Permutation.
Require Coq.Sorting.Sorted.
Require Coq.Sorting.Sorting.
Require Coq.Strings.Ascii.
Require Coq.Strings.String.
Require Coq.Structures.GenericMinMax.
Require Coq.Structures.Orders.
Require Coq.Wellfounded.Wellfounded.
Require Coq.ZArith.ZArith.
Require Coq.ZArith.ZArith_base.
Require Coq.ZArith.Zcomplements.
Require Coq.ZArith.Znumtheory.
Require Coq.funind.FunInd.
Require Coq.funind.Recdef.
Require Coq.micromega.Lia.
Require Ltac2.Init.
Require VST.floyd.simple_reify.
Require VST.msl.simple_CCC.
Require VST.veric.lift.
Require compcert.cfrontend.Clight.
Require compcert.cfrontend.Cop.
Require compcert.cfrontend.Ctypes.
Require compcert.common.AST.
Require compcert.common.Errors.
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
Require CertiGraph.lib.EquivDec_ext.
Require Ltac2.Bool.
Require Ltac2.Constant.
Require Ltac2.Constr.
Require Ltac2.Constructor.
Require Ltac2.Evar.
Require Ltac2.Float.
Require Ltac2.Ident.
Require Ltac2.Ind.
Require Ltac2.Int.
Require Ltac2.Ltac1.
Require Ltac2.Message.
Require Ltac2.Meta.
Require Ltac2.Proj.
Require Ltac2.Std.
Require Ltac2.String.
Require Ltac2.Uint63.
Require Ltac2.Char.
Require Ltac2.Control.
Require Ltac2.Env.
Require Ltac2.Printf.
Require VST.floyd.find_nth_tactic.
Require VST.msl.Axioms.
Require CertiGraph.lib.Coqlib.
Require Ltac2.Option.
Require Ltac2.Pattern.
Require CertiGraph.lib.Relation_ext.
Require VST.msl.Extensionality.
Require VST.zlist.sublist.
Require Ltac2.Array.
Require Ltac2.List.
Require VST.floyd.computable_theorems.
Require VST.msl.sepalg.
Require VST.msl.seplog.
Require VST.zlist.Zlength_solver.
Require CertiGraph.lib.Equivalence_ext.
Require Ltac2.Fresh.
Require VST.msl.ghost.
Require VST.sepcomp.extspec.
Require CertiGraph.lib.List_Func_ext.
Require CertiGraph.msl_ext.seplog.
Require VST.floyd.jmeq_lemmas.
Require Ltac2.Notations.
Require VST.msl.base.
Require VST.zlist.list_solver.
Require VST.msl.eq_dec.
Require VST.msl.functors.
Require VST.msl.ghost_seplog.
Require VST.msl.sig_isomorphism.
Require CertiGraph.CertiGC.gc.
Require CertiGraph.lib.Ensembles_ext.
Require VST.msl.Coqlib2.
Require VST.msl.cjoins.
Require VST.msl.sepalg_generators.
Require VST.floyd.Clightnotations.
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
Require CertiGraph.lib.List_ext.
Require VST.msl.age_to.
Require VST.msl.tree_shares.
Require VST.veric.coqlib4.
Require CertiGraph.graph.find_not_in.
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
Require CertiGraph.lib.EnumEnsembles.
Require CertiGraph.lib.relation_list.
Require VST.sepcomp.semantics_lemmas.
Require VST.floyd.compact_prod_sum.
Require VST.msl.contractive.
Require VST.sepcomp.event_semantics.
Require Ltac2.Ltac2.
Require VST.msl.knot_full_sa.
Require VST.veric.base.
Require VST.sepcomp.step_lemmas.
Require VST.veric.type_induction.
Require CertiGraph.graph.graph_model.
Require VST.veric.Cop2.
Require VST.veric.composite_compute.
Require VST.veric.address_conflict.
Require CertiGraph.graph.path_lemmas.
Require VST.floyd.functional_base.
Require VST.veric.align_mem.
Require VST.veric.compspecs.
Require CertiGraph.graph.reachable_ind.
Require VST.veric.Clight_base.
Require VST.veric.Clight_lemmas.
Require VST.veric.Clight_core.
Require CertiGraph.graph.graph_gen.
Require VST.msl.msl_standard.
Require VST.msl.normalize.
Require VST.msl.alg_seplog.
Require VST.msl.sepalg_list.
Require VST.veric.shares.
Require VST.msl.log_normalize.
Require VST.msl.wand_frame.
Require VST.msl.wandQ_frame.
Require CertiGraph.msl_ext.log_normalize.
Require VST.msl.iter_sepcon.
Require VST.msl.ramification_lemmas.
Require VST.veric.local.
Require VST.veric.rmaps.
Require VST.veric.rmaps_lemmas.
Require CertiGraph.msl_ext.iter_sepcon.
Require VST.veric.compcert_rmaps.
Require VST.veric.juicy_base.
Require CertiGraph.msl_ext.ramification_lemmas.
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
Require VST.floyd.SeparationLogicFacts.
Require VST.floyd.SeparationLogicAsLogic.
Require VST.floyd.SeparationLogicAsLogicSoundness.
Require VST.floyd.base.
Require VST.floyd.computable_functions.
Require VST.floyd.seplog_tactics.
Require VST.floyd.typecheck_lemmas.
Require VST.floyd.const_only_eval.
Require VST.floyd.base2.
Require VST.floyd.canon.
Require VST.floyd.linking.
Require VST.floyd.client_lemmas.
Require CertiGraph.CertiGC.GCGraph.
Require CertiGraph.CertiGC.env_graph_gc.
Module Export spatial_gcgraph.
Import VST.veric.compcert_rmaps.
Import CertiGraph.graph.graph_model.
Import CertiGraph.CertiGC.GCGraph.
Export CertiGraph.CertiGC.env_graph_gc.
Import CertiGraph.msl_ext.iter_sepcon.

Local Open Scope logic.

Definition vertex_at (sh: share) (p: val) (header: Z) (lst_fields: list val) :=
  Eval cbv delta [Archi.ptr64] match
         in
         (data_at sh (if Archi.ptr64 then tulong else tuint)
                  (Z2val header) (offset_val (- WORD_SIZE) p) *
          data_at sh (tarray int_or_ptr_type (Zlength lst_fields)) lst_fields p).
Definition vertex_rep (sh: share) (g: LGraph) (v: VType): mpred. exact (vertex_at sh (vertex_address g v) (make_header g v) (make_fields_vals g v)). Defined.
Definition generation_rep (g: LGraph) (gen: nat): mpred. exact (iter_sepcon (map (fun x => (gen, x))
                   (nat_inc_list (nth_gen g gen).(number_of_vertices)))
              (vertex_rep (nth_sh g gen) g)). Defined.
Definition graph_rep (g: LGraph): mpred. exact (iter_sepcon (nat_inc_list (length g.(glabel).(g_gen))) (generation_rep g)). Defined.

Definition fun_info_rep (sh: share) (fi: fun_info) (p: val) : mpred :=
  Eval cbv delta [Archi.ptr64] match
         in
         let len := Zlength (live_roots_indices fi) in
         data_at
           sh (tarray (if Archi.ptr64 then tulong else tuint) (len + 2))
           (map Z2val (fun_word_size fi :: len :: live_roots_indices fi)) p.
Definition space_rest_rep (sp: space): mpred. exact (if (Val.eq sp.(space_start) nullval)
  then emp
  else data_at_ (space_sh sp)
                (tarray int_or_ptr_type (sp.(total_space) - sp.(used_space)))
                (offset_val (WORD_SIZE * used_space sp) sp.(space_start))). Defined.
Definition heap_rest_rep (hp: heap): mpred. exact (iter_sepcon hp.(spaces) space_rest_rep). Defined.
Definition space_tri (sp: space): (reptype space_type). exact (let s := sp.(space_start) in (s, (offset_val (WORD_SIZE * sp.(used_space)) s,
                                    offset_val (WORD_SIZE * sp.(total_space)) s))). Defined.
Definition heap_struct_rep (sh: share) (sp_reps: list (@reptype CompSpecs space_type)) (h: val):
  mpred. exact (@data_at CompSpecs sh heap_type sp_reps h). Defined.

Definition before_gc_thread_info_rep (sh: share) (ti: thread_info) (t: val) :=
  let nursery := heap_head ti.(ti_heap) in
  let p := nursery.(space_start) in
  let n_lim := offset_val (WORD_SIZE * nursery.(total_space)) p in
  data_at sh thread_info_type
          (offset_val (WORD_SIZE * nursery.(used_space)) p,
           (n_lim, (ti.(ti_heap_p), ti.(ti_args)))) t *
  heap_struct_rep
    sh ((p, (Vundef, n_lim))
          :: map space_tri (tl ti.(ti_heap).(spaces))) ti.(ti_heap_p) *
  heap_rest_rep ti.(ti_heap).

Definition thread_info_rep (sh: share) (ti: thread_info) (t: val) :=
  data_at sh thread_info_type (Vundef, (Vundef, (ti.(ti_heap_p), ti.(ti_args)))) t *
  heap_struct_rep sh (map space_tri ti.(ti_heap).(spaces)) ti.(ti_heap_p) *
  heap_rest_rep ti.(ti_heap).

Definition single_outlier_rep (p: GC_Pointer) :=
  EX sh: share, !!(readable_share sh) &&
                  (data_at_ sh (tptr tvoid) (GC_Pointer2val p) * TT).

Definition outlier_rep (outlier: outlier_t) :=
  fold_right andp TT (map single_outlier_rep outlier).

Lemma sizeof_tarray_int_or_ptr: forall n,
    0 <= n -> sizeof (tarray int_or_ptr_type n) = (WORD_SIZE * n)%Z.
Admitted.

Definition valid_int_or_ptr (x: val) :=
  match x with
  | Vint i => if Archi.ptr64 then False else Int.testbit i 0 = true
  | Vptr _ z => Ptrofs.testbit z 0 = false /\ Ptrofs.testbit z 1 = false
  | Vlong i => if Archi.ptr64 then Int64.testbit i 0 = true else False
  | _ => False
  end.
Program Definition weak_derives (P Q: mpred): mpred. exact ((! (P >=> Q))%pred). Defined.

Definition generation_data_at_ g t_info gen :=
  data_at_ (nth_sh g gen)
           (tarray int_or_ptr_type (gen_size t_info gen)) (gen_start g gen).

Lemma graph_and_heap_rest_data_at_: forall (g: LGraph) (t_info: thread_info) gen,
    graph_has_gen g gen ->
    graph_thread_info_compatible g t_info ->
    graph_rep g * heap_rest_rep (ti_heap t_info) |--
                                generation_data_at_ g t_info gen * TT.
Admitted.

Lemma generation_data_at__ptrofs: forall g t_info gen b i,
    Vptr b i = gen_start g gen ->
    generation_data_at_ g t_info gen |--
                        !! (WORD_SIZE * gen_size t_info gen + Ptrofs.unsigned i <=
                            Ptrofs.max_unsigned).
Admitted.
Definition space_token_rep (sp: space): mpred. exact (if Val.eq (space_start sp) nullval then emp
  else malloc_token Ews (tarray int_or_ptr_type (total_space sp)) (space_start sp)). Defined.
Definition ti_token_rep (ti: thread_info): mpred. exact (malloc_token Ews heap_type (ti_heap_p ti) *
  iter_sepcon (spaces (ti_heap ti)) space_token_rep). Defined.

End spatial_gcgraph.
Export VST.veric.rmaps.
Export CertiGraph.CertiGC.GCGraph.
Definition all_string_constants (sh: share) (gv: globals) : mpred.
Admitted.
Definition MSS_constant (gv: globals): mpred.
Admitted.

Definition test_int_or_ptr_spec :=
 DECLARE _test_int_or_ptr
 WITH x : val
 PRE [int_or_ptr_type]
   PROP (valid_int_or_ptr x)
   PARAMS (x)
   GLOBALS ()
   SEP ()
 POST [ tint ]
   PROP()
   LOCAL(temp ret_temp
          (Vint (Int.repr (match x with
                           | Vint _ => if Archi.ptr64 then 0 else 1
                           | Vlong _ => if Archi.ptr64 then 1 else 0
                           | _ => 0
                           end))))
   SEP().

Definition int_or_ptr_to_int_spec :=
  DECLARE _int_or_ptr_to_int
  WITH x : val
  PRE [int_or_ptr_type ]
    PROP (is_int I32 Signed x)
    PARAMS (x)
    GLOBALS ()
    SEP ()
  POST [ (if Archi.ptr64 then tlong else tint) ]
    PROP() LOCAL (temp ret_temp x) SEP().

Definition int_or_ptr_to_ptr_spec :=
  DECLARE _int_or_ptr_to_ptr
  WITH x : val
  PRE [int_or_ptr_type ]
    PROP (isptr x)
    PARAMS (x)
    GLOBALS ()
    SEP ()
  POST [ tptr tvoid ]
    PROP() LOCAL (temp ret_temp x) SEP().

Definition int_to_int_or_ptr_spec :=
  DECLARE _int_to_int_or_ptr
  WITH x : val
  PRE [ (if Archi.ptr64 then tlong else tint) ]
    PROP (valid_int_or_ptr x)
    PARAMS (x)
    GLOBALS ()
    SEP ()
  POST [ int_or_ptr_type ]
    PROP() LOCAL (temp ret_temp x) SEP().

Definition ptr_to_int_or_ptr_spec :=
  DECLARE _ptr_to_int_or_ptr
  WITH x : val
  PRE [tptr tvoid ]
    PROP (valid_int_or_ptr x)
    PARAMS (x)
    GLOBALS ()
    SEP()
  POST [ int_or_ptr_type ]
    PROP() LOCAL (temp ret_temp x) SEP().

Definition Is_block_spec :=
  DECLARE _Is_block
  WITH x : val
  PRE [int_or_ptr_type ]
    PROP (valid_int_or_ptr x)
    PARAMS (x)
    GLOBALS ()
    SEP()
  POST [ tint ]
    PROP()
    LOCAL(temp ret_temp
               (Vint (Int.repr (match x with
                                | Vptr _ _ => 1
                                | _ => 0
                                end))))
    SEP().

Definition abort_with_spec :=
  DECLARE _abort_with
  WITH s: val, str: list byte, sh: share
  PRE [tptr tschar]
    PROP (readable_share sh)
    PARAMS (s)
    GLOBALS ()
    SEP (cstring sh str s)
  POST [ tvoid ]
    PROP (False) LOCAL() SEP().

Definition IS_FROM_TYPE :=
  ProdType (ProdType (ProdType
                        (ProdType (ConstType share) (ConstType val))
                        (ConstType Z)) (ConstType val)) Mpred.

Program Definition Is_from_spec :=
  DECLARE _Is_from
  TYPE IS_FROM_TYPE
  WITH sh: share, start : val, n: Z, v: val, P: mpred
  PRE [tptr int_or_ptr_type,
       tptr int_or_ptr_type,
       tptr int_or_ptr_type]
    PROP ()
    PARAMS (start; offset_val n start; v)
    GLOBALS ()
    SEP (weak_derives P (memory_block sh n start * TT) && emp;
         weak_derives P (valid_pointer v * TT) && emp; P)
  POST [tint]
    EX b: {v_in_range v start n} + {~ v_in_range v start n},
    PROP ()
    LOCAL (temp ret_temp (Vint (Int.repr (if b then 1 else 0))))
    SEP (P).
Admit Obligations.

Definition forward_p_address
           (p: forward_p_type) (ti: val) (f_info: fun_info) (g: LGraph) :=
  match p with
  | inl root_index => field_address
                        thread_info_type
                        [ArraySubsc (Znth root_index (live_roots_indices f_info));
                           StructField _args] ti
  | inr (v, n) => offset_val (WORD_SIZE * n) (vertex_address g v)
  end.

Definition limit_address g t_info from :=
  offset_val (WORD_SIZE * gen_size t_info from) (gen_start g from).

Definition next_address t_info to :=
  field_address heap_type
                [StructField _next;
                   ArraySubsc (Z.of_nat to); StructField _spaces] (ti_heap_p t_info).

Definition forward_spec :=
  DECLARE _forward
  WITH rsh: share, sh: share, gv: globals, fi: val, ti: val,
       g: LGraph, t_info: thread_info, f_info: fun_info,
       roots : roots_t, outlier: outlier_t,
       from: nat, to: nat, depth: Z, forward_p: forward_p_type
  PRE [tptr int_or_ptr_type,
       tptr int_or_ptr_type,
       tptr (tptr int_or_ptr_type),
       tptr int_or_ptr_type,
       tint]
    PROP (readable_share rsh; writable_share sh;
          super_compatible (g, t_info, roots) f_info outlier;
          forward_p_compatible forward_p roots g from;
          forward_condition g t_info from to;
          0 <= depth <= Int.max_signed;
          from <> to)
    PARAMS (gen_start g from;
           limit_address g t_info from;
           next_address t_info to;
           forward_p_address forward_p ti f_info g;
           Vint (Int.repr depth))
    GLOBALS ()
    SEP (all_string_constants rsh gv;
         fun_info_rep rsh f_info fi;
         outlier_rep outlier;
         graph_rep g;
         thread_info_rep sh t_info ti)
  POST [tvoid]
    EX g': LGraph, EX t_info': thread_info, EX roots': roots_t,
    PROP (super_compatible (g', t_info', roots') f_info outlier;
          roots' = upd_roots from to forward_p g roots f_info;
          forward_relation from to (Z.to_nat depth)
                           (forward_p2forward_t forward_p roots g) g g';
          forward_condition g' t_info' from to;
          thread_info_relation t_info t_info')
    LOCAL ()
    SEP (all_string_constants rsh gv;
         fun_info_rep rsh f_info fi;
         outlier_rep outlier;
         graph_rep g';
         thread_info_rep sh t_info' ti).

Definition forward_roots_spec :=
  DECLARE _forward_roots
  WITH rsh: share, sh: share, gv: globals, fi: val, ti: val,
       g: LGraph, t_info: thread_info, f_info: fun_info,
       roots: roots_t, outlier: outlier_t, from: nat, to: nat
  PRE [tptr int_or_ptr_type,
       tptr int_or_ptr_type,
       tptr (tptr int_or_ptr_type),
       tptr (if Archi.ptr64 then tulong else tuint),
       tptr thread_info_type]
    PROP (readable_share rsh; writable_share sh;
          super_compatible (g, t_info, roots) f_info outlier;
          forward_condition g t_info from to;
          from <> to)
    PARAMS (gen_start g from;
           limit_address g t_info from;
           next_address t_info to;
           fi; ti)
    GLOBALS (gv)
    SEP (all_string_constants rsh gv;
         fun_info_rep rsh f_info fi;
         outlier_rep outlier;
         graph_rep g;
         thread_info_rep sh t_info ti)
  POST [tvoid]
    EX g' : LGraph, EX t_info': thread_info, EX roots': roots_t,
    PROP (super_compatible (g', t_info', roots') f_info outlier;
          forward_roots_relation from to f_info roots g roots' g';
          forward_condition g' t_info' from to;
          thread_info_relation t_info t_info')
    LOCAL ()
    SEP (all_string_constants rsh gv;
         fun_info_rep rsh f_info fi;
         outlier_rep outlier;
         graph_rep g';
         thread_info_rep sh t_info' ti).

Definition do_scan_spec :=
  DECLARE _do_scan
  WITH rsh: share, sh: share, gv: globals, fi: val, ti: val,
       g: LGraph, t_info: thread_info, f_info: fun_info,
       roots : roots_t, outlier: outlier_t,
       from: nat, to: nat, to_index: nat
  PRE [tptr int_or_ptr_type,
       tptr int_or_ptr_type,
       tptr int_or_ptr_type,
       tptr (tptr int_or_ptr_type)]
    PROP (readable_share rsh; writable_share sh;
          super_compatible (g, t_info, roots) f_info outlier;
          forward_condition g t_info from to;
          from <> to; closure_has_index g to to_index;
          0 < gen_size t_info to; gen_unmarked g to)
    PARAMS (gen_start g from;
           limit_address g t_info from;
           offset_val (- WORD_SIZE) (vertex_address g (to, to_index));
           next_address t_info to)
    GLOBALS ()
    SEP (all_string_constants rsh gv;
         fun_info_rep rsh f_info fi;
         outlier_rep outlier;
         graph_rep g;
         thread_info_rep sh t_info ti)
  POST [tvoid]
    EX g': LGraph, EX t_info': thread_info,
    PROP (super_compatible (g', t_info', roots) f_info outlier;
          forward_condition g' t_info' from to;
          do_scan_relation from to to_index g g';
          thread_info_relation t_info t_info')
    LOCAL ()
    SEP (all_string_constants rsh gv;
         fun_info_rep rsh f_info fi;
         outlier_rep outlier;
         graph_rep g';
         thread_info_rep sh t_info' ti).

Definition do_generation_spec :=
  DECLARE _do_generation
  WITH rsh: share, sh: share, gv: globals, fi: val, ti: val,
       g: LGraph, t_info: thread_info, f_info: fun_info,
       roots: roots_t, outlier: outlier_t, from: nat, to: nat
  PRE [tptr space_type,
       tptr space_type,
       tptr (if Archi.ptr64 then tulong else tuint),
       tptr thread_info_type]
    PROP (readable_share rsh; writable_share sh;
          super_compatible (g, t_info, roots) f_info outlier;
          do_generation_condition g t_info roots f_info from to;
          from <> to)
    PARAMS (space_address t_info from;
           space_address t_info to;
           fi; ti)
    GLOBALS (gv)
    SEP (all_string_constants rsh gv;
         fun_info_rep rsh f_info fi;
         outlier_rep outlier;
         graph_rep g;
         thread_info_rep sh t_info ti)
  POST [tvoid]
    EX g' : LGraph, EX t_info': thread_info, EX roots': roots_t,
    PROP (super_compatible (g', t_info', roots') f_info outlier;
          thread_info_relation t_info t_info';
          do_generation_relation from to f_info roots roots' g g')
    LOCAL ()
    SEP (all_string_constants rsh gv;
         fun_info_rep rsh f_info fi;
         outlier_rep outlier;
         graph_rep g';
         thread_info_rep sh t_info' ti).

Definition create_space_spec :=
  DECLARE _create_space
  WITH sh: share, s: val, n: Z, gv: globals, rsh: share
  PRE [tptr space_type, if Archi.ptr64 then tulong else tuint]
    PROP (writable_share sh;
          readable_share rsh;
          0 <= n < MAX_SPACE_SIZE)
    PARAMS (s; if Archi.ptr64 then Vlong (Int64.repr n) else Vint (Int.repr n))
    GLOBALS (gv)
    SEP (mem_mgr gv; all_string_constants rsh gv; data_at_ sh space_type s;
        MSS_constant gv)
  POST [tvoid]
    EX p: val,
    PROP () LOCAL ()
    SEP (mem_mgr gv; all_string_constants rsh gv; MSS_constant gv;
         malloc_token Ews (tarray int_or_ptr_type n) p;
         data_at_ Ews (tarray int_or_ptr_type n) p;
         data_at sh space_type (p, (p, (offset_val (WORD_SIZE * n) p))) s).
Definition zero_triple: (val * (val * val)).
Admitted.

Definition create_heap_spec :=
  DECLARE _create_heap
  WITH sh: share, gv: globals
  PRE []
    PROP (readable_share sh)
    PARAMS ()
    GLOBALS (gv)
    SEP (mem_mgr gv; all_string_constants sh gv; MSS_constant gv)
  POST [tptr heap_type]
    EX h: val, EX p: val,
    PROP () LOCAL (temp ret_temp h)
    SEP (mem_mgr gv; all_string_constants sh gv; MSS_constant gv;
        malloc_token Ews heap_type h;
         data_at Ews heap_type
                 ((p, (p, (offset_val (WORD_SIZE * NURSERY_SIZE) p)))
                    :: repeat zero_triple (Z.to_nat (MAX_SPACES - 1))) h;
         malloc_token Ews (tarray int_or_ptr_type NURSERY_SIZE) p;
         data_at_ Ews (tarray int_or_ptr_type NURSERY_SIZE) p).

Definition make_tinfo_spec :=
  DECLARE _make_tinfo
  WITH sh: share, gv: globals
  PRE []
    PROP (readable_share sh)
    PARAMS ()
    GLOBALS (gv)
    SEP (mem_mgr gv; all_string_constants sh gv; MSS_constant gv)
  POST [tptr thread_info_type]
    EX t: val, EX h: val, EX p: val,
    PROP () LOCAL (temp ret_temp t)
    SEP (mem_mgr gv; all_string_constants sh gv; MSS_constant gv;
         malloc_token Ews thread_info_type t;
         data_at Ews thread_info_type
                 (p, (offset_val (WORD_SIZE * NURSERY_SIZE) p,
                      (h, repeat Vundef (Z.to_nat MAX_ARGS)))) t;
         malloc_token Ews heap_type h;
         data_at Ews heap_type
                 ((p, (p, (offset_val (WORD_SIZE * NURSERY_SIZE) p)))
                    :: repeat zero_triple (Z.to_nat (MAX_SPACES - 1))) h;
         malloc_token Ews (tarray int_or_ptr_type NURSERY_SIZE) p;
         data_at_ Ews (tarray int_or_ptr_type NURSERY_SIZE) p).

Definition resume_spec :=
  DECLARE _resume
  WITH rsh: share, sh: share, gv: globals, fi: val, ti: val,
       g: LGraph, t_info: thread_info, f_info: fun_info,
       roots : roots_t
  PRE [tptr (if Archi.ptr64 then tulong else tuint),
       tptr thread_info_type]
    PROP (readable_share rsh; writable_share sh;
          graph_thread_info_compatible g t_info;
          graph_gen_clear g O)
    PARAMS (fi; ti)
    GLOBALS (gv)
    SEP (all_string_constants rsh gv;
         fun_info_rep rsh f_info fi;
         graph_rep g;
         thread_info_rep sh t_info ti)
  POST [tvoid]
    PROP (fun_word_size f_info <= total_space (heap_head (ti_heap t_info)))
    LOCAL ()
    SEP (all_string_constants rsh gv;
         fun_info_rep rsh f_info fi;
         graph_rep g;
         before_gc_thread_info_rep sh t_info ti).

Definition garbage_collect_spec :=
  DECLARE _garbage_collect
  WITH rsh: share, sh: share, gv: globals, fi: val, ti: val,
       g: LGraph, t_info: thread_info, f_info: fun_info,
       roots : roots_t, outlier: outlier_t
  PRE [tptr (if Archi.ptr64 then tulong else tuint),
       tptr thread_info_type]
    PROP (readable_share rsh; writable_share sh;
          super_compatible (g, t_info, roots) f_info outlier;
          garbage_collect_condition g t_info roots f_info;
          safe_to_copy g)
    PARAMS (fi; ti)
    GLOBALS (gv)
    SEP (all_string_constants rsh gv; MSS_constant gv;
         fun_info_rep rsh f_info fi;
         outlier_rep outlier;
         graph_rep g;
         before_gc_thread_info_rep sh t_info ti;
         ti_token_rep t_info)
  POST [tvoid]
    EX g': LGraph, EX t_info': thread_info, EX roots': roots_t,
    PROP (super_compatible (g', t_info', roots') f_info outlier;
          garbage_collect_relation f_info roots roots' g g';
          garbage_collect_condition g' t_info' roots' f_info;
          safe_to_copy g')
    LOCAL ()
    SEP (mem_mgr gv; MSS_constant gv;
         all_string_constants rsh gv;
         fun_info_rep rsh f_info fi;
         outlier_rep outlier;
         graph_rep g';
         before_gc_thread_info_rep sh t_info' ti;
         ti_token_rep t_info').

Definition reset_heap_spec :=
  DECLARE _reset_heap
  WITH h: val
  PRE [tptr heap_type]
    PROP ()
    PARAMS (h)
    GLOBALS ()
    SEP ()
  POST [tvoid]
  PROP () LOCAL () SEP ().

Definition free_heap_spec :=
  DECLARE _free_heap
  WITH h: val
  PRE [tptr heap_type]
    PROP () PARAMS (h) GLOBALS () SEP ()
  POST [tvoid]
  PROP () LOCAL () SEP ().
Definition Gprog: funspecs.
exact (ltac:(with_library prog
                     [test_int_or_ptr_spec;
                      int_or_ptr_to_int_spec;
                      int_or_ptr_to_ptr_spec;
                      int_to_int_or_ptr_spec;
                      ptr_to_int_or_ptr_spec;
                      Is_block_spec;
                      Is_from_spec;
                      abort_with_spec;
                      forward_spec;
                      forward_roots_spec;
                      do_scan_spec;
                      do_generation_spec;
                      create_space_spec;
                      create_heap_spec;
                      make_tinfo_spec;
                      resume_spec;
                      garbage_collect_spec;
                      reset_heap_spec;
                      free_heap_spec])).
Defined.

Lemma body_do_scan: semax_body Vprog Gprog f_do_scan do_scan_spec.
Proof.
  start_function.
  forward.
  forward_loop (EX n: nat, EX g': LGraph, EX t_info': thread_info,
                PROP (super_compatible (g', t_info', roots) f_info outlier;
                      forward_condition g' t_info' from to;
                      thread_info_relation t_info t_info';
                      closure_has_index g' to (to_index + n);
                      scan_vertex_while_loop from to (nat_seq to_index n) g g')
                LOCAL
                (temp _s (offset_val (- WORD_SIZE)
                                     (vertex_address g' (to, (to_index + n)%nat)));
                 temp _from_start (gen_start g' from);
                 temp _from_limit (limit_address g' t_info' from);
                 temp _next (next_address t_info' to))
                SEP (all_string_constants rsh gv; fun_info_rep rsh f_info fi;
               outlier_rep outlier; graph_rep g'; thread_info_rep sh t_info' ti))
  break: (EX g' : LGraph, EX t_info' : thread_info,
          PROP (super_compatible (g', t_info', roots) f_info outlier;
                forward_condition g' t_info' from to;
                do_scan_relation from to to_index g g';
                thread_info_relation t_info t_info')
          LOCAL ()
          SEP (all_string_constants rsh gv; fun_info_rep rsh f_info fi;
               outlier_rep outlier; graph_rep g'; thread_info_rep sh t_info' ti)).
  -
 Exists O g t_info.
destruct H as [? [? [? ?]]].
    replace (to_index + 0)%nat with to_index by lia.
entailer!.
    split; [|split]; [red; auto | apply tir_id | constructor].
  -
 Intros n g' t_info'.
remember (to_index + n)%nat as index.
    unfold next_address, thread_info_rep.
Intros.
    unfold heap_struct_rep.
destruct H5 as [? [? [? ?]]].
    destruct H6 as [? [? [? [? ?]]]].
    assert (0 <= Z.of_nat to < 12).
{
      clear -H5 H14.
destruct H5 as [_ [_ ?]].
red in H14.
      pose proof (spaces_size (ti_heap t_info')).
      rewrite Zlength_correct in H0.
rep_lia.
}
    destruct (gt_gs_compatible _ _ H5 _ H14) as [? [? ?]].
rewrite nth_space_Znth in *.
    remember (Znth (Z.of_nat to) (spaces (ti_heap t_info'))) as sp_to.
    assert (isptr (space_start sp_to)) by (rewrite <- H18; apply start_isptr).
    remember (map space_tri (spaces (ti_heap t_info'))).
    assert (@Znth (val * (val * val)) (Vundef, (Vundef, Vundef))
                  (Z.of_nat to) l = space_tri sp_to).
{
      subst l sp_to.
now rewrite Znth_map by (rewrite spaces_size; rep_lia).
}
    forward; rewrite H22; unfold space_tri.
1: entailer!.
    unfold vertex_address, vertex_offset.
rewrite offset_offset_val.
    simpl vgeneration; simpl vindex.
    replace (WORD_SIZE * (previous_vertices_size g' to index + 1) + - WORD_SIZE) with
        (WORD_SIZE * (previous_vertices_size g' to index))%Z by rep_lia.
    unfold gen_start at 1.
rewrite if_true by assumption.
rewrite H18.
    remember (WORD_SIZE * used_space sp_to)%Z as used_offset.
    remember (WORD_SIZE * previous_vertices_size g' to index)%Z as index_offset.
    freeze [0; 1; 2; 4; 5] FR.
    gather_SEP (graph_rep g') (heap_rest_rep (ti_heap t_info')).
    assert (
        forall b i,
          Vptr b i = space_start sp_to ->
          graph_rep g' * heap_rest_rep (ti_heap t_info') |--
      !! (WORD_SIZE * total_space sp_to + Ptrofs.unsigned i <= Ptrofs.max_unsigned)).
{
      intros.
sep_apply (graph_and_heap_rest_data_at_ _ _ _ H14 H5).
      assert (space_start sp_to = gen_start g' to) by
          (unfold gen_start; rewrite if_true by assumption;
           rewrite <- H18; reflexivity).
rewrite H24 in H23.
      sep_apply (generation_data_at__ptrofs g' t_info' to b i H23).
      unfold gen_size; rewrite nth_space_Znth; entailer!.
}
    assert_PROP (force_val
                   (sem_cmp_pp Clt (offset_val index_offset (space_start sp_to))
                               (offset_val used_offset (space_start sp_to))) =
                 Vint (if if zlt index_offset used_offset then true else false
                       then Int.one else Int.zero)).
{
      remember (space_start sp_to).
destruct v; try contradiction.
inv_int i.
      specialize (H23 b (Ptrofs.repr ofs) eq_refl).
      rewrite Ptrofs.unsigned_repr in H23 by rep_lia.
sep_apply H23.
Intros.
      assert (0 <= ofs + used_offset <= Ptrofs.max_unsigned).
{
        subst.
        pose proof (space_order (Znth (Z.of_nat to) (spaces (ti_heap t_info')))).
        unfold WORD_SIZE in *.
rep_lia.
}
      assert (0 <= ofs + index_offset <= Ptrofs.max_unsigned).
{
        subst.
red in H8.
pose proof (pvs_ge_zero g' to (to_index + n)%nat).
        pose proof (pvs_mono g' to _ _ H8).
unfold WORD_SIZE in *.
rep_lia.
}
      apply prop_right.
      rewrite force_sem_cmp_pp; [|rewrite isptr_offset_val; assumption..].
      simpl.
rewrite !ptrofs_add_repr, if_true.
2: reflexivity.
      unfold Ptrofs.ltu.
rewrite !Ptrofs.unsigned_repr; auto.
f_equal.
      if_tac; if_tac; try reflexivity; lia.
}
    forward_if (gen_has_index g' to index).
    +
 remember (Znth (Z.of_nat to) (spaces (ti_heap t_info'))) as sp_to.
      sep_apply (graph_and_heap_rest_data_at_ _ _ _ H14 H5).
      unfold generation_data_at_.
      assert (gen_start g' to = space_start sp_to) by
          (subst; unfold gen_start; rewrite if_true; assumption).
rewrite H31.
      rewrite data_at__memory_block.
Intros.
rewrite sizeof_tarray_int_or_ptr.
      2: unfold gen_size; apply total_space_range.
      remember (WORD_SIZE * used_space sp_to)%Z as used_offset.
      remember (to_index + n)%nat as index.
      remember (WORD_SIZE * previous_vertices_size g' to index)%Z as index_offset.
      destruct (space_start sp_to); try contradiction.
simpl.
unfold test_order_ptrs.
      simpl.
case (peq b b); intros.
2: contradiction.
simpl.
      assert (sepalg.nonidentity (nth_sh g' to)).
{
        apply readable_nonidentity, writable_readable_share.
unfold nth_sh.
        apply generation_share_writable.
}
      assert (forall offset,
                 0 <= offset <= used_offset ->
                 memory_block (nth_sh g' to) (WORD_SIZE * gen_size t_info' to)
                              (Vptr b i) * TT * FRZL FR |--
        weak_valid_pointer (Vptr b (Ptrofs.add i (Ptrofs.repr offset)))).
{
        intros.
change (Vptr b (Ptrofs.add i (Ptrofs.repr offset))) with
            (offset_val offset (Vptr b i)).
        sep_apply (memory_block_weak_valid_pointer
                     (nth_sh g' to) (WORD_SIZE * gen_size t_info' to)
                     (Vptr b i) offset); auto.
        3: apply extend_weak_valid_pointer.
        -
 subst.
unfold gen_size.
split.
1: apply (proj1 H34).
          transitivity (WORD_SIZE * used_space (nth_space t_info' to))%Z.
          +
 rewrite nth_space_Znth.
apply (proj2 H34).
          +
 apply Zmult_le_compat_l.
apply (proj2 (space_order _)).
            unfold WORD_SIZE.
lia.
        -
 clear -H3 H7.
destruct H7 as [? [? ?]].
          rewrite <- H0.
unfold WORD_SIZE.
lia.
}
      apply andp_right; apply H34.
      *
 subst.
split.
        1: pose proof (pvs_ge_zero g' to (to_index + n)%nat); unfold WORD_SIZE; lia.
        apply Zmult_le_compat_l.
2: unfold WORD_SIZE; lia.
rewrite <- H20.
        apply pvs_mono.
assumption.
      *
 split; [|lia]; subst; apply Z.mul_nonneg_nonneg;
                                  [unfold WORD_SIZE; lia | apply space_order].
    +
 assert (index_offset < used_offset).
{
        destruct (zlt index_offset used_offset); trivial.
        try solve [
           match type of H24 with force_val ?x = _ => destruct x; simpl in H24; subst; easy end];

            rewrite H24 in H25; unfold typed_true in H25; easy.
}
      forward.
entailer!.
red.
rewrite <- H20 in H26.
      rewrite <- Z.mul_lt_mono_pos_l in H26 by (unfold WORD_SIZE; lia).
      apply pvs_lt_rev in H26.
assumption.
    +
 assert (~ index_offset < used_offset).
{
        destruct (zlt index_offset used_offset); trivial.
        try solve [
           match type of H24 with force_val ?x = _ => destruct x; simpl in H24; subst; easy end];

        now rewrite H24 in H25; unfold typed_false in H25.
}
      forward.
thaw FR.
unfold thread_info_rep, heap_struct_rep.
      Exists g' t_info'.
unfold forward_condition.
entailer!.
      split; [red; auto | exists n; split; trivial].
      unfold gen_has_index.
rewrite <- H20 in H26.
      rewrite <- Z.mul_lt_mono_pos_l in H26 by (unfold WORD_SIZE; lia).
      intro; apply H26.
now apply pvs_mono_strict.
    +
 clear H8 H23 H24.
Intros.
thaw FR.
freeze [1;2;3;4;5;6] FR.
      assert (graph_has_v g' (to, index)) by easy.

      localize [vertex_rep (nth_sh g' to) g' (to, index)].
      assert (readable_share (nth_sh g' to)) by
          (unfold nth_sh; apply writable_readable_share, generation_share_writable).
      unfold vertex_rep, vertex_at.
Intros.
      assert (offset_val (- WORD_SIZE) (vertex_address g' (to, index)) =
              offset_val index_offset (space_start sp_to)).
{
        unfold vertex_address.
rewrite offset_offset_val.
unfold vertex_offset.
        simpl vgeneration.
simpl vindex.
        replace (WORD_SIZE * (previous_vertices_size g' to index + 1) + - WORD_SIZE)
          with index_offset by rep_lia.
        f_equal.
unfold gen_start.
        rewrite if_true by assumption; now rewrite H18.
}
      rewrite H25.
forward.
rewrite <- H25.
      gather_SEP (data_at _ _ _ _) (data_at _ _ _ _).
      replace_SEP 0 (vertex_rep (nth_sh g' to) g' (to, index)) by
          (unfold vertex_rep, vertex_at; entailer!).

Fail
      unlocalize [graph_rep g'];
        [ apply graph_vertex_ramif_stable; assumption | ].

eapply (unlocalize_triple [graph_rep g']); [ prove_split_FRZ_in_SEP | | ].
{

set (J := fst (RamG, H23)).
change RamG with J.
clear.

refine (ex_intro _ _ eq_refl).

Check J.
Check H23.
