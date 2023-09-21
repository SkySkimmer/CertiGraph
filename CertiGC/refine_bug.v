(* -*- mode: coq; coq-prog-args: ("-emacs" "-w" "-overriding-logical-loadpath" "-w" "-deprecated-native-compiler-option,-native-compiler-disabled" "-native-compiler" "ondemand" "-Q" "/github/workspace/cwd" "Top" "-Q" "/github/workspace/CertiGraph/lib" "CertiGraph.lib" "-Q" "/github/workspace/CertiGraph/msl_ext" "CertiGraph.msl_ext" "-Q" "/github/workspace/CertiGraph/msl_application" "CertiGraph.msl_application" "-Q" "/github/workspace/CertiGraph/graph" "CertiGraph.graph" "-Q" "/github/workspace/CertiGraph/heap_model_direct" "CertiGraph.heap_model_direct" "-Q" "/github/workspace/CertiGraph" "CertiGraph" "-Q" "/home/coq/.opam/4.13.1+flambda/lib/coq/user-contrib/VST" "VST" "-Q" "/home/coq/.opam/4.13.1+flambda/lib/coq/user-contrib/compcert" "compcert" "-Q" "/home/coq/.opam/4.13.1+flambda/lib/coq/user-contrib/Bignums" "Bignums" "-Q" "/home/coq/.opam/4.13.1+flambda/lib/coq/user-contrib/Flocq" "Flocq" "-Q" "/home/coq/.opam/4.13.1+flambda/lib/coq/user-contrib/Ltac2" "Ltac2" "-Q" "/home/coq/.opam/4.13.1+flambda/lib/coq/user-contrib/MenhirLib" "MenhirLib" "-top" "CertiGraph.CertiGC.refine_bug") -*- *)
(* File reduced by coq-bug-minimizer from original input, then from 248 lines to 293 lines, then from 306 lines to 1139 lines, then from 1144 lines to 745 lines, then from 758 lines to 2718 lines, then from 2722 lines to 1108 lines, then from 1120 lines to 836 lines, then from 849 lines to 1155 lines, then from 1160 lines to 909 lines *)
(* coqc version 8.17.1 compiled with OCaml 4.13.1
   coqtop version 8.17.1
   Expected coqc runtime on this file: 26.729 sec *)
Require Coq.Init.Ltac.
Require Coq.ZArith.ZArith.
Require Coq.Program.Basics.
Require Coq.micromega.Lia.
Require compcert.lib.Integers.
Require compcert.common.Values.
Require Coq.Arith.EqNat.
Require Coq.Relations.Relations.
Require compcert.lib.Axioms.
Require compcert.lib.Coqlib.
Require compcert.lib.Floats.
Require compcert.common.AST.
Require compcert.common.Memdata.
Require compcert.common.Memtype.
Require compcert.common.Memory.
Require compcert.common.Globalenvs.
Require Coq.Logic.ClassicalFacts.
Require Coq.Logic.FunctionalExtensionality.
Require VST.msl.Axioms.
Require Coq.Logic.EqdepFacts.
Require VST.msl.Extensionality.
Require Coq.Lists.List.
Require Coq.Bool.Bool.
Require VST.msl.base.
Require VST.msl.Coqlib2.
Require Coq.Sorting.Permutation.
Require VST.msl.eq_dec.
Require Coq.Sets.Ensembles.
Require Coq.Logic.ConstructiveEpsilon.
Require VST.veric.coqlib4.
Require VST.veric.base.
Require compcert.export.Clightdefs.
Require compcert.cfrontend.Ctypes.
Require compcert.cfrontend.Cop.
Require compcert.cfrontend.Clight.
Require compcert.lib.Maps.
Require VST.sepcomp.Address.
Require VST.veric.Memory.
Require VST.veric.Clight_base.
Require VST.veric.Clight_lemmas.
Require VST.veric.val_lemmas.
Require Coq.funind.Recdef.
Require Coq.Wellfounded.Wellfounded.
Require VST.msl.ageable.
Require VST.msl.sepalg.
Require VST.msl.sepalg_generators.
Require VST.msl.age_sepalg.
Require Coq.Structures.GenericMinMax.
Require VST.msl.boolean_alg.
Require VST.msl.functors.
Require Coq.Classes.RelationClasses.
Require VST.msl.predicates_hered.
Require Coq.Arith.Arith.
Require VST.msl.knot_full_variant.
Require VST.msl.sig_isomorphism.
Require Coq.Logic.Eqdep_dec.
Require VST.msl.knot.
Require VST.msl.knot_shims.
Require VST.msl.sepalg_functors.
Require CertiGraph.CertiGC.GCGraph.
Require CertiGraph.CertiGC.gc.
Require VST.floyd.library.
Require VST.floyd.proofauto.
Export VST.floyd.proofauto.
Export VST.floyd.library.
Export CertiGraph.CertiGC.gc.

#[export] Instance CompSpecs : compspecs.
make_compspecs prog.
Defined.
Definition Vprog : varspecs.
mk_varspecs prog.
Defined.
Definition thread_info_type : type. exact (Tstruct _thread_info noattr). Defined.
Definition space_type : type. exact (Tstruct _space noattr). Defined.
Definition heap_type: type. exact (Tstruct _heap noattr). Defined.
Import CertiGraph.CertiGC.GCGraph.

Local Open Scope logic.

Definition vertex_at (sh: share) (p: val) (header: Z) (lst_fields: list val) :=
  Eval cbv delta [Archi.ptr64] match
         in
         (data_at sh (if Archi.ptr64 then tulong else tuint)
                  (Z2val header) (offset_val (- WORD_SIZE) p) *
          data_at sh (tarray int_or_ptr_type (Zlength lst_fields)) lst_fields p).
Definition vertex_rep (sh: share) (g: LGraph) (v: VType): mpred.
exact (vertex_at sh (vertex_address g v) (make_header g v) (make_fields_vals g v)).
Defined.
Definition graph_rep (g: LGraph): mpred.
Admitted.

Definition fun_info_rep (sh: share) (fi: fun_info) (p: val) : mpred :=
  Eval cbv delta [Archi.ptr64] match
         in
         let len := Zlength (live_roots_indices fi) in
         data_at
           sh (tarray (if Archi.ptr64 then tulong else tuint) (len + 2))
           (map Z2val (fun_word_size fi :: len :: live_roots_indices fi)) p.
Definition heap_rest_rep (hp: heap): mpred.
Admitted.
Definition space_tri (sp: space): (reptype space_type).
exact (let s := sp.(space_start) in (s, (offset_val (WORD_SIZE * sp.(used_space)) s,
                                    offset_val (WORD_SIZE * sp.(total_space)) s))).
Defined.
Definition heap_struct_rep (sh: share) (sp_reps: list (@reptype CompSpecs space_type)) (h: val):
  mpred.
exact (@data_at CompSpecs sh heap_type sp_reps h).
Defined.

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
Program Definition weak_derives (P Q: mpred): mpred.
Admitted.

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
Definition ti_token_rep (ti: thread_info): mpred.
Admitted.
Export VST.veric.rmaps.
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
