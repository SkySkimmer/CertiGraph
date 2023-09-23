(* -*- mode: coq; coq-prog-args: ("-emacs" "-w" "-overriding-logical-loadpath" "-w" "-deprecated-native-compiler-option,-native-compiler-disabled" "-native-compiler" "ondemand" "-Q" "/github/workspace/cwd" "Top" "-Q" "/github/workspace/CertiGraph/lib" "CertiGraph.lib" "-Q" "/github/workspace/CertiGraph/msl_ext" "CertiGraph.msl_ext" "-Q" "/github/workspace/CertiGraph/msl_application" "CertiGraph.msl_application" "-Q" "/github/workspace/CertiGraph/graph" "CertiGraph.graph" "-Q" "/github/workspace/CertiGraph/heap_model_direct" "CertiGraph.heap_model_direct" "-Q" "/github/workspace/CertiGraph" "CertiGraph" "-Q" "/home/coq/.opam/4.13.1+flambda/lib/coq/user-contrib/VST" "VST" "-Q" "/home/coq/.opam/4.13.1+flambda/lib/coq/user-contrib/compcert" "compcert" "-Q" "/home/coq/.opam/4.13.1+flambda/lib/coq/user-contrib/Bignums" "Bignums" "-Q" "/home/coq/.opam/4.13.1+flambda/lib/coq/user-contrib/Flocq" "Flocq" "-Q" "/home/coq/.opam/4.13.1+flambda/lib/coq/user-contrib/Ltac2" "Ltac2" "-Q" "/home/coq/.opam/4.13.1+flambda/lib/coq/user-contrib/MenhirLib" "MenhirLib" "-top" "CertiGraph.CertiGC.refine_bug") -*- *)
(* File reduced by coq-bug-minimizer from original input, then from 248 lines to 293 lines, then from 306 lines to 1139 lines, then from 1144 lines to 745 lines, then from 758 lines to 2718 lines, then from 2722 lines to 1108 lines, then from 1120 lines to 836 lines, then from 849 lines to 1155 lines, then from 1160 lines to 909 lines, then from 727 lines to 139 lines, then from 152 lines to 655 lines, then from 657 lines to 144 lines, then from 157 lines to 1418 lines, then from 1420 lines to 199 lines, then from 212 lines to 2324 lines, then from 2327 lines to 228 lines, then from 241 lines to 2815 lines, then from 2818 lines to 249 lines, then from 262 lines to 6396 lines, then from 6401 lines to 363 lines, then from 376 lines to 1830 lines, then from 1830 lines to 363 lines, then from 376 lines to 981 lines, then from 985 lines to 364 lines, then from 377 lines to 3092 lines, then from 3076 lines to 366 lines, then from 379 lines to 3551 lines, then from 3552 lines to 375 lines, then from 388 lines to 692 lines, then from 696 lines to 375 lines, then from 388 lines to 849 lines, then from 853 lines to 387 lines, then from 400 lines to 866 lines, then from 871 lines to 385 lines, then from 398 lines to 3832 lines, then from 3835 lines to 504 lines, then from 517 lines to 3129 lines, then from 3133 lines to 2318 lines, then from 2311 lines to 515 lines, then from 528 lines to 2614 lines, then from 2616 lines to 628 lines, then from 641 lines to 978 lines, then from 983 lines to 635 lines, then from 648 lines to 2005 lines, then from 2005 lines to 732 lines, then from 745 lines to 1661 lines, then from 1665 lines to 753 lines, then from 766 lines to 2033 lines, then from 2037 lines to 778 lines, then from 791 lines to 1344 lines, then from 1349 lines to 772 lines, then from 785 lines to 2681 lines, then from 2660 lines to 893 lines, then from 895 lines to 811 lines, then from 824 lines to 1472 lines, then from 1476 lines to 823 lines, then from 836 lines to 2366 lines, then from 2371 lines to 840 lines, then from 853 lines to 1260 lines, then from 1261 lines to 892 lines, then from 905 lines to 960 lines, then from 965 lines to 904 lines, then from 917 lines to 1065 lines, then from 1070 lines to 885 lines, then from 898 lines to 1548 lines, then from 1553 lines to 889 lines, then from 902 lines to 1743 lines, then from 1748 lines to 922 lines, then from 935 lines to 2718 lines, then from 2718 lines to 997 lines *)
(* coqc version 8.17.1 compiled with OCaml 4.13.1
   coqtop version 8.17.1
   Expected coqc runtime on this file: 1.345 sec *)
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
Require Coq.Lists.ListSet.
Require compcert.common.AST.
Require compcert.common.Values.
Require compcert.common.Memory.
Require compcert.common.Globalenvs.
Require compcert.lib.Maps.
Require VST.sepcomp.extspec.
Require Coq.Arith.EqNat.
Require Coq.Relations.Relations.
Require compcert.lib.Axioms.
Require compcert.lib.Coqlib.
Require compcert.lib.Integers.
Require compcert.lib.Floats.
Require compcert.common.Memdata.
Require compcert.common.Memtype.
Require Coq.Logic.ClassicalFacts.
Require VST.msl.Axioms.
Require Coq.Logic.EqdepFacts.
Require VST.msl.Extensionality.
Require Coq.Bool.Bool.
Require VST.msl.base.
Require VST.msl.Coqlib2.
Require VST.msl.eq_dec.
Require Coq.Logic.ConstructiveEpsilon.
Require VST.veric.coqlib4.
Require VST.veric.base.
Require VST.sepcomp.Address.
Require VST.veric.Memory.
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
Require VST.veric.juicy_mem.
Require VST.veric.mpred.
Require VST.msl.ghost_seplog.
Require VST.msl.alg_seplog.
Require compcert.export.Clightdefs.
Export VST.veric.base.
Import VST.veric.compcert_rmaps.

 

Program Definition noat (l: AV.address) : pred rmap :=
    fun m => identity (m @ l).
Admit Obligations.

Module Export VST_DOT_veric_DOT_own_WRAPPED.
Module Export own.
Import VST.msl.ghost.
Import VST.veric.compcert_rmaps.
Local Open Scope pred.

Notation ghost_approx m := (ghost_fmap (approx (level m)) (approx (level m))).

Program Definition ghost_is g: pred rmap :=
  fun m => join_sub (ghost_approx m g) (ghost_of m).
Admit Obligations.

Definition Own g: pred rmap := allp noat && ghost_is g.

Program Definition bupd (P: pred rmap): pred rmap :=
  fun m => forall c, joins (ghost_of m) (ghost_approx m c) ->
    exists b, joins b (ghost_approx m c) /\
    exists m', level m' = level m /\ resource_at m' = resource_at m /\ ghost_of m' = b /\ P m'.
Admit Obligations.

Definition singleton {A} k (x : A) : list (option A) := repeat None k ++ Some x :: nil.

Definition gname := nat.

Definition own {RA: Ghost} (n: gname) (a: G) (pp: preds) :=
  EX v : _, Own (singleton n (existT _ RA (exist _ a v), pp)).

End own.
Module Export VST.
Module Export veric.
Module Export own.
Include VST_DOT_veric_DOT_own_WRAPPED.own.
End own.
Export VST.msl.ghost.

Notation "|==> P" := (own.bupd P) (at level 99, P at level 200): pred.
Export VST.veric.shares.
Definition ext_ref {Z} (ora : Z) : {g : Ghost & {a : G | valid a}}.
Admitted.
Export compcert.export.Clightdefs.
Export compcert.cfrontend.Ctypes.
Export compcert.cfrontend.Cop.
Export compcert.cfrontend.Clight.
Import VST.veric.val_lemmas.
Import compcert.lib.Maps.
Definition eqb_option {A} (f: A -> A -> bool) (x y: option A) : bool.
Admitted.
Definition eqb_attr (a b: attr) : bool.
Admitted.
Definition eqb_floatsize (a b: floatsize) : bool.
Admitted.
Definition eqb_ident : ident -> ident -> bool.
Admitted.
Definition eqb_intsize (a b: intsize) : bool.
Admitted.

Definition eqb_signedness (a b : signedness) :=
 match a, b with
 | Signed, Signed => true
 | Unsigned, Unsigned => true
 | _, _ => false
 end.

Definition eqb_calling_convention (a b: calling_convention) :=
 andb (eqb_option Z.eqb (cc_vararg a) (cc_vararg b))
     (andb  (eqb (cc_unproto a) (cc_unproto b))
      (eqb (cc_structret a) (cc_structret b))).

Fixpoint eqb_type (a b: type) {struct a} : bool :=
 match a, b with
 | Tvoid, Tvoid => true
 | Tint ia sa aa, Tint ib sb ab => andb (eqb_intsize ia ib)
                                                    (andb (eqb_signedness sa sb) (eqb_attr aa ab))
 | Tlong sa aa, Tlong sb ab => andb (eqb_signedness sa sb) (eqb_attr aa ab)
 | Tfloat sa aa, Tfloat sb ab => andb (eqb_floatsize sa sb) (eqb_attr aa ab)
 | Tpointer ta aa, Tpointer tb ab => andb (eqb_type ta tb) (eqb_attr aa ab)
 | Tarray ta sa aa, Tarray tb sb ab => andb (eqb_type ta tb)
                                                                   (andb (Zeq_bool sa sb) (eqb_attr aa ab))
 | Tfunction sa ta ca, Tfunction sb tb cb =>
       andb (andb (eqb_typelist sa sb) (eqb_type ta tb)) (eqb_calling_convention ca cb)
 | Tstruct ia aa, Tstruct ib ab => andb (eqb_ident ia ib) (eqb_attr aa ab)
 | Tunion ia aa, Tunion ib ab => andb (eqb_ident ia ib) (eqb_attr aa ab)
 | _, _ => false
 end
with eqb_typelist (a b: typelist)  {struct a}: bool :=
  match a, b with
  | Tcons ta ra, Tcons tb rb => andb (eqb_type ta tb) (eqb_typelist ra rb)
  | Tnil, Tnil => true
  | _ , _ => false
  end.
Definition int_or_ptr_type : type.
Admitted.
Definition tc_val (ty: type) : val -> Prop.
Admitted.

Definition tc_val' t v := v <> Vundef -> tc_val t v.
Import VST.veric.compcert_rmaps.
Import VST.veric.mpred.

Section Invariants.

Import Coq.Sets.Ensembles.

Global Arguments Union {_} _ _.
Global Arguments Disjoint {_} _ _.
Global Arguments Full_set {_}.

#[global] Polymorphic Program Instance set_PCM : Ghost := { valid := fun _ : Ensemble nat => True;
  Join_G a b c := Disjoint a b /\ c = Union a b }.
Admit Obligations.

Definition ghost_set g s := own(RA := set_PCM) g s NoneP.

Class invG := { g_inv : gname; g_en : gname; g_dis : gname }.
Definition wsat : mpred.
Admitted.

End Invariants.
Module Export fupd.

Section FancyUpdates.

Context {inv_names : invG}.

Definition fupd E1 E2 P :=
  ((wsat * ghost_set g_en E1) -* |==> |>FF || (wsat * ghost_set g_en E2 * P))%pred.

End FancyUpdates.

Inductive Annotation :=
  WeakAnnotation : (environ -> mpred) -> Annotation
| StrongAnnotation : (environ -> mpred) -> Annotation.

Inductive tycontext : Type :=
  mk_tycontext : forall (tyc_temps: PTree.t type)
                        (tyc_vars: PTree.t type)
                        (tyc_ret: type)
                        (tyc_globty: PTree.t type)
                        (tyc_globsp: PTree.t funspec)
                        (tyc_annot: PTree.t Annotation),
                             tycontext.
Definition temp_types (Delta: tycontext): PTree.t type.
Admitted.
Definition ret_type (Delta: tycontext) : type.
Admitted.
Definition local:  (environ -> Prop) -> environ->mpred.
Admitted.
Definition tc_environ (Delta: tycontext) : environ -> Prop.
Admitted.

Section invs.
Definition func_ptr (f: funspec) (v: val): mpred.
Admitted.
Definition typed_true (t: type) (v: val)  : Prop.
Admitted.
Definition typed_false (t: type)(v: val) : Prop.
Admitted.
Definition subst {A} (x: ident) (v: environ -> val) (P: environ -> A) : environ -> A.
Admitted.
Definition globals_only (rho: environ) : environ.
Admitted.

Fixpoint make_args (il: list ident) (vl: list val) (rho: environ)  :=
  match il, vl with
  | nil, nil => globals_only rho
  | i::il', v::vl' => env_set (make_args il' vl' rho) i v
   | _ , _ => rho
  end.

End invs.
Export VST.veric.lift.

Record ret_assert : Type := {
 RA_normal: environ->mpred;
 RA_break: environ->mpred;
 RA_continue: environ->mpred;
 RA_return: option val -> environ->mpred
}.
Import VST.sepcomp.extspec.
Import VST.veric.juicy_mem.

Record juicy_ext_spec (Z: Type) := {
  JE_spec:> external_specification juicy_mem external_function Z;
  JE_pre_hered: forall e t ge_s typs args z, hereditary age (ext_spec_pre JE_spec e t ge_s typs args z);
  JE_pre_ext: forall e t ge_s typs args z a a', ext_order a a' ->
    joins (ghost_of (m_phi a')) (Some (ext_ref z, NoneP) :: nil) ->
    ext_spec_pre JE_spec e t ge_s typs args z a ->
    ext_spec_pre JE_spec e t ge_s typs args z a';
  JE_post_hered: forall e t ge_s tret rv z, hereditary age (ext_spec_post JE_spec e t ge_s tret rv z);
  JE_post_ext: forall e t ge_s tret rv z, hereditary ext_order (ext_spec_post JE_spec e t ge_s tret rv z);
  JE_exit_hered: forall rv z, hereditary age (ext_spec_exit JE_spec rv z);
  JE_exit_ext: forall rv z, hereditary ext_order (ext_spec_exit JE_spec rv z)
}.

Class OracleKind := {
  OK_ty : Type;
  OK_spec: juicy_ext_spec OK_ty
}.

#[ global] Instance inv_names : invG := { g_inv := 1%nat; g_en := 2%nat; g_dis := 3%nat}.
Module Export Clight_Cop2.
Definition sem_cast (t1 t2: type): val -> option val.
Admitted.
Definition sem_unary_operation
            (op: Cop.unary_operation) (ty: type) (v: val): option val.
Admitted.
Definition sem_binary_operation'
    {CS: compspecs} (op: Cop.binary_operation)
    (t1:type) (t2: type) : val -> val -> option val.
Admitted.
Import LiftNotation.

Definition eval_unop (op: Cop.unary_operation) (t1 : type) :=
       force_val1 (Clight_Cop2.sem_unary_operation op t1).

Definition is_comparison op :=
match op with
  | Cop.Oeq | Cop.One | Cop.Olt | Cop.Ogt | Cop.Ole | Cop.Oge => true
  | _ => false
end.

Definition eval_binop {CS:compspecs} (op: Cop.binary_operation) (t1 t2 : type) :=
       force_val2 (Clight_Cop2.sem_binary_operation'  op t1 t2).

Definition eval_cast (t1 t2 : type) :=
  force_val1 (sem_cast t1 t2).
Definition eval_field {CS: compspecs} (ty: type) (fld: ident) : val -> val.
Admitted.
Definition eval_var (id:ident) (ty: type) (rho: environ) : val.
Admitted.

Fixpoint eval_expr {CS: compspecs} (e: expr) : environ -> val :=
 match e with
 | Econst_int i ty => `(Vint i)
 | Econst_long i ty => `(Vlong i)
 | Econst_float f ty => `(Vfloat f)
 | Econst_single f ty => `(Vsingle f)
 | Etempvar id ty => eval_id id
 | Eaddrof a ty => eval_lvalue a
 | Eunop op a ty =>  `(eval_unop op (typeof a)) (eval_expr a)
 | Ebinop op a1 a2 ty =>
                  `(eval_binop op (typeof a1) (typeof a2)) (eval_expr a1) (eval_expr a2)
 | Ecast a ty => `(eval_cast (typeof a) ty) (eval_expr a)
 | Evar id ty => eval_var id ty
 | Ederef a ty => eval_expr a
 | Efield a i ty => `(eval_field (typeof a) i) (eval_lvalue a)
 | Esizeof t ty => `(if complete_type cenv_cs t
                             then Vptrofs (Ptrofs.repr (sizeof t)) else Vundef)
 | Ealignof t ty => `(if complete_type cenv_cs t
                             then Vptrofs (Ptrofs.repr (alignof t)) else Vundef)
 end

 with eval_lvalue {CS: compspecs} (e: expr) : environ -> val :=
 match e with
 | Evar id ty => eval_var id ty
 | Ederef a ty => eval_expr a
 | Efield a i ty => `(eval_field (typeof a) i) (eval_lvalue a)
 | _  => `Vundef
 end.

Fixpoint eval_exprlist {CS: compspecs} (et: list type) (el:list expr) : environ -> list val :=
 match et, el with
 | t::et', e::el' =>
    `(@cons val) (`force_val (`(sem_cast (typeof e) t) (eval_expr e))) (eval_exprlist et' el')
 | _, _ => `nil
 end.
Definition bool_type (t: type) : bool.
Admitted.

Definition is_int_type ty :=
match ty with
| Tint _ _ _ => true
| _ => false
end.

Definition is_neutral_cast t1 t2 :=
 match t1, t2 with
 | Tint IBool _ _, Tint _ _ _ => true
 | Tint I8 Signed _, Tint I8 Signed _ => true
 | Tint I8 Signed _, Tint I16 Signed _ => true
 | Tint I16 Signed _, Tint I16 Signed _ => true
 | Tint I8 Unsigned _, Tint I8 Unsigned _ => true
 | Tint I8 Unsigned _, Tint I16 Unsigned _ => true
 | Tint I16 Unsigned _, Tint I16 Unsigned _ => true
 | Tint _ _ _, Tint I32 _ _ => true
 | Tlong _ _, Tlong _ _ => true
 | Tfloat F64 _, Tfloat F64 _ => true
 | Tfloat F32 _, Tfloat F32 _ => true
 | Tpointer _ _, Tpointer _ _ => eqb_type t1 t2
                    || negb (eqb_type t1 int_or_ptr_type)
                     && negb (eqb_type t2 int_or_ptr_type)
 | _, _ => false
 end.

Definition size_compatible {C: compspecs} t p :=
  match p with
  | Vptr b i_ofs => Ptrofs.unsigned i_ofs + sizeof t < Ptrofs.modulus
  | _ => True
  end.
Export VST.msl.seplog.
Export VST.msl.ghost_seplog.
Export VST.veric.composite_compute.
Export VST.veric.align_mem.
Import VST.veric.own.
Import compcert.cfrontend.Ctypes.

#[export] Program Instance Bveric: BupdSepLog mpred gname compcert_rmaps.RML.R.preds :=
  { bupd := bupd; own := @own }.
Admit Obligations.

#[export] Program Instance Fveric: FupdSepLog mpred gname compcert_rmaps.RML.R.preds nat :=
  { fupd := fupd.fupd }.
Admit Obligations.

Local Open Scope logic.

Definition cast_pointer_to_bool t1 t2 :=
 match t1 with (Tpointer _ _ | Tarray _ _ _ | Tfunction _ _ _) =>
           match t2 with Tint IBool _ _ => true | _ => false end
 | _ => false
end.

Definition cast_expropt {CS: compspecs} (e: option expr) t : environ -> option val :=
 match e with Some e' => `Some (eval_expr (Ecast e' t))  | None => `None end.

Definition typecheck_tid_ptr_compare
Delta id :=
match (temp_types Delta) ! id with
| Some t => is_int_type t
| None => false
end.
Definition mapsto (sh: Share.t) (t: type) (v1 v2 : val): mpred.
Admitted.

Definition mapsto_ sh t v1 := mapsto sh t v1 Vundef.

Definition globals := ident -> val.

Definition align_compatible {C: compspecs} t p :=
  match p with
  | Vptr b i_ofs => align_compatible_rec cenv_cs t (Ptrofs.unsigned i_ofs)
  | _ => True
  end.
Definition allp_fun_id (Delta : tycontext) (rho : environ): mpred.
Admitted.

Definition tc_fn_return (Delta: tycontext) (ret: option ident) (t: type) :=
 match ret with
 | None => True
 | Some i => match (temp_types Delta) ! i with Some t' => t=t' | _ => False end
 end.
Definition ret_temp : ident.
Admitted.
Definition get_result1 (ret: ident) (rho: environ) : environ.
Admitted.

Definition maybe_retval (Q: assert) retty ret :=
 match ret with
 | Some id => fun rho => !!(tc_val' retty (eval_id id rho)) && Q (get_result1 id rho)
 | None =>
    match retty with
    | Tvoid => (fun rho => Q (globals_only rho))
    | _ => fun rho => EX v: val, !!(tc_val' retty v) && Q (make_args (ret_temp::nil) (v::nil) rho)
    end
 end.

Definition overridePost  (Q: environ->mpred)  (R: ret_assert) :=
 match R with
  {| RA_normal := _; RA_break := b; RA_continue := c; RA_return := r |} =>
  {| RA_normal := Q; RA_break := b; RA_continue := c; RA_return := r |}
 end.
Definition normal_ret_assert (Q: environ->mpred) : ret_assert.
Admitted.
Definition switch_ret_assert (R: ret_assert) : ret_assert.
Admitted.
Definition loop1_ret_assert (Inv: environ->mpred) (R: ret_assert) : ret_assert.
Admitted.
Definition loop2_ret_assert (Inv: environ->mpred) (R: ret_assert) : ret_assert.
Admitted.
Definition tc_temp_id  (id: ident)  (ty: type) {CS: compspecs} (Delta: tycontext)
                       (e:expr): environ -> mpred.
Admitted.
Definition typeof_temp (Delta: tycontext) (id: ident) : option type.
Admitted.
Definition tc_expr {CS: compspecs} (Delta: tycontext) (e: expr) : environ -> mpred.
Admitted.
Definition tc_exprlist {CS: compspecs} (Delta: tycontext) (t: list type) (e: list expr)  : environ -> mpred.
Admitted.
Definition tc_lvalue {CS: compspecs} (Delta: tycontext) (e: expr) : environ -> mpred.
Admitted.

Definition tc_expropt {CS: compspecs} Delta (e: option expr) (t: type) : environ -> mpred :=
   match e with None => `!!(t=Tvoid)
                     | Some e' => tc_expr Delta (Ecast e' t)
   end.

Definition blocks_match op v1 v2  :=
match op with Cop.Olt | Cop.Ogt | Cop.Ole | Cop.Oge =>
  match v1, v2 with
    Vptr b _, Vptr b2 _ => b=b2
    | _, _ => False
  end
| _ => True
end.
Definition decode_encode_val_ok (chunk1 chunk2: memory_chunk) : Prop.
Admitted.
Definition numeric_type (t: type) : bool.
Admitted.
Definition obox (Delta: tycontext) (i: ident) (P: environ -> mpred): environ -> mpred.
Admitted.

Definition oboxopt Delta ret P :=
  match ret with
  | Some id => obox Delta id P
  | _ => P
  end.

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

