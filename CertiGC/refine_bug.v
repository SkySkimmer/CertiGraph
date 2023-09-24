(* -*- mode: coq; coq-prog-args: ("-emacs" "-w" "-overriding-logical-loadpath" "-w" "-deprecated-native-compiler-option,-native-compiler-disabled" "-native-compiler" "ondemand" "-Q" "/github/workspace/cwd" "Top" "-Q" "/github/workspace/CertiGraph/lib" "CertiGraph.lib" "-Q" "/github/workspace/CertiGraph/msl_ext" "CertiGraph.msl_ext" "-Q" "/github/workspace/CertiGraph/msl_application" "CertiGraph.msl_application" "-Q" "/github/workspace/CertiGraph/graph" "CertiGraph.graph" "-Q" "/github/workspace/CertiGraph/heap_model_direct" "CertiGraph.heap_model_direct" "-Q" "/github/workspace/CertiGraph" "CertiGraph" "-Q" "/home/coq/.opam/4.13.1+flambda/lib/coq/user-contrib/VST" "VST" "-Q" "/home/coq/.opam/4.13.1+flambda/lib/coq/user-contrib/compcert" "compcert" "-Q" "/home/coq/.opam/4.13.1+flambda/lib/coq/user-contrib/Bignums" "Bignums" "-Q" "/home/coq/.opam/4.13.1+flambda/lib/coq/user-contrib/Flocq" "Flocq" "-Q" "/home/coq/.opam/4.13.1+flambda/lib/coq/user-contrib/Ltac2" "Ltac2" "-Q" "/home/coq/.opam/4.13.1+flambda/lib/coq/user-contrib/MenhirLib" "MenhirLib" "-top" "CertiGraph.CertiGC.refine_bug") -*- *)
(* File reduced by coq-bug-minimizer from original input, then from 248 lines to 293 lines, then from 306 lines to 1139 lines, then from 1144 lines to 745 lines, then from 758 lines to 2718 lines, then from 2722 lines to 1108 lines, then from 1120 lines to 836 lines, then from 849 lines to 1155 lines, then from 1160 lines to 909 lines, then from 727 lines to 139 lines, then from 152 lines to 655 lines, then from 657 lines to 144 lines, then from 157 lines to 1418 lines, then from 1420 lines to 199 lines, then from 212 lines to 2324 lines, then from 2327 lines to 228 lines, then from 241 lines to 2815 lines, then from 2818 lines to 249 lines, then from 262 lines to 6396 lines, then from 6401 lines to 363 lines, then from 376 lines to 1830 lines, then from 1830 lines to 363 lines, then from 376 lines to 981 lines, then from 985 lines to 364 lines, then from 377 lines to 3092 lines, then from 3076 lines to 366 lines, then from 379 lines to 3551 lines, then from 3552 lines to 375 lines, then from 388 lines to 692 lines, then from 696 lines to 375 lines, then from 388 lines to 849 lines, then from 853 lines to 387 lines, then from 400 lines to 866 lines, then from 871 lines to 385 lines, then from 398 lines to 3832 lines, then from 3835 lines to 504 lines, then from 517 lines to 3129 lines, then from 3133 lines to 2318 lines, then from 2311 lines to 515 lines, then from 528 lines to 2614 lines, then from 2616 lines to 628 lines, then from 641 lines to 978 lines, then from 983 lines to 635 lines, then from 648 lines to 2005 lines, then from 2005 lines to 732 lines, then from 745 lines to 1661 lines, then from 1665 lines to 753 lines, then from 766 lines to 2033 lines, then from 2037 lines to 778 lines, then from 791 lines to 1344 lines, then from 1349 lines to 772 lines, then from 785 lines to 2681 lines, then from 2660 lines to 893 lines, then from 895 lines to 811 lines, then from 824 lines to 1472 lines, then from 1476 lines to 823 lines, then from 836 lines to 2366 lines, then from 2371 lines to 840 lines, then from 853 lines to 1260 lines, then from 1261 lines to 892 lines, then from 905 lines to 960 lines, then from 965 lines to 904 lines, then from 917 lines to 1065 lines, then from 1070 lines to 885 lines, then from 898 lines to 1548 lines, then from 1553 lines to 889 lines, then from 902 lines to 1743 lines, then from 1748 lines to 922 lines, then from 935 lines to 2718 lines, then from 2718 lines to 997 lines, then from 1008 lines to 924 lines, then from 937 lines to 1221 lines, then from 1226 lines to 942 lines, then from 955 lines to 1291 lines, then from 1296 lines to 984 lines, then from 997 lines to 1278 lines, then from 1282 lines to 1088 lines, then from 1101 lines to 1553 lines, then from 1557 lines to 1167 lines, then from 1180 lines to 1495 lines, then from 1500 lines to 1176 lines, then from 1189 lines to 1340 lines, then from 1343 lines to 1218 lines, then from 1231 lines to 3579 lines, then from 3574 lines to 1250 lines, then from 1263 lines to 1367 lines, then from 1372 lines to 1266 lines, then from 1278 lines to 1254 lines, then from 1267 lines to 2204 lines, then from 2208 lines to 1277 lines, then from 1290 lines to 3502 lines, then from 3499 lines to 1281 lines, then from 1294 lines to 3043 lines, then from 3046 lines to 1542 lines, then from 1555 lines to 2919 lines, then from 2921 lines to 1551 lines, then from 1564 lines to 1653 lines, then from 1658 lines to 1567 lines, then from 1580 lines to 1567 lines, then from 1580 lines to 2131 lines, then from 2135 lines to 1537 lines, then from 1550 lines to 2714 lines, then from 2713 lines to 1557 lines, then from 1570 lines to 2436 lines, then from 2437 lines to 1569 lines, then from 1582 lines to 2503 lines, then from 2506 lines to 1578 lines, then from 1591 lines to 1575 lines, then from 1588 lines to 9598 lines, then from 9590 lines to 1673 lines, then from 1686 lines to 2310 lines, then from 2313 lines to 1674 lines, then from 1687 lines to 2544 lines, then from 2546 lines to 2189 lines *)
(* coqc version 8.17.1 compiled with OCaml 4.13.1
   coqtop version 8.17.1
   Expected coqc runtime on this file: 1.742 sec *)
Require Coq.Init.Ltac.
Require Coq.Logic.ClassicalFacts.
Require Coq.Logic.FunctionalExtensionality.
Require VST.msl.Axioms.
Require Coq.Logic.EqdepFacts.
Require VST.msl.Extensionality.
Require Coq.Lists.List.
Require Coq.Bool.Bool.
Require Coq.Relations.Relations.
Require Coq.micromega.Lia.
Require VST.msl.base.
Require VST.msl.eq_dec.
Require VST.msl.sepalg.
Require Coq.Structures.GenericMinMax.
Require VST.msl.boolean_alg.
Require Coq.Logic.ProofIrrelevance.
Require Coq.Setoids.Setoid.
Require Coq.Classes.Morphisms.
Require Coq.Classes.Equivalence.
Require Coq.Sets.Ensembles.
Require Coq.Sets.Constructive_sets.
Require Coq.Relations.Relation_Definitions.
Require Coq.Program.Basics.
Require CertiGraph.lib.Coqlib.
Require Coq.Classes.EquivDec.
Require CertiGraph.lib.EquivDec_ext.
Require CertiGraph.lib.Ensembles_ext.
Require Coq.Sorting.Permutation.
Require Coq.ZArith.ZArith_base.
Require Coq.ZArith.Zcomplements.
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
Require compcert.lib.Axioms.
Require compcert.lib.Coqlib.
Require compcert.lib.Integers.
Require compcert.lib.Floats.
Require compcert.common.Memdata.
Require compcert.common.Memtype.
Require VST.sepcomp.Address.
Require VST.veric.Memory.
Require VST.msl.ghost.
Require compcert.cfrontend.Ctypes.
Require VST.msl.Coqlib2.
Require Coq.Logic.ConstructiveEpsilon.
Require VST.veric.coqlib4.
Require VST.veric.base.
Require Coq.Sorting.Sorting.
Require Coq.Structures.Orders.
Require VST.veric.composite_compute.
Require VST.veric.type_induction.
Require VST.veric.align_mem.
Require VST.veric.compspecs.
Require VST.msl.sig_isomorphism.
Require VST.msl.functors.
Require Coq.funind.Recdef.
Require Coq.Wellfounded.Wellfounded.
Require VST.msl.ageable.
Require Coq.Logic.Eqdep_dec.
Require VST.msl.knot.
Require Coq.Classes.RelationClasses.
Require VST.msl.predicates_hered.
Require Coq.Arith.Arith.
Require VST.msl.knot_full_variant.
Require VST.msl.knot_shims.
Require compcert.export.Clightdefs.

Module Export AdmitTactic.
Module Import LocalFalse.
Inductive False : Prop := .
End LocalFalse.
Axiom proof_admitted : False.
Import Coq.Init.Ltac.
Tactic Notation "admit" := abstract case proof_admitted.
End AdmitTactic.

Module Export VST_DOT_msl_DOT_sepalg_generators_WRAPPED.
Module Export sepalg_generators.
 

 
Import VST.msl.base.
Import VST.msl.sepalg.
#[global] Instance Join_unit : Join unit. exact (fun x y z => True). Defined.

  #[global] Instance Perm_unit : Perm_alg unit.
Admitted.

  #[global] Instance Sep_unit: FSep_alg unit.
Admitted.

  #[global] Instance Sing_unit: Sing_alg unit.
Admitted.

  #[global] Instance Canc_unit: Canc_alg unit.
Admitted.

  #[global] Instance Disj_unit: Disj_alg unit.
Admitted.

  #[global] Instance Cross_unit: Cross_alg unit.
Admitted.

 

  Inductive Void : Type :=.
#[global] Instance Join_void : Join Void. exact (fun x y z => False). Defined.

  #[global] Instance Perm_void : Perm_alg Void.
Admitted.
  #[global] Instance Sep_void: FSep_alg Void.
Admitted.
  #[global] Instance Canc_void: Canc_alg Void.
Admitted.
  #[global] Instance Disj_void: Disj_alg Void.
Admitted.
  #[global] Instance Cross_void: Cross_alg Void.
Admitted.

 

  Inductive join_bool : bool -> bool -> bool -> Prop :=
  | jb_fff: join_bool false false false
  | jb_tft: join_bool true false true
  | jb_ftt: join_bool false true true.
#[global] Instance Join_bool : Join bool. exact (join_bool). Defined.

  #[global] Instance Perm_bool: Perm_alg bool.
Admitted.

  #[global] Instance Sep_bool: FSep_alg bool.
Admitted.

  #[global] Instance Sing_bool: Sing_alg bool.
Admitted.

  #[global] Instance Canc_bool: Canc_alg bool.
Admitted.

  #[global] Instance Disj_bool: Disj_alg bool.
Admitted.

  #[global] Instance Cross_bool: Cross_alg bool.
Admitted.

Section JOIN_EQUIV.
#[local] Instance Join_equiv (A: Type) : Join A. exact (fun x y z => x=y/\y=z). Defined.

  #[local] Instance Perm_equiv (A: Type) :  @Perm_alg A (Join_equiv A).
Admitted.

  #[local] Instance Sep_equiv (A: Type): FSep_alg A.
Admitted.

  #[local] Instance Canc_equiv (A: Type): Canc_alg A.
Admitted.

  #[local] Instance Disj_equiv (A: Type): Disj_alg A.
Admitted.

  #[local] Instance Cross_equiv (A: Type): Cross_alg A.
Admitted.

Lemma join_equiv_refl: forall A (v: A), @join A (Join_equiv A) v v v.
Admitted.
End JOIN_EQUIV.

 
#[global] Existing Instance Perm_equiv.
#[global] Existing Instance Sep_equiv.
#[global] Existing Instance Canc_equiv.
#[global] Existing Instance Disj_equiv.
#[global] Existing Instance Cross_equiv.

#[export] Hint Extern 1 (@join _ _ _ _ _) =>
   match goal with |- @join _ (@Join_equiv _) _ _ _ => apply join_equiv_refl end
   : core.

Section SepAlgProp.
  Variable A:Type.
  Variable JOIN: Join A.
  Variable PA: Perm_alg A.
  Variable P:A -> Prop.

  Variable HPjoin : forall x y z, join x y z -> P x -> P y -> P z.
#[global] Instance Join_prop : Join (sig P). exact (fun x y z: (sig P) => join (proj1_sig x) (proj1_sig y) (proj1_sig z)). Defined.

  #[global] Instance Perm_prop : Perm_alg (sig P).
Admitted.

  #[global] Instance Sep_prop (SA: Sep_alg A)(HPcore : forall x, P x -> P (core x)): Sep_alg (sig P).
Admitted.

 #[global] Instance Sing_prop  (SA: Sep_alg A)(Sing_A: Sing_alg A)
               (HPcore : forall x, P x -> P (core x)): P the_unit ->
    @Sing_alg (sig P) Join_prop (Sep_prop _ HPcore).
Admitted.

  #[global] Instance Canc_prop  {CA: Canc_alg A}:  Canc_alg (sig P).
Admitted.

  #[global] Instance Disj_prop {DA: Disj_alg A}: Disj_alg (sig P).
Admitted.

 

End SepAlgProp.
#[global] Existing Instance Join_prop.
#[global] Existing Instance Perm_prop.
#[global] Existing Instance Sep_prop.
#[global] Existing Instance Sing_prop.
#[global] Existing Instance Canc_prop.
#[global] Existing Instance Disj_prop.

 
Section SepAlgFun.
  Variable key: Type.
  Variable t' : Type.
  Variable JOIN: Join t'.
  Variable Pt': Perm_alg t'.
#[global] Instance Join_fun: Join (key -> t'). exact (fun a b c : key -> t' => forall x, join (a x) (b x) (c x)). Defined.

  #[global] Instance Perm_fun : Perm_alg (key -> t').
Admitted.

  #[global] Instance Sep_fun (SA: Sep_alg t'): Sep_alg (key -> t').
Admitted.

 #[global] Instance Sing_fun (SA: Sep_alg t'): Sing_alg t' -> Sing_alg (key -> t').
Admitted.

 #[global] Instance Canc_fun: Canc_alg t' -> Canc_alg (key -> t').
Admitted.

 #[global] Instance Disj_fun: Disj_alg t' -> Disj_alg (key -> t').
Admitted.
End SepAlgFun.

#[global] Existing Instance Join_fun.
#[global] Existing Instance Perm_fun.
#[global] Existing Instance Sep_fun.
#[global] Existing Instance Sing_fun.
#[global] Existing Instance Canc_fun.
#[global] Existing Instance Disj_fun.

 

Section SepAlgPi.
  Variable I:Type.
  Variable Pi: I -> Type.
  Variable pi_J: forall i, Join (Pi i).
  Variable PA:  forall i, Perm_alg (Pi i).

  Let P := forall i:I, Pi i.
#[global] Instance Join_pi: Join P. exact (fun x y z => forall i:I, join (x i) (y i) (z i)). Defined.

  #[global] Instance Perm_pi  : Perm_alg P.
Admitted.

  #[global] Instance Sep_pi (SA : forall i:I, Sep_alg (Pi i)): Sep_alg P.
Admitted.

  #[global] Instance Canc_pi: (forall i, Canc_alg (Pi i)) -> Canc_alg P.
Admitted.

  #[global] Instance Disj_pi: (forall i, Disj_alg (Pi i)) -> Disj_alg P.
Admitted.

End SepAlgPi.
#[global] Existing Instance Join_pi.
#[global] Existing Instance Perm_pi.
#[global] Existing Instance Sep_pi.
#[global] Existing Instance Canc_pi.
#[global] Existing Instance Disj_pi.

 
Section SepAlgSigma.
  Variable I:Type.
  Variable Sigma: I -> Type.
  Variable JOIN: forall i, Join (Sigma i).
  Variable PA: forall i, Perm_alg (Sigma i).
  Let S := sigT Sigma.

  Inductive join_sigma : S -> S -> S -> Prop :=
    j_sig_def : forall (i:I) (a b c:Sigma i),
      join a b c ->
      join_sigma (existT Sigma i a) (existT Sigma i b) (existT Sigma i c).
#[global] Instance Join_sigma: Join S. exact (join_sigma). Defined.

  #[global] Instance Perm_sigma: Perm_alg S.
Admitted.

  #[global] Instance Sep_sigma (SA : forall i:I, Sep_alg (Sigma i)) : Sep_alg S.
Admitted.

  #[global] Instance Canc_sigma: (forall i, Canc_alg (Sigma i)) -> Canc_alg S.
Admitted.

  #[global] Instance Disj_sigma: (forall i, Disj_alg (Sigma i)) -> Disj_alg S.
Admitted.
End SepAlgSigma.

#[global] Existing Instance Join_sigma.
#[global] Existing Instance Perm_sigma.
#[global] Existing Instance Sep_sigma.
#[global] Existing Instance Canc_sigma.
#[global] Existing Instance Disj_sigma.

 
Section SepAlgProd.

  Variables (A: Type) (Ja: Join A).
  Variables (B: Type) (Jb: Join B) .
#[local] Instance Join_prod : Join (A*B). exact (fun (x y z:A*B) =>  join (fst x) (fst y) (fst z) /\ join (snd x) (snd y) (snd z)). Defined.

  Variables (PAa: Perm_alg A)(PAb: Perm_alg B).
  #[local] Instance Perm_prod  : Perm_alg (A*B).
Admitted.

  #[global] Instance Sep_prod (SAa: Sep_alg A) (SAb: Sep_alg B) : Sep_alg (A*B).
Admitted.

  #[global] Instance Sing_prod {SAa: Sep_alg A} {SAb: Sep_alg B} {SingA: Sing_alg A}{SingB: Sing_alg B}: Sing_alg (A*B).
Admitted.

  #[global] Instance Canc_prod {CAa: Canc_alg A} {CAb:  Canc_alg B}: Canc_alg (A*B).
Admitted.

  #[global] Instance Disj_prod {DAa: Disj_alg A} {DAb:  Disj_alg B}: Disj_alg (A*B).
Admitted.

End SepAlgProd.

Arguments Perm_prod [A] [Ja] [B] [Jb] _ _.
Arguments Sep_prod [A] [Ja] [B] [Jb] [PAa] [PAb] _ _.
#[global] Existing Instance Join_prod.
#[global] Existing Instance Perm_prod.
#[global] Existing Instance Sep_prod.
#[global] Existing Instance Canc_prod.
#[global] Existing Instance Disj_prod.

 
Section SepAlgSum.

  Variables (A: Type) (Ja: Join A) .
  Variables (B: Type) (Jb: Join B) .
  Variables (PAa: Perm_alg A) (PAb: Perm_alg B).
#[global] Instance Join_sum : Join (A+B). exact ((fun (x y z: A+B) =>
    match x, y, z with
    | inl xa, inl ya, inl za => join xa ya za
    | inr xb, inr yb, inr zb => join xb yb zb
    | _, _, _ => False
    end)). Defined.

  #[global] Instance Perm_sum: Perm_alg (A+B).
Admitted.

  #[global] Instance Sep_sum (SAa: Sep_alg A) (SAb: Sep_alg B): Sep_alg (A+B).
Admitted.

  #[global] Instance Canc_sum {CAa: Canc_alg A} {CAb:  Canc_alg B}: Canc_alg (A+B).
Admitted.

  #[global] Instance Disj_sum {DAa: Disj_alg A} {DAb:  Disj_alg B}: Disj_alg (A+B).
Admitted.

End SepAlgSum.
#[global] Existing Instance Join_sum.
#[global] Existing Instance Perm_sum.
#[global] Existing Instance Sep_sum.
#[global] Existing Instance Canc_sum.
#[global] Existing Instance Disj_sum.

 
Section sa_list.

  Variables (A: Type) (Ja: Join A)  (PAa: Perm_alg A).

  Inductive list_join : list A -> list A -> list A -> Prop :=
  | lj_nil : list_join nil nil nil
  | lj_cons : forall x y z xs ys zs,
      join x y z ->
      list_join xs ys zs ->
      list_join (x::xs) (y::ys) (z::zs).
#[global] Instance Join_list: Join (list A). exact (list_join). Defined.

  #[global] Instance Perm_list: Perm_alg (list A).
Admitted.

  #[global] Instance Sep_list (SAa: Sep_alg A) : Sep_alg (list A).
Admitted.

  #[global] Instance Canc_list {CA: Canc_alg A}: Canc_alg (list A).
Admitted.

  #[global] Instance Disj_list {DAa: Disj_alg A} : Disj_alg (list A).
Admitted.

End sa_list.
#[global] Existing Instance Join_list.
#[global] Existing Instance Perm_list.
#[global] Existing Instance Sep_list.
#[global] Existing Instance Canc_list.
#[global] Existing Instance Disj_list.

 

Definition raw_join_hom A B (j1: A -> A -> A -> Prop) (j2: B -> B -> B -> Prop) (f:A ->B) :=
  forall x y z,
    j1 x y z ->
    j2 (f x) (f y) (f z).
Arguments raw_join_hom [A B] _ _ _.

Definition join_hom {A} {JA: Join A} {B} {JB: Join B} (f:A ->B) :=
  forall x y z,
    join x y z ->
    join (f x) (f y) (f z).

 
Section sa_preimage.
  Variables A B:Type.
  Variable B_J: Join B.
   Variable PA: Perm_alg B.

  Variable f:A -> B.
  Variable f':B -> A.

  Hypothesis Hf'_f : forall x, f' (f x) = x.
  Hypothesis Hf_f' : join_hom (f oo f').

  Lemma f_inj : forall x y : A,  f x = f y -> x = y.
Admitted.
#[global] Instance Join_preimage: Join A. exact (fun a b c => join (f a) (f b) (f c)). Defined.

  #[global] Instance Perm_preimage  : @Perm_alg _  Join_preimage.
Admitted.

  Context {SAb: Sep_alg B}.
  Hypothesis Hcore : forall x, core (f (f' x)) = f (f' (core x)).

  #[global] Instance Sep_preimage : Sep_alg A.
Admitted.

 #[global] Instance Sing_preimage {Sing_b: Sing_alg B}: Sing_alg A.
Admitted.

 #[global] Instance Canc_preimage {CAb: Canc_alg B} : Canc_alg A.
Admitted.

 #[global] Instance Disj_preimage {DAb: Disj_alg B} : Disj_alg A.
Admitted.

End sa_preimage.

#[global] Existing Instance Join_preimage.
#[global] Existing Instance Perm_preimage.
#[global] Existing Instance Sep_preimage.
#[global] Existing Instance Sing_preimage.
#[global] Existing Instance Canc_preimage.
#[global] Existing Instance Disj_preimage.

Section SepAlgBijection.
  Variables (A: Type) (Ja: Join A)(PAa: Perm_alg A).
  Variable B:Type .

  Variable bij : bijection A B.
#[global] Instance Join_bij: Join B. exact (fun (x y z : B) => join (bij_g _ _ bij x) (bij_g _ _ bij y) (bij_g _ _ bij z)). Defined.

  Lemma Perm_bij  : Perm_alg B.
Admitted.

  #[global] Instance Sep_bij {SAa: Sep_alg A} : Sep_alg B.
Admitted.

 Lemma Sing_bij {SAa: Sep_alg A}{SingA: Sing_alg A} : Sing_alg B.
Admitted.

 #[global] Instance Canc_bij {SAa: Canc_alg A} : Canc_alg B.
Admitted.

  #[global] Instance  Disj_bij {DAa: Disj_alg A} : Disj_alg B.
Admitted.

End SepAlgBijection.
#[global] Existing Instance Join_bij.
#[global] Existing Instance Perm_bij.
#[global] Existing Instance Sep_bij.
#[global] Existing Instance Sing_bij.
#[global] Existing Instance Canc_bij.
#[global] Existing Instance Disj_bij.

End sepalg_generators.

End VST_DOT_msl_DOT_sepalg_generators_WRAPPED.
Module Export VST_DOT_msl_DOT_sepalg_generators.
Module Export VST.
Module Export msl.
Module Export sepalg_generators.
Include VST_DOT_msl_DOT_sepalg_generators_WRAPPED.sepalg_generators.
End sepalg_generators.

End msl.

End VST.

End VST_DOT_msl_DOT_sepalg_generators.
Import VST.msl.base.
Import VST.msl.eq_dec.
Import VST.msl.boolean_alg.

Module Share <: SHARE_MODEL.

  Inductive ShareTree : Set :=
  | Leaf : bool -> ShareTree
  | Node : ShareTree -> ShareTree -> ShareTree
  .
Fixpoint canonicalTree (x:ShareTree) : Prop.
Admitted.

  Inductive shareTreeOrd : ShareTree -> ShareTree -> Prop :=
  | Leaf_Ord : forall b1 b2, implb b1 b2 = true ->
       shareTreeOrd (Leaf b1) (Leaf b2)
  | LeafNode_Ord : forall b l r,
       shareTreeOrd (Node (Leaf b) (Leaf b)) (Node l r) ->
       shareTreeOrd (Leaf b) (Node l r)
  | NodeLeaf_Ord : forall b l r,
       shareTreeOrd (Node l r) (Node (Leaf b) (Leaf b)) ->
       shareTreeOrd (Node l r) (Leaf b)
  | Node_Ord : forall l1 l2 r1 r2,
       shareTreeOrd l1 l2 ->
       shareTreeOrd r1 r2 ->
       shareTreeOrd (Node l1 r1) (Node l2 r2)
  .

  Definition canonTree :=  { t:ShareTree | canonicalTree t }.
#[global] Instance EqDec_canonTree : EqDec canonTree.
Admitted.

  Module BA <: BOOLEAN_ALGEBRA.
    Definition t := canonTree.
    Definition Ord (x y:canonTree) := shareTreeOrd (proj1_sig x) (proj1_sig y).
Definition lub (x y:canonTree) : canonTree.
Admitted.
Definition glb (x y:canonTree) : canonTree.
Admitted.
Definition top : canonTree.
Admitted.
Definition bot : canonTree.
Admitted.
Definition comp (x:canonTree) : canonTree.
Admitted.

    Lemma ord_refl : forall x, Ord x x.
Admitted.

    Lemma ord_trans : forall x y z, Ord x y -> Ord y z -> Ord x z.
Admitted.

    Lemma ord_antisym : forall x y, Ord x y -> Ord y x -> x = y.
Admitted.

    Lemma lub_upper1 : forall x y, Ord x (lub x y).
Admitted.

    Lemma lub_upper2 : forall x y, Ord y (lub x y).
Admitted.

    Lemma lub_least : forall x y z,
      Ord x z -> Ord y z -> Ord (lub x y) z.
Admitted.

    Lemma glb_lower1 : forall x y, Ord (glb x y) x.
Admitted.

    Lemma glb_lower2 : forall x y, Ord (glb x y) y.
Admitted.

    Lemma glb_greatest : forall x y z,
      Ord z x -> Ord z y -> Ord z (glb x y).
Admitted.

    Lemma top_correct : forall x, Ord x top.
Admitted.

    Lemma bot_correct : forall x, Ord bot x.
Admitted.

    Lemma comp1 : forall x, lub x (comp x) = top.
Admitted.

    Lemma comp2 : forall x, glb x (comp x) = bot.
Admitted.

    Lemma nontrivial : top <> bot.
Admitted.

    Lemma distrib1 : forall x y z,
      glb x (lub y z) = lub (glb x y) (glb x z).
Admitted.

  End BA.

  Module BAF := BA_Facts BA.
  Include BAF.
Definition Lsh  : Share.t.
Admitted.
Definition Rsh  : Share.t.
Admitted.
Import VST.msl.sepalg.

Section SA_LOWER.
  Variable A : Type.
#[local] Instance Join_lower: Join (option A).
Admitted.

End SA_LOWER.

#[global] Existing Instance Join_lower.

Definition share : Type.
exact (Share.t).
Defined.
Import VST.msl.ageable.

Class Age_alg (A:Type) {JOIN: Join A}{as_age : ageable A}{SA: Sep_alg A} :=
mkAge {
  age1_join : forall x {y z x'}, join x y z -> age x x' ->
    exists y':A, exists z':A, join x' y' z' /\ age y y' /\ age z z'
; age1_join2 : forall x {y z z'}, join x y z -> age z z' ->
    exists x':A, exists y':A, join x' y' z' /\ age x x' /\ age y y'
; unage_join : forall x {x' y' z'}, join x' y' z' -> age x x' ->
    exists y:A, exists z:A, join x y z /\ age y y' /\ age z z'
; unage_join2 : forall z {x' y' z'}, join x' y' z' -> age z z' ->
    exists x:A, exists y:A, join x y z /\ age x x' /\ age y y'
; age_core : forall x y : A, age x y -> age (core x) (core y)
}.

Import VST.msl.predicates_hered.

Class Ext_alg (A : Type) `{EO : Ext_ord A} {J : Join A} {SA : Sep_alg A} :=
  { ext_join_commut : forall {x y z z'}, join x y z -> ext_order z z' ->
      exists x', ext_order x x' /\ join x' y z';
    join_ext_commut : forall {x x' y' z'}, ext_order x x' -> join x' y' z' ->
      exists z, join x y' z /\ ext_order z z';

    id_exists : forall x, exists e, identity e /\ unit_for e x
  }.

Section Predicates.

Context {A : Type} {JA : Join A} {PA : Perm_alg A} {SA : Sep_alg A} {AG : ageable A} {XA : Age_alg A} {EO : Ext_ord A} {EA : Ext_alg A}.

Program Definition sepcon  (p q:pred A) : pred A := fun x:A =>
  exists y:A, exists z:A, join y z x /\ p y /\ q z.
Admit Obligations.

End Predicates.

Notation "P '*' Q" := (sepcon P Q) : pred.

Module Type KNOT_FULL_BASIC_INPUT.

End KNOT_FULL_BASIC_INPUT.

Module Type KNOT_FULL_SA_INPUT.
  Declare Module KI: KNOT_FULL_BASIC_INPUT.

End KNOT_FULL_SA_INPUT.

Module Type KNOT_BASIC.
  Declare Module KI:KNOT_FULL_BASIC_INPUT.

End KNOT_BASIC.

Module Type KNOT_ASSM.
  Declare Module KI: KNOT_FULL_BASIC_INPUT.
  Declare Module KSAI: KNOT_FULL_SA_INPUT with Module KI := KI.
  Declare Module K: KNOT_BASIC with Module KI := KI.

End KNOT_ASSM.
Export VST.msl.knot_shims.
Export VST.msl.functors.

Export MixVariantFunctor.
Export MixVariantFunctorGenerator.

Definition nonempty_share (sh: share) :=
       sepalg.nonidentity sh.
Definition readable_share (sh: share) :=
       nonempty_share (Share.glb Share.Rsh sh).
Definition writable_share (sh: share) :=
    nonempty_share (Share.glb Share.Lsh sh) /\ join_sub Share.Rsh sh.

Lemma bot_unreadable: ~readable_share Share.bot.
Admitted.
Import VST.msl.ghost.
Import VST.veric.compspecs.

Module Type ADR_VAL.
Parameter address : Type.

Parameter kind: Type.
End ADR_VAL.

Inductive TypeTree: Type :=
  | ConstType: Type -> TypeTree
  | CompspecsType: TypeTree
  | Mpred: TypeTree
  | DependentType: nat -> TypeTree
  | ProdType: TypeTree -> TypeTree -> TypeTree
  | ArrowType: TypeTree -> TypeTree -> TypeTree
  | SigType: forall (I : Type), (I -> TypeTree) -> TypeTree
  | PiType: forall (I : Type), (I -> TypeTree) -> TypeTree
  | ListType: TypeTree -> TypeTree.
Definition dependent_type_functor_rec (ts: list Type): TypeTree -> functor.
exact (fix dtfr (T: TypeTree): functor :=
  match T with
  | ConstType A => fconst A
  | CompspecsType => fconst compspecs
  | Mpred => fidentity
  | DependentType n => fconst (nth n ts unit)
  | ProdType T1 T2 => fpair (dtfr T1) (dtfr T2)
  | ArrowType T1 T2 => ffunc (dtfr T1) (dtfr T2)
  | SigType _ f => fsig (fun i => dtfr (f i))
  | PiType _ f => fpi (fun i => dtfr (f i))
  | ListType T => flist (dtfr T)
  end).
Defined.
Definition fpreds: functor.
Admitted.

Module Type STRAT_MODEL.
  Declare Module AV : ADR_VAL.
  Import AV.
Definition f_res : functor.
Admitted.
Definition ghost (PRED : Type) : Type.
exact (list (option ({g: Ghost & {a: @G g | ghost.valid a}} * fpreds PRED)%type)).
Defined.
Definition ghost_fmap (A B:Type) (f:A->B) (g:B->A)(x:ghost A) : ghost B.
Admitted.

  Axiom ff_ghost : functorFacts ghost ghost_fmap.
Definition f_ghost : functor.
exact (Functor ff_ghost).
Defined.
Definition f_pre_rmap : functor.
exact (fpair (ffunc (fconst address) f_res) f_ghost).
Defined.

End STRAT_MODEL.

Module StratModel (AV' : ADR_VAL) : STRAT_MODEL with Module AV:=AV'.
  Module AV := AV'.
  Import AV.
Definition f_res : functor.
Admitted.
Definition ghost (PRED : Type) : Type.
exact (list (option ({g: Ghost & {a: @G g | ghost.valid a}} * fpreds PRED)%type)).
Defined.
Definition ghost_fmap (A B:Type) (f:A->B) (g:B->A)(x:ghost A) : ghost B.
Admitted.

  Lemma ff_ghost : functorFacts ghost ghost_fmap.
Admitted.
Definition f_ghost : functor.
exact (Functor ff_ghost).
Defined.
Definition f_pre_rmap : functor.
exact (fpair (ffunc (fconst address) f_res) f_ghost).
Defined.

End StratModel.

Module Type RMAPS.
  Declare Module AV:ADR_VAL.
  Import AV.

  Parameter rmap : Type.
  Axiom Join_rmap: Join rmap.
#[global] Existing Instance Join_rmap.
  Axiom Perm_rmap: Perm_alg rmap.
#[global] Existing Instance Perm_rmap.
  Axiom Sep_rmap: Sep_alg rmap.
#[global] Existing Instance Sep_rmap.
  Axiom ag_rmap: ageable rmap.
#[global] Existing Instance ag_rmap.
  Axiom Age_rmap: Age_alg rmap.
#[global] Existing Instance Age_rmap.
  Axiom Ext_rmap: Ext_ord rmap.
#[global] Existing Instance Ext_rmap.
  Axiom ExtA_rmap: Ext_alg rmap.
#[global] Existing Instance ExtA_rmap.

  Inductive preds : Type :=
    SomeP : forall A : TypeTree,
      (forall ts: list Type, dependent_type_functor_rec ts A (pred rmap)) -> preds.

  Definition NoneP := SomeP (ConstType unit) (fun _ => tt).

  Inductive resource : Type :=
    | NO: forall sh: Share.t, ~(readable_share sh) -> resource
    | YES: forall sh: Share.t, readable_share sh -> kind -> preds -> resource
    | PURE: kind -> preds -> resource.
#[global] Instance Join_resource: Join resource.
Admitted.
Definition ghost : Type.
exact (list (option ({g: Ghost & {a: @G g | ghost.valid a}} * preds)%type)).
Defined.
Definition ghost_fmap (f g:pred rmap -> pred rmap)(x:ghost) : ghost.
Admitted.
Definition resource_at (phi:rmap) : address -> resource.
Admitted.
  Infix "@" := resource_at (at level 50, no associativity).
Definition ghost_of (phi:rmap) : ghost.
Admitted.

  Program Definition approx (n:nat) (p: pred rmap) : pred rmap :=
    fun w => level w < n /\ p w.
Admit Obligations.

End RMAPS.

Module Rmaps (AV':ADR_VAL): RMAPS with Module AV:=AV'.
  Module Export AV:=AV'.

  Module SM := StratModel(AV).
  Import SM.

  Module Export TyF.
    Definition F := f_pre_rmap.

    Definition Rel A (r1 r2 : f_pre_rmap A) := fst r1 = fst r2 /\ join_sub (snd r1) (snd r2).
    Lemma Rel_fmap :
      forall (A B : Type) (f1 : A -> B) (f2 : B -> A) (x y : F A),
      Rel A x y -> Rel B (fmap F f1 f2 x) (fmap F f1 f2 y).
Admitted.
    Lemma Rel_refl : forall (A : Type) (x : F A), Rel A x x.
Admitted.
    Lemma Rel_trans :
      forall (A : Type) (x y z : F A),
      Rel A x y -> Rel A y z -> Rel A x z.
Admitted.
  End TyF.

  Module TyFSA <: KNOT_FULL_SA_INPUT with Module KI:=TyF.
    Module KI := TyF.

  End TyFSA.

  Module K := Knot_MixVariantHeredProp(TyF).

  Module KA <: KNOT_ASSM with Module KI := TyF with Module KSAI := TyFSA
    with Module K := K.
    Module KI := TyF.
    Module KSAI := TyFSA.
    Module K := K.

  End KA.

  Definition rmap := K.knot.
#[global] Instance Join_rmap : Join rmap.
Admitted.
#[global] Instance Perm_rmap : Perm_alg rmap.
Admitted.
#[global] Instance Sep_rmap : Sep_alg rmap.
Admitted.
#[global] Instance ag_rmap : ageable rmap.
Admitted.
#[global] Instance Age_rmap : Age_alg rmap.
Admitted.
#[global] Instance Ext_rmap : Ext_ord rmap.
Admitted.
#[global] Instance ExtA_rmap : Ext_alg rmap.
Admitted.

  Inductive preds : Type :=
    SomeP : forall A : TypeTree,
    (forall ts: list Type, dependent_type_functor_rec ts A (pred rmap)) -> preds.

  Definition NoneP := SomeP (ConstType unit) (fun _ => tt).

  Inductive resource : Type :=
    | NO: forall sh: Share.t, ~ readable_share sh -> resource
    | YES: forall sh: Share.t, readable_share sh -> kind -> preds -> resource
    | PURE: kind -> preds -> resource.
Definition ghost : Type.
exact (list (option ({g: Ghost & {a: @G g | ghost.valid a}} * preds)%type)).
Defined.
#[global] Instance Join_resource: Join resource.
Admitted.
Definition ghost_fmap (f g:pred rmap -> pred rmap)(x:ghost) : ghost.
Admitted.
Definition resource_at (phi:rmap) : address -> resource.
Admitted.
Definition ghost_of (phi:rmap) : ghost.
Admitted.

  Program Definition approx (n:nat) (p: (pred rmap)) : (pred rmap) :=
    fun w => level w < n /\ p w.
Admit Obligations.

End Rmaps.

Module Rmaps_Lemmas (R0: RMAPS).
Module R := R0.

End Rmaps_Lemmas.
Module Export compcert_rmaps.
Import VST.veric.base.
Export VST.veric.Memory.

Definition typesig := (list type * type)%type.

Inductive kind : Type := VAL : memval -> kind
                                   | LK : forall n i : Z, kind
                                   | FUN: typesig -> calling_convention -> kind.

Module CompCert_AV <: ADR_VAL.

Definition address := address.
Definition kind := kind.

End CompCert_AV.

Module R := Rmaps (CompCert_AV).
Module RML := Rmaps_Lemmas(R).
Export R.
Export Mem.
Import compcert.lib.Maps.
Definition perm_of_sh (sh: Share.t): option permission.
Admitted.
Definition contents_at (m: mem) (loc: address) : memval.
Admitted.

Definition contents_cohere (m: mem) (phi: rmap) :=
  forall rsh sh v loc pp, phi @ loc = YES rsh sh (VAL v) pp -> contents_at m loc = v /\ pp=NoneP.

Definition perm_of_res (r: resource) :=

 match r with
 | NO sh _ => if eq_dec sh Share.bot then None else Some Nonempty
 | PURE _ _ => Some Nonempty
 | YES sh rsh (VAL _) _ => perm_of_sh sh
 | YES sh rsh _ _ => Some Nonempty
 end.

Definition perm_of_res' (r: resource) :=

 match r with
 | NO sh _ => if eq_dec sh Share.bot then None else Some Nonempty
 | PURE _ _ => Some Nonempty
 | YES sh _ _ _ => perm_of_sh sh
 end.

Definition access_cohere (m: mem)  (phi: rmap) :=
  forall loc,  access_at m loc Cur = perm_of_res (phi @ loc).

Definition max_access_at m loc := access_at m loc Max.

Definition max_access_cohere (m: mem) (phi: rmap)  :=
  forall loc,
    perm_order'' (max_access_at m loc) (perm_of_res' (phi @ loc)).

Definition alloc_cohere (m: mem) (phi: rmap) :=
 forall loc,  (fst loc >= nextblock m)%positive -> phi @ loc = NO Share.bot bot_unreadable.

Inductive juicy_mem: Type :=
  mkJuicyMem: forall (m: mem) (phi: rmap)
    (JMcontents: contents_cohere m phi)
    (JMaccess: access_cohere m phi)
    (JMmax_access: max_access_cohere m phi)
    (JMalloc: alloc_cohere m phi),
       juicy_mem.

Section selectors.
Variable (j: juicy_mem).
Definition m_dry := match j with mkJuicyMem m _ _ _ _ _ => m end.
Definition m_phi := match j with mkJuicyMem _ phi _ _ _ _ => phi end.
End selectors.
#[export] Instance juicy_mem_ageable: ageable juicy_mem.
Admitted.

#[export] Program Instance juicy_mem_ord: Ext_ord juicy_mem :=
  { ext_order a b := m_dry a = m_dry b /\ ext_order (m_phi a) (m_phi b) }.
Admit Obligations.

Module VST_DOT_veric_DOT_lift_WRAPPED.
Module Export lift.

Structure Lift := mkLift {
         lift_S: Type;
         lift_T: Type;
         lift_prod : Type;
         lift_last: Type;
         lifted:> Type;
         lift_curry: lift_T -> lift_prod -> lift_last;
         lift_uncurry_open: ((lift_S -> lift_prod) -> (lift_S -> lift_last)) -> lifted
}.

Definition Tend (S: Type) (A: Type) :=
    mkLift S A unit A
          (S -> A)
          (fun f _ => f)
          (fun f => f (fun _: S => tt)).
Canonical Structure Tarrow (A: Type) (H: Lift) :=
    mkLift (lift_S H)
      (A -> lift_T H)
      (prod A (lift_prod H))
      (lift_last H)
      ((lift_S H -> A) -> lifted H)
      (fun f x => match x with (x1,x2) => lift_curry H (f x1) x2 end)
      (fun f x => lift_uncurry_open H (fun y: lift_S H -> lift_prod H => f (fun z => (x z, y z)))).
Definition liftx {H: Lift} (f: lift_T H) : lifted H.
Admitted.

Module Export LiftNotation.
Notation "'`' x" := (liftx x) (at level 10, x at next level).

Notation "'`(' x ')'" := (liftx (x : _)).
End LiftNotation.

End lift.

End VST_DOT_veric_DOT_lift_WRAPPED.
Module Export VST.
Module Export veric.
Module lift.
Include VST_DOT_veric_DOT_lift_WRAPPED.lift.
End lift.
Definition force_val (v: option val) : val.
Admitted.

Definition force_val1 (f: val -> option val) (v: val) := force_val (f v).
Definition force_val2 (f: val -> val -> option val) (v1 v2: val) := force_val (f v1 v2).
Definition offset_val (ofs: Z) (v: val) : val.
Admitted.

Definition isptr v :=
   match v with | Vptr _ _ => True | _ => False end.
Module Export mpred.
Import VST.veric.composite_compute.

Set Implicit Arguments.
Module Export Map.
Section map.
Variables (B : Type).

Definition t := positive -> option B.
Definition get (h: t) (a:positive) : option B.
Admitted.

End map.

End Map.
Unset Implicit Arguments.

Section FUNSPEC.

Definition genviron := Map.t block.

Definition venviron := Map.t (block * type).

Definition tenviron := Map.t val.

Inductive environ : Type :=
 mkEnviron: forall (ge: genviron) (ve: venviron) (te: tenviron), environ.
Definition ge_of (rho: environ) : genviron.
Admitted.
Definition te_of (rho: environ) : tenviron.
Admitted.

Definition mpred := pred rmap.

Definition argsEnviron:Type := genviron * (list val).
Definition AssertTT (A: TypeTree): TypeTree.
exact (ArrowType A (ArrowType (ConstType environ) Mpred)).
Defined.
Definition ArgsTT (A: TypeTree): TypeTree.
exact (ArrowType A (ArrowType (ConstType argsEnviron) Mpred)).
Defined.
Definition super_non_expansive {A: TypeTree}
  (P: forall ts, dependent_type_functor_rec ts (AssertTT A) mpred): Prop.
Admitted.
Definition args_super_non_expansive {A: TypeTree}
  (P: forall ts, dependent_type_functor_rec ts (ArgsTT A) mpred): Prop.
Admitted.

Inductive funspec :=
   mk_funspec: typesig -> calling_convention -> forall (A: TypeTree)
     (P: forall ts, dependent_type_functor_rec ts (ArgsTT A) mpred)
     (Q: forall ts, dependent_type_functor_rec ts (AssertTT A) mpred)
     (P_ne: args_super_non_expansive P) (Q_ne: super_non_expansive Q),
     funspec.

End FUNSPEC.

Definition assert := environ -> mpred.

Arguments sizeof {env} !t / .
Arguments alignof {env} !t / .

Arguments complete_legal_cosu_type {cenv} !t / .
Fixpoint typelist_of_type_list (params : list type) : typelist.
Admitted.

Definition eval_id (id: ident) (rho: environ) := force_val (Map.get (te_of rho) id).
Definition env_set (rho: environ) (x: ident) (v: val) : environ.
Admitted.

Import VST.veric.lift.
Canonical Structure LiftEnviron := Tend environ.

End mpred.

Class NatDed (A: Type) := mkNatDed {
  andp: A -> A -> A;
  orp: A -> A -> A;
  exp: forall {T:Type}, (T -> A) -> A;
  allp: forall {T:Type}, (T -> A) -> A;
  imp: A -> A -> A;
  prop: Prop -> A;
  derives: A -> A -> Prop;
  pred_ext: forall P Q, derives P Q -> derives Q P -> P=Q;
  derives_refl: forall P, derives P P;
  derives_trans: forall P Q R, derives P Q -> derives Q R -> derives P R;
  TT := prop True;
  FF := prop False;
  andp_right:  forall X P Q:A, derives X P -> derives X Q -> derives X (andp P Q);
  andp_left1:  forall P Q R:A, derives P R -> derives (andp P Q) R;
  andp_left2:  forall P Q R:A, derives Q R -> derives (andp P Q) R;
  orp_left: forall P Q R, derives P R -> derives Q R -> derives (orp P Q) R;
  orp_right1: forall P Q R, derives P Q -> derives P (orp Q R);
  orp_right2: forall P Q R, derives P R -> derives P (orp Q R);
  exp_right: forall {B: Type} (x:B) (P: A) (Q: B -> A),
                        derives P (Q x) -> derives P (exp Q);
  exp_left: forall {B: Type} (P: B -> A) (Q: A),
                      (forall x, derives (P x) Q) -> derives (exp P) Q;
  allp_left: forall {B}(P: B -> A) x Q, derives (P x) Q -> derives (allp P) Q;
  allp_right: forall {B}(P: A) (Q: B -> A),  (forall v, derives P (Q v)) -> derives P (allp Q);
  imp_andp_adjoint: forall P Q R, derives (andp P Q) R <-> derives P (imp Q R);
  prop_left: forall (P: Prop) Q, (P -> derives TT Q) -> derives (prop P) Q;
  prop_right: forall (P: Prop) Q, P -> derives Q (prop P);
  prop_imp_prop_left: forall (P Q: Prop), derives (imp (prop P) (prop Q)) (prop (P -> Q));
  allp_prop_left: forall {B: Type} (P: B -> Prop), derives (allp (fun b => prop (P b))) (prop (forall b, P b))

}.

#[global] Program Instance LiftNatDed (A B: Type) {ND: NatDed B} : NatDed (A -> B) :=
 mkNatDed (A -> B)
      (fun P Q x => andp (P x) (Q x))
      (fun P Q x => orp (P x) (Q x))
      (fun T (F: T -> A -> B) (a: A) => exp (fun x => F x a))
      (fun T (F: T -> A -> B) (a: A) => allp (fun x => F x a))
      (fun P Q x => imp (P x) (Q x))
      (fun P x => prop P)
      (fun P Q => forall x, derives (P x) (Q x))
     _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _.
Admit Obligations.
Delimit Scope logic with logic.
Local Open Scope logic.
Notation "P '|--' Q" := (derives P%logic Q%logic) (at level 80, no associativity) : logic_derives.
Open Scope logic_derives.
Notation "'EX' x .. y , P " :=
  (exp (fun x => .. (exp (fun y => P%logic)) ..)) (at level 65, x binder, y binder, right associativity) : logic.
Notation "'ALL' x .. y , P " :=
  (allp (fun x => .. (allp (fun y => P%logic)) ..)) (at level 65, x binder, y binder, right associativity) : logic.
Infix "||" := orp (at level 50, left associativity) : logic.
Infix "&&" := andp (at level 40, left associativity) : logic.
Notation "P '-->' Q" := (imp P Q) (at level 55, right associativity) : logic.
Notation "'!!' e" := (prop e) (at level 15) : logic.

Class SepLog (A: Type) {ND: NatDed A} := mkSepLog {
  emp: A;
  sepcon: A -> A -> A;
  wand: A -> A -> A;
  ewand: A -> A -> A;
  sepcon_assoc: forall P Q R, sepcon (sepcon P Q) R = sepcon P (sepcon Q R);
  sepcon_comm:  forall P Q, sepcon P Q = sepcon Q P;
  wand_sepcon_adjoint: forall (P Q R: A),  (sepcon P Q |-- R) <-> (P |-- wand Q R);
  sepcon_andp_prop: forall P Q R, sepcon P (!!Q && R) = !!Q && (sepcon P R);
  sepcon_derives: forall P P' Q Q' : A, (P |-- P') -> (Q |-- Q') -> sepcon P Q |-- sepcon P' Q';

  ewand_conflict: forall P Q R, (sepcon P Q |-- FF) -> andp P (ewand Q R) |-- FF
}.

Notation "P '*' Q" := (sepcon P Q) : logic.
Notation "P '-*' Q" := (wand P Q) (at level 60, right associativity) : logic.

#[global] Instance LiftSepLog (A B: Type) {NB: NatDed B}{SB: SepLog B} : SepLog (A -> B).
Admitted.

Class Indir (A: Type) {ND: NatDed A} := mkIndir {
  later: A -> A;
  now_later: forall P: A, P |-- later P;
  later_K: forall P Q, later (P --> Q) |-- later P --> later Q;
  later_allp: forall T (F: T -> A),  later (allp F) = ALL x:T, later (F x);
  later_exp: forall T (F: T-> A), EX x:T, later (F x) |-- later (exp F);
  later_exp': forall T (any:T) F, later (exp F) = EX x:T, later (F x);
  later_exp'': forall T F, later (exp F) |-- (EX x:T, later (F x)) || later FF;

  later_prop: forall PP: Prop, later (!! PP) |-- !! PP || later FF;
  loeb: forall P,   (later P |-- P) ->  TT |-- P
}.

Notation "'|>' e" := (later e) (at level 20, right associativity): logic.

#[global] Instance LiftIndir (A: Type) (B: Type)  {NB: NatDed B}{IXB: Indir B} :
         @Indir (A -> B) (LiftNatDed A B).
Admitted.
Import Coq.Sets.Ensembles.
Import Coq.Lists.List.

Definition pred_infinite {N} (P : N -> Prop) := forall l, exists x, ~In x l /\ P x.

Class BupdSepLog (A N D: Type) {ND: NatDed A}{SL: SepLog A} := mkBSL {
  bupd: A -> A;
  own: forall {RA: Ghost}, N -> G -> D -> A;
  infinite_names: forall (l : list N), exists x, ~In x l;
  bupd_intro: forall P, P |-- bupd P;
  bupd_mono: forall P Q, (P |-- Q) -> bupd P |-- bupd Q;
  bupd_trans: forall P, bupd (bupd P) |-- bupd P;
  bupd_frame_r: forall P Q, bupd P * Q |-- bupd (P * Q);
  own_alloc_strong: forall {RA: Ghost} P a pp, pred_infinite P -> valid a ->
    emp |-- bupd (EX g: N, !!(P g) && own g a pp);
  own_op: forall {RA: Ghost} g (a1 a2 a3: G) pp, join a1 a2 a3 ->
    own g a3 pp = own g a1 pp * own g a2 pp;
  own_valid_2: forall {RA: Ghost} g (a1 a2: G) pp,
    own g a1 pp * own g a2 pp |-- !!valid_2 a1 a2;
  own_update_ND: forall {RA: Ghost} g (a: G) B pp, fp_update_ND a B ->
    own g a pp |-- bupd (EX b : _, !!(B b) && own g b pp);
  own_dealloc: forall {RA: Ghost} g (a: G) pp,
    own g a pp |-- emp
  }.

Declare Scope logic_upd.

Open Scope logic_upd.

#[global] Instance LiftBupdSepLog (A B N D: Type) {NB: NatDed B}{SB: SepLog B}{BSLB: BupdSepLog B N D} :
  BupdSepLog (A -> B) N D.
Admitted.

Class FupdSepLog (A N D I: Type) {ND: NatDed A}{IA: Indir A}{SL: SepLog A}{BSL: BupdSepLog A N D} := mkFSL {
  fupd: Ensemble I -> Ensemble I -> A -> A;
  fupd_mask_union: forall E1 E2, Disjoint _ E1 E2 ->
    emp |-- fupd (Union _ E1 E2) E2 (fupd E2 (Union _ E1 E2) emp);
  except_0_fupd: forall E1 E2 P, ((|> FF) || fupd E1 E2 P) |-- fupd E1 E2 P;
  fupd_mono: forall E1 E2 P Q, (P |-- Q) -> fupd E1 E2 P |-- fupd E1 E2 Q;
  fupd_trans: forall E1 E2 E3 P, fupd E1 E2 (fupd E2 E3 P) |-- fupd E1 E3 P;
  fupd_mask_frame_r': forall E1 E2 Ef P, Disjoint _ E1 Ef ->
    fupd E1 E2 (!! (Disjoint _ E2 Ef) --> P) |-- fupd (Union _ E1 Ef) (Union _ E2 Ef) P;
  fupd_frame_r: forall E1 E2 P Q, (fupd E1 E2 P) * Q |-- fupd E1 E2 (P * Q);
  bupd_fupd: forall E P, bupd P |-- fupd E E P
  }.
Notation "|={ E }=> P" := (fupd E E P) (at level 99, E at level 50, P at level 200): logic_upd.

#[global] Instance LiftFupdSepLog (A B N D I: Type) {NB: NatDed B}{IB: Indir B}{SB: SepLog B}{BSLB: BupdSepLog B N D}{FSLB: FupdSepLog B N D I} :
  FupdSepLog (A -> B) N D I.
Admitted.

#[global] Instance algNatDed (T: Type){agT: ageable T}{EO: Ext_ord T} : NatDed (pred T).
Admitted.

#[global] Instance algSepLog (T: Type) {agT: ageable T}{JoinT: Join T}{PermT: Perm_alg T}{SepT: Sep_alg T}{AgeT: Age_alg T}{EO: Ext_ord T}{ET: Ext_alg T} :
      @SepLog (pred T) (algNatDed T).
Admitted.

#[global] Instance algIndir (T: Type) {agT: ageable T}{JoinT: Join T}{PermT: Perm_alg T}{SepT: Sep_alg T}
                {AgeT: Age_alg T}{EO: Ext_ord T}:
         @Indir (pred T) (algNatDed T).
Admitted.

Export VST.veric.base.

Program Definition noat (l: AV.address) : pred rmap :=
    fun m => identity (m @ l).
Admit Obligations.
Module Export own.
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

Notation "|==> P" := (own.bupd P) (at level 99, P at level 200): pred.
Definition ext_ref {Z} (ora : Z) : {g : Ghost & {a : G | valid a}}.
Admitted.
Export compcert.export.Clightdefs.
Export compcert.cfrontend.Ctypes.
Export compcert.cfrontend.Cop.
Export compcert.cfrontend.Clight.
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
Export VST.veric.composite_compute.
Export VST.veric.align_mem.

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
