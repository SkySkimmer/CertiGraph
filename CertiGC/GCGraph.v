Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Export Coq.Program.Basics.
Require Import compcert.lib.Integers.
Require Import compcert.common.Values.
Require Import VST.veric.Clight_lemmas.
Require Import VST.veric.val_lemmas.
Require Import VST.veric.shares.
Require Import VST.msl.seplog.
Require Import VST.msl.shares.
Require Import VST.floyd.sublist.
Require Import VST.floyd.coqlib3.
Require Import RamifyCoq.lib.EquivDec_ext.
Require Import RamifyCoq.lib.List_ext.
Require Import RamifyCoq.graph.graph_model.
Require Import RamifyCoq.graph.graph_gen.
Require Import RamifyCoq.msl_ext.iter_sepcon.
Import ListNotations.

Local Open Scope Z_scope.

Definition MAX_SPACES: Z := 12.
Lemma MAX_SPACES_eq: MAX_SPACES = 12. Proof. reflexivity. Qed.
Hint Rewrite MAX_SPACES_eq: rep_omega.
Global Opaque MAX_SPACES.

Definition NURSERY_SIZE: Z := Z.shiftl 1 16.
Lemma NURSERY_SIZE_eq: NURSERY_SIZE = Z.shiftl 1 16. Proof. reflexivity. Qed.
Hint Rewrite NURSERY_SIZE_eq: rep_omega.
Global Opaque NURSERY_SIZE.

Definition MAX_ARGS: Z := 1024.
Lemma MAX_ARGS_eq: MAX_ARGS = 1024. Proof. reflexivity. Qed.
Hint Rewrite MAX_ARGS_eq: rep_omega.
Global Opaque MAX_ARGS.

Definition WORD_SIZE: Z := 4.
Lemma WORD_SIZE_eq: WORD_SIZE = 4. Proof. reflexivity. Qed.
Hint Rewrite WORD_SIZE_eq: rep_omega.
Global Opaque WORD_SIZE.

Definition MAX_SPACE_SIZE: Z := Z.shiftl 1 29.
Lemma MAX_SPACE_SIZE_eq: MAX_SPACE_SIZE = Z.shiftl 1 29. Proof. reflexivity. Qed.
Hint Rewrite MAX_SPACE_SIZE_eq: rep_omega.
Global Opaque MAX_SPACE_SIZE.

Lemma MSS_eq_unsigned:
  Int.unsigned (Int.shl (Int.repr 1) (Int.repr 29)) = MAX_SPACE_SIZE.
Proof.
  rewrite Int.shl_mul_two_p.
  rewrite (Int.unsigned_repr 29) by (compute; split; discriminate).
  rewrite mul_repr, MAX_SPACE_SIZE_eq. rewrite Int.Zshiftl_mul_two_p by omega.
  rewrite !Z.mul_1_l, Int.unsigned_repr;
    [reflexivity | compute; split; intro S; discriminate].
Qed.

Lemma MSS_max_unsigned_range: forall n,
    0 <= n < MAX_SPACE_SIZE -> 0 <= n <= Int.max_unsigned.
Proof.
  intros. destruct H. split. 1: assumption. rewrite Z.lt_eq_cases. left.
  transitivity MAX_SPACE_SIZE. 1: assumption.  rewrite MAX_SPACE_SIZE_eq.
  compute; reflexivity.
Qed.

Lemma MSS_max_4_unsigned_range: forall n,
    0 <= n < MAX_SPACE_SIZE -> 0 <= 4 * n <= Int.max_unsigned.
Proof.
  intros. destruct H. split. 1: omega.
  rewrite Z.lt_eq_cases. left. transitivity (4 * MAX_SPACE_SIZE). 1: omega.
  rewrite MAX_SPACE_SIZE_eq. compute; reflexivity.
Qed.

Lemma MSS_max_4_signed_range: forall n,
    0 <= n < MAX_SPACE_SIZE -> Ptrofs.min_signed <= WORD_SIZE * n <= Ptrofs.max_signed.
Proof.
  intros. destruct H. rewrite WORD_SIZE_eq. split.
  - transitivity 0. 2: omega. rewrite Z.le_lteq. left. apply Ptrofs.min_signed_neg.
  - rewrite Z.lt_le_pred in H0. rewrite Z.le_lteq. left.
    apply Z.le_lt_trans with (4 * Z.pred MAX_SPACE_SIZE). 1: omega.
    rewrite Z.mul_pred_r, MAX_SPACE_SIZE_eq.
    unfold Ptrofs.max_signed, Ptrofs.half_modulus, Ptrofs.modulus, Ptrofs.wordsize,
    Wordsize_Ptrofs.wordsize. destruct Archi.ptr64 eqn:? .
    inversion Heqb. simpl. omega.
Qed.

Local Close Scope Z_scope.

Definition VType: Type := nat * nat.
Definition EType: Type := VType * nat.
Definition vgeneration: VType -> nat := fst.
Definition vindex: VType -> nat := snd.

Instance V_EqDec: EqDec VType eq.
Proof.
  hnf. intros [x] [y]. destruct (Nat.eq_dec x y).
  - destruct (Nat.eq_dec n n0); subst.
    + left. reflexivity.
    + right. intro. apply n1. inversion H. reflexivity.
  - right. intro. apply n1. inversion H. reflexivity.
Defined.

Instance E_EqDec: EqDec EType eq.
Proof.
  hnf. intros [x] [y]. destruct (equiv_dec x y).
  - hnf in e. destruct (Nat.eq_dec n n0); subst.
    + left; reflexivity.
    + right; intro; apply n1; inversion H; reflexivity.
  - right; intro; apply c; inversion H; reflexivity.
Defined.

Inductive GC_Pointer := | GCPtr: block -> ptrofs -> GC_Pointer.

Definition raw_field: Type := option (Z + GC_Pointer).

Definition Z2val (x: Z) : val := Vint (Int.repr x).

Definition GC_Pointer2val (x: GC_Pointer) : val :=
  match x with | GCPtr b z => Vptr b z end.

Record raw_vertex_block : Type :=
  {
    raw_mark: bool;
    copied_vertex: VType;
    raw_fields: list raw_field;
    raw_color: Z;
    raw_tag: Z;
    raw_fields_not_nil: raw_fields <> nil;
  }.

Definition raw_fields_head (rvb: raw_vertex_block): raw_field :=
  match rvb.(raw_fields) as l return (raw_fields rvb = l -> raw_field) with
  | nil => fun m => False_rect _ (raw_fields_not_nil _ m)
  | r :: _ => fun _ => r
  end eq_refl.

Lemma raw_fields_head_cons:
  forall rvb, exists r l, raw_fields rvb = r :: l /\ raw_fields_head rvb = r.
Proof.
  intros. destruct rvb eqn:? . simpl. unfold raw_fields_head; simpl.
  destruct raw_fields0. 1: contradiction. exists r, raw_fields0. split; reflexivity.
Qed.

Record generation_info: Type :=
  {
    start_address: val;
    number_of_vertices: nat;
    generation_sh: share;
    start_isptr: isptr start_address;
    generation_share_writable: writable_share generation_sh;
  }.

Definition IMPOSSIBLE_VAL := Vptr xH Ptrofs.zero.
Lemma IMPOSSIBLE_ISPTR: isptr IMPOSSIBLE_VAL. Proof. exact I. Qed.
Global Opaque IMPOSSIBLE_VAL.

Definition null_info: generation_info :=
  Build_generation_info IMPOSSIBLE_VAL O Tsh IMPOSSIBLE_ISPTR writable_share_top.

Record graph_info : Type :=
  {
    g_gen: list generation_info;
    g_gen_not_nil: g_gen <> nil;
  }.

Definition graph_info_head (gi: graph_info): generation_info :=
  match gi.(g_gen) as l return (g_gen gi = l -> generation_info) with
  | nil => fun m => False_rect _ (g_gen_not_nil _ m)
  | s :: _ => fun _ => s
  end eq_refl.

Lemma graph_info_head_cons:
  forall gi, exists s l, g_gen gi = s :: l /\ graph_info_head gi = s.
Proof.
  intros. destruct gi eqn:? . simpl. unfold graph_info_head. simpl. destruct g_gen0.
  1: contradiction. exists g, g_gen0. split; reflexivity.
Qed.

Definition LGraph := LabeledGraph VType EType raw_vertex_block unit graph_info.

Local Coercion pg_lg: LabeledGraph >-> PreGraph.

Record space: Type :=
  {
    space_start: val;
    used_space: Z;
    total_space: Z;
    space_sh: share;
    space_order: (0 <= used_space <= total_space)%Z;
    space_upper_bound: (total_space < MAX_SPACE_SIZE)%Z;
  }.

Definition null_space: space.
Proof.
  refine (Build_space nullval 0 0 emptyshare _ _).
  - split; apply Z.le_refl.
  - rewrite MAX_SPACE_SIZE_eq. compute; reflexivity.
Defined.

Lemma total_space_tight_range: forall sp, (0 <= total_space sp < MAX_SPACE_SIZE)%Z.
Proof.
  intros. split.
  - destruct (space_order sp). transitivity (used_space sp); assumption.
  - apply space_upper_bound.
Qed.

Lemma total_space_range: forall sp, (0 <= total_space sp <= Int.max_unsigned)%Z.
Proof. intros. apply MSS_max_unsigned_range, total_space_tight_range. Qed.

Lemma total_space_signed_range: forall sp,
    (Ptrofs.min_signed <= WORD_SIZE * (total_space sp) <= Ptrofs.max_signed)%Z.
Proof. intros. apply MSS_max_4_signed_range, total_space_tight_range. Qed.

Record heap: Type :=
  {
    spaces: list space;
    spaces_size: Zlength spaces = MAX_SPACES;
  }.

Lemma heap_spaces_nil: forall h: heap, nil = spaces h -> False.
Proof.
  intros. pose proof (spaces_size h). rewrite <- H, Zlength_nil in H0. discriminate.
Qed.

Definition heap_head (h: heap) : space :=
  match h.(spaces) as l return (l = spaces h -> space) with
  | nil => fun m => False_rect space (heap_spaces_nil h m)
  | s :: _ => fun _ => s
  end eq_refl.

Lemma heap_head_cons: forall h, exists s l, spaces h = s :: l /\ heap_head h = s.
Proof.
  intros. destruct h eqn:? . simpl. unfold heap_head. simpl. destruct spaces0.
  1: inversion spaces_size0. exists s, spaces0. split; reflexivity.
Qed.

Record thread_info: Type :=
  {
    ti_heap_p: val;
    ti_heap: heap;
    ti_args: list val;
    arg_size: Zlength ti_args = MAX_ARGS;
  }.

Definition single_vertex_size (g: LGraph) (v: VType): Z :=
  Zlength (vlabel g v).(raw_fields) + 1.

Lemma single_vertex_size_gt_zero: forall g v, (0 < single_vertex_size g v)%Z.
Proof.
  intros. unfold single_vertex_size.
  pose proof (Zlength_nonneg (raw_fields (vlabel g v))). omega.
Qed.

Fixpoint previous_vertices_size (g: LGraph) (gen i: nat): Z :=
  match i with
  | O => 0
  | S n => single_vertex_size g (gen, n) + previous_vertices_size g gen n
  end.

Lemma previous_size_ge_zero: forall g gen i, (0 <= previous_vertices_size g gen i)%Z.
Proof.
  intros. induction i; simpl. 1: omega.
  pose proof (single_vertex_size_gt_zero g (gen, i)). omega.
Qed.

Definition generation_space_compatible (g: LGraph)
           (tri: nat * generation_info * space) : Prop :=
  match tri with
  | (gen, gi, sp) =>
    gi.(start_address) = sp.(space_start) /\
    gi.(generation_sh) = sp.(space_sh) /\
    previous_vertices_size g gen gi.(number_of_vertices) = sp.(used_space)
  end.

Fixpoint nat_seq (s: nat) (total: nat): list nat :=
  match total with
  | O => nil
  | S n => s :: nat_seq (S s) n
  end.

Lemma nat_seq_S: forall i num, nat_seq i (S num) = nat_seq i num ++ [num + i].
Proof.
  intros. revert i. induction num; intros. 1: simpl; reflexivity.
  remember (S num). simpl. rewrite (IHnum (S i)). subst. simpl. repeat f_equal. omega.
Qed.

Lemma nat_seq_In_prop: forall s n i, In i (nat_seq s n) -> s <= i.
Proof.
  intros. revert s H. induction n; intros; simpl in H. 1: contradiction. destruct H.
  - rewrite Nat.le_lteq. right; assumption.
  - specialize (IHn _ H). clear H. omega.
Qed.

Definition nat_inc_list (n: nat) : list nat := nat_seq O n.

Lemma nat_inc_list_S: forall num, nat_inc_list (S num) = nat_inc_list num ++ [num].
Proof. intros. unfold nat_inc_list. rewrite nat_seq_S. repeat f_equal. omega. Qed.

Definition graph_thread_info_compatible (g: LGraph) (ti: thread_info): Prop :=
  Forall (generation_space_compatible g)
         (combine (combine (nat_inc_list (length g.(glabel).(g_gen)))
                           g.(glabel).(g_gen)) ti.(ti_heap).(spaces)) /\
  Forall (eq nullval)
         (skipn (length g.(glabel).(g_gen)) (map space_start ti.(ti_heap).(spaces))).

Record fun_info : Type :=
  {
    fun_word_size: Z;
    live_roots_indices: list Z;
    fi_index_range: forall i, In i live_roots_indices -> (0 <= i < MAX_ARGS)%Z;
    word_size_range: (0 <= fun_word_size <= Int.max_unsigned)%Z;
  }.

Definition vertex_offset (g: LGraph) (v: VType): Z :=
  previous_vertices_size g (vgeneration v) (vindex v) + 1.

Definition gen_start (g: LGraph) (gen: nat): val :=
  (nth gen g.(glabel).(g_gen) null_info).(start_address).

Definition vertex_address (g: LGraph) (v: VType): val :=
  offset_val (WORD_SIZE * vertex_offset g v) (gen_start g (vgeneration v)).

Definition root_t: Type := Z + GC_Pointer + VType.

Instance root_t_inhabitant: Inhabitant root_t := inl (inl Z.zero).

Definition root2val (g: LGraph) (fd: root_t) : val :=
  match fd with
  | inl (inl z) => Z2val z
  | inl (inr p) => GC_Pointer2val p
  | inr v => vertex_address g v
  end.

Definition roots_t: Type := list root_t.

Definition outlier_t: Type := list GC_Pointer.

Instance Inhabitant_val: Inhabitant val := nullval.

Definition fun_thread_arg_compatible
           (g: LGraph) (ti: thread_info) (fi: fun_info) (roots: roots_t) : Prop :=
  map (root2val g) roots = map ((flip Znth) ti.(ti_args)) fi.(live_roots_indices).

Definition roots_compatible (g: LGraph) (outlier: outlier_t) (roots: roots_t): Prop :=
  incl (filter_sum_right (filter_sum_left roots)) outlier /\
  Forall (vvalid g) (filter_sum_right roots).

Definition outlier_compatible (g: LGraph) (outlier: outlier_t): Prop :=
  forall v,
    vvalid g v ->
    incl (filter_sum_right (filter_option (vlabel g v).(raw_fields))) outlier.

Definition
  super_compatible
  (g_ti_r: LGraph * thread_info * roots_t) (fi: fun_info) (out: outlier_t) : Prop :=
  let (g_ti, r) := g_ti_r in
  let (g, ti) := g_ti in
  graph_thread_info_compatible g ti /\
  fun_thread_arg_compatible g ti fi r /\
  roots_compatible g out r /\
  outlier_compatible g out.

Definition reset_generation_info (gi: generation_info) : generation_info :=
  Build_generation_info (start_address gi) O (generation_sh gi) (start_isptr gi)
                        (generation_share_writable gi).

Fixpoint reset_nth_gen_info
         (n: nat) (gi: list generation_info) : list generation_info :=
  match n with
  | O => match gi with
         | nil => nil
         | g :: l => reset_generation_info g :: l
         end
  | S m => match gi with
           | nil => nil
           | g :: l => g :: reset_nth_gen_info m l
           end
  end.

Lemma reset_nth_gen_info_preserve_length: forall n gl,
    length (reset_nth_gen_info n gl) = length gl.
Proof.
  intros. revert n. induction gl; simpl; intros; destruct n; simpl;
                      [| | | rewrite IHgl]; reflexivity.
Qed.

Lemma reset_nth_gen_info_not_nil: forall n g, reset_nth_gen_info n (g_gen g) <> nil.
Proof.
  intros. pose proof (g_gen_not_nil g). destruct (g_gen g).
  - contradiction.
  - destruct n; simpl; discriminate.
Qed.

Definition reset_nth_graph_info (n: nat) (g: graph_info) : graph_info :=
  Build_graph_info (reset_nth_gen_info n g.(g_gen)) (reset_nth_gen_info_not_nil n g).

Definition reset_nth_gen_graph (n: nat) (g: LGraph) : LGraph :=
  Build_LabeledGraph _ _ _ (pg_lg g) (vlabel g) (elabel g)
                     (reset_nth_graph_info n (glabel g)).

Lemma reset_space_order: forall sp, (0 <= 0 <= total_space sp)%Z.
Proof. intros. pose proof (space_order sp). omega. Qed.

Definition reset_space (sp: space) : space :=
  Build_space (space_start sp) 0 (total_space sp) (space_sh sp) (reset_space_order sp)
              (space_upper_bound sp).

Fixpoint reset_nth_space (n: nat) (s: list space): list space :=
  match n with
  | O => match s with
         | nil => nil
         | sp :: l => reset_space sp :: l
         end
  | S m => match s with
           | nil => nil
           | sp :: l => sp :: reset_nth_space m l
           end
  end.

Lemma reset_nth_space_Zlength: forall n s, Zlength s = Zlength (reset_nth_space n s).
Proof.
  induction n; intros; simpl.
  - destruct s; simpl; [|rewrite !Zlength_cons]; reflexivity.
  - destruct s; [|rewrite !Zlength_cons, (IHn s0)]; reflexivity.
Qed.

Lemma reset_nth_heap_Zlength: forall n h,
    Zlength (reset_nth_space n (spaces h)) = MAX_SPACES.
Proof. intros. rewrite <- reset_nth_space_Zlength. apply spaces_size. Qed.

Definition reset_nth_heap (n: nat) (h: heap) : heap :=
  Build_heap (reset_nth_space n (spaces h)) (reset_nth_heap_Zlength n h).

Definition reset_nth_heap_thread_info (n: nat) (ti: thread_info) :=
  Build_thread_info (ti_heap_p ti) (reset_nth_heap n (ti_heap ti))
                    (ti_args ti) (arg_size ti).

Definition resume_graph_relation (g1 g2: LGraph): Prop :=
  g1.(pg_lg) = g2.(pg_lg) /\
  g1.(vlabel) = g2.(vlabel) /\
  g1.(elabel) = g2.(elabel) /\
  tl (glabel g1).(g_gen) = tl (glabel g2).(g_gen) /\
  let h1 := graph_info_head g1.(glabel) in
  let h2 := graph_info_head g2.(glabel) in
  start_address h1 = start_address h2 /\
  generation_sh h1 = generation_sh h2 /\ number_of_vertices h2 = O.

Definition resume_thread_info_relation (t1 t2: thread_info): Prop :=
  t1.(ti_heap_p) = t2.(ti_heap_p) /\
  t1.(ti_args) = t2.(ti_args) /\
  tl t1.(ti_heap).(spaces) = tl t2.(ti_heap).(spaces) /\
  let h1 := heap_head t1.(ti_heap) in
  let h2 := heap_head t2.(ti_heap) in
  h1.(space_start) = h2.(space_start) /\ h1.(total_space) = h2.(total_space) /\
  h1.(space_sh) = h2.(space_sh) /\ h2.(used_space) = 0%Z.

Lemma reset_resume_g_relation: forall g,
    resume_graph_relation g (reset_nth_gen_graph O g).
Proof.
  intros. hnf. unfold reset_nth_gen_graph. simpl.
  destruct (graph_info_head_cons (glabel g)) as [s [l [? ?]]]. rewrite H, H0. simpl.
  destruct (graph_info_head_cons (reset_nth_graph_info 0 (glabel g))) as
      [s' [l' [? ?]]]. rewrite H2. unfold reset_nth_graph_info in H1. simpl in H1.
  rewrite H in H1. inversion H1. subst l' s'.
  unfold reset_generation_info. simpl. tauto.
Qed.

Lemma reset_resume_t_relation: forall t,
    resume_thread_info_relation t (reset_nth_heap_thread_info O t).
Proof.
  intros. hnf. unfold reset_nth_heap_thread_info. simpl.
  destruct (heap_head_cons (ti_heap t)) as [s [l [? ?]]]. rewrite H0, H. simpl.
  destruct (heap_head_cons (reset_nth_heap 0 (ti_heap t))) as [s' [l' [? ?]]].
  rewrite H2. unfold reset_nth_heap in H1. simpl in H1. rewrite H in H1.
  inversion H1. subst l' s'. unfold reset_space. simpl. tauto.
Qed.

Fixpoint get_edges' (lf: list raw_field) (v: VType) (n: nat) : list EType :=
  match lf with
  | nil => nil
  | Some _ :: lf' => get_edges' lf' v (n + 1)
  | None :: lf' => (v, n) :: get_edges' lf' v (n + 1)
  end.

Definition get_edges (g: LGraph) (v: VType): list EType :=
  get_edges' (raw_fields (vlabel g v)) v O.

Lemma get_edges'_range: forall v n l m,
    In (v, n) (get_edges' l v m) -> m <= n < m + length l.
Proof.
  intros v n l. revert v n. induction l; simpl; intros. 1: exfalso; auto.
  specialize (IHl v n (m + 1)). destruct a. 1: apply IHl in H; omega.
  simpl in H. destruct H. 1: inversion H; omega. apply IHl in H. omega.
Qed.

Lemma get_edges'_nth: forall n l a m v,
    n < length l -> nth n l a = None <-> In (v, n + m) (get_edges' l v m).
Proof.
  induction n.
  - induction l; simpl; intros. 1: inversion H. destruct a.
    + split; intros. inversion H0. apply get_edges'_range in H0. exfalso; omega.
    + simpl. intuition.
  - destruct l; simpl; intros. 1: inversion H. assert (n < length l) by omega.
    specialize (IHn l a (m + 1) v H0).
    replace (n + (m + 1)) with (S (n + m)) in IHn by omega. rewrite IHn.
    destruct o; intuition. simpl in H3. destruct H3; auto. inversion H3. omega.
Qed.

(*
Class SoundGCGraph (g: LGraph) :=
  {
    field_decided_edges: forall v e,
      vvalid g v -> (src g e = v /\ evalid g e <-> In e (get_edges g v));
    generation_limit: (Zlength g.(glabel) <= MAX_SPACES)%Z;
    vertex_valid: forall v,
        vvalid g v <->
        vgeneration v < length g.(glabel) /\
        vindex v < (nth (vgeneration v) g.(glabel) null_info).(number_of_vertices);
    (* Other constraints would be added later *)
  }.

Definition Graph :=
  GeneralGraph VType EType raw_vertex_block unit graph_info (fun g => SoundGCGraph g).

Local Coercion lg_gg : GeneralGraph >-> LabeledGraph.

Definition Graph_LGraph (g: Graph): LGraph := lg_gg g.

 *)

Definition make_header (g: LGraph) (v: VType): Z:=
  let vb := vlabel g v in if vb.(raw_mark)
                          then 0 else
                            vb.(raw_tag) + (Z.shiftl vb.(raw_color) 8) +
                            (Z.shiftl (Zlength vb.(raw_fields)) 10).

Definition field_t: Type := Z + GC_Pointer + EType.

Instance field_t_inhabitant: Inhabitant field_t := inl (inl Z.zero).

Definition field2val (g: LGraph) (fd: field_t) : val :=
  match fd with
  | inl (inl z) => Z2val z
  | inl (inr p) => GC_Pointer2val p
  | inr e => vertex_address g (dst g e)
  end.

Fixpoint make_fields' (g: LGraph) (l_raw: list raw_field)
         (v: VType) (n: nat): list field_t :=
  match l_raw with
  | nil => nil
  | Some (inl z) :: l => inl (inl z) :: make_fields' g l v (n + 1)
  | Some (inr ptr) :: l => inl (inr ptr) :: make_fields' g l v (n + 1)
  | None :: l => inr (v, n) :: make_fields' g l v (n + 1)
  end.

Lemma make_fields'_eq_length: forall g l v n, length (make_fields' g l v n) = length l.
Proof.
  intros. revert n. induction l; intros; simpl. 1: reflexivity.
  destruct a; [destruct s|]; simpl; rewrite IHl; reflexivity.
Qed.

Definition make_fields (g: LGraph) (v: VType): list field_t :=
  make_fields' g (vlabel g v).(raw_fields) v O.

Definition make_fields_vals (g: LGraph) (v: VType): list val :=
  let vb := vlabel g v in
  let original_fields_val := map (field2val g) (make_fields g v) in
  if vb.(raw_mark)
  then vertex_address g vb.(copied_vertex) :: tl original_fields_val
  else original_fields_val.

Lemma fields_eq_length: forall g v,
    Zlength (make_fields_vals g v) = Zlength (raw_fields (vlabel g v)).
Proof.
  intros. rewrite !Zlength_correct. f_equal. unfold make_fields_vals, make_fields.
  destruct (raw_mark (vlabel g v)).
  - destruct (raw_fields_head_cons (vlabel g v)) as [r [l [? ?]]].
    rewrite H; simpl; destruct r; [destruct s|]; simpl;
      rewrite map_length, make_fields'_eq_length; reflexivity.
  - rewrite map_length, make_fields'_eq_length. reflexivity.
Qed.

Lemma vertex_address_the_same: forall (g1 g2: LGraph) v,
    (forall v, g1.(vlabel) v = g2.(vlabel) v) ->
    map start_address g1.(glabel).(g_gen) = map start_address g2.(glabel).(g_gen) ->
    vertex_address g1 v = vertex_address g2 v.
Proof.
  intros. unfold vertex_address. f_equal.
  - f_equal. unfold vertex_offset. f_equal. remember (vindex v). clear Heqn.
    induction n; simpl; auto. rewrite IHn. f_equal. unfold single_vertex_size.
    rewrite H. reflexivity.
  - unfold gen_start. rewrite <- !(map_nth start_address), H0. reflexivity.
Qed.

Lemma make_fields_the_same: forall (g1 g2: LGraph) v,
    (forall e, dst g1 e = dst g2 e) ->
    (forall v, g1.(vlabel) v = g2.(vlabel) v) ->
    map start_address g1.(glabel).(g_gen) = map start_address g2.(glabel).(g_gen) ->
    make_fields_vals g1 v = make_fields_vals g2 v.
Proof.
  intros. unfold make_fields_vals, make_fields. remember O. clear Heqn. rewrite H0.
  remember (raw_fields (vlabel g2 v)) as l. clear Heql.
  assert (forall n, make_fields' g1 l v n = make_fields' g2 l v n). {
    induction l; intros; simpl; auto.
    destruct a; [destruct s|]; rewrite IHl; reflexivity.
  } rewrite H2. cut (forall fl, map (field2val g1) fl = map (field2val g2) fl).
  - intros. rewrite H3. rewrite (vertex_address_the_same g1 g2) by assumption.
    reflexivity.
  - apply map_ext. intros. unfold field2val. destruct a. 1: reflexivity.
    rewrite H. apply vertex_address_the_same; assumption.
Qed.

Lemma start_address_reset: forall n l,
    map start_address l = map start_address (reset_nth_gen_info n l).
Proof.
  intros. revert n.
  induction l; intros; simpl; destruct n; simpl; [| | | rewrite <- IHl]; reflexivity.
Qed.

Lemma vertex_address_reset: forall (g: LGraph) v n,
    vertex_address g v = vertex_address (reset_nth_gen_graph n g) v.
Proof.
  intros. apply vertex_address_the_same; unfold reset_nth_gen_graph;
            simpl; [intro | rewrite <- start_address_reset]; reflexivity.
Qed.

Lemma make_fields_reset: forall (g: LGraph) v n,
    make_fields_vals g v = make_fields_vals (reset_nth_gen_graph n g) v.
Proof.
  intros. apply make_fields_the_same; unfold reset_nth_gen_graph; simpl;
            [intros; reflexivity..| apply start_address_reset].
Qed.

Lemma resume_preverse_graph_thread_info_compatible: forall (g g': LGraph) t t',
    graph_thread_info_compatible g t ->
    resume_graph_relation g g' ->
    resume_thread_info_relation t t' ->
    graph_thread_info_compatible g' t'.
Proof.
  intros. hnf in *. destruct H. destruct H0 as [? [? [? [? [? ?]]]]]. cbn in H7.
  destruct H7. destruct H1 as [? [? [? ?]]]. cbn in H11.
  destruct H11 as [? [? [? ?]]].
  destruct (graph_info_head_cons (glabel g')) as [gi' [gl' [? ?]]].
  rewrite H15, H16 in *.
  destruct (graph_info_head_cons (glabel g)) as [gi [gl [? ?]]]. rewrite H17, H18 in *.
  destruct (heap_head_cons (ti_heap t')) as [h' [l' [? ?]]]. rewrite H19, H20 in *.
  destruct (heap_head_cons (ti_heap t)) as [h [l [? ?]]]. rewrite H21, H22 in *.
  simpl in *. subst gl'. subst l'. split. 2: apply H2. constructor.
  - apply Forall_inv in H. hnf in *. destruct H as [? [? ?]]. split; [|split].
    + rewrite <- H6, <- H11. assumption.
    + rewrite <- H7, <- H13. assumption.
    + rewrite H8, H14. simpl. reflexivity.
  - apply Forall_tl in H.
    remember (combine (combine (nat_seq 1 (length gl)) gl) l) as hl.
    rewrite Forall_forall in H |- *. intros. destruct x as [[gen gin] sp].
    specialize (H _ H5). hnf in H |- *. destruct H as [? [? ?]].
    split; [|split]; [assumption..|].
    rewrite <- H23. remember (number_of_vertices gin) as n. clear -H3.
    assert (forall v, vlabel g v = vlabel g' v) by
        (intro; rewrite H3; reflexivity). induction n; simpl; auto. rewrite IHn.
    f_equal. unfold single_vertex_size. rewrite H. reflexivity.
Qed.

Definition copy1v_add_edge
           (s: VType) (g: PreGraph VType EType) (p: EType * VType):
  PreGraph VType EType := pregraph_add_edge g (fst p) s (snd p).

Definition pregraph_copy1v (g: LGraph) (old_v new_v: VType) : PreGraph VType EType :=
  let old_edges := get_edges g old_v in
  let new_edges := combine (repeat new_v (length old_edges)) (map snd old_edges) in
  let new_edge_dst_l := combine new_edges (map (dst g) old_edges) in
  fold_left (copy1v_add_edge new_v) new_edge_dst_l (pregraph_add_vertex g new_v).

Definition copy1v_mod_rvb (rvb: raw_vertex_block) (new_v: VType) : raw_vertex_block :=
  Build_raw_vertex_block true new_v (raw_fields rvb) (raw_color rvb) (raw_tag rvb)
                         (raw_fields_not_nil rvb).

Definition copy1v_update_vlabel (g: LGraph) (old_v new_v: VType) :=
  let old_rvb := vlabel g old_v in
  update_vlabel (update_vlabel (vlabel g) old_v (copy1v_mod_rvb old_rvb new_v))
                new_v old_rvb.

Definition copy1v_mod_gen_info (gi: generation_info) : generation_info :=
  Build_generation_info (start_address gi) (number_of_vertices gi + 1)
                        (generation_sh gi) (start_isptr gi)
                        (generation_share_writable gi).

Definition copy1v_mod_gen_info_list
           (l: list generation_info) (to: nat) : list generation_info :=
  firstn to l ++ copy1v_mod_gen_info (nth to l null_info) :: skipn (to + 1) l.

Lemma copy1v_mod_gen_no_nil: forall l to, copy1v_mod_gen_info_list l to <> nil.
Proof.
  repeat intro. unfold copy1v_mod_gen_info_list in H. apply app_eq_nil in H.
  destruct H. inversion H0.
Qed.

Definition copy1v_update_glabel (gi: graph_info) (to: nat): graph_info :=
  Build_graph_info (copy1v_mod_gen_info_list (g_gen gi) to)
                   (copy1v_mod_gen_no_nil (g_gen gi) to).

Definition copy1v_new_v (g: LGraph) (to: nat): VType :=
  (to, number_of_vertices (nth to g.(glabel).(g_gen) null_info)).

Definition lgraph_copy1v (g: LGraph) (v: VType) (to: nat): LGraph :=
  let new_v := copy1v_new_v g to in
  Build_LabeledGraph _ _ _ (pregraph_copy1v g v new_v)
                     (copy1v_update_vlabel g v new_v)
                     (elabel g) (copy1v_update_glabel (glabel g) to).

Definition forward_t: Type := Z + GC_Pointer + VType + EType.

Definition root2forward (r: root_t): forward_t :=
  match r with
  | inl (inl z) => inl (inl (inl z))
  | inl (inr p) => inl (inl (inr p))
  | inr v => inl (inr v)
  end.

Definition field2forward (f: field_t): forward_t :=
  match f with
  | inl (inl z) => inl (inl (inl z))
  | inl (inr p) => inl (inl (inr p))
  | inr e => inr e
  end.

Inductive forward_relation (from to: nat):
  nat -> forward_t -> LGraph -> LGraph -> Prop :=
| fr_z: forall depth z g, forward_relation from to depth (inl (inl (inl z))) g g
| fr_p: forall depth p g, forward_relation from to depth (inl (inl (inr p))) g g
| fr_v_not_in: forall depth v g,
    vgeneration v <> from -> forward_relation from to depth (inl (inr v)) g g
| fr_v_in_forwarded: forall depth v g,
    vgeneration v = from -> (vlabel g v).(raw_mark) = true ->
    forward_relation from to depth (inl (inr v)) g g
| fr_e_to_forwarded: forall depth e (g: LGraph),
    vgeneration (dst g e) = from -> (vlabel g (dst g e)).(raw_mark) = true ->
    let new_g := labeledgraph_gen_dst g e (vlabel g (dst g e)).(copied_vertex) in
    forward_relation from to depth (inr e) g new_g
| fr_e_not_to: forall depth e (g: LGraph),
    vgeneration (dst g e) <> from -> forward_relation from to depth (inr e) g g
| fr_v_in_not_forwarded_O: forall v g,
    vgeneration v = from -> (vlabel g v).(raw_mark) = false ->
    forward_relation from to O (inl (inr v)) g (lgraph_copy1v g v to)
| fr_e_to_not_forwarded_O: forall e (g: LGraph),
    vgeneration (dst g e) = from -> (vlabel g (dst g e)).(raw_mark) = true ->
    let new_g := labeledgraph_gen_dst (lgraph_copy1v g (dst g e) to) e
                                      (copy1v_new_v g to) in
    forward_relation from to O (inr e) g new_g
| fr_v_in_not_forwarded_Sn: forall depth v g g',
    vgeneration v = from -> (vlabel g v).(raw_mark) = false ->
    let new_g := lgraph_copy1v g v to in
    forward_loop from to depth (make_fields new_g (copy1v_new_v g to)) new_g g' ->
    forward_relation from to (S depth) (inl (inr v)) g g'
| fr_e_to_not_forwarded_Sn: forall depth e (g g': LGraph),
    vgeneration (dst g e) = from -> (vlabel g (dst g e)).(raw_mark) = true ->
    let new_g := labeledgraph_gen_dst (lgraph_copy1v g (dst g e) to) e
                                      (copy1v_new_v g to) in
    forward_loop from to depth (make_fields new_g (copy1v_new_v g to)) new_g g' ->
    forward_relation from to (S depth) (inr e) g g'
with
forward_loop (from to: nat): nat -> list field_t -> LGraph -> LGraph -> Prop :=
| fl_nil: forall depth g, forward_loop from to depth nil g g
| fl_cons: forall depth g1 g2 g3 f fl,
    forward_relation from to depth (field2forward f) g1 g2 ->
    forward_loop from to depth fl g2 g3 -> forward_loop from to depth (f :: fl) g1 g3.

Definition graph_gen_has (g: LGraph) (n: nat): Prop := n < length g.(glabel).(g_gen).

Definition nth_space (t_info: thread_info) (n: nat): space :=
  nth n t_info.(ti_heap).(spaces) null_space.

Definition gen_size (t_info: thread_info) (n: nat): Z :=
  total_space (nth_space t_info n).
