Require Import VST.floyd.proofauto.
Require Import CertiGraph.priq.priq_arr_specs.
Require Import CertiGraph.graph.graph_model.
Require Import CertiGraph.graph.FiniteGraph.
Require Import CertiGraph.graph.undirected_graph.
Require Import CertiGraph.graph.MathAdjMatGraph.
(* Require Import CertiGraph.graph.SpaceAdjMatGraph_noncont. *)
Require Import CertiGraph.prim.MatrixUGraph.
Require Import CertiGraph.prim.noroot_prim.
Require Import CertiGraph.prim.spatial_undirected_matrix.
Require Import CertiGraph.lib.List_ext.

Local Open Scope Z_scope.

Instance CompSpecs : compspecs. Proof. make_compspecs prog. Defined.

Definition Vprog : varspecs. mk_varspecs prog. Defined.

Definition initialise_list_spec :=
  DECLARE _initialise_list
  WITH sh: share, arr : val, old_list: list val, a: Z
  PRE [tptr tint, tint]
     PROP ( writable_share sh;
            Zlength old_list = SIZE; (*<--I'm not sure if this is derivable from SEP*)
            repable_signed a
          )
     PARAMS ( arr; Vint (Int.repr a) )
     GLOBALS ()
     SEP (data_at sh (tarray tint SIZE) (old_list) (arr))
  POST [ tvoid ]
     PROP ()
     LOCAL ()
     SEP (data_at sh (tarray tint SIZE) (list_repeat (Z.to_nat SIZE) (Vint (Int.repr a))) arr
         ).

Definition initialise_matrix_spec :=
  DECLARE _initialise_matrix
  WITH sh: share, arr : val, old_contents: list (list Z), a: Z
  PRE [tptr (tarray tint SIZE), tint]
     PROP ( writable_share sh;
            Zlength old_contents = SIZE;
            forall row, In row old_contents -> Zlength row = SIZE;
            repable_signed a
          )
     PARAMS ( arr ; Vint (Int.repr a) )
     GLOBALS ()
     SEP (undirected_matrix sh (old_contents) (arr))
  POST [ tvoid ]
     PROP ()
     LOCAL ()
     SEP (undirected_matrix sh (list_repeat (Z.to_nat SIZE) (list_repeat (Z.to_nat SIZE) a)) arr
         ).

Definition prim_spec :=
  DECLARE _prim
  WITH sh: share, g: G, garbage: list V, gptr : pointer_val, parent_ptr : pointer_val
  PRE [tptr (tarray tint SIZE), tptr tint]
     PROP ( writable_share sh
          )
     PARAMS ( pointer_val_val gptr; pointer_val_val parent_ptr)
     GLOBALS ()
     SEP (undirected_matrix sh (graph_to_symm_mat g) (pointer_val_val gptr);
          data_at sh (tarray tint SIZE) (map (fun x => Vint (Int.repr x)) garbage) (pointer_val_val parent_ptr)
         )
  POST [ tint ]
     EX mst: G,
     EX fmst: FiniteGraph mst,
     EX parents: list V,
     PROP ( (*connected_graph mst;*)
            minimum_spanning_forest mst g;
            Permutation (EList mst) (map (fun v => eformat (v, Znth v parents))
              (filter (fun v => Znth v parents <? SIZE) (nat_inc_list (Z.to_nat SIZE))))
          )
     RETURN (Vint (Int.repr 0))
     SEP (undirected_matrix sh (graph_to_symm_mat g) (pointer_val_val gptr);
          data_at sh (tarray tint SIZE) (map (fun x => Vint (Int.repr x)) parents) (pointer_val_val parent_ptr)
         ).

Definition Gprog : funspecs :=
  ltac:(with_library prog
                     [push_spec;
                     pq_emp_spec;
                     popMin_spec;
                     adjustWeight_spec;
                     initialise_list_spec;
                     initialise_matrix_spec;
                     prim_spec
       ]).