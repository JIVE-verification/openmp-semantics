(* the for construct *)

From Coq Require Import String ZArith.
From compcert Require Import Clight Cop Clightdefs AST Integers Ctypes Values.
From compcert Require Import -(notations) lib.Maps.
From VST.concurrency.openmp_sem Require Import notations canonical_loop_nest.
From RecordUpdate Require Import RecordSet.
Import RecordSetNotations.

From stdpp Require Import base list.


(* Steps:

    0. (TODO) Determine if the for loop conforms to the syntax for canonical loop nest: 
        for (init; test; incr) { body }

    is_a_canonical_loop_nest (s:statement) : option CanonicalLoopNest

    where body is unspecified for now. it should not contain any jump to the outside of body

    1. determine whether a loop is a canonical loop nest
       this includes instantiating a chunk split module

    2. invoke transform_chunks, assgin workload to threads
    3. insert barrier at the end
*)

(* a chunk (a,b) specifies a portion of the loop boundary [a,b), where a<b *)
Definition chunk : Type := nat * nat.
Definition sum_list (l: list nat) := fold_right plus 0 l.
Definition sum_firstn (n: nat) (l: list nat) := sum_list (firstn n l).

(* split the index into segments. *)
Module Type ChunkSplit.

    (* the logical iteration indexes for the for loop;
       derived with simple static analysis? *)

    (* the lowerbound of loop range *)
    Parameter lb : nat.
    (* each loop increases by incr *)
    Parameter incr : nat.
    (* the number of iterations *)
    Parameter iter_num : nat.
    

    (* number of threads to split the workloads  *)
    Parameter thread_num : nat.
    Parameter thread_num_positive : 0 < thread_num.

    (* a partition of the loop range.
       =nil or [lb, lb)? if iter_num = 0,
       =[lb,lb+incr) if iter_num=1 *)
    Parameter chunks : list chunk.

    (* the chunks are constructed with a list of chunk sizes *)
    Parameter chunks_is_a_partition :
        iter_num > 1 ->
        (* the chunks are constructed with a list of positive chunk ste *)
        ∃ chunk_sizes : list nat,
        Forall (λ n, 0 < n) chunk_sizes ∧
        length chunk_sizes = length chunks ∧
        ∀ i chk, nth_error chunks i = Some chk ->
            chk = (lb + incr * (sum_firstn i chunk_sizes),
                   lb + incr * (sum_firstn (i + 1) chunk_sizes)).

    (* i: the OMP team thread number
       team_workloads[i] : a list of chunks that is assigned to thread i *)
    Parameter team_workloads : list $ list chunk.
    Parameter team_workloads_length : length team_workloads = thread_num.
    (* team workloads is a permutation of [0..chunk_num) *)
    Parameter team_workloads_is_a_division :
        Permutation (concat team_workloads) chunks.
End ChunkSplit.

Module ExampleSplit : ChunkSplit.
    (*
        step = 2
        lb = 3
        (10-3) / 2 = 3
        [3, 5, 7, 9]

        for(int i=3; i<10; i+=2){
            // do something
        }
    *)

(*  An example of a loop split:
    
    for(int i=3; i<10; i+=2){
            // do something
    }


    1st thread: 
    for(int i=9; i!=11; i+=2){
            // do something
    }
    for(int i=3; i!=5; i+=2){
            // do something
    }
    (barrier)
    
*)

    Definition lb := 3.
    Definition incr := 2.
    Definition iter_num := 3.
    Definition thread_num := 5.

    Lemma thread_num_positive : 0 < thread_num. Proof. unfold thread_num. lia. Qed.
    (* this specifies 3 loops, with loop indexes {3}, {5,7}, {9} *)
    Definition chunks := [(3, 5); (5, 9); (9, 11)].
    Definition chunk_sizes := [1;2;1].
    Lemma chunks_is_a_partition : iter_num > 1 ->
        (* the chunks are constructed with a list of positive chunk ste *)
        ∃ chunk_sizes : list nat,
        Forall (λ n, 0 < n) chunk_sizes ∧
        length chunk_sizes = length chunks ∧
        ∀ i chk, nth_error chunks i = Some chk ->
            chk = (lb + incr * (sum_firstn i chunk_sizes),
                   lb + incr * (sum_firstn (i + 1) chunk_sizes)).
    Proof. intros _. exists chunk_sizes. split.
        { unfold chunk_sizes. repeat apply List.Forall_cons; try lia. done. }
        split.
        { done. }
        intros. 
        do 4 (destruct i; [ simpl in *; congruence | ]).
        simpl in *. congruence.
    Qed.

    Definition team_workloads := [[(9, 11); (3, 5)];
                                  [(5, 9)];
                                  []; []; []].
    Lemma team_workloads_length : length team_workloads = thread_num. Proof. reflexivity. Qed.
    Lemma team_workloads_is_a_division : Permutation (concat team_workloads) chunks.
    Proof. simpl concat. unfold chunks. rewrite Permutation_swap. 
          apply Permutation_skip.
          rewrite Permutation_swap. done. Qed.
End ExampleSplit.

Section For.
    (* transform the rage of the original loop to the range of the chunk.
       result is a segment of the original loop if chunk is a sgement of the iterations *)
    Definition transform_chunk
        (loop: CanonicalLoopNest) (ty: type) (var_id: AST.ident) (var_ty: type)
        (Hty: integer_expr (Evar var_id ty)) (chk: chunk) : CanonicalLoopNest :=
    match loop with
    | CanonicalLoopNestCons _ test_expr incr_expr loop_body =>
        CanonicalLoopNestCons 
            (InitStmtCons var_id (Econst_int (Int.repr (Z.of_nat chk.1)) ty))
            (TestExpr1 (VarInt (Evar var_id ty) Hty) ROP_ne (Econst_int (Int.repr (Z.of_nat chk.2)) ty))
            incr_expr
            loop_body
    end.

    (* a sequence of loop segments *)
    Definition transform_chunks (chks: list chunk) (loop: CanonicalLoopNest)  (ty: type) (var_id: AST.ident) (var_ty: type)
        (Hty: integer_expr (Evar var_id ty)) : statement :=
    foldr (λ loop_seg accu, Ssequence accu $ elaborate_canonical_loop_nest loop_seg)
          Sskip (map (transform_chunk loop ty var_id var_ty Hty) chks).
End For.
