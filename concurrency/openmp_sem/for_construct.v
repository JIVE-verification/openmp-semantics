(* the for construct *)

From Coq Require Import String ZArith.
From compcert Require Import Clight Cop Clightdefs AST Integers Ctypes Values.
From compcert Require Import -(notations) lib.Maps.
From VST.concurrency.openmp_sem Require Import notations canonical_loop_nest clight_fun.
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

Definition val_to_Z (v: val) : option Z :=
    match v with
    | Vint i => Some $ Int.intval i
    | _ => None
    end.

Definition expr_to_Z ge e le m (exp: expr) : option Z :=
    match @eval_expr_fun ge e le m exp with
    | Some v => val_to_Z v
    | None => None
    end.
    
(* take a CanonicalLoopNest, return the lb, incr and iter_num. *)
Definition lb_of_loop (loop: CanonicalLoopNest) ge e le m : option Z :=
    match loop with
    | CanonicalLoopNestCons init_stmt test_expr incr_expr loop_body =>
        match init_stmt with
        | InitStmtCons var_id lb => expr_to_Z ge e le m lb
        end
    end.

Definition incr_of_loop (loop: CanonicalLoopNest) ge e le m : option Z :=
    match loop with
    | CanonicalLoopNestCons init_stmt test_expr incr_expr loop_body =>
        match incr_expr with
        | VarPlusIncr _ incr => expr_to_Z ge e le m incr.(canonical_loop_nest.e)
        | VarMinusIncr _ incr => z ← expr_to_Z ge e le m incr.(canonical_loop_nest.e);
                                 Some $ Z.opp z
        | _ => None (* assume other cases are converted to the above ones *)
        end
    end.

(* take a CanonicalLoopNest, return the number of iterations *)
Definition iter_num_of_loop (loop: CanonicalLoopNest) ge e le m : option nat :=
    lb ← lb_of_loop loop ge e le m;
    incr ← incr_of_loop loop ge e le m;
    match loop with
    | CanonicalLoopNestCons init_stmt test_expr incr_expr loop_body =>
        (* ub here is the value in the test_expr, whether it is inclusive or not
           depends on the kind of test_expr *)
        match test_expr with
        | TestExpr1 _ rel_op ub =>
            match expr_to_Z ge e le m ub with
            | None => None
            | Some ub =>
                match rel_op with
                | ROP_le =>
                    if decide (incr <= 0)%Z then None else (* standard p.201, 13 *)
                    if decide ((ub - lb) / incr < 0)%Z
                    then Some 0 (* this is what gcc does *)
                    else Some $ 1 + Z.to_nat ((ub - lb) / incr)%Z
                | ROP_lt =>
                    if decide (incr <= 0)%Z then None else
                    (* [var < ub] same as [var <= ub-1], and the arithmetics are in Z so no risk of overflow *)
                    if decide (((ub-1) - lb) / incr < 0)%Z
                    then Some 0
                    else Some $ 1 + Z.to_nat (((ub-1) - lb) / incr)%Z
                | ROP_ge => 
                    if decide (incr >= 0)%Z then None else
                    if decide ((ub - lb) / incr < 0)%Z
                    then Some 0
                    else Some $ 1 + Z.to_nat ((ub - lb) / incr)%Z
                | ROP_gt =>
                    if decide (incr >= 0)%Z then None else
                    (* [var > ub] same as [var >= ub+1], and the arithmetics are in Z so no risk of overflow *)
                    if decide ((lb - (ub-1)) / incr < 0)%Z
                    then Some 0
                    else Some $ 1 + Z.to_nat (((ub+1) - lb) / incr)%Z
                | ROP_ne =>
                    (* standard p.201, 21 *)
                    if decide ((incr <> 1) ∨ incr <> -1)%Z then None else
                    Some $ Z.to_nat ((ub - lb) / incr)%Z
                end
            end
        | _ => None (* assume TestExpr2 has been converted to TestExpr1 *)
        end
    end.


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
    
    #pragma omp for
    for(i=3; i<10; i+=2){
            // do something
    }
    for(int i=3; i<10; i+=2){
            // do something
    }

    for(int i=3; i!=5; i+=2){
            // do something
    }
    for(int i=5; i!=9; i+=2){
            // do something
    }
    for(int i=9; i!=11; i+=2){
            // do something
    }
    
    -> example assignment of the workload:
        1st thread:
        for(int i=9; i!=11; i+=2){
            // do something
        }
        for(int i=3; i!=5; i+=2){
            // do something
        }
        
        2nd thread:
        for(int i=5; i!=9; i+=2){
            // do something
        }

        3-5rd thread:
        // do nothing

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
                                  [];
                                  [];
                                  []].
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
        (loop: CanonicalLoopNest) (chk: chunk) : CanonicalLoopNest :=
    match loop with
    | CanonicalLoopNestCons init_stmt test_expr incr_expr loop_body =>
        match init_stmt with
        | InitStmtCons var_id init_expr =>
            let ty := typeof init_expr in
            CanonicalLoopNestCons 
                (InitStmtCons var_id (Econst_int (Int.repr (Z.of_nat chk.1)) ty))
                (TestExpr1 (VarInt (Evar var_id ty)) ROP_ne (Econst_int (Int.repr (Z.of_nat chk.2)) ty))
                incr_expr
                loop_body
        end
    end.

    (* a sequence of loop segments *)
    Definition transform_chunks (chks: list chunk) (loop: CanonicalLoopNest) : statement :=
    foldr (λ loop_seg accu, Ssequence accu $ elaborate_canonical_loop_nest loop_seg)
          Sskip (map (transform_chunk loop) chks).

End For.
