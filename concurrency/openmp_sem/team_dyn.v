From mathcomp.ssreflect Require Import ssreflect ssrbool.
Require Import Coq.Program.Wf FunInd Recdef.
From compcert Require Import Values Clight Memory Ctypes AST Globalenvs.
From VST.concurrency.openmp_sem Require Import reduction notations for_construct clight_fun.
From stdpp Require Import base list.
From RecordUpdate Require Import RecordSet.
Import RecordSetNotations.

Section SiblingTree.

  Context {B:Type}.
  (* a tree that can have multiple children *)
  Inductive stree :=
  | SNode : B -> list stree -> stree.

  Definition data (st: stree) : B :=
    match st with | SNode b _ => b end.

  Definition kids (st: stree) : list stree :=
    match st with | SNode _ kids => kids end.

  #[export] Instance stree_settable : Settable stree := settable! SNode < data; kids >.

  Definition update_data (st: stree) (b: B) : stree :=
    match st with | SNode _ kids => SNode b kids end.

  Definition update_kids (st: stree) (kids: list stree) : stree :=
    match st with | SNode b _ => SNode b kids end.

  (* stree eliminator, with the ability of knowing a node's parent
     f (parent: option B) (current_node_info: B) (previously accumulated results: A) *)
  Fixpoint fold_tree_p {A: Type} (st: stree) (f: option B -> B -> A -> A) (accu: A) (parent: option B) : A :=
    match st with | SNode b kids =>
    let accu' := f parent b accu in
       foldr (λ st accu, fold_tree_p st f accu $ Some b) accu' kids
    end.

  Definition tree_cursor : Type := stree -> stree.

  Definition tree_ref : Type := stree * tree_cursor.
  #[export] Instance settable_tree_ref {A B: Type}: Settable _ := settable! (@pair A B) <fst; snd>.
  Definition of_tref (tref: tree_ref) : stree := tref.2 tref.1.

  (* elements to the left and to the right *)
  Definition list_cursor {A: Type} : Type := @list A * @list A.

  Definition list_ref {A: Type} : Type := A * @list_cursor A.

  Definition list_cursor_kont {A: Type} (l_cursor: list_cursor) (m : A) : list A :=
    let (l, r) := l_cursor in l ++ [m] ++ r.

  Fixpoint make_list_ref_aux {A: Type} (lst: @list A) (l: @list A) : list $ @list_ref A :=
    match lst with 
    | m::r => (m, (l, r)) :: make_list_ref_aux r (l++[m])
    | _ => nil
    end.

  Definition make_list_ref {A: Type} (l: @list A) : list $ @list_ref A :=
    make_list_ref_aux l nil.

  Definition tree_size (s: stree) :=
    fold_tree_p s (λ _ _ acc, 1 + acc) 0 None.

  Definition tree_ref_size (ref: tree_ref) :=
    let '(st, _) := ref in tree_size st.

  Definition kids_ref_list ref : list tree_ref :=
    let '(s, t_cursor) := ref in
    match s with | SNode d kids =>
      (λ l_ref, 
      let '(kid_st, l_cursor) := l_ref in
                                (kid_st, t_cursor ∘ (SNode d) ∘ (list_cursor_kont l_cursor))) 
      <$> (make_list_ref kids)
    end
    .

    (* probably needs to measure this; fix *)
  Program Fixpoint stree_lookup_aux (is_target: stree -> bool) (ref : tree_ref) (accu: option tree_ref) {measure (tree_ref_size ref)}: option tree_ref :=
    match accu with
    | Some _ => accu (* already found *)
    | None =>
      match ref with
      | (st, cursor) =>
      if is_target st then Some ref
      else
        foldr (λ ref accu, stree_lookup_aux is_target ref accu) accu
              $ kids_ref_list ref
      end
    end.
  Next Obligation.
    intros. Admitted.
  Next Obligation.
    intros. Admitted.

  Definition stree_lookup (is_target: stree -> bool) (t: stree) : option tree_ref :=
    stree_lookup_aux is_target (t, id) None.

  Lemma lookup_ref_same (is_target: stree -> bool) (t: stree) :
    forall ref,
    stree_lookup is_target t = Some ref →
    of_tref ref = t.
  Admitted.

  Lemma lookup_has_prop (is_target: stree -> bool) (t: stree) (ref: tree_ref) :
    stree_lookup is_target t = Some ref →
    is_target (fst ref) = true.
  Admitted.

  (* lookup with is_target, if found, update the data of the subtree root to b' *)
  Definition stree_update (is_target: stree -> bool) (f: stree -> option stree) (st: stree) : option stree :=
    ref ← stree_lookup is_target st;
    subtree ← f ref.1;
    Some (ref.2 subtree).

End SiblingTree.

Notation " x '.data' " := (data x) (at level 3).
Notation " x '.kids' " := (kids x) (at level 3).

(* contexts regarding a team are the parallel_construct_context and the team_executing_context. *)
Variant parallel_construct_context' :=
| team_ctx_parallel : red_vars -> (* used for the reduction at the end of the for construct *)
                  parallel_construct_context'.
Definition parallel_construct_context : Type := (nat * parallel_construct_context').
            

(* the context for the current team executing region.
  Note that the parallel construct is not a team-executing construct.
  Every team_executing_context carries a nat, it is the corresponding pragma's index.
  The team would have to check  *)
Variant team_executing_context' :=
| team_ctx_for :
            (* The team workload split. Is A partition of iterations.
               A thread works on a chunk of iterations. *)
           (list $ list chunk) -> 
           red_vars -> (* used for the reduction at the end of the for construct *)
           team_executing_context'
| team_ctx_single : team_executing_context'
| team_ctx_barrier : team_executing_context'
.
Definition team_executing_context : Type := (nat * team_executing_context').

(* we assume each pragma in the program have distinct index, and two teamcontexts
  come from the same pragma if they have the same index. *)
Definition matching_par_ctx (c1 c2: parallel_construct_context) : bool :=
  c1.1 =? c2.1.

(* two team executing contexts are the same if they have the same index and
   their corresponding team_executing_context' are the same. *)
Definition matching_tm_exec_ctx (c1 c2: team_executing_context) : bool :=
  c1.1 =? c2.1.
 

(* a thread context is the *)
Variant thread_context :=
| thread_ctx_parallel : pv_map -> thread_context
| thread_ctx_for : pv_map -> thread_context
| thread_ctx_single : pv_map -> thread_context
| thread_ctx_barrier : thread_context.

Definition pv_of_thread_ctx (td_ctx: thread_context) : pv_map :=
  match td_ctx with
  | thread_ctx_parallel pvm => pvm
  | thread_ctx_for pvm => pvm
  | thread_ctx_single pvm => pvm
  | thread_ctx_barrier => pvm_init (* an empty pv map *)
  end.

Section OpenMPThreads.

    (* OpenMP context for a thread in a parallel region *)
    Record o_ctx := {
      t_tid : nat; (* thread id *)
      (* every time we run a cothe th privatized variables and their original values *)
      o_thread_ctxs : list thread_context;
      (* o_team_ctxs fields exists iff this node has a team of children.
         o_team_ctxs.1 is for the parallel region enclosing the team;
         o_team_ctxs.2 exists iff some threads in the team are working in some team executing region.
      *)
      o_team_ctxs : option (parallel_construct_context * option team_executing_context);
    }.

    #[export] Instance settable_o_ctx : Settable _ :=
      settable! Build_o_ctx <t_tid; o_thread_ctxs; o_team_ctxs>.

    Section OpenMPTeam.

    (* team id -> team_tree *) 

    (**   (0)

           parallel(3)-> 

           [0]
        /  |  \   
      [(0), (1), (2)]]

            parallel(2) ->

           [0]
        /    |    \   
      [(0), [1], (2)]]
            / \
    [(0),[(0),(1)], (2)]]      
            
    *)

      (* model of the dynamics of a team. 
         Each node is either a thread with no children, which we call a leaf node, that represents an executing thread;
         or a thread that has children, which are the team that it spawned. This team includes the thread itself, and
         the parent node data contains bookkeeping info about this team. When the team is done, we can fire the team,
         and the parent thread recovers its previous state as a leaf node.
         The bookkeeping data of a team contains `Some privatized_vars` if the parallel region of the team (i.e. the lifetime
         span of the team) also contains a reduction clause. *)
      Definition team_tree := @stree (o_ctx).

      Implicit Types (pvm : pv_map) (ot: o_ctx) (tree: team_tree)
        (i: ident) (ge orig_ge: genv) (le orig_le: env)
        (ce:composite_env) (m: mem) (b:Values.block) (ty:type)
        (td_ctx: thread_context) (tm_exec_ctx: team_executing_context) (par_ctx: parallel_construct_context).

      (* the first thread in the program *)
      Definition ot_init (tid: nat) : o_ctx := Build_o_ctx tid [] None.

      (* a team starts with just the main thread *)
      Definition node_init (tid: nat) : team_tree := SNode (ot_init tid) [].

      Definition is_tid (tid: nat) (ot: o_ctx) : Prop :=
        ot.(t_tid) = tid.
      #[global] Instance is_tid_dec (tid: nat) (ot: o_ctx) : Decision (is_tid tid ot).
      Proof. apply Nat.eq_dec. Qed.

      (* the list of all leaf threads *)
      Fixpoint tree_to_list (tree: team_tree) : (list o_ctx) :=
        match tree with
        | SNode ot ts =>
          match ts with
          | [] => [ot] (* leaf node*)
          | _ => concat (tree_to_list <$> ts)
          end
        end.

      Definition leaf_tids (t: team_tree) : list nat :=
        t_tid <$> tree_to_list t.

      Definition has_tid' (tid: nat) (tree: team_tree) : Prop :=
        In tid $ leaf_tids tree.
        
      (* o_ctx of the (immediate) team led by root of tree; does not include subteams *)
      Definition team_info (tree: team_tree) : list o_ctx :=
        data <$> kids tree.

      Definition has_tid (tid: nat) (tree: team_tree) : bool :=
        isSome $ stree_lookup (λ st, decide $ is_tid tid $ st.data) tree.

      Lemma has_tid_correct tid tree :
        has_tid tid tree = true ↔ has_tid' tid tree.
      Proof. Admitted.

      Definition tid_unique (tree: team_tree) : Prop :=
        NoDup $ t_tid <$> tree_to_list tree.

      Record team_tree_inv (tree: team_tree) : Prop :=
        { inv_tid_unique : tid_unique tree }.

      (** folloing opeartions assume that tids in the trees are NoDup, and the indexing tid exists as a leaf
           node in the tree. *)
      (** spawns a team at every TeamLeaf that contains tid.
       * should require that tid is unique in tree.
       *)

      (* t is a leaf node and represents tid *)
      Definition is_leaf_tid (tid: nat) (t: team_tree) : bool :=
        match t with
        | SNode ot [] => decide (is_tid tid ot)
        | _ => false
        end.

      (* find the leaf node that represents tid *)
      Definition lookup_tid (tid: nat) (t: team_tree) : option tree_ref :=
        stree_lookup (is_leaf_tid tid) t.

      Definition update_tid (tid: nat) (t: team_tree) (f: team_tree -> option team_tree) : option team_tree :=
        stree_update (is_leaf_tid tid) f t.

      (* whether tree is the parent of a leaf node for tid. *)
      Definition is_parent_tree_of (tid: nat) (tree: team_tree) : Prop :=
        match tree with
        | SNode ot kids =>
           (Exists (λ kid, is_leaf_tid tid kid=true) tree.kids) end.

      #[global] Instance is_parent_tree_of_dec tid tree : Decision (is_parent_tree_of tid tree).
      Proof.
        move : tree => [ot ts].
        rewrite /is_parent_tree_of.
        apply Exists_dec. apply _.
      Qed.

      Definition parent_tree_of (tid: nat) (tree: team_tree) : option tree_ref :=
        stree_lookup (λ st, decide $ is_parent_tree_of tid st) tree.

      (* the parallel pragma spawns a team of threads, each gets initialized thread contexts;
         sets team_ctxs.1. *)
      Definition spawn_team (tid: nat) (team_mates: list nat) rvs (spar_index:nat) (tree: team_tree) : option team_tree :=
        update_tid tid tree (λ leaf, Some $ leaf <| kids := map node_init (tid::team_mates) |>
                                                 <| data; o_team_ctxs := Some ((spar_index, team_ctx_parallel rvs), None) |>).
      
      (* t must be a leaf node for that thread.
         append a of thread context to t. *)
      Definition leaf_add_td_ctx (t: team_tree) td_ctx : team_tree :=
        t <| data; o_thread_ctxs ::= cons td_ctx |>.

      Definition mate_add_td_ctx (tid:nat) (td_ctx: thread_context) (tree: team_tree) : option team_tree :=
        update_tid tid tree (λ leaf, Some $ leaf_add_td_ctx leaf td_ctx).

      (* Maintenance of the team context when tid enters a team executing construct.
          if it is the first thread in the team that enters this construct <-> data.o_team_ctxs.2 is None,
          it sets data.o_team_ctxs.2 according to (idx, pragma);
          otherwise, someone else in the team has already entered a team executing construct, 
          and it must enter the same construct, so it checks whether (idx, pragma) corresponds to data.o_team_ctxs.2. *)
      Definition mate_maybe_add_team_exec_ctx (tree: team_tree) tid tm_exec_ctx : option (team_tree * team_executing_context) :=
        pref ← parent_tree_of tid tree;
        tm_ctx ← pref.1.data.(o_team_ctxs);
        match tm_ctx.2 with
        | Some tm_exec_ctx' => 
          if matching_tm_exec_ctx tm_exec_ctx tm_exec_ctx' 
          then Some (tree, tm_exec_ctx')
          else None
        | None => let tree' := of_tref $ pref <| fst; data; o_team_ctxs := Some (tm_ctx.1, Some tm_exec_ctx) |> in
          Some (tree', tm_exec_ctx)
        end
      .

      (* find tid's teammates' thread ids, including tid.
         If tid is root, return itself. *)
      Definition team_mates_tids tid tree: list nat :=
      match parent_tree_of tid tree with
      | None => [tid]
      | Some pref => map (λ kid, kid.data.(t_tid)) pref.1.kids
      end.

      Definition mate_pop_thread_context (tree: team_tree) (tid: nat) : option (team_tree * thread_context) :=
        ref ← lookup_tid tid tree;
        match ref.1.data.(o_thread_ctxs) with
        | [] => None
        | th_ctx::tl =>
          let t' := of_tref $ ref <| fst; data; o_thread_ctxs := tl |> in
          Some (t', th_ctx)
        end.

      (* pop the team executing context for the team that tid is in *)
      Definition team_pop_team_exec_context (tree: team_tree) (tid: nat) : option (team_tree * team_executing_context) :=
        pref ← parent_tree_of tid tree;
        tm_ctxs ← pref.1.data.(o_team_ctxs);
        tm_exec_ctx ← tm_ctxs.2;
        Some (of_tref $ pref <| fst; data; o_team_ctxs := Some (tm_ctxs.1, None) |>, tm_exec_ctx).
      
      (*** ending a parallel construct ***)
      (* pop the parallel context for the team that tid is in *)
      Definition team_pop_parallel_context (tree: team_tree) (tid: nat) : option (team_tree * parallel_construct_context) :=
        pref ← parent_tree_of tid tree;
        tm_ctxs ← pref.1.data.(o_team_ctxs);
        (* must not have a team_executing context *)
        match tm_ctxs.2 with
        | Some _ => None
        | None => Some (of_tref $ pref <| fst; data; o_team_ctxs := None |>, tm_ctxs.1) end.

      (* all teammates of tid have no thread context left *)
      Definition thread_context_resolved (tree: team_tree) (tid: nat) : bool :=
        match parent_tree_of tid tree with
        | Some pref => forallb (λ kid, decide (kid.data.(o_thread_ctxs) = [])) pref.1.kids
        | None => false
        end.

      (* there is no team context for the team of tid *)
      Definition team_context_resolved (tree: team_tree) (tid: nat) : bool :=
        match parent_tree_of tid tree with
        | Some pref => decide (pref.1.data.(o_team_ctxs) = None)
        | None => false
        end.

      (* finish a team when there is no team or thread context left to resolve *)
      Definition team_fire (tid: nat) (tree: team_tree) : option team_tree :=
        if thread_context_resolved tree tid &&
           team_context_resolved tree tid
        then pref ← parent_tree_of tid tree;
             Some $ of_tref (pref <| fst; kids := [] |>)
        else None.

      (* returns the first i if f(l[i])=true. *)
      Fixpoint find_index {A:Type} (f: A->bool) (l:list A) : option nat :=
        match l with
        | [] => None
        | x::xs => if f x then Some 0 else
                   match find_index f xs with
                   | None => None
                   | Some n => Some (S n)
                   end
        end.
      
      (* thread num is the index to tid of parent tree's kids list. *)
      Definition get_thread_num tid tree : option nat :=
        ref ← parent_tree_of tid tree;
        find_index (is_leaf_tid tid) ref.1.kids.

      (* tid is a leader of its current team if it's parent node has the same tid. *)
      Definition is_leader (tid: nat) (tree: team_tree) : bool :=
        match parent_tree_of tid tree with
        | None => true
        | Some pref => pref.1.data.(t_tid) =? tid
        end.

    End OpenMPTeam.
End OpenMPThreads.