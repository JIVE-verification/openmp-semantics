From mathcomp.ssreflect Require Import ssreflect ssrbool.
Require Import Coq.Program.Wf FunInd Recdef.
From compcert Require Import Values Clight.
From VST.concurrency.openmp_sem Require Import reduction notations for_construct.
From stdpp Require Import base list.
From RecordUpdate Require Import RecordSet.
Import RecordSetNotations.

Section SiblingTree.

  Context {B:Type}.
  (* a tree that can have multiple children *)
  Inductive stree :=
  | SNode : B -> list stree -> stree.

  Definition data_of (st: stree) : B :=
    match st with | SNode b _ => b end.

  Definition kids_of (st: stree) : list stree :=
    match st with | SNode _ kids => kids end.

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

  Lemma lookup_has_prop (is_target: stree -> bool) (t: stree) (ref: tree_ref) :
    stree_lookup is_target t = Some ref →
    is_target (fst ref) = true.
  Admitted.

  (* lookup with is_target, if found, update the data of the subtree root to b' *)
  Definition stree_update (is_target: stree -> bool) (b': B) (st: stree) : option stree :=
    ref ← stree_lookup is_target st;
    Some (ref.2 $ update_data ref.1 b').

End SiblingTree.

Notation " x '.data_of' " := (data_of x) (at level 20).
Notation " x '.kids_of' " := (kids_of x) (at level 20).
Notation " x '.update_data' b " := (update_data x b) (at level 20).
Notation " x '.update_kids' kids " := (update_kids x kids) (at level 20).

Section OpenMPThreads.

    (* OpenMP thread info *)
    Record ot_info := {
      t_tid : nat; (* thread id *)
      o_team_id : nat; (* each of new team should get a different number *)
      (* o_tid : nat; thread id in the current team, NOT tid *)
      (* o_level : nat; nesting level *)
      o_done : bool; (* if it is spawned by some primary thread, set to true when 
                     it has reached the last barrier *)
      o_work_sharing : bool; (* is in work-sharing region; can only enter once *)
      (* work loads of the team that is this thread spawns, i.e. the children of this node.
         now chunk split is decided the first time a thread hits the for pragma; if need to
         allow more flexible scheduling, when thread i hits the for pragma, maybe only
         instantiate that thread's workload and quantify over the uninstantiated part
         [ team_workloads[i]=something ∧ ∃ rest workloads, s.t. the workloads are still
           consistent ] *)
      (* if it can pass the barrier; issued by a thread to all its teammmates when it does
         not have a ticket and sees that all its team mates are at a barrier *)
      o_barrier_ticket : bool;
      o_team_workloads : option $ list $ list chunk 
    }.

    #[export] Instance settable_ot_info : Settable _ :=
      settable! Build_ot_info <t_tid; o_team_id; o_done; o_work_sharing; o_barrier_ticket; o_team_workloads>.

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
      Definition team_tree := @stree (ot_info * option contrib_maps).

      (* the first thread in the program *)
      Definition ot_init (tid: nat) := Build_ot_info tid 0 false.

      (* a team starts with just the main thread *)
      Definition team_init (tid: nat) := SNode (ot_init tid) [].

      (* ot creates a new team with the other team_mates and starts a new parallel region, which is not work-sharing. *)
      Definition spawn_team' (ot: ot_info) (team_mates: list nat) (pv : option contrib_maps): team_tree :=
        SNode (ot, pv) $ (λ tid, SNode ((Build_ot_info tid 0 false false false None), None) []) <$> (cons (ot.(t_tid)) team_mates).

      Definition is_tid (tid: nat) (ot: ot_info) : Prop :=
        ot.(t_tid) = tid.
      #[global] Instance is_tid_dec (tid: nat) (ot: ot_info) : Decision (is_tid tid ot).
      Proof. apply Nat.eq_dec. Qed.

      (* the list of all leaf threads *)
      Fixpoint tree_to_list (tree: team_tree) : (list ot_info) :=
        match tree with
        | SNode (ot, pv) ts =>
          match ts with
          | [] => [ot] (* leaf node*)
          | _ => concat (tree_to_list <$> ts)
          end
        end.

      Definition leaf_tids (t: team_tree) : list nat :=
        t_tid <$> tree_to_list t.

      Definition has_tid' (tid: nat) (tree: team_tree) : Prop :=
        In tid $ leaf_tids tree.
        
      (* ot_info of the (immediate) team led by root of tree; does not include subteams *)
      Definition team_info (tree: team_tree) : list ot_info :=
        (fst ∘ data_of) <$> kids_of tree.

      Definition has_tid (tid: nat) (tree: team_tree) : bool :=
        isSome $ stree_lookup (λ st, decide $ is_tid tid $ st.data_of.1) tree.

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
        | SNode (ot, None) [] => decide (is_tid tid ot)
        | _ => false
        end.

      (* find the leaf node that represents tid *)
      Definition lookup_tid (tid: nat) (t: team_tree) : option tree_ref :=
        stree_lookup (is_leaf_tid tid) t.

      Definition spawn_team (tid: nat) (team_mates: list nat) (tree: team_tree) (cms : option contrib_maps): option team_tree :=
        (λ ref, ref.2 $ spawn_team' (ref.1.data_of.1) team_mates cms) <$> lookup_tid tid tree.

      (* a spawned team is done when all team members are TeamLeaf (so don't have a working team)
         and are done *)
      Definition is_team_done (tid: nat) (tree: team_tree) : Prop :=
        match tree with
        | SNode p ts => 
          Forall (λ t, match t with SNode (ot,_) kids => (* all team members must be leaf *)
                             ot.(o_done) = true ∧ kids = [] end) ts end.

      #[global] Instance is_team_done_decidable tid tree : Decision (is_team_done tid tree).
      Proof.
        move : tree => [ot ts].
        rewrite /is_team_done. apply Forall_dec => [[? ?]].
        tc_solve.
      Qed.
      
      (** assume tid is the primary thread of some team, turn that TeamNode to TeamLeaf,
          set pv to None (since reduction is finished)
       * Happens when all threads, including primary, are done in this team.
      *)
      Definition fire_team (tid: nat) (tree: team_tree) : option team_tree :=
        (λ ref, ref.2 $ SNode (ref.1.data_of.1, None) []) <$> lookup_tid tid tree.

      (* whether the root of the tree is the leader of tid.
         this requires that they are in the same team.  *)
      Definition is_leader_tree_of (tid: nat) (tree: team_tree) : Prop :=
        match tree with
        | SNode ot kids =>
           (In tid $ t_tid <$> team_info tree) end.
      
      #[global] Instance is_leader_tree_of_dec tid tree : Decision (is_leader_tree_of tid tree).
      Proof.
        move : tree => [ot ts].
        rewrite /is_leader_tree_of.
        apply In_dec => [? ?]. apply Nat.eq_dec.
      Qed.

      Definition leader_tree_of (tid: nat) (tree: team_tree) : option tree_ref :=
        stree_lookup (λ st, decide $ is_leader_tree_of tid st) tree.

      Lemma has_leader_or_no_kid (tid: nat) (tree: team_tree) :
        has_tid tid tree ->
        tree.kids_of <> [] ->
        ∃ leader_tree,  leader_tree_of tid tree = Some leader_tree.
      Proof. Admitted.

      Definition set_tid_done (tid: nat) (tree: team_tree) : option team_tree :=
        ref ← lookup_tid tid tree;
        let '(ot, pv) := ref.1.data_of in
        let kids := ref.1.kids_of in
        Some (ref.2 $ SNode (ot <|o_done := true|>, pv) kids).

    End OpenMPTeam.
    
End OpenMPThreads.