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

Section OpenMPThreads.

    (* OpenMP thread info *)
    Record ot_info := {
      t_tid : nat; (* thread id *)
      (* o_level : nat; nesting level *)
      o_work_sharing : bool; (* is in work-sharing region; can only enter once *)
      (* work loads of the team that is this thread spawns, i.e. the children of this node.
         now chunk split is decided the first time a thread hits the for pragma; if need to
         allow more flexible scheduling, when thread i hits the for pragma, maybe only
         instantiate that thread's workload and quantify over the uninstantiated part
         [ team_workloads[i]=something ∧ ∃ rest workloads, s.t. the workloads are still
           consistent ] *)
      o_team_workloads : option $ list $ list chunk;
      (* Privatization and reduction data.
         Each list item is: the original le at the time of privatization
                            and the set of privatized variables.
         the orig_le is used for looking up addr of original copies
         of private vars, and at the end of a privatization scope, the thread's le
         is restored to orig_le. *)
      o_pr: list pv_map;
      (* a stack of reduction information of kids. First thread encountering a reduction adds a stack. *)
      o_red_stack: list red_vars
    }.

    #[export] Instance settable_ot_info : Settable _ :=
      settable! Build_ot_info <t_tid; o_work_sharing; o_team_workloads; o_pr; o_red_stack>.

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
      Definition team_tree := @stree (ot_info).

      Implicit Types (pvm : pv_map) (ot: ot_info) (tree: team_tree)
        (i: ident) (ge orig_ge: genv) (le orig_le: env)
        (ce:composite_env) (m: mem) (b:Values.block) (ty:type).

      (* the first thread in the program *)
      Definition ot_init (tid: nat) : ot_info := Build_ot_info tid false None [] [].

      (* a team starts with just the main thread *)
      Definition team_init (tid: nat) : team_tree := SNode (ot_init tid) [].

      Definition is_tid (tid: nat) (ot: ot_info) : Prop :=
        ot.(t_tid) = tid.
      #[global] Instance is_tid_dec (tid: nat) (ot: ot_info) : Decision (is_tid tid ot).
      Proof. apply Nat.eq_dec. Qed.

      (* the list of all leaf threads *)
      Fixpoint tree_to_list (tree: team_tree) : (list ot_info) :=
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
        
      (* ot_info of the (immediate) team led by root of tree; does not include subteams *)
      Definition team_info (tree: team_tree) : list ot_info :=
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

      (* returns a list of team trees that corresponds to the new team that the parallel construct spawns.
         First item in team_mates_tids should be the parent's tid, since the parent thread becomes the leader of the new team.  *)
      Definition spawn_team' (team_mates_tids: list nat) : option $ list team_tree :=
        foldr (λ tid tl,
                tl ← tl;
                let mate := SNode (Build_ot_info tid false None [] []) [] in
                Some $ mate::tl)
          (Some [])
          team_mates_tids.

      Definition spawn_team (tid: nat) (team_mates: list nat) (tree: team_tree) : option team_tree :=
        update_tid tid tree (λ leaf,
          mates ← spawn_team' (tid::team_mates);
          Some $ leaf <| kids := mates |>).

      (* t must be a leaf node for that thread. *)
      Definition team_pr_add_pvm (t: team_tree) pvm orig_le: team_tree :=
        t <| data; o_pr ::= cons pvm |>.

      (* start a new privatization&reduction scope.
         register pvm, original local env and reduction clauses for a thread.
         Assume ge is invariant during the scope.
         tree is the whole team tree. Start reduction scope for the parent thread;
        if parent haven't had reduction information registered, add that to parent's o_red_stack. *)
      Definition team_pr_start_tid (tree: team_tree) (tid: nat) pvm ge orig_le m (rcs: list reduction_clause_type) : option team_tree :=
        t ← update_tid tid tree (λ leaf, Some $ team_pr_add_pvm leaf pvm orig_le);
        (* if parent's reduction info stack size is less than the kid's reduction info (by 1), that means the
           kid is the first to encounter the reduction region and registers the info for parent node. *)
        pref ← parent_tree_of tid tree;
        ref ← lookup_tid tid tree;
        let red_stack_depth := length pref.1.data.(o_red_stack) in
        let o_pr_depth := length ref.1.data.(o_pr) in
        if red_stack_depth <? o_pr_depth then
          rvs ← init_rvs rcs ge orig_le m;
          Some $ of_tref $ pref  <| fst; data; o_red_stack ::= cons rvs |>
        else Some t
      .

      (* find tid's teammates' thread ids, including tid.
         If tid is root, return itself. *)
      Definition team_mates_tids tid tree: list nat :=
      match parent_tree_of tid tree with
      | None => [tid]
      | Some pref => map (λ kid, kid.data.(t_tid)) pref.1.kids
      end.

      (* End a privatization & reduction scope for a thread.
         t must be a leaf node for that thread.
         pop a stack in o_pr, deallocate privatized copies in le, restore local to orig_le. *)
      Definition team_pr_end (t: team_tree) ce m le: option (team_tree * env * mem) :=
        match t.data.(o_pr) with
        | [] => None
        | pvm::tl =>
          m' ← pvm_free_private pvm ce m le;
          le' ← pvm_restore_le pvm le;
          let t' := t <| data; o_pr := tl |> in
          Some (t', le', m')
        end
        .

      Definition team_pr_end_tid (tree: team_tree) (tid: nat) ce m le : option (team_tree * env * mem) :=
        ref ← lookup_tid tid tree;
        subtree'_le'_m' ← team_pr_end ref.1 ce m le;
        let '(subtree', le', m') := (subtree'_le'_m': (team_tree * env * mem)) in
        Some $ (ref.2 subtree', le', m').
      
      (** assume tid is the primary thread of some team, turn that TeamNode to TeamLeaf,
          set pv to None (since reduction is finished)
       * Happens when all threads, including primary, are done in this team.
      *)
      Definition fire_team (tid: nat) (tree: team_tree) : option team_tree :=
        update_tid tid tree (λ leaf, Some $ leaf <| kids := [] |>).

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

      (* rvs for a leaf tid is stored at its parent's node. *)
      Definition team_pop_rvs tid tree: option (team_tree * red_vars) :=
        ref ← parent_tree_of tid tree;
        match ref.1.data.(o_red_stack) with
        | [] => None
        | rvs::tl => Some (of_tref $ ref <| fst; data; o_red_stack := tl |>, rvs)
        end.

      (* tid is a leader of its current team if it's parent node has the same tid. *)
      Definition is_leader (tid: nat) (tree: team_tree) : bool :=
        match parent_tree_of tid tree with
        | None => true
        | Some pref => pref.1.data.(t_tid) =? tid
        end.

    End OpenMPTeam.
End OpenMPThreads.