From mathcomp.ssreflect Require Import ssreflect ssrbool.
Require Import Coq.Program.Wf FunInd Recdef.
From compcert Require Import Values Clight Memory Ctypes AST Globalenvs.
From VST.concurrency.openmp_sem Require Import reduction notations for_construct clight_fun.
From stdpp Require Import base list.
From RecordUpdate Require Import RecordSet.
Import RecordSetNotations.
From Coq Require Import Nat.
From Equations Require Import Equations.
(* Section ListCursor.
  Inductive list_zipper {A:Type} : Type :=
  | ListZip (content: A) (before after: list A) : list_zipper.

End ListCursor. *)

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
  (* Fixpoint fold_tree_p {A: Type} (st: stree) (f: option B -> B -> A -> A) (accu: A) (parent: option B) : A :=
    match st with | SNode b kids =>
    let accu' := f parent b accu in
       foldr (λ st accu, fold_tree_p st f accu $ Some b) accu' kids
    end. *)

  Fixpoint fold_stree {A: Type} (f: B -> A -> A) (s: stree) (base: A) :=
    f (data s) (foldr (fold_stree f) base (kids s)).
  
  Fixpoint stree_measure s :=
    1 + (foldr add 0 $ (stree_measure <$> kids s)).

  Lemma stree_measure_pos s : stree_measure s > 0.
    rewrite /stree_measure /=.
    induction s. destruct l; simpl; lia.
  Qed.

End SiblingTree.

Notation " x '.data' " := (data x) (at level 3).
Notation " x '.kids' " := (kids x) (at level 3).

Section SiblingTreeZipper.
  Context {B:Type}.

  Notation stree := (@stree B).
  Definition sforest := list stree.

  (* from haskell tree zipper `tree_pos`, 
    https://hackage.haskell.org/package/rosezipper-0.2/docs/src/Data-Tree-Zipper.html*)
  Inductive tree_zipper : Type :=
  (* this : the focused stree
    before : the list of siblings to the left, in reverse order
     after : the list of siblings to the right (in normal order)
    parents : each item in the list is the parent node and its left and right siblings.

            []        parents[n].2     []
                       ...
    parents[1].1   parents[1].2      parents[1].3
                  /    |         \
                /      |          \
    parents[0].1   parents[0].2    parents[0].3
                  /    |    \
            before   this    after
    *)
  | TreeZip (this: stree) (before after: sforest) (parents: list (sforest * B * sforest))
  .

  Implicit Type (tz: tree_zipper).

  Definition this_of tz : stree :=
    match tz with
    | TreeZip this _ _ _ => this
    end.

  Definition before_of tz : sforest :=
    match tz with
    | TreeZip _ before _ _ => before end.

  Definition after_of tz : sforest :=
    match tz with
    | TreeZip _ _ after _ => after
    end.

  Definition parents_of tz : list (sforest * B * sforest) :=
    match tz with
    | TreeZip _ _ _ parents => parents
    end.

  #[export] Instance tree_zipper_settable : Settable tree_zipper := settable! TreeZip < this_of; before_of; after_of; parents_of >.

  (* all siblings and itself *)
  Definition forest_of tz : sforest :=
    (rev (before_of tz)) ++ [this_of tz] ++ after_of tz.

  Definition go_left tz : option tree_zipper :=
    match tz with
    | TreeZip this (h::b) a p =>
      Some (TreeZip h b (this::a) p)
    | _ => None
    end.

  Definition go_right tz : option tree_zipper :=
    match tz with
    | TreeZip this b (h::a) p =>
      Some (TreeZip h (this::b) a p)
    | _ => None
    end.

  (* go to the parent *)
  Definition go_up tz : option tree_zipper :=
    match tz with
    | TreeZip this b a ((l, p, r)::ps) =>
      Some (TreeZip (SNode p $ forest_of tz) l r ps)
    | _ => None
    end.

  (* go to the left most child *)
  Definition go_down tz : option tree_zipper :=
    match tz with
    | TreeZip (SNode d (k::ks)) b a ps =>
      Some (TreeZip k [] ks ((b, d, a)::ps))
    | _ => None
    end.

  Lemma left_right_idem:
    ∀ tz tz'',
      (tz' ← go_left tz; go_right tz') = Some tz''
      -> tz = tz''.
  Proof.
    intros. destruct tz. destruct before; first done.
    unfold_mbind_in_hyp. inv H. done.
  Qed.
  
  Lemma right_left_idem:
    ∀ tz tz'',
      (tz' ← go_right tz; go_left tz') = Some tz''
      -> tz = tz''.
  Proof.
    intros. destruct tz. destruct after; first done.
    unfold_mbind_in_hyp. inv H. done.
  Qed.

  Definition tree_pos_iter tz : option tree_zipper :=
    match go_right tz with
    | Some tz' => Some tz'
    | None =>
      match go_down tz with
      | Some tz' => Some tz'
      | None => None
      end
    end.

  (* measured in size of right siblings and children *)
  Definition tree_pos_measure tz : nat :=
    match tz with
    | TreeZip this _ a _ => stree_measure this + foldr add 0 (stree_measure <$> a)
    end.

  Lemma tree_pos_iter_wf tz tz':
    tree_pos_iter tz = Some tz'
    → tree_pos_measure tz' < tree_pos_measure tz.
  Proof.
    intros H.
    rewrite /tree_pos_iter in H.
    destruct_match.
    { rewrite /go_right in Heqo.
      destruct tz => //. destruct after  => //. inv Heqo.
      rewrite /tree_pos_measure /fmap /= -/fmap.
      assert (stree_measure this > 0) by apply stree_measure_pos.
      lia. }
    destruct_match.
    rewrite /go_down in Heqo0.
    destruct_match.
    destruct_match.
    destruct_match.
    inv Heqo0.
    rewrite /tree_pos_measure.
    rewrite  /stree_measure /= -/stree_measure /fmap. lia.
  Defined.

  (* the equation for the case when we go down *)
  Definition tree_zipper_iter_rel : relation tree_zipper.
  Proof. rewrite /relation. intros tz tz'. 
    refine (tree_pos_iter tz' = Some tz). Defined.

  #[export] Instance tree_zipper_iter_wf : WellFounded tree_zipper_iter_rel.
  Proof. rewrite /WellFounded.  eapply (well_founded_lt_compat _  (tree_pos_measure)).
    intros. apply tree_pos_iter_wf. rewrite H //. Defined.

  (* not used for now *)
  Section TreeZipperIter.
    
    Program Fixpoint fold_tree_zipper' {A: Type} tz (f: tree_zipper -> A -> A) (base: A) {measure (tree_pos_measure tz) } : A :=
      let rest:A :=
        match tree_pos_iter tz with
        | Some tz' => fold_tree_zipper' tz' f base
        | None => base
        end in
      f tz rest
      .
    Next Obligation. intros. by apply tree_pos_iter_wf. Defined.
    Next Obligation. apply measure_wf. apply lt_wf. Defined.

    Equations fold_tree_zipper {A: Type} tz (f: tree_zipper -> A -> A) (base: A) : A by wf tz tree_zipper_iter_rel :=
      (* go right if possible *)
      fold_tree_zipper (TreeZip this b (h::a) p) f base :=
        let tz := (TreeZip this b (h::a) p) in
          f tz (fold_tree_zipper (TreeZip h (this::b) a p) f base);
      fold_tree_zipper (TreeZip (SNode d (h::kids)) b [] p) f base :=
        let tz := (TreeZip (SNode d (h::kids)) b [] p) in
          f tz (fold_tree_zipper (TreeZip h [] kids ((b,d,[])::p)) f base);
      fold_tree_zipper tz f base := base.
    Next Obligation. rewrite /tree_zipper_iter_rel. rewrite /tree_pos_iter //. Defined.
    Next Obligation. rewrite /tree_zipper_iter_rel. rewrite /tree_pos_iter //. Defined.
  End TreeZipperIter.

  (* TODO maybe rewrite stree_lookup with fold_tree_zipper *)
  Program Fixpoint stree_lookup (f: tree_zipper -> bool) tz {measure (tree_pos_measure tz)} : option tree_zipper :=
  if f tz then Some tz else
  let right_res :=
      match go_right tz with
    | Some tz_r => stree_lookup f tz_r
    | None => None 
    end in
  match right_res with
  | Some res => Some res
  | None => 
    match go_down tz with
    | Some tz_d => stree_lookup f tz_d
    | None => None
    end
  end.
  Next Obligation. destruct tz. destruct after; try done. inv Heq_anonymous.
    simpl. rewrite /fmap. destruct this; simpl. lia. Defined.
  Next Obligation. destruct tz. destruct this. destruct l; try done. inv Heq_anonymous.
    simpl. rewrite /fmap. lia. Defined.
  Next Obligation. apply measure_wf. apply lt_wf. Defined.

  (* go_up is well-founded *)
  Definition tree_pos_measure_up tz : nat :=
    match tz with
    | TreeZip _ _ _ p => length p 
    end.

  Lemma go_up_wf tz tz':
    go_up tz = Some tz'
    → tree_pos_measure_up tz' < tree_pos_measure_up tz.
  Proof.
    intros H.
    rewrite /go_up in H.
    destruct tz => //.
    destruct parents; first done.
    repeat destruct_match. inv H. simpl. lia.
  Defined.

  (* Using Equations would generate the rewrite lemmas automatically,
     but the definition would be a bit hard to read (it has to be defined on patterns of tz) and may not compute. *)
  Program Fixpoint root tz {measure (tree_pos_measure_up tz)}: tree_zipper :=
    match go_up tz with
    | Some tz' => root tz'
    | None => tz
    end.
  Next Obligation. apply go_up_wf. rewrite Heq_anonymous //. Defined.
  Next Obligation. apply measure_wf. apply lt_wf. Defined.

  Lemma root_eq_1 this b a l d r p :
    root $ TreeZip this b a ((l,d,r)::p) = root $ TreeZip (SNode d ((rev b)++[this]++a)) l r p.
  Proof.
    rewrite /root.
    rewrite WfExtensionality.fix_sub_eq_ext /=.
    rewrite /forest_of //.
  Qed.

 Lemma root_eq_2 tz : 
     (go_up tz = None) → root tz = tz.
  Proof. intros. rewrite /root.
    rewrite WfExtensionality.fix_sub_eq_ext /= H //.
  Qed.

  Definition to_stree (tz: tree_zipper) : option stree :=
    match (root tz) with
    | TreeZip this [] [] _ => Some this
    | _ => None
    end.

  Lemma go_right_same_tree (tz tz': tree_zipper) :
    go_right tz = Some tz' → to_stree tz = to_stree tz'.
  Proof.
    intros H.
    induction tz. destruct after; first done.
    rewrite /root.
    inv H. 
    destruct parents; rewrite /to_stree.
    - rewrite !root_eq_2 //. destruct before; done.
    - destruct p as [[? ?] ?]. rewrite !root_eq_1 //.
      rewrite app_assoc //.
  Qed.

  Lemma stree_lookup_correct (is_target: tree_zipper -> bool)  (tz tz': tree_zipper):
    stree_lookup is_target tz = Some tz' →
    is_target tz' = true ∧ to_stree tz = to_stree tz'.
  Admitted.

  (* lookup with is_target, if found, update the data of the subtree root to b' *)
  Definition stree_update (is_target: tree_zipper -> bool) (f: stree -> option stree) (tz: tree_zipper) : option tree_zipper :=
    tz' ← stree_lookup is_target tz;
    cur ← f (this_of tz');
    Some (tz' <| this_of := cur |>).

End SiblingTreeZipper.

Section TreeZipperTests.
  Example test_stree_lookup :
    stree_lookup (λ x, data $ this_of x =? 3) 
      (TreeZip (SNode 0 []) [] [(SNode 1 []);(SNode 2 [SNode 3 []])] []) = Some (TreeZip (SNode 3 []) [] [] [([SNode 1 []; SNode 0 []], 2, [])]).
  Proof.
    cbv. done.
  Qed.
End TreeZipperTests.

Notation " x '.this' " := (this_of x) (at level 3).
Notation " x '.before' " := (before_of x) (at level 3).
Notation " x '.after' " := (after_of x) (at level 3).
Notation " x '.parents' " := (parents_of x) (at level 3).
Notation " x '.forest' " := (forest_of x) (at level 3).

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
        isSome $ stree_lookup (λ st, decide $ is_tid tid $ st.this.data) tree.

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