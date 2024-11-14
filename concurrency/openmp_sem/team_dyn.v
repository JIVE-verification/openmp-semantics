From stdpp Require Import list.
From mathcomp.ssreflect Require Import ssreflect ssrbool ssrfun.
Import ListNotations.
Section OpenMPThreads.
    
    (* OpenMP thread info *)
    Record ot_info := {
      t_tid : nat; (* thread id *)
      o_team_id : nat; (* each of new team should get a different number *)
      (* o_tid : nat; thread id in the current team, NOT tid *)
      (* o_level : nat; nesting level *)
      o_done : bool (* if it is spawned by some primary thread, set to true when 
                     it has reached the last barrier *)
    }.

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

      (* model of the dynamics of a team. Only the leaf threads are executing, the parents are for bookkeeping. *)
      Inductive team_tree :=
      | TeamLeaf : ot_info -> team_tree
      (* parent thread and the including itself *)
      | TeamNode : ot_info -> (* parent thread *)
                   list team_tree -> (* the team that it spawns, 
                                        first thread is same as parent thread but o_tid=0 *)
                   team_tree.

      (* the first thread in the program *)
      Definition ot_init (tid: nat) := Build_ot_info tid 0 false.

      (* a team starts with just the main thread *)
      Definition team_init (tid: nat) := TeamLeaf (ot_init tid).

      (* ot creates a new team with the other team_mates *)
      Definition spawn_team' (ot: ot_info) (team_mates: list nat) : team_tree :=
        TeamNode ot $ (λ tid, TeamLeaf (Build_ot_info tid 0 false)) <$> (cons (ot.(t_tid)) team_mates).

      Definition is_tid (tid: nat) (ot: ot_info) :=
        ot.(t_tid) = tid.
      #[global] Instance is_tid_dec (tid: nat) (ot: ot_info) : Decision (is_tid tid ot).
      Proof. apply Nat.eq_dec. Qed.

      (* the list of all leaf threads *)
      Fixpoint tree_to_list (tree: team_tree) : (list ot_info) :=
        match tree with
        | TeamLeaf ot => nil
        | TeamNode ot ts => concat (map tree_to_list ts)
        end.

      Definition has_tid (tid: nat) (tree: team_tree) : Prop :=
        In tid $ map t_tid $ tree_to_list tree.

      Definition get_ot (tid: nat) (tree: team_tree) : option ot_info :=
        find (λ ot, decide (ot.(t_tid) = tid)) $ tree_to_list tree.

      Definition tid_unique (tree: team_tree) : Prop :=
        NoDup $ map t_tid $ tree_to_list tree.

      (* `tree` and `tids` contain the same tid, where `tids` is the  *)
      Definition matching_tids (tree: team_tree) (tids: list nat) : Prop :=
        ∀ tid, In tid tids ↔ has_tid tid tree.

      Class team_tree_inv (tree: team_tree) : Prop :=
        { inv_tid_unique    : tid_unique tree;
          inv_matching_tids : matching_tids tree (map t_tid $ tree_to_list tree) }.

      (** folloing opeartions assume that tids in the trees are NoDup, and the indexing tid exists as a leaf
           node in the tree. *)
      (** spawns a team at every TeamLeaf that contains tid.
       * should require that tid is unique in tree.
       *)
      Fixpoint spawn_team (tid: nat) (team_mates: list nat) (tree: team_tree): team_tree :=
        match tree with
        | TeamLeaf ot => if decide $ is_tid tid ot then spawn_team' ot team_mates else tree
        | TeamNode p ts => TeamNode p $ map (spawn_team tid team_mates) ts
        end.

      (* a spawned team is done when all team members are TeamLeaf (so don't have a working team)
         and are done *)
      Definition is_team_done (tid: nat) (tree: team_tree) : Prop :=
        ∃ p ts,
          tree = TeamNode p ts ∧ 
          Forall (λ t, ∃ ot, t=TeamLeaf ot ∧ (* all team members must be leaf *)
                             ot.(o_done) = true) ts.

      (** assume tid is the primary thread of some team, turn that TeamNode to TeamLeaf.
       * Happens when all threads, including primary, are done in this team.
      *)
      Fixpoint fire_team (tid: nat) (tree: team_tree) : team_tree :=
        match tree with
        | TeamLeaf _ => tree
        | TeamNode p ts => if decide $ is_tid tid p then TeamLeaf p else TeamNode p $ map (fire_team tid) ts
        end.

      Fixpoint team_tids' (trees: list team_tree) : list nat :=
        match trees with
        | TeamLeaf ot :: trees' => ot.(t_tid) :: team_tids' trees'
        | TeamNode ot _ :: trees' => ot.(t_tid) :: team_tids' trees'
        | nil => nil
        end.

      (* get all the tids of the team that is at the shallowest level of tree  *)
      Definition team_tids (tree: team_tree) : option $ list nat :=
        match tree with
        | TeamLeaf _ => None
        | TeamNode ot ts => Some $ team_tids' ts
        end.

      (* tid is in the (shallowest) team represented by tree *)
      Definition in_team (tid: nat) (tree: team_tree) : Prop :=
        ∃ tids, team_tids tree = Some tids ∧ In tid tids.


      Fixpoint measure_tree (tree: team_tree) : nat :=
        match tree with
        | TeamLeaf _ => 1
        | TeamNode _ ts => 1 + list_sum (map measure_tree ts)
        end.

Require Import Coq.Program.Wf.

      (* FIXME this is so cursed *)
      (* the team that contains tid *)
       Definition is_subtree_aux (subtree: team_tree) (tree: team_tree) : Prop :=
        subtree = tree ∨
        ∃ ot ts, tree = TeamNode ot ts ∧
        In subtree ts.
      
      (* transitive closure of is_subtree_aux *)
      Definition is_subtree (subtree: team_tree) (tree: team_tree) : Prop :=
        is_subtree_aux subtree tree ∨ ∃ sub', is_subtree_aux subtree sub' ∧ is_subtree_aux sub' tree.

      (* find the leader's tid for input tid *)
      Definition leader_tid (tid: nat) (tree: team_tree) (leader_tid: nat) : Prop :=
        ∃ subtree ot_leader ts,
          is_subtree subtree tree ∧
          subtree = TeamNode ot_leader ts ∧
          is_tid leader_tid ot_leader ∧
          in_team tid subtree.

      (* TODO make a tree_map? *)
      (* set the tid to be done in its current parallel scope;
         i.e. only the ot_info in the TeamLeaf that contains tid *)
      Fixpoint set_tid_done (tid: nat) (tree: team_tree) : team_tree :=
        match tree with
        | TeamLeaf ot => 
          if decide (is_tid tid ot)
          then TeamLeaf $ Build_ot_info ot.(t_tid) ot.(o_team_id) true 
          else TeamLeaf ot
        | TeamNode ot ts => TeamNode ot $ map (set_tid_done tid) ts
        end.

    End OpenMPTeam.

End OpenMPThreads.