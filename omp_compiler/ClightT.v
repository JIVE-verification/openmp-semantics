From Coq Require Import String List ZArith.
From compcert Require Import Coqlib Integers Floats Values AST Ctypes Cop Csyntax Csyntaxdefs.
From compcert Require Import Clight SimplExpr .
Import Csyntaxdefs.CsyntaxNotations.
Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope csyntax_scope.
From stdpp Require Import base list.

(* assume existence of pthread function names *)
Definition __opaque_pthread_t : ident := $"_opaque_pthread_t".
Definition __opaque_pthread_attr_t : ident := $"_opaque_pthread_attr_t".

(** *

  We lift CLight stmt to stmtT to include extra info about variables in an OMP
  pragma, encoded in the pragma_info type.
  TODO These info are supposed to be computed by a parser; we make up these info
  for now. *)

(* shared vars, vars in the private cluse, vars in the reduction clause and
  local vars. *)
Record pragma_info : Type := mk_pragma_info {
  shared_vars : list (ident * type);
  private_vars : list (ident * type);
  reduction_vars : list (ident * type);
  local_vars: list (ident * type)
}.

Definition empty_pragma_info : pragma_info :=
  mk_pragma_info [] [] [] [].

(* private variables are those specified in the private clause plus those in the reduction  *)
Definition parallel_info_spec (par_info: pragma_info) vars: Prop :=
  match par_info with
  | mk_pragma_info ss ps rs _ => 
      ss ⊆ vars ∧ ps ⊆ vars ∧ rs ⊆ vars ∧
      list_disjoint ss ps ∧ list_disjoint ss rs ∧ list_disjoint ps rs
  end.
 
(* lifts analysis info to an AST tagged with info *)
Inductive statementT : Type :=
  | SskipT : statementT                   (**r do nothing *)
  | SassignT : expr -> expr -> statementT (**r assignment [lvalue = rvalue] *)
  | SsetT : ident -> expr -> statementT   (**r assignment [tempvar = rvalue] *)
  | ScallT: option ident -> expr -> list expr -> statementT (**r function call *)
  | SbuiltinT: option ident -> external_function -> typelist -> list expr -> statementT (**r builtin invocation *)
  | SsequenceT : statementT -> statementT -> statementT  (**r sequence *)
  | SifthenelseT : expr  -> statementT -> statementT -> statementT (**r conditional *)
  | SloopT: statementT -> statementT -> statementT (**r infinite loop *)
  | SbreakT : statementT                      (**r [break] statementT *)
  | ScontinueT : statementT                   (**r [continue] statementT *)
  | SreturnT : option expr -> statementT      (**r [return] statementT *)
  | SswitchT : expr -> labeled_statementsT -> statementT  (**r [switch] statementT *)
  | SlabelT : label -> statementT -> statementT
  | SgotoT : label -> statementT
  (* each Spragma in the program is indexed by a uniquely natural number *)
  | SpragmaT : pragma_info -> nat -> pragma_label -> statementT -> statementT

with labeled_statementsT : Type :=            (**r cases of a [switch] *)
  | LSnilT: labeled_statementsT
  | LSconsT: option Z -> statementT -> labeled_statementsT -> labeled_statementsT.
                      (**r [None] is [default], [Some x] is [case x] *)
              
Fixpoint erase_info (sT: statementT) : statement :=
  match sT with
  | SskipT => Sskip
  | SassignT l r => Sassign l r
  | SsetT id e => Sset id e
  | ScallT id e args => Scall id e args
  | SbuiltinT id ef tl args => Sbuiltin id ef tl args
  | SsequenceT s1 s2 => Ssequence (erase_info s1) (erase_info s2)
  | SifthenelseT e s1 s2 => Sifthenelse e (erase_info s1) (erase_info s2)
  | SloopT s1 s2 => Sloop (erase_info s1) (erase_info s2)
  | SbreakT => Sbreak
  | ScontinueT => Scontinue
  | SreturnT oe => Sreturn oe
  | SswitchT e ls => Sswitch e (erase_info_labeled_statements ls)
  | SlabelT l s => Slabel l (erase_info s)
  | SgotoT l => Sgoto l
  | SpragmaT _ n pl s => Spragma n pl (erase_info s)
  end
  with erase_info_labeled_statements (lsT: labeled_statementsT) : labeled_statements :=
  match lsT with
  | LSnilT => LSnil
  | LSconsT c s ls => LScons c (erase_info s) (erase_info_labeled_statements ls)
  end
  .

(* idea: instead of dealing with nested parallel regions, we only transform the deepestly
   nested parallel region (i.e. a parallel region that does not have a parallel region nested
   inside it). Then an ident in `Evar id _` in that region must be one of these:
   1. privatized variable, must be shared in the outer parallel region. 
   2. reduction variable, similar to 1
   3. local, declared in this parallel region
   4. otherwise, shared.  *)
Fixpoint stmt_to_stmtT (stmt: statement) : statementT :=
  match stmt with
  | Sskip => SskipT
  | Sassign l r => SassignT l r
  | Sset id e => SsetT id e
  | Scall id e args => ScallT id e args
  | Sbuiltin id ef tl args => SbuiltinT id ef tl args
  | Ssequence s1 s2 => SsequenceT (stmt_to_stmtT s1) (stmt_to_stmtT s2)
  | Sifthenelse e s1 s2 => SifthenelseT e (stmt_to_stmtT s1) (stmt_to_stmtT s2)
  | Sloop s1 s2 => SloopT (stmt_to_stmtT s1) (stmt_to_stmtT s2)
  | Sbreak => SbreakT
  | Scontinue => ScontinueT
  | Sreturn oe => SreturnT oe
  | Sswitch e ls => SswitchT e (labeled_statements_to_labeled_statementsT ls)
  | Slabel l s => SlabelT l (stmt_to_stmtT s)
  | Sgoto l => SgotoT l
  | Spragma n pl stmt' => SpragmaT empty_pragma_info n pl (stmt_to_stmtT stmt')
  end
with labeled_statements_to_labeled_statementsT (ls: labeled_statements) : labeled_statementsT :=
  match ls with
  | LSnil => LSnilT
  | LScons c s ls' => LSconsT c (stmt_to_stmtT s) (labeled_statements_to_labeled_statementsT ls')
  end.
Record functionT  : Type := makeFunctionT {
  fn_returnT: type;
  fn_callconvT: calling_convention;
  fn_paramsT: list (ident * type);
  fn_varsT: list (ident * type);
  fn_tempsT: list (ident * type);
  fn_bodyT: statementT
}.

Definition program := Ctypes.program functionT.

Fixpoint lower_stmt (s: statementT) : statement :=
  match s with
  | SsequenceT a b => Ssequence (lower_stmt a) (lower_stmt b)
  | SifthenelseT a b c => Sifthenelse a (lower_stmt b) (lower_stmt c)
  | SloopT a b => Sloop (lower_stmt a) (lower_stmt b)  
  | SlabelT a b => Slabel a (lower_stmt b)
  | SpragmaT a b c d => (lower_stmt d)
  | SassignT l r => Sassign l r
  | SsetT id e => Sset id e
  | ScallT id e args => Scall id e args
  | SbuiltinT id ef tl args => Sbuiltin id ef tl args
  | SbreakT => Sbreak
  | ScontinueT => Scontinue
  | SreturnT oe => Sreturn oe
  | SswitchT e ls => Sswitch e (lower_labeled_statements ls)
  | SgotoT l => Sgoto l
  | SskipT => Sskip
  end 
  with lower_labeled_statements (ls: labeled_statementsT) : labeled_statements :=
  match ls with
  | LSnilT => LSnil
  | LSconsT c s ls => LScons c (lower_stmt s) (lower_labeled_statements ls)
  end
.