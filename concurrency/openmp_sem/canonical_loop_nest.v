From compcert Require Import Clight Cop Ctypes Ctypesdefs.
From compcert Require Import -(notations) lib.Maps.
From VST.concurrency.openmp_sem Require Import notations.
From RecordUpdate Require Import RecordSet.
Import RecordSetNotations.

From stdpp Require Import base list.

Section LoopNest.

    Definition integer_expr (e: expr) :=
    match typeof e with
    | Tint _ _ _ => True
    | _ => False
    end.

    Definition pointer_expr (e: expr) :=
    match typeof e with
    | Tpointer _ _ => True
    | _ => False
    end.

    (* an expr that gives the result of loading the loop variable.
        p.199,23 var holds either an integer type or a pointer *)
    Inductive Var :=
    | VarInt (var: expr) : (* integer_expr var  -> *) Var
    (* | VarPtr (var: expr) : pointer_expr var -> Var *)
    .
    
    Definition get_var_expr (var: Var) :=
    match var with
    | VarInt e => e
    (* | VarPtr e _ => e *)
    end.
 
(** standard p.67 loop-nest-associated directive:
 *  An executable directive for which the associated user code must be a canonical loop nest. 
 *)

(* p.200, 4
   lb:
   Expressions of a type compatible with the type of var that are loop invariant with 
   respect to the outermost loop.
   (or: stuff related to var-outer, for nested loops. Not supported at the moment) *)

    (* p.198, 24 init-expr
       initialization is a statement in clight instead of expr  *)
    Variant InitStmt :=
    | InitStmtCons (var_id: AST.ident) (lb: expr) (* var_id = lb *).
    (* TODO support new var initialization stmt: type var_id = lb *)
    
    Definition make_init_stmt (s:statement) : option InitStmt :=
    match s with
    | Sset i lb_expr => Some (InitStmtCons i lb_expr)
    | _ => None
    end.

    Definition elaborate_init_stmt (init_stmt: InitStmt) :=
    match init_stmt with
    | InitStmtCons var_id lb =>
        Sset var_id lb
    end.

    (* p.199, 5 relational_op *)
    Variant relational_op :=
    | ROP_lt
    | ROP_le
    | ROP_gt
    | ROP_ge
    | ROP_ne.

    Definition elaborate_relational_op (rop: relational_op) :=
    match rop with
    | ROP_lt => Olt
    | ROP_le => Ole
    | ROP_gt => Ogt
    | ROP_ge => Oge
    | ROP_ne => One
    end.

    Record Incr :=
    {
       e:expr;
       Hinteger_expr: integer_expr e
    }.

    (* incr-expr, p199, 2
       incr: p.201, 1 Integer expressions that are loop invariant with respect to the outermost
             loop of the loop nest.
        *)
    Variant IncrExpr :=
    (*
    these four cases are desugared into the rest cases; a=a+1 etc
    | IncrOneVar : AST.ident -> incr_expr (* ++var *)
    | VarIncrOne : AST.ident -> incr_expr (* var++ *)
    | DecrOneVar : AST.ident -> incr_expr (* --var *)
    | VarDecrOne : AST.ident -> incr_expr (* var-- *) *)
    | VarPlusEqIncr   (var : expr) (incr: Incr) (* var += incr *)
    | VarMinusEqIncr  (var : expr) (incr: Incr) (* var -= incr *)
    | VarPlusIncr     (var : expr) (incr: Incr) (* var = var + incr *)
    | IncrPlusVar     (var : expr) (incr: Incr) (* var = incr + var *)
    | VarMinusIncr    (var : expr) (incr: Incr) (* var = var - incr *)
    .

    Definition elaborate_incr_expr  (incr_expr: IncrExpr) :=
    match incr_expr with
    | VarPlusEqIncr  var incr => Ebinop Oadd var incr.(e) (typeof var)
    | VarMinusEqIncr var incr => Ebinop Osub var incr.(e) (typeof var)
    | VarPlusIncr    var incr => Ebinop Oadd var incr.(e) (typeof var)
    | IncrPlusVar    var incr => Ebinop Oadd incr.(e) var (typeof var)
    | VarMinusIncr   var incr => Ebinop Osub var incr.(e) (typeof var)
    end.
    

    (* p199,2 test-expr *)
    Inductive TestExpr :=
    | TestExpr1 (var:Var) (rel_op:relational_op) (ub: expr)
    | TestExpr2 (var:Var) (rel_op:relational_op) (ub: expr)
    .


    Definition elaborate_test_expr (test_expr: TestExpr) :=
        match test_expr with
        | TestExpr1 var rel_op ub =>
            let var_expr := get_var_expr var in
            Ebinop (elaborate_relational_op rel_op) var_expr ub (typeof var_expr)
        | TestExpr2 var rel_op ub =>
            let var_expr := get_var_expr var in
            Ebinop (elaborate_relational_op rel_op) var_expr ub (typeof var_expr)
        end.

    Inductive CanonicalLoopNest :=
    | CanonicalLoopNestCons (init_stmt: InitStmt)  (test_expr: TestExpr) (incr_expr: IncrExpr) (loop_body: statement). 

    Definition elaborate_canonical_loop_nest (canonical_loop_nest: CanonicalLoopNest) : statement :=
    match canonical_loop_nest with
    | CanonicalLoopNestCons init_stmt test_expr incr_expr loop_body =>
        match init_stmt with
        | InitStmtCons var_id _ =>
        Sfor
            (elaborate_init_stmt init_stmt)
            (elaborate_test_expr test_expr)
            (Sset var_id (elaborate_incr_expr incr_expr))
            loop_body
        end
    end.

(* TODO what do we want to assume about loop_body?
   Can we have a simpler version of structured-blocks?
   maybe no breaks/continues to the outer part?  *)

   Definition _in : AST.ident := __max.
   Definition _out : AST.ident := __max.
   Definition _t'1 : AST.ident := __max.

   (*
    for (int i=0; i!=2; i++) {
        // short cuircuiting a loop
        if (i==0) {
            i=1;
        }
        count+=1;
    }
 *)

    Definition eg_loop : statement :=
    Ssequence
        (Sifthenelse (Ebinop Ogt (Etempvar _in tint) (Etempvar _out tint) tint)
        (Sset _t'1 (Ecast (Etempvar _in tint) tint))
        (Sset _t'1 (Ecast (Etempvar _out tint) tint)))
        (Sset _out (Etempvar _t'1 tint))
    .

   Definition make_canonical_loop_nest (s: statement) : option CanonicalLoopNest :=
   match s with
   | Ssequence s1 (Sloop (Ssequence (Sifthenelse e2 Sskip Sbreak) s3) s4) => None
   | _ => None
   end.

   Lemma eg_loop_is_canonical_loop_nest : ∃ cnl, make_canonical_loop_nest eg_loop = Some cnl.
   Proof. Admitted.

End LoopNest.