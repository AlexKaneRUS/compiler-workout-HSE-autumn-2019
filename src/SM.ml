open GT       
open Language
       
(* The type for the stack machine instructions *)
@type insn =
(* binary operator                 *) | BINOP of string
(* put a constant on the stack     *) | CONST of int                 
(* read to stack                   *) | READ
(* write from stack                *) | WRITE
(* load a variable to the stack    *) | LD    of string
(* store a variable from the stack *) | ST    of string with show

(* The type for the stack machine program *)                                                               
type prg = insn list

(* The type for the stack machine configuration: a stack and a configuration from statement
   interpreter
 *)
type config = int list * Stmt.config

(* Stack machine interpreter

     val eval : config -> prg -> config

   Takes a configuration and a program, and returns a configuration as a result
 *)                         
 let rec eval (config : config) (prg : prg) : config = 
   (match prg with
    | []        -> config
    | (x :: xs) ->
      eval (match config with
       | (stack, ((st, i, o) as cfg)) ->
         (match x with
          | BINOP bo ->
            (match stack with
             | (r :: l :: ls) -> (Expr.eval st (Binop (bo, Const l, Const r)) :: ls, cfg)
             | _              -> failwith "SM: Can't calculate binop: too few values."
            )
          | CONST v  -> (v :: stack, cfg)
          | READ     -> 
            (match i with
             | (y :: ys) -> (y :: stack, (st, ys, o))
             | _         -> failwith "SM: No input to read."
            )
          | WRITE    ->
            (match stack with
             | (y :: ys) -> (ys, (st, i, o @ [y]))
             | _         -> failwith "SM: No stack to output."
            )
          | LD v -> (st v :: stack, cfg)
          | ST v ->
            (match stack with
             | (y :: ys) -> (ys, (Expr.update v y st, i, o))
             | _         -> failwith "SM: No stack to store."
            )
         )
      ) xs
   )

(* Top-level evaluation

     val run : prg -> int list -> int list

   Takes a program, an input stream, and returns an output stream this program calculates
*)
let run p i = let (_, (_, _, o)) = eval ([], (Language.Expr.empty, i, [])) p in o

(* Stack machine compiler

     val compile : Language.Stmt.t -> prg

   Takes a program in the source language and returns an equivalent program for the
   stack machine
 *)
 let rec compileExpr (expr : Expr.t) : prg = 
   match expr with 
   | Const c          -> [CONST c]
   | Var v            -> [LD v]
   | Binop (op, l, r) -> compileExpr l @ compileExpr r @ [BINOP op]

 let rec compile (stmt : Stmt.t) : prg = 
   (match stmt with 
    | Read v        -> (READ :: [ST v])
    | Write e       -> compileExpr e @ [WRITE]
    | Assign (x, e) -> compileExpr e @ [ST x]
    | Seq (l, r)    -> compile l @ compile r
   )
