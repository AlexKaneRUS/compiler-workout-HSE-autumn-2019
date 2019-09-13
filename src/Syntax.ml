(* Opening a library for generic programming (https://github.com/dboulytchev/GT).
   The library provides "@type ..." syntax extension and plugins like show, etc.
*)
open GT 
    
(* Simple expressions: syntax and semantics *)
module Expr =
  struct
    
    (* The type for expressions. Note, in regular OCaml there is no "@type..." 
       notation, it came from GT. 
    *)
    @type t =
    (* integer constant *) | Const of int
    (* variable         *) | Var   of string
    (* binary operator  *) | Binop of string * t * t with show

    (* Available binary operators:
        !!                   --- disjunction
        &&                   --- conjunction
        ==, !=, <=, <, >=, > --- comparisons
        +, -                 --- addition, subtraction
        *, /, %              --- multiplication, division, reminder
    *)
                                                            
    (* State: a partial map from variables to integer values. *)
    type state = string -> int 

    (* Empty state: maps every variable into nothing. *)
    let empty = fun x -> failwith (Printf.sprintf "Undefined variable %s" x)

    (* Update: non-destructively "modifies" the state s by binding the variable x 
      to value v and returns the new state.
    *)
    let update x v s = fun y -> if x = y then v else s y
    
    let toInt x =
      match x with
      | true  -> 1
      | false -> 0
      
    let toBool x =
      match x with
      | 0 -> false
      | _ -> true

    (* Expression evaluator

          val eval : state -> t -> int
 
       Takes a state and an expression, and returns the value of the expression in 
       the given state.
    *)
    let rec eval st expr = 
      match expr with 
      | Const c          -> c
      | Var v            -> st v
      | Binop (op, l, r) -> 
        let (lEval, rEval) = (eval st l, eval st r) in
          match op with
          | "+"  -> lEval + rEval
          | "-"  -> lEval - rEval
          | "*"  -> lEval * rEval
          | "/"  -> lEval / rEval
          | "%"  -> lEval mod rEval
          | "<"  -> toInt (lEval < rEval)
          | "<=" -> toInt (lEval <= rEval)
          | ">"  -> toInt (lEval > rEval)
          | ">=" -> toInt (lEval >= rEval)
          | "==" -> toInt (lEval == rEval)
          | "!=" -> toInt (lEval <> rEval)
          | "&&" -> toInt (toBool lEval && toBool rEval)
          | "!!" -> toInt (toBool lEval || toBool rEval)
          | a    -> failwith ("Unknown binary operator: " ^ a)

  end
                    
(* Simple statements: syntax and sematics *)
module Stmt =
  struct

    (* The type for statements *)
    @type t =
    (* read into the variable           *) | Read   of string
    (* write the value of an expression *) | Write  of Expr.t
    (* assignment                       *) | Assign of string * Expr.t
    (* composition                      *) | Seq    of t * t with show

    (* The type of configuration: a state, an input stream, an output stream *)
    type config = Expr.state * int list * int list 

    (* Statement evaluator

          val eval : config -> t -> config

       Takes a configuration and a statement, and returns another configuration
    *)
    let rec eval config stmt = 
      match config with
      | (st, i, o) -> 
        (match stmt with 
         | Read x       -> 
           (match i with
            | []        -> failwith "No input to read from."
            | (y :: ys) -> (Expr.update x y st, ys, o))
         | Write e       -> (st, i, o @ [Expr.eval st e])
         | Assign (x, e) -> (Expr.update x (Expr.eval st e) st, i, o)
         | Seq (l, r)    -> eval (eval config l) r
        )
                                                         
  end

(* The top-level definitions *)

(* The top-level syntax category is statement *)
type t = Stmt.t    

(* Top-level evaluator

     eval : int list -> t -> int list

   Takes a program and its input stream, and returns the output stream
*)
let eval i p =
  let _, _, o = Stmt.eval (Expr.empty, i, []) p in o
