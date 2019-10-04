open GT       
open Language
       
(* The type for the stack machine instructions *)
@type insn =
(* binary operator                 *) | BINOP of string
(* put a constant on the stack     *) | CONST of int                 
(* read to stack                   *) | READ
(* write from stack                *) | WRITE
(* load a variable to the stack    *) | LD    of string
(* store a variable from the stack *) | ST    of string
(* a label                         *) | LABEL of string
(* unconditional jump              *) | JMP   of string                                                                                                                
(* conditional jump                *) | CJMP  of string * string with show
                                                   
(* The type for the stack machine program *)                                                               
type prg = insn list

(* The type for the stack machine configuration: a stack and a configuration from statement
   interpreter
 *)
type config = int list * Stmt.config

(* Stack machine interpreter

     val eval : env -> config -> prg -> config

   Takes an environment, a configuration and a program, and returns a configuration as a result. The
   environment is used to locate a label to jump to (via method env#labeled <label_name>)
*)                         
let rec eval env (config : config) (prg : prg) : config = 
    (match prg with
     | []        -> config
     | (x :: xs) ->
       match config with
        | (stack, ((st, i, o) as cfg)) ->
          (match x with
           | BINOP bo ->
             (match stack with
              | (r :: l :: ls) -> eval env (Expr.eval st (Binop (bo, Const l, Const r)) :: ls, cfg) xs
              | _              -> failwith "SM: Can't calculate binop: too few values."
             )
           | CONST v  -> eval env (v :: stack, cfg) xs
           | READ     -> 
             (match i with
              | (y :: ys) -> eval env (y :: stack, (st, ys, o)) xs
              | _         -> failwith "SM: No input to read."
             )
           | WRITE    ->
             (match stack with
              | (y :: ys) -> eval env (ys, (st, i, o @ [y])) xs
              | _         -> failwith "SM: No stack to output."
             )
           | LD v -> eval env (st v :: stack, cfg) xs
           | ST v ->
             (match stack with
              | (y :: ys) -> eval env (ys, (Expr.update v y st, i, o)) xs
              | _         -> failwith "SM: No stack to store."
             )
           | LABEL l        -> eval env (stack, cfg) xs
           | JMP l          -> eval env (stack, cfg) (env#labeled l)
           | CJMP (jmp, l)  -> 
             (match stack with
              | (y :: ys) -> 
                if (y <> 0 && jmp = "nz" || y = 0 && jmp = "z")
                  then eval env (stack, cfg) (env#labeled l)
                  else eval env (stack, cfg) xs
              | _         -> failwith "SM: No stack to do conditional jump."
             )
          )
    )

(* Top-level evaluation

     val run : prg -> int list -> int list

   Takes a program, an input stream, and returns an output stream this program calculates
*)
let run p i =
  let module M = Map.Make (String) in
  let rec make_map m = function
  | []              -> m
  | (LABEL l) :: tl -> make_map (M.add l tl m) tl
  | _ :: tl         -> make_map m tl
  in
  let m = make_map M.empty p in
  let (_, (_, _, o)) = eval (object method labeled l = M.find l m end) ([], (Expr.empty, i, [])) p in o

class label_generator =
  object (self)
    val counter = 0

    method get_label = "label_" ^ string_of_int counter, {< counter = counter + 1 >}
  end

(* Stack machine compiler

     val compile : Language.Stmt.t -> prg

   Takes a program in the source language and returns an equivalent program for the
   stack machine
*)
let rec compile' label_generator =
  let rec expr = function
  | Expr.Var   x          -> [LD x]
  | Expr.Const n          -> [CONST n]
  | Expr.Binop (op, x, y) -> expr x @ expr y @ [BINOP op]
  in
  function
  | Stmt.Seq (s1, s2)  -> 
  let s1_comp, new_gen = compile' label_generator s1 in
  let s2_comp, new_gen = compile' new_gen s2 in
  s1_comp @ s2_comp, new_gen
  | Stmt.Read x        -> [READ; ST x], label_generator
  | Stmt.Write e       -> expr e @ [WRITE], label_generator
  | Stmt.Assign (x, e) -> expr e @ [ST x], label_generator
  | Stmt.Skip          -> [], label_generator
  | Stmt.If (cond, th, el) -> 
  let el_l, new_gen = label_generator#get_label in
  let end_l, new_gen = new_gen#get_label in
  let th_comp, new_gen = compile' new_gen th in
  let el_comp, new_gen = compile' new_gen el in
  expr cond @ [CJMP ("z", el_l)] @ th_comp @ [JMP end_l; LABEL el_l] @ el_comp @ [LABEL end_l], new_gen
  | Stmt.While (cond, body) -> 
  let cond_l, new_gen = label_generator#get_label in
  let end_l, new_gen = new_gen#get_label in
  let body_comp, new_gen = compile' new_gen body in
  [LABEL cond_l] @ expr cond @ [CJMP ("z", end_l)] @ body_comp @ [JMP cond_l; LABEL end_l], new_gen
  | Stmt.Until (body, cond) -> 
  let body_l, new_gen = label_generator#get_label in
  let end_l, new_gen = new_gen#get_label in
  let body_comp, new_gen = compile' new_gen body in
  [LABEL body_l] @ body_comp @ expr cond @ [CJMP ("z", body_l)], new_gen
  
let compile t = 
let res, _ = compile' (new label_generator) t in
res
