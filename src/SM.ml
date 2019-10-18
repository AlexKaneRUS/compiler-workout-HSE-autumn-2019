open GT       
open Language

open Expr
       
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
(* conditional jump                *) | CJMP  of string * string
(* begins procedure definition     *) | BEGIN of string * string list * string list
(* end procedure definition        *) | END
(* calls a function/procedure      *) | CALL  of string * int * bool
(* returns from a function         *) | RET   of bool with show
                                                   
(* The type for the stack machine program *)                                                               
type prg = insn list
                            
(* The type for the stack machine configuration: control stack, stack and configuration from statement
   interpreter
 *)
type config = (prg * State.t) list * int list * Expr.config

(* Stack machine interpreter

     val eval : env -> config -> prg -> config

   Takes an environment, a configuration and a program, and returns a configuration as a result. The
   environment is used to locate a label to jump to (via method env#labeled <label_name>)
*)   
let rec print_list = function 
[] -> ()
| e::l -> print_int e ; print_string " " ; print_list l

let rec print_list_insn = function 
[] -> ()
| e::l -> (GT.show(insn) e) ; print_string " " ; print_list_insn l
                                               
let rec eval env (config : config) (prg : prg) : config = 
    (match prg with
     | []        -> config
     | (x :: xs) ->
       match config with
        | (cs, stack, ((st, i, o, ret) as cfg)) ->
          (match x with
           | BINOP bo ->
             (match stack with
              | (r :: l :: ls) -> 
              (* print_int l; print_string bo; print_int r; print_string "="; print_int (Expr.to_func bo l r); print_string "\n"; 
              print_string "stack "; print_list stack; print_string "\n"; *)
              eval env (cs, Expr.to_func bo l r :: ls, cfg) xs
              | _              -> failwith "SM: Can't calculate binop: too few values."
             )
           | CONST v  -> eval env (cs, v :: stack, cfg) xs
           | READ     -> 
             (match i with
              | (y :: ys) -> eval env (cs, y :: stack, (st, ys, o, ret)) xs
              | _         -> failwith "SM: No input to read."
             )
           | WRITE    ->
             (match stack with
              | (y :: ys) -> eval env (cs, ys, (st, i, o @ [y], ret)) xs
              | _         -> failwith "SM: No stack to output."
             )
           | LD v -> eval env (cs, State.eval st v :: stack, cfg) xs
           | ST v ->
             (match stack with
              | (y :: ys) -> eval env (cs, ys, (State.update v y st, i, o, ret)) xs
              | _         -> failwith "SM: No stack to store."
             )
           | LABEL l        -> eval env (cs, stack, cfg) xs
           | JMP l          -> eval env (cs, stack, cfg) (env#labeled l)
           | CJMP (jmp, l)  -> 
             (match stack with
              | (y :: ys) -> 
                if (y <> 0 && jmp = "nz" || y = 0 && jmp = "z")
                  then eval env (cs, ys, cfg) (env#labeled l)
                  else eval env (cs, ys, cfg) xs
              | _         -> failwith "SM: No stack to do conditional jump."
             )
           | BEGIN (_, args, locs)  -> 
             let rec addVal st al vl = 
             (match al, vl with
              | (x :: xs), (y :: ys) -> addVal (State.update x y st) xs ys
              | [], ys               -> (st, ys)
              | _, _                 -> failwith "SM: Wrong number of arguments for function call."
             ) in
             let fstate, fstack = addVal (State.enter st (args @ locs)) args stack in
             eval env (cs, fstack, (fstate, i, o, ret)) xs
           | CALL (name, i, b)  -> 
             eval env ((xs, st) :: cs, stack, cfg) (env#labeled name)
           | END  -> 
             (match cs with
              | []               -> config
              | ((p, st') :: cs) -> eval env (cs, stack, (State.leave st st', i, o, ret)) p
             )
           | RET x ->
             (match cs with
              | []               -> config
              | ((p, st') :: cs) -> eval env (cs, stack, (State.leave st st', i, o, ret)) p
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
  let (_, _, (_, _, o, _)) = eval (object method labeled l = M.find l m end) ([], [], (State.empty, i, [], None)) p in
  o

class label_generator =
  object (self)
    val counter = 0

    method get_label = "label_" ^ string_of_int counter, {< counter = counter + 1 >}
  end

(* Stack machine compiler
     val compile : Language.t -> prg
   Takes a program in the source language and returns an equivalent program for the
   stack machine
*)
let rec compile' label_generator =
  let rec expr = function
  | Expr.Var   x          -> [LD x]
  | Expr.Const n          -> [CONST n]
  | Expr.Binop (op, x, y) -> expr x @ expr y @ [BINOP op]
  | Expr.Call (name, args) -> 
  (List.flatten (List.rev (List.map expr args))) @ [CALL (name, 0, false)]
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
  | Stmt.Repeat (body, cond) -> 
  let body_l, new_gen = label_generator#get_label in
  let end_l, new_gen = new_gen#get_label in
  let body_comp, new_gen = compile' new_gen body in
  [LABEL body_l] @ body_comp @ expr cond @ [CJMP ("z", body_l)], new_gen
  | Call (name, args) -> 
  (List.flatten (List.rev (List.map expr args))) @ [CALL (name, 0, false)], label_generator
  | Return x -> 
    (match x with
     | None   -> [RET false], label_generator
     | Some x -> expr x @ [RET true], label_generator)
  
let rec compileDefinition label_generator = 
  function
  | (name, (args, locs, body)) -> let body, new_gen = compile' label_generator body in
                                  [LABEL name; BEGIN (name, args, locs)] @ body @ [END], new_gen
  
let compile t =
let (defs, t) = t in 
let res, new_gen = compile' (new label_generator) t in
let defs, new_gen = List.fold_left (fun (l, gen) y -> let l', new_gen = compileDefinition gen y in l @ l', new_gen) ([], new_gen) defs in
res @ [END] @ defs