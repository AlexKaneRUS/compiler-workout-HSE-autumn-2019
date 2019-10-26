open GT       
open Language
       
(* The type for the stack machine instructions *)
@type insn =
(* binary operator                 *) | BINOP   of string
(* put a constant on the stack     *) | CONST   of int
(* put a string on the stack       *) | STRING  of string                      
(* load a variable to the stack    *) | LD      of string
(* store a variable from the stack *) | ST      of string
(* store in an array               *) | STA     of string * int
(* a label                         *) | LABEL   of string
(* unconditional jump              *) | JMP     of string
(* conditional jump                *) | CJMP    of string * string
(* begins procedure definition     *) | BEGIN   of string * string list * string list
(* end procedure definition        *) | END
(* calls a function/procedure      *) | CALL    of string * int * bool
(* returns from a function         *) | RET     of bool with show
                                                   
(* The type for the stack machine program *)
type prg = insn list
                            
(* The type for the stack machine configuration: control stack, stack and configuration from statement
   interpreter
*)
type config = (prg * State.t) list * Value.t list * Expr.config

(* Stack machine interpreter

     val eval : env -> config -> prg -> config

   Takes an environment, a configuration and a program, and returns a configuration as a result. The
   environment is used to locate a label to jump to (via method env#labeled <label_name>)
*)
let split n l =
  let rec unzip (taken, rest) = function
  | 0 -> (List.rev taken, rest)
  | n -> let h::tl = rest in unzip (h::taken, tl) (n-1)
  in
  unzip ([], l) n
        
let rec print_list = function 
[] -> ()
| e::l -> print_int e ; print_string " " ; print_list l

let rec print_list_insn = function 
[] -> ()
| e::l -> (GT.show(insn) e) ; print_string " " ; print_list_insn l
                                               
let rec eval env config prg = 
    (match prg with
     | []        -> config
     | (x :: xs) ->
       match config with
        | (cs, stack, ((st, i, o) as cfg)) ->
          (match x with
           | BINOP bo ->
             (match stack with
              | (r :: l :: ls) -> 
              eval env (cs, Value.of_int (Expr.to_func bo (Value.to_int l) (Value.to_int r)) :: ls, cfg) xs
              | _              -> failwith "SM: Can't calculate binop: too few values."
             )
           | CONST v  -> eval env (cs, Value.of_int v :: stack, cfg) xs
           | LD v -> eval env (cs, State.eval st v :: stack, cfg) xs
           | ST v ->
             (match stack with
              | (y :: ys) -> eval env (cs, ys, (State.update v y st, i, o)) xs
              | _         -> failwith "SM: No stack to store."
             )
           | LABEL l        -> eval env (cs, stack, cfg) xs
           | JMP l          -> eval env (cs, stack, cfg) (env#labeled l)
           | CJMP (jmp, l)  -> 
             (match stack with
              | (y :: ys) -> 
                if (Value.to_int y <> 0 && jmp = "nz" || Value.to_int y = 0 && jmp = "z")
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
             eval env (cs, fstack, (fstate, i, o)) xs
           | CALL (name, nargs, b)  -> 
             if Builtin.isBuiltin name
             then eval env (env#builtin config name nargs b) xs
             else eval env ((xs, st) :: cs, stack, cfg) (env#labeled name)
           | END  -> 
             (match cs with
              | []               -> config
              | ((p, st') :: cs) -> eval env (cs, stack, (State.leave st st', i, o)) p
             )
           | RET x ->
             (match cs with
              | []               -> config
              | ((p, st') :: cs) -> eval env (cs, stack, (State.leave st st', i, o)) p
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
  let (_, _, (_, _, o)) =
    eval
      (object
         method is_label l = M.mem l m
         method labeled l = M.find l m
         method builtin (cstack, stack, (st, i, o)) f n p =
           let f = match f.[0] with 'L' -> String.sub f 1 (String.length f - 1) | _ -> f in
           let args, stack' = split n stack in
           let (st, i, o, r) = Language.Builtin.eval (st, i, o, None) (List.rev args) f in
           let stack'' = if p then stack' else let Some r = r in r::stack' in
           Printf.printf "Builtin: %s\n";
           (cstack, stack'', (st, i, o))
       end
      )
      ([], [], (State.empty, i, []))
      p
  in
  o

(* Stack machine compiler

     val compile : Language.t -> prg

   Takes a program in the source language and returns an equivalent program for the
   stack machine
*)
class label_generator =
  object (self)
    val counter = 0

    method get_label = "label_" ^ string_of_int counter, {< counter = counter + 1 >}
  end

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
  | Stmt.Assign (x, _, e) -> expr e @ [ST x], label_generator
  | Stmt.Skip             -> [], label_generator
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
  (List.flatten (List.rev (List.map expr args))) @ [CALL (name, List.length args, true)], label_generator
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
