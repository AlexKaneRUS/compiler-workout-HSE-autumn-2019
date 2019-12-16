open GT
       
(* X86 codegeneration interface *)

(* The registers: *)
let regs = [|"%ebx"; "%ecx"; "%esi"; "%edi"; "%eax"; "%edx"; "%ebp"; "%esp"|]

(* We can not freely operate with all register; only 3 by now *)                    
let num_of_regs = Array.length regs - 5

(* We need to know the word size to calculate offsets correctly *)
let word_size = 4;;

(* We need to distinguish the following operand types: *)
@type opnd = 
| R of int     (* hard register                    *)
| S of int     (* a position on the hardware stack *)
| M of string  (* a named memory location          *)
| L of int     (* an immediate operand             *)
| LL of string
with show

(* For convenience we define the following synonyms for the registers: *)         
let ebx = R 0
let ecx = R 1
let esi = R 2
let edi = R 3
let eax = R 4
let edx = R 5
let ebp = R 6
let esp = R 7

(* Now x86 instruction (we do not need all of them): *)
type instr =
(* copies a value from the first to the second operand  *) | Mov   of opnd * opnd
(* makes a binary operation; note, the first operand    *) | Binop of string * opnd * opnd
(* designates x86 operator, not the source language one *)
(* x86 integer division, see instruction set reference  *) | IDiv  of opnd
(* see instruction set reference                        *) | Cltd
(* sets a value from flags; the first operand is the    *) | Set   of string * string
(* suffix, which determines the value being set, the    *)                     
(* the second --- (sub)register name                    *)
(* pushes the operand on the hardware stack             *) | Push  of opnd
(* pops from the hardware stack to the operand          *) | Pop   of opnd
(* call a function by a name                            *) | Call  of string
(* returns from a function                              *) | Ret
(* a label in the code                                  *) | Label of string
(* a conditional jump                                   *) | CJmp  of string * string
(* a non-conditional jump                               *) | Jmp   of string
(* directive                                            *) | Meta  of string

(* arithmetic correction: decrement                     *) | Dec   of opnd
(* arithmetic correction: or 0x0001                     *) | Or1   of opnd
(* arithmetic correction: shl 1                         *) | Sal1  of opnd
(* arithmetic correction: shr 1                         *) | Sar1  of opnd
                                                                                                                                   
(* Instruction printer *)
let show instr =
  let binop = function
  | "+"   -> "addl"
  | "-"   -> "subl"
  | "*"   -> "imull"
  | "&&"  -> "andl"
  | "!!"  -> "orl" 
  | "^"   -> "xorl"
  | "cmp" -> "cmpl"
  | _     -> failwith "unknown binary operator"
  in
  let opnd = function
  | R i -> regs.(i)
  | S i -> if i >= 0
           then Printf.sprintf "-%d(%%ebp)" ((i+1) * word_size)
           else Printf.sprintf "%d(%%ebp)"  (8+(-i-1) * word_size)
  | M x -> x
  | L i -> Printf.sprintf "$%d" i
  | LL s -> "$" ^ s
  in
  match instr with
  | Cltd               -> "\tcltd"
  | Set   (suf, s)     -> Printf.sprintf "\tset%s\t%s"     suf s
  | IDiv   s1          -> Printf.sprintf "\tidivl\t%s"     (opnd s1)
  | Binop (op, s1, s2) -> Printf.sprintf "\t%s\t%s,\t%s"   (binop op) (opnd s1) (opnd s2)
  | Mov   (s1, s2)     -> Printf.sprintf "\tmovl\t%s,\t%s" (opnd s1) (opnd s2)
  | Push   s           -> Printf.sprintf "\tpushl\t%s"     (opnd s)
  | Pop    s           -> Printf.sprintf "\tpopl\t%s"      (opnd s)
  | Ret                -> "\tret"
  | Call   p           -> Printf.sprintf "\tcall\t%s" p
  | Label  l           -> Printf.sprintf "%s:\n" l
  | Jmp    l           -> Printf.sprintf "\tjmp\t%s" l
  | CJmp  (s , l)      -> Printf.sprintf "\tj%s\t%s" s l
  | Meta   s           -> Printf.sprintf "%s\n" s
  | Dec    s           -> Printf.sprintf "\tdecl\t%s" (opnd s)
  | Or1    s           -> Printf.sprintf "\torl\t$0x0001,\t%s" (opnd s)
  | Sal1   s           -> Printf.sprintf "\tsall\t%s" (opnd s)
  | Sar1   s           -> Printf.sprintf "\tsarl\t%s" (opnd s)
                                         
(* Opening stack machine to use instructions without fully qualified names *)
open SM

(* Symbolic stack machine evaluator

     compile : env -> prg -> env * instr list

   Take an environment, a stack machine program, and returns a pair --- the updated environment and the list
   of x86 instructions
*)
let compileSimple x env = function
| (lOp, rOp) -> 
  let op, env = env#allocate in
  env, [Mov (lOp, eax); Binop (x, rOp, eax); Mov (eax, op)]
  
let showReg (R i) = regs.(i)
      
let compileComparison x env = function
| (lOp, rOp) ->
  let op, env = env#allocate in
  let suf = (match x with
  | "<" -> "l"
  | "<=" -> "le"
  | ">" -> "g"
  | ">=" -> "ge"
  | "==" -> "e"
  | "!=" -> "ne") in
  env, [Mov (lOp, eax); Binop ("cmp", rOp, eax); Mov (L 0, eax); Set (suf, "%al"); Mov (eax, op)]
  
let intToBool x = [Mov (x, eax); Binop ("cmp", L 0, eax); Mov (L 0, eax);
                   Set ("ne", "%al"); Mov (eax, x)]
                   
let compileLogic x env = function
| (lOp, rOp) -> 
  let op, env = env#allocate in
  env, intToBool lOp @ intToBool rOp @ [Mov (lOp, eax); Binop (x, rOp, eax); Mov (eax, op)]

let rec compileDiv env = function
| (lOp, rOp) -> 
  let op, env = env#allocate in
  env, [Mov (lOp, eax); Cltd; IDiv rOp; Mov (eax, op)]
  
let rec compileMod env = function
| (lOp, rOp) -> 
  let op, env = env#allocate in
  env, [Mov (lOp, eax); Cltd; IDiv rOp; Mov (edx, op)]

(* Symbolic stack machine evaluator
     compile' : env -> prg -> env * instr list
   Take an environment, a stack machine program, and returns a pair --- the updated environment and the list
   of x86 instructions
*)
let rec range_rec l a b = 
  if a = b then l @ [b]
  else range_rec (l @ [a]) (a + 1) b

let range a b = range_rec [] a b

let compile_call env additional_arguments = function 
| (CALL (name, nargs, isProcedure)) ->
let name, add, needRev = 
(match name with 
| "raw" -> "Lraw", [], true
| "write" -> "Lwrite", [], true
| "read" -> "Lread", [], true
| ".elem" -> "Belem", [], true
| ".array" -> "Barray", [Push (L nargs)], true
| ".length" -> "Blength", [], true
| "Bsta" -> "Bsta", [], true
| "Bsexp" -> "Bsexp", [], true
| "Btag" -> "Btag", [], true
| _ -> name, [], false
)
in
let additional_arguments = additional_arguments @ add in
let registersToStack, stackToRegisters = 
  List.fold_left (fun (st, reg) x -> st @ [Push x], Pop x :: reg) ([], []) (env#live_registers nargs) in
let argsOnStack, env = 
  if nargs = 0 then [], env
  else List.fold_left (fun (st, env) _ -> let op, env = env#pop' "compile_call" in Push op :: st, env) ([], env) (range 0 (nargs - 1)) in
let env, notProcAdd = if not isProcedure then let op, env = env#allocate in env, [Mov (eax, op)] else env, [] in
env, 
registersToStack @ (if needRev then List.rev argsOnStack else argsOnStack) @ 
additional_arguments @ [Call name; Binop ("+", L (4 * (nargs + List.length additional_arguments)), esp)] @ 
stackToRegisters @ notProcAdd
| _ -> failwith "Won't compile."

let rec compile' env = function
| []           -> env, []
| (CONST x)::prg -> 
  let op, env     = env#allocate in
  let env, instrs = compile' env prg in
  env, (Mov (L x, op))::instrs
| (LD x)::prg -> 
  let op, env = env#allocate in 
  let p = [Mov (env#loc x, eax); Mov (eax, op)] in
  let env, instrs = compile' env prg in
  env, p @ instrs
| (ST x)::prg -> 
  let op, env = env#pop' "st" in 
  let env = env#global x in
  let env, instrs = compile' env prg in
  env, [Mov (op, eax); Mov(eax, env#loc x)] @ instrs
| (LABEL l)::prg -> 
  let env = if env#is_barrier then (env#drop_barrier)#retrieve_stack l else env in
  let env, instrs = compile' env prg in
  env, [Label l] @ instrs
| (JMP l)::prg -> 
  let env = (env#set_stack l)#set_barrier in
  let env, instrs = compile' env prg in
  env, [Jmp l] @ instrs
| (CJMP (z, l))::prg -> 
  let op, env = env#pop' "cjmp" in
  let env = env#set_stack l in
  let env, instrs = compile' env prg in
  env, [Binop ("cmp", L 0, op); CJmp (z, l)] @ instrs
| (BINOP x)::prg -> 
  let rOp, lOp, env = env#pop2 in
  let env, instrs = (match x with
                     | "+"  -> compileSimple x env (lOp, rOp)
                     | "-"  -> compileSimple x env (lOp, rOp)
                     | "*"  -> compileSimple x env (lOp, rOp)
                     | "/"  -> compileDiv env (lOp, rOp)
                     | "%"  -> compileMod env (lOp, rOp)
                     | "<"  -> compileComparison x env (lOp, rOp)
                     | "<=" -> compileComparison x env (lOp, rOp)
                     | ">"  -> compileComparison x env (lOp, rOp)
                     | ">=" -> compileComparison x env (lOp, rOp)
                     | "==" -> compileComparison x env (lOp, rOp)
                     | "!=" -> compileComparison x env (lOp, rOp)
                     | "&&" -> compileLogic x env (lOp, rOp)
                     | "!!" -> compileLogic x env (lOp, rOp)
                     | a    -> failwith ("Unknown binary operator: " ^ a)) in
  let env, instrs' = compile' env prg in
  env, instrs @ instrs'
| (CALL (name, nargs, isProcedure))::prg -> 
let env, p = compile_call env [] (CALL (name, nargs, isProcedure)) in
let env, rest = compile' env prg in 
env, p @ rest
| (BEGIN (name, args, locs))::prg  -> 
let env = env#enter name args locs in
let p = [Push ebp; Mov (esp, ebp); Binop ("-", L (4 * List.length locs), esp); Binop ("-", LL env#lsize, esp)] in
let env, rest = compile' env prg in
env, p @ rest
| END::prg   ->
let p = [Binop ("+", L (4 * List.length env#locals), esp); Meta (Printf.sprintf "\t.set\t%s,\t%d" env#lsize (4 * env#allocated)); Jmp "epilogue"] in
let env', prg = compile' env prg in
env#move_globals env', p @ prg
| (RET ret)::prg -> 
let mv, env = if ret then let op, env = env#pop' "ret" in [Mov (op, eax)], env else [], env in
let env, prg = compile' env prg in
env, mv @ prg
| (STA (tag, n))::prg -> 
let e, env = env#pop' "sta" in
let arrLoc = env#loc tag in
let env, p = compile_call env [Push arrLoc; Push e; Push (L (n - 1))] (CALL ("Bsta", n - 1, false)) in
let env, rest = compile' env prg in 
env, p @ rest
| (SEXP (tag, n))::prg -> 
let env = env#push (L (env#hash tag)) in
let env, p = compile_call env [Push (L (n + 1))] (CALL ("Bsexp", n + 1, false)) in
let env, rest = compile' env prg in 
env, p @ rest
| DROP::prg ->
let _, env = env#pop' "drop" in
let env, rest = compile' env prg in 
env, rest
| DUP::prg ->
let op = env#peek in
let op1, env = env#allocate in
let env, rest = compile' env prg in 
env, [Mov (op, eax); Mov (eax, op1)] @ rest
| SWAP::prg ->
let op1, op2 = env#peek2 in
let env, rest = compile' env prg in 
env, [Mov (op2, eax); Mov (op1, op2); Mov (eax, op1)] @ rest
| (TAG n)::prg ->
let env = env#push (L (env#hash n)) in
let env, p = compile_call env [] (CALL ("Btag", 2, false)) in
let env, rest = compile' env prg in 
env, p @ rest
| (ENTER vars)::prg ->
let args, env = 
  if (List.length vars) = 0 then [], env
  else List.fold_left (fun (st, env) _ -> let op, env = env#pop' "enter" in op :: st, env) ([], env) (range 0 (List.length vars - 1)) in
let env = env#scope vars in
let argsToLocs = List.fold_left (fun res (name, op) -> [Mov (op, eax); Mov (eax, env#loc name)] @ res) [] (List.combine (List.rev vars) args) in
let env, rest = compile' env prg in 
env, argsToLocs @ rest
| LEAVE::prg ->
let env = env#unscope in
let env, rest = compile' env prg in 
env, rest

let compile env p =
let env, prg = compile' env p in
env, prg @ [Label "epilogue"; Mov (ebp, esp); Pop ebp; Ret]

(* A set of strings *)           
module S = Set.Make (String) 

(* A map indexed by strings *)
module M = Map.Make (String) 

(* Environment implementation *)
class env =
  let chars          = "_abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNJPQRSTUVWXYZ" in
  let make_assoc l i = List.combine l (List.init (List.length l) (fun x -> x + i)) in
  let rec assoc  x   = function [] -> raise Not_found | l :: ls -> try List.assoc x l with Not_found -> assoc x ls in
  object (self)
    val globals     = S.empty (* a set of global variables         *)
    val stringm     = M.empty (* a string map                      *)
    val scount      = 0       (* string count                      *)
    val stack_slots = 0       (* maximal number of stack positions *)
    val static_size = 0       (* static data size                  *)
    val stack       = []      (* symbolic stack                    *)
    val args        = []      (* function arguments                *)
    val locals      = []      (* function local variables          *)
    val fname       = ""      (* function name                     *)
    val stackmap    = M.empty (* labels to stack map               *)
    val barrier     = false   (* barrier condition                 *)
                        
    method show_stack =
      GT.show(list) (GT.show(opnd)) stack
             
    method print_locals =
      Printf.printf "LOCALS: size = %d\n" static_size;
      List.iter
        (fun l ->
          Printf.printf "(";
          List.iter (fun (a, i) -> Printf.printf "%s=%d " a i) l;
          Printf.printf ")\n"
        ) locals;
      Printf.printf "END LOCALS\n"

    (* check barrier condition *)
    method is_barrier = barrier

    (* set barrier *)
    method set_barrier = {< barrier = true >}

    (* drop barrier *)
    method drop_barrier = {< barrier = false >}
                            
    (* associates a stack to a label *)
    method set_stack l = (*Printf.printf "Setting stack for %s\n" l;*) {< stackmap = M.add l stack stackmap >}
                               
    (* retrieves a stack for a label *)
    method retrieve_stack l = (*Printf.printf "Retrieving stack for %s\n" l;*)
      try {< stack = M.find l stackmap >} with Not_found -> self
                               
    (* gets a name for a global variable *)
    method loc x =
      try S (- (List.assoc x args)  -  1)
      with Not_found ->  
        try S (assoc x locals) with Not_found -> M ("global_" ^ x)
        
    (* allocates a fresh position on a symbolic stack *)
    method allocate =    
      let x, n =
	let rec allocate' = function
	| []                            -> ebx          , stack_slots
	| (S n)::_                      -> S (n+1)      , n+2
	| (R n)::_ when n < num_of_regs -> R (n+1)      , stack_slots
	| _                             -> S static_size, static_size+1
	in
	allocate' stack
      in
      x, {< stack_slots = max n stack_slots; stack = x::stack >}

    (* pushes an operand to the symbolic stack *)
    method push y = {< stack = y::stack >}

    (* pops one operand from the symbolic stack *)
    method pop = let x::stack' = stack in x, {< stack = stack' >}

    method pop' s = try let x::stack' = stack in x, {< stack = stack' >} with _ -> failwith s

    (* pops two operands from the symbolic stack *)
    method pop2 = let x::y::stack' = stack in x, y, {< stack = stack' >}

    (* peeks the top of the stack (the stack does not change) *)
    method peek = List.hd stack

    (* peeks two topmost values from the stack (the stack itself does not change) *)
    method peek2 = let x::y::_ = stack in x, y

    (* tag hash: gets a hash for a string tag *)
    method hash tag =
      let h = Pervasives.ref 0 in
      for i = 0 to min (String.length tag - 1) 4 do
        h := (!h lsl 6) lor (String.index chars tag.[i])
      done;
      !h      
             
    (* registers a global variable in the environment *)
    method global x  = {< globals = S.add ("global_" ^ x) globals >}

    method locals = locals

    method move_globals (s : env) = 
      {< globals = S.of_list s#globals >}

    (* registers a string constant *)
    method string x =
      try M.find x stringm, self
      with Not_found ->
        let y = Printf.sprintf "string_%d" scount in
        let m = M.add x y stringm in
        y, {< scount = scount + 1; stringm = m>}
                       
    (* gets all global variables *)      
    method globals = S.elements globals

    (* gets all string definitions *)      
    method strings = M.bindings stringm

    (* gets a number of stack positions allocated *)
    method allocated = stack_slots                                
                                
    (* enters a function *)
    method enter f a l =
      let n = List.length l in
      {< static_size = n; stack_slots = n; stack = []; locals = [make_assoc l 0]; args = make_assoc a 0; fname = f >}

    (* enters a scope *)
    method scope vars =
      let n = List.length vars in
      let static_size' = n + static_size in
      {< stack_slots = max stack_slots static_size'; static_size = static_size'; locals = (make_assoc vars static_size) :: locals >}

    (* leaves a scope *)
    method unscope =
      let n = List.length (List.hd locals) in
      {< static_size = static_size - n; locals = List.tl locals >}
        
    (* returns a label for the epilogue *)
    method epilogue = Printf.sprintf "L%s_epilogue" fname
                                     
    (* returns a name for local size meta-symbol *)
    method lsize = Printf.sprintf "L%s_SIZE" fname

    (* returns a list of live registers *)
    method live_registers depth =
      let rec inner d acc = function
      | []             -> acc
      | (R _ as r)::tl -> inner (d+1) (if d >= depth then (r::acc) else acc) tl
      | _::tl          -> inner (d+1) acc tl
      in
      inner 0 [] stack
       
  end
  
(* Generates an assembler text for a program: first compiles the program into
   the stack code, then generates x86 assember code, then prints the assembler file
*)
let genasm (ds, stmt) =
  let stmt = Language.Stmt.Seq (stmt, Language.Stmt.Return (Some (Language.Expr.Call ("raw", [Language.Expr.Const 0])))) in
  (* let () = SM.print_prg (SM.compile (ds, stmt)) in *)
  let env, code =
    compile
      (new env)
      ((LABEL "main") :: (BEGIN ("main", [], [])) :: SM.compile (ds, stmt))
  in
  let data = Meta "\t.data" :: (List.map (fun s      -> Meta (Printf.sprintf "%s:\t.int\t0"         s  )) env#globals) @
                               (List.map (fun (s, v) -> Meta (Printf.sprintf "%s:\t.string\t\"%s\"" v s)) env#strings) in 
  let asm = Buffer.create 1024 in
  List.iter
    (fun i -> Buffer.add_string asm (Printf.sprintf "%s\n" @@ show i))
    (data @ [Meta "\t.text"; Meta "\t.globl\tmain"] @ code);
  Buffer.contents asm

(* Builds a program: generates the assembler file and compiles it with the gcc toolchain *)
let build prog name =
  let outf = open_out (Printf.sprintf "%s.s" name) in
  Printf.fprintf outf "%s" (genasm prog);
  close_out outf;
  let inc = try Sys.getenv "RC_RUNTIME" with _ -> "../runtime" in
  Sys.command (Printf.sprintf "gcc -m32 -o %s %s/runtime.o %s.s" name inc name)
 
