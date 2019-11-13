(* X86 codegeneration interface *)

(* The registers: *)
let regs = [|"%ebx"; "%ecx"; "%esi"; "%edi"; "%eax"; "%edx"; "%ebp"; "%esp"|]

(* We can not freely operate with all register; only 4 by now *)                    
let num_of_regs = Array.length regs - 5

(* We need to know the word size to calculate offsets correctly *)
let word_size = 4

(* We need to distinguish the following operand types: *)
type opnd = 
| R of int     (* hard register                    *)
| S of int     (* a position on the hardware stack *)
| M of string  (* a named memory location          *)
| L of int     (* an immediate operand             *)

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

let rec compile' env = function
| []           -> env, []
| (CONST x)::prg -> 
  let op, env     = env#allocate in
  let env, instrs = compile' env prg in
  env, (Mov (L x, op))::instrs
| (LD x)::prg -> 
  let op, env = env#allocate in 
  let env, instrs = compile' env prg in
  env, [Mov (env#loc x, eax); Mov (eax, op)] @ instrs
| (ST x)::prg -> 
  let op, env = env#pop in 
  let env = env#global x in
  let env, instrs = compile' env prg in
  env, [Mov (op, eax); Mov(eax, env#loc x)] @ instrs
| (LABEL l)::prg -> 
  let env, instrs = compile' env prg in
  env, [Label l] @ instrs
| (JMP l)::prg -> 
  let env, instrs = compile' env prg in
  env, [Jmp l] @ instrs
| (CJMP (z, l))::prg -> 
  let op, env = env#pop in
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
let name = if name = "write" then "Lwrite" else if name = "read" then "Lread" else name in
let registersToStack, stackToRegisters = 
  List.fold_left (fun (st, reg) x -> st @ [Push x], Pop x :: reg) ([], []) env#live_registers in
let argsOnStack, env = 
  if nargs = 0 then [], env
  else List.fold_left (fun (st, env) _ -> let op, env = env#pop in Push op :: st, env) ([], env) (range 0 (nargs - 1)) in
let env, notProcAdd = 
  if (not isProcedure) then let op, env = env#allocate in env, [Mov (eax, op)] else env, [] in
let env, rest = compile' env prg in 
env, registersToStack @ argsOnStack @ [Call name; Binop ("+", L (4 * nargs), esp)] @ stackToRegisters @ notProcAdd @ rest
| (BEGIN (name, args, locs))::prg  -> 
let env = env#enter name args locs in
let env, rest = compile' env prg in
env, [Push ebp; Mov (esp, ebp); Binop ("-", L (4 * List.length locs), esp)] @ rest
| END::prg   ->
let env', prg = compile' env prg in
env#move_globals env', [Binop ("+", L (4 * List.length env#locals), esp); Jmp "epilogue"] @ prg
| (RET ret)::prg -> 
let mv, env = if ret then let op, env = env#pop in [Mov (op, eax)], env else [], env in
let env, prg = compile' env prg in
env, mv @ prg

let compile env p =
let env, prg = compile' env p in
env, prg @ [Label "epilogue"; Mov (ebp, esp); Pop ebp; Ret]

(* A set of strings *)           
module S = Set.Make (String)

(* Environment implementation *)
let make_assoc l = List.combine l (List.init (List.length l) (fun x -> x))
                     
class env =
  object (self)
    val globals     = S.empty (* a set of global variables         *)
    val stack_slots = 0       (* maximal number of stack positions *)
    val stack       = []      (* symbolic stack                    *)
    val args        = []      (* function arguments                *)
    val locals      = []      (* function local variables          *)
    val fname       = ""      (* function name                     *)
                        
    (* gets a name for a global variable *)
    method loc x =
      try S (- (List.assoc x args)  -  1)
      with Not_found ->  
        try S (List.assoc x locals) with Not_found -> M ("global_" ^ x)
        
    (* allocates a fresh position on a symbolic stack *)
    method allocate =    
      let x, n =
        let rec allocate' = function
        | []                            -> R 0     , 0
        | (S n)::_                      -> S (n+1) , n+2
        | (R n)::_ when n < num_of_regs -> R (n+1) , stack_slots
        | (M _)::s                      -> allocate' s
        | _                             -> let n = List.length locals in S n, n+1
        in
        allocate' stack
      in
      x, {< stack_slots = max n stack_slots; stack = x::stack >}

    (* pushes an operand to the symbolic stack *)
    method push y = {< stack = y::stack >}

    (* pops one operand from the symbolic stack *)
    method pop = let x::stack' = stack in x, {< stack = stack' >}

    (* pops two operands from the symbolic stack *)
    method pop2 = let x::y::stack' = stack in x, y, {< stack = stack' >}

    (* registers a global variable in the environment *)
    method global x  = {< globals = S.add ("global_" ^ x) globals >}

    (* gets all global variables *)      
    method globals = S.elements globals

    method locals = locals

    (* gets a number of stack positions allocated *)
    method allocated = stack_slots                                
                                
    (* enters a function *)
    method enter f a l =
      {< stack_slots = List.length l; stack = []; locals = make_assoc l; args = make_assoc a; fname = f >}

    method move_globals (s : env) = 
      {< globals = S.of_list s#globals >}
      
    (* returns a label for the epilogue *)
    method epilogue = Printf.sprintf "L%s_epilogue" fname
                                     
    (* returns a name for local size meta-symbol *)
    method lsize = Printf.sprintf "L%s_SIZE" fname

    (* returns a list of live registers *)
    method live_registers =
      List.filter (function R _ -> true | _ -> false) stack
       
  end
  
(* Generates an assembler text for a program: first compiles the program into
   the stack code, then generates x86 assember code, then prints the assembler file
*)
let genasm (ds, stmt) =
  let stmt = Language.Stmt.Seq (stmt, Language.Stmt.Return (Some (Language.Expr.Const 0))) in
  let env, code =
    compile
      (new env)
      ((LABEL "main") :: (BEGIN ("main", [], [])) :: SM.compile (ds, stmt))
  in
  let data = Meta "\t.data" :: (List.map (fun s -> Meta (s ^ ":\t.int\t0")) env#globals) in 
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
 
