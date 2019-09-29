(* X86 codegeneration interface *)

(* The registers: *)
let regs = [|"%ebx"; "%ecx"; "%esi"; "%edi"; "%eax"; "%edx"; "%ebp"; "%esp"|]

(* We can not freely operate with all register; only 3 by now *)                    
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
  | S i -> Printf.sprintf "-%d(%%ebp)" ((i+1) * word_size)
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

(* Opening stack machine to use instructions without fully qualified names *)
open SM

let showReg = function
| R i -> regs.(i)

let compileSimple x env = function
| (R _ as lOp, rOp) -> 
  let op, env = env#allocate in
  env, [Binop (x, lOp, rOp); Push op; Mov (lOp, op)]
| (lOp, (R _ as rOp)) -> 
  let op, env = env#allocate in
  env, [Binop (x, rOp, lOp); Push op; Mov (rOp, op)]
| (lOp, rOp) -> 
  let op, env = env#allocate in
  env, [Mov (lOp, eax); Binop (x, eax, rOp); Push op; Mov (eax, op)]
  
let compileSub env = function
| (lOp, (R _ as rOp)) -> 
  let op, env = env#allocate in
  env, [Mov (lOp, eax); Binop ("-", eax, rOp); Push op; Mov (eax, op)]
| lr -> compileSimple "-" env lr

let compileEquality x env = function
| (lOp, rOp) ->
  let op, env = env#allocate in
  match x with
  | "==" -> 
  env, [Binop ("cmp", lOp, rOp); Push op; Set ("ZF", showReg op)]
  | "!=" -> 
  env, [Binop ("cmp", lOp, rOp); Set ("SF", showReg eax);
        Binop ("cmp", rOp, lOp); Set ("SF", showReg edx);
        Binop ("!!", eax, edx); Push op; Mov (eax, op)]
        
let compileComparison x env = function
| (lOp, rOp) ->
  let op, env = env#allocate in
  match x with
  | "<" -> 
  env, [Binop ("cmp", rOp, lOp); Push op; Set ("SF", showReg op)]
  | "<=" -> 
  env, [Binop ("cmp", rOp, lOp); Set ("SF", showReg eax); Set ("ZF", showReg edx);
        Binop ("!!", eax, edx); Push op; Mov (eax, op)]
  | ">" -> 
  env, [Binop ("cmp", lOp, rOp); Push op; Set ("SF", showReg op)]
  | ">=" -> 
  env, [Binop ("cmp", lOp, rOp); Set ("SF", showReg eax); Set ("ZF", showReg edx);
        Binop ("!!", eax, edx); Push op; Mov (eax, op)]

let rec compileDiv env = function
| (lOp, rOp) -> 
  let op, env = env#allocate in
  env, [Mov (lOp, eax); IDiv rOp; Push op; Mov (eax, op)]
  
let rec compileMod env = function
| (lOp, rOp) -> 
  let op, env = env#allocate in
  env, [Mov (lOp, eax); IDiv rOp; Push op; Mov (edx, op)]

(* Symbolic stack machine evaluator

     compile : env -> prg -> env * instr list

   Take an environment, a stack machine program, and returns a pair --- the updated environment and the list
   of x86 instructions
*)
let rec compile env = function
| []           -> env, []
| (CONST x)::prg -> 
  let op, env     = env#allocate in
  let env, instrs = compile env prg in
  env, (Mov (L x, op))::instrs
| (LD x)::prg -> 
  let op, env = env#allocate in 
  let env, instrs = compile env prg in
  env, (Mov (M (env#loc x), op))::instrs
| (ST x)::prg -> 
  let op, env = env#pop in 
  let env = env#global x in
  let env, instrs = compile env prg in
  env, (Mov (op, M (env#loc x)))::instrs
| READ::prg -> 
  let op, env = env#allocate in 
  let env, instrs = compile env prg in
  env, [Call "Lread"; Pop op] @ instrs
| WRITE::prg -> 
  let op, env = env#pop in 
  let env, instrs = compile env prg in
  env, [Push op; Call "Lwrite"] @ instrs
| (BINOP x)::prg -> 
  let lOp, rOp, env = env#pop2 in
  let env, instrs = (match x with
                     | "+"  -> compileSimple x env (lOp, rOp)
                     | "-"  -> compileSub env (lOp, rOp)
                     | "*"  -> compileSimple x env (lOp, rOp)
                     | "/"  -> compileDiv env (lOp, rOp)
                     | "%"  -> compileMod env (lOp, rOp)
                     | "<"  -> compileComparison x env (lOp, rOp)
                     | "<=" -> compileComparison x env (lOp, rOp)
                     | ">"  -> compileComparison x env (lOp, rOp)
                     | ">=" -> compileComparison x env (lOp, rOp)
                     | "==" -> compileEquality x env (lOp, rOp)
                     | "!=" -> compileEquality x env (lOp, rOp)
                     | "&&" -> compileSimple x env (lOp, rOp)
                     | "!!" -> compileSimple x env (lOp, rOp)
                     | a    -> failwith ("Unknown binary operator: " ^ a)) in
  let env, instrs' = compile env prg in
  env, instrs @ instrs'


(* A set of strings *)           
module S = Set.Make (String)

(* Environment implementation *)
class env =
  object (self)
    val stack_slots = 0        (* maximal number of stack positions *)
    val globals     = S.empty  (* a set of global variables         *)
    val stack       = []       (* symbolic stack                    *)

    (* gets a name for a global variable *)
    method loc x = "global_" ^ x                                 

    (* allocates a fresh position on a symbolic stack *)
    method allocate =    
      let x, n =
	let rec allocate' = function
	| []                            -> ebx     , 0
	| (S n)::_                      -> S (n+1) , n+1
	| (R n)::_ when n < num_of_regs -> R (n+1) , stack_slots
	| _                             -> S 0     , 1
	in
	allocate' stack
      in
      x, {< stack_slots = max n stack_slots; stack = x::stack >}

    (* pushes an operand to the symbolic stack *)
    method push y = {< stack = y::stack >}

    (* pops one operand from the symbolic stack *)
    method pop  = let x::stack'    = stack in x,    {< stack = stack' >}

    (* pops two operands from the symbolic stack *)
    method pop2 = let x::y::stack' = stack in x, y, {< stack = stack' >}

    (* registers a global variable in the environment *)
    method global x  = {< globals = S.add ("global_" ^ x) globals >}

    (* gets the number of allocated stack slots *)
    method allocated = stack_slots

    (* gets all global variables *)      
    method globals = S.elements globals
  end

(* compiles a unit: generates x86 machine code for the stack program and surrounds it
   with function prologue/epilogue
*)
let compile_unit env scode =  
  let env, code = compile env scode in
  env, 
  ([Push ebp; Mov (esp, ebp); Binop ("-", L (word_size*env#allocated), esp)] @ 
   code @
   [Mov (ebp, esp); Pop ebp; Binop ("^", eax, eax); Ret]
  )

(* Generates an assembler text for a program: first compiles the program into
   the stack code, then generates x86 assember code, then prints the assembler file
*)
let genasm prog =
  let env, code = compile_unit (new env) (SM.compile prog) in
  let asm = Buffer.create 1024 in
  Buffer.add_string asm "\t.data\n";
  List.iter
    (fun s ->
       Buffer.add_string asm (Printf.sprintf "%s:\t.int\t0\n" s)
    )
    env#globals;
  Buffer.add_string asm "\t.text\n";
  Buffer.add_string asm "\t.globl\tmain\n";
  Buffer.add_string asm "main:\n";
  List.iter
    (fun i -> Buffer.add_string asm (Printf.sprintf "%s\n" @@ show i))
    code;
  Buffer.contents asm

(* Builds a program: generates the assembler file and compiles it with the gcc toolchain *)
let build stmt name =
  let outf = open_out (Printf.sprintf "%s.s" name) in
  Printf.fprintf outf "%s" (genasm stmt);
  close_out outf;
  let inc = try Sys.getenv "RC_RUNTIME" with _ -> "../runtime" in
  Sys.command (Printf.sprintf "gcc -m32 -o %s %s/runtime.o %s.s" name inc name)
 
