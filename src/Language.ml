(* Opening a library for generic programming (https://github.com/dboulytchev/GT).
   The library provides "@type ..." syntax extension and plugins like show, etc.
*)
open GT

(* Opening a library for combinator-based syntax analysis *)
open Ostap
open Combinators

(* Values *)
module Value =
  struct

    @type t = Int of int | String of bytes | Array of t array | Sexp of string * t list (*with show*)

    let to_int = function 
    | Int n -> n 
    | _ -> failwith "int value expected"

    let to_string = function 
    | String s -> s 
    | _ -> failwith "string value expected"

    let to_array = function
    | Array a -> a
    | _       -> failwith "array value expected"

    let sexp   s vs = Sexp (s, vs)
    let of_int    n = Int    n
    let of_string s = String s
    let of_array  a = Array  a

    let tag_of = function
    | Sexp (t, _) -> t
    | _ -> failwith "symbolic expression expected"

    let update_string s i x = Bytes.set s i x; s 
    let update_array  a i x = a.(i) <- x; a
                      
  end
       
(* States *)
module State =
  struct
                                                                
    (* State: global state, local state, scope variables *)
    type t =
    | G of (string -> Value.t)
    | L of string list * (string -> Value.t) * t

    (* Undefined state *)
    let undefined x = failwith (Printf.sprintf "Undefined variable: %s" x)

    (* Bind a variable to a value in a state *)
    let bind x v s = fun y -> if x = y then v else s y 

    (* Empty state *)
    let empty = G undefined

    (* Update: non-destructively "modifies" the state s by binding the variable x 
       to value v and returns the new state w.r.t. a scope
    *)
    let update x v s =
      let rec inner = function
      | G s -> G (bind x v s)
      | L (scope, s, enclosing) ->
         if List.mem x scope then L (scope, bind x v s, enclosing) else L (scope, s, inner enclosing)
      in
      inner s

    (* Evals a variable in a state w.r.t. a scope *)
    let rec eval s x =
      match s with
      | G s -> s x
      | L (scope, s, enclosing) -> if List.mem x scope then s x else eval enclosing x

    (* Creates a new scope, based on a given state *)
    let rec enter st xs =
      match st with
      | G _         -> L (xs, undefined, st)
      | L (_, _, e) -> enter e xs

    (* Drops a scope *)
    let leave st st' =
      let rec get = function
      | G _ as st -> st
      | L (_, _, e) -> get e
      in
      let g = get st in
      let rec recurse = function
      | L (scope, s, e) -> L (scope, s, recurse e)
      | G _             -> g
      in
      recurse st'

    (* Push a new local scope *)
    let push st s xs = L (xs, s, st)

    (* Drop a local scope *)
    let drop (L (_, _, e)) = e
                               
  end

(* Builtins *)
module Builtin =
  struct
      
    let eval (st, i, o, _) args = function
    | "read"     -> (match i with z::i' -> (st, i', o, Some (Value.of_int z)) | _ -> failwith "Unexpected end of input")
    | "write"    -> (st, i, o @ [Value.to_int @@ List.hd args], None)
    | ".elem"    -> let [b; j] = args in
                    (st, i, o, let i = Value.to_int j in
                               Some (match b with
                                     | Value.String   s  -> Value.of_int @@ Char.code (Bytes.get s i)
                                     | Value.Array    a  -> a.(i)
                                     | Value.Sexp (_, a) -> List.nth a i
                               )
                    )         
    | ".length"     -> (st, i, o, Some (Value.of_int (match List.hd args with Value.Sexp (_, a) -> List.length a | Value.Array a -> Array.length a | Value.String s -> Bytes.length s)))
    | ".array"      -> (st, i, o, Some (Value.of_array @@ Array.of_list args))
    | "isArray"  -> let [a] = args in (st, i, o, Some (Value.of_int @@ match a with Value.Array  _ -> 1 | _ -> 0))
    | "isString" -> let [a] = args in (st, i, o, Some (Value.of_int @@ match a with Value.String _ -> 1 | _ -> 0))     

    let isBuiltin = function
    | "read" | "write" | ".elem" | ".length"
    | ".array" | "isArray" | "isString"       -> true
    | _                                       -> false                    
       
  end
    
(* Simple expressions: syntax and semantics *)
module Expr =
  struct
    
    (* The type for expressions. Note, in regular OCaml there is no "@type..." 
       notation, it came from GT. 
    *)
    @type t =
    (* integer constant   *) | Const  of int
    (* array              *) | Array  of t list
    (* string             *) | String of string
    (* S-expressions      *) | Sexp   of string * t list
    (* variable           *) | Var    of string
    (* binary operator    *) | Binop  of string * t * t
    (* element extraction *) | Elem   of t * t
    (* length             *) | Length of t 
    (* function call      *) | Call   of string * t list with show

    (* Available binary operators:
        !!                   --- disjunction
        &&                   --- conjunction
        ==, !=, <=, <, >=, > --- comparisons
        +, -                 --- addition, subtraction
        *, /, %              --- multiplication, division, reminder
    *)

    (* The type of configuration: a state, an input stream, an output stream, an optional value *)
    type config = State.t * int list * int list * Value.t option
                                                            
    (* Expression evaluator

          val eval : env -> config -> t -> int * config


       Takes an environment, a configuration and an expresion, and returns another configuration. The 
       environment supplies the following method

           method definition : env -> string -> int list -> config -> config

       which takes an environment (of the same type), a name of the function, a list of actual parameters and a configuration, 
       an returns a pair: the return value for the call and the resulting configuration
    *)                                                       
    let to_func op =
      let bti   = function true -> 1 | _ -> 0 in
      let itb b = b <> 0 in
      let (|>) f g   = fun x y -> f (g x y) in
      match op with
      | "+"  -> (+)
      | "-"  -> (-)
      | "*"  -> ( * )
      | "/"  -> (/)
      | "%"  -> (mod)
      | "<"  -> bti |> (< )
      | "<=" -> bti |> (<=)
      | ">"  -> bti |> (> )
      | ">=" -> bti |> (>=)
      | "==" -> bti |> (= )
      | "!=" -> bti |> (<>)
      | "&&" -> fun x y -> bti (itb x && itb y)
      | "!!" -> fun x y -> bti (itb x || itb y)
      | _    -> failwith (Printf.sprintf "Unknown binary operator %s" op)    
    
    let rec eval env ((st, i, o, r) as conf) expr = 
    match expr with
    | Const n -> (st, i, o, Some (Value.of_int n))
    | Var x   -> (st, i, o, Some (State.eval st x))
    | Binop (op, le, re) -> 
    let (_, _, _, Some l) as conf = eval env conf le in
    let (st, i, o, Some r) = eval env conf re in
    (st, i, o, Some (Value.of_int (to_func op (Value.to_int l) (Value.to_int r))))
    | Call (name, args) -> 
    let (st, i, o, args) = List.fold_left 
      (fun (st, i, o, acc) x -> 
        let (st, i, o, Some r) = eval env (st, i, o, None) x in
        (st, i, o, acc @ [r])
      ) (st, i, o, []) args in
    env#definition env name args (st, i, o, None)
    | Elem (array, index) ->
    let (st, i, o, Some array) = eval env conf array in
    let (st, i, o, Some ind) = eval env (st, i, o, None) index in
    Builtin.eval (st, i, o, None) [array; ind] ".elem"
    | Array array ->
    let (st, i, o, array) = eval_list env conf array in
    Builtin.eval (st, i, o, None) array ".array"
    | Length array -> 
    let (st, i, o, Some array) = eval env conf array in
    Builtin.eval (st, i, o, None) [array] ".length"
    | Sexp (n, es) -> 
    let (st, i, o, array) = eval_list env conf es in 
    (st, i, o, Some (Value.sexp n array))
    and eval_list env conf xs =
      let vs, (st, i, o, _) =
        List.fold_left
          (fun (acc, conf) x ->
             let (_, _, _, Some v) as conf = eval env conf x in
             v::acc, conf
          )
          ([], conf)
          xs
      in
      (st, i, o, List.rev vs)
         
    (* Expression parser. You can use the following terminals:

         IDENT   --- a non-empty identifier a-zA-Z[a-zA-Z0-9_]* as a string
         DECIMAL --- a decimal constant [0-9]+ as a string                                                                                                                  
    *)
    ostap (   
      parse:                                   
        !(Ostap.Util.expr 
                (fun x -> x)
          (Array.map (fun (a, s) -> a, 
                              List.map  (fun s -> ostap(- $(s)), (fun x y -> Binop (s, x, y))) s
                            ) 
                  [|                
        `Lefta, ["!!"];
        `Lefta, ["&&"];
        `Nona , ["=="; "!="; "<="; "<"; ">="; ">"];
        `Lefta, ["+" ; "-"];
        `Lefta, ["*" ; "/"; "%"];
                  |] 
          )
          primary);
          
      primary:
            name:IDENT -" "* -"(" args:!(Util.listBy)[ostap ("," " "*)][parse]? -")" {Call (name, (match args with None -> [] | Some s -> s))}
          | n:DECIMAL {Const n}
          | -"(" parse -")"
          | array_length
          | array_elem
          | array_init
          | sexp
          | x:IDENT   {Var x}
          | -"\'" char_lit:IDENT -"\'" {Const (Char.code (String.get char_lit 0))}
          | -"\"" str_lit:IDENT -"\"" {Array (List.map (fun x -> Const (Char.code x)) (List.init (String.length str_lit) (String.get str_lit)))}
          | -"[" -" "* elems:!(Util.listBy)[ostap ("," " "*)][parse]? -" "* -"]" {Array (match elems with None -> [] | Some s -> s)};

      array_init:
        -"[" -" "* elems:!(Util.listBy)[ostap ("," " "*)][parse]? -" "* -"]"  
        {Array (match elems with None -> [] | Some s -> s)}
      | x:IDENT {Var x};

      array_elem:
            x:array_init -" "* indexes:!(Util.listBy)[ostap (" "*)][index] 
            {List.fold_left (fun x y -> Elem (x, y)) x indexes};

      array_length:
          x:array_elem -" "* -"." -" "* -"length" {Length x}
        | x:array_init -" "* -"." -" "* -"length" {Length x};

      index:
          -" "* -"[" -" "* ind:!(parse) -" "* -"]";
      
      sexp: 
          -"`" name:IDENT -" "* -"(" args:!(Util.listBy)[ostap ("," " "*)][parse] -")" {Sexp (name, args)}
        | -"`" name:IDENT {Sexp (name, [])}
      )
    
  end
                    
(* Simple statements: syntax and sematics *)
module Stmt =
  struct

    (* Patterns in statements *)
    module Pattern =
      struct

        (* The type for patterns *)
        @type t =
        (* wildcard "-"     *) | Wildcard
        (* S-expression     *) | Sexp   of string * t list
        (* identifier       *) | Ident  of string
        with show, foldl

        (* Pattern parser *)                                 
        ostap (
          parse:
            -"_" {Wildcard}
          | sexp
          | name:IDENT {Ident name};

          sexp: 
            -"`" name:IDENT -" "* -"(" args:!(Util.listBy)[ostap ("," " "*)][parse] -")" {Sexp (name, args)}
          | -"`" name:IDENT {Sexp (name, [])}
        )
        
        let vars p =
          transform(t) (fun f -> object inherit [string list, _] @t[foldl] f method c_Ident s _ name = name::s end) [] p  

        let rec union xss xss1 = 
        let module M = Set.Make (String) in
        match xss, xss1 with
        | None, _ -> None
        | _, None -> None
        | Some (xs, s), Some (xs1, s1) -> Some (M.union xs xs1, (fun x -> if M.mem x xs1 then s1 x else s x))

        let rec zip_with f l l1 = match l, l1 with
        | _, [] -> []
        | [], _ -> []
        | (x::xs), (y::ys) -> f x y :: zip_with f xs ys

        let rec pattern_eval p l = 
        let module M = Set.Make (String) in
        match p, l with
        | Wildcard, _ -> Some (M.empty, State.undefined)
        | Ident x, e  -> Some (M.singleton x, State.bind x e State.undefined)
        | Sexp (t, exprs), Value.Sexp (tag, arr) -> 
        if t = tag && List.length exprs = List.length arr then
          List.fold_left union (Some (M.empty, State.undefined)) (zip_with pattern_eval exprs arr)
        else None
        | _ -> None
      end
        
    (* The type for statements *)
    @type t =
    (* assignment                       *) | Assign of string * Expr.t list * Expr.t
    (* composition                      *) | Seq    of t * t 
    (* empty statement                  *) | Skip
    (* conditional                      *) | If     of Expr.t * t * t
    (* loop with a pre-condition        *) | While  of Expr.t * t
    (* loop with a post-condition       *) | Repeat of t * Expr.t
    (* pattern-matching                 *) | Case   of Expr.t * (Pattern.t * t) list
    (* return statement                 *) | Return of Expr.t option
    (* call a procedure                 *) | Call   of string * Expr.t list 
    (* leave a scope                    *) | Leave  with show
                                                                                   
    (* Statement evaluator

         val eval : env -> config -> t -> config

       Takes an environment, a configuration and a statement, and returns another configuration. The 
       environment is the same as for expressions
    *)
    let update st x v is =
      let rec update a v = function
      | []    -> v           
      | i::tl ->
          let i = Value.to_int i in
          (match a with
           | Value.String s when tl = [] -> Value.String (Value.update_string s i (Char.chr @@ Value.to_int v))
           | Value.Array a               -> Value.Array  (Value.update_array  a i (update a.(i) v tl))
           ) 
      in
      State.update x (match is with [] -> v | _ -> update (State.eval st x) v is) st

    let skip_op l r =
    match r with
    | Skip -> l
    | _    -> Seq (l, r)
      
    let rec eval env ((st, i, o, r) as conf) k stmt =
    let module M = Set.Make (String) in
    let rec eval_pat env ((st, i, o, r) as conf) k = function
    | (v, [])          -> failwith "Bad pattern match."
    | (v, (p, s) :: t) -> match Pattern.pattern_eval p v with 
                          | Some (vars, st') -> eval env (State.push st st' (M.elements vars), i, o, None) (skip_op Leave k) s
                          | None -> eval_pat env conf k (v, t)
    in
    match (k, stmt) with
    | (Skip, Skip) -> conf
    | (k, Skip)    -> eval env conf Skip k
    | (k, Assign (x, inds, e)) -> 
    (match inds with
    | _::_ ->
    let (st, i, o, inds) = Expr.eval_list env conf inds in
    let (st, i, o, Some y) = Expr.eval env conf e in
    eval env (update st x y inds, i, o, None) Skip k
    | [] ->
    let (st, i, o, Some r) = Expr.eval env conf e in
    eval env (update st x r [], i, o, None) Skip k)
    | (k, Seq (l, r)) ->
    eval env conf (skip_op r k) l
    | (k, If (e, th, el)) ->
    let (st, i, o, Some r) = Expr.eval env conf e in
    let c = (st, i, o, None) in
    if Value.to_int r = 1 then eval env c k th else eval env c k el
    | (k, While (e, body)) ->
    let (st, i, o, Some r) = Expr.eval env conf e in
    let c = (st, i, o, None) in
    if Value.to_int r = 1 then eval env c (skip_op stmt k) body else eval env c Skip k
    | (k, Repeat (body, expr)) ->
    eval env conf (skip_op (If (Binop ("==", expr, Const 0), stmt, Skip)) k) body
    | (k, Call (name, args)) ->
    let (st, i, o, args) = List.fold_left 
      (fun (st, i, o, acc) x -> 
        let (st, i, o, Some r) = Expr.eval env (st, i, o, None) x in
        (st, i, o, acc @ [r])
      ) (st, i, o, []) args in
    eval env (env#definition env name args (st, i, o, None)) Skip k
    | (_, Return None)     -> conf
    | (_, Return (Some e)) -> Expr.eval env conf e
    | (k, Leave) -> eval env (State.drop st, i, o, None) Skip k
    | (k, Case (e, ps)) ->
    let (st, i, o, Some e) = Expr.eval env conf e in
    eval_pat env (st, i, o, None) k (e, ps)
                                                        
    (* Statement parser *)
    ostap (
      parse  : seq | assign | skip | ifP | whileP | repeatP | forP | callP | returnP | caseP;                                                                      
      assign : x:IDENT -" "* inds:!(Util.listBy)[ostap (" "*)][indP]? -" "* -":=" -" "* y:!(Expr.parse) {Assign (x, (match inds with None -> [] | Some l -> l), y)};
      seq    : l:(assign | skip | ifP | whileP | repeatP | forP | callP) -" "* -";" -" "* r:parse {Seq (l, r)};
      skip   : "skip" {Skip};
      ifP    : -"if" -" "* ifHelper;
      ifHelper : cond:!(Expr.parse) -" "* -"then" -" "* th:!(parse) el:!(elseP) {If (cond, th, el)};
      elseP    : -"elif" -" "* ifHelper
              | -"else" -" "* parse -"fi"
              | -"fi" {Skip};
      whileP : "while" -" "* cond:!(Expr.parse) -" "* 
                  -"do" -" "* body:!(parse) 
                  -"od" {While (cond, body)};
      repeatP : "repeat" -" "* body:!(parse) -" "* 
                -"until" -" "* cond:!(Expr.parse)
                {Repeat (body, cond)};
      forP   : -"for" -" "* pred:!(parse) -" "* "," -" "*
              cond:!(Expr.parse) -" "* -"," -" "* 
              post:!(parse) -" "* -"do" 
              body:!(parse) -" "* -"od" 
              {Seq (pred, While (cond, Seq (body, post)))};
      callP   : name:IDENT -" "* -"(" args:!(Util.listBy)[ostap ("," " "*)][Expr.parse]? -")" {Call (name, (match args with None -> [] | Some s -> s))};
      returnP : -" "* -"return" -" "* expr:!(Expr.parse)? {Return expr};
      indP : -"[" -" "* x:!(Expr.parse) -" "* -"]";
      caseP : -"case" -" "* e:!(Expr.parse) -" "* -"of" -" "* matches:!(Util.listBy)[ostap ("|" " "*)][caseHelper]? -" "* -"esac" {Case (e, (match matches with None -> [] | Some s -> s))};
      caseHelper: p:!(Pattern.parse) -" "* -"->" -" "* s:!(parse) {(p, s)}
    )
      
  end

(* Function and procedure definitions *)
module Definition =
  struct

    (* The type for a definition: name, argument list, local variables, body *)
    type t = string * (string list * string list * Stmt.t)

    ostap (
      arg  : IDENT;
      parse: %"fun" name:IDENT "(" args:!(Util.list0 arg) ")"
         locs:(%"local" !(Util.list arg))?
        "{" body:!(Stmt.parse) "}" {
        (name, (args, (match locs with None -> [] | Some l -> l), body))
      }
    )

  end
    
(* The top-level definitions *)

(* The top-level syntax category is a pair of definition list and statement (program body) *)
type t = Definition.t list * Stmt.t    

(* Top-level evaluator

     eval : t -> int list -> int list

   Takes a program and its input stream, and returns the output stream
*)
let eval (defs, body) i =
  let module M = Map.Make (String) in
  let m          = List.fold_left (fun m ((name, _) as def) -> M.add name def m) M.empty defs in  
  let _, _, o, _ =
    Stmt.eval
      (object
         method definition env f args ((st, i, o, r) as conf) =
           try
             let xs, locs, s      =  snd @@ M.find f m in
             let st'              = List.fold_left (fun st (x, a) -> State.update x a st) (State.enter st (xs @ locs)) (List.combine xs args) in
             let st'', i', o', r' = Stmt.eval env (st', i, o, r) Stmt.Skip s in
             (State.leave st'' st, i', o', r')
           with Not_found -> Builtin.eval conf args f
       end)
      (State.empty, i, [], None)
      Stmt.Skip
      body
  in
  o

(* Top-level parser *)
let parse = ostap (!(Definition.parse)* !(Stmt.parse))