(* Opening a library for generic programming (https://github.com/dboulytchev/GT).
   The library provides "@type ..." syntax extension and plugins like show, etc.
*)
open GT

(* Opening a library for combinator-based syntax analysis *)
open Ostap
open Ostap.Combinators

(* States *)
module State =
  struct

    (* State: global state, local state, scope variables *)
    type t = {g : string -> int; l : string -> int; scope : string list}

    (* Empty state *)
    let empty =
      let e x = failwith (Printf.sprintf "Undefined variable: %s" x) in
      {g = e; l = e; scope = []}

    (* Update: non-destructively "modifies" the state s by binding the variable x
       to value v and returns the new state w.r.t. a scope
    *)
    let update x v s =
      let u x v s = fun y -> if x = y then v else s y in
      if List.mem x s.scope then {s with l = u x v s.l} else {s with g = u x v s.g}

    (* Evals a variable in a state w.r.t. a scope *)
    let eval s x = (if List.mem x s.scope then s.l else s.g) x

    (* Creates a new scope, based on a given state *)
    let push_scope st xs = {empty with g = st.g; scope = xs}

    (* Drops a scope *)
    let drop_scope st st' = {st' with g = st.g}

  end

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

    (* Expression evaluator

          val eval : state -> t -> int

       Takes a state and an expression, and returns the value of the expression in
       the given state.
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

    let rec eval st expr =
      match expr with
      | Const n -> n
      | Var   x -> State.eval st x
      | Binop (op, x, y) -> to_func op (eval st x) (eval st y)

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
        n:DECIMAL {Const n}
      | x:IDENT   {Var x}
      | -"(" parse -")"
    )
end

(* Simple statements: syntax and sematics *)
module Stmt =
  struct

    (* The type for statements *)
    @type t =
    (* read into the variable           *) | Read   of string
    (* write the value of an expression *) | Write  of Expr.t
    (* assignment                       *) | Assign of string * Expr.t
    (* composition                      *) | Seq    of t * t
    (* empty statement                  *) | Skip
    (* conditional                      *) | If     of Expr.t * t * t
    (* loop with a pre-condition        *) | While  of Expr.t * t
    (* loop with a post-condition       *) | Repeat of t * Expr.t
    (* call a procedure                 *) | Call   of string * Expr.t list with show

    (* The type of configuration: a state, an input stream, an output stream *)
    type config = State.t * int list * int list

    let assign x e (s, i, o) = (State.update x (Expr.eval s e) s, i, o)

    let read x (s, (z :: i), o) = ((State.update x z s), i, o)

    let write e (s, i, o) = (s, i, o @ [Expr.eval s e])

    let rec arg_eval args s = match args with
        | [] -> []
        | (x :: xs) -> (Expr.eval s x) :: arg_eval xs s

    let rec arg_put values variables s = match (values, variables) with
        | ([], []) -> s
        | (v :: vs, x :: xs) -> arg_put vs xs (State.update x v s)

    (* Statement evaluator

         val eval : env -> config -> t -> config

       Takes an environment, a configuration and a statement, and returns another configuration. The
       environment supplies the following method

           method definition : string -> (string list, string list, t)

       which returns a list of formal parameters and a body for given definition
    *)
    let rec eval env conf t = match t with
        | Read x -> read x conf
        | Write e -> write e conf
        | Assign (x, e) -> assign x e conf
        | Skip -> conf
        | If (cond, bt, bf) ->  let (s, _, _) = conf in
            if (Expr.eval s cond) <> 0
            then eval env conf bt
            else eval env conf bf
        | While (cond, bd) -> let (s, _, _) = conf in
            if Expr.eval s cond <> 0
            then eval env (eval env conf bd) (While (cond, bd))
            else conf
        |  Repeat (bd, cond) -> let (s, i, o) = eval env conf bd in
            if Expr.eval s cond <> 0
            then (s, i, o)
            else eval env (s, i, o) (Repeat (bd, cond))
        | Call (f, l) -> let (args, locl, bd) = env#definition f in
                         let (s, i, o) = conf in
                         let s' = arg_put (arg_eval l s) args (State.push_scope s (args @ locl)) in
                         let (s', i, o) = eval env (s', i, o) bd in
                        (State.drop_scope s' s, i, o)
        | Seq (t, k) -> eval env (eval env conf t) k
    (* Statement parser *)
    ostap (
      simple_stmt:
          x:IDENT ":=" e:!(Expr.parse) {Assign(x, e)}
        | f:IDENT "(" args:(!(Util.list0) [Expr.parse]) ")" {Call (f, args)}
        | "read" "(" x:IDENT ")" {Read x}
        | "write" "(" e:!(Expr.parse) ")" {Write e}
        | "skip" {Skip}
        | "while" cond:!(Expr.parse) "do" st:stmt "od" {While(cond, st)}
        | "for" init:stmt "," cond:!(Expr.parse) "," incr:stmt "do" st:stmt "od" {Seq (init, While(cond, Seq(st, incr)))}
        | "repeat" st:stmt "until" cond:!(Expr.parse) {Repeat (st, cond)}
        | "if" cond:!(Expr.parse) "then" bt:stmt "elif" elif:elseif "fi" {If (cond, bt, elif)}
        | "if" cond:!(Expr.parse) "then" bt:stmt "else" bf:stmt "fi" {If (cond, bt, bf)}
        | "if" cond:!(Expr.parse) "then" bt:stmt "fi" {If (cond, bt, Skip)};

        elseif:
          cond:!(Expr.parse) "then" bt:stmt "elif" elif:elseif {If (cond, bt, elif)}
        | cond:!(Expr.parse) "then" bt:stmt "else" bf:stmt {If (cond, bt, bf)}
        | cond:!(Expr.parse) "then" bt:stmt {If (cond, bt, Skip)};

        stmt: <s::ss> : !(Util.listBy)[ostap (";")][simple_stmt] {List.fold_left (fun s ss -> Seq (s, ss)) s ss};
parse: stmt
    )
  end

(* Function and procedure definitions *)
module Definition =
  struct

    (* The type for a definition: name, argument list, local variables, body *)
    type t = string * (string list * string list * Stmt.t)

    ostap (
        parse: "fun" name:IDENT "(" args:!(vars) ")" locl:!(loc) "{" bd:!(Stmt.parse) "}" {(name, (args, locl, bd))};
        vars: x:IDENT "," r:!(vars) {[x] @ r} | x:IDENT {[x]} | empty {[]};
        loc:"local" x:IDENT "," r:!(vars) {[x] @ r} | "local" x:IDENT {[x]} | "local" {[]} | empty {[]}
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
  let m        = List.fold_left (fun m ((name, _) as def) -> M.add name def m) M.empty defs in
  let _, _, o  = Stmt.eval (object method definition f = snd @@ M.find f m end) (State.empty, i, []) body in o

(* Top-level parser *)
let parse = ostap (!(Definition.parse)* !(Stmt.parse))
