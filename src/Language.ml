(* Opening a library for generic programming (https://github.com/dboulytchev/GT).
   The library provides "@type ..." syntax extension and plugins like show, etc.
*)
open GT

(* Opening a library for combinator-based syntax analysis *)
open Ostap
open Combinators

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
    let enter st xs = {empty with g = st.g; scope = xs}

    (* Drops a scope *)
    let leave st st' = {st' with g = st.g}

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
    (* binary operator  *) | Binop of string * t * t
    (* function call    *) | Call  of string * t list with show

    (* Available binary operators:
        !!                   --- disjunction
        &&                   --- conjunction
        ==, !=, <=, <, >=, > --- comparisons
        +, -                 --- addition, subtraction
        *, /, %              --- multiplication, division, reminder
    *)

    (* The type of configuration: a state, an input stream, an output stream, an optional value *)
    type config = State.t * int list * int list * int option

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

    let eval_binop op left right = (to_func op) left right


    (* Expression evaluator

          val eval : env -> config -> t -> int * config


       Takes an environment, a configuration and an expresion, and returns another configuration. The
       environment supplies the following method

           method definition : env -> string -> int list -> config -> config

       which takes an environment (of the same type), a name of the function, a list of actual parameters and a configuration,
       an returns a pair: the return value for the call and the resulting configuration
    *)
    let rec eval env ((s, i, o, r) as conf) expr = match expr with
      | Const n -> (s, i, o, Some n)
      | Var x -> (s, i, o, Some (State.eval s x))
      | Binop (op, expr1, expr2) -> let (s1, i1, o1, Some r1) = eval env conf expr1 in
                                    let (s2, i2, o2, Some r2) = eval env (s1, i1, o1, Some r1) expr2 in
                                    (s2, i2, o2, Some (eval_binop op r1 r2))
      | Call (name, args) -> let rec eval_exprs env conf exprs = match exprs with
        | [] -> (conf, [])
        | expr :: exprs' -> let (s', i', o', Some r') = eval env conf expr in
                            let (conf'', r'') = eval_exprs env (s', i', o', Some r') exprs' in (conf'', r' :: r'')
      in let (conf', rvs) = eval_exprs env conf args in env#definition env name rvs conf'

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
      | fname:IDENT -"(" args:!(Ostap.Util.list0)[parse] -")" { Call (fname, args) }
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
    (* return statement                 *) | Return of Expr.t option
    (* call a procedure                 *) | Call   of string * Expr.t list with show

    let assign x (s, i, o, Some r) = (State.update x r s, i, o, None)

    let read x (s, (z :: i), o, _) = ((State.update x z s), i, o, None)

    let write (s, i, o, Some r) = (s, i, o @ [r], None)

    let seq s1 s2 = match s2 with
      | Skip -> s1
      | _ -> Seq (s1, s2)

    let rec eval_args args s = match args with
      | [] -> []
      | (arg :: args') -> (Expr.eval s arg) :: eval_args args' s

    let rec put_args values variables s = match (values, variables) with
      | ([], []) -> s
      | (v :: values', x :: variables') -> put_args values' variables' (State.update x v s)

    (* Statement evaluator

         val eval : env -> config -> t -> config

       Takes an environment, a configuration and a statement, and returns another configuration. The
       environment is the same as for expressions
    *)
    let rec eval env ((st, i, o, r) as conf) k stmt = match stmt, k with
      | Skip, Skip -> conf
      | Skip, k -> eval env conf Skip k
      | Assign (x, e), k -> let conf' = Expr.eval env conf e in
                            let c = assign x conf' in eval env c Skip k
      | Read x, k -> let c = read x conf in eval env c Skip k
      | Write e, k -> let conf' = Expr.eval env conf e in
                      let c = write conf' in eval env c Skip k
      | If (cond, th, el), k -> let (st', i', o', Some r') = Expr.eval env conf cond in
        if r' <> 0 then eval env (st', i', o', None) k th else eval env (st', i', o', None) k el
      | While (cond, b), k -> let (st', i', o', Some r') = Expr.eval env conf cond in
        if r' <> 0 then eval env (st', i', o', None) (Seq (While (cond, b), k)) b else eval env (st', i', o', None) Skip k
      | Repeat (b, cond), k -> let (st', i', o', r') = eval env conf Skip b in
                               let (st'', i'', o'', Some r'') = Expr.eval env (st', i', o', r') cond  in
                               if r'' <> 0 then eval env (st'', i'', o'', None) Skip k else eval env (st'', i'', o'', None) k (Repeat (b, cond))
      | Call (name, args), k -> let conf' = Expr.eval env conf (Expr.Call (name, args)) in eval env conf' Skip k
      | Seq (t1, t2), k -> eval env conf (seq t2 k) t1
      | Return (None), k -> conf
      | Return (Some e), k -> Expr.eval env conf e

    (* Statement parser *)
    ostap (
      simple_stmt:
        x:IDENT ":=" e:!(Expr.parse) {Assign (x, e)}
      | f:IDENT "(" args:(!(Util.list0) [Expr.parse]) ")" {Call (f, args)} (*args:(!(Util.list0By) [ostap (",")] [Expr.parse])*)
      | "read" "(" x:IDENT ")"         {Read x}
      | "write" "(" e:!(Expr.parse) ")" {Write e}
      | "skip" {Skip}
      | "while" cond:!(Expr.parse) "do" b:!(parse) "od" {While (cond, b)}
      | "repeat" b:!(parse) "until" cond:!(Expr.parse) {Repeat (b, cond)}
      | "for" pre_action:!(parse) -"," loop_cond:!(Expr.parse) -"," post_action:!(parse) "do" b:!(parse) "od" { Seq (pre_action, While (loop_cond, Seq (b, post_action))) }
      | "return" c:!(Expr.parse) {Return (Some c)}
      | "return" {Return None}
      | "skip" {Skip}
      | if_statement;

      if_statement: "if" cond:!(Expr.parse) "then" th:!(parse) "fi" {If (cond, th, Skip)}
                  | "if" cond:!(Expr.parse) "then" th:!(parse) el:!(else_statement) "fi" {If (cond, th, el)};
      else_statement: "else" b:!(parse) {b}
                    | "elif" cond:!(Expr.parse) "then" th:!(parse) el:!(else_statement) {If (cond, th, el)}
                    | "elif" cond:!(Expr.parse) "then" th:!(parse) {If (cond, th, Skip)};

      parse: <s::ss> : !(Util.listBy)[ostap (";")][simple_stmt] {List.fold_left (fun s ss -> Seq (s, ss)) s ss}
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
         method definition env f args (st, i, o, r) =
           let xs, locs, s      = snd @@ M.find f m in
           let st'              = List.fold_left (fun st (x, a) -> State.update x a st) (State.enter st (xs @ locs)) (List.combine xs args) in
           let st'', i', o', r' = Stmt.eval env (st', i, o, r) Stmt.Skip s in
           (State.leave st'' st, i', o', r')
       end)
      (State.empty, i, [], None)
      Stmt.Skip
      body
  in
  o

(* Top-level parser *)
let parse = ostap (!(Definition.parse)* !(Stmt.parse))
