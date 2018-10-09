(* Opening a library for generic programming (https://github.com/dboulytchev/GT).
   The library provides "@type ..." syntax extension and plugins like show, etc.
*)
open GT

open Ostap
(* Opening a library for combinator-based syntax analysis *)
open Ostap.Combinators

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

    (* Expression evaluator

          val eval : state -> t -> int

       Takes a state and an expression, and returns the value of the expression in
       the given state.
    *)
    let toInt p = if p then 1 else 0

    let applyBinOp op l r = match op with
        | "+" -> l + r
        | "-" -> l - r
        | "*" -> l * r
        | "/" -> l / r
        | "%" -> l mod r
        | "&&" -> toInt (l <> 0 && r <> 0)
        | "!!" -> toInt (l <> 0 || r <> 0)
        | "==" -> toInt (l == r)
        | "!=" -> toInt (l <> r)
        | "<=" -> toInt (l <= r)
        | "<"  -> toInt (l < r)
        | ">=" -> toInt (l >= r)
        | ">" -> toInt (l > r)
        | _ -> failwith (Printf.sprintf "Undefined operation %s" op)

    let rec eval s e = match e with
        | Const v -> v
        | Var x -> s x
        | Binop (op, el, er) -> applyBinOp op (eval s el) (eval s er)

    (* Expression parser. You can use the following terminals:

         IDENT   --- a non-empty identifier a-zA-Z[a-zA-Z0-9_]* as a string
         DECIMAL --- a decimal constant [0-9]+ as a string

    *)
    ostap (
        expr:
        !(Util.expr
            (fun x -> x)
            [|
                `Lefta, [
                    ostap ("!!"), (fun x y -> Binop("!!", x, y))
                ];
                `Lefta, [
                    ostap ("&&"), (fun x y -> Binop("&&", x, y))
                ];
                `Nona, [
                    ostap ("=="), (fun x y -> Binop("==", x, y));
                    ostap ("!="), (fun x y -> Binop("!=", x, y));
                    ostap ("<="), (fun x y -> Binop("<=", x, y));
                    ostap ("<"),  (fun x y -> Binop("<", x, y));
                    ostap (">="), (fun x y -> Binop(">=", x, y));
                    ostap (">"),  (fun x y -> Binop(">", x, y))
                ];
                `Lefta, [
                    ostap ("+"),  (fun x y -> Binop("+", x, y));
                    ostap ("-"),  (fun x y -> Binop("-", x, y))
                ];
                `Lefta , [
                    ostap ("*"),  (fun x y -> Binop("*", x, y));
                    ostap ("/"),  (fun x y -> Binop("/", x, y));
                    ostap ("%"),  (fun x y -> Binop("%", x, y))
                 ]
            |]
            primary
        );

      primary: x:IDENT {Var x} | n:DECIMAL {Const n} | -"(" expr -")"
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
    (* loop with a post-condition       *) | Repeat of Expr.t * t  with show

    (* The type of configuration: a state, an input stream, an output stream *)
    type config = Expr.state * int list * int list

    (* Statement evaluator

         val eval : config -> t -> config

       Takes a configuration and a statement, and returns another configuration
    *)
    let rec eval c st = match c, st with
        | (s, z :: zs, o), Read x -> ((Expr.update x z s), zs, o)
        | _, Read x -> failwith (Printf.sprintf "No input")
        | (s, i, o), Write e -> (s, i, o @ [Expr.eval s e])
        | (s, i, o), Assign (x, e) -> ((Expr.update x (Expr.eval s e) s), i, o)
        | ca, Seq (ta, tb) -> eval (eval ca ta) tb
        | ca, Skip -> ca
        | (s, i, o), If (cond, bt, bf) ->
            if (Expr.eval s cond) <> 0
            then eval (s, i ,o) bt
            else eval (s, i ,o) bf
        | (s, i, o), While (cond, bd) ->
            if (Expr.eval s cond) <> 0
            then eval (s, i, o) (Seq(bd, While (cond, bd)))
            else (s, i, o)
        | (s, i, o), Repeat (cond, bd) ->
            let (s', i', o') = eval (s, i, o) bd in
            if (Expr.eval s' cond) <> 0
            then (s', i', o')
            else eval (s', i', o') (Repeat (cond, bd))

    (* Statement parser *)
    ostap (
       stmt:
           x :IDENT ":=" e:!(Expr.expr) {Assign (x, e)}
           | "read" "(" x:IDENT ")" {Read x}
           | "write" "(" e:!(Expr.expr) ")" {Write e}
           | "skip" {Skip}
           | "while" cond:!(Expr.expr) "do" bd:stmt "od" {While (cond, bd)}
           | "for" init:stmt "," cond:!(Expr.expr) "," it:stmt "do" bd:stmt "od" {Seq (init, While (cond, Seq (bd, it)))}
           | "repeat" bd:stmt "until" cond:!(Expr.expr) {Repeat (cond, bd)}
           | "if" cond:!(Expr.expr) "then" bt:stmt "fi" {If (cond, bt, Skip)}
           | "if" cond:!(Expr.expr) "then" bt:stmt "elif" elif:elseif "fi" {If (cond, bt, elif)}
           | "if" cond:!(Expr.expr) "then" bt:stmt "else" bf:stmt "fi" {If (cond, bt, bf)};
       elseif:
           cond:!(Expr.expr) "then" bt:stmt "elif" elif:elseif {If (cond, bt, elif)}
           | cond:!(Expr.expr) "then" bt:stmt "else" bf:stmt {If (cond, bt, bf)}
           | cond:!(Expr.expr) "then" bt:stmt {If (cond, bt, Skip)};


       parse: <s::ss> : !(Util.listBy)[ostap (";")][stmt] {List.fold_left (fun s ss -> Seq (s, ss)) s ss}
   )

  end

(* The top-level definitions *)

(* The top-level syntax category is statement *)
type t = Stmt.t

(* Top-level evaluator

     eval : t -> int list -> int list

   Takes a program and its input stream, and returns the output stream
*)
let eval p i =
  let _, _, o = Stmt.eval (Expr.empty, i, []) p in o

(* Top-level parser *)
let parse = Stmt.parse