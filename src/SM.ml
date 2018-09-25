open GT       
open Language
open Language.Expr
open Language.Stmt

(* The type for the stack machine instructions *)
@type insn =
(* binary operator                 *) | BINOP of string
(* put a constant on the stack     *) | CONST of int                 
(* read to stack                   *) | READ
(* write from stack                *) | WRITE
(* load a variable to the stack    *) | LD    of string
(* store a variable from the stack *) | ST    of string with show

(* The type for the stack machine program *)                                                               
type prg = insn list

(* The type for the stack machine configuration: a stack and a configuration from statement
   interpreter
 *)
type config = int list * Stmt.config

let bigStep conf i = match conf, i with
    | (l, c), CONST n -> (n :: l, c)
    | (l, (s, z :: zs, o)), READ -> (z :: l, (s, zs, o))
    | _, READ -> failwith "No input"
    | (z :: zs, (s, i, o)), WRITE -> (zs, (s, i, o @ [z]))
    | _, WRITE -> failwith "Trying to write from empty stack"
    | (l, (s, i, o)), LD x -> ((s x) :: l, (s, i, o))
    | (z :: zs, (s, i, o)), ST x -> (zs, (Language.Expr.update x z s, i, o))
    | _, ST _ ->  failwith "Trying to store from empty stack"
    | (y :: x :: zs, (s, i, o)), BINOP op -> ((Language.Expr.applyBinOp op x y) :: zs, (s, i, o))
    | (z :: zs, _), BINOP _ -> failwith "Trying to binop with one element stack"
    | _, BINOP _ -> failwith "Trying to binop with empty stack"

(* Stack machine interpreter
     val eval : config -> prg -> config
   Takes a configuration and a program, and returns a configuration as a result
 *)                         
let eval = List.fold_left bigStep
(* Top-level evaluation

     val run : prg -> int list -> int list

   Takes a program, an input stream, and returns an output stream this program calculates
*)
let run p i = let (_, (_, _, o)) = eval ([], (Expr.empty, i, [])) p in o

(* Stack machine compiler

     val compile : Language.Stmt.t -> prg

   Takes a program in the source language and returns an equivalent program for the
   stack machine
*)
let rec compile =
  let rec expr = function
  | Expr.Var   x          -> [LD x]
  | Expr.Const n          -> [CONST n]
  | Expr.Binop (op, x, y) -> expr x @ expr y @ [BINOP op]
  in
  function
  | Stmt.Seq (s1, s2)  -> compile s1 @ compile s2
  | Stmt.Read x        -> [READ; ST x]
  | Stmt.Write e       -> expr e @ [WRITE]
  | Stmt.Assign (x, e) -> expr e @ [ST x]
