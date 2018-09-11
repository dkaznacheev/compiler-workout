open GT       
       
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
type config = int list * Syntax.Stmt.config

let bigStep conf i = match conf, i with
    | (l, c), CONST n -> (n :: l, c)
    | (l, (s, z :: zs, o)), READ -> (z :: l, (s, zs, o))
    | _, READ -> failwith "No input"
    | (z :: zs, (s, i, o)), WRITE -> (zs, (s, i, o @ [z]))
    | _, WRITE -> failwith "Trying to write from empty stack"
    | (l, (s, i, o)), LD x -> ((s x) :: l, (s, i, o))
    | (z :: zs, (s, i, o)), ST x -> (zs, (Syntax.Expr.update x z s, i, o))
    | _, ST _ ->  failwith "Trying to store from empty stack"
    | (y :: x :: zs, (s, i, o)), BINOP op -> ((Syntax.Expr.applyBinOp op x y) :: zs, (s, i, o))
    | (z :: zs, _), BINOP _ -> failwith "Trying to binop with one element stack"
    | _, BINOP _ -> failwith "Trying to binop with empty stack"

(* Stack machine interpreter

     val eval : config -> prg -> config

   Takes a configuration and a program, and returns a configuration as a result
 *)                         
let eval = List.fold_left bigStep

(* Top-level evaluation

     val run : int list -> prg -> int list

   Takes an input stream, a program, and returns an output stream this program calculates
*)
let run i p = let (_, (_, _, o)) = eval ([], (Syntax.Expr.empty, i, [])) p in o

(* Stack machine expression compiler

     val compile : Syntax.Expr.t -> prg

   Takes an expression in the source language and returns an equivalent program for the
   stack machine
 *)
let rec compileExpr e = match e with
    | Syntax.Expr.Const n -> [CONST n]
    | Syntax.Expr.Var x -> [LD x]
    | Syntax.Expr.Binop (op, a, b) -> (compileExpr a) @ (compileExpr b) @ [BINOP op]

(* Stack machine compiler

     val compile : Syntax.Stmt.t -> prg

   Takes a program in the source language and returns an equivalent program for the
   stack machine
 *)
let rec compile t = match t with
    | Syntax.Stmt.Assign (x, e) -> (compileExpr e) @ [ST x]
    | Syntax.Stmt.Read x -> READ :: [ST x]
    | Syntax.Stmt.Write e -> (compileExpr e) @ [WRITE]
    | Syntax.Stmt.Seq (ta, tb) -> (compile ta) @ (compile tb)  





