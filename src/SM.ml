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
(* store a variable from the stack *) | ST    of string
(* a label                         *) | LABEL of string
(* unconditional jump              *) | JMP   of string
(* conditional jump                *) | CJMP  of string * string with show

(* The type for the stack machine program *)
type prg = insn list

(* The type for the stack machine configuration: a stack and a configuration from statement
   interpreter
 *)
type config = int list * Stmt.config

(* Stack machine interpreter
     val eval : env -> config -> prg -> config
   Takes an environment, a configuration and a program, and returns a configuration as a result. The
   environment is used to locate a label to jump to (via method env#labeled <label_name>)
*)
let rec eval env conf prg = match prg with
    | [] -> conf
    | i :: ps -> (match conf, i with
        | (l, c), CONST n -> eval env (n :: l, c) ps
        | (l, (s, z :: zs, o)), READ -> eval env (z :: l, (s, zs, o)) ps
        | _, READ -> failwith "No input"
        | (z :: zs, (s, i, o)), WRITE -> eval env (zs, (s, i, o @ [z])) ps
        | _, WRITE -> failwith "Trying to write from empty stack"
        | (l, (s, i, o)), LD x -> eval env ((s x) :: l, (s, i, o)) ps
        | (z :: zs, (s, i, o)), ST x -> eval env (zs, (Language.Expr.update x z s, i, o)) ps
        | _, ST _ ->  failwith "Trying to store from empty stack"
        | (y :: x :: zs, (s, i, o)), BINOP op -> eval env ((Language.Expr.applyBinOp op x y) :: zs, (s, i, o)) ps
        | (z :: zs, _), BINOP _ -> failwith "Trying to binop with one element stack"
        | _, BINOP _ -> failwith "Trying to binop with empty stack"
        | c, LABEL l -> eval env c ps
        | c, JMP l -> eval env c (env#labeled l)
        | ([], (s, i, o)), CJMP (cond, l) -> conf
        | (z :: zs, (s, i, o)), CJMP (cond, l) ->
            if ((cond = "z") = (z = 0))
            then eval env conf (env#labeled l)
            else eval env conf ps
        | _ -> failwith "Impossible instruction"
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
  let (_, (_, _, o)) = eval (object method labeled l = M.find l m end) ([], (Expr.empty, i, [])) p in o

(* Stack machine compiler

     val compile : Language.Stmt.t -> prg

   Takes a program in the source language and returns an equivalent program for the
   stack machine
*)
let gen_label n = Printf.sprintf "L%d" n

let rec compile' n =
  let rec expr = function
  | Expr.Var   x          -> [LD x]
  | Expr.Const n          -> [CONST n]
  | Expr.Binop (op, x, y) -> expr x @ expr y @ [BINOP op]
  in
  function
  | Stmt.Seq (s1, s2)  -> let p1, m = compile' n s1 in
                          let p2, k = compile' m s2 in
                          p1 @ p2, k
  | Stmt.Read x        -> [READ; ST x], n
  | Stmt.Write e       -> expr e @ [WRITE], n
  | Stmt.Assign (x, e) -> expr e @ [ST x], n
  | Stmt.Skip -> [], n
  | Stmt.If (cond, bt, bf) -> let pt, m = compile' (n + 1) bt in
                              let pf, k = compile' (m + 1) bf in
                              (expr cond) @
                              [CJMP ("z", gen_label n)] @
                              pt @
                              [JMP (gen_label m)] @
                              [LABEL (gen_label n)] @
                              pf @
                              [JMP (gen_label m)] @
                              [LABEL (gen_label m)], k
  | Stmt.While (cond, bd) -> let pb, m = compile' (n + 2) bd in
                             [LABEL (gen_label n)] @
                             expr cond @
                             [CJMP ("z", (gen_label (n + 1)))] @
                             pb @
                             [JMP (gen_label n)] @
                             [LABEL (gen_label (n + 1))], m
 | Stmt.Repeat (cond, bd) -> let pb, m = compile' (n + 1) bd in
                             [LABEL (gen_label n)] @
                             pb @
                             expr cond @
                             [CJMP ("z", (gen_label n))], m

 let compile st = let res, _ = compile' 0 st in res
