open GT
open Language

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
(* conditional jump                *) | CJMP  of string * string
(* begins procedure definition     *) | BEGIN of string list * string list
(* end procedure definition        *) | END
(* calls a procedure               *) | CALL  of string with show

(* The type for the stack machine program *)
type prg = insn list

(* The type for the stack machine configuration: control stack, stack and configuration from statement
   interpreter
 *)
type config = (prg * State.t) list * int list * Stmt.config

let eval_binop op (w, y :: x :: st, c) = (w, (Language.Expr.to_func op x y) :: st, c)

let load x (w, st, (s, i, o)) = (w, (Language.State.eval s x) :: st, (s, i, o))

let store x (w, z :: st, (s, i, o)) = (w, st, (Language.State.update x z s, i, o))

let rec arg_put args c = match args with
    | [] -> c
    | (x :: xs) -> arg_put xs (store x c)

(* Stack machine interpreter

     val eval : env -> config -> prg -> config

   Takes an environment, a configuration and a program, and returns a configuration as a result. The
   environment is used to locate a label to jump to (via method env#labeled <label_name>)
*)
let rec eval env (w, st, (s, i, o)) prg = match prg with
   | [] -> (w, st, (s, i, o))
   | p :: ps -> match p with
     | CONST n -> eval env (w, n :: st, (s, i, o)) ps
     | BINOP op -> eval env (eval_binop op (w, st, (s, i, o))) ps
     | READ -> eval env (let z :: i' = i in (w, z :: st, (s, i', o))) ps
     | WRITE -> eval env (let z :: st' = st in (w, st, (s, i, o @ [z]))) ps
     | LD x  -> eval env (load x (w, st, (s, i, o))) ps
     | ST x  -> eval env (store x (w, st, (s, i, o))) ps
     | LABEL _ -> eval env (w, st, (s, i, o)) ps
     | JMP l -> eval env (w, st, (s, i, o)) (env#labeled l)
     | BEGIN (args, locl) -> let c = (w, st, (s, i, o)) in
                               let (w, st, (c, i, o)) = c in
                               let c = State.push_scope c (args @ locl) in
                                 eval env (arg_put args (w, st, (c, i, o))) ps
     | END -> (match w with
         | [] -> (w, st, (s, i, o))
         | (prg, s') :: w' -> eval env (w', st, (State.drop_scope s s', i, o)) prg)
     | CALL f -> let c = (w, st, (s, i, o)) in
                 let (w, st, (c, i, o)) = c in
                   eval env ((ps, c) :: w, st, (c, i, o)) (env#labeled f)
     | CJMP (c, l) -> let z :: st' = st in
       (if ((c = "z") && (z = 0) || (c = "nz") && (z <> 0))
        then (eval env (w, st', (s, i, o)) (env#labeled l))
        else (eval env (w, st, (s, i, o)) ps))

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
  let (_, _, (_, _, o)) = eval (object method labeled l = M.find l m end) ([], [], (State.empty, i, [])) p in o

(* Stack machine compiler

     val compile : Language.t -> prg

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
    | Stmt.Repeat (bd, cond) -> let pb, m = compile' (n + 1) bd in
                             [LABEL (gen_label n)] @
                             pb @
                             expr cond @
                             [CJMP ("z", (gen_label n))], m
    | Stmt.Call (f, l) -> List.concat (List.map expr l) @ [CALL f], n

let rec compile_fs i = function
    | [] -> [], i
    | (name, (args, locals, bd)) :: l -> let comp_bd, i = compile' i bd in
                                           let r, i = compile_fs i l in
                                               [LABEL name] @ [BEGIN (args, locals)] @ comp_bd @ [END] @ r, i

let compile (fs, p) = let defs, i = compile_fs 0 fs in
                           let p', _ = compile' i p in
                             p' @  [END] @ defs
