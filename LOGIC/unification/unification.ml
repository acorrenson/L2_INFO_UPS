(* ============================================ *)
(* = Unification algorithm                    = *)
(* = Arthur Correnson                         = *)
(* ============================================ *)


(* ============================================ *)
(* = Types                                    = *)
(* ============================================ *)

(** Type for terms *)
type term =
  | Var of string
  | Function of string * term list

(** Shortcut to declare constants *)
let const s = Function(String.uppercase_ascii s, [])

(** Monadic result *)
type 'a result =
  | Failure
  | Success of 'a

(** Result propagation *)
let (>>=) a f =
  match a with
  | Success x -> f x
  | Failure -> Failure

(** Decision *)
let (|=) b v = if b then Success (v ()) else Failure


(* ============================================ *)
(* = Utils                                    = *)
(* ============================================ *)

(** Module for variable Set *)
module VarSet = Set.Make(String)

(** Extract the set of free variables in a term *)
let rec fv t =
  match t with
  | Var x -> VarSet.add x VarSet.empty
  | Function (_, l) -> List.fold_right (fun t a -> VarSet.union a (fv t)) l VarSet.empty

(** Ensure that a set does'nt include a variable *)
let not_in x s =
  match (VarSet.find_opt x s) with
  | Some x -> false
  | None -> true

(** Substitute a term to a variable in a term *)
let rec substitute x y t =
  match t with
  | Var v when v = x -> y
  | Function (n, l) -> Function(n, List.map (substitute x y) l)
  | _ -> t

(** perform subsitution on a list of pairs *)
let substitute_pairs x y l =
  List.map (fun (a, b) -> substitute x y a, substitute x y b) l


(* ============================================ *)
(* = Unification Algorithm                    = *)
(* ============================================ *)

(** Decomposition rule *)
let rule_decompose lt1 lt2 e s =
  (List.map2 (fun t1 t2 -> (t1, t2)) lt1 lt2)@e, s

(** Elimination rule *)
let rule_eliminate x t e s =
  let s' = (Var x, t)::(substitute_pairs x t s)
  and e' = substitute_pairs x t e in
  (e', s')

(** Find a unification rule and apply it to the pair (Equations, Solution) *)
let find_rule (e, s) =
  match e with
  (* Delete *)
  | (t1, t2)::e' when t1 = t2 -> Success (e', s)
  (* Decompose/Clash *)
  | (Function (x, lt1), Function (y, lt2))::e' ->
    (x = y && (List.length lt1 = List.length lt2))
    |= (fun () -> rule_decompose lt1 lt2 e' s)
  (* Elim/Check *)
  | (Var x, t)::e' ->
    (t <> (Var x) && not_in x (fv t))
    |= (fun () -> rule_eliminate x t e' s)
  (* Orient *)
  | (t, Var x)::e' -> Success ((Var x, t)::e', s)
  (* Done *)
  | [] -> Success ([], s)

(** Resolve a list of term equations using unification *)
let unify u =
  let rec step = function
    | ([], s) -> Success(s)
    | p -> (find_rule p) >>= step
  in
  step (u, [])


(* ============================================ *)
(* = Pretty Printing                          = *)
(* ============================================ *)

(** Term to string conversion *)
let rec string_of_term t =
  match t with
  | Var x -> String.lowercase_ascii x
  | Function (x, []) -> String.uppercase_ascii x
  | Function (s, l) ->
    let rev = List.rev l in
    let lst = List.hd rev in
    let beg = List.tl rev |> List.rev in
    s
    ^ "("
    ^ (List.fold_left (fun a t -> a ^ (string_of_term t) ^ ", ") "" beg)
    ^ (string_of_term lst) ^ ")"

(** Print a solution *)
let print_sol (t1, t2) =
  print_endline ((string_of_term t1) ^ " = " ^(string_of_term t2))

(** Print an equation *)
let print_eq (t1, t2) =
  print_endline ((string_of_term t1) ^ " =? " ^(string_of_term t2))

let print_sols l = 
  match l with
  | Success s -> List.iter print_sol s
  | Failure -> print_endline "Impossible unification"

(* ============================================ *)
(* = Test                                     = *)
(* ============================================ *)

(* Test 1 *)
let _ =
  let t1 = Function("f", [Function("g", [Var "x"])]) in
  let t2 = Function("f", [Var "y"]) in
  let e1 = (t1, t2) in
  let e2 = (Var "x", const "z") in
  let el = [e2; e1] in
  let r = unify el in
  print_endline "=================";
  print_endline "Trying to unify :";
  List.iter print_eq el;
  print_endline "=================";
  print_sols r;
  print_newline ()

(* Test 2 *)
let _ =
  let t1 = Function("g", [Function("g", [Var "x"])]) in
  let t2 = Function("f", [Var "y"]) in
  let e1 = (t1, t2) in
  let el = [e1] in
  let r = unify el in
  print_endline "=================";
  print_endline "Trying to unify :";
  List.iter print_eq el;
  print_endline "=================";
  print_sols r;
  print_newline ()

(* Test 3 *)
let _ =
  let t1 = Function("f", [Function("g", [Var "x"; Var "y"])]) in
  let t2 = Function("f", [Function("g", [Var "y"; const "z"])]) in
  let e1 = (t1, t2) in
  let el = [e1] in
  let r = unify el in
  print_endline "=================";
  print_endline "Trying to unify :";
  List.iter print_eq el;
  print_endline "=================";
  print_sols r;
  print_newline ()

(* Test 4 *)
let _ =
  let e1 = (Var "x", Var "y") in
  let e2 = (Var "y", Var "z") in
  let e3 = (Var "x", const "c") in
  let el = [e1; e2; e3] in
  let r = unify el in
  print_endline "=================";
  print_endline "Trying to unify :";
  List.iter print_eq el;
  print_endline "=================";
  print_sols r;
  print_newline ()

(* Test 5 *)
let _ =
  let e1 = (Var "x", Var "y") in
  let e2 = (Var "y", const "d") in
  let e3 = (Var "x", const "c") in
  let el = [e1; e2; e3] in
  let r = unify el in
  print_endline "=================";
  print_endline "Trying to unify :";
  List.iter print_eq el;
  print_endline "=================";
  print_sols r;
  print_newline ()

let _ =
  let f1 = Function("g", [Var "Y"; Function("g", [ Function ("f", [Var "X"]); Var "Z"])]) in
  let f2 = Function("g", [Function("g", [ Function ("f", [Var "X"]); Function ("f", [const "a"])]); Var "Y" ]) in
  let el = [f1, f2] in
  let r = unify el in
  print_endline "=================";
  print_endline "Trying to unify :";
  List.iter print_eq el;
  print_endline "=================";
  print_sols r;
  print_newline ()