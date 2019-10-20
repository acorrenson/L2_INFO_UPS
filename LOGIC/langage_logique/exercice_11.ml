(* Implementation en OCAML  *)
(* de l'exercice 11 du TD   *)
(* de logique.              *)


(** Definition inductive des expressions de la logique propositionnelle *)
type expr =
  | Atom of string
  | Bottom
  | Top
  | Not   of expr
  | And   of expr * expr
  | Or    of expr * expr
  | Impl  of expr * expr


(** Retrait des implications dans une formule *)
let rec nf e =
  match e with
  | Not a -> 
    Not (nf a)
  | And (a, b) ->
    And (nf a, nf b)
  | Or  (a, b) ->
    Or (nf a, nf b)
  | Impl (a, b) ->
    Or (Not (nf a), nf b)
  | _ -> e


(** Affichage  *)
let rec pprint e =
  match e with
  | Atom s ->
    print_string s 
  | Bottom ->
    print_string "⟘"
  | Top -> 
    print_string "⟙"
  | Not (Atom s) ->
    print_string "¬";
    print_string s
  | Not Top ->
    print_string "¬";
    print_string "⟙"
  | Not Bottom ->
    print_string "¬";
    print_string "⟘"
  | Not (Not a) ->
    print_string "¬¬";
    pprint a
  | Not a ->
    print_string "¬(";
    pprint a;
    print_string ")"
  | And (a , b) ->
    print_string "("; 
    pprint a;
    print_string " ∧ ";
    pprint b;
    print_string ")"
  | Or (a, b) ->
    print_string "(";
    pprint a;
    print_string " ∨ ";
    pprint b;
    print_string ")" 
  | Impl (a, b) ->
    print_string "("; 
    pprint a;
    print_string " -> ";
    pprint b;
    print_string ")"


let _ =
  let p = Atom "p" in
  let q = Atom "q" in
  let r = Atom "r" in
  let s = Atom "s" in
  let form = Impl (Impl (Not p, q), And (r, s)) in
  pprint form;
  print_newline ();
  pprint (nf form)
