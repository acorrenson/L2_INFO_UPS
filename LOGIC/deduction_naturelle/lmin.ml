(* ----------------------------- *)
(* -- Mini utilitaire pour la -- *)
(* -- deduction naturelle.    -- *)
(* ----------------------------- *)

type form =
  | Prop of char
  | Impl of form * form
(** formules de la logique minimale *)


(** Notation infixe pour l'implication *)
let ( **> )  a b  = Impl (a, b)


(** Erreur d'application de règle de déduction *)
exception Rule_fail


(**
 * Règle de l'axiome
 *)
let axiome h a =
  try List.find ((=) a) h
  with Not_found -> raise Rule_fail


(**
 * Règle du modus ponens ou "Elimintation de l'implication" 
 *)
let modus_ponens ctx =
  match ctx with
  | Impl (a, b) :: c :: [] when c = a ->
    b
  | c :: Impl (a, b) :: [] when c = a ->
    b
  | _ -> raise Rule_fail


(** Affichage  *)
let rec pprint f =
  match f with
  | Prop c -> print_char c
  | Impl (a, b) -> 
    print_char '(';
    pprint a;
    print_string "->";
    pprint b;
    print_char ')'

(** Affichage mutiple *)
let pprint_set h =
  List.iter (fun x -> pprint x; print_char ' ') h

let ctx = [(Prop 'a') **> (Prop 'b'); (Prop 'a')]
let _ =
    List.iter (fun x -> pprint x; print_char ' ') ctx |> print_newline;
    modus_ponens [(Prop 'a') **> (Prop 'b'); Prop 'a']
  |> pprint
  |> print_newline


