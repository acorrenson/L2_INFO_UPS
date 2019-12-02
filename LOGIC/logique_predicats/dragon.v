(* ========================== *)
(* Exercice 4 du test CT      *)
(* Une histoire de dragons ?  *)
(* ========================== *)

Variable Dragon : Set.
Variable Voler : Dragon -> Prop.
Variable Rouge : Dragon -> Prop.
Variable Heureux : Dragon -> Prop.
Variable Enfant : Dragon -> Dragon -> Prop.

(* Axiom 1 *)
(* Un dragon est heureux si tous ses enfants savent voler. *)
Axiom dragon_1:
  forall x, (forall y, Enfant y x -> Voler y) -> Heureux x.

(* Axiom 2 *)
(* Tous les dragons rouges savent voler *)
Axiom dragon_2:
  forall x, Rouge x -> Voler x.

(* Axiom 3 *)
(* Un dragon est rouge s'il est l'enfant d'au moins un dragon rouge *)
Axiom dragon_3:
  forall x, (exists y, Enfant x y /\ Rouge y) -> Rouge x.

(* Lemme *)
(* Les dragons rouges sont heureux *)
Lemma dragon_rouge_heureux:
  forall x, Rouge x -> Heureux x.
Proof.
  intros.
  apply dragon_1.
  intros.
  apply dragon_2.
  apply dragon_3.
  exists x.
  split.
  - apply H0.
  - apply H.
Qed.
