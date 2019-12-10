(* ========================== *)
(* Exercice 12 du test CT     *)
(* Base de données de vols    *)
(* ========================== *)

Variable Aeroport : Set.
Variable tls : Aeroport.
Variable cdg : Aeroport.
Variable led : Aeroport.
Variable fra : Aeroport.
Variable ory : Aeroport.
Variable V : Aeroport -> Aeroport -> Prop.

(* Axiom 1 *)
(* Si il existe un vol de x à y et de y à z alors il exsite un vol de x à z *)
Axiom transitivite:
  forall x y z, V x y -> V y z -> V x z.

Axiom tls_cdg: V tls cdg. (* Il existe un vol de tls à cdg *)
Axiom tls_ory: V tls ory. (* Il existe un vol de tls à ory *)
Axiom cdg_fra: V cdg fra. (* Il existe un vol de cdg à fra *)
Axiom fra_led: V fra led. (* Il existe un vol de dra à led *)

Lemma vol_tls_led:
  V tls  led.
Proof.
  apply transitivite with (y := cdg).
  - apply tls_cdg.
  - apply transitivite with (y := fra).
    * apply cdg_fra.
    * apply fra_led.
Qed.
