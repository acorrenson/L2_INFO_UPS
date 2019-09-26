(* --------------------- *)
(* -- Inductive Nat ---- *)
(* --------------------- *)

Inductive nat : Set :=
  | O : nat
  | S : nat -> nat.


(* --------------------- *)
(* ----- Addition ------ *)
(* --------------------- *)

Fixpoint plus (n m:nat) : nat :=
  match n with
  | O   => m
  | S n => S (plus n m)
  end.


(* --------------------- *)
(* -- Multiplication --- *)
(* --------------------- *)

Fixpoint mult(n m:nat) : nat :=
  match n with
  | O => O
  | S n => plus m (mult n m)
  end.


(* --------------------- *)
(* --- Modulo 2 -------- *)
(* --------------------- *)

Fixpoint mod2(n:nat) : nat :=
  match n with
  | O   => O
  | S p =>  match p with
            | O => S O
            | S q => mod2 q
            end

  end.


(* --------------------- *)
(* ------- TESTS ------- *)
(* --------------------- *)

(* Should outputs (S (S O)) *)
Eval compute in (plus (S O) (S O)).

(* Should outputs (S (S (S (S O)))) *)
Eval compute in (mult (S (S O)) (S (S O))).

(* Should outputs O *)
Eval compute in (mod2 (S (S (S (S O))))).

(* Should outputs S O *)
Eval compute in (mod2 (S (S (S O)))).

(* Should outputs O *)
Eval compute in (mod2 ((S O))).
