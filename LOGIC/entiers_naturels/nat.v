Inductive nat : Set :=
  | O : nat
  | S : nat -> nat.


(* Minimalistic version of addition *)
Fixpoint plus (n m:nat) : nat :=
  match n with
  | O   => m
  | S n => S (plus n m)
  end.


(* Multiplication *)
Fixpoint mult(n m:nat) : nat :=
  match n with
  | O => O
  | S n => plus m (mult n m)
  end.


Eval compute in (plus (S O) (S O)).
Eval compute in (mult (S (S O)) (S (S O))).