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
  | S p => S (plus p m)
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
(* -Plus is commutative- *)
(* --------------------- *)


(* Usefull Lemma 1 *)
Lemma plus_n_o : 
  forall n : nat, plus n O = n.
Proof.
  intros. 
  induction n. 
  - simpl. reflexivity. 
  - simpl. rewrite -> IHn. reflexivity. 
Qed.


(* Usefull Lemma 2 *)
Lemma plus_n_Sm :
  forall n m : nat, plus n (S m) = S(plus n m).
Proof.
  intros.
  induction n. 
  - simpl. reflexivity. 
  - simpl. rewrite -> IHn. reflexivity.
Qed.


(* Final Lemma : plus is commutative *)
Lemma commut_plus : 
  forall n m : nat, plus n m = plus m n.
Proof.
  intros. 
  induction m. 
  - simpl. rewrite -> plus_n_o. reflexivity. 
  - simpl. rewrite <- IHm. apply plus_n_Sm.
Qed.


(* --------------------- *)
(* -Plus is Associative- *)
(* --------------------- *)

Lemma assoc_plus :
  forall n p q : nat, plus (plus n p) q = (plus n (plus p q)).
Proof. 
  intros. 
  induction n.
  - simpl. reflexivity.
  - simpl. rewrite IHn. reflexivity.
Qed.


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