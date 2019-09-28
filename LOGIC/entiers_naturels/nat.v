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
(* -Mult is commutative- *)
(* --------------------- *)


(* Usefull Lemma 1 *)
Lemma mult_n_o :
  forall n : nat, mult n O = O.
Proof.
  intros. 
  induction n.
  - simpl.  reflexivity. 
  - simpl. rewrite -> IHn. reflexivity. 
Qed.


(* Usefull Lemma 2 *)
Lemma mult_n_Sm : 
  forall n m: nat, mult n (S m) = plus (mult n m) n.
Proof.
  intros . 
  induction n.
  - simpl. reflexivity. 
  - simpl. 
    rewrite assoc_plus. rewrite IHn.
    rewrite plus_n_Sm. rewrite plus_n_Sm.
    reflexivity. 
Qed.

(* Final Lemma : mult is commutative *)
Lemma commut_mult : 
  forall n m : nat, mult n m = mult m n.
Proof.
  intros . 
  induction n.
  - simpl. rewrite mult_n_o. reflexivity. 
  - simpl. rewrite -> mult_n_Sm. 
    rewrite -> IHn. rewrite -> commut_plus. reflexivity. 
Qed.


(* --------------------- *)
(* - Order relation    - *)
(* --------------------- *)

(* Less or Equal than *)
Definition le (n m : nat) := exists p : nat, plus n p = m.

(* Reflexivity *)
Lemma refl_le : 
  forall n : nat, le n n.
Proof.
  intros .
  unfold le. 
  exists O.
  rewrite -> plus_n_o. reflexivity. 
Qed.

(* Transitivity *)
Lemma trans_le:
  forall a b c : nat, le a b -> le b c -> le a c.
Proof. 
  intros . 
  unfold le. elim H0; elim H. 
  intros . 
  exists (plus x x0).
  rewrite <- assoc_plus . 
  rewrite -> H1. 
  rewrite -> H2. reflexivity. 
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