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
  induction n; auto.
  simpl. 
  rewrite IHn. auto. 
Qed.

(* Usefull Lemma 2 *)
Lemma plus_n_Sn :
  forall n m : nat, plus n (S m) = S(plus n m).
Proof.
  intros.
  induction n. simpl. tauto.
  simpl.  
  rewrite -> IHn. 
  tauto. 
Qed.

(* Final theorem : plus is commutative *)
Theorem commut_plus : 
  forall n m : nat, plus n m = plus m n.
Proof.
  intros. 
  induction m. simpl.
  apply plus_n_o. simpl.  
  rewrite <- IHm.
  apply plus_n_Sn.
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