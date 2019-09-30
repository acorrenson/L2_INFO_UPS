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

Notation "a + b" := (plus a b).

(* --------------------- *)
(* -- Multiplication --- *)
(* --------------------- *)

Fixpoint mult(n m:nat) : nat :=
  match n with
  | O => O
  | S n => plus m (mult n m)
  end.

Notation "a * b" := (mult a b).

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


Lemma mult_distrib_plus :
  forall l a b : nat, mult l (plus a b) = plus (mult l a) (mult l b).
Proof. 
  intros . 
  induction l. 
  - simpl. reflexivity. 
  - replace (S l * a) with (l * a + a).
    replace (S l * b) with (l * b + b).
    replace (l*a + a + (l*b + b)) with (l*a + l*b + a + b). 
    rewrite <- IHl.
    simpl. rewrite commut_plus. 
    rewrite -> assoc_plus. reflexivity.  

    (* Justification for replace 1 *)
    * rewrite <- assoc_plus. 
      replace (l*a + l*b + a) with (l*a + a + l*b).
      reflexivity. 
      replace (l*a + l*b) with (l*b + l*a). 
      rewrite -> assoc_plus. 
      replace (a + l*b) with (l*b + a).
      rewrite <- assoc_plus. 
      replace (l*a + l*b) with (l*b + l*a). 
      reflexivity. 
      rewrite -> commut_plus.       
      reflexivity. 
      rewrite -> commut_plus.
      reflexivity. 
      rewrite -> commut_plus.
      reflexivity. 

    (* Justification for replace 2 *)
    * simpl. 
      rewrite -> commut_plus. 
      reflexivity. 

    (* Justification for replace 3 *)
    * simpl. 
      rewrite -> commut_plus. 
      reflexivity.
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

Lemma plus_n_m_o :
  forall n m : nat, plus n m = O -> m = O.
Proof. 
  intros.
  induction n. 
  - rewrite <- H. simpl. reflexivity. 
  - discriminate. 
Qed.


Lemma plus_a_b_a_c : 
  forall a b c: nat, plus a b = plus a c -> b = c.
Proof. 
  intros .  
  induction a. 
  - replace (plus O b) with b in H.
    replace (plus O c) with c in H. 
    apply H.
    auto.
    auto. 
  - replace (plus (S a) b) with (S (plus a b)) in H. 
    replace (plus (S a) c) with (S (plus a c)) in H.
    injection H.
    auto. 
    simpl. reflexivity. 
    simpl. reflexivity. 
Qed.


(* Antisymetry *)
Lemma antisym_le:
  forall a b : nat, le a b -> le b a -> a = b.
Proof. 
  intros . 
  unfold le in  H, H0. 
  elim H. 
  elim H0. 
  intros . 
  rewrite <- H1 in H2.
  rewrite assoc_plus in H2.
  rewrite -> plus_n_m_o in H2. 

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