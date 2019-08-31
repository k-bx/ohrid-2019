Require Import Arith ZArith List Bool.

(* Give a statement expressed solely with natural number operations (essentially
  multiplication) and logical connectives, expressing that the square root of a number
  that is not a perfect square is always irrational. *)
Check forall n, (~ exists k, n = k * k) ->
   forall p q, q <> 0 -> (q * q) * n <> p * p.

(* write a specification spec_f_id_when_p for a function f : nat -> nat, and a boolean
  predicate p : nat -> bool stating
  that for every number n, f n = n when p n is true.  Don't use an if-then-else
  statement.  The function spec_f_id_when_p should have the type
  (nat -> nat) -> (nat -> bool) -> Prop *)

Definition spec_f_id_when_p (f : nat -> nat) (p : nat -> bool) : Prop :=
      (forall n, p n = true -> f n = n).

(* write a specification spec_f_id_when_p2, expressing the same thing as above,
  but using an if-then-else statement. *)

Definition spec_f_id_when_p2 (f : nat -> nat) (p : nat -> bool) : Prop :=
      forall n, if p n then f n = n else True.

(* As a later exercise, we will have to show that the two specifications
  are equivalent. Give the logical statement that expresses this equivalence. *)

Check forall f p, spec_f_id_when_p f p <-> spec_f_id_when_p2 f p.

(* answer to the later exercise. *)

Lemma ensure_spec_f_id_when_p_same:
  forall f p, spec_f_id_when_p f p <-> spec_f_id_when_p2 f p.
Proof.
intros f p.
now split; intros h n; generalize (h n); destruct (p n) eqn:vpn; auto.
Qed.

(* Write an inductive predicate on list A, for an arbitrary A (where
   equality is not necessarily decidable), to express that a list
   of elements of A is a palindrome. Make A an implicit argument. *)

Inductive palindrome {A : Type} : list A -> Prop :=
  pal0 : palindrome nil
| pal1 x : palindrome (x :: nil)
| pal_step x l : palindrome l -> palindrome (x :: l ++ x :: nil).

(* advanced exercise (related to cnv3).  Write a logical statement expressing
  that a list of pairs is the convolute of two lists
  a_1, ..., a_n  and b_1, ..., b_m, when n = m.  This convolute is
  (a_1, b_n) (a_2, b_{n-1}) ... (a_n, b1).  You can use the pre-existing
  functions over lists length and nth. *)

Definition convolute_prop {A B : Type} (eA : A) (eB : B)
  (l1 : list A) (l2 : list B) (l : list (A * B)) :=
  length l1 = length l2 -> 
  length l = length l1 /\
  forall i, i <= length l1 ->
    nth i l (eA, eB) = (nth i l1 eA, nth (length l1 - S i) l2 eB).

