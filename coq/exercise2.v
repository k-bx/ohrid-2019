Require Import Arith ZArith List Bool.

(* Give a statement expressed solely with natural number operations (essentially
  multiplication) and logical connectives, expressing that the square root of a number
  that is not a perfect square is always irrational. *)

(* write a specification spec_f_id_when_p for a function f : nat -> nat, and a boolean
  predicate p : nat -> bool stating
  that for every number n, f n = n when p n is true.  Don't use an if-then-else
  statement.  The function spec_f_id_when_p should have the type
  (nat -> nat) -> (nat -> bool) -> Prop *)

(* write a specification spec_f_id_when_p2, expressing the same thing as above,
  but using an if-then-else statement. *)

(* As a later exercise, we will have to show that the two specifications
  are equivalent. Give the logical statement that expresses this equivalence. *)


(* Write an inductive predicate on list A, for an arbitrary A (where
   equality is not necessarily decidable), to express that a list
   of elements of A is a palindrome. Make A an implicit argument. *)

(* advanced exercise (related to cnv3).  Write a logical statement expressing
  that a list of pairs is the convolute of two lists
  a_1, ..., a_n  and b_1, ..., b_m, when n = m.  This convolute is
  (a_1, b_n) (a_2, b_{n-1}) ... (a_n, b1).  You can use the pre-existing
  functions over lists length and nth. *)


