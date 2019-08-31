Require Import Arith List Bool.

(* using pattern matching, define a function next3 that maps
   0 to 1
   1 to 2
   any number larger than 2 to 0 *)

(* Define a function sumf that takes f : nat -> nat and n : nat as arguments
  and returns f 0 + f 1 + ... + f n *)

(* Define a function eiseinstein that takes as input a list of numbers
 (a_1 ... a_k) and returns as output the list
 (a_1 (a_1 + a_2) a_2 (a_2 + a_3) a_3 ... ).  This function will be used
 in later exercises. *)

(* Write a function iterates that takes an arbitrary type A,
  a function f : A -> A,
  a number n : nat, and and element a : A and returns the list
  a (f a)  (f (f a)) ...  of length n. *)

(* By computing the list containing all the iterated values of next3
   from 1 up to next3 ^ n, and then counting the number of 0 in this list,
   one can compute n / 3.  Use function count_occ and Nat.eq_dec from
   library Arith to perform this computation.  Name the resulting
   function div3. *)

(* write a function adjacent which takes two natural numbers
   a and b and a l : list nat and returns true exactly when
   the list l contains a and b in adjacent position and in this
   order. *)

(* Define a function zip that takes as input two lists and returns the
   list of pairs of elements at the same rank in these lists. 
   if the first list is (a_1 ... a_k) and the second list is (b_1 ... b_l)
   and m = min k l, it should return
   (a_1, b_1) (a_2, b_2) ... (a_m, b_m) *)

(* using the function zip, rev, Nat.eqb, and forallb, define a function that
  takes a list of natural numbers as arguments and checks that this list
  is a palindrome (it is equal to its reverse). *)

(* advanced exercise (borrowed from Ilya Sergey's course on Coq. *)
(* implement the function cnv3 from
   https://www.brics.dk/RS/05/3/BRICS-RS-05-3.pdf *)
   