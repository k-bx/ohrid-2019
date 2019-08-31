Require Import Arith List Bool.

(* using pattern matching, define a function next3 that maps
   0 to 1
   1 to 2
   any number larger than 2 to 0 *)

Definition next3 (n : nat) :=
  match n with 0 => 1 | 1 => 2 | _ => 0 end.

(* Define a function sumf that takes f : nat -> nat and n : nat as arguments
  and returns f 0 + f 1 + ... + f n *)

Fixpoint sumf (f : nat -> nat) (n : nat) :=
  match n with 0 => f 0 | S p => sumf f p + f p end.

(* Define a function eiseinstein that takes as input a list of numbers
 (a_1 ... a_k) and returns as output the list
 (a_1 (a_1 + a_2) a_2 (a_2 + a_3) a_3 ... ).  This function will be used
 in later exercises. *)

Fixpoint eisenstein (l : list nat) : list nat :=
  match l with
  | a :: l' =>
     match l' with
       b :: _ =>  a :: (a + b) :: eisenstein l'
     | _ => l
     end
  | _ => l
  end.

(* Write a function iterates that takes an arbitrary type A,
  a function f : A -> A,
  a number n : nat, and and element a : A and returns the list
  a (f a)  (f (f a)) ...  of length n. *)

Fixpoint iterates {A : Type} (f : A -> A) (n : nat) (a : A) :=
  match n with 0 => nil | S p => a :: map f (iterates f p a) end.

(* By computing the list containing all the iterated values of next3
   from 1 up to next3 ^ n, and then counting the number of 0 in this list,
   one can compute n / 3.  Use function count_occ and Nat.eq_dec from
   library Arith to perform this computation.  Name the resulting
   function div3. *)

Definition div3 (n : nat) : nat :=
  count_occ Nat.eq_dec (iterates next3 n 1) 0.

(* write a function adjacent which takes two natural numbers
   a and b and a l : list nat and returns true exactly when
   the list l contains a and b in adjacent position and in this
   order. *)

Fixpoint adjacent (a b : nat) (l : list nat) :=
  match l with
  | a :: (b :: _ as l') => if Nat.eq_dec a b then true else adjacent a b l'
  | _ => false
  end.
  
(* Define a function zip that takes as input two lists and returns the
   list of pairs of elements at the same rank in these lists. 
   if the first list is (a_1 ... a_k) and the second list is (b_1 ... b_l)
   and m = min k l, it should return
   (a_1, b_1) (a_2, b_2) ... (a_m, b_m) *)

Fixpoint zip {A B : Type} (l1 : list A) (l2 : list B) : list (A * B) :=
   match l1, l2 with
   | a :: l1', b :: l2'  => (a, b) :: zip l1' l2'
   | _, _ => nil
   end.

(* using the function zip, rev, Nat.eqb, and forallb, define a function that
  takes a list of natural numbers as arguments and checks that this list
  is a palindrome (it is equal to its reverse). *)

Definition palindrome (l : list nat) :=
  forallb (fun '(x, y) => Nat.eqb x y) (zip l (rev l)).

(* advanced exercise (borrowed from Ilya Sergey's course on Coq. *)
(* implement the function cnv3 from
   https://www.brics.dk/RS/05/3/BRICS-RS-05-3.pdf *)
   