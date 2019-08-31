Require Import Arith ZArith List Psatz.

(* sum_squares *)

Fixpoint sumn2 n :=
  match n with
  | 0 => 0
  | S p => S p ^ 2 + sumn2 p
  end.

Compute 6 * sumn2 10.
Lemma sum_squares n : 6 * sumn2 n = n * (n + 1) * (2 * n + 1).
Proof.
(* please complete this proof. *)
Admitted.

(* In the following example, we still use natural number to control the
  recursion, but the arithmetic formula is actually based on integers. *)
Fixpoint sumn3 n :=
  match n with
  | 0 => 0%Z
  | S p => (Z.of_nat (S p) ^ 3 + sumn3 p)%Z
  end.

Compute sumn3 1000.
Compute (4 * sumn3 1000 - 1000 ^ 4 - 2 * 1000 ^ 3 - 1000 ^ 2)%Z.

Lemma sum_cubes n : (4 * sumn3 n = Z.of_nat n ^ 2 * (Z.of_nat n + 1) ^ 2)%Z.
Proof.
(* complete this proof. *)
Qed.

(* Second family of exercises. *)

(* One can define addition of natural numbers in (at least) three different
   ways.  One of them is displayed by function Nat.add, the function used
   by the notation "_ + _" *)

Locate "_ + _".

Print Nat.add.

(* The following alternative definition has the advantage of being
  tail recursive.  However, it is tricky to show that this function
  always returns the same result. As a big challenge, you can try addressing
  this proof without the help of the intermediate statements that I will
  suggest. *)

Fixpoint add' (x y : nat) :=
  match x with 0 => y | S x' => add' x' (S y) end.

(* Your mission is to prove the following statement:

add'_add :  forall x y, add' x y = x + y

It will be useful to use existing theorems about
Nat.add for this exercise.
*)

(* It is interesting to compare the proofs of associativity
  and commutativity for Nat.add (noted as +) and add'.
  For add', the problem is quite hard if we don't
  to prove more general facts.  Also proving add'_assoc
  will rely on add'_Sn_m as an auxiliary lemma. *)
Lemma nat_add_assoc n m p : n + (m + p) = n + m + p.
Proof.
(* redo this proof, using basically only induction,
   simpl, rewrite, and reflexivity. *)
Qed.

(* Once we have proved that add' is the same as Nat.add on all pairs
  of natural numbers, it is easy to deduce that add' is both
  associative and commutative.   Please write lemmas add'_assoc
  and add'_comm for this. *)

(* Advanced exercise about add'.  How would you prove that add'
  is associative and commutative without resorting to the equivalence
  with Nat.add ? *)

(* This lemma is quite tricky and teaches us to pay attention to
  the need to prove more general statements when performing proofs
  by induction.*)
Lemma add'_Sn_m : forall n m, add' (S n) m = S (add' n m).
Proof.
(* perform this proof. *)
Qed.

Lemma add'_assoc n m p : add' n (add' m p) = add' (add' n m) p.
Proof.
(* perform this proof, using the previous lemma. *)
Qed.

Lemma add'_n_Sm n m : add' n (S m) = S (add' n m).
Proof.
(* perform this proof, no need for special lemmas. *)
Qed.

Lemma add'_comm n m : add' n m = add' m n.
Proof.
(* perform this proof, use add'_n_Sm and add'_Sn_m. *)
Qed.

(* To define the reverse function, there are (at least) two choices, both
   of which are described in the library for lists for Coq.  One is called
   rev and the other is rev_append. *)
Print rev_append.
Print rev.
Check rev_alt.
Check rev_append_rev.

(* Your exercise is to redo the proof of rev_append_rev. How does the proof you obtain
   compare with the proof of add'_add? *)

Lemma rev_append_rev' {A : Type}(l l' : list A): rev_append l l' = rev l ++ l'.
Proof.
(* perform this proof. *)
Qed.

(* advanced exercise following the exercises on sum_squares and sum_cubes. *)
(* write a function sum_powers more general than sumn, sumn2, or sumn3, where the power
   at which each number is raised is given as a first argument.
   
   There exists a polynomial p with rational coefficients
   of degree 5, such that sum_powers 4 n = p n.  By successive trials, can you find
   these rational coefficients? *)

Fixpoint sum_powers k n :=
  match n with
  | 0 => 0%Z
  | S p => (Z.of_nat (S p) ^ k + sum_powers k p)%Z
  end.

(* the polynomial solution can be found by educated guess work when looking at the
  value obtained for sumn4 10000 and comparing with 10000 ^ 5, to find the main
  coefficient (divisor), and comparing the difference with 10000 ^ 4, and so on.
  Using natural numbers for the recursion is handy, but using integers for the computations
  is a necessity, for complexity reasons. 
  The following line checks that we found the right coefficients on a sample of values. *)

(* advanced exercise: In the exercises for the first part of the course, you
  were asked to define a function cnv3 to compute the symbolic convolution of
  two lists.  IN the exercises for the second part of the course, you were
  asked to define a statement expressing that cnv3 performs the expected work
  when applied to two lists of the same length.  Now, your mission is to prove
  that statement, or to correct it if was actually wrong. *)
