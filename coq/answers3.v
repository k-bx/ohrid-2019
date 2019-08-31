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
induction n as [| n IH].
  reflexivity.
change (sumn2 (S n)) with (S n ^ 2 + sumn2 n).
rewrite Nat.mul_add_distr_l.
rewrite IH.
simpl; ring.
Qed.

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
induction n as [ | n IH].
  reflexivity.
change (sumn3 (S n)) with (Z.of_nat (S n) ^ 3 + sumn3 n)%Z.
rewrite Z.mul_add_distr_l.
rewrite IH. 
rewrite Nat2Z.inj_succ.
unfold Z.succ.
ring.
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

  forall x y, add' x y = x + y

It will be useful to use existing theorems about
Nat.add for this exercise.
*)

Lemma add'_add : forall n m, add' n m = n + m.
Proof.
intros n.
induction n as [ | n IH].
  trivial.
intros m; rewrite Nat.add_succ_comm; simpl; rewrite IH.
reflexivity.
Qed.

(* It is interesting to compare the proofs of associativity
  and commutativity for Nat.add (noted as +) and add'.
  For add', the problem is quite hard if we don't
  to prove more general facts.  Also proving add'_assoc
  will rely on add'_Sn_m as an auxiliary lemma. *)
Lemma nat_add_assoc n m p : n + (m + p) = n + m + p.
Proof.
induction n as [ | n IH].
  trivial.
simpl; rewrite IH; trivial.
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
intros n; induction n as [ | n IH].
  trivial.
intros m.
change (add' (S n) (S m) = S (add' (S n) m)).
rewrite IH.
trivial.
Qed.

Lemma add'_assoc n m p : add' n (add' m p) = add' (add' n m) p.
Proof.
induction n as [ | n IH].
  reflexivity.
rewrite !add'_Sn_m, IH.
reflexivity.
Qed.

Lemma add'_n_Sm n m : add' n (S m) = S (add' n m).
Proof.
revert m; induction n as [|n IH]; intros m.
  reflexivity.
simpl; rewrite !IH.
reflexivity.
Qed.

Lemma add'_comm n m : add' n m = add' m n.
Proof.
revert m; induction n as [|n IH]; intros m.
  simpl; induction m as [|m Im].
    reflexivity.
  simpl; rewrite add'_n_Sm, <- Im; reflexivity.
simpl; rewrite !add'_n_Sm, IH; reflexivity.
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
revert l'.
induction l as [ | x l IH].
   intros l'; reflexivity.
intros l'; simpl.
rewrite IH. simpl; rewrite <- app_assoc.
reflexivity.
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
Compute (fun x => (10 ^ 10 * sum_powers 4 x) / Z.of_nat x ^ 5)%Z (10 ^ 4).
(* The result looks very close to 1/5. *)

Compute (fun x => (10 ^ 10 * sum_powers 4 x))%Z (10 ^ 4).
Compute (fun x => (sum_powers 4 x))%Z (10 ^ 4).
Compute (fun x => (sum_powers 4 x) - (Z.of_nat x ^ 5) / 5)%Z (10 ^ 4).
Compute (fun x => (10 ^ 10 * ((sum_powers 4 x) - (Z.of_nat x ^ 5) / 5) / Z.of_nat x ^ 4))%Z
  (10 ^ 4).
(* Here the result looks like 1/2 *)
Compute (fun x => (sum_powers 4 x) - (Z.of_nat x ^ 5) / 5)%Z (10 ^ 4).
Compute (fun x => (sum_powers 4 x) - (Z.of_nat x ^ 5) / 5
                   -(Z.of_nat x ^ 4)/ 2)%Z (10 ^ 4).
(* Comparing the two previous results shows that we did get rid of one part of the order
  of (10 ^ 4) ^ 4 *)
Compute (fun x => (10 ^ 10 * ((sum_powers 4 x) - (Z.of_nat x ^ 5) / 5
                   -(Z.of_nat x ^ 4)/ 2)) / Z.of_nat x ^ 3)%Z (10 ^ 4).
(* This looks lie 1/3 *)
Compute (fun x => (sum_powers 4 x) - (Z.of_nat x ^ 5) / 5
                   -(Z.of_nat x ^ 4)/ 2 - Z.of_nat x ^ 3 / 3)%Z (10 ^ 4).
(* Now the result does not look it is of the same order of magnitude as
  (10 ^ 4) ^ 2, so we assume the coefficient for degree 2 is 0 *)
Compute (fun x => (10 ^ 10 * ((sum_powers 4 x) - (Z.of_nat x ^ 5) / 5
                   -(Z.of_nat x ^ 4)/ 2 - Z.of_nat x ^ 3/ 3)) / Z.of_nat x)%Z ( 10 ^ 4).
(* the result has only 9 digits, so the number we are looking at is 1/3 *)
Compute (fun x => (10 ^ 10 * ((sum_powers 4 x) - (Z.of_nat x ^ 5) / 5
                   -(Z.of_nat x ^ 4)/ 2 - Z.of_nat x ^ 3/ 3 + Z.of_nat x / 30)))%Z (10 ^ 4).
(* I finally conclude with the following result, which I check on a varied sample. *)
Compute map (fun x => 30 * sum_powers 4 x
              - 6 * Z.of_nat x ^ 5 - 15 * Z.of_nat x ^ 4 - 10 * Z.of_nat x ^ 3 +
               Z.of_nat x)%Z
            (5 :: 9 :: 13 :: 12 :: 1000::nil).

(* The polynomial can be factorized through a little guess work. The main coefficient,
   once the 1/30 factor has been removed, is 6, so the guess work looks for values that
   are multiples of 1/2 and 1/3.  The last trinomial could be further factorized, but
   that would require working with algebraic numbers, which less handy for calculations. *)
Lemma factorize_pol (x : Z) : (6 * x ^ 5 + 15 * x ^ 4 + 10 * x ^ 3 - x = 
  x * (x + 1) * (2 * x  + 1) * (3 * x ^ 2 + 3 * x - 1))%Z.
Proof.
ring.
Qed.

Lemma sum_fourth_powers n : (30 * sum_powers 4 n = Z.of_nat n * (Z.of_nat n + 1) *
       (2 * Z.of_nat n + 1) * 
       (3 * Z.of_nat n ^ 2 + 3 * Z.of_nat n - 1))%Z.
Proof.
induction n as [ | n IH].
  reflexivity.
cbn [sum_powers].
rewrite Z.mul_add_distr_l.
rewrite IH. 
rewrite Nat2Z.inj_succ.
unfold Z.succ.
ring.
Qed.

(* advanced exercise: In the exercises for the first part of the course, you
  were asked to define a function cnv3 to compute the symbolic convolution of
  two lists.  IN the exercises for the second part of the course, you were
  asked to define a statement expressing that cnv3 performs the expected work
  when applied to two lists of the same length.  Now, your mission is to prove
  that statement, or to correct it if was actually wrong. *)

(* The solution is given in a different file "convolute1.v" *)
