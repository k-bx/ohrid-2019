Require Import Arith ZArith List Bool String.

(* This is the specification of what it means to be
  a prime number. *)
Definition prime_number (n : nat) : Prop :=
  (2 <= n) /\
  (forall x, 1 < x < n -> ~ exists k, n = k * x).

(* Primality can actually be tested by a program
  we write in Coq. *)
Definition prime_bool (n : nat) : bool :=
  Nat.leb 2 n &&
  forallb (fun x => negb (n mod x =? 0)) (seq 2 (n - 2)).

(* The following is a property that we can state, but
   not verify using a terminating program, in general. *)
Definition ext_equal {A B : Type} (f g : A -> B) : Prop :=
  forall x : A, f x = g x.

Fixpoint r_id (n : nat) :=
  match n with 0 => 0 | S p => S (r_id p) end.

(* r_id is extensionally equal to (fun x : nat => x)
   but it is essentially different. *)

(* Inductive predicates can also be used to write
  specifications. *)

Inductive sortedP {A : Type} (R : A -> A -> Prop) :
   list A -> Prop :=
| sorted0 : sortedP R nil
| sorted1 (x : A) : sortedP R (x :: nil)
| sorted2 (x y : A) l : R x y -> sortedP R (y :: l) -> sortedP R (x :: y :: l).

(* There is no procedure to decide
   sortedP (fun f g => forall x y, f x <= g y)
   still we know that the following property holds:

   sortedP ((fun x => x + 1) :: (fun x => x ^ 2 + x + 1) ::
            (fun x => x ^ 3 + x ^ 2 + x + 1) :: nil)
*)

Open Scope Z_scope.

(* In the current state of our knowledge (Aug. 2019) , it is not known whether
  the following Collatz predicate is decidable or not. *)
Inductive Collatz : Z -> Prop :=
| c1 : Collatz 1
| c2 : forall n, n mod 2 = 0 -> Collatz (n / 2) ->
       Collatz n
| c3 : forall n, n mod 2 = 1 -> Collatz (3 * n + 1) ->
       Collatz n.

Close Scope Z_scope.

Open Scope string_scope.

Inductive wfpar : string -> Prop :=
  wf0 : wfpar EmptyString
| wfcat : forall s1 s2, wfpar s1 -> wfpar s2 -> 
          wfpar (s1 ++ s2)
| wfadd : forall s1, wfpar s1 ->
          wfpar ("(" ++ s1 ++ ")").

Close Scope string_scope.

Inductive t_closure {T : Type} (R : T -> T -> Prop) :
  T -> T -> Prop :=
  tc1 : forall x y, R x y -> t_closure R x y
| tc_s : forall x y z, R x y -> t_closure R y z ->
  t_closure R x z.

Inductive t_closure2 {T : Type} (R : T -> T -> Prop) :
  T -> T -> Prop :=
  tc2_1 : forall x y, R x y -> t_closure2 R x y
| tc2_s : forall x y z,
  t_closure2 R x y -> t_closure2 R y z ->
  t_closure2 R x z.
