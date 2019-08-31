Require Import Arith ZArith.

(* This is a comment. *)
(* the following block describes an algorithm that adds the n first natural
   numbers. *)
Fixpoint sumn (n : nat) :=
  match n with 0 => 0 | S p => sumn p + (p + 1) end.

(* The next part does a similar study, but for another algorithm,
which computes the square root of a number in a stupid and naive way. *)
Fixpoint sqrt_aux (n p : nat) :=
  match n with
  | S k => if k ^ 2 <=? p then k else sqrt_aux k p
  | 0 => 0
  end. 

Definition sqrt (p : nat) := sqrt_aux (p + 1) p.

(* It takes 6 seconds to compute the square root of 1000 *)
Compute sqrt 1000.

(* It is possible to write a more efficient algorithm, that does
  not compute any square. *)
Fixpoint sqrt2_aux (n p : nat) : nat * nat :=
  match n with
  | 0 => (0, 0)
  | S n' => 
      match p with
      | 0 => (0, 0)
      | 1 => (1, 0)
      | 2 => (1, 1)
      | 3 => (1, 2)
      | _ => let q := p / 4 in
        let r := p mod 4 in
        let (v, r') := sqrt2_aux n' q in
        if (4 * v) + 1 <=? 4 * r' + r then
           (2 * v + 1, 4 * r' + r - (4 * v + 1))
        else (2 * v , 4 * r' + r)
      end
  end.

Definition sqrt2 n := fst (sqrt2_aux n n).

(* We shall now describe a similar algorithm, but with a binary
   encoding of numbers. *)

Open Scope Z_scope.

Fixpoint sqrtp (p : positive) : Z * Z :=
  let mkres := fun '(v, r) => 
    if 4 * v + 1 <=? 4 * r + Zpos p mod 4 then
      (2 * v + 1, 4 * r + Zpos p mod 4 - (4 * v + 1))
    else
      (2 * v, 4 * r + Zpos p mod 4) in
  match p with
  | xH => (1, 0)
  | xO xH => (1, 1)
  | xI xH => (1, 2)
  | xO (xO q) => mkres (sqrtp q)
  | xI (xO q) => mkres (sqrtp q)
  | xO (xI q) => mkres (sqrtp q)
  | xI (xI q) => mkres (sqrtp q)
  end.

Definition sqrtz (z : Z) :=
  match z with Zpos p => sqrtp p | _ => (0, 0) end.

(* Note that we are now able to compute square roots of much larger
   numbers. *)

Compute sqrtz 200000000000000000000.
