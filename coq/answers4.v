Require Import Arith ZArith List Bool Psatz.

(* Define a function that has the following type
   forall x y : nat, {z | z = x + y}
   and whose algorithmic content is the same as function add'
   from file exercise3.v *)

Program Fixpoint addts (x y : nat) : {z | z = x + y} :=
  match x with
  | 0 => y
  | S x' => addts x' (S y)
  end.

(* that was too easy.  Without using Program we get into the following steps. *)

Fail Fixpoint addt1 (x y : nat) : {z | z = x + y} :=
  match x with
  | 0 => exist _ y _
  | S x' => 
    let '(exist _ v h) := addt1 x' (S y) in exist _ v _
  end.

Fail Fixpoint addt1 (x y : nat) : {z | z = x + y} :=
  match x return {z | z = x + y} with
  | 0 => exist _ y eq_refl
  | S x' => 
    let '(exist _ v h) := addt1 x' (S y) in exist _ v _
  end.

Fixpoint addt2 (f : forall x' y v, v = x' + S y -> v = S x' + y)
  (x y : nat) : {z | z = x + y} :=
  match x return {z | z = x + y} with
  | 0 => exist _ y eq_refl
  | S x' => 
    let '(exist _ v h) := addt2 f x' (S y) in
    exist _ v (f x' y v h)
  end.

Check fun (x' y v : nat) (vv : v = x' + S y) =>
   eq_ind_r (fun e => v = e) vv (Nat.add_succ_comm x' y).

Fixpoint addt3 (x y : nat) : {z | z = x + y} :=
  match x return {z | z = x + y} with
  | 0 => exist _ y eq_refl
  | S x' =>
    let '(exist _ v vv) := addt3 x' (S y) in
    exist _ v (eq_ind_r (fun e => v = e) vv (Nat.add_succ_comm x' y))
  end.
