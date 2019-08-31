Require Import Arith ZArith List Bool Psatz.

Lemma non_perfect_square_square_root_not_rational :
   forall n, (~ exists k, n = k * k) ->
   forall p q, q <> 0 -> (q * q) * n <> p * p.
Proof.
intros n main.
intros p' q' qn0 abs.
set (p := p' / Nat.gcd p' q').
set (q := q' / Nat.gcd p' q').
assert (gcdn0 : Nat.gcd p' q' <> 0).
  now intros ab'; apply qn0, (Nat.gcd_eq_0_r p' q').
assert (gcd1: Nat.gcd p q = 1).
  now apply Nat.gcd_div_gcd; auto.
assert (simp' := fun x => Nat.divide_div_mul_exact p' _ x gcdn0
              (Nat.gcd_divide_l _ _)).
assert (simq' := fun x => Nat.divide_div_mul_exact q' _ x gcdn0
              (Nat.gcd_divide_r _ _)).
assert (q' = q * Nat.gcd p' q').
  rewrite Nat.mul_comm; unfold q; rewrite <- simq'.
  now rewrite Nat.mul_comm, Nat.div_mul; auto.
assert (p' = p * Nat.gcd p' q').
  rewrite Nat.mul_comm; unfold p; rewrite <- simp'.
  now rewrite Nat.mul_comm, Nat.div_mul; auto.
assert (restate: q * q * n = p * p).
  unfold q; rewrite <- (Nat.mul_comm n), Nat.mul_assoc, <- !simq'.
  rewrite (Nat.mul_comm (_ / _) q').
  assert (Nat.divide (Nat.gcd p' q') (n * q')).
    now apply Nat.divide_mul_r, Nat.gcd_divide_r.
  rewrite <- Nat.divide_div_mul_exact; auto.
  rewrite (Nat.mul_comm q'), <- Nat.mul_assoc, Nat.mul_comm, abs.
  now rewrite simp', Nat.mul_comm, simp'; fold p.
clear simp' simq'.
assert (gcdc : Nat.gcd q p = 1) by now rewrite Nat.gcd_comm.
assert (qd : Nat.divide q (p * p)).
  now exists (q * n); ring [restate].
assert (tmp:=Nat.gauss _ _ _ qd gcdc).
rewrite <- (Nat.mul_1_r p) in tmp.
assert (t2:=Nat.gauss _ _ _ tmp gcdc).
apply Nat.divide_1_r in t2.
now apply main; exists p; rewrite <- restate, t2, !Nat.mul_1_l.
Qed.