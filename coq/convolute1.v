Require Import Arith List Psatz.

Fixpoint walk {A B : Type} (ys : list B)
  (xs : list A) : list B * list (A * B) :=
match xs with
  nil => (ys, nil)
| x :: xs' => 
  let (zs, r) := walk ys xs' in
  match zs with
  | nil => (nil, nil)
  | y :: ys' => (ys', (x, y) :: r)
  end
end.

Definition convolute {A B : Type} (xs : list A) (ys : list B) : list (A * B) :=
  let '(_, r) := walk ys xs in r.

Compute convolute (1 :: 2 :: 3 :: nil) (4 :: 5 :: 6 :: nil).

Fixpoint pal_walk {A : Type} (cmp : A -> A -> bool)
  (xs xs' : list A) : list A * bool :=
  match xs, xs' with
  | nil, nil => (nil, true)
  | nil, _ => (nil, false)
  | x :: xs, _ :: _ :: xs'  =>
    let (zs, v) := pal_walk cmp xs xs' in
      if v then
        match zs with
        | nil => (nil, false)
        | z :: zs' => (zs', cmp x z)
        end
      else
        (nil, false)
  | x :: xs, _ :: nil => (xs, true)
  | xs, nil => (xs, true)
  end.

Definition palindrome {A : Type} (cmp : A -> A -> bool)
  (l : list A) := 
  let '(_, r) := pal_walk cmp l l in r.

Compute palindrome Nat.eqb (1 :: nil).

Definition palindrome' {A : Type} (cmp : A -> A -> bool)
  (l : list A) :=
  forallb (fun '(x, y) => cmp x y) (convolute l l).

Compute palindrome' Nat.eqb (1 :: 2 :: 3 :: 2 :: 1 :: nil).

Compute walk (4 :: 5 :: 6 :: nil) (2 :: 3 :: nil).

(* Frankly, I needed to test the walk function on an example to guess what
  I wanted to set as the main properties. *)
(* Then my first statement was wrong.  Look at commit ca72c6c9 to see the  difference. *)
Lemma walk_correct A B (l1 : list A) (l2 : list B) (eA : A) eB :
  length l1 <= length l2 ->
  length (snd (walk l2 l1)) = length l1 /\
  length (fst (walk l2 l1)) = length l2 - length l1 /\
  (forall i, i < length l1 -> 
    nth i (snd (walk l2 l1)) (eA, eB) = 
    (nth i l1 eA, nth (length l1 - S i) l2 eB)) /\
  forall i, length l1 <= i < length l2 ->
    nth (i - length l1) (fst (walk l2 l1)) eB =
    nth i l2 eB.
Proof.
revert l2.
induction l1 as [ | x l1]; intros l2.
  simpl; intros _.
  split;[ auto | ].
  split;[ lia | ].
  split.
    intros i ilt0.
    exfalso; lia.
  now intros i iint; rewrite Nat.sub_0_r.
simpl; intros cl2.
assert (cl2' : length l1 <= length l2) by lia.
destruct (walk l2 l1) as [[ | y ys'] r] eqn: vwalk.
  generalize (IHl1 l2 cl2'); rewrite vwalk; simpl; intros [h1 [h2 _]].
  generalize (Nat.sub_gt _ _ cl2); rewrite <- h2; intros abs; exfalso.
  now apply abs; trivial.
generalize (IHl1 l2 cl2'); rewrite vwalk; simpl; intros [h1 [h2 [h3 h4]]].
split;[rewrite h1; trivial |].
split;[lia | ].
split.
  intros i ibnd; apply lt_n_Sm_le in ibnd.
change (nth i ((x, y):: r) (eA, eB) =
      (nth i (x :: l1) eA, nth (S (length l1) - (S i)) l2 eB)).
  destruct i as [ | i].
    simpl.
    rewrite Nat.sub_0_r.
    assert (cnd: length l1 <= length l1 < length l2) by lia.
    generalize (h4 (length l1) cnd); rewrite Nat.sub_diag.
    now intros it; rewrite it.
  simpl; apply h3; lia.
intros i iint; destruct i as [ | i];[lia | ].
change (S i - S (length l1)) with (i - length l1).
rewrite <- (h4 (S i)); try lia.
now rewrite Nat.sub_succ_l; try lia.
Qed.

Lemma convolute_correct A B (l1 : list A) (l2 : list B) eA eB :
  length l2 = length l1 ->
  length (convolute l1 l2) = length l1 /\
  forall i, i < length l1 -> nth i (convolute l1 l2) (eA, eB) =
                      (nth i l1 eA, nth (length l1 - S i) l2 eB).
Proof.
intros lll.
assert (lell : length l1 <= length l2) by lia.
destruct (walk_correct _ _ l1 l2 eA eB lell) as [h1 [h2 [h3 h4]]].
split.
  unfold convolute; destruct (walk l2 l1) as [v1 v2].
  exact h1.
intros i ci; exact (h3 i ci).
Qed.