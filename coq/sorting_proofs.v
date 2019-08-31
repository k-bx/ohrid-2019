Require Import Arith ZArith List Bool Psatz.

(* The next two functions describe a polymorphic insertion sort algorithm. *)
Fixpoint insert {A : Type} (cmp : A -> A -> bool) (a : A) (l : list A) :
   list A :=
  match l with
  | nil => a::nil
  | b :: l' => if cmp a b then a :: l else b :: insert cmp a l'
  end.

Fixpoint sort {A : Type} (cmp : A -> A -> bool) (l : list A) :=
  match l with
  | nil => nil
  | a :: l' => insert cmp a (sort cmp l')
  end.

Inductive sortedP {A : Type} (R : A -> A -> Prop) :
   list A -> Prop :=
| sorted0 : sortedP R nil
| sorted1 (x : A) : sortedP R (x :: nil)
| sorted2 (x y : A) l : R x y -> sortedP R (y :: l) -> sortedP R (x :: y :: l).

Definition p_rel {A : Type} (f : A -> A -> bool) (x y : A) := f x y = true.
  
Hint Unfold p_rel.

Lemma sorted_insert {A : Type} {cmp : A -> A -> bool} (l : list A) (x : A) :
  (forall x y, cmp x y = false -> cmp y x = true) ->
  sortedP (p_rel cmp) l -> sortedP (p_rel cmp) (insert cmp x l).
Proof.
intros revcmp.
induction 1 as [ | y | y z l cmpyz sl IH].
    now simpl; apply sorted1.
  simpl; destruct (cmp x y) eqn:vcmp.
    now apply sorted2; auto; apply sorted1.
  now apply sorted2; auto; apply sorted1.
simpl.
destruct (cmp x y) eqn:cmpxy.
  now apply sorted2; auto; apply sorted2.
destruct (cmp x z) eqn:cmpxz.
  now apply sorted2; auto; apply sorted2.
apply sorted2; auto.
now revert IH; simpl; rewrite cmpxz.
Qed.

Lemma sorted_sort {A : Type} {cmp : A -> A -> bool} (l : list A) :
  (forall x y, cmp x y = false -> cmp y x = true) ->
  sortedP (p_rel cmp) (sort cmp l).
Proof.
intros revcmp.
induction l as [ | a l IH].
  now apply sorted0.
simpl; apply sorted_insert; auto.
Qed.

Inductive bin (A : Type) :=
  | Node (t1 t2 : bin A)
  | Leaf (x : A).

Arguments Node {A}.
Arguments Leaf {A}.

Fixpoint insert_bin {A : Type} (t : bin A) (a : A) :=
  match t with
  | Leaf b => Node (Leaf b) (Leaf a)
  | Node t1 t2 => Node t2 (insert_bin t1 a)
  end.

Fixpoint list_to_bin {A : Type} (t : bin A) (l : list A) :=
  match l with
  | nil => t
  | a :: l' => insert_bin (list_to_bin t l') a
  end.

Fixpoint merge_aux {A : Type} (cmp : A -> A -> bool)
   (f : list A -> list A) (a : A) (l1 l2 : list A) : list A :=
  match l2 with
  | b :: l2' =>
    if cmp a b then a :: f l2 else b :: merge_aux cmp f a l1 l2'
  | nil => a :: l1
  end.

Lemma sorted_merge_aux {A : Type} {cmp : A -> A -> bool} 
  (f : list A -> list A) (a : A) (l1 l2 : list A) :
  (forall x y, cmp x y = false -> cmp y x = true) ->
  (forall y l, sortedP (p_rel cmp) (y :: l) -> p_rel cmp a y ->
             sortedP (p_rel cmp) (a :: f (y :: l))) ->
  sortedP (p_rel cmp) (a :: l1) ->
  sortedP (p_rel cmp) l2 ->
  sortedP (p_rel cmp) (merge_aux cmp f a l1 l2).
Proof.
intros revcmp fP sal1; induction 1 as [ | y | y z l2 cmpyz szl2 IH].
    simpl; assumption.
  simpl; destruct (cmp a y) eqn: cmpay.
    now apply fP; auto; apply sorted1.
  now apply sorted2; auto.
change (merge_aux cmp f a l1 (y :: z :: l2)) with
  (if cmp a y then a :: f (y :: z :: l2) else y :: merge_aux cmp f a l1 (z :: l2)).
destruct (cmp a y) eqn:cmpay.
  now apply fP; auto; apply sorted2.
revert IH.
change (merge_aux cmp f a l1 (z :: l2)) with
  (if cmp a z then a :: f (z :: l2) else z :: merge_aux cmp f a l1 l2).
destruct (cmp a z) eqn:cmpaz.
  now apply sorted2; auto.
apply sorted2; auto.
Qed.

Fixpoint merge {A : Type} (cmp : A -> A -> bool) (l1 l2 : list A) :=
  match l1 with
  | a :: l1' => merge_aux cmp (merge cmp l1') a l1' l2
  | nil => l2
  end.

Lemma sorted_merge {A : Type} {cmp : A -> A -> bool} (l1 l2 : list A) :
  (forall x y, cmp x y = false -> cmp y x = true) ->
  sortedP (p_rel cmp) l1 -> sortedP (p_rel cmp) l2 ->
  sortedP (p_rel cmp) (merge cmp l1 l2).
Proof.
intros revcmp sl1; revert l2.
induction sl1.
    now simpl; auto.
  simpl; intros l2 sl2.
  assert (tmp : forall y l, sortedP (p_rel cmp) (y :: l) ->
                        p_rel cmp x y -> sortedP (p_rel cmp) (x :: y :: l)).
    now intros y l syl cmpxy; apply sorted2; auto.
  now apply sorted_merge_aux; auto; apply sorted1.
intros l2 sl2.
change (merge cmp (x :: y :: l) l2) with
  (merge_aux cmp (merge cmp (y :: l)) x (y :: l) l2).
apply sorted_merge_aux; auto.
  intros z l2' szl2' cmpxz.
  generalize (IHsl1 (z :: l2') szl2'); simpl; destruct (cmp y z) eqn:cmpyz.
    now intros IH'; apply sorted2; auto.
  now intros IH'; apply sorted2; auto.
now apply sorted2.
Qed.

Fixpoint merge_tree {A : Type} (cmp : A -> A -> bool)
  (t : bin A) :=
  match t with
  | Leaf x => x :: nil
  | Node t1 t2 => merge cmp (merge_tree cmp t1) (merge_tree cmp t2)
  end.

Lemma sorted_merge_tree {A : Type} cmp (t : bin A) :
  (forall x y : A, cmp x y = false -> cmp y x = true) ->
  sortedP (p_rel cmp) (merge_tree cmp t).
Proof.
intros revcmp.
induction t as [t1 IH1 t2 IH2 | x].
  now apply sorted_merge; auto.
now apply sorted1.
Qed.

Definition merge_sort {A : Type} (cmp : A -> A -> bool)
  (l : list A) :=
  match l with
  | nil => nil
  | a :: l' => merge_tree cmp (list_to_bin (Leaf a) l')
  end.

Lemma sorted_merge_sort {A : Type} (cmp : A -> A -> bool) l :
  (forall x y : A, cmp x y = false -> cmp y x = true) ->
  sortedP (p_rel cmp) (merge_sort cmp l).
Proof.
intros revcmp.
destruct l as [ | x l].
  now apply sorted0.
now simpl; apply sorted_merge_tree.
Qed.

Inductive search_tree (A : Type) :=
  Snode (x : A) (t1 t2 : search_tree A)
| Sleaf.

Arguments Snode {A}.
Arguments Sleaf {A}.

Inductive present {A : Type} (x : A) : search_tree A -> Prop :=
    present1 t1 t2 : present x (Snode x t1 t2)
  | presentl v t1 t2 : present x t1 -> present x (Snode v t1 t2)
  | presentr v t1 t2 : present x t2 -> present x (Snode v t1 t2).

Inductive sorted_search_tree {A : Type} (R : A -> A -> Prop) : search_tree A -> Prop :=
  sortedTN v t1 t2 :
    sorted_search_tree R t1 -> sorted_search_tree R t2 ->
    (forall x, present x t1 -> R x v) ->
    (forall x, present x t2 -> R v x) ->
    sorted_search_tree R (Snode v t1 t2)
 | sortedTL : sorted_search_tree R Sleaf.

Fixpoint insert_stree {A : Type} (cmp : A -> A -> bool)
  (x : A) (t : search_tree A) :=
  match t with
    Sleaf => Snode x Sleaf Sleaf
  | Snode y t1 t2 =>
    if cmp x y then Snode y (insert_stree cmp x t1) t2
    else Snode y t1 (insert_stree cmp x t2)
  end.

Lemma present_insert_stree {A : Type} cmp t (x y : A) :
  present x (insert_stree cmp y t) <-> (present x t \/ x = y).
Proof.
induction t as [v t1 IH1 t2 IH2 | ].
  simpl; destruct (cmp y v); split.
  - intros hp; inversion hp. 
        now left; constructor.
      assert (left_case : present x (insert_stree cmp y t1)) by auto.
      apply IH1 in left_case; destruct left_case as [lc1 | lc2]; auto.
      now left; apply presentl.
    assert (right_case : present x t2) by auto.
    now left; apply presentr.
  - intros [px | xy]; cycle 1.
      now apply presentl; apply IH1; right.
    inversion px;[constructor | |now apply presentr].
    now apply presentl; apply IH1; left.
  - intros hp; inversion hp. 
        now left; constructor.
      now left; apply presentl.
    assert (right_case : present x (insert_stree cmp y t2)) by auto.
    apply IH2 in right_case; destruct right_case as [lc1 | lc2]; auto.
    now left; apply presentr.
  - intros [px | xy]; cycle 1.
      now apply presentr; apply IH2; right.
    inversion px;[constructor | now apply presentl |].
    now apply presentr; apply IH2; left.
  - split; simpl.
      intros hp; inversion hp;[now right | | ];
      (assert (abs : present x Sleaf) by auto);
      now inversion abs.
now intros [abs | xy]; try inversion abs; rewrite xy; constructor.
Qed.

Lemma sorted_insert_stree {A : Type} (cmp : A -> A -> bool) t x :
  (forall x y : A, cmp x y = false -> cmp y x = true) ->
  sorted_search_tree (p_rel cmp) t -> 
  sorted_search_tree (p_rel cmp) (insert_stree cmp x t).
Proof.
intros revcmp.
induction 1 as [v t1 t2 st1 IH1 st2 IH2 cmp1 cmp2 | ].
  simpl; destruct (cmp x v) eqn:cmpxv.
    apply sortedTN; auto.
    intros z inz.  
    rewrite present_insert_stree in inz; destruct inz as [old | new].
      now apply cmp1.
    now rewrite new.
  apply sortedTN; auto.
  intros z inz.
  rewrite present_insert_stree in inz; destruct inz as [old | new].
    now apply cmp2.
  now rewrite new; auto.
now simpl; apply sortedTN; try constructor; intros z inz; inversion inz.
Qed.

Fixpoint list_to_stree {A : Type} cmp (l : list A) :=
  match l with
    nil => Sleaf
  | a :: l' => insert_stree cmp a (list_to_stree cmp l')
  end.

Lemma sorted_list_to_tree {A : Type} (cmp : A -> A -> bool) l :
  (forall x y : A, cmp x y = false -> cmp y x = true) ->
  sorted_search_tree (p_rel cmp) (list_to_stree cmp l).
Proof.
intros revcmp.
induction l as [|x l IH].
  now simpl; apply sortedTL.
now simpl; apply sorted_insert_stree; auto.
Qed.

Fixpoint search_tree_to_list {A : Type} (t : search_tree A) (l : list A) :=
  match t with
    Sleaf => l
  | Snode y t1 t2 => search_tree_to_list t1 (y :: search_tree_to_list t2 l)
  end.

Inductive above_head {A : Type} (R : A -> A -> Prop) (t : search_tree A) :
   list A -> Prop :=
  ah1 (x : A) (l : list A) : (forall y, present y t -> R y x) ->
       above_head R t (x :: l)
| ah0 : above_head R t nil.

Lemma In_search_tree_to_list {A : Type} l t (x : A) :
  In x (search_tree_to_list t l) <-> (In x l \/ present x t).
Proof.
revert l; induction t as [v t1 IHt1 t2 IHt2 | ]; intros l.
  split.
    simpl; rewrite IHt1; simpl; intros [[vx | ins] | inl].
        now right; rewrite vx; constructor.
      rewrite IHt2 in ins; destruct ins as [inl | int]; auto.
      now right; apply presentr.
    now right; apply presentl.
  intros [inl | pp].
    now simpl; apply IHt1; simpl; left; right; apply IHt2; left.
  inversion pp.
      (assert (xv : x = v) by auto); rewrite <- xv.
      now simpl; rewrite IHt1; simpl; left; left.
    now simpl; rewrite IHt1; right.
  now simpl; rewrite IHt1; left; simpl; right; rewrite IHt2; right.
simpl; split.
  now left.
now intros [inxl | abs]; try inversion abs.
Qed.

Lemma search_tree_to_list_head {A : Type} l t (z : A) l' :
  search_tree_to_list t l = z::l' -> present z t \/ t = Sleaf.
Proof.
revert l l'; induction t as [v t1 IHt1 t2 IHt2|]; intros l l'.
  simpl; intros qq; generalize qq; intros qq'.
  apply IHt1 in qq; destruct qq as [int1 | t1n].
    now left; apply presentl.
  rewrite t1n in qq'; simpl in qq'; injection qq'; intros _ vz; rewrite vz. 
  now left; constructor.
now intros _; right.
Qed.

Lemma sorted_search_tree_to_list {A : Type} (R : A -> A -> Prop) l t :
  sorted_search_tree R t -> above_head R t l -> sortedP R l ->
   sortedP R (search_tree_to_list t l).
Proof.
intros st; revert l; induction st as [v t1 t2 st1 IHt1 st2 IHt2 cmp1 cmp2 | ].
  intros l ah sl; simpl; apply IHt1.
    now constructor.
  destruct (search_tree_to_list t2 l) as [| z l'] eqn:st2l.
    now apply sorted1.
  apply sorted2.
    assert (zin : In z (search_tree_to_list t2 l)).
      now rewrite st2l; simpl; left.
    destruct t2 as [v' t21 t22 | ] eqn:vt2.
      assert (tmp:= search_tree_to_list_head l t2 z l'); rewrite vt2 in tmp.
      apply tmp in st2l; destruct st2l as [zt2 | abs]; try discriminate.
      now apply cmp2.
    simpl in st2l.
    rewrite st2l in ah; inversion ah.
    assert (present v (Snode v t1 Sleaf)) by constructor.
    now auto.
  rewrite <- st2l.
  apply IHt2.
  destruct l as [| b l2].
    now constructor.
  constructor; intros y yt2; inversion ah.
    assert (present y (Snode v t1 t2)) by (now apply presentr); now auto.
  auto.
now simpl; auto.
Qed.

Definition tree_sort {A : Type} (cmp : A -> A -> bool) (l : list A) : list A:=
  search_tree_to_list (list_to_stree cmp l) nil.

Lemma sorted_tree_sort {A : Type} (cmp : A -> A -> bool) (l : list A) :
  (forall x y : A, cmp x y = false -> cmp y x = true) ->
  sortedP (p_rel cmp) (tree_sort cmp l).
Proof.
intros revcmp.
unfold tree_sort.
apply sorted_search_tree_to_list.
    now apply sorted_list_to_tree; apply revcmp.
  now constructor.
now constructor.
Qed.