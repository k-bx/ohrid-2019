Require Import Arith ZArith Psatz List.

(* This example has been tested with coq-8.9 *)

Open Scope Z_scope.

Inductive lang := var (_ : nat) | bin (_ _ : lang).

Fixpoint interp (op : Z -> Z -> Z) (l : list Z) (t : lang) : Z :=
  match t with
  | var v => nth v l 0
  | bin x y => op (interp op l x) (interp op l y)
  end.

(* normlizing binary trees with respect to associativity: choosing
  a reference shape. *)
Fixpoint norm_aux t1 t2 : lang :=
  match t1 with
  | var x => bin (var x) t2
  | bin t t' => norm_aux t (norm_aux t' t2)
  end.

Fixpoint norm t :=
  match t with
  | var x => t
  | bin t1 t2 => norm_aux t1 (norm t2)
  end.

Section assoc_reflection_proofs.

Variable op : Z -> Z -> Z.

Hypothesis op_assoc : forall a b c, op a (op b c) = op (op a b) c.

Lemma norm_aux_c l t1 t2 :
  interp op l (norm_aux t1 t2) = op (interp op l t1) (interp op l t2).
Proof.
revert t2; induction t1 as [i | t1 IH1 t2 IH2]; intros t3.
  now auto.
now simpl; rewrite IH1, IH2, op_assoc.
Qed.

Lemma norm_c l t :  interp op l t = interp op l (norm t).
Proof.
induction t as [i | t1 IH1 t2 IH2]; auto; simpl.
now rewrite IH2, norm_aux_c.
Qed.

Lemma norm_c2 l t1 t2 : norm t1 = norm t2 -> interp op l t1 = interp op l t2.
Proof. now intros nn; rewrite (norm_c _ t1), (norm_c _ t2); apply f_equal.  Qed.

End assoc_reflection_proofs.

Arguments norm_c2 {op}.

Example axpypzpt x y z t : (x + y) + (z + t) = x + (y + z) + t.
Proof.
change (interp Z.add (x::y::z::t::nil)(bin (bin (var 0) (var 1))
                                           (bin (var 2) (var 3))) =
        interp Z.add (x::y::z::t::nil)
              (bin (bin (var 0) (bin (var 1) (var 2))) (var 3))).
apply (norm_c2 Z.add_assoc).
reflexivity.
Qed.

(* Now adding the reification phase. *)

Class Reify (op : Z -> Z -> Z)  (x : Z) (t : lang) (l : list Z).

Instance binRf op x y l e1 e2 {_ : Reify op x e1 l} {_ : Reify op y e2 l} :
   Reify op (op x y) (bin e1 e2) l | 1 := {}.

Class Nth (i : nat) (l : list Z) (e : Z).

Instance nth0 e l : Nth 0 (e :: l) e | 0 := {}.

Instance nthS i e l e'
   {_ : Nth i l e} : Nth (S i) (e' :: l) e | 2 := {}.

(* proof search can fill the values for the list of variables
  even when there is already some value in the list. *)
Example nth_test : exists l i, Nth i (42::l) 17.
Proof. eexists. eexists.
Fail eapply nth0.
eapply nthS.
eapply nth0.
Grab Existential Variables.
exact nil.
Qed.

Example nth_test1 : exists l i, Nth i (42::l) 17.
Proof. eexists. eexists.
typeclasses eauto.
Grab Existential Variables.
exact nil.
Qed.

Instance varRf op e i l 
  {_ : Nth i l e} : Reify op e (var i) l | 100.

(* When closing goals, it is unacceptable that lists are incomplete.
  But we can also rely on the type classes mechanism to make sure the
  list is not incomplete.
*)
Class Closed (l : list Z).

Instance closed0 : Closed nil.

Instance closed1 a l {_ : Closed l} : Closed (a :: l).

Definition reify_trigger op (term : Z) {expr : lang} {lvar : list Z}
 {_ : Reify op term expr lvar} `{Closed lvar} := (lvar, expr).

Ltac reify_step op :=
match goal with |- ?u = ?v =>
  match eval red in (reify_trigger op (op u v)) with
    (?a, bin ?b ?c) => change (interp op a b = interp op a c)
  end
end.

Example axpypzpt' x y z t : (x + y) + (z + t) = x + (y + z) + t.
Proof.
reify_step Z.add.
apply (norm_c2 Z.add_assoc).
reflexivity.
Qed.

Section tries.

Variable op : Z -> Z -> Z.

Hypothesis op_assoc : forall x y z, op x (op y z) = op (op x y) z.

Compute fold_right op 12 (List.map Z.of_nat (seq 2 10)).

Compute fold_right (fun a b => op b a) 2 (List.rev (List.map Z.of_nat (seq 3 10))).

Example try_2_12 :
 op 2 (op 3 (op 4 (op 5 (op 6 (op 7 (op 8 (op 9 (op 10 (op 11 12))))))))) =
 op (op (op (op (op (op (op (op (op (op 2 3) 4) 5) 6) 7) 8) 9) 10) 11)
         12.
Proof.
reify_step op.
now apply (norm_c2 op_assoc).
Qed.

Example try_2_12_rep :
 op 2 (op 3 (op 4 (op 5 (op 6 (op 7 (op 8 (op 9 (op 10 (op 11 12))))))))) =
 op (op (op (op (op (op (op (op (op (op 2 3) 4) 5) 6) 7) 8) 9) 10) 11)
         12.
Proof.
now repeat rewrite op_assoc.
Qed.

Print try_2_12.

Print try_2_12_rep.

End tries.

(* Now adding the commutative property to the operator. *)

Fixpoint lang_insert (x : nat) (t : lang) :=
  match t with
    bin (var y) t' =>
      if (x <=? y)%nat then bin (var x) (bin (var y) t')
      else bin (var y) (lang_insert x t')
  | var y =>
      if (x <=? y)%nat then bin (var x) (var y)
      else bin (var y) (var x)
  | _ => bin (var x) t
  end.

Fixpoint lang_sort (t : lang) :=
  match t with
  | bin (var x) t' => lang_insert x (lang_sort t')
  | _ => t
  end.

Section comm_reflection_proofs.

Variable op : Z -> Z -> Z.

Hypotheses (op_assoc : forall a b c, op a (op b c) = op (op a b) c)
  (op_comm : forall a b, op a b = op b a).

Lemma lang_insert_c l x t :
  interp op l (lang_insert x t) = interp op l (bin (var x) t).
Proof.
induction t as [ j | [ j | t11 t12] _ t2 IH ]; simpl; auto;
  case (x <=? j)%nat; simpl; auto.
now rewrite IH; simpl; rewrite !op_assoc, (op_comm (_ x l 0)).
Qed.

Lemma lang_sort_c l t :
  interp op l (lang_sort t) = interp op l t.
Proof.
induction t as [ i | [ j | t11 t12] _ t2 IH]; auto.
now simpl; rewrite lang_insert_c; simpl; rewrite IH.
Qed.

Lemma lang_sort_c2 l t1 t2 :
  lang_sort (norm t1) = lang_sort (norm t2) -> interp op l t1 = interp op l t2.
Proof.
intros nn; rewrite (norm_c _ op_assoc _ t1), (norm_c _ op_assoc _ t2).
rewrite <- (lang_sort_c _ (norm t1)), <- (lang_sort_c _ (norm t2)).
now apply f_equal.
Qed.

End comm_reflection_proofs.

Arguments lang_sort_c2 {op}.

Example cxpypz x y z : x + y + z = z + x + y.
Proof.
reify_step Z.add.
apply (lang_sort_c2 Z.add_assoc Z.add_comm).
compute.
reflexivity.
Qed.

Example cxmymy x y : x * y * y = y * x * y.
Proof.
reify_step Z.mul.
apply (lang_sort_c2 Z.mul_assoc Z.mul_comm).
compute.
reflexivity.
Qed.

Class comm_monoid (op : Z -> Z -> Z) :=
  {op_assoc : forall x y z, op x (op y z) = op (op x y) z;
   op_comm : forall x y, op x y = op y x}.

Lemma lang_sort_c2' {op : Z -> Z -> Z} `{comm_monoid op} l t1 t2 :
  lang_sort (norm t1) = lang_sort (norm t2) ->
  interp op l t1 = interp op l t2.
Proof.
intros sn2; apply lang_sort_c2, sn2.
  apply op_assoc.
now apply op_comm.
Qed.

Example cxpypz2 x y z : x + y + z = z + x + y.
Proof.
reify_step Z.add.
Fail apply lang_sort_c2'.
Abort.

Instance add_comm_monoid : comm_monoid Z.add :=
  {op_assoc := Z.add_assoc; op_comm := Z.add_comm}.

Instance mul_comm_monoid : comm_monoid Z.mul :=
  {op_assoc := Z.mul_assoc; op_comm := Z.mul_comm}.

Example cxpypz2 x y z : x + y + z = z + x + y.
Proof.
reify_step Z.add.
now apply lang_sort_c2'.
Qed.

Example cxmymz2 x y z : x * y * z = z * x * y.
Proof.
reify_step Z.mul.
now apply lang_sort_c2'.
Qed.

Inductive nth_p : list Z -> nat -> Z -> Prop :=
  nth_0 : forall x l, nth_p (x :: l) 0 x
| nth_S : forall x y i l, nth_p l i x -> nth_p (y :: l) (S i) x.

Inductive interp_p (op : Z -> Z -> Z) (l : list Z) : lang -> Z -> Prop :=
  p_bin : forall t1 t2 e1 e2,
    interp_p op l t1 e1 -> interp_p op l t2 e2 ->
    interp_p op l (bin t1 t2) (op e1 e2)
| p_var : forall i x, nth_p l i x -> interp_p op l (var i) x.

Ltac reify_auto op :=
  repeat (eapply p_bin); eapply p_var; repeat (eapply nth_0 || eapply nth_S).

