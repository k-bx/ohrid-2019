Require Import ZArith List.

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

(* in the next two lines, we test our function on a small piece of data. *)
Open Scope Z_scope.

Compute sort Z.leb (1 :: 3 :: 2 :: 5 :: 2 :: nil).

(* We shall now describe another sorting algorithm, based on the construction
  of a balanced binary tree. This construction also shuffles the elements
  in a regular fashion.  For instance, all elements of the input list with
  an even rank end up in the second subtree. *)

(* The datatype for binary trees. *)
Inductive bin (A : Type) :=
  | Node (t1 t2 : bin A)
  | Leaf (x : A).

Arguments Node {A}.
Arguments Leaf {A}.

(* inserting an element in a tree: the new element always ends up in the
   right subtree, but with all elements that were previously in the
   left subtree.  This way not all elements are inserted in the same subtree.
*)
Fixpoint insert_bin {A : Type} (t : bin A) (a : A) :=
  match t with
  | Leaf b => Node (Leaf b) (Leaf a)
  | Node t1 t2 => Node t2 (insert_bin t1 a)
  end.

(* Now, we need to transform the input list into a binary tree.
  The next functions adds all elements of the list (last argument) into
  the tree (last-but-one) *)
Fixpoint list_to_bin {A : Type} (t : bin A) (l : list A) :=
  match l with
  | nil => t
  | a :: l' => insert_bin (list_to_bin t l') a
  end.

(* A little test. *)
Compute list_to_bin (Leaf 1) (3 :: 2 :: 5 :: 2 :: nil).

(* merging two lists in a sorted way is a bit difficult to program
  because of the constraint imposed by Coq that a recursive function
  show call itself on a subterm of one of its arguments.  The first,
  function describing all merging step that consume only elements of
  the second list. The function f that is passed as argument if the
  whole merging function. *)
Fixpoint merge_aux {A : Type} (cmp : A -> A -> bool)
   (f : list A -> list A) (a : A) (l1 l2 : list A) : list A :=
  match l2 with
  | b :: l2' =>
    if cmp a b then a :: f l2 else b :: merge_aux cmp f a l1 l2'
  | nil => a :: l1
  end.

(* Now this is the general merging function, which consumes elements
  from both lists.  Note that this general function appears only one
  in the body of the function, as an argument to merge_aux. *)
Fixpoint merge {A : Type} (cmp : A -> A -> bool) (l1 l2 : list A) :=
  match l1 with
  | a :: l1' => merge_aux cmp (merge cmp l1') a l1' l2
  | nil => l2
  end.

(* Once we have a function that merges two lists, we can apply it
  recursively to merge all results of sorting elements from a binary tree. *)
Fixpoint merge_tree {A : Type} (cmp : A -> A -> bool)
  (t : bin A) :=
  match t with
  | Leaf x => x :: nil
  | Node t1 t2 => merge cmp (merge_tree cmp t1) (merge_tree cmp t2)
  end.

(* The merge_sort function is then defined as the function that
  combines the operation of making a tree and then sorting it.  A
  special case must be made for empty lists, because the data type
  for tree does provide empty trees. *)
Definition merge_sort {A : Type} (cmp : A -> A -> bool)
  (l : list A) :=
  match l with
  | nil => nil
  | a :: l' => merge_tree cmp (list_to_bin (Leaf a) l')
  end.

(* We are now finished describing a merge_sort algorithm.  To test
  it we want to construct a big non sorted list. *)

Definition sample := Eval compute in 
  (snd (Z.iter 10000 (fun '(x, l) => (x + 1, x :: l)) (0, nil))).

Compute firstn 10 sample.

(* On one of my machines, sorting with insertion sort takes 16 seconds. *)
Time Compute sort Z.leb sample.

(* Sorting with merge_sort takes less than a second. *)
Time Compute merge_sort Z.leb sample.

(* Consider the intermediate tree that is constructed for merge_sort. *)
Definition the_tree := 
  Eval compute in 
   (match sample with a :: l => list_to_bin (Leaf a) l | _ => Leaf 0 end).

(* This test shows that the second subtree contains all the even values. *)
Compute match the_tree with 
  Node t1 t2 => merge_tree Z.leb t2
| Leaf x => x :: nil
end.

Compute match the_tree with
  Node t1 t2 => t2 | _ => Leaf (-1) end.

(* A third sorting algorithm is based on constructing a binary tree in such
  a way that it the small values are in the left most part.
  It can be done in a very simple way, but the tree is not always balanced.
  So the algorithm is easier to write, but the complexity is only as good
  as merge_sort when the input list is sufficiently random. *)

Inductive search_tree (A : Type) :=
  Snode (x : A) (t1 t2 : search_tree A)
| Sleaf.

Arguments Snode {A}.
Arguments Sleaf {A}.

Fixpoint insert_stree {A : Type} (cmp : A -> A -> bool)
  (x : A) (t : search_tree A) :=
  match t with
    Sleaf => Snode x Sleaf Sleaf
  | Snode y t1 t2 =>
    if cmp x y then Snode y (insert_stree cmp x t1) t2
    else Snode y t1 (insert_stree cmp x t2)
  end.

Fixpoint list_to_stree {A : Type} cmp (l : list A) :=
  match l with
    nil => Sleaf
  | a :: l' => insert_stree cmp a (list_to_stree cmp l')
  end.

Fixpoint search_tree_to_list {A : Type} (t : search_tree A) (l : list A) :=
  match t with
    Sleaf => l
  | Snode y t1 t2 => search_tree_to_list t1 (y :: search_tree_to_list t2 l)
  end.

Definition tree_sort {A : Type} (cmp : A -> A -> bool) (l : list A) : list A:=
  search_tree_to_list (list_to_stree cmp l) nil.

(* In the next section, we construct a list of values to sort in such
  a way that looks quite random. *)

(* If n divides x, this function returns 0, if n does not divide x, it
  returns n - 1.   For 0 and 1, this function is identity. *)

Definition test_prime_step x n:= 
      if orb (n =? 1) (n =? 0) then n
      else if x mod n =? 0 then 0 else (n - 1).

(* To test whether a number x is prime in a naive way, we test all
  numbers smaller than the square root to see if they divide x. *)

Definition test_prime (x : Z) :=
  (Z.iter (Z.sqrt x) (test_prime_step x) (Z.sqrt x)) =? 1.

Compute filter test_prime (map (fun n => 21200 + Z.of_nat n)(seq 0 100)).

Compute filter test_prime (map (fun n => 14444 + Z.of_nat n) (seq 0 100)).

Compute filter test_prime (map (fun n => 11010 + Z.of_nat n) (seq 0 100)).

(* Not an expert in generating random sequences, but this will do. *)
Definition sample2 := Eval vm_compute in
  snd (fst (Z.iter 10000
    (fun '(x, l, y) => 
      let y' := (14447 * x + 11027 * y + 127) mod 21247 in
      (x - 1, y' :: l, y'))
    (0, nil, 7))).

Definition s_sample2 :=
  Eval vm_compute in list_to_stree Z.leb sample2.

(* the search_tree data structure can also be used to check
  whether a given number is in the list, in much more efficient way
  than traversing a list. *)

Fixpoint present_stree {A : Type} (cmp eqb : A -> A -> bool)
  (x : A) (t : search_tree A) :=
  match t with
  | Snode y t1 t2 =>
    if eqb x y then true
    else
      if cmp x y then present_stree cmp eqb x t1
      else present_stree cmp eqb x t2
  | Sleaf => false
  end.

(* A few tests checking that all our sorting functions are consistent. *)

(* First checking that probably no data is lost. *)
Compute length sample2.
Compute length (tree_sort Z.leb sample2).
Compute length (merge_sort Z.leb sample2).
(* we should also do this, but it takes time
  Compute length (sort Z.leb sample2).
*)
(* Now we can check that both tree_sort and merge_sort return the same
value. *)

Fixpoint zip {A B : Type} (l1 : list A) (l2 : list B) : list (A * B) :=
  match l1, l2 with
  | a::l1, b::l2 => (a, b) :: zip l1 l2
  | _, _ => nil
  end.

Compute (forallb (fun '(x, y) => x =? y) (zip (tree_sort Z.leb sample2)
                    (merge_sort Z.leb sample2))).

(* insertion_sort is very good if the input is almost sorted. *)
Time Compute (rev sample).
Compute length (sort Z.leb (rev sample)).
(* merge_sort is pretty decent even when the input is already sorted. *)
Compute length (merge_sort Z.leb sample).
(* tree_sort only has good complexity if the input is close to random,
   but not if it is already sorted. *)

(* Time Compute length (tree_sort Z.leb sample). *)
(* Time Compute length (tree_sort Z.leb (rev sample)). *)

(* we can also replace merge_sort with sort, but again, this take time. *)
(* Compute (forallb (fun '(x, y) => x =? y) (zip (tree_sort Z.leb sample2)
                    (sort Z.leb sample2))) *)

(* The rest of this files contains a few question driven by curiosity. *)

(* You can check the presence of all numbers from sample in sample2. *)
Time Definition sample3' :=
  Eval vm_compute in
  filter (fun x => present_stree Z.leb Z.eqb x s_sample2) sample.

(* The following computation shows that not all numbers from 
  0-9999 appear in sample2. *)
Compute length sample3'.

(* Question: how would you construct sample3 by searching directly
   in the list sample2?
   You can use existing boolean test function on lists, like existsb. *)

(* Question: perform the opposite search: all elements of sample2 that are
   in sample.  The length of the list that you obtain is likely to not
   be the same. *)

(* Question: how would you check whether there are duplicates in sample2? *)
(* Can you return the list of all elements that appear at least twice in
   sample2?
   Write your code in such a way that this list contains no duplicates. *)

(* Question: can we build a balanced search_tree from a sorted list?
   the function list_to_search_tree will not produce a balanced result. *)