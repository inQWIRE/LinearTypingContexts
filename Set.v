Require Import HoTT.
Require Import Monad.
Require Import Permutation.
Require Import NCM.

Instance hset_option : forall B, IsHSet B -> IsHSet (option B).
Admitted.


(* Consider the propositional truncation of Permutation *)
Section MySet.

Open Scope list_scope.
Set Implicit Arguments.
Variable A : Type.

Definition TPermutation : list A -> list A -> Type :=
  fun ls1 ls2 => Trunc -1 (Permutation ls1 ls2).

Lemma tperm_skip : forall x ls1 ls2, TPermutation ls1 ls2 -> 
                   TPermutation (x :: ls1) (x :: ls2).
Proof. 
  intros x ls1 ls2 p.
  apply (Trunc_rec (fun p' => tr (perm_skip x p')) p).
Defined.

Definition set := quotient TPermutation.

Definition singleton (a : A) : set :=
  class_of TPermutation (a :: nil).

Definition empty : set := class_of TPermutation nil.


Variable R : A -> A -> Type.
Variable decR : forall a b, Decidable (R a b).

Fixpoint in_set' (x : A) (ls : list A) : Bool :=
  match ls with
  | nil => false
  | y::ls' => match decR x y with
                  | inl _ => true
                  | inr _ => in_set' x ls'
                  end
  end.

Lemma in_set_correct : forall x ls1 ls2,
      TPermutation ls1 ls2 -> in_set' x ls1 = in_set' x ls2.
Admitted.

Definition in_set (x : A) (X : set) : Bool :=
  (quotient_rec TPermutation (in_set' x) (in_set_correct x) X).
Notation " x ∈? X " := (in_set x X) (at level 80).
Notation " x ∈ X " := (x ∈? X = true) (at level 80).

Definition add (x : A) (X : set) : set.
Proof.
  exact (quotient_functor TPermutation TPermutation (cons x) (tperm_skip x) X).
Defined.

Definition disjoint_add (x : A) (X : set) : option set :=
  if x ∈? X then None else Some (add x X).

Fixpoint merge_into (ls : list A) (X : set) : option set :=
  match ls with
  | nil => Some X
  | a :: ls' => do X' ← disjoint_add a X;
                merge_into ls' X'
  end.

Lemma merge_set_correct : forall X ls1 ls2, TPermutation ls1 ls2 ->
      merge_into ls1 X = merge_into ls2 X.
Admitted.


Definition merge_set (X1 X2 : set) : option set :=
  quotient_rec TPermutation (fun l => merge_into l X2) 
           ( merge_set_correct X2) X1.
Notation "X ⋓ Y" := (merge_set X Y) (at level 40).

Lemma merge_set_empty : forall X, X ⋓ empty = Some X.
Admitted.

Lemma merge_set_assoc : forall a b c, (do x ← b ⋓ c; a ⋓ x) = (do x ← a ⋓ b; x ⋓ c).
Admitted.

Lemma merge_set_comm : forall a b, a ⋓ b = b ⋓ a.
Admitted.

Lemma merge_set_nilpotence : forall a, a <> empty -> a ⋓ a = None.
Admitted.

Instance PMonoid_set : PMonoid set :=
  { one' := empty
  ; m' := merge_set
  ; base' := fun x => x <> empty }.
Instance PMonoid_set_laws : PMonoid_Laws set.
Proof.
  split.
  - apply merge_set_empty.
  - apply merge_set_assoc.
  - apply merge_set_comm.
  - apply merge_set_nilpotence.
Defined.
(* so option set is an NCM *)

End MySet.

(* Specialize this to an association set *)



