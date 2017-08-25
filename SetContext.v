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

Definition singleton_set (a : A) : set :=
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
End MySet.

Arguments empty {A}.


About quotient_functor.
Definition set_functor : forall (A B : Type) (f : A -> B),
           (forall x y : list A, Permutation x y -> 
                                 Permutation (fmap f x) (fmap f y)) ->
           set A -> set B.
Proof.
  intros A B f H.
  About quotient_functor.
  assert (H' : forall x y : list A, TPermutation x y -> 
                                    TPermutation (fmap f x) (fmap f y)). 
  { intros x y.
    apply (Trunc_functor (-1)).
    apply H.
  }
  apply (quotient_functor _ _ (fmap f) H').
Defined.

(*****************************************)
(* Specialize this to an association set *)
(*****************************************)

Section SetContext.

Variable A : Type.
Definition PreCtx (X : Type) := set (X * A).

Definition shift {X} : PreCtx X -> PreCtx (option X).
Proof. 
  apply (set_functor (fun (z : X * A) => let (x,a) := z in (Some x, a))).
  intros x y p.
  induction p; simpl; auto.
  - destruct x as [x Q1], y as [y Q2]; simpl.
    apply perm_swap.
  - apply (perm_trans IHp1 IHp2).
Defined.

End SetContext.



Definition R {A X} (z1 z2 : X * A) : Type :=
  (fst z1) = (fst z2).
  
About merge_set.

Lemma decR : forall {A X} `{DecidablePaths X} (z1 z2 : X * A), Decidable (R z1 z2).
Proof.
  intros. apply H.
Defined.


Instance PMonoid_set A X `{decX : DecidablePaths X} : PMonoid (PreCtx A X) :=
  { one' := empty
  ; m' := merge_set R decR
  ; base' := fun x => x <> empty }.
Instance PMonoid_set_laws A X `{decX : DecidablePaths X} : PMonoid_Laws (PreCtx A X).
Proof.
  split.
  - apply merge_set_empty.
  - apply merge_set_assoc.
  - apply merge_set_comm.
  - apply merge_set_nilpotence.
Defined.


(* So option(PreCtx X) is an NCM *)
Definition Ctx X A := option (PreCtx A X).
Definition extend {X A : Type} (Γ : Ctx X A) (a : A) : Ctx (option X) A :=
  do Γ' ← (Γ : option (PreCtx A X));
  return_ (add (None,a) (shift Γ')).
Definition singleton {X A : Type} (x : X) (a : A) : Ctx X A :=
  Some (singleton_set (x,a)).


Definition fmap_Ctx {A X Y} (f : X -> Y): Ctx X A -> Ctx Y A.
Proof.
  apply (@fmap option optionF).
  apply (set_functor (fun (z : X * A) => let (x,a) := z in (f x, a))).
  intros x y pf.
  induction pf; simpl; auto.
  - apply perm_swap.
  - apply (perm_trans IHpf1 IHpf2).
Defined.

Instance CtxF {A} : Functor (fun Z => Ctx Z A) := {fmap := @fmap_Ctx A}.

Section CtxFunctor.

Variable A X Y : Type.
Variable (f : X -> Y).
Variable decX : `{DecidablePaths X}.
Variable decY : `{DecidablePaths Y}.


Lemma fmap_merge : forall (Γ1 Γ2 : Ctx X A),
                   fmap f (Γ1 · Γ2) = fmap f Γ1 · fmap f Γ2.
Admitted.

Lemma fmap_singleton : forall (x : X) (a : A),
                       fmap f (singleton x a) = singleton (f x) a.
Admitted.

Lemma fmap_extend : forall (Γ : Ctx X A) (a : A),
      fmap (@fmap option optionF _ _ f) (extend Γ a) = extend (fmap f Γ) a.
Admitted.


Lemma fmap_None_inv : forall (Γ : Ctx X A), fmap f Γ = None -> Γ = None.
Admitted.

End CtxFunctor.