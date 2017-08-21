Require Import HoTT.

Set Implicit Arguments.

Section Multiset.

Variable A : Type.
Variable decA : DecidablePaths A.


Inductive multiset : Type :=
  Bag : (A -> nat) -> multiset.

Definition EmptyBag := Bag (fun a:A => 0). Print sum.  Search DecidablePaths.

Definition SingletonBag (a:A) :=
    Bag (fun a':A => match dec_paths a a' with
                       | inl _ => 1
                       | inr _ => 0
                     end).


Definition multiplicity (m:multiset) (a:A) : nat := let (f) := m in f a.

Definition meq (m1 m2:multiset) :=
    forall a:A, multiplicity m1 a = multiplicity m2 a.


Lemma meq_refl : forall x:multiset, meq x x.
Proof.
  intros x a. reflexivity. 
Defined.

Lemma meq_trans : forall x y z:multiset, meq x y -> meq y z -> meq x z.
Proof.
  intros x y z H1 H2 a.
  exact (H1 a @ H2 a).
Defined.

Lemma meq_sym : forall x y:multiset, meq x y -> meq y x.
Proof.
  intros x y H a. exact (H a)^.
Defined.

  Definition munion (m1 m2:multiset) :=
    Bag (fun a:A => multiplicity m1 a + multiplicity m2 a)%nat.

Lemma multiplicity_munion : forall m1 m2 a,
      multiplicity (munion m1 m2) a = (multiplicity m1 a + multiplicity m2 a)%nat.
Proof.
  auto.
Defined.

Lemma munion_empty_left : forall x:multiset, meq x (munion EmptyBag x).
Proof.
  intros x a. reflexivity.
Defined.

Lemma munion_empty_right : forall x:multiset, meq x (munion x EmptyBag).
Proof.
  intros x a. simpl.
  rewrite <- nat_plus_n_O. reflexivity.
Defined.

Lemma munion_comm : forall x y:multiset, meq (munion x y) (munion y x).
Proof.
  intros x y a; simpl.
  apply nat_plus_comm.
Defined.

Lemma nat_plus_ass : forall x y z, ((x + y) + z = x + (y + z))%nat.
Proof.
  induction x; intros; auto.
  simpl. rewrite IHx; auto.
Defined.

Lemma munion_ass :
    forall x y z:multiset, meq (munion (munion x y) z) (munion x (munion y z)).
Proof.
  intros x y z a; simpl.
  apply nat_plus_ass.
Defined.

Lemma meq_left :
    forall x y z:multiset, meq x y -> meq (munion x z) (munion y z).
Proof.
  intros x y z H a; simpl.
  rewrite (H a). reflexivity.
Defined.

Lemma meq_right :
    forall x y z:multiset, meq x y -> meq (munion z x) (munion z y).
Proof.
  intros x y z H a; simpl.
  rewrite (H a). reflexivity.
Defined.

Lemma meq_munion : forall x x' y y' : multiset,
    meq x x' -> meq y y' -> meq (munion x y) (munion x' y').
Proof.
  intros x x' y y' Hx Hy.
  refine (meq_trans (meq_left _ Hx) (meq_right _ Hy)).
Defined.



Lemma meq_inv_contradiction : forall m,
    (exists a, multiplicity m a > 0) ->
    ~ meq EmptyBag m.
Proof.
  intros m [a Ha] Hm.
  unfold meq in Hm.
  rewrite <- Hm in Ha; exact Ha.
Defined.


End Multiset.

Unset Implicit Arguments.

Arguments EmptyBag {A}. 
Arguments SingletonBag {A} {decA}.

Hint Resolve meq_refl munion_empty_left munion_empty_right munion_comm munion_ass.