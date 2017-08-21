Require Import HoTT.
Set Implicit Arguments.

Section Permutation.

Variable A : Type.

Open Scope list_scope.
Inductive Permutation : list A -> list A -> Type :=
| perm_nil: Permutation nil nil
| perm_skip x l l' : Permutation l l' -> Permutation (x::l) (x::l')
| perm_swap x y l : Permutation (y::x::l) (x::y::l)
| perm_trans l l' l'' :
    Permutation l l' -> Permutation l' l'' -> Permutation l l''.

Lemma list_inv_contr : forall {a : A} {l}, nil <> a :: l.
Proof.
  intros a l H.
  set (P := fun (l : list A) => match l with
                                | nil => Unit
                                | _ :: _ => Empty
                                end).
  exact (transport P H tt).
Defined.

Theorem Permutation_nil : forall (l : list A), Permutation nil l -> l = nil.
Proof.
  intros l pf. remember (nil : list A) as l' eqn:H_l'.
  generalize dependent H_l'.
  induction pf; intros H_l'; auto.
  - exact (Empty_rec (list_inv_contr H_l')).
  - exact (Empty_rec (list_inv_contr H_l')).
  - refine (IHpf2 _ @ (IHpf1 H_l')).
    refine (H_l' @ (IHpf1 H_l')^).
Defined.

Theorem Permutation_nil_cons : forall (l : list A) (x : A),
 ~ Permutation nil (x::l).
Proof.
  intros l x H.
  apply Permutation_nil in H.
  apply (list_inv_contr H^).
Defined.


Theorem Permutation_refl : forall l : list A, Permutation l l.
Proof.
  induction l; auto.
  - exact perm_nil.
  - exact (perm_skip _ IHl).
Defined.

Theorem Permutation_sym : forall l l' : list A,
 Permutation l l' -> Permutation l' l.
Proof.
  intros l l' H.
  induction H.
  - exact perm_nil.
  - exact (perm_skip _ IHPermutation).
  - exact (perm_swap _ _ _).
  - apply (perm_trans IHPermutation2 IHPermutation1).
Defined.


Lemma Permutation_in : forall l1 l2 (a : A) l,
      Permutation l (l1 ++ l2) ->
      Permutation (a :: l) (l1 ++ a :: l2).
Proof.
  induction l1 as [ | b l1]; intros l2 a l H; simpl in *; [apply perm_skip; auto|].
  apply perm_trans with (l' := a :: (b :: l1 ++ l2)); [apply perm_skip; auto|].
  apply perm_trans with (l' := b :: a :: l1 ++ l2); [apply perm_swap | ].
  apply perm_skip. apply IHl1; auto. apply Permutation_refl.
Defined.

End Permutation.

Hint Resolve Permutation_refl perm_nil perm_skip.


(*
Section Permutation_properties.

Variable A:Type.

Implicit Types a b : A.
Implicit Types l m : list A.


Theorem Permutation_in : forall (l l' : list A) (x : A),
 Permutation l l' -> In x l -> In x l'.
*)