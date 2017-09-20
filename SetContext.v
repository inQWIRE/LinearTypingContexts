Require Import HoTT.
Require Import Monad.
Require Import Permutation.
Require Import Monoid.
Require Import TypingContext.

Instance hset_option : forall B, IsHSet B -> IsHSet (option B).
Admitted.

Set Implicit Arguments.

(* Consider the propositional truncation of Permutation *)
Section MySet.

Open Scope list_scope.
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
Definition from_list ls : set := class_of _ ls.



Lemma from_list_eq : forall ls1 ls2, Permutation ls1 ls2 ->
                     from_list ls1 = from_list ls2.
Proof.
  intros. 
  apply related_classes_eq.
  apply tr. 
  auto.
Defined.


Lemma IsHSet_implies_IsHProp : forall X, IsHSet X -> forall (x y : X), IsHProp (x = y).
Proof.
  auto.
Defined.


Lemma bool_HProp : forall (a b : Bool), IsHProp (a = b).
Proof. apply IsHSet_implies_IsHProp. apply hset_bool. Defined.


Lemma hset_set : IsHSet set.
Proof.
  apply quotient_set.
Defined.

Lemma hprop_set : forall (X Y : set), IsHProp (X = Y).
Proof. apply IsHSet_implies_IsHProp. apply hset_set.
Defined.

Lemma hprop_option_set : forall (X Y : option (set)), IsHProp (X = Y).
Proof. apply IsHSet_implies_IsHProp. apply hset_option. apply hset_set.
Defined.

(*************************)
(*** Recursion Schemes ***)
(*************************)

Section set_rec.
  Variable B : Type.
  Variable B_HSet : IsHSet B.
  Variable dclass : list A -> B.
  Variable dclass_eq : forall ls1 ls2 : list A, Permutation ls1 ls2 -> 
           dclass ls1 = dclass ls2.
  Definition set_rec : set -> B.
  Proof.
    apply (quotient_rec TPermutation dclass).
    unfold TPermutation. 
    intros ls1 ls2 trunc.
    exact (Trunc_rec (@dclass_eq ls1 ls2) trunc).
  Defined.
End set_rec.


Section set_ind.
  Variable P : set -> Type.
  Variable P_HProp : forall (X : set), IsHProp (P X).

  Let P_HProp' : forall (X : set) (x y : P X), x = y.
  Proof. apply P_HProp. Defined.

  Let P_HSet : forall X : set, IsHSet (P X).
  Proof. 
    intros X. apply trunc_succ.
  Defined.

  Variable dclass : forall (ls : list A), P (from_list ls).

  Local Lemma P_mere_relation : forall (X : set) (x y : P X), IsHProp (x = y).
  Proof. intros. apply trunc_succ. Defined.


  Local Lemma dclass_eq : forall (ls1 ls2 : list A) 
                            (perm : Permutation ls1 ls2),
    transport P (related_classes_eq TPermutation (tr perm)) (dclass ls1) 
    = dclass ls2.
  Proof.
    intros. apply P_HProp'. 
  Defined.

  Definition set_ind : forall (X : set), P X.
  Proof. 
    apply (quotient_ind TPermutation _ dclass).
    intros ls1 ls2. 
    apply Trunc_ind; intros; [apply P_mere_relation | apply dclass_eq ]. 
  Defined.

End set_ind.


Section set_rec2.
  Variable B : Type.
  Variable B_HSet : IsHSet B.
  Variable dclass : list A -> list A -> B.
  Variable dclass_eq : forall ls1 ls2 : list A, Permutation ls1 ls2 -> 
                       forall ls1' ls2' : list A, Permutation ls1' ls2' ->
           dclass ls1 ls1' = dclass ls2 ls2'.

  Definition set_rec2 : set -> set -> B.
  Proof.
    transparent assert (dclass' : (list A -> set -> B)).
    { intros ls1. apply set_rec with (dclass := dclass ls1); auto. }
    assert (dclass'_eq : forall ls1 ls2, Permutation ls1 ls2 ->
                     forall X, dclass' ls1 X = dclass' ls2 X).
    { intros ls1 ls2 perm.
      assert (forall b1 b2 : B, IsHProp (b1 = b2)) by auto.
      apply set_ind; intros; auto.
      simpl. apply dclass_eq; auto. 
    }
    intros X Y.
    generalize dependent X.
    apply set_rec with (dclass := fun ls1 => dclass' ls1 Y); auto.
  Defined.
End set_rec2.

Section set_ind2.
  Variable P : set -> set -> Type.
  Variable P_HProp : forall (X Y : set), IsHProp (P X Y).

  Let P_HProp' : forall (X Y : set) (x y : P X Y), x = y.
  Proof. apply P_HProp. Defined.

  Let P_HSet : forall X Y : set, IsHSet (P X Y).
  Proof. 
    intros X Y. apply trunc_succ.
  Defined.

  Variable dclass : forall (ls1 ls2 : list A), P (from_list ls1) (from_list ls2).

  Let P_mere_relation : forall (X Y : set) (x y : P X Y), IsHProp (x = y).
  Proof. intros. apply trunc_succ. Defined.

  Definition set_ind2 : forall (X Y : set), P X Y.
  Proof. 
    intros X.
    apply set_ind; auto.
    intros ls2.
    generalize dependent X.
    apply set_ind; auto.
  Defined.

End set_ind2.

Section set_rec3.
  Variable B : Type.
  Variable B_HSet : IsHSet B.
  Variable dclass : list A -> list A -> list A -> B.
  Variable dclass_eq : forall ls1 ls2 : list A, Permutation ls1 ls2 -> 
                       forall ls1' ls2' : list A, Permutation ls1' ls2' ->
                       forall ls1'' ls2'' : list A, Permutation ls1'' ls2'' -> 
           dclass ls1 ls1' ls1''= dclass ls2 ls2' ls2''.

  Let B_HProp : forall (b c : B), IsHProp (b = c).
  Proof. auto. Defined.

  Definition set_rec3 : set -> set -> set -> B.
  Proof.
    transparent assert (dclass' : (list A -> set -> set -> B)).
    { intros ls1.
      apply set_rec2 with (dclass := fun ls2 ls3 => dclass ls1 ls2 ls3); auto.
    }
    intros X Y Z. generalize dependent X.
    assert (dclass'_eq : forall ls1 ls2, Permutation ls1 ls2 ->
            dclass' ls1 Y Z = dclass' ls2 Y Z).
    { intros ls1 ls2 perm.
      generalize dependent Y; generalize dependent Z.
      apply set_ind2; auto. 
      intros. apply dclass_eq; auto.
    }
    apply set_rec with (dclass := fun ls1 => dclass' ls1 Y Z); auto.
  Defined.    

End set_rec3.

Section set_ind3.
  Variable P : set -> set -> set -> Type.
  Variable P_HProp : forall (X Y Z : set), IsHProp (P X Y Z).

  Let P_HProp' : forall (X Y Z : set) (x y : P X Y Z), x = y.
  Proof. apply P_HProp. Defined.

  Let P_HSet : forall X Y Z : set, IsHSet (P X Y Z).
  Proof. 
    intros X Y Z. apply trunc_succ.
  Defined.

  Variable dclass : forall (ls1 ls2 ls3 : list A), 
           P (from_list ls1) (from_list ls2) (from_list ls3).

  Let P_mere_relation : forall (X Y Z : set) (x y : P X Y Z), IsHProp (x = y).
  Proof. intros. apply trunc_succ. Defined.

  Definition set_ind3 : forall (X Y Z : set), P X Y Z.
  Proof. 
    intros X.
    apply set_ind2; auto.
    intros ls2 ls3.
    generalize dependent X.
    apply set_ind; auto.
  Defined.

End set_ind3.


Definition singleton_set (a : A) : set := from_list (a :: nil).

Definition empty : set := from_list nil.


End MySet.
Hint Resolve hset_set.
Hint Resolve hset_bool.
Hint Resolve bool_HProp.
Hint Resolve hprop_set.
Hint Resolve hprop_option_set.


Section set_list_functor.
  Variable A : Type.
  Variable B : Type.

  About quotient_functor.
  Variable f : list A -> list B.
  Variable f_correct : forall ls1 ls2 : list A, Permutation ls1 ls2 ->
                                                Permutation (f ls1) (f ls2).
  Definition set_list_functor : set A -> set B.
  Proof.
    apply (quotient_functor _ _ f).
    intros ls1 ls2.
    unfold TPermutation.
    apply (Trunc_functor _ (@f_correct ls1 ls2)).
  Defined.
End set_list_functor.

Section defns.
  Variable A : Type.

Section add.

Definition add (x : A) : set A -> set A.
Proof.
  apply (set_list_functor (cons x)).
  intros. apply perm_skip; auto.
Defined.
End add.


Fixpoint append ls1 ls2 : list A :=
  match ls1 with
  | nil => ls2
  | a :: ls1' => a :: (append ls1' ls2)
  end.

Lemma append_correct : forall ls1 ls2, Permutation ls1 ls2 ->
                           forall ls1' ls2', Permutation ls1' ls2' ->
                           Permutation (append ls1 ls1') (append ls2 ls2').
Admitted.
  
Definition merge : set A -> set A -> set A.
Proof.
  apply set_rec2 with (dclass := fun ls1 ls2 => from_list (append ls1 ls2)); 
    auto.
  intros. 
  apply from_list_eq.
  apply append_correct; auto.
Defined.


Arguments empty {A}.
Notation "∅" := empty.
Notation "X ∪ Y" := (merge X Y) (at level 40).

Section merge.



(*Lemma merge_correct : (from_list ls1) ⋓ (from_list ls2) = Some ( *)
(* Properties of merge: *)
(* X ∪ ∅ = Some X *)
(* X ∪ Y = Y ∪ X *)
(* X ∪ (Y ∪ Z) = (X ∪ Y) ∪ Z *)
(* X <> ∅ -> X ∪ X = None *)

Lemma append_nil_r : forall ls, append ls nil = ls.
Proof.
  induction ls; auto.
  simpl. 
  rewrite IHls; auto.
Defined.

Lemma merge_empty_r : forall X, X ∪ ∅ = X.
Proof.
  apply set_ind; intros; auto.
  simpl. rewrite append_nil_r; auto.
Defined.

Lemma append_cons : forall ls1 ls2 a, 
    Permutation (append ls1 (a :: ls2)) (a :: (append ls1 ls2)).
Proof.
  induction ls1 as [ | b ls1]; intros; auto.
  simpl.
  apply perm_trans with (l' := b :: a :: append ls1 ls2); auto.
  apply perm_swap.
Defined.


Lemma append_comm : forall ls1 ls2,
      Permutation (append ls1 ls2) (append ls2 ls1).
Proof.
  induction ls1 as [ | a ls1]; intros ls2; simpl.
  - rewrite append_nil_r; auto.
  - eapply perm_trans; [ | apply Permutation_sym; apply append_cons].
    auto.
Defined.

Lemma merge_comm : forall a b, a ∪ b = b ∪ a.
Proof.
  apply set_ind2; auto.
  intros; simpl.
  apply from_list_eq.
  apply append_comm.
Defined.

Lemma append_assoc : forall ls1 ls2 ls3, 
    append (append ls1 ls2) ls3 = append ls1 (append ls2 ls3).
Admitted.

Lemma merge_assoc : forall a b c, (a ∪ b) ∪ c = a ∪ (b ∪ c).
Proof.
  apply set_ind3; auto.
  intros; simpl.
  rewrite append_assoc. reflexivity.
Defined.

End merge.



Arguments empty {A}.

Section set_functor.
  Variable B : Type.
  Variable (f : A -> B).

  Let f' : list A -> list B := fmap f.

  Let f'_correct : forall ls1 ls2, Permutation ls1 ls2 -> Permutation (f' ls1) (f' ls2).
  Proof.
    intros ls1 ls2 perm. unfold f'.
    induction perm; simpl; auto.
    - apply perm_swap; auto.
    - eapply perm_trans; eauto.
  Defined.

  Definition set_fmap : set A -> set B.
  Proof.
    apply set_list_functor with (f := f'); auto.
  Defined.    

End set_functor.

(* We want a relation here (as opposed to equality) because when we think
   about e.g. typing contexts, we only care about equality up to 
   the first argument e.g. we want x:Bool ∪ x:Nat to fail
*)
  Context (R : relation A) `{relR : is_mere_relation A R}
          `{reflexiveR : Reflexive _ R} 
          `{transitiveR : Transitive _ R} 
          `{symmetricR : Symmetric _ R}
          `{decR : forall x y, Decidable (R x y)}.

Definition b_decR a b : Bool :=
  if decR a b then true else false.
Notation "a R? b" := (b_decR a b) (at level 40).


Lemma R_HProp : forall a b, IsHProp (R a b).
Proof. auto. Defined.
Hint Resolve R_HProp.

Lemma decR_true : forall a b (pf : R a b), a R? b = true.
Proof.
  intros.
  unfold b_decR.
  destruct (decR a b) as [pf' | ]; auto.
  contradiction.
Defined.

Lemma decR_false : forall a b (pf : ~ R a b), a R? b = false.
Proof.
  intros.
  unfold b_decR.
  destruct (decR a b) as [pf' | pf']; auto. 
  contradiction.
Defined.


Section in_set.
Fixpoint in_list (x : A) (ls : list A) : Bool :=
  match ls with
  | nil => false
  | y::ls' => (x R? y) || (in_list x ls')
  end.

Lemma in_set_correct : forall ls1 ls2, Permutation ls1 ls2 ->
    forall x, in_list x ls1 = in_list x ls2.
Proof.
  intros ls1 ls2 p; induction p; intros; auto.
  - simpl. destruct (b_decR x0 x); simpl; auto.
  - simpl. destruct (b_decR x0 y); destruct (b_decR x0 x); auto.
  - rewrite IHp1, IHp2. reflexivity.
Defined.

Definition in_set (x : A) : set A -> Bool.
Proof.
  apply (set_rec _ (in_list x)).
  intros; apply in_set_correct; auto.
Defined.

End in_set.

Notation " x ∈? X " := (in_set x X) (at level 80).
Notation " x ∈ X " := (x ∈? X = true) (at level 80).

Section disjoint.

Fixpoint disjoint_list (ls1 ls2 : list A) : Bool :=
  match ls1 with
  | nil => true
  | a :: ls1' => negb (in_list a ls2) && disjoint_list ls1' ls2
  end.


Lemma disjoint_list_correct : forall ls1 ls2,
      Permutation ls1 ls2 ->
      forall ls1' ls2', Permutation ls1' ls2' ->
      disjoint_list ls1 ls1' = disjoint_list ls2 ls2'.
Admitted.

Lemma disjoint_list_nil_r : forall ls, disjoint_list ls nil = true.
Proof. induction ls; auto. Qed.


Definition disjoint : set A -> set A -> Bool.
Proof.
  apply set_rec2 with (dclass := disjoint_list); auto.
  intros. apply disjoint_list_correct; auto.
Defined.

End disjoint.
Notation "X ⊥⊥ Y" := (disjoint X Y) (right associativity, at level 46).

Open Scope bool_scope.

Lemma disjoint_nilpotent : forall a, a <> empty -> a ⊥⊥ a = false.
Admitted.

Lemma disjoint_comm : forall a b, a ⊥⊥ b = b ⊥⊥ a.
Admitted.


Lemma disjoint_merge_r : forall a b c, a ⊥⊥ (merge b c) = (a ⊥⊥ b) && (a ⊥⊥ c).
Admitted.

Lemma disjoint_merge_l : forall a b c, (merge a b) ⊥⊥ c = (a ⊥⊥ c) && (b ⊥⊥ c).
Admitted.

Lemma singleton_disjoint : forall a b, 
      singleton_set a ⊥⊥ singleton_set b = negb (a R? b).
Proof. intros. simpl. destruct (a R? b); auto. Qed.


Lemma merge_append : forall ls1 ls2, 
      (from_list ls1) ∪ (from_list ls2) = from_list (ls1 ++ ls2).
Proof.
  induction ls1 as [ | x1 ls1]; intros; auto.
Qed.


(* PROPERTIES *)

Lemma disjoint_empty : forall X, X ⊥⊥ empty = true.
Proof.
  apply set_ind; auto.
  induction ls; auto.
Defined.

Lemma in_list_R : forall a b ls, R a b -> in_list a ls = in_list b ls.
Proof.
  intros a b ls pf_R. induction ls; auto.
  simpl.
  destruct (decR a a0) as [R_a_a0 | R_a_a0].
  * assert (R_b_a0 : R b a0) by exact (transitiveR (symmetricR pf_R) R_a_a0).
    repeat rewrite decR_true; simpl; auto.
  * assert (R_b_a0 : ~ R b a0).
    { intros R_b_a0. apply R_a_a0.
      exact (transitiveR pf_R R_b_a0). }
    repeat rewrite decR_false; simpl; auto.
Defined.

Definition add_in_property a b X := (a ∈? X) = (b ∈? X).

Lemma add_R : forall a b X, R a b -> add_in_property a b X.
Proof.
  intros a b X pf_R. generalize dependent X. 
  set (dclass := ((fun ls => in_list_R ls pf_R) 
              : forall ls, add_in_property a b (from_list ls))).
  simpl in dclass.
  apply (set_ind _ _ dclass).
Defined.

Lemma add_in : forall a b X, R a b -> (a ∈? add b X) = true.
  Proof.
  intros a b X pf_R. generalize dependent X.
  apply (set_ind); intros; auto.
  simpl.
  rewrite decR_true; auto.
Defined.

Lemma add_not_in : forall a b, ~ R a b -> forall X, (a ∈? add b X) = (a ∈? X).
Proof.
  intros a b pf_R.
  apply set_ind; intros; auto.
  simpl.
  rewrite decR_false; auto.
Defined.

Lemma add_symmetric : forall a b,
      ~ R a b -> forall X, add a (add b X) = add b (add a X).
Proof.
  intros a b pf_R.
  apply set_ind; intros; auto.
  simpl. 
    apply related_classes_eq.
    apply tr.
    apply perm_swap.
Defined.



End defns.

(*****************************************)
(* Specialize this to an association set *)
(*****************************************)


Arguments empty {A}.
Notation "∅" := empty.
Notation "X ∪ Y" := (merge X Y) (at level 40).

Section SetContext.

Variable A : Type.
Definition PreCtx X := set (X * A).

Definition shift {X} : PreCtx X -> PreCtx (option X) :=
  set_fmap (fun (z : X * A) => let (x,a) := z in (Some x, a)).

Variable X : Type.
Context `{decX : DecidablePaths X}.

Definition R (z1 z2 : X * A) : Type :=
  (fst z1) = (fst z2).

Notation "X ⊥⊥ Y" := (@disjoint _ R _ _ _ _ _ X Y) (right associativity, at level 46).

Hint Unfold R.
Instance decR : forall (z1 z2 : X * A), 
    Decidable (R z1 z2).
Proof.
  intros z1 z2. apply decX.
Defined.

About merge.
Global Instance reflexiveR : Reflexive R.
Proof.
  intros [x a]. unfold R. auto.
Defined.
Global Instance symmetricR : Symmetric R.
Proof.
  intros [x a] [y b]. unfold R.
  simpl; intros eq; exact (eq^).
Defined.
Global Instance transitiveR : Transitive R.
Proof.
  intros [x a] [y b] [z c]. unfold R.
  simpl.
  apply Overture.concat.
Defined.

About merge.

Definition disjoint_merge : PreCtx X -> PreCtx X -> option (PreCtx X).
Proof.
  intros Γ1 Γ2. About disjoint.
  set (b := @disjoint _ R _ _ _ _ _ Γ1 Γ2).
  exact (if b then Some (Γ1 ∪ Γ2) else None).
Defined.

Ltac true_false_contradiction :=
  match goal with
  | [ H : true = false |- _ ] => exact (Empty_rec (true_ne_false H))
  | [ H : false = true |- _ ] => exact (Empty_rec (false_ne_true H))
  end.


Open Scope bool_scope.
Lemma andb_true_r : forall b, b && true = b.
Proof. destruct b; auto.
Defined.

Lemma andb_false_r : forall b, b && false = false.
Proof. destruct b; auto. Defined.

Lemma ifb_eta : forall (b : Bool), (if b then true else false) = b.
Proof.  destruct b; auto. Defined.

Lemma andb_true_inv1 : forall b1 b2, b1 && b2 = true -> b1 = true.
Proof. destruct b1; auto. Defined.

Lemma andb_true_inv2 : forall b1 b2, b1 && b2 = true -> b2 = true.
Proof. destruct b2; auto. destruct b1; auto. Defined.

Lemma negb_or : forall b1 b2, negb (b1 || b2) = negb b1 && negb b2.
Proof.
  destruct b1, b2; auto.
Qed.

Lemma negb_and : forall b1 b2, negb (b1 && b2) = negb b1 || negb b2.
Proof. destruct b1, b2; auto. Qed.

Lemma andb_orb_r : forall b1 b2 b3, b1 && (b2 || b3) = (b1 && b2) || (b1 && b3).
Proof.
Admitted.

Lemma andb_orb_l : forall b1 b2 b3, (b1 || b2) && b3 = (b1 && b3) || (b2 && b3).
Proof.
Admitted.


Lemma andb_assoc : forall b1 b2 b3, b1 && (b2 && b3) = (b1 && b2) && b3.
Proof. destruct b1, b2, b3; auto. Qed.

Global Instance PPCM_set : PPCM (PreCtx X) :=
  { one' := ∅
  ; m' := disjoint_merge }.

Global Instance PPCM_set_laws : PPCM_Laws (PreCtx X).
Proof.
  split.
  - unfold m'. simpl. 
    unfold disjoint_merge.
    intros Γ.
    rewrite disjoint_empty.
    rewrite merge_empty_r. 
    reflexivity.
  - intros. 
    unfold m'; simpl.
    unfold disjoint_merge.
    remember (b ⊥⊥ c) as disj_b_c eqn:H_b_c.
    remember (a ⊥⊥ b) as disj_a_b eqn:H_a_b.
    destruct disj_a_b; destruct disj_b_c; simpl; auto.
    * rewrite disjoint_merge_r.
      rewrite disjoint_merge_l.
      rewrite H_a_b. simpl.
      rewrite H_b_c. 
      rewrite andb_true_r.
      rewrite merge_assoc. 
      reflexivity.
    * rewrite disjoint_merge_l. rewrite H_b_c.
      rewrite andb_false_r. reflexivity.
    * rewrite disjoint_merge_r. rewrite H_a_b.
      auto.
  - unfold m'; simpl. unfold disjoint_merge.
    intros a b.
    rewrite disjoint_comm.
    rewrite merge_comm.
    reflexivity.
Defined.


Section merge_disjoint3.
  About set_ind3.
  Let P (Γ1 Γ2 Γ3 : set (X * A)) := 
      Γ1 ∪ Γ2 ⊥⊥ Γ3 = (Γ1 ⊥⊥ Γ3) && (Γ2 ⊥⊥ Γ3).
(*(Γ1 ⊥⊥ Γ2) && (Γ1 ∪ Γ2 ⊥⊥ Γ3) = (Γ1 ⊥⊥ Γ2) && (Γ1 ⊥⊥ Γ3) && (Γ2 ⊥⊥ Γ3)*)
  Let H : forall Γ1 Γ2 Γ3, IsHProp (P Γ1 Γ2 Γ3). intros. auto.
    unfold P. auto. 
  Qed.

  Let P_list : forall ls1 ls2 ls3, P (from_list ls1) (from_list ls2) (from_list ls3).
  Proof.
    induction ls1 as [ | [x1 a1] ls1]; 
    destruct ls2 as [ | [x2 a2] ls2], ls3 as [ | [x3 a3] ls3]; unfold P; 
    simpl; intros; auto.
    - rewrite append_nil_r.
      rewrite disjoint_list_nil_r.
      auto.
    - unfold b_decR, decR; simpl.
      rewrite append_nil_r.
      rewrite andb_true_r.
      reflexivity.
    - repeat rewrite disjoint_list_nil_r. auto.
    - unfold b_decR, decR in *; simpl in *.
      unfold P in IHls1; simpl in IHls1.
      destruct (decX x1 x2); simpl in *.
      * (* x1 = x2 *) HoTT_subst. 
        rewrite IHls1. simpl. 
        unfold b_decR; simpl.
        destruct (decX x1 x3); simpl; auto.
        repeat rewrite andb_assoc. reflexivity.
      * (* x2 <> x2 *)
        destruct (decX x1 x3); simpl; auto.
        rewrite IHls1. simpl.
        unfold b_decR; simpl.
        repeat rewrite andb_assoc. reflexivity.
  Qed.


  Lemma merge_disjoint3 : forall Γ1 Γ2 Γ3, P Γ1 Γ2 Γ3. 
  Proof. 
    exact (set_ind3 P H P_list).
  Qed.
End merge_disjoint3.


Global Instance PTypingContext_set : PTypingContext X A (PreCtx X) :=
  { singleton' := fun x a => singleton_set (x,a) }.
Global Instance PTypingContext_set_Laws : PTypingContext_Laws X A (PreCtx X).
Proof.
  split.
  - intros; simpl. unfold disjoint_merge. 
    remember (Γ1 ⊥⊥ Γ2) as b12 eqn:H12.
    remember (Γ1 ⊥⊥ Γ3) as b13 eqn:H13.
    remember (Γ2 ⊥⊥ Γ3) as b23 eqn:H23.
    apply (@Overture.concat _ _ (b12 && ((Γ1 ∪ Γ2) ⊥⊥ Γ3))).
    { destruct b12; auto. simpl. destruct (Γ1 ∪ Γ2 ⊥⊥ Γ3); auto. }
    apply (@Overture.concat _ _ (b12 && b13 && b23));
      [ | destruct b12, b13, b23; auto].
    HoTT_subst.
    rewrite merge_disjoint3.
    repeat rewrite andb_assoc.
    reflexivity.
  - unfold m'. simpl.
    intros.
    unfold disjoint_merge.
    rewrite singleton_disjoint. unfold b_decR, decR. simpl.
    destruct (decX x y); simpl; auto.
    * split; auto.
    * split; intros contr;
      [exact (Empty_rec (Some_neq_None contr)) | contradiction].
Qed.

End SetContext.    

    

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
  apply (set_fmap (fun (z : X * A) => let (x,a) := z in (f x, a))).
Defined.

Instance CtxF {A} : Functor (fun Z => Ctx Z A) := {fmap := @fmap_Ctx A}.

Section Ctx_ind.
  Variable A : Type.
  Variable X : Type.
  Variable decX : `{DecidablePaths X}.
  Variable P : Ctx X A -> Type.
  Variable P_HProp : forall Γ, IsHProp (P Γ).
  Variable P_None : P ⊥.
  Variable P_Some  : forall ls, P (Some (from_list ls)).
  Definition Ctx_ind : forall Γ, P Γ.
  Proof.
    destruct Γ as [ Γ | ]; auto.
    generalize dependent Γ. apply set_ind; auto.
  Defined.
End Ctx_ind.
About Ctx_ind.
Arguments Ctx_ind {A X decX}.

Section Ctx_ind2.
  Variable A : Type.
  Variable X : Type.
  Variable decX : `{DecidablePaths X}.
  Variable P : Ctx X A -> Ctx X A -> Type.
  Variable P_HProp : forall Γ1 Γ2, IsHProp (P Γ1 Γ2).
  Variable P_None_None : P ⊥ ⊥.
  Variable P_None_Some : forall ls, P ⊥ (Some (from_list ls)).
  Variable P_Some_None : forall ls, P (Some (from_list ls)) ⊥.
  Variable P_Some_Some : forall ls1 ls2, P (Some (from_list ls1)) (Some (from_list ls2)).
  Definition Ctx_ind2 : forall Γ1 Γ2, P Γ1 Γ2.
  Proof.
    destruct Γ1 as [ Γ1 | ], Γ2 as [Γ2 | ].
    - generalize dependent Γ1; generalize dependent Γ2. 
      apply set_ind2; auto.
    - generalize dependent Γ1. apply set_ind; auto.
    - generalize dependent Γ2. apply set_ind; auto.
    - exact P_None_None.
  Defined.
End Ctx_ind2.

Section Ctx_rec.
  About set_rec.
  Variable A : Type.
  Variable X : Type.
  Variable decX : `{DecidablePaths X}.
  Variable B : Type.
  Variable B_HSet : IsHSet B.
  Variable dclass_None : B.
  Variable dclass_Some : list (X * A) -> B.
  Variable dclass_Some_correct : forall ls1 ls2, Permutation ls1 ls2 ->
           dclass_Some ls1 = dclass_Some ls2.

  Definition Ctx_rec : Ctx X A -> B.
  Proof.
    intros [Γ | ]; [ | exact dclass_None ].
    generalize dependent Γ.
    apply set_rec with (dclass := dclass_Some); auto.
  Defined.
End Ctx_rec.


Notation "X ⊥⊥ Y" := (@disjoint _ (@R _ _) _ _ _ _ _ X Y) (right associativity, at level 46).


Section CtxFunctor.

Variable A X Y : Type.
Variable (f : X -> Y).
Variable decX : `{DecidablePaths X}.
Variable decY : `{DecidablePaths Y}.
About PMonoid_set.

Let f' (z : X * A) : Y * A :=
  match z with
  | (x,a) => (f x, a)
  end.

Lemma fmap_from_list : forall (ls : list (X * A)),
      fmap f (Some (from_list ls)) = Some (from_list (fmap f' ls)).
Proof.
  induction ls; auto.
Defined.

Lemma from_list_cons : forall Y `{DecidablePaths Y} (y : Y) (a : A) (ls : list (Y * A)),
                  Some (from_list ((y,a) :: ls)) = disjoint_merge (singleton_set (y,a)) (from_list ls).
Admitted.

Lemma fmap_singleton_merge : forall (x : X) a (Γ : Ctx X A),
                       fmap f (singleton x a ∙ Γ) = singleton (f x) a ∙ fmap f Γ.
Proof.
  intros.
  simpl.
  destruct Γ; auto. simpl. unfold singleton_set. unfold disjoint_merge.
  set (b := from_list ((x,a) :: nil) ⊥⊥ p).
Admitted.

Lemma fmap_merge : forall (Γ1 Γ2 : Ctx X A),
                   fmap f (Γ1 ∙ Γ2) = fmap f Γ1 ∙ fmap f Γ2.
Proof.
  eapply Ctx_ind2; eauto.
  - admit (* not IsHProp? *).
  - intros.
    repeat rewrite fmap_from_list. 
    generalize dependent ls2.
    induction ls1 as [ | [x1 a1] ls1]; intros ls2; try (simpl; auto; fail).
    erewrite from_list_cons. 
    assert (eq : disjoint_merge (singleton_set (x1,a1)) (from_list ls1) 
               = singleton x1 a1 ∙ Some (from_list ls1)) by auto.
    rewrite eq.
    rewrite <- M_assoc.
    rewrite fmap_singleton_merge.
    rewrite IHls1. 
    rewrite M_assoc. f_ap.
    simpl. unfold f' at 2. simpl.
    erewrite from_list_cons.
    reflexivity.
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