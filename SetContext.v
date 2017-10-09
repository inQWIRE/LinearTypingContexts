Require Import HoTT.
Require Import Monad.
Require Import MerePermutation.
Require Import Permutation.
Require Import Monoid.
(*Require Import TypingContext.*)
Require Import List.

Print transport.
Definition transport_2 {A B} (P : A -> B -> Type) {x x' : A} {y y' : B} (p : x = x') (p' : y = y') (u : P x y) : P x' y'.
Proof.
  destruct p. destruct p'. exact u.
Defined.
Lemma transport_2_1_l : forall {A B} (P : A -> B -> Type) 
                                {x : A } {y y' : B} (p : y = y') (u : P x y), 
      transport_2 P 1%path p u = transport (P x) p u.
Proof.
  destruct p; auto.
Defined.
Lemma transport_2_1_r : forall {A B} (P : A -> B -> Type) 
                               {x x' : A} {y : B} (p : x = x') (u : P x y), 
      transport_2 P p 1%path u = transport (fun x => P x y) p u.
Proof.
  destruct p; auto.
Defined.


Section quotient_ind2.
  About quotient_ind.
  Variable A : Type.
  Variable R : relation A.
  Variable sR : is_mere_relation A R.
  Variable P : quotient R -> quotient R -> Type.
  Variable P_IsHProp : forall x y, IsHProp (P x y).
  Variable dclass : forall x y : A, P (class_of R x) (class_of R y). 

  Let P_HSet : forall q1 q2, IsHSet (P q1 q2). 
  Proof. intros. apply trunc_succ. Qed.

  Let dclass' : forall q y, P q (class_of R y).
  Proof.
    intros q y.
    generalize dependent q.
    apply quotient_ind with (dclass0 := fun x' => dclass x' y); auto.
    intros.
    apply P_IsHProp.
  Defined.


  Definition quotient_ind2 : forall x y, P x y.
  Proof.
    intros q.
    apply quotient_ind with (dclass0 := dclass' q); auto.
    intros x y H.
    apply P_IsHProp.
  Defined.

End quotient_ind2.
Arguments quotient_ind2 {A} {R} {sR}.

Instance hset_option : forall B, IsHSet B -> IsHSet (option B).
Admitted.

Ltac true_false_contradiction :=
  match goal with
  | [ H : true = false |- _ ] => exact (Empty_rec (true_ne_false H))
  | [ H : false = true |- _ ] => exact (Empty_rec (false_ne_true H))
  end.


(* Consider the propositional truncation of Permutation *)
Section MySet.

Set Implicit Arguments.
Open Scope list_scope.
Variable A : Type.
Variable decA : `{DecidablePaths A}.

Definition set := quotient bPermutation.
Definition from_list ls : set := class_of _ ls.


Lemma from_list_eq : forall ls1 ls2, Permutation ls1 ls2 ->
                     from_list ls1 = from_list ls2.
Proof.
  intros. 
  apply related_classes_eq; auto.
  apply Permutation_bPermutation.
  auto.
Qed.


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

Section set_rect.
  Variable P : set -> Type.
  Variable P_HSet : forall (X : set), IsHSet (P X).

  Variable dclass : forall (ls : list A), P (from_list ls).

  Variable dclass_eq : forall (ls1 ls2 : list A) 
                              (perm : bPermutation ls1 ls2),
    transport P (related_classes_eq bPermutation perm) (dclass ls1) 
    = dclass ls2.

  Definition set_rect : forall (X : set), P X.
  Proof. 
    apply (quotient_ind bPermutation _ dclass dclass_eq). 
  Defined.

End set_rect.

Section set_ind. 
  Variable P : set -> Type.
  Variable P_HProp : forall (X : set), IsHProp (P X).

  Variable dclass : forall (ls : list A), P (from_list ls).
  
  Let dclass_eq : forall (ls1 ls2 : list A) 
                         (perm : bPermutation ls1 ls2),
    transport P (related_classes_eq bPermutation perm) (dclass ls1) 
    = dclass ls2.
  Proof.
    intros; apply P_HProp.
  Qed.
  
  Definition set_ind : forall X, P X.
  Proof.
    apply (set_rect _ _ dclass dclass_eq).
  Defined.
End set_ind.


Section set_rec.
  Variable B : Type.
  Variable B_HSet : IsHSet B.
  Variable dclass : list A -> B.
  Variable dclass_eq : forall ls1 ls2 : list A, Permutation ls1 ls2 -> 
           dclass ls1 = dclass ls2.
  Definition set_rec : set -> B.
  Proof.
    apply (set_rect _ _ dclass).
    intros. 
    rewrite transport_const.
    apply dclass_eq; auto.
    eapply bPermutation_Permutation; auto.
  Defined.

End set_rec.


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
Arguments set A {decA}.


Section set_list_functor.
  Variable A : Type.
  Variable decA : `{DecidablePaths A}.
  Variable B : Type.
  Variable decB : `{DecidablePaths B}.


  About quotient_functor.
  Variable f : list A -> list B.
  Variable f_correct : forall ls1 ls2 : list A, Permutation ls1 ls2 ->
                                                Permutation (f ls1) (f ls2).
  Definition set_list_functor : set A -> set B.
  Proof.
    apply (quotient_functor _ _ f).
    intros x y perm.
    apply Permutation_bPermutation.
    apply f_correct.
    apply bPermutation_Permutation.
    auto.
  Defined.
End set_list_functor.

Section defns.
  Variable A : Type.
  Variable decA : `{DecidablePaths A}.

Definition add (x : A) : set A -> set A.
Proof.
  apply (set_list_functor _ (cons x)).
  intros. apply perm_skip; auto.
Defined.



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
  apply set_rec2 with (dclass := fun ls1 ls2 => from_list _ (append ls1 ls2)); 
    auto.
  intros. 
  apply from_list_eq.
  apply append_correct; auto.
Defined.

Arguments empty {A} {decA}.
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

Lemma perm_append_cons : forall ls1 ls2 a, 
    Permutation (append ls1 (a :: ls2)) (a :: (append ls1 ls2)).
Proof.
  induction ls1 as [ | b ls1]; intros; auto.
  simpl. 
  apply perm_trans with (l' := b :: a :: append ls1 ls2); auto.
    apply perm_swap.
Qed.


Lemma perm_append_comm : forall ls1 ls2,
      Permutation (append ls1 ls2) (append ls2 ls1).
Proof.
  induction ls1 as [ | a ls1]; intros ls2; simpl.
  - rewrite append_nil_r; auto. 
  - eapply perm_trans with (l' := a :: append ls2 ls1); auto. 
    apply Permutation_sym; auto.
    apply perm_append_cons.
Qed.

Lemma merge_comm : forall a b, a ∪ b = b ∪ a.
Proof.
  apply set_ind2; auto.
  intros; simpl.
  apply from_list_eq.
  apply perm_append_comm.
Qed.

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
About singleton_set.
Arguments singleton_set {A} {decA}.

Section set_functor.
  Variable B : Type.
  Variable decB : `{DecidablePaths B}.
  Variable (f : A -> B).

  Let f' : list A -> list B := fmap f.

  Let f'_correct : forall ls1 ls2, Permutation ls1 ls2 -> Permutation (f' ls1) (f' ls2).
  Proof.
    induction 1; unfold f'; simpl; auto.
    - apply perm_swap.
    - eapply perm_trans; eauto.
  Qed.

  Definition set_fmap : set A -> set B.
  Proof.
    apply set_list_functor with (f := f'); auto.
  Defined.    

End set_functor.

(* We want a relation here (as opposed to equality) because when we think
   about e.g. typing contexts, we only care about equality up to 
   the first argument e.g. we want x:Bool ∪ x:Nat to fail
*)

Section in_set.

Lemma in_set_correct : forall ls1 ls2, Permutation ls1 ls2 ->
    forall x, bin x ls1 = bin x ls2.
Proof.
  intros ls1 ls2 p; induction p; intros; auto.
  - simpl. destruct (b_dec x0 x); simpl; auto.
  - simpl. destruct (b_dec x0 y); destruct (b_dec x0 x); auto.
  - rewrite IHp1, IHp2. reflexivity.
Defined.

Definition in_set (x : A) : set A -> Bool.
Proof.
  apply (set_rec _ (bin x)).
  intros; apply in_set_correct; auto.
Defined.

End in_set.

Notation " x ∈? X " := (in_set x X) (at level 80).
Notation " x ∈ X " := (x ∈? X = true) (at level 80).

Definition disjoint_add (x : A) (X : set A) : option (set A) :=
  if x ∈? X then None else Some (add x X).

Section disjoint.

Fixpoint disjoint_list (ls1 ls2 : list A) : Bool :=
  match ls1 with
  | nil => true
  | a :: ls1' => negb (bin a ls2) && disjoint_list ls1' ls2
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

Arguments from_list {A} {decA}.

Definition list_is_empty (ls : list A) : Bool :=
  match ls with
  | nil => true
  | _   => false
  end.
  
Definition is_empty : set A -> Bool.
Proof.
  apply set_rec with (dclass := list_is_empty); auto.
  induction 1; auto.
  exact (IHX1 @ IHX2).
Defined.

Lemma disjoint_nilpotent : forall a, a ⊥⊥ a = is_empty a.
Proof. 
  apply set_ind; auto.
  induction ls; simpl; auto. 
  rewrite b_dec_true; auto.
Qed.

Lemma b_dec_sym : forall a b, (a =? b) = (b =? a).
Proof.
  intros.
  destruct (decA a b).
  - rewrite b_dec_true; auto.
    rewrite b_dec_true; auto; exact p^.
  - rewrite b_dec_false; auto.
    destruct (decA b a); auto.
    * set (p' := p^). contradiction.
    * rewrite b_dec_false; auto.
Qed.


Lemma disjoint_list_cons_r : forall ls1 ls2 b,
      disjoint_list ls1 (b :: ls2) = negb (bin b ls1) && disjoint_list ls1 ls2.
Proof.
  induction ls1; intros; auto.
  simpl. rewrite IHls1; auto.
  rewrite b_dec_sym.
  destruct (b =? a), (bin a ls2), (bin b ls1); simpl; auto.
Qed.

    
Lemma disjoint_comm : forall a b, a ⊥⊥ b = b ⊥⊥ a.
Proof.
  apply set_ind2; auto.
  induction ls1 as [ | a1 ls1]; destruct ls2 as [ | a2 ls2]; simpl in *; auto.
  - exact (disjoint_list_nil_r _)^.
  - exact (disjoint_list_nil_r _).
  - rewrite IHls1. rewrite disjoint_list_cons_r. simpl.
    rewrite b_dec_sym.
    destruct (a2 =? a1), (bin a1 ls2), (bin a2 ls1); simpl; auto.
Qed.


Lemma disjoint_merge_r : forall a b c, a ⊥⊥ (merge b c) = (a ⊥⊥ b) && (a ⊥⊥ c).
Admitted.

Lemma disjoint_merge_l : forall a b c, (merge a b) ⊥⊥ c = (a ⊥⊥ c) && (b ⊥⊥ c).
Admitted.

Lemma singleton_disjoint : forall a b, 
      singleton_set a ⊥⊥ singleton_set b = negb (a =? b).
Proof. intros. simpl. destruct (a =? b); auto. Qed.


Lemma merge_append : forall ls1 ls2, 
      (from_list ls1) ∪ (from_list ls2) = from_list (ls1 ++ ls2).
Proof.
  induction ls1 as [ | x1 ls1]; intros; auto.
Qed.


(* PROPERTIES *)

Lemma disjoint_empty : forall X, X ⊥⊥ ∅ = true.
Proof.
  apply set_ind; auto.
  induction ls; auto.
Defined.

Definition add_in_property a b X := (a ∈? X) = (b ∈? X).

Lemma add_in : forall a X, (a ∈? add a X) = true.
  Proof.
  intros a.
  apply set_ind; auto.
  intros; simpl.
  rewrite b_dec_true; auto.
Defined.

Lemma add_not_in : forall a b, a <> b -> forall X, (a ∈? add b X) = (a ∈? X).
Proof.
  intros a b neq.
  apply set_ind; intros; auto.
  simpl.
  rewrite b_dec_false; auto.
Defined.

Lemma add_symmetric : forall a b,
      a <> b -> forall X, add a (add b X) = add b (add a X).
Proof.
  intros a b pf_R.
  apply set_ind; intros; auto.
  simpl. 
  apply related_classes_eq.
  apply Permutation_bPermutation.
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
Variable X : Type.
Context `{decX : DecidablePaths X}.
Context `{Funext}.
Definition R (z1 z2 : X * A) : Type :=
  (fst z1) = (fst z2).
Definition dom := quotient R.

Instance decR : DecidablePaths dom.
Proof.
  unfold DecidablePaths. unfold dom.
  intros q.
  set (P := fun y => Decidable (q = y)). About quotient_ind.
  transparent assert (dclass : (forall z, P (class_of _ z))).
  { intros [x a].
    unfold P. clear P. 
    generalize dependent q.
    set (Q := fun q => Decidable (q = class_of R (x, a))).
    transparent assert (dclass' : (forall z, Q (class_of _ z))).
    { unfold Q; clear Q.
      intros [y b].
      destruct (decX x y).
      * left.
        apply related_classes_eq.
        unfold R.
        simpl.
        exact p^.
      * right.
        intros contr. 
        admit (* :( *).
    }
    apply quotient_ind with (dclass := dclass'); unfold Q; auto.
    - intros. apply hset_sum.
    - intros [y b] [z c] HR.
      unfold R in HR. simpl in HR.
      unfold dclass'. simpl.
      destruct (decX x y); auto.
      * set (p' := p @ HR).
        destruct (decX x z); [ | contradiction].
        admit.
      * admit.
  }
  apply quotient_ind with (dclass0 := dclass); auto.
  - unfold P. intros. apply hset_sum.
  - intros [x a] [y b] HR.
    admit.
Admitted.
  

Definition PreCtx := set dom.

(*
Definition shift {X} : PreCtx X -> PreCtx (option X) :=
  set_fmap (fun (z : X * A) => let (x,a) := z in (Some x, a)).
*)

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
  intros Γ1 Γ2.
  set (b := @disjoint _ R _ _ _ _ _ Γ1 Γ2).
  exact (if b then Some (Γ1 ∪ Γ2) else None).
Defined.



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

About disjoint_merge.
    

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
  Variable dclass_Some_correct : forall ls1 ls2, Perm _ ls1 ls2 ->
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

Lemma from_list_cons : forall {Z} `{DecidablePaths Z} (z : Z) (a : A) ls,
      from_list ((z,a) :: ls) = singleton_set (z,a) ∪ from_list ls.
Proof. auto. Qed.

(*
Lemma from_list_cons : forall {Z} `{DecidablePaths Z} (z : Z) (a : A) ls,
      bin (@R A Z) (z,a) ls = false ->
      Some (from_list ((z,a) :: ls)) = singleton z a ∙ Some (from_list ls).
Proof.
  intros. simpl. unfold disjoint_merge. simpl.
  rewrite andb_true_r.
  rewrite X0. auto.
Defined.

Lemma from_list_cons_undefined : forall {Z} `{DecidablePaths Z} (z : Z) (a : A) ls,
      bin (@R A Z) (z,a) ls = true ->
      from_list ((z,a) :: ls) = singleton_set z a ∪ from_list ls.
*)

Open Scope bool_scope.

Lemma fmap_cons : forall x a ls, fmap f' ((x,a) :: ls) = (f x, a) :: fmap f' ls.
Proof. intros; simpl; unfold f'; auto. Qed.

Lemma disjoint_merge_cons : forall {Z} `{DecidablePaths Z} (z : Z) (a : A) ls1 ls2,
      disjoint_merge (from_list ((z,a) :: ls1)) (from_list ls2)
    = singleton z a ∙ disjoint_merge (from_list ls1) (from_list ls2).
Proof.
  intros. simpl. unfold disjoint_merge.
  assert (eq : from_list ((z,a) :: ls1) ⊥⊥ from_list ls2 
        = negb (bin (@R A Z) (z,a) ls2) && (from_list ls1 ⊥⊥ from_list ls2))
    by auto.
  rewrite eq.
  remember (from_list ls1 ⊥⊥ from_list ls2) as b eqn:Hb.
  rewrite Hb.
  destruct b.
  * rewrite andb_true_r.
  *





Instance PCM_set_laws Z `{DecidablePaths Z} : PCM_Laws (option (PreCtx A Z)).
Proof.
  apply PPCM_to_PCM_Laws.
  apply PPCM_set_laws.
Defined.
Hint Resolve PCM_set_laws.

Lemma fmap_merge : forall (Γ1 Γ2 : Ctx X A),
                   fmap f (Γ1 ∙ Γ2) = fmap f Γ1 ∙ fmap f Γ2.
Proof.
  eapply Ctx_ind2; eauto.
  - admit (* not IsHProp? *).
  - intros.
    repeat rewrite fmap_from_list. 
    generalize dependent ls2.
    induction ls1 as [ | [x1 a1] ls1]; intros ls2; try (simpl; auto; fail).
    remember (bin (@R A X) (x1,a1) ls1) as b1 eqn:Hb1.
    remember (bin (@R A X) (x1,a1) ls2) as b2 eqn:Hb2.
    simpl.

    destruct b1, b2. 
    (* in the first three cases, if x1 occurs in either ls1 or ls2, then    
       both sides should be undefined *)
    * 
    *
    *
    *

    rewrite from_list_cons.
    rewrite M_comm_assoc; [ | apply (@PPCM_to_PCM_Laws _ _ (@PPCM_set_laws A X _))].
    rewrite <- M_assoc.
    rewrite <- from_list_cons.
    rewrite IHls1.
    repeat rewrite fmap_cons.
    repeat rewrite from_list_cons.
    monoid.
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