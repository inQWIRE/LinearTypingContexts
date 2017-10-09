Require Import HoTT.
Require Import Monad.
Require Import List.
Require Import Permutation.



Definition b_dec {X} `{decX : DecidablePaths X} (x y : X) : Bool :=
    if decX x y then true else false.
Notation "x =? y" := (b_dec x y) (at level 30).

Lemma b_dec_true : forall {X} `{DecidablePaths X} x y, x = y -> x =? y = true.
Proof.
  intros.
  unfold b_dec. destruct (H x y); auto. contradiction.
Qed.

Lemma b_dec_false : forall {X} `{DecidablePaths X} x y, x <> y -> x =? y = false.
Proof.
  intros.
  unfold b_dec. destruct (H x y); auto. contradiction.
Qed.

Section MerePermutation.

  Variable A : Type.
  Variable decA : `{DecidablePaths A}.

  Open Scope bool_scope.

  Fixpoint bin (a : A) (ls : list A) : Bool :=
    match ls with
    | nil => false
    | b :: ls' => a =? b || bin a ls'
    end.

  Notation "a ∈? ls" := (bin a ls) (at level 30).

  Fixpoint remove (a : A) (ls : list A) : option (list A) :=
    match ls with
    | nil => None
    | b :: ls' => if a =? b then Some ls' else fmap (cons b) (remove a ls')
    end.

  Fixpoint bpermutation ls1 ls2 : Bool :=
    match ls1 with
    | nil => match ls2 with 
             | nil => true
             | _   => false
             end
    | a :: ls1' => match remove a ls2 with
                   | Some ls2' => bpermutation ls1' ls2'
                   | None      => false
                   end
    end.
  Definition bPermutation ls1 ls2 := bpermutation ls1 ls2 = true.
  Hint Unfold bPermutation.

  Lemma IsHSet_implies_IsHProp : forall X, IsHSet X -> 
                                 forall (x y : X), IsHProp (x = y).
  Proof.
    auto.
  Defined.

  Lemma bpermutation_is_mere_permutation : is_mere_relation (list A) bPermutation.
  Proof.
    intros x y. 
    apply IsHSet_implies_IsHProp.
    apply hset_bool.
  Qed.

  Ltac true_false_contradiction :=
  match goal with
  | [ H : true = false |- _ ] => exact (Empty_rec (true_ne_false H))
  | [ H : false = true |- _ ] => exact (Empty_rec (false_ne_true H))
  end.


  Lemma bPerm_refl : forall ls, bPermutation ls ls.
  Admitted.

  Lemma bPerm_symm : forall ls1 ls2, bPermutation ls1 ls2 ->
                                                bPermutation ls2 ls1.
  Admitted.

  Lemma bPerm_skip : forall x ls1 ls2, bPermutation ls1 ls2 -> 
                                       bPermutation (x :: ls1) (x :: ls2).
  Admitted.

  Lemma bPerm_swap : forall x y ls, bPermutation (x :: y :: ls) (y :: x :: ls).
  Admitted.

  Lemma bPerm_remove_contra : forall a ls1  ls1' ls2,
        bPermutation ls1 ls2 ->
        remove a ls1 = Some ls1' ->
        remove a ls2 <> None.
  Admitted.

  Lemma bPerm_remove : forall a ls1 ls1' ls2 ls2',
        bPermutation ls1 ls2 ->
        remove a ls1 = Some ls1' ->
        remove a ls2 = Some ls2' ->
        bPermutation ls1' ls2'.
  Admitted.

  Lemma bPerm_trans : forall ls1 ls2 ls3, 
        bPermutation ls1 ls2 ->
        bPermutation ls2 ls3 ->
        bPermutation ls1 ls3.
  Proof.
    induction ls1 as [ | a ls1]; unfold bPermutation; simpl; intros.
    - destruct ls2; [ | true_false_contradiction].
      destruct ls3; simpl in *; [ | true_false_contradiction].
      auto.
    - remember (remove a ls2) as x eqn:Hx.
      destruct x as [ls2' | ]; [ | true_false_contradiction].
      remember (remove a ls3) as y eqn:Hy.
      destruct y as [ls3' | ];
        [ | apply (bPerm_remove_contra a ls2 ls2' ls3) in Hy; auto; 
            contradiction].
      apply (IHls1 ls2'); auto.
      apply (bPerm_remove a ls2 _ ls3); auto.
  Qed.

  Lemma Permutation_bPermutation : forall ls1 ls2, Permutation ls1 ls2 ->
                                                   bPermutation ls1 ls2.
  Proof. 
    induction 1; unfold bPermutation; auto.
    - simpl.
      rewrite b_dec_true; auto.
    - simpl. destruct (decA y x).
      * rewrite b_dec_true; auto.
        simpl. rewrite b_dec_true; [ apply bPerm_refl | exact p^].
      * rewrite b_dec_false; auto.
        rewrite b_dec_true; auto. 
        simpl.
        rewrite b_dec_true; auto.
        apply bPerm_refl.
    - apply (bPerm_trans l l' l''); auto.
  Qed.

  Lemma Some_None_contra : forall {Z} (z : Z), Some z <> None.
  Admitted.
  Lemma None_Some_contra : forall {Z} (z : Z), None <> Some z.
  Admitted.
  Lemma Some_Some_inv : forall {Z} (z1 z2 : Z), Some z1 = Some z2 -> z1 = z2.
  Admitted.

  Ltac option_contradiction :=
    match goal with
    | [H : Some _ = None |- _ ] => apply (Empty_rec (Some_None_contra _ H))
    | [H : None = Some _ |- _ ] => apply (Empty_rec (None_Some_contra _ H))
    end.

 
  Lemma Permutation_remove : forall a ls1 ls2 ls2',
        Permutation ls1 ls2' ->
        remove a ls2 = Some ls2' ->
        Permutation (a :: ls1) ls2.
  Proof.
    induction 1; simpl; intros.
    - destruct ls2 as [ | b ls2']; simpl in *; [option_contradiction | ].
      destruct (decA a b).
      * rewrite b_dec_true in X; auto.
        apply Some_Some_inv in X.
        rewrite p, X.
        auto.
      * rewrite b_dec_false in X; auto.
        admit. (* TODO *)
Admitted.

  Lemma bPermutation_Permutation : forall ls1 ls2, bPermutation ls1 ls2 ->
                                                   Permutation ls1 ls2.
  Proof.
    induction ls1; unfold bPermutation; simpl; intros.
    - destruct ls2; auto; true_false_contradiction.
    - remember (remove a ls2) as x eqn:Hx.
      destruct x as [ls2' | ]; [ | true_false_contradiction].
      apply (Permutation_remove a ls1 ls2 ls2'); auto.
  Qed.


End MerePermutation.
About bPermutation.
Arguments bPermutation {A} {decA}.
Hint Resolve bPerm_refl.
Arguments remove {A} {decA}.
Arguments Permutation_bPermutation {A} {decA}.
Arguments bPermutation_Permutation {A} {decA}.
About bin.
Arguments bin {A} {decA}.