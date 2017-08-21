Require Import HoTT.
Require Import Multiset.
Require Import Permutation.
Require Import List.

Set Implicit Arguments.
Open Scope list_scope.

Section Permut.

Variable A : Type.
Variable decA : DecidablePaths A.


Fixpoint list_contents (l:list A) : multiset A :=
  match l with
  | nil => EmptyBag
  | a :: l => munion (SingletonBag a) (list_contents l)
  end.

Lemma list_contents_app :
  forall l m:list A,
    meq (list_contents (l ++ m)) (munion (list_contents l) (list_contents m)).
Proof.
  induction l; intros m; simpl.
  - apply munion_empty_left.
  - apply (@meq_trans _ _ (munion (SingletonBag a) (munion (list_contents l) (list_contents m)))).
    * apply meq_right. apply IHl.
    * apply meq_sym. apply munion_ass.
Defined.

Lemma list_contents_cons : forall a l, 
      meq (list_contents (a :: l)) (munion (SingletonBag a) (list_contents l)).
Proof.
  auto.
Defined.

Definition permutation (l m:list A) := meq (list_contents l) (list_contents m).
Hint Unfold permutation.

Lemma permut_refl : forall l:list A, permutation l l.
Proof. intros l. auto. Defined.

Lemma permut_sym :
  forall l1 l2 : list A, permutation l1 l2 -> permutation l2 l1.
Proof.
  intros. apply meq_sym; auto.
Defined.

Lemma permut_trans :
  forall l m n:list A, permutation l m -> permutation m n -> permutation l n.
Proof.
  intros l m n H1 H2. apply (meq_trans H1 H2).
Defined.


Lemma permut_cons :
  forall l m:list A,
    permutation l m -> forall a:A, permutation (a :: l) (a :: m).
Proof. 
  intros l m H a b; simpl. rewrite (H b); auto.
Defined.
  

Lemma permut_app :
  forall l l' m m':list A,
    permutation l l' -> permutation m m' -> permutation (l ++ m) (l' ++ m').
Proof.
  intros l l' m m' H1 H2. unfold permutation.
  refine (meq_trans (list_contents_app _ _) _). 
  refine (meq_trans (meq_munion H1 H2) _).
  refine (meq_sym (list_contents_app _ _)).
Defined.

Lemma permut_swap : forall a b l,
      permutation (a :: b :: l) (b :: a :: l).
Proof.
  intros a b l.
  unfold permutation.
  assert (H : forall (x y : A) l', x :: y :: l' = (x :: y :: nil) ++ l') 
    by reflexivity.
  rewrite (H a b l), (H b a l); clear H.
  apply meq_trans 
    with (y := munion (list_contents (a :: b :: nil)) (list_contents l));
    [apply list_contents_app | ].
  apply meq_trans
    with (y := munion (list_contents (b :: a :: nil)) (list_contents l));
    [ | apply meq_sym; apply list_contents_app].
  apply meq_left.
  intros z.
  simpl. repeat rewrite <- nat_plus_n_O. apply nat_plus_comm.
Defined.

Lemma Permutation_permutation : forall l l',
  Permutation l l' -> permutation l l'.
Proof.
  intros l l' H.
  induction H; auto.
  - apply (permut_cons IHPermutation).
  - apply permut_swap.
  - apply meq_trans with (y := list_contents l'); auto.
Defined.

Lemma perm_inv_contradiction : forall a l, ~ permutation nil (a :: l).
Proof.
  intros a l. unfold permutation. apply meq_inv_contradiction.
  exists a; simpl. destruct (dec_paths a a).
  * simpl. exact tt.
  * contradiction.
Defined.


Lemma perm_cons_inv : forall a l l', 
      permutation (a :: l) l' -> 
      exists l1 l2, l' = l1 ++ a :: l2 /\ permutation l (l1 ++ l2).
Proof.
Admitted.

Lemma perm_nil_inv : forall l, permutation nil l -> l = nil.
Admitted.


Lemma permutation_Permutation : forall l l',
      permutation l l' -> Permutation l l'.
Proof.
  induction l as [ | a l]; intros l' H.
  - rewrite (perm_nil_inv H). auto.
  - destruct (perm_cons_inv H) as [l1 [l2 [H1 H2]]].
    rewrite H1.
    apply Permutation_in; auto.
Defined.


Lemma multiplicity_In_O : forall l x, 
      ~ In x l -> multiplicity (list_contents l) x = 0.
Proof.
  induction l; intros x H; simpl; auto.
  simpl in H.
  assert (Hx : x <> a) by auto.
  assert (Hx' : a <> x) by (exact (fun G => Hx G^)). 
  assert (Hl : ~ In x l) by auto.
  destruct (dec_paths a x); [contradiction | ].
  apply IHl; auto.
Defined.

Lemma meq_multiplicity : forall (ls1 ls2 : list A),
      (forall x, In x ls1 \/ In x ls2 ->
                 multiplicity (list_contents ls1) x 
               = multiplicity (list_contents ls2) x) ->
      meq (list_contents ls1) (list_contents ls2).
Proof.
  intros ls1 ls2 H x.
  destruct (in_dec x ls1); [apply H; auto | ].
  destruct (in_dec x ls2); [apply H; auto | ].
  repeat rewrite multiplicity_In_O; auto. 
Defined.


End Permut.

Arguments list_contents {A} {decA}.