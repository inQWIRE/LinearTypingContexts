Require Import Monad.
Require Import NCM.

Section IndexContext.
Set Implicit Arguments.

Variable A : Type.


(* An index map is a map from nats to A's encoded as a list of option A's;
   index i maps to a if ls[i]=Some a *)
Definition IdxMap := list (option A).

Definition mergeOption (o1 o2 : option A) : option (option A) :=
  match o1, o2 with
  | _, None => Some o1
  | None, _ => Some o2
  | Some _, Some _ => None
  end.
Fixpoint mergeIdxMap (i1 i2 : IdxMap) : option IdxMap :=
  match i1, i2 with
  | nil, _ => Some i2
  | _, nil => Some i1
  | o1 :: i1, o2 :: i2 => do o ← mergeOption o1 o2;
                          do i ← mergeIdxMap i1 i2;
                          Some (o :: i)
  end.

Lemma mergeIdxMap_nil_r : forall i, mergeIdxMap i nil = Some i.
Proof.
  destruct i; auto.
Defined.
Hint Resolve mergeIdxMap_nil_r.

Lemma mergeIdxMap_step : forall o1 o2 i1 i2,
    mergeIdxMap (o1 :: i1) (o2 :: i2) = do o ← mergeOption o1 o2;
                                        do i ← mergeIdxMap i1 i2;
                                        Some (o :: i).
Proof.
  intros; auto.
Defined.

Fixpoint isEmpty (i : IdxMap) :=
  match i with
  | nil => True
  | None :: i => isEmpty i
  | Some _ :: _ => False
  end.


(* This will hold for all monads if you depend on functional extensionality *)
Lemma bind_option_eq : forall X Y (e : option X) (f f' : X -> option Y), 
      (forall x, f x = f' x) -> bind e f = bind e f'.
Proof.
  intros. destruct e; auto.
  simpl. auto.
Defined.
Arguments bind_option_eq {X Y} e.

(* This should really hold for all monads *)
Lemma bind_permut : forall {X Y Z} (ma : option X) (mb : option Y) (g : X -> Y -> option Z),
  bind ma (fun x => bind mb (g x)) = bind mb (fun y => bind ma (fun x => g x y)).
Proof.
  intros. destruct ma; destruct mb; auto.
Defined.


Lemma mergeOption_assoc : forall x y z,
                          do a ← mergeOption x y; mergeOption a z
                        = do b ← mergeOption y z; mergeOption x b.
Proof.
  destruct x; destruct y; destruct z; auto.
Defined.

Lemma mergeOption_comm : forall x y, mergeOption x y = mergeOption y x.
Proof.
  destruct x; destruct y; auto.
Defined.

                                       

Global Instance PMonoid_IdxMap : PMonoid IdxMap := 
    { one' := nil; m' := mergeIdxMap; base' := fun i => ~(isEmpty i) }.
Global Instance PMonoid_IdxMap_Laws : PMonoid_Laws IdxMap.
Proof.
  split.
  - auto.
  - assert (H : forall X (x : X), Some x = return_ x) by reflexivity.
    induction a as [ | x a]; intros;
    [  simpl; destruct (mergeIdxMap b c); auto | ].
    destruct b as [ | y b]; destruct c as [ | z c]; auto.
    * repeat rewrite mergeIdxMap_nil_r.
      rewrite H, <- bind_left_unit.
      rewrite (bind_right_unit _ (m' (x :: a) (y :: b))) at 1.
      apply bind_option_eq; auto. 
    * repeat rewrite mergeIdxMap_step.
      repeat rewrite <- bind_associativity.
      rewrite (bind_option_eq (mergeOption y z) _
                (fun x0 => do i ← mergeIdxMap b c; m' (x :: a) (x0 :: i))); 
        [ | intros; rewrite <- bind_associativity; apply bind_option_eq; auto ].
      rewrite (bind_option_eq (mergeOption x y)  _
                (fun x0 => do i ← mergeIdxMap a b; m' (x0 :: i) (z :: c))); 
        [ | intros; rewrite <- bind_associativity; apply bind_option_eq; auto ].
      erewrite (bind_option_eq (mergeOption y z));
        [ | intros; apply bind_option_eq; intros; apply mergeIdxMap_step ].
      erewrite (bind_option_eq (mergeOption x y));
        [ | intros; apply bind_option_eq; intros; apply mergeIdxMap_step ].
      erewrite (bind_option_eq (mergeOption y z));
        [ | intros; apply bind_permut].
      erewrite (bind_option_eq (mergeOption x y));
        [ | intros; apply bind_permut].
      repeat rewrite bind_associativity.
      rewrite mergeOption_assoc.
      apply bind_option_eq; intros.
      repeat rewrite bind_associativity.
      rewrite IHa. reflexivity.
  - induction a as [ | x a]; destruct b as [ | y b]; auto.
    repeat rewrite mergeIdxMap_step.
    rewrite mergeOption_comm.
    apply bind_option_eq; intros o.
    rewrite IHa. reflexivity.
  - induction a as [ | o a]; intros H.
    * simpl in H. contradiction. 
    * simpl in *. destruct o; simpl; auto.
      rewrite IHa; auto.
Defined.

(* Now option IdxCtx should be an NCM *)


Fixpoint singleton' (x : nat) (a : A) :=
  match x with
  | O => Some a :: nil
  | S x' => None :: singleton' x' a 
  end.
Definition singleton x a := Some (singleton' x a).


Lemma singleton_not_empty : forall x a, base (singleton x a).
Proof.
  induction x; simpl; auto. 
Defined.
Hint Resolve singleton_not_empty.


Example test : forall x y a b, singleton x a ∙ singleton y b = singleton y b ∙ singleton x a ∙ 1.
Proof.
  intros. reification.
Defined.

End IndexContext.
    
