Require Import Monad.
Require Import NCM.
Require Import List.
Require Import Orders.
Require Import Mergesort.
Require Import Arith.
Import ListNotations.

Variable A : Type.
Variable a1 a2 a3: A.

Module FinMapOrder <: TotalLeBool.
  Definition t := nat * A.
  Fixpoint leb (x y : t) := let (m,_) := x in 
                      let (n,_) := y in
                      (m <=? n)%nat.
  Infix "<=?" := leb (at level 70).
  Theorem leb_total : forall a1 a2, (a1 <=? a2 =true) \/ (a2 <=? a1 = true).
  Proof.
    intros [a1] [a2].
    simpl.
    rewrite 2 Nat.leb_le.
    apply Nat.le_ge_cases.
  Qed.
End FinMapOrder.

Module Import FinMapSort := Sort FinMapOrder.

Section ListContext.
Set Implicit Arguments.

Definition FinMap := list (nat * A).
Definition ListContext := option FinMap.

Eval compute in (sort [(1,a1); (3,a3); (0,a2); (2,a1)]%nat).

(* TODO: Disjoint merge that also sorts the inputs *)
Definition mergeListContext' (ls1 ls2 : FinMap) : ListContext.
Admitted.

Definition mergeListContext (ls1 ls2 : ListContext) : ListContext :=
  match ls1, ls2 with
  | Some ls1', Some ls2' => mergeListContext' ls1' ls2'
  | _, _ => None
  end.


Definition singleton (x : nat) (a : A) : ListContext :=
  Some ((x,a) :: nil).

Instance NCM_ListContext : NCM ListContext := 
    { one := Some nil
    ; zero := None
    ; m := mergeListContext 
    ; base := fun b => exists x a, b = singleton x a}.
Opaque base.

Lemma singleton_base : forall x a, base (singleton x a).
Proof. intros. exists x. exists a. reflexivity. Defined.
Hint Resolve singleton_base.

(* TODO: laws *)
Instance NCM_ListContext_Laws : NCM_Laws ListContext.
Admitted.


Example test : forall (x : nat) (a : A), singleton x a ∙ singleton x a = 0.
Proof.
  intros. reification.
Defined.

End ListContext.
