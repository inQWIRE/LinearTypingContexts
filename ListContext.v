Require Import HoTT.
Require Import Monad.
Require Import NCM.

Section ListContext.
Set Implicit Arguments.

Variable A : Type.

Definition FinMap := list (nat * A).
Definition ListContext := option FinMap.

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


Lemma singleton_base : forall x a, base (singleton x a).
Proof. intros. exists x. exists a. reflexivity. Defined.
Hint Resolve singleton_base.
Hint Unfold List.Forall.

(* TODO: laws *)
Instance NCM_ListContext_Laws : NCM_Laws ListContext.
Admitted.


Example test : forall (x : nat) (a : A), singleton x a · singleton x a = 0.
Proof.
  intros. reification.
Defined.

