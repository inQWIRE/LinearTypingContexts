Require Import Monad.
Require Import NCM.

Definition FinMap A := list (nat * A).
Definition ListContext A := option (FinMap A).

(* Disjoint merge that also sorts the inputs *)
Definition mergeListContext' {A} (ls1 ls2 : FinMap A) : ListContext A.
Admitted.

Definition mergeListContext {A} (ls1 ls2 : ListContext A) : ListContext A :=
  match ls1, ls2 with
  | Some ls1', Some ls2' => mergeListContext' ls1' ls2'
  | _, _ => None
  end.

Instance NCM_ListContext A : NCM (ListContext A) := 
    { one := Some nil
    ; zero := None
    ; m := mergeListContext }.
(* TODO: laws *)

Definition singleton {A} (x : nat) (a : A) : ListContext A :=
  Some ((x,a) :: nil).

Example text : forall {A} (x : nat) (a : A), singleton x a · singleton x a = 0.
Proof.
  intros. reification.