Require Import HoTT.

Set Implicit Arguments.

Section List.

Variable A : Type.

(**********)
(* Length *)
(**********)
Open Scope list_scope.
Fixpoint length (l : list A) : nat :=
  match l with
  | nil => 0
  | _ :: l' => S (length l')
  end.

(***********)
(* In List *)
(***********)

Open Scope list_scope.
Fixpoint In (a : A) (l : list A) :=
  match l with
  | nil => Empty
  | b :: l' => a = b \/ In a l'
  end.

Variable decA : DecidablePaths A.

Definition in_dec : forall a l, Decidable (In a l).
Proof.
  induction l as [ | b l]; simpl.
  - right; auto.
  - apply decidable_sum.
Defined.

(**********)
(* Forall *)
(**********)

Variable P : A -> Type.
Fixpoint Forall (l : list A) :=
  match l with
  | nil => Unit
  | a :: l' => P a /\ Forall l'
  end.


Lemma forall_in : forall (ls : list A),
      Forall ls -> forall i, In i ls -> P i.
Proof.
  induction ls as [ | a ls]; intros pf_forall i pf_in;
    simpl in *.
  - contradiction.
  - destruct pf_forall as [pf_P pf_forall]. 
    destruct pf_in as [pf_eq | pf_in].
    * rewrite pf_eq; auto.
    * apply IHls; auto.
Defined.

End List.

Hint Unfold Forall.
Arguments in_dec {A} {decA}.