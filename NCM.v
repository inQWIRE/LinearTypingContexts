Require Import HoTT.
Require Import Monad.
Require Import List.
Require Import Multiset.
Require Import Permutation.
Require Import PermutationReflection.
Hint Resolve tt.

(*
Require Import PermutSetoid.
Require Import Sorting.Permutation.
Require Import Sorting.PermutEq. (* Standard library *)  
*)


(* Nilpotent Commutative Monoid *)
Class NCM A :=
    { zero : A
    ; one  : A
    ; m    : A -> A -> A 
    ; base : A -> Type }.
Notation "0" := zero.
Notation "1" := one.
Notation "a · b" := (m a b) (right associativity, at level 20).


Class NCM_Laws A `{NCM A} :=
  { NCM_unit  : forall a, a · 1 = a
  ; NCM_assoc : forall a b c, a · (b · c) = (a · b) · c
  ; NCM_absorb: forall a, a · 0 = 0
  ; NCM_comm  : forall a b, a · b = b · a
  ; NCM_nilpotent : forall a, base a -> a · a = 0 }.
Hint Resolve NCM_unit NCM_absorb.

Set Implicit Arguments.


(****************************)
(* Interpretable type class *)
(****************************)

Class Interpretable (A B : Type) := { interp : B -> A }.
Notation "[ b ]" := (interp b).

About one.


Section NCM.
  Variable A : Type.
  Variable NCM_A : `{NCM A}.
  Variable NCM_A_Laws : `{NCM_Laws A}.



Lemma NCM_unit_l : forall a, 1 · a = a.
Proof. intros. rewrite NCM_comm. auto. Defined.
Hint Resolve NCM_unit_l.
Lemma NCM_absorb_l : forall a, 0 · a = 0. 
Proof. intros. rewrite NCM_comm. auto. Defined.
Hint Resolve NCM_absorb_l.

Lemma NCM_comm_assoc : forall a b c, a · b · c = b · a · c.
Proof.
  intros. rewrite NCM_assoc. rewrite (NCM_comm a b). rewrite <- NCM_assoc.
  reflexivity.
Defined.


(****************************)
(* Interpretable type class *)
(****************************)

Open Scope list_scope.

Global Instance Interp_A : Interpretable A A := {interp := fun x => x}.

Definition interp_option {B} `{Interpretable A B} (b : option B) : A :=
  match b with
  | Some b' => [b']
  | None => 0
  end.
Global Instance Interp_option (B : Type) `{Interpretable A B} : Interpretable A (option B) :=
  { interp := interp_option }.

Fixpoint interp_list {B} `{Interpretable A B} (ls : list B) :=
  match ls with
  | nil => 1
  | b :: ls' => [b] · interp_list ls'
  end.
Global Instance Interp_list (B : Type) `{Interpretable A B} : Interpretable A (list B) :=
  { interp := interp_list }.





(***************************************)
(* Structural representation of an NCM *)
(***************************************)

Inductive NCM_exp :=
| NCM_zero : NCM_exp
| NCM_one  : NCM_exp
| NCM_var  : A -> NCM_exp
| NCM_m    : NCM_exp -> NCM_exp -> NCM_exp.


Fixpoint interp_NCM (e : NCM_exp) : A :=
  match e with
  | NCM_zero => 0
  | NCM_one => 1
  | NCM_var a => a
  | NCM_m e1 e2 => interp_NCM e1 · interp_NCM e2
  end.
Global Instance Interp_NCM : Interpretable A NCM_exp := {interp := interp_NCM}.



(****************)
(* lists of A's *)
(****************)

Fixpoint flatten (e : NCM_exp) : option (list A) :=
  match e with
  | NCM_zero => None
  | NCM_one  => Some nil
  | NCM_var a => Some (a :: nil)
  | NCM_m e1 e2 => do ls1 ← flatten e1;
                   do ls2 ← flatten e2;
                   return_ (ls1 ++ ls2)
  end.


Lemma flatten_correct' : forall (ls1 ls2 : list A),
      [ls1] · [ls2] = [ls1 ++ ls2].
Proof.
  induction ls1; intros; auto.
  simpl.
  rewrite <- NCM_assoc. unfold interp in *; simpl in *.
  rewrite IHls1. reflexivity.
Defined.


Lemma flatten_correct : forall e, [e] = [flatten e].
Proof.
  intros. unfold interp; simpl.
  induction e; simpl; try rewrite NCM_unit; auto. 
  rewrite IHe1, IHe2.
  destruct (flatten e1) as [ ls1 | ]; auto.
  destruct (flatten e2) as [ ls2 | ]; simpl; auto.
  apply flatten_correct'.
Defined.




(*****************)
(* lists of nats *)
(*****************)


(* Instead of working with list A directly, we instead want to work with
   a pair of a list A and a list nat-- the elements in the second list
   index into the first list, and let us compare elements.
 *)


Fixpoint index (xs : list A) (n : nat) : option A :=
  match xs, n with
  | nil, _ => None 
  | (x :: _), 0 => Some x
  | (_ :: xs), S x => index xs x
  end.

Fixpoint index_wrt (values : list A) (indices : list nat) : list A :=
  match indices with
  | nil => nil
  | i :: indices' => [index values i] :: index_wrt values indices'
  end.

Instance Interp_nat_list : Interpretable A (list A * list nat) :=
  { interp := fun x => match x with
                       | (values, idx) => [index_wrt values idx]
                       end }.


(* Default list_nat representation of a value *)
 
Fixpoint nats_lt n : list nat :=
  match n with
  | O => nil
  | S n' => O :: fmap S (nats_lt n')
  end.


Lemma index_wrt_cons : forall idx a values,
      index_wrt (a :: values) (fmap S idx) = index_wrt values idx.
Proof. 
  induction idx as [ | n]; intros a values; auto.
  simpl. 
  rewrite IHidx; auto.
Defined.

Fixpoint length {B} (l : list B) : nat :=
  match l with
  | nil => 0
  | _ :: l' => S (length l')
  end.

Lemma index_wrt_default : forall ls, 
      index_wrt ls (nats_lt (length ls)) = ls.
Proof.
  induction ls; simpl; auto.
  rewrite index_wrt_cons.
  rewrite IHls. 
  reflexivity.
Defined.

(****************)
(* Permutations *)
(****************)

Lemma interp_permutation : forall (values : list A) (idx1 idx2 : list nat),
      Permutation idx1 idx2 -> 
      [index_wrt values idx1] = [index_wrt values idx2].
Proof.
  intros values idx1 idx2 pf.
  induction pf; simpl in *; auto.
  - rewrite IHpf; auto.
  - rewrite NCM_assoc.
    rewrite (NCM_comm (interp_option (index values y)) (interp_option (index values x))).
    rewrite <- NCM_assoc. reflexivity.
  - rewrite IHpf1, IHpf2. reflexivity.
Defined.

About permutation.
Arguments permutation {A} {decA}.
Lemma permutation_reflection : forall (ls1 ls2 : list nat),
      permutation ls1 ls2 -> Permutation ls1 ls2.
Proof.
  apply permutation_Permutation.
Defined.


(**************)
(* Nilpotence *)
(**************)

(* There are two ways the interpretation of a list might be zero. 
   First, if 0 occurs in the list, the result will be zero, and two,
   if any non-1 element occurs in the list more than once, the result
   will be 0.
   With automation, we only have to check the second, as we can assume
   that our list will be populated with non-zero (and non-1) elements.
*)

Lemma interp_0 : forall (ls : list A),
      In 0 ls ->
      [ls] = 0.
Proof.
  induction ls; intros pf_in; simpl in *.
  - contradiction.
  - destruct pf_in as [eq | pf_in].
    * rewrite <- eq. apply NCM_absorb_l.
    * rewrite IHls; auto.
Defined.


Lemma in_nilpotent : forall (ls : list A) a,
      In a ls ->
      base a ->
      a · [ls] = 0.
Proof.
  induction ls as [ | b ls]; intros a pf_in pf_neq_1; simpl in *.
  - contradiction.
  - destruct pf_in as [pf_in | pf_in].
    * rewrite pf_in in *.
      rewrite NCM_assoc. 
      rewrite NCM_nilpotent; auto.
    * rewrite NCM_comm_assoc.
      rewrite IHls; auto.
Defined.


Lemma in_interp_nat : forall i a values idx,
      In i idx ->
      index values i = Some a ->
      In a (index_wrt values idx).
Proof.
  induction idx as [ | j idx]; intros pf_in pf_a; simpl in *.
  - contradiction.
  - destruct pf_in as [eq | pf_in].
    * rewrite <- eq in *. rewrite pf_a. left; auto.
    * right. apply IHidx; auto.
Defined.


(* find the value of the first duplicated value in the list *)
Fixpoint find_duplicate (ls : list nat) : option nat :=
  match ls with
  | nil => None
  | n :: ls' => if in_dec n ls' then Some n 
                else find_duplicate ls'
  end.



Lemma in_index : forall i a values,
      a = [index values i] -> a = 0 \/ In a values.
Proof.
  induction i; destruct values as [ | v values]; intros H; simpl in *; auto.
  destruct (IHi _ _ H); auto.
Defined.

Lemma in_index_wrt : forall a idx values,
      In a (index_wrt values idx) ->
      a = 0 \/ In a values. 
Proof.
  induction idx as [ | i]; intros values pf_in; simpl in *.
  - contradiction.
  - destruct pf_in as [pf_in | pf_in].
    * (* index values i = a implies In a values? not if a = 0... *)
      apply (in_index i); auto.
    * apply IHidx; auto.
Defined.

Lemma option_contradiction : forall {B C} {b : B}, Some b = None -> C.
Proof. 
  intros B C b H.
  set (P := fun (e : option B) => match e with
                                  | Some _ => Unit
                                  | None => Empty
                                  end).
  refine (Empty_rec (transport P H tt)).
Defined.

Lemma duplicate_nilpotent : forall values idx,
      Forall base values ->
      (exists i, find_duplicate idx = Some i) ->
      [index_wrt values idx] = 0.
Proof.
  intros values idx pf_forall.
  induction idx as [ | j idx]; intros [i pf_dup]; simpl in *.
  - apply (option_contradiction pf_dup^).
  - change ([index values j] · [index_wrt values idx] = 0).
    remember (index values j) as x eqn:H_a.
    destruct x as [a | ]; [ | apply NCM_absorb_l].
    (* if j occurs in idx, then we can apply in_nilpotent. *)
     assert (H_a' : a = [index values j]) by (rewrite H_a; auto). 
    remember (in_index j values H_a') as z eqn:H'.
    destruct z;
     [ rewrite p; simpl; apply NCM_absorb_l | ].
    destruct (in_dec j idx) as [H | H].
    * apply in_nilpotent; [ apply (in_interp_nat j); auto | ].
      apply (forall_in _ _ pf_forall); auto.
    * simpl; rewrite IHidx; auto.
      destruct (find_duplicate idx) as [k | ].
      + exists k; auto.
      + apply (option_contradiction pf_dup^).
Defined.      

End NCM.
(* TODO: We need to get the implicit arguments better. In this case, since
  NCM_unit_l doesn't actually use the NCM_Laws in the type (or maybe for another
  reason) it does not treat it as an implicit type. For now we can do it
  manually, but that's really annoying.
*)

Arguments NCM_unit_l {A} {NCM_A} {NCM_A_laws} : rename. 
Arguments NCM_absorb_l {A} {NCM_A} {NCM_A_laws} : rename.
Arguments NCM_comm_assoc {A} {NCM_A} {NCM_A_laws} : rename.
Arguments NCM_zero {A} : rename.
Arguments NCM_one {A} : rename.
Arguments NCM_var {A} : rename.
Arguments NCM_m {A} : rename.
Arguments flatten_correct' {A} {NCM_A} {NCM_A_laws} : rename.
Arguments flatten_correct {A} {NCM_A} {NCM_A_laws} : rename.
Arguments index_wrt {A} {NCM_A} : rename.
Arguments interp_permutation {A} {NCM_A} {NCM_A_laws} : rename.
Arguments interp_0 {A} {NCM_A} {NCM_A_laws} : rename.
Arguments in_nilpotent {A} {NCM_A} {NCM_A_laws} : rename.
Arguments in_interp_nat {A} {NCM_A} {NCM_A_laws} : rename.
Arguments in_index {A} {NCM_A} : rename.
Arguments in_index_wrt {A} {NCM_A} : rename.
Arguments duplicate_nilpotent {A} {NCM_A} {NCM_A_laws} : rename.


(***************************)
(* Putting it all together *)
(***************************)


Ltac lookup x xs :=
  match xs with
    | x :: _ => O
    | _ :: ?xs' =>
        let n := lookup x xs' in
        constr:(S n)
  end.

(* Also want an Ltac version *)
Ltac find_duplicate ls :=
  match ls with
  | ?n :: ?ls' => let z := lookup n ls' in n
  | _ :: ?ls' => find_duplicate ls'
  end.

Ltac simpl_args :=
  match goal with
  [ |- [ ?e1 ] = [ ?e2 ] ] => let H1 := fresh "H" in
                              let H2 := fresh "H" in
                              let x1 := fresh "x" in
                              let x2 := fresh "x" in 
                              remember e1 as x1 eqn:H1; 
                              remember e2 as x2 eqn:H2;
                              simpl in H1, H2;
                              rewrite <- H1, <- H2 in *; clear x1 x2 H1 H2
  end.




(* reify_wrt values ls returns a list of indices idx so that
   interp_list_nat' values idx = ls
*)
Ltac reify_wrt values ls :=
  match ls with
  | nil => constr:(@nil nat)
  | ?a :: ?ls' => let i := lookup a values in
                  let idx := reify_wrt values ls' in
                  constr:(i :: idx)
  end.



Ltac reification_wrt :=
  match goal with
  | [ |- ?a = ?a ] => reflexivity
  | [ |- [Some ?ls1] = [Some ?ls2] ] =>
    let idx1 := reify_wrt ls1 ls1 in
    let idx2 := reify_wrt ls1 ls2 in
    let ls1' := constr:(index_wrt ls1 idx1) in
    let ls2' := constr:(index_wrt ls1 idx2) in
    change ([ls1'] = [Some ls2'])
  | [ |- [Some ?ls1] = ?a2 ] =>
    let idx := reify_wrt ls1 ls1 in
    let ls1' := constr:(index_wrt ls1 idx) in
    change ([ls1'] = a2)
  | [ |- ?a1 = [Some ?ls2] ] =>
    let idx := reify_wrt ls2 ls2 in
    let ls2' := constr:(index_wrt ls2 idx) in
    change (a1 = [ls2'])
  end.


Ltac destruct_finite_In :=
  repeat match goal with
  | [ H : In _ _ + In _ _ |- _ ] => destruct H
  | [ H : In _ nil |- _ ] => apply (Empty_rec H)
  | [ H : In ?a (_ :: _) |- _ ] => destruct H as [H | H]; try (rewrite H; reflexivity)
  end.


Close Scope nat_scope.

Ltac reify A a :=
  match a with
  | 0 => constr:(@NCM_zero A)
  | 1 => constr:(@NCM_one A)
  | ?a1 · ?a2 => let e1 := reify A a1 in
                 let e2 := reify A a2 in
                 constr:(@NCM_m A e1 e2)
  | _ => constr:(@NCM_var A a)
  end.


Ltac prep_reification := 
  match goal with
  | [ |- ?a1 = ?a2 ] => 
    let A := type of a1 in
    let e1 := reify A a1 in
    let e2 := reify A a2 in
    change (([e1] : A) = ([e2] : A));
    repeat rewrite flatten_correct; auto;
    simpl_args;
    reification_wrt
  end.

Ltac solve_reification :=
  match goal with
  | [ |- [ index_wrt ?values ?idx ] = [ None ] ] => 
    let val := find_duplicate idx in
    apply duplicate_nilpotent; auto; exists val; reflexivity
  | [ |- [ None ] = [ index_wrt ?values ?idx ] ] => 
    let val := find_duplicate idx in
    rewrite duplicate_nilpotent; auto; exists val; reflexivity
  | [ |- [ _ ] = [ _ ] ] =>  
                        apply interp_permutation;
                        apply permutation_reflection;
                        apply meq_multiplicity; intros; destruct_finite_In
  end.
Ltac reification := prep_reification; solve_reification.
(* This doesn't account for EVARs yet *)


Section Examples.
Variable A : Type.
Variable NCM_A : `{NCM A}.
Variable NCM_A_Laws : `{NCM_Laws A}.



Example NCM_comm' : forall (a b : A), a · b = b · a.
Proof. 
  intros. reification.  
Defined.

Example NCM_unit' : forall a, 1 · a  = a.
Proof. intros. reification.
Defined.


Example NCM_absorb' : forall a, 0 · a = 0.
Proof. intros. reification.
Defined.

Example NCM_nilpotent' : forall a, base a -> a · a = 0.
Proof.
  intros. reification.
Defined.

End Examples.









