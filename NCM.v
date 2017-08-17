Require Import Monad.
Require Import PermutSetoid.
Require Import Sorting.Permutation.
Require Import Sorting.PermutEq. (* Standard library *)  


Class NCM A :=
    { zero : A
    ; one  : A
    ; m    : A -> A -> A }.
Notation "0" := zero.
Notation "1" := one.
Notation "a · b" := (m a b) (right associativity, at level 20).


Class NCM_Laws A `{NCM A} :=
  { NCM_unit  : forall a, a · 1 = a
  ; NCM_assoc : forall a b c, a · (b · c) = (a · b) · c
  ; NCM_absorb: forall a, a · 0 = 0
  ; NCM_comm  : forall a b, a · b = b · a
  ; NCM_nilpotent : forall a, a = 1 \/ a · a = 0 }.
Hint Resolve NCM_unit NCM_absorb.

Set Implicit Arguments.


(****************************)
(* Interpretable type class *)
(****************************)

Class Interpretable (A B : Type) := { interp : B -> A }.
Notation "[ b ]" := (interp b).


Section NCM.
  Variable A : Type.
(*
  Variable zero : A.
  Variable one : A.
  Variable m : A -> A -> A. 
*)
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

Definition interp_option {B} `{Interpretable A B} (o : option B) : A :=
  match o with
  | Some b => [b]
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
  destruct (flatten e1) as [ ls1 | ] eqn:H1; auto.
  destruct (flatten e2) as [ ls2 | ] eqn:H2; simpl; auto.
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
Require Import List.
Print map. Print list_fmap.

Lemma index_wrt_cons : forall idx a values,
      index_wrt (a :: values) (fmap S idx) = index_wrt values idx.
Proof. 
  induction idx as [ | n]; intros a values; auto.
  simpl. 
  rewrite IHidx; auto.
Defined.

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

Lemma interp_permutation : forall values idx1 idx2, 
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

Lemma permutation_reflection : forall ls1 ls2,
      @permutation nat _ PeanoNat.Nat.eq_dec ls1 ls2 -> Permutation ls1 ls2.
Proof.
  intros. apply (permutation_Permutation PeanoNat.Nat.eq_dec); auto.
Defined.


Require Import Multiset. About list_contents.
Require Import Arith.

Search multiplicity. Print multiplicity.

(*
Lemma list_contents_multiplicity : forall ls x, 
        length ls <= x -> multiplicity (list_contents eq Nat.eq_dec ls) x = 0%nat.
Proof.
Admitted.
*)
Notation contents := (list_contents eq Nat.eq_dec).

Lemma meq_multiplicity : forall (ls1 ls2 : list nat),
      (forall x, In x ls1 \/ In x ls2 ->
                 multiplicity (contents ls1) x = multiplicity (contents ls2) x) ->
      meq (contents ls1) (contents ls2).
Proof.
  intros ls1 ls2 H x.
  Search In.
  destruct (in_dec Nat.eq_dec x ls1); [apply H; auto | ].
  destruct (in_dec Nat.eq_dec x ls2); [apply H; auto | ].
  repeat rewrite multiplicity_In_O; auto. 
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
    * rewrite eq. apply NCM_absorb_l.
    * rewrite IHls; auto.
Defined.


Lemma in_nilpotent : forall (ls : list A) a,
      In a ls ->
      a <> 1 ->
      a · [ls] = 0.
Proof.
  induction ls as [ | b ls]; intros a pf_in pf_neq_1; simpl in *.
  - contradiction.
  - destruct pf_in as [pf_in | pf_in].
    * rewrite pf_in in *.
      rewrite NCM_assoc. 
      destruct (NCM_nilpotent a) as [ | H]; [contradiction | ].
      rewrite H; auto.
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
    * subst. rewrite pf_a. left; auto.
    * right. apply IHidx; auto.
Defined.


(* Instead of using multiplicity, use a special operation intended to check for duplicates *)

(*
Lemma duplicate_nilpotent' : forall values idx i,
      index values i <> 1 ->
      multiplicity (contents idx) i > 1 ->
      interp_list' (interp_list_nat' values idx) = 0.
Proof.
  induction idx; intros i H_i H_multiplicity.
  - simpl in H_multiplicity. inversion H_multiplicity.
  - simpl in H_multiplicity. destruct (Nat.eq_dec a i) eqn:H_a_i; simpl in *.
    * subst. 
      apply gt_S_n in H_multiplicity.
      apply multiplicity_In in H_multiplicity.
      apply in_nilpotent; auto.
      apply in_interp_nat. auto.
    * rewrite (IHidx i); auto.
Defined.

Lemma duplicate_nilpotent : forall values idx i,
      index values i <> 1 ->
      multiplicity (contents idx) i > 1 ->
      interp_list_nat values (Some idx) = 0.
Proof.
  intros. unfold interp_list_nat; simpl. apply (duplicate_nilpotent' _ _ i); auto.
Qed.
*)

About in_dec.

(* find the value of the first duplicated value in the list *)
Fixpoint find_duplicate (ls : list nat) : option nat :=
  match ls with
  | nil => None
  | n :: ls' => if in_dec Nat.eq_dec n ls' then Some n 
                else find_duplicate ls'
  end.



Require Import List.
Search (list ?A -> (?A -> Prop) -> Prop).

 
Lemma forall_in : forall {B : Type} P (ls : list B),
      Forall P ls -> forall i, In i ls -> P i.
Proof.
  intros B P ls H i pf_in.
  induction H; auto.
  - contradiction.
  - destruct pf_in as [eq | pf_in].
    * subst; auto.
    * apply IHForall; auto.
Defined.

Lemma in_index : forall i a values,
      [index values i] = a -> a = 0 \/ In a values.
Proof.
  induction i; destruct values; intros; auto.
  - simpl in H. right. left. auto.
  - simpl in H. 
    destruct (IHi _ _ H); auto.
    right. right. auto.
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

Lemma duplicate_nilpotent : forall values idx,
      Forall (fun x => x <> 1) values ->
      (exists i, find_duplicate idx = Some i) ->
      [index_wrt values idx] = 0.
Proof.
  intros values idx pf_forall.
  induction idx as [ | j idx]; intros [i pf_dup]; simpl in *.
  - inversion pf_dup.
  - change ([index values j] · [index_wrt values idx] = 0).
    destruct (index values j) as [a | ] eqn:H_a; [ | apply NCM_absorb_l].
    (* if j occurs in idx, then we can apply in_nilpotent. *)
     assert (H_a' : [index values j] = a) by (rewrite H_a; auto).
     destruct (in_index j values H_a') eqn:H'; auto;
     [ rewrite e; simpl; apply NCM_absorb_l | ].
    destruct (in_dec Nat.eq_dec j idx) as [H | H].
    * apply in_nilpotent; [ apply (in_interp_nat j); auto | ].
      apply (@forall_in _ (fun x => x <> 1) values); auto. 
    * simpl; rewrite IHidx; auto.
      destruct (find_duplicate idx) as [k | ].
      + exists k; auto.
      + inversion pf_dup.
Defined.      

End NCM.
About NCM_unit_l.
(* TODO: We need to get the implicit arguments better. In this case, since
  NCM_unit_l doesn't actually use the NCM_Laws in the type (or maybe for another
  reason) it does not treat it as an implicit type. For now we can do it
  manually, but that's really annoying.
*)

Arguments NCM_unit_l {A} {NCM_A} {NCM_laws} : rename. 
About NCM_unit_l.

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


Ltac reify a :=
  match a with
  | 0 => NCM_zero
  | 1 => NCM_one
  | ?a1 · ?a2 => let e1 := reify a1 in
                 let e2 := reify a2 in
                 constr:(NCM_m e1 e2)
  | _ => constr:(NCM_var a)
  end.


Ltac simpl_args :=
  match goal with
  [ |- [ ?e1 ] = [ ?e2 ] ] => remember e1 as x1 eqn:H1; 
                          remember e2 as x2 eqn:H2;
                          simpl in H1, H2;
                          rewrite H1, H2 in *; clear x1 x2 H1 H2
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
  | [ H : In _ _ \/ In _ _ |- _ ] => destruct H
  | [ H : In ?a _ |- _ ] => inversion H; try (subst; reflexivity)
  end.

Ltac prep_reification := 
  match goal with
  | [ _ : NCM ?A |- ?a1 = ?a2 ] => 
    let e1 := reify a1 in
    let e2 := reify a2 in
    change (([e1] : A) = ([e2] : A));
    repeat rewrite flatten_correct; auto;
    simpl_args;
    reification_wrt
  end.

Ltac solve_reification :=
  match goal with
  | [ |- [ index_wrt ?values ?idx ] = [ None ] ] => 
    let val := find_duplicate idx in
    rewrite duplicate_nilpotent; auto; exists val; reflexivity
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
  intros.
    let e1 := reify (a · b) in 
    let e2 := reify (b · a) in
    change (([e1] : A) = [e2]).
    repeat rewrite flatten_correct; auto.
    simpl_args.
index_wrt ls1 idx1
    reification_wrt.

reification.
Defined.

Example NCM_unit' : forall a, 1 · a = a.
Proof. intros. reification. Defined.


Example NCM_absorb' : forall a, 0 · a = 0.
Proof. intros; reification. Defined.

Example NCM_nilpotent' : forall a, a <> 1 -> a · a = 0.
Proof.
  intros. reification.
Defined.

End Examples.










(*

Fixpoint interp_list' {A} `{Nilpotent_Commutative_Monoid A} 
                (indices : list nat) (values : list A) : A :=
  match indices with
  | nil => one
  | (i :: indices') => index i values · interp_list' indices' values
  end.

Definition interp_list {A} `{Nilpotent_Commutative_Monoid A} 
                (indices : option (list nat)) (values : list A) : A :=
  match indices with
  | None => zero
  | Some ls => interp_list' ls values
  end.
Lemma flatten_correct : forall e, interp_NCM e = interp_list (flatten e).


Ltac reify a :=
  match a with
  | 0 => constr:(None)
  | 1 => constr:(Some nil)
  | ?a1 · ?a2 => let o1 := reify a1 in
                 let o2 := reify a2 in
                 constr:(do ls1 ← o1;
                         do ls2 ← o2;
                         return_ (ls1 ++ ls2))
  | _ => constr:(Some (a :: nil))
  end.
Ltac reify_wrt' ls a :=
  match a with
  | 0 => constr:(None)
  | 1 => constr:(Some nil)
  | ?a1 · ?a2 => let o1 := reify_wrt' ls a1 in
                 let o2 := reify_wrt' ls a2 in
                 constr:(do ls1 ← o1;
                         do ls2 ← o2;
                         return_ (ls1 ++ ls2))
  | _ => let i := lookup a ls in
         constr:(Some (i :: nil))
  end.
Ltac reify_wrt ls a := 
  match ls with
  | Some ?ls' => reify_wrt' ls' a
  | None      => None
  end.

Fixpoint list_up_to (n : nat) : list nat :=
  match n with
  | 0 => nil
  | S n' => list_up_to n' ++ n' :: nil
  end.


Ltac reification :=
  match goal with
  | [ |- ?a1 = ?a2 ] => let values := reify a1 in
                        let ls1 := reify_wrt values a1 in
                        let ls2 := reify_wrt values a2 in
                        change (interp_list ls1 values = interp_list ls2 values)
  end.

Ltac simpl_exp e :=
  remember e as e' eqn:H; simpl in H;
  match goal with
  | [H : _ = ?e |- _] => clear H; constr:(e)
  end.

Lemma comm : forall A `{Nilpotent_Commutative_Monoid A} (a b : A),
             a · b = b · a.
Proof. intros.  
  let a1 := constr:(a · b) in
  let values := reify a1 in
  remember values as values' eqn:H0. simpl in H0.
  match goal with
  | [ H0 : _ = ?values |- _ ] => clear H0; idtac values
(*    let ls1 := reify_wrt values (a · b) in idtac ls1*)
  end.
  let values := constr:(Some (a :: b :: nil)) in 
  let ls1 := reify_wrt values (a · b) in 
  remember ls1 as ls1' eqn:H1; simpl in H1;
  match goal with 
  | [ H1 : _ = ?ls1 |- _ ] => clear H1; idtac ls1
  end.
  let values := constr:(Some (a :: b :: nil)) in 
  let ls2 := reify_wrt values (b · a) in 
  remember ls2 as ls2' eqn:H2; simpl in H2;
  match goal with 
  | [ H2 : _ = ?ls2 |- _ ] => clear H2; idtac ls2
  end.
  let values := constr:(a :: b :: nil) in
  let ls1 := constr:(Some (0 :: 1 :: nil)%nat) in 
  let ls2 := constr:(Some (1 :: 0 :: nil)%nat) in
  let a1 := constr:(interp ls1 values) in idtac a1.
  assert (a · b = interp (Some (0 :: 1 :: nil)%nat) (a :: b :: nil)).
  simpl.
  change (interp ls1 values = interp ls2 values).

  let ls1' := simpl_exp ls1 in idtac ls1'.
  

  remember ls1 as ls1' eqn:H1; simpl in H1.
  match goal with
  | [H1 : _ = Some ?ls1 |- _ ] => 
  end.
  
  let ls1' :=  in
  match values with
  | Some values => set (values' := values)
  end.
  set (values' := values). 

  let ls1 := reify_wrt values a1 in idtac ls1.

  let values := reify (a · b) in idtac values. (* do ls1 ← Some (a :: nil);
                                                  do ls2 ← Some (b :: nil);
                                                  return_ (ls1 ++ ls2) *)
  set (values := do ls1 ← Some (a :: nil);
                 do ls2 ← Some (b :: nil);
                 return_ (ls1 ++ ls2)). simpl in values.
  set (values' := (a :: b :: nil)). 
  let i := lookup a (a :: b :: nil) in idtac i.
  let values := constr:(a :: b :: nil) in
  let i := lookup a values in
  let ls1 := reify_wrt' values (a · b) in 
  set (values0 := ls1). simpl in values0.


  let ls1 := reify_wrt' values' (a · b) in idtac ls1.
  set (values := reify a1).
reification.



(* Sorting lists *)
Require Import Compare_dec.

(* inserts a number into an already sorted lists *)
(* if n already occurs in ls, fail *)
Fixpoint insert (n : nat) (ls : list nat) : option (list nat) :=
  match ls with
  | nil => Some (n :: nil)
  | m :: ls => match lt_eq_lt_dec n m with
                 (* If n < m, the result n::m::ls is sorted *)
               | inleft (left _) => Some (n :: m :: ls)
                 (* If n = m, fail *)
               | inleft (right _) => None
                 (* If n > m, insert it into the tail of the list *)
               | inright _ => do ls' ← insert n ls;
                              return_ (m :: ls')
               end
  end.


(* merges two sorted lists *)
(* not a good implementation of merge *)
(* will fail if the lists contain duplicates *)
Fixpoint merge (ls1 ls2 : list nat) : option (list nat) :=
  match ls1 with
  | nil => return_ ls2
  | n1 :: ls1 => do ls ← merge ls1 ls2;
                 insert n1 ls
  end.



Instance NCM_sorted_list : Nilpotent_Commutative_Monoid (option (list nat)) :=
  { zero := None
  ; one  := Some nil
  ; m    := fun o1 o2 => do ls1 ← o1;
                         do ls2 ← o2;
                         merge ls1 ls2
  }.

Print In.
Fixpoint Sorted (l : list nat) : Prop :=
  match l with
  | nil => True
  | a :: l' => Sorted l' /\ match l' with
                            | nil => True
                            | b :: l'' => a < b
                            end
  end.

Lemma merge_nil_r : forall ls, Sorted ls -> merge ls nil = Some ls.
Proof.
  induction ls; simpl; intros; auto.
  destruct H.
  rewrite IHls; auto.
  destruct ls; auto.
  simpl. destruct (lt_eq_lt_dec a n) as [[ | ] | ]; auto.
  - absurd (a = n); auto. apply PeanoNat.Nat.lt_neq; auto.
  - absurd (n < a); auto. apply PeanoNat.Nat.lt_asymm; auto.
Defined.

Lemma merge_assoc : forall a b c, 
      Some a · Some b · Some c = (Some a · Some b) · Some c.
Admitted.
Lemma merge_comm : forall a b, Some a · Some b = Some b · Some a.
Admitted.

Lemma in_insert_0 : forall ls n, In n ls -> Sorted ls -> insert n ls = None.
Proof.
  induction ls as [ | m ls]; simpl; intros; auto.
  - contradiction.
  - destruct (lt_eq_lt_dec n m) as [[ | ] | ]; auto.
    * admit (* there is a contradiction here *).
    * assert (m <> n). apply PeanoNat.Nat.lt_neq; auto.
      destruct H; [contradiction | ].
      destruct H0; auto.
      rewrite IHls; auto.
Admitted.


Lemma insert_in : forall a ls ls', insert a ls' = Some ls -> In a ls.
Admitted.
Lemma insert_tail : forall a b ls ls', In a ls' -> insert b ls' = Some ls -> In a ls.
Admitted.

Lemma merge_in : forall ls1 ls2 ls n, In n ls1 \/ In n ls2 
              -> merge ls1 ls2 = Some ls 
              -> In n ls.
Proof.
  induction ls1; simpl; intros. 
  - inversion H0; subst. destruct H; [contradiction | auto].
  - destruct (merge ls1 ls2)  as [ls' | ] eqn:pf_merge; [ | inversion H0].
    destruct H as [ [ | ] | ].
    * subst. eapply insert_in; eauto.
    * eapply insert_tail; [ | eauto].
      eapply IHls1; [ |  eauto]. auto.
    * eapply insert_tail; [ | eauto].
      eapply IHls1; [ | eauto]. auto.
Defined.

Instance NCM_sorted_list_laws : NCM_Laws (option (list nat)).
Proof.
  split.
  - destruct a; simpl; auto. apply merge_nil_r.
  - destruct a as [a | ], b as [b | ], c as [c | ]; auto.
    * apply merge_assoc.
    * simpl. destruct (merge a b); auto.
  - destruct a; auto.
  - destruct a as [a | ], b as [b | ]; auto.
    apply merge_comm.
  - destruct a as [[ | a] | ]; auto.
    right; simpl.
    destruct (merge l (a :: l)) eqn:H; auto.
    apply in_insert_0.
    eapply merge_in; [ | exact H].
    simpl; auto.
Defined.



(* Convert an mexp to a sorted list *)
(*Record mlist A := mk_mlist { bases : list nat
                           ; evar : option A }.*)
Inductive mlist A :=
| mk_mlist : list nat -> option A -> mlist A.
Arguments mk_mlist {A}.
(* mlist is an instance of Nilpotent_Commutative_Monoid *)

Definition mlist_M {A} (e1 : mlist A) (e2 : mlist A) : option (mlist A) :=
  match e1, e2 with
  | mk_mlist ls1 (Some _), mk_mlist ls2 (Some _) => None
  | mk_mlist ls1 (Some evar1), mk_mlist ls2 None => 
    do ls ← merge ls1 ls2;
    return_ (mk_mlist ls (Some evar1) )
  | mk_mlist ls1 None, mk_mlist ls2 (Some evar2) => 
    do ls ← merge ls1 ls2;
    return_ (mk_mlist ls (Some evar2) )
  | mk_mlist ls1 None, mk_mlist ls2 None => 
    do ls ← merge ls1 ls2;
    return_ (mk_mlist ls None)
  end.

Instance NCM_olist {A} : Nilpotent_Commutative_Monoid (option (mlist A)) :=
  { zero := None
  ; one  := Some (mk_mlist nil None)
  ; m    := fun x1 x2 => do e1 ← x1;
                         do e2 ← x2;
                         mlist_M e1 e2 }.

(* TODO: prove NCM laws *)

Fixpoint to_mlist {A} (e : mexp A) : option (mlist A) :=
  match e with
  | Evar a  => Some (mk_mlist nil (Some a))
  | Base i  => Some (mk_mlist (i :: nil) None)
  | Zero    => 0
  | One     => 1
  | M e1 e2 => to_mlist e1 · to_mlist e2
  end.
(* Note: the result will also be sorted! *)


(* Now, when we compare two mlists, we will want to unify the values, and match
the remaining indices with the remaining mvar.
*)
Inductive Result A :=
| Success
| Failure
| Resolve : list nat -> A -> Result A.
Arguments Success {A}.
Arguments Failure {A}.
Arguments Resolve {A}.

Require Import PeanoNat.

Fixpoint remove (n : nat) (ls : list nat) : option (list nat) :=
  match ls with
  | nil => return_ nil
  | (m :: ls) => if Nat.eq_dec m n then return_ ls 
                 else do ls' ← remove n ls;
                      return_ (m :: ls')
  end.


(* returns the elements of ls1 ∪ ls2 that do not occur in ls1 ∩ ls2 *)
Fixpoint xor_list (ls1 ls2 : list nat) : list nat :=
  match ls1 with
  | nil => ls2
  | x :: ls1 => match remove x ls2 with
                | Some ls2' => (* x did occur in ls2 *) 
                    xor_list ls1 ls2'
                | None => (* x did not occur in ls2 *)
                    x :: (xor_list ls1 ls2)
                end
  end.

Fixpoint unify {A} (e1 e2 : mexp A) : option (mexp A) :=

Ltac unify e1 e2 (* : mlist A *) :=
  match e with
  | mk_mlist nil None => idtac
  | mk_mlist (

*)