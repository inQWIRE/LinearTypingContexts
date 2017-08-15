Require Import Monad.
Require Import PermutSetoid.
Require Import Sorting.Permutation.
Require Import Sorting.PermutEq. (* Standard library *)  About permutation. 
                                                         About permut_In_In. 
                                                         About Permutation.


Section NCM.
  Variable A : Type.
  Variable zero : A.
  Variable one : A.
  Variable m : A -> A -> A.

(*  

Class Nilpotent_Commutative_Monoid A := 
    { zero : A
    ; one  : A
    ; m    : A -> A -> A }. *)
Notation "0" := zero.
Notation "1" := one.
Notation "a · b" := (m a b) (right associativity, at level 20).

(* I care about the NCM laws up to a certain equivalence relation, 
   at least in the case of lists. That means I either want to paramaterize
   the NCM_Laws type class with an (equivalence) relation, or we want to
   consider a HIT to do that. That's quite annoying... 
   Maybe we don't actually want the laws for a list, but always be talking in
   terms of its interpretation...
 *)

(*
Class NCM_Laws :=
  { m_unit  : forall a, a · 1 = a
  ; m_assoc : forall a b c, a · (b · c) = (a · b) · c
  ; m_absorb: forall a, a · 0 = 0
  ; m_comm  : forall a b, a · b = b · a
  ; m_nilpotent : forall a, a = 1 \/ a · a = 0 }.
*)
Hypothesis NCM_unit : forall a, a · 1 = a.
Hypothesis NCM_assoc : forall a b c, a · (b · c) = (a · b) · c.
Hypothesis NCM_absorb : forall a, a · 0 = 0.
Hypothesis NCM_comm : forall a b, a · b = b · a.
Hypothesis NCM_nilpotent : forall a, a = 1 \/ a · a = 0.

Lemma NCM_unit_l : forall a, 1 · a = a.
Proof. intros. rewrite NCM_comm. auto. Defined.
Hint Resolve NCM_unit_l.
Lemma NCM_absorb_l : forall a, 0 · a = 0. 
Proof. intros. rewrite NCM_comm. auto. Defined.
Hint Resolve NCM_absorb_l.

Require Import List.
Open Scope list_scope.


(* Structural representation of an NCM *)
Inductive NCM :=
| NCM_zero : NCM
| NCM_one  : NCM
| NCM_var  : A -> NCM
| NCM_m    : NCM -> NCM -> NCM.

(*
Instance NCM_NCM {A} : Nilpotent_Commutative_Monoid (NCM A) :=
  { zero := NCM_zero
  ; one  := NCM_one
  ; m    := NCM_m}.
*)

Fixpoint interp_NCM (e : NCM) : A :=
  match e with
  | NCM_zero => 0
  | NCM_one => 1
  | NCM_var a => a
  | NCM_m e1 e2 => interp_NCM e1 · interp_NCM e2
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

(****************)
(* lists of A's *)
(****************)

Fixpoint flatten (e : NCM) : option (list A) :=
  match e with
  | NCM_zero => None
  | NCM_one  => Some nil
  | NCM_var a => Some (a :: nil)
  | NCM_m e1 e2 => do ls1 ← flatten e1;
                   do ls2 ← flatten e2;
                   return_ (ls1 ++ ls2)
  end.

Fixpoint interp_list' (ls : list A) : A :=
  match ls with
  | nil => 1
  | a :: ls' => a · interp_list' ls'
  end.
Definition interp_list (ls : option (list A)) : A :=
  match ls with
  | Some ls' => interp_list' ls'
  | None => 0
  end.

Lemma flatten_correct' : forall ls1 ls2, 
      interp_list' ls1 · interp_list' ls2 = interp_list' (ls1 ++ ls2).
Proof.
  induction ls1; intros; simpl; auto.
  rewrite <- NCM_assoc. rewrite IHls1. reflexivity.
Defined.


Lemma flatten_correct : forall e, interp_NCM e = interp_list (flatten e).
Proof.
  intros.
  induction e; simpl; auto.
  rewrite IHe1, IHe2.
  destruct (flatten e1) as [ ls1 | ] eqn:H1; auto.
  destruct (flatten e2) as [ ls2 | ] eqn:H2; auto.
  simpl.
  apply flatten_correct'.
Defined.




(*****************)
(* lists of nats *)
(*****************)


(* Instead of working with list A directly, we instead want to work with
   a pair of a list A and a list nat-- the elements in the second list
   index into the first list, and let us compare elements.
 *)


Fixpoint index (xs : list A) (n : nat) : A :=
  match xs, n with
  | nil, _ => 0
  | (x :: _), 0 => x
  | (_ :: xs), S x => index xs x
  end.

Definition interp_list_nat' (values : list A) (indices : list nat) : list A :=
  map (index values) indices.
Definition interp_list_nat (values : list A) (indices : option (list nat)) 
                                             : A :=
  interp_list (fmap (interp_list_nat' values) indices).


Ltac lookup x xs :=
  match xs with
    | x :: _ => O
    | _ :: ?xs' =>
        let n := lookup x xs' in
        constr:(S n)
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


(****************)
(* Permutations *)
(****************)

Lemma interp_permutation : forall values idx1 idx2, 
      Permutation idx1 idx2 -> 
      interp_list' (interp_list_nat' values idx1) 
    = interp_list' (interp_list_nat' values idx2).
Proof.
  intros values idx1 idx2 pf.
  induction pf; simpl; auto.
  - rewrite IHpf; auto.
  - rewrite NCM_assoc. rewrite (NCM_comm (index values y) (index values x)).
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

(***************************)
(* Putting it all together *)
(***************************)

Ltac simpl_args f :=
  match goal with
  [ |- f ?e1 = f ?e2 ] => remember e1 as x1 eqn:H1; 
                          remember e2 as x2 eqn:H2;
                          simpl in H1, H2;
                          rewrite H1, H2 in *; clear x1 x2 H1 H2
  end.




Ltac reification_wrt :=
  match goal with
  | [ |- interp_list None = interp_list None ] => reflexivity
  | [ |- interp_list (Some ?ls1) = interp_list (Some ?ls2) ] =>
    let idx1 := reify_wrt ls1 ls1 in
    let idx2 := reify_wrt ls1 ls2 in
    let ls1' := constr:(interp_list_nat' ls1 idx1) in
    let ls2' := constr:(interp_list_nat' ls1 idx2) in
    change (interp_list (Some ls1') = interp_list (Some ls2'))
  end.


Ltac destruct_finite_In :=
  repeat match goal with
  | [ H : In _ _ \/ In _ _ |- _ ] => destruct H
  | [ H : In ?a _ |- _ ] => inversion H; try (subst; reflexivity)
  end.

Ltac reification :=
  match goal with
  | [ |- ?a1 = ?a2 ] => let e1 := reify a1 in
                        let e2 := reify a2 in
                        change (interp_NCM e1 = interp_NCM e2);
                        repeat rewrite flatten_correct; 
                        simpl_args interp_list;
                        reification_wrt;
                        apply interp_permutation;
                        apply permutation_reflection;
                        apply meq_multiplicity; intros; destruct_finite_In
  end.
(* This doesn't account for EVARs yet *)
(* Also not sure if it says anything about the nilpotent part... *)


Example NCM_comm' : forall (a b : A), a · b = b · a.
Proof.
  intros. reification. 
Defined.

Example NCM_unit' : forall a, 1 · a = a.
Proof. intros. reification. Defined.


Example NCM_absorb' : forall a, 0 · a = 0.
Proof. intros; reification. Defined.


End NCM.











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