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
Notation "0" := zero : NCM_scope.
Notation "1" := one : NCM_scope.
Notation "a ∙ b" := (m a b) (left associativity, at level 25) : NCM_scope.


Open Scope NCM_scope.

Class NCM_Laws A `{NCM A} :=
  { NCM_unit  : forall a, a ∙ 1 = a
  ; NCM_assoc : forall a b c, a ∙ (b ∙ c) = (a ∙ b) ∙ c
  ; NCM_absorb: forall a, a ∙ 0 = 0
  ; NCM_comm  : forall a b, a ∙ b = b ∙ a
  ; NCM_nilpotent : forall a, base a -> a ∙ a = 0
  ; NCM_base_0 : ~ base 0
  ; NCM_1_0 : 1 <> 0
}.
Hint Resolve NCM_unit NCM_absorb NCM_base_0 NCM_1_0.



Set Implicit Arguments.



(****************************)
(* Interpretable type class *)
(****************************)

Class Interpretable (A B : Type) := { interp : B -> A }.
Notation "[ b ]" := (interp b) : NCM_scope.

About one.


Section NCM.
  Variable A : Type.
  Variable NCM_A : `{NCM A}.
  Variable NCM_A_Laws : `{NCM_Laws A}.



Lemma NCM_unit_l : forall a, 1 ∙ a = a.
Proof. intros. rewrite NCM_comm. auto. Defined.
Hint Resolve NCM_unit_l.
Lemma NCM_absorb_l : forall a, 0 ∙ a = 0. 
Proof. intros. rewrite NCM_comm. auto. Defined.
Hint Resolve NCM_absorb_l.

Lemma NCM_comm_assoc : forall a b c, a ∙ (b ∙ c) = b ∙ (a ∙ c).
Proof.
  intros. rewrite NCM_assoc. rewrite (NCM_comm a b). rewrite <- NCM_assoc.
  reflexivity.
Defined.

Lemma NCM_comm_assoc' : forall a b c, a ∙ b ∙ c = b ∙ a ∙ c.
Proof.
  intros. rewrite (NCM_comm a b). reflexivity.
Defined.


Lemma NCM_base_1 : ~ base 1.
Proof.
  intros H.
  assert (H' : 1 = 0).
  {
    apply NCM_nilpotent in H.
    rewrite NCM_unit in H. 
    assumption.
  }
  apply NCM_base_0.
  rewrite H' in H; auto.
Defined.

Lemma base_neq_0 : forall a, base a -> a <> 0.
Proof.
  intros a H H'.
  rewrite H' in H.
  apply NCM_base_0; auto.
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

Lemma interp_Some : forall a, [Some a] = a.
Proof.
  auto.
Defined.

Fixpoint interp_list {B} `{Interpretable A B} (ls : list B) :=
  match ls with
  | nil => 1
  | b :: ls' => [b] ∙ interp_list ls'
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
  | NCM_m e1 e2 => interp_NCM e1 ∙ interp_NCM e2
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
      [ls1] ∙ [ls2] = [ls1 ++ ls2].
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
      a ∙ [ls] = 0.
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

Lemma option_inversion : forall {B} {b c : B}, Some b = Some c -> b = c.
Admitted.

Lemma duplicate_nilpotent : forall values idx,
      (exists i, find_duplicate idx = Some i /\ base [index values i] ) ->
      [index_wrt values idx] = 0.
Proof.
  intros values idx.
  induction idx as [ | j idx]; intros [i [pf_dup pf_base]]; simpl in *.
  - apply (option_contradiction pf_dup^).
  - change ([index values j] ∙ [index_wrt values idx] = 0).
    destruct (in_dec j idx).
    * apply option_inversion in pf_dup. 
      rewrite pf_dup in *.
      remember (index values i) as z eqn:Hz.
      destruct z; auto.
      rewrite in_nilpotent; auto.
      apply (in_interp_nat i); auto.
    * simpl. rewrite IHidx; auto.
      exists i. split; auto.
Defined.
  
(********************************)
(* Proving properties are not 0 *)
(********************************)



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

Ltac print_goal :=
  match goal with
  | [|- ?G ] => idtac G
  end.

Ltac append ls1 ls2 := 
  match ls1 with
  | ?x :: ?l => let l' := append l ls2 in constr:(x :: l')
  | nil      => ls2
  end.

Ltac lookup x xs :=
  match xs with
    | x :: _ => constr:(O)
    | ?y :: ?xs' => let n := lookup x xs' in constr:(S n)
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
(* evar case 
  | ?a :: ?ls' => let i := constr:(100) in 
                 let idx := reify_wrt values ls' in
                 constr:(i :: idx) (* change *)
*)
  end.


(* Jen's version: 
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
*)

Ltac type_of_goal := 
  match goal with
  | [ |- ?a = _ ] => type of a
  end.

Ltac reification_wrt :=
  let A := type_of_goal in
  match goal with
  | [ |- ?a = ?a ] => reflexivity
  | [ |- [Some ?ls1] = [Some ?ls2] ] =>
    let src := append ls1 ls2 in 
    let idx1 := reify_wrt src ls1 in
    let idx2 := reify_wrt src ls2 in
    let ls1' := constr:(index_wrt src idx1) in
    let ls2' := constr:(index_wrt src idx2) in
    change (([ls1'] : A) = ([ls2'] : A))
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
  | ?a1 ∙ ?a2 => let e1 := reify A a1 in
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
    simpl_args  
  end.

Ltac simplify_duplicates values idx :=
  let val := find_duplicate idx in
  rewrite (duplicate_nilpotent values idx);
  [| exists val; split; [reflexivity | simpl; auto] ].

Ltac find_permutation :=
  apply interp_permutation;
  apply permutation_reflection;
  apply meq_multiplicity;
  intros; destruct_finite_In;
  fail.

Ltac solve_reification :=
  match goal with
  | [ |- [ index_wrt ?values1 ?idx1 ] = [ index_wrt ?values2 ?idx2 ] ] => 
    simplify_duplicates values1 idx1; 
    simplify_duplicates values2 idx2; auto
  | [ |- [ index_wrt ?values ?idx ] = _ ] => simplify_duplicates values idx; auto
  | [ |- _ = [ index_wrt ?values ?idx ] ] => simplify_duplicates values idx; auto
  | [ |- [ _ ] = [ _ ] ] =>  find_permutation
  end.
Ltac reification := prep_reification; reification_wrt; solve_reification.
(* This doesn't account for EVARs yet *)


Section Examples.
Variable A : Type.
Variable NCM_A : `{NCM A}.
Variable NCM_A_Laws : `{NCM_Laws A}.



Example NCM_comm' : forall (a b : A), a ∙ b = b ∙ a.
Proof.
  intros.
  prep_reification.
  reification_wrt.
  solve_reification.
Defined.

Example NCM_unit' : forall a, 1 ∙ a  = a.
Proof. 
  intros. prep_reification. 
Defined.


Example NCM_absorb' : forall a, 0 ∙ a = 0.
Proof.
  intros. prep_reification. 
Defined.

Example NCM_nilpotent' : forall a, base a -> a ∙ a = 0.
Proof.
  intros. prep_reification. reification_wrt. solve_reification.
Defined.

Example NCM_aab : forall a b, base a -> base b -> a ∙ a ∙ b = 0.
Proof.
  intros. prep_reification. reification_wrt.
  solve_reification.
Defined.

Example NCM_aba : forall a b, base a -> a ∙ b ∙ a = a ∙ a ∙ b.
Proof.
  intros. prep_reification. reification_wrt. solve_reification.
Qed.

Example NCM_aabb : forall a b, base a -> base b -> a ∙ a = b ∙ b.
Proof.
  intros. prep_reification. reification_wrt. solve_reification.
Qed. 

Example NCM_abc : forall a b c, a ∙ b ∙ c = c ∙ a ∙ 1 ∙ b.   
Proof.
  intros. prep_reification. reification_wrt. solve_reification. 
Defined.

(* Now to deal with evars!!! *)

Ltac has_evars term := 
  match term with
    | ?L = ?R        => has_evar L; has_evar R
    | ?L = ?R        => has_evars L
    | ?L = ?R        => has_evars R
    | ?Γ1 ∙ ?Γ2      => has_evar Γ1; has_evar Γ2
    | ?Γ1 ∙ ?Γ2      => has_evars Γ1
    | ?Γ1 ∙ ?Γ2      => has_evars Γ2
  end.

Ltac repos_evar :=
  repeat match goal with 
  | [ |- ?G ] => has_evars G; fail 1
  | [ |- ?a = ?b ] => has_evar b; symmetry 
  | [ |- context[?a ∙ ?b]] => has_evar a; rewrite (NCM_comm a b)
  end;
  repeat match goal with 
  | [ |- ?a ∙ (?b ∙ ?c) = _ ] => rewrite (NCM_assoc a b c)
  end.
  
Ltac rm_evar ls :=
  match ls with
  | nil => nil 
  | ?a :: ?ls' => let ls'' := rm_evar ls' in constr:(a :: ls'')
  | ?a :: ?ls' => ls' (* I cannot believe this works. Jeez. *)
  end.

Ltac split_reify_wrt vs1 vs2 ls :=
  match ls with
  | nil => constr:((@nil nat, @nil nat))
  (* in subset vs1 *)
  | ?a :: ?ls' => let i := lookup a vs1 in
                 let idx := split_reify_wrt vs1 vs2 ls' in
                 match idx with 
                 | (?l, ?r) => constr:((i :: l, r))
                 end
  (* not in subset vs1 *)
  | ?a :: ?ls' => let i := lookup a vs2 in
                 let idx := split_reify_wrt vs1 vs2 ls' in
                 match idx with 
                 | (?l, ?r) => constr:((l, i :: r))
                 end
  end.
  

Ltac simpl_args_evar :=
  match goal with
  [ |- [ ?e1 ] ∙ ?ev = [ ?e2 ] ] => 
                          let H1 := fresh "H" in
                          let H2 := fresh "H" in
                          let x1 := fresh "x" in
                          let x2 := fresh "x" in
                          remember e1 as x1 eqn:H1; 
                          remember e2 as x2 eqn:H2;
                          simpl in H1, H2;
                          rewrite <- H1, <- H2 in *; clear x1 x2 H1 H2
 end.

Ltac prep_reification_evar := 
  match goal with
  | [ |- ?a1 ∙ ?ev = ?a2 ] => 
    let A := type of a1 in
    let e1 := reify A a1 in
    let e2 := reify A a2 in
    change (([e1] : A) ∙ ev = ([e2] : A));
    repeat rewrite flatten_correct; auto;
    simpl_args_evar  
  end.

Ltac reification_wrt_evar :=
  let A := type_of_goal in
  match goal with
  | [ |- [Some ?ls1] ∙ ?ev = [Some ?ls2] ] =>
    let sub := ls1 in
    let super := append sub ls2 in 
    let idx := split_reify_wrt sub super ls2 in
    let ls2' := match idx with
                | (?idx2, ?idx3) => constr:(index_wrt super (idx2 ++ idx3))
                end in
    apply (@Overture.concat A _ ([ls2'] : A));
      [ | simpl; reification]
  end.


Lemma split_list : forall values ls1 ls2,
  [index_wrt values (ls1 ++ ls2)] = [index_wrt values ls1] ∙ [index_wrt values ls2].
Proof.
  induction ls1; intros.
  + simpl. rewrite NCM_unit_l. reflexivity.
  + simpl in *. rewrite IHls1. rewrite NCM_assoc. reflexivity.
Qed.  

Lemma split_m : forall a1 a2 b1 b2, a1 = a2 -> b1 = b2 -> a1 ∙ b1 = a2 ∙ b2.
Proof. 
  intros a1 a2 b1 b2 Ha Hb.
  rewrite Ha, Hb.
  reflexivity.
Defined.

Ltac reification' := 
  repos_evar;
  prep_reification_evar;
  reification_wrt_evar;
  rewrite split_list;
  apply split_m; [reification | reflexivity].


Example NCM_evar : forall a b c, exists d, b = d -> a ∙ b ∙ c = c ∙ d ∙ a ∙ 1.   
Proof.
  intros. 
  evar (y : A).
  exists y. unfold y.
  intros.
  reification'.
Qed.  

Example NCM_evar2 : forall a b c d e, exists x, x = d ∙ e ∙ b -> 
                                      a ∙ x ∙ c = b ∙ c ∙ d ∙ 1 ∙ e ∙ a. 
Proof.
  intros. 
  evar (y : A).
  exists y. unfold y.
  intros.
  reification'.
Qed.  


End Examples.


Unset Implicit Arguments.
Class PMonoid (A : Type) :=
  { one' : A ; m' : A -> A -> option A; base' : A -> Prop }.
Print NCM_Laws.
Class PMonoid_Laws (A : Type) `{PMonoid A} :=
  { PMonoid_unit : forall a, m' a one' = Some a ;
    PMonoid_assoc : forall a b c, (do x ← m' b c; m' a x) = (do x ← m' a b; m' x c) ;
    PMonoid_comm : forall a b, m' a b = m' b a ;
    PMonoid_nilpotence : forall a, base' a -> m' a a = None
   }.

Instance PMonoid_NCM {A} `{PMonoid A} : NCM (option A) :=
  { one := Some one'
  ; zero := None 
  ; m := fun x1 x2 => do a1 ← x1;
                      do a2 ← x2;
                      m' a1 a2
  ; base := fun x => match x with
                     | None => False
                     | Some a => base' a
                     end }.

Instance PMonoid_NCM_Laws A `{PMonoid A} `{PMonoid_Laws A} : NCM_Laws (option A).
Proof.
  split.
  - destruct a; auto. apply PMonoid_unit.
  - destruct a; destruct b; destruct c; simpl; auto.
    * apply PMonoid_assoc.
    * destruct (m' a a0); auto.
  - destruct a; auto.
  - destruct a; destruct b; auto. apply PMonoid_comm.
  - destruct a; auto. intros X. apply PMonoid_nilpotence. exact X.
  - auto.
  - simpl. intros G. apply (option_contradiction G).
Defined.

