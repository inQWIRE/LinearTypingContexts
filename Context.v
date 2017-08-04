Require Import Monad.

Class Nilpotent_Commutative_Monoid (A : Type) := 
    { zero : A
    ; one  : A
    ; m    : A -> A -> A }.
Notation "0" := zero.
Notation "1" := one.
Notation "a · b" := (m a b) (right associativity, at level 20).

Class Nilpotent_Commutative_Monoid_Laws A `{Nilpotent_Commutative_Monoid A} :=
  { m_unit  : forall a, a · 1 = a
  ; m_assoc : forall a b c, a · (b · c) = (a · b) · c
  ; m_absorb: forall a, a · 0 = 0
  ; m_comm  : forall a b, a · b = b · a
  ; m_nilpotent : forall a, a = 1 \/ a · a = 0 }.

Inductive mexp A :=
  | Evar : A -> mexp A
  | Base : nat -> mexp A
  | Zero : mexp A
  | One  : mexp A
  | M    : mexp A -> mexp A -> mexp A.
Arguments Evar {A}.
Arguments Base {A}.
Arguments Zero {A}.
Arguments One {A}.
Arguments M {A}.

(* Put EVars into Base, or add another constructor? *)


Ltac lookup x xs :=
  match xs with
    | (x, _) => O
    | (_, ?xs') =>
      let n := lookup x xs' in
        constr:(S n)
  end.

Open Scope list_scope.
Fixpoint index {A} (xs : list A) (n : nat) : option A :=
  match xs, n with
  | nil, _ => None
  | (x :: _), 0 => Some x
  | (_ :: xs), S x => index xs x
  end.

Ltac reify ls a :=
  match a with
  | zero => Zero
  | one  => One
  | ?a1 · ?a2 => let r1 := reify a1 in
                 let r2 := reify a2 in
                 constr:(M r1 r2)
  | _ => tryif is_evar a then constr:(Evar a) 
         else let x := lookup a ls in constr:(Base a)
  end.

(* Sorting lists *)
Require Import Compare_dec.

(* inserts a number into an already sorted lists *)

Fixpoint insert (n : nat) (ls : list nat) : option (list nat) :=
  match ls with
  | nil => Some (n :: nil)
  | m :: ls => match lt_eq_lt_dec n m with
               | inleft (left _) => Some (n :: m :: ls)
               | inleft (right _) => None
               | inright _ => do ls' ← insert n ls;
                              return_ (m :: ls')
               end
  end.


(* merges two sorted lists *)
(* not a good implementation of merge *)
(* may fail if the lists contain duplicates *)
Fixpoint merge (ls1 ls2 : list nat) : option (list nat) :=
  match ls1, ls2 with
  | ls1, nil => return_ ls1
  | nil, ls2 => return_ ls2
  | n1 :: ls1, n2 :: ls2 => match lt_eq_lt_dec n1 n2 with
                            | inleft (left _)(* n1 < n2 *) => 
                              do ls ← merge ls1 ls2;
                              do ls' ← insert n2 ls;
                              return_ (n1 :: ls')
                            | inleft (right _) (* n1 = n2 *) => None
                            | inright _ (* n1 > n2 *) => 
                              do ls ← merge ls1 ls2;
                              do ls' ← insert n1 ls;
                              return_ (n2 :: ls')
                            end
  end.



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