(* Require Import HoTT. *)

Class Nilpotent_Commutative_Monoid (A : Set) := 
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
  | Base : A -> mexp A
  | Zero : mexp A
  | One  : mexp A
  | M    : mexp A -> mexp A -> mexp A.

(* Put EVars into Base, or add another constructor? *)

Ltac reify a :=
  match a with
  | zero => Zero
  | one  => One
  | ?a1 · ?a2 => let r1 := reify a1 in
                 let r2 := reify a2 in
                 constr:(M r1 r2)
  | _ => tryif is_evar a then constr:(Evar a) else constr:(Base a)
  end.

Inductive mexp' A :=
  | Evar' : A -> mexp'  A
  | Base' : nat -> mexp' A
  | Zero' : mexp' A
  | One'  : mexp' A
  | M'    : mexp' A -> mexp' A -> mexp' A.


Ltac lookup x xs :=
  match xs with
    | (x, _) => O
    | (_, ?xs') =>
      let n := lookup x xs' in
        constr:(S n)
  end.

Ltac reify' ls a :=
  match a with
  | zero => Zero'
  | one  => One'
  | ?a1 · ?a2 => let r1 := reify a1 in
                 let r2 := reify a2 in
                 constr:(M' r1 r2)
  | _ => tryif is_evar a then constr:(Evar' a) else let x := lookup a ls in
                                                    constr:(Base' x)
  end.
