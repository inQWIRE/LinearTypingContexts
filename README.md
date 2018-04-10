This repository contains a framework for reasoning about linear typing contexts
in Coq. 

The file `Monoid.v` describes the algebraic structure of partial commutative
monoids, which are characterized by the following parts:

- A base type "A"
- A unit element "⊤ : A"
- An undefined element "⊥ : A"
- A merge operation, written "a ∙ b"

Partial commutative monoids satisfy the following laws:

- (A,⊤,∙) forms a commutative monoid
- a ∙ ⊥ = ⊥

The tactic `monoid` solves goals of the form `a = b`, where `a` and `b` are made up of PCM constructors and at most one EVar.

The file `TypingContext.v` describes additional structure on top of PCM's. A typing context "Ctx" with domain "X" and image "A" satisfies:

- `Ctx` is a partial commutative monoid
- for `x:X` and `a:A`, a singleton context `singleton x a : Ctx`
- for any context `Γ:Ctx`, a predicate `is_valid Γ` that checks if Γ is the
  undefined element ⊥.
  
The tactic `validate` solves goals of the form `is_valid Γ`. It is based on the following principles:
 
- (Γ₁ ∙ Γ₂ ∙ Γ₃) is valid if and only if all of (Γ₁ ∙ Γ₂), (Γ₁ ∙ Γ₃), and (Γ₂ ∙
  Γ₃) are valid.
- ⊤ is valid
- the singleton context (x,a) is valid
- for two singletons (x,a) and (y,b), the context `singleton x a ∙ singleton y
  b` is valid if and only if `x <> y`.


We give the following instantiation of the `TypingContext` type class:
  - `SetContext.v`: Contexts are lists quotiented by permutations of the list.
