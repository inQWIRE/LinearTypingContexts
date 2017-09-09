This repository contains a framework for reasoning about linear typing contexts
in Coq. The file `NCM.v` describes the algebraic structure of typing contexts.
This is characterized by the following parts.

- A type of typing contexts "A"
- An empty context, written "1 : A"
- A context merge operation, written "Γ1 · Γ2"
- To account for the fact that merge is partial, an undefined context "0 : A"
- A subset "B ⊂ A" of non-empty contexts

These components satisfy the following properties:
- (A,1,·) forms a commutative monoid
- 0 absorbes all elements of A, so a · 0 = 0
- all non-empty contexts are nilpotent: b ∈ B implies b · b = 0

The file `NCM.v` gives these properties, which we call *nilpotent commutative
monoids* as a type class. We define proof tactics to solve goals of the form "Γ1
= Γ2", including when one of the contexts are undefined. The highest-level
tactic is `reification`.

TODO: rename tactic

TODO: goals of the form Γ <> 0.

We give a few instantiation of the NCM type class:
  - `IndexContext.v`: Contexts are `list (option T)` where variables are natural
    numbers that index into a list
  - `ListContext.v`: Contexts are `list (nat * T)` where variables of type
    `nat` (could be any ordered type) and are sorted by the variable, so merge
    is deterministic. (TODO: fill in undefineds in this file)
