Require Import Monad.
Require Import Monoid.

(*
Class TypingCtx_Laws X A Ctx `{PCM_Ctx : PCM_Laws Ctx} :=
  { singleton : X -> A -> Ctx
  ; Ctx_rect : forall (P : Ctx -> Type)
                      (P_bot : P ⊥)
                      (P_top : P ⊤)
                      (P_singleton : forall x a, P (singleton x a))
                      (P_merge : forall Γ1 Γ2, P Γ1 -> P Γ2 -> P (Γ1 ∙ Γ2))
                      (Γ : Ctx), P Γ
  }
  .*)

Class TypingContext (X A Ctx : Type) :=
  { singleton : X -> A -> Ctx
  ; validity : Ctx -> bool
(*  ; in_dom : X -> Ctx -> bool*)
  }.

(*
Infix "XOR" := xorb (at level 30) : bool_scope.
Infix "∈?" := in_dom (at level 25).
Notation "x ∈ Γ" := (x ∈? Γ = true) (at level 50).
Notation "x ∉ Γ" := (x ∈? Γ = false) (at level 50).
Notation "x ∉? Γ" := (negb (x ∈? Γ)) (at level 25).

*)
Open Scope bool_scope.

Class DecidablePaths X := {decPaths : forall (x y : X), {x = y} + {x <> y}}.


  Definition bdec {X} `{DecidablePaths X} (x y : X) : bool :=
    if decPaths x y then true else false.
  Infix "=?" := bdec (at level 25).
  Notation "x <>? y" := (negb (x =? y)) (at level 25).

Section DecidablePaths.
  Context X `{DecidablePaths X}.

  Lemma bdec_eq : forall x y, x =? y = true <-> x = y.
  Proof.
    intros.
    unfold bdec. 
    destruct (decPaths x y) eqn:decX.
    - split; auto.
    - split; auto. intros. absurd (false = true); auto.
  Qed.

  Lemma bdec_neq : forall x y, x <>? y = true <-> x <> y.
  Proof.
    intros.
    unfold bdec.
    destruct (decPaths x y) eqn:decX.
    - split; intros; auto. inversion H0. 
    - split; auto.
  Qed.

  Lemma bdec_eq' : forall x, x =? x = true.
  Proof.
    intros x. apply bdec_eq. auto.
  Qed.

End DecidablePaths.

Class TypingContext_Laws X A Ctx `{DecidablePaths X} 
                                 `{PCM_Ctx : PCM_Laws Ctx} 
                                 `{TypingContext X A Ctx} :=
  { validity3 : forall Γ1 Γ2 Γ3, 
    validity (Γ1 ∙ Γ2 ∙ Γ3) =  validity (Γ1 ∙ Γ2) 
                            && validity (Γ1 ∙ Γ3) 
                            && validity (Γ2 ∙ Γ3)
  ; validity_reflection : forall Γ, validity Γ = false <-> Γ = ⊥
  ; validity_singleton : forall x a, validity (singleton x a) = true
  ; validity_top : validity ⊤ = true
  ; validity_singleton_merge : forall x y a b, 
    validity (singleton x a ∙ singleton y b) = (x <>? y)
  }.

Section TypingContexts.

Context X A Ctx `{TypingContext_Laws X A Ctx}.

Definition is_valid Γ := (validity Γ = true). 

Lemma is_valid3 : forall Γ1 Γ2 Γ3, 
    is_valid (Γ1 ∙ Γ2 ∙ Γ3) <->  is_valid (Γ1 ∙ Γ2) 
                                 /\ is_valid (Γ1 ∙ Γ3) 
                                 /\ is_valid (Γ2 ∙ Γ3).
Proof.
  unfold is_valid. intros.
  rewrite validity3. split; [intros eq | intros [eq1 [eq2 eq3] ] ].
  - destruct (validity (Γ1 ∙ Γ2)), (validity (Γ1 ∙ Γ3)), (validity (Γ2 ∙ Γ3)); auto.
  - rewrite eq1, eq2, eq3. auto.
Defined.

Lemma is_valid3_forward : forall Γ1 Γ2 Γ3,
      is_valid (Γ1 ∙ Γ2) ->
      is_valid (Γ1 ∙ Γ3) ->
      is_valid (Γ2 ∙ Γ3) ->
      is_valid (Γ1 ∙ Γ2 ∙ Γ3).
Proof. intros. apply is_valid3. auto. Qed.

Definition validity_reflection_true : forall Γ, validity Γ = true <-> Γ <> ⊥.
Proof.
  intros Γ. split; intros.
  - intros eq0. apply validity_reflection in eq0. rewrite eq0 in *. 
    absurd (false = true); auto.
  - destruct (validity Γ) eqn:v_Γ; auto.
    apply validity_reflection in v_Γ. contradiction.
Qed.
Lemma singleton_is_valid : forall x a, is_valid (singleton x a). 
Proof.
  apply validity_singleton.
Defined.

Lemma top_is_valid : is_valid ⊤.
Proof.
  apply validity_top.
Defined.
Lemma top_not_bottom : ⊤ <> ⊥.
Proof. apply validity_reflection_true. apply validity_top. Qed.

Lemma singleton_merge_is_valid : forall x y a b, 
    is_valid (singleton x a ∙ singleton y b) <-> (x <> y).
Proof.
  intros. unfold is_valid.
  rewrite validity_singleton_merge.
  split; apply bdec_neq.
Qed.

Lemma singleton_merge_invalid : forall x a b,
    ~ is_valid (singleton x a ∙ singleton x b).
Proof.
  intros. unfold is_valid.
  rewrite validity_singleton_merge. 
  rewrite bdec_eq'. simpl. auto.
Qed.

End TypingContexts.
About is_valid.
Arguments is_valid {X A Ctx TypingContext} : rename.


(***************************************************)
(* Tactics to solve goals of the form "is_valid Γ" *)
(***************************************************)

(* This is the naive tactic, but instead of working top down, we want to be a little smarter by working bottom up *)
Ltac validate_dumb :=
  repeat match goal with
  | [ H : is_valid ?Γ |- is_valid ?Γ ]              => exact H
  | [ |- is_valid ⊤ ]                               => apply top_is_valid
  | [ |- is_valid (singleton _ _) ]                 => apply singleton_is_valid
  | [ |- is_valid (singleton _ _ ∙ singleton _ _) ] => eapply singleton_merge_is_valid; auto
  | [ |- is_valid (_ ∙ _ ∙ _) ]                     => eapply is_valid3; auto
  | [ |- _ /\ _]                                    => split
  end.

Ltac introduce_valid_singletons :=
  repeat match goal with
  | [ |- context[singleton ?x ?a] ] => 
    assert (is_valid (singleton x a)) 
    by apply (@singleton_is_valid _ _ _ _ _ _ _ _);
    let Γ := fresh "Γ" in
    remember (singleton x a) as Γ (* so that we don't match this x again *)
  end; subst.

Ltac introduce_valid_term Γ :=
  match Γ with
  | _               => match goal with
                       [ H : is_valid Γ |- _ ] => idtac
                       end
  | ?Γ1 ∙ ?Γ2 ∙ ?Γ3 => let Γ12 := constr:(Γ1 ∙ Γ2) in
                       let Γ13 := constr:(Γ1 ∙ Γ3) in
                       let Γ23 := constr:(Γ2 ∙ Γ3) in
                       introduce_valid_term Γ12;
                       introduce_valid_term Γ13;
                       introduce_valid_term Γ23;
                       assert (is_valid Γ) by validate_dumb;
                       let Γ' := fresh "Γ" in
                       remember Γ as Γ'
  | _               => assert (is_valid Γ) by validate_dumb;
                       let Γ' := fresh "Γ" in
                       remember Γ as Γ'
  end; subst.

Ltac validate :=
  repeat rewrite M_assoc;
  match goal with
  | [ |- is_valid ?Γ ] => introduce_valid_term Γ
  end; auto.


Section Tests.

Context X A Ctx `{TypingContext_Laws X A Ctx}.

Lemma test3 : forall x y z a b c, x <> y -> y <> z -> x <> z ->
             is_valid (singleton x a ∙ singleton y b ∙ singleton z c).
Proof.
  intros. validate. 
Qed.


Lemma test4 : forall x y z w a b c d, x <> y -> y <> z -> x <> z -> x <> w -> y <> w -> z <> w ->
             is_valid (singleton x a ∙ singleton y b ∙ singleton z c ∙ singleton w d).
Proof.
  intros. validate. 
Qed.

End Tests.


(* In the end, solve goals of this form *)
(* The unicode symbol is \uplus *)
Notation "Γ1 ⊎ Γ2 == Γ" := (Γ = Γ1 ∙ Γ2 /\ is_valid Γ) (at level 75).

Ltac solve_ctx := 
  match goal with
  | [ |- _ /\ _ ] => split
  | [ |- is_valid ?Γ ] => validate
  | [ |- _ = _ ] => monoid
  end.
