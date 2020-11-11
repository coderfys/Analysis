(***************************************************************************)
(*   This is part of FA_Landau, it is distributed under the terms of the   *)
(*             GNU Lesser General Public License version 3                 *)
(*                (see file LICENSE for more details)                      *)
(*                                                                         *)
(*           Copyright 2020-2022: Yaoshun Fu and Wensheng Yu.              *)
(***************************************************************************)

Require Export Pre_Logic.

Section Ensemble.

Set Implicit Arguments.

Variable U :Type.

Definition Ensemble := U -> Prop.

Definition In x (A :Ensemble) : Prop := A x.

Definition No_Empty (A :Ensemble) := ∃ x, In x A.

End Ensemble.

Notation "x ∈ A" := (In x A) (at level 10).

Inductive Ensemble_P {X :Type} (P :X -> Prop) x : Prop :=
  | intro_Ensemble_P : P x -> x ∈ (Ensemble_P P).

Notation " /{ x | P /}" := (Ensemble_P (λ x, P)) (x ident).

Section EnsembleBasic.

Set Implicit Arguments.

Variable (U :Type) (A B :Ensemble U) (cA :Ensemble (Ensemble U)).

Definition Union := /{ x | x ∈ A \/ x ∈ B /}.

Definition Intersection := /{ x | x ∈ A /\ x ∈ B /}.

Definition EleUnion := /{ a | ∃ A, A ∈ cA /\ a ∈ A /}.

Definition EleIntersection := /{ a | ∀ A, A ∈ cA -> a ∈ A /}.

Definition Included := ∀ x, x ∈ A -> x ∈ B.

Definition Same_Ensemble := ∀ x, x ∈ A <-> x ∈ B.

End EnsembleBasic.

Notation "A ∪ B" := (Union A B) (at level 60, right associativity).
Notation "A ∩ B" := (Intersection A B) (at level 60, right associativity).
Notation "∪ cA" := (EleUnion cA) (at level 66).
Notation "∩ cA" := (EleIntersection cA) (at level 66).
Notation "A ⊂ B" := (Included A B) (at level 70).

Corollary ens_ext : ∀ {T :Type} {A B :Ensemble T}, 
  Same_Ensemble A B -> A = B.
Proof.
  intros; apply fun_ext; intros; apply prop_ext, H.
Qed.

Section Map.

Set Implicit Arguments.

Variable U V :Type.
Definition Relation := U -> V -> Prop.
Variable (A :Ensemble U) (B :Ensemble V) (f :Relation).

Definition Rel := 
  (∀ x y, f x y -> x ∈ A) /\ (∀ x y, f x y -> y ∈ B).

Definition to_at_most_one_output := ∀ x y z, f x y -> f x z -> y = z.

Definition to_at_least_one_output := ∀ x, x ∈ A -> ∃ y, f x y.

Definition from_at_most_one_input := ∀ x y z, f x z -> f y z -> x = y.

Definition from_at_least_one_input := ∀ y, y ∈ B -> ∃ x, f x y.

Definition Injection := to_at_most_one_output /\ 
  to_at_least_one_output /\ from_at_most_one_input /\ Rel.

Definition Surjection := to_at_most_one_output /\ 
  to_at_least_one_output /\ from_at_least_one_input /\ Rel.

Definition Bijection := to_at_most_one_output /\ 
  to_at_least_one_output /\ from_at_most_one_input /\ 
  from_at_least_one_input /\ Rel.

End Map.
