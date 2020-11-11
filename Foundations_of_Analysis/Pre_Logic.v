(***************************************************************************)
(*   This is part of FA_Landau, it is distributed under the terms of the   *)
(*             GNU Lesser General Public License version 3                 *)
(*                (see file LICENSE for more details)                      *)
(*                                                                         *)
(*           Copyright 2020-2022: Yaoshun Fu and Wensheng Yu.              *)
(***************************************************************************)

Notation "∀ x .. y , P" := (forall x, .. (forall y, P) ..)
  (at level 200, x binder, y binder, right associativity,
  format "'[ ' '[ ' ∀ x .. y ']' , '/' P ']'") : type_scope.

Notation "∃ x .. y , P" := (exists x, .. (exists y, P) ..)
  (at level 200, x binder, y binder, right associativity,
  format "'[ ' '[ ' ∃ x .. y ']' , '/' P ']'") : type_scope.

Notation "'λ' x .. y , t" := (fun x => .. (fun y => t) ..)
  (at level 200, x binder, y binder, right associativity,
  format "'[ ' '[ ' 'λ' x .. y ']' , '/' t ']'").

Section logic.

Axiom classicT : ∀ P, {P} + {~P}.

Proposition classic : ∀ P, P \/ ~P.
Proof.
  intros; destruct (classicT P); auto. 
Qed.

Proposition property_not : ∀ P Q,
  (~(P /\ Q) <-> (~P) \/ (~Q)) /\ (~(P \/ Q) <-> (~P) /\ (~Q)).
Proof.
  intros; destruct (classic P); tauto.
Qed.

Proposition property_not' : ∀ P, (~ (~ P) <-> P).
Proof.
  intros; destruct (classic P); tauto.
Qed.

Proposition peirce : ∀ P, (~ P -> P) -> P.
Proof.
  intros; destruct (classic P); auto.
Qed.

Proposition inp : ∀ (P Q :Prop), (P -> Q) -> (~ Q -> ~ P).
Proof.
  intros; intro; auto.
Qed.

Proposition not_all_not_ex : ∀ {U} (P :U -> Prop),
  ~ (∀ n, ~ P n) ->  ∃ n, P n.
Proof.
  intros; apply property_not'; intro.
  apply H; intros n H1; apply H0; eauto.
Qed.

Proposition ex_not_all_not : ∀ {U} (P :U -> Prop),
  (∃ n, P n) -> ~ (∀ n, ~ P n).
Proof.
  intros; intro. destruct H. eapply H0; eauto.
Qed.

Proposition not_all_ex_not : ∀ {U} (P :U -> Prop),
  ~ (∀ n, P n) -> ∃ n, ~ P n.
Proof.
  intros; apply not_all_not_ex; intro.
  apply H; intro n; apply property_not'; auto.
Qed.

Proposition ex_not_ex_all : ∀ {U} (P :U -> Prop),
  (∃ n, ~ P n) ->  ~ (∀ n, P n).
Proof.
  intros; intro. destruct H. apply H; auto.
Qed.

Proposition not_ex_all_not : ∀ {U} (P :U -> Prop),
  ~ (∃ n, P n) -> ∀ n, ~ P n.
Proof.
  intros; intro; elim H; eauto.
Qed.

Proposition all_not_not_ex : ∀ {U} (P :U -> Prop),
  (∀ n, ~ P n) -> ~ (∃ n, P n).
Proof.
  intros; intro; destruct H0; eapply H; eauto.
Qed.

Proposition not_ex_and : ∀ {U} (P Q :U -> Prop), 
  ~ (∃ n, P n /\ Q n) -> ∀ n, P n -> ~ Q n.
Proof.
  intros; intro; elim H; eauto.
Qed.

Proposition all_imp_not : ∀ {U} (P Q :U -> Prop),
  (∀ n, P n -> ~ Q n) -> ~ (∃ n, P n /\ Q n).
Proof.
  intros; intro. destruct H0, H0. eapply H; eauto.
Qed.

End logic.

Ltac Absurd := apply peirce; intros.

Axiom prop_ext : ∀ {P Q:Prop}, P <-> Q -> P = Q.

Lemma proof_irr : ∀ {P :Prop} (p q :P), p = q.
Proof.
  intros. cut (P=True); intros.
  - subst P; destruct p, q; auto.
  - apply prop_ext; split; auto.
Qed.

Axiom fun_ext : ∀ T1 T2 (P Q :T1 -> T2), 
  (∀ m, P m = Q m) -> P = Q.
