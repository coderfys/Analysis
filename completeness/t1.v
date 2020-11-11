(***************************************************************************)
(*   This is part of FA_Completeness, it is distributed under the terms    *)
(*           of the GNU Lesser General Public License version 3            *)
(*                (see file LICENSE for more details)                      *)
(*                                                                         *)
(*           Copyright 2020-2022: Yaoshun Fu and Wensheng Yu.              *)
(***************************************************************************)

Require Export R_sup.
Require Import DFT.

Definition supremum y A := 
  Boundup_Ens y A /\ ∀ z, Boundup_Ens z A -> y ≦ z.
Definition infimum y A := 
  Bounddown_Ens y A /\ ∀ z, Bounddown_Ens z A -> z ≦ y.

Corollary Cor_supremum : ∀ s S, supremum s S ->
  ∀ ε, ε > O -> ∃ x, x ∈ S /\ (s - ε) < x.
Proof.
  intros; destruct H; Absurd.
  assert (Boundup_Ens (s - ε) S).
  { red; intros. destruct (Co_T167 x (s - ε)); auto. elim H2; eauto. }
  apply H1 in H3. apply LePl_R with (z:=ε) in H3; Simpl_Rin H3.
  destruct (@Pl_R s ε). LEGR H3 (H4 H0).
Qed.

Corollary Cor_infimum : ∀ s S, infimum s S -> 
  ∀ ε, ε > O -> ∃ x, x ∈ S /\ x < (s + ε).
Proof.
  intros; destruct H; Absurd.
  assert (Bounddown_Ens (s + ε) S).
  { red; intros. destruct (Co_T167 (s + ε) x); auto. elim H2; eauto. }
  apply H1 in H3. destruct (@Pl_R s ε). LEGR H3 (H4 H0).
Qed.

Theorem SupremumT : ∀ R, No_Empty R -> 
  (∃ x, Boundup_Ens x R) -> ∃ y, supremum y R.
Proof.
  intros; destruct H0 as [x H0], 
  (classic (∃ x, EnsMax x R)) as [H1 | H1].
  - destruct H1 as [Max [H1 H2]].
    exists Max; red; intros; split; auto.
  - set (S:= /{ z | Boundup_Ens z R /});
    set (S':= /{ w | ~ w ∈ S /}). assert (∃ y, Split S' S y).
    { apply DedekindCut; red; intros.
      - destruct (classic (Ξ ∈ S)); auto. left; constructor; auto.
      - red in H; destruct H as [r H]. exists r; constructor; intro.
        destruct H2; apply H1. exists r; red; auto.
      - exists x; constructor; auto.
      - destruct H2, H3, (Theorem167 Ξ Γ) as [H4 | [H4 | H4]]; auto.
        + elim H2; constructor; rewrite H4; auto.
        + elim H2; constructor; red in H3|-*; intros.
          apply H3 in H5; left; eapply Theorem172; eauto. }
    destruct H2 as [y [H2 H3]].
    exists y; red; intros; split; red; intros; try red.
    + destruct (Theorem167 x0 y) as [H5 | [H5 | H5]]; auto.
      apply H3 in H5; destruct H5; elim H1.
      exists x0; red; auto.
    + destruct (Theorem167 y z) as [H5 | [H5 | H5]]; auto.
      apply H2 in H5; destruct H5; elim H5; constructor; auto.
Qed.

Theorem InfimumT : ∀ R, No_Empty R -> 
  (∃ x, Bounddown_Ens x R) -> ∃ y, infimum y R.
Proof.
  intros; destruct H0 as [x H0].
  set (R' := /{ r | (- r) ∈ R /}).
  assert (∃ y, supremum y R').
  { apply SupremumT.
    - destruct H; red. exists (-x0); constructor; Simpl_R.
    - exists (-x); red; intros; destruct H1. apply LEminus; Simpl_R. }
  destruct H1 as [y [H1]].
  exists (-y); split; try red; intros.
  - apply LEminus; Simpl_R. apply H1; constructor; Simpl_R.
  - apply LEminus; Simpl_R. apply H2; red; intros; destruct H4.
    apply LEminus; Simpl_R.
Qed.
