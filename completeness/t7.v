(***************************************************************************)
(*   This is part of FA_Completeness, it is distributed under the terms    *)
(*           of the GNU Lesser General Public License version 3            *)
(*                (see file LICENSE for more details)                      *)
(*                                                                         *)
(*           Copyright 2020-2022: Yaoshun Fu and Wensheng Yu.              *)
(***************************************************************************)

Require Import t6.
Require Export Seq.

Definition CauchySeq (a :Seq) := ∀ ε, ε > O -> 
  ∃ N, ∀ m n, (IGT_N m N) -> (IGT_N n N) -> |(a m) - (a n)| < ε.

Inductive RelCauchy N (a :Seq) x y :Prop :=
  | RelCauchy_in : ILT_N x N -> y = |a x| -> RelCauchy N a x y.

Theorem CCT : ∀ a, (∃ ξ, Limit a ξ) <-> CauchySeq a.
Proof.
  split; try red; intros.
  - destruct H as [ξ H]; red in H. apply Pr_2a in H0.
    destruct (H _ H0) as [N H1]. exists N; intros.
    apply H1 in H2; apply H1 in H3.
    rewrite <- Theorem178, Theorem181 in H3.
    pose proof (Theorem189 H2 H3); Simpl_Rin H4.
    pose proof (Ab2 ((a m)- ξ) (ξ - (a n))).
    unfold Minus_R in H5; rewrite <- Theorem186 in H5; Simpl_Rin H5.
    eapply Theorem172; eauto.
  - destruct H with 1 as [N H0]; simpl; auto.
    assert (∀ n, IGT_N n N` -> |a n| < |a N`| + 1); intros.
    { pose proof (Theorem18 N 1); Simpl_Nin H2.
      eapply Theorem15 in H1; eauto.
      pose proof (H0 _ _ H1 H2); pose proof (Ab2' (a n) (a N`)).
      assert ((|a n| - |a N`|) < 1). { eapply Theorem172; left; eauto. }
      apply Theorem188_1' with (Θ:=|a N`|) in H5; Simpl_Rin H5.
      rewrite Theorem175; auto. }
    set (R:= /{ z| ∃ m, ILE_N m N` /\ z = |a m| /}).
    assert (fin R).
    { exists (N`)`, (RelCauchy (N`)` a); repeat split;
      try red; intros.
      - destruct H2, H3; subst y; auto.
      - destruct H2; exists (|a x|); constructor; auto.
      - destruct H2, H2, H2; exists x; constructor; auto.
        apply Theorem26'; auto.
      - destruct H2; auto.
      - destruct H2; apply Theorem26 in H2; eauto. }
    assert (No_Empty R).
    { red; exists (|a N`|); constructor; unfold ILE_N; eauto. }
    apply FinMax in H3; auto; destruct H3 as [M1 H3], H3.
    set (M := (R2max M1 (|a N`| + 1))).
    assert (∀ n, |a n| ≦ M); intros.
    { destruct (Theorem10 n N`) as [H5| [H5 |H5]].
       - assert (|a N`| ∈ R). { split; exists N`; split; auto; red; auto. }
         subst n; apply H4 in H6.
         eapply Theorem173; eauto; apply Pr_max2.
      - apply H1 in H5. pose proof (Pr_max3 M1 (|a N`| +1)).
        left; eapply Theorem172; eauto.
      - assert (|a n| ∈ R). 
        { constructor; exists n; split; try red; auto. }
        apply H4 in H6. eapply Theorem173; eauto; apply Pr_max2. }
    assert (Bounddown_Seq (-M) a).
    { red; intros. pose proof (H5 n); apply Ab1' in H6; tauto. }
    assert (Boundup_Seq M a).
    { red; intros. pose proof (H5 n); apply Ab1' in H7; tauto. }
    assert (M > - M).
    { assert (M > O).
      { pose proof (Pr_max3 M1 (|a N`| +1)).
        eapply Theorem172; right; split; eauto.
        destruct (a N`); simpl; auto. }
      destruct M; simpl; tauto. }
    destruct (SCT _ _ _ H8 H6 H7) as [a' H9].
    destruct H9, H9 as [s H9], H9, H10 as [ξ H10].
    exists ξ; red; intros. apply Pr_2a in H12.
    destruct (H _ H12) as [N1 H13], (H10 _ H12) as [N2 H14].
    exists (Plus_N N1 N2); intros.
    pose proof (Theorem18 N2 N1); rewrite Theorem6 in H16.
    apply (Theorem15 _ _ n) in H16; auto.
    apply H14 in H16; rewrite H11 in H16.
    pose proof (Theorem18 N1 N2).
    apply (Theorem15 _ _ n) in H17; auto.
    pose proof (SubSeq_P _ _ _ H9 H11 n).
    assert (IGT_N (s n) N1).
    { apply Theorem13 in H18. eapply Theorem16; eauto. }
    pose proof (H13 _ _ H17 H19).
    pose proof (Theorem189 H20 H16); Simpl_Rin H21.
    pose proof (Ab2 ((a n) - (a (s n))) ((a (s n)) - ξ)).
    unfold Minus_R at 2 in H22; rewrite <- Theorem186 in H22;
    Simpl_Rin H22. eapply Theorem172; eauto.
Qed.


















