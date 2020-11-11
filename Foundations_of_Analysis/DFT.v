(***************************************************************************)
(*   This is part of FA_Landau, it is distributed under the terms of the   *)
(*             GNU Lesser General Public License version 3                 *)
(*                (see file LICENSE for more details)                      *)
(*                                                                         *)
(*           Copyright 2020-2022: Yaoshun Fu and Wensheng Yu.              *)
(***************************************************************************)

(* REALS *)

(* SECTION V Dedekind's Fundamental Theorem *)

Require Export reals.

Section Dedekind.

Variable Fst Snd :Ensemble Real.

Definition R_Divide := ∀ Ξ, Ξ ∈ Fst \/ Ξ ∈ Snd.

Definition ILT_FS := ∀ Ξ Γ, Ξ ∈ Fst -> Γ ∈ Snd -> Ξ < Γ.

Definition Split Ξ :=
  (∀ Γ, Γ < Ξ -> Γ ∈ Fst) /\ (∀ Γ, Γ > Ξ -> Γ ∈ Snd).

Corollary Split_Pa : ∀ Ξ1 Ξ2, 
  R_Divide -> ILT_FS -> Ξ1 ∈ Fst -> Ξ2 < Ξ1 -> Ξ2 ∈ Fst.
Proof.
  intros; destruct H with Ξ2; auto; LGR H2 (H0 _ _ H1 H3).
Qed.

Corollary Split_Pb : ∀ Ξ1 Ξ2, 
  R_Divide -> ILT_FS -> Ξ1 ∈ Snd -> Ξ1 < Ξ2 -> Ξ2 ∈ Snd.
Proof.
  intros;  destruct H with Ξ2; auto; LGR H2 (H0 _ _ H3 H1).
Qed.

Corollary Split_Pc : ∀ Ξ,
  R_Divide -> ILT_FS -> Ξ ∈ Fst -> Ξ ∈ Snd -> False.
Proof.
  intros; pose proof (H0 _ _ H1 H2); apply OrdR1 in H3; auto.
Qed.

End Dedekind.

Theorem DedekindCut_Unique : ∀ Fst Snd, R_Divide Fst Snd ->
  No_Empty Fst -> No_Empty Snd -> ILT_FS Fst Snd ->
  ∀ Z1 Z2, Split Fst Snd Z1 -> Split Fst Snd Z2 -> Z1 = Z2.
Proof.
  assert (∀ Fst Snd, R_Divide Fst Snd -> No_Empty Fst -> 
    No_Empty Snd -> ILT_FS Fst Snd -> ∀ Ξ1 Ξ2, Split Fst Snd Ξ1 ->
    Split Fst Snd Ξ2 -> ~ Ξ1 < Ξ2).
  { intros; intro; red in H, H0, H1, H2, H3, H4; destruct H3, H4.
    assert (neq_zero 2). { reflexivity. }
    assert (Ξ1 < ((Ξ1 + Ξ2) / (1 + 1)) H8).
    { apply Theorem203_1' with (Θ:=(1 + 1)); Simpl_R.
      rewrite Theorem201; Simpl_R.
      rewrite (Theorem175 Ξ1 Ξ2); apply Theorem188_1'; auto. }
    assert (((Ξ1 + Ξ2) / (1 + 1)) H8 < Ξ2).
    { apply Theorem203_1' with (Θ:=(1 + 1)); Simpl_R.
      rewrite Theorem201; Simpl_R; apply Theorem188_1'; auto. }
    apply H6 in H9; apply H4 in H10.
    eapply Split_Pc in H9; eauto. }
  intros; destruct (Theorem167 Z1 Z2) as [H6 | [H6 | H6]]; auto;
  eapply H in H6; eauto; tauto.
Qed.

Definition ded_C Fst :=
  /{X|(P X*)∈Fst /\ (∃ Ξ, Ξ∈Fst /\ (P X*)<Ξ)/}.

Lemma Lemma_DFTa : ∀ Fst Snd, R_Divide Fst Snd ->
  No_Empty Snd -> ILT_FS Fst Snd -> (∃ a, P a ∈ Fst) ->
  Cut_p1 (ded_C Fst) /\ Cut_p2 (ded_C Fst) /\ Cut_p3 (ded_C Fst).
Proof.
  intros; destruct H2 as [ξ H2]; repeat split.
  - EC Z ξ H3; exists Z; constructor; split.
    + eapply Split_Pa; eauto; simpl; apply Theorem158_1; auto.
    + apply (cutp3 ξ) in H3; destruct H3 as  [X [H3 H4]].
      assert (Num_L X ξ); auto. apply Theorem158_1 in H5.
      apply Theorem82 in H4; exists (P X); split.
      * eapply Split_Pa; eauto.
      * simpl; apply Theorem154_3; auto.
  - destruct H0 as [Ξ H0], Ξ; pose proof (H1 _ _ H2 H0);
    simpl in H3; try tauto. ENC W c H4; apply Theorem158_2 in H4.
    exists W; intro; destruct H5, H5, H4.
    + assert ((P W) ∈ Snd).
      { eapply Split_Pb ; eauto; simpl; auto. }
      eapply Split_Pc; eauto.
    + rewrite <- (eq2 H4) in H0; eapply Split_Pc; eauto.
  - destruct H3, H3; eapply Split_Pa; eauto; simpl.
    apply Theorem154_3; auto.
  - destruct H3, H3; apply Theorem91 in H4.
    destruct H4 as [Z [H4 H6]]. exists (P Z); split.
    + eapply Split_Pa; eauto; simpl; apply Theorem154_3; auto.
    + simpl; apply Theorem154_3; auto.
  - red; intros; destruct H3, H3, H4 as [Ξ [H4 H5]], Ξ;
    simpl in H5; try tauto. apply Theorem159 in H5; destruct H5 as
      [Z [H5 H6]]. exists Z; split; try (constructor; split).
    * eapply Split_Pa; eauto.
    * exists (P c); split; auto.
    * apply Theorem83; apply Theorem154_3'; auto.
Qed.
 
Definition Ded_C Fst Snd (l1 :R_Divide Fst Snd) (l2 :No_Empty Snd)
  (l3 :ILT_FS Fst Snd) (l4 :∃ ξ, P ξ ∈ Fst) : Cut.
  apply mkcut with (ded_C Fst); eapply Lemma_DFTa; eauto.
Defined.

Definition Opp_En Fst := /{ Ξ | (-Ξ) ∈ Fst /}.

Lemma Lemma_DFTb : ∀ Fst Snd, R_Divide Fst Snd ->
  No_Empty Fst -> No_Empty Snd -> ILT_FS Fst Snd ->
  R_Divide (Opp_En Snd) (Opp_En Fst) /\ No_Empty (Opp_En Snd)
  /\ No_Empty (Opp_En Fst) /\  ILT_FS (Opp_En Snd) (Opp_En Fst).
Proof.
  repeat split; red in *; intros.
  - destruct H with (-Ξ); [right|left]; constructor; auto.
  - destruct H1 as [Ξ H1]; exists (-Ξ); constructor; Simpl_R.
  - destruct H0 as [Ξ H0]; exists (-Ξ); constructor; Simpl_R.
  - destruct H3, H4; eapply H2 in H3; eauto.
    apply Theorem183_1'; auto.
Qed.

Lemma Lemma_DFTc : ∀ Fst Snd, R_Divide Fst Snd -> No_Empty Fst ->
   No_Empty Snd -> ILT_FS Fst Snd ->
   (∃ ξ, (P ξ) ∈ Fst) -> (∃ Ξ, Split Fst Snd Ξ).
Proof.
  intros; set (ξ := (Ded_C Fst Snd H H1 H2 H3)).
  exists (P ξ); split; intros Γ H4.
  - elim H3; intros η H5. destruct H with Γ; auto.
    pose proof (H2 _ _ H5 H6). destruct Γ; simpl in H7; try tauto.
    simpl in H4; apply Theorem159 in H4.
    destruct H4 as [X [H4 H8]]. apply Theorem158_1 in H8.
    destruct H8, H8. apply (Split_Pa Fst Snd (P X) (P c)); auto.
  - destruct Γ; simpl in H4; try tauto. apply Theorem159 in H4;
    destruct H4 as [X [H4 H5]]. destruct H with (P c); auto.
    apply (Split_Pb Fst Snd (P X) (P c)); auto.
    assert (Num_U X ξ). { apply Theorem158_2; left; auto. }
    elim H7; constructor; split; eauto.
    apply (Split_Pa Fst Snd (P c) (P X)); auto.
Qed.

Theorem DedekindCut : ∀ Fst Snd, R_Divide Fst Snd -> No_Empty Fst
  -> No_Empty Snd -> ILT_FS Fst Snd -> (∃ Ξ, Split Fst Snd Ξ).
Proof.
  intros; destruct (classic (∃ ξ, (P ξ) ∈ Fst)) as [H3 |H3].
  - apply Lemma_DFTc; auto.
  - destruct (classic (O ∈ Fst)) as [H4 |H4].
    + exists O; red; split; intros Ξ H5.
      * destruct Ξ; inversion H5; destruct H with (N c); auto.
        elim (H2 _ _ H4 H6).
      * destruct Ξ; inversion H5; destruct H with (P c); auto.
        elim H3; eauto.
    + destruct (classic (~ (∃ ξ, (N ξ) ∈ Snd))) as [H5 |H5].
      * exists O; red; split; intros Ξ H6.
        { destruct Ξ; inversion H6; destruct H with (N c); auto;
          elim H5; eauto. }
        { destruct Ξ; inversion H6; destruct H with (P c); auto;
          elim H3; eauto. }
      * apply -> property_not' in H5.
        assert (∃ ξ, (P ξ) ∈ (Opp_En Snd)).
        { destruct H5 as [ξ H5]; exists ξ; constructor. auto. }
        destruct (Lemma_DFTb _ _ H H0 H1 H2), H8, H9.
        destruct (Lemma_DFTc _ _ H7 H8 H9 H10 H6) as [Ξ H11].
        destruct H11; exists (-Ξ); split; intros Γ H13.
        { apply Theorem183_1 in H13; rewrite Theorem177 in H13.
          apply H12 in H13; destruct H13;
          rewrite Theorem177 in H13; auto. }
        { apply Theorem183_1 in H13; rewrite Theorem177 in H13.
          apply H11 in H13; destruct H13;
          rewrite Theorem177 in H13; auto. }
Qed.
