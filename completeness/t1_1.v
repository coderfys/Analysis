(***************************************************************************)
(*   This is part of FA_Completeness, it is distributed under the terms    *)
(*           of the GNU Lesser General Public License version 3            *)
(*                (see file LICENSE for more details)                      *)
(*                                                                         *)
(*           Copyright 2020-2022: Yaoshun Fu and Wensheng Yu.              *)
(***************************************************************************)

Require Export R_sup.
Require Import t1.

Section Dedekind.

Variable Fst Snd :Ensemble Real.

Definition R_Divide := ∀ Ξ, Ξ ∈ Fst \/ Ξ ∈ Snd.

Definition ILT_FS := ∀ Ξ Γ, Ξ ∈ Fst -> Γ ∈ Snd -> Ξ < Γ.

Definition Split Ξ := 
  (∀ Γ, Γ < Ξ -> Γ ∈ Fst) /\ (∀ Γ, Γ > Ξ -> Γ ∈ Snd).

End Dedekind.

Theorem DedekindCut : ∀ Fst Snd, R_Divide Fst Snd -> 
  No_Empty Fst -> No_Empty Snd -> ILT_FS Fst Snd ->
  (∃ Ξ, Split Fst Snd Ξ).
Proof.
  intros; assert (∃ x, Boundup_Ens x Fst).
  { destruct H1; exists x; red; intros. left; apply H2; auto. }
  apply SupremumT in H0; auto. destruct H0 as [Ξ  [H0]].
  exists Ξ; split; intros.
  - destruct H with Γ; auto. assert (Boundup_Ens Γ Fst).
    { red; intros; left; apply H2; auto. }
    apply H4 in H7; LEGR H7 H5.
  - destruct H with Γ; auto. apply H0 in H6; LEGR H6 H5.
Qed.

Theorem DedekindCut_Unique : ∀ Fst Snd, R_Divide Fst Snd ->
  No_Empty Fst -> No_Empty Snd -> ILT_FS Fst Snd ->
  ∀ Z1 Z2, Split Fst Snd Z1 -> Split Fst Snd Z2 -> Z1 = Z2.
Proof.
  assert (∀ Fst Snd, R_Divide Fst Snd -> No_Empty Fst 
    -> No_Empty Snd -> ILT_FS Fst Snd 
    -> ∀ Ξ1 Ξ2, Split Fst Snd Ξ1 -> Split Fst Snd Ξ2 -> ~ Ξ1<Ξ2).
  { intros; intro; red in H, H0, H1, H2, H3, H4; destruct H3, H4.
    pose proof (Mid_P' _ _ H5); pose proof (Mid_P _ _ H5).
    apply H6 in H8; apply H4 in H9. intros;
    pose proof (H2 _ _ H9 H8). apply OrdR1 in H10; tauto. }
  intros; destruct (Theorem167 Z1 Z2) as [H6 | [H6 | H6]]; auto;
  eapply H in H6; eauto; tauto.
Qed.
