(***************************************************************************)
(*   This is part of FA_Completeness, it is distributed under the terms    *)
(*           of the GNU Lesser General Public License version 3            *)
(*                (see file LICENSE for more details)                      *)
(*                                                                         *)
(*           Copyright 2020-2022: Yaoshun Fu and Wensheng Yu.              *)
(***************************************************************************)

Require Import t2.
Require Export Seq.

Definition NestedIntervals a b := Increase a /\ 
  Decrease b /\ ILT_Seq a b /\ Limit (Minus_Seq b a) O.

Theorem NITex : ∀ a b, NestedIntervals a b -> 
  ∃ ξ, (∀ n, a n ≦ ξ /\ ξ ≦ b n) /\ Limit a ξ /\ Limit b ξ.
Proof.
  intros; red in H; destruct H, H0, H1.
  assert (Boundup_Seq (b 1) a).
  { red; intros. red in H, H0, H1; destruct (Theorem24 n).
    - pose proof H3; apply H in H3. eapply Theorem173; eauto.
    - rewrite H3; auto. }
  destruct (MCTup _ _ H H3) as [ξ H4].
  assert (Limit b ξ).
  { rewrite (SeqCon1 a b), <- Theorem175''; apply SeqLimPlus; auto. }
  exists ξ; repeat split; auto.
  - apply Increase_limitP; auto. - apply Decrease_limitP; auto.
Qed.

Theorem NITuni : ∀ a b, NestedIntervals a b -> ∀ ξ1 ξ2,
  (∀ n, a n ≦ ξ1 /\ ξ1 ≦ b n) /\ Limit a ξ1 /\ Limit b ξ1 ->
  (∀ n, a n ≦ ξ2 /\ ξ2 ≦ b n) /\ Limit a ξ2 /\ Limit b ξ2 -> ξ1 = ξ2.
Proof.
  intros; destruct H0 as [_ [H0 _]], H1 as [_ [H1 _]].
  eapply LimUni; eauto.
Qed.

Corollary Cor_NIT: ∀ a b, NestedIntervals a b -> 
  ∃ ξ, (∀ N, a N ≦ ξ /\ ξ ≦ b N) /\ 
  (∀ ε, ε > O -> ∃ N, ∀ n, (IGT_N n N) -> 
  [(a n) | (b n)] ⊂ (ξ|-ε)).
Proof.
  intros. apply NITex in H; destruct H as [ξ H], H, H0.
  exists ξ; split; intros; auto.
  destruct H0 with ε as [N1 H3]; auto.
  destruct H1 with ε as [N2 H4]; auto.
  exists (Plus_N N1 N2); intros.
  pose proof (H3 _ (Theorem15 _ _ _ (Theorem18 N1 N2) H5)).
  pose proof (Theorem18 N2 N1); rewrite Theorem6 in H7.
  pose proof (H4 _ (Theorem15 _ _ _ H7 H5)).
  red; intros; destruct H9, H9; constructor; split.
  - apply Ab1 in H6; destruct H6.
    apply Theorem172 with (Γ:=a n); right; split; auto.
    apply Theorem188_1' with (Θ:=ξ) in H6; Simpl_Rin H6.
    rewrite Theorem175 in H6; auto.
  - apply Ab1 in H8; destruct H8.
    apply Theorem172 with (Γ:=b n); left; split; auto.
    apply Theorem188_1' with (Θ:=ξ) in H11; Simpl_Rin H11.
    rewrite Theorem175; auto.
Qed.





























