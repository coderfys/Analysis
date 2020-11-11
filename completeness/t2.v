(***************************************************************************)
(*   This is part of FA_Completeness, it is distributed under the terms    *)
(*           of the GNU Lesser General Public License version 3            *)
(*                (see file LICENSE for more details)                      *)
(*                                                                         *)
(*           Copyright 2020-2022: Yaoshun Fu and Wensheng Yu.              *)
(***************************************************************************)

Require Import t1.
Require Export Seq.

Theorem MCTup : ∀ a y,
  Increase a -> Boundup_Seq y a -> ∃ ξ, Limit a ξ.
Proof.
  intros; red in H, H0.
  set (J:= /{ r | ∃ t, r = (a t) /}).
  assert (exists p, supremum p J).
  { apply SupremumT.
    - red; exists (a 1); constructor; eauto.
    - exists y; red; intros. destruct H1, H1; rewrite H1; auto. }
  destruct H1 as [z H1]; pose proof H1; destruct H1.
  exists z; red; intros. eapply Cor_supremum in H2; eauto.
  destruct H2 as [x [[[n H2]]]]; subst x. exists n; intros.
  apply -> Ab1; split; apply Theorem188_1 with (Θ:=z); Simpl_R.
  - rewrite Theorem175; unfold Minus_R in H4. eapply Theorem172; eauto.
  - assert (a n0 ∈ J). { constructor; eauto. }
    apply H1 in H6; eapply Theorem172.
    left; split; eauto. rewrite Theorem175; apply Pl_R; auto.
Qed.

Theorem MCTdown : ∀ a y,
  Decrease a -> Bounddown_Seq y a -> ∃ ξ, Limit a ξ.
Proof.
  intros; red in H, H0.
  assert (∃ ξ, Limit (minus_Seq a) ξ).
  { apply (MCTup _ (-y)); red; intros; 
    unfold minus_Seq; apply -> LEminus; auto. }
  destruct H1 as [ξ H1]. exists (-ξ); red; intros.
  apply H1 in H2; destruct H2 as [N H2].
  exists N; intros; unfold minus_Seq in H2.
  unfold Minus_R; rewrite <- Theorem178, Theorem180; Simpl_R.
Qed.







