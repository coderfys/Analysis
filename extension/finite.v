(***************************************************************************)
(*   This is part of FA_Landau, it is distributed under the terms of the   *)
(*             GNU Lesser General Public License version 3                 *)
(*                (see file LICENSE for more details)                      *)
(*                                                                         *)
(*           Copyright 2020-2022: Yaoshun Fu and Wensheng Yu.              *)
(***************************************************************************)

Require Export Nats.

Inductive Compose {U V W} (f :Relation U V) (g :Relation V W) x y :Prop :=
  | Com_intro: ∀ z, f x z -> g z y -> Compose f g x y.

Corollary comp : 
  ∀ {U V W A B C} {f :Relation U V} {g :Relation V W},
  Surjection A B f -> Surjection B C g -> Surjection A C (Compose f g).
Proof.
  intros; red; repeat split; intros; try red; intros.
  - destruct H1, H2.
    assert (z0 = z1). { eapply H; eauto. }
    subst z0; eapply H0; eauto.
  - apply H in H1; destruct H1; pose proof H1.
    apply H in H2; apply H0 in H2; destruct H2.
    exists x1; econstructor; eauto.
  - apply H0 in H1; destruct H0 as [_ [_ [_ [H0 _]]]], H1.
    pose proof H1; apply H0 in H1.
    apply H in H1; destruct H1. exists x0; econstructor; eauto.
  - destruct H1; eapply H; eauto.
  - destruct H1; eapply H0; eauto.
Qed.

Definition Fin_En x := /{ z | z < x /}.
Definition fin {U} (A :Ensemble U) := (∃ x f, Surjection (Fin_En x) A f).

Inductive RelE {U} (A :Ensemble U)(x :Nat) y :=
  | RelE_intro : y ∈ A -> RelE A x y.

Corollary Fin_Empty : ∀ {U} (A :Ensemble U), ~ No_Empty A -> fin A.
Proof.
  intros; exists 1,(RelE A); red; repeat split;
  try red; intros; try (destruct H0; elim H; red; eauto).
  - N1F H0.
  - destruct H; red; eauto.
Qed.

Inductive RelUn {U} p q (f g :Relation Nat U) x r :Prop :=
  | RelUn_intro : x < p -> f x r -> RelUn p q f g x r
  | RelUn_intro' : ∀ H :p ≦ x, x ≦ (p + q)
    -> g (((x + 1) - p) (Theorem26' H)) r -> RelUn p q f g x r.

Corollary Fin_Union : ∀ {U} {A B :Ensemble U}, 
  fin A -> fin B -> fin (A ∪ B).
Proof.
  intros; destruct H as [x [f1 H]], H0 as [y [f2 H0]].
  set (f3 := RelUn x y f1 f2); red. exists (((x + y) - 1) N1P), f3.
  red; repeat split; try red; intros.
  - destruct H1, H2; [|LEGN H2 H1|LEGN H1 H2|].
    * apply H with x0; auto.
    * rewrite (proof_irr H2 H1) in H6; eapply H0; eauto.
  - destruct H as [_ [H _]],  H0 as [_ [H0 _]], H1; red in H, H0.
    destruct (classic (x ≦ x0)) as  [H2 | H2].
    * apply Theorem26' in H2.
      destruct H0 with (Minus_N (x0 + 1) x H2); try constructor.
      + apply Theorem19_1 with (z:=1) in H1; Simpl_Nin H1.
        apply Theorem20_1 with (z:=x); Simpl_N.
        rewrite Theorem6; auto.
      + apply Theorem19_1 with (z:=1) in H1; Simpl_Nin H1.
        pose proof H2. apply Theorem26 in H4.
        rewrite (proof_irr H2 (Theorem26' H4)) in H3.
        exists x1; constructor 2 with H4; auto.
        left; eapply Theorem15; eauto. apply Nlt_S_.
    * apply property_not in H2; destruct H2.
      destruct (Theorem10 x x0) as [H4 | [H4 | H4]]; try tauto.
      destruct H with x0; try constructor; auto.
      exists x1; constructor; auto; red; auto.
  - destruct H1, H1, H as [_ [_ [H]]], H0 as [_ [_ [H0]]], H2, H3.
    * destruct H with y0; auto. exists x0; constructor; auto.
      apply H2 in H6; destruct H6; auto.
    * destruct H0 with y0; auto; destruct (H3 _ _ H6).
      assert (x ≦ ((Minus_N (x0 + x) 1 N1P))).
      { destruct x0.
        - right; apply Theorem20_2 with (z:=1); Simpl_N.
        - left; apply Theorem20_1 with (z:=1); Simpl_N.
          rewrite Theorem6; exists x0; Simpl_N. }
      exists ((Minus_N (x0 + x) 1 N1P)). econstructor 2 with H8.
      + left; apply Theorem20_1 with (z:=1); Simpl_N.
        apply Theorem19_1 with (z:=x) in H7.
        eapply Theorem15; eauto. rewrite Theorem6. apply Nlt_S_.
      + assert (x0 = 
          (Minus_N (Minus_N (x0 + x) 1 N1P + 1) x (Theorem26' H8))).
        { apply Theorem20_2 with (z:=x); Simpl_N. }
        { rewrite <- H9; auto. }
  - destruct H1; auto.
    * exists (Minus_N ((Minus_N x x0 H1) + y) 1 N1P).
      apply Theorem20_2 with (z:=1).
      rewrite Theorem5; Simpl_N.
      rewrite <- Theorem5,(Theorem6 x0 (Minus_N x x0 H1));Simpl_N.
    * destruct H0 as [_ [_ [_ [H0 _]]]]. apply H0 in H3. 
      destruct H3. apply Theorem19_1 with (z:=x) in H3.
      Simpl_Nin H3. rewrite <- NPl_1, Theorem6 in H3.
      exists (Minus_N (x + y) (x0 + 1) H3).
      apply Theorem20_2 with (z:=(x0 + 1)).
      rewrite Theorem5; Simpl_N.
      rewrite <- NPlS_, Theorem6; f_equal; Simpl_N.
  - destruct H1.
    * apply H in H2; auto. * apply H0 in H3; auto.
Qed.

Inductive RelAB {U V} A B v (f :Relation U V) x y :Prop :=
  | Como1_intro : x ∈ A -> f x y -> RelAB A B v f x y
  | Como1_intro' : ~ x ∈ A -> x ∈ B -> y = v -> RelAB A B v f x y.

Corollary Fin_EleUnion :  ∀ {U B}, fin B -> 
  (∀ b :Ensemble U, b ∈ B -> fin b) -> fin (∪ B).
Proof.
  intros; destruct H as [x [f H]].
  generalize dependent B; generalize dependent f;
  generalize dependent x; induction x; intros.
  - apply Fin_Empty; intro; destruct H1, H1, H1, H1.
    apply H in H1; destruct H1, H as [_ [_ [_ [H _]]]].
    apply H in H1; destruct H1. N1F H1.
  - rename H0 into H1; rename H into H0; rename IHx into H.
    destruct H0, H2, H3, H4; red in H0, H2, H3.
    destruct H2 with x as [b H6]. constructor; apply Nlt_S_.
    assert (∪ B = (∪ /{ z | z ∈ B /\ z <> b/}) ∪ b).
    { apply ens_ext; red; split; intros; destruct H7; constructor.
      - destruct H7, H7, (classic (x0 ∈ b)); auto.
        left; constructor. exists x1; split; auto.
        constructor; split; auto. intro; subst b; auto.
      - destruct H7; eauto. destruct H7, H7, H7, H7, H7; eauto. }
    rewrite H7; apply Fin_Union.
    + set (B':= /{ z | z ∈ B /\ z <> b /}).
      set (A:=/{ z | ∃ b', (b' ∈ B') /\ (f z b') /}).
      assert ((~ ∃ c, c ∈ B /\ c <> b) -> fin (EleUnion B')) as G.
      { intros. apply Fin_Empty; intro.
        destruct H9, H9, H9, H9, H9, H9. apply H8; eauto. }
      destruct (classic (∃ c, c ∈ B /\ c <> b)) as [H8 | H8];auto.
      destruct H8, H8. apply H with (RelAB A (Fin_En x) x0 f).
      red; repeat split; try red; intros. 
      { destruct H10, H11; try tauto.
        - eapply H0; eauto. - subst y z; auto. }
      { destruct (classic (x1 ∈ A)).
        - destruct H10, H2 with x1.
          + constructor; eapply Theorem15; eauto. apply Nlt_S_.
          + exists x2; constructor; auto.
        - exists x0; constructor 2; eauto. }
      { destruct H10, H10, H3 with y; auto. 
        exists x1; constructor; auto.
        constructor; exists y; split; auto. constructor; auto. }
      { destruct H10.
        - destruct H10, H10, H10, H10, H10.
          eapply H0 in H12; eauto; subst x2.
          pose proof H11; apply H4 in H11; destruct H11.
          apply Theorem26 in H11. destruct H11; auto.
          subst x1. elim H13; eapply H0; eauto.
        - destruct H11; auto. }
      { destruct H10;[eapply H5; eauto|subst y; auto]. }
      { subst y; destruct H10.
        - destruct H10,H10,H10,H10,H10. apply H13; eapply H0;eauto.
        - subst x0; auto. }
      { intros; destruct H10, H10; auto. }
  + apply H5 in H6; auto.
Qed.

Corollary Fin_Included : ∀ {U} (A B :Ensemble U), 
  A ⊂ B -> fin B -> fin A.
Proof.
  intros; red. pose proof (Fin_Empty A) as G.
  destruct (classic (No_Empty A)) as [H1 | H1]; try tauto.
  destruct H0 as [N [f H0]], H1 as [u H1].
  set (A1:=/{ z | ∃ b', (b' ∈ A) /\ (f z b') /}).
  assert (A1 ⊂ (Fin_En N)).
  { red; intros; destruct H2, H2, H2. eapply H0; eauto. }
  exists N, (RelAB A1 (Fin_En N) u f). red; repeat split; try red; intros.
  - destruct H3, H4; try tauto;[eapply H0; eauto|subst y z; auto].
  - destruct (classic (x ∈ A1)).
    * apply H0 in H3. destruct H3 as [y H3]. exists y; constructor; auto.
    * exists u; constructor 2; eauto.
  - pose proof H3. apply H, H0 in H3. destruct H3.
    exists x. constructor; auto. constructor. exists y; auto.
  - destruct H3; [|destruct H4; auto]. destruct H0 as [_ [_ [_ [H0 _]]]].
    apply H0 in H4. destruct H4; auto.
  - destruct H3; [|subst u; auto]. destruct H3, H3, H3.
    assert (x0 = y); try eapply H0; eauto. subst y; auto.
Qed.
