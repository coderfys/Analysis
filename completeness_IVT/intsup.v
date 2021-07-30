(***************************************************************************)
(*   This is part of FA_3rdCalculus, it is distributed under the terms     *)
(*         of the GNU Lesser General Public License version 3              *)
(*                (see file LICENSE for more details)                      *)
(*                                                                         *)
(*            Copyright 2020-2022: Yaoshun Fu and Wensheng Yu.             *)
(***************************************************************************)

Require Import R_sup1.

Definition Fun := Real -> Real.

Definition Dot_con (f :Fun) x0 := ∀ ε, ε > O -> 
  ∃ δ, δ > O /\  ∀ x, | x - x0 | < δ -> | f x - f x0 | < ε.

Definition DotR_con (f :Fun) x0 := ∀ ε, ε > O -> 
  ∃ δ, δ > O /\  ∀ x, x-x0 < δ -> O ≦ x-x0 -> | f x - f x0 | < ε.

Definition DotL_con (f :Fun) x0 := ∀ ε, ε > O -> 
  ∃ δ, δ > O /\  ∀ x, x0-x < δ -> O ≦ x0-x -> | f x - f x0 | < ε.

Fact Dc_DLc : ∀ {f c}, Dot_con f c -> DotL_con f c.
Proof.
  intros; red; intros. destruct (H _ H0), H1.
  exists x; split; auto. intros. destruct H4.
  - apply H2. apply -> Ab1; split.
    + apply Theorem183_1'. rewrite Theorem181. Simpl_R.
    + apply Theorem183_1 in H4. rewrite Theorem181 in H4.
      eapply Theorem171; eauto.
  - symmetry in H4. apply Theorem182_2 in H4. subst c. Simpl_R.
Qed.

Fact Dc_DRc : ∀ {f c}, Dot_con f c -> DotR_con f c.
Proof.
  intros; red; intros. destruct (H _ H0), H1.
  exists x; split; auto. intros. destruct H4.
  - apply H2. apply -> Ab1; split; auto.
    eapply Theorem171; eauto. apply Theorem176_1; auto.
  - symmetry in H4. apply Theorem182_2 in H4. subst c. Simpl_R.
Qed.

Fact DRc_ln : ∀ {f a}, DotR_con f a -> f a < O -> 
  ∃ δ, δ > O /\ ∀ x, x - a < δ -> O ≦ x - a -> f x < O.
Proof.
  intros. apply Theorem182_1' in H0; apply H in H0.
  destruct H0 as [δ H0], H0. exists δ; split; intros; auto.
  apply H1 in H2; auto. apply Ab1'' in H2; destruct H2; Simpl_Rin H4.
Qed.

Fact DLc_lp : ∀ {f b}, DotL_con f b -> f b > O -> 
  ∃ δ, δ > O /\ ∀ x, b - x < δ -> O ≦ b - x -> f x > O.
Proof.
  intros; apply Theorem182_1' in H0; apply H in H0.
  destruct H0 as [δ H0], H0. exists δ; split; intros; auto.
  apply H1 in H2; auto; apply Ab1'' in H2; destruct H2; Simpl_Rin H2.
Qed.

Definition FunClose_con f a b := a < b /\ DotR_con f a /\
  DotL_con f b /\ (∀ z, z ∈ (a|b) -> Dot_con f z).

Ltac temtac1 x :=
  exists x; split; intros; Simpl_R; rewrite <- Theorem178, Theorem180; Simpl_R.

Fact Fc_mFc : ∀ f a b, FunClose_con f a b ->
  FunClose_con (λ x, - f(x)) a b.
Proof.
  intros. destruct H, H0, H1. repeat split; auto; red; intros.
  - destruct (H0 _ H3), H4. temtac1 x.
  - destruct (H1 _ H3), H4. temtac1 x.
  - destruct (H2 _ H3 _ H4), H5. temtac1 x.
Qed.

Ltac temtac2 x := exists x; split; auto; intros; rewrite Mi_R'; Simpl_R.

Fact Fc_Fmc : ∀ {f a b} C, FunClose_con f a b -> 
  FunClose_con (λ x, f(x) - C) a b.
Proof.
  intros. destruct H, H0, H1. repeat split; auto; red; intros.
  - destruct (H0 _ H3), H4. temtac2 x.
  - destruct (H1 _ H3), H4. temtac2 x.
  - destruct (H2 _ H3 _ H4), H5. temtac2 x.
Qed.

Definition Zero_point_theorem := ∀ f a b, FunClose_con f a b ->
  f(a)·f(b) < O -> ∃ ξ, ξ ∈ [a|b] /\ f ξ = O.

Definition supremum y A := 
  Boundup_Ens y A /\ ∀ z, Boundup_Ens z A -> y ≦ z.

Definition infimum y A := 
  Bounddown_Ens y A /\ ∀ z, Bounddown_Ens z A -> z ≦ y.

Corollary Cor_sup : ∀ s S, supremum s S ->
  ∀ ε, ε > O -> ∃ x, x ∈ S /\ (s - ε) < x.
Proof.
  intros; destruct H; Absurd.
  assert (Boundup_Ens (s - ε) S).
  { red; intros. destruct (Co_T167 x (s - ε)); auto. elim H2; eauto. }
  apply H1 in H3. apply LePl_R with (z:=ε) in H3; Simpl_Rin H3.
  destruct (@Pl_R s ε). LEGR H3 (H4 H0).
Qed.

Definition SupremumT := ∀ R, No_Empty R -> 
  (∃ x, Boundup_Ens x R) -> ∃ y, supremum y R.

Definition InfimumT := ∀ R, No_Empty R -> 
  (∃ x, Bounddown_Ens x R) -> ∃ y, infimum y R.

Section Sup_imply_Int.

Hypothesis SupT : SupremumT.

Theorem ZTcase1 : ∀ {f a b}, FunClose_con f a b ->
  f a < O -> f b > O -> ∃ ξ, ξ ∈ [a|b] /\ f ξ = O.
Proof.
  intros. destruct H as [H [H2 [H3]]].
  set (R:= /{ z | a ≦ z /\ z ≦ b /\ f z ≦ O /}).
  assert (a ∈ R). { constructor. repeat split; red; auto. }
  assert (Boundup_Ens b R). { red; intros. destruct H6; tauto. }
  assert (∃ ξ, supremum ξ R). { apply SupT; [red|]; eauto. }
  destruct H7 as [ξ]. inversion H7.
  assert (ξ ∈ [a|b]). { constructor; split; auto. }
  exists ξ; split; auto.
  destruct (Theorem167 (f ξ) O) as [H11|[H11|H11]]; auto.
  - inversion H10. destruct H12, H13.
    + assert (DotR_con f ξ).
      { destruct H12; subst; auto. apply Dc_DRc, H4. split; auto. }
      destruct (DRc_ln H14 H11) as [δ []].
      set (c:=R2min (ξ+((δ/2) NoO_N)) (mid ξ b)).
      assert (c ∈ R).
      { repeat split; left.
        - eapply Theorem172; left; split; eauto. apply R2mgt.
          + apply Pl_R, Pr_2a; auto.
          + apply Mid_P'; auto.
        - apply R2mlt. right. apply Mid_P; auto.
        - apply H16.
          + apply Theorem188_1 with (Θ:=ξ); Simpl_R. apply R2mlt. left.
            apply Theorem188_1 with (Θ:=-ξ); Simpl_R. apply Pr_2b; auto.
          + apply LePl_R with (z:=ξ); Simpl_R. left. apply R2mgt.
            * apply Pl_R, Pr_2a; auto.
            * apply Mid_P'; auto. } apply H8 in H17.
      assert (ξ < c).
      { apply R2mgt; [apply Pl_R, Pr_2a| apply Mid_P']; auto. } LEGR H17 H18.
    + subst b. LGR H11 H1.
  - inversion H10. destruct H12, H12.
    + assert (DotL_con f ξ).
      { destruct H13; subst; auto. apply Dc_DLc, H4. split; auto. }
      destruct (DLc_lp H14 H11) as [δ []].
      destruct (Cor_sup _ _ H7 _ H15), H17.
      inversion H17. destruct H19 as [_ [_ H19]]. apply H8 in H17.
      apply LePl_R with (z:=-x) in H17; Simpl_Rin H17.
      apply H16 in H17; [LEGR H19 H17|].
      apply Theorem188_1' with (Θ:=δ) in H18; Simpl_Rin H18. 
      rewrite Theorem175 in H18.
      apply Theorem188_1 with (Θ:=x); Simpl_R.
    + subst a. LGR H11 H0.
Qed.

Theorem ZTcase2 : ∀ {f a b}, FunClose_con f a b ->
  f a > O -> f b < O -> ∃ ξ, ξ ∈ [a|b] /\ f ξ = O.
Proof.
  intros; apply Fc_mFc in H. apply Theorem183_1 in H0.
  apply Theorem183_1 in H1. eapply ZTcase1 in H; eauto.
  destruct H as [ξ [H]]. apply Theorem183_2 in H2; Simpl_Rin H2; eauto.
Qed.

Theorem ZPT : Zero_point_theorem.
Proof.
  red; intros. assert ((f a < O /\ f b > O) \/ (f a > O /\ f b < O)).
  { destruct (f a), (f b); simpl; inversion H0; auto. }
  destruct H1, H1; [apply ZTcase1| apply ZTcase2]; auto.
Qed.

Theorem IVTcase1 : ∀ f a b, FunClose_con f a b -> f a < f b ->
  ∀ C, f a < C -> C < f b -> ∃ ξ, ξ ∈ [a|b] /\ f ξ = C.
Proof.
  intros. apply Theorem182_3' in H1. apply Theorem182_1' in H2.
  destruct (ZTcase1 (Fc_Fmc C H) H1 H2), H3.
  apply Theorem182_2 in H4. eauto.
Qed.

Theorem IVTcase2 : ∀ f a b, FunClose_con f a b -> f a > f b ->
  ∀ C, f b < C -> C < f a -> ∃ ξ, ξ ∈ [a|b] /\ f ξ = C.
Proof.
  intros. apply Theorem182_3' in H1. apply Theorem182_1' in H2.
  destruct (ZTcase2 (Fc_Fmc C H) H2 H1), H3.
  apply Theorem182_2 in H4. eauto.
Qed.

End Sup_imply_Int.

Section Int_imply_Sup.

Hypothesis ZPT : Zero_point_theorem.

Theorem SupT : SupremumT.
Proof.
  red; intros. destruct (classic (∃ x, EnsMax x R)) as [H1 | H1].
  - destruct H1 as [Max [H1 H2]].
    exists Max; red; intros; split; auto.
  - set (S:= /{ z | Boundup_Ens z R /}); set (S':= /{ w | ~ w ∈ S /}).
    assert (∀ r, {r ∈ S'} + {r ∈ S}) as P.
    { intros. destruct (classicT (r ∈ S)); auto. left. constructor. auto. }
    assert (∀ r, ~ ((r ∈ S') /\ (r ∈ S))) as Q.
    { intros; intro. destruct H2, H2; auto. } Absurd.
    assert (∀ r, r ∈ S' -> ∃ r0, r0 > r /\ r0 ∈ S').
    { intros. destruct H3. Absurd. elim H3. constructor. red. intros.
      destruct (Co_T167 x r); auto. elim H4. exists x. split; auto.
      constructor. intro. destruct H7. elim H1. exists x; split; auto. }
    assert (∀ r, r ∈ S -> ∃ r0, r0 < r /\ r0 ∈ S).
    { intros. Absurd. elim H2. exists r; split; try red; intros.
      - destruct H4; auto.
      - destruct (Co_T167 r z); auto.
        elim H5. exists z; split; auto. constructor. auto. }
    assert (∀ x, x ∈ S' -> ∀ y, y ≦ x -> y ∈ S').
    { intros. constructor; intro. destruct H5, H7. elim H5. constructor.
      red; intros. apply H7 in H8. eapply Theorem173; eauto. }
    assert (∀ x, x ∈ S -> ∀ y, x ≦ y -> y ∈ S).
    { intros. constructor; red; intros. destruct H6.
      apply H6 in H8. eapply Theorem173; eauto. }
    destruct H as [a H], H0 as  [b H0].
    assert (a ∈ S').
    { constructor. intro. destruct H7. elim H1; exists a; red; auto. }
    assert (b ∈ S). { constructor; intros. auto. }
    assert (a < b).
    { destruct H7, (Co_T167 b a); auto. destruct (H7 (H6 _ H8 _ H9)). }
    set (f:= λ x, match P x with | left _ => -(1) | right _ => 1 end).
    assert (f a = -(1)).
    { unfold f. destruct P; auto. destruct (Q a); auto. }
    assert (f b = 1).
    { unfold f. destruct P; auto. destruct (Q b); auto. } 
    assert (FunClose_con f a b). 
    { repeat split; auto; red; intros.
      - destruct (H3 _ H7) as [r [H13]]. pose proof (Theorem182_1' _ _ H13).
        exists (r-a); split; auto; intros.
        apply Theorem188_1' with (Θ:=a) in H16; Simpl_Rin H16.
        assert (x ∈ S'). { eapply H5; red; eauto. }
        rewrite H10. unfold f. destruct P; Simpl_R. destruct (Q x); auto.
      - destruct (H4 _ H8) as [r [H13]]. pose proof (Theorem182_1' _ _ H13).
        exists (b-r); split; auto; intros.
        apply Theorem183_1 in H16. do 2 rewrite Theorem181 in H16.
        apply Theorem188_1' with (Θ:=b) in H16; Simpl_Rin H16.
        assert (x ∈ S). { eapply H6; red; eauto. }
        rewrite H11. unfold f. destruct P; Simpl_R. destruct (Q x); auto.
      - destruct (P z).
        + destruct (H3 _ i) as [z0 [H14]]. pose proof (Theorem182_1' _ _ H14).
          exists (z0-z); split; auto; intros. apply Ab1 in H17; destruct H17.
          apply Theorem188_1' with (Θ:=z) in H18; Simpl_Rin H18.
          assert (x ∈ S'). { eapply H5; red; eauto. } 
          unfold f. destruct P, P; Simpl_R; edestruct Q; eauto.
        + destruct (H4 _ i) as [z0 [H14]]. pose proof (Theorem182_1' _ _ H14).
          exists (z-z0); split; auto; intros. apply Ab1 in H17; destruct H17.
          rewrite Theorem181 in H17.
          apply Theorem188_1' with (Θ:=z) in H17; Simpl_Rin H17.
          assert (x ∈ S). { eapply H6; red; eauto. } 
          unfold f. destruct P, P; Simpl_R; edestruct Q; eauto. }
  assert (f a · f b < O). { rewrite H10, H11; reflexivity. }
  destruct (ZPT _ _ _ H12 H13), H14.
  unfold f in H15; destruct P; inversion H15.
Qed.

Theorem InfT : InfimumT.
Proof.
  red; intros; destruct H0 as [x H0]. set (R' := /{ r | (-r) ∈ R /}).
  assert (∃ y, supremum y R').
  { apply SupT.
    - destruct H; red. exists (-x0); constructor; Simpl_R.
    - exists (-x); red; intros; destruct H1. apply LEminus; Simpl_R. }
  destruct H1 as [y [H1]].
  exists (-y); split; try red; intros; apply LEminus; Simpl_R.
  - apply H1; constructor; Simpl_R.
  - apply H2; red; intros; destruct H4. apply LEminus; Simpl_R.
Qed.

End Int_imply_Sup.
