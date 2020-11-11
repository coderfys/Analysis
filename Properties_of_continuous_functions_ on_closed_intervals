(***************************************************************************)
(*   This is part of FA_ConFun, it is distributed under the terms of the   *)
(*             GNU Lesser General Public License version 3                 *)
(*                (see file LICENSE for more details)                      *)
(*                                                                         *)
(*           Copyright 2020-2022: Yaoshun Fu and Wensheng Yu.              *)
(***************************************************************************)

Require Import t1.

Definition Fun := Real -> Real.

Definition FunDot_con (f :Fun) x0 := ∀ ε, ε > O -> 
  ∃ δ, δ > O /\  ∀ x, | x - x0 | < δ -> | f x - f x0 | < ε.

Definition FunDot_conr (f :Fun) x0 := ∀ ε, ε > O -> 
  ∃ δ, δ > O /\  ∀ x, x-x0 < δ -> O ≦ x-x0 -> | f x - f x0 | < ε.

Definition FunDot_conl (f :Fun) x0 := ∀ ε, ε > O -> 
  ∃ δ, δ > O /\  ∀ x, x0-x < δ -> O ≦ x0-x -> | f x - f x0 | < ε.

Definition FunOpen_con f a b := a < b /\ (∀ z, z ∈ (a|b) -> FunDot_con f z).

Definition FunClose_con f a b := a < b /\ FunDot_conr f a /\
  FunDot_conl f b /\ (∀ z, z ∈ (a|b) -> FunDot_con f z).

Corollary Pr_FunDot :  ∀ f x0, FunDot_con f x0 -> ∀ ε, ε > O -> 
  ∃ δ, δ > O /\  ∀ x, | x - x0 | ≦ δ -> | f x - f x0 | < ε.
Proof.
  intros; apply H in H0; destruct H0 as  [δ [H0]].
  exists ((δ/2) NoO_N); split; intros.
  - apply Pos; simpl; auto.
  - apply H1; eapply Theorem172; left; split; eauto. apply Pr_2b; auto.
Qed.

Corollary limP1 : ∀ f a,
  FunDot_conr f a -> f a > O -> ∀ r, r > O -> r < f a ->
  ∃ δ, δ > O /\ ∀ x, x - a < δ -> O ≦ x - a -> f x > r.
Proof.
  intros. apply Theorem182_1' in H2; apply H in H2.
  destruct H2 as [δ H2], H2.
  exists δ; split; intros; auto. apply H3 in H4; auto;
  apply Ab1'' in H4; destruct H4; Simpl_Rin H4.
Qed.

Corollary limP1' : ∀ f a, FunDot_conr f a -> f a > O -> ∃ δ,
  δ > O /\ ∀ x, x - a < δ -> O ≦ x - a -> f x > ((f a)/2) NoO_N.
Proof.
  intros; apply limP1; try apply Pr_2b; try apply Pr_2a; auto.
Qed.

Corollary limP2 : ∀ f b,
  FunDot_conl f b -> f b > O -> ∀ r, r > O -> r < f b ->
  ∃ δ, δ > O /\  ∀ x, b - x < δ -> O ≦ b - x -> f x > r.
Proof.
  intros; apply Theorem182_1' in H2; apply H in H2.
  destruct H2 as [δ H2], H2. exists δ; split; intros; auto.
  apply H3 in H4; auto; apply Ab1'' in H4;
  destruct H4; Simpl_Rin H4.
Qed.

Corollary limP2' : ∀ f b, FunDot_conl f b -> f b > O -> ∃ δ,
  δ > O /\  ∀ x, b - x < δ -> O ≦ b - x -> f x > ((f b)/2) NoO_N.
Proof.
  intros; apply limP2; try apply Pr_2b; try apply Pr_2a; auto.
Qed.

Corollary limP3 : ∀ f a b c, (∀ z, z ∈ (a|b) -> FunDot_con f z)
  -> c ∈ (a|b) -> f c > O -> ∀ r, r > O -> r < f c ->
  ∃ δ, δ > O /\  ∀ x, | x - c | < δ -> f x > r.
Proof.
  intros. apply Theorem182_1' in H3; pose proof (H _ H0 _ H3).
  destruct H4 as [δ H4], H4. exists δ; split; intros; auto.
  apply H5 in H6; auto; apply Ab1'' in H6; destruct H6; Simpl_Rin H6.
Qed.

Corollary limP3' : ∀ f a b c, (∀ z, z ∈ (a|b) -> FunDot_con f z)
  -> c ∈ (a|b) -> f c > O ->
  ∃ δ, δ > O /\  ∀ x, | x - c | < δ -> f x > ((f c)/2) NoO_N.
Proof.
  intros; eapply limP3; try apply Pr_2b; try apply Pr_2a; eauto.
Qed.

Corollary Pr_Fun1 : ∀ f M a b, FunClose_con f a b ->
  FunClose_con (λ x, M - (f x)) a b.
Proof.
  intros; destruct H, H0, H1.
  repeat split; auto; red; intros.
  - apply H0 in H3; destruct H3 as [δ [H3]].
    exists δ; split; intros; auto.
    rewrite Mi_R'; Simpl_R. simpl. rewrite Theorem178; auto.
  - apply H1 in H3; destruct H3 as [δ [H3]].
    exists δ; split; intros; auto.
    rewrite Mi_R'; Simpl_R. simpl. rewrite Theorem178; auto.
  - apply H2 in H3; apply H3 in H4; destruct H4 as [δ [H4]].
    exists δ; split; intros; auto.
    rewrite Mi_R'; Simpl_R. simpl. rewrite Theorem178; auto.
Qed.

Corollary Pr_Fun2 : ∀ f a b (P: ∀ z, z ∈ [a|b] -> neq_zero (f z))
  (Q:∀ z, z ∈ [a|b] -> (f z) > O),
  FunClose_con f a b -> FunClose_con 
  (λ x, match classicT (x ∈ [a|b]) with
        | left l => (1/(f x)) (P _ l)
        | right _ => f x end) a b.
Proof.
  intros; destruct H, H0, H1.
  assert (a ∈ [a|b]) as G1. { constructor; split; red; auto. }
  assert (b ∈ [a|b]) as G2. { constructor; split; red; auto. }
  assert (∀z, z ∈ (a|b) -> f z > O) as G3.
  { intros; destruct H3,H3.
    apply Q; constructor; split; red; auto. }
  repeat split; auto; red; intros.
  - assert (f a > O); auto.
    destruct (limP1' f a H0 H4) as [δ1 H5], H5.
    assert (((f a) · ((f a)/2) NoO_N) > O) as Q1.
    { apply Pos; auto; apply Pos'; simpl; auto. }
    pose proof (Pos _ _ H3 Q1).
    apply H0 in H7. destruct H7 as [δ2 [H7]].
    assert ((R2min δ1 (R2min δ2 (b - a))) > O).
    { destruct (Rcase2 δ1 (R2min δ2 (b - a))).
      - rewrite Pr_min; auto.
      - rewrite Pr_min1, Pr_min; auto.
        destruct (Rcase2 δ2 (b - a)).
        + rewrite Pr_min; auto.
        + rewrite Pr_min1,Pr_min; auto. apply Theorem182_1'; auto. }
    exists (R2min δ1 (R2min δ2 (b - a))); split; intros; auto.
    destruct (classicT (a ∈ [a|b])); try tauto.
    assert ((R2min δ1 (R2min δ2 (b - a))) ≦ δ1) as P1.
    { apply Pr_min2. }
    assert ((R2min δ1 (R2min δ2 (b - a))) ≦ δ2) as P2.
    { pose proof (Pr_min2 δ2 (b - a)).
      pose proof (Pr_min3 δ1 (R2min δ2 (b - a))).
      eapply Theorem173; eauto. }
    assert ((R2min δ1 (R2min δ2 (b - a))) ≦ (b - a)) as P3.
    { rewrite (Pr_min1 δ2 _).
      pose proof (Pr_min2 (b - a) δ2).
      pose proof (Pr_min3 δ1 (R2min (b - a) δ2)).
      eapply Theorem173; eauto. }
    assert (x ∈ [a|b]).
    { apply LePl_R with (z:=a) in H11; Simpl_Rin H11.
      constructor; split; auto.
      apply LePl_R with (z:=-a); Simpl_R.
      left; eapply Theorem172; eauto. }
    destruct (classicT (x ∈ [a|b])); try tauto.
    apply Theorem203_1' with (Θ:=(f a)); auto.
    pattern (f a) at 3; rewrite <- Ab3; auto.
    rewrite <- Theorem193, Theorem202'; Simpl_R.
    pattern (f a) at 1; rewrite Theorem194, Di_Rt; Simpl_R.
    apply Theorem203_1' with (Θ:=(f x)); auto.
    pattern (f x) at 3; rewrite <- Ab3; auto.
    rewrite <- Theorem193, Theorem202'; Simpl_R.
    rewrite <- Theorem181, Theorem178.
    assert (x - a < δ1). { eapply Theorem172; eauto. }
    assert (x - a < δ2). { eapply Theorem172; eauto. }
    apply H6 in H13; auto. apply H8 in H14; auto.
    eapply Theorem171; eauto.
    rewrite <- Theorem199, Theorem194, (Theorem194 (ε · f a)).
    apply Theorem203_1; auto. apply Pos; auto.
    - assert (f b > O); auto.
      destruct (limP2' f b H1 H4) as [δ1 H5], H5.
      assert (((f b) · ((f b)/2) NoO_N) > O) as Q1.
      { apply Pos; auto. apply Pos'; simpl; auto. }
      pose proof (Pos _ _ H3 Q1).
      apply H1 in H7. destruct H7 as [δ2 [H7]].
      assert ((R2min δ1 (R2min δ2 (b - a))) > O).
      { destruct (Rcase2 δ1 (R2min δ2 (b - a))).
        - rewrite Pr_min; auto.
        - rewrite Pr_min1, Pr_min; auto. destruct (Rcase2 δ2 (b - a)).
          + rewrite Pr_min; auto.
          + rewrite Pr_min1, Pr_min; auto. apply Theorem182_1'; auto. }
      exists (R2min δ1 (R2min δ2 (b - a))); split; intros; auto.
      destruct (classicT (b ∈ [a|b])); try tauto.
      assert ((R2min δ1 (R2min δ2 (b - a))) ≦ δ1) as P1. { apply Pr_min2. }
      assert ((R2min δ1 (R2min δ2 (b - a))) ≦ δ2) as P2.
      { pose proof (Pr_min2 δ2 (b - a)).
        pose proof (Pr_min3 δ1 (R2min δ2 (b - a))). eapply Theorem173; eauto. }
      assert ((R2min δ1 (R2min δ2 (b - a))) ≦ (b - a)) as P3.
      { rewrite (Pr_min1 δ2 _). pose proof (Pr_min2 (b - a) δ2).
        pose proof (Pr_min3 δ1 (R2min (b - a) δ2)). eapply Theorem173; eauto. }
      assert (x ∈ [a|b]).
      { apply LePl_R with (z:=x) in H11; Simpl_Rin H11.
        constructor; split; red; auto.
        assert (b - x < b - a). { eapply Theorem172; eauto. }
        apply Theorem183_1 in H12. repeat rewrite Theorem181 in H12.
        apply Theorem188_1' with (Θ:=b) in H12; Simpl_Rin H12. }
      destruct (classicT (x ∈ [a|b])); try tauto.
      apply Theorem203_1' with (Θ:=(f b)); auto.
      pattern (f b) at 3; rewrite <- Ab3; auto.
      rewrite <- Theorem193, Theorem202'; Simpl_R.
      pattern (f b) at 1; rewrite Theorem194, Di_Rt; Simpl_R.
      apply Theorem203_1' with (Θ:=(f x)); auto.
      pattern (f x) at 3; rewrite <- Ab3; auto.
      rewrite <- Theorem193, Theorem202'; Simpl_R.
      rewrite <- Theorem181, Theorem178.
      assert (b - x < δ1). { eapply Theorem172; eauto. }
      assert (b - x < δ2). { eapply Theorem172; eauto. }
      apply H6 in H13; auto. apply H8 in H14; auto.
      eapply Theorem171; eauto.
      rewrite <- Theorem199, Theorem194, (Theorem194 (ε · f b)).
      apply Theorem203_1; auto. apply Pos; auto.
  - assert (f z > O); auto.
    destruct (limP3' f a b z H2 H3 H5) as [δ1 H6], H6.
    assert (((f z) · ((f z)/2) NoO_N) > O) as Q1.
    { apply Pos; auto. apply Pos'; simpl; auto. }
    pose proof (Pos _ _ H4 Q1). specialize (H2 z H3).
    apply H2 in H8. destruct H8 as [δ2 [H8]].
    assert ((R2min δ1 (R2min δ2 (R2min (z - a) (b - z)))) > O).
    { destruct (Pr_min4 δ1 (R2min δ2 (R2min (z-a) (b-z)))); rewrite H10; auto.
      destruct (Pr_min4 δ2 (R2min (z-a) (b-z))); rewrite H11; auto.
      destruct H3, H3. apply Theorem182_1' in H3.
      apply Theorem182_1' in H12.
      destruct (Pr_min4 (z - a) (b - z)); rewrite H13; auto. }
    exists ((R2min δ1 (R2min δ2 (R2min (z-a) (b-z))))); split; intros; auto.
    assert (z ∈ [a|b]).
    { destruct H3, H3; constructor; split; red; auto. }
    clear H3; rename H12 into H3.
    destruct (classicT (z ∈ [a|b])); try tauto.
    assert ((R2min δ1 (R2min δ2 (R2min (z-a) (b-z))))≦δ1) as P1.
    { apply Pr_min2. }
    assert ((R2min δ1 (R2min δ2 (R2min (z-a) (b-z))))≦δ2) as P2.
    { rewrite Pr_min1, Pr_min1'; apply Pr_min2. }
    assert ((R2min δ1 (R2min δ2 (R2min (z-a) (b-z))))≦(z-a)) as P3.
    { rewrite <- Pr_min1', Pr_min1, Pr_min1'; apply Pr_min2. }
    assert ((R2min δ1 (R2min δ2 (R2min (z-a) (b-z))))≦(b-z)) as P4.
    { repeat rewrite <- Pr_min1'; rewrite Pr_min1; apply Pr_min2. }
    assert (x ∈ [a|b]).
    { assert (|x - z| < z - a). { eapply Theorem172; eauto. }
      assert (|x - z| < b - z). { eapply Theorem172; eauto. }
      apply Ab1'' in H12; destruct H12 as [H12 _].
      apply Ab1'' in H13; destruct H13 as [_ H13].
      unfold Minus_R in H12; rewrite Theorem180 in H12.
      rewrite <- Theorem186 in H12; Simpl_Rin H12.
      rewrite Theorem175 in H13; Simpl_Rin H13.
      constructor; split; red; auto. }
    destruct (classicT (x ∈ [a|b])); try tauto.
    apply Theorem203_1' with (Θ:=(f z)); auto.
    pattern (f z) at 3; rewrite <- Ab3; auto.
    rewrite <- Theorem193, Theorem202'; Simpl_R.
    pattern (f z) at 1; rewrite Theorem194, Di_Rt; Simpl_R.
    apply Theorem203_1' with (Θ:=(f x)); auto.
    pattern (f x) at 3; rewrite <- Ab3; auto.
    rewrite <- Theorem193, Theorem202'; Simpl_R.
    rewrite <- Theorem181, Theorem178.
    assert (|x - z| < δ1). { eapply Theorem172; eauto. }
    assert (|x - z| < δ2). { eapply Theorem172; eauto. }
    apply H7 in H13; auto. apply H9 in H14; auto.
    eapply Theorem171; eauto.
    rewrite <- Theorem199, Theorem194, (Theorem194 (ε · f z)).
    apply Theorem203_1; auto. apply Pos; auto.
Qed.

Definition FunClose_boundup f a b := 
  a < b /\ ∃ up, (∀ z, z ∈ [a|b] -> f z ≦ up).

Definition FunClose_bounddown f a b := 
  a < b /\ ∃ down, (∀ z, z ∈ [a|b] -> down ≦ f z).

Lemma L1 : ∀ f a b, FunClose_con f a b -> ∀ x0, x0 ∈ (a|b) ->
  ∃ δ, δ > O /\ (∃ up down, (∀ z, z ∈ [x0|-δ] -> f z ≦ up) /\
  (∀ z, z ∈ [x0|-δ] -> down ≦ f z)).
Proof.
  intros; apply H in H0.
  assert (1 > O). { simpl; auto. } eapply Pr_FunDot in H1; eauto.
  destruct H1 as [δ H2], H2. exists δ; split; auto.
  assert (∀z, z ∈ [x0|-δ] -> |f z| ≦ (|f x0| + 1)).
  { intros; left; destruct H3. apply Ab1''' in H3. apply H2 in H3.
    apply Theorem188_1' with (Θ:=|f x0|) in H3.
    rewrite Theorem175 in H3.
    pose proof (Ab2 ((f z) - (f x0)) (f x0)); Simpl_Rin H4.
    eapply Theorem172; eauto. }
  exists (|f x0|+1), (- (|f x0|+1)); split; intros; apply H3 in H4;
  apply Ab1' in H4; tauto.
Qed.

Theorem T1 : ∀ f a b, FunClose_con f a b -> FunClose_boundup f a b.
Proof.
  intros; destruct H; split; auto.
  set (R:=/{ t | FunClose_boundup f a t /\ t ≦ b /}).
  assert (Boundup_Ens b R). { red; intros; destruct H1; tauto. }
  destruct H0; red in H0. assert (1 > O). { simpl; auto. }
  destruct H0 with 1 as [δ [H4 H5]]; auto.
  destruct (Co_T167 (b - a) δ).
  - exists (R2max ((f a) + 1) (f (δ + a))); intros. destruct H7, H7.
    apply LePl_R with (z:=-a) in H8; Simpl_Rin H8.
    eapply Theorem173 in H6; eauto. 
    apply LePl_R with (z:=-a) in H7; Simpl_Rin H7; destruct H6.
    + apply H5 in H7; auto; apply Ab1'' in H7; destruct H7.
      left; eapply Theorem172; right; split; eauto; apply Pr_max2.
    + apply Theorem188_2' with (Θ:=a) in H6; Simpl_Rin H6.
      subst z; apply Pr_max3.
  - assert (((δ/2) NoO_N + a) ∈ R).
    { constructor; repeat split.
      - rewrite Theorem175; apply Pl_R; apply Pr_2a; auto.
      - exists ((f a) + 1); intros; destruct H7, H7.
        assert (|z - a|< δ).
        { rewrite Ab5; auto; apply Theorem188_3 with (Θ:=a);
          Simpl_R. eapply Theorem172; left; split; eauto.
          apply Theorem188_3'; apply Pr_2b; auto. }
          apply Ab1'' in H9; destruct H9. rewrite Theorem175 in H10.
          apply LePl_R with (z:=-a) in H7; Simpl_Rin H7.
          apply Theorem188_3' with (Θ:=-a) in H10; Simpl_Rin H10.
          apply H5 in H10; auto; apply Ab1'' in H10;
          destruct H10; red; auto.
      - left; apply Theorem188_1 with (Θ:=-a); Simpl_R.
        eapply Theorem171; eauto. apply Pr_2b; auto. }
    assert (∃ y, supremum y R).
    { apply SupremumT; eauto; red; eauto. }
    destruct H8 as [ξ H8]; pose proof H8; destruct H8.
    red in H8; apply H8 in H7. apply H9 in H1; destruct H1.
    { assert (ξ ∈ (a|b)). 
      { constructor; split; auto. 
        eapply Theorem172; right; split; try apply H7.
        rewrite Theorem175; apply Pl_R; apply Pr_2a; auto. }
      eapply L1 in H11; try split; eauto.
      destruct H11 as [δ1 H11], H11, H12 as [up [_ [H12 _]]].
      destruct (Cor_supremum _ _ H9 _ H11) as [t0 H13],H13,H13,H13.
      assert (FunClose_boundup f a (ξ + δ1)).
      { red; split.
        - assert (a < ξ).
          { eapply Theorem172; right; split; try apply H7.
            rewrite Theorem175; apply Pl_R; apply Pr_2a; auto. }
          eapply Theorem171; eauto. apply Pl_R; auto.
        - destruct H13, H16 as [up1 H16].
          exists (R2max up up1); intros; destruct H17, H17.
          destruct (Co_T167 z t0).
          + assert (z ∈ [a|t0]). { constructor; auto. }
            apply H16 in H20. eapply Theorem173; eauto. apply Pr_max3.
          + assert (z ∈ [ξ|-δ1]).
            { constructor; split; auto. left; eapply Theorem171; eauto. }
            apply H12 in H20. eapply Theorem173; eauto. apply Pr_max2. }
        - destruct (Co_T167 (ξ + δ1) b).
          + assert ((ξ + δ1) ∈ R). { constructor; split; auto. }
            apply H8 in H18. destruct (@Pl_R ξ δ1). LEGR H18 (H19 H11).
          + destruct H16, H18 as [up1 H18].
            exists up1; intros; destruct H19, H19.
            apply H18; constructor; split; auto.
            left; eapply Theorem172; eauto. }
      { subst ξ; destruct H2; red in H1.
        destruct H1 with 1 as [δ1 [H11]]; auto.
        assert (FunClose_boundup f (b - δ1) b).
        { red; split.
          - apply Theorem188_3  with (Θ:=δ1); Simpl_R. apply Pl_R; auto.
          - exists (R2max ((f b) + 1) (f (b - δ1))); intros.
            destruct H13, H13, H13.
            + apply Theorem188_3' with (Θ:=δ1) in H13;
              Simpl_Rin H13. rewrite Theorem175 in H13.
              apply Theorem188_3' with (Θ:=-z) in H13;
              Simpl_Rin H13. apply LePl_R with (z:=-z) in H14;
              Simpl_Rin H14. apply H12 in H13; red; auto.
              apply Ab1'' in H13; destruct H13.
              left; eapply Theorem172; right; split; eauto. apply Pr_max2. 
            + rewrite <- H13; apply Pr_max3. }
        destruct (Cor_supremum _ _ H9 _ H11) as [t0 H14], H14, H14, H14.
        destruct H13 as [_ [up1 H13]], H14 as [_ [up2 H14]].
        exists (R2max up1 up2); intros; destruct H17, H17.
        destruct (Co_T167 (b - δ1) z).
        - assert (z ∈ [(b - δ1)|b]). { constructor; auto. }
          apply H13 in H20; eapply Theorem173; eauto; apply Pr_max2.
        - assert (z ∈ [a|t0]).
          { constructor; split; auto; left; eapply Theorem171; eauto. }
          apply H14 in H20; eapply Theorem173; eauto; apply Pr_max3. }
Qed.

Theorem T1' : ∀ f a b,
  FunClose_con f a b -> FunClose_bounddown f a b.
Proof.
  intros; apply Pr_Fun1 with (M:=O) in H; simpl in H.
  apply T1 in H; destruct H as [H [up H0]].
  red; split; auto; exists (-up); intros.
  apply H0 in H1; destruct H1.
  - left; apply Theorem183_3'; Simpl_R.
  - right; apply Theorem183_2'; Simpl_R.
Qed.

Theorem T2 : ∀ f a b, FunClose_con f a b -> 
  ∃ z, z ∈ [a|b] /\ (∀ w, w ∈ [a|b] -> f w ≦ f z).
Proof.
  intros. pose proof H as G.
  apply T1 in H; destruct H as [H [up H0]].
  set (R:=/{ w | ∃ z, z ∈ [a|b] /\ w = f z /}).
  assert (∃ y, supremum y R).
  { apply SupremumT.
    - red. exists (f a); constructor.
      exists a; split; auto. constructor; split; red; auto.
    - exists up; red; intros; destruct H1, H1 as [z H1], H1.
      apply H0 in H1. subst x; auto. }
  destruct H1 as [M H1], H1; red in H1.
  destruct (classic (∃ x, x ∈ [a|b] /\ M = f x)) as [H3 | H3].
  - destruct H3, H3; subst M.
    exists x; split; intros; auto. apply H1; constructor; eauto.
  - assert (∀ x, x ∈ [a|b] -> f x < M).
    { intros. assert (f x ∈ R). { constructor; eauto. }
      apply H1 in H5; destruct H5; auto. elim H3; eauto. }
    assert (∀ x, x ∈ [a|b] -> neq_zero (M - (f x))).
    { intros; apply H4 in H5; apply Theorem182_1' in H5.
      destruct (M - f x); simpl; auto. }
    set (g:= λ x, match classicT (x ∈ [a|b]) with
                   | left l => (1/(M - (f x))) (H5 _ l)
                   | right _ => M - f x end).
    assert (FunClose_con g a b).
    { destruct G, H7, H8.
      assert (FunClose_con f a b). repeat split; auto.
      assert (∀ z, z ∈ [a|b] -> (M - (f z)) > O).
      { intros. apply Theorem188_1 with (Θ :=(f z));
        Simpl_R; apply H4; auto. }
      apply (Pr_Fun1 f M a b) in H10.
      pose proof (Pr_Fun2 (λ x,M - f x) a b H5 H11 H10);
      simpl in H12. destruct H12, H13, H14. repeat split; auto. }
    apply T1 in H6; destruct H6, H7 as [K H7].
    assert (K > O).
    { assert ((mid a b) ∈ [a|b]).
      { constructor; split.
        - left. apply Mid_P'; auto.
        - left. apply Mid_P; auto. } pose proof H8.
      apply H7 in H8. eapply Theorem172; right; split; eauto.
      unfold g. destruct (classicT ((mid a b) ∈ [a|b])); try tauto.
      apply Pos'; try reflexivity.
      apply Theorem182_1'. apply H4; auto. }
      assert (neq_zero K). { destruct K; simpl; auto. }
    assert (∀ z, z ∈ [a|b] -> f z ≦ (M - ((1/ K) H9))).
    { intros. pose proof H10. apply H7 in H10. unfold g in H10.
      destruct (classicT (z ∈ [a|b])); try tauto. destruct H10.
      - left. apply Theorem203_1' with (Θ:= K); Simpl_R.
        unfold Minus_R. rewrite Theorem201', Theorem197'; Simpl_R.
        apply H4 in H11. apply Theorem182_1' in H11.
        apply Theorem203_1 with (Θ:= (M - f z)) in H10;
        Simpl_Rin H10. unfold Minus_R in H10.
         rewrite Theorem194, Theorem201' in H10.
        rewrite Theorem197' in H10; Simpl_Rin H10.
        apply Theorem188_1' with (Θ :=((f z) · K)) in H10;
        Simpl_Rin H10. apply Theorem188_1 with (Θ :=1); Simpl_R.
        rewrite Theorem175; auto. 
      - right. symmetry in H10; apply ROv_uni in H10.
        rewrite <- H10; Simpl_R. }
  assert (Boundup_Ens (M - (1/K) H9) R).
  { red; intros. destruct H11, H11, H11. subst x; auto. }
  apply H2 in H11.
  assert (M > (M - (1/K) H9)).
  { apply Theorem188_1 with (Θ :=(1/K) H9); Simpl_R.
    apply Pl_R; auto; apply Pos'; simpl; auto. } LEGR H11 H12.
Qed.

Theorem T2' : ∀ f a b, FunClose_con f a b -> 
  ∃ z, z ∈ [a|b] /\ (∀ w, w ∈ [a|b] -> f z ≦ f w).
Proof.
  intros; apply Pr_Fun1 with (M:=O) in H; simpl in H.
  apply T2 in H; destruct H as [up [H0]].
  exists up; split; intros; auto.
  apply H in H1; destruct H1.
  - left; apply Theorem183_3'; Simpl_R.
  - right; apply Theorem183_2'; Simpl_R.
Qed.

Lemma L3 : ∀ {f a b C}, FunDot_conl f b -> b > a -> f b > C -> 
  ∃ z, a < z /\ z < b /\ f z > C.
Proof.
  intros. apply Theorem182_1' in H1; apply H in H1.
  destruct H1 as [δ H1], H1.
  assert (b - (δ/2) NoO_N < b).
  { apply Theorem188_1 with (Θ:=(δ/2) NoO_N); Simpl_R.
    apply Pl_R; apply Pr_2a; auto. }
  assert (b - (b - ((δ/2) NoO_N)) < δ).
  { Simpl_R; apply Pr_2b; auto. }
  assert (O ≦ b- (b - ((δ/2) NoO_N))).
  { left; apply Theorem182_1'; auto. }
  destruct (Co_T167 (b - (δ/2) NoO_N) a).
  - pose proof (Mid_P' _ _ H0). pose proof (Mid_P _ _ H0).
    exists (mid a b); repeat split; auto.
    assert (b - (mid a b) < δ).
    { assert (b - (δ/2) NoO_N < (mid a b)).
      { eapply Theorem172; eauto. }
      pose proof (Pr_2b H1). eapply Theorem171; eauto.
      apply Theorem188_1 with (Θ:=(mid a b)); Simpl_R.
      apply Theorem188_1' with (Θ:=(δ/2) NoO_N) in H9;
      Simpl_Rin H9. rewrite Theorem175; auto. }
  assert (O ≦ b - ((mid a b))).
  { left; apply Theorem188_1 with (Θ:=(mid a b)); Simpl_R. }
  apply H2 in H9; auto; apply Ab1'' in H9;
  destruct H9; Simpl_Rin H9.
  - exists (b - (δ/2) NoO_N); repeat split; auto.
    apply H2 in H4; auto; apply Ab1'' in H4;
    destruct H4; Simpl_Rin H4.
Qed.

Theorem T3 : ∀ f a b, FunClose_con f a b -> f a < f b ->
  ∀ C, f a < C -> C < f b -> ∃ ξ, ξ ∈ (a|b) /\ f ξ = C.
Proof.
  intros; set (R:= /{ t | (∀ x, x ∈ [a|t] -> f x < C) /\ t < b /}).
  assert (∃ w, w ∈ (a|b) /\ w ∈ R).
  { destruct H, H3; red in H3.
    apply Theorem182_1' in H1.
    destruct (H3 _ H1) as [δ1 H5], H5, (Co_T167 (b - a) δ1).
    - assert ((mid a b) ∈ (a|b)).
      { constructor; split; try apply Mid_P';
        try apply Mid_P; auto. }
        exists (mid a b); split; auto; constructor; split; intros.
        + destruct H8, H8, H9, H9.
          apply LePl_R with (z:=-a) in H9; Simpl_Rin H9.
          assert (x - a < δ1).
          { apply Theorem188_1 with (Θ:=a); Simpl_R.
            apply LePl_R with (z:=a) in H7; Simpl_Rin H7.
            assert (b > x). { eapply Theorem172; eauto. }
            eapply Theorem172; eauto. }
          apply H6 in H12; auto. apply Ab1'' in H12; destruct H12.
          rewrite Theorem175 in H13; Simpl_Rin H13.
        + destruct H8; tauto.
    - assert ((a + ((δ1/2) NoO_N)) ∈ (a|b)).
      { constructor; split.
        - apply Pl_R; apply Pr_2a; auto.
        - apply Theorem188_1' with (Θ:=a) in H7; Simpl_Rin H7.
          eapply Theorem171; eauto.
          rewrite Theorem175; apply Theorem188_1'.
          apply Pr_2b; auto. }
      exists (a + (δ1/2) NoO_N); split; auto;
      constructor; split; intros.
      + destruct H8, H8, H9, H9.
        apply LePl_R with (z:=-a) in H9; Simpl_Rin H9.
        assert (x - a < δ1).
        { apply Theorem188_1 with (Θ:=a); Simpl_R.
          eapply Theorem172; left; split; eauto.
          rewrite Theorem175; apply Theorem188_1'.
          apply Pr_2b; auto. }
        apply H6 in H12; auto. apply Ab1'' in H12; destruct H12.
        rewrite Theorem175 in H13; Simpl_Rin H13.
      + destruct H8; tauto. }
  destruct H3 as [w H3], H3, H3.
  assert (Boundup_Ens b R).
  { red; intros; red; destruct H5; tauto. }
  assert (∃ ξ, supremum ξ R). { apply SupremumT; try red; eauto. }
  destruct H6 as [ξ H6].
  assert (ξ ∈ (a|b)).
  { constructor; split.
    - apply H6 in H4; destruct H3; eapply Theorem172; eauto.
    - destruct H as [H [_ [H7 _]]].
      destruct (L3 H7 H H2) as [z H8], H8, H9.
      pose proof H6.
      destruct H6; apply H12 in H5; destruct H5; auto. subst ξ.
      apply Theorem182_1' in H9.
      destruct (Cor_supremum _ _ H11 _ H9) as [z1 [H13]], H13, H13;
      Simpl_Rin H5.
      assert (z ∈ [a|z1]). { constructor; split; red; auto. }
      apply H13 in H15. LGR H15 H10. }
  destruct (Theorem167 (f ξ) C) as [H8 | [H8 | H8]]; eauto.
  - assert (((C - (f ξ))/2) NoO_N > O).
    { apply Theorem182_1' in H8. apply Pos; simpl; auto. }
    pose proof H7. apply H in H7. apply H7 in H9.
    destruct H9 as [δ [H9]].
    destruct (Cor_supremum _ _ H6 _ H9) as [t0 [H12]], H12, H12.
    assert ((ξ + (R2min ((δ/2) NoO_N) (((b - ξ)/2) NoO_N))) ∈ R).
    { assert ((ξ + (R2min ((δ/2) NoO_N)  (((b-ξ)/2) NoO_N))) < b).
      { assert (ξ + (((b - ξ)/2) NoO_N) < b).
        { apply Theorem203_1' with (Θ:=2);  try reflexivity.
          rewrite Theorem201'; Simpl_R.
          rewrite <- NPl1_, <- Real_PZp.
          repeat rewrite  Theorem201; Simpl_R.
          rewrite Theorem186, (Theorem175 _ (b - ξ)); Simpl_R.
          destruct H10, H10. apply Theorem188_1'; auto. }
        destruct (Rcase2 ((δ/2) NoO_N)  (((b - ξ)/2) NoO_N)).
        - rewrite Pr_min; auto.
          eapply Theorem172; left; split; eauto.
          rewrite Theorem175, (Theorem175 ξ _). apply LePl_R; auto.
        - rewrite Pr_min1, Pr_min; auto. }
      constructor; split; intros; auto.
      destruct H16, H16, (Co_T167 x t0 ).
      + apply H12; constructor; auto.
      + assert (| x - ξ | < δ).
         { apply Ab1''; split.
           - eapply Theorem171; eauto.
           - eapply Theorem172; left; split; eauto.
             rewrite Theorem175, (Theorem175 ξ _).
             apply Theorem188_1'. pose proof (Pr_2b H9).
             eapply Theorem172; left;
             split; eauto; apply Pr_min2. }
         apply H11, Ab1'' in H19; destruct H19.
         apply Theorem203_1 with (Θ:=2) in H20; try reflexivity.
         rewrite Theorem201' in H20; Simpl_Rin H20.
         rewrite <- NPl1_, <- Real_PZp in H20.
         repeat rewrite Theorem201 in H20; Simpl_Rin H20.
         rewrite Theorem186, (Theorem175 _ (C - (f ξ))) in H20;
         Simpl_Rin H20.  apply Theorem188_1' with (Θ:= C) in H8.
         eapply Theorem171 in H8; eauto.
         apply Theorem203_1' with (Θ:=2); try reflexivity.
         rewrite <- NPl1_, <- Real_PZp.
         repeat rewrite Theorem201; Simpl_R. } apply H6 in H15.
         assert (ξ + R2min ((δ/2) NoO_N) (((b - ξ)/2) NoO_N) > ξ).
         { apply Pl_R.
           destruct (Pr_min4 ((δ/2) NoO_N) (((b - ξ)/2) NoO_N));
           rewrite H16.
           - apply Pos; simpl; auto.
           - apply Theorem203_1' with (Θ:=2);
             try reflexivity; Simpl_R.
             destruct H10, H10; apply Theorem182_1'; auto. }
         LEGR H15 H16.
  - assert (FunDot_conl f ξ).
    { red; intros; apply H in H7; apply H7 in H9.
      destruct H9 as [δ [H9]].
      exists δ; split; intros; auto.
      apply H10. apply Ab1''; split.
      - apply Theorem188_1 with (Θ:= δ); Simpl_R.
        apply Theorem188_1' with (Θ:= x) in H11; Simpl_Rin H11.
        rewrite Theorem175; auto.
      - apply LePl_R with (z:=x) in H12; Simpl_Rin H12.
        eapply Theorem172; left; split; eauto; apply Pl_R; auto. }
    destruct H7, H7, (L3 H9 H7 H8) as [z H11], H11, H12.
    assert (Boundup_Ens z R).
    { red; intros; destruct H14, H14.
      destruct (Co_T167 x z); auto.
      assert (f z < C). 
      { apply H14; constructor; split; red; auto. }
      LGR H17 H13. }
    apply H6 in H14. LEGR H14 H12.
Qed.

Theorem T3' : ∀ f a b, FunClose_con f a b -> f a > f b ->
  ∀ C, f b < C -> C < f a -> ∃ ξ, ξ ∈ (a|b) /\ f ξ = C.
Proof.
  intros; apply Pr_Fun1 with (M:=O) in H; simpl in H.
  apply Theorem183_1 in H0; apply Theorem183_1 in  H1.
  apply Theorem183_1 in H2; eapply T3 in H; eauto.
  destruct H as [ξ [H]]; apply Theorem183_2' in H3; eauto.
Qed.

Theorem zero_point_theorem : ∀ f a b, FunClose_con f a b ->
  (f a · f b) < O -> ∃ ξ, ξ ∈ (a|b) /\ f ξ = O.
Proof.
  intros. assert ((f a < O /\ f b > O) \/ (f a > O /\ f b < O)).
  { destruct (f a), (f b); simpl; inversion H0; auto. }
  destruct H1, H1.
  - apply T3; auto. eapply Theorem171; eauto.
  - apply T3'; auto. eapply Theorem171; eauto.
Qed.

Definition Un_Con f a b := a < b /\ 
  ∀ ε, ε > O -> ∃ δ, δ > O /\  ∀ x1 x2, x1 ∈ [a|b] -> 
  x2 ∈ [a|b] -> |x1 - x2| < δ -> |f x1 - f x2| < ε.

Theorem T4 :  ∀ f a b, FunClose_con f a b -> Un_Con f a b.
Proof.
  intros; destruct H, H0, H1.
  split; intros; auto.
  set (R:= /{ t | (a < t /\ ∃δ, δ > O /\ (∀x1 x2,x1 ∈ [a|t] -> 
  x2 ∈ [a|t] -> | x1-x2 | < δ -> | f x1 - f x2 | < ε)) /\ t≦b /}).
  assert (∃ c, c ∈ R).
  { pose proof (Pr_2a H3).
    apply H0 in H4; destruct H4 as [δ [H4]]. pose proof (Pr_2a H4).
  exists (a + (R2min ((δ/2) NoO_N) (b - a))); repeat split.
  - destruct (Pr_min4 ((δ/2) NoO_N) (b - a)); rewrite H7.
    + apply Pl_R; apply Pr_2a; auto.
    + rewrite Theorem175; Simpl_R.
  - exists δ; split; intros; auto.
    + destruct H7, H7, H8, H8. 
      assert (x1 ≦ a+ ((δ/2) NoO_N)).
      { eapply Theorem173; eauto. rewrite Theorem175, (Theorem175 a _).
        apply LePl_R; apply Pr_min2. }
      assert (x2 ≦ a+ ((δ/2) NoO_N)).
      { eapply Theorem173; eauto. rewrite Theorem175, (Theorem175 a _).
        apply LePl_R; apply Pr_min2. }
      clear H9 H10 H11. rename H12 into H9. rename H13 into H10.
      apply LePl_R with (z:=-a) in H7; Simpl_Rin H7.
      apply LePl_R with (z:=-a) in H8; Simpl_Rin H8.
      assert (x1 - a < δ).
      { apply Theorem188_1 with (Θ:=a); Simpl_R.
        eapply Theorem172; left; split; eauto.
        rewrite Theorem175; apply Theorem188_1'. apply Pr_2b; auto. }
      assert (x2 - a < δ).
      { apply Theorem188_1 with (Θ:=a); Simpl_R.
        eapply Theorem172; left; split; eauto.
        rewrite Theorem175; apply Theorem188_1'. apply Pr_2b; auto. } 
      apply H5 in H11; auto. apply H5 in H12; auto.
      pose proof (Theorem189 H11 H12); Simpl_Rin H13.
      rewrite <- (Theorem178 (f x2 - f a)), Theorem181 in H13.
      pose proof (Ab2 (f x1 - f a) (f a - f x2)).
      unfold Minus_R in H14. rewrite <- Theorem186 in H14.
      Simpl_Rin H14. eapply Theorem172; eauto.
  - pose proof (Pr_min3 ((δ/2) NoO_N) (b - a)).
    apply LePl_R with (z:=a) in H7; Simpl_Rin H7. rewrite Theorem175; auto. }
  destruct H4 as [c H4].
  assert (Boundup_Ens b R). { red; intros; destruct H5; tauto. } 
  assert (exists ξ, supremum ξ R).
  { apply SupremumT; try red; eauto. }
  destruct H6 as [ξ H6]. pose proof H6 as G3. destruct H6.
  assert (a < ξ).
  { pose proof H4. apply H6 in H4. destruct H8, H8, H8.
    eapply Theorem172; eauto. } 
  apply H7 in H5. destruct H5.
  - assert (ξ ∈ (a|b)). { constructor; auto. }
    pose proof (Pr_2a H3).
    apply H2 in H9. eapply Pr_FunDot in H10; eauto.
    destruct H10 as [δ1 [H10]].
    assert (∀x1 x2, x1 ∈ [(ξ-δ1)|(ξ+δ1)] -> 
    x2 ∈ [(ξ-δ1)|(ξ+δ1)] -> |f x1 - f x2| < ε).
    { intros; destruct H12, H13.
      apply Ab1''' in H12. apply Ab1''' in H13.
      apply H11 in H12. apply H11 in H13.
      pose proof (Theorem189 H12 H13); Simpl_Rin H14.
      rewrite <- (Theorem178 (f x2 - f ξ)), Theorem181 in H14.
      pose proof (Ab2 (f x1 - f ξ) (f ξ - f x2)).
      unfold Minus_R in H15. rewrite <- Theorem186 in H15.
      Simpl_Rin H15. eapply Theorem172; eauto. }
    pose proof (Pr_2a H10). pose proof H13 as H14.
    eapply Cor_supremum in H14; eauto.
    destruct H14 as [t0 [H14]], H14, H14, H14, H17 as [δ2 [H17]].
    assert ((R2min b (ξ + δ1)) ∈ R). 
    { repeat split; try apply Pr_min2.
      - destruct (Pr_min4 b (ξ + δ1)); rewrite H19; auto.
        rewrite <- (Theorem175' a); apply Theorem189; auto.
      - exists (R2min ((δ1/2) NoO_N) δ2); split; intros.
        + destruct (Pr_min4 ((δ1/2) NoO_N) δ2); rewrite H19; auto.
        + assert ((x1 ∈ [a|t0] /\ x2 ∈ [a|t0] \/ 
            x1 ∈ [(ξ - δ1)|(ξ + δ1)] /\ x2 ∈ [(ξ - δ1)|(ξ + δ1)])).
         { destruct H19, H19, H20, H20.
           destruct (Co_T167 x1 (t0 - (δ1/2) NoO_N)).
           - left; split; constructor; split; auto.
             + left; eapply Theorem172; left; split; eauto.
               apply Theorem188_1 with (Θ:=(δ1/2) NoO_N); Simpl_R.
               apply Pl_R; auto.
             + left. apply Ab1'' in H21. destruct H21.
               apply LePl_R with (z:=(δ1/2) NoO_N) in H24;
               Simpl_Rin H24. apply Theorem188_1' with
                 (Θ:=(R2min ((δ1/2) NoO_N) δ2)) in H21;
               Simpl_Rin H21. eapply Theorem172; right; split;
               eauto. eapply Theorem173; eauto.
               rewrite Theorem175, (Theorem175 x1 _).
               apply LePl_R; apply Pr_min2.
           - destruct (Co_T167 x2 (ξ - δ1)).
             + left; split; constructor; split; auto.
               * apply Ab1'' in H21; destruct H21.
                 assert (x1 < x2 + (δ1/2) NoO_N).
                 { eapply Theorem172; right; split; eauto.
                   rewrite Theorem175, (Theorem175 x2 _).
                 apply LePl_R; apply Pr_min2. }
                 apply LePl_R with (z:=(δ1/2) NoO_N) in H25.
                 assert (x1 < ξ - δ1 + (δ1/2) NoO_N).
                 { eapply Theorem172; eauto. }
                 left; eapply Theorem172; right; split; eauto.
                 left; eapply Theorem172; left; split; eauto; right.
                 unfold Minus_R. rewrite Theorem186. f_equal.
                 apply Theorem183_2'. rewrite Theorem180; Simpl_R.
                 apply Theorem188_2 with (Θ:=(δ1/2) NoO_N); Simpl_R.
               * eapply Theorem173; eauto.
                 left; eapply Theorem172; left; split; eauto.
                 left. apply Theorem183_1'.
                 repeat rewrite Theorem181.
                 apply Theorem188_1 with (Θ:=ξ); Simpl_R.
                 apply Pr_2b; auto.
             + right; split; constructor; split; auto.
               * left; apply (Theorem171 _ (t0 - (δ1/2) NoO_N) _);
                 auto. apply Theorem188_1 with (Θ:=(δ1/2) NoO_N);
                 Simpl_R. eapply Theorem172; left; split; eauto;
                 right. unfold Minus_R. rewrite Theorem186. f_equal.
                 apply Theorem183_2'. rewrite Theorem180; Simpl_R.
                 apply Theorem188_2 with (Θ:=(δ1/2) NoO_N); Simpl_R.
               * eapply Theorem173; eauto; apply Pr_min3.
               * red; auto.
               * eapply Theorem173; eauto; apply Pr_min3. }
           destruct H22, H22; auto. apply H18; auto.
           eapply Theorem172; right; split; eauto. apply Pr_min3. }
    destruct (Co_T167 (ξ + δ1) b).
    + rewrite Pr_min1, Pr_min in H19; auto.
      assert (ξ + δ1 ≦ ξ). { apply H6; auto. }
      destruct (Pl_R ξ δ1). LEGR H21 (H22 H10).
    + destruct H19, H19, H19 as [_ [δ [H19]]].
      exists δ; split; intros; auto.
      destruct H23, H23, H24, H24; apply H22; auto. 
      * constructor; split; auto. rewrite Pr_min; red; auto.
      * constructor; split; auto. rewrite Pr_min; red; auto. 
  - assert (∃ δ, δ > O /\ ∀ x1 x2, x1 ∈ [(b - δ)|b] -> 
    x2 ∈ [(b - δ)|b] -> | f x1 - f x2 | < ε).
    { pose proof (Pr_2a H3). apply H1 in H9.
      destruct H9 as [δ [H9]]. pose proof (Pr_2a H9).
    exists (R2min ((δ/2) NoO_N) (b - a)); split; intros.
  - destruct (Pr_min4 ((δ/2) NoO_N) (b - a)); rewrite H12; auto.
    apply Theorem182_1'; auto.
  - destruct H12, H12, H13, H13. 
    assert (b - x1 < δ).
    { apply Theorem188_1 with (Θ:=x1); Simpl_R.
      apply LePl_R with (z:=R2min ((δ/2) NoO_N) (b - a)) in H12;
      Simpl_Rin H12. eapply Theorem172; left; split; eauto.
      rewrite Theorem175; apply Theorem188_1'.
      pose proof (Pr_min2 ((δ/2) NoO_N) (b - a)).
      eapply Theorem172; left; split; eauto. apply Pr_2b; auto. }
    assert (b - x2 < δ).
    { apply Theorem188_1 with (Θ:=x2); Simpl_R.
      apply LePl_R with (z:=R2min ((δ/2) NoO_N) (b - a)) in H13;
      Simpl_Rin H13. eapply Theorem172; left; split; eauto.
      rewrite Theorem175; apply Theorem188_1'.
      pose proof (Pr_min2 ((δ/2) NoO_N) (b - a)).
      eapply Theorem172; left; split; eauto. apply Pr_2b; auto. }
    apply LePl_R with (z:=- x2) in H15; Simpl_Rin H15.
    apply LePl_R with (z:=- x1) in H14; Simpl_Rin H14.
    apply H10 in H16; auto. apply H10 in H17; auto.
    pose proof (Theorem189 H16 H17); Simpl_Rin H18.
    rewrite <- (Theorem178 (f x2 - f b)), Theorem181 in H18.
    pose proof (Ab2 (f x1 - f b) (f b - f x2)).
    unfold Minus_R in H19. rewrite <- Theorem186 in H19.
    Simpl_Rin H19. eapply Theorem172; eauto. }
    destruct H9 as [δ1 [H9]]. pose proof (Pr_2a H9).
    destruct (Cor_supremum _ _ G3 _ H11) as [t [H12]].
    rewrite H5 in *. destruct H12, H12, H12, H15 as [δ2 [H15]].
    exists (R2min ((δ1/2) NoO_N) δ2); split; intros.
    + destruct (Pr_min4 ((δ1/2) NoO_N) δ2); rewrite H17; auto.
    + assert ((x1 ∈ [a|t] /\ x2 ∈ [a|t] \/ 
               x1 ∈ [(b - δ1)|b] /\ x2 ∈  [(b - δ1)|b])).
      { destruct H17,H17,H18,H18, (Co_T167 x1 (t - (δ1/2) NoO_N)).
        - left; split; constructor; split; auto.
          + left; eapply Theorem172; left; split; eauto.
            apply Theorem188_1 with (Θ:=(δ1/2) NoO_N); Simpl_R.
            apply Pl_R; auto.
          + left. apply Ab1'' in H19; destruct H19.
            apply LePl_R with (z:=(δ1/2) NoO_N) in H22;
            Simpl_Rin H22. apply Theorem188_1' with
              (Θ:=(R2min ((δ1/2) NoO_N) δ2)) in H19; Simpl_Rin H19.
            eapply Theorem172; right; split; eauto.
            eapply Theorem173; eauto.
            rewrite Theorem175, (Theorem175 x1 _).
            apply LePl_R; apply Pr_min2.
         - destruct (Co_T167 x2 (b - δ1)).
           + left; split; constructor; split; auto.
             * apply Ab1'' in H19; destruct H19.
               assert (x1 < x2 + (δ1/2) NoO_N).
               { eapply Theorem172; right; split; eauto.
                 rewrite Theorem175, (Theorem175 x2 _).
                apply LePl_R; apply Pr_min2. }
               apply LePl_R with (z:=(δ1/2) NoO_N) in H23.
               assert (x1 < b - δ1 + (δ1/2) NoO_N).
               { eapply Theorem172; eauto. }
               left; eapply Theorem172; right; split; eauto.
               left; eapply Theorem172; left; split; eauto; right.
               unfold Minus_R. rewrite Theorem186. f_equal.
               apply Theorem183_2'. rewrite Theorem180; Simpl_R.
               apply Theorem188_2 with (Θ:=(δ1/2) NoO_N); Simpl_R.
             * eapply Theorem173; eauto.
               left; eapply Theorem172; left; split; eauto.
               left. apply Theorem183_1'. repeat rewrite Theorem181.
               apply Theorem188_1 with (Θ:=b); Simpl_R.
               apply Pr_2b; auto.
           + right; split; constructor; split; red; auto.
             left; apply (Theorem171 _ (t - (δ1/2) NoO_N) _); auto.
             apply Theorem188_1 with (Θ:=(δ1/2) NoO_N); Simpl_R.
             eapply Theorem172; left; split; eauto; right.
             unfold Minus_R. rewrite Theorem186. f_equal.
             apply Theorem183_2'. rewrite Theorem180; Simpl_R.
             apply Theorem188_2 with (Θ:=(δ1/2) NoO_N); Simpl_R. }
    destruct H20, H20; auto. apply H16; eauto.
    eapply Theorem172; right; split; eauto; apply Pr_min3.
Qed.
