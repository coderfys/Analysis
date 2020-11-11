(***************************************************************************)
(*   This is part of FA_Landau, it is distributed under the terms of the   *)
(*             GNU Lesser General Public License version 3                 *)
(*                (see file LICENSE for more details)                      *)
(*                                                                         *)
(*           Copyright 2020-2022: Yaoshun Fu and Wensheng Yu.              *)
(***************************************************************************)

Require Export finite reals.

Corollary uneqOP : ∀ {c}, c > O -> neq_zero c.
Proof.
  intros. destruct c; auto. inversion H.
Qed.

Corollary Pos : ∀ x y, x > O -> y > O -> (x · y) > O.
Proof.
  intros; destruct x, y; simpl; auto.
Qed.

Corollary Pos' : ∀ x y l, x > O -> y > O -> (x/y) l > O.
Proof.
  intros; destruct x, y; simpl; auto; elim H; elim H0.
Qed.

Corollary Pl_R : ∀ x y, y > O <-> x + y > x.
Proof.
  split; intros.
  - apply Theorem188_1 with (Θ:=-x); Simpl_R.
  - apply Theorem188_1' with (Θ:=-x) in H; Simpl_Rin H.
Qed.

Corollary Pl_R' : ∀ x y, y > O <-> x - y < x + y.
Proof.
  split; intros.
  - apply Theorem188_1 with (Θ:=y); Simpl_R.
    rewrite Theorem186; simpl; apply Pl_R. destruct y; auto.
  - apply Theorem188_1' with (Θ:=y) in H; Simpl_Rin H.
    rewrite Theorem186 in H; apply Pl_R in H. destruct y; auto.
Qed.

Corollary Mi_R : ∀ a b c d, (a - c) + (b - d) = (a + b) - (c + d).
Proof.
  intros. unfold Minus_R.
  rewrite Theorem180. repeat rewrite <- Theorem186.
  apply Theorem188_2 with (Θ:=d); Simpl_R. unfold Minus_R.
  do 2 rewrite Theorem186. rewrite (Theorem175 b); auto.
Qed.

Corollary Mi_R' : ∀ a b c d, (a - c) - (b - d) = (a - b) - (c - d).
Proof.
  intros. unfold Minus_R at 2 3. rewrite <- Mi_R. Simpl_R.
  unfold Minus_R at 2. f_equal.
  rewrite Theorem181, Theorem175. Simpl_R.
Qed.

Corollary Real_PZp : ∀ n m :Nat, n + m = Real_PZ (Plus_N n m).
Proof.
  intros; simpl; unfold Cut_I; rewrite <- (eq2 Theorem155_1).
  rewrite (eq1 (Theorem112_1 _ _)); Simpl_N.
Qed.

Corollary Real_TZp : ∀ n m :Nat, n · m = Real_PZ (Times_N n m).
Proof.
  intros; simpl; unfold Cut_I; rewrite <- (eq2 Theorem155_3).
  rewrite (eq1 (Theorem112_2 _ _)); Simpl_N.
Qed.

Corollary RN1 : ∀ a, a` - 1 = a.
Proof.
  intros; apply Theorem188_2 with (Θ:=1); Simpl_R.
  rewrite Real_PZp; Simpl_N.
Qed.

Corollary RN2 : ∀ a :Nat, a` - a = 1.
Proof.
  intros; apply Theorem188_2 with (Θ:=a); Simpl_R.
  rewrite Real_PZp; Simpl_N.
Qed.

Corollary RN3 : ∀ a :Nat, a + 1 = a`.
Proof.
  intros; rewrite Real_PZp; Simpl_N.
Qed.

Corollary RN4 : ∀ a :Nat, 1 + a = a`.
Proof.
  intros; rewrite Real_PZp; Simpl_N.
Qed.

Hint Rewrite RN1 RN2 RN3 RN4 : Real.

Corollary R_T2 : ∀ a, 2 · a = a + a.
Proof.
  intros. rewrite <- NPl1_, <-Real_PZp, Theorem201'; Simpl_R.
Qed.

Corollary OrderNRlt : ∀ n m :Nat, ILT_N n m -> n < m.
Proof.
  intros; simpl. apply Theorem154_1; apply Theorem111_1'; auto.
Qed.

Corollary OrderNRle : ∀ n m :Nat, ILE_N n m -> n ≦ m.
Proof.
  intros; destruct H; [left; apply OrderNRlt|subst n; red]; auto.
Qed.

Corollary NoO_N : ∀ {N :Nat}, neq_zero N.
Proof.
  intros; simpl; auto.
Qed.

Definition RdiN r (N :Nat) := (r/N) NoO_N.

Corollary RdN1 : ∀ a n, a > O -> RdiN a n > O.
Proof.
  intros. unfold RdiN. apply Pos; simpl; auto.
Qed.

Corollary RdN2 : ∀ a b n, a·(RdiN b n) = RdiN (a·b) n.
Proof.
  intros. unfold RdiN. rewrite Di_Rt; auto.
Qed.

Corollary RdN3 : ∀ a b n, (RdiN a n) + (RdiN b n) = RdiN (a+b) n.
Proof.
  intros. unfold RdiN. rewrite Di_Rp; auto.
Qed.

Corollary RdN4 : ∀ a b n, (RdiN a n) - (RdiN b n) = RdiN (a-b) n.
Proof.
  intros. unfold RdiN. rewrite Di_Rm; auto.
Qed.

Corollary Pr_2a : ∀ {z}, z > O -> (z/2) NoO_N > O.
Proof.
  intros; apply Pos; simpl; auto.
Qed.

Corollary Pr_2b : ∀ {z}, z > O -> (z/2) NoO_N < z.
Proof.
  intros; apply Theorem203_1' with (Θ:=2); Simpl_R; [|reflexivity].
  replace 2 with (Plus_N 1 1); auto.
  rewrite <- Real_PZp,  Theorem201; Simpl_R; apply Pl_R; auto.
Qed.

Corollary Pr_2c : ∀ z l, ((z/2) l) + ((z/2) l) = z.
Proof.
  intros; rewrite Di_Rp, <- (Theorem195 z),
    <- Theorem201, Real_PZp; Simpl_R.
Qed.

Hint Rewrite Pr_2c : Real.

Corollary Ab1 : ∀ x y, -x < y /\ y < x <-> |y| < x.
Proof.
  split; intros; destruct x, y; simpl in *; tauto.
Qed.

Corollary Ab1' : ∀ x y, -x ≦ y /\ y ≦ x <-> |y| ≦ x.
Proof.
  split; intros.
  - destruct H, H, H0; red.
    + left; apply -> Ab1; auto.
    + subst y; destruct x; simpl in *; destruct H; auto.
    + subst y; destruct x; simpl in *; destruct H0; auto.
    + subst y; destruct x; simpl in *; destruct H0; auto.
  - destruct H; split; red.
    + apply Ab1 in H; tauto. + apply Ab1 in H; tauto.
    + destruct x, y; simpl; auto; inversion H; auto.
    + destruct x, y; simpl; auto; inversion H; auto.
Qed.

Corollary Ab1'' : ∀ x y z, x - y < z /\ z < x + y <-> |z - x| < y.
Proof.
  split; intros.
  - destruct H; apply (Ab1 y (z - x)); split.
    + apply Theorem188_1 with (Θ:=x); Simpl_R.
      rewrite Theorem175; auto.
    + apply Theorem188_1 with (Θ:=x); Simpl_R.
      rewrite Theorem175; auto.
  - apply (Ab1 y (z - x)) in H; destruct H; split.
    + apply Theorem188_1' with (Θ:=x) in H; Simpl_Rin H.
      rewrite Theorem175 in H; auto.
    + apply Theorem188_1' with (Θ:=x) in H0; Simpl_R.
      unfold Minus_R in H0; rewrite Theorem186 in H0; Simpl_Rin H0.
      rewrite Theorem175; auto.
Qed.

Corollary Ab2 : ∀ x y, |x + y| ≦ |x| + |y|.
Proof.
  intros; destruct x, y; simpl; red; auto.
  - destruct (Ccase c c0) as [[H | H] | H]; simpl; left; auto.
    + rewrite (eq2 Theorem130).
      apply Theorem136_3 with (ζ:=c); Simpl_C.
      rewrite (eq2 Theorem131); apply Theorem133.
    + apply Theorem136_3 with (ζ:=c0); Simpl_C.
      rewrite (eq2 Theorem131); apply Theorem133.
  - destruct (Ccase c c0) as [[H | H] | H]; simpl; left; auto.
    + rewrite (eq2 Theorem130).
      apply Theorem136_3 with (ζ:=c); Simpl_C.
      rewrite (eq2 Theorem131); apply Theorem133.
    + apply Theorem136_3 with (ζ:=c0); Simpl_C.
      rewrite (eq2 Theorem131); apply Theorem133.
Qed.

Corollary Ab2' : ∀ x y, |x| - |y| ≦ |x - y|.
Proof.
  intros; destruct (Ab2 (x-y) y); Simpl_Rin H.
  - left; apply Theorem188_1 with (Θ:=|y|); Simpl_R.
  - right; apply Theorem188_2 with (Θ:=|y|); Simpl_R.
Qed.

Corollary Ab3 : ∀ x, x > O -> |x| = x.
Proof.
  intros; destruct x; simpl in *; auto; elim H.
Qed.

Corollary Ab3' : ∀ x, O ≦ x -> |x| = x.
Proof.
  intros. destruct H, x; inversion H; reflexivity.
Qed.

Corollary Ab3'' : ∀ x, x < O -> |x| = -x.
Proof.
  intros. destruct x; inversion H; reflexivity.
Qed.

Corollary Ab3''' : ∀ x, x ≦ O -> |x| = -x.
Proof.
  intros. destruct H, x; inversion H; reflexivity.
Qed.

Corollary Ab4 : ∀ x y, x > y -> |x - y| = x - y.
Proof.
  intros; destruct x, y; simpl in *; try tauto;
  destruct (Ccase c c0) as [[H0 | H0] | H0]; simpl; auto; LGC H H0.
Qed.

Corollary Ab5 : ∀ x y, y ≦ x -> |x - y| = x - y.
Proof.
  intros; destruct H.
  - apply Ab4; auto. - rewrite H; simpl; Simpl_R.
Qed.

Corollary Ab6 : ∀ x y, y ≦ x -> |y - x| = x - y.
Proof.
  intros; rewrite <- Theorem178, Theorem181; apply Ab5; auto.
Qed.

Corollary Ab7 : ∀ x, x ≦ |x|.
Proof.
  intros; destruct x; red; simpl; auto.
Qed.

Corollary Ab8 : ∀ x, x <> O -> |x| > O.
Proof.
  intros. destruct x; simpl; tauto.
Qed.

Corollary Ab8' : ∀ x y, x <> y -> |x - y| > O.
Proof.
  intros. apply Ab8; intro; apply H, Theorem182_2; auto.
Qed.

Corollary Ab1''' : ∀ x y z, x-y ≦ z /\ z ≦ x+y <-> |z-x| ≦ y.
Proof.
  split; intros.
  - destruct H, H, H0; try subst z; Simpl_R.
    + left; apply Ab1''; auto.
    + apply Pl_R' in H. destruct y; inversion H; red; auto.
    + unfold Minus_R; rewrite (Theorem175 x _); Simpl_R.
      apply Pl_R' in H0. destruct y; inversion H0; red; auto.
    + unfold Minus_R; rewrite (Theorem175 x _); Simpl_R.
      apply Theorem183_2 in H0.
      rewrite Theorem181,Theorem175,Theorem180 in H0; Simpl_Rin H0.
      apply Theorem188_2' with (Θ:=x) in H0; Simpl_Rin H0.
      rewrite Theorem178; red; destruct y; auto.
  - destruct H; split; red.
    + apply Ab1'' in H; tauto. + apply Ab1'' in H; tauto.
    + destruct (Theorem167 x z) as [H0 | [H0 | H0]].
      * subst z; Simpl_Rin H; simpl in H. rewrite <- H; Simpl_R.
      * rewrite Ab4 in H; auto; left.
        assert (y > O). { rewrite <- H; apply Theorem182_1'; auto. }
        apply Theorem188_1 with (Θ:=y); Simpl_R.
        rewrite <- (Theorem175' x). apply Theorem189; auto.
      * rewrite <- Theorem178, Theorem181, Ab4 in H; auto; right.
        apply Theorem188_2 with (Θ:=y); Simpl_R.
        rewrite Theorem175, <- H; Simpl_R.
    + destruct (Theorem167 x z) as [H0 | [H0 | H0]].
      * subst z; Simpl_Rin H; simpl in H. rewrite <- H; Simpl_R.
      * right; rewrite Theorem175. apply Theorem188_2 with (Θ:=-x);
        Simpl_R. apply Theorem182_1' in H0. rewrite <- H.
        destruct (z-x); inversion H0; auto.
      * left; rewrite Theorem175. apply Theorem188_3 with (Θ:=-x);
        Simpl_R. apply Theorem182_3' in H0. eapply Theorem171;
        eauto; rewrite <- H. destruct (z-x); inversion H0; auto.
Qed.

Corollary Ab9 : ∀ x y, (∀ z, z > O -> |x - y| ≦ z) -> x = y.
Proof.
  intros; destruct (Theorem167 x y) as [H0 | [H0 | H0]]; auto.
  - rewrite <- Theorem178, Theorem181 in H.
    rewrite Ab4 in H; auto. apply Theorem182_1' in H0.
    pose proof (Pr_2a H0). apply H in H1; destruct H1.
    + LGR H1 (Pr_2b H0). + EGR H1 (Pr_2b H0).
  - rewrite Ab4 in H; auto. apply Theorem182_1' in H0.
    pose proof (Pr_2a H0). apply H in H1; destruct H1.
   + LGR H1 (Pr_2b H0). + EGR H1 (Pr_2b H0).
Qed.

Fixpoint Pow x n :=
  match n with
   | 1 => x
   | m` => (Pow x m) · x
  end.

Notation "x ^ n" := (Pow x n).

Corollary Pow1 : ∀ x, x^1 = x.
Proof.
  intros; simpl; auto.
Qed.

Corollary PowS : ∀ x n, x^n` = x^n · x.
Proof.
  intros; simpl; auto.
Qed.

Corollary powO : ∀ n, O^n = O.
Proof.
  intros. destruct n; simpl; Simpl_R.
Qed.

Corollary pow1 : ∀ n, 1^n = 1.
Proof.
  intros. induction n; auto. simpl. rewrite IHn; Simpl_R.
Qed.

Corollary square_p1 : ∀ a, O ≦ a^2.
Proof.
  intros; red; destruct a; simpl; auto.
Qed.

Corollary square_p2 : ∀ a, |a|^2 = a^2.
Proof.
  intros. destruct a; simpl; auto.
Qed.

Corollary square_p3 : ∀ a, (-a)^2 = a^2.
Proof.
  intros. destruct a; simpl; auto.
Qed.

Corollary powT : ∀ a b n, a^n · b^n = (a·b)^n.
Proof.
  induction n; simpl; auto.
  rewrite (Theorem194 _ b), Theorem199, <- (Theorem199 a).
  rewrite (Theorem194 (a·b)), <- Theorem199, IHn; auto.
Qed.

Corollary powm : ∀ a n, (-a)^n = (-(1))^n · a^n.
Proof.
  induction n; intros; Simpl_R. repeat rewrite PowS.
  rewrite IHn, Theorem199, Theorem199, Theorem197''; Simpl_R.
Qed.

Corollary Archimedes : ∀ x, ∃ N:Nat, x < N.
Proof.
  intros; destruct x.
  - exists 1; reflexivity.
  - ENC X c H. destruct (Theorem115 1 X) as [n H0]; Simpl_Prin H0.
    pose proof (Theorem119 _ _ _ H H0).
    apply Theorem158_2 in H1; apply Theorem124 in H1.
    assert (IGT_C (Plus_N n 1) c).
    { eapply Theorem127; left; split; eauto.
      apply Theorem154_3; apply Theorem111_3'; red; eauto. }
    exists (Plus_N n 1); simpl; auto.
  - exists 1; reflexivity.
Qed.

Corollary LEminus : ∀ x y, x ≦ y <-> -y ≦ -x.
Proof.
  split; intros; destruct H.
  - left; apply Theorem183_1; auto.
  - right; apply Theorem183_2; auto.
  - left; apply Theorem183_1'; auto.
  - right; apply Theorem183_2'; auto.
Qed.

Corollary Co_T167 : ∀ x y, x ≦ y \/ y < x.
Proof.
  intros; destruct (Theorem167 x y) as [H | [H | H]];
  unfold ILE_R; auto.
Qed.

Corollary Rcase : ∀ x y, {x ≦ y} + {y < x}.
Proof.
  intros. destruct (classicT (x ≦ y)); auto. right.
  destruct (Co_T167 x y); tauto.
Qed.

Corollary Rcase2 : ∀ x y, x ≦ y \/ y ≦ x.
Proof.
  intros; destruct (Theorem167 x y) as [H | [H | H]];
  unfold ILE_R; auto.
Qed.

Definition R2max x y := ((x + y + |x - y|)/2) NoO_N.
Definition R2min x y := ((x + y - |x - y|)/2) NoO_N.

Corollary Pr_min : ∀ x y, x ≦ y -> (R2min x y = x).
Proof.
  intros; unfold R2min; rewrite Ab6; auto.
  unfold Minus_R; rewrite Theorem180.
  rewrite Theorem186, <- (Theorem186 _ (-y) _); Simpl_R.
  pattern x at 1 2; rewrite <- Theorem195.
  rewrite <- Theorem201, Real_PZp; Simpl_R.
Qed.

Corollary Pr_min1 : ∀ x y, (R2min x y) = (R2min y x).
Proof.
  intros; unfold R2min.
  rewrite (Theorem175 x y), <- Theorem178, Theorem181; auto.
Qed.

Corollary Pr_min1' : ∀ x y z,
  R2min (R2min x y) z = R2min x (R2min y z).
Proof.
  intros; destruct (Rcase2 x y), (Rcase2 y z).
  - rewrite (Pr_min y z), (Pr_min x y); auto.
    rewrite Pr_min; auto. eapply Theorem173; eauto.
  - rewrite (Pr_min1 y z), (Pr_min z y), (Pr_min x y); auto.
  - rewrite (Pr_min1 x y), (Pr_min1 x (R2min y z)); auto.
    repeat rewrite (Pr_min y _); auto.
  - rewrite (Pr_min1 x y), (Pr_min1 y z).
    rewrite (Pr_min y x), (Pr_min z y); auto.
    rewrite Pr_min1, (Pr_min1 x z). repeat rewrite Pr_min; auto.
    eapply Theorem173; eauto.
Qed.

Corollary Pr_min2 : ∀ x y, (R2min x y) ≦ x.
Proof.
  intros; destruct (Rcase2 x y); red.
  - rewrite Pr_min; auto. - rewrite Pr_min1, Pr_min; auto.
Qed.

Corollary Pr_min3 : ∀ x y, (R2min x y) ≦ y.
Proof.
  intros; rewrite Pr_min1; apply Pr_min2.
Qed.

Corollary Pr_min4 : ∀ x y, (R2min x y) = x \/ R2min x y = y.
Proof.
  intros; destruct (Rcase2 x y).
  - left; apply Pr_min; auto.
  - right; rewrite Pr_min1; apply Pr_min; auto.
Qed.

Corollary Pr_max : ∀ x y, x ≦ y -> (R2max x y = y).
Proof.
  intros; unfold R2max; rewrite Ab6; auto.
  rewrite Theorem175, <- Theorem186; Simpl_R.
  pattern y at 1 2; rewrite <- Theorem195.
  rewrite <- Theorem201, Real_PZp; Simpl_R.
Qed.

Corollary Pr_max1 : ∀ x y, (R2max x y) = (R2max y x).
Proof.
  intros; unfold R2max.
  rewrite (Theorem175 x y), <- Theorem178, Theorem181; auto.
Qed.

Corollary Pr_max1' : ∀ x y z,
  R2max (R2max x y) z = R2max x (R2max y z).
Proof.
  intros; destruct (Rcase2 x y), (Rcase2 y z).
  - rewrite (Pr_max y z), (Pr_max x y); auto.
    repeat rewrite Pr_max; auto. eapply Theorem173; eauto.
  - rewrite (Pr_max1 y z), (Pr_max z y),
      (Pr_max x y), Pr_max1, Pr_max; auto.
  - rewrite (Pr_max1 x y), (Pr_max1 x (R2max y z)); auto.
    repeat rewrite (Pr_max y _); auto. apply Pr_max1.
  - rewrite (Pr_max1 x y), (Pr_max1 y z).
    rewrite (Pr_max y x), (Pr_max z y); auto.
    rewrite Pr_max1, (Pr_max1 x y). repeat rewrite Pr_max; auto.
    eapply Theorem173; eauto.
Qed.

Corollary Pr_max2 : ∀ x y, x ≦ (R2max x y).
Proof.
  intros; destruct (Rcase2 x y).
  - rewrite Pr_max; auto.
  - rewrite Pr_max1, Pr_max; red; auto.
Qed.

Corollary Pr_max3 : ∀ x y, y ≦ (R2max x y).
Proof.
  intros; rewrite Pr_max1; apply Pr_max2.
Qed.

Corollary Pr_max4 : ∀ x y, (R2max x y) = x \/ R2max x y = y.
Proof.
  intros; destruct (Rcase2 x y).
  - right; apply Pr_max; auto.
  - left; rewrite Pr_max1; apply Pr_max; auto.
Qed.

Definition Boundup_Ens y A := ∀ x, x ∈ A -> x ≦ y.
Definition Bounddown_Ens y A := ∀ x, x ∈ A -> y ≦ x.

Definition EnsMax x X := x ∈ X /\ (Boundup_Ens x X).
Definition EnsMin x X := x ∈ X /\ (Bounddown_Ens x X).

Corollary FinMin : ∀ R, fin R -> No_Empty R -> ∃ r, EnsMin r R.
Proof.
  intros; destruct H as [n [f H]]; generalize dependent R;
  generalize dependent f; induction n; intros.
  - destruct H0 as [r H0].
    apply H in H0; destruct H0, H as [_ [_ [_ [H _]]]].
    apply H in H0; destruct H0; N1F H0.
  - rename H0 into H1; rename H into H0; rename IHn into H.
    rename n into m; assert (m ∈ (Fin_En m`)).
    { constructor; red; exists 1; Simpl_N. }
    apply H0 in H2; destruct H2 as [x H2].
    destruct (classic (∃ y, y <> x /\ y ∈ R)) as [H3 | H3].
    + destruct H3 as [y H3], H3.
      set (R1 := /{ r | r ∈ R /\ r <> x /}).
      set (N1 := /{ n | ∃ r1, r1 ∈ R1 /\ f n r1 /}).
      assert (Surjection (Fin_En m) R1 (RelAB N1 (Fin_En m) y f)).
      { destruct H0, H5, H6, H7; repeat split; try red; intros. 
        - destruct H9, H10; try tauto.
          + eapply H0; eauto.  + subst y0 z; auto.
        - destruct (classic (x0 ∈ N1)).
          + destruct H9, H5 with x0.
            * constructor. eapply Theorem15; eauto.
              red; exists 1; Simpl_N.
            * exists x1; constructor; auto.
          + exists y; constructor 2; eauto.
        - destruct H9, H9, H6 with y0; auto.
          exists x0; constructor; auto.
          constructor; exists y0; split; auto. constructor; auto.
        - destruct H9.
          + destruct H9, H9, H9, H9, H9.
            apply (H0 _ _ _ H10) in H11; subst x1.
            pose proof H10; apply H7 in H10; destruct H10.
            apply Theorem26 in H10. destruct H10; auto.
            subst x0; elim H12; eapply H0; eauto.
          + destruct H10; auto.
        - destruct H9. 
          + eapply H8; eauto. + subst y0; auto.
        - subst y0; destruct H9.
          + destruct H9,H9,H9,H9,H9. apply H12; eapply H0; eauto.
          + subst x; auto. }
    assert (No_Empty R1). { red; exists y; constructor; auto. }
    destruct (H _ _ H5 H6) as [r1 H7], H7.
    assert (R1 ⊂ R). { red; intros; destruct H9; tauto. }
    assert (R = Union R1 (/{ r | r = x /})).
    { apply ens_ext; split; intros.
      - destruct (classic (x0 = x)).
        + constructor; right; constructor; auto.
        + constructor; left; constructor; auto.
      - destruct H10, H10; auto. destruct H10. subst x0.
        eapply H0; eauto. }
    destruct (Rcase2 r1 x).
    * exists r1; split; auto; red; intros.
      rewrite H10 in H12. destruct H12, H12.
      { apply H8 in H12; auto. }
      { destruct H12; subst x0; auto. }
    * apply H0 in H2. exists x; split; auto; red; intros.
      rewrite H10 in H12. destruct H12, H12.
      { apply H8 in H12; eapply Theorem173; eauto. }
      { destruct H12; subst x0; red ;auto. }
  + apply H0 in H2. exists x; split; auto; red; intros; red.
    destruct (Theorem167 x0 x) as [H5 | [H5 | H5]]; auto.
    elim H3; exists x0; split; auto.
    intro; eapply OrdR2; eauto.
Qed.

Inductive RelMax (f :Relation Nat Real) n y : Prop :=
  | M_in : f n (-y) -> RelMax f n y.

Corollary FinMax : ∀ R, fin R -> No_Empty R -> ∃ r, EnsMax r R.
Proof.
  intros; set (R' := /{ r | (-r) ∈ R /} ).
  destruct H as [n [f H]], H, H1, H2, H3.
  assert (fin R').
  { red; exists n, (RelMax f); repeat split; try red; intros.
    - destruct H5, H6. apply Theorem183_2'. eapply H; eauto.
    - destruct H1 with x; auto.
      exists (- x0); constructor; Simpl_R.
    - destruct H5, H2 with (-y); auto. exists x; constructor; auto.
    - destruct H5. apply H3 in H5. destruct H5; auto.
    - destruct H5. apply H4 in H5; auto. }
  assert (No_Empty R'). 
  { destruct H0; exists (- x); constructor; Simpl_R. }
  destruct (FinMin _ H5 H6) as [M H7], H7, H7.
  exists (- M); red; split; auto; red; intros.
  apply LEminus; Simpl_R. apply H8; constructor; Simpl_R.
Qed.

Definition mid x y := RdiN (x + y) 2.

Corollary Mid_P : ∀ x y, y > x -> y > mid x y.
Proof.
  intros; apply Theorem203_1' with (Θ:=2); simpl; auto.
  unfold mid, RdiN; Simpl_R.
  rewrite <- NPl1_, <-Real_PZp, Theorem201; Simpl_R.
  apply Theorem188_1'; auto.
Qed.

Corollary Mid_P' : ∀ x y, y > x -> x < mid x y.
Proof.
  intros; apply Theorem203_1' with (Θ:=2); simpl; auto.
  unfold mid, RdiN; Simpl_R; rewrite Theorem175.
  rewrite <- NPl1_, <-Real_PZp, Theorem201; Simpl_R.
  apply Theorem188_1'; auto.
Qed.

Corollary Midp1 : ∀ x y l, mid x y - ((y-x)/2) l = x.
Proof.
  intros. unfold mid, RdiN. rewrite (proof_irr l NoO_N), Di_Rm.
  unfold Minus_R. rewrite Theorem180, <- Theorem186. Simpl_R.
  rewrite <- Di_Rp. Simpl_R.
Qed.

Corollary Midp2 : ∀ x y l, y - ((y-x)/2) l = mid x y.
Proof.
  intros. pose proof (Midp1 x y l).
  apply Theorem188_2' with (Θ:=((y-x)/2) l) in H; Simpl_Rin H.
  rewrite H; apply Theorem188_2 with (Θ:=((y-x)/2) l); Simpl_R.
  rewrite Theorem186; Simpl_R.
Qed.

Corollary MiR : ∀ x y z l l1,
  (z - (x/(y·2)) l) - (x/(y·2)) l = z - (x/y) l1.
Proof.
  intros; unfold Minus_R; rewrite Theorem186,<- Theorem180; Simpl_R.
  f_equal. rewrite Di_Rp, <- (RTi1_ x), <- Theorem201'.
  rewrite Real_PZp; Simpl_N. apply ROv_uni.
  rewrite <- Di_Rt, <- Theorem199, Theorem194; Simpl_R.
Qed.

Definition oo x y := /{ z | x < z /\ z < y /}.
Definition cc x y := /{ z | x ≦ z /\ z ≦ y /}.
Definition neighO x y := /{ z | (x - y) < z /\ z < (x + y) /}.
Definition neighC x y := /{ z | (x - y) ≦ z /\ z ≦ (x + y) /}.

Notation " ( x | y ) " := (oo x y).
Notation " [ x | y ] " := (cc x y).
Notation " ( x  |- y ) " := (neighO x y).
Notation " [ x  |- y ] " := (neighC x y).










