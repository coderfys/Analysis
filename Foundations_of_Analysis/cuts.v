(***************************************************************************)
(*   This is part of FA_Landau, it is distributed under the terms of the   *)
(*             GNU Lesser General Public License version 3                 *)
(*                (see file LICENSE for more details)                      *)
(*                                                                         *)
(*           Copyright 2020-2022: Yaoshun Fu and Wensheng Yu.              *)
(***************************************************************************)

(* CUTS *)

(* SECTION I Definition *)

Require Export frac.

Definition Cut_p1 (E :Ensemble Rat) := (∃ X, X ∈ E) /\ ∃ Y, ~ Y ∈ E.
Definition Cut_p2 (E :Ensemble Rat) := ∀ X, X ∈ E -> ∀ Y, Y < X -> Y ∈ E.
Definition Cut_p3 (E :Ensemble Rat) := ∀ X, X ∈ E -> ∃ Y, Y ∈ E /\ Y > X.

Lemma D28_p1 : ∀ E, Cut_p1 E <-> (∃ X, X ∈ E) /\ ~ (∀ Y, Y ∈ E).
Proof.
  split; intros; split; try apply H; destruct H.
  - intro; destruct H0; auto.
  - apply not_all_ex_not in H0; auto.
Qed.

Lemma D28_p2 : ∀ E, Cut_p2 E <-> (∀ X Y, X ∈ E -> ~ Y ∈ E -> X < Y).
Proof.
 split; intros.
  - red in H; destruct (Theorem81 X Y) as [H2 | [H2 | H2]]; auto.
    + rewrite (eq1 H2) in H0; contradiction.
    + eapply H in H0; eauto; contradiction.
  - red; intros; Absurd; eapply H in H0; eauto; LGPr H0 H1.
Qed.

Lemma D28_p3 : ∀ E, Cut_p3 E <-> ~ (∃ Y, Y ∈ E /\ (∀ X, X ∈ E -> X ≦ Y)).
Proof.
  split; intros.
  - intro; destruct H0, H0, H with x; auto; destruct H2.
    apply H1 in H2; destruct H2; try LGPr H2 H3; try EGPr H2 H3.
  - red; intros; Absurd.
    elim H; exists X; split; intros; auto; red.
    destruct (Theorem81 X0 X) as [H3 | [H3 | H3]]; try tauto.
    elim H1; eauto.
Qed.

Record Cut := mkcut {
  CR :> Ensemble Rat;
  cutp1 : Cut_p1 CR;
  cutp2 : Cut_p2 CR;
  cutp3 : Cut_p3 CR }.

Definition upper_class R := /{ Y | ∀ X, X ∈ R -> Y > X /}.

Definition Num_L X (ξ :Cut) := X ∈ ξ.

Definition Num_U X (ξ :Cut) := ~ X ∈ ξ.

Definition Equal_C (ξ η :Cut) :=(∀ X, X ∈ ξ <-> X ∈ η).
Definition No_Equal_C (ξ η :Cut) := ~ Equal_C ξ η.

Notation " ξ ≈ η " := (Equal_C ξ η ) (at level 60).

Corollary eq2 : ∀ {ξ η :Cut}, ξ ≈ η -> ξ = η.
Proof.
  intros; assert (Same_Ensemble ξ η).
  { red; red in H; auto. }
  apply ens_ext in H0; destruct ξ, η; simpl in H0; subst CR0.
  rewrite (proof_irr _ cutp7), (proof_irr _ cutp8), 
  (proof_irr _ cutp9); auto.
Qed.

Theorem Theorem116 : ∀ ξ, ξ ≈ ξ.
Proof.
  intros; red; intro; split; intro; auto.
Qed.

Theorem Theorem117 : ∀ ξ η, ξ ≈ η -> η ≈ ξ.
Proof.
  intros; red in H; red; intros; split; intros; apply H; auto.
Qed.

Theorem Theorem118 : ∀ ξ η ζ, ξ ≈ η -> η ≈ ζ -> ξ ≈ ζ.
Proof.
  intros; red in H; red in H0; red; intros.
  split; intros; try apply H0; try apply H; try apply H0; auto.
Qed.

Lemma Lemma_T119 : ∀ (ξ :Cut) X Y, X ∈ ξ -> ~ Y ∈ ξ -> X < Y.
Proof.
  intros; destruct ξ; apply (D28_p2 CR0); auto.
Qed.

Theorem Theorem119 : ∀ X X1 ξ, Num_U X ξ -> X1 > X -> Num_U X1 ξ.
Proof.
  intros; intro; red in H.
  eapply Lemma_T119 in H; eauto; LGPr H H0.
Qed.

Theorem Theorem120 : ∀ X X1 ξ, Num_L X ξ -> X1 < X -> Num_L X1 ξ.
Proof.
  intros; red in H; red; destruct ξ.
  unfold Cut_p2 in cutp5; apply cutp5 with X; auto.
Qed.

(* SECTION II Ordering *)

Definition IGT_C ξ η := (∃ X, Num_L X ξ /\ Num_U X η).
Notation " x > y " := (IGT_C x y).

Definition ILT_C ξ η := (∃ X, Num_L X η /\ Num_U X ξ).
Notation " x < y " := (ILT_C x y).

Theorem Theorem121 : ∀ ξ η, ξ > η -> η < ξ.
Proof.
  intros; auto.
Qed.

Theorem Theorem122 : ∀ ξ η, ξ < η -> η > ξ.
Proof.
  intros; auto.
Qed.

Lemma OrdC1: ∀ {ξ η}, ξ ≈ η -> ξ > η -> False.
Proof.
  intros; red in H; red in H0.
  destruct H0 as [X H0], H0; red in H0, H1.
  apply H1; apply H; auto.
Qed.

Lemma OrdC2: ∀ {ξ η}, ξ ≈ η -> ξ < η -> False.
Proof.
  intros; red in H; red in H0.
  destruct H0 as [X H0], H0; red in H0, H1.
  apply H1; apply H; auto.
Qed.

Lemma OrdC3: ∀ {ξ η}, ξ < η -> ξ > η -> False.
Proof.
  intros; red in H; red in H0.
  destruct H as [X H], H; red in H; red in H1.
  destruct H0 as [Y H0]; destruct H0; red in H0; red in H2.
  assert (ILT_Pr X Y); try eapply Lemma_T119; eauto.
  assert (ILT_Pr Y X); try eapply Lemma_T119; eauto; LGPr H3 H4.
Qed.

Ltac EGC H H1 := destruct (OrdC1 H H1).
Ltac ELC H H1 := destruct (OrdC2 H H1).
Ltac LGC H H1 := destruct (OrdC3 H H1).

Corollary ex_In_C : ∀ ξ, ∃ a, Num_L a ξ.
Proof.
  intros; destruct ξ as [CR [p1 p2]]; auto.
Qed.

Corollary ex_NoIn_C : ∀ ξ, ∃ a, Num_U a ξ.
Proof.
  intros; destruct ξ as [CR [p1 p2]]; auto.
Qed.

Ltac EC X ξ H := destruct (ex_In_C ξ) as [X H].
Ltac ENC X ξ H := destruct (ex_NoIn_C ξ) as [X H].

Theorem Theorem123 : ∀ ξ η, ξ < η \/ ξ > η \/ ξ ≈ η.
Proof.
  intros; destruct (classic (ξ ≈ η)) as [H | H]; auto.
  unfold Equal_C in H; apply not_all_ex_not in H.
  destruct H as [X H], (classic (X ∈ ξ)), (classic (X ∈ η)).
  - elim H; split; intros; auto.
  - right; left; red; eauto.
  - left; red; eauto.
  - elim H; split; intros; contradiction.
Qed.

Definition IGE_C ξ η := ξ > η \/ ξ ≈ η.
Notation " ξ ≧ η " := (IGE_C ξ η) (at level 55).

Definition ILE_C ξ η := ξ < η \/ ξ ≈ η.
Notation " ξ ≦ η " := (ILE_C ξ η) (at level 55).

Theorem Theorem124 : ∀ ξ η, ξ ≧ η -> η ≦ ξ.
Proof.
  intros; red; red in H; destruct H; try tauto.
  apply Theorem117 in H; auto.
Qed.

Theorem Theorem125 : ∀ ξ η, ξ ≦ η -> η ≧ ξ.
Proof.
  intros; red; red in H; destruct H; try tauto.
  apply Theorem117 in H; auto.
Qed.

Theorem Theorem126: ∀ ξ η ζ, ξ < η -> η < ζ -> ξ < ζ.
Proof.
  intros; destruct H as [X H], H, H0 as [Y H0], H0.
  assert (ILT_Pr X Y); try eapply Lemma_T119; eauto.
  apply Theorem83 in H3.
  apply Theorem119 with (ξ:=ξ) in H3; auto.
  red; red in H3; eauto.
Qed.

Theorem Theorem127 : ∀ ξ η ζ,
  (ξ ≦ η /\ η < ζ) \/ (ξ < η /\ η ≦ ζ) -> ξ < ζ.
Proof.
  intros; destruct H as [[[H | H] H0] | [H [H0 | H0]]].
  - eapply Theorem126; eauto.
  - red in H0; destruct H0 as [X H0], H0.
    red; exists X; split; auto. red; red in H; red in H0; intro.
    apply H in H2; contradiction.
  - eapply Theorem126; eauto.
  - red in H; destruct H as [X H], H.
    red; exists X; split; auto. red; red in H1; red in H0.
    apply H0 in H; auto.
Qed.

Theorem Theorem128: ∀ ξ η ζ, ξ ≦ η -> η ≦ ζ -> ξ ≦ ζ.
Proof.
  intros; red in H; red in H0; destruct H.
  - left; eapply Theorem127; eauto.
  - destruct H0.
    + left; apply Theorem127 with (η:=η); auto; unfold ILE_C; auto.
    + right; eapply Theorem118; eauto.
Qed.

(* SECTION III Addition *)

Definition plus_C ξ η := 
  /{ Z | ∃ X Y, Num_L X ξ /\ Num_L Y η /\ Z ≡ (X + Y) /}.

Theorem Theorem129_2 : ∀ ξ η X X0, ∀ Z, Z ∈ (plus_C ξ η) 
  -> Num_U X ξ /\ Num_U X0 η -> ~ Z ≡ (X + X0).
Proof.
  intros; destruct H, H as [x [x0 [H [H1 H2]]]], H0; intro.
  assert (ILT_Pr x X); try eapply Lemma_T119; eauto.
  assert (ILT_Pr x0 X0); try eapply Lemma_T119; eauto.
  rewrite (eq1 H4) in H2; EGPr H2 (Theorem98 H5 H6).
Qed.

Theorem Theorem129_1 : ∀ ξ η, 
  Cut_p1 (plus_C ξ η) /\ Cut_p2 (plus_C ξ η) /\ Cut_p3 (plus_C ξ η).
Proof.
  intros; EC X ξ H;ENC X1 ξ H0;EC Y η H1;ENC Y1 η H2; repeat split.
  - exists (X + Y); constructor; exists X, Y; repeat split; autoPr.
  - exists (X1 + Y1); intro.
    eapply Theorem129_2; eauto; autoPr.
  - destruct H3, H3 as [Z [U [H3 [H5 H6]]]].
    exists (Z · (Y0/(Z + U))), (U · (Y0/(Z + U))).
    assert (ILT_Pr (Y0/(Z + U)) 1).
    { apply Theorem106_3 with (Z:=(Z + U));
      rewrite <- (eq1 H6); Simpl_Pr. }
    repeat split.
    + red. destruct ξ. apply cutp2 with Z; auto.
      apply Theorem105_3 with (Z:=Z) in H7; Simpl_Prin H7.
      rewrite (eq1 Theorem102); auto.
    + red; destruct η; apply cutp2 with U; auto.
      apply Theorem105_3 with (Z:=U) in H7; Simpl_Prin H7.
      rewrite (eq1 Theorem102); auto.
    + rewrite <- (eq1 Theorem104'); Simpl_Pr; autoPr.
  - red; intros; destruct H3,H3 as [Z [U [H3 [H5 H6]]]]; red in H3.
    destruct ξ; apply cutp3 in H3; destruct H3 as [Z1 [H3 H7]].
    exists (Z1 + U); split.
    + constructor; exists Z1, U; repeat split; autoPr.
    + rewrite (eq1 H6); apply Theorem96_1; auto.
Qed.

Definition Plus_C (ξ η :Cut) : Cut.
  apply mkcut with (plus_C ξ η); apply Theorem129_1.
Defined.
Notation " X + Y " := (Plus_C X Y).

Theorem Theorem130 : ∀ {ξ η :Cut}, (ξ + η) ≈ (η + ξ).
Proof.
  intros; red; intros. split; intros;
  destruct H, H as [X0 [Y0 [H [H0 H1]]]]; constructor;
  exists Y0, X0; repeat split; try rewrite (eq1 Theorem92); auto.
Qed.

Theorem Theorem131 : ∀ {ξ η ζ}, ((ξ + η) + ζ) ≈ (ξ + (η + ζ)).
Proof.
  intros; red; intros; split; intros; 
  destruct H, H as [X0 [Y0 [H [H0 H1]]]].
  - red in H; destruct H, H as [X2 [Y2 [H [H2 H3]]]]; constructor.
    exists X2, (Plus_Pr Y2 Y0); repeat split; auto.
    + exists Y2, Y0; repeat split; autoPr.
    + rewrite (eq1 H3), (eq1 Theorem93) in H1; auto.
  - destruct H0, H0 as [X2 [Y2 [H0 [H2 H3]]]]; constructor.
    exists (Plus_Pr X0 X2), Y2; repeat split; auto.
    + exists X0, X2; repeat split; autoPr.
    + rewrite (eq1 H3), <- (eq1 Theorem93) in H1; auto.
Qed.

Theorem Theorem132 : ∀ (A :Rat) ξ, 
  ∃ U X l, Num_U U ξ /\ Num_L X ξ /\ A ≡ ((U - X) l).
Proof.
  intros; EC X ξ H; ENC Y ξ H0. pose proof (Lemma_T119 _ _ _ H H0).
  set (ℳ:=/{ n | ~ (Plus_Pr ((Int n) · A) X) ∈ ξ /}).
  assert (No_Empty ℳ).
  { destruct (Theorem115 A ((Y - X) H1)) as [n H2].
    red; exists n; constructor; intro.
    apply Theorem96_1 with (Z:=X) in H2; Simpl_Prin H2.
    apply Theorem119 with (ξ:=ξ) in H2; auto. }
  apply Theorem27 in H2; destruct H2 as [u [H2 H3]], H2.
  destruct u.
  - exists (Plus_Pr X A), X, (Theorem94 X A).
    Simpl_Prin H2; repeat split; try rewrite (eq1 Theorem92); auto.
    apply Theorem97_2 with (Z:=X); Simpl_Pr; autoPr.
  - pose proof (Theorem94 (Plus_Pr (u · A) X) A).
    rewrite (eq1 Theorem93), (eq1 (@Theorem92 X A)) in H4.
    rewrite <- (eq1 Theorem93) in H4.
    pattern A at 2 in H4; rewrite <- PrTi1_ in H4.
    rewrite <- (eq1 Theorem104') in H4; Simpl_Prin H4. 
    exists (Plus_Pr (u` · A) X), (Plus_Pr (u · A) X), H4.
    assert (~ (ILE_N u` u)); try intro.
    { pose proof (Theorem18 u 1); Simpl_Nin H6.
      destruct H5; try LGN H5 H6; EGN H5 H6. }
    specialize H3 with u; pose proof (inp _ _ H3 H5).
    assert ((Plus_Pr (u · A) X) ∈ ξ).
    { Absurd; elim H6; constructor; auto. }
    repeat split; auto.
    apply Theorem97_2 with (Z:=(Plus_Pr (u · A) X)); Simpl_Pr.
    rewrite <- PrPl_1, (eq1 Theorem104'), <- (eq1 Theorem93).
    Simpl_Pr. rewrite (eq1 (@ Theorem92 A (u · A))); autoPr.
Qed.

Theorem Theorem133 : ∀ ξ η, ξ + η > ξ.
Proof.
  intros; EC Y η H.
  destruct (Theorem132 Y ξ) as [X [Y0 [H0 [H1 [H2 H3]]]]].
  red; exists (Plus_Pr Y0 Y); repeat split.
  - exists Y0, Y; repeat split; autoPr.
  - apply Theorem96_2 with (Z:=Y0) in H3; Simpl_Prin H3.
    rewrite (eq1 Theorem92), (eq1 H3); auto.
Qed.

Theorem Theorem134 : ∀ ξ η ζ, ξ > η -> ξ + ζ > η + ζ.
Proof.
  intros; red in H; destruct H as [X [H H0]]; red in H.
  destruct ξ; apply cutp3 in H; destruct H as [Y [H H1]],
    (Theorem132 (Minus_Pr Y X H1) ζ) as [Z [U [H2 [H3 [H4 H5]]]]].
  red; exists (Plus_Pr X Z); repeat split.
  - exists Y, U; repeat split; auto.
    apply Theorem96_2 with (Z:=U) in H5; Simpl_Prin H5.
    rewrite (eq1 Theorem92) in H5.
    apply Theorem96_2 with (Z:=X) in H5.
    rewrite (eq1 Theorem93) in H5; Simpl_Prin H5.
    rewrite (eq1 Theorem92); rewrite (eq1 Theorem92) in H5.
    apply Theorem79; auto.
  - red; intro; apply Theorem129_2 with (X:=X) (X0:=Z) in H6; auto.
    elim H6; autoPr.
Qed.

Theorem Theorem135_1 : ∀ ξ η ζ, ξ > η -> ξ + ζ > η + ζ.
Proof.
  intros; apply Theorem134; auto.
Qed.

Theorem Theorem135_2 : ∀ ξ η ζ, ξ ≈ η -> ξ + ζ ≈ η + ζ.
Proof.
  intros; rewrite (eq2 H); apply Theorem116.
Qed.

Theorem Theorem135_3 : ∀ ξ η ζ, ξ < η -> ξ + ζ < η + ζ.
Proof.
  intros; apply Theorem135_1; auto.
Qed.

Theorem Theorem136_1 : ∀ ξ η ζ, ξ + ζ > η + ζ -> ξ > η.
Proof.
  intros; destruct (Theorem123 ξ η) as [H0 | [H0 | H0]]; auto.
  - apply Theorem135_3 with (ζ:=ζ) in H0; LGC H0 H.
  - apply Theorem135_2 with (ζ:=ζ) in H0; EGC H0 H.
Qed.

Theorem Theorem136_2 : ∀ ξ η ζ, ξ + ζ ≈ η + ζ -> ξ ≈ η.
Proof.
  intros; destruct (Theorem123 ξ η) as [H0 | [H0 | H0]]; auto.
  - apply Theorem135_3 with (ζ:=ζ) in H0; ELC H H0.
  - apply Theorem135_1 with (ζ:=ζ) in H0; EGC H H0.
Qed.

Theorem Theorem136_3 : ∀ ξ η ζ, ξ + ζ < η + ζ -> ξ < η.
Proof.
  intros; destruct (Theorem123 ξ η) as [H0 | [H0 | H0]]; auto.
  - apply Theorem135_1 with (ζ:=ζ) in H0; LGC H H0.
  - apply Theorem135_2 with (ζ:=ζ) in H0; ELC H0 H.
Qed.

Theorem Theorem137 : ∀ {ξ η ζ υ},
  ξ > η -> ζ > υ -> (ξ + ζ) > (η + υ).
Proof.
  intros; apply (Theorem135_1 _ _ ζ) in H.
  apply (Theorem135_1 _ _ η) in H0.
  rewrite (eq2 Theorem130), (eq2 (@Theorem130 υ η)) in H0.
  eapply Theorem126 ; eauto.
Qed.

Theorem Theorem138 : ∀ ξ η ζ υ,
  (ξ ≧ η /\ ζ > υ) \/ (ξ > η /\ ζ ≧ υ) -> (ξ + ζ) > (η + υ).
Proof.
  intros; destruct H as [[[H | H] H0] | [H [H0 | H0]]].
  - apply Theorem137; auto.
  - rewrite (eq2 H), (eq2 Theorem130), (eq2 (@Theorem130 η υ)).
    apply Theorem135_1; auto.
  - apply Theorem137; auto.
  - rewrite (eq2 H0); apply Theorem135_1; auto.
Qed.

Theorem Theorem139 : ∀ ξ η ζ υ,
  (ξ ≧ η /\ ζ ≧ υ) -> (ξ + ζ) ≧ (η + υ).
Proof.
  intros; destruct H as [H H0], H0.
  - left; apply Theorem138; auto.
  - destruct H.
    + rewrite (eq2 H0); left; apply Theorem135_1; auto.
    + right; rewrite (eq2 H), (eq2 H0); apply Theorem116.
Qed.

Theorem Theorem140_1 : ∀ η υ1 υ2 ξ,
  η + υ1 ≈ ξ -> η + υ2 ≈ ξ -> υ1 ≈ υ2.
Proof.
  intros; apply Theorem117 in H; eapply Theorem118 in H; eauto.
  rewrite (eq2 Theorem130), (eq2 (@ Theorem130 η υ1)) in H.
  apply Theorem136_2, Theorem117 in H; auto.
Qed.

Definition minus_C ξ η :=
  /{ Z | ∃ X Y l, Num_L X ξ /\ Num_U Y η /\ Z ≡ ((X - Y) l) /}.

Lemma Lemma_T140 : ∀ ξ η, ξ > η -> Cut_p1 (minus_C ξ η) /\
  Cut_p2 (minus_C ξ η) /\ Cut_p3 (minus_C ξ η).
Proof.
  intros; repeat split.
  - destruct H as [X [H H1]].
    apply (cutp3 ξ) in H; destruct H as [Y [H H2]].
    exists ((Y - X) H2); constructor.
    exists Y, X, H2; repeat split; autoPr.
  - destruct (cutp1 ξ) as [p1 [X1 p1']].
    exists X1; intro; destruct H0, H0 as [X [Y [H0 [H1 [H2 H3]]]]].
    assert (ILT_Pr ((X - Y) H0) X1).
    { apply Theorem86 with (Y:=X).
      - apply Theorem97_3 with (Z:=Y); Simpl_Pr; apply Theorem94.
      - apply D28_p2 with (Y:=X1) in H1; auto; apply cutp2. }
    apply Theorem79 in H3; ELPr H3 H4.
  - destruct H0, H0 as [X0 [Y0 [H0 [H2 [H3 H4]]]]].
    rewrite (eq1 H4) in H1. apply Theorem96_3 with
      (Z:=Y0) in H1. Simpl_Prin H1; red in H0.
    pose proof (cutp2 ξ _ H2 _ H1).
    pose proof (Theorem94 Y0 Y); rewrite (eq1 Theorem92) in H6.
    exists (Plus_Pr Y Y0), Y0, H6; repeat split; auto.
    apply Theorem97_2 with (Z:=Y0); Simpl_Pr; autoPr.
  - red; intros; destruct H0, H0 as [X0 [Y [H0 [H1 [H2 H3]]]]].
    apply (cutp3 ξ) in H1; destruct H1 as [Y0 [H1 H4]].
    pose proof (Theorem86 _ _ _ H0 H4).
    exists ((Y0 - Y) H5); split.
    + constructor; exists Y0, Y, H5; repeat split; autoPr.
    + rewrite (eq1 H3); apply Theorem97_1 with (Z:=Y); Simpl_Pr.
Qed.

Definition Minus_C ξ η (l :ξ > η) : Cut.
  intros; apply mkcut with (minus_C ξ η); apply Lemma_T140; auto.
Defined.
Notation " X - Y " := (Minus_C X Y).

Lemma Lemma_T140' : ∀ ξ η l, (η + ((ξ - η) l)) ≈ ξ. 
Proof.
  intros; red; split; intros.
  - destruct H, H as [X0 [Y0 [H [H0 H1]]]],
      H0, H0 as [X1 [Y1 [H2 [H3 [H4 H5]]]]].
    rewrite (eq1 H1), (eq1 H5); apply (cutp2 ξ) with X1; auto.
    rewrite (eq1 Theorem92); pose proof (Lemma_T119 η _ _ H H4).
    apply Theorem97_3 with (Z:=(Minus_Pr Y1 X0 H0)); auto.
    rewrite (eq1 Theorem93), (eq1 (@Theorem92 X0 _)).
    Simpl_Pr; apply Theorem94; auto.
  - destruct (classic (X ∈ η)) as [H0 |H0].
    + destruct (Theorem133 η ((ξ - η) l)) as [Z [H1 H2]].
      pose proof (Lemma_T119 η _ _ H0 H2).
      apply (cutp2 (Plus_C η ((ξ - η) l))) with Z; auto.
    + destruct (cutp3 ξ _ H) as [Y [H1 H2]].
      destruct (Theorem132 (Minus_Pr Y X H2) η) as
        [Y2 [Y1 [H3 [H4 [H5 H6]]]]]. apply Theorem79 in H6.
      pose proof (Lemma_T119 η _ _ H5 H0).
      pose proof  (Theorem120 _ _ _ H H7).
      apply Theorem96_2 with (Z:=Y1) in H6; Simpl_Prin H6.
      rewrite (eq1 Theorem92) in H6.
      apply Theorem96_2 with (Z:=X) in H6.
      rewrite (eq1 Theorem93) in H6; Simpl_Prin H6.
      rewrite (eq1 Theorem92) in H6. assert (IGT_Pr Y Y2).
      { destruct (Theorem81 Y Y2) as [H9 | [H9 | H9]]; auto.
        - rewrite (eq1 H9) in H6.
          apply Theorem97_2 in H6; EGPr H6 H7.
        - EGPr H6 (Theorem98 H7 H9). }
      constructor; exists Y1, (Minus_Pr Y Y2 H9).
      repeat split; auto.
      * exists Y, Y2, H9; repeat split; autoPr.
      * apply Theorem97_2 with (Z:=Y2).
        rewrite (eq1 Theorem93); Simpl_Pr.
Qed.

Theorem Theorem140_2 : ∀ ξ η (l :ξ > η), ∃ v, (η + v) ≈ ξ.
Proof.
  intros; exists ((ξ - η) l); apply Lemma_T140'; auto.
Qed.

Corollary CMi1 : ∀ ξ η l, ((ξ - η) l) + η = ξ.
Proof.
  intros; apply eq2; rewrite (eq2 Theorem130); apply Lemma_T140'.
Qed.

Corollary CMi1' : ∀ ξ η l, η + ((ξ - η) l) = ξ.
Proof.
  intros; rewrite (eq2 Theorem130); apply CMi1. 
Qed.

Corollary CMi2 : ∀ ξ η l, ((ξ + η) - η) l = ξ.
Proof.
  intros; apply eq2; apply Theorem136_2 with (ζ:=η).
  rewrite CMi1; apply Theorem116.
Qed.

Corollary CMi2' : ∀ ξ η l, ((η + ξ) - η) l = ξ.
Proof.
  intros; apply eq2, Theorem136_2 with (ζ:=η).
  rewrite CMi1; apply Theorem130.
Qed.

Hint Rewrite CMi1 CMi1' CMi2 CMi2' : Cut.
Ltac Simpl_C := autorewrite with Cut; auto.
Ltac Simpl_Cin H := autorewrite with Cut in H; auto.

(* SECTION IV Multiplication *)

Definition times_C ξ η :=
  /{ Z | ∃ X Y, Num_L X ξ /\ Num_L Y η /\ Z ≡ (X · Y) /}.

Theorem Theorem141_2 : ∀ ξ η X Y Z, Z ∈ (times_C ξ η) ->
  Num_U X ξ /\ Num_U Y η -> ~ Z ≡ (Times_Pr X Y).
Proof.
  intros; destruct H, H as [X0 [Y0 [H1 [H2 H3]]]]; intro.
  rewrite (eq1 H) in H3; destruct H0.
  pose proof (Lemma_T119 ξ _ _ H1 H0).
  EGPr H3 (Theorem107 H5 (Lemma_T119 η _ _ H2 H4)).
Qed.

Theorem Theorem141_1 : ∀ ξ η, Cut_p1 (times_C ξ η) /\
  Cut_p2 (times_C ξ η) /\ Cut_p3 (times_C ξ η).
Proof.
  intros; EC X ξ H;ENC X1 ξ H0;EC Y η H1;ENC Y1 η H2; repeat split.
  - exists (X · Y); constructor; exists X, Y; repeat split; autoPr.
  - exists (X1 · Y1); intro.
    apply Theorem141_2 with (X:=X1) (Y:=Y1) in H3; auto.
    apply H3; autoPr.
  - destruct H3, H3 as [X2[Y2 [H3 [H5 H6]]]].
    exists X2, (Y0/X2); repeat split; auto.
    + apply (cutp2 η) with Y2; auto.
      apply Theorem106_3 with (Z:=X2); Simpl_Pr.
      rewrite (eq1 H6), (eq1 Theorem102) in H4; auto.
    + Simpl_Pr; autoPr.
  - red; intros; destruct H3, H3 as [X2 [Y2 [H3 [H4 H5]]]].
    apply (cutp3 ξ) in H3; destruct H3 as [X3 [H3 H6]].
    exists (X3 · Y2); split.
    + constructor; exists X3, Y2; intros; repeat split; autoPr.
    + apply Theorem105_1 with (Z:=Y2) in H6.
      rewrite (eq1 H5); auto.
Qed.

Definition Times_C (ξ η :Cut) : Cut.
  apply mkcut with (times_C ξ η); apply Theorem141_1.
Defined.
Notation " X · Y " := (Times_C X Y).

Theorem Theorem142 : ∀ {ξ η}, ξ · η ≈ η · ξ.
Proof.
  intros; red; intros; split; intros;
  destruct H; destruct H as [X0 [Y0 [H1 [H2 H3]]]];
  constructor; exists Y0, X0; repeat split; auto;
  rewrite (eq1 Theorem102); auto.
Qed.

Theorem Theorem143 : ∀ {ξ η ζ}, (ξ · η) · ζ ≈ ξ · (η · ζ).
Proof.
  intros; red; intros; split; intros.
  - destruct H, H as [X0 [Y0 [H1 [H2 H3]]]].
    destruct H1, H as [X1 [Y1 [H [H0 H1]]]].
    constructor; exists X1, (Times_Pr Y1 Y0); repeat split; auto.
    + exists Y1, Y0; repeat split; autoPr.
    + rewrite <- (eq1 Theorem103), <- (eq1 H1); auto.
  - destruct H, H as [X0 [Y0 [H1 [H2 H3]]]].
    destruct H2, H as [X1 [Y1 [H [H0 H2]]]].
    constructor; exists (Times_Pr X0 X1), Y1; repeat split; auto.
    + exists X0, X1; repeat split; autoPr.
    + rewrite  (eq1 Theorem103), <- (eq1 H2); auto.
Qed.

Theorem Theorem144 : ∀ {ξ η ζ}, ξ · (η + ζ) ≈ (ξ · η) + (ξ · ζ).
Proof.
  intros; red; intros; split; intros.
  - destruct H, H as [X0 [Y0 [H [H0 H1]]]].
    destruct H0, H0 as [X1 [Y1 [H0 [H2 H3]]]]. constructor.
    exists (Times_Pr X0 X1), (Times_Pr X0 Y1); repeat split.
    + exists X0, X1; repeat split; autoPr.
    + exists X0, Y1; repeat split; autoPr.
    + rewrite <- (eq1 Theorem104), <- (eq1 H3); auto.
  - destruct H, H as [X0 [Y0 [H [H0 H1]]]],
      H,H as [X1[Y1 [H [H2 H3]]]], H0,H0 as [X2[Y2 [H0 [H4 H5]]]].
    rewrite (eq1 H3), (eq1 H5) in H1.
    destruct (Theorem81 X1 X2) as [H6 | [H6 | H6]].
    + constructor; exists X1, (Plus_Pr Y1 Y2); repeat split; auto.
      * exists Y1, Y2; repeat split; autoPr.
      * rewrite <- (eq1 H6), <- (eq1 Theorem104) in H1; auto.
    + assert (IGT_Pr(Plus_Pr (Times_Pr X1 Y1) (Times_Pr X1 Y2)) X).
      { rewrite (eq1 H1); rewrite (eq1 Theorem92).
        rewrite (eq1 (@Theorem92 (Times_Pr X1 Y1) _)).
        apply Theorem96_1; apply Theorem105_1; auto. }
        assert ((Plus_Pr (Times_Pr X1 Y1) (Times_Pr X1 Y2)) ∈ 
          (ξ · (η + ζ))).
        { constructor; exists X1, (Plus_Pr Y1 Y2).
          repeat split; auto.
          - exists Y1, Y2; repeat split; autoPr.
          - apply Theorem79; apply Theorem104. }
      eapply (cutp2 (ξ · (η + ζ))); eauto.
    + assert (IGT_Pr(Plus_Pr (Times_Pr X2 Y1) (Times_Pr X2 Y2)) X).
      { rewrite (eq1 H1); apply Theorem96_1.
        apply Theorem105_1; auto. }
      assert ((Plus_Pr (Times_Pr X2 Y1) (Times_Pr X2 Y2)) ∈ 
        (ξ · (η + ζ))).
      { constructor; exists X2, (Plus_Pr Y1 Y2).
        repeat split; auto.
        + exists Y1, Y2; repeat split; autoPr.
        + apply Theorem79; apply Theorem104. }
      eapply (cutp2 (ξ · (η + ζ))); eauto.
Qed.

Corollary Theorem144' : ∀ {ξ η ζ}, 
  ((η + ζ) · ξ) ≈ ((η · ξ) + (ζ · ξ)).
Proof.
  intros; rewrite (eq2 Theorem142); try apply Theorem129_1.
  pattern (η·ξ); rewrite (eq2 Theorem142).
  pattern (ζ·ξ); rewrite (eq2 Theorem142); apply Theorem144.
Qed.

Theorem Theorem145_1 : ∀ ξ η ζ, ξ > η -> (ξ · ζ) > (η · ζ).
Proof.
  intros; apply Theorem140_2 in H; destruct H as [x H].
  rewrite <- (eq2 H), (eq2 Theorem142), (eq2 Theorem144).
  pattern (η·ζ); rewrite (eq2 Theorem142); apply Theorem133.
Qed.

Theorem Theorem145_2 : ∀ ξ η ζ, ξ ≈ η -> (ξ · ζ) ≈ (η · ζ).
Proof.
  intros; rewrite (eq2 H); apply Theorem116.
Qed.

Theorem Theorem145_3 : ∀ ξ η ζ, ξ < η -> (ξ · ζ) < (η · ζ).
Proof.
  intros; apply Theorem145_1; auto.
Qed.

Theorem Theorem146_1 : ∀ ξ η ζ, (ξ · ζ) > (η · ζ) -> ξ > η .
Proof.
  intros; destruct (Theorem123 ξ η) as [H0 | [H0 | H0]]; auto.
  - apply Theorem145_3 with (ζ:=ζ) in H0; LGC H0 H.
  - apply Theorem145_2 with (ζ:=ζ) in H0; EGC H0 H.
Qed.

Theorem Theorem146_2 : ∀ ξ η ζ, (ξ · ζ) ≈ (η · ζ) -> ξ ≈ η.
Proof.
  intros; destruct (Theorem123 ξ η) as [H0 | [H0 | H0]]; auto.
  - apply Theorem145_3 with (ζ:=ζ) in H0; ELC H H0.
  - apply Theorem145_1 with (ζ:=ζ) in H0; EGC H H0.
Qed.

Theorem Theorem146_3 : ∀ ξ η ζ, (ξ · ζ) < (η · ζ) -> ξ < η.
Proof.
  intros; destruct (Theorem123 ξ η) as [H0 | [H0 | H0]]; auto.
  - apply Theorem145_1 with (ζ:=ζ) in H0; LGC H H0.
  - apply Theorem145_2 with (ζ:=ζ) in H0; ELC H0 H.
Qed.

Theorem Theorem147 : ∀ {ξ η ζ υ}, 
  ξ > η -> ζ > υ -> (ξ · ζ) > (η · υ).
Proof.
  intros; apply (Theorem145_1 _ _ ζ) in H.
  apply (Theorem145_1 _ _ η) in H0.
  rewrite (eq2 (@Theorem142 η ζ)) in H.
  rewrite (eq2 (@Theorem142 υ η)) in H0. eapply Theorem126; eauto.
Qed.

Theorem Theorem148 : ∀ ξ η ζ υ, 
  (ξ ≧ η /\ ζ > υ) \/ (ξ > η /\ ζ ≧ υ) -> (ξ · ζ) > (η · υ).
Proof.
  intros; destruct H as [[[H | H] H0] | [H [H0 | H0]]].
  - apply Theorem147; auto.
  - rewrite (eq2 Theorem142), (eq2 (@Theorem142 η υ)), (eq2 H).
    apply Theorem145_1; auto.
  - apply Theorem147; auto.
  - rewrite (eq2 H0); apply Theorem145_1; auto.
Qed.

Theorem Theorem149 : ∀ ξ η ζ υ,
  ξ ≧ η /\ ζ ≧ υ -> (ξ · ζ) ≧ (η · υ).
Proof.
  intros; destruct H as [H H0], H0.
  - left; apply Theorem148; auto.
  - destruct H.
    + rewrite (eq2 H0); left; apply Theorem145_1; auto.
    + right; rewrite (eq2 H), (eq2 H0); apply Theorem116.
Qed.

Definition rat_C R := /{ X | ILT_Pr X R /}.

Theorem Theorem150 : ∀ R, 
  Cut_p1 (rat_C R) /\ Cut_p2 (rat_C R) /\ Cut_p3 (rat_C R).
Proof.
  intros; repeat split.
  - destruct (Theorem90 R) as [x H].
    exists x; constructor; auto.
  - exists R; intro; destruct H; ELPr (Theorem78 R) H.
  - destruct H; apply Theorem86 with X; auto.
  - red; intros; destruct H, (Theorem91 _ _ H) as [Z [H0 H1]].
    exists Z; split; try constructor; auto.
Qed.

Definition Star (R :Rat) : Cut.
  apply mkcut with (rat_C R); apply Theorem150.
Defined.
Notation " R * " := (Star R)(at level 0).

Theorem Theorem151 : ∀ {ξ}, ξ · 1* ≈ ξ.
Proof.
  intros; red; intros; split; intros.
  - destruct H, H as [x [x0 [H [H0 H1]]]], H0.
    assert (ILT_Pr X x).
    { apply Theorem105_3 with (Z:=x) in H0; Simpl_Prin H0.
      rewrite (eq1 Theorem102), <- (eq1 H1) in H0; auto. }
    apply (cutp2 ξ) with x; auto.
  - apply (cutp3 ξ) in H; destruct H as [X1 [H H0]].
    constructor; exists X1, (X/X1); repeat split; auto.
    + apply Theorem106_3 with (Z:=X1); Simpl_Pr.
    + Simpl_Pr; autoPr.
Qed.

Corollary Co_D37 : ∀ ξ, ξ · 1* = ξ.
Proof.
  intros; apply eq2; apply Theorem151.
Qed.

Corollary Co_D37' : ∀ ξ, 1* · ξ = ξ.
Proof.
  intros; rewrite (eq2 Theorem142); apply Co_D37.
Qed.

Hint Rewrite Co_D37 Co_D37' : Cut.

Definition Least_Num_U X ξ := 
  (Num_U X ξ) /\ (∀ Y, Num_U Y ξ -> ~ IGT_Pr X Y).

Definition recip_C ξ :=
  /{ X | ∃ Y, Num_U Y ξ /\ (~ Least_Num_U Y ξ) /\ X ≡ 1/Y /}.

Lemma Lemma_T152 : ∀ ξ, 
  Cut_p1 (recip_C ξ) /\ Cut_p2 (recip_C ξ) /\ Cut_p3 (recip_C ξ).
Proof.
  intros; EC X ξ H; ENC Y ξ H0; repeat split.
  - exists (1/(Plus_Pr Y Y)); constructor.
    exists (Plus_Pr Y Y); repeat split; autoPr.
    + apply Theorem119 with (X:=Y); try apply Theorem94; auto.
    + intro; destruct H1; apply H2 in H0.
      apply H0; apply Theorem94.
  - exists (1/X); intro; destruct H1, H1 as [X0 [H2 [H3 H4]]].
    generalize (Lemma_T119 ξ _ _ H H2); intro.
    apply PrOverP2 in H1; apply Theorem79 in H4; ELPr H4 H1.
  - destruct H1; destruct H1 as [X1 [H1 [H3 H4]]].
    exists (1/Y0); repeat split.
    + red; intro; rewrite (eq1 H4) in H2.
      apply PrOverP2 in H2; Simpl_Prin H2.
      apply Theorem119 with (ξ:=ξ) in H2; auto.
    + intro; destruct H5 as [H5 H6].
      apply PrOverP2 in H2; rewrite (eq1 H4) in H2; Simpl_Prin H2.
      apply H6 in H1; contradiction.
    + Simpl_Pr; autoPr.
  - red; intros Z H1; destruct H1, H1 as [X0 [H2 [H3 H4]]].
    assert (exists X1, Num_U X1 ξ /\ ILT_Pr X1 X0).
    { Absurd; unfold Least_Num_U in H3; apply property_not in H3.
      destruct H3; try contradiction; elim H3.
      intros; intro; apply H1; eauto. }
    destruct H1 as [X1 [H1 H5]]. apply Theorem91 in H5.
    destruct H5 as [X2 H5], H5. apply PrOverP2 in H6.
    exists (1/X2); rewrite <- (eq1 H4) in H6; split; auto.
    constructor; exists X2; repeat split; autoPr.
    + apply Theorem119 with X1; auto.
    + intro; red in H7; destruct H7. apply H8 in H5; auto.
Qed.

Definition Recip_C (ξ :Cut) : Cut.
  apply mkcut with (recip_C ξ); apply Lemma_T152.
Defined.
Notation " / ξ " := (Recip_C ξ).

Lemma Lemma_T152' : ∀ {ξ}, (ξ · /ξ) ≈ 1*.
Proof.
  intros; red; intros U; split; intro; destruct H; constructor.
  - destruct H as [X [Y H]], H as [H [H0 H1]].
    destruct H0, H0 as [X0 [H0 [H2 H3]]].
    generalize (Lemma_T119 ξ _ _ H H0); intro.
    rewrite (eq1 H3) in H1. rewrite (eq1 H1).
    apply Theorem106_3 with (Z:=X0).
    rewrite (eq1 Theorem103); Simpl_Pr.
  - EC X ξ H0.
    generalize (Theorem132 (Times_Pr (Minus_Pr 1 U H) X) ξ); intro.
    destruct H1 as [Y1 [X1 [H1 [H2 [H3 H4]]]]].
    exists X1, (1/(X1/U)); repeat split; auto.
    + exists (X1/U); generalize (Lemma_T119 ξ _ _ H0 H2); intro.
      assert (IGT_Pr
        (Times_Pr (Minus_Pr 1 U H) Y1) (Minus_Pr Y1 X1 H1)).
      { apply Theorem105_3 with (Z:=(Minus_Pr 1 U H)) in H5.
        rewrite (eq1 Theorem102) in H4.
        rewrite (eq1 H4), (eq1 Theorem102) in H5; auto. }
      assert (ILT_Pr (Times_Pr U Y1) X1).
      { apply Theorem96_3 with (Z:=(Times_Pr U Y1)) in H6.
        rewrite (eq1 Theorem92), <- (eq1 Theorem104') in H6.
        Simpl_Prin H6. apply Theorem96_3 with (Z:=X1) in H6.
        rewrite (eq1 Theorem93) in H6; Simpl_Prin H6.
        rewrite (eq1 (@Theorem92 Y1 X1)) in H6.
        apply Theorem97_3 in H6; auto. }
      assert (ILT_Pr Y1 (X1/U)).
      { apply Theorem106_3 with (Z:=U).
        rewrite (eq1 Theorem102); Simpl_Pr. }
      repeat split; try (apply Theorem119 with Y1; auto); autoPr.
      intro; destruct H9; apply H10 in H2; contradiction.
    + apply Theorem106_2 with (Z:=(X1/U)).
      rewrite (eq1 Theorem103); Simpl_Pr; autoPr.
Qed.

Theorem Theorem152 : ∀ ξ, ∃ υ :Cut, (ξ · υ) ≈ 1*.
Proof.
  intros; exists (Recip_C ξ); apply Lemma_T152'.
Qed.

Theorem Theorem153_1 : ∀ η υ1 υ2 ξ, 
  (η · υ1) ≈ ξ ->  (η · υ2) ≈ ξ -> υ1 ≈ υ2.
Proof.
  intros. assert (η · υ1 ≈ η · υ2).
  { apply Theorem117 in H0; eapply Theorem118; eauto. }
  rewrite (eq2 Theorem142), (eq2 (@Theorem142 η υ2)) in H1.
  apply Theorem146_2 in H1; auto.
Qed.

Theorem Theorem153_2 : ∀ η ξ, ∃ υ :Cut, η · υ ≈ ξ.
Proof.
  intros; exists (/η · ξ).
  rewrite <- (eq2 Theorem143), (eq2 Lemma_T152').
  rewrite (eq2 Theorem142); apply Theorem151.
Qed.

Definition Over_C (ξ η :Cut) : Cut.
  exact (ξ · /η).
Defined.
Notation " X / Y " := (Over_C X Y).

Corollary Cdt : ∀ E N, (E/N) · N = E.
Proof.
  intros; apply eq2; unfold Over_C; rewrite (eq2 Theorem143).
  rewrite (eq2 (@Theorem142 (/N) N)), (eq2 Lemma_T152').
  apply Theorem151.
Qed.

Corollary Ctd : ∀ E N,  (E · N) / N = E.
Proof.
  intros; apply eq2; unfold Over_C.
  rewrite (eq2 Theorem143), (eq2 Lemma_T152'); apply Theorem151.
Qed.

Hint Rewrite Cdt Ctd : Cut.

(* SECTION V Rational Cuts and Integeral Cuts *)

Definition Cut_R X := Star X.

Definition Cut_I X := Star (Int X).

Theorem Theorem154_1 : ∀ X Y, IGT_Pr X Y -> X* > Y*.
Proof.
  intros; red; intros; exists Y; split.
  - red; constructor; auto.
  - red; intro; destruct H0; ELPr (Theorem78 Y) H0.
Qed.

Theorem Theorem154_2 : ∀ X Y, X ≡ Y -> X* ≈ Y*.
Proof.
  intros; rewrite (eq1 H); apply Theorem116.
Qed.

Theorem Theorem154_3 : ∀ X Y, ILT_Pr X Y -> X* < Y*.
Proof.
  intros; apply Theorem154_1; auto.
Qed.

Corollary Theorem154_1' : ∀ X Y, X* > Y* -> IGT_Pr X Y.
Proof.
  intros; destruct (Theorem81 X Y) as [H0 | [H0 | H0]]; auto.
  - apply Theorem154_2 in H0; EGC H0 H.
  - apply Theorem154_3 in H0; LGC H0 H.
Qed.

Corollary Theorem154_2' : ∀ X Y, X* ≈ Y* -> X ≡ Y.
Proof.
  intros; destruct (Theorem81 X Y) as [H0 | [H0 | H0]]; auto.
  - apply Theorem154_1 in H0; EGC H H0.
  - apply Theorem154_3 in H0; ELC H H0.
Qed.

Corollary Theorem154_3' : ∀ X Y, X* < Y* -> ILT_Pr X Y.
Proof.
  intros; apply Theorem154_1'; auto.
Qed.

Theorem Theorem155_1 : ∀ {X Y:Rat}, (Plus_Pr X Y)* ≈ (X* + Y*).
Proof.
  intros; red; intros U; split; intro.
  - destruct H; constructor.
    exists (Times_Pr X (Over_Pr U (Plus_Pr X Y))).
    exists (Times_Pr Y (Over_Pr U (Plus_Pr X Y))).
    assert (ILT_Pr (Over_Pr U (Plus_Pr X Y)) 1).
    { apply Theorem106_3 with (Z:=(Plus_Pr X Y)); Simpl_Pr. }
    repeat split.
    + apply Theorem105_3 with (Z:=X) in H0; Simpl_Prin H0.
      rewrite (eq1 Theorem102); auto.
    + apply Theorem105_3 with (Z:=Y) in H0; Simpl_Prin H0.
      rewrite (eq1 Theorem102); auto.
    + rewrite <- (eq1 Theorem104'), (eq1 Theorem102); Simpl_Pr.
      apply Theorem78.
  - destruct H, H as [X2 [Y2 [H [H0 H1]]]]; constructor.
    destruct H, H0; rewrite (eq1 H1); apply Theorem98; auto.
Qed.


Theorem Theorem155_2 : ∀ {X Y l}, 
  (Minus_Pr X Y l)* ≈ ((X* - Y*) (Theorem154_1 X Y l)).
Proof.
  intros; apply Theorem136_2 with (ζ:=Y*); Simpl_C.
  rewrite <- (eq2 Theorem155_1); Simpl_Pr; apply Theorem116.
Qed.

Theorem Theorem155_3 : ∀ {X Y}, (Times_Pr X Y)* ≈ (X* · Y*).
Proof.
  intros; red; intros U; split; intro.
  - destruct H; apply Theorem91 in H; destruct H as [U1 H], H.
    constructor; exists (Over_Pr U1 Y), 
      (Times_Pr Y (Over_Pr U U1)); repeat split.
    + apply Theorem106_3 with (Z:=Y); Simpl_Pr.
    + assert (ILT_Pr (Over_Pr U U1) 1).
      { apply Theorem106_3 with (Z:=U1); Simpl_Pr. }
      rewrite (eq1 Theorem102).
      apply Theorem105_3 with (Z:=Y) in H1; Simpl_Prin H1.
    + rewrite <- (eq1 Theorem103); Simpl_Pr; apply Theorem78.
  - destruct H, H as [X2 [Y2 [H [H0 H1]]]]; constructor.
    red in H, H0; destruct H, H0; rewrite (eq1 H1).
    apply Theorem107; auto.
Qed.

Theorem Theorem155_4 : ∀ {X Y}, (Over_Pr X Y)* ≈ X*/Y*.
Proof.
  intros; apply Theorem146_2 with (ζ:=(Cut_R Y)); Simpl_C.
  rewrite <- (eq2 Theorem155_3); Simpl_Pr; apply Theorem116.
Qed.

Definition ℳ113 := /{ i | ∃ x :Nat, i ≈ x* /}.

Theorem Theorem156_1 : 1* ∈ ℳ113.
Proof. 
  constructor; exists 1; apply Theorem116.
Qed.

Theorem Theorem156_2 : ∀ (x :Nat), x* ∈ ℳ113 -> (x`)* ∈ ℳ113.
Proof.
  intros; destruct H, H; constructor; exists (x0`).
  apply Theorem154_2' in H; pose proof (H _ _ Eqf_Ne Eqf_Ne).
  red in H0;simpl in H0;Simpl_Nin H0; rewrite H0; apply Theorem116.
Qed.

Theorem Theorem156_3 : ∀ (x :Nat), ~ (x`)* ≈ 1*.
Proof.
  intros; intro; apply Theorem154_2' in H.
  generalize (H _ _ Eqf_Ne Eqf_Ne); intros.
  red in H0; simpl in H0; Simpl_Nin H0.
  apply AxiomIII in H0; auto.
Qed.

Theorem Theorem156_4 : ∀ (x y:Nat), (x`)* ≈ (y`)* -> x* ≈ y*.
Proof.
  intros; apply Theorem154_2' in H.
  generalize (H _ _ Eqf_Ne Eqf_Ne); intros.
  red in H0; simpl in H0; Simpl_Nin H0.
  apply AxiomIV in H0; rewrite H0; apply Theorem116.
Qed.

Theorem Theorem156_5 : ∀ ℳ, 1* ∈ ℳ /\
  (∀ (x :Nat), x* ∈ ℳ -> (x`)* ∈ ℳ) -> ∀ (y :Nat), y* ∈ ℳ.
Proof.
  intros; destruct H. set (ℳ0:=/{ x | x* ∈ ℳ /}).
  assert (1 ∈ℳ0). { constructor; auto. }
  assert (∀ x:Nat, x ∈ ℳ0 -> x` ∈ ℳ0); intros.
  { destruct H2; constructor; auto. }
  assert (∀ x:Nat, x ∈ ℳ0). { apply AxiomV; auto. }
  destruct H3 with y; auto.
Qed.

Coercion Star_Con (R :Rat) := R*.

Theorem Theorem157 : ∀ (X :Rat) ξ, Least_Num_U X ξ -> X ≈ ξ.
Proof.
  intros; red in H; destruct H; red; intros; split; intros.
  - Absurd; destruct H1; apply H0 in H2; contradiction.
  - constructor; eapply Lemma_T119; eauto.
Qed.

Theorem Theorem158_1 : ∀ (X :Rat) ξ, Num_L X ξ <-> X < ξ.
Proof.
  split; intros.
  - red; exists X; split; auto; red; intro; destruct H0.
    ELPr (Theorem78 X) H0.
  - destruct H as [X0 H], H.
    assert (~ ILT_Pr X0 X). { intro; apply H0; constructor; auto. }
    destruct (Theorem81 X0 X) as [H2|[H2|H2]]; try contradiction.
    + rewrite <- (eq1 H2); auto. + eapply Theorem120; eauto.
Qed.

Theorem Theorem158_2 : ∀ X ξ, Num_U X ξ <-> X ≧ ξ.
Proof.
  split; intros; destruct (classic (Least_Num_U X ξ)) as [H0 | H0].
  - right; apply Theorem157; auto.
  - left; red; intros.
    assert (exists X1, Num_U X1 ξ /\ ILT_Pr X1 X).
    { Absurd; unfold Least_Num_U in H0; apply property_not in H0.
      destruct H0; try contradiction; elim H0; intros; intro.
      apply H1; eauto. }
    destruct H1 as [X1 H1], H1; exists X1; split; auto.
    red; constructor; auto.
  - red in H0; tauto.
  - destruct H.
    + red in H; destruct H as [X1 H], H, H.
      apply Theorem119 with (ξ:=ξ) in H; auto.
    + rewrite <- (eq2 H); red; intro; destruct H1.
      ELPr (Theorem78 X) H1.
Qed.

Theorem Theorem159 : ∀ ξ η, ξ < η -> ∃ Z :Rat, ξ < Z /\ Z < η.
Proof.
  intros; destruct H as [X [H H0]].
  destruct (cutp3 η _ H) as [Z [H1 H2]]; apply Theorem158_1 in H1.
  exists Z; split; auto.
  apply Theorem158_2 in H0; apply Theorem124 in H0.
  apply Theorem154_3 in H2; apply Theorem127 with (η:=X); auto.
Qed.

Theorem Theorem160 : ∀ (Z :Rat) ξ η, 
  Z > (ξ · η) -> ∃ X Y :Rat, Z ≈ (X · Y) /\ X ≧ ξ /\ Y ≧ η.
Proof.
  intros. assert (∀ ξ η, exists ζ :Cut, ζ ≦ ξ /\ ζ ≦ η); intros.
  { destruct (Theorem123 ξ0 η0) as [H0 | [H0 | H0]].
    - exists ξ0; split; red; try tauto; right; apply Theorem116.
    - exists η0; split; red; auto; right; apply Theorem116.
    - exists ξ0; split; red; try tauto; right; apply Theorem116. }
  specialize H0 with (1*) (((Z - (ξ · η)) H)/((ξ + η) + 1)); 
  destruct H0 as [ζ [H0 H1]].
  generalize (Theorem133 ξ ζ) (Theorem133 η ζ); intros.
  apply Theorem159 in H2; apply Theorem159 in H3.
  destruct H2 as [Z1 [H2 H4]], H3 as [Z2 [H3 H5]].
  assert (((ξ + ζ) · (η + ζ)) > (Z1 · Z2));
  try apply Theorem147; auto. rewrite (eq2 Theorem144) in H6.
  assert (((ξ + 1) · ζ) ≧ ((ξ + ζ) · ζ)).
  { destruct H0.
    + left; apply Theorem145_1.
      rewrite (eq2 Theorem130), (eq2 (@Theorem130 ξ ζ)).
      apply Theorem135_1; auto.
    + right; apply Theorem145_2.
      rewrite (eq2 Theorem130), (eq2 (@Theorem130 ξ ζ)).
      rewrite (eq2 H0); apply Theorem116. }
  assert ((((ξ + ζ) · η) + ((ξ + 1) · ζ)) ≧
    (((ξ + ζ) · η) + ((ξ + ζ) · ζ))).
  { rewrite (eq2 Theorem130), (eq2 (@Theorem130 ((ξ + ζ) · η) _)).
    destruct H7.
    + left; apply Theorem135_1; auto.
    + right; apply Theorem135_2; auto. }
  assert (Z ≧ (((ξ + ζ) · η) + ((ξ + 1) · ζ))).
  { rewrite (eq2 (@Theorem142 _ η)), (eq2 Theorem144),
      (eq2 (@Theorem142 _ ξ)), (eq2 Theorem131),
       <- (eq2 Theorem144'), <- (eq2 Theorem131).
    rewrite (eq2 (@Theorem130 η ξ)); Simpl_C.
    rewrite (eq2 Theorem130); destruct H1.
    + left; apply Theorem145_3 with (ζ:=(ξ + η + 1)) in H1.
      Simpl_Cin H1. rewrite (eq2 Theorem142) in H1.
      apply Theorem135_3 with (ζ:= ξ · η) in H1; Simpl_Cin H1.
    + right; apply Theorem145_2 with (ζ:=(ξ + η + 1)) in H1.
      Simpl_Cin H1. rewrite (eq2 Theorem142) in H1.
      apply Theorem135_2 with (ζ:= ξ · η) in H1; Simpl_Cin H1.
      apply Theorem117; auto. }
  apply Theorem124 in H8; apply Theorem124 in H9.
  assert ((Z1 · Z2) < (((ξ + ζ) · η) + ((ξ + 1) · ζ))).
  { apply Theorem127 with (η:=(((ξ + ζ) · η) + ((ξ + ζ) · ζ))).
    right; tauto. }
  assert (Z1 · Z2 < Z). { eapply Theorem127; eauto. }
  exists (Over_Pr Z Z2), Z2; split.
  - rewrite (eq2 Theorem155_4); Simpl_C; apply Theorem116.
  - split; left; auto; apply Theorem126 with (η:=Z1); auto.
    apply Theorem146_3 with (ζ:=Z2).
    rewrite (eq2 Theorem155_4); Simpl_C.
Qed.

Theorem Theorem161_1 : ∀ ξ ζ η,
  ξ · ξ ≈ ζ -> ~ η ≈ ξ -> ~ η · η ≈ ζ.
Proof.
  intros; intro; apply Theorem117 in H1.
  pose proof (Theorem118 _ _ _ H H1).
  destruct (Theorem123 η ξ) as [H3 | [H3 | H3]]; try tauto.
  - EGC H2 (Theorem147 H3 H3). - ELC H2 (Theorem147 H3 H3).
Qed.

Definition sqrt_cut ζ := /{ ξ | ξ · ξ < ζ /}.

Lemma Lemma_T161 : ∀ ζ, Cut_p1 (sqrt_cut ζ) /\
  Cut_p2 (sqrt_cut ζ) /\ Cut_p3 (sqrt_cut ζ).
Proof.
  assert (∀ ξ η, ∃ R :Rat, R < ξ /\ R < η) as G1.
  { intros; EC X ξ H; EC X1 η H0.
    apply Theorem158_1 in H; apply Theorem158_1 in H0.
    destruct (Theorem123 ξ η) as [H1 | [H1 | H1]].
    - exists X; split; auto; eapply Theorem126; eauto.
    - exists X1; split; auto; eapply Theorem126; eauto.
    - exists X; split; try rewrite <- (eq2 H1); auto. }
  assert (∀ ξ η, ∃ R :Rat, R ≧ ξ /\ R ≧ η) as G2.
  { intros; ENC X ξ H; ENC X1 η H0.
    apply Theorem158_2 in H; apply Theorem158_2 in H0.
    destruct (Theorem123 ξ η) as [H1 | [H1 | H1]].
    - exists X1; split; auto.
      apply Theorem125; apply Theorem124 in H0.
      eapply Theorem128; eauto; left; auto.
    - exists X; split; auto.
      apply Theorem125; apply Theorem124 in H.
      eapply Theorem128; eauto; red; tauto.
    - exists X; split; auto.
      apply Theorem125; apply Theorem124 in H.
      eapply Theorem128; eauto; right; apply Theorem117; auto. }
  intros; repeat split.
  - destruct (G1 1 ζ) as [X [H H0]].
    apply Theorem145_3 with (ζ:=X) in H; Simpl_Cin H.
    exists X; constructor; eapply Theorem126; eauto.
  - destruct (G2 1 ζ) as [X [H H0]].
    exists X; intro; destruct H1. assert ((X ≧ 1) /\ (X ≧ ζ)).
    auto. apply Theorem149 in H2; Simpl_Cin H2.
    destruct H2; try LGC H1 H2; ELC H2 H1.
  - destruct H; apply Theorem91 in H0; destruct H0 as [X0[H0 H1]].
    pose proof (Theorem86 _ _ _ H0 H1); apply Theorem154_3 in H2.
    assert (Y · Y < X · X). { apply Theorem147; auto. }
    eapply Theorem126; eauto.
  - red; intros; destruct H.
    destruct (G1 1 (((ζ - X·X) H) / (X + (X +1)))) as [Z [H0 H1]].
    pose proof (Theorem94 X Z); exists (Plus_Pr X Z).
    split; auto; constructor.
    apply Theorem135_3 with (ζ:=X) in H0.
    rewrite (eq2 Theorem130), (eq2 (@Theorem130 1 X)) in H0.
    apply Theorem145_3 with (ζ:=(X + (X + 1))) in H1; Simpl_Cin H1.
    rewrite (eq2 Theorem142) in H1.
    apply Theorem145_3 with (ζ:=Z) in H0. rewrite
      (eq2 Theorem155_1), (eq2 Theorem144), (eq2 Theorem144').
    apply Theorem135_3 with (ζ:=((X + Z) · X)) in H0.
    rewrite (eq2 Theorem130), (eq2 (@Theorem130 ((X + 1) · Z) _)),
      (eq2 (@Theorem144' X _ _ )), (eq2 (@Theorem142 Z X)),
      (eq2 (@Theorem131 _ _ ((X + 1) · Z))),
      <- (eq2 Theorem144') in H0.
    apply Theorem135_3 with (ζ:=X · X) in H1; Simpl_Cin H1.
    rewrite (eq2 Theorem130) in H1; rewrite
      (eq2 (@Theorem142 X Z)) in H0. eapply Theorem126; eauto.
Qed.

Definition Sqrt_C (ξ :Cut) : Cut.
  apply mkcut with (sqrt_cut ξ); apply Lemma_T161.
Defined.
Notation " √ ξ " := (Sqrt_C ξ)(at level 0).

Lemma Lemma_T161' : ∀ {ζ}, (√ζ · √ζ) ≈ ζ.
Proof.
  intro; destruct (Theorem123 (√ζ · √ζ) ζ) as [H | [ H | H]]; auto.
  - destruct (Theorem159 (√ζ · √ζ) ζ H) as [Z H0], H0.
    apply Theorem160 in H0.
    destruct H0 as [X1 [X2 [H0 [H2 H3]]]]; red in H2, H3.
    destruct (Theorem123 X1 X2) as [H4 | [H4 | H4]].
    + assert (X1 < √ζ).
      { apply Theorem158_1; red; constructor.
        apply Theorem126 with Z; auto.
        rewrite (eq2 H0), (eq2 (@Theorem142 X1 X2)).
        apply Theorem145_3; auto. }
      destruct H2; try LGC H5 H2; ELC H2 H5.
    + assert (X2 < √ζ).
      { apply Theorem158_1; red; constructor.
        apply Theorem126 with Z; auto.
        rewrite (eq2 H0); apply Theorem145_3; auto. }
      destruct H3; try LGC H5 H3; ELC H3 H5.
    + assert (X1 < √ζ).
      { apply Theorem158_1; red; constructor.
        rewrite (eq2 H4) in H0; rewrite (eq2 H0) in H1.
        rewrite (eq2 H4); auto. }
        destruct H2; try LGC H5 H2; try ELC H2 H5.
  - destruct (Theorem159 ζ (√ζ · √ζ) H) as [Z H0], H0.
    apply Theorem158_1 in H1.
    destruct H1, H1 as [X1 [X2 [H1 [H2 H3]]]].
    destruct (Theorem81 X1 X2) as [H4 | [H4 | H4]].
    + rewrite (eq1 H4) in H3. rewrite (eq1 H3),
        (eq2 Theorem155_3) in H0. destruct H2; LGC H2 H0.
    + assert (ILT_Pr Z (Times_Pr X1 X1)).
      { rewrite (eq1 H3), (eq1 Theorem102).
        apply Theorem105_3; auto. }
      apply Theorem154_3 in H5; rewrite (eq2 Theorem155_3) in H5.
      assert (ζ < (X1 · X1)); try apply Theorem126 with Z; auto.
      destruct H1; LGC H1 H6.
    + assert (ILT_Pr Z (Times_Pr X2 X2)).
      { rewrite (eq1 H3); apply Theorem105_3; auto. }
      apply Theorem154_3 in H5; rewrite (eq2 Theorem155_3) in H5.
      assert (ζ < (X2 · X2)); try apply Theorem126 with Z; auto.
      destruct H2; LGC H2 H6.
Qed.

Theorem Theorem161_2 : ∀ ζ, ∃ ξ, ξ · ξ ≈ ζ.
Proof.
  intros; exists √ζ; apply Lemma_T161'.
Qed.

Definition Irrat_C E := ~ (∃ X :Rat, E ≈ X).

Notation " 2 " := 1`.

Theorem Theorem162 : ∃ ξ, Irrat_C ξ.
Proof.
  intros; exists (√2); red; intro; destruct H as [X H]. assert
    (∀ x y, ILT_N (Times_N x x)(Times_N y y) -> ILT_N x y) as G1.
  { intros; destruct (Theorem10 x y) as [H1 | [H1 | H1]]; auto.
     - rewrite H1 in *; apply Theorem33_1 in H0; auto.
     - LGN H0 (Theorem34 _ _ _ _ H1 H1). } assert
  (∀ f1 f2, (Times_F f1 f1) ~ (Times_F f2 f2) -> f1 ~ f2) as G2.
  { intros; destruct (Theorem41 f1 f2) as [H1 | [H1 | H1]]; auto.
     - EGF H0 (Theorem74 _ _ _ _ H1 H1).
     - ELF H0 (Theorem74 _ _ _ _ H1 H1). }
  chan X f0 H0; destruct f0 as [p q].
  set (M162 := /{ y | ∃ x, (Over x y) ~ (Over p q) /}).
  assert (No_Empty M162).
  { red; exists q; constructor; exists p; apply Theorem37. }
  apply Theorem27 in H0; destruct H0 as [y H0],H0,H0,H0 as [x H0].
  assert ((fsr (Over p q)) ≡ (fsr (Over x y))).
  { red; intros; destruct H2, H3.
    eapply Theorem39; eauto; autoF; eapply Theorem39; eauto. }
  rewrite (eq1 H2) in H.
  assert ((√2 · √2) ≈ ((fsr (Over x y)) · (fsr (Over x y)))).
  { rewrite (eq2 H); apply Theorem116. }
  rewrite <- (eq2 Theorem155_3) in H3.
  assert ((Times_Pr (fsr (Over x y)) (fsr (Over x y))) ≡ 
    (fsr (Over (Times_N x x ) (Times_N y y)))).
  { red; intros; do 5 destruct H4; destruct H5, H6, H6.
    pose proof (Theorem39 H7 (Theorem68 H4 H6)).
    eapply Theorem39; eauto; autoF. }
  rewrite (eq1 H4), (eq2 Lemma_T161') in H3.
  apply Theorem154_2' in H3; clear H4.
  red in H3; pose proof (H3 _ _ Eqf_Ne Eqf_Ne). red in H4.
  simpl in H4; Simpl_Nin H4; clear H3; rename H4 into H3.
  assert (ILT_N y x).
  { apply G1; rewrite <- H3; apply Theorem18. }
  assert (ILT_N x (Times_N 2 y)).
  { apply G1; Simpl_N; rewrite Theorem30, Theorem30', H3.
    apply Theorem18. }
  destruct H4 as [u H4]. assert (ILT_N u y).
  { Simpl_Nin H5; rewrite H4, Theorem6 in H5.
    apply Theorem20_3 in H5; auto. }
  assert (∀ v w, (Times_N (Plus_N v w) (Plus_N v w)) =
    (Plus_N (Plus_N (Times_N v v) (Times_N 2 (Times_N v w)))
      (Times_N w w))).
  { intros; rewrite Theorem30; repeat rewrite Theorem30'; Simpl_N.
    rewrite (Theorem29 w v); repeat rewrite Theorem5; auto. }
  pose proof H6; destruct H6 as [t H6].
  assert ((Plus_N (Times_N x x) (Times_N t t)) =
    (Plus_N (Times_N x x) (Times_N 2 (Times_N u u)))).
  { pattern x at 1 2; rewrite H4, H7, Theorem5.
    rewrite (Theorem29 y u), <- Theorem31.
    pattern y at 3; rewrite H6, Theorem30.
    rewrite <- (Theorem5 (Times_N y y) _), Theorem5,
      <- (Theorem5 _ _ (Times_N t t)), (Theorem6 _ (Times_N u u)),
      (Theorem31 _ _ t), <- H7, <- H6, Theorem5,
      (Theorem6 _ (Times_N y y)),<- Theorem5,Theorem31,H3; auto. }
  rewrite Theorem6, (Theorem6 _(Times_N 2 (Times_N u u))) in H9.
  apply Theorem20_2 in H9; Simpl_Nin H9.
  assert (u ∈ M162).
  { constructor; exists t.
    assert (Equal_F (Times_F (Over t u) (Over t u)) (Over 2 1)).
    { red; simpl; Simpl_N. }
    assert (Equal_F (Times_F (Over x y) (Over x y)) (Over 2 1)).
    { red; simpl; Simpl_N. }
    assert ((Times_F (Over t u) (Over t u)) ~ (Times_F (Over x y)
      (Over x y))).
    { apply Theorem38 in H11; eapply Theorem39; eauto. }
    apply G2 in H12; eapply Theorem39; eauto. }
  apply H1 in H10; destruct H10; try LGN H8 H10.
  symmetry in H10; ELN H10 H8.
Qed.
