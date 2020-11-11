(***************************************************************************)
(*   This is part of FA_Landau, it is distributed under the terms of the   *)
(*             GNU Lesser General Public License version 3                 *)
(*                (see file LICENSE for more details)                      *)
(*                                                                         *)
(*           Copyright 2020-2022: Yaoshun Fu and Wensheng Yu.              *)
(***************************************************************************)

(* FRACTIONS *)

(* SECTION I Definition and Equivalence *)

Require Export Nats.

Inductive Fra : Type := Over : Nat -> Nat -> Fra.
Notation " x / y " := (Over x y).

Definition Get_Num f := match f with x1/x2 => x1 end.

Definition Get_Den f := match f with x1/x2 => x2 end.

Definition Equal_F f1 f2 := 
  (Get_Num f1) · (Get_Den f2) = (Get_Num f2) · (Get_Den f1).
Notation " f1 ~ f2 " := (Equal_F f1 f2)(at level 55).

Theorem Theorem37 : ∀ f1, f1 ~ f1.
Proof.
 intros; destruct f1; constructor.
Qed.

Theorem Theorem38 : ∀ f1 f2, f1 ~ f2 -> f2 ~ f1.
Proof.
  intros; destruct f1 as [x1 x2], f2 as [y1 y2].
  red in H; red; simpl in *; rewrite H; auto.
Qed.

Ltac autoF := try apply Theorem37; try apply Theorem38; auto.

Lemma Lemma_T39 : ∀ x y z u, (x · y) · (z · u) = (x · u) · (z · y).
Proof.
  intros; rewrite Theorem31, <- (Theorem31 y z u).
  rewrite (Theorem29 (y · z)), <- Theorem31, (Theorem29 y); auto.
Qed.

Theorem Theorem39 : ∀ {f1 f2 f3}, f1 ~ f2 -> f2 ~ f3 -> f1 ~ f3.
Proof.
  intros; destruct f1 as [x1 x2], f2 as [y1 y2], f3 as [z1 z2].
  unfold Equal_F in *; simpl in *.
  apply Theorem32_2 with (z:=(y1·z2)) in H.
  rewrite Lemma_T39,H0,(Lemma_T39 y1),(Theorem29 (y1 · y2)) in H.
  apply Theorem33_2 in H; auto.
Qed.

Theorem Theorem40 : ∀ x x1 x2, x1/x2 ~ (x1 · x)/(x2 · x).
Proof.
  intros; red; simpl; rewrite (Theorem29 x2 x), Theorem31; auto.
Qed.

(* SECTION II Ordering *)

Definition IGT_F f1 f2 := 
  (Get_Num f1) · (Get_Den f2) > (Get_Num f2) · (Get_Den f1).
Notation " x > y " := (IGT_F x y).

Definition ILT_F f1 f2 := 
  (Get_Num f1) · (Get_Den f2) < (Get_Num f2) · (Get_Den f1).
Notation " x < y " := (ILT_F x y).

Theorem Theorem41 : ∀ f1 f2, (f1 ~ f2) \/ (f1 > f2) \/ (f1 < f2).
Proof.
  intros; destruct f1 as [x1 x2], f2 as [y1 y2]; apply Theorem10.
Qed.

Theorem Theorem42 : ∀ f1 f2, f1 > f2 -> f2 < f1.
Proof.
  intros; destruct f1 as [x1 x2], f2 as [y1 y2]; auto.
Qed.

Theorem Theorem43 : ∀ f1 f2, f1 < f2 -> f2 > f1.
Proof.
  intros; destruct f1 as [x1 x2], f2 as [y1 y2]; auto.
Qed.

Theorem Theorem44 : ∀ {f1 f2 f3 f4},
  f1 > f2 -> f1 ~ f3 -> f2 ~ f4 -> f3 > f4.
Proof.
  intros; destruct f1 as [x1 x2], f2 as [y1 y2],
    f3 as [z1 z2], f4 as [u1 u2].
  unfold IGT_F, Equal_F in *; simpl in *.
  apply Theorem32_2 with (z:=(z1 · x2)) in H1.
  pattern (z1 · x2) at 2 in H1; rewrite <- H0 in H1.
  rewrite Lemma_T39, (Lemma_T39 u1 y2 x1 z2) in H1.
  apply Theorem32_1 with (z:=(u1 · z2)) in H.
  rewrite Theorem29, <- H1, Theorem29 in H.
  rewrite (Theorem29 (y1 · x2)) in H; apply Theorem33_1 in H; auto.
Qed.

Theorem Theorem45 : ∀ {f1 f2 f3 f4},
  f1 < f2 -> f1 ~ f3 -> f2 ~ f4 -> f3 < f4.
Proof.
  intros; apply Theorem43 in H; apply Theorem42.
  eapply Theorem44; eauto.
Qed.

Definition IGE_F f1 f2 := (f1 > f2) \/ (f1 ~ f2).
Notation " x ≳ y " := (IGE_F x y) (at level 55).

Definition ILE_F f1 f2 := (f1 < f2) \/ (f1 ~ f2).
Notation " x ≲ y " := (ILE_F x y) (at level 55).

Theorem Theorem46 : ∀ f1 f2 f3 f4,
  f1 ≳ f2 -> f1 ~ f3 -> f2 ~ f4 -> f3 ≳ f4.
Proof.
  intros; red in H; red; destruct H.
  - left; eapply Theorem44; eauto.
  - right; eapply Theorem39; eauto. eapply Theorem39; eauto; autoF.
Qed.

Theorem Theorem47 : ∀ f1 f2 f3 f4,
  f1 ≲ f2 -> f1 ~ f3 -> f2 ~ f4 -> f3 ≲ f4.
Proof.
  intros; red in H; red; destruct H.
  - left; eapply Theorem45; eauto.
  - right; eapply Theorem39; eauto. eapply Theorem39; eauto; autoF.
Qed.

Theorem Theorem48 : ∀ f1 f2, f1 ≳ f2 -> f2 ≲ f1.
Proof.
  intros; destruct H.
  - left; apply Theorem42; auto.
  - right; now apply Theorem38.
Qed.

Theorem Theorem49 : ∀ f1 f2, f1 ≲ f2 -> f2 ≳ f1.
Proof.
  intros; destruct H.
  - left; apply Theorem43; auto.
  - right; now apply Theorem38.
Qed.

Theorem Theorem50 : ∀ f1 f2 f3, f1 < f2 -> f2 < f3 -> f1 < f3.
Proof.
  intros; destruct f1 as [x1 x2], f2 as [y1 y2], f3 as [z1 z2].
  unfold ILT_F in *; simpl in *.
  apply Theorem33_3 with (z:=(y1 · y2)).
  rewrite Lemma_T39, (Theorem29 (z1 · x2)), (Lemma_T39 y1).
  eapply Theorem34; eauto.
Qed.

Theorem Theorem51 : ∀ f1 f2 f3, 
  (f1 ≲ f2 /\ f2 < f3) \/ (f1 < f2 /\ f2 ≲ f3) -> f1 < f3.
Proof.
  intros; destruct H as [[[H | H1] H0] | [H [H0 | H1]]].
  - eapply Theorem50; eauto.
  - eapply Theorem45; eauto; autoF.
  - eapply Theorem50; eauto.
  - eapply Theorem45; eauto; autoF.
Qed.

Theorem Theorem52 : ∀ f1 f2 f3, f1 ≲ f2 -> f2 ≲ f3 -> f1 ≲ f3.
Proof.
  intros; destruct H.
  - left; eapply Theorem51; eauto.
  - red in H0; destruct H0.
    + left; eapply Theorem45; eauto; autoF.
    + right; eapply Theorem39; eauto.
Qed.

Theorem Theorem53 : ∀ f1, ∃ f2, f2 > f1.
Proof.
  intros; destruct f1 as [x1 x2]; exists ((x1 + x1)/x2).
  red; simpl; rewrite Theorem30'; apply Theorem18.
Qed.

Theorem Theorem54 : ∀ f1, ∃ f2, f2 < f1.
Proof.
  intros; destruct f1 as [x1 x2]; exists (x1/(x2 + x2)).
  red; simpl; rewrite Theorem30; apply Theorem18.
Qed.

Theorem Theorem55 : ∀ f1 f2, f1 < f2 -> ∃ f3, f1 < f3 /\ f3 < f2.
Proof.
  intros; destruct f1 as [x1 x2], f2 as [y1 y2].
  red in H; simpl in H. exists ((x1 + y1) / (x2 + y2)).
  split; red; simpl; rewrite Theorem30, Theorem30'.
  - rewrite Theorem6, (Theorem6 _ (y1 · x2)); now apply Theorem19_1.
  - now apply Theorem19_3.
Qed.

(* SECTION III Addition *)

Definition Plus_F f1 f2 := 
  match f1,f2 with x1/x2,y1/y2 => (x1 · y2 + y1 · x2)/(x2 · y2) end.
Notation " f1 + f2 " := (Plus_F f1 f2).

Theorem Theorem56 : ∀ {f1 f2 f3 f4}, f1 ~ f2 -> f3 ~ f4 -> 
  (f1 + f3) ~ (f2 + f4).
Proof.
  intros; destruct f1 as [x1 x2], f2 as [y1 y2],
    f3 as [z1 z2], f4 as [u1 u2]. unfold Equal_F in *; simpl in *.
  repeat rewrite Theorem30'; rewrite (Lemma_T39 u1), <- H0.
  rewrite (Lemma_T39 z1), (Theorem29 y2 x2); apply Theorem19_2.
  rewrite (Theorem29 y2 u2), Lemma_T39, H.
  repeat rewrite <- Theorem31; apply Theorem32_2.
  repeat rewrite Theorem31; rewrite (Theorem29 u2 x2); auto.
Qed.

Theorem Theorem57 : ∀ x x1 x2,  x1/x + x2/x ~ (Plus_N x1 x2)/x.
Proof.
  intros; unfold Plus_F; simpl.
  rewrite <- Theorem30'; apply Theorem31.
Qed.

Theorem Theorem58 : ∀ f1 f2, f1 + f2 ~ f2 + f1.
Proof.
  intros; destruct f1 as [x1 x2], f2 as [y1 y2]; unfold Plus_F.
  simpl. now rewrite (Theorem6 (x1 · y2)), (Theorem29 x2).
Qed.

Theorem Theorem59 : ∀ f1 f2 f3, (f1 + f2) + f3 ~ f1 + (f2 + f3).
Proof.
  intros; destruct f1 as [x1 x2], f2 as [y1 y2], f3 as [z1 z2].
  unfold Plus_F; simpl; repeat rewrite Theorem30'.
  repeat rewrite Theorem31; rewrite Theorem5.
  rewrite (Theorem29 x2 z2), (Theorem29 y2 x2); autoF.
Qed.

Theorem Theorem60 : ∀ f1 f2, (f1 + f2) > f1.
Proof.
  intros; destruct f1 as [x1 x2], f2 as [y1 y2]; red; simpl.
  rewrite Theorem30', Theorem31, (Theorem29 y2 x2); apply Theorem18.
Qed.

Theorem Theorem61 : ∀ f1 f2 f3, f1 > f2 -> (f1 + f3) > (f2 + f3).
Proof.
  assert (∀ x y z, ((x · y) · z) = ((x · z) · y)) as G.
  { intros; rewrite Theorem31, (Theorem29 y z), <- Theorem31; auto. }
  intros; destruct f1 as [x1 x2], f2 as [y1 y2], f3 as [z1 z2].
  unfold IGT_F in *; simpl in *.
  apply Theorem32_1 with (z:=z2) in H. rewrite G, (G y1 x2 z2) in H.
  repeat rewrite Theorem30'; repeat rewrite Theorem31.
  rewrite <- (Theorem31 x2 y2 z2), (Theorem29 x2 y2), Theorem31.
  apply Theorem19_1; repeat rewrite <- Theorem31.
  now apply Theorem32_1.
Qed.

Theorem Theorem62_1 : ∀ f1 f2 f3, f1 > f2 -> (f1 + f3) > (f2 + f3).
Proof.
  intros; apply Theorem61; auto.
Qed.

Theorem Theorem62_2 : ∀ f1 f2 f3, f1 ~ f2 -> (f1 + f3) ~ (f2 + f3).
Proof.
  intros; eapply Theorem56; eauto; autoF.
Qed.

Theorem Theorem62_3 : ∀ f1 f2 f3, f1 < f2 -> (f1 + f3) < (f2 + f3).
Proof.
  intros; apply Theorem42; apply Theorem62_1; now apply Theorem43.
Qed.

Lemma OrdF1 : ∀ {f1 f2}, f1 ~ f2 -> f1 > f2 -> False.
Proof.
  intros; destruct f1 as [x1 x2], f2 as [y1 y2].
  red in H, H0; simpl in *; EGN H H0.
Qed.

Lemma OrdF2 : ∀ {f1 f2}, f1 ~ f2 -> f1 < f2 -> False.
Proof.
  intros; destruct f1 as [x1 x2], f2 as [y1 y2].
  red in H, H0; simpl in *; ELN H H0.
Qed.

Lemma OrdF3 : ∀ {f1 f2}, f1 < f2 -> f1 > f2 -> False.
Proof.
  intros; destruct f1 as [x1 x2], f2 as [y1 y2].
  red in H, H0; simpl in *; LGN H H0.
Qed.

Ltac EGF H H1 := destruct (OrdF1 H H1).
Ltac ELF H H1 := destruct (OrdF2 H H1).
Ltac LGF H H1 := destruct (OrdF3 H H1).

Theorem Theorem63_1 : ∀ f1 f2 f3, (f1 + f3) > (f2 + f3) -> f1 > f2.
Proof.
  intros; destruct (Theorem41 f1 f2) as [H0 | [H0 | H0]]; auto.
  - apply Theorem62_2 with (f3:=f3) in H0; EGF H0 H.
  - apply Theorem62_3 with (f3:=f3) in H0; LGF H0 H.
Qed.

Theorem Theorem63_2 : ∀ f1 f2 f3, (f1 + f3) ~ (f2 + f3) -> f1 ~ f2.
Proof.
  intros; destruct (Theorem41 f1 f2) as [H0 | [H0 | H0]]; auto.
  - apply Theorem62_1 with (f3:=f3) in H0; EGF H H0.
  - apply Theorem62_3 with (f3:=f3) in H0; ELF H H0.
Qed.

Theorem Theorem63_3 : ∀ f1 f2 f3, (f1 + f3) < (f2 + f3) -> f1 < f2.
Proof.
  intros; destruct (Theorem41 f1 f2) as [H0 | [H0 | H0]]; auto.
  - apply Theorem62_2 with (f3:=f3) in H0; ELF H0 H.
  - apply Theorem62_1 with (f3:=f3) in H0; LGF H H0.
Qed.

Theorem Theorem64 : ∀ {f1 f2 f3 f4},
  f1 > f2 -> f3 > f4 -> (f1 + f3) > (f2 + f4).
Proof.
  intros; apply (Theorem61 _ _ f3) in H;
  apply(Theorem61 _ _ f2) in H0.
  apply (@Theorem44 _ _ (f1+f3) (f3+f2)) in H;
  autoF; try apply Theorem58.
  apply (@Theorem44 _ _ (f3+f2) (f2+f4)) in H0;
  autoF; try apply Theorem58.
  apply Theorem43; eapply Theorem50; eauto; apply Theorem42; eauto.
Qed.

Theorem Theorem65 : ∀ f1 f2 f3 f4, (f1 ≳ f2 /\ f3 > f4) \/ 
  (f1 > f2 /\ f3 ≳ f4) -> (f1 + f3) > (f2 + f4).
Proof.
  intros; destruct H as [[[H | H1] H0] | [H [H0 | H1]]].
  - apply Theorem64; auto.
  - apply Theorem62_1 with (f3:=f1) in H0.
    apply Theorem62_2 with (f3:=f4) in H1.
    eapply Theorem44; eauto; try apply Theorem58.
    eapply Theorem39; eauto; apply Theorem58.
  - apply Theorem64; auto.
  - apply Theorem62_1 with (f3:=f3) in H. 
    apply Theorem62_2 with (f3:=f2) in H1.
    eapply Theorem44; eauto; autoF.
    apply (@Theorem39 _ (f4 + f2)); try apply Theorem58.
    apply (@Theorem39 _ (f3 + f2)); try apply Theorem58; autoF.
Qed.

Theorem Theorem66 : ∀ f1 f2 f3 f4,
  (f1 ≳ f2 /\ f3 ≳ f4) -> (f1 + f3) ≳ (f2 + f4).
Proof.
  intros; destruct H; red in H; destruct H.
  - left; apply Theorem65; auto.
  - destruct H0.
    + left; apply Theorem65; left; split; auto; red; tauto.
    + right; apply Theorem62_2 with (f3:=f3) in H.
      apply Theorem62_2 with (f3:=f2) in H0.
      apply (@Theorem39 _ (f2 + f3)); auto.
      apply (@Theorem39 _ (f3 + f2)); try apply Theorem58.
      eapply Theorem39; eauto; try apply Theorem58.
Qed.

Theorem Theorem67_1 : ∀ f1 f2, f1 > f2 -> ∃ f3, (f2 + f3) ~ f1.
Proof.
  intros; destruct f1 as [x1 x2], f2 as [y1 y2].
  red in H; simpl in H. red in H; destruct H as [z H1].
  exists (z/(x2 · y2)); red; simpl. repeat rewrite <- Theorem31.
  rewrite H1. repeat rewrite Theorem30'; repeat rewrite Theorem31.
  rewrite (Theorem29 y2 x2); auto.
Qed.

Theorem Theorem67_2 : ∀ f1 f2 f3 f4, (f2 + f3) ~ f1 ->
  (f2 + f4) ~ f1 -> f3 ~ f4.
Proof.
  intros; apply Theorem63_2 with (f3:=f2); apply (@Theorem39 _ f1).
  - clear H0; eapply Theorem39; eauto; apply Theorem58.
  - apply Theorem38 in H0; eapply Theorem39; eauto; apply Theorem58.
Qed.

Definition Minus_F f1 f2 : (f1>f2) -> Fra :=
  match f1,f2 with x1/x2,y1/y2 => 
    λ l, (((x1 · y2) - (y1 · x2)) l)/(x2 · y2) end.

Notation " f1 - f2 " := (Minus_F f1 f2).

Lemma D14 : ∀ f1 f2 l, ((f1 - f2) l) + f2 ~ f1.
Proof.
  intros; destruct f1, f2; simpl; red; simpl.
  rewrite (Theorem29 (n0 · n2) n2), (Theorem29 n0 n2).
  repeat rewrite <- Theorem31; apply Theorem32_2.
  rewrite (Theorem29 (n1 · n2) n0), <- Theorem31, <- Theorem30'.
  apply Theorem32_2; rewrite (Theorem29 n0 n1); Simpl_N.
Qed.

(* SECTION IV Multiplication *)

Definition Times_F f1 f2 := 
  match f1,f2 with x1/x2,y1/y2 => (x1 · y1)/(x2 · y2) end.
Notation " f1 · f2 " := (Times_F f1 f2).

Lemma Lemma_T68 : ∀ x y z u, 
  (Times_N (Times_N x y) (Times_N z u)) = 
  (Times_N (Times_N x z) (Times_N y u)).
Proof.
 intros; repeat rewrite <- Theorem31; apply Theorem32_2.
 repeat rewrite Theorem31; rewrite (Theorem29 z y); auto.
Qed.

Theorem Theorem68 : ∀ {f1 f2 f3 f4},
  f1 ~ f2 -> f3 ~ f4 -> (f1 · f3) ~ (f2 · f4).
Proof.
  intros; destruct f1 as [x1 x2], f2 as [y1 y2],
    f3 as [z1 z2], f4 as [u1 u2]. unfold Equal_F in *; simpl in *.
  apply Theorem32_2 with (z:=(Times_N z1 u2)) in H.
  pattern (Times_N z1 u2) at 2 in H; rewrite H0, Lemma_T68 in H.
  rewrite H; apply Lemma_T68.
Qed.

Theorem Theorem69 : ∀ f1 f2, (f1 · f2) ~ (f2 · f1).
Proof.
  intros; destruct f1 as [x1 x2], f2 as [y1 y2]; red; simpl.
  rewrite (Theorem29 x2 y2); apply Theorem32_2; apply Theorem29.
Qed.

Theorem Theorem70 : ∀ f1 f2 f3, ((f1 · f2) · f3) ~ (f1 · (f2 · f3)).
Proof.
  intros; destruct f1 as [x1 x2], f2 as [y1 y2], f3 as [z1 z2].
  red; simpl; repeat rewrite Theorem31; constructor.
Qed.

Theorem Theorem71 : ∀ f1 f2 f3,
  (f1 · (f2 + f3)) ~ ((f1 · f2) + (f1 · f3)).
Proof.
  intros; destruct f1 as [x1 x2], f2 as [y1 y2], f3 as [z1 z2].
  red; simpl. rewrite (Theorem29 x2 z2), (Theorem29 x2 y2).
  rewrite <- (Theorem31 _ y2), <- (Theorem31 (Times_N x1 y1)).
  rewrite <- Theorem30', Theorem30, (Theorem31 x1), (Theorem31 x1).
  rewrite (Theorem31 _ _ (Times_N x2 (Times_N y2 z2))).
  f_equal; rewrite Lemma_T68, <- (Theorem31 x2); apply Theorem29.
Qed.

Theorem Theorem72_1 : ∀ {f1 f2} f3,
  f1 > f2 -> (f1 · f3) > (f2 · f3).
Proof.
  intros; destruct f1 as [x1 x2], f2 as [y1 y2], f3 as [z1 z2].
  unfold IGT_F in *; simpl in *.
  apply Theorem32_1 with (z:=(Times_N z1 z2)) in H.
  rewrite Lemma_T68 in H. rewrite <- (Lemma_T68 y1 _ _ _); auto.
Qed.

Theorem Theorem72_2 : ∀ {f1 f2} f3, 
  f1 ~ f2 -> (f1 · f3) ~ (f2 · f3).
Proof.
  intros; eapply Theorem68; eauto; autoF.
Qed.

Theorem Theorem72_3 : ∀ {f1 f2} f3, 
  f1 < f2 -> (f1 · f3) < (f2 · f3).
Proof.
  intros; apply Theorem42; apply Theorem72_1; now apply Theorem43.
Qed.

Theorem Theorem73_1 : ∀ f1 f2 f3, (f1 · f3) > (f2 · f3) -> f1 > f2.
Proof.
  intros; destruct (Theorem41 f1 f2) as [H0 | [H0 | H0]]; auto.
  - apply (Theorem72_2 f3) in H0; EGF H0 H.
  - apply (Theorem72_3 f3) in H0; LGF H0 H.
Qed.

Theorem Theorem73_2 : ∀ f1 f2 f3, (f1 · f3) ~ (f2 · f3) -> f1 ~ f2.
Proof.
  intros; destruct (Theorem41 f1 f2) as [H0 | [H0 | H0]]; auto.
  - apply (Theorem72_1 f3) in H0; EGF H H0.
  - apply (Theorem72_3 f3) in H0; ELF H H0.
Qed.

Theorem Theorem73_3 : ∀ f1 f2 f3, (f1 · f3) < (f2 · f3) -> f1 < f2.
Proof.
  intros; destruct (Theorem41 f1 f2) as [H0 | [H0 | H0]]; auto.
  - apply (Theorem72_2 f3) in H0; ELF H0 H.
  - apply (Theorem72_1 f3) in H0; LGF H H0.
Qed.

Theorem Theorem74 : ∀ f1 f2 f3 f4,
  f1 > f2 -> f3 > f4 -> (f1 · f3) > (f2 · f4).
Proof.
  intros; apply (Theorem72_1 f3) in H; apply (Theorem72_1 f2) in H0.
  pose proof (Theorem44 H (Theorem37 (f1 · f3)) (Theorem69 f2 f3)).
  pose proof (Theorem44 H0 (Theorem37 (f3 · f2)) (Theorem69 f4 f2)).
  apply Theorem42 in H1; apply Theorem42 in H2; apply Theorem43.
  eapply Theorem50; eauto.
Qed.

Theorem Theorem75 : ∀ f1 f2 f3 f4, (f1 ≳ f2 /\ f3 > f4) \/
  (f1 > f2 /\ f3 ≳ f4) -> (f1 · f3) > (f2 · f4).
Proof.
  intros; destruct H as [[[H | H] H0] | [H [H0 | H0]]].
  - apply Theorem74; auto.
  - apply (Theorem72_1 f1) in H0; apply (Theorem72_2 f4) in H.
    eapply Theorem44; eauto; try apply Theorem69.
    eapply Theorem39; eauto; apply Theorem69.
  - apply Theorem74; auto.
  - apply (Theorem72_1 f3) in H; apply (Theorem72_2 f2) in H0.
    eapply Theorem44; eauto; try apply Theorem69; autoF.
    apply (@Theorem39 _ (f3·f2)); try apply Theorem69.
    apply (@Theorem39 _ (f4·f2)); try apply Theorem69; autoF.
Qed.
 
Theorem Theorem76 : ∀ f1 f2 f3 f4, 
  (f1 ≳ f2 /\ f3 ≳ f4) -> (f1 · f3) ≳ (f2 · f4).
Proof.
  intros; destruct H, H.
  - left; apply Theorem75; auto.
  - destruct H0.
    + left; apply Theorem75; left; split; auto; red; tauto.
    + right; apply (Theorem72_2 f3) in H.
      apply (Theorem72_2 f2) in H0.
      apply (@Theorem39 _ (f2·f3)); auto.
      apply (@Theorem39 _ (f3·f2)); try apply Theorem69.
      apply (@Theorem39 _ (f4·f2)); try apply Theorem69; auto.
Qed.

Theorem Theorem77 : ∀ f1 f2, ∃ f3, (f2 · f3) ~ f1.
Proof.
  intros; destruct f1 as [x1 x2], f2 as [y1 y2].
  exists ((Times_N x1 y2)/(Times_N x2 y1)); red; simpl.
  rewrite (Theorem29 x2 _); repeat rewrite <- Theorem31; f_equal.
  rewrite Theorem31; apply Theorem29.
Qed.

Theorem Theorem77' : ∀ f1 f2 f3 f4, 
  (f2 · f3) ~ f1 -> (f2 · f4) ~ f1 -> f3 ~ f4.
Proof.
  intros; pose proof (Theorem39 H (Theorem38 _ _ H0)).
  apply Theorem73_2 with (f3:=f2).
  apply (@Theorem39 _ (f2·f3)); try apply Theorem69.
  apply (@Theorem39 _ (f2·f4)); try apply Theorem69; auto.
Qed.

(* SECTION V Rational Numbers and Integers *)

Definition Eqf f := /{ f1 | f1 ~ f /}.
Definition Eqf_p F := ∃ f, Same_Ensemble (Eqf f) F.

Record Rat : Type := mkrat {
  F_Ens :> Ensemble Fra;
  ratp : Eqf_p F_Ens }.

Definition Equal_Pr' (X Y :Rat) := Same_Ensemble X Y.
Definition Equal_Pr (X Y :Rat) := ∀ f1 f2, 
  f1 ∈ X -> f2 ∈ Y -> f1 ~ f2.

Definition fsr (f :Fra) : Rat.
  apply mkrat with (Eqf f); exists f; red; intros; split; auto.
Defined.

Lemma Eqf_Ne : ∀ {f}, f ∈ (Eqf f).
Proof.
  intros; constructor; autoF.
Qed.

Lemma Rat_Ne : ∀ X :Rat, ∃ f, f ∈ X.
Proof.
  intros; destruct X as [sf [f H]].
  exists f; rewrite <- (ens_ext H).
  constructor; autoF.
Qed.

Ltac exel X f H := destruct (Rat_Ne X) as [f H].

Corollary eq0 : ∀ X Y, Equal_Pr' X Y <-> Equal_Pr X Y.
Proof.
  intros; split; intros; red; intros.
  - apply ens_ext in H; rewrite H in H0.
    destruct Y as [sf [f H2]]; rewrite <- (ens_ext H2) in *.
    destruct H0, H1; eapply Theorem39; eauto; autoF.
  - destruct X as [sf1 [f1 H0]], Y as [sf2 [f2 H1]].
    assert (Same_Ensemble (Eqf f1) sf1); auto.
    apply ens_ext in H2; subst sf1.
    assert (Same_Ensemble (Eqf f2) sf2); auto.
    apply ens_ext in H2; subst sf2. 
    pose proof (H _ _ Eqf_Ne Eqf_Ne).
    red; intros; split; intros; destruct H3; constructor.
    + eapply Theorem39; eauto.
    + eapply Theorem39; eauto; autoF.
Qed.

Definition No_Equal_Pr X Y :=  ~ Equal_Pr X Y.

Notation " X ≡ Y " := (Equal_Pr X Y) (at level 60).

Lemma eq1 : ∀ {X Y :Rat}, X ≡ Y -> X = Y.
Proof.
  intros; apply eq0 in H; red in H; apply ens_ext in H.
  destruct X, Y; simpl in H; subst F_Ens0.
  rewrite (proof_irr ratp0 ratp1); auto.
Qed.

Lemma Ratp : ∀ X :Rat, ∃ f, Equal_Pr (fsr f) X.
Proof.
  intros; destruct X as [sf [f H]]; exists f.
  red; simpl; intros; apply H in H1; destruct H0, H1.
  eapply Theorem39; eauto; autoF.
Qed.

Ltac chan X f H := destruct (Ratp X) as [f H]; 
  apply eq1 in H; subst X.

Theorem Theorem78 : ∀ X, X ≡ X.
Proof.
  intros; red; intros; chan X f H1.
  destruct H, H0; eapply Theorem39; eauto; autoF.
Qed.

Theorem Theorem79 : ∀ X Y, X ≡ Y -> Y ≡ X.
Proof.
  intros; red; intros; apply Theorem38.
  red in H; eapply H; eauto.
Qed.

Ltac autoPr := try apply Theorem79; try apply Theorem78; auto.

Theorem Theorem80 : ∀ X Y Z, X ≡ Y -> Y ≡ Z -> X ≡ Z.
Proof.
  intros; red; intros; chan Y f H3.
  generalize (H0 f _ Eqf_Ne H2) (H _ f H1 Eqf_Ne); intros.
  eapply Theorem39; eauto.
Qed.

Definition IGT_Pr (X Y:Rat) := ∀ f1 f2, f1∈X -> f2∈Y -> f1 > f2.
Notation " x > y " := (IGT_Pr x y).

Definition ILT_Pr (X Y:Rat) := ∀ f1 f2, f1∈Y -> f2∈X -> f2 < f1.
Notation " x < y " := (ILT_Pr x y).

Theorem Theorem81 : ∀ X Y, X ≡ Y \/ X > Y \/ X < Y.
Proof.
  intros. chan X f1 H. chan Y f2 H0.
  destruct (Theorem41 f1 f2) as [H | [H | H]].
  - left; red; intros; destruct H0, H1.
    eapply Theorem39; eauto; eapply Theorem39; eauto; autoF.
  - right; left; red; intros; destruct H0, H1.
    eapply Theorem44; eauto; autoF.
  - right; right; red; intros; destruct H0, H1.
    eapply Theorem45; eauto; autoF.
Qed.

Lemma OrdPr1 : ∀ {X Y}, X ≡ Y -> X > Y -> False.
Proof.
  intros; red in H, H0. exel X f1 H1; exel Y f2 H2.
  EGF (H _ _ H1 H2) (H0 _ _ H1 H2).
Qed.

Lemma OrdPr2 : ∀ {X Y}, X ≡ Y -> X < Y -> False.
Proof.
  intros; red in H, H0. exel X f1 H1; exel Y f2 H2.
  ELF (H _ _ H1 H2) (H0 _ _ H2 H1).
Qed.

Lemma OrdPr3 : ∀ {X Y}, X < Y -> X > Y -> False.
Proof.
  intros; red in H, H0. exel X f1 H1; exel Y f2 H2.
  LGF (H _ _ H2 H1) (H0 _ _ H1 H2).
Qed.

Ltac EGPr H H1 := destruct (OrdPr1 H H1).
Ltac ELPr H H1 := destruct (OrdPr2 H H1).
Ltac LGPr H H1 := destruct (OrdPr3 H H1).

Theorem Theorem82 : ∀ {X Y}, X > Y -> Y < X.
Proof.
  intros; auto.
Qed.

Theorem Theorem83 : ∀ {X Y}, X < Y -> Y > X.
Proof.
  intros; auto.
Qed.

Definition IGE_Pr X Y := (X > Y) \/ (X ≡ Y).
Notation " x ≧ y " := (IGE_Pr x y) (at level 55).

Definition ILE_Pr X Y := (X < Y) \/ (X ≡ Y).
Notation " x ≦ y " := (ILE_Pr x y) (at level 55).

Theorem Theorem84 : ∀ X Y, X ≧ Y -> Y ≦ X.
Proof.
  intros; destruct H; red; try tauto; right; apply Theorem79; auto.
Qed.

Theorem Theorem85 : ∀ X Y, X ≦ Y -> Y ≧ X.
Proof.
  intros; destruct H; red; try tauto; right; apply Theorem79; auto.
Qed.

Theorem Theorem86 : ∀ X Y Z, X < Y -> Y < Z -> X < Z.
Proof.
  intros; red in H, H0|- *; intros.
  exel Y f3 H3; eapply Theorem50; eauto.
Qed.

Theorem Theorem87 : ∀ X Y Z,
  (X ≦ Y /\ Y < Z) \/ (X < Y /\ Y ≦ Z) -> X < Z.
Proof.
  intros; red; intros. assert ( ∀ X Y,
    X ≦ Y <-> ∀ f1 f2, f1 ∈ X -> f2 ∈ Y -> ILE_F f1 f2) as G.
  { split; intros; red.
    - destruct H2; auto.
    - destruct (Theorem81 X0 Y0) as [H3 | [H3 | H3]]; auto.
      red in H3; exel X0 f1' H4; exel Y0 f2' H5.
      generalize (H2 _ _ H4 H5) (H3 _ _ H4 H5); intros.
      destruct H6; try LGF H6 H7; EGF H6 H7. }
  exel Y f3 H2; destruct H as [[H H3] | [H H3]].
  - eapply G in H; eauto. eapply Theorem51; eauto.
  - eapply G in H3; eauto. eapply Theorem51; eauto.
Qed.

Theorem Theorem88 : ∀ X Y Z, X ≦ Y -> Y ≦ Z -> X ≦ Z.
Proof.
  intros; destruct H0.
  - left; eapply Theorem87; eauto. - rewrite <- (eq1 H0); auto.
Qed.

Theorem Theorem89 : ∀ X, ∃ Z, Z > X.
Proof.
  intros; chan X f H.
  destruct (Theorem53 f) as [f1 H]; exists (fsr f1).
  red; intros; destruct H0, H1. eapply Theorem44; eauto; autoF.
Qed.

Theorem Theorem90 : ∀ X, ∃ Z, Z < X.
Proof.
  intros; chan X f H.
  destruct (Theorem54 f) as [f1 H]; exists (fsr f1).
  red; intros; destruct H0, H1. eapply Theorem44; eauto; autoF.
Qed.

Theorem Theorem91 : ∀ X Y, X < Y -> ∃ Z, X < Z /\ Z < Y.
Proof.
  intros; chan X f1 H0; chan Y f2 H0.
  pose proof (H _ _ Eqf_Ne Eqf_Ne).
  destruct (Theorem55 f1 f2 H0) as [f3 H1], H1.
  exists (fsr f3); split; red; intros; destruct H3, H4.
  - apply (@Theorem45 f1 f3 f4 f0); autoF.
  - eapply Theorem44; eauto; autoF.
Qed.

Definition Plus_Pr (X Y :Rat) : Rat.
  apply mkrat with 
    (/{ f | ∃ f1 f2, f1 ∈ X /\ f2 ∈ Y /\ f ~ (f1 + f2) /}).
  chan X f1 H; chan Y f2 H. red; exists (f1 + f2).
  red; split; red; intros; destruct H; constructor.
  - exists f1, f2; repeat split; auto.
  - destruct H as [f3 [f4 H]], H, H0, H, H0.
    eapply Theorem39; eauto; eapply Theorem56; eauto.
Defined.

Notation " X + Y " := (Plus_Pr X Y).

Ltac chan1 H H2 := pose proof ((Theorem78 _) _ _ H H2).

Theorem Theorem92 : ∀ {X Y}, X + Y ≡ Y + X.
Proof.
  intros; red; intros; repeat destruct H, H0; destruct H1, H2.
  chan1 H2 H; chan1 H0 H1.
  apply (@Theorem39 _ (Plus_F x x1)); auto.
  apply (@Theorem39 _ (Plus_F x0 x2)); autoF.
  apply (@Theorem39 _ (Plus_F x1 x)); try apply Theorem58.
  eapply Theorem56; auto.
Qed.

Theorem Theorem93 : ∀ {X Y Z}, ((X + Y) + Z) ≡ (X + (Y + Z)).
Proof.
  intros; red; intros; repeat destruct H, H0, H.
  destruct H1, H2, H3; repeat destruct H2; destruct H7.
  chan1 H0 H; clear H H0. chan1 H2 H3; clear H2 H3.
  chan1 H7 H1; clear H1 H7.
  apply (@Theorem39 _ (Plus_F x x0)); auto.
  apply (@Theorem39 _ (Plus_F x1 x2)); autoF.
  apply (@Theorem39 _ (Plus_F x1 (Plus_F x5 x6))).
  { eapply Theorem56; eauto; apply Theorem37. }
  apply (@Theorem39 _ (Plus_F (Plus_F x3 x4) x0)).
  - apply (@Theorem39 _ (Plus_F (Plus_F x1 x5) x6)).
    { apply Theorem38; apply Theorem59. }
    repeat apply Theorem56; auto.
  - eapply Theorem56; eauto; autoF.
Qed.

Theorem Theorem94 : ∀ X Y, X + Y > X.
Proof.
  intros; red; intros; repeat destruct H; destruct H1.
  chan1 H H0; apply Theorem38 in H2.
  apply (Theorem44 (Theorem60 x x0) ); auto.
Qed.

Theorem Theorem95 : ∀ X Y Z, X > Y -> X + Z > Y + Z.
Proof.
  intros; red; intros; repeat destruct H0, H1; destruct H2, H3.
  red in H; generalize (H _ _ H0 H1); intros.
  chan1 H2 H3; apply Theorem38 in H4; apply Theorem38 in H5.
  apply (@Theorem44 (Plus_F x x1) (Plus_F x0 x2)); auto.
  apply Theorem65; right; split; auto; right; auto.
Qed.

Theorem Theorem96_1 : ∀ X Y Z, X > Y-> X + Z > Y + Z.
Proof.
  intros; apply Theorem95; auto.
Qed.

Theorem Theorem96_2 : ∀ X Y Z, X ≡ Y -> X + Z ≡ Y + Z.
Proof.
  intros; rewrite (eq1 H); apply Theorem78.
Qed.

Theorem Theorem96_3 : ∀ X Y Z, X < Y-> X + Z < Y + Z.
Proof.
  intros; apply Theorem96_1; auto.
Qed.

Theorem Theorem97_1 : ∀ X Y Z, X + Z > Y + Z -> X > Y.
Proof.
  intros; destruct (Theorem81 X Y) as [H0 | [H0 | H0]]; auto.
  - apply Theorem96_2 with (Z:=Z) in H0; EGPr H0 H.
  - apply Theorem96_3 with (Z:=Z) in H0; LGPr H0 H.
Qed.

Theorem Theorem97_2 : ∀ X Y Z,  X + Z ≡ Y + Z -> X ≡ Y.
Proof.
  intros; destruct (Theorem81 X Y) as [H0 | [H0 | H0]]; auto.
  - apply Theorem96_1 with (Z:=Z) in H0; EGPr H H0.
  - apply Theorem96_3 with (Z:=Z) in H0; ELPr H H0.
Qed.

Theorem Theorem97_3 : ∀ X Y Z, X + Z < Y + Z -> X < Y.
Proof.
  intros; destruct (Theorem81 X Y) as [H0 | [H0 | H0]]; auto.
  - apply Theorem96_2 with (Z:=Z) in H0; ELPr H0 H.
  - apply Theorem96_1 with (Z:=Z) in H0; LGPr H H0.
Qed.

Theorem Theorem98 : ∀ {X Y Z U}, X > Y -> Z > U -> X + Z > Y + U.
Proof.
  intros; red in H, H0 |- *; intros.
  repeat destruct H1, H2; destruct H3, H4.
  generalize (Theorem64 (H _ _ H1 H2) (H0 _ _ H3 H4)); intros.
  eapply Theorem44; eauto; autoF.
Qed.

Theorem Theorem99 : ∀ X Y Z U, 
  (X ≧ Y /\ Z > U) \/ (X > Y /\ Z ≧ U) -> X + Z > Y + U.
Proof.
  intros; destruct H as [[H H0] | [H H0]].
  - destruct H.
    + eapply Theorem98; eauto.
    + apply Theorem96_1 with (Z:=X) in H0; rewrite (eq1 H) in *.
      rewrite (eq1 Theorem92), (eq1 (@ Theorem92 Y U)); auto.
  - destruct H0.
    + eapply Theorem98; eauto.
    + rewrite (eq1 H0); apply Theorem96_1; auto.
Qed.

Theorem Theorem100 : ∀ X Y Z U, (X ≧ Y /\ Z ≧ U) -> X + Z ≧ Y + U.
Proof.
  intros; destruct H as [[H | H] H0].
  - left; eapply Theorem99; eauto.
  - rewrite (eq1 H), (eq1 Theorem92), (eq1 (@ Theorem92 Y U)).
    destruct H0.
    + left; apply Theorem96_1; auto.
    + right; apply Theorem96_2; auto.
Qed.

Theorem Theorem101 : ∀ X Y, X > Y -> ∃ U, (Y + U) ≡ X.
Proof.
  intros; chan X f1 H0; chan Y f2 H0.
  pose proof (H _ _ Eqf_Ne Eqf_Ne); apply Theorem67_1 in H0.
  destruct H0 as [f3 H0]; exists (fsr f3); red; intros; destruct H2.
  do 5 destruct H1; destruct H3, H3.
  pose proof (Theorem56 H1 H3).
  eapply Theorem39; eauto; eapply Theorem39; eauto.
  eapply Theorem39; eauto; autoF.
Qed.

Theorem Theorem101' : ∀ X Y U Z,
  (Y + U) ≡ X -> (Y + Z) ≡ X -> U ≡ Z.
Proof.
  intros; rewrite (eq1 Theorem92) in H.
  rewrite (eq1 Theorem92) in H0.
  rewrite (eq1 (Theorem79 _ _ H0)) in H.
  apply Theorem97_2 in H; auto.
Qed.

Definition Minus_Pr X Y (l:X > Y) :Rat.
  apply mkrat with 
    (/{ f | ∃ f1 f2 l, f1 ∈ X /\ f2 ∈ Y /\ f ~ ((f1 - f2) l) /}).
  red; generalize l; intros; apply Theorem101 in l.
  destruct l as [U H]. chan X f1 H0; chan Y f2 H0; chan U f3 H0.
  exists f3; red; split; intros; destruct H0; constructor.
  - pose proof (l0 _ _ Eqf_Ne Eqf_Ne).
    exists f1, f2, H1; repeat split.
    apply (@Theorem39 _ f3); auto. apply Theorem63_2 with (f3:=f2).
    apply (@Theorem39 _ f1); [ idtac | apply Theorem38; apply D14].
    apply H; try apply Eqf_Ne.
    constructor; exists f2, f3; repeat split; apply Theorem58.
  - do 5 destruct H0; destruct H1, H1.
    eapply Theorem39; eauto; autoF. apply Theorem63_2 with (f3:=x1).
    apply (@Theorem39 _ x0); [|apply Theorem38; apply D14].
    apply H; constructor; auto. exists f2, f3; repeat split.
    apply (@Theorem39 _ (Plus_F f3 f2)); try apply Theorem58.
    eapply Theorem56; eauto; autoF.
Defined.

Notation " X - Y " := (Minus_Pr X Y).

Corollary PrMi1 : ∀ X Y l, (Y - X) l + X = Y.
Proof.
  intros; apply eq1. chan X f1 H; chan Y f2 H; red; intros.
  do 10 destruct H; destruct H0, H1, H1, H2, H2.
  generalize (Theorem39 H1 (Theorem38 _ _ H2)); intros.
  pose proof (Theorem56 H4 H5).
  apply (@Theorem39 _ _ x1) in H6; try apply D14.
  generalize (Theorem39 H (Theorem38 _ _ H0)); intros.
  eapply Theorem39; eauto; eapply Theorem39; eauto.
Qed.

Corollary PrMi1' : ∀ X Y l, X + ((Y - X) l) = Y.
Proof.
  intros; now rewrite (eq1 Theorem92), PrMi1.
Qed.

Corollary PrMi2 : ∀ X Y l, ((Y + X) - X) l = Y.
Proof.
  intros; apply eq1; apply Theorem97_2 with (Z:=X).
  rewrite (PrMi1 _ _ _); autoPr.
Qed.

Corollary PrMi2' : ∀ X Y l, ((X + Y) - X) l = Y.
Proof.
  intros; apply eq1; apply Theorem97_2 with (Z:=X).
  rewrite (PrMi1 _ _ _); apply Theorem92.
Qed.

Hint Rewrite PrMi1 PrMi1' PrMi2 PrMi2' : Prat.
Ltac Simpl_Pr := autorewrite with Prat; auto.
Ltac Simpl_Prin H := autorewrite with Prat in H; auto.

Definition Times_Pr (X Y :Rat) : Rat.
  apply mkrat with 
    (/{ f | ∃ f1 f2, f1 ∈ X /\ f2 ∈ Y /\ f ~ (f1 · f2) /}).
  chan X f1 H; chan Y f2 H. red; exists (f1 · f2).
  red; split; red; intros; destruct H; constructor.
  - exists f1, f2; repeat split; auto.
  - destruct H as [f3 [f4 H]], H, H0, H, H0.
    pose proof (Theorem68 H H0). eapply Theorem39; eauto.
Defined.
Notation " X · Y " := (Times_Pr X Y).

Theorem Theorem102 : ∀ {X Y}, X · Y ≡ Y · X.
Proof.
  intros; red; intros; repeat destruct H, H0; destruct H1, H2.
  chan1 H2 H; chan1 H0 H1.
  apply (@Theorem39 _ (Times_F x x1)); auto.
  apply Theorem38, (@Theorem39 _ (Times_F x0 x2)); auto.
  apply (@Theorem39 _ (Times_F x1 x)); try apply Theorem69.
  eapply Theorem68; auto.
Qed.

Theorem Theorem103 : ∀ {X Y Z}, ((X · Y) · Z) ≡ (X · (Y · Z)).
Proof.
  intros; red; intros; repeat destruct H, H0, H.
  destruct H1, H2, H3; repeat destruct H2; destruct H7.
  chan1 H0 H; clear H H0. chan1 H2 H3; clear H2 H3.
  chan1 H7 H1; clear H1 H7.
  apply (@Theorem39 _ (Times_F x x0)); auto.
  apply (@Theorem39 _ (Times_F x1 x2)); autoF.
  apply (@Theorem39 _ (Times_F x1 (Times_F x5 x6))).
  { eapply Theorem68; eauto; apply Theorem37. }
  apply (@Theorem39 _ (Times_F (Times_F x3 x4) x0)).
  - apply (@Theorem39 _ (Times_F (Times_F x1 x5) x6)).
    { apply Theorem38; apply Theorem70. }
    repeat apply Theorem68; auto.
  - eapply Theorem68; eauto; autoF.
Qed.

Theorem Theorem104 : ∀ {X Y Z},
  (X · (Y + Z)) ≡ ((X · Y) + (X · Z)).
Proof.
  intros; red; intros; repeat destruct H, H0.
  destruct H1, H2; repeat destruct H0, H1, H2; destruct H5, H6, H7.
  chan1 H H0; chan1 H0 H2; clear H H0 H2.
  chan1 H1 H5; clear H1 H5.
  chan1 H6 H7; clear H6 H7.
  pose proof (Theorem68 H12 (Theorem37 x8)).
  pose proof (Theorem39 H10 (Theorem38 _ _ H1)); clear H1 H10 H12.
  pose proof (Theorem56 H H0).
  pose proof (Theorem39 H9 H1); clear H1 H9.
  pose proof (Theorem39 H3 (Theorem68 H11 H5)).
  pose proof (Theorem39 H4 (Theorem56 H8 H2)).
  apply Theorem38 in H6.
  eapply Theorem39; eauto; eapply Theorem39; eauto; apply Theorem71.
Qed.

Theorem Theorem104' : ∀ {X Y Z},
  ((Y + Z) · X) ≡ ((Y · X) + (Z · X)).
Proof.
  intros; rewrite (eq1 (Theorem102)), (eq1 (@ Theorem102 Y X)),
  (eq1 (@ Theorem102 Z X)); apply Theorem104.
Qed.

Theorem Theorem105_1 : ∀ X Y Z, X > Y -> (X · Z) > (Y · Z).
Proof.
  intros; red; intros; repeat destruct H0, H1; destruct H2, H3.
  red in H; pose proof (H _ _ H0 H1).
  chan1 H2 H3; apply Theorem38 in H4; apply Theorem38 in H5.
  apply (@Theorem44 (Times_F x x1) (Times_F x0 x2)); auto.
  apply Theorem75; right; split; auto; right; auto.
Qed.

Theorem Theorem105_2 : ∀ X Y Z, X ≡ Y -> (X · Z) ≡ (Y · Z).
Proof.
  intros; rewrite (eq1 H); autoPr.
Qed.

Theorem Theorem105_3 : ∀ X Y Z, X < Y -> (X · Z) < (Y · Z).
Proof.
  intros; apply Theorem105_1; auto.
Qed.

Theorem Theorem106_1 : ∀ X Y Z, (X · Z) > (Y · Z) -> X > Y.
Proof.
  intros; destruct (Theorem81 X Y) as [H0 | [H0 | H0]]; auto.
  - apply Theorem105_2 with (Z:=Z) in H0; EGPr H0 H.
  - apply Theorem105_3 with (Z:=Z) in H0; LGPr H0 H.
Qed.

Theorem Theorem106_2 : ∀ X Y Z, (X · Z) ≡ (Y · Z) -> X ≡ Y.
Proof.
  intros; destruct (Theorem81 X Y) as [H0 | [H0 | H0]]; auto.
  - apply Theorem105_1 with (Z:=Z) in H0; EGPr H H0.
  - apply Theorem105_3 with (Z:=Z) in H0; ELPr H H0.
Qed.

Theorem Theorem106_3 : ∀ X Y Z, (X · Z) < (Y · Z) -> X < Y.
Proof.
  intros; destruct (Theorem81 X Y) as [H0 | [H0 | H0]]; auto.
  - apply Theorem105_2 with (Z:=Z) in H0; ELPr H0 H.
  - apply Theorem105_1 with (Z:=Z) in H0; LGPr H H0.
Qed.

Theorem Theorem107 : ∀ {X Y Z U},
  X > Y -> Z > U -> (X · Z) > (Y · U).
Proof.
  intros; red in H, H0 |- *; intros.
  repeat destruct H1, H2; destruct H3, H4.
  generalize (Theorem74 _ _ _ _ (H _ _ H1 H2) (H0 _ _ H3 H4)).
  intros. eapply Theorem44; eauto; autoF.
Qed.

Theorem Theorem108 : ∀ X Y Z U, 
  (X ≧ Y /\ Z > U) \/ (X > Y /\ Z ≧ U) -> (X · Z) > (Y · U).
Proof.
  intros; destruct H as [[H H0] | [H H0]].
  - destruct H.
    + eapply Theorem107; eauto.
    + apply Theorem105_1 with (Z:=X) in H0; rewrite (eq1 H) in *.
      rewrite (eq1 Theorem102), (eq1 (@Theorem102 Y U)); auto.
  - destruct H0.
    + eapply Theorem107; eauto.
    + rewrite (eq1 H0); apply Theorem105_1; auto.
Qed.

Theorem Theorem109 : ∀ X Y Z U,
  (X ≧ Y /\ Z ≧ U) -> (X · Z) ≧ (Y · U).
Proof.
  intros; destruct H as [[H | H] H0].
  - left; eapply Theorem108; eauto.
  - rewrite (eq1 H), (eq1 Theorem102), (eq1 (@Theorem102 Y U));
    auto. destruct H0.
    + left; apply Theorem105_1; auto.
    + right; apply Theorem105_2; auto.
Qed.

Theorem Theorem110 : ∀ X Y, ∃ U, Y · U ≡ X.
Proof.
  intros; chan X f1 H; chan Y f2 H.
  destruct (Theorem77 f1 f2) as [f3 H].
  exists (fsr f3); red; intros.
  do 5 destruct H0; destruct H1, H2, H2.
  generalize (Theorem39 H1 (Theorem38 _ _ H)); intros.
  eapply Theorem39; eauto; eapply Theorem39; eauto.
  eapply Theorem68; eauto. autoF.
Qed.

Theorem Theorem110' : ∀ X Y U Z, 
  (Y · U) ≡ X -> (Y · Z) ≡ X -> U ≡ Z .
Proof.
  intros; rewrite (eq1 Theorem102) in H.
  rewrite (eq1 Theorem102) in H0.
  rewrite (eq1 (Theorem79 _ _ H0)) in H.
  apply Theorem106_2 in H; auto.
Qed.

Theorem Theorem111_1 : ∀ x y,
  (fsr (x/1)) > (fsr (y/1)) -> IGT_N x y.
Proof.
  intros. exel (fsr (x / 1)) f1 H0; exel (fsr (y / 1)) f2 H1.
  pose proof (H _ _ H0 H1); destruct H0, H1.
  eapply Theorem45 in H2; eauto.
  red in H2; simpl in H2; Simpl_Nin H2.
Qed.

Theorem Theorem111_2 : ∀ x y, (fsr (x/1)) ≡ (fsr (y/1)) -> x = y.
Proof.
  intros. exel (fsr (x / 1)) f1 H0; exel (fsr (y / 1)) f2 H1.
  pose proof (H _ _ H0 H1); destruct H0, H1.
  pose proof (Theorem39 (Theorem38 _ _ H0) (Theorem39 H2 H1)).
  red in H3; simpl in H3; Simpl_Nin H3.
Qed.

Theorem Theorem111_3 : ∀ x y, 
  (fsr (x/1)) < (fsr (y/1)) -> ILT_N x y.
Proof.
  intros. apply Theorem111_1; auto.
Qed.

Theorem Theorem111_1' : ∀ x y,
  IGT_N x y -> (fsr (x/1)) > (fsr (y/1)).
Proof.
  intros; red; intros; destruct H0, H1.
  apply Theorem38 in H0; apply Theorem38 in H1.
  eapply Theorem45; eauto. red; simpl; Simpl_N.
Qed.

Theorem Theorem111_2' : ∀ x y, x = y -> (fsr (x/1)) = (fsr (y/1)).
Proof.
  intros; now subst x.
Qed.

Theorem Theorem111_3' : ∀ x y,
  ILT_N x y -> (fsr (x/1)) < (fsr (y/1)).
Proof.
  intros; apply Theorem111_1'; auto.
Qed.

Definition Inter x := fsr (x/1).

Theorem Theorem112_1 : ∀ x y,
  (Inter x) + (Inter y) ≡ (Inter(Plus_N x y)).
Proof.
  intros; red; intros; do 5 destruct H; destruct H0, H1, H1.
  eapply Theorem39; eauto; apply Theorem38 in H0. 
  eapply Theorem39; eauto. generalize (Theorem56 H H1); intros.
  eapply Theorem39; eauto; simpl; Simpl_N; apply Theorem37.
Qed.

Theorem Theorem112_2 : ∀ x y, 
  (Inter x) · (Inter y) ≡ (Inter (Times_N x y)).
Proof.
  intros; red; intros; do 5 destruct H; destruct H0, H1, H1.
  eapply Theorem39; eauto; apply Theorem38 in H0.
  eapply Theorem39; eauto. generalize (Theorem68 H H1); intros.
  eapply Theorem39; eauto; simpl; Simpl_N; apply Theorem37.
Qed.

Definition ℳ113 := /{ X | ∃ x, X ≡ (Inter x) /}.

Theorem Theorem113_1 : (Inter 1) ∈ ℳ113.
Proof.
  constructor; exists 1; autoPr.
Qed.

Theorem Theorem113_2 : ∀ x y z,
  y ≡ (Inter x`) -> z ≡ (Inter x`) -> y ≡ z.
Proof.
  intros; apply Theorem79 in H0; eapply Theorem80; eauto.
Qed.

Theorem Theorem113_3 : ∀ x, ~ (Inter 1) ≡ (Inter x`).
Proof.
  intros; intro. repeat red in H.
  pose proof (H  _ _ Eqf_Ne Eqf_Ne); simpl in H0; Simpl_Nin H0.
  apply (AxiomIII x); auto.
Qed.

Theorem Theorem113_4 : ∀ x y, (Inter x`) ≡ (Inter y`) -> x = y.
Proof.
  intros; repeat red in H.
  pose proof (H  _ _ Eqf_Ne Eqf_Ne); simpl in H0; Simpl_Nin H0.
  apply AxiomIV in H0; auto.
Qed.

Theorem Theorem113_5 : ∀ ℳ, (Inter 1) ∈ ℳ  /\ 
  (∀ x, (Inter x) ∈ ℳ -> (Inter x`) ∈ ℳ) -> ∀ x, (Inter x) ∈ ℳ.
Proof.
  intros; destruct H. set (ℳ0 := /{ x | (Inter x) ∈ ℳ /}).
  assert (1 ∈ ℳ0). { constructor; eauto. }
  assert (∀ x, x ∈ ℳ0 -> x` ∈ ℳ0); intros.
  { destruct H2; constructor; apply H0 in H2; eauto. }
  assert (∀ x, x ∈ ℳ0). { apply AxiomV; auto. }
  destruct H3 with x; auto.
Qed.

Coercion Int (x :Nat) : Rat := Inter x.

Corollary PrTi_1 : ∀ X, (X · 1) = X.
Proof.
  intros; apply eq1; chan X f H; red; intros.
  do 5 destruct H; destruct H0, H1, H1.
  eapply Theorem39; eauto.
  apply Theorem38 in H0; eapply Theorem39; eauto.
  pose proof (Theorem68 H H1). eapply Theorem39; eauto.
  destruct f; red; simpl; Simpl_N.
Qed.

Corollary PrTi1_ : ∀ X, (1 · X) = X.
Proof.
  intro; rewrite (eq1 Theorem102); apply PrTi_1.
Qed.

Corollary PrPl_1 : ∀ x :Nat, Int x + Int 1 = Int x`.
Proof.
  intros; apply eq1; red; intros.
  do 5 destruct H; destruct H0, H1, H1. eapply Theorem39; eauto.
  apply Theorem38 in H0; eapply Theorem39; eauto.
  pose proof (Theorem56 H H1).
  eapply Theorem39; eauto. red; simpl; Simpl_N.
Qed.

Hint Rewrite PrTi_1 PrTi1_ PrPl_1 : Prat.

Theorem Theorem114 : ∀ x y Z, Z ≡ (fsr (x/y)) -> (y · Z) ≡ x.
Proof.
  intros; rewrite (eq1 H); red; intros.
  do 5 destruct H0. destruct H1, H2, H2. eapply Theorem39; eauto.
  apply Theorem38 in H1; eapply Theorem39; eauto.
  pose proof (Theorem68 H0 H2). eapply Theorem39; eauto.
  red; simpl; Simpl_N; apply Theorem29.
Qed.

Definition Recip_Rat  f := match f with x/y => y/x end.

Definition Over_Pr (X Y :Rat) : Rat.
  apply (mkrat /{ f | ∃ f1 f2, f1 ∈ X /\ f2 ∈ Y /\ 
    f ~ (Times_F f1 (Recip_Rat f2)) /}).
  chan X f1 H; chan Y f2 H.
  red; exists (Times_F f1 (Recip_Rat f2)); 
  split; red; intros; destruct H; constructor.
  - exists f1, f2; repeat split; auto.
  - destruct H as [f3 [f4 H]], H, H0, H, H0.
    eapply Theorem39; eauto; eapply Theorem68; eauto.
    destruct f2, f4; red in H0|-*; simpl in *.
    rewrite Theorem29, <- H0, Theorem29; auto.
Defined.

Notation " X / Y " := (Over_Pr X Y).

Corollary PrOverP1 : ∀ X Y Z, Z ≡ Y/X <-> Z · X ≡ Y.
Proof.
  intros; chan X f1 H; chan Y f2 H; chan Z f3 H; split; red; intros.
  - do 5 destruct H0; destruct H1, H2, H2.
    pose proof (Theorem68 H0 H2). pose proof (Theorem39 H3 H4).
    eapply Theorem39; eauto.
    apply Theorem38 in H1; eapply Theorem39; eauto.
    set (M := (/{ f | ∃ f3 f6, f3 ∈ (Eqf f2) /\ 
    f6 ∈ (Eqf f1) /\ f ~ Times_F f3 (Recip_Rat f6) /})).
    assert ((Times_F f2 (Recip_Rat f1)) ∈ M).
    { constructor; exists f2, f1; repeat split. }
    pose proof (H _ _ Eqf_Ne H6).
    destruct f1, f2, f3; red in H7|-*; simpl in *.
    rewrite Theorem31 in H7|-*.
    rewrite (Theorem29 n n2), (Theorem29 n4 n0); auto.
  - do 5 destruct H1; destruct H0, H2, H2.
    set (M := (/{ f | ∃ f2 f6, f2 ∈ (Eqf f3) /\ 
    f6 ∈ (Eqf f1) /\ f ~ Times_F f2 f6 /})).
    assert ((Times_F f3 f1) ∈ M).
    { constructor; exists f3, f1; repeat split. }
    pose proof (H _ _ H4 Eqf_Ne). pose proof (Theorem68 H0 H2).
    pose proof (Theorem39 H6 H5).
    pose proof (Theorem39 H7 (Theorem38 _ _ H1)).
    clear H0; apply Theorem38 in H3; eapply Theorem39; eauto.
    destruct f0, x, x0; red in H8|-*; simpl in *.
    rewrite Theorem31 in H8|-*.
    rewrite (Theorem29 n2 n3), (Theorem29 n4 n0); auto.
Qed.

Corollary Prdt : ∀ Y X, (Y/X · X) = Y.
Proof.
  intros; apply eq1; apply PrOverP1; autoPr.
Qed.

Corollary Prtd : ∀ Y X, (X · (Y/X)) = Y.
Proof.
  intros; rewrite (eq1 Theorem102); apply Prdt.
Qed.

Corollary Prdd : ∀ X, 1/(1/X) = X.
Proof.
  intros; symmetry; apply eq1, PrOverP1; rewrite Prtd; autoPr.
Qed.

Hint Rewrite Prdt Prtd Prdd : Prat.

Corollary PrOverP2 : ∀ X Y, X < Y -> 1/Y < 1/X.
Proof.
  intros; apply Theorem106_3 with (Z:=Y); Simpl_Pr.
  apply Theorem106_3 with (Z:=X); Simpl_Pr.
  rewrite (eq1 Theorem102), <- (eq1 Theorem103); Simpl_Pr.
Qed.

Theorem Theorem115 : ∀ X Y, ∃ z :Nat, (z · X) > Y.
Proof.
  intros; destruct (Theorem89 (Over_Pr Y X)) as [Z H].
  apply Theorem105_1 with (Z:=X) in H; Simpl_Prin H.
  chan Z f H0; destruct f as [z v]; exists z; red; intros.
  do 5 destruct H0; destruct H2.
  set (M := (/{ f | ∃ f3 f4, f3 ∈ (Eqf (Over z v)) /\ 
  f4 ∈ X /\ f ~ (Times_F f3 f4) /})).
  assert ((Times_F (Over z v) x0) ∈ M).
  { constructor; exists (Over z v), x0; repeat split; auto. }
  pose proof (H _ _ H4 H1).
  pose proof (Theorem68 H0 (Theorem37 x0)).
  pose proof (Theorem38 _ _ (Theorem39 H3 H6)).
  eapply Theorem44; try apply H7; try apply Theorem37.
  eapply Theorem51; right; split; try apply H5.
  destruct v; [right; autoF|].
  left; apply Theorem72_3; red; simpl; Simpl_N. 
  exists (Times_N z v); apply Theorem6.
Qed.
