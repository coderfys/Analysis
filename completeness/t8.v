(***************************************************************************)
(*   This is part of FA_Completeness, it is distributed under the terms    *)
(*           of the GNU Lesser General Public License version 3            *)
(*                (see file LICENSE for more details)                      *)
(*                                                                         *)
(*           Copyright 2020-2022: Yaoshun Fu and Wensheng Yu.              *)
(***************************************************************************)

Require Import t7.
Require Export Seq.

Section Dedekind.

Variable Fst Snd :Ensemble Real.

Definition R_Divide := ∀ Ξ, Ξ ∈ Fst \/ Ξ ∈ Snd.

Definition ILT_FS := ∀ Ξ Γ, Ξ ∈ Fst -> Γ ∈ Snd -> Ξ < Γ.

Definition Split Ξ := 
  (∀ Γ, Γ < Ξ -> Γ ∈ Fst) /\ (∀ Γ, Γ > Ξ -> Γ ∈ Snd).

End Dedekind.

Section Constr8.

Variable (Fst Snd :Ensemble Real) (x y :Real).
Hypothesis (H :R_Divide Fst Snd) (G :ILT_FS Fst Snd).
Hypothesis (P1 :x ∈ Fst) (P2 :y ∈ Snd).

Let yx2 n := ((y-x)/(2^n))  powSeq'.

Lemma tem : ∀ z m, z - (yx2 m) < z.
Proof.
  intros. pose proof (G _ _ P1 P2). apply Theorem182_1' in H0.
  apply Theorem188_1 with (Θ:= yx2 m); Simpl_R.
  apply Pl_R; apply Pos'; auto. apply powSeq.
Qed.

Lemma tem1 : ∀ x y z, x - y = z -> x - z = y.
Proof.
  intros; apply Theorem188_2' with (Θ:=y0) in H0; Simpl_Rin H0.
  apply Theorem188_2 with (Θ:=z); Simpl_R.
  rewrite Theorem175; auto.
Qed.

Lemma caseFS : ∀ r, {r ∈ Fst} + {r ∈ Snd}.
Proof.
  intros; destruct (classicT (r ∈ Fst)); auto.
  right; destruct H with r; tauto.
Qed.

Fixpoint Codc n := 
  match n with
   | 1 => mid x y
   | m` => match (caseFS (Codc m)) with
            | left _ => (Codc m) + (yx2 n)
            | right _ => (Codc m) - (yx2 n)
           end
  end.

Fixpoint Coda n := 
  match n with
   | 1 => x
   | m` => match (caseFS (Codc m)) with
           | left _ => Codc m
           | right _ => Coda m
          end
  end.

Fixpoint Codb n := 
  match n with
   | 1 => y
   | m` => match (caseFS (Codc m)) with
            | left _ => Codb m
            | right _ => Codc m
           end
  end.

Lemma DL1 : ∀ n, Coda n ∈ Fst.
Proof.
  intros; induction n.
  - simpl; auto. - simpl; destruct caseFS; auto.
Qed.

Lemma DL2 : ∀ n, Codb n ∈ Snd.
Proof.
  intros; induction n.
  - simpl; auto. - simpl; destruct caseFS; auto.
Qed.

Lemma DL01 : ∀ n, (Codc n) - (yx2 n) = (Coda n).
Proof.
  intros; induction n.
  - simpl Codc; simpl Coda; simpl Pow. apply Midp1.
  - simpl Codc; simpl Coda; simpl Pow.
    destruct caseFS; Simpl_R. rewrite <- IHn. apply MiR.
Qed.

Lemma DL01' : ∀ n, (Codb n) - (yx2 n) = (Codc n).
Proof.
  intros; induction n.
  - simpl Codc; simpl Codb; simpl Pow. apply Midp2.
  - simpl Codc; simpl Codb. destruct caseFS; Simpl_R.
    rewrite <- IHn. apply Theorem188_2 with (Θ:= -(yx2 n`));
    Simpl_R. simpl; apply MiR.
Qed.

Lemma DL02 : ∀ n, Codc n = mid (Coda n) (Codb n).
Proof.
  intro; pose proof (DL01 n); pose proof (DL01' n).
  apply tem1 in H1; apply tem1 in H0. rewrite <- H0 in H1.
  apply Theorem188_2' with (Θ:= (Coda n)) in H1; Simpl_Rin H1.
  rewrite Theorem175 in H1.
  unfold Minus_R in H1; rewrite <- Theorem186 in H1.
  apply Theorem188_2' with (Θ:= (Codc n)) in H1; Simpl_Rin H1.
  unfold mid, RdiN; rewrite H1, <- Di_Rp; Simpl_R.
Qed.

Lemma DL3 : Increase Coda.
Proof.
  red; intros; induction m; intros; [N1F H0|].
  simpl; destruct caseFS; auto.
  - apply Theorem25 in H0; destruct H0.
    + replace m` with (Plus_N m 1) in H0; auto.
      apply Theorem20_1 in H0. apply IHm in H0.
      eapply Theorem173; eauto. left. rewrite <- DL01. apply tem.
    + replace m` with (Plus_N m 1) in H0; auto.
      apply Theorem20_2 in H0.
      subst m; left. rewrite <- DL01. apply tem.
  - apply Theorem25 in H0.
    replace m` with (Plus_N m 1) in H0; auto. destruct H0.
    + apply Theorem20_1 in H0; auto.
    + apply Theorem20_2 in H0; subst n; red; auto.
Qed.

Lemma DL4 : Decrease Codb.
Proof.
  red; intros; induction m; [N1F H0|].
  simpl; destruct (caseFS (Codc m)); auto.
  - apply Theorem25 in H0; destruct H0.
    + replace m` with (Plus_N m 1) in H0; auto.
      apply Theorem20_1 in H0; auto.
    + replace m` with (Plus_N m 1) in H0; auto.
      apply Theorem20_2 in H0. subst m; right; auto.
  - apply Theorem25 in H0.
    replace m` with (Plus_N m 1) in H0; auto. destruct H0.
    + replace m` with (Plus_N m 1) in H0; auto.
      apply Theorem20_1 in H0. apply IHm in H0.
      eapply Theorem173; eauto. left. rewrite <- DL01'. apply tem.
    + replace m` with (Plus_N m 1) in H0; auto.
      apply Theorem20_2 in H0.
      subst m; left. rewrite <- DL01'. apply tem.
Qed.

Lemma DL5a : ∀ n, (Codb n`) - (Coda n`) 
  = (((Codb n) - (Coda n))/ 2) NoO_N.
Proof.
  intros. simpl Codb; simpl Coda. destruct caseFS.
  - rewrite DL02. apply tem1. apply Midp2.
  - rewrite DL02. apply tem1. apply Midp1.
Qed.

Lemma DL5b : Minus_Seq Codb Coda = 
  λ N, ((((Codb 1) - (Coda 1)) · 2)/(2^N)) powSeq'.
Proof.
  intros; apply eq_Seq; intros; unfold Minus_Seq. induction m.
  - apply ROv_uni; rewrite Pow1; apply Theorem194.
  - apply ROv_uni; rewrite PowS, DL5a.
    rewrite Di_Rt, Theorem194, <- Theorem199; Simpl_R.
    rewrite IHm; Simpl_R.
Qed.

Lemma DL5 : Limit (Minus_Seq Codb Coda) O.
Proof.
  intros; rewrite DL5b; apply Limit_Pow'.
Qed.

Lemma DL6 : CauchySeq Coda.
Proof.
  red; intros; pose proof DL5.
  assert (∃ ξ, Limit (Minus_Seq Codb Coda) ξ); eauto.
  apply CCT in H2; pose proof (H2 _ H0); clear H2.
  destruct H3 as [N H2]; exists N; intros.
  pose proof (H2 _ _ H3 H4); unfold Minus_Seq in H5.
  assert (∀ w x y z, w ≦ x -> y ≦ z -> 
    x - w ≦ | x - w - (y - z)|) as G2; intros.
  { apply LePl_R with (z:=-w) in H6; Simpl_Rin H6.
    apply LePl_R with (z:=-z) in H7; Simpl_Rin H7.
    pattern (x0 - w) at 1; rewrite <- Theorem175', Ab5.
    - unfold Minus_R at 2; apply Theorem168; 
      apply Theorem191; red; auto.
      apply LEminus in H7; apply Theorem168' in H7; auto.
    - eapply Theorem173; eauto.   }
  destruct (Theorem10 m n) as [H6 | [H6 | H6]].
  - subst m; Simpl_R.
  - eapply Theorem172; left; split; eauto.
    pose proof (DL3 _ _ H6); pose proof (DL4 _ _ H6).
    rewrite Ab5, Mi_R', <- Theorem178, Theorem181; auto.
  - eapply Theorem172; left; split; eauto.
    pose proof (DL3 _ _ H6); pose proof (DL4 _ _ H6).
    rewrite Ab6, Mi_R'; auto.
    unfold Minus_R at 2; rewrite Theorem175, Theorem181.
    rewrite <- (Theorem177 (Codb m - Codb n)), Theorem181; Simpl_R.
Qed.

End Constr8.

Theorem DedekindCut : ∀ Fst Snd,
  R_Divide Fst Snd -> No_Empty Fst -> 
  No_Empty Snd -> ILT_FS Fst Snd -> (∃ E, Split Fst Snd E).
Proof.
  intros; destruct H0 as [A H0], H1 as [B H1].
  generalize (DL3 Fst Snd _ _ H H2 H0 H1) (DL4 Fst Snd _ _ H H2 H0 H1)
    (DL5 Fst Snd A B H) (DL6 Fst Snd _ _ H H2 H0 H1); intros.
  apply CCT in H6;  destruct H6 as [ξ H6].
  set (a:=Coda Fst Snd A B H) in *.
  set (b:=Codb Fst Snd A B H) in *. assert (Limit b ξ).
  { rewrite (SeqCon1 a b), <- Theorem175'';
    apply SeqLimPlus; auto. } exists ξ; split; intros Z H9.
  - pose proof (DL1 _ _ A B H H0). apply Theorem182_1' in H9.
    destruct H6 with (ξ - Z) as [N H10]; auto.
    pose proof (Theorem18 N 1); Simpl_Nin H11.
    apply H10 in H11; rewrite Ab6 in H11; try apply Increase_limitP; auto.
    apply Theorem183_1 in H11; repeat rewrite Theorem181 in H11.
    apply Theorem188_1' with (Θ:=ξ) in H11; Simpl_Rin H11.
    specialize H8 with N`. destruct H with Z; auto; LGR H11 (H2 _ _ H8 H12).
  - pose proof (DL2 _ _ A B H H1); apply Theorem182_1' in H9.
    destruct H7 with (Z -ξ) as [N H10]; auto.
    pose proof (Theorem18 N 1); Simpl_Nin H11.
    apply H10 in H11; rewrite Ab5 in H11; 
    try apply Decrease_limitP; auto.
    apply Theorem188_1' with (Θ:=ξ) in H11; Simpl_Rin H11.
    specialize H8 with N`. destruct H with Z; auto.
    LGR H11 (H2 _ _ H12 H8).
Qed.

Theorem DedekindCut_Unique : ∀ Fst Snd, R_Divide Fst Snd -> 
  No_Empty Fst -> No_Empty Snd -> ILT_FS Fst Snd -> 
  ∀ Z1 Z2, Split Fst Snd Z1 -> Split Fst Snd Z2 -> Z1 = Z2.
Proof.
  assert (∀ Fst Snd, R_Divide Fst Snd -> No_Empty Fst 
   -> No_Empty Snd -> ILT_FS Fst Snd -> 
    ∀ Ξ1 Ξ2, Split Fst Snd Ξ1 -> Split Fst Snd Ξ2 -> ~ Ξ1 < Ξ2).
  { intros; intro; red in H, H0, H1, H2, H3, H4; destruct H3, H4.
    pose proof (Mid_P' _ _ H5); pose proof (Mid_P _ _ H5).
    apply H6 in H8; apply H4 in H9. pose proof (H2 _ _ H9 H8). 
    apply OrdR1 in H10; tauto. }
  intros; destruct (Theorem167 Z1 Z2) as [H6 | [H6 | H6]]; auto;
  eapply H in H6; eauto; tauto.
Qed.
























