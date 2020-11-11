(***************************************************************************)
(*   This is part of FA_Completeness, it is distributed under the terms    *)
(*           of the GNU Lesser General Public License version 3            *)
(*                (see file LICENSE for more details)                      *)
(*                                                                         *)
(*           Copyright 2020-2022: Yaoshun Fu and Wensheng Yu.              *)
(***************************************************************************)

Require Import t3.
Require Export Seq.

Inductive RR := | rr : ∀ r1 r2, r1 < r2 -> RR.
Definition Fst (A :RR) := match A with rr a b l => a end.
Definition Snd (A :RR) := match A with rr a b l => b end.
Definition RRens_ooens cH := 
  /{ i | ∃ h, h ∈ cH /\ i = (Fst h | Snd h) /}.
Definition OpenCover x y cH := (x < y) /\ 
  (∀ z, z ∈ [x | y] -> (∃ h, h ∈ (RRens_ooens cH) /\ z ∈ h)).
Definition FinCover x y cH := (x < y) /\ 
  ∃ ch, ch ⊂ cH /\ fin ch /\ OpenCover x y ch.
Definition InfinCover_Only x y cH := 
  OpenCover x y cH /\ ~ FinCover x y cH.

Corollary CoverP1 : ∀ x y cH, FinCover x (mid x y) cH -> 
  FinCover (mid x y) y cH -> FinCover x y cH.
Proof.
  intros; destruct H, H1 as [R1 H1], H1, H2.
  destruct H0, H4 as [R2 H4], H4, H5.
  pose proof (Theorem171 _ _ _ H H0).
  red; split; auto; exists (Union R1 R2);
  repeat split; auto; intros.
  - red; intros; destruct H8, H8; auto.
  - apply Fin_Union; auto.
  - destruct H8, H8, (Rcase2 z (mid x y)).
    * assert (z ∈ [x | (mid x y)]). { constructor; auto. }
      apply H3 in H11; destruct H11, H11, H11, H11, H11.
      exists x0; split; auto. constructor; exists x1; split; auto.
      constructor; auto.
    * assert (z ∈ [(mid x y) | y]). { constructor; auto. }
      apply H6 in H11; destruct H11, H11, H11, H11, H11.
      exists x0; split; auto. constructor; exists x1; split; auto.
      constructor; auto.
Qed.

Corollary CoverP2 : ∀ x y cH, InfinCover_Only x y cH 
  -> {InfinCover_Only x (mid x y) cH} +
  {InfinCover_Only (mid x y) y cH}.
Proof.
  intros; destruct (classicT (InfinCover_Only x (mid x y) cH)) 
    as [H0 | H0]; auto.
  right; Absurd; apply property_not in H0; apply property_not in H1.
  destruct H, H0, H.
  - elim H0; red; split; intros.
    + apply Mid_P'; auto.
    + apply H3; destruct H4, H4; constructor; split; auto.
      eapply Theorem173; eauto; left; apply Mid_P; auto.
  - destruct H1.
    + elim H1; red; split; intros.
      * apply Mid_P; auto.
      * apply H3; destruct H4, H4; constructor; split; auto.
        eapply Theorem173; eauto; left; apply Mid_P'; auto.
    + apply -> property_not' in H0; apply -> property_not' in H1.
      elim H2; apply CoverP1; auto.
Qed.

Section Constr5.

Variable (x y :Real) (rr :Ensemble RR).
Hypothesis H :InfinCover_Only x y rr.

Let ICO_dec x y:= classicT (InfinCover_Only x y rr).
Let yx2 n := ((y-x)/(2^n))  powSeq'.

Lemma tem: ∀ z m, z - (yx2 m) < z.
Proof.
  intros; destruct H, H0. apply Theorem182_1' in H0.
  apply Theorem188_1 with (yx2 m); Simpl_R.
  apply Pl_R; apply Pos'; auto. apply powSeq.
Qed.

Lemma tem1 : ∀ x y z, x - y = z -> x - z = y.
Proof.
  intros; apply Theorem188_2' with (Θ:=y0) in H0; Simpl_Rin H0.
  apply Theorem188_2 with (Θ:=z); Simpl_R. rewrite Theorem175; auto.
Qed.

Fixpoint Codc n := 
  match n with
   | 1 => mid x y
   | m` => match ICO_dec ((Codc m) - (yx2 m)) (Codc m) with
            | left _ => (Codc m) - (yx2 n)
            | right _ => (Codc m) + (yx2 n)
           end
  end.

Fixpoint Coda n := 
  match n with
   | 1 => x
   | m` => match ICO_dec (Coda m) (Codc m) with
            | left _ => Coda m
            | right _ => Codc m
           end
  end.

Fixpoint Codb n := 
  match n with
   | 1 => y
   | m` => match ICO_dec (Coda m) (Codc m) with
            | left _ => Codc m
            | right _ => Codb m
           end
  end.

Lemma FL01 : ∀ n, (Codc n) - (yx2 n) = (Coda n).
Proof.
  intros; induction n.
  - simpl Codc; simpl Coda; simpl Pow; apply  Midp1.
  - simpl Codc; simpl Coda; simpl Pow; rewrite IHn.
    destruct ICO_dec; Simpl_R. rewrite <- IHn; apply MiR.
Qed.

Lemma FL01' : ∀ n, (Codb n) - (yx2 n) = (Codc n).
Proof.
  intros; induction n.
  - simpl Codc; simpl Codb; simpl Pow; apply Midp2.
  - simpl Codc; simpl Codb. rewrite (FL01 n).
    destruct ICO_dec; auto. 
    apply Theorem188_2 with (Θ:= - (yx2 n`)); Simpl_R.
    simpl; rewrite <- IHn; apply MiR.
Qed.

Lemma FL02 : ∀ n, Codc n = mid (Coda n) (Codb n).
Proof.
  intro; pose proof (FL01 n); pose proof (FL01' n).
  apply tem1 in H1; apply tem1 in H0. rewrite <- H0 in H1.
  apply Theorem188_2' with (Θ:= (Coda n)) in H1; Simpl_Rin H1.
  rewrite Theorem175 in H1.
  unfold Minus_R in H1; rewrite <- Theorem186 in H1.
  apply Theorem188_2' with (Θ:= (Codc n)) in H1; Simpl_Rin H1. 
  unfold mid, RdiN; rewrite H1, <- Di_Rp; Simpl_R.
Qed.

Lemma FL1 : ∀ n, InfinCover_Only (Coda n) (Codb n) rr.
Proof.
  intros; induction n; simpl; auto. simpl; destruct ICO_dec; auto.
  apply CoverP2 in IHn; rewrite <- FL02 in IHn. destruct IHn; tauto.
Qed.

Lemma FL2 : Increase Coda.
Proof.
  red; intros; induction m; intros; [N1F H0|].
  rename H0 into H1; rename IHm into H0. apply Theorem26 in H1.
  assert ((Coda m) ≦ (Coda m`)).
  { simpl; destruct ICO_dec.
    - red; auto. - left; rewrite <- FL01; apply tem. }
  destruct H1.
  - apply H0 in H1; eapply Theorem173; eauto. - subst n; auto.
Qed.

Lemma FL3 : Decrease Codb.
Proof.
  red; intros; induction m; intros; [N1F H0|].
  rename H0 into H1; rename IHm into H0. apply Theorem26 in H1.
  assert ((Codb m`) ≦ (Codb m)).
  { simpl; destruct ICO_dec.
    - left; rewrite <- FL01'; apply tem. - red; auto. }
  destruct H1.
  - eapply Theorem173; eauto. - subst n; auto.
Qed.

Lemma FL4 : ILT_Seq Coda Codb.
Proof.
  red; intros; destruct (FL1 n), H0; left; auto.
Qed.

Lemma FL5a : ∀ n, 
  (Codb n`) - (Coda n`) = (((Codb n) - (Coda n))/ 2) NoO_N.
Proof.
  intros; simpl Codb; simpl Coda. destruct ICO_dec.
  - rewrite FL02. apply tem1. apply Midp1.
  - rewrite FL02. apply tem1. apply Midp2.
Qed.

Lemma FL5b : Minus_Seq Codb Coda = 
  λ n, (((y - x) · 1`) / (2^n)) powSeq'.
Proof.
  apply eq_Seq; intros; unfold Minus_Seq; induction m.
  - apply ROv_uni; rewrite Pow1; apply Theorem194.
  - apply ROv_uni; rewrite PowS, FL5a.
    rewrite Di_Rt, Theorem194, <- Theorem199; Simpl_R.
    rewrite IHm; Simpl_R.
Qed.

Lemma FL5 : Limit (Minus_Seq Codb Coda) O.
Proof.
  rewrite FL5b; apply Limit_Pow'.
Qed.

End Constr5.

Inductive fin1 (r :RR) x y :=
  | fin1_intro : ILT_N x 2 -> y = r -> fin1 r x y.

Theorem FinCoverT : ∀ x y cH, OpenCover x y cH -> FinCover x y cH.
Proof.
  intros; Absurd.
  assert (InfinCover_Only x y cH); unfold InfinCover_Only; auto.
  generalize (FL1 x y cH H1) (FL2 x y cH H1)
    (FL3 x y cH H1) (FL4 x y cH H1) (FL5 x y cH); intros.
  set (a:=(Coda x y cH)) in *; set (b:=(Codb x y cH)) in *.
  assert (NestedIntervals a b). { red; repeat split; auto. }
  clear H3 H4 H6.
  destruct (Cor_NIT _ _ H7) as [ξ [H6 H8]], H.
  assert (ξ ∈ [x | y]).
  { destruct H6 with 1; constructor; split; 
    eapply Theorem173; red; eauto. }
  destruct (H3 _ H4) as [R [H9 H10]], H9, H9 as [rr0 [H9 H11]].
  remember rr0 as rr'. destruct rr' as [rr1 rr2 l].
  simpl in H11; subst R; destruct H10, H10.
  apply Theorem182_1' in H10. apply Theorem182_1' in H11.
  assert (R2min (ξ -rr1) (rr2 - ξ) > O).
  { destruct (Pr_min4 (ξ -rr1) (rr2 - ξ)); rewrite H12; auto. }
  apply H8 in H12. destruct H12 as [n H12].
  pose proof (H12 _ (Theorem18 n 1)); Simpl_Nin H13; clear H12.
  specialize H2 with n`; red in H2; destruct H2, H2; elim H12.
  red; split; auto.
  exists /{ r | r = rr0 /}; repeat split; intros; auto.
  + red; intros; destruct H15; subst x0 rr0; auto.
  + red; exists 2, (fin1 rr0); repeat split; try red; 
    intros; destruct H15; auto.
    * destruct H16; subst y0 z; auto.
    * exists rr0; constructor; auto.
    * exists 1; constructor; auto. apply Nlt_S_.
  + subst rr0; exists (rr1 | rr2); split.
    * constructor; exists (rr rr1 rr2 l); split; auto. constructor; auto.
    * apply H13 in H15; destruct H15, H15.
      apply (Theorem188_1' _ _ (R2min (ξ-rr1) (rr2-ξ))) in H15; Simpl_Rin H15.
      assert (z + (ξ - rr1) > ξ).
      { eapply Theorem172; right; split; eauto.
        rewrite Theorem175, (Theorem175 z). apply LePl_R; apply Pr_min2. }
      assert (z < ξ + (rr2 - ξ)).
      { eapply Theorem172; right; split; eauto.
        rewrite Theorem175, (Theorem175 ξ). apply LePl_R; apply Pr_min3. }
      apply Theorem188_1' with (Θ:=-(ξ - rr1)) in H17; Simpl_Rin H17.
      rewrite Theorem175 in H18; Simpl_Rin H18. split; auto.
Qed.

























