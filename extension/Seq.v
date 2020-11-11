(***************************************************************************)
(*   This is part of FA_Landau, it is distributed under the terms of the   *)
(*             GNU Lesser General Public License version 3                 *)
(*                (see file LICENSE for more details)                      *)
(*                                                                         *)
(*           Copyright 2020-2022: Yaoshun Fu and Wensheng Yu.              *)
(***************************************************************************)

Require Export finite R_sup.

Definition Seq := Nat -> Real.

Corollary eq_Seq : ∀ (P Q :Seq), (∀ m, P m = Q m) -> P = Q.
Proof.
  intros; apply fun_ext; auto.
Qed.

Definition Boundup_Seq y (a :Seq) := ∀ n, (a n) ≦ y.
Definition Bounddown_Seq y (a :Seq) := ∀ n, y ≦ (a n).
Definition ILT_Seq (a b :Seq) := ∀ n, a n ≦ b n.

Definition Increase (a :Seq) := ∀ n m, ILT_N n m -> (a n) ≦ (a m).
Definition Decrease (a :Seq) := ∀ n m, ILT_N n m -> (a m) ≦ (a n).

Corollary IncP : ∀ a, Increase a -> ∀ N, (a 1) ≦ (a N).
Proof.
  intros; induction N; red; auto.
  eapply Theorem173; eauto; apply H, Nlt_S_. 
Qed.

Corollary DecP : ∀ b, Decrease b -> ∀ N, (b N) ≦ (b 1).
Proof.
  intros; induction N; red; auto.
  eapply Theorem173; eauto; apply H, Nlt_S_. 
Qed.

Definition Plus_Seq (a b :Seq) := λ n, a n + b n.
Definition minus_Seq (a :Seq) := λ n, - a n.
Definition Minus_Seq (a b :Seq) := λ n, a n - b n.

Corollary SeqCon1 : ∀ a b :Seq, b = Plus_Seq (Minus_Seq b a) a.
Proof.
  intros; unfold Minus_Seq, Plus_Seq; apply eq_Seq; intros; Simpl_R.
Qed.

Definition SubSeq (a b :Seq) := ∃ s, (∀ n m, ILT_N n m -> 
  ILT_N (s n) (s m)) /\ (∀ n, (a n) = b (s n)).

Corollary SubSeq_P : ∀ (z b :Seq) s, 
  (∀ n m, ILT_N n m -> ILT_N (s n) (s m)) ->
  (∀ n, (z n) = b (s n)) -> ∀ n, IGE_N (s n) n.
Proof.
  intros; induction n; [apply Theorem24|].
  pose proof (Theorem18 n 1); Simpl_Nin H1. apply H in H1.
  assert (IGT_N (s n`) n).
  { eapply Theorem16; left; split; eauto; apply Theorem13; auto. }
  apply Theorem25 in H2; Simpl_Nin H2.
Qed.

Definition Limit (a :Seq) ξ := ∀ ε, ε > O -> 
  ∃ N, ∀ n, (IGT_N n N) -> |(a n) - ξ| < ε.

Corollary SeqLimPlus : ∀ a b ξ1 ξ2, Limit a ξ1 -> Limit b ξ2 -> 
  Limit (Plus_Seq a b) (ξ1 + ξ2).
Proof.
  intros; red in H, H0; red; intros. pose proof (Pr_2a H1).
  destruct (H _ H2) as [N1 H3], (H0 _ H2) as [N2 H4].
  exists (Plus_N N1 N2); intros. pose proof (Theorem18 N1 N2).
  pose proof (Theorem18 N2 N1). rewrite Theorem6 in H7.
  generalize (Theorem15 _ _ _ H6 H5) (Theorem15 _ _ _ H7 H5); intros.
  apply H3 in H8; apply H4 in H9; unfold Plus_Seq.
  pose proof (Theorem189 H8 H9). Simpl_Rin H10.
  eapply Theorem172; left; split; eauto. rewrite <- Mi_R; apply Ab2.
Qed.

Corollary SqueezeT : ∀ a b c ξ, 
  (∃ N, ∀ n, IGT_N n N -> ((a n) ≦ (b n)) /\ ((b n) ≦ (c n))) -> 
  Limit a ξ -> Limit c ξ -> Limit b ξ.
Proof.
  intros; red; intros.
  destruct (H0 _ H2) as [N2 H3], (H1 _ H2) as [N3 H4], H as [N1 H].
  exists (Plus_N N1 (Plus_N N2 N3)); intros.
  assert (IGT_N (Plus_N N1 (Plus_N N2 N3)) N1). { apply Theorem18. }
  assert (IGT_N (Plus_N N1 (Plus_N N2 N3)) N2).
  { rewrite <- Theorem5,(Theorem6 _ N2),Theorem5. apply Theorem18. }
  assert (IGT_N (Plus_N N1 (Plus_N N2 N3)) N3).
  { rewrite <- Theorem5, Theorem6. apply Theorem18. }
  apply (Theorem15 _ _ n) in H6; auto.
  apply (Theorem15 _ _ n) in H7; auto.
  apply (Theorem15 _ _ n) in H8; auto.
  apply H in H6; destruct H6. apply H3 in H7. apply H4 in H8.
  apply Ab1'' in H7; apply Ab1'' in H8; destruct H7, H8.
  apply Ab1''; split; eapply Theorem172; eauto.
Qed.

Corollary LimUni : ∀ a ξ1 ξ2, Limit a ξ1 -> Limit a ξ2 -> ξ1 = ξ2.
Proof.
  intros; destruct (classic (ξ1 = ξ2)); auto.
  apply Ab8' in H1; apply Pr_2a in H1; pose proof H1.
  apply H in H1; destruct H1 as [N1 H3].
  apply H0 in H2; destruct H2 as [N2 H2].
  pose proof (Theorem18 N1 N2).
  pose proof (Theorem18 N2 N1); rewrite Theorem6 in H4.
  apply H3 in H1; apply H2 in H4.
  rewrite <- Theorem178, Theorem181 in H1.
  pose proof (Theorem189 H1 H4); Simpl_Rin H5.
  pose proof (Ab2 (ξ1 - a (Plus_N N1 N2)) (a (Plus_N N1 N2) - ξ2)).
  unfold Minus_R at 2 in H6; rewrite <- Theorem186 in H6.
  Simpl_Rin H6. LEGR H6 H5.
Qed.

Corollary Increase_limitP : ∀ a ξ, 
  Increase a -> Limit a ξ -> (∀ n, a n ≦ ξ).
Proof.
  intros; red in H, H0; red.
  destruct (Theorem167 (a n) ξ) as [H1 | [H1 | H1]]; auto.
  assert (a n - ξ > O). { apply Theorem188_1 with (Θ:=ξ); Simpl_R. }
  apply H0 in H2; destruct H2 as [N H2].
  destruct (Theorem10 n N) as [H3 | [H3 | H3]]; auto.
  - generalize (Theorem18 N 1) (Theorem18 N 1); intros; subst n.
    apply H in H4; apply H2 in H5.
    assert (a (Plus_N N 1) > ξ). 
    { eapply Theorem172; right; split; eauto. }
    rewrite Ab4 in H5; auto.
    apply Theorem188_1' with (Θ:=ξ) in H5; Simpl_Rin H5. LEGR H4 H5.
  - generalize (Theorem15 _ _ _ H3 (Theorem18 n 1)) (Theorem18 n 1); intros.
    apply H2 in H4; apply H in H5.
    assert (a (Plus_N n 1) > ξ).
    { eapply Theorem172; right; split; eauto. }
    rewrite Ab4 in H4; auto.
    apply Theorem188_1' with (Θ:=ξ) in H4; Simpl_Rin H4. LEGR H5 H4.
  - generalize (Theorem18 N 1) (Theorem18 N 1); intros.
    pose proof (Theorem15 _ _ _ H3 H5); intros. apply H in H6.
    assert (a (Plus_N N 1) > ξ). { eapply Theorem172; right; split; eauto. }
    apply H2 in H4. rewrite Ab4 in H4; auto.
    apply Theorem188_1' with (Θ:=ξ) in H4; Simpl_Rin H4. LEGR H6 H4.
Qed.

Corollary Decrease_limitP : ∀ b ξ, 
  Decrease b -> Limit b ξ -> (∀ n, ξ ≦ b n).
Proof.
  intros. assert (Increase (minus_Seq b)).
  { red in H; red; intros; unfold minus_Seq. apply H in H1; destruct H1.
    - left; apply Theorem183_1; auto. 
    - right; apply Theorem183_2; auto. }
  assert (Limit (minus_Seq b) (-ξ)).
  { red in H0; red; intros; unfold minus_Seq.
    apply H0 in H2; destruct H2 as [N H2].
    exists N; intros; apply H2 in H3.
    unfold Minus_R; rewrite <- Theorem178, Theorem180; Simpl_R. }
  destruct (Increase_limitP _ _ H1 H2 n); unfold minus_Seq in H3.
  - left; apply Theorem183_1'; auto.
  - right; apply Theorem183_2'; auto.
Qed.

Definition HarmonicSeq :Seq := λ n, (1/n) NoO_N.

Corollary Limit_Har : Limit HarmonicSeq O.
Proof.
  red; intros. assert (neq_zero ε). { destruct ε; simpl; auto. }
  destruct (Archimedes (((1/ε) H0))) as [N H1].
  exists N; intros. unfold HarmonicSeq; Simpl_R.
  apply OrderNRlt in H2. pose proof (Theorem171 _ _ _ H1 H2).
  apply Theorem203_1 with (Θ:=ε) in H3; Simpl_Rin H3. rewrite Ab3.
  - apply Theorem203_1' with (Θ:=n); Simpl_R; [|reflexivity].
    rewrite Theorem194; auto.
  - apply Theorem203_1' with (Θ:=n); Simpl_R; simpl; auto.
Qed.

Definition ZeroSeq :Seq := λ n, O.

Corollary Limit_Ze : Limit ZeroSeq O.
Proof.
  red; intros; exists 1; intros. unfold ZeroSeq; Simpl_R.
Qed.

Corollary powSeq : ∀ {n}, 2^n > O.
Proof.
  intros; induction n; [|apply Pos]; simpl; auto.
Qed.

Corollary powSeq' : ∀ {n}, neq_zero (2^n).
Proof.
  intros; apply uneqOP, powSeq.
Qed.

Definition PowSeq :Seq := λ n, (1/(2^n))  powSeq'.

Corollary Limit_Pow : Limit PowSeq O.
Proof.
  apply (SqueezeT ZeroSeq _ HarmonicSeq _); 
  try apply Limit_Har; try apply Limit_Ze.
  exists 1; intros; split; unfold HarmonicSeq, PowSeq, ZeroSeq.
  - left; apply Pos'; try reflexivity; apply powSeq.
  - left. assert (1 > O). { simpl; auto. }
    pose proof (OrderNRlt _ _ H). pose proof (Theorem171 _ _ _ H0 H1).
    apply Theorem203_1' with (Θ:=n); Simpl_R. rewrite Theorem194, Di_Rt.
    apply Theorem203_1' with (Θ:=2^n); Simpl_R; try apply powSeq.
    clear H1 H0 H2. destruct H; Simpl_Nin H; subst n. induction x.
    + rewrite PowS, Pow1. pattern 2 at 2;  rewrite <- NPl1_.
      rewrite <- Real_PZp, Theorem201; Simpl_R.
      apply Theorem182_1; Simpl_R; simpl; auto.
    + rewrite PowS. apply (Theorem203_1 _ _ 2) in IHx; [|reflexivity].
      eapply Theorem171; eauto.
      rewrite <- (NPl_1 1), <- Real_PZp, Theorem201; Simpl_R.
      rewrite <- NPl_1, <- Real_PZp.
      eapply Theorem190; left; split; red; auto.
      apply OrderNRlt; red; exists x; Simpl_N.
Qed.

Corollary Limit_Pow' : ∀ x, Limit (λ n, (x/(2^n)) powSeq') O.
Proof.
  intros; red; intros.
  destruct (classic (x = O)) as [H0 | H0].
  { exists 1; intros; rewrite H0; Simpl_R. }
  assert (neq_zero (|x|)). { destruct x; simpl; auto. }
  pose proof (Ab8 _ H0). pose proof (Pos' _ _ H1 H H2).
  destruct (Limit_Pow _ H3) as [N H4]. exists N; intros; Simpl_R.
  apply H4 in H5; Simpl_Rin H5; unfold PowSeq in H5.
  apply Theorem203_1 with (Θ:=(|x|)) in H5; Simpl_Rin H5.
  rewrite <- Theorem193, Theorem194, Di_Rt in H5; Simpl_Rin H5.
Qed.

Definition NatEns := /{ x | ∃ z :Nat, z = x /}.
Definition NatEnsD1 n := /{ x | ∃ z :Nat, (z = x /\ x <> n ) /}.

Inductive N1_N N n m :Prop :=
| N1_N_intro : ILT_N n N -> n = m -> N1_N N n m
| N1_N_intro' : IGT_N n N -> (Plus_N m 1) = n -> N1_N N n m.

Lemma NatEns_P : ∀ N, Surjection (NatEnsD1 N) NatEns (N1_N N).
Proof.
  intros; red; repeat split; try red; intros; eauto.
  - destruct H, H0.
    + subst x; auto. + subst x y; LGN H H0. + subst x z; LGN H H0.
    + subst x; apply Theorem20_2 in H2; auto.
  - destruct H, H, H.
    destruct (Theorem10 x N) as [H1 | [H1 | H1]]; try tauto. 
    + exists (Minus_N x 1 (N1P' H1)); constructor 2; Simpl_N.
    + exists x; constructor; auto.
  - destruct (classic (ILT_N y N)).
    + exists y; constructor; auto; constructor; auto.
    + exists (Plus_N y 1); constructor 2; auto. apply Theorem26'.
      destruct (Theorem10 y N); red; try tauto. right; auto.
  - destruct H; subst x.
    + exists y; split; auto; intro; ELN H0 H.
    + exists (Plus_N y 1); split; auto; intro; EGN H0 H.
Qed.

Corollary Infin_NatEns : ~ fin NatEns.
Proof.
  apply all_not_not_ex; intros; induction n; intro.
  - destruct H, H, H0, H1, H2. red in H1.
    assert (1 ∈ NatEns). { constructor; eauto. }
    apply H1 in H4; destruct H4.
    apply H2 in H4; destruct H4; N1F H4.
  - apply IHn; destruct H; rename x into f1; rename n into x.
    destruct H, H0, H1, H2.
    assert (x ∈ (Fin_En x`)). 
    { constructor; red; exists 1; Simpl_N. }
    destruct H0 with x; auto. set (P:= NatEnsD1 x0).
    set (N:=/{ n | ∃ b', (b' ∈ P) /\ (f1 n b') /}).
    assert (∃ c, c ∈ NatEns /\ c <> x0).
    { exists (Plus_N x0 1); split.
      - constructor; eauto. - intro; EGN H6 (Theorem18 x0 1). }
    destruct H6, H6. 
    assert (Surjection (Fin_En x) P (RelAB N (Fin_En x) x1 f1)).
    { red; repeat split; try red; intros. 
      - destruct H8, H9; try tauto.
        + eapply H; eauto. + subst y z; auto.
      - destruct (classic (x2 ∈ N)).
        + destruct H8, H0 with x2.
          * constructor; eauto. apply Le_Lt; red; auto.
          * exists x3; constructor; auto.
        + exists x1; constructor 2; eauto.
      - pose proof H8. destruct H8, H8, H8.
        destruct H1 with y; auto.
        + constructor; eauto.
        + exists x3; constructor; auto. split; exists y; split; auto.
      - destruct H8.
        + destruct H8, H8, H8, H8, H8, H8.
          apply (H _ _ _ H9) in H10; subst x3.
          pose proof H9; apply H2 in H9; destruct H9.
          apply Theorem26 in H9. destruct H9; auto.
          subst x2 y; elim H11; eapply H; eauto.
        + destruct H9; auto.
      - destruct H8. 
        + exists y; split; auto; intro; subst y.
          do 6 destruct H8. apply H11; eapply H; eauto.
        + subst y; eauto. }
    pose proof (comp H8 (NatEns_P x0)). eauto.
Qed.

Definition SeqEns (a :Seq) := /{ r | ∃ n, r = a n /}.
Definition AllSeq (a :Seq) := /{ z | ∃ n , z = (n, (a n)) /}.
Definition SeqFam a := /{ z | ∃ r, r ∈ (SeqEns a) /\ 
  z = /{ z1 | z1 ∈ (AllSeq a) /\ snd z1 = r /} /}.


Corollary BoundSeqEns : ∀ a x, 
  (Bounddown_Seq x a <-> Bounddown_Ens x (SeqEns a)) /\ 
  (Boundup_Seq x a <-> Boundup_Ens x (SeqEns a)).
Proof.
  split; split; intros; red; intros;
  try (destruct H0, H0; rewrite H0; auto); apply H; split; eauto.
Qed.

Inductive RelSeqEnstoSeqFam a r P :Prop :=
  | RelSeqEnstoSeqFam_intro : r ∈ (SeqEns a) -> 
    P = /{ z1 | z1 ∈ (AllSeq a) /\ snd z1 = r /} -> 
    RelSeqEnstoSeqFam a r P.

Corollary SeqEns_P1 : ∀ a, 
  Surjection (SeqEns a) (SeqFam a) (RelSeqEnstoSeqFam a).
Proof.
  intros; repeat split; try red; intros.
  - destruct H, H0; subst y; auto.
  - exists /{ z1 | z1 ∈ (AllSeq a) /\ snd z1 = x /}; split; auto.
  - destruct H, H, H; exists x; constructor; auto.
  - destruct H, H; auto.
  - destruct H; exists x; split; auto.
Qed.

Corollary AllSeq_eq :  ∀ a, AllSeq a = ∪ (SeqFam a).
Proof.
  intros; apply ens_ext; split; intros; destruct H, H; constructor.
  - exists /{ z | z ∈ (AllSeq a) /\ snd z = (a x0) /}.
    subst x; repeat constructor; eauto.
    exists (a x0); split; auto; constructor; eauto.
  - destruct H, H, H, H; subst x0; destruct H0, H0, H0; auto.
Qed.

Inductive RelNtoAllS (P :Ensemble (prod Nat Real)) p n :Prop :=
  | RelNtoAllS_intro :  p ∈ P -> n = fst p -> RelNtoAllS P p n.

Lemma AllSeq_P1 : ∀ a, 
  Surjection (AllSeq a) NatEns (RelNtoAllS (AllSeq a)).
Proof.
  repeat split; try red; intros; eauto.
  - destruct H, H0. subst y. auto.
  - destruct H, H. exists x0; constructor.
    + constructor; eauto. + rewrite H; simpl; auto.
  - destruct H, H; exists (x,a x); constructor.
    + constructor; eauto. + rewrite H; auto.
  - destruct H, H, H; eauto.
Qed.

Corollary Infin_AllSeq : ∀ a, ~ fin (AllSeq a).
Proof.
  intros; intro. destruct H, H.
  apply Infin_NatEns; red; exists x.
  pose proof (comp H (AllSeq_P1 a)); eauto.
Qed.