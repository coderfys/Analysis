(***************************************************************************)
(*   This is part of FA_Completeness, it is distributed under the terms    *)
(*           of the GNU Lesser General Public License version 3            *)
(*                (see file LICENSE for more details)                      *)
(*                                                                         *)
(*           Copyright 2020-2022: Yaoshun Fu and Wensheng Yu.              *)
(***************************************************************************)

Require Import t4.
Require Export R_sup.

Definition AccumulationPoint e E :=
  ∀ x, x > O -> ∃ y, y ∈ (e|-x) /\ y ∈ E /\ y <> e.
Definition AccumulationPoint' e E :=
  ∀ x, x > O -> ~ fin /{ z | z ∈ (e|-x) /\ z ∈ E /}.

Inductive Relcond A e x y :=
  | Relcond_intro : x ∈ A -> |x - e| = y -> Relcond A e x y.

Corollary Cor_acc : ∀ e E, AccumulationPoint e E ->
  AccumulationPoint' e E.
Proof.
  assert (∀ e E, (AccumulationPoint e E) -> 
  ∀ b, b > O -> ~ fin /{ z | z ∈ (e|-b) /\ z ∈ E /\ z <> e /}).
  { intros; red in H; intro.
    apply H in H0.
    set (R1:=/{ z | z ∈ (e|-b) /\ z ∈ E /\ z <> e /}).
    set (R:=/{ z | ∃ r, r ∈ R1 /\ r <> e /\ z = | r - e | /}).
    assert (Surjection R1 R (Relcond R1 e)).
    { repeat split; intros; try apply conj; try red; intros.
      - destruct H2, H3; auto. subst y; auto.
      - exists (|x - e|). constructor; auto.
      - destruct H2, H2, H2, H3; exists x; constructor; auto.
      - destruct H2, i, H2, H2; tauto.
      - destruct H2, i, H2, H2; tauto.
      - destruct H2, i; tauto.
      - destruct H2, i; tauto.
      - destruct H2, i, H2, H2, H2, H3; exists x; repeat split; auto. }
    assert (fin R).
    { destruct H1 as [N [f H1]]; pose proof (comp H1 H2); red; eauto. }
    assert (No_Empty R).
    { destruct H0, H0, H0, H0, H4.
      red; exists (|x - e|); constructor; exists x; repeat split; auto. }
    destruct (FinMin _ H3 H4) as [m H5], H5, H5, H5, H5, H7.
    pose proof (Ab8' _ _ H7); apply H in H9.
    destruct H9, H9, H9, H9, H10, H5, H5, H5, H5.
    subst m; pose proof (conj H5 H14).
    apply Ab1'' in H8; pose proof (conj H9 H11). apply Ab1'' in H15.
    assert (|x0 - e| ∈ R). 
    { constructor; exists x0; split; auto; constructor; split; auto.
      constructor; apply Ab1''; eapply Theorem171; eauto. }
    apply H6 in H16; LEGR H16 H15. }
  red; intros; intro. eapply H in H1; eauto; apply H1.
  eapply Fin_Included; eauto.
  red; intros; destruct H3; constructor; tauto.
Qed.

Inductive fin1 (r :Real) x y :=
  | fin1_intro : ILT_N x 2 -> y = r -> fin1 r x y.

Corollary Cor_acc' : ∀ e E, AccumulationPoint' e E
  -> AccumulationPoint e E.
Proof.
  intros; red; intros; pose proof H0; apply H in H0; Absurd;
  elim H0. destruct (classic (e ∈ E)) as [H3 | H3].
  - exists 2, (fin1 e); repeat apply conj; try red; intros.
    + destruct H4, H5; subst y; auto.
    + destruct H4; exists e; constructor; auto.
    + destruct H4, H4; exists 1; constructor; auto.
      * apply Nlt_S_. * Absurd; elim H2; eauto.
    + destruct H4; constructor; auto.
    + destruct H4; constructor; subst y; split; auto.
      constructor; split; try apply Pl_R; auto.
      apply Theorem188_1 with (Θ:= x); Simpl_R; apply Pl_R; auto.
  - assert (/{ z | z∈(e|-x) /\ z∈E /} = /{ z | z∈(e|-x) /\ z∈E /\ z<>e /}).
    { apply ens_ext; split; intros; destruct H4; constructor.
      - destruct H4; split; [| split]; auto; intro; subst x0; tauto.
      - destruct H4, H5; auto. } rewrite H4.
     apply Fin_Empty; intro; destruct H5, H5; apply H2; eauto.
Qed.

Axiom constructive_indefinite_description :
  ∀ {A : Type} {P : A->Prop},
    (∃ x, P x) -> { x : A | P x }.

Definition Cid {A : Type} {P : A->Prop} (l: ∃ x, P x) := 
  constructive_indefinite_description l.

Inductive RRtoR A B x y : Prop :=
  | RRtoR_intro: x ∈ A -> y ∈ B -> y ∈ (Fst x | Snd x) ->
  RRtoR A B x y .

Theorem APT : ∀ E x y, x < y -> ~ fin E -> Bounddown_Ens x E -> 
  Boundup_Ens y E -> ∃ e, AccumulationPoint e E.
Proof.
  assert (∀ E, ~ (∃ e, AccumulationPoint e E) -> 
     ∀ z, ∃ δ, δ > O /\ (∀ w, w ∈ (z|-δ) /\ w ∈ E -> w = z)) as G.
  { intros; Absurd; elim H. exists z; red; intros.
    Absurd; elim H0. exists x; split; intros; auto.
    destruct H3; Absurd. elim H2; eauto. }
  intros; red in H1, H2; Absurd. pose proof (G E H3).
  set (Gete p :=(proj1_sig (Cid (H4 p))) ).
  assert (∀ x, Gete x > O).
  { intros; unfold Gete; destruct (Cid (H4 x0)); simpl proj1_sig; tauto. }
  assert (G1: ∀ x y, y > O -> x - y < x + y). { apply Pl_R'. }
  set (R:= /{ r | ∃ x, r = (rr (x-(Gete x)) (x+(Gete x)) (G1 x _ (H5 x))) /}).
  assert (OpenCover x y R).
  { red; split; auto; intros.
    exists (z|-(Gete z)); split; constructor; intros.
    - exists (rr (z-(Gete z)) (z+(Gete z)) (G1 z _ (H5 z))).
      split; simpl; auto; constructor; eauto.
    - split; try apply Pl_R; auto.
      apply Theorem188_1 with (Θ:=Gete z); Simpl_R; apply Pl_R; auto. }
  apply FinCoverT in H6; destruct H6 as [H6 [h1 H7]], H7, H8.
  set (g:=(RRtoR /{ z | z ∈ h1 /\
  (∃ r, r ∈ E /\ r ∈ (Fst z | Snd z))/} E)).
  assert (Surjection /{ z | z ∈ h1 /\
  (∃ r, r ∈ E /\ r ∈ (Fst z | Snd z))/} E g).
  { red; repeat split; try red; intros.
    - destruct H10, H10, H11, H11, H10, H11.
      apply H7 in H10; destruct H10, H10 as [r1 H10]. 
      clear H11; subst x0; simpl in *; unfold Gete in *.
      destruct (Cid (H4 r1)); simpl proj1_sig in *; destruct a.
      apply (Theorem165 _ r1 _); auto; symmetry; auto.
    - destruct H10, H10, H11 as [r [H11 H12]].
      exists r; constructor; auto.  constructor; split; auto; eauto.
    - assert (y0 ∈ [x | y]). { constructor; split; auto. }
      destruct H9; apply H12 in H11.
      destruct H11 as [R1 [H11 H13]], H11, H11 as [rr1 [H11 H14]].
      subst R1; destruct H13; pose proof H11.
      apply H7 in H11; destruct H11, H11 as [r1 H11].
      exists rr1; constructor; auto; constructor; auto.
      split; auto; exists y0; repeat split; tauto.
    - destruct H10, H10; tauto.
    - destruct H10; eauto. - destruct H10; auto. }
  assert (fin /{ z | z ∈ h1 /\ (∃ r, r ∈ E /\ r ∈ (Fst z | Snd z))/}).
  { apply Fin_Included with (B:=h1); auto.
    red; intros; destruct H11; tauto. }
  destruct H11 as [N [f H11]]; elim H0.
  pose proof (comp H11 H10). red. eauto.
Qed.


























