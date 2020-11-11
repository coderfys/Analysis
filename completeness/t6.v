(***************************************************************************)
(*   This is part of FA_Completeness, it is distributed under the terms    *)
(*           of the GNU Lesser General Public License version 3            *)
(*                (see file LICENSE for more details)                      *)
(*                                                                         *)
(*           Copyright 2020-2022: Yaoshun Fu and Wensheng Yu.              *)
(***************************************************************************)

Require Import t5.
Require Export Seq.

Lemma SL1: ∀ a, fin (SeqEns a) -> ∃ r, r ∈ (SeqEns a) 
  /\ ~ fin /{ z | z ∈ (AllSeq a) /\ (snd z) = r /}.
Proof.
  intros; Absurd.
  pose proof (not_ex_all_not _ H0); simpl in H1.
  assert (∀ n, (n ∈ (SeqEns a) -> 
    fin /{ z | z ∈ (AllSeq a) /\ snd z = n /})).
  { intros; pose proof (H1 n).
    apply property_not in H3; destruct H3; try tauto.
    apply property_not'; auto. } clear H0 H1.
  assert (∀ m, fin /{ z | z ∈ (AllSeq a) /\ snd z = m /}).
  { intros; destruct (classic (m ∈ (SeqEns a))) as [H0 | H0]; auto.
    apply Fin_Empty; intro; destruct H1, H1, H1, H1, H1.
    subst x; simpl in H3; apply H0; constructor; eauto. } clear H2.
  assert (fin (AllSeq a)).
  { rewrite AllSeq_eq; apply Fin_EleUnion; intros.
    - destruct H as [x [f H]]; pose proof (comp H (SeqEns_P1 _)).
      red; eauto.
    - destruct H1, H1, H1; rewrite H2; auto. }
  destruct (Infin_AllSeq _ H1).
Qed.

Lemma SL2 : ∀ a, fin (SeqEns a) -> ∃ N, ∀ n, (∃ m, IGT_N m n /\ a m = a N).
Proof.
  intros; destruct (SL1 a H) as [r [H0 H1 ]].
  destruct H0 as [[N H0]]; subst r.
  exists N; intros; Absurd; elim H1.
  apply Fin_Included with 
    (B:=/{ z | z ∈ (AllSeq a) /\ (~ (IGT_N (fst z) n)) /}).
  - red; intros; destruct H2, H2, x. constructor; split; auto.
    intro; destruct H2, H2; rewrite H2 in H3, H4.
    simpl fst in H4; simpl snd in H3. elim H0; eauto.
  - set (A:=/{z | z ∈ (AllSeq a) /\ (~ (IGT_N (fst z) n))/}).
    exists n`, (λ n p, RelNtoAllS A p n).
    red; repeat split; try red; intros.
    + destruct H2, H2, H2, H2, H2, H3, H3, H3, H3, H3.
      subst x y z; simpl in H6; subst x0; auto.
    + exists (x, (a x)); constructor; simpl; auto.
      constructor; split; try constructor; eauto.
      intro; destruct H2; simpl in H3.
      apply Theorem26 in H2; LEGN H2 H3.
    + destruct H2, H2, H2, H2; subst y; simpl in H3.
      exists x; constructor; simpl; auto.
      constructor; split; try constructor; eauto.
    + destruct H2,H2,H2, H2, H2; subst y; simpl in H3, H4; subst x.
      apply Theorem26'; red. destruct (Theorem10 x0 n); try tauto.
    + destruct H2, H2, H2, H2; auto.
    + destruct H2, H2; tauto.
Qed.

Section Extract_Seq.

Variable (N :Nat) (f :Relation Nat Nat) (l :∀ y, ∃ x, f y x).

Fixpoint Extract_Seq n := 
  match n with
  | 1 => N
  | m` => proj1_sig (Cid (l (Extract_Seq m)))
end.

End Extract_Seq.

Theorem SCT_fin : ∀ a, 
  fin (SeqEns a) -> ∃ b, (SubSeq b a) /\ (∃ ξ, Limit b ξ).
Proof.
  intros; destruct (SL2 _ H) as [N H0].
  set (Extract_Seq0 := Extract_Seq N _ H0).
  exists (λ n, a (Extract_Seq0 n)); split.
  - red; exists Extract_Seq0; split; intros; auto.
    generalize dependent n; induction m; intros; [N1F H1|].
    rename H1 into H2. rename IHm into H1.
    apply Theorem26 in H2; destruct H2.
    + apply H1 in H2; eapply Theorem15; eauto.
      simpl; destruct (Cid (H0 (Extract_Seq0 m))), a0; simpl; auto.
    + subst m; simpl.
      destruct (Cid (H0 (Extract_Seq0 n))), a0; simpl; auto.
  - set (c := a N). assert (∀ m, a (Extract_Seq0 m) = c); intros.
    { rename m into p; destruct p; simpl; auto.
      destruct (Cid (H0 (Extract_Seq0 p))), a0; simpl; auto. }
    exists c; red; intros.
    exists 1; intros; rewrite H1; Simpl_R.
Qed.

Inductive Relsubseq N (a :Seq) x y :Prop :=
  | Relsubseq_in : ILT_N x N -> y = a x -> Relsubseq N a x y.

Lemma SL3 : ∀ {e a}, AccumulationPoint e (SeqEns a) -> 
  ∀  n k, k > O -> ∃ m, IGT_N m n /\ (a m) ∈ (e|-k).
Proof.
  intros; Absurd; elim (Cor_acc _ _ H _ H0).
  assert (fin /{ z | ∃ m, ILE_N m n /\ z = a m /}).
  { exists n`, (Relsubseq n` a); red; intros;
    repeat split; try red; intros.
    - destruct H2, H3; rewrite H4; auto.
    - destruct H2; exists (a x); constructor; auto.
    - destruct H2, H2, H2; exists x; constructor; auto.
      apply Theorem26'; auto.
    - destruct H2; auto.
    - destruct H2; apply Theorem26 in H2; eauto. }
  eapply Fin_Included; eauto; red; intros. destruct H3, H3, H4, H4.
  constructor; exists x0; split; auto; red; subst x.
  destruct (Theorem10 x0 n) as [H4 | [H4 | H4]]; auto. elim H1; eauto.
Qed.

Lemma RNGO : ∀ {n :Nat}, (1/n) NoO_N > O.
Proof.
  intros; apply Theorem203_1' with (Θ:=n); Simpl_R; simpl; auto.
Qed.

Section Extract_Seq'.

Variable (N :Nat) (P :Nat -> ∀ y, y > O -> Nat -> Prop).
Variable l :∀ z y (l: y >O), ∃ x, P z y l x.

Fixpoint Extract_Seq' n := 
  match n with
  | 1 => N
  | m` => proj1_sig (Cid (l (Extract_Seq' m) ((1/n) NoO_N) RNGO))
end.

End Extract_Seq'.

Theorem SCT_infin : ∀ a x y, x < y -> ~ fin (SeqEns a) -> 
  Bounddown_Seq x a -> Boundup_Seq y a -> 
  ∃ b, (SubSeq b a) /\ (∃ ξ, Limit b ξ).
Proof.
  intros. apply BoundSeqEns in H1. apply BoundSeqEns in H2.
  destruct (APT _ _ _ H H0 H1 H2) as [e H3].
  destruct H3 with 1; simpl; auto. destruct H4, H5, H5, H5 as [N H5].
  pose proof (SL3 H3). set (Extract_Seq0' := Extract_Seq' N _ H7).
  exists (λ n, a (Extract_Seq0' n)); split.
  - red; exists Extract_Seq0'; split; intros; auto.
    generalize dependent n; induction m; intros; [N1F H8|].
    rename H8 into H9. rename IHm into H8.
    apply Theorem26 in H9; destruct H9.
    + apply H8 in H9; eapply Theorem15; eauto.
      replace (Extract_Seq0' m`) with (proj1_sig 
        (Cid (H7 (Extract_Seq0' m) ((1/m`) NoO_N) RNGO))); auto.
      destruct Cid. simpl; tauto.
    + subst n. replace (Extract_Seq0' m`) with (proj1_sig
        (Cid (H7 (Extract_Seq0' m) ((1/m`) NoO_N) RNGO))); auto.
      destruct Cid. simpl; tauto.
  - assert (∀ n, (a (Extract_Seq0' n)) ∈ (e|-((1/n) NoO_N))).
    { intros; destruct n; Simpl_R.
      - simpl; constructor; Simpl_R; subst x0.
        destruct H4; auto.
      - replace (Extract_Seq0' n`) with (proj1_sig
          (Cid (H7 (Extract_Seq0' n) ((1/n`) NoO_N) RNGO))); auto.
        destruct Cid. simpl; tauto. }
    exists e; red; intros.
    assert (neq_zero ε). { destruct ε; simpl; auto. }
    destruct (Archimedes ((1/ε) H10)) as [M H11]. exists M; intros.
    apply OrderNRlt in H12. eapply Theorem171 in H12; eauto.
    destruct H8 with n;  apply Ab1'' in H13. eapply Theorem171; eauto.
    apply Theorem203_1 with (Θ:=ε) in H12; Simpl_Rin H12.
    rewrite Theorem194 in H12.
    apply Theorem203_1' with (Θ:=n); Simpl_R; simpl; auto.
Qed.

Theorem SCT : ∀ a x y, x < y -> Bounddown_Seq x a ->
  Boundup_Seq y a -> ∃ b, (SubSeq b a) /\ (∃ ξ, Limit b ξ).
Proof.
  intros; destruct (classic (fin (SeqEns a))).
  - apply SCT_fin; auto.
  - eapply SCT_infin; eauto.
Qed.

















