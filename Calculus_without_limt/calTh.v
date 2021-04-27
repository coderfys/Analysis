(***************************************************************************)
(*   This is part of FA_3rdCalculus, it is distributed under the terms     *)
(*         of the GNU Lesser General Public License version 3              *)
(*                (see file LICENSE for more details)                      *)
(*                                                                         *)
(*            Copyright 2020-2022: Yaoshun Fu and Wensheng Yu.             *)
(***************************************************************************)

Require Export HighDer IntSys.

Theorem NewtonLeibniz : ∀ {F f a b} , uni_derivative F f a b -> F# =∫ f a b.
Proof.
  intros. pose proof H. apply Med_der in H0; destruct H0.
  apply DefInt_Int; auto; intros.
  eapply derF2MiC; eauto. apply Med_der; auto.
Qed.

Theorem UpLimVarInt : ∀ {S f a b}, uniform_continuous f a b ->
  S =∫ f a b -> uni_derivative (S a) f a b.
Proof.
  intros. destruct H0. apply Med_der. split; auto. apply Int_med; auto.
  split; split; red; auto. left. eapply uclt; eauto.
Qed.

Fact tlp : ∀ {m n} l, ILE_N (Minus_N n` m (Le_Lt l)) n.
Proof.
  intros. apply LePl_N with (z:=m); Simpl_N.
  rewrite Theorem6, <- NPl1_. apply LePl_N, Theorem24'.
Qed.

Lemma TLpre : 
  ∀ {H a b n m M} (l :N_uni_derivability H a b n),
  (∀ k l1, (k_th k l1 l) a = O) -> 
  (∀ x, x ∈ [a|b] -> m ≦ (n_th l) x) -> 
  (∀ x, x ∈ [a|b] -> (n_th l) x ≦ M) -> 
  ∀ k l1 l2, let j:=(Minus_N k 1 l2) in 
  let i:= (Minus_N n` k (Le_Lt l1)) in
  ∀ x, x ∈ [a|b] -> m·(Rdifa ((x-a)^j) j) ≦ (m_th i (tlp l1) l) x /\
  (m_th i (tlp l1) l) x  ≦  M·(Rdifa ((x-a)^j) j).
Proof.
  intros. pose proof (Nder_lt l) as G. destruct k; [N1F l2|].
  unfold j. Simpl_N. generalize dependent x; induction k; intros.
  + mdg1 f. rewrite rdf_1. simpl. ndh2 f1 H1 H2.
    assert (ILT_N (Minus_N n` 2 (Le_Lt l1)) n).
    { apply Theorem20_1 with (z:=2); Simpl_N. apply Nlt_S_. }
    pose proof (H0 _ H4). kdh1 f2 H5.
    rewrite <- (uniNder n0 n2) in H5; [|eapply ccil; eauto].
    assert (n = Plus_N (Minus_N n` 2 (Le_Lt l1)) 1).
    { apply Theorem20_2 with (z:=1). rewrite Theorem5; Simpl_N. }
    rewrite H6 in n1.
    generalize (NderOM1 n0 n1)(dermxc a m G)(dermxc a M G); intros.
    assert ((λ x, m·(x-a)) a = f a). { Simpl_R. }
    assert (f a = (λ x, M·(x-a)) a). { Simpl_R. }
    pose proof (derVle H8 H7 H10 H1 _ H3).
    pose proof (derVle H7 H9 H11 H2 _ H3). auto.
  + assert (ILE_N k` n). { eapply Theorem17; eauto. left; apply Nlt_S_. }
    assert (tH:=(Theorem18 1 k)). Simpl_Nin tH.
    pose proof (IHk H4 tH). simpl in H5. clear tH. mdg1 f.
    assert (IGT_N n k`).
    { apply Theorem20_1 with (z:=1), Theorem26'; auto. } 
    assert (i = Minus_N n k` H6).
    { unfold i. erewrite NMi5; eauto. } rewrite H7 in n0.
    generalize (derrdf1 a k m G)(derrdf1 a k M G); intros. mdh1 f1 H5.
    rewrite (NMi7 _ H6) in n1. pose proof (NderOM1 n0 n1).
    assert (ILT_N (Minus_N n k` H6) n).
    { apply Theorem20_1 with (z:=k`); rewrite NMi1. apply Theorem18. }
    pose proof (H0 _ H11). kdh1 f3 H12.
    rewrite <- (uniNder n0 n2) in H12; [|eapply ccil; eauto].
    assert ((λ x, m· (Rdifa ((x - a)^k`) k`)) a = f a).
    { Simpl_R. rewrite powO. unfold Rdifa. Simpl_R. }
    assert (f a = (λ x, M· (Rdifa ((x - a)^k`) k`)) a).
    { Simpl_R. rewrite powO. unfold Rdifa. Simpl_R. }
    assert (∀x, x ∈ [a|b] -> m · Rdifa ((x-a)^ k) k ≦ f1 x).
    { apply H5. } pose proof (derVle H8 H10 H13 H15 _ H3).
    assert (∀x, x ∈ [a|b] -> f1 x ≦ M · Rdifa ((x-a)^ k) k).
    { apply H5. } pose proof (derVle H10 H9 H14 H17 _ H3). auto.
Qed.

Theorem TaylorLemma : 
  ∀ {H a b n m M} (l :N_uni_derivability H a b n),
  H a = O -> (∀ k l1, (k_th k l1 l) a = O) -> 
  (∀ x, x ∈ [a|b] -> m ≦ (n_th l) x) -> 
  (∀ x, x ∈ [a|b] -> (n_th l) x ≦ M) -> 
  ∀ x, x ∈ [a|b] -> m·(Rdifa ((x-a)^n) n) ≦ H x /\
  H x ≦ M·(Rdifa ((x-a)^n) n).
Proof.
  intros. assert (G:= Nder_lt l). destruct (Theorem24 n).
  - assert (ILE_N n n). { red; auto. } 
    generalize (ccil H4) (TLpre l H1 H2 H3 _ H6 H5); intros.
    mdh1 f H8. Simpl_Nin n0. simpl in n0. set (j:=Minus_N n 1 H5) in *.
    pose proof (H1 _ H5). kdh1 f1 H9. simpl in n1.
    rewrite (unider n1 n0) in H9; [|eapply ccil; eauto].
    assert (∀ x, x ∈ [a|b] -> m · Rdifa ((x-a)^j) j ≦ f x). { apply H8. }
    assert (∀ x, x ∈ [a|b] -> f x ≦ M · Rdifa ((x-a)^j) j). { apply H8. }
    generalize (derrdf1 a j m G) (derrdf1 a j M G); intros.
    unfold j in H12, H13. Simpl_Nin H12. Simpl_Nin H13.
    assert ((λ x, m·(Rdifa ((x-a)^n) n)) a = H a).
    { rewrite H0. Simpl_R. rewrite powO. unfold Rdifa. Simpl_R. }
    assert ((λ x, H a = M·(Rdifa ((x-a)^n) n)) a).
    { rewrite H0. Simpl_R. rewrite powO. unfold Rdifa. Simpl_R. }
    pose proof (derVle H12 n0 H14 H10 _ H4).
    pose proof (derVle n0 H13 H15 H11 _ H4). auto.
  - subst n. rewrite rdf_1. simpl. ndh2 f1 H2 H3. simpl in n.
    generalize (dermxc a m G) (dermxc a M G); intros.
    assert ((λ x, m·(x-a)) a = H a). { Simpl_R. }
    assert ((λ x, H a = M·(x-a)) a). { Simpl_R. }
    pose proof (derVle H5 n H7 H2 _ H4).
    pose proof (derVle n H6 H8 H3 _ H4). auto.
Qed.

Fixpoint TaylorFormula_main F a b c n
  :N_uni_derivability F a b n -> Rfun := match n with
  | 1 => λ _ _, F c
  | p` => λ l x, (p_th l c)·(Rdifa ((x-c)^p) p) + 
    TaylorFormula_main F a b c p (Nderpred l) x end.

Fact tayp1 : ∀ F a b c n l, TaylorFormula_main F a b c n l c = F c.
Proof.
  intros. induction n; simpl; auto. rewrite (IHn (Nderpred l)).
  Simpl_R; rewrite powO; unfold Rdifa; Simpl_R.
Qed.

Fact tayp2 : ∀ {F a b c n} l, c ∈ [a|b] -> 
  N_uni_derivative (TaylorFormula_main F a b c n l) (Φ(O)) a b n.
Proof.
  intros. pose proof (Nder_lt l). pose proof (@derC); unfold Φ in *.
  generalize dependent F; induction n; intros; [simpl|]; auto.
  inversion l as [f H2]. destruct (NderNec H2) as [f0 [H3]].
  simpl TaylorFormula_main. apply (@NderFPl _ (λ _, O)).
  - pdg1 f1. pose proof (Nderrdf2 c (f1 c) n H0). eapply NderOP1; eauto. 
  - pose proof (IHn _ (Nderpred l)). eapply NderOP1; eauto. 
Qed.

Fact Ndec : ∀ n m, {ILT_N n m} + {ILE_N m n}.
Proof.
  intros. unfold ILE_N; destruct (Ncase n m) as [[H|H]|H]; auto.
Qed.

Definition TFmain_kthd F a b c n k (l :N_uni_derivability F a b n) :Rfun := 
  match Ndec k n with 
  | left l1 => TaylorFormula_main (k_th k l1 l) a b c (Minus_N n k l1) 
                (NderCut k l1 l)
  | right _ => Φ(O)
  end.

Fact taykdp0 : ∀ {F1 F2 a b c m n} l1 l2, 
  c ∈ [a|b] -> (∀ x, x ∈ [a|b] -> F1 x = F2 x) -> n = m -> 
  TaylorFormula_main F1 a b c n l1 = TaylorFormula_main F2 a b c m l2.
Proof.
  intros. subst n. induction m; simpl.
  - apply H0 in H. rewrite H; auto.
  - rewrite (IHm (Nderpred l1) (Nderpred l2)). pdg2 f (Nderpred l2) f0.
    apply (@NderF _ F2) in n0; auto. rewrite (uniNder n n0 _ H); auto.
Qed.

Fact taykdp1 : ∀ {F a b c k n l} l0, c ∈ [a|b] -> 
  let m:=Minus_N n k l0 in (TFmain_kthd F a b c n` k l) =
  Plus_Fun (λ x, p_th l c · Rdifa ((x-c)^m) m) 
  (TFmain_kthd F a b c n k (Nderpred l)).
Proof.
  intros. unfold TFmain_kthd. destruct Ndec. destruct Ndec.
  - pose proof (proof_irr i0 l0). subst i0.
    assert (N_uni_derivability (k_th k i l) a b (Minus_N n k l0)`).
    { kdg1 f. pose proof (NderCut k i l). kdh1 f0 H0. rewrite (NMi7 _ l0) in H0.
      destruct H0 as [f1]. exists f1. apply (NderF H0 (uniNder n1 n0)). }
    rewrite taykdp0 with (l2:=H0); auto; [|apply NMi7]. simpl.
    pdg2 f0 (Nderpred l) f1. kdh1 f2 n1. pose proof (NderOrdPl n2 n1).
    Simpl_Nin H1. rewrite (uniNder n0 H1 _ H). unfold m.
    assert (∀ x, x ∈ [a|b] -> k_th k i l x = k_th k l0 (Nderpred l) x).
    { kdg2 f (Nderltn i l) f3. eapply uniNder; eauto. }
    rewrite (taykdp0 _ (NderCut k l0 (Nderpred l))); auto.
  - LEGN i0 l0.
  - LEGN i (Theorem15 _ _ _ l0 (Nlt_S_ n)).
Qed.

Fact taykdp2 : ∀ {F a b c n} l, c ∈ [a|b] -> 
  TFmain_kthd F a b c n` n l = Φ(n_th (Nderpred l) c).
Proof.
  intros. unfold TFmain_kthd. destruct Ndec; [|LEGN i (Nlt_S_ n)].
  assert (N_uni_derivability (k_th n i l) a b 1).
  { kdg1 f0. inversion l as [f1]. destruct (NderNec H0) as [f2 [H2]].
    exists f1. apply (derF H1 (uniNder H2 n0)). }
  rewrite taykdp0 with (l2:=H0); Simpl_N. simpl.
  ndg1 f. kdg1 f0. rewrite (uniNder n0 n1); auto.
Qed.

Fact taykdp3 : ∀ {F a b c n l k} l1, c ∈ [a|b] -> 
  TFmain_kthd F a b c n k l c = k_th k l1 l c.
Proof.
  intros. generalize dependent F. induction n; intros; [N1F l1|].
  destruct (Theorem26 _ _ l1).
  - rewrite taykdp1 with H0; auto. kdg1 f. pdg1 f0. unfold Plus_Fun.
    Simpl_R. rewrite powO. unfold Rdifa. Simpl_R.
    rewrite (IHn H0 _ (Nderpred l)). kdg1 f1. eapply uniNder; eauto.
  - subst k. rewrite taykdp2; auto.
    kdg1 f. ndg1 f0. unfold Φ; eapply uniNder; eauto.
Qed.

Fact tayder : ∀ {F a b n} k l c, c ∈ [a|b] ->
  N_uni_derivative (TaylorFormula_main F a b c n l)
  (TFmain_kthd F a b c n k l) a b k.
Proof.
  intros. pose proof (Nder_lt l). destruct (Ndec k n).
  - generalize dependent k. induction n; intros; [N1F i|].
    pose proof i. apply Theorem26 in H1. destruct H1.
    + pose proof (IHn (Nderpred l) _ H1). simpl TaylorFormula_main.
      rewrite taykdp1 with H1; auto. apply NderFPl; [apply Nderrdf1|]; auto.
    + subst k. rewrite taykdp2; auto.
      rewrite <- (Theorem175' (n_th (Nderpred l) c)).
      apply NderFPl; [|apply tayp2; auto]. pdg1 f. ndg1 f0.
      rewrite (uniNder n0 n1); auto. unfold Φ. apply Nderrdf2; auto.
  - unfold TFmain_kthd. destruct Ndec; [LEGN i i0|].
    pose proof (@derC a b); unfold Φ in *. induction k.
    + destruct i; [N1F H2|]. subst n. apply H1; auto.
    + destruct i; [|subst n; apply tayp2; auto].
      apply Theorem26 in H2. eapply NderOP1; eauto.
Qed.

Lemma TTpre : ∀ {F a b n M l}, 
  (∀ x, x ∈ [a|b] -> |(n_th l) x| ≦ M) -> ∀ c x, c ∈ [a|b] -> x ∈ [c|b] -> 
  |F(x)-(TaylorFormula_main F a b c n l x)|≦ M·(Rdifa (|x-c|^n) n).
Proof.
  intros. inversion H0 as [[_ [K|K]]].
  2: { subst c. destruct H1, H1. LEGER H1 H2. subst x. rewrite tayp1; Simpl_R.
       simpl Abs_R. rewrite powO. unfold Rdifa. Simpl_R; red; auto. }
  inversion l as [f]. pose proof (tayp2 l H0). 
  set (G:=Minus_Fun F (TaylorFormula_main F a b c n l)).
  assert (N_uni_derivative G f a b n).
  { apply (Nderf (NderFMi H2 H3)); intros. unfold Minus_Fun; Simpl_R. }
  pose proof H4. pose proof H2. apply (Nderin H0 K) in H3.
  apply (Nderin H0 K) in H4; apply (Nderin H0 K) in H6.
  assert (G c = O). { unfold G, Minus_Fun. rewrite tayp1; Simpl_R. }
  set (H8:= Ndervety H4).
  assert (∀ k l1,k_th k l1 H8 c = O); intros.
  { kdg1 f1. pose proof (tayder k l c H0). eapply Nderin in H9; eauto.
    pose proof (Nderltn l1 (Ndervety H6)). destruct H10 as [f2].
    pose proof (NderFMi H10 H9). unfold Minus_Fun in H11.
    rewrite (uniNder n0 H11); [|eapply ccil; eauto].
    rewrite (taykdp3 l1 H0). kdg1 f3.
    rewrite (uniNder (Nderin H0 K n1) H10); Simpl_R. eapply ccil; eauto. }
  assert (∀x, x ∈ [c|b] -> |n_th H8 x| ≦ M); intros.
  { pose proof H10. eapply ccisub in H10; eauto; [|apply (ccir H0)].
    pose proof H10. apply H in H10.
    assert (n_th H8 x0 = n_th l x0).
    { ndg2 f1 H8 f2. rewrite (uniNder n1 H2), (uniNder n0 H4); auto. }
    rewrite H13; auto. } 
  assert (∀x, x ∈ [c|b] -> -M ≦ n_th H8 x). { intros; apply (Ab1' M); auto. }
  assert (∀x, x ∈ [c|b] -> n_th H8 x ≦ M). { intros; apply (Ab1' M); auto. }
  pose proof (TaylorLemma H8 H7 H9 H11 H12 _ H1).
  rewrite Theorem197' in H13. apply Ab1' in H13. destruct H1, H1.
  rewrite powp1; auto. apply LePl_R with (z:=c); Simpl_R.
Qed.

Theorem TaylorThoerem : ∀ {F a b n l}, 
  ∀ M, (∀ x, x ∈ [a|b] -> |(n_th l) x|≦M) ->
  ∀ c x, c ∈ [a|b] -> x ∈ [a|b] -> 
  |F(x)-(TaylorFormula_main F a b c n l x)|≦ M·(Rdifa (|x-c|^n) n).
Proof.
  intros. assert (x ∈ [c|b] \/ x ∈ [a|c]).
  { destruct H0, H0, H1, H1, (Rcase2 x c); [right|left]; split; auto. }
  destruct H2; [apply TTpre; auto|].
  inversion l as [f]. pose proof (Nderf_mi H3). pose proof (Ndervety H4).
  assert (∀x, x ∈[(-b)|(-a)] -> |n_th H5 x| ≦ M); intros.
  { pose proof H6. apply ccimi in H6; Simpl_Rin H6. apply H in H6.
    eapply Theorem173; eauto; right.
    ndg2 f1 H5 f2. apply Nderf_mi in n1; auto.
    rewrite (uniNder n0 n1), Theorem193, powp2; Simpl_R. }
  pose proof H0. apply ccimi in H0. apply ccimi in H2.
  pose proof (TTpre H6 _ _ H0 H2). simpl in H8. Simpl_Rin H8.
  rewrite <- (Theorem178 (-x+c)), Theorem180 in H8. Simpl_Rin H8.
  eapply Theorem173; eauto. right; f_equal. f_equal.
  clear H H3 H6 H8 H4. induction n; simpl; Simpl_R.
  f_equal; auto. pdg2 f1 (Nderpred l) f2.
  apply Nderf_mi in n1. Simpl_Rin n1.
  assert ((λ x,F(--x))=(λ x,F(x))). { apply fun_ext; intro; Simpl_R. }
  rewrite H in n1. rewrite (uniNder n0 n1), Theorem175; Simpl_R.
  rewrite (Theorem194 ((-(1))^n)), Theorem199. f_equal.
  rewrite <- Theorem181, (powm (c-x)), <- rdft.
  rewrite <- Theorem199, powp3; Simpl_R.
Qed.