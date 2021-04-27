(***************************************************************************)
(*   This is part of FA_3rdCalculus, it is distributed under the terms     *)
(*         of the GNU Lesser General Public License version 3              *)
(*                (see file LICENSE for more details)                      *)
(*                                                                         *)
(*            Copyright 2020-2022: Yaoshun Fu and Wensheng Yu.             *)
(***************************************************************************)

Require Export UnD.

Fixpoint N_uni_derivative F f a b n :=
  match n with
  | 1 => uni_derivative F f a b
  | p` => ∃ f1, uni_derivative F f1 a b /\ N_uni_derivative f1 f a b p
  end.

Definition N_uni_derivability F a b n := ∃ f, N_uni_derivative F f a b n.

Fact NderNec : ∀ {F f a b n}, N_uni_derivative F f a b n` -> 
  ∃ f1, N_uni_derivative F f1 a b n /\ uni_derivative f1 f a b.
Proof.
  intros. generalize dependent F; induction n; intros; 
  destruct H as [f1 [H]]; [eauto|]. destruct (IHn _ H0) as [f2 [H1]].
  exists f2. split; auto. red; eauto.
Qed.

Fact NderSuf : ∀ {F f a b n}, 
  (∃ f1, N_uni_derivative F f1 a b n /\ uni_derivative f1 f a b) ->
  N_uni_derivative F f a b n`.
Proof.
  intros. destruct H as [f0 [H]]. generalize dependent F. induction n; intros.
  - exists f0; auto.
  - destruct H as [f1 [H]]. pose proof (IHn _ H1). exists f1. auto.
Qed.

Fact Nderf : ∀ {F f1 f2 a b n}, N_uni_derivative F f1 a b n ->
  (∀ x, x ∈ [a|b] -> f1 x = f2 x) -> N_uni_derivative F f2 a b n.
Proof.
  intros. generalize dependent F. induction n; intros.
  - eapply derf; eauto.
  - destruct H as [f3 [H]]. simpl. eauto.
Qed.

Fact NderF : ∀ {F1 F2 f a b n}, N_uni_derivative F1 f a b n ->
  (∀ x, x ∈ [a|b] -> F1 x = F2 x) -> N_uni_derivative F2 f a b n.
Proof.
  intros. generalize dependent f. induction n; intros.
  - simpl in *. eapply derF; eauto.
  - destruct H as [f3 [H]]. exists f3. split; auto.
    eapply derF; eauto.
Qed.

Fact NderFf : ∀ {F1 F2 f1 f2 a b n}, 
  N_uni_derivative F1 f1 a b n -> (∀ x, x ∈ [a|b] -> F1 x = F2 x) -> 
  (∀ x, x ∈ [a|b] -> f1 x = f2 x) -> N_uni_derivative F2 f2 a b n.
Proof.
  intros. eapply NderF in H; eauto. eapply Nderf in H; eauto.
Qed.

Fact uniNder : ∀ {F f1 f2 a b k}, 
   N_uni_derivative F f1 a b k -> N_uni_derivative F f2 a b k -> 
   ∀ x, x ∈ [a|b] -> f1 x = f2 x.
Proof.
  intros. generalize dependent F. induction k; intros. 
  - eapply unider; eauto.
  - destruct H as [f3 [H]], H0 as [f4 [H0]].
    eapply IHk; eauto. pose proof (unider H0 H). eapply NderF; eauto.
Qed.

Fact NderOrdPl : ∀ {F f1 f2 a b n k}, N_uni_derivative F f1 a b n ->
  N_uni_derivative f1 f2 a b k -> N_uni_derivative F f2 a b (Plus_N n k).
Proof.
  intros. generalize dependent F; generalize dependent f1; 
  generalize dependent f2; induction k; intros; apply NderSuf; [eauto|].
  destruct (NderNec H0) as [f3 [H1]]. pose proof (IHk _ _ H1 _ H). eauto.
Qed.

Fact NderOrdMi : ∀ {F f1 f2 a b n k}, N_uni_derivative F f1 a b n ->
  N_uni_derivative F f2 a b (Plus_N n k) -> N_uni_derivative f1 f2 a b k.
Proof.
  intros. generalize dependent F; generalize dependent f1; 
  generalize dependent f2; induction k; intros.
  - destruct (NderNec H0) as [f3 [H1]]. apply (derF H2 (uniNder H1 H)).
  - Simpl_Nin H0. destruct (NderNec H0) as [f3 [H1]].
    pose proof (IHk _ _ _ H H1). apply NderSuf; eauto.
Qed.

Fact NderOP1 : ∀ {F f1 f2 a b n}, N_uni_derivative F f1 a b n ->
  uni_derivative f1 f2 a b -> N_uni_derivative F f2 a b n`.
Proof. intros. rewrite <- NPl_1. eapply NderOrdPl; eauto. Qed.

Fact NderOM1 : ∀ {F f1 f2 a b n}, N_uni_derivative F f1 a b n -> 
  N_uni_derivative F f2 a b n` -> uni_derivative f1 f2 a b.
Proof. intros. rewrite <- NPl_1 in H0. apply (NderOrdMi H H0). Qed.

Fact Nder_lt : ∀ {F a b k}, N_uni_derivability F a b k -> a < b.
Proof.
  intros. destruct H as [f H]. generalize dependent F. induction k; intros.
  - eapply der_lt; eauto. - destruct H, H; eauto.
Qed.

Fact Nderin : ∀ {F f a b c n}, c ∈ [a|b] -> c < b ->
  N_uni_derivative F f a b n -> N_uni_derivative F f c b n.
Proof.
  intros. pose proof (ccir H).
  generalize dependent F; induction n; intros.
  - eapply dersub; eauto.
  - destruct H1 as [f1 [H1]]. exists f1; split; auto.
    eapply dersub; eauto.
Qed.

Fact Ndervety : ∀ {F f a b n}, 
  N_uni_derivative F f a b n -> N_uni_derivability F a b n.
Proof.
  intros. red; eauto.
Qed.

Fact Nderpred : ∀ {F a b n},
  N_uni_derivability F a b n` -> N_uni_derivability F a b n.
Proof.
  intros. generalize dependent F. induction n; intros.
  - destruct H as [f [f1 [H]]]. red; eauto.
  - destruct H as [f [f1 [H]]]. apply Ndervety in H0.
    destruct (IHn _ H0) as [f2 H1]. red; exists f2. red; eauto.
Qed.

Fact Nderltn : ∀ {F a b n k}, ILT_N k n -> 
  N_uni_derivability F a b n -> N_uni_derivability F a b k.
Proof.
  intros. induction n; [N1F H|]. destruct (Theorem26 _ _ H).
  - apply Nderpred in H0; auto.
  - subst k. apply Nderpred; auto.
Qed.

Fact Nderlen : ∀ {F a b n m},  ILE_N m n -> 
  N_uni_derivability F a b n -> N_uni_derivability F a b m.
Proof.
  intros. destruct H. - eapply Nderltn; eauto. - subst m; auto.
Qed.

Axiom cid : ∀ {A :Type} {P :A -> Prop}, (∃ x, P x) -> { x :A | P x }.

Definition Getele {A :Type} {P :A -> Prop} (Q :∃ x, P x) := proj1_sig (cid Q).

Definition n_th {F a b n} (H :N_uni_derivability F a b n) 
  := Getele H.

Definition p_th {F a b n} (H :N_uni_derivability F a b n`) 
  := Getele (Nderpred H).

Definition k_th {F a b n} k (H :ILT_N k n) 
  (H0 :N_uni_derivability F a b n) := Getele (Nderltn H H0).

Definition m_th {F a b n} k (H :ILE_N k n) 
  (H0 :N_uni_derivability F a b n) := Getele (Nderlen H H0).

Ltac mdg1 f := unfold m_th, Getele; 
  destruct cid as [f ]; simpl proj1_sig.
Ltac mdh1 f H := unfold m_th, Getele in H; 
  destruct cid as [f ]; simpl proj1_sig in H.
Ltac kdg1 f := unfold k_th, Getele; 
  destruct cid as [f ]; simpl proj1_sig.
Ltac kdg2 f l f1 := unfold k_th, Getele; 
  destruct (cid l) as [f ], cid as [f1]; simpl proj1_sig.
Ltac kdh1 f H := unfold k_th, Getele in H; 
  destruct cid as [f ]; simpl proj1_sig in H.
Ltac ndg1 f := unfold n_th, Getele; 
  destruct cid as [f ]; simpl proj1_sig.
Ltac ndh1 f H := unfold n_th, Getele in H; 
  destruct cid as [f ]; simpl proj1_sig in H.
Ltac ndh2 f H H0 := unfold n_th, Getele in H, H0; 
  destruct cid as [f ]; simpl proj1_sig in H, H0.
Ltac ndg2 f l f1 := unfold n_th, Getele; 
  destruct (cid l) as [f ], cid as [f1]; simpl proj1_sig.
Ltac pdg1 f := unfold p_th, Getele; 
  destruct cid as [f ]; simpl proj1_sig.
Ltac pdg2 f l f1 := unfold p_th, Getele; 
  destruct (cid l) as [f ], cid as [f1]; simpl proj1_sig.

Fact NderCut : ∀ {F a b n} k l1 (l :N_uni_derivability F a b n), 
  N_uni_derivability (k_th k l1 l) a b (Minus_N n k l1).
Proof.
  intros. generalize dependent F. induction n; intros; [N1F l1|].
  destruct (Theorem26 _ _ l1).
  - inversion l as [f]. destruct (NderNec H0) as [f0 [H1]].
    pose proof (IHn H _ (Ndervety H1)). kdg1 f1. kdh1 f2 H3.
    rewrite (NMi7 _ H). destruct H3 as [f3]. exists f. apply NderSuf.
    exists f3. pose proof (NderOrdPl n1 H3). Simpl_Nin H4.
    apply @NderF with (F2:=f1) in H3; [|eapply uniNder; eauto].
    apply @derF with (F2:=f3) in H2; [|eapply uniNder; eauto]. auto.
  - subst k. Simpl_N. kdg1 f. inversion l as [f1].
    pose proof (NderOM1 n0 H). red; eauto.
Qed.

Fact NderfMu : ∀ {F f a b c n},
  N_uni_derivative F f a b n ->
  N_uni_derivative (mult_fun c F) (mult_fun c f) a b n.
Proof.
  intros. generalize dependent F; induction n; intros.
  - simpl in *. apply derfMu; auto.
  - destruct H as [f1 [H]].
    exists(mult_fun c f1). split; auto. apply derfMu; auto.
Qed.

Fact NderFPl : ∀ {F f G g a b n},
  N_uni_derivative F f a b n -> N_uni_derivative G g a b n -> 
  N_uni_derivative (Plus_Fun F G) (Plus_Fun f g) a b n.
Proof.
  intros. generalize dependent F; generalize dependent G.
  induction n; intros.
  - simpl in *. apply derFPl; auto.
  - destruct H as [f1 [H]], H0 as [g1 [H0]].
    exists(Plus_Fun f1 g1). split; auto. apply derFPl; auto.
Qed.

Fact NderFMi : ∀ {F f G g a b n},
  N_uni_derivative F f a b n -> N_uni_derivative G g a b n -> 
  N_uni_derivative (Minus_Fun F G) (Minus_Fun f g) a b n.
Proof.
  intros. generalize dependent F; generalize dependent G.
  induction n; intros.
  - simpl in *. apply derFMi; auto.
  - destruct H as [f1 [H]], H0 as [g1 [H0]].
    exists(Minus_Fun f1 g1). split; auto. apply derFMi; auto.
Qed.

Fact Nderf_mi : ∀ {F f a b n}, N_uni_derivative F f a b n ->
  N_uni_derivative (λ x, F(-x)) (λ x, (-(1))^n · f(-x)) (-b) (-a) n.
Proof.
  intros. generalize dependent f. induction n; intros.
  - unfold N_uni_derivative in *. unfold Pow. apply derf_mi in H.
    apply @derf with (f1:=(λ x, -f(-x))); intros; Simpl_R.
  - pose proof (Nderpred (Ndervety H)).
    destruct H0 as [f1 H0]. pose proof (IHn _ H0).
    pose proof (NderOM1 H0 H). apply derf_mi in H2.
    apply derfMu with (c:=(-(1))^n)  in H2. unfold mult_fun in H2.
    eapply NderOP1; eauto. apply (derf H2); intros.
    rewrite PowS, Theorem199; Simpl_R.
Qed.

(*--------------------------------------*)

Fact dermxc : ∀ {a b} c m, a < b -> uni_derivative (λ x,m·(x-c)) (λ _,m) a b.
Proof.
  intros. pattern m at 2. rewrite <- Theorem195. apply derfMu.
  pose proof (derFMi (derCx 1 H) (derC c H)).
  apply (derF H0); intros; unfold Minus_Fun; Simpl_R.
Qed.

Fact derpow1 : ∀ {a b} c n, a < b ->
  uni_derivative (λ x, (x-c)^n`)(λ x, n`·(x-c)^n) a b.
Proof.
  intros. pose proof (dermxc c 1 H). induction n.
  - pose proof (derFMu H0 H0). cbv beta in H1.
    apply (derFf H1); unfold Mult_Fun; intros; Simpl_R. rewrite R_T2; auto.
  - pose proof (derFMu IHn H0). cbv beta in H1.
    apply (derFf H1); unfold Mult_Fun; intros; Simpl_R.
    rewrite <- (RN3 (n`)), Theorem201', Theorem199; Simpl_R.
Qed.

Fact derrdf1 : ∀ {a b} c n z, a < b ->
  uni_derivative (λ x, (z·Rdifa ((x-c)^n`) n`))
  (λ x, (z·Rdifa ((x-c)^n) n)) a b.
Proof.
  intros. apply derfMu. pose proof (derpow1 c n H).
  pose proof (derfMu (Rdifa 1 n`) H0). unfold mult_fun in H1.
  apply (derFf H1); intros; [|unfold Rdifa].
  - rewrite Theorem194, rdft; Simpl_R.
  - apply eqTi_R with (z:=factorial n); [apply facun0|Simpl_R].
    rewrite Theorem194, <- Theorem199, Di_Rt.
    rewrite <- Theorem199, (Theorem194 _ n`), Di_Rt; Simpl_R.
Qed.

Fact Nderrdf1 : ∀ {a b} c z n k l, a < b ->
  N_uni_derivative (λ x, (z·Rdifa ((x-c)^n) n))
  (λ x, (z·Rdifa ((x-c)^(Minus_N n k l)) (Minus_N n k l))) a b k.
Proof.
  intros. pose proof (@derrdf1 a b c).
  generalize dependent n. induction k; intros.
  - simpl. pose proof (H0 (Minus_N n 1 l) z H). Simpl_Nin H1.
  - set (l1:=(N1P' l)). assert (IGT_N (Minus_N n 1 l1) k).
    { apply Theorem20_1 with (z:=1); Simpl_N. }
    assert (Minus_N n k` l = Minus_N (Minus_N n 1 l1) k H1).
    { apply Theorem20_2 with (z:=k`); Simpl_N. } rewrite H2.
    generalize (IHk _ H1)(Theorem15 _ _ _ (Nlt_S_ k) l); intros.
    pose proof (derrdf1 c (Minus_N n 1 l1) z H). Simpl_Nin H5. red; eauto.
Qed.

Fact Nderrdf2 : ∀ {a b} c z n, a < b ->
  N_uni_derivative (λ x, (z·Rdifa ((x-c)^n) n)) (λ x, z) a b n.
Proof.
  intros. induction n.
  - simpl. pose proof (dermxc c z H).
    eapply derF; eauto. intros. rewrite rdf_1; auto.
  - pose proof (derrdf1 c n z H). red; eauto.
Qed.
