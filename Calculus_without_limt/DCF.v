(***************************************************************************)
(*   This is part of FA_3rdCalculus, it is distributed under the terms     *)
(*         of the GNU Lesser General Public License version 3              *)
(*                (see file LICENSE for more details)                      *)
(*                                                                         *)
(*     Copyright 2020-2022: Yaoshun Fu and Wensheng Yu.        *)
(***************************************************************************)

Require Export calpre.

Definition diff_quo_median F f a b :=
  ∀ u v l, u ∈ [a|b] -> v ∈ [a|b] -> ∃ p q, p ∈ [u|v] /\ q ∈ [u|v] /\ 
  f p ≦ ((F v - F u)/(v-u))(uneqOP l) /\ ((F v - F u)/(v-u))(uneqOP l) ≦ f q.

Fact medC : ∀ a b C, diff_quo_median (Φ(C)) (Φ(O)) a b.
Proof.
  intros; red; intros. Simpl_R. apply Theorem182_1 in l.
  exists u, v. repeat split; red; auto.
Qed.

Fact medCx : ∀ a b C, diff_quo_median (λ x, C·x) (Φ(C)) a b.
Proof.
  intros; red; intros. rewrite <- Theorem202. Simpl_R.
  apply Theorem182_1 in l. exists u, v. repeat split; red; auto.
Qed.

Fact medfMu : ∀ {a b F f} c, diff_quo_median F f a b -> 
  diff_quo_median (mult_fun c F) (mult_fun c f) a b.
Proof.
  intros. red; intros. destruct (H _ _ l H0 H1) as [p [q [H2 [H3 [H4]]]]].
  unfold mult_fun. destruct (Theorem167 c O) as [H6|[H6|H6]].
  - exists p, q. subst c. unfold ILE_R; Simpl_R.
  - exists q, p. split; [|split]; auto. apply Theorem176_3 in H6.
    apply (LeTi_R1' _ _ (-c)), LEminus in H4; auto.
    do 2 rewrite Theorem197' in H4. Simpl_Rin H4.
    apply (LeTi_R1' _ _ (-c)), LEminus in H5; auto.
    do 2 rewrite Theorem197' in H5. Simpl_Rin H5.
    rewrite <- Theorem202, <- Di_Rt. auto.
  - apply (LeTi_R1' _ _ c) in H4; apply (LeTi_R1' _ _ c) in H5; auto.
    rewrite Di_Rt, Theorem202 in H4, H5. exists p, q; auto.
Qed.

Fact medf_mi : ∀ {F f a b}, diff_quo_median F f a b ->
  diff_quo_median (λ x, F(-x)) (λ x, -f(-x)) (-b) (-a).
Proof.
  intros. red; intros. pose proof l. rewrite <- Theorem181 in H2.
  unfold Minus_R in H2. rewrite Theorem180, RMic in H2.
  apply ccimi in H0. apply ccimi in H1. Simpl_Rin H0. Simpl_Rin H1.
  destruct (H _ _ H2 H1 H0) as [p [q [H3 [H4 [H5]]]]].
  apply ccimi in H3. apply ccimi in H4. Simpl_Rin H3. Simpl_Rin H4.
  exists (-q), (-p). split; [|split]; Simpl_R.
  apply LeTi_R1 with (z:=-u--v) in H5; Simpl_Rin H5.
  apply LeTi_R1 with (z:=-u--v) in H6; Simpl_Rin H6.
  rewrite Theorem175 in H5, H6. Simpl_Rin H5. Simpl_Rin H6.
  split; apply LeTi_R2 with (z:=v-u); Simpl_R;
  apply LEminus; rewrite Theorem197', Theorem181; Simpl_R.
Qed.

Fact medf_cd : ∀ {F f a b} c d l,
  diff_quo_median F f a b -> diff_quo_median (multfun_pl F c d) 
  (mult_fun c (multfun_pl f c d))(((a-d)/c) (uneqOP l))(((b-d)/c) (uneqOP l)).
Proof.
  intros. red; intros. apply cciMu, cciMi in H0; Simpl_Rin H0.
  apply cciMu, cciMi in H1; Simpl_Rin H1.
  assert ((c·v+d) - (c·u+d) > O). 
  { rewrite <- Mi_R, <- Theorem202; Simpl_R. apply Pos; auto. }
  destruct (H _ _ H2 H0 H1) as [p [q [H3 [H4 [H5]]]]].
  rewrite <- (Theorem177 d),RMic, RMic in H3, H4.
  apply cciMi in H3. apply cciMi in H4. Simpl_Rin H3. Simpl_Rin H4.
  assert ((1/c) (uneqOP l) > O). { apply Pos'; simpl; auto. }
  assert (c=(1/(1/c) (uneqOP l)) (uneqOP H7)). 
  { apply eqTi_R with (z:=(1/c) (uneqOP l)); Simpl_R. intro. EGR H8 H7. }
  rewrite Theorem194, (Theorem194 c) in H3, H4.
  rewrite H8, Di_Rt, Di_Rt in H3, H4. Simpl_Rin H3. Simpl_Rin H4.
  apply cciMu in H3; auto. rewrite Theorem194, Di_Rt in H3. Simpl_Rin H3.
  apply cciMu in H4; auto. rewrite Theorem194, Di_Rt in H4. Simpl_Rin H4.
  apply LeTi_R1' with (z:=(c·v+d) - (c·u+d)) in H5; Simpl_Rin H5.
  apply LeTi_R1' with (z:=(c·v+d) - (c·u+d)) in H6; Simpl_Rin H6.
  rewrite <- Mi_R, <- Theorem202 in H5, H6. Simpl_Rin H5. Simpl_Rin H6.
  rewrite (Theorem194 c (v-u)), Theorem199 in H5, H6.
  exists (((p-d)/c) (uneqOP l)), (((q-d)/c) (uneqOP l)).
  split; [|split]; auto. unfold mult_fun, multfun_pl. Simpl_R; split;
  apply LeTi_R2' with (z:=v-u); Simpl_R.
Qed.

Fact medfmi : ∀ {F f a b}, diff_quo_median F f a b -> 
  diff_quo_median (minus_fun F) (minus_fun f) a b.
Proof.
  intros. pose proof (medfMu (-(1)) H). do 2 rewrite <- mFun; auto.
Qed.

Fact medpos_inc : ∀ F f a b, diff_quo_median F f a b -> 
  (∀ x, x ∈ [a|b] -> f(x) ≧ O) -> fun_inc F [a|b].
Proof.
  intros; red; intros. pose proof (Theorem182_1' _ _ H3) as l.
  destruct (H _ _ l H1 H2) as [p [q [H4 [H5 [H6]]]]].
  apply LeTi_R1' with (z:=(y-x)) in H6; Simpl_Rin H6.
  apply LePl_R with (z:=-(F x)); Simpl_R. eapply Theorem173; eauto.
  eapply ccisub in H4; eauto. pose proof (H0 _ H4).
  apply Theorem168 in H8. apply Rle3; red; auto.
Qed.

Fact medneg_dec : ∀ F f a b, diff_quo_median F f a b -> 
  (∀ x, x ∈ [a|b] -> f(x) ≦ O) -> fun_dec F [a|b].
Proof.
  intros. apply medfmi in H. rewrite (mmFun F). apply inde.
  eapply medpos_inc; eauto; intros.
  unfold minus_fun. apply Theorem168', LEminus; Simpl_R.
Qed.

Fact medpos_sinc : ∀ F f a b, diff_quo_median F f a b -> 
  (∀ x, x ∈ [a|b] -> f(x) > O) -> fun_sinc F [a|b].
Proof.
  intros; red; intros. pose proof (Theorem182_1' _ _ H3) as l.
  destruct (H _ _ l H1 H2) as [p [q [H4 [H5 [H6]]]]].
  apply LeTi_R1' with (z:=(y-x)) in H6; Simpl_Rin H6.
  apply Theorem182_1. eapply Theorem172; right; split; try apply H6.
  eapply ccisub in H4; eauto. apply Pos; auto.
Qed.

Fact medneg_sdec : ∀ F f a b, diff_quo_median F f a b -> 
  (∀ x, x ∈ [a|b] -> f(x) < O) -> fun_sdec F [a|b].
Proof.
  intros. apply medfmi in H. rewrite (mmFun F). apply insde.
  eapply medpos_sinc; eauto; intros. unfold minus_fun.
  apply Theorem183_1'; Simpl_R. apply H0; auto.
Qed.

Lemma medccpre : ∀ {F f a b}, diff_quo_median F f a b -> 
  fun_inc f [a|b] -> ∀ {x1 x2}, x1 < x2 -> x1 ∈ [a|b] -> x2 ∈ [a|b] -> 
  ∀ c, c > O -> c < 1 -> F(c·x1+(1-c)·x2) ≦ c·F(x1) + (1-c)·F(x2).
Proof.
  intros. pose proof (Theorem182_1' _ _ H1) as l. apply Theorem182_1' in H5.
  assert ((c·x1 + (1-c)·x2) - x1 = (1-c)·(x2-x1)) as G1.
  { rewrite Theorem202, Theorem175. unfold Minus_R. rewrite Theorem186.
    f_equal. rewrite <- Theorem197', Theorem180, Theorem175. Simpl_R.
    rewrite Theorem201'. Simpl_R. }
  assert (x2 - (c·x1 + (1-c)·x2) = c·(x2-x1)) as G2.
  { rewrite Theorem175. unfold Minus_R. rewrite Theorem180, <- Theorem186.
    rewrite Theorem201', Theorem180, <- Theorem186. Simpl_R. simpl Minus_R.
    rewrite Theorem197'. Simpl_R. rewrite <- Theorem202; auto. }
  assert ((c·x1 + (1-c)·x2) - x1 > O) as l1. { rewrite G1. apply Pos; auto. }
  assert (x2 - (c·x1 + (1-c)·x2) > O) as l2. { rewrite G2. apply Pos; auto. }
  assert ((c·x1 + (1-c)·x2) ∈ [a|b]).
  { apply Theorem182_1 in l1. apply Theorem182_1 in l2. split; split.
    - destruct H2, H2. eapply Theorem173; eauto. left; auto.
    - destruct H3, H3. eapply Theorem173; eauto. left; auto. }
  destruct (H _ _ l1 H2 H6) as [p1 [q1 [H7 [H8 [H9]]]]].
  destruct (H _ _ l2 H6 H3) as [p2 [q2 [H11 [H12 [H13]]]]].
  apply LeTi_R1 with (z:=((c·x1 + (1-c)·x2) - x1)) in H10; Simpl_Rin H10.
  apply LeTi_R1 with (z:=(x2 - (c·x1 + (1-c)·x2))) in H13; Simpl_Rin H13.
  rewrite G1, G2 in *. apply LeTi_R1' with (z:=c) in H10; Simpl_Rin H10.
  apply LeTi_R1' with (z:=1-c) in H13; Simpl_Rin H13.
  apply LEminus in H10. pose proof (Theorem191' H13 H10). Simpl_Rin H15.
  rewrite Theorem194, (Theorem194 (1-c)), (Theorem194 c), (Theorem194 c) in H15.
  repeat rewrite Theorem199 in H15. 
  rewrite (Theorem194 c), <- Theorem202' in H15.
  do 2 rewrite Theorem202 in H15. unfold Minus_R in H15 at 4.
  rewrite Theorem181, Mi_R, <- Theorem201' in H15. Simpl_Rin H15.
  rewrite Theorem175 in H15.
  apply LePl_R with (z:=-F(c·x1+(1-c)·x2)); Simpl_R.
  eapply Theorem173; eauto. apply Rle3.
  - apply LePl_R with (z:=f q1); Simpl_R.
    generalize (ccisub _ _ H2 H6 H8) (ccisub _ _ H6 H3 H11); intros.
    destruct H8, H8, H11, H11. eapply Theorem173 in H11; eauto.
    destruct H11. apply H0; auto. subst p2; red; auto. 
  - left; repeat apply Pos; auto.
Qed.

Fact medconc : ∀ {F f a b}, diff_quo_median F f a b -> 
  fun_inc f [a|b] -> convexdown F [a|b].
Proof.
  intros; red; intros. destruct (Theorem167 x1 x2) as [H5|[H5|H5]].
  - subst x1. repeat rewrite <- Theorem201'. red; Simpl_R.
  - eapply medccpre; eauto.
  - apply Theorem182_1' in H4.
    assert (1-c < 1).
    { apply Theorem188_1 with (Θ:=c); Simpl_R. apply Pl_R; auto. }
    pose proof (medccpre H H0 H5 H2 H1 _ H4 H6). Simpl_Rin H7.
    rewrite Theorem175, (Theorem175 (c·F(x1))); auto.
Qed.

Fact medconv : ∀ {F f a b}, diff_quo_median F f a b -> 
  fun_dec f [a|b] -> convexup F [a|b].
Proof.
  intros; red; intros. apply medfmi in H.
  apply LEminus. rewrite Theorem180, <- Theorem197'', <- Theorem197''.
  destruct (inde (minus_fun f) a b). rewrite <- mmFun in H6. apply H6 in H0.
  apply (medconc H H0); auto.
Qed.
