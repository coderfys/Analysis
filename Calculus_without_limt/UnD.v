(***************************************************************************)
(*   This is part of FA_3rdCalculus, it is distributed under the terms     *)
(*         of the GNU Lesser General Public License version 3              *)
(*                (see file LICENSE for more details)                      *)
(*                                                                         *)
(*            Copyright 2020-2022: Yaoshun Fu and Wensheng Yu.             *)
(***************************************************************************)

Require Export DCF.

Definition uni_derivative F f a b := 
  ∃ d, fun_pinc d (O|b-a] /\ unbRecF d (O|b-a] /\ ∃ M, O < M /\ 
  ∀ x h, x ∈ [a|b] -> (x+h) ∈ [a|b] -> |F(x+h) - F(x) - f(x)·h| ≦ M·|h|·d(|h|).

Corollary Co_der : ∀ {F f d M a b}, 
  (∀ x h, x ∈ [a|b] -> (x+h) ∈ [a|b] -> 
  |F(x+h) - F(x) - f(x)·h| ≦ M·|h|·d(|h|)) -> 
  ∀ {p q}, p ∈ [a|b] -> q ∈ [a|b] -> 
  |F(q) - F(p) - f(p)·(q-p)| ≦ M·|q-p|·d(|q-p|).
Proof.
  intros. pattern q at 1; rewrite <- (RMi1' _ p). apply H; Simpl_R.
Qed.

Definition uni_derivability F a b := ∃ f, uni_derivative F f a b.

Fact der_lt : ∀ {F f a b}, uni_derivative F f a b -> a < b.
Proof.
  intros. destruct H as [d [_ [H _]]], (H O) as [z [l [H0 _]]], H0, H0.
  apply Theorem182_1. eapply Theorem172; eauto.
Qed.

Fact dersub : ∀ {F f u v a b}, u ∈ [a|b] -> v ∈ [a|b] -> v > u ->
  uni_derivative F f a b -> uni_derivative F f u v.
Proof.
  intros. destruct H2 as [d [H2 [H5 [M [H6]]]]], H2.
  exists d. repeat split; intros.
  - apply H2, (ocisub v u); auto.
  - red; intros. apply H4; auto; apply (ocisub v u); auto.
  - red; intros. destruct (H5 M0) as [z [l [H7]]].
    destruct (Co_T167 z (v-u)), H7, H7.
    + exists z, l; split; auto. split; split; auto.
    + apply Theorem182_1' in H1.
      assert ((v-u) ∈ (O|b-a]).
      { apply (ocisub v u); auto. split; unfold ILE_R; auto. }
      assert (z ∈ (O|b-a]). { split; unfold ILE_R; auto. }
      set (H13:=uneqOP (H2 _ H11)).
      exists (v-u), H13; split.
      * split; unfold ILE_R; auto.
      * eapply Theorem172; right; split; eauto.
        pose proof (H2 _ H11). pose proof (H2 _ H12).
        rewrite Ab3; [| apply Pos'; simpl; auto ].
        rewrite Ab3; [| apply Pos'; simpl; auto ].
        apply LeTi_R2' with (z:=(d z)); Simpl_R.
        rewrite Di_Rt; Simpl_R.
        apply LeTi_R2' with (z:=(d (v-u))); Simpl_R.
  - exists M; split; intros; auto.
    apply (ccisub _ _ H H0) in H7. apply (ccisub _ _ H H0) in H8; auto.
Qed.

Fact derf : ∀ {F f1 f2 a b}, uni_derivative F f1 a b ->
  (∀ x, x ∈ [a|b] -> f1 x = f2 x) -> uni_derivative F f2 a b.
Proof.
  intros. simpl in *. destruct H as [d [H]], H1, H2 as [M [H2]].
  exists d; split; [|split]; auto.
  exists M; split; auto; intros. rewrite <- H0; auto.
Qed.

Fact derF : ∀ {F1 F2 f a b}, uni_derivative F1 f a b ->
  (∀ x, x ∈ [a|b] -> F1 x = F2 x) -> uni_derivative F2 f a b.
Proof.
  intros. destruct H as [d [H]], H1, H2 as [M [H2]].
  exists d; split; [|split]; auto.
  exists M; split; auto; intros. repeat rewrite <- H0; auto.
Qed.

Fact derFf : ∀ {F1 F2 f1 f2 a b}, 
  uni_derivative F1 f1 a b -> (∀ x, x ∈ [a|b] -> F1 x = F2 x) -> 
  (∀ x, x ∈ [a|b] -> f1 x = f2 x) -> uni_derivative F2 f2 a b.
Proof.
  intros. eapply derF in H; eauto. eapply derf in H; eauto.
Qed.

Fact ucderf : ∀ {F f a b}, uni_derivative F f a b -> uniform_continuous f a b.
Proof.
  intros. destruct H as [d [H [H0 [M [H1]]]]]. set (D1:=λ x, 2·M·d(x)).
  set (D:=λ x, match classicT (x=O) with 
               | left _ => O | right _ => D1(x) end).
  assert (G1 :2·M > O). { apply Pos; simpl; auto. } destruct H.
  assert (G2 :fun_pinc D1 (O |b-a]).
  { red; split; intros; unfold D.
    - apply Pos; auto.
    - red; intros. apply LeTi_R1'; auto. }
  assert (G3 :unbRecF D1 (O|b-a]).
  { red; intros; unfold D1. destruct (H0 (2·M·M0)) as [z [l [H6]]].
    assert ((2·M·d(z)) > O). { apply Pos; auto. }
    exists z, (uneqOP H5); split; auto.
    apply Theorem203_1' with (Θ:=2·M·d(z)); auto.
    pattern (2·M·d(z)) at 3. rewrite <- Ab3; auto.
    rewrite <- Theorem193; Simpl_R.
    apply Theorem203_1 with (Θ:=d(z)) in H4; auto.
    pattern (d z) at 2 in H4. rewrite <- Ab3 in H4; auto.
    rewrite <- Theorem193, Theorem199 in H4; Simpl_Rin H4.
    rewrite Theorem194, Theorem199, (Theorem194 _ M0); auto. }
  assert (∀ z, z ∈ (O|b-a] -> D z = D1 z).
  { intros. destruct H4, H4.
    unfold D; destruct classicT; auto. EGR e H4. }
  assert (fun_pinc D (O|b-a]).
  { destruct G2. split; [|red]; intros; repeat rewrite H4; auto. }
  assert (unbRecF D (O|b-a]).
  { red; intros. destruct (G3 M0) as [z [l [H8]]].
    exists z. rewrite H4; eauto. } exists D. split; auto. split; auto. intros. 
  assert ((x+h+(-h)) ∈ [a|b]). { Simpl_R. }
  pose proof (H2 _ _ H7 H8); pose proof (H2 _ _ H8 H9); Simpl_Rin H11.
  rewrite <- Theorem178 in H11. unfold Minus_R in H11.
  rewrite Theorem180 in H11. Simpl_Rin H11.
  rewrite Theorem181, Theorem197'' in H11. Simpl_Rin H11.
  pose proof (Rle4 H11 H10). Simpl_Rin H12. repeat rewrite Theorem178 in H12.
  unfold D. destruct classicT.
  { destruct h; inversion e; Simpl_R; red; auto. }
  destruct (Theorem170 h); try tauto. apply LeTi_R2 with (z:=|h|); auto.
  rewrite <- Theorem193, Theorem202'. unfold D1.
  rewrite Theorem199, (Theorem194 (d(|h|))).
  rewrite Theorem199, <- (Theorem199 M), R_T2; auto.
Qed.

Fact boundderf : ∀ {F f a b}, uni_derivative F f a b -> bound_ran f a b.
Proof.
  intros. eapply ucbound, ucderf; eauto.
Qed.

Fact lipderF : ∀ {F f a b}, uni_derivative F f a b -> Lipschitz F a b.
Proof.
  intros. pose proof (der_lt H). apply Theorem182_1' in H0.
   destruct (boundderf H) as [A [H1]], H as [d [H [H3 [M [H4]]]]].
  assert (M·d(|b-a|)+A > O).
  { rewrite <- (Theorem175' O), Ab3; auto. apply Theorem189; auto.
    apply Pos; auto. apply H; split; split; red; auto. }
  exists (M·d(|b-a|)+A). split; auto; intros. pose proof (H5 _ _ H7 H8).
  eapply Theorem173 in H9; try apply Ab2'.
  apply LePl_R with (z:=|f(x)·h|) in H9; Simpl_Rin H9.
  rewrite Theorem193, Theorem194, <- Theorem199, <- Theorem201' in H9.
  destruct (classic (h=O)). { subst h. Simpl_R; red; auto. }
  eapply Theorem173; eauto. apply LeTi_R; [apply Theorem170'|].
  apply Theorem191'; [| left; auto]. rewrite Theorem194. apply LeTi_R1'; auto.
  pose proof (ccile1 H7 H8); Simpl_Rin H11. apply Ab8 in H10.
  eapply Co_inc; try apply H; try rewrite (Ab3 (b-a)); auto; 
  split; split; red; auto.
Qed.

Fact boundderF : ∀ {F f a b}, uni_derivative F f a b -> bound_ran F a b.
Proof.
  intros. exact (lipbound (lipderF H)).
Qed.

Fact unider : ∀ {F f1 f2 a b}, uni_derivative F f1 a b -> 
  uni_derivative F f2 a b -> ∀x, x ∈ [a|b] -> f1 x = f2 x.
Proof.
  intros. pose proof (der_lt H).
  destruct H as [d1 H], H, H3, H4 as [M1 [H4]].
  destruct H0 as [d2 H0], H0, H6, H7 as [M2 [H7]].
  Absurd. apply Ab8' in H9. set (M:= R2max M1 M2). set (d:= maxfun d1 d2).
  assert (M > O). { unfold M. destruct (Pr_max4 M1 M2); now rewrite H10. }
  assert (∀ x h,x ∈ [a|b] -> (x+h) ∈ [a|b] -> h <> O -> 
    |f1(x)-f2(x)| ≦ (M+M)· d(|h|)).
  { intros. pose proof (H5 _ _ H11 H12). pose proof (H8 _ _ H11 H12).
    pose proof (Rle4 H14 H15). Simpl_Rin H16. rewrite Theorem178 in H16.
    rewrite <- Theorem202', Theorem193 in H16.
    pose proof (ociabs H11 H12 H13). apply Ab8 in H13.
    destruct H, H0. apply LeTi_R2 with (z:=|h|); auto.
    eapply Theorem173; eauto. repeat rewrite Theorem199, Theorem201'.
    apply Theorem191'; rewrite Theorem199, (Theorem194 _ (|h|)).
    - apply LeTi_R3.
      + left. apply Pos; auto. + left; auto. + apply Pr_max2.
      + apply LeTi_R1'; auto. unfold d. rewrite maxfx. apply Pr_max2.
    - apply LeTi_R3.
      + left. apply Pos; auto. + left; auto. + apply Pr_max3.
      + apply LeTi_R1'; auto. unfold d. rewrite maxfx. apply Pr_max3. }
  assert (∃ h, (x+h) ∈ [a|b] /\ h <> O).
  { pose proof H1. destruct H1, H1, H1.
    - pose proof (ccil H12). exists (a-x); split; Simpl_R.
      apply Theorem182_3' in H1. intro. ELR H15 H1.
    - subst a. pose proof (ccir H12). exists (b-x); split; Simpl_R.
      apply Theorem182_1' in H2. intro. EGR H14 H2. } destruct H12 as [h [H12]].
  assert (fun_pinc d (O|b-a]). { apply fpcp2; auto. }
  assert (unbRecF d (O|b-a]). { apply ubrp2; auto. }
  assert (unbRecF d (O|(|h|)]).
  { red; intros. destruct (H15 M0) as [z1 [l1 [H16]]].
    assert (R2min z1 (|h|) ∈ (O|b-a]).
    { destruct H16, H16. apply Ab8 in H13. split; split.
      - apply R2mgt; auto.
      - eapply Theorem173; eauto. apply Pr_min2. }
    pose proof H18. apply H14 in H18.
    exists (R2min z1 (|h|)), (uneqOP H18). split; auto.
    - destruct H19, H19. split; split; auto. apply Pr_min3.
    - destruct (Co_T167 M0 O) as [G|G].
      { eapply Theorem172; left; split; eauto.
        apply Ab8''. intro. inversion H20. }
      apply Rlt1 in H17. apply Rlt1.
      eapply Theorem172; left; split; eauto. apply LeTi_R1'; auto.
      destruct H14. rewrite Ab3, (Ab3 (d z1)); auto.
      eapply Co_inc; eauto. apply Pr_min2. } set (l1:= uneqOP H9).
  destruct (H16 (((M+M)/(|f1 x - f2 x|)) l1)) as [z [l [H17]]], H17, H17.
  assert (d z > O) as G1.
  { apply H14. destruct (ociabs H1 H12 H13), H20.
    split; split; auto. eapply Theorem173; eauto. }
  assert ((x+z) ∈ [a|b] \/ (x+(-z)) ∈ [a|b]).
  { destruct (Theorem167 h O) as [H20 | [H20| H20]]; try tauto.
    - right. split. split.
      + rewrite Ab3'' in H19; auto.
        destruct H12, H12. eapply Theorem173; eauto.
        unfold Minus_R. rewrite Theorem175, (Theorem175 x). apply LePl_R.
        apply LEminus. Simpl_R.
      + destruct H1, H1. eapply Theorem173; eauto.
        left. apply Theorem188_1 with (Θ:=z); Simpl_R. apply Pl_R; auto.
    - left. rewrite Ab3 in H19; auto. split. split.
      + destruct H1, H1. eapply Theorem173; eauto. left. apply Pl_R; auto.
      + destruct H12, H12. eapply Theorem173; eauto.
        apply Theorem191'; red; auto. }
  assert (z<>O). { intro. EGR H21 H17. }
  assert (-z<>O). { intro. apply H21. apply Theorem183_2'; Simpl_R. }
  destruct H20.
  - pose proof (H11 _ _ H1 H20 H21). rewrite (Ab3 z) in H23; auto.
    apply Theorem203_1 with (Θ:=|f1 x - f2 x|) in H18; Simpl_Rin H18.
    rewrite Theorem194, <- Theorem193, Di_Rt in H18; Simpl_Rin H18.
    apply Rlt1 in H18. rewrite Ab3 in H18; auto. LEGR H23 H18.
  - pose proof (H11 _ _ H1 H20 H22).
    rewrite Theorem178, (Ab3 z) in H23; auto.
    apply Theorem203_1 with (Θ:=|f1 x - f2 x|) in H18; Simpl_Rin H18.
    rewrite Theorem194, <- Theorem193, Di_Rt in H18; Simpl_Rin H18.
    apply Rlt1 in H18. rewrite Ab3 in H18; auto. LEGR H23 H18.
Qed.

Fact derC : ∀ {a b} C, a < b -> uni_derivative (Φ(C)) (Φ(O)) a b.
Proof.
  intros. generalize (fpcp1 a b)(ubrp1 H); intros.
  exists Δ. split; auto. split; auto.
  exists 1; split; [reflexivity|intros]. Simpl_R. apply square_p1.
Qed.

Fact derCx : ∀ {a b} C, a < b -> uni_derivative (λ x, C·x) (Φ(C)) a b.
Proof.
  intros. generalize (fpcp1 a b)(ubrp1 H); intros.
  exists Δ. split; auto. split; auto.
  exists 1; split; [reflexivity|intros].
  rewrite <- Theorem202. Simpl_R. apply square_p1.
Qed.

Fact derfMu : ∀ {a b F f} c, uni_derivative F f a b -> 
  uni_derivative (mult_fun c F) (mult_fun c f) a b.
Proof.
  intros. destruct H as [d [H]], H0, H1 as [M [H1]].
  exists d; split; auto. split; auto.
  destruct (classic (c=O)) as [H3 | H3]; unfold mult_fun.
  - subst c; exists M; split; intros; Simpl_R; simpl.
    eapply Theorem173; eauto. apply Theorem170'.
  - exists (|c|·M); split; intros.
    + apply Pos; auto. apply Ab8; auto.
    + pose proof (H2 _ _ H4 H5). rewrite Theorem199.
      repeat rewrite <- Theorem202, Theorem199.
      rewrite Theorem193, <- (Theorem199 M).
      apply LeTi_R'; auto. apply Theorem170'.
Qed.

Fact derf_mi : ∀ {F f a b}, uni_derivative F f a b ->
  uni_derivative (λ x, F(-x)) (λ x, -f(-x)) (-b) (-a).
Proof.
  intros. destruct H as [d [H [H2 [M [H3]]]]].
  exists d; split; Simpl_R; rewrite Theorem175; Simpl_R. split; auto.
  exists M; split; intros; Simpl_R.
  apply ccimi in H1. Simpl_Rin H1. apply ccimi in H4. Simpl_Rin H4.
  pose proof (Co_der H0 H1 H4). Simpl_Rin H5.
  assert (-(x+h) + x = -h). 
  { apply Theorem183_2'. rewrite Theorem180; Simpl_R. }
  rewrite H6, Theorem178, <- Theorem197 in H5; auto.
Qed.

Fact derf_cd : ∀ {F f a b} c d l,
  uni_derivative F f a b -> uni_derivative (multfun_pl F c d) 
  (mult_fun c (multfun_pl f c d))(((a-d)/c) (uneqOP l))(((b-d)/c) (uneqOP l)).
Proof.
  intros. destruct H as [p [H]], H, H0, H2 as [M [H2]].
  exists (multfun_ p c); repeat apply conj; try red; unfold multfun_; intros.
  - apply ociMu with (d:=c) in H4; auto.
    rewrite Mi_R' in H4; Simpl_Rin H4. apply H; auto.
  - apply ociMu with (d:=c) in H4; apply ociMu with (d:=c) in H5; auto.
    rewrite Mi_R' in H4, H5; Simpl_Rin H4; Simpl_Rin H5.
    apply Theorem203_1 with (Θ:=c) in H6; auto.
    rewrite Theorem194, (Theorem194 _ c) in H6; auto.
  - destruct (H0 M0), H4, H4.
    assert (neq_zero (p (c · (x / c) (uneqOP l)))). { Simpl_R. }
    exists ((x/c) (uneqOP l)), H6; split.
    + apply ociMu'; Simpl_R. rewrite Mi_R'; Simpl_R.
    + apply Rlt1 in H5. apply Rlt1. Simpl_R.
  - exists (c·M); split; intros.
    + apply Pos; auto.
    + apply cciMu, cciMi in H4; apply cciMu, cciMi in H5; auto.
      pose proof (Co_der H3 H4 H5).
      assert (c·(x+h) + d - (c·x + d) = c·h).
      { rewrite Theorem201. rewrite <- Mi_R. Simpl_R. }
      rewrite H7 in H6. unfold multfun_pl, mult_fun.
      rewrite (Theorem194 _ (f(c·x+d))), Theorem199.
      pattern c at 5 6; rewrite <- Ab3; auto.
      rewrite (Theorem194 (|c|)), (Theorem199 M), <- Theorem193; auto.
Qed.

Fact derfmi : ∀ {F f a b}, uni_derivative F f a b -> 
  uni_derivative (minus_fun F) (minus_fun f) a b.
Proof.
  intros. pose proof (derfMu (-(1)) H). do 2 rewrite <- mFun; auto.
Qed.

Fact derFPl : ∀ {F G f g a b},
  uni_derivative F f a b -> uni_derivative G g a b -> 
  uni_derivative (Plus_Fun F G) (Plus_Fun f g) a b.
Proof.
  intros. destruct H as [d1 H], H, H1, H2 as [M1 [H2]].
  destruct H0 as [d2 H0], H0, H4, H5 as [M2 [H5]]. set (d:=maxfun d1 d2).
  assert (fun_pinc d (O|b-a]). { apply fpcp2; auto. }
  assert (unbRecF d (O|b-a]). { eapply ubrp2; eauto. }
  exists d. split; auto. split; auto.
  exists (M1 + M2); split; intros.
  - destruct M1, M2; simpl; auto; inversion H2; inversion H5.
  - generalize (H3 _ _ H9 H10) (H6 _ _ H9 H10); intros.
    pose proof (Theorem191' H11 H12).
    eapply Theorem173 in H13; try apply Ab2; eauto.
    rewrite Mi_R, <- Theorem201', Mi_R in H13.
    eapply Theorem173; eauto. repeat rewrite Theorem201'.
    apply Theorem191'; apply LeTi_R'; red.
    + destruct M1, h; simpl; tauto.
    + unfold d, maxfun; destruct Rcase; auto.
    + destruct M2, h; simpl; tauto.
    + unfold d, maxfun; destruct Rcase; auto.
Qed.

Fact derFMi : ∀ {F G f g a b}, 
  uni_derivative F f a b -> uni_derivative G g a b -> 
  uni_derivative (Minus_Fun F G) (Minus_Fun f g) a b.
Proof.
  intros. exact (derFPl H (derfmi H0)).
Qed.

Lemma dMupre : ∀ A B C D a b c, 
  (A-B)·(C-D)+D·(A-B-a·c)+B·(C-D-b·c) = A·C-B·D-(a·D+B·b)·c.
Proof.
  intros. rewrite (Theorem202 (A-B)), (Theorem194 D), (Theorem202' D (A-B)).
  unfold Minus_R. rewrite <- Theorem186. Simpl_R.
  repeat rewrite Theorem202. repeat rewrite Theorem202'.
  rewrite Mi_R. unfold Minus_R. rewrite <- Theorem186. Simpl_R.
  rewrite (Theorem194 (a·c)). repeat rewrite <- Theorem199.
  rewrite (Theorem194 D), Theorem201'; auto.
Qed.

Fact derFMu : ∀ {F G f g a b}, 
  uni_derivative F f a b -> uni_derivative G g a b -> 
  uni_derivative (Mult_Fun F G) (λ x, (f x)·(G x) + (F x)·(g x)) a b.
Proof.
  intros. pose proof (der_lt H) as K. apply Theorem182_1' in K.
  destruct (lipderF H) as [M1 [H1]], (lipderF H0) as [M2 [H3]]. 
  destruct (boundderF H) as [A1 [H5]], (boundderF H0) as [A2 [H7]].
  destruct H as [d1 H], H, H9, H10 as [M3 [H10]].
  destruct H0 as [d2 H0], H0, H12, H13 as [M4 [H14]].
  assert (fun_pinc Δ (O|b-a]). { apply fpcp1; auto. }
  assert (unbRecF Δ (O|b-a]). { apply ubrp1, Theorem182_1; auto. }
  pose proof (fpcp2 (fpcp2 H H0) H15) as K2.
  pose proof (ubrp2 (fpcp2 H H0) H15 (ubrp2 H H0 H9 H12) H16) as K3.
  set (d:=maxfun (maxfun d1 d2) Δ) in *. exists d.
  split; auto. split; auto.
  assert (M1·M2 + A2·M3 + A1·M4 > O).
  { generalize (Pos _ _ H1 H3) (Pos _ _ H7 H10) (Pos _ _ H5 H14); intros.
    exact (Theorem189 (Theorem189 H17 H18) H19). }
  exists (M1·M2 + A2·M3 + A1·M4); split; auto; intros.
  destruct (classic (h=O)) as [K4|K4]. { subst h. Simpl_R. red; auto. }
  generalize (H11 _ _ H18 H19) (H13 _ _ H18 H19) 
    (H2 _ _ H18 H19) (H4 _ _ H18 H19); intros.
  apply LeTi_R' with (z:=|G x|) in H20; [|apply Theorem170'].
  apply LeTi_R' with (z:=|F x|) in H21; [|apply Theorem170'].
  apply (LeTi_R3 (|G(x+h) - G x|) (M2·|h|)) in H22; auto.
  2:apply Theorem170'. 2: apply Rle3; red; auto; apply Theorem170'.
  rewrite <- Theorem193, Theorem199, (Theorem194 (|h|)) in H22.
  do 2 rewrite <- Theorem199 in H22. clear H23.
  rewrite <- Theorem199, <- Theorem193 in H20, H21.
  rewrite (Theorem199 _ (|h|)), absqu in H22.
  pose proof (Theorem191' H20 H21). eapply Theorem173 in H23; try apply Ab2.
  pose proof (Theorem191' H22 H23). eapply Theorem173 in H24; try apply Ab2.
  rewrite <- Theorem186, dMupre in H24. unfold Mult_Fun.
  eapply Theorem173; eauto. rewrite <- absqu, <- Theorem186. 
  pose proof (ociabs H18 H19 K4). apply Ab8 in K4.
  repeat rewrite Theorem201'. apply Theorem191'; [apply Theorem191'|].
  - rewrite <- Theorem199. apply LeTi_R'.
    + left. apply Pos; [apply Pos|]; auto.
    + unfold d. rewrite maxfx. apply Pr_max3.
  - assert (((A2·M3)·|h|)·d1(|h|) ≦ ((A2·M3)·|h|)·d(|h|)).
    { apply LeTi_R'.
      - left. apply Pos; [apply Pos|]; auto.
      - unfold d. rewrite maxfx, maxfx. rewrite Pr_max1'. apply Pr_max2. }
    eapply Theorem173; eauto. apply LeTi_R. 
    + left; apply H; auto.
    + rewrite Theorem199. apply LeTi_R1; [|red; auto]. apply Pos; auto.
  - assert (((A1·M4)·|h|)·d2(|h|) ≦ ((A1·M4)·|h|)·d(|h|)).
    { apply LeTi_R'.
      - left. apply Pos; [apply Pos|]; auto.
      - unfold d. rewrite maxfx, maxfx.
        rewrite (Pr_max1 (d1(|h|))), Pr_max1'. apply Pr_max2. }
    eapply Theorem173; eauto. apply LeTi_R. 
    + left; apply H0; auto.
    + rewrite Theorem199. apply LeTi_R1; [|red; auto]. apply Pos; auto.
Qed.

Definition fu_seg f i n x1 x2 :=
  match i with 
  | 1 => f(x1+(RdiN (x2-x1) n)) - f x1
  | p` => f(x1+(RdiN ((x2-x1)·p`) n)) - f(x1+(RdiN ((x2-x1)·p) n))
  end.

Definition sum_fseg f i n x1 x2 := Cum (λ i, fu_seg f i n x1 x2) i.

Fact fseg0 : ∀ f n x1 x2 m, 
  Cum (λ i, fu_seg f i n x1 x2) m = sum_fseg f m n x1 x2.
Proof.
  intros; auto.
Qed.

Fact fseg1 : ∀ f u v i n, fu_seg f i n u v = 
  f(u+(RdiN ((v-u)· i) n)) - f(u+(RdiN ((v-u)· (i-1)) n)).
Proof.
  intros. induction i; unfold fu_seg; Simpl_R.
Qed.

Fact fseg2 : ∀ f u v i n,
  sum_fseg f i n u v = f(u+(RdiN ((v-u)·i) n)) - f u.
Proof.
  intros; unfold sum_fseg. induction i; simpl; Simpl_R.
  rewrite IHi, Theorem175, Mi_R, Theorem175, <- Mi_R. Simpl_R.
Qed.

Fact fseg3 : ∀ f u v n, sum_fseg f n n u v = f v - f u.
Proof.
  intros. rewrite fseg2. unfold RdiN. Simpl_R.
Qed.

Lemma rdnle1 : ∀ {i n z}, ILE_N i n -> z > O -> 
  O ≦ RdiN (z·(i-1)) n /\ RdiN (z·(i-1)) n ≦ z.
Proof.
  split; intros; red; destruct i; Simpl_R; left.
  - apply RdN1. apply Pos; simpl; auto.
  - unfold RdiN. apply (Theorem203_1' _ _ n); Simpl_R.
    2: reflexivity. rewrite Theorem194, (Theorem194 _ i).
    apply Theorem203_1; auto. pose proof (Nlt_S_ i).
    apply OrderNRlt. eapply Theorem16; eauto.
Qed.

Lemma rdnle2 : ∀ {i n z}, ILE_N i n -> z > O -> 
  O ≦ RdiN (z·i) n /\ RdiN (z·i) n ≦ z.
Proof.
  split; intros.
  - left; apply RdN1; apply Pos; simpl; auto.
  - unfold RdiN. apply (LeTi_R2 _ _ n); Simpl_R; [reflexivity|].
    apply LeTi_R1'; auto. apply OrderNRle; auto.
Qed.

Fact rdnin : ∀ {i n u v a b}, 
  u ∈ [a|b] -> v ∈ [a|b] -> v > u -> ILE_N i n -> 
  (u+(RdiN (((v-u)·(i-1))) n)) ∈ [a|b] /\ (u+(RdiN (((v-u)·i)) n)) ∈ [a|b].
Proof.
  intros; destruct H, H, H0, H0.
  apply Theorem182_1' in H1. repeat split.
  - eapply Theorem173; try apply H. apply LeRp1, rdnle1; auto.
  - eapply Theorem173; try apply H4. apply LeRp2, rdnle1; auto.
  - eapply Theorem173; try apply H. apply LeRp1, rdnle2; auto.
  - eapply Theorem173; try apply H4. apply LeRp2, rdnle2; auto.
Qed.

Fact derpos_inc : ∀ {F f a b}, uni_derivative F f a b -> 
  (∀ x, x ∈ [a|b] -> f(x) ≧ O) -> fun_inc F [a|b].
Proof.
  intros; red; intros. destruct H as [d [H [H4 [M [H5]]]]].
  destruct (Co_T167 (F x) (F y)); auto. apply Theorem182_3' in H7. 
  set (u:=y - x) in *. set (V:=F y - F x) in *.
  assert(∀ n, ∃ i, (ILE_N i n) /\ 
    F(x+u·(RdiN i n))-F(x+u·(RdiN (i-1) n))≦(RdiN V n)).
  { intros. Absurd. pose proof (not_ex_and _ _ H8). clear H8. cbv beta in H9.
    set (f2:= λ i, fu_seg F i n x y); set (f1:= λ i:Nat, RdiN V n).
    assert (∀ i, (ILE_N i n) -> f1 i < f2 i).
    { intros. apply H9 in H8. do 2 rewrite RdN2 in H8.
      destruct (Co_T167 (f2 i) (f1 i)); auto. 
      unfold f1, f2 in H10. rewrite fseg1 in H10. tauto. }
    pose proof (cumlt n H8). unfold f1, f2 in H10.
    rewrite cumcon, fseg0, fseg3 in H10. unfold RdiN in H10; Simpl_Rin H10.
    apply OrdR1 in H10; tauto. }
  assert (|V| > O). { destruct V; inversion H7; auto. }
  destruct (H4 (M·((u/|V|) (uneqOP H9)))) as [r [H10 [H11]]].
  assert (r > O). { destruct H11; tauto. }
  destruct (Archimedes ((u/r) (uneqOP H13))) as [n H14].
  destruct (H8 n) as [i [H16]]. pose proof (Theorem182_1' _ _ H3) as G.
  assert (u·RdiN i n = u·RdiN (i-1)n + u·RdiN 1 n).
  { rewrite <- Theorem201. unfold RdiN. rewrite Di_Rp; Simpl_R. }
  assert (|RdiN V n| ≦ |F(x+u·RdiN (i-1)n + u·RdiN 1 n) 
    - F(x+u·RdiN (i-1)n) - f(x+u·RdiN (i-1)n)·(u·RdiN 1 n)|).
  { rewrite Theorem186, <- H17.
    assert (RdiN V n < O). 
    { unfold RdiN.  apply (Theorem203_1' _ _ n); Simpl_R. reflexivity. }
    assert (F(x+u·RdiN i n) - F(x+u·RdiN (i-1)n) < O).
    { eapply Theorem172; eauto. }
    assert (O ≦ f(x+u·RdiN (i-1)n)).
    { rewrite RdN2. apply Theorem168, H0, (rdnin H1 H2 H3 H16). }
    assert (O ≦ (u·RdiN 1 n)). 
    { rewrite RdN2. left. apply RdN1; Simpl_R. }
    pose proof (Rle3 _ _ H20 H21). rewrite Abope1;[|red|]; auto.
    rewrite <- (Theorem175' (|RdiN V n|)).
    apply Theorem191'; [|apply Theorem170'].
    repeat rewrite Ab3''; auto. apply -> LEminus; auto. }
  assert (|F(x+u·RdiN (i-1)n + u·RdiN 1 n) 
    - F(x+u·RdiN (i-1)n) - f(x+u·RdiN (i-1)n)·(u·RdiN 1 n)| 
     ≦ M·|(u·RdiN 1 n)|·d(|(u·RdiN 1 n)|)).
  { destruct (rdnin H1 H2 H3 H16). apply H6; repeat rewrite RdN2; auto.
    rewrite Theorem186, RdN3, <- Theorem201; Simpl_R. }
  eapply Theorem173 in H19; eauto.
  assert (M·|(u·RdiN 1 n)|·d(|(u·RdiN 1 n)|) ≦ M·|(u·RdiN 1 n)|·d(r)).
  { assert (RdiN u n > O). { apply RdN1; auto. }
    repeat rewrite RdN2; Simpl_R; apply LeTi_R1'.
    - apply Pos; auto; Simpl_R. rewrite Ab3; auto.
    - apply H; auto.
      + rewrite Ab3; auto. apply (ocisub y x); auto. apply ociDi; auto.
      + rewrite Ab3; [|apply RdN1; auto].
        apply Theorem203_1 with (Θ:=r) in H14; Simpl_Rin H14. 
        rewrite Theorem194 in H14. unfold RdiN.
        apply Theorem203_1' with (Θ:=n); Simpl_R. reflexivity. }
  eapply Theorem173 in H20; eauto.
  assert (|V| ≦ M·|u|· d r).
  { rewrite RdN2 in H20; Simpl_Rin H20.
    apply (LeTi_R1 _ _ (|n|)) in H20; [| rewrite Ab3; reflexivity].
    rewrite Theorem199, (Theorem194 (d r)), <-Theorem199 in H20.
    rewrite (Theorem199 M), <- Theorem193, <- Theorem193 in H20.
    unfold RdiN in H20. Simpl_Rin H20. }
  apply Theorem203_1 with (Θ:=|V|) in H12; auto. destruct H.
  rewrite Theorem199, <- Theorem193 in H12. Simpl_Rin H12.
  apply Theorem203_1 with (Θ:=d r) in H12; auto.
  pattern (d r) at 2 in H12. rewrite <- Ab3 in H12; auto.
  rewrite <- Theorem193, Theorem194, <- Theorem199 in H12.
  Simpl_Rin H12. rewrite (Ab3 u) in H21; auto. LEGR H21 H12.
Qed.

Fact derneg_dec : ∀ {F f a b}, uni_derivative F f a b -> 
  (∀ x, x ∈ [a|b] -> f(x) ≦ O) -> fun_dec F [a|b].
Proof.
  intros. apply derfmi in H. rewrite (mmFun F). apply inde.
  eapply derpos_inc; eauto; intros.
  unfold minus_fun. apply Theorem168', LEminus; Simpl_R.
Qed.

Fact derpos_sinc : ∀ {F f a b}, uni_derivative F f a b -> 
  (∀ x, x ∈ [a|b] -> f(x) > O) -> fun_sinc F [a|b].
Proof.
  intros; red; intros. pose proof H. 
  apply derpos_inc in H4; [| intros; red; auto ].
  destruct (H4 _ _ H1 H2 H3); auto.
  assert (∀ u, u ∈ [x | y] -> F x = F u).
  { intros. inversion H6. destruct H7.
    pose proof (ccil H6). pose proof (ccir H6). apply OrdR5.
    - eapply Co_inc; eauto. apply (ccisub x y); auto.
    - rewrite H5. eapply Co_inc; eauto. apply (ccisub x y); auto. }
  assert (uni_derivative F (Φ(O)) x y).
  { apply (derF (derC (F x) H3)); intros; auto. }
  pose proof (dersub H1 H2 H3 H). pose proof (unider H7 H8).
  assert (x ∈ [x | y]). { split; split; red; auto. }
  pose proof (ccisub x y H1 H2 H10).
  apply H9 in H10. apply H0 in H11. ELR H10 H11.
Qed.

Fact derneg_sdec : ∀ {F f a b}, uni_derivative F f a b -> 
  (∀ x, x ∈ [a|b] -> f(x) < O) -> fun_sdec F [a|b].
Proof.
  intros. apply derfmi in H. rewrite (mmFun F). apply insde.
  eapply derpos_sinc; eauto; intros. unfold minus_fun.
  apply Theorem183_1'; Simpl_R. apply H0; auto.
Qed.

Corollary derFC : ∀ {F a b}, uni_derivative F (Φ(O)) a b ->
  ∀ {x y}, x ∈ [a|b] -> y ∈ [a|b] -> F x = F y.
Proof.
  intros. pose proof H. eapply derpos_inc in H; [|intros; red; auto].
  eapply derneg_dec in H2; [|intros; red; auto].
  destruct (Theorem167 x y); [subst x; auto|].
  destruct H3; apply OrdR5; auto.
Qed.

Corollary derF2MiC : ∀ {F1 F2 f a b}, 
  uni_derivative F1 f a b -> uni_derivative F2 f a b -> 
  ∀ {x y}, x ∈ [a|b] -> y ∈ [a|b] -> F1# x y = F2# x y.
Proof.
  intros. pose proof (derFMi H H0). unfold Minus_Fun in H3.
  apply (@derf _ _ (Φ(O))) in H3; [|intros; Simpl_R].
  pose proof (derFC H3 H2 H1). apply Theorem182_2' in H4.
  unfold input2Mi. apply Theorem182_2. rewrite Mi_R'; auto.
Qed.

Corollary derVle : ∀ {F G f g a b}, uni_derivative F f a b ->
  uni_derivative G g a b -> F a = G a ->
  (∀ x, x ∈ [a|b] -> f x ≦ g x) -> ∀ x, x ∈ [a|b] -> F x ≦ G x.
Proof.
  intros. pose proof (derFMi H H0).
  assert (∀x, x ∈ [a|b] -> (Minus_Fun f g) x ≦ O).
  { intros. unfold Minus_Fun. apply LePl_R with (z:=g x0); Simpl_R. }
  pose proof (derneg_dec H4 H5). inversion H3.
  destruct H7, H7; [|subst x; red; auto].
  apply Theorem182_1' in H7. pose proof (ccil H3).
  pose proof (H6 a x H9 H3 (Theorem182_1 _ _ H7)).
  unfold Minus_Fun in H10. rewrite H1 in H10. Simpl_Rin H10.
  apply LePl_R with (z:=G x) in H10; Simpl_Rin H10.
Qed.

Theorem derVTpre :∀ {F f a b},
  uni_derivative F f a b -> ∃ u, u ∈ [a|b] /\ F(b) - F(a) ≦ (f u)·(b-a).
Proof.
  intros. Absurd. pose proof (not_ex_and _ _ H0). simpl in H1.
  assert (∀ x, x ∈ [a|b] -> f x · (b-a) < F b - F a).
  { intros. apply H1 in H2.
    destruct (Co_T167 (F(b)-F(a)) (f(x)·(b-a))); tauto. }
  clear H0 H1. rename H2 into H0. pose proof (der_lt H).
  set (G:=λ x, (F b-F a)·x - F(x)·(b-a)). set (g:=λ x, (F b-F a) - f(x)·(b-a)).
  assert (uni_derivative G g a b).
  { apply derFMi; [apply derCx; auto|].
    pose proof (derfMu (b-a) H); unfold mult_fun in H2.
    apply (derFf H2); intros; apply Theorem194. }
  assert (∀ x, x ∈ [a|b] -> g(x) > O).
  { intros. apply Theorem182_1', H0; auto. }
  assert (G a = G b). 
  { unfold G. repeat rewrite Theorem202, Theorem202'.
    rewrite Mi_R'. Simpl_R. rewrite Mi_R'. Simpl_R. now rewrite Theorem181. }
  pose proof (derpos_sinc H2 H3).
  assert (a ∈ [a|b]). { split; split; red; auto. } pose proof (ccir H6).
  apply H5 in H1; auto. ELR H4 H1.
Qed.

Theorem derValT :∀ {F f a b},
  uni_derivative F f a b -> ∃ u v, u ∈ [a|b] /\ v ∈ [a|b] /\
  f(u)·(b-a) ≦ F(b) - F(a) /\ F(b) - F(a) ≦ f(v)·(b-a).
Proof.
  intros. destruct (derVTpre H) as [v [H0]], (derVTpre (derfmi H)) as [u [H2]].
  apply LEminus in H3. unfold minus_fun, Minus_R in H3.
  rewrite Theorem180, Theorem197' in H3. Simpl_Rin H3. exists u, v; auto.
Qed.

Theorem Med_der : ∀ {F f a b}, uni_derivative F f a b 
  <-> diff_quo_median F f a b /\ uniform_continuous f a b.
Proof.
  repeat split; red; intros.
  - assert (uni_derivative F f u v). 
    { eapply dersub; eauto. now apply Theorem182_1. }
    destruct (derValT H2) as [p [q]], H3, H4, H5.
    exists p, q; try repeat apply conj; auto;
    apply LeTi_R2 with (z:=(v-u)); Simpl_R.
  - eapply ucderf; eauto.
  - destruct H, H0 as [d [H0 [H1]]].
    exists d; split; auto. split; auto.
    exists 1; split; intros; try reflexivity; Simpl_R.
    assert (∀u v z, u ∈ [a|b] -> (u+v) ∈ [a|b] -> z ∈ [u|u+v] -> 
      v > O -> |F(u+v)-F(u)-f(z)·v| ≦ |v|·d(|v|)).
    { intros. assert (u+v-u > O). { Simpl_R. }
      destruct (H _  _ H9) as [p [q [H10 [H11 [H12]]]]]; auto.
      apply LePl_R with (z:=-f(z)) in H12; Simpl_Rin H12.
      apply LePl_R with (z:=-f(z)) in H13; Simpl_Rin H13.
      pose proof (R2AMge (conj H12 H13)). 
      assert (v ∈ (O|b-a]) as G.
      { apply (ocisub (u+v) u); Simpl_R. split; split; red; auto. }
      assert (∀j, j ∈ [u|u+v] -> |f j - f z|≦ d(v)).
      { intros. destruct H0, (classic (j=z)).
        - subst j; Simpl_R. left. apply H0; auto.
        - pose proof (ccile1 H7 H15). Simpl_Rin H18.
          eapply ccisub in H7; eapply ccisub in H15; eauto.
          rewrite <- (RMi1' _ z) in H15. pose proof (H2 _ _ H7 H15).
          Simpl_Rin H19. eapply Theorem173; eauto.
          apply (@Co_inc d ((O|b-a])); auto. eapply ociabs; eauto.
          intro. apply H17, Theorem182_2; auto. }
      assert (R2max (|f p-f z|) (|f q-f z|) ≦ d(v)). { apply R2Mle; auto. }
      eapply Theorem173 in H16; eauto.
      apply LeTi_R1 with (z:=u+v-u) in H16; auto.
      pattern (u+v-u) at 3 in H16. rewrite <- Ab3 in H16; auto.
      rewrite <- Theorem193, Theorem202' in H16; Simpl_Rin H16.
      rewrite (Ab3 v), (Theorem194 v); auto. }
    destruct (Theorem167 h O) as [H6|[H6|H6]].
    + subst h; Simpl_R; red; auto.
    + apply Theorem176_3 in H6; pose proof (ccir' x _ H6).
      pattern x at 3 in H7. rewrite <- (RMi2 _ h) in H7.
      eapply H5 in H7; eauto; Simpl_R. Simpl_Rin H7.
      rewrite <- Theorem178, <- (Theorem178 h). unfold Minus_R.
      rewrite Theorem180, <- Theorem197''. Simpl_R. now rewrite Theorem181.
    + apply H5; auto. apply ccil'; auto.
Qed.

Corollary derconc : ∀ {F f a b}, uni_derivative F f a b -> 
  fun_inc f [a|b] -> convexdown F [a|b].
Proof.
  intros. apply Med_der in H. destruct H. eapply medconc; eauto.
Qed.

Corollary derconv : ∀ {F f a b}, uni_derivative F f a b -> 
  fun_dec f [a|b] -> convexup F [a|b].
Proof.
  intros. apply Med_der in H. destruct H. eapply medconv; eauto.
Qed.
