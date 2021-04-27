(***************************************************************************)
(*   This is part of FA_3rdCalculus, it is distributed under the terms     *)
(*         of the GNU Lesser General Public License version 3              *)
(*                (see file LICENSE for more details)                      *)
(*                                                                         *)
(*            Copyright 2020-2022: Yaoshun Fu and Wensheng Yu.             *)
(***************************************************************************)

Require Export UnD.

Definition str_derivative F f a b := ∃ M, O < M /\ 
  ∀ x h, x ∈ [a|b] -> (x+h) ∈ [a|b] -> |F(x+h) - F(x) - f(x)·h| ≦ M·h^2.

Corollary Co_std : ∀ {F f M a b}, 
  (∀ x h, x ∈ [a|b] -> (x+h) ∈ [a|b] -> |F(x+h) - F(x) - f(x)·h| ≦ M·h^2) -> 
  ∀ {p q}, p ∈ [a|b] -> q ∈ [a|b] -> |F(q) - F(p) - f(p)·(q-p)| ≦ M·(q-p)^2.
Proof.
  intros. pattern q at 1; rewrite <- (RMi1' _ p). apply H; Simpl_R.
Qed.

Definition str_derivability F a b := ∃ f, str_derivative F f a b.

Fact std_le : ∀ {F f a b}, b ≦ a -> str_derivative F f a b.
Proof.
  intros. exists 1; split; intros;[reflexivity|].
  pose proof H0. destruct H0, H0.
  eapply Theorem173 in H3; eauto. LEGER H H3. subst b.
  destruct H1, H1, H2, H2. LEGER H0 H5. LEGER H1 H4. subst a.
  rewrite <- H7. apply (Theorem188_2' _ _ (-x)) in H7. Simpl_Rin H7.
  subst h. Simpl_R. apply square_p1.
Qed.

Fact std_lt : ∀ {F f a b}, (a < b -> str_derivative F f a b) -> 
  str_derivative F f a b.
Proof.
  intros. destruct (Co_T167 b a); auto. apply std_le; auto.
Qed.

Fact stdsub : ∀ {F f u v a b}, u ∈ [a|b] -> v ∈ [a|b] -> 
  str_derivative F f a b -> str_derivative F f u v.
Proof.
  intros. destruct H1 as [M [H1]].
  exists M; split; intros; auto. apply H2; apply (ccisub u v); auto.
Qed.

Fact std_imply_der : ∀ {F f a b},
  a < b -> str_derivative F f a b -> uni_derivative F f a b.
Proof.
  intros; red; intros. destruct H0 as [M [H0]].
  exists Δ; split; [apply fpcp1 |split]; [apply ubrp1; auto|].
  exists M; split; auto; intros. rewrite Theorem199, absqu; auto.
Qed. 

Fact stdf : ∀ {F f1 f2 a b}, str_derivative F f1 a b ->
  (∀ x, x ∈ [a|b] -> f1 x = f2 x) -> str_derivative F f2 a b.
Proof.
  intros. destruct H as [M [H]].
  exists M; split; auto; intros. rewrite <- H0; auto.
Qed.

Fact stdF : ∀ {F1 F2 f a b}, str_derivative F1 f a b ->
  (∀ x, x ∈ [a|b] -> F1 x = F2 x) -> str_derivative F2 f a b.
Proof.
  intros. destruct H as [M [H]].
  exists M; split; auto; intros. repeat rewrite <- H0; auto.
Qed.

Fact stdFf : ∀ {F1 F2 f1 f2 a b}, 
  str_derivative F1 f1 a b -> (∀ x, x ∈ [a|b] -> F1 x = F2 x) -> 
  (∀ x, x ∈ [a|b] -> f1 x = f2 x) -> str_derivative F2 f2 a b.
Proof.
  intros. eapply stdF in H; eauto. eapply stdf in H; eauto.
Qed.

Fact lipstdf : ∀ {F f a b}, str_derivative F f a b -> Lipschitz f a b.
Proof.
  intros. destruct H as [M [H]]. exists (2·M); split; intros.
  - apply Pos; simpl; auto.
  - destruct (classic (h = O)).
    + subst h; Simpl_R; simpl; red; auto.
    + assert ((x+h+(-h)) ∈ [a|b]). { Simpl_R. }
      generalize (H0 _ _ H1 H2) (H0 _ _ H2 H4); intros; Simpl_Rin H6.
      rewrite square_p3, <- Theorem178 in H6. unfold Minus_R in H6 at 1.
      rewrite <- Theorem197'' in H6. Simpl_Rin H6.
      rewrite Theorem180, Theorem181 in H6. Simpl_Rin H6.
      pose proof (Rle4 H6 H5). Simpl_Rin H7. rewrite Theorem178 in H7.
      apply Ab8 in H3. apply LeTi_R2 with (z:=|h|); auto.
      rewrite <- Theorem193, Theorem202', Theorem199, Theorem199.
      rewrite R_T2, absqu; auto.
Qed.

Fact boundstdf : ∀ {F f a b}, str_derivative F f a b -> bound_ran f a b.
Proof.
  intros. exact (lipbound (lipstdf H)).
Qed.

Fact lipstdF : ∀ {F f a b}, str_derivative F f a b -> Lipschitz F a b.
Proof.
  intros. destruct (boundstdf H) as [A [H0]], H as [M [H]].
  assert (M·|b-a|+A > O).
  { destruct M, (b-a), A; simpl; auto; inversion H; inversion H0. }
  exists (M·|b-a|+A). split; auto; intros. pose proof (H2 _ _ H4 H5).
  eapply Theorem173 in H6; try apply Ab2'.
  apply LePl_R with (z:=|f x · h|) in H6; Simpl_Rin H6.
  rewrite <- absqu, Theorem193, <- Theorem199, <- Theorem201' in H6.
  eapply Theorem173; eauto. apply LeTi_R; [apply Theorem170'|].
  apply Theorem191'; [| left; auto]. apply LeTi_R1'; auto.
  pose proof (ccile1 H4 H5); Simpl_Rin H7.
  eapply Theorem173; eauto; apply Ab7.
Qed.

Fact boundstdF : ∀ {F f a b}, str_derivative F f a b -> bound_ran F a b.
Proof.
  intros. exact (lipbound (lipstdF H)).
Qed.

Fact stdC : ∀ {a b} C, str_derivative (Φ(C)) (Φ(O)) a b.
Proof.
  intros. exists 1; split; [reflexivity|intros]. Simpl_R. apply square_p1.
Qed.

Fact stdCx : ∀ {a b} C, str_derivative (λ x, C·x) (Φ(C)) a b.
Proof.
  intros. exists 1; split; [reflexivity|intros].
  rewrite <- Theorem202. Simpl_R. apply square_p1.
Qed.

Fact stdfMu : ∀ {a b F f} c, str_derivative F f a b -> 
  str_derivative (mult_fun c F) (mult_fun c f) a b.
Proof.
  intros. destruct H as [M [H]].
  destruct (classic (c=O)) as [H1 | H1]; unfold mult_fun.
  - exists M. split; auto; intros. subst c; Simpl_R.
    apply Rle3; [red; auto|apply square_p1].
  - exists (|c|·M). split; intros.
    + apply Pos; auto. apply Ab8; auto.
    + pose proof (H0 _ _ H2 H3). rewrite Theorem199, <- Theorem202.
      rewrite <- Theorem202, Theorem193, Theorem199.
      apply LeTi_R'; auto. apply Theorem170'.
Qed.

Fact stdf_mi : ∀ {F f a b}, str_derivative F f a b ->
  str_derivative (λ x, F(-x)) (λ x, -f(-x)) (-b) (-a).
Proof.
  intros. destruct H as [M [H]].
  exists M; split; intros; auto.
  apply ccimi in H1. Simpl_Rin H1. apply ccimi in H2. Simpl_Rin H2.
  rewrite Theorem180 in H2. pose proof (H0 _ _ H1 H2). Simpl_R.
  rewrite Theorem180, Theorem197, <- square_p3. auto.
Qed.

Fact stdf_cd : ∀ {F f a b} c d l, str_derivative F f a b -> 
  str_derivative (multfun_pl F c d) 
  (mult_fun c (multfun_pl f c d))(((a-d)/c) (uneqOP l))(((b-d)/c) (uneqOP l)).
Proof.
  intros. destruct H as [M [H]].
  exists (c^2·M); split; intros.
  - apply Pos; auto. apply Pos; auto.
  - apply cciMu, cciMi in H1; apply cciMu, cciMi in H2; auto.
    pose proof (Co_std H0 H1 H2).
    assert (c·(x+h) + d - (c·x + d) = c·h).
    { rewrite Theorem201. rewrite <- Mi_R. Simpl_R. }
    rewrite H4 in H3. unfold multfun_pl, mult_fun.
    rewrite (Theorem194 _ (f(c·x+d))), Theorem199.
    rewrite (Theorem194 _ M), Theorem199, powT; auto. 
Qed.

Fact stdfmi : ∀ {F f a b}, str_derivative F f a b -> 
  str_derivative (minus_fun F) (minus_fun f) a b.
Proof.
  intros. pose proof (stdfMu (-(1)) H). do 2 rewrite <- mFun; auto.
Qed.

Fact stdFPl : ∀ {F G f g a b},
  str_derivative F f a b -> str_derivative G g a b -> 
  str_derivative (Plus_Fun F G) (Plus_Fun f g) a b.
Proof.
  intros. destruct H as [M1 [H]], H0 as [M2 [H0]].
  exists (M1 + M2); split; intros.
  - destruct M1, M2; simpl; auto; inversion H; inversion H0.
  - pose proof (Theorem191' (H1 _ _ H3 H4) (H2 _ _ H3 H4)).
    eapply Theorem173 in H5; try apply Ab2; eauto.
    rewrite Mi_R, <- Theorem201', Mi_R, <- Theorem201' in H5; auto.
Qed.

Fact stdFMi : ∀ {F G f g a b}, str_derivative F f a b -> 
  str_derivative G g a b -> str_derivative (Minus_Fun F G) (Minus_Fun f g) a b.
Proof.
  intros. exact (stdFPl H (stdfmi H0)).
Qed.

Fact stdFMu : ∀ {F G f g a b}, 
  str_derivative F f a b -> str_derivative G g a b -> 
  str_derivative (Mult_Fun F G) (λ x, (f x)·(G x) + (F x)·(g x)) a b.
Proof.
  intros. destruct (lipstdF H) as [M1 [H1]], (lipstdF H0) as [M2 [H3]], 
    (boundstdF H) as [A1 [H5]], (boundstdF H0) as [A2 [H7]].
  destruct H as [M3 [H]], H0 as [M4 [H0]].
  assert (M1·M2 + A2·M3 + A1·M4 > O).
  { generalize (Pos _ _ H1 H3) (Pos _ _ H7 H) (Pos _ _ H5 H0); intros.
    pose proof (Theorem189 (Theorem189 H11 H12) H13). Simpl_Rin H14. }
  exists (M1·M2 + A2·M3 + A1·M4); split; auto; intros.
  generalize (H9 _ _ H12 H13) (H10 _ _ H12 H13) 
    (H2 _ _ H12 H13) (H4 _ _ H12 H13); intros.
  apply LeTi_R' with (z:=|G x|) in H14; [|apply Theorem170'].
  apply LeTi_R' with (z:=|F x|) in H15; [|apply Theorem170'].
  apply (LeTi_R3 (|G(x+h) - G x|) (M2·|h|)) in H16; auto.
  2:apply Theorem170'. 2: apply Rle3; red; auto; apply Theorem170'.
  rewrite <- Theorem193, Theorem199, (Theorem194 (|h|)) in H16.
  do 2 rewrite <- Theorem199 in H16. clear H17.
  rewrite <- Theorem199, <- Theorem193 in H14, H15.
  rewrite (Theorem199 _ (|h|)), absqu in H16.
  pose proof (Theorem191' H14 H15). eapply Theorem173 in H17; try apply Ab2.
  pose proof (Theorem191' H16 H17). eapply Theorem173 in H18; try apply Ab2.
  rewrite <- Theorem186, dMupre in H18. repeat rewrite <- Theorem201' in H18.
  unfold Mult_Fun. eapply Theorem173; eauto.
  apply LeTi_R; [simpl; apply square_p1|].
  rewrite Theorem186. rewrite Theorem175,(Theorem175 (M1·M2)).
  apply LePl_R, Theorem191'; apply LeTi_R1; auto; left; auto.
Qed.

Corollary unistd : ∀ {F f1 f2 a b}, a < b -> str_derivative F f1 a b -> 
  str_derivative F f2 a b -> ∀x, x ∈ [a|b] -> f1 x = f2 x.
Proof.
  intros. eapply unider; eauto; eapply std_imply_der; eauto.
Qed.

Corollary stdpos_inc : ∀ {F f a b}, str_derivative F f a b -> 
  (∀ x, x ∈ [a|b] -> f(x) ≧ O) -> fun_inc F [a|b].
Proof.
  intros; red; intros. eapply derpos_inc; eauto.
  apply std_imply_der; auto. exact (ccilt H1 H2 H3).
Qed.

Corollary stdneg_dec : ∀ {F f a b}, str_derivative F f a b -> 
  (∀ x, x ∈ [a|b] -> f(x) ≦ O) -> fun_dec F [a|b].
Proof.
  intros; red; intros. eapply derneg_dec; eauto.
  apply std_imply_der; auto. exact (ccilt H1 H2 H3).
Qed.

Corollary stdpos_sinc : ∀ {F f a b}, str_derivative F f a b -> 
  (∀ x, x ∈ [a|b] -> f(x) > O) -> fun_sinc F [a|b].
Proof.
  intros; red; intros. eapply derpos_sinc; eauto.
  apply std_imply_der; auto. exact (ccilt H1 H2 H3).
Qed.

Corollary stdneg_sdec : ∀ {F f a b}, str_derivative F f a b -> 
  (∀ x, x ∈ [a|b] -> f(x) < O) -> fun_sdec F [a|b].
Proof.
  intros; red; intros. eapply derneg_sdec; eauto.
  apply std_imply_der; auto. eexact (ccilt H1 H2 H3).
Qed.

Corollary stdconc : ∀ {F f a b}, 
  str_derivative F f a b -> fun_inc f [a|b] -> convexdown F [a|b].
Proof.
  intros. destruct (Co_T167 b a).
  - red; intros. cut (a=b); intros.
    + subst a. destruct H2, H2, H3, H3. LEGER H2 H6. LEGER H3 H7.
      subst b x1. do 2 rewrite <- Theorem201'. red; Simpl_R.
    + destruct H2, H2. eapply Theorem173 in H6; eauto. apply OrdR5; auto.
  - apply std_imply_der in H; auto. eapply derconc; eauto.
Qed.

Corollary stdconv : ∀ {F f a b}, 
  str_derivative F f a b -> fun_dec f [a|b] -> convexup F [a|b].
Proof.
  intros. destruct (Co_T167 b a).
  - red; intros. cut (a=b); intros.
    + subst a. destruct H2, H2, H3, H3. LEGER H2 H6. LEGER H3 H7.
      subst b x1. do 2 rewrite <- Theorem201'. red; Simpl_R.
    + destruct H2, H2. eapply Theorem173 in H6; eauto. apply OrdR5; auto.
  - apply std_imply_der in H; auto. eapply derconv; eauto.
Qed.

Lemma mstdpre :  ∀ {f M} a b p q, 
  (∀ x h, x ∈ [a|b] -> (x+h) ∈ [a|b] -> |f(x+h) - f(x)| ≦ M·|h|) -> 
  p ∈ [a|b] -> q ∈ [a|b] -> (∀ u v, u ∈ [p|q] -> 
  v ∈ [p|q] -> |f(v) - f(u)| ≦ M · |v-u|).
Proof.
  intros. pattern v at 1 in H3; rewrite <- (RMi1' v u) in H3.
  eapply (ccisub p q) in H2; eapply (ccisub p q) in H3; eauto.
  pose proof (H _ _ H2 H3). Simpl_Rin H4.
Qed.

Theorem Med_std : ∀ {F f a b}, str_derivative F f a b <->
  diff_quo_median F f a b /\ Lipschitz f a b.
Proof.
  repeat split; intros.
  - red; intros. pose proof (Theorem182_1 _ _ l). eapply ccilt in H2; eauto.
    eapply Med_der; eauto. apply std_imply_der; auto.
  - eapply lipstdf; eauto.
  - destruct H, H0 as [M [H0]].
    exists M; split; intros; auto.
    destruct (Theorem167 O h) as [H5 | [H5 | H5]].
    + subst h; Simpl_R; simpl; red; auto.
    + assert (x+h-x > O). { Simpl_R. }
      destruct (H _  _ H4) as [p [q [H6 [H7 [H8]]]]]; auto.
      apply LePl_R with (z:=-f(x)) in H8; Simpl_Rin H8.
      apply LePl_R with (z:=-f(x)) in H9; Simpl_Rin H9.
      pose proof (R2Mge (conj H8 H9)).
      assert (R2max (|f p - f x|) (|f q - f x|) ≦ M·h).
      { apply R2Mle.
        - assert (|p-x| ≦ h). { apply ccile2; auto. }
          apply LeTi_R1' with (z:=M) in H11; auto.
          eapply Theorem173; eauto.
          apply (mstdpre a b x (x+h)); auto. apply ccil'; auto.
        - assert (|q-x| ≦ h). { apply ccile2; auto. }
          apply LeTi_R1' with (z:=M) in H11; auto.
          eapply Theorem173; eauto.
          apply (mstdpre a b x (x+h)); auto. apply ccil'; auto. }
      eapply Theorem173 in H11; eauto.
      apply LeTi_R1 with (z:=(x+h-x)) in H11; auto.
      pattern (x+h-x) at 3 in H11. rewrite <- Ab3 in H11; auto.
      rewrite <- Theorem193, Theorem202' in H11; Simpl_Rin H11.
      rewrite Theorem199 in H11; auto.
    + assert ((x+h+(-h)) ∈ [a|b]). { Simpl_R. }
      apply Theorem176_3 in H5.
      assert (x+h+(-h) - (x+h) > O). { Simpl_R. }
      destruct (H _ _ H6 H3 H4) as [p [q [H7 [H8 [H9]]]]].
      apply LePl_R with (z:=-f(x)) in H9; Simpl_Rin H9.
      apply LePl_R with (z:=-f(x)) in H10; Simpl_Rin H10.
      pose proof (R2Mge (conj H9 H10)). Simpl_Rin H7. Simpl_Rin H8.
      assert (R2max (|f p - f x|) (|f q - f x|) ≦ M · |h|).
      { apply R2Mle.
        - assert (|p-x| ≦ |h|). { apply ccile3; auto. }
          apply LeTi_R1' with (z:=M) in H12; auto.
          eapply Theorem173; eauto.
          apply (mstdpre a b (x+h) x); auto. apply ccir'; auto.
        - assert (|q-x| ≦ |h|). { apply ccile3; auto. }
          apply LeTi_R1' with (z:=M) in H12; auto.
          eapply Theorem173; eauto.
          apply (mstdpre a b (x+h) x); auto. apply ccir'; auto. }
      eapply Theorem173 in H12; eauto.
      apply LeTi_R1 with (z:=(x + h + - h - (x + h))) in H12; auto.
      pattern (x+h+-h-(x+h)) at 3 in H12. rewrite <- Ab3 in H12; auto.
      rewrite <- Theorem193, Theorem202' in H12; Simpl_Rin H12.
      unfold Minus_R at 1. rewrite <- Theorem178, 
        Theorem180, Theorem181, <- Theorem197''; Simpl_R.
      pattern (-h) at 2 in H12; rewrite <- Ab3 in H12; auto. 
      rewrite Theorem178, Theorem199 in H12; auto.
      rewrite <- square_p2; auto.
Qed.

Theorem Meds_std : ∀ {F f a b}, str_derivative F f a b <->
  diff_quo_median F f a b /\ Lipschitz f a b.
Proof.
  repeat split; intros.
  - red; intros. pose proof (Theorem182_1 _ _ l). eapply ccilt in H2; eauto.
    eapply Med_der; eauto. apply std_imply_der; auto.
  - eapply lipstdf; eauto.
  - destruct H, H0 as [M [H0]]. exists M; split; intros; auto.
    assert (∀u v z, u ∈ [a|b] -> (u+v) ∈ [a|b] -> z ∈ [u|u+v] -> 
      v > O -> |F(u+v)-F(u)-f(z)·v| ≦ M·v^2).
    { intros. assert (u+v-u > O). { Simpl_R. }
      destruct (H _  _ H8) as [p [q [H9 [H10 [H11]]]]]; auto.
      apply LePl_R with (z:=-f(z)) in H11; Simpl_Rin H11.
      apply LePl_R with (z:=-f(z)) in H12; Simpl_Rin H12.
      pose proof (R2Mge (conj H11 H12)). 
      assert (v ∈ (O|b-a]) as G.
      { apply (ocisub (u+v) u); Simpl_R. split; split; red; auto. }
      assert (∀j, j ∈ [u|u+v] -> |f j - f z|≦ M·v).
      { intros. pose proof (ccile1 H6 H14). Simpl_Rin H15.
        apply LeTi_R1' with (z:=M) in H15; auto.
        eapply Theorem173; eauto. apply (mstdpre a b u (u+v)); auto. }
      assert (R2max (|f p-f z|) (|f q-f z|) ≦ M·v). { apply R2Mle; auto. }
      eapply Theorem173 in H15; eauto.
      apply LeTi_R1 with (z:=u+v-u) in H15; auto.
      pattern (u+v-u) at 3 in H15. rewrite <- Ab3 in H15; auto.
      rewrite <- Theorem193, Theorem202' in H15; Simpl_Rin H15.
      rewrite Theorem199 in H15; auto. }
    destruct (Theorem167 h O) as [H5|[H5|H5]].
    + subst h; Simpl_R; red; auto.
    + apply Theorem176_3 in H5; pose proof (ccir' x _ H5).
      pattern x at 3 in H6. rewrite <- (RMi2 _ h) in H6.
      eapply H4 in H6; eauto; Simpl_R. Simpl_Rin H6.
      rewrite <- square_p3, <- Theorem178. unfold Minus_R.
      rewrite Theorem180, <- Theorem197''. Simpl_R. now rewrite Theorem181.
    + apply H4; auto. apply ccil'; auto.
Qed.