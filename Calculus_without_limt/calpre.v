(***************************************************************************)
(*   This is part of FA_3rdCalculus, it is distributed under the terms     *)
(*         of the GNU Lesser General Public License version 3              *)
(*                (see file LICENSE for more details)                      *)
(*                                                                         *)
(*            Copyright 2020-2022: Yaoshun Fu and Wensheng Yu.             *)
(***************************************************************************)

Require Export R_sup1.

Definition Rfun := Real -> Real.

Definition input2Mi (F :Rfun) := λ u v, F(v) - F(u).
Notation "F #" := (input2Mi F)(at level 5).

Definition Δ :Rfun := λ x, x.

Definition Φ :Real -> Rfun := λ C, (λ _, C).

Definition maxfun (f g :Rfun) := 
  λ x, match (Rcase (f x)(g x)) with
        | left _ => g x
        | right _ => f x
       end.

Fact maxfx : ∀ f1 f2 x, maxfun f1 f2 x = R2max (f1 x) (f2 x).
Proof.
  intros. unfold maxfun. destruct Rcase.
  - rewrite Pr_max; auto.
  - rewrite Pr_max1, Pr_max; auto; red; auto.
Qed.

Definition mult_fun c (f :Rfun) := λ x, c·f(x).

Definition multfun_ (f :Rfun) c := λ x, f(c·x). 

Definition multfun_pl (f :Rfun) c d := λ x, f(c·x+d).

Definition minus_fun (f :Rfun) := λ x, - f(x).

Definition Plus_Fun (f g :Rfun) := λ x, f(x) + g(x).

Definition Minus_Fun (f g :Rfun) := λ x, f(x) - g(x).

Definition Mult_Fun (f g :Rfun) := λ x, f(x) · g(x).

Fact mFun : ∀ f, mult_fun (-(1)) f = minus_fun f.
Proof.
  intros; apply fun_ext; intros. unfold mult_fun, minus_fun; Simpl_R.
Qed.

Fact mmFun : ∀ f, f = minus_fun (minus_fun f).
Proof.
  intros. apply fun_ext; intros; unfold minus_fun; Simpl_R.
Qed.

Fact MFun : ∀ f g, Minus_Fun f g = Plus_Fun f (minus_fun g).
Proof.
  intros; unfold Minus_Fun, Plus_Fun, minus_fun; Simpl_R.
Qed.

Definition fun_inc f I := ∀ x y, x ∈ I -> y ∈ I -> x < y -> f x ≦ f y.

Definition fun_sinc f I := ∀ x y, x ∈ I -> y ∈ I -> x < y -> f x < f y.

Definition fun_dec f I := ∀ x y, x ∈ I -> y ∈ I -> x < y -> f y ≦ f x.

Definition fun_sdec f I := ∀ x y, x ∈ I -> y ∈ I -> x < y -> f x > f y.

Definition convexdown f I := ∀ x1 x2, x1 ∈ I -> x2 ∈ I -> 
  ∀ c, c > O -> c < 1 -> f(c·x1+(1-c)·x2) ≦ c·f(x1) + (1-c)·f(x2).

Definition convexup f I := ∀ x1 x2, x1 ∈ I -> x2 ∈ I -> 
  ∀ c, c > O -> c < 1 -> c·f(x1) + (1-c)·f(x2) ≦ f(c·x1+(1-c)·x2).

Fact inde : ∀ F a b, fun_inc F [a|b] <-> fun_dec (minus_fun F) [a|b].
Proof.
  split; intros; red; intros; unfold minus_fun.
  - apply LEminus; Simpl_R.
  - apply LEminus, H; auto.
Qed.

Fact insde : ∀ F a b, fun_sinc F [a|b] <-> fun_sdec (minus_fun F) [a|b].
Proof.
  split; intros; red; intros; unfold minus_fun.
  - apply Theorem183_1, H; auto.
  - apply Theorem183_1', H; auto.
Qed.

Definition fun_pinc f I := (∀ z, z ∈ I -> f z > O) /\ fun_inc f I.

Corollary Co_inc : ∀ {f I}, fun_inc f I -> 
  ∀{x y}, x ∈ I -> y ∈ I -> x ≦ y -> f x ≦ f y.
Proof.
  intros; destruct H2; auto. subst x; red; auto.
Qed.

Fact fpcp1 : ∀ a b, fun_pinc Δ (O|b-a].
Proof.
  split; red; intros. destruct H, H; auto. destruct H0, H0; red; auto.
Qed.

Fact fpcp2 : ∀ {d1 d2 I}, fun_pinc d1 I -> fun_pinc d2 I -> 
  fun_pinc (maxfun d1 d2) I.
Proof.
  split; intros; destruct H, H0; unfold maxfun.
  - destruct Rcase; auto. 
  - red; intros. destruct Rcase, Rcase; auto.
    + left. eapply Theorem172; eauto.
    + eapply Theorem173; eauto.
Qed.

Definition unbRecF (f :Rfun) I := ∀ M, ∃ z l, z ∈ I /\ M < |(1/(f z)) l|.

Fact ubrp1 : ∀ {a b}, a < b -> unbRecF Δ (O|b-a].
Proof.
  intros; red; intros. apply Theorem182_1' in H. destruct (Co_T167 M O).
  - exists (b-a). exists (uneqOP H); split.
    + split; split; red; auto.
    + eapply Theorem172; left; split; eauto. apply Ab8''. intro. inversion H1.
  - assert ((M+M) > O). { destruct M; simpl; auto. } set (l:=uneqOP H1).
    assert ((R2min (b-a) ((1/(M+M)) l)) > O).
    { apply R2mgt; auto. apply Pos'; simpl; auto. } set (l1:=uneqOP H2).
    exists (R2min (b-a) ((1/(M+M)) l)), l1; split.
    + split; split; auto. apply Pr_min2.
    + apply Rlt1. rewrite Ab3; auto.
      assert (M·((1/(M+M)) l) < 1).
      { rewrite Di_Rt; apply Theorem203_1' with (Θ:=M+M); Simpl_R.
        apply Pl_R; auto. }
      eapply Theorem172; left; split; eauto.
      apply LeTi_R1'; auto. apply Pr_min3.
Qed.

Fact ubrp2 : ∀ {d1 d2 I}, fun_pinc d1 I -> fun_pinc d2 I -> 
  unbRecF d1 I -> unbRecF d2 I -> unbRecF (maxfun d1 d2) I.
Proof.
  intros; red; intro. set (d:=maxfun d1 d2) in *.
  destruct (H1 M) as [z1 [l1 [H3]]], (H2 M) as [z2 [l2 [H5]]], H, H0.
  assert ((R2min z1 z2) ∈ I). { destruct (Pr_min4 z1 z2); rewrite H9; auto. }
  assert (d(R2min z1 z2) > O).
  { unfold d, maxfun. destruct Rcase, (Pr_min4 z1 z2); rewrite H10; auto. }
  exists (R2min z1 z2), (uneqOP H10). split; auto.
  destruct (Co_T167 M O).
  { eapply Theorem172; left; split; eauto. apply Ab8''. intro. inversion H12. }
  apply Rlt1 in H4. apply Rlt1 in H6. apply Rlt1.
  assert (M·|d1(R2min z1 z2)| < |1|).
  { eapply Theorem172; left; split; try apply H4. apply LeTi_R1'; auto.
    repeat rewrite Ab3; auto. eapply Co_inc; eauto. apply Pr_min2. }
  assert (M·|d2(R2min z1 z2)| < |1|).
  { eapply Theorem172; left; split; try apply H6. apply LeTi_R1'; auto.
    repeat rewrite Ab3; auto. eapply Co_inc; eauto. apply Pr_min3. }
  unfold d, maxfun; destruct Rcase; auto.
Qed.

Definition bound_ran f a b := ∃ A, A > O /\ ∀ x, x ∈ [a|b] -> |f x| < A.

Fact brp1 : ∀ {f d a b}, fun_pinc d (O|b-a] -> 
  (∀ x h, x ∈ [a|b] -> (x+h) ∈ [a|b] -> |f(x+h) - f(x)| ≦ d(|h|)) -> 
  bound_ran f a b.
Proof.
  intros. destruct H. assert (|f(a)|+1>O). { destruct (f a); simpl; auto. }
  destruct (Co_T167 b a).
  { exists (|f(a)|+1). split; auto; intros. destruct H4, H4.
    eapply Theorem173 in H3; eauto. LEGER H3 H4. subst x.
    apply Pl_R. reflexivity. } apply Theorem182_1' in H3.
  assert (|b-a| ∈ (O|b-a]). { rewrite Ab3; auto. split; split; red; auto. }
  pose proof (H _ H4). pose proof (Theorem189 H2 H5). Simpl_Rin H6.
  exists (|f a|+1+d(|b-a|)). split; auto; intros.
  pose proof (ccil H7). pose proof H7. destruct H9, H9, H9.
  - rewrite <- (RMi1' x a) in H7. pose proof (H0 _ _ H8 H7). Simpl_Rin H11.
    eapply Theorem173 in H11; try apply Ab2'.
    apply LePl_R with (z:=|f a|) in H11; Simpl_Rin H11.
    rewrite Theorem175, <- Theorem186. apply Theorem182_1' in H9.
    assert (d(|x-a|) + |f a| ≦ d(|b-a|) + |f a|).
    { apply LePl_R; auto. apply LePl_R with (z:=-a) in H10. Simpl_Rin H10.
      eapply Co_inc; eauto; rewrite Ab3; [| |rewrite Ab3|]; auto.
      split; split; auto. } eapply Theorem173 in H12; eauto.
    eapply Theorem172; left; split; eauto. apply Pl_R. reflexivity.
  - rewrite <- H9, Theorem186. apply Pl_R.
    rewrite <- (Theorem175' O). apply Theorem189; simpl; auto.
Qed.

Definition uniform_continuous f a b :=
  ∃ d, fun_pinc d (O|b-a] /\ unbRecF d (O|b-a] /\
  ∀ x h, x ∈ [a|b] -> (x+h) ∈ [a|b] -> |f(x+h) - f(x)| ≦ d(|h|).

Corollary Co_uc : ∀ {f d a b}, 
  (∀ x h, x ∈ [a|b] -> (x+h) ∈ [a|b] -> |f(x+h) - f x| ≦ d(|h|)) -> 
  ∀ {p q}, p ∈ [a|b] -> q ∈ [a|b] -> |f(q) - f(p)| ≦ d(|q-p|).
Proof.
  intros. pattern q at 1; rewrite <- (RMi1' _ p). apply H; Simpl_R.
Qed.

Fact uclt : ∀ {f a b}, uniform_continuous f a b -> a < b.
Proof.
  intros. destruct H as [d [_ [H _]]], (H 1), H0, H0, H0, H0.
  apply Theorem182_1. eapply Theorem172; eauto.
Qed.

Fact ucbound : ∀ {f a b}, uniform_continuous f a b -> bound_ran f a b.
Proof.
  intros. destruct H as [d [H [H1]]]. eapply brp1; eauto.
Qed.

Definition Lipschitz f a b := ∃ M, M > O /\ 
  ∀ x h, x ∈ [a|b] -> (x+h) ∈ [a|b] -> |f(x+h) - f(x)| ≦ M·|h|.

Fact lipbound : ∀ {f a b}, Lipschitz f a b -> bound_ran f a b.
Proof.
  intros. destruct H as [M [H]]. set (d:= λ x, M·x).
  apply @brp1 with (d:=d); auto. unfold d; split; try red; intros.
  - destruct H1, H1. apply Pos; auto.
  - destruct H1, H1, H2, H2. apply LeTi_R1'; red; auto.
Qed.

Fixpoint Cum f n :=
  match n with
    | 1 => f 1
    | p` => Cum f p + f p`
  end.

Fact cumlt : ∀ {f1 f2} n, 
  (∀ i, ILE_N i n -> f1 i < f2 i) -> Cum f1 n < Cum f2 n.
Proof.
  intros; revert H; induction n; intros; simpl; f_equal.
  - apply H; apply Theorem24'.
  - apply Theorem189.
    + apply IHn; intros; apply H; left; apply Le_Lt; auto.
    + apply H; red; auto.
Qed.

Fact cumle : ∀ f1 f2 n, 
  (∀ i, ILE_N i n -> f1 i ≦ f2 i) -> Cum f1 n ≦ Cum f2 n.
Proof.
  intros; revert H; induction n; intros; simpl; f_equal.
  - apply H; apply Theorem13; apply Theorem24.
  - apply Theorem168, Theorem191; apply Theorem168'.
    + apply IHn; intros; apply H; left; apply Le_Lt; auto.
    + f_equal; apply H; red; auto.
Qed.

Fact cumTi : ∀ h f n, Cum (mult_fun h f) n = h · (Cum f n).
Proof.
  intros; induction n; simpl; auto. rewrite IHn, Theorem201; auto.
Qed.

Fact cumMi : ∀ f1 f2 n, 
  Cum f1 n - Cum f2 n = Cum (λ x, f1(x) - f2(x)) n.
Proof.
  intros; induction n; simpl; auto. rewrite <- Mi_R, IHn; auto.
Qed.

Fact cumab : ∀ f1 n, |Cum f1 n| ≦ Cum (λ x, |f1 x|) n.
Proof.
  intros. induction n; simpl; [red; auto|].
  eapply Theorem173; try apply Ab2. now apply LePl_R.
Qed.

Fact cumcon : ∀ n z, Cum (λ m, z) n = n · z.
Proof.
  intros; induction n; Simpl_R. simpl Cum. rewrite IHn.
  pattern z at 2. rewrite <- RTi1_, <- Theorem201'; Simpl_R.
Qed.
