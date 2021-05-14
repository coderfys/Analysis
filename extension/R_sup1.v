(***************************************************************************)
(*   This is part of FA_3rdCalculus, it is distributed under the terms     *)
(*         of the GNU Lesser General Public License version 3              *)
(*                (see file LICENSE for more details)                      *)
(*                                                                         *)
(*            Copyright 2020-2022: Yaoshun Fu and Wensheng Yu.             *)
(***************************************************************************)

Require Export R_sup.

Lemma eqTi_R : ∀ x y z, z <> O -> x·z = y·z -> x = y.
Proof.
  intros. apply Theorem182_2' in H0.
  rewrite <- Theorem202' in H0. apply Theorem182_2.
  apply Theorem192 in H0. destruct H0; tauto.
Qed.

Lemma LeTi_R : ∀ x y z, O ≦ z -> x ≦ y -> x · z ≦ y · z.
Proof.
  intros; destruct H0; red.
  - destruct H.
    + left; apply Theorem203_1; auto. 
    + subst z; Simpl_R.
  - subst x; Simpl_R.
Qed.

Lemma LeTi_R' : ∀ x y z, O ≦ z -> x ≦ y -> z · x ≦ z· y.
Proof.
  intros. rewrite Theorem194, (Theorem194 z). apply LeTi_R; auto.
Qed.

Lemma LeTi_R1 : ∀ x y z, O < z -> x ≦ y -> x · z ≦ y · z.
Proof.
  intros; apply LeTi_R; red; auto.
Qed.

Lemma LeTi_R1' : ∀ x y z,O < z ->  x ≦ y -> z · x ≦ z· y.
Proof.
  intros; apply LeTi_R'; red; auto.
Qed.

Lemma LeTi_R2 : ∀ x y z, O < z -> x · z ≦ y · z -> x ≦ y.
Proof.
  intros; destruct H0; red.
  - apply Theorem203_1' in H0; auto.
  - destruct (Theorem167 x y) as [H1 | [H1 | H1]]; auto.
    apply Theorem203_1 with (Θ:=z) in H1; auto. EGR H0 H1.
Qed.

Lemma LeTi_R2' : ∀ x y z, O < z -> z · x ≦ z · y -> x ≦ y.
Proof.
  intros; rewrite Theorem194, (Theorem194 z) in H0.
  eapply LeTi_R2; eauto.
Qed.

Lemma LeTi_R3 : ∀ y z w x, O ≦ y -> O ≦ w -> 
  x ≦ w -> y ≦ z -> x·y ≦ w·z.
Proof.
  intros. apply LeTi_R' with (z:=y) in H1; auto.
  apply LeTi_R' with (z:=w) in H2; auto.
  rewrite Theorem194, (Theorem194 y) in H1.
  eapply Theorem173; eauto.
Qed.

Fixpoint factorial n : Real :=
  match n with
  | 1 => n
  | p` => p` · (factorial p)
  end.

Lemma facun0 : ∀ n, (factorial n) <> O.
Proof.
  do 2 intro. induction n. inversion H. apply IHn.
  apply Theorem192 in H. destruct H; auto. inversion H.
Qed.

Definition facn0 {n} := uneqO (facun0 n).

Definition Rdifa r n := (r/(factorial n)) facn0.

Lemma rdft : ∀ a b n, a·(Rdifa b n) = Rdifa (a·b) n.
Proof.
  intros. unfold Rdifa. rewrite Di_Rt; auto.
Qed.

Lemma rdf_1 : ∀ {a}, Rdifa a 1 = a.
Proof.
  intros. unfold Rdifa; Simpl_R.
Qed.

Lemma rdfp1 : ∀ a k l, (Rdifa (a^k`) k`) · ((k`/a) l) = Rdifa (a^k) k.
Proof.
  intros. apply eqTi_R with (z:=a); [ intro; destruct a, l; inversion H|].
  rewrite Theorem199; Simpl_R. rewrite (Theorem194 _ a).
  apply eqTi_R with (z:=factorial k); [apply facun0|].
  unfold Rdifa. rewrite (Theorem199 a); Simpl_R.
  rewrite Theorem199. Simpl_R. rewrite Theorem194; auto.
Qed.

Lemma absqu : ∀ h, | h |·| h | = h^2.
Proof.
  intros. destruct h; simpl; auto.
Qed.

Lemma powp1 : ∀ a n, O ≦ a -> |a|^n = a^n.
Proof.
  induction n; intros; simpl; rewrite Ab3'; auto.
Qed.

Lemma powp2 : ∀ n, |(-(1))^n| = 1.
Proof.
  induction n; intros; simpl in *; auto.
  rewrite Theorem193, IHn. Simpl_R.
Qed.

Lemma powp3 : ∀ n, (-(1))^n · (-(1))^n = 1.
Proof.
  intros. rewrite powT. Simpl_R. apply pow1.
Qed.

Lemma R2mgt : ∀ a b c, c < a -> c < b -> c < R2min a b.
Proof.
  intros. destruct (Pr_min4 a b); rewrite H1; auto.
Qed.

Lemma R2mlt : ∀ a b c, a < c \/ b < c -> R2min a b < c.
Proof.
  intros. generalize Pr_min2 Pr_min3; intros.
  destruct H; eapply Theorem172; eauto.
Qed.

Lemma R2Mle : ∀ a b c, a ≦ c -> b ≦ c -> R2max a b ≦ c.
Proof.
  intros. destruct (Pr_max4 a b); rewrite H1; auto.
Qed.

Lemma R2AMge : ∀ {a b c}, a ≦ c /\ c ≦ b -> |c| ≦ R2max (|a|) (|b|).
Proof.
  intros. destruct H, c; simpl.
  - pose proof (Pr_max3 (|a|) (|b|)). eapply Theorem173; eauto.
    eapply Theorem173; eauto. apply Ab7.
  - pose proof (Pr_max3 (|a|) (|b|)). eapply Theorem173; eauto.
    eapply Theorem173; eauto. apply Ab7.
  - pose proof (Pr_max2 (|a|) (|b|)). eapply Theorem173; eauto.
    apply LEminus in H. simpl in H. eapply Theorem173; eauto.
    destruct a; red; simpl; auto.
Qed.

Lemma LeRp1 : ∀ a b, O ≦ b -> a ≦ a+b.
Proof.
  intros; destruct H; 
    [left; apply Pl_R; auto | right; subst b; Simpl_R].
Qed.

Lemma LeRp2 : ∀ a b c, b ≦ c-a -> a+b ≦ c.
Proof.
  intros. apply LePl_R with (z:=-a); Simpl_R.
Qed.

Lemma Rlt1 : ∀ a b c l, a < |(b/c) l| <-> a·|c|<|b|.
Proof.
  split; intros.
  - apply Theorem203_1 with (Θ:=|c|) in H; Simpl_Rin H.
    + rewrite <- Theorem193 in H. Simpl_Rin H.
    + destruct c; simpl; auto.
  - apply Theorem203_1' with (Θ:=|c|); Simpl_R.
    + rewrite <- Theorem193. Simpl_R.
    + destruct c; simpl; auto.
Qed.

Lemma Rle1 : ∀ a b, a ≦ O -> b ≦ O -> a ≦ b -> |b| ≦ |a|.
Proof.
  intros. repeat rewrite Ab3'''; auto.
  apply -> LEminus; auto.
Qed.

Lemma Rle2 : ∀ {a b z1 z2 w1 w2}, z1 ≦ a -> a ≦ z2 ->
  w1 ≦ b -> b ≦ w2 -> z1-w2 ≦ a-b /\ a-b ≦ z2-w1.
Proof.
  intros; split; unfold Minus_R; apply Theorem191'; auto;
  apply LEminus; Simpl_R.
Qed.

Lemma Rle3 : ∀ a b, O ≦ a -> O ≦ b -> O ≦ a·b.
Proof.
  intros; destruct H, H0; try rewrite <- H; try rewrite <- H0; 
  red; Simpl_R. left; apply Pos; auto.
Qed.

Lemma Rle4 : ∀ {a b c d e f}, |a-c|≦e -> |b-d|≦f -> |a-b-(c-d)|≦e+f.
Proof. 
  intros. rewrite <- Theorem178 in H0. pose proof (Theorem191' H H0).
  eapply Theorem173 in H1; try apply Ab2; eauto.
  Simpl_Rin H1. rewrite Mi_R' in H1; auto.
Qed.

Lemma Abope1 : ∀ a b, a ≦ O -> O ≦ b -> |a-b| = |a| + |b|.
Proof.
  intros; destruct H.
  - destruct H0. 
    + destruct a, b; inversion H; inversion H0.
      unfold Minus_R; simpl; auto.
    + subst b; simpl; Simpl_R.
  - subst a; simpl; Simpl_R. apply Theorem178.
Qed.

Definition oc x y := /{ z | x < z /\ z ≦ y /}.
Definition co x y := /{ z | x ≦ z /\ z < y /}.

Notation "( a | b ]" := (oc a b).
Notation "[ a | b )" := (co a b).

Lemma ociMu : ∀ a b c d l, d > O -> 
  a ∈ (O|(b/d)l - (c/d)l] -> (d·a) ∈ (O|b-c].
Proof.
  intros; destruct H0, H0; constructor; split.
  - apply Pos; auto.
  - apply LeTi_R1' with (z:=d) in H1; auto.
    rewrite Theorem202 in H1; Simpl_Rin H1.
Qed.

Lemma ociMu' : ∀ a b c d l, d > O -> 
  (d·a) ∈ (O|b-c] -> a ∈ (O|(b/d)l - (c/d)l].
Proof.
  intros; destruct H0, H0; constructor; split.
  - destruct a, d; inversion H; inversion H0; auto.
  - apply LeTi_R2' with d; auto.
    rewrite Theorem202; Simpl_R.
Qed.

Lemma ociDi : ∀ {c} n, c > O -> (RdiN c n) ∈ (O|c].
Proof.
  intros; constructor; split; unfold RdiN.
  - apply Pos'; simpl; auto.
  - apply LeTi_R2 with (z:=n); Simpl_R; [reflexivity|].
    pattern c at 1. rewrite <- Theorem195.
    apply LeTi_R1'; auto. apply OrderNRle, Theorem24'.
Qed.

Lemma ocisub : ∀ u v a b h, u ∈ [a|b] -> v ∈ [a|b] ->
  h ∈ (O|u-v] -> h ∈ (O|b-a].
Proof.
  intros; destruct H, H, H0, H0, H1, H1.
  split; split; auto. eapply Theorem173; eauto. unfold Minus_R.
  apply Theorem191'; auto. apply -> LEminus; auto.
Qed.

Lemma ccil : ∀ {x a b}, x ∈ [a|b] -> a ∈ [a|b].
Proof.
  intros. destruct H, H. split; split; red; auto.
  eapply Theorem173; eauto.
Qed.

Lemma ccir : ∀ {x a b}, x ∈ [a|b] -> b ∈ [a|b].
Proof.
  intros. destruct H, H. split; split; red; auto.
  eapply Theorem173; eauto.
Qed.

Lemma ccil' : ∀ x h, h > O -> x ∈ [x|x+h].
Proof.
  intros. split; split; red; auto. left. apply Pl_R; auto.
Qed.

Lemma ccir' : ∀ x h, - h > O -> x ∈ [x+h|x].
Proof.
  intros. split; split; red; auto. left. 
  apply Theorem188_1 with (Θ:=-h); Simpl_R. apply Pl_R; auto.
Qed.

Lemma ccimi : ∀ a b c, c ∈ [a|b] -> (-c) ∈ [(-b)|(-a)].
Proof.
  intros; destruct H, H. apply LEminus in H.
  apply LEminus in H0. split; auto.
Qed.

Lemma cciMu : ∀ a b c d l, d > O -> 
  a ∈ [(b/d)l|(c/d)l] -> (d·a) ∈ [b|c].
Proof.
  intros; destruct H0, H0; constructor; split.
  - apply LeTi_R1' with (z:=d) in H0; Simpl_Rin H0.
  - apply LeTi_R1' with (z:=d) in H1; Simpl_Rin H1.
Qed.

Lemma cciMi : ∀ a b c d, a ∈ [b-c|d-c] -> (a+c) ∈ [b|d].
Proof.
  intros; destruct H, H; constructor; split;
  apply LePl_R with (z:=-c); Simpl_R.
Qed.

Lemma ccisub : ∀ u v {a b h}, u ∈ [a|b] -> v ∈ [a|b] ->
  h ∈ [u|v] -> h ∈ [a|b].
Proof.
  intros; destruct H, H, H0, H0, H1, H1. split; split;
  [apply (Theorem173 a u h)|apply (Theorem173 h v b)]; auto.
Qed.

Lemma ccisub1 : ∀ {a b c d}, c ∈ [a|b] -> d ∈ [c|b] -> d ∈ [a|b].
Proof.
  intros. destruct H, H, H0, H0. split; split; auto.
  apply (Theorem173 _ c); auto.
Qed.

Lemma ccilt : ∀ {v u a b}, v ∈ [a|b] -> u ∈ [a|b] -> u > v -> a < b.
Proof.
  intros; destruct H, H, H, H0, H0, H0; [| | |rewrite H in H0; ELR H0 H1];
  eapply Theorem172; eauto.
Qed.

Lemma ccile1 : ∀ {a b c d}, c ∈ [a|b] -> d ∈ [a|b] -> |d-c| ≦ b-a.
Proof.
  intros; destruct H, H, H0, H0. apply -> Ab1'; split.
  - rewrite Theorem181. apply Theorem191'; auto.
    apply -> LEminus; auto.
  - apply Theorem191'; auto. apply -> LEminus; auto.
Qed.

Lemma ccile2 : ∀ a x h, a ∈ [x|x+h] -> |a-x| ≦ h.
Proof.
  intros. destruct H, H. apply ->  Ab1'. split.
  - apply LePl_R with (z:=x); Simpl_R. eapply Theorem173; eauto.
    rewrite Theorem175. apply LePl_R with (z:=h); Simpl_R.
    eapply Theorem173; eauto.
  - apply LePl_R with (z:=x); Simpl_R. rewrite Theorem175; auto.
Qed.

Lemma ccile3 : ∀ a x h, a ∈ [x+h|x] -> |a-x| ≦ |h|.
Proof.
  intros. destruct H, H. apply Rle1.
  - destruct (Pl_R x h), (Co_T167 h O); auto.
    eapply Theorem173 in H0; eauto. LEGR H0 (H1 H3).
  - apply LePl_R with (z:=x); Simpl_R.
  - apply LePl_R with (z:=x); Simpl_R. rewrite Theorem175; auto.
Qed.

Lemma ociabs : ∀ {a b x h}, 
  x ∈ [a|b] -> (x+h) ∈ [a|b] -> h <> O -> |h| ∈ (O|b-a].
Proof.
  intros. apply Ab8 in H1. pose proof (ccile1 H H0). Simpl_Rin H2.
  split; split; auto.
Qed.
