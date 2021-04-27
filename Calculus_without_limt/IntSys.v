(***************************************************************************)
(*   This is part of FA_3rdCalculus, it is distributed under the terms     *)
(*         of the GNU Lesser General Public License version 3              *)
(*                (see file LICENSE for more details)                      *)
(*                                                                         *)
(*            Copyright 2020-2022: Yaoshun Fu and Wensheng Yu.             *)
(***************************************************************************)

Require Export DCF.

Definition additivity S a b:=
  ∀ u v w, u ∈ [a|b] -> v ∈ [a|b] -> w ∈ [a|b] -> S u v + S v w = S u w. 

Definition intermed S f a b :=
  ∀ u v, u ∈ [a|b] -> v ∈ [a|b] -> v > u -> 
  ∃ p q, p ∈ [u|v] /\ q ∈ [u|v] /\ f(p)·(v-u) ≦ S u v /\ S u v ≦ f(q)·(v-u).

Definition integralsystem S f a b := additivity S a b /\ intermed S f a b.

Definition integrable S f a b :=
  ∀ S', integralsystem S' f a b -> 
  (∀ x y, x ∈ [a|b] -> y ∈ [a|b] -> S x y = S' x y).

Definition definiteiInt S f a b := integralsystem S f a b /\ integrable S f a b.

Notation " S =∫ f " := (definiteiInt S f)(at level 10).

Theorem Int_med : ∀ {S f a b},
  integralsystem S f a b -> ∀ c, c ∈ [a|b] -> diff_quo_median (S c) f a b.
Proof.
  intros. destruct H. red; intros.
  pose proof (H _ _ _ H0 H2 H3). rewrite <- H4; Simpl_R.
  destruct (H1 _ _ H2 H3 (Theorem182_1 _ _ l)) as [p [q [H5 [H6 [H7]]]]].
  exists p, q. split; auto. split; auto.
  split; apply LeTi_R2 with (z:=v-u); Simpl_R.
Qed.

Theorem Med_Int : ∀ {F f a b},
  diff_quo_median F f a b -> integralsystem F# f a b.
Proof.
  intros. split; red; intros.
  - unfold input2Mi. rewrite <- (Theorem181 (F v)); Simpl_R.
    rewrite Mi_R'. Simpl_R. apply Theorem181.
  - apply Theorem182_1' in H2.
    destruct (H _ _ H2 H0 H1) as [p [q [H3 [H4 [H5]]]]].
    apply LeTi_R1 with (z:=v-u) in H5; Simpl_Rin H5.
    apply LeTi_R1 with (z:=v-u) in H6; Simpl_Rin H6. exists p, q; auto.
Qed.

Theorem Int_DefInt : ∀ {S f a b}, S =∫ f a b ->
  ∀ c, c ∈ [a|b] -> ∀ F, diff_quo_median F f a b -> 
  ∀ u v, u ∈ [a|b] -> v ∈ [a|b] -> (S c)# u v = F# u v.
Proof.
  intros. destruct H. pose proof (Int_med H _ H0).
  destruct H. pose proof (Med_Int H1). rewrite <- (H4 _ H7); auto.
  unfold input2Mi; apply Theorem188_2 with (Θ:=S c u); Simpl_R.
  rewrite Theorem175. rewrite H; auto.
Qed.

Theorem DefInt_Int : ∀ {F f a b} , diff_quo_median F f a b ->
  (∀ F', diff_quo_median F' f a b -> 
  ∀ u v, u ∈ [a|b] -> v ∈ [a|b] -> F# u v = F'# u v) -> F# =∫ f a b.
Proof.
  intros. split; [apply Med_Int; auto|red; intros].
  pose proof (Int_med H1 _ H2). destruct H1.
  rewrite (H0 _ H4 _ _ H2 H3). unfold input2Mi.
  pattern (S' x y) at 1. rewrite <- (H1 x x y); Simpl_R.
Qed.