(***************************************************************************)
(*   This is part of FA_3rdCalculus, it is distributed under the terms     *)
(*         of the GNU Lesser General Public License version 3              *)
(*                (see file LICENSE for more details)                      *)
(*                                                                         *)
(*            Copyright 2020-2022: Yaoshun Fu and Wensheng Yu.             *)
(***************************************************************************)

Require Import StD calTh.

(* Higher order strong derivative *)
Fixpoint N_str_derivative F f a b n :=
  match n with
  | 1 => str_derivative F f a b
  | p` => ∃ f1, str_derivative F f1 a b /\ N_str_derivative f1 f a b p
  end.

Definition N_str_derivability F a b n := ∃ f, N_str_derivative F f a b n.

Fact Nstd_imply_der : ∀ {F f a b n}, a < b -> N_str_derivative F f a b n ->
  N_uni_derivative F f a b n.
Proof.
  intros. generalize dependent F. induction n; intros.
  - apply std_imply_der; auto.
  - destruct H0 as [f1 [H0]]. apply (std_imply_der H) in H0. exists f1; auto.
Qed.

Fact Nstdpred : ∀ {F a b n},
  N_str_derivability F a b n` -> N_str_derivability F a b n.
Proof.
  intros. generalize dependent F. induction n; intros.
  - destruct H as [f [f1 [H]]]. red; eauto.
  - destruct H as [f [f1 [H]]], (IHn f1) as [f2]; [red; eauto|].
    exists f2. red; eauto.
Qed.

Definition N_th {F a b n} (H :N_str_derivability F a b n) :=
  Getele H.

Definition P_th {F a b n} (H :N_str_derivability F a b n`) :=
  Getele (Nstdpred H).

Ltac Ndg f := unfold N_th, Getele; destruct (cid) as [f ]; simpl proj1_sig.
Ltac Pdg f := unfold P_th, Getele; destruct (cid) as [f ]; simpl proj1_sig.

(* Main term of Taylor formula for higher order strong derivative *)
Fixpoint TFmain_std F a b c n
  :N_str_derivability F a b n -> Rfun := match n with
  | 1 => λ _ _, F c
  | p` => λ l x, (P_th l c)·(Rdifa ((x-c)^p) p) +
  TFmain_std F a b c p (Nstdpred l) x end.

(* The uniqueness of main term of Taylor formula *)
Fact TF_eq : ∀ {F a b n} l1 l2, ∀ {c x}, c ∈ [a|b] ->
  TFmain_std F a b c n l1 x = TaylorFormula_main F a b c n l2 x.
Proof.
  intros. pose proof (Nder_lt l2). revert l1 l2. induction n; intros; auto.
  pose proof (IHn (Nstdpred l1) (Nderpred l2)). simpl; f_equal; auto.
  Pdg f1. pdg1 f2. apply Nstd_imply_der in n0; auto.
  rewrite (uniNder n0 n1); auto.
Qed.

(* Taylor theorem for higher order strong derivative *)
Theorem TTstd : ∀ {F a b n l},
  ∀ M, (∀ x, x ∈ [a|b] -> |(N_th l) x|≦M) ->
  ∀ c x, c ∈ [a|b] -> x ∈ [a|b] ->
  |F(x)-(TFmain_std F a b c n l x)|≦ M·(Rdifa (|x-c|^n) n).
Proof.
  intros. pose proof (ccil H0). destruct H2, H2 as [_ [H2| H2]].
  - assert (l1:N_uni_derivability F a b n).
    { inversion l as [f]. exists f. apply Nstd_imply_der; auto. }
    assert (∀ x,x ∈ [a|b] -> |n_th l1 x| ≦ M).
    { intros. eapply Theorem173; eauto. right. f_equal. ndg1 f1. Ndg f2.
      apply Nstd_imply_der in n1; auto. eapply uniNder; eauto. }
    rewrite (TF_eq _ l1); auto. exact (TaylorThoerem _ H3 _ _ H0 H1).
  - subst a. destruct H0, H0, H1, H1. LEGER H0 H2. LEGER H1 H3. subst b c.
    assert (∀ F a b c n l, F c = TFmain_std F a b c n l c).
    { intros. induction n0; simpl; auto. rewrite (IHn0 (Nstdpred l0)).
      Simpl_R. rewrite powO; unfold Rdifa; Simpl_R. }
    rewrite <- H4; Simpl_R. rewrite powO. right; unfold Rdifa; Simpl_R.
Qed.
