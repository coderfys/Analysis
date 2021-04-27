(***************************************************************************)
(*   This is part of FA_Landau, it is distributed under the terms of the   *)
(*             GNU Lesser General Public License version 3                 *)
(*                (see file LICENSE for more details)                      *)
(*                                                                         *)
(*           Copyright 2020-2022: Yaoshun Fu and Wensheng Yu.              *)
(***************************************************************************)

(* NATURAL NUMBERS *)

(* SECTION I Axioms *)

Require Export Pre_Ensemble.

Inductive Nat : Type := 
  | One 
  | Successor : Nat -> Nat.

Notation "1" := One.
Notation " x ` " := (Successor x)(at level 0).

Corollary AxiomIII : ∀ x, x` <> 1.
Proof.
  intros; intro; inversion H.
Qed.

Corollary AxiomIV : ∀ x y, x` = y` -> x = y.
Proof.
  intros; inversion H; auto.
Qed.

Corollary AxiomV : ∀ ℳ, 1 ∈ ℳ /\ (∀ x, x ∈ ℳ -> x` ∈ ℳ) -> ∀ z, z ∈ ℳ.
Proof.
  intros; destruct H; induction z; auto.
Qed.

(* SECTION II Additions *)

Theorem Theorem1 : ∀ x y, x <> y -> x` <> y`.
Proof.
  intros x y H H0; apply AxiomIV in H0; auto.
Qed.

Theorem Theorem2 : ∀ x, x` <> x.
Proof.
  intros; set (ℳ:=/{ x | x` <> x /}).
  assert (1 ∈ ℳ). { constructor; apply AxiomIII. }
  assert (∀ x, x ∈ ℳ -> x` ∈ ℳ); intros.
  { destruct H0; constructor; apply Theorem1; auto. }
  assert (∀ x, x ∈ ℳ). { apply AxiomV; auto. }
  destruct H1 with x; auto.
Qed.

Theorem Theorem3 : ∀ x, (x <> 1 -> ∃ u, x = u`).
Proof.
  intros; set (ℳ:=/{ x | x = 1 \/ (x <> 1 -> ∃ u, x = u`) /}).
  assert (1 ∈ ℳ). { constructor; tauto. }
  assert (∀ x, x ∈ ℳ -> x` ∈ ℳ); intros.
  { destruct H0; constructor; right; intros; eauto. }
  assert (∀ x, x ∈ ℳ). { apply AxiomV; auto. }
  destruct H2 with x, H3; tauto.
Qed.

Fixpoint Plus_N x y :=
  match y with
  | 1 => x`
  | z` => (Plus_N x z)`
  end.

Notation " x + y " := (Plus_N x y).

Theorem Theorem4 : exists! f, ∀ x, 
  (f x 1 = x` /\ ∀ y, f x y` = (f x y)`).
Proof.
  exists Plus_N; split; intros; [simpl; auto|].
  apply fun_ext; intros; apply fun_ext; intros.
  specialize H with m; destruct H. induction m0.
  - rewrite H; auto.
  - rewrite H0, <- IHm0; auto.
Qed.

Corollary NPl_1 : ∀ x, x + 1 = x`.
Proof.
  intros; reflexivity.
Qed.

Corollary NPl_S : ∀ x y, x + y` = (x + y)`.
Proof.
  intros; reflexivity.
Qed.

Corollary NPl1_ : ∀ x, 1 + x = x`.
Proof.
  intros; induction x; auto.
  simpl; rewrite IHx; auto.
Qed.

Corollary NPlS_ : ∀ x y, x` + y = (x + y)`.
Proof.
  intros; induction y; auto.
  simpl; rewrite IHy; auto.
Qed.

Hint Rewrite NPl_1 NPl_S NPl1_ NPlS_ : Nat.

Ltac Simpl_N := autorewrite with Nat; auto.
Ltac Simpl_Nin H := autorewrite with Nat in H; auto.

Theorem Theorem5 : ∀ x y z, (x + y) + z = x + (y + z).
Proof.
  intros; set (ℳ:=/{ z | (x + y) + z = x + (y + z) /}).
  assert (1 ∈ ℳ). { constructor; Simpl_N. }
  assert (∀ z, z ∈ ℳ -> z` ∈ ℳ); intros.
  { destruct H0; constructor; Simpl_N; rewrite H0; auto. }
  assert (∀ z, z ∈ ℳ). { apply AxiomV; auto. }
  destruct H1 with z; auto.
Qed.

Theorem Theorem6 : ∀ x y, x + y = y + x.
Proof.
  intros; set (ℳ:=/{ x | x + y = y + x /}).
  assert (1 ∈ ℳ).
  { constructor; Simpl_N. }
  assert (∀ x, x ∈ ℳ -> x` ∈ ℳ); intros.
  { destruct H0; constructor; Simpl_N; rewrite H0; auto. }
  assert (∀ z, z ∈ ℳ). { apply AxiomV; auto. }
  destruct H1 with x; auto.
Qed.

Theorem Theorem7 : ∀ x y, y <> x + y.
Proof.
  intros; set (ℳ:=/{ y | y <> x + y /}). assert (1 ∈ ℳ). 
  { constructor; Simpl_N; intro; eapply AxiomIII; eauto. }
  assert (∀ y, y ∈ ℳ -> y` ∈ ℳ); intros.
  { destruct H0; constructor; Simpl_N; apply Theorem1 in H0; auto. }
  assert (∀ y, y ∈ ℳ). { apply AxiomV; auto. }
  destruct H1 with y; auto.
Qed.

Theorem Theorem8 : ∀ x y z, y <> z -> x + y <> x + z.
Proof.
  intros; set (ℳ:=/{ x | y <> z -> x + y <> x + z /}).
  assert (1 ∈ ℳ). { constructor; Simpl_N; apply Theorem1. }
  assert (∀ x, x ∈ ℳ -> x` ∈ ℳ); intros.
  { destruct H1; constructor; intro.
    apply H1 in H2; apply Theorem1 in H2; Simpl_N. }
  assert (∀ x, x ∈ ℳ). { apply AxiomV; auto. }
  destruct H2 with x; auto.
Qed.

Lemma Lemma_T9a: ∀ x y, x = y -> ∀ u, x <> y + u.
Proof.
  intros; rewrite <- H, Theorem6; apply Theorem7.
Qed.

Lemma Lemma_T9b: ∀ x y, x = y -> ∀ v, y <> x + v.
Proof.
  intros; apply Lemma_T9a; auto.
Qed.

Lemma Lemma_T9c: ∀ x y u, x = y + u -> ∀ v, y <> x + v.
Proof.
  intros; rewrite H, Theorem5, Theorem6; apply Theorem7.
Qed.

Theorem Theorem9 : ∀ x y, 
  x = y \/ (∃ u, x = y + u) \/ (∃ v, y = x + v).
Proof.
  intros; 
  set (ℳ:=/{ y | x = y \/ (∃ u, x = y + u) \/ (∃ v, y = x + v) /}).
  assert (1 ∈ ℳ).
  { constructor; destruct x; auto. right; left; exists x; Simpl_N. }
  assert (∀ y, y ∈ ℳ -> y` ∈ ℳ); intros.
  { destruct H0, H0 as [H0 | [[u H0] | [v H0]] ]; constructor.
    - right; right; exists 1; rewrite H0; Simpl_N.
    - destruct u.
      + Simpl_Nin H0; auto.
      + right; left; exists u; Simpl_N; Simpl_Nin H0.
    - right; right; exists v`; Simpl_N; rewrite H0; auto. }
  assert (∀ y, y ∈ ℳ). { apply AxiomV; auto. }
  destruct H1 with y; auto.
Qed.

(* SECTION III Ordering *)

Definition IGT_N x y := ∃ u, x = y + u.
Notation " x > y " := (IGT_N x y).

Definition ILT_N x y := ∃ v, y = x + v.
Notation " x < y " := (ILT_N x y).

Corollary Nlt_S_ : ∀ x, x < x`.
Proof.
  intros. red; exists 1; auto.
Qed.

Theorem Theorem10 : ∀ x y, x = y \/ x > y \/ x < y.
Proof.
  intros; destruct (Theorem9 x y) as [H | [H | H]]; auto.
Qed.

Theorem Theorem11 : ∀ x y, x > y -> y < x.
Proof.
  intros; auto.
Qed.

Theorem Theorem12 : ∀ x y, x < y -> y > x.
Proof.
  intros; auto.
Qed.

Definition IGE_N x y := x > y \/ x = y.
Notation " x ≧ y " := (IGE_N x y) (at level 55).

Definition ILE_N x y := x < y \/ x = y.
Notation " x ≦ y " := (ILE_N x y) (at level 55).

Theorem Theorem13 : ∀ x y, x ≧ y -> y ≦ x.
Proof.
  intros; red; red in H; destruct H; auto.
Qed.

Theorem Theorem14 : ∀ x y, x ≦ y -> y ≧ x.
Proof.
  intros; red; red in H; destruct H; auto.
Qed.

Theorem Theorem15 : ∀ x y z, x < y -> y < z -> x < z.
Proof.
  intros; unfold ILT_N in *; destruct H, H0.
  rewrite H, Theorem5 in H0; eauto.
Qed.

Theorem Theorem16 : ∀ x y z, 
  (x ≦ y /\ y < z) \/ (x < y /\ y ≦ z) -> x < z.
Proof.
  intros; destruct H as [[[H | H] H0] | [H [H0 | H0]]].
  - eapply Theorem15; eauto.
  - rewrite H; auto.
  - eapply Theorem15; eauto.
  - rewrite <- H0; auto.
Qed.

Theorem Theorem17 : ∀ x y z, x ≦ y -> y ≦ z -> x ≦ z.
Proof.
  intros; red in H; destruct H.
  - left; eapply Theorem16; right; split; eauto.
  - rewrite H; auto.
Qed.

Theorem Theorem18 : ∀ x y, x + y > x.
Proof.
  intros; red; eauto.
Qed.

Theorem Theorem19_1 : ∀ x y z, x > y -> x + z > y + z.
Proof.
  intros; red in H; red; destruct H; exists x0.
  rewrite H, Theorem5, (Theorem6 x0 z), Theorem5; auto.
Qed.

Theorem Theorem19_2 : ∀ x y z, x = y -> x + z = y + z.
Proof.
  intros; rewrite H; auto.
Qed.

Theorem Theorem19_3 : ∀ x y z, x < y -> x + z < y + z.
Proof.
  intros; apply Theorem19_1; auto.
Qed.

Lemma OrdN1 : ∀ {x y}, x = y -> x > y -> False.
Proof.
  intros; red in H0; destruct H0; rewrite H, Theorem6 in H0.
  eapply Theorem7; eauto.
Qed.

Lemma OrdN2 : ∀ {x y}, x = y -> x < y -> False.
Proof.
  intros; symmetry in H; eapply OrdN1; eauto.
Qed.

Lemma OrdN3 : ∀ {x y}, x < y -> x > y -> False.
Proof.
  intros; red in H; red in H0; destruct H, H0.
  rewrite H, Theorem5, Theorem6 in H0; eapply Theorem7; eauto.
Qed.

Ltac EGN H H1 := destruct (OrdN1 H H1).
Ltac ELN H H1 := destruct (OrdN2 H H1).
Ltac LGN H H1 := destruct (OrdN3 H H1).

Lemma OrdN4 : ∀ {x y}, x ≦ y -> x > y -> False.
Proof.
  intros; destruct H; try LGN H H0; EGN H H0.
Qed.

Lemma OrdN5 : ∀ {x y}, x ≧ y -> x < y -> False.
Proof.
  intros; destruct H; try LGN H H0; ELN H H0.
Qed.

Ltac LEGN H H1 := destruct (OrdN4 H H1).
Ltac GELN H H1 := destruct (OrdN5 H H1).

Corollary LEGEN : ∀ {x y}, x ≦ y -> y ≦ x -> x = y.
Proof.
  intros; destruct H; auto. LEGN H0 H.
Qed.

Theorem Theorem20_1 : ∀ x y z, x + z > y + z -> x > y.
Proof.
  intros; destruct (Theorem10 x y) as [H0 | [H0 | H0]]; auto.
  - apply Theorem19_2 with (z:=z) in H0; EGN H0 H.
  - apply Theorem19_1 with (z:=z) in H0; LGN H H0.
Qed.

Theorem Theorem20_2 : ∀ x y z, x + z = y + z -> x = y.
Proof.
  intros; destruct (Theorem10 x y) as [H0 | [H0 | H0]]; auto.
  - apply Theorem19_1 with (z:=z) in H0; EGN H H0.
  - apply Theorem19_3 with (z:=z) in H0; ELN H H0.
Qed.

Theorem Theorem20_3 : ∀ x y z, x + z < y + z -> x < y.
Proof.
  intros; destruct (Theorem10 x y) as [H0 | [H0 | H0]]; auto.
  - apply Theorem19_2 with (z:=z) in H0; ELN H0 H.
  - apply Theorem19_1 with (z:=z) in H0; LGN H H0.
Qed.

Corollary LePl_N  : ∀ x y z, x ≦ y <-> x + z ≦ y + z.
Proof.
  split; intros; destruct H.
  - left; apply Theorem19_1; auto.
  - subst x; right; auto.
  - left; apply Theorem20_1 with (z:=z); Simpl_N.
  - right; apply Theorem20_2 with (z:=z); Simpl_N.
Qed.

Theorem Theorem21 : ∀ x y z u, x > y -> z > u -> x + z > y + u.
Proof.
  intros. apply Theorem19_1 with (z:=z) in H.
  apply Theorem19_1 with (z:=y) in H0.
  rewrite Theorem6, (Theorem6 u y) in H0; eapply Theorem15; eauto.
Qed.

Theorem Theorem22 : ∀ x y z u, 
  (x ≧ y /\ z > u) \/ (x > y /\ z ≧ u) -> x + z > y + u.
Proof.
  intros; destruct H as [[H H0] | [H H0]].
  - red in H; destruct H; [apply Theorem21; auto|].
    rewrite H, Theorem6, (Theorem6 y u); apply Theorem19_1; auto.
  - red in H0; destruct H0; [apply Theorem21; auto|].
    rewrite H0; apply Theorem19_1; auto.
Qed.

Theorem Theorem23 : ∀ x y z u, 
  x ≧ y /\ z ≧ u -> (x + z) ≧ (y + u).
Proof.
  intros; destruct H, H.
  - left; apply Theorem22; auto.
  - destruct H0.
    + left; apply Theorem22; left; split; try red; auto.
    + right; rewrite H, H0; auto.
Qed.

Theorem Theorem24 : ∀ x, x ≧ 1.
Proof.
  intros; destruct x; red; try tauto.
  left; red; exists x; Simpl_N.
Qed.

Corollary Theorem24' : ∀ x, 1 ≦ x.
Proof.
  intros; apply Theorem13, Theorem24.
Qed.

Lemma OrdN6 : ∀ {n}, n < 1 -> False.
Proof.
  intros; GELN (Theorem24 n) H.
Qed.

Ltac N1F H := destruct (OrdN6 H).

Theorem Theorem25 : ∀ x y, y > x -> y ≧ (x + 1).
Proof.
  intros; red in H; destruct H; rewrite H; apply Theorem23.
  split; try apply Theorem24; red; auto.
Qed.

Theorem Theorem26 : ∀ x y, y < (x + 1) -> y ≦ x.
Proof.
  intros; destruct (Theorem10 y x) as [H0 | [H0 | H0]]; red; auto.
  apply Theorem25 in H0; GELN H0 H.
Qed.

Corollary Theorem26' : ∀ {x y}, y ≦ x -> y < (x + 1).
Proof.
  intros; apply (Theorem16 _ x _); left; split; red; eauto.
Qed.

Corollary Le_Lt : ∀ {x y}, y ≦ x -> y < x`.
Proof.
  intros; apply Theorem26'; auto.
Qed.

Corollary Lt_Le : ∀ {u x}, u < x -> u` ≦ x.
Proof. 
  intros; apply Theorem26;apply Theorem19_3 with (z:=1) in H; auto.
Qed.

Corollary N1P : ∀ {x y}, 1 < x + y.
Proof.
  intros; pose proof (Theorem13 _ _ (Theorem24 x)).
  apply (Theorem16 _ x _); left; split; auto; apply Theorem18.
Qed.

Corollary N1P' : ∀ {x y}, x > y -> x > 1.
Proof.
  intros; pose proof (Theorem13 _ _ (Theorem24 y)).
  eapply Theorem16; eauto.
Qed.

Theorem Theorem27 : ∀ N, No_Empty N  -> 
  ∃ x, x ∈ N /\ (∀ y, y ∈ N -> x ≦ y).
Proof.
  intros; set (ℳ:=/{ x | ∀ y, y ∈ N -> x ≦ y /}).
  assert (1 ∈ ℳ).
  { constructor; intros; apply Theorem13, Theorem24. }
  assert (~ ∀ z, z ∈ ℳ -> z` ∈ ℳ).
  { intro; assert (∀ z, z ∈ ℳ). { apply AxiomV; auto. }
    red in H; destruct H; destruct H2 with x`; apply H3 in H.
    pose proof (Theorem18 x 1); Simpl_Nin H4; LEGN H H4. }
  assert (∃ m, m ∈ ℳ /\ ~ m` ∈ ℳ).
  { Absurd. elim H1; intros.  Absurd; elim H2; eauto. }
  destruct H2 as [m [H2 H3]]; exists m; split; intros; auto.
  - Absurd; elim H3; constructor; intros.
    pose proof H5; destruct H2; apply H2 in H5; red.
    destruct (Theorem10 m` y) as [H7 | [H7 | H7]]; try tauto.
    apply Theorem26 in H7; pose proof (LEGEN H5 H7). subst m; tauto.
  - destruct H2; auto.
Qed.

Fixpoint lt_N x y := 
  match x , y with
   | 1 , p` => True
   | p` , q` => lt_N p q
   | _ , _  => False
  end.

Corollary eqvltN : ∀ x y, x < y <-> lt_N x y.
Proof.
  split; intros; generalize dependent y; 
  induction x, y; simpl; auto; intros; try (N1F H).
  - apply IHx; repeat rewrite <- NPl_1 in H.
    apply Theorem20_1 in H; auto.
  - destruct H.
  - rewrite <- NPl1_; apply N1P.
  - destruct H.
  - apply IHx in H. repeat rewrite <- NPl_1.
    apply Theorem19_1; auto.
Qed.

Theorem ltcase : ∀ x y, {lt_N y x} + {lt_N x y} + {x = y}.
Proof.
  intros. generalize dependent y. 
  induction x, y; simpl; auto; intros.
  destruct (IHx y) as [[H | H] | H]; auto. rewrite H; simpl; auto.
Qed.

Theorem Ncase : ∀ x y, {x < y} + {x > y} + {x = y}.
Proof.
  intros. destruct (ltcase x y) as [[H | H] | H]; auto;
  apply eqvltN in H; auto.
Qed.

Lemma Min_N : ∀ z x (l :z>x), {y | x + y = z}.
Proof.
  intros. apply eqvltN in l. induction z.
  - destruct x, l.
  - assert ({lt_N x z} + {x = z}).
    { clear IHz. generalize dependent z. 
      induction x, z; simpl; auto; intros.
      - apply eqvltN in l. N1F l.
      - apply IHx in l. destruct l; auto.
        rewrite e; auto. }
    destruct H.
    + apply IHz in l0; destruct l0.
      exists x0`; Simpl_N; rewrite e; auto.
    + exists 1; rewrite e; Simpl_N.
Qed.

Definition Minus_N z x l := proj1_sig (Min_N z x l).
Notation " x - y " := (Minus_N x y).

Lemma NMi_uni : ∀ z x l y, x + y = z -> (z - x) l = y.
Proof.
  intros; unfold Minus_N; destruct (Min_N z x l); simpl.
  rewrite <- H, Theorem6, (Theorem6 x) in e.
  eapply Theorem20_2; eauto.
Qed.

Corollary NMi1 : ∀ x y l, ((x - y) l) + y = x.
Proof.
  intros; unfold Minus_N; destruct (Min_N x y l); simpl.
  rewrite Theorem6; auto.
Qed.

Corollary NMi1' : ∀ x y l, y + ((x - y) l) = x.
Proof.
  intros; rewrite Theorem6; apply NMi1. 
Qed.

Corollary NMi2 : ∀ x y l, ((x + y) - y) l = x.
Proof.
  intros; unfold Minus_N; apply NMi_uni; apply Theorem6. 
Qed.

Corollary NMi2' : ∀ x y l, ((y + x) - y) l = x.
Proof.
  intros; unfold Minus_N; apply NMi_uni; auto. 
Qed.

Hint Rewrite NMi1 NMi1' NMi2 NMi2' : Nat.

Corollary NMi3 : ∀ x l, ((x - 1) l)` = x.
Proof.
  intros; rewrite <- NPl1_; Simpl_N.
Qed.

Corollary NMi4 : ∀ x l, (x` - 1) l = x.
Proof.
  intros; apply Theorem20_2 with (z:=1); Simpl_N.
Qed.

Corollary NMi5 : ∀ x y l l', (x` - y`) l = (x - y) l'.
Proof.
  intros; apply Theorem20_2 with (z:=y`); Simpl_N.
Qed.

Corollary NMi6 : ∀ n l, Minus_N n` n l = 1.
Proof.
  intros; apply Theorem20_2 with (z:=n); Simpl_N.
Qed.

Hint Rewrite NMi3 NMi4 NMi5 NMi6 : Nat.

Corollary NMi7 : ∀ {n k} l l1, Minus_N n` k l = (Minus_N n k l1)`.
Proof.
  intros; apply Theorem20_2 with (z:=k); Simpl_N.
Qed.

(* SECTION IV Multiplication *)

Fixpoint Times_N x y :=
  match y with
   | 1 => x
   | z` => (Times_N x z) + x
  end.

Notation " x · y " := (Times_N x y)(at level 40).

Theorem Theorem28 : exists! f, ∀ x, 
  (f x 1 = x /\ ∀ y, f x y` = f x y + x ).
Proof.
  exists Times_N; split; intros; [simpl; auto|].
  apply fun_ext; intros; apply fun_ext; intros. 
  specialize H with m; destruct H. induction m0.
  - rewrite H; auto.
  - rewrite H0, <- IHm0; auto.
Qed.

Corollary NTi_1 : ∀ x, x · 1 = x.
Proof.
  intros; reflexivity.
Qed.

Corollary NTi_S : ∀ x y, x · y` = (x · y + x).
Proof.
  intros; reflexivity.
Qed.

Corollary NTi1_ : ∀ x, 1 · x = x.
Proof.
  intros; induction x; auto.
  simpl; rewrite IHx; auto.
Qed.

Corollary NTiS_ : ∀ x y, x` · y = (x · y + y).
Proof.
  intros; induction y; auto.
  simpl; rewrite IHy. repeat rewrite Theorem5.
  rewrite (Theorem6 x); auto.
Qed.

Hint Rewrite NTi_1 NTi_S NTi1_ NTiS_ : Nat.

Theorem Theorem29 : ∀ x y, x · y = y · x.
Proof.
  intros; set (ℳ:=/{ x | x · y = y · x /}).
  assert (1 ∈ ℳ). { constructor; Simpl_N. }
  assert (∀ x, x ∈ ℳ -> x` ∈ ℳ); intros.
  { destruct H0; constructor; Simpl_N; rewrite H0; auto. }
  assert (∀ x, x ∈ ℳ). { apply AxiomV; auto. }
  destruct H1 with x; auto.
Qed.

Theorem Theorem30 : ∀ x y z, x · (y + z) = (x · y) + (x · z).
Proof.
  intros; set (ℳ:=/{ z | x · (y + z) = (x · y) + (x · z) /}).
  assert (1 ∈ ℳ). { constructor; Simpl_N. }
  assert (∀ z, z ∈ ℳ -> z` ∈ ℳ); intros.
  { destruct H0; split; Simpl_N; rewrite H0,Theorem5; auto. }
  assert (∀ z, z ∈ ℳ). { apply AxiomV; auto. }
  destruct H1 with z; auto.
Qed.

Corollary Theorem30' : ∀ x y z, (y + z) · x =  (y · x) + (z · x).
Proof.
  intros; 
  rewrite Theorem29,(Theorem29 y),(Theorem29 z); apply Theorem30.
Qed.

Theorem Theorem31 : ∀ x y z, (x · y) · z = x · (y · z).
Proof.
  intros; set (ℳ:=/{ z | (x · y) · z = x · (y · z) /}).
  assert (1 ∈ ℳ). { constructor; Simpl_N. }
  assert (∀ z, z ∈ ℳ -> z` ∈ ℳ); intros.
  { destruct H0; split; Simpl_N; rewrite H0, Theorem30; auto. }
  assert (∀ z, z ∈ ℳ). { apply AxiomV; auto. }
  destruct H1 with z; auto.
Qed.

Theorem Theorem32_1 : ∀ {x y} z, x > y -> x · z > y · z.
Proof.
  intros; red in H; red; destruct H.
  exists (x0 · z); rewrite H; apply Theorem30'.
Qed.

Theorem Theorem32_2 : ∀ {x y} z, x = y -> x · z = y · z.
Proof.
  intros; rewrite H; auto.
Qed.

Theorem Theorem32_3 : ∀ {x y} z, x < y -> x · z < y · z.
Proof.
  intros; apply Theorem32_1; auto.
Qed.

Theorem Theorem33_1 : ∀ x y z, x · z > y · z -> x > y .
Proof.
  intros; destruct (Theorem10 x y) as [H0 | [H0 | H0]]; auto.
  - apply (Theorem32_2 z) in H0; EGN H0 H.
  - apply (Theorem32_1 z) in H0; LGN H H0.
Qed.

Theorem Theorem33_2 : ∀ x y z, x · z = y · z -> x = y.
Proof.
  intros; destruct (Theorem10 x y) as [H0 | [H0 | H0]]; auto.
  - apply (Theorem32_1 z) in H0. EGN H H0.
  - apply (Theorem32_1 z) in H0; ELN H H0.
Qed.

Theorem Theorem33_3 : ∀ x y z, x · z < y · z -> x < y .
Proof.
  intros; destruct (Theorem10 x y) as [H0 | [H0 | H0]]; auto.
  - apply (Theorem32_2 z) in H0; ELN H0 H.
  - apply (Theorem32_1 z) in H0; LGN H H0.
Qed.

Theorem Theorem34 : ∀ x y z u, x > y -> z > u -> x · z > y · u.
Proof.
  intros. apply (Theorem32_1 z) in H; apply (Theorem32_1 y) in H0.
  rewrite Theorem29,(Theorem29 u y) in H0; eapply Theorem15; eauto.
Qed.

Theorem Theorem35 : ∀ x y z u, 
  (x ≧ y /\ z > u) \/ (x > y /\ z ≧ u) -> x · z > y · u.
Proof.
  intros; destruct H as [[[H | H] H0] | [H [H0 | H0]]].
  - apply Theorem34; auto.
  - rewrite H, Theorem29, (Theorem29 y u); apply Theorem32_1; auto.
  - apply Theorem34; auto.
  - rewrite H0; apply Theorem32_1; auto.
Qed.

Theorem Theorem36 : ∀ x y z u, 
  x ≧ y /\ z ≧ u -> (x · z) ≧ (y · u).
Proof.
  intros; destruct H; red in H; destruct H.
  - left; apply Theorem35; auto.
  - destruct H0.
    + left; apply Theorem35; left; split; red; auto.
    + right; rewrite H, H0; auto.
Qed.
