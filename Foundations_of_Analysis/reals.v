(***************************************************************************)
(*   This is part of FA_Landau, it is distributed under the terms of the   *)
(*             GNU Lesser General Public License version 3                 *)
(*                (see file LICENSE for more details)                      *)
(*                                                                         *)
(*           Copyright 2020-2022: Yaoshun Fu and Wensheng Yu.              *)
(***************************************************************************)

(* REALS *)

(* SECTION I Definition *)

Require Export cuts.

Inductive Real : Type :=
  | O : Real
  | P : Cut -> Real
  | N : Cut -> Real.

Definition Equal_R Ξ Γ := 
  match Ξ, Γ with
   | P ξ, P η => ξ ≈ η
   | N ξ, N η => ξ ≈ η
   | O, O => True
   | _, _ => False
  end.

Definition No_Equal_R Ξ Γ := ~ Equal_R Ξ Γ.

Corollary eq3 : ∀ Ξ Γ, Equal_R Ξ Γ <-> Ξ = Γ.
Proof.
  split; intros.
  - destruct Ξ, Γ; auto; try elim H; simpl in H;
    try rewrite (eq2 H); auto.
  - rewrite H; destruct Γ; simpl; auto; apply Theorem116.
Qed.

Corollary No_Equal_Real : ∀ Ξ Γ, No_Equal_R Ξ Γ <-> Ξ <> Γ.
Proof.
  split; intros; intro; apply eq3 in H0; auto.
Qed.

Theorem Theorem163 :∀ (Ξ :Real), Ξ = Ξ.
Proof.
  auto.
Qed.

Theorem Theorem164 : ∀ (Ξ Γ :Real), Ξ = Γ -> Γ = Ξ.
Proof.
  auto.
Qed.

Theorem Theorem165 : ∀ (Ξ Γ Θ :Real), Ξ = Γ -> Γ = Θ -> Ξ = Θ.
Proof.
  intros. rewrite <- H0; auto.
Qed.

(* SECTION II Ordering *)

Definition Abs_R Ξ := 
  match Ξ with
   | N ξ => P ξ
   | Ξ => Ξ
  end.

Notation " | Ξ | " := (Abs_R Ξ)(at level 10).

Theorem Theorem166 : ∀ Ξ, Ξ <> O -> ∃ ξ, |Ξ| = (P ξ).
Proof.
  intros; destruct Ξ; simpl; eauto; elim H; auto.
Qed.

Definition ILT_R Ξ Γ := 
  match Ξ, Γ with
   | P ξ, P η => ξ < η
   | P _, _ => False
   | O, P _ => True
   | O, _ => False
   | N ξ, N η => ξ > η
   | N _, _ => True
  end.
Notation " Ξ < Γ " := (ILT_R Ξ Γ).

Definition IGT_R Ξ Γ := ILT_R Γ Ξ.
Notation " Ξ > Γ " := (IGT_R Ξ Γ).

Theorem Theorem167 : ∀ Ξ Γ, Ξ = Γ \/ Ξ < Γ \/ Ξ > Γ.
Proof.
  intros; destruct Ξ, Γ; simpl; try tauto; destruct 
    (Theorem123 c c0) as [H | [H | H]]; try rewrite (eq2 H); auto.
Qed.

Lemma OrdR1 : ∀ {Ξ Γ}, Ξ = Γ -> Ξ > Γ -> False.
Proof.
  intros; destruct Ξ, Γ; simpl in *; auto; try discriminate.
  - apply eq3 in H; simpl in H; EGC H H0.
  - apply eq3 in H; simpl in H; ELC H H0.
Qed.

Lemma OrdR2 : ∀ {Ξ Γ}, Ξ = Γ -> Ξ < Γ -> False.
Proof.
  intros; destruct Ξ, Γ; simpl in *; auto; try discriminate.
  - apply eq3 in H; simpl in H; ELC H H0.
  - apply eq3 in H; simpl in H; EGC H H0.
Qed.

Lemma OrdR3 : ∀ {Ξ Γ}, Ξ < Γ -> Ξ > Γ -> False.
Proof.
  intros; destruct Ξ, Γ; simpl in *; auto; try tauto; LGC H0 H.
Qed.

Ltac EGR H H1 := destruct (OrdR1 H H1).
Ltac ELR H H1 := destruct (OrdR2 H H1).
Ltac LGR H H1 := destruct (OrdR3 H H1).

Definition IGE_R Ξ Γ := Ξ > Γ \/ Ξ = Γ.
Notation " Ξ ≧ Γ " := (IGE_R Ξ Γ).

Definition ILE_R Ξ Γ := Ξ < Γ \/ Ξ = Γ.
Notation " Ξ ≦ Γ " := (ILE_R Ξ Γ).

Lemma OrdR4 : ∀ {Ξ Γ}, Ξ ≦ Γ -> Ξ > Γ -> False.
Proof.
  intros; destruct H; try LGR H H0; EGR H H0.
Qed.

Ltac LEGR H H1 := destruct (OrdR4 H H1).

Lemma OrdR5 : ∀ {Ξ Γ}, Ξ ≦ Γ -> Γ ≦ Ξ -> Ξ = Γ.
Proof.
  intros; destruct H; auto; LEGR H0 H.
Qed.

Ltac LEGER H H1 := pose proof (OrdR5 H H1).

Theorem Theorem168 : ∀ Ξ Γ, Ξ ≧ Γ -> Γ ≦ Ξ.
Proof.
  intros; red in H; red; destruct H; auto.
Qed.

Theorem Theorem168' : ∀ Ξ Γ, Ξ ≦ Γ -> Γ ≧ Ξ.
Proof.
  intros; red in H; red; destruct H; auto.
Qed.

Theorem Theorem169 : ∀ ξ, (P ξ) > O.
Proof.
  intros; simpl; auto.
Qed.

Theorem Theorem169' : ∀ ξ, (N ξ) < O.
Proof.
  intros; simpl; auto.
Qed.

Theorem Theorem170 : ∀ Ξ, | Ξ | ≧ O.
Proof.
  intros; red; destruct Ξ; simpl; tauto.
Qed.

Theorem Theorem170' : ∀ z, O ≦ |z|.
Proof.
  intros. apply Theorem168, Theorem170.
Qed.

Theorem Theorem171 : ∀ Ξ Γ Θ, Ξ < Γ -> Γ < Θ -> Ξ < Θ.
Proof.
  intros; destruct Ξ, Γ, Θ; elim H; elim H0; intros; auto;
  red in H; red in H0; red; eapply Theorem126; eauto.
Qed.

Theorem Theorem172 : ∀ Ξ Γ Θ,
  (Ξ ≦ Γ /\ Γ < Θ) \/ (Ξ < Γ /\ Γ ≦ Θ) -> Ξ < Θ.
Proof.
  intros; destruct H as [[[H | H] H0] | [H [H0 | H0]]].
  - eapply Theorem171; eauto.
  - rewrite H; auto.
  - eapply Theorem171; eauto.
  - rewrite <- H0; auto.
Qed.

Theorem Theorem173 : ∀ Ξ Γ Θ, Ξ ≦ Γ -> Γ ≦ Θ -> Ξ ≦ Θ.
Proof.
  intros; unfold ILE_R in *; destruct H.
  - left; eapply Theorem172; eauto.
  - rewrite <- H in H0; auto.
Qed.

Definition Is_rational Ξ := 
  match Ξ with
   | P ξ => ∃ X :Rat, ξ ≈ X*
   | O => True
   | N ξ => ∃ X :Rat, ξ ≈ X*
  end.

Definition Is_irrational Ξ := ~ (Is_rational Ξ).

Definition Is_integer Ξ := 
  match Ξ with
   | P ξ => ∃ x :Nat, ξ ≈ x*
   | O => True
   | N ξ => ∃ x :Nat, ξ ≈ x*
  end.

Theorem Theorem174 : ∀ x, Is_integer x -> Is_rational x.
Proof.
  intros; destruct x; repeat red in H;
  destruct H; repeat red; eauto.
Qed.

(* SECTION III Addition *)

Lemma Ccase : ∀ ξ η, {IGT_C η ξ} + {IGT_C ξ η} + {ξ ≈ η}.
Proof.
  intros; destruct (classicT (ξ ≈ η)),(classicT (IGT_C ξ η)); auto.
  left; left; destruct (Theorem123 ξ η) as [H | [H | H]]; tauto.
Qed.

Definition Plus_R Ξ Γ : Real :=
  match Ξ, Γ with 
   | P ξ, P η => P (ξ + η)
   | N ξ, N η => N (ξ + η)
   | O, _ => Γ
   | _, O => Ξ
   | P ξ, N η => match Ccase ξ η with
                  | inright _ => O
                  | inleft (left l) => N ((η - ξ) l)
                  | inleft (right l) => P ((ξ - η) l)
                 end
   | N ξ, P η => match Ccase ξ η with
                  | inright _ => O
                  | inleft (left l) => P ((η - ξ) l)
                  | inleft (right l) => N ((ξ - η) l)
                 end
  end.
Notation " Ξ + Γ " := (Plus_R Ξ Γ).

Theorem Theorem175 : ∀ Ξ Γ, Ξ + Γ = Γ + Ξ.
Proof.
  intros; destruct Ξ, Γ; simpl; try rewrite (eq2 Theorem130); auto.
  - destruct (Ccase c c0) as [[A|A]|A], (Ccase c0 c) as [[B|B]|B]; auto;
    [LGC A B|rewrite (proof_irr A B); auto|EGC B A|
     rewrite (proof_irr A B); auto|LGC A B|ELC B A|EGC A B|ELC A B].
  - destruct (Ccase c c0) as [[A|A]|A], (Ccase c0 c) as [[B|B]|B]; auto;
    [LGC A B|rewrite (proof_irr A B); auto|EGC B A|
     rewrite (proof_irr A B); auto|LGC A B|ELC B A|EGC A B|ELC A B].
Qed.

Theorem Theorem175' : ∀ Ξ, Ξ + O = Ξ.
Proof.
  intros; rewrite Theorem175; simpl; auto.
Qed.

Theorem Theorem175'' : ∀ Ξ, O + Ξ = Ξ.
Proof.
  intros; simpl; auto.
Qed.

Hint Rewrite Theorem175' Theorem175'' : Real.
Ltac Simpl_R := autorewrite with Real; auto.
Ltac Simpl_Rin H := autorewrite with Real in H; auto.

Definition minus_R Ξ := 
  match Ξ with
   | O => O
   | P ξ => N ξ
   | N ξ => P ξ
  end.
Notation " - Ξ " := (minus_R Ξ).

Theorem Theorem176_1 : ∀ Ξ, Ξ > O -> -Ξ < O.
Proof.
  intros; destruct Ξ; simpl; elim H; auto.
Qed.

Theorem Theorem176_2 : ∀ Ξ, Ξ = O -> -Ξ = O.
Proof.
  intros; rewrite H; simpl; auto.
Qed.

Theorem Theorem176_3 : ∀ Ξ, Ξ < O -> -Ξ > O.
Proof.
  intros; destruct Ξ; simpl; elim H; auto.
Qed.

Theorem Theorem176_1' : ∀ Ξ, -Ξ < O -> Ξ > O.
Proof.
  intros; destruct Ξ; simpl; elim H; auto.
Qed.

Theorem Theorem176_2' : ∀ Ξ, -Ξ = O -> Ξ = O.
Proof.
  intros; destruct Ξ; simpl; auto; inversion H.
Qed.

Theorem Theorem176_3' : ∀ Ξ, -Ξ > O -> Ξ < O.
Proof.
  intros; destruct Ξ; simpl; elim H; auto.
Qed.

Theorem Theorem177 : ∀ Ξ, -(-Ξ) = Ξ.
Proof.
  intros; destruct Ξ; simpl; auto.
Qed.

Theorem Theorem178 : ∀ Ξ, |(-Ξ)| = |Ξ|.
Proof.
  intros; destruct Ξ; simpl; auto.
Qed.

Theorem Theorem179 : ∀ Ξ, (Ξ + (-Ξ)) = O.
Proof. 
  intros; destruct Ξ; simpl; auto.
  - destruct (Ccase c c) as [[A|A]|A]; try apply Theorem163;
    [EGC (Theorem116 c) A|EGC (Theorem116 c) A].
  - destruct (Ccase c c) as [[A|A]|A]; try apply Theorem163;
    [EGC (Theorem116 c) A|EGC (Theorem116 c) A].
Qed.

Theorem Theorem179' : ∀ Ξ, ((-Ξ) + Ξ) = O.
Proof.
  intros; rewrite Theorem175; apply Theorem179.
Qed.

Hint Rewrite Theorem177 Theorem179 Theorem179' : Real.

Theorem Theorem180 : ∀ Ξ Γ, -(Ξ + Γ) = (-Ξ) + (-Γ).
Proof.
  intros; destruct Ξ, Γ; simpl; auto;
  destruct (Ccase c c0) as [[A|A]|A], (Ccase c0 c) as [[B|B]|B];
  try apply Theorem163.
Qed.

Definition Minus_R Ξ Γ := Ξ + (-Γ).
Notation " Ξ - Γ " := (Minus_R Ξ Γ).

Corollary RMia : ∀ Ξ, (Ξ - Ξ) = O.
Proof.
  intros; apply Theorem179.
Qed.

Corollary RMib : ∀ Ξ, (Ξ - O) = Ξ.
Proof.
  intros; unfold Minus_R; Simpl_R.
Qed.

Corollary RMic : ∀ Ξ Γ , Ξ + (-Γ) = Ξ - Γ.
Proof.
  intros; unfold Minus_R; auto.
Qed.

Corollary RMid : ∀ Ξ Γ, Ξ - (-Γ) = Ξ + Γ.
Proof.
  intros. unfold Minus_R. now rewrite Theorem177.
Qed.

Hint Rewrite RMia RMib RMic RMid : Real.

Theorem Theorem181 : ∀ Ξ Γ, -(Ξ - Γ) = Γ - Ξ.
Proof.
 intros. unfold Minus_R; rewrite Theorem180, Theorem177.
 apply Theorem175.
Qed.

Theorem Theorem182_1 : ∀ Ξ Γ, (Ξ - Γ) > O -> Ξ > Γ.
Proof.
  intros; destruct Ξ, Γ; simpl; auto; simpl in H;
  destruct (Ccase c c0) as [[A|A]|A], H; auto.
Qed.

Theorem Theorem182_2 : ∀ Ξ Γ, Ξ - Γ = O -> Ξ = Γ.
Proof.
  intros; destruct Ξ, Γ; simpl in *; auto; inversion H;
  destruct (Ccase c c0) as [[A|A]|A];
  inversion H; rewrite (eq2 A); auto.
Qed.

Theorem Theorem182_3 : ∀ Ξ Γ, (Ξ - Γ) < O -> Ξ < Γ.
Proof.
  intros; apply Theorem182_1; apply Theorem176_3 in H.
  rewrite Theorem181 in H; auto.
Qed.

Theorem Theorem182_1' : ∀ Ξ Γ, Ξ > Γ -> (Ξ - Γ) > O.
Proof.
  intros; destruct Ξ, Γ; simpl; auto.
  - destruct (Ccase c c0) as [[A|A]|A]; auto; simpl in *.
    + LGC H A. + EGC A H.
  - destruct (Ccase c c0) as [[A|A]|A]; auto; simpl in *.
    + LGC H A. + ELC A H.
Qed.

Theorem Theorem182_2' : ∀ Ξ Γ, Ξ = Γ -> (Ξ - Γ) = O.
Proof.
  intros; subst Ξ; destruct Γ; simpl; auto;
  destruct (Ccase c c) as [[A|A]|A]; auto; EGC (Theorem116 c) A.
Qed.

Theorem Theorem182_3' : ∀ Ξ Γ, Ξ < Γ -> (Ξ - Γ) < O.
Proof.
  intros; apply Theorem182_1' in H; apply Theorem176_1 in H.
  unfold Minus_R in H; now rewrite 
    Theorem180, Theorem177, Theorem175 in H.
Qed.

Theorem Theorem183_1 : ∀ Ξ Γ, Ξ > Γ -> -Γ > -Ξ.
Proof.
  intros; destruct Ξ, Γ; simpl; auto.
Qed.

Theorem Theorem183_2 : ∀ Ξ Γ, Ξ = Γ -> -Ξ = -Γ.
Proof.
  intros; rewrite H; auto.
Qed.

Theorem Theorem183_3 : ∀ Ξ Γ, Ξ < Γ -> -Γ < -Ξ.
Proof.
  intros; apply Theorem183_1; auto.
Qed.

Theorem Theorem183_1' : ∀ Ξ Γ, -Γ > -Ξ -> Ξ > Γ.
Proof.
  intros; destruct Ξ, Γ; simpl; auto.
Qed.

Theorem Theorem183_2' : ∀ Ξ Γ,  -Ξ = -Γ -> Ξ = Γ.
Proof.
  intros; rewrite <- Theorem177, <- (Theorem177 Ξ), H; auto.
Qed.

Theorem Theorem183_3' : ∀ Ξ Γ, -Γ < -Ξ -> Ξ < Γ.
Proof.
  intros; apply Theorem183_1'; auto.
Qed.

Theorem Theorem184 : ∀ Ξ, ∃ ξ η, Ξ = (P ξ) - (P η).
Proof.
  intros; destruct Ξ.
  - exists 1, 1; unfold Minus_R; rewrite Theorem179; auto.
  - exists (Plus_C c 1), 1; simpl.
    pose proof (Theorem133 1 c); rewrite (eq2 Theorem130) in H.
    destruct (Ccase (Plus_C c 1) 1) as [[A|A]|A]; Simpl_C; [LGC A H|EGC A H].
  - exists 1,(Plus_C c 1); simpl.
    pose proof (Theorem133 1 c); rewrite (eq2 Theorem130) in H.
    destruct (Ccase 1 (Plus_C c 1)) as [[A|A]|A]; Simpl_C; [LGC A H|ELC A H].
Qed.

Lemma Theorem185Pa : ∀ {Ξ Γ ξ}, (P ξ) = Ξ - Γ -> Ξ > Γ.
Proof.
  intros; apply Theorem182_1; rewrite <- H; simpl; auto.
Qed.

Lemma Theorem185Pb : ∀ {Ξ Γ ξ}, (N ξ) = Ξ - Γ -> Ξ < Γ.
Proof.
  intros; apply Theorem183_2 in H; simpl in H.
  rewrite Theorem181 in H; apply Theorem185Pa in H; auto.
Qed.

Theorem Theorem185P1 : ∀ {ξ η ζ1 ζ2 υ1 υ2}, 
  (P ξ) = (P ζ1) - (P ζ2) -> (P η) = (P υ1) - (P υ2)
  -> (P ξ) + (P η) = ((P ζ1) + (P υ1)) - ((P ζ2) + (P υ2)).
Proof.
  intros; generalize H, H0; intros.
  apply Theorem185Pa in H; apply Theorem185Pa in H0.
  simpl in H; simpl in H0; rewrite H1, H2.
  pose proof (Theorem137 H H0). unfold Minus_R.
  simpl minus_R; simpl Plus_R at 5; simpl Plus_R at 2.
  destruct (Ccase ζ1 ζ2) as [[A|A]|A]; [LGC H A| |EGC A H].
  simpl Plus_R at 2. destruct (Ccase υ1 υ2) as [[B|B]|B];
  [LGC H0 B| |EGC B H0]. simpl Plus_R at 2.
  destruct (Ccase (Plus_C ζ1 υ1) (Plus_C ζ2 υ2))
    as [[C|C]|C]; [LGC H3 C| |EGC C H3]. simpl; apply eq3; simpl.
  apply Theorem136_2 with (ζ:=(Plus_C ζ2 υ2)); Simpl_C.
  rewrite (eq2 (@Theorem130 ζ2 υ2)), (eq2 Theorem131).
  rewrite <- (eq2 (@Theorem131 _ υ2 ζ2)); Simpl_C.
  rewrite (eq2 (@Theorem130 υ1 ζ2)), <- (eq2 Theorem131).
  Simpl_C; apply Theorem116.
Qed.

Theorem Theorem185P2 : ∀ {Ξ ζ1 ζ2 υ1 υ2},
  O = (P ζ1) - (P ζ2) -> Ξ = (P υ1) - (P υ2)
  -> O + Ξ = ((P ζ1) + (P υ1)) - ((P ζ2) + (P υ2)).
Proof.
  intros; apply Theorem164 in H; apply Theorem182_2 in H.
  destruct Ξ; simpl Plus_R at 1.
  - apply Theorem164 in H0; apply Theorem182_2 in H0.
    rewrite H, H0; apply Theorem164; apply Theorem182_2'; auto.
  - rewrite H; apply Theorem165 with (Γ:=((P υ1) - (P υ2))); auto.
    apply Theorem185Pa in H0; repeat simpl in H.
    assert (IGT_C (Plus_C ζ2 υ1) (Plus_C ζ2 υ2)).
    { rewrite (eq2 Theorem130), (eq2 (@Theorem130 ζ2 υ2)).
      apply Theorem135_1; auto. }
    unfold Minus_R; simpl minus_R; simpl Plus_R at 3.
    simpl Plus_R at 1. destruct (Ccase υ1 υ2) as [[A|A]|A];
    [LGC H0 A| |EGC A H0]. simpl Plus_R at 1.
    destruct (Ccase (Plus_C ζ2 υ1) (Plus_C ζ2 υ2))
      as [[B|B]|B]; [LGC B H1| |EGC B H1]. apply eq3; simpl.
    apply Theorem136_2 with (ζ:=(Plus_C ζ2 υ2)); Simpl_C.
    rewrite (eq2 (@Theorem130 ζ2 υ2)), <- (eq2 Theorem131).
    Simpl_C. rewrite (eq2 Theorem130); apply Theorem116.
  - rewrite H; apply Theorem165 with (Γ:=((P υ1) - (P υ2))); auto.
    apply Theorem185Pb in H0; simpl in H0; simpl in H0.
    assert (IGT_C (Plus_C ζ2 υ2) (Plus_C ζ2 υ1)).
    { rewrite (eq2 Theorem130), (eq2 (@Theorem130 ζ2 υ1)).
      apply Theorem135_1; auto. }
    unfold Minus_R; simpl minus_R; simpl Plus_R at 3.
    simpl Plus_R at 1. destruct (Ccase υ1 υ2) as [[A|A]|A];
    [|LGC H0 A|ELC A H0]. simpl Plus_R.
    destruct (Ccase (Plus_C ζ2 υ1) (Plus_C ζ2 υ2))
      as [[B|B]|B]; [|LGC H1 B|ELC B H1]. apply eq3.
    apply Theorem136_2 with (ζ:=(Plus_C ζ2 υ1)); Simpl_C.
    rewrite (eq2 (@Theorem130 ζ2 υ1)), <- (eq2 Theorem131).
    Simpl_C. rewrite (eq2 Theorem130); apply Theorem116.
Qed.

Theorem Theorem185P3 : ∀ {ξ η ζ1 ζ2 υ1 υ2},
  (P ξ) = (P ζ1) - (P ζ2) -> (N η) = (P υ1) - (P υ2) ->
  (P ξ) + (N η) = ((P ζ1) + (P υ1)) - ((P ζ2) + (P υ2)).
Proof.
  assert (∀ {ζ1 ζ2 υ1 υ2} l1 l2,
    (Minus_C ζ1 ζ2 l1) ≈ (Minus_C υ2 υ1 l2) <-> 
    (Plus_C ζ1 υ1) ≈ (Plus_C ζ2 υ2)) as G1.
  { split; intros.
    - apply (Theorem135_2 _ _ υ1) in H; Simpl_Cin H. rewrite
        (eq2 Theorem130) in H; apply (Theorem135_2 _ _ ζ2) in H.
      rewrite (eq2 Theorem131) in H; Simpl_Cin H.
      rewrite (eq2 Theorem130), (eq2 (@Theorem130 ζ2 υ2)); auto.
    - apply (Theorem136_2 _ _ υ1); Simpl_C.
      rewrite (eq2 Theorem130). apply (Theorem136_2 _ _ ζ2).
      rewrite (eq2 Theorem131); Simpl_C.
      rewrite (eq2 Theorem130), (eq2 (@Theorem130 υ2 ζ2)); auto. }
  assert (∀ {ζ1 ζ2 υ1 υ2} l1 l2,
    IGT_C (Minus_C ζ1 ζ2 l1) (Minus_C υ2 υ1 l2) ->
    IGT_C (Plus_C ζ1 υ1) (Plus_C ζ2 υ2)) as G2.
  { intros; apply (Theorem135_1 _ _ υ1) in H; Simpl_Cin H. rewrite
      (eq2 Theorem130) in H; apply (Theorem135_1 _ _ ζ2) in H.
    rewrite (eq2 Theorem131) in H; Simpl_Cin H.
    rewrite (eq2 Theorem130), (eq2 (@Theorem130 ζ2 υ2)); auto. }
  intros; generalize H, H0; intros.
  apply Theorem185Pa in H; apply Theorem185Pb in H0.
  simpl in H0, H; rewrite H1, H2. pose proof (Theorem137 H H0).
  unfold Minus_R; simpl minus_R; simpl Plus_R at 5.
  simpl Plus_R at 2. destruct (Ccase ζ1 ζ2) as [[A|A]|A];
  [LGC H A| |EGC A H]. apply eq3; simpl Plus_R at 2.
  destruct (Ccase υ1 υ2) as [[B|B]|B]; [|LGC H0 B|ELC B H0].
  simpl; destruct (Ccase(Plus_C ζ1 υ1)(Plus_C ζ2 υ2)) as [[C|C]|C],
    (Ccase (Minus_C ζ1 ζ2 A) (Minus_C υ2 υ1 B)) as [[D|D]|D];
  simpl; auto.
  - apply G1; rewrite (eq2 (@Theorem130 ζ1 υ1)).
    rewrite <- (eq2 Theorem131); Simpl_C.
    rewrite <- (eq2 Theorem131); Simpl_C.
    rewrite (eq2 Theorem130); apply Theorem116.
  - apply G2 in D; LGC D C.
  - apply G1 in D; ELC D C.
  - apply G2 in D; rewrite (eq2 Theorem130) in D.
    rewrite (eq2 (@Theorem130 υ1 ζ1)) in D; LGC C D.
  - apply G1; rewrite <- (eq2 Theorem131); Simpl_C.
    rewrite (eq2 (@Theorem130 ζ1 υ1)),<- (eq2 Theorem131); Simpl_C.
    rewrite (eq2 Theorem130); apply Theorem116.
  - apply G1 in D; EGC D C.
  - apply G2 in D; rewrite (eq2 Theorem130) in D.
    rewrite (eq2 (@Theorem130 υ1 ζ1)) in D; ELC C D.
  - apply G2 in D; EGC C D.
Qed.

Theorem Theorem185 : ∀ {Ξ Γ ζ1 ζ2 υ1 υ2}, 
  Ξ = (P ζ1) - (P ζ2) -> Γ = (P υ1) - (P υ2)
  -> Ξ + Γ = ((P ζ1) + (P υ1)) - ((P ζ2) + (P υ2)).
Proof.
  intros; destruct Ξ.
  - apply Theorem185P2; auto.
  - destruct Γ.
    + rewrite (Theorem175 _ (P υ1)), (Theorem175 _ (P υ2)).
      apply Theorem185P2; auto.
    + apply Theorem185P1; auto. + apply Theorem185P3; auto.
  - destruct Γ.
    + rewrite (Theorem175 _ (P υ1)), (Theorem175 _ (P υ2)).
      apply Theorem185P2; auto.
    + rewrite Theorem175, (Theorem175 _ (P υ1)),
        (Theorem175 _ (P υ2)). apply Theorem185P3; auto.
    + apply Theorem183_2 in H; apply Theorem183_2 in H0.
      apply Theorem183_2'; rewrite Theorem181 in H0.
      rewrite Theorem181 in H; rewrite Theorem181, Theorem180.
      simpl minus_R in *; apply Theorem185P1; auto.
Qed.

Theorem Theorem186 : ∀ Ξ Γ Θ, (Ξ + Γ) + Θ = Ξ + (Γ + Θ).
Proof.
  intros; generalize (Theorem184 Ξ),(Theorem184 Γ),(Theorem184 Θ).
  intros. destruct H as [ζ1 [ζ2 H]],
    H0 as [υ1 [υ2 H0]], H1 as [c1 [c2 H1]].
  generalize (Theorem185 H H0), (Theorem185 H0 H1); intros.
  generalize (Theorem185 H2 H1), (Theorem185 H H3); intros.
  simpl Plus_R in H4; simpl Plus_R in H5.
  repeat rewrite (eq2 Theorem131) in H4.
  apply Theorem164 in H5; eapply Theorem165; eauto.
Qed.

Corollary RMi1 : ∀ Ξ Γ, (Ξ - Γ) + Γ = Ξ.
Proof.
  intros; unfold Minus_R; rewrite Theorem186; Simpl_R.
Qed.

Corollary RMi1' : ∀ Ξ Γ, Γ + (Ξ - Γ) = Ξ.
Proof.
  intros; rewrite Theorem175; apply RMi1.
Qed.

Corollary RMi2 : ∀ Ξ Γ, (Ξ + Γ) - Γ = Ξ.
Proof.
  intros; unfold Minus_R; rewrite Theorem186; Simpl_R.
Qed.

Corollary RMi2' : ∀ Ξ Γ, (Γ + Ξ) - Γ = Ξ.
Proof.
  intros; rewrite Theorem175; apply RMi2.
Qed.

Corollary RMi3 : ∀ Ξ Γ, Γ - (Γ - Ξ) = Ξ.
Proof.
  intros; unfold Minus_R; rewrite Theorem175, (Theorem175 Γ _).
  rewrite Theorem180; Simpl_R; rewrite RMi1; auto.
Qed.

Hint Rewrite RMi1 RMi1' RMi2 RMi2' RMi3 : Real.

Theorem Theorem187_1 : ∀ Ξ Γ, ∃ Θ, Γ + Θ = Ξ.
Proof.
  intros; exists (Ξ - Γ); rewrite Theorem175; Simpl_R.
Qed.

Theorem Theorem187_2 : ∀ Ξ Γ Θ, Γ + Θ = Ξ -> Ξ - Γ = Θ.
Proof.
  intros; unfold Minus_R.
  rewrite Theorem175, <- H, <- Theorem186; Simpl_R.
Qed.

Theorem Theorem188_1 : ∀ Ξ Γ Θ, Ξ + Θ > Γ + Θ -> Ξ > Γ.
Proof.
  intros; apply Theorem182_1' in H; apply Theorem182_1.
  unfold Minus_R in H; rewrite Theorem180 in H.
  rewrite (Theorem175 (-Γ) _), Theorem186 in H.
  rewrite <- (Theorem186 Θ _ _) in H; Simpl_Rin H.
Qed.

Theorem Theorem188_2 : ∀ Ξ Γ Θ, Ξ + Θ = Γ + Θ -> Ξ = Γ.
Proof.
  intros; apply Theorem182_2' in H; apply Theorem182_2.
  unfold Minus_R in H; rewrite Theorem180 in H.
  rewrite (Theorem175 (-Γ) _), Theorem186 in H.
  rewrite <- (Theorem186 Θ _ _) in H; Simpl_Rin H.
Qed.

Theorem Theorem188_3 : ∀ Ξ Γ Θ, Ξ + Θ < Γ + Θ -> Ξ < Γ.
Proof.
  intros; eapply Theorem188_1; eauto.
Qed.

Theorem Theorem188_1' : ∀ Ξ Γ Θ, Ξ > Γ -> Ξ + Θ > Γ + Θ.
Proof.
  intros; apply Theorem182_1' in H; apply Theorem182_1.
  unfold Minus_R; rewrite Theorem180.
  pattern ((-Γ) + (- Θ)); rewrite Theorem175, Theorem186.
  pattern (Θ + (- Θ + - Γ)); rewrite <- Theorem186; Simpl_R.
Qed.

Theorem Theorem188_2' : ∀ Ξ Γ Θ, Ξ = Γ -> Ξ + Θ = Γ + Θ.
Proof.
  intros; rewrite H; auto.
Qed.

Theorem Theorem188_3' : ∀ Ξ Γ Θ, Ξ < Γ -> Ξ + Θ < Γ + Θ.
Proof.
  intros; eapply Theorem188_1'; eauto.
Qed.

Corollary LePl_R : ∀ x y z, x ≦ y <-> x + z ≦ y + z.
Proof.
  split; intros; destruct H.
  - left; apply Theorem188_1'; auto. - right; rewrite H; auto.
  - left; eapply Theorem188_1; eauto.
  - right; eapply Theorem188_2; eauto.
Qed.

Theorem Theorem189 : ∀ {Ξ Γ Θ Φ}, Ξ > Γ -> Θ > Φ -> Ξ + Θ > Γ + Φ.
Proof.
  intros; apply Theorem171 with (Γ:=(Γ + Θ)).
  - rewrite Theorem175,(Theorem175 Γ Θ); apply Theorem188_3'; auto.
  - apply Theorem188_3'; auto.
Qed.

Theorem Theorem190 : ∀ Ξ Γ Θ Φ,
  (Ξ ≧ Γ /\ Θ > Φ) \/ (Ξ > Γ /\ Θ ≧ Φ) -> Ξ + Θ > Γ + Φ.
Proof.
  intros; destruct H as [[[H | H] H0] | [H [H0 | H0]]].
  - apply Theorem189; auto.
  - rewrite H, Theorem175,(Theorem175 Γ Φ).
    apply Theorem188_3'; auto.
  - apply Theorem189; auto.
  - rewrite H0; apply Theorem188_1'; auto.
Qed.

Theorem Theorem191 : ∀ {Ξ Γ Θ Φ},
  Ξ ≧ Γ -> Θ ≧ Φ -> (Ξ + Θ) ≧ (Γ + Φ).
Proof.
  intros; destruct H.
  - left; apply Theorem190; auto.
  - destruct H0.
    + left; apply Theorem190; left; split; red; tauto.
    + right; rewrite H, H0; apply Theorem163.
Qed.

Theorem Theorem191' : ∀ {Ξ Γ Θ Φ},
  Ξ ≦ Γ -> Θ ≦ Φ -> (Ξ + Θ) ≦ (Γ + Φ).
Proof.
  intros; apply Theorem168, Theorem191; apply Theorem168'; auto.
Qed.

(* SECTION IV Multiplication *)

Definition Times_R Ξ Γ : Real :=
  match Ξ, Γ with 
   | P ξ , P η => P (ξ · η)
   | N ξ , N η => P (ξ · η)
   | P ξ, N η => N (ξ · η)
   | N ξ, P η => N (ξ · η)
   | _ , _ => O
  end.

Notation " Ξ · Γ " := (Times_R Ξ Γ).

Theorem Theorem192 : ∀ Ξ Γ, Ξ · Γ = O -> Ξ = O \/ Γ = O.
Proof.
  intros; destruct Ξ, Γ; try tauto; inversion H.
Qed.

Theorem Theorem193 : ∀ Ξ Γ, |Ξ · Γ| = |Ξ| · |Γ|.
Proof.
  intros; destruct Ξ, Γ; simpl; auto; try apply Theorem116.
Qed.

Theorem Theorem194 : ∀ Ξ Γ, Ξ · Γ = Γ · Ξ.
Proof.
  intros; destruct Ξ, Γ; simpl; try rewrite (eq2 Theorem142); auto.
Qed.

Corollary RTi_O : ∀ Ξ, Ξ · O = O.
Proof.
  intros; rewrite Theorem194; simpl; auto.
Qed.

Corollary RTiO_ : ∀ Ξ, O · Ξ = O.
Proof.
  intros; simpl; auto.
Qed.

Hint Rewrite RTi_O RTiO_ : Real.

Coercion Real_PZ x := P (Cut_I x).

Theorem Theorem195 : ∀ Ξ, Ξ · 1 = Ξ.
Proof.
  intros; destruct Ξ; simpl; auto; Simpl_C.
Qed.

Theorem Theorem195' : ∀ Ξ, Ξ · (- (1))  = - Ξ.
Proof.
  intros; destruct Ξ; simpl; auto; Simpl_C.
Qed.

Corollary RTi1_ : ∀ Ξ, 1 · Ξ = Ξ.
Proof.
  intros; destruct Ξ; simpl; auto; Simpl_C.
Qed.

Corollary RTin1_ : ∀ Ξ, -(1) · Ξ = -Ξ.
Proof.
  intros; destruct Ξ; simpl; auto; Simpl_C.
Qed.

Hint Rewrite Theorem195 Theorem195' RTi1_ RTin1_ : Real.

Theorem Theorem196 : ∀ Ξ Γ, Ξ <> O -> 
  Ξ <> O -> Ξ · Γ = |Ξ| · |Γ| \/ Ξ · Γ = - (|Ξ| · |Γ|).
Proof.
  intros; destruct Ξ, Γ; simpl; tauto.
Qed.

Theorem Theorem197 : ∀ Ξ Γ, -Ξ · Γ = Ξ · -Γ.
Proof.
  intros; destruct Ξ, Γ; simpl; auto.
Qed.

Theorem Theorem197' : ∀ Ξ Γ, -Ξ · Γ = - (Ξ · Γ).
Proof.
  intros; destruct Ξ, Γ; simpl; auto.
Qed.

Theorem Theorem197'' : ∀ Ξ Γ, Ξ · -Γ = - (Ξ · Γ).
Proof.
  intros; destruct Ξ, Γ; simpl; auto.
Qed.

Theorem Theorem198 : ∀ Ξ Γ, -Ξ · -Γ = Ξ · Γ.
Proof.
  intros; destruct Ξ, Γ; simpl; auto.
Qed.

Theorem Theorem199 : ∀ Ξ Γ Θ, (Ξ · Γ) · Θ = Ξ · (Γ · Θ).
Proof.
  intros; destruct Ξ, Γ, Θ; simpl;
  try rewrite (eq2 Theorem143); auto.
Qed.

Theorem Theorem200 : ∀ ξ η ζ, 
  (P ξ) · ((P η) - (P ζ)) = ((P ξ) · (P η)) - ((P ξ) · (P ζ)).
Proof.
  intros; destruct (Theorem167 (P η) (P ζ)) as [H | [H |H]].
  - rewrite H; unfold Minus_R; repeat rewrite Theorem179; Simpl_R.
  - simpl in H; assert (ILT_C (Times_C ξ η) (Times_C ξ ζ)).
    { rewrite (eq2 Theorem142), (eq2 (@Theorem142 ξ ζ)).
      apply Theorem145_3; auto. } unfold Minus_R; simpl; 
    destruct (Ccase η ζ) as [[A|A]|A]; [|LGC H A|ELC A H].
    destruct (Ccase (Times_C ξ η) (Times_C ξ ζ)) 
      as [[B|B]|B]; [|LGC H0 B|ELC B H0].
    apply eq3; simpl; apply Theorem136_2 with (ζ:=(Times_C ξ η)).
    Simpl_C. rewrite <- (eq2 Theorem144).
    Simpl_C; apply Theorem116.
  - simpl in H; assert (ILT_C (Times_C ξ ζ) (Times_C ξ η)).
    { rewrite (eq2 Theorem142), (eq2 (@Theorem142 ξ η)).
      apply Theorem145_3; auto. } unfold Minus_R; simpl;
    destruct (Ccase η ζ) as [[A|A]|A]; [LGC H A| |EGC A H].
    destruct (Ccase (Times_C ξ η) (Times_C ξ ζ))
      as [[B|B]|B]; [LGC H0 B| |EGC B H0]. apply eq3; simpl.
    apply Theorem136_2 with (ζ:=(Times_C ξ ζ)); Simpl_C.
    rewrite <- (eq2 Theorem144); Simpl_C; apply Theorem116.
Qed.

Theorem Theorem201 : ∀ Ξ Γ Θ, Ξ · (Γ + Θ) = Ξ · Γ + Ξ · Θ.
Proof.
  assert (∀ Γ Θ ξ, (P ξ)·(Γ+Θ) = ((P ξ)·Γ)+((P ξ)·Θ)) as G; intros.
  { destruct (Theorem184 Θ) as [η1 [η2 H]],
      (Theorem184 Γ) as [ζ1 [ζ2 H0]]. rewrite (Theorem185 H0 H).
    simpl Plus_R at 1; simpl Plus_R at 1; rewrite Theorem200.
    simpl Times_R at 1; simpl Times_R at 1.
    repeat rewrite Lemma_T144_1; rewrite H, H0.
    repeat rewrite Theorem200; unfold Minus_R.
    rewrite <- Theorem186, (Theorem186 _ _ (P ξ · P η1)).
    rewrite (Theorem175 _ (P ξ · P η1));
    repeat rewrite <- Theorem186. simpl Times_R.
    simpl Plus_R at 4; simpl minus_R; rewrite Theorem186.
    simpl Plus_R at 3; repeat rewrite (eq2 Theorem144); auto. }
  intros; destruct Ξ; [simpl; auto|apply G|].
  apply Theorem183_2'; rewrite Theorem180.
  repeat rewrite <- Theorem197'', <- Theorem197.
  simpl minus_R; apply G.
Qed.

Theorem Theorem201' : ∀ Ξ Γ Θ, (Γ + Θ) · Ξ = Γ · Ξ +  Θ · Ξ.
Proof.
  intros; rewrite Theorem194, Theorem201,
    Theorem194, (Theorem194 Θ); auto.
Qed.

Theorem Theorem202 : ∀ Ξ Γ Θ, Ξ · (Γ - Θ) = (Ξ · Γ) - (Ξ · Θ).
Proof.
  intros; unfold Minus_R; rewrite Theorem201, Theorem197''.
  apply Theorem163.
Qed.

Theorem Theorem202' : ∀ Ξ Γ Θ, (Γ - Θ) · Ξ = (Γ · Ξ) - (Θ · Ξ).
Proof.
  intros; rewrite Theorem194, (Theorem194 Γ Ξ), (Theorem194 Θ Ξ).
  apply Theorem202.
Qed.

Theorem Theorem203_1 : ∀ Ξ Γ Θ, Ξ > Γ -> Θ > O -> Ξ · Θ > Γ · Θ.
Proof.
   intros; apply Theorem182_1' in H. assert ((Ξ - Γ) · Θ > O).
   { destruct (Ξ - Γ); destruct Θ, H, H0; simpl; auto. }
   rewrite Theorem194, Theorem202 in H1; apply Theorem182_1 in H1.
   rewrite Theorem194, (Theorem194 Γ Θ); auto.
Qed.

Theorem Theorem203_1' : ∀ Ξ Γ Θ, Ξ · Θ > Γ · Θ -> Θ > O -> Ξ > Γ.
Proof.
  intros; destruct Θ; inversion H0; destruct Ξ,Γ; simpl in H; auto;
  apply Theorem146_3 with (ζ:=c); auto.
Qed.

Theorem Theorem203_2 : ∀ Ξ Γ Θ, Ξ > Γ -> Θ = O -> Ξ · Θ = Γ · Θ.
Proof.
  intros; rewrite H0; Simpl_R.
Qed.

Theorem Theorem203_3 : ∀ Ξ Γ Θ, Ξ > Γ -> Θ < O -> Ξ · Θ < Γ · Θ.
Proof.
  intros; rewrite <- Theorem198, <- (Theorem198 Γ Θ).
  apply Theorem203_1; try (apply Theorem183_3; auto).
  destruct Θ; simpl; auto.
Qed.

Theorem Theorem204_1 : ∀ {Γ Θ1 Θ2}, Γ<>O -> Γ·Θ1 = Γ·Θ2 -> Θ1 = Θ2.
Proof.
  intros; apply Theorem182_2' in H0.
  rewrite <- Theorem202 in H0; apply Theorem192 in H0.
  destruct H0; try tauto; apply Theorem182_2 in H0; auto.
Qed.

Definition neq_zero Ξ := 
  match Ξ with
   | O => False
   | _ => True
  end.

Corollary uneqO : ∀ {x}, x <> O -> neq_zero x.
Proof.
  intros. destruct x; simpl; auto.
Qed.

Definition Over_R Ξ Γ : (neq_zero Γ) -> Real := 
  match Γ with
   | O => λ l, match l with end
   | P ξ => λ _, (P (1/ξ)) · Ξ
   | N ξ => λ _, (N (1/ξ)) · Ξ
  end.
Notation " X / Y " := (Over_R X Y).

Corollary Rdt : ∀ Ξ Γ l, Γ · ((Ξ/Γ) l) = Ξ.
Proof.
  intros; destruct Ξ, Γ; simpl; destruct l; auto;
  rewrite <- (eq2 Theorem143), (eq2 (@Theorem142 c0 _)); Simpl_C.
Qed.

Theorem Theorem204_2 : ∀ Ξ Γ, Γ <> O -> ∃ Θ, Γ · Θ = Ξ.
Proof.
  intros. exists ((Ξ/Γ) (uneqO H)). apply Rdt.
Qed.

Corollary ROv_uni : ∀ x y z l, y · z = x <-> z = (x / y) l.
Proof.
  split; intros.
  - apply (@Theorem204_1 y).
    + intro; destruct y; inversion H0; tauto.
    + rewrite H. symmetry. apply Rdt.
  - rewrite H. apply Rdt.
Qed.

Corollary Rdt' : ∀ Ξ Γ l, ((Ξ/Γ) l)·Γ = Ξ.
Proof.
  intros; destruct Ξ, Γ; simpl; destruct l; auto;
  rewrite (eq2 Theorem142), <- (eq2 Theorem143),
  (eq2 (@Theorem142 c0 (Over_C 1 c0))); Simpl_C.
Qed.

Corollary Rtd : ∀ Ξ Γ l, ((Ξ·Γ)/Γ) l = Ξ.
Proof.
  intros; destruct Ξ, Γ; simpl; auto; destruct l;
  rewrite (eq2 Theorem142), (eq2 Theorem143),
  (eq2 (@Theorem142 c0 (Over_C 1 c0))); Simpl_C.
Qed.

Hint Rewrite Rdt Rdt' Rtd : Real.

Corollary Rtd' : ∀ Ξ Γ l, ((Γ · Ξ) / Γ) l = Ξ.
Proof.
  intros; rewrite Theorem194; Simpl_R.
Qed.

Corollary Rd : ∀ Ξ l, (Ξ/Ξ) l = 1.
Proof.
  intros; destruct Ξ; simpl; destruct l; Simpl_C.
Qed.

Corollary RdO_ : ∀ x l, (O/x) l = O.
Proof.
  intros; destruct x; inversion l; auto.
Qed.

Lemma Rd1_ : ∀ a l, (a/1) l = a.
Proof.
  intros; symmetry; apply ROv_uni; Simpl_R.
Qed.

Hint Rewrite Rdt' Rtd' Rd RdO_ Rd1_ : Real.

Corollary Di_Rt : ∀ x y z l, x·(y/z) l = (x·y/z) l.
Proof.
  intros; destruct x, y, z; elim l; simpl; auto; now rewrite
    (eq2 Theorem142), (eq2 Theorem143), (eq2 (@Theorem142 _ c)).
Qed.

Corollary Di_Rp : ∀ x y z l, (x/z) l + (y/z) l = ((x+y)/z) l.
Proof.
  intros; rewrite <- (Theorem195 x), <- (Theorem195 y).
  repeat rewrite <- Di_Rt; rewrite <- Theorem201', Di_Rt; Simpl_R.
Qed.

Corollary Di_Rm : ∀ x y z l, (x/z) l - (y/z) l = ((x-y)/z) l.
Proof.
  intros; rewrite <- (Theorem195 x), <- (Theorem195 y).
  repeat rewrite <- Di_Rt; rewrite <- Theorem202', Di_Rt; Simpl_R.
Qed.
