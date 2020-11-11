(***************************************************************************)
(*   This is part of FA_Landau, it is distributed under the terms of the   *)
(*             GNU Lesser General Public License version 3                 *)
(*                (see file LICENSE for more details)                      *)
(*                                                                         *)
(*           Copyright 2020-2022: Yaoshun Fu and Wensheng Yu.              *)
(***************************************************************************)

(* Complex Numbers *)

(* SECTION I Definition *)

Require Export reals.

Inductive Cn := Pair : Real -> Real -> Cn.
Notation " [ Ξ , Γ ] " := (Pair Ξ Γ)(at level 0).

Corollary eq4 : ∀ Ξ1 Ξ2 Γ1 Γ2,
  [Ξ1, Ξ2] = [Γ1, Γ2] <-> Ξ1 = Γ1 /\ Ξ2 = Γ2.
Proof.
  intros; split; intros.
  - inversion H; auto.
  - destruct H; rewrite H, H0; auto.
Qed.

Theorem Theorem206 : ∀ α :Cn, α = α.
Proof.
  intros; auto.
Qed.

Theorem Theorem207 : ∀ (α β :Cn), α = β -> β = α.
Proof.
  intros; auto.
Qed.

Theorem Theorem208 : ∀ (α β δ :Cn), α = β -> β = δ -> α = δ.
Proof.
  intros; subst β; auto.
Qed.

Definition nC := [O, O].

Definition eC := [1, O].

(* SECTION II Addition *)

Definition Plus_Cn α β := 
  match α, β with [Ξ1, Ξ2], [Γ1, Γ2] 
   => [Ξ1 + Γ1, Ξ2 + Γ2] 
  end. 

Notation " α +# β " := (Plus_Cn α β)(at level 50).

Theorem Theorem209 : ∀ α β, α +# β = β +# α.
Proof.
  intros; destruct α, β; simpl.
  rewrite Theorem175, (Theorem175 r0 r2); auto.
Qed.

Theorem Theorem210 : ∀ α, α +# nC = α.
Proof.
  intros; destruct α; simpl; Simpl_R.
Qed.

Theorem Theorem210' : ∀ α, nC +# α = α.
Proof.
  intros; destruct α; simpl; Simpl_R.
Qed.

Hint Rewrite Theorem210 Theorem210' : Cn.
Ltac Simpl_Cn := autorewrite with Cn; auto.
Ltac Simpl_Cnin H := autorewrite with Cn in H; auto.

Theorem Theorem211 : ∀ α β δ, (α +# β) +# δ = α +# (β +# δ).
Proof.
  intros; destruct α, β, δ; simpl; repeat rewrite Theorem186; auto.
Qed.

Theorem Theorem212 : ∀ α β μ, β +# μ = α -> 
  ∀ Ξ1 Ξ2 Γ1 Γ2, α = [Ξ1, Ξ2] -> β = [Γ1, Γ2] ->
  μ = [(Ξ1 - Γ1), (Ξ2 - Γ2)].
Proof.
  intros; subst α β; destruct μ; simpl in H0; inversion H0.
  rewrite Theorem175, (Theorem175 Γ2). Simpl_R.
Qed.

Theorem Theorem212' : ∀ α β μ1 μ2,
  β +# μ1 = α -> β +# μ2 = α -> μ1 = μ2.
Proof.
  intros; subst α; destruct μ1, μ2, β; simpl in H0; inversion H0.
  rewrite Theorem175, (Theorem175 r3) in H1;
  apply Theorem188_2 in H1.
  rewrite Theorem175, (Theorem175 r4) in H2;
  apply Theorem188_2 in H2. rewrite H1, H2; auto.
Qed.

Definition Minus_Cn α β : Cn :=
  match α, β with [Ξ1, Ξ2], [Γ1, Γ2]
   => [(Ξ1 - Γ1), (Ξ2 - Γ2)]
  end.
Notation " α -# β " := (Minus_Cn α β)(at level 50).

Theorem Theorem213 : ∀ α β, α -# β = nC <-> α = β.
Proof.
  intros; split; intros.
  - destruct β, α; simpl in H; inversion H; rewrite H1 in H2.
    apply Theorem182_2 in H1; apply Theorem182_2 in H2.
    rewrite H1, H2; auto.
  - rewrite H; destruct β; simpl; Simpl_R.
Qed.

Definition minus_Cn α :Cn := (nC -# α).
Notation " -# α " := (minus_Cn α)(at level 40).

Theorem Theorem214 : ∀ α Ξ1 Ξ2, α = [Ξ1, Ξ2] -> 
  -# α = [(minus_R Ξ1), (minus_R Ξ2)].
Proof.
  intros; destruct α; inversion H; auto.
Qed.

Theorem Theorem215 : ∀ α, -# (-# α) = α.
Proof.
  intros; destruct α; unfold minus_Cn; simpl; Simpl_R.
Qed.

Theorem Theorem216 : ∀ α, α +# (-# α) = nC.
Proof.
  intros; destruct α; simpl; Simpl_R.
Qed.

Theorem Theorem216' : ∀ α, (-# α) +# α = nC.
Proof.
  intros; destruct α; simpl; Simpl_R.
Qed.

Hint Rewrite Theorem215 Theorem216 Theorem216' : Cn.

Theorem Theorem217 : ∀ α β, -# (α +# β) = (-# α) +# (-# β).
Proof.
  intros; destruct α, β; unfold minus_Cn; simpl.
  repeat rewrite <- Theorem180; auto.
Qed.

Theorem Theorem218 : ∀ α β, α -# β = α +# (-# β).
Proof.
  intros; destruct α, β; simpl; auto.
Qed.

Theorem Theorem219 : ∀ α β, -# (α -# β) = β -# α.
Proof.
  intros; rewrite Theorem218, Theorem217.
  rewrite Theorem215, Theorem209, <- Theorem218; auto.
Qed.

Corollary CnMi_uni : ∀ α β δ, α +# β = δ <-> β = δ -# α .
Proof.
  split; intros.
  - eapply Theorem212'; eauto.
    rewrite Theorem209, Theorem218, Theorem211; Simpl_Cn.
  - rewrite H, Theorem209, Theorem218, Theorem211; Simpl_Cn.
Qed.

Corollary CnMi1 : ∀ α, (α -# α) = nC.
Proof.
  intros; rewrite Theorem218; apply Theorem216.
Qed.

Corollary CnMi1' : ∀ α, (α -# nC) = α.
Proof.
  intros; destruct α; simpl; Simpl_R.
Qed.

Hint Rewrite CnMi1 CnMi1' : Cn.

(* SECTION III Multiplication *)

Definition Times_Cn α β :=
  match α, β with [Ξ1, Ξ2], [Γ1, Γ2]
   => [(Ξ1 · Γ1) - (Ξ2 · Γ2), (Ξ1 · Γ2) + (Ξ2 · Γ1)]
  end.
Notation " α ·# β " := (Times_Cn α β)(at level 40).

Theorem Theorem220 : ∀ α β, α ·# β = β ·# α.
Proof.
  intros; destruct α, β; simpl;
  rewrite Theorem194, (Theorem194 r0 r2);
  rewrite  Theorem175, (Theorem194 r0 r1), (Theorem194 r r2); auto.
Qed.

Theorem Theorem221 : ∀ α β, α ·# β = nC <-> α = nC \/ β = nC.
Proof.
  split; intros.
  - destruct α, β; simpl in H. inversion H; rewrite H1 in H2.
    destruct (classic ([r1, r2] = nC)) as [H3 | H3]; auto.
    assert (~ ((r1 = O) /\ (r2 = O))).
    { intro; destruct H0; rewrite H4, H0 in H3; apply H3; auto. }
    assert (((r1 · r1) + (r2 · r2)) > (O + O)).
    { apply property_not in H0; destruct H0; apply Theorem190.
      + right; split; destruct r1, r2;
        unfold IGE_R; simpl; try tauto.
      + left; split; destruct r1, r2;
        unfold IGE_R; simpl; try tauto. }
    Simpl_Rin H4; apply Theorem182_2 in H1.
    assert ((r · r1) · r1 =(r0 · r2) · r1). { rewrite H1; auto. }
    assert (((r · r2) + (r0 · r1)) · r2 =O · r2).
    { rewrite H2; auto. }
    Simpl_Rin H6; rewrite Theorem201' in H6.
    repeat rewrite Theorem199 in H5;
    repeat rewrite Theorem199 in H6.
    rewrite (Theorem194 r2 r1) in H5.
    rewrite <- H5, <- Theorem201, Theorem175 in H6.
    apply Theorem192 in H6; destruct H6.
    + rewrite H6 in H1; simpl in H1; symmetry in H1.
      rewrite H6 in H2; simpl in H2.
      apply Theorem192 in H1; apply Theorem192 in H2.
      apply property_not in H0; destruct H0.
      * destruct H2; try tauto. left; rewrite H2, H6; auto.
      * destruct H1; try tauto. left; rewrite H1, H6; auto.
    + rewrite H6 in H4; simpl in H4; elim H4.
  - destruct H; rewrite H.
    * destruct β; simpl; auto. * destruct α; simpl; Simpl_R.
Qed.

Corollary CnTi_O : ∀ α, α ·# nC = nC.
Proof.
  intros; apply Theorem221; tauto.
Qed.

Corollary CnTiO_ : ∀ α, nC ·# α = nC.
Proof.
  intros; apply Theorem221; tauto.
Qed.

Theorem Theorem222 : ∀ α, α ·# eC = α.
Proof.
  intros; destruct α; simpl; repeat rewrite Theorem195; Simpl_R.
Qed.

Corollary Theorem222' : ∀ α, eC ·# α = α.
Proof.
  intros; rewrite Theorem220; apply Theorem222.
Qed.

Hint Rewrite CnTi_O CnTiO_ Theorem222 Theorem222' : Cn.

Theorem Theorem223 : ∀ α, α ·# (-# eC) = (-# α).
Proof.
  intros; destruct α; simpl; Simpl_R.
Qed.

Theorem Theorem224 : ∀ α β, (-# α) ·# β = -# (α ·# β).
Proof.
  intros; destruct α, β; simpl; unfold minus_Cn; simpl.
  repeat rewrite Theorem197'; unfold Minus_R; rewrite Theorem177.
  rewrite Theorem180, Theorem177.
  rewrite Theorem194, (Theorem194 r0 r2), Theorem180; auto.
Qed.

Theorem Theorem224' : ∀ α β, α ·# (-# β) = -# (α ·# β).
Proof.
  intros; rewrite Theorem220, Theorem224, Theorem220; auto.
Qed.

Theorem Theorem224'' : ∀ α β, (-# α) ·# β = α ·# (-# β).
Proof.
  intros; rewrite Theorem224, Theorem224'; auto.
Qed.

Theorem Theorem225 : ∀ α β, (-# α) ·# (-# β) = (α ·# β).
Proof.
  intros; rewrite Theorem224'', Theorem215; auto.
Qed.

Theorem Theorem226 : ∀ α β δ, (α ·# β) ·# δ = α ·# (β ·# δ).
Proof.
  intros; destruct α, β, δ; simpl.
  repeat rewrite Theorem202', Theorem201', Theorem202, Theorem201.
  repeat rewrite Theorem199; unfold Minus_R.
  repeat rewrite Theorem186; repeat rewrite <- Theorem180.
  apply eq4; split.
  - rewrite (Theorem175 (r0·(r2·r3)) _), Theorem186; auto.
  - rewrite (Theorem175 (- (r0·(r2·r4))) _), Theorem186; auto.
Qed.

Theorem Theorem227 : ∀ α β δ, α ·# (β +# δ) = (α ·# β) +# (α ·# δ).
Proof.
  intros; destruct α, β, δ; simpl; repeat rewrite Theorem201.
  unfold Minus_R; repeat rewrite Theorem186.
  rewrite Theorem180, <- (Theorem186 (r · r3) _ _).
  rewrite (Theorem175  _ (- (r0 · r2))), Theorem186.
  rewrite <- (Theorem186 (r0 · r1) _ _), (Theorem175 _ (r · r4)).
  rewrite <- (Theorem186 (r · r4) _ _); auto.
Qed.

Theorem Theorem228 : ∀ α β δ, α ·# (β -# δ) = (α ·# β) -# (α ·# δ).
Proof.
  intros; now rewrite Theorem218,Theorem218,Theorem227,Theorem224'.
Qed.

Definition Get_l β: Real := 
  match β with 
   [Ξ1, Ξ2] => Ξ1
  end.

Definition Get_r β : Real := 
  match β with 
   [Ξ1, Ξ2] => Ξ2
  end.

Definition Square_Cn β := 
  match β with 
   [Ξ1, Ξ2] => (Ξ1 · Ξ1) + (Ξ2 · Ξ2)
  end.

Lemma Lemma_D64 : ∀ {β}, β <> nC -> neq_zero (Square_Cn β).
Proof.
  intros; destruct β; simpl.
  assert (~ ((r = O) /\ (r0 = O))).
  { intro; destruct H0; rewrite H0, H1 in H; apply H; auto. }
  assert ((r · r + r0 · r0)> (O + O)).
  { apply property_not in H0;destruct H0; apply Theorem190.
    + right; split; destruct r, r0; unfold IGE_R; simpl; try tauto.
    + left; split; destruct r, r0; unfold IGE_R; simpl; try tauto. }
  destruct ((r · r) + (r0 · r0)); elim H1; auto.
Qed.

Definition Out_l β l := ((Get_l β)/(Square_Cn β)) (Lemma_D64 l).
Definition Out_r β l :=
  minus_R (((Get_r β)/(Square_Cn β)) (Lemma_D64 l)).

Lemma Lemma_T229 : ∀ α β l,
  β ·# ([(Out_l β l), (Out_r β l)] ·# α) = α.
Proof.
  intros; destruct β; unfold Out_l, Out_r; simpl Get_l; simpl Get_r.
  rewrite <- Theorem226; simpl Times_Cn at 2.
  repeat rewrite Theorem197'', Di_Rt.
  unfold Minus_R; rewrite Theorem177, Di_Rp.
  repeat rewrite Di_Rt; rewrite (Theorem194 r r0); Simpl_R.
  rewrite Theorem220, Theorem222; auto.
Qed.

Theorem Theorem229 : ∀ β μ1 μ2 α, 
  β ·# μ1 = α -> β ·# μ2 = α -> β <> nC -> μ1 = μ2.
Proof.
  intros; rewrite <- H in H0; apply Theorem213 in H0.
  rewrite <- Theorem228 in H0; apply Theorem221 in H0.
  destruct H0; try tauto; apply -> Theorem213 in H0; auto.
Qed.

Theorem Theorem229' : ∀ α β, β <> nC -> ∃ μ, β ·# μ = α.
Proof.
  intros; exists ([(Out_l β H), (Out_r β H)] ·# α);
  apply Lemma_T229.
Qed.

Definition Over_Cn α β l : Cn := ([(Out_l β l), (Out_r β l)] ·# α).
Notation " α /# β " := (Over_Cn α β)(at level 40).

Corollary CnOv_uni : ∀ a b c l, a ·# b = c <-> b = (c /# a) l.
Proof.
  split; intros.
  - pose proof (Lemma_T229 c a l). eapply Theorem229; eauto.
  - rewrite H; apply Lemma_T229.
Qed.

(* SECTION IV Subtraction *)

Theorem Theorem230 : ∀ α β, (α -# β) +# β = α.
Proof.
  intros; rewrite Theorem209; apply CnMi_uni; auto.
Qed.

Theorem Theorem231 : ∀ α β, (α +# β) -# β = α.
Proof.
  intros; symmetry; apply CnMi_uni; apply Theorem209.
Qed.

Theorem Theorem232 : ∀ α β, α -# (α -# β) = β.
Proof.
  intros; symmetry; apply CnMi_uni; apply Theorem230.
Qed.

Hint Rewrite Theorem230 Theorem231 Theorem232 : Cn.

Theorem Theorem233 : ∀ α β δ, (α -# β) -# δ = α -# (β +# δ).
Proof.
  intros; repeat rewrite Theorem218.
  rewrite Theorem211, Theorem217; auto.
Qed.

Theorem Theorem234 : ∀ α β δ, (α +# β) -# δ = α +# (β -# δ).
Proof.
  intros; repeat rewrite Theorem218; apply Theorem211.
Qed.

Theorem Theorem235 : ∀ α β δ, (α -# β) +# δ = α -# (β -# δ).
Proof.
  intros; repeat rewrite Theorem218.
  rewrite Theorem217, Theorem215; apply Theorem211.
Qed.

Theorem Theorem236 : ∀ α β δ, (α +# δ) -# (β +# δ) = α -# β.
Proof.
  intros; symmetry; apply CnMi_uni;
  rewrite Theorem209, <- Theorem211; Simpl_Cn.
Qed.

Theorem Theorem237 : ∀ α β δ μ,
  (α -# β) +# (δ -# μ) = (α +# δ) -# (β +# μ).
Proof.
  intros; apply CnMi_uni; rewrite <- Theorem235, Theorem233.
  rewrite Theorem235,(Theorem209 _ α), <- Theorem211.
  rewrite (Theorem209 _ μ), (Theorem234 μ _ β); Simpl_Cn.
  rewrite Theorem209, Theorem236; auto.
Qed.

Theorem Theorem238 : ∀ α β δ μ,
  (α -# β) -# (δ -# μ) = (α +# μ) -# (β +# δ).
Proof.
  intros; symmetry; apply CnMi_uni; rewrite Theorem209, Theorem237.
  repeat rewrite Theorem211; rewrite (Theorem209 μ δ);
  apply Theorem236.
Qed.

Theorem Theorem239 : ∀ α β δ μ,
  α -# β = δ -# μ <-> α +# μ = β +# δ.
Proof.
  split; intros.
  - apply Theorem213 in H; rewrite Theorem238 in H;
    apply Theorem213; auto.
  - apply Theorem213; rewrite Theorem238; apply Theorem213; auto.
Qed.

(* SECTION V Division *)

Theorem Theorem240 : ∀ α β l, ((α /# β) l) ·# β = α.
Proof.
  intros; rewrite Theorem220; apply <- CnOv_uni; auto.
Qed.

Theorem Theorem240' : ∀ α β l, β ·# ((α /# β) l) = α.
Proof.
  intros; apply <- CnOv_uni; auto.
Qed.

Theorem Theorem241 : ∀ α β l, ((α ·# β) /# β) l = α.
Proof.
  intros; symmetry; apply CnOv_uni; apply Theorem220.
Qed.

Hint Rewrite Theorem240 Theorem240' Theorem241 : Cn.

Lemma cndicom :  ∀ {α β}, β ·# α <> nC -> α ·# β <> nC.
Proof.
  intros; rewrite Theorem220; auto.
Qed.

Corollary CnDi_com : ∀ β δ {α l}, 
  (α /# (β ·# δ)) l = (α /# (δ ·# β)) (cndicom l).
Proof.
  intros;
  apply CnOv_uni; rewrite Theorem220, (Theorem220 δ β); Simpl_Cn.
Qed.

Lemma Lemma_T242 : ∀ {β α} l, β <> nC -> (β /# α) l <> nC.
Proof.
  intros; intro; symmetry in H0; apply CnOv_uni in H0.
  destruct α, β; simpl in H0; Simpl_Rin H0.
Qed.
 
Theorem Theorem242 : ∀ β α l l1,
  (α /# ((α /# β) l)) (Lemma_T242 l l1) = β.
Proof.
  intros; symmetry; apply CnOv_uni; Simpl_Cn.
Qed.

Lemma Lemma_T243 : ∀ {β α:Cn}, β <> nC -> α <> nC -> β ·# α <> nC.
Proof.
  intros; intro; apply Theorem221 in H1; tauto.
Qed.

Theorem Theorem243 : ∀ α β δ l l1, 
  (((α /# β) l) /# δ) l1 = (α /# (β ·# δ)) (Lemma_T243 l l1).
Proof.
  intros; apply CnOv_uni; rewrite Theorem220, (Theorem220 β δ).
  rewrite <- Theorem226; Simpl_Cn.
Qed.

Theorem Theorem244 : ∀ α β δ l,
  ((α ·# β) /# δ) l = α ·# ((β /# δ) l).
Proof.
  intros; symmetry; apply CnOv_uni;
  rewrite Theorem220, Theorem226; Simpl_Cn.
Qed.

Theorem Theorem245 : ∀ α β δ l l1, 
  ((α /# β) l) ·# δ = (α /# ((β /# δ) l1)) (Lemma_T242 l1 l).
Proof.
  intros; apply CnOv_uni; rewrite Theorem220, Theorem226.
  rewrite (Theorem220 δ ); Simpl_Cn.
Qed.

Theorem Theorem246 : ∀ α β δ l l1, 
  ((α ·# δ) /# (β ·# δ)) (Lemma_T243 l l1) = (α /# β) l.
Proof.
  intros; symmetry; apply CnOv_uni;
  rewrite Theorem220, <- Theorem226; Simpl_Cn.
Qed.

Theorem Theorem247 : ∀ α β δ μ l l1, 
  ((α /# β) l) ·# ((δ /# μ) l1) =
  ((α ·# δ) /# (β ·# μ)) (Lemma_T243 l l1).
Proof.
  intros; apply CnOv_uni;
  rewrite <- Theorem226, (Theorem220 (β ·# μ)).
  rewrite <- Theorem226; Simpl_Cn;
  rewrite Theorem220, (Theorem220 α).
  rewrite (Theorem220 α _), <- Theorem226; Simpl_Cn.
Qed.

Theorem Theorem248 : ∀ β α δ μ l l1 l2, 
  (((α /# β) l) /# ((δ /# μ) l2)) (Lemma_T242 l2 l1) = 
  ((α ·# μ) /# (β ·# δ)) (Lemma_T243 l l1).
Proof.
  intros; symmetry; apply CnOv_uni;
  rewrite Theorem247, Theorem220, Theorem226.
  symmetry; apply CnOv_uni.
  rewrite  <- (Theorem226 μ), (Theorem220 μ).
  rewrite Theorem220; repeat rewrite <- Theorem226; Simpl_Cn.
Qed.

Theorem Theorem249 : ∀ α l, (nC /# α) l = nC.
Proof.
  intros; symmetry; apply CnOv_uni; Simpl_Cn.
Qed.

Theorem Theorem250 : ∀ α l, (α /# α) l = eC.
Proof.
  intros; symmetry; apply CnOv_uni; Simpl_Cn.
Qed.

Hint Rewrite Theorem249 Theorem250 : Cn.

Theorem Theorem251 : ∀ α β l, (α /# β) l = eC <-> α = β.
Proof.
  split; intros.
  - symmetry in H; apply CnOv_uni in H; Simpl_Cnin H.
  - rewrite H; Simpl_Cn.
Qed.

Theorem Theorem252 : ∀ α β δ μ l l1, 
  (α /# β) l = (δ /# μ) l1 <-> α ·# μ = β ·# δ.
Proof.
  split; intros.
  - destruct (classic (δ = nC)) as [H0 | H0].
    + subst δ; Simpl_Cn; Simpl_Cnin H;
      symmetry in H; apply CnOv_uni in H.
      Simpl_Cnin H; rewrite <- H; Simpl_Cn.
    + pose proof (Theorem248 β α δ μ l H0 l1).
      rewrite H in H1; Simpl_Cnin H1; symmetry in H1.
      apply Theorem251 in H1; auto.
  - destruct (classic (δ = nC)) as [H0 | H0].
    + subst δ; Simpl_Cn; Simpl_Cnin H.
      apply Theorem221 in H; destruct H; try tauto.
      rewrite H; symmetry; apply CnOv_uni; Simpl_Cn.
    + pose proof (Theorem248 β α δ μ l H0 l1).
      rewrite H in H1; Simpl_Cnin H1; apply Theorem251 in H1; auto.
Qed.

Theorem Theorem253 : ∀ α β δ l, 
  ((α /# β) l) +# ((δ /# β) l) = ((α +# δ) /# β) l.
Proof.
  intros; apply CnOv_uni; rewrite Theorem227, Theorem220; Simpl_Cn.
Qed.

Theorem Theorem254 : ∀ α β δ μ l l1,
  ((α /# β) l) +# ((δ /# μ) l1) = 
  ((α ·# μ +# β ·# δ) /# (β ·# μ)) (Lemma_T243 l l1).
Proof.
  intros; rewrite <- Theorem246 with (δ:=μ) (l1:=l1).
  pattern ((δ /# μ) l1);
  rewrite <- Theorem246 with (δ:=β) (l1:=l).
  rewrite (CnDi_com μ β), (Theorem220 δ).
  rewrite (proof_irr (cndicom (Lemma_T243 l1 l)) (Lemma_T243 l l1)).
  rewrite Theorem253; auto.
Qed.

Theorem Theorem255 : ∀ α β δ l, 
  ((α /# β) l) -# ((δ /# β) l) = ((α -# δ) /# β) l.
Proof.
  intros; apply CnOv_uni; rewrite Theorem228, Theorem220; Simpl_Cn.
Qed.

Theorem Theorem256 : ∀ α β δ μ l l1, 
  ((α /# β) l) -# ((δ /# μ) l1) = 
  ((α ·# μ -# β ·# δ) /# (β ·# μ)) (Lemma_T243 l l1).
Proof.
  intros; rewrite <- Theorem246 with (δ:=μ) (l1:=l1).
  pattern ((δ /# μ) l1);
  rewrite <- Theorem246 with (δ:=β) (l1:=l).
  rewrite (CnDi_com μ β), (Theorem220 δ β).
  rewrite (proof_irr (cndicom (Lemma_T243 l1 l)) (Lemma_T243 l l1)).
  rewrite Theorem255; auto.
Qed.

(* SECTION VI Complex Conjugates *)

Definition Conj α := match α with [Ξ1, Ξ2] => [Ξ1, -Ξ2] end.
Notation " α ⁻ " := (Conj α)(at level 0).

Theorem Theorem257 : ∀ α, (α⁻)⁻ = α.
Proof.
  intros; destruct α; simpl; Simpl_R.
Qed.

Theorem Theorem258 : ∀ α, α⁻ = nC <-> α = nC.
Proof.
  split; intros; destruct α; simpl in H; simpl; inversion H; auto.
  destruct r0; simpl; auto; inversion H2.
Qed.

Theorem Theorem259 : ∀ α, (α⁻) = α <-> ∃ Z, α = [Z, O].
Proof.
  split; intros; destruct α.
  - inversion H; destruct r0; inversion H; eauto.
  - destruct H; inversion H; auto.
Qed.

Theorem Theorem260 : ∀ α β, (α +# β)⁻ = α⁻ +# β⁻.
Proof.
  intros; destruct α, β; simpl; rewrite Theorem180; auto.
Qed.

Theorem Theorem261 : ∀ α β, (α ·# β)⁻ = α⁻ ·# β⁻.
Proof.
  intros; destruct α, β; simpl; rewrite Theorem198, 
  Theorem197', Theorem197'', Theorem180; auto.
Qed.

Theorem Theorem262 : ∀ α β, (α -# β)⁻ = α⁻ -# β⁻.
Proof.
  intros; apply CnMi_uni;
  rewrite Theorem209, <- Theorem260, Theorem230; auto.
Qed.

Lemma Lemma_T263 : ∀ {α}, α <> nC -> α⁻ <> nC.
Proof.
  intros; intro; apply -> Theorem258 in H0; auto.
Qed.

Theorem Theorem263 : ∀ α β l,
  ((α /# β) l)⁻ = (α⁻ /# β⁻) (Lemma_T263 l).
Proof.
  intros; apply CnOv_uni;
  rewrite Theorem220, <- Theorem261, Theorem240; auto.
Qed.

(* SECTION VII Absolute *)

Definition neq_N Ξ := 
  match Ξ with
   | N ξ => False
   | _ => True
  end.

Definition Sqrt_R Ξ : (neq_N Ξ) -> Real := 
  match Ξ with
   | N ξ => λ l, match l return Real with end
   | O => λ _, O
   | P ξ => λ _, (P (√ξ))
  end.
Notation " √` Ξ " := (Sqrt_R Ξ)(at level 0).

Corollary Co_D67 : ∀ Ξ l, (√`Ξ l) · (√` Ξ l) = Ξ.
Proof.
  intros; destruct Ξ; simpl; destruct l;
  try rewrite (eq2 Lemma_T161'); auto.
Qed.

Lemma D68 : ∀ Ξ1 Ξ2, neq_N ((Ξ1 · Ξ1) + (Ξ2 · Ξ2)).
Proof.
  intros; destruct Ξ1, Ξ2; simpl; auto.
Qed.

Definition Abs_Cn α := 
  match α with [Ξ1, Ξ2]
   => Sqrt_R ((Ξ1 · Ξ1) + (Ξ2 · Ξ2)) (D68 Ξ1 Ξ2)
  end.

Notation " |- α -| " := (Abs_Cn α).

Theorem Theorem264 : ∀ α, α <> nC <-> |- α -| > O.
Proof.
  intros; destruct α; split; intros.
  - destruct r, r0; simpl; auto.
  - destruct r, r0; simpl in H; elim H; intro; inversion H0.
Qed.

Theorem Theorem264' : ∀ α, α = nC <-> |- α -| = O.
Proof.
  split; intros.
  - rewrite H; simpl; auto.
  - destruct α; simpl in H.
    destruct r, r0; simpl in H; auto; discriminate.
Qed.

Theorem Theorem264'' : ∀ α, |- α -| ≧ O.
Proof.
  intros; destruct (classic (α = nC)) as [H | H].
  - apply Theorem264' in H; right; auto.
  - apply Theorem264 in H; left; auto.
Qed.

Lemma Lemma_T265 : ∀ Ξ Γ, 
  Ξ ≧ O -> Γ ≧ O -> (Ξ · Ξ) ≧ (Γ · Γ) -> Ξ ≧ Γ.
Proof.
  intros; destruct H, H0; red.
  - destruct (Theorem167 Ξ Γ) as [H2 | [H2 | H2]]; auto.
    pose proof H2; apply Theorem203_1 with (Θ:=Ξ) in H3; auto.
    apply Theorem203_1 with (Θ:=Γ) in H2; auto.
    rewrite Theorem194 in H3; pose proof  (Theorem171 _ _ _ H3 H2).
    apply Theorem168 in H1; LEGR H1 H4.
  - rewrite <- H0 in H; tauto.
  - rewrite H in H1; destruct Γ; simpl in H1; auto;
    destruct H1; inversion H1.
  - rewrite H, H0; auto.
Qed.

Theorem Theorem265 : ∀ Ξ1 Ξ2, |- [Ξ1, Ξ2] -| ≧ | Ξ1 |.
Proof.
  intros; simpl; apply Lemma_T265.
  - destruct Ξ1, Ξ2; red; simpl; tauto.
  - destruct Ξ1; red; simpl; auto.
  - rewrite Co_D67; destruct Ξ1, Ξ2; red; simpl; try tauto;
    left; apply Theorem121; apply Theorem133.
Qed.

Theorem Theorem265' : ∀ Ξ1 Ξ2, |- [Ξ1, Ξ2] -| ≧ | Ξ2 |.
Proof.
  intros; simpl; apply Lemma_T265.
  - destruct Ξ1, Ξ2; red; simpl; tauto.
  - destruct Ξ2; red; simpl; auto.
  - rewrite Co_D67; destruct Ξ1, Ξ2; red; simpl; try tauto;
    left; rewrite (eq2 Theorem130); apply Theorem133.
Qed.

Theorem Theorem266 : ∀ Ξ Γ, 
  [Ξ, O] ·# [Ξ, O] = [Γ, O] ·# [Γ, O] -> Ξ ≧ O -> Γ ≧ O -> Ξ = Γ.
Proof.
  intros; simpl in H; Simpl_Rin H; inversion H; destruct Γ, Ξ;
  simpl in *; auto;
  try discriminate; apply eq3 in H3; apply eq3; simpl in *.
  - Absurd; pose proof (Theorem161_1 _ _ _ (Theorem117 _ _ H3) H2).
    elim H4; apply Theorem116.
  - destruct H0; inversion H0.
  - destruct H1; inversion H1.
  - Absurd; pose proof (Theorem161_1 _ _ _ (Theorem117 _ _ H3) H2).
    elim H4; apply Theorem116.
Qed.

Theorem Theorem267 : ∀ α, [|-α-|, O] ·# [|-α-|, O] = α ·# α⁻.
Proof.
  intros; simpl; Simpl_R; destruct α; simpl; rewrite Co_D67.
  unfold Minus_R; rewrite Theorem197'', Theorem177.
  rewrite  Theorem197'', (Theorem194 r r0); Simpl_R.
Qed.

Theorem Theorem268 : ∀ α β, |-(α ·# β)-| = |-α-| · |-β-|.
Proof.
  intros. pose proof (Theorem267 (Times_Cn α β)).
  rewrite Theorem261, Theorem226, <- (Theorem226 β ) in H.
  rewrite (Theorem220 β), Theorem226, <- Theorem226 in H.
  rewrite <- (Theorem267 α), <- (Theorem267 β), Theorem226 in H.
  rewrite <- (Theorem226 _ _ [|- β -|, O]) in H.
  rewrite (Theorem220 [|- α -|, O] [|- β -|, O]), Theorem226 in H.
  rewrite <- (Theorem226 _ _ ([|- α -|, O] ·# [|- β -|, O])) in H.
  simpl Times_Cn in H at 5 6; Simpl_Rin H.
  apply Theorem266; auto; try apply Theorem264''.
  assert (∀ A B, A ≧ O -> B ≧ O -> A · B ≧ O); intros.
  { destruct A, B; red; simpl; try tauto.
     - destruct H1; inversion H1.
     - destruct H0; inversion H0. }
  apply H0; apply Theorem264''.
Qed.

Lemma Lemma_T269 : ∀ {α}, α <> nC -> neq_zero |-α-|.
Proof.
  intros; destruct α; destruct r, r0; simpl; auto.
Qed.

Theorem Theorem269 : ∀ α β l, 
  |- (α /# β) l -| = (|-α-| / |-β-|) (Lemma_T269 l).
Proof.
  intros; pose proof (Theorem240 α β l).
  pattern α at 2; rewrite <- H; rewrite Theorem268; Simpl_R.
Qed.

Theorem Theorem270 : ∀ α β, α +# β = eC -> |-α-| + |-β-| ≧ 1.
Proof.
  intros; destruct α, β; simpl in H; inversion H;
  apply Theorem191; apply Theorem168'.
  - apply Theorem173 with (Γ:=|r|); apply Theorem168;
    try apply Theorem265. destruct r; red; simpl; auto.
  - apply Theorem173 with (Γ:=|r1|); apply Theorem168;
    try apply Theorem265. destruct r1; red; simpl; auto.
Qed.

Theorem Theorem271 : ∀ α β, |- α +# β -| ≦ |- α -| + |- β -|.
Proof.
  intros; apply Theorem168;
  destruct (classic ((α +# β) = nC)) as [H | H].
  - rewrite H; simpl; change O with (Plus_R O O). 
    apply Theorem191; apply Theorem264''.
  - pose proof (Theorem250 _ H); rewrite <- Theorem253 in H0.
    apply Theorem270 in H0; repeat rewrite Theorem269 in H0;
    destruct H0.
    + left; apply Theorem203_1 with (Θ:=|- α +# β -|) in H0;
      Simpl_Rin H0.
      * rewrite Theorem201' in H0; Simpl_Rin H0.
      * apply Theorem264; auto.
    + rewrite Di_Rp in H0; symmetry in H0.
      apply ROv_uni in H0; Simpl_Rin H0; red; auto.
Qed.

Theorem Theorem272 : ∀ α, |- -#α -| = |- α -|.
Proof.
  intros; destruct α, r, r0; simpl; auto.
Qed.

Theorem Theorem273 : ∀ α β, |- (α -# β) -| ≧ | |-α-| - |-β-| |.
Proof.
  intros; generalize (Theorem230 α β) (Theorem230 β α); intros.
  assert (|- α -# β -| ≧  (|- α -| - |- β -|)).
  { pose proof (Theorem271 (α -# β) β); rewrite Theorem230 in H1.
    apply Theorem168' in H1; destruct H1.
    - left; apply Theorem188_1 with (Θ:=|- β -|); Simpl_R.
    - right; apply Theorem188_2 with (Θ:=|- β -|); Simpl_R. }
  assert (|- β -# α -| ≧  (|- β -| - |- α -|)).
  { pose proof (Theorem271 (β -# α) α); rewrite Theorem230 in H2.
    apply Theorem168' in H2; destruct H2.
    - left; apply Theorem188_1 with (Θ:=|- α -|); Simpl_R.
    - right; apply Theorem188_2 with (Θ:=|- α -|); Simpl_R. }
  rewrite <- Theorem219, Theorem272, <- Theorem181 in H2.
  destruct |- α -# β -|, (|- α -| - |- β -|); simpl; auto.
Qed.

(* SECTION VIII Sum and Product *)

Section T274.

Variables p q :Nat.
Variables f :Nat -> Nat -> Prop.

Inductive T274h x y : Prop :=
  T274h_intro : ILT_N x p -> ILT_N y q -> f x y -> T274h x y.

Inductive T274h' x y : Prop :=
  | T274h'_l : f p y -> f x q -> T274h' x y
  | T274h'_r : x <> p -> y <> q -> f x y -> T274h' x y.

End T274.

Definition Ensemble_LE x := /{ z | ILE_N z x /}.

Lemma Lemma274 : ∀ x y f, 
  Bijection (Ensemble_LE x`) (Ensemble_LE y`) f -> 
  ∃ f, Bijection (Ensemble_LE x) (Ensemble_LE y) f.
Proof.
  intros; destruct H, H0, H1, H2, (classic (f x` y`)) as [H4 |H4].
  - exists (T274h x` y` f); red; repeat split; try red; intros.
    + destruct H5, H6; eauto.
    + destruct H5; red in H0; apply Le_Lt in H5.
      assert (x0 ∈ (Ensemble_LE x`)). { constructor; red; tauto. }
      apply H0 in H6; destruct H6; exists x1; constructor; auto.
      pose proof H6; destruct H3; apply H8 in H6; destruct H6, H6;
      auto. rewrite H6 in H7; ELN (H1 _ _ _ H7 H4) H5.
    + destruct H5, H6; eauto.
    + destruct H5; red in H2; apply Le_Lt in H5.
      assert (y0 ∈ (Ensemble_LE y`)). { constructor; red; tauto. }
      apply H2 in H6; destruct H6; exists x0; constructor; auto.
      pose proof H6; destruct H3; apply H3 in H6; destruct H6, H6;
      auto. rewrite H6 in H7; ELN (H _ _ _ H7 H4) H5.
    + destruct H5; apply Theorem26; Simpl_N.
    + destruct H5; apply Theorem26; Simpl_N.
  - exists (T274h' x` y` f); red; repeat split; try red; intros.
    + destruct H5, H6; eauto.
      * red in H; elim H8; eapply H; eauto.
      * red in H; elim H7; eapply H; eauto.
    + destruct H5; red in H0; apply Le_Lt in H5.
      assert (x0 ∈ (Ensemble_LE x`)). { constructor; red; tauto. }
      apply H0 in H6; destruct H6.
      assert (x` ∈ (Ensemble_LE x`)). { constructor; red; tauto. }
      apply H0 in H7; destruct H7.
      destruct (classic (x1 = y`)) as [H8 |H8].
      * rewrite H8 in H6; exists x2; constructor; auto.
      * exists x1; constructor 2; auto; intro; ELN H9 H5.
    + destruct H5, H6; eauto.
      * red in H1; elim H6; eapply H1; eauto.
      * red in H1; elim H5; eapply H1; eauto.
    + destruct H5; red in H2; apply Le_Lt in H5.
      assert (y0 ∈ (Ensemble_LE y`)). { constructor; red; tauto. }
      apply H2 in H6; destruct H6.
      assert (y` ∈ (Ensemble_LE y`)). { constructor; red; tauto. }
      apply H2 in H7; destruct H7.
      destruct (classic (x0 = x`)) as  [H8| H8].
      * rewrite H8 in H6; exists x1; constructor; auto.
      * exists x0; constructor 2; auto; intro; ELN H9 H5.
    + destruct (Theorem10 x0 x) as [H6 | [H6 | H6]], H3, H5;
      try tauto.
      * pose proof H8; apply Theorem25 in H6; Simpl_Nin H6.
        apply H3 in H8; destruct H8.
        apply Theorem13 in H6; apply LEGEN in H6; auto.
        rewrite H6 in H9; contradiction.
      * apply Theorem25 in H6; Simpl_Nin H6.
        apply H3 in H9; destruct H9. apply Theorem13 in H6;
        apply LEGEN in H6; auto; contradiction.
    + destruct (Theorem10 y0 y) as [H6 | [H6 | H6]], H3, H5;
      try tauto.
      * pose proof H5; apply Theorem25 in H6; Simpl_Nin H6.
        apply H7 in H5; destruct H5.
        apply Theorem13 in H6; apply LEGEN in H6; auto.
        rewrite H6 in H9; contradiction.
      * apply Theorem25 in H6; Simpl_Nin H6.
        apply H7 in H9; destruct H9. apply Theorem13 in H6;
        apply LEGEN in H6; auto; contradiction.
Qed.

Theorem Theorem274 : ∀ x y, ILT_N x y -> 
  ∀ f, ~(Bijection (Ensemble_LE x) (Ensemble_LE y) f).
Proof.
  intros; intro.
  set (M274 := /{ x | ∀ y, ILT_N x y -> 
  ∀ f, ~ Bijection (Ensemble_LE x) (Ensemble_LE y) f /}).
  assert (1 ∈ M274).
  { constructor; intros; intro; red in H2; destruct H2, H3, H4, H5.
    red in H2, H3, H4, H5, H6; destruct H6; red in H1; destruct H1.
    assert (1 ∈ (Ensemble_LE y0)).
    { constructor; left; exists x0; auto. }
    assert (x0` ∈ (Ensemble_LE y0)).
    { constructor; right; Simpl_Nin H1. }
    apply H5 in H8; apply H5 in H9; destruct H8, H9.
    assert (∀ x y, f0 x y -> x = 1); intros.
    { apply H6 in H10; destruct H10, H10; auto.
      destruct (Theorem24 x3); try LGN H10 H11; ELN H11 H10. }
    generalize (H10 _ _ H8); generalize (H10 _ _ H9); intros.
    subst x1 x2; apply AxiomIII with (x:=x0); eauto. }
  assert (∀ x, x ∈ M274 -> x` ∈ M274); intros.
  { destruct H2; constructor; intros; intro.
    assert (exists z, y0 = z`).
    { destruct H3; Simpl_Nin H3; eauto. }
    destruct H5; subst y0; apply Lemma274 in H4; destruct H4.
    repeat rewrite <- NPl_1 in H3.
    apply Theorem20_3 in H3; eapply H2; eauto. }
    assert (∀ x, x ∈ M274). { apply AxiomV; auto. }
    destruct H3 with x; eapply H4; eauto.
Qed.

Inductive Z : Type := 
  | Po : Nat -> Z
  | ZO : Z
  | Ne : Nat -> Z.

Definition defined := Z -> Cn.

Fixpoint RepZ n (f :defined) o := 
  match n with
   | 1 => f (Po 1)
   | m` => o (RepZ m f o) (f (Po n))
  end.

Definition Ope := Cn -> Cn -> Cn.
Definition law_com (o :Ope) := ∀ x y, o x y = o y x.
Definition law_ass (o :Ope) := ∀ x y z, o (o x y) z = o x (o y z).

Theorem Theorem275 : ∀ f h n o, RepZ 1 f o = (f (Po 1)) ->
  RepZ 1 h o = (f (Po 1)) ->
  (∀ n, RepZ n` f o = o (RepZ n f o) (f (Po n`))) -> 
  (∀ n, RepZ n` h o = o (RepZ n h o) (f (Po n`)))
  -> RepZ n f o = RepZ n h o.
Proof.
  intros; set (M275 := /{ n | RepZ n f o = RepZ n h o /}).
   assert (1 ∈ M275). { constructor; rewrite H, H0; auto. }
  assert (∀ x, x ∈ M275 -> x` ∈ M275); intros.
  { destruct H4; constructor; rewrite H1, H2, H4; auto. }
  assert (∀ x, x ∈ M275). { apply AxiomV; auto. }
  destruct H5 with n; auto.
Qed.

Theorem Theorem275' : ∀ f n o, ∃ C, C = RepZ n f o.
Proof.
  intros; exists (RepZ n f o); auto.
Qed.

Theorem Theorem276 : ∀ f n o,
  RepZ n` f o = o (RepZ n f o) (f (Po n`)).
Proof.
  intros; auto.
Qed.

Definition Rep_P n f := RepZ n f (Plus_Cn).
Definition Rep_T n f := RepZ n f (Times_Cn).

Theorem Theorem277 : ∀ f o , RepZ 1 f o = (f (Po 1)).
Proof.
  intros; auto.
Qed.

Theorem Theorem278 : ∀ f n o,
  RepZ n` f  o= o (RepZ n f o) (f (Po n`)).
Proof.
  intros; apply Theorem276.
Qed.

Definition Con_C (α :Cn) := λ n :Z, α.

Theorem Theorem279 : ∀ x α, Rep_P x (Con_C α) = α ·# [x, O].
Proof.
  intros; set (M279 :=  /{ x | Rep_P x (Con_C α) = α ·# [x, O] /}).
  assert (1 ∈ M279).
  { constructor; unfold Rep_P; simpl. unfold Con_C; Simpl_Cn. }
  assert (∀ x, x ∈ M279 -> x` ∈ M279); intros.
  { destruct H0; constructor; unfold Rep_P in *; simpl.
    rewrite H0; unfold Con_C. pattern α at 2;
    rewrite <- Theorem222, <- Theorem227; simpl Plus_Cn.
    unfold Cut_I; rewrite <-  (eq2 Theorem155_1); Simpl_Pr. }
  assert (∀  x, x ∈ M279). { apply AxiomV; auto. }
  destruct H1 with x; auto.
Qed.

Theorem Theorem280 : ∀ f o, RepZ 1` f o = o (f (Po 1)) (f (Po 1`)).
Proof.
  intros; rewrite Theorem278, Theorem277; auto.
Qed.

Section Integers.

Definition ZtoR j := 
  match j with
   | Po x => P x
   | ZO => O
   | Ne x => N x
  end.

Definition ILT_Z (j k :Z) :=
  match j, k with 
   | Po a , Po b => ILT_N a b
   | ZO , Po _ => True
   | Ne _, Po _ => True
   | Ne _, ZO => True
   | Ne a , Ne b => ILT_N b a
   | _ , _ => False
  end.
  
Definition IGT_Z (j k :Z) := ILT_Z k j.

Definition ILE_Z (j k :Z) :=
  match j, k with 
   | Po a , Po b => ILE_N a b
   | ZO , Po _ => True
   | ZO , ZO => True
   | Ne _, Po _ => True
   | Ne _, ZO => True
   | Ne a , Ne b => ILE_N b a
   | _ , _ => False
  end.

Definition IGE_Z (j k :Z) := ILE_Z k j.

Definition ILE_Z' (j k :Z) := ILT_Z j k \/ j = k.

Definition IGE_Z' (j k :Z) := ILE_Z' k j.

Lemma Zle_inv : ∀ {j k}, ILE_Z' j k -> ILE_Z j k.
Proof.
  intros; destruct H, j, k; simpl in H; simpl; 
  try red; auto; inversion H; auto.
Qed.

Lemma Zle_inv' : ∀ {j k}, ILE_Z j k -> ILE_Z' j k.
Proof.
  intros; destruct j, k; simpl in H; simpl; try red; auto;
  destruct H.
  - left; f_equal; auto.
  - right; subst n; auto.
  - left; f_equal; auto.
  - right; subst n; auto.
Qed.

Definition Plus_Z (j k :Z) : Z :=
  match j, k with 
   | Po a , Po b => Po (Plus_N a b)
   | Ne a , Ne b => Ne (Plus_N a b)
   | ZO , _ => k
   | _, ZO => j
   | Po a , Ne b => match Ncase a b with
                     | inright _ => ZO
                     | inleft (left l) => Ne (Minus_N b a l)
                     | inleft (right l) => Po (Minus_N a b l)
                    end
   | Ne a , Po b => match Ncase a b with
                     | inright _ => ZO
                     | inleft (left l) => Po (Minus_N b a l)
                     | inleft (right l) => Ne (Minus_N a b l)
                    end
  end.

Definition minus_Z (j :Z) : Z := 
  match j with
  | Po a => Ne a
  | ZO => j
  | Ne b => Po b 
  end.

Corollary Zminp1 : ∀ j k, minus_Z j = minus_Z k <-> j = k.
Proof.
  split; intros.
  - destruct j, k; simpl in H; inversion H; auto.
  - subst; auto.
Qed.

Corollary Zminp2 : ∀ j, minus_Z (minus_Z j) = j.
Proof.
  intros; destruct j; auto.
Qed.

Definition Minus_Z (j k :Z) : Z :=Plus_Z j (minus_Z k).

Corollary ZPlup1 : ∀ j k, Plus_Z j (minus_Z k) = Minus_Z j k.
Proof.
  intros; auto.
Qed.

Corollary ZPlup2 : ∀ j k,
  minus_Z (Plus_Z j k) = Plus_Z (minus_Z j) (minus_Z k).
Proof.
  intros; destruct j, k; simpl; auto;
  destruct (Ncase n n0) as [[H | H] | H]; simpl; auto.
Qed.

Corollary ZPlup3 : ∀ (j :Z), Plus_Z j (minus_Z j) = ZO.
Proof.
  intros. destruct j; simpl minus_Z; simpl; auto.
  - destruct (Ncase n n) as [[H | H] | H]; auto;
    assert (n = n); auto; EGN H0 H.
  - destruct (Ncase n n) as [[H | H] | H]; auto;
    assert (n = n); auto; EGN H0 H.
Qed.

Corollary ZPlup4 : ∀ (j k :Z), Plus_Z (Minus_Z j k) k = j.
Proof.
  intros; destruct j, k; simpl; auto.
  - destruct (Ncase n n0) as [[H | H] | H].
    + assert (ILT_N (Minus_N n0 n H) n0). { exists n; Simpl_N. }
      simpl; destruct (Ncase n n0) as [[H1|H1]|H1];
      [|LGN H H1|ELN H1 H].
      destruct (Ncase (Minus_N n0 n H) n0) as [[H2 | H2] | H2];
      [|LGN H0 H2|ELN H2 H0]. f_equal;
      apply Theorem20_2 with (z:=(Minus_N n0 n H)); Simpl_N.
    + simpl; Simpl_N.
    + rewrite H; simpl; auto.
  - pose proof (Theorem18 n0 n).
    destruct (Ncase (Plus_N n n0) n0) as [[H0 | H0] | H0].
    + rewrite Theorem6 in H; LGN H H0.
    + f_equal; apply Theorem20_2 with (z:=n0); Simpl_N.
    + rewrite Theorem6 in H; EGN H0 H.
  - assert (n=n); auto.
    destruct (Ncase n n) as [[H0 | H0] | H0]; simpl; auto; EGN H H0.
  - assert (n=n); auto.
    destruct (Ncase n n) as [[H0 | H0] | H0]; simpl; auto; EGN H H0.
  - pose proof (Theorem18 n0 n).
    destruct (Ncase (Plus_N n n0) n0) as [[H0 | H0] | H0].
    + rewrite Theorem6 in H; LGN H H0.
    + f_equal; apply Theorem20_2 with (z:=n0); Simpl_N.
    + rewrite Theorem6 in H; EGN H0 H.
  - destruct (Ncase n n0) as [[H | H] | H].
    + assert (ILT_N (Minus_N n0 n H) n0). { exists n; Simpl_N. }
      simpl; destruct (Ncase n n0) as [[H1|H1]|H1]; [|LGN H H1|ELN H1 H].
      destruct (Ncase (Minus_N n0 n H) n0) as [[H2|H2]|H2];
      [|LGN H0 H2|ELN H2 H0]. f_equal;
      apply Theorem20_2 with (z:=(Minus_N n0 n H)); Simpl_N.
    + simpl; Simpl_N.
    + rewrite H; simpl; auto.
Qed.

Definition Times_Z (j k :Z) : Z :=
   match j, k with 
 | Po a , Po b => Po (Times_N a b)
 | Ne a , Ne b => Po (Times_N a b)
 | Po a, Ne b => Ne (Times_N a b)
 | Ne a, Po b => Ne (Times_N a b)
 | _ , _ => ZO
end.

Corollary ZTimp1 : ∀ j k,
  minus_Z (Times_Z j k) = Times_Z j (minus_Z k).
Proof.
  intros; destruct j, k; simpl; auto.
Qed.

Corollary ZTimp2 : ∀ j, Times_Z j (Po 1) = j.
Proof.
  intros; destruct j; simpl; auto.
Qed.

Corollary ZTimp3 : ∀ j, Times_Z j ZO = ZO.
Proof.
  intros; destruct j; simpl; auto.
Qed.

End Integers.

Corollary Zltp1 : ∀ j k, ILT_Z j k <-> ILT_Z ZO (Minus_Z k j).
Proof.
  split; intros.
  - destruct j, k; simpl in H|-*; auto.
    + destruct (Ncase n0 n) as [[H0|H0]|H0]; auto;
      [LGN H H0|EGN H0 H].
    + destruct (Ncase n0 n) as [[H0|H0]|H0]; auto;
      [LGN H H0|ELN H0 H].
  - destruct j, k; simpl in H|-*; auto.
    + destruct (Ncase n0 n) as [[H0 | H0] | H0]; auto; destruct H.
    + destruct (Ncase n0 n) as [[H0 | H0] | H0]; auto; destruct H.
Qed.

Corollary Zltp2 : ∀ j x, ILT_Z j (Plus_Z j (Po x)).
Proof.
  intros; destruct j; simpl; auto.
  - apply Theorem18.
  - destruct (Ncase n x) as [[H | H] | H]; auto.
    apply Theorem20_1 with (z:=x); Simpl_N. apply Theorem18.
Qed.

Corollary Zltp3 : ∀ {j k i},  ILT_Z j k -> ILT_Z k i -> ILT_Z j i.
Proof.
  intros; destruct j, k, i; simpl in H, H0|-*; auto.
  - eapply Theorem15; eauto. - destruct H. - destruct H.
  - destruct H0. - destruct H0. - eapply Theorem15; eauto.
Qed.

Corollary Zlt_le : ∀ {j k}, ILT_Z j k -> ILE_Z (Plus_Z j (Po 1)) k.
Proof.
  intros; destruct j, k; simpl in H|-*; auto.
  - apply Lt_Le; auto.
  - apply Theorem13; apply Theorem24.
  - destruct (Ncase n 1) as [[H0 | H0] | H0]; auto. N1F H0.
  - destruct (Ncase n 1) as [[H0 | H0] | H0]; auto. N1F H0.
  - destruct (Ncase n 1) as [[H0 | H0] | H0]; simpl.
    + N1F H0.
    + apply LePl_N with (z:=1); Simpl_N.
      apply Theorem25, Theorem13 in H; auto.
    + subst n; N1F H.
Qed.

Corollary Zle_lt : ∀ {j k}, ILE_Z j k -> ILT_Z j (Plus_Z k (Po 1)).
Proof.
  intros; apply Zle_inv' in H; destruct H.
  - pose proof (Zltp2 k 1); eapply Zltp3; eauto.
  - subst j; apply Zltp2.
Qed.

Theorem ZPl_com : ∀ (j k :Z), Plus_Z j k = Plus_Z k j.
Proof.
  intros; destruct j, k; simpl; try rewrite Theorem6; auto.
  - destruct (Ncase n n0) as [[H | H] | H], 
      (Ncase n0 n) as [[H0 | H0] | H0]; auto;
    [LGN H H0|rewrite (proof_irr H H0)|EGN H0 H|rewrite 
    (proof_irr H H0)|LGN H0 H|ELN H0 H|EGN H H0|ELN H H0]; auto.
  - destruct (Ncase n n0) as [[H | H] | H], 
      (Ncase n0 n) as [[H0 | H0] | H0]; auto;
    [LGN H H0|rewrite (proof_irr H H0)|EGN H0 H|rewrite 
    (proof_irr H H0)|LGN H0 H|ELN H0 H|EGN H H0|ELN H H0]; auto.
Qed.

Lemma ZPl_ass_pre1 : ∀ x y z l l0 l1, 
  Minus_N x (Minus_N y z l) l0 = Minus_N (Plus_N z x) y l1.
Proof.
  intros; apply NMi_uni. apply Theorem20_2 with (z:=y).
  rewrite Theorem5; Simpl_N.
  rewrite <- Theorem5; Simpl_N; apply Theorem6.
Qed.

Lemma ZPl_ass_pre2 : ∀ x y l, IGT_N y (Minus_N y x l).
Proof.
  intros; apply Theorem20_1 with (z:=x); Simpl_N.
  apply Theorem18.
Qed.

Lemma ZPl_assP1 : ∀ j x y, 
  Plus_Z (Plus_Z j (Po x)) (Po y) = Plus_Z j (Plus_Z (Po x) (Po y)).
Proof.
  intros; destruct j; simpl; try rewrite Theorem5; auto.
  destruct (Ncase n x) as [[H | H] | H];
  destruct (Ncase n (Plus_N x y)) as [[H0 | H0] | H0]; simpl.
  - f_equal. apply Theorem20_2 with (z:=n); Simpl_N.
    rewrite (Theorem6 _ y), Theorem5; Simpl_N; apply Theorem6.
  - pose proof (Theorem15 _ _ _ H0 H).
    pose proof (Theorem18 x y); LGN H1 H2.
  - subst n; pose proof (Theorem18 x y); LGN H H0.
  - assert (ILT_N (Minus_N n x H) y).
    { apply Theorem20_1 with (z:=x); rewrite Theorem6; Simpl_N. }
    destruct (Ncase (Minus_N n x H) y) as [[H2|H2]|H2]; 
    [f_equal; apply ZPl_ass_pre1|LGN H1 H2|ELN H2 H1].
  - assert (IGT_N (Minus_N n x H) y).
    { apply Theorem20_1 with (z:=x);
      Simpl_N; rewrite Theorem6; auto. }
    destruct (Ncase (Minus_N n x H) y) as [[H2|H2]|H2];
    [LGN H1 H2| |EGN H2 H1].
    f_equal; symmetry; apply NMi_uni. 
    rewrite Theorem6, (Theorem6 x), <- Theorem5; Simpl_N.
  - assert ((Minus_N n x H) = y).
    { apply Theorem20_2 with (z:=x);
      Simpl_N; rewrite Theorem6; auto. }
    destruct (Ncase (Minus_N n x H) y) as [[H2 | H2] | H2]; auto.
    + ELN H1 H2. + EGN H1 H2.
  - f_equal; subst n.
    apply Theorem20_2 with (z:=x); Simpl_N; apply Theorem6.
  - subst n; pose proof (Theorem18 x y); LGN H H0.
  - subst n; pose proof (Theorem18 x y); ELN H0 H.
Qed.

Lemma ZPl_assP2 : ∀ j x y, 
  Plus_Z (Plus_Z j (Ne x)) (Po y) = Plus_Z j (Plus_Z (Ne x) (Po y)).
Proof.
  intros; destruct j; simpl.
  - destruct (Ncase n x) as [[H | H] | H];
    destruct (Ncase x y) as [[H0 | H0] | H0]; simpl.
    + pose proof (Theorem15 _ _ _ (ZPl_ass_pre2 n x H) H0).
      destruct (Ncase (Minus_N x n H) y) as [[H2 | H2] | H2].
      * f_equal. pose proof (Theorem15 _ _ _ H0 (Theorem18 y n)).
        rewrite Theorem6 in H3. rewrite ZPl_ass_pre1 with (l1:=H3).
        apply Theorem20_2 with (z:=x); Simpl_N.
        rewrite Theorem5; Simpl_N.
      * LGN H1 H2. * ELN H2 H1.
    + destruct (Ncase (Minus_N x n H) y) as [[H1 | H1] | H1];
      destruct (Ncase n (Minus_N x y H0)) as [[H2|H2]|H2]; auto.
      * pose proof H1; apply Theorem19_1 with (z:=n) in H3;
        Simpl_Nin H3. pose proof H2;
        apply Theorem19_1 with (z:=y) in H4; Simpl_Nin H4.
        rewrite Theorem6 in H3. LGN H3 H4.
      * f_equal. pose proof H1;
        apply Theorem19_1 with (z:=n) in H3; Simpl_Nin H3.
        pose proof H2; apply Theorem19_1 with (z:=y) in H4;
        Simpl_Nin H4. rewrite ZPl_ass_pre1 with (l1:=H3);
        rewrite ZPl_ass_pre1 with (l1:=H4).
        apply Theorem20_2 with (z:=x); Simpl_N; apply Theorem6.
      * pose proof H1; apply Theorem19_1 with (z:=n) in H3;
        Simpl_Nin H3. apply Theorem19_2 with (z:=y) in H2;
        Simpl_Nin H2. rewrite Theorem6 in H2. EGN H2 H3.
      * f_equal; symmetry; apply NMi_uni.
        apply Theorem20_2 with (z:=y); Simpl_N.
        rewrite Theorem5, Theorem6; Simpl_N.
      * pose proof H1; apply Theorem19_1 with (z:=n) in H3;
        Simpl_Nin H3. pose proof H2;
        apply Theorem19_1 with (z:=y) in H4; Simpl_Nin H4.
        rewrite Theorem6 in H3. LGN H3 H4.
      * pose proof H1; apply Theorem19_1 with (z:=n) in H3;
        Simpl_Nin H3. apply Theorem19_2 with (z:=y) in H2;
        Simpl_Nin H2. rewrite Theorem6 in H2. ELN H2 H3.
      * pose proof H2;
        apply Theorem19_1 with (z:=y) in H3; Simpl_Nin H3.
        apply Theorem19_2 with (z:=n) in H1; Simpl_Nin H1.
        rewrite Theorem6 in H1. EGN H1 H3.
      * pose proof H2;
        apply Theorem19_1 with (z:=y) in H3; Simpl_Nin H3.
        apply Theorem19_2 with (z:=n) in H1; Simpl_Nin H1.
        rewrite Theorem6 in H1. ELN H1 H3.
    + subst x. pose proof (ZPl_ass_pre2 n y H).
      destruct (Ncase (Minus_N y n H) y) as [[H1 | H1] | H1].
      * f_equal; apply NMi_uni; Simpl_N.
      * LGN H0 H1. * ELN H1 H0.
    + f_equal; rewrite Theorem6; apply Theorem20_2 with (z:=x).
      repeat rewrite Theorem5; Simpl_N; apply Theorem6.
    + pose proof (Theorem15 _ _ _ (ZPl_ass_pre2 y x H0) H).
      destruct (Ncase n (Minus_N x y H0)) as [[H2|H2]|H2];
        [LGN H1 H2| |EGN H2 H1].
      f_equal; symmetry; apply  NMi_uni.
      rewrite (Theorem6 _ y), <- Theorem5; Simpl_N.
    + subst x; Simpl_N.
    + subst x; rewrite Theorem6; Simpl_N.
    + subst n; pose proof (ZPl_ass_pre2 y x H0).
      destruct (Ncase x (Minus_N x y H0)) as [[H1|H1]|H1];
        [LGN H H1| |EGN H1 H].
      f_equal; symmetry; apply NMi_uni; Simpl_N.
    + subst n x; auto.
  - destruct (Ncase x y) as [[H | H] | H]; auto.
  - destruct (Ncase (Plus_N n x) y) as [[H | H] | H];
    destruct (Ncase x y) as [[H0 | H0] | H0]; simpl.
    + assert (ILT_N n (Minus_N y x H0)). 
      { apply Theorem20_1 with (z:=x); Simpl_N. }
      destruct (Ncase n (Minus_N y x H0)) as [[H2|H2]|H2];
        [|LGN H1 H2|ELN H2 H1].
      f_equal; apply NMi_uni; rewrite Theorem6,<- Theorem5; Simpl_N.
    + pose proof (Theorem15 _ _ _ H H0).
      pose proof (Theorem18 x n).
      rewrite Theorem6 in H2; LGN H1 H2.
    + subst y; pose proof (Theorem18 x n).
      rewrite Theorem6 in H0; LGN H H0.
    + assert (IGT_N n (Minus_N y x H0)). 
      { apply Theorem20_1 with (z:=x); Simpl_N.  }
      destruct (Ncase n (Minus_N y x H0)) as [[H2|H2]|H2];
        [LGN H1 H2| |EGN H2 H1].
      f_equal; symmetry; apply NMi_uni.
      apply Theorem20_2 with (z:=y); rewrite Theorem5; Simpl_N.
      rewrite (Theorem6 n), <- Theorem5; Simpl_N; apply Theorem6.
    + f_equal; apply Theorem20_2 with (z:=y);
      rewrite Theorem5; Simpl_N.
    + subst x; Simpl_N.
    + assert (n = (Minus_N y x H0)).
      { apply Theorem20_2 with (z:=x); Simpl_N.  }
      destruct (Ncase n (Minus_N y x H0)) as [[H2 | H2] | H2];
      auto. * ELN H1 H2. * EGN H1 H2.
    + subst y; pose proof (Theorem18 x n).
      rewrite Theorem6 in H; LGN H H0.
    + subst y; pose proof (Theorem18 x n).
      rewrite Theorem6 in H; ELN H0 H.
Qed.

Theorem ZPl_ass : ∀ j k i, 
  Plus_Z (Plus_Z j k) i = Plus_Z j (Plus_Z k i).
Proof.
  intros. destruct k, i; try rewrite (ZPl_com _ ZO); auto.
  - apply ZPl_assP1.
  - apply Zminp1; repeat rewrite ZPlup2.
    simpl minus_Z; apply ZPl_assP2.
  - apply ZPl_assP2.
  - apply Zminp1; repeat rewrite ZPlup2.
    simpl minus_Z; apply ZPl_assP1.
Qed.

Theorem ZTi_com : ∀ (j k :Z), Times_Z j k = Times_Z k j.
Proof.
  intros; destruct j, k; simpl; try rewrite (Theorem29); auto.
Qed.

Lemma ZTi_disP1 : ∀ j k x,  Times_Z j (Plus_Z k (Po x)) =
  Plus_Z (Times_Z j k) (Times_Z j (Po x)).
Proof.
  intros; destruct j, k; simpl; try rewrite Theorem30; auto.
  - destruct (Ncase n0 x) as [[H | H] | H].
    + assert (ILT_N (Times_N n n0) (Times_N n x)).
      { rewrite Theorem29,(Theorem29 n); apply Theorem32_1; auto. }
      destruct (Ncase (Times_N n n0)
        (Times_N n x)) as [[H1|H1]|H1].
      * f_equal; apply Theorem20_2 with (z:=(Times_N n n0));
        Simpl_N. rewrite <- Theorem30; Simpl_N.
      * LGN H0 H1. * ELN H1 H0.
    + assert (IGT_N (Times_N n n0) (Times_N n x)).
      { rewrite Theorem29, (Theorem29 n x);
        apply Theorem32_1; auto. }
      destruct (Ncase (Times_N n n0) (Times_N n x))
        as [[H1|H1]|H1]; [LGN H0 H1| |EGN H1 H0].
      f_equal; apply Theorem20_2 with (z:=(Times_N n x)); Simpl_N.
      rewrite <- Theorem30; Simpl_N.
    + destruct (Ncase (Times_N n n0) (Times_N n x))
        as [[H1|H1]|H1]; auto.
      * apply Theorem32_2 with (z:=n) in H.
        rewrite Theorem29, (Theorem29 x) in H; ELN H H1.
      * apply Theorem32_2 with (z:=n) in H.
        rewrite Theorem29, (Theorem29 x) in H; EGN H H1.
  - destruct (Ncase n0 x) as [[H | H] | H].
    + assert (ILT_N (Times_N n n0) (Times_N n x)).
      { rewrite Theorem29, (Theorem29 n);
        apply Theorem32_1; auto. }
      destruct (Ncase (Times_N n n0) (Times_N n x))
        as [[H1|H1]|H1]; [|LGN H0 H1|ELN H1 H0].
      f_equal; apply Theorem20_2 with (z:=(Times_N n n0)); Simpl_N.
      rewrite <- Theorem30; Simpl_N.
    + assert (IGT_N (Times_N n n0) (Times_N n x)).
      { rewrite Theorem29,(Theorem29 n); apply Theorem32_1; auto. }
      destruct (Ncase (Times_N n n0) (Times_N n x))
        as [[H1|H1]|H1]; [LGN H0 H1| |EGN H1 H0].
      f_equal; apply Theorem20_2 with (z:=(Times_N n x)); Simpl_N.
      rewrite <- Theorem30; Simpl_N.
    + destruct (Ncase (Times_N n n0) (Times_N n x))
        as [[H1|H1]|H1]; auto.
      * apply Theorem32_2 with (z:=n) in H.
        rewrite Theorem29, (Theorem29 x) in H; ELN H H1.
      * apply Theorem32_2 with (z:=n) in H.
        rewrite Theorem29, (Theorem29 x) in H; EGN H H1.
Qed.

Theorem ZTi_dis : ∀ j k i, 
  Times_Z j (Plus_Z k i) = Plus_Z (Times_Z j k) (Times_Z j i).
Proof.
  intros; destruct i.
  - apply ZTi_disP1.
  - rewrite ZPl_com, (ZTi_com _ ZO); simpl.
    rewrite ZPl_com; simpl; auto.
  - apply Zminp1. rewrite ZTimp1. repeat rewrite ZPlup2.
    repeat rewrite ZTimp1; simpl; apply ZTi_disP1.
Qed.

Lemma ZPl_same_eqP1 : ∀ j k x,
  Plus_Z j (Po x) = Plus_Z k (Po x) -> j = k.
Proof.
  intros; destruct j, k; simpl in H|-*; auto; inversion H.
  - f_equal; eapply Theorem20_2; eauto.
  - pose proof (Theorem18 x n); rewrite Theorem6 in H0; EGN H1 H0.
  - destruct (Ncase n0 x) as [[H2 | H2] | H2]; inversion H.
    apply Theorem19_2 with (z:=n0) in H3; Simpl_Nin H3.
    pose proof (Theorem18 x n0).
    pattern x at 2 in H0; rewrite <- H3 in H0.
    rewrite Theorem5, (Theorem6 n) in H0.
    pose proof (Theorem18 (Plus_N x n0) n); LGN H0 H4.
  - pose proof (Theorem18 x n); rewrite Theorem6 in H0; ELN H1 H0.
  - destruct (Ncase n x) as [[H2 | H2] | H2]; inversion H.
    apply Theorem19_2 with (z:=n) in H3; Simpl_Nin H3.
    pose proof (Theorem18 x n); EGN H3 H0.
  - destruct (Ncase n x) as [[H2 | H2] | H2]; inversion H.
    apply Theorem19_2 with (z:=n) in H3; Simpl_Nin H3.
    pose proof (Theorem18 x n0).
    pattern x at 2 in H0; rewrite H3 in H0.
    rewrite (Theorem6 n0) in H0.
    pose proof (Theorem18 (Plus_N x n0) n); LGN H0 H4.
  - destruct (Ncase n x) as [[H2 | H2] | H2]; inversion H.
    apply Theorem19_2 with (z:=n) in H3; Simpl_Nin H3.
    pose proof (Theorem18 x n); ELN H3 H0.
  - destruct (Ncase n0 x) as [[H2 | H2] | H2];
    destruct (Ncase n x) as [[H3 | H3] | H3]; inversion H.
    + pose proof (NMi1 x n H3). pose proof (NMi1 x n0 H2).
      rewrite Theorem6, <-H0, (Theorem6 _ n), H4 in H5.
      apply Theorem20_2 in H5; f_equal; auto.
    + apply Theorem19_2 with (z:=x) in H4; Simpl_Nin H4.
      f_equal; auto.
    + subst x n; auto.
Qed.

Corollary ZPl_same_eq : ∀ j k i,
  Plus_Z j i = Plus_Z k i <-> j = k.
Proof.
  split; intros.
  { destruct i.
    - eapply ZPl_same_eqP1; eauto.
    - rewrite ZPl_com, (ZPl_com k) in H; simpl in H; auto.
    - apply Zminp1 in H. repeat rewrite ZPlup2 in H. simpl in H.
      apply ZPl_same_eqP1 in H; apply -> Zminp1 in H; auto. }
  rewrite H; auto.
Qed.

Lemma Zltp4 : ∀ {j k}, ILT_Z j k -> {x | Minus_Z k j = Po x}.
Proof.
  intros; destruct j, k; simpl in H; try inversion H.
  - exists (Minus_N n0 n H). apply ZPl_same_eq with (i:=(Po n)).
    rewrite ZPlup4.  simpl; Simpl_N.
  - exists n; auto.
  - exists (Plus_N n0 n).
    apply ZPl_same_eq with (i:=(Ne n)). rewrite ZPlup4. simpl.
    pose proof (Theorem18 n n0). rewrite Theorem6 in H0.
    destruct (Ncase (Plus_N n0 n) n) as [[H1 | H1] | H1]; Simpl_N.
    + LGN H0 H1. + EGN H1 H0.
  - exists n; auto.
  - exists (Minus_N n n0 H). unfold Minus_Z.
    apply Zminp1. rewrite ZPlup2. simpl minus_Z. rewrite ZPl_com.
    replace (Po n0) with (minus_Z (Ne n0)); auto. rewrite ZPlup1.
    apply ZPl_same_eq with (i:=(Ne n0)). 
    rewrite ZPlup4. simpl; Simpl_N.
Qed.

Corollary ZPl_same_lt : ∀ j k i, 
  ILT_Z (Plus_Z j i) (Plus_Z k i) <-> ILT_Z j k.
Proof.
  split; intros.
  - apply Zltp1 in H. unfold Minus_Z in H.
    rewrite ZPlup2, (ZPl_com (minus_Z j)) in H.
    rewrite <- ZPl_ass, (ZPl_ass k) in H.
    rewrite ZPlup3, (ZPl_com k) in H; simpl Plus_Z at 2 in H.
    rewrite ZPlup1 in H; apply Zltp1; auto.
  - apply Zltp1; unfold Minus_Z.
    rewrite ZPlup2, (ZPl_com (minus_Z j)).
    rewrite <- ZPl_ass, (ZPl_ass k).
    rewrite ZPlup3, (ZPl_com k); simpl Plus_Z at 2.
    rewrite ZPlup1; apply -> Zltp1; auto.
Qed.

Corollary ZMi_uni : ∀ j k i, Plus_Z j k = i -> j = Minus_Z i k.
Proof.
  intros; apply ZPl_same_eq with (i:=k); rewrite ZPlup4; auto.
Qed.

Corollary ZPl_same_le : ∀ j k i, 
  ILE_Z j k <-> ILE_Z (Plus_Z j i) (Plus_Z k i).
Proof.
  split; intros.
  - apply Zle_inv' in H; apply Zle_inv; destruct H.
    + left; apply ZPl_same_lt; auto.
    + subst j; right; auto.
  - apply Zle_inv' in H; apply Zle_inv; destruct H.
    + left; eapply ZPl_same_lt; eauto.
    + right; eapply ZPl_same_eq; eauto.
Qed.

Corollary Zle_lt' : ∀ {j i},
  ILT_Z j (Plus_Z i (Po 1)) -> ILE_Z j i.
Proof.
  intros; apply Zlt_le, ZPl_same_le in H; auto.
Qed.

Theorem Theorem281u : ∀ f x y o, law_ass o ->
  RepZ (Plus_N x y) f o = 
    o (RepZ x f o) (RepZ y (λ n, f (Plus_Z (Po x) n)) o).
Proof.
  intros; induction y; auto.
  simpl; rewrite IHy, H; auto.
Qed.

Theorem Theorem281t : ∀ f x y, Rep_T (Plus_N x y) f =
  (Rep_T x f) ·# (Rep_T y (λ n, f (Plus_Z (Po x) n))).
Proof.
  intros; apply Theorem281u; red; apply Theorem226.
Qed.

Theorem Theorem281p : ∀ f x y, Rep_P (Plus_N x y) f =
  (Rep_P x f) +# (Rep_P y (λ n, f (Plus_Z (Po x) n))).
Proof.
  intros; apply Theorem281u; red; apply Theorem211.
Qed.

Theorem Theorem282u : ∀ f g x o, law_ass o -> law_com o ->
  RepZ x (λ z, o (f z) (g z)) o = o (RepZ x f o) (RepZ x g o).
Proof.
  intros; set (M282 := /{ x | RepZ x (λ z, o (f z) (g z)) o = 
  o (RepZ x f o) (RepZ x g o) /}).
  assert (1 ∈ M282). { constructor; simpl; auto. }
  assert (∀ x, x ∈ M282 -> x` ∈ M282); intros.
  { destruct H2; constructor; simpl. rewrite H2. repeat rewrite H.
    rewrite <- (H _  _ (g (Po x0`))),(H0 _ (f (Po x0`))), H; auto. }
  assert (∀ x, x ∈ M282). { apply AxiomV; auto. }
  destruct H3 with x; auto.
Qed.

Theorem Theorem282t : ∀ f g x,
  Rep_T x (λ z, (f z) ·# (g z)) = (Rep_T x f) ·# (Rep_T x g).
Proof.
  intros; apply Theorem282u;
  red; try apply Theorem220; apply Theorem226.
Qed.

Theorem Theorem282p : ∀ f g x,
  Rep_P x (λ z, (f z) +# (g z)) = (Rep_P x f) +# (Rep_P x g).
Proof.
  intros; apply Theorem282u;
  red; try apply Theorem211; apply Theorem209.
Qed.

Definition spZ0 (s :Z ->Z) := ∀ a b, s a = s b -> a = b.

Definition spZ1 (s :Z ->Z) n := ∀ a, ILE_Z (Po a) (Po n) -> 
  ILE_Z (s (Po a)) (Po n) /\ ∃ m, s (Po a) = (Po m).

Definition spZ2 (s :Z ->Z) n := ∀ a, ILE_Z (Po a) (Po n) ->
  ∃ b, s (Po b) = (Po a) /\ ILE_Z (Po b) (Po n).

Lemma eq_RepZs : ∀ f (s1 s2 :Z ->Z) x o, 
  (∀ a, ILE_N a x -> s1 (Po a) = s2 (Po a)) ->
  (RepZ x (λ n, f (s1 n)) o) = (RepZ x (λ n, f (s2 n)) o).
Proof.
  intros; revert H; induction x; intros; simpl; f_equal.
  - apply H; apply Theorem13; apply Theorem24.
  - rewrite IHx; auto. intros; apply H; left; apply Le_Lt; auto.
  - f_equal; apply H; red; tauto.
Qed.

Lemma Lemma_T283Za : ∀ f s x o, law_ass o -> law_com o -> 
  (∀ f s, spZ0 s -> spZ1 s x -> spZ2 s x -> 
  RepZ x f o = RepZ x (λ n, f (s n)) o) ->
  spZ0 s -> spZ1 s x` -> spZ2 s x` -> s (Po x`) = (Po x`) ->
  RepZ x` f o = RepZ x` (λ n, f (s n)) o. 
Proof.
  intros; rewrite <- NPl_1. repeat rewrite Theorem281u; auto.
  simpl; rewrite H5; f_equal; apply H1; red; intros; auto.
  - assert (ILE_Z (s (Po a)) (Po x`)).
    { apply H3; left; apply Le_Lt; auto. }  split.
    + apply Zle_lt'; simpl. apply Zle_inv' in H7. destruct H7; auto.
      rewrite <- H5 in H7; apply H2 in H7. inversion H7; subst a.
      simpl in H6; apply Le_Lt in H6; apply OrdN2 in H6; tauto.
    + apply H3; simpl in H6|-*. left.
      eapply Theorem16; left; split; eauto. exists 1; Simpl_N.
  - assert (ILE_N a x`). { left; apply Le_Lt; auto. }
    apply H4 in H7; destruct H7, H7.
    exists x0; split; auto; destruct H8.
    * apply Theorem26; Simpl_N.
    * subst x0; rewrite H7 in H5; inversion H5; subst a; auto.
Qed.

Lemma Lemma_T283Zb : ∀ f s x o, law_ass o -> law_com o -> 
  (∀ f s, spZ0 s -> spZ1 s x -> spZ2 s x -> 
  RepZ x f o = RepZ x (λ n, f (s n)) o) ->
  spZ0 s -> spZ1 s x` -> spZ2 s x` -> s (Po 1) = (Po 1) ->
  RepZ x` f o = RepZ x` (λ n, f (s n)) o. 
Proof.
  intros. rewrite <- NPl1_; repeat rewrite Theorem281u; auto.
  repeat rewrite Theorem277; rewrite H5; f_equal.
  assert ((λ n, f (s (Plus_Z (Po 1) n))) = (λ n,
    f (Plus_Z (Po 1) (Minus_Z (s (Plus_Z (Po 1) n)) (Po 1))))).
  { apply fun_ext; intros; f_equal. rewrite (ZPl_com _ 
    (Minus_Z (s (Plus_Z (Po 1) m)) (Po 1))), ZPlup4; auto. }
  rewrite H6. apply H1 with (f :=(λ n, f (Plus_Z (Po 1) n))) 
    (s:=(λ n, (Minus_Z (s (Plus_Z (Po 1) n)) (Po 1)))); red; intros.
  - apply ZPl_same_eq with (i:=(Po 1)) in H7;
    repeat rewrite ZPlup4 in H7.
    apply H2 in H7; rewrite ZPl_com, (ZPl_com _ b) in H7.
    apply ZPl_same_eq in H7; auto.
  - split.
    + apply ZPl_same_le with (i:= (Po 1)).
      rewrite ZPlup4, (ZPl_com (Po 1)). simpl in H7.
      apply LePl_N with (z:=1) in H7; Simpl_Nin H7. apply H3; auto.
    + assert (ILE_Z (Po a`) (Po x`)).
      { simpl in H7|-*.
        apply LePl_N with (z:=1) in H7; Simpl_Nin H7. }
      apply H3 in H8. destruct H8 as [_ [m H8]].
      assert (IGT_N m 1).
      { destruct m.
        - rewrite <- H5 in H8. apply H2 in H8. inversion H8.
        - rewrite <- NPl1_;  apply N1P. }
      exists (Minus_N m 1 H9).
      apply ZPl_same_eq with (i:=(Po 1)). rewrite ZPlup4.
      simpl; Simpl_N.
  - apply ZPl_same_le with (i:=(Po 1)) in H7;
    repeat rewrite ZPlup4 in H7.
    apply H4 in H7; destruct H7, H7; destruct x0.
    + rewrite H7 in H5; inversion H5.
    + simpl in H7, H8; apply LePl_N with (z:=1) in H8.
      exists x0; split; auto. apply ZPl_same_eq with (i:=(Po 1)).
      rewrite ZPlup4. simpl; Simpl_N.
Qed.

Lemma eq_dec : ∀ {T :Type} (t1 t2 : T), {t1 = t2} + {t1 <> t2}.
Proof.
  intros; destruct (classicT (t1 = t2)); auto.
Qed.

Definition s4Z' (x :Nat) (s :Z ->Z) := 
  λ n, if eq_dec n (Po 1) then (Po 1) 
   else if eq_dec n (Po x`) then (Po x`) else s n.

Lemma Lemma_T283Zc : ∀ x1 x f s o, x = Plus_N x1 1 -> 
  (RepZ x1 (λ n, f (s (Plus_Z (Po 1) n))) o) =
  (RepZ x1 (λ n, f ((s4Z' x s) (Plus_Z (Po 1) n))) o).
Proof.
  intros; apply eq_RepZs; intros.
  unfold s4Z'; destruct (eq_dec (Plus_Z (Po 1) (Po a)) (Po 1)).
  - inversion e; Simpl_Nin H2; destruct (AxiomIII _ H2).
  - destruct (eq_dec (Plus_Z (Po 1) (Po a)) (Po x`)); auto.
    inversion e; Simpl_Nin H2; apply AxiomIV in H2.
    subst a x; Simpl_Nin H0; apply OrdN4 in H0; try tauto.
    red; exists 1; auto.
Qed.

Theorem Theorem283Zu : ∀ f s n o, law_ass o -> law_com o -> 
  (spZ0 s) -> (spZ1 s n) -> (spZ2 s n) -> 
  RepZ n f o = RepZ n (λ m, f (s m)) o.
Proof.
  intros f s n o L1 L2 H H0 H1.
  set (M283:= /{ n | ∀ f s, (spZ0 s) -> (spZ1 s n) -> (spZ2 s n) -> 
  RepZ n f o = RepZ n (λ m, f (s m)) o /}).
  assert (1 ∈ M283).
  { constructor; intros; simpl.
    assert (ILE_Z (Po 1) (Po 1)). { simpl; red; auto. }
    pose proof H5. apply H3 in H5. destruct H5 as [H5 [m P1]]. 
    apply Zle_inv' in H5. destruct H5.
    - apply H4 in H6; destruct H6 as [b [H6]], H7; [N1F H7|].
      subst b; rewrite H6 in H5; simpl in H5; N1F H5.
    - rewrite H5; auto. }
  assert (∀ x, x ∈ M283 -> x` ∈ M283); intros.
  { destruct H3; constructor; intros.
    destruct (classic (s0 (Po x`) = (Po x`))) as [H7 |H7].
    - apply Lemma_T283Za; auto.
    - destruct (classic (s0 (Po 1) = (Po 1))) as [H8 |H8].
      + apply Lemma_T283Zb; auto.
      + pose proof (Theorem13 _ _ (Theorem24 x`)).
        destruct (H6 _ H9) as [b [H10 H11]].
        set (s1 := (λ n, match  (eq_dec n (Po 1)) with
                          | left _ => (Po 1)
                          | right _ => match  (eq_dec n (Po b)) with
                                        | left _ => s0 (Po 1)
                                        | right _ => s0 n
                                       end
                         end )).
        assert (spZ0 s1 /\ spZ1 s1 x` /\ spZ2 s1 x`) as G1.
        { repeat split; try red; intros.
          - unfold s1 in H12. destruct (eq_dec a (Po 1)).
            + destruct eq_dec; try subst a; auto.
              destruct eq_dec; symmetry in H12; try tauto.
              rewrite <- H10 in H12; pose proof (H4 _ _ H12); tauto.
            + destruct (eq_dec a (Po b)).
              * destruct eq_dec; try tauto.
                destruct eq_dec; try subst b0; auto.
                symmetry in H12; pose proof (H4 _ _ H12); tauto.
              * destruct (eq_dec b0 (Po 1)).
                { rewrite <- H10 in H12;
                  pose proof (H4 _ _ H12); tauto. }
                { destruct (eq_dec b0 (Po b)); try apply H4; auto.
                  pose proof (H4 _ _ H12); contradiction. }
          - unfold s1. assert (ILE_N 1 x`).
            { apply Theorem13; apply Theorem24. } 
            destruct eq_dec; auto. destruct eq_dec; apply H5; auto.
          - unfold s1. destruct eq_dec; eauto. destruct eq_dec.
            + apply H5; simpl; apply Theorem13, Theorem24.
            + apply H5; auto.
          - assert (ILE_N 1 x`).
            { apply Theorem13; apply Theorem24. }  
            unfold s1; destruct (eq_dec (Po a) (Po 1)).
            + exists 1; split; auto.
              destruct (eq_dec (Po 1) (Po 1)); auto. elim n0; auto.
            + destruct (eq_dec (Po a) (s0 (Po 1))).
              * exists b. destruct (eq_dec (Po b) (Po 1)); 
                  try rewrite e0 in *; try tauto. symmetry in e.
                destruct eq_dec; auto. elim n2; auto.
              * apply H6 in H12. destruct H12, H12.
                exists x0; symmetry in H12.
                destruct eq_dec; try rewrite e in *; try tauto.
                symmetry in H12; destruct eq_dec; auto.
                elim n0; rewrite <- H12, e; auto. }
        assert (s1 (Po 1) = (Po 1)) as G2.
        { unfold s1. destruct eq_dec; auto. elim n0; auto. }
        apply H5 in H9. destruct H9 as [H9 [m1 P1]]. 
        apply Zle_inv' in H9. destruct H9.
        {  set (s2 := (λ n, match  (eq_dec n (Po 1)) with
                             | left _ => s0 (Po 1)
                             | right _ =>
                                 match (eq_dec n (s0 (Po 1))) with
                                  | left _ => (Po 1)
                                  | right _ => n
                                 end
                            end )). 
        assert (s0 = (λ x, s2 (s1 x))).
        { apply fun_ext; intros; unfold s1. destruct eq_dec.
          { subst m; unfold s2; destruct eq_dec; tauto. }
          destruct (eq_dec m (Po b)).
          { rewrite e, H10. unfold s2.
            destruct eq_dec; try tauto. destruct eq_dec; tauto. }
          { assert ((s0 m) <> (Po 1)).
            { intro; rewrite <- H10 in H12;
              pose proof (H4 _ _ H12); tauto. }
            unfold s2; destruct eq_dec; try tauto.
            destruct (eq_dec (s0 m) (s0 (Po 1))); auto.
            pose proof (H4 _ _ e); tauto. } } rewrite H12.
        assert (RepZ x` (λ n, f0 (s2 n)) o =
          RepZ x` (λ n, f0 (s2 (s1 n))) o).
        { apply (Lemma_T283Zb (λ x, f0 (s2 x)) s1 x); auto;
          try apply G1. } rewrite <- H13.
        apply Lemma_T283Za; auto; try red; intros.
        - unfold s2 in H14. destruct (eq_dec a (Po 1)).
          + destruct eq_dec; try subst a; auto.
            destruct eq_dec; symmetry in H12; try tauto. 
            symmetry in H14; contradiction.
          + destruct (eq_dec a (s0 (Po 1))).
            * destruct eq_dec; symmetry in H14; try tauto.
              destruct eq_dec; try subst b0; tauto.
            * destruct eq_dec; try tauto. destruct eq_dec; tauto.
        - unfold s2. assert (ILE_N 1 x`).
          { apply Theorem13; apply Theorem24. }
          destruct eq_dec; auto. destruct eq_dec; eauto.
        - assert (ILE_N 1 x`).
          { apply Theorem13; apply Theorem24. }  
          unfold s2. destruct (eq_dec (Po a) (s0 (Po 1))).
          + exists 1; split; auto. 
            destruct (eq_dec (Po 1) (Po 1)); auto. tauto.
          + destruct (eq_dec (Po a) (Po 1)).
            * assert (ILE_Z (Po 1) (Po (x) `)). 
              { simpl; apply Theorem13, Theorem24. }
              apply H5 in H16. destruct H16 as [H16 [m H17]].
              exists m. destruct (eq_dec (Po m) (Po 1)).
              { elim n0; rewrite H17, e0; auto. }
              { destruct (eq_dec (Po m) (s0 (Po 1))).
                - split; auto; rewrite e0; auto.
                - elim n2; rewrite H17; auto. }
            * exists a. destruct eq_dec; try tauto.
              destruct eq_dec; try tauto; split; auto.
        - unfold s2. destruct eq_dec; [inversion e|].
          destruct eq_dec; auto. rewrite <- e in H9. simpl in H9.
          apply OrdN2 in H9; tauto. } destruct H11.
        { set (s3:=(λ n, match (eq_dec n (Po 1)) with
                          | left _ => (Po b)
                          | right _ => match  (eq_dec n (Po b)) with
                                        | left _ => (Po 1)
                                        | right _ => n
                                       end
                         end )). 
          assert (s0 = (λ x, s1 (s3 x))).
          { apply fun_ext; intros; unfold s3.
            destruct (eq_dec m (Po 1)).
            { subst m; unfold s1. destruct eq_dec.
              - inversion e. subst b; try contradiction.
              - destruct (eq_dec (Po b) (Po b)); tauto. }
            destruct (eq_dec m (Po b)).
            { rewrite e, H10. unfold s1.
              destruct (eq_dec (Po 1) (Po 1)); try tauto. }
            { unfold s1; destruct (eq_dec m (Po 1)); try tauto.
              destruct (eq_dec m (Po b)); tauto. } } rewrite H12.
          assert (RepZ x` f0 o = RepZ x` (λ n, f0 (s1 n)) o).
          { apply (Lemma_T283Zb f0 s1 x); auto; try apply G1. }
          rewrite H13. apply (Lemma_T283Za (λ n, f0 (s1 n)) s3 x);
          auto; try red; intros.
          - unfold s3 in H14. destruct (eq_dec a (Po 1)).
            + destruct eq_dec; try subst a; auto.
              destruct eq_dec;[subst b0; auto|elim n1; auto].
            + destruct (eq_dec a (Po b)).
              * destruct (eq_dec b0 (Po 1)).
                { subst a b0; auto. }
                { destruct eq_dec; try subst b0; tauto. }
              * destruct (eq_dec b0 (Po 1)); try tauto.
                destruct (eq_dec b0 (Po b)); tauto.
          - unfold s3. assert (ILE_N 1 x`).
            { apply Theorem13; apply Theorem24. } 
            destruct (eq_dec (Po a) (Po 1)).
            + inversion e; split; eauto; simpl; red; auto.
            + destruct (eq_dec (Po a) (Po b)); eauto.
          - assert (ILE_N 1 x`).
            { apply Theorem13; apply Theorem24. }
            unfold s3. destruct (eq_dec a b).
            + exists 1; split; auto.
              destruct eq_dec;[subst a; auto|elim n0; auto].
            + destruct (eq_dec (Po a) (Po 1)).
              * exists b. destruct (eq_dec (Po b) (Po 1)).
                { split;[rewrite e, e0; auto|simpl; red; auto]. }
                { destruct (eq_dec (Po b) (Po b)).
                  - split; auto. simpl; red; auto.
                  - elim n2; auto. }
              * exists a. destruct eq_dec; try tauto.
                destruct eq_dec; try tauto;
                split; auto. inversion e; contradiction.
          - unfold s3. destruct (eq_dec (Po x`) (Po 1)).
            + inversion e.
            + destruct (eq_dec (Po x`) (Po b)); auto. 
              inversion e; subst b; apply OrdN1 in H11; tauto. }
       { destruct x. 
         - simpl; rewrite H9, L2; f_equal; f_equal; subst b; auto.
         - pattern (x`)` at 2; rewrite <- NPl_1. 
           rewrite Theorem281u; auto; simpl RepZ at 3.
           pattern x` at 2; rewrite <- NPl1_, Theorem281u; auto.
           simpl RepZ at 2. subst b.
           rewrite L1, L2, (L2 _ (f0 (s0 (Po (x`)`)))), H10, H9.
           set (s4 := (s4Z' x` s0)).
           erewrite Lemma_T283Zc; eauto.
           assert (s4 (Po 1) = (Po 1)).
           { unfold s4, s4Z'. destruct eq_dec; tauto. }
           assert (s4 (Po (x`)`) = Po (x`)`).
           { unfold s4, s4Z'. destruct eq_dec; auto.
             destruct eq_dec; tauto. }
           pattern (Po 1) at 1; rewrite <- H11. rewrite <- H12.
           assert ((RepZ 1 (λ z, (f0 (s4 z)))) o = f0 (s4 (Po 1))).
           { simpl; auto. } rewrite <- H13.
           rewrite <- Theorem281u, Theorem6; auto. simpl RepZ at 2.
           assert ((RepZ 1 (λ z,
             (f0 (s4 (Plus_Z (Po x) z))))) o = f0 (s4 (Po x`))).
           { simpl; auto. } rewrite <- H14, <- Theorem281u; auto.
            apply Lemma_T283Zb; auto; red; intros.
            + unfold s4, s4Z' in H15. destruct (eq_dec a (Po 1)).
              * destruct eq_dec; try subst a; auto. destruct eq_dec.
                { inversion H15. }
                { rewrite H15 in H10; symmetry in H10.
                  pose proof (H4 _ _ H10); contradiction. }
              * destruct eq_dec.
                { destruct eq_dec.
                  { inversion H15. }
                  { destruct (eq_dec b (Po (x`)`)); try subst a;
                    auto. rewrite H15 in H9; symmetry in H9.
                    pose proof (H4 _ _ H9); contradiction. } }
                { destruct (eq_dec b (Po 1)).
                  { rewrite <- H10 in H15; pose proof (H4 _ _ H15); tauto. }
                  { destruct eq_dec; try subst a; auto.
                    rewrite <- H9 in H15; pose proof (H4 _ _ H15); tauto. } }
            + unfold s4, s4Z'. assert (ILE_N 1 (x`)`).
              { apply Theorem13; apply Theorem24. } 
              destruct eq_dec; eauto. destruct eq_dec; auto.
              split; eauto. simpl; red; auto.
            + assert (ILE_N 1 (x`)`).
              { apply Theorem13; apply Theorem24. }  
              unfold s4, s4Z'. destruct (eq_dec a 1).
              * exists 1; split; auto.
                destruct eq_dec;[subst a; auto|elim n0; auto].
              * destruct (eq_dec a (x`)`).
                { exists (x`)`. destruct eq_dec.
                  { inversion e0. }
                  { destruct (eq_dec  (Po (x`)`)  (Po (x`)`)).
                    { subst a; split; auto; red; auto. }
                    { elim n2; auto. } } }
                { apply H6 in H15; destruct H15, H15.
                  exists x0. destruct (eq_dec (Po x0) (Po 1)).
                  { inversion e; subst x0. rewrite H15 in H9.
                    inversion H9; contradiction. }
                  { destruct (eq_dec (Po x0) (Po (x`)`)); auto.
                    inversion e. subst x0. rewrite H15 in H10.
                    inversion H10; contradiction. } } } }
  assert (∀ n, n ∈ M283); intros. { apply AxiomV; auto. }
  destruct H4 with n; auto.
Qed.

Lemma D70N_ex : ∀ j k (l :ILE_Z j k), 
  { x | Plus_Z j (Po x) = (Plus_Z k (Po 1))}.
Proof.
  intros; apply Zle_lt, Zltp4 in l; destruct l.
  exists x; apply ZPl_same_eq with (i:=j) in e.
  rewrite ZPlup4, (ZPl_com _ j) in e; auto.
Qed.

Definition D70N_get j k l := proj1_sig (D70N_ex j k l).

Definition RepZ' j k f l o := RepZ (D70N_get j k l) 
  (λ n, f (Minus_Z (Plus_Z n j) (Po 1))) o.

Lemma Lemma_T284Za : ∀ y u x, Minus_Z (Plus_Z x (Po 1)) y =
  Plus_Z (Minus_Z (Plus_Z u (Po 1)) y) (Minus_Z x u).
Proof. 
  intros; rewrite ZPl_com.
  apply ZPl_same_eq with (i:=y). rewrite ZPlup4.
  rewrite ZPl_ass, (ZPl_com _ y), <- ZPl_ass, ZPlup4.
  rewrite (ZPl_com _ (Minus_Z x u)), <- ZPl_ass, ZPlup4.
  apply ZPl_com.
Qed.

Lemma T284Z_cond : ∀ {y u x} (l:ILE_Z y u)(l1:ILT_Z u x),
  ILE_Z y x.
Proof.
  intros; apply Zle_inv' in l; apply Zle_inv; destruct l; left.
  - eapply Zltp3; eauto. - subst y; auto.
Qed.

Theorem Theorem284Zu : ∀ y u x f o l1 l2, law_ass o ->
  RepZ' y x f (T284Z_cond l1 l2) o = 
  o (RepZ' y u f l1 o) (RepZ' (Plus_Z u (Po 1)) x f (Zlt_le l2) o).
Proof.
  intros; unfold RepZ', D70N_get. 
  destruct (D70N_ex y x (T284Z_cond l1 l2)), 
   ((D70N_ex y u l1)), (D70N_ex (Plus_Z u (Po 1))); simpl.
  rewrite ZPl_com in e. apply ZMi_uni in e. 
  rewrite Lemma_T284Za with (u:=u) in e.
  destruct (Zltp4 l2) as [n H0]. rewrite H0 in *.
  destruct (Zltp4 (Zle_lt l1)) as [m H1]. rewrite H1 in *.
  inversion e. assert (x1 = m).
  { rewrite ZPl_com in e0; apply ZMi_uni in e0.
    rewrite <- e0 in H1; inversion H1; auto. } assert (x2 = n).
  { rewrite ZPl_ass, (ZPl_com (Po 1)), <-ZPl_ass in e1.
    apply ZPl_same_eq in e1.
    rewrite ZPl_com in e1; apply ZMi_uni in e1.
    rewrite <- e1 in H0. inversion H0; auto. }
  subst x0 x1 x2. rewrite Theorem281u; auto.
  f_equal; f_equal; rewrite <- H1. apply fun_ext; intros; f_equal.
  apply ZPl_same_eq with (i:=(Po 1)). repeat rewrite ZPlup4.
  rewrite (ZPl_com _ m0), ZPl_ass, ZPlup4; auto.
Qed.

Theorem Theorem285Zu : ∀ y x v f l l1 o,
  RepZ' y x f l o = 
  RepZ' (Plus_Z y v) (Plus_Z x v) (λ n, f (Minus_Z n v)) l1 o.
Proof.
  intros; unfold RepZ'; f_equal.
  - unfold D70N_get; destruct (D70N_ex y x l), 
    (D70N_ex (Plus_Z y v) (Plus_Z x v) l1); simpl.
    rewrite (ZPl_com x), (ZPl_ass v), <- e in e0.
    rewrite <- ZPl_ass, (ZPl_com v) in e0.
    rewrite ZPl_com, (ZPl_com _ (Po x0)) in e0.
    apply ZPl_same_eq in e0; inversion e0; auto.
  - apply fun_ext; intros; f_equal.
    apply ZPl_same_eq with (i:=v). rewrite ZPlup4.
    apply ZPl_same_eq with (i:=(Po 1)). rewrite ZPlup4.
    rewrite (ZPl_com _ v), ZPl_ass, ZPlup4.
    rewrite (ZPl_com v); apply ZPl_ass.
Qed.

Definition spZ3 (s :Z ->Z) n m := 
  ∀ a, ILE_Z m a -> ILE_Z a n -> ILE_Z m (s a) /\ ILE_Z (s a) n.

Definition spZ4 (s :Z ->Z) n m := 
  ∀ a, ILE_Z m a -> ILE_Z a n ->
  ∃ b, s b = a /\ ILE_Z m b /\ ILE_Z b n.

Theorem Theorem286Zu : ∀ f x y s l o, law_ass o -> law_com o -> 
  spZ0 s -> spZ3 s x y -> spZ4 s x y ->
  RepZ' y x (λ x, f (s x)) l o = RepZ' y x f l o.
Proof.
  intros. set (s1 := λ n, Minus_Z (s (Minus_Z (Plus_Z n y) (Po 1))) 
    (Minus_Z y (Po 1))). unfold RepZ'.
  assert ((λ n, f (s (Minus_Z (Plus_Z n y) (Po 1)))) = 
  (λ n, f (Plus_Z (s1 n) (Minus_Z y (Po 1))))).
  { apply fun_ext; intros; unfold s1; rewrite ZPlup4; auto. }
  rewrite H4. unfold D70N_get. destruct ((D70N_ex y x l)); simpl.
  pose proof e as G. rewrite ZPl_com in G. apply ZMi_uni in G.
  rewrite <- (Theorem283Zu (λ n,
    f (Plus_Z n (Minus_Z y (Po 1)))) s1); try red; intros; auto.
  - f_equal; apply fun_ext; intros; f_equal.
    apply ZPl_same_eq with (i:=(Po 1)).
    rewrite ZPl_ass; repeat rewrite ZPlup4; auto.
  - unfold s1 in H5.
    apply ZPl_same_eq with (i:=(Minus_Z y (Po 1))) in H5.
    repeat rewrite ZPlup4 in H5. apply H1 in H5.
    apply ZPl_same_eq with (i:=(Po 1)) in H5.
    repeat rewrite ZPlup4 in H5. eapply ZPl_same_eq; eauto.
  - unfold s1. split.
    { apply ZPl_same_le with (i:=(Minus_Z y (Po 1)));
      rewrite ZPlup4.
      assert ((Plus_Z (Po x0) (Minus_Z y (Po 1))) = x).
      { apply ZPl_same_eq with (i:=(Po 1)).
        rewrite ZPl_ass, G. repeat rewrite ZPlup4; auto. }
      rewrite H6. apply H2.
      + apply ZPl_same_le with (i:=(Po 1)); rewrite ZPlup4, ZPl_com.
        apply ZPl_same_le; simpl; apply Theorem13; apply Theorem24.
      + rewrite <- H6. apply ZPl_same_le with (i:=(Po 1));
        rewrite ZPlup4. rewrite ZPl_ass, ZPlup4.
        apply ZPl_same_le; auto. }
    { apply inhabited_sig_to_exists; constructor.
      apply Zltp4, ZPl_same_lt with (i:=(Po 1)). 
      apply Zle_lt; rewrite ZPlup4; apply H2. 
      - apply ZPl_same_le with (i:=(Po 1)); rewrite ZPlup4, ZPl_com.
        apply ZPl_same_le; simpl. apply Theorem13, Theorem24.
      - rewrite G in H5.
        apply ZPl_same_le with (i:=y) in H5; rewrite ZPlup4 in H5.
        apply ZPl_same_le with (i:=(Po 1)); rewrite ZPlup4; auto. }
  - rewrite G in H5.
    apply ZPl_same_le with (i:=y) in H5; rewrite ZPlup4 in H5.
    apply ZPl_same_le with (i:=(minus_Z (Po 1))) in H5.
    rewrite (ZPl_ass x), ZPlup1, ZPlup3 in H5.
    rewrite (ZPl_com x) in H5; simpl Plus_Z at 2 in H5.
    assert (ILE_Z y (Minus_Z (Plus_Z (Po a) y) (Po 1))).
    { apply ZPl_same_le with (i:=(Po 1)). rewrite ZPlup4, ZPl_com.
      apply ZPl_same_le; simpl; apply Theorem13; apply Theorem24. }
    destruct (H3 _ H6 H5), H7, H8. pose proof H8.
    apply ZPl_same_le with (i:=(minus_Z (Po 1))) in H10.
    apply Zle_lt in H10. rewrite ZPlup1 in H10.
    rewrite ZPl_ass, (ZPl_com _ (Po 1)), ZPlup3 in H10.
    rewrite ZPl_com in H10; simpl in H10.
    destruct (Zltp4 H10) as [n H11]. exists n; split.
    + unfold s1. symmetry. apply ZMi_uni.
      assert (x1 = (Minus_Z (Plus_Z (Po n) y) (Po 1))).
      { apply ZMi_uni. apply ZMi_uni in H11. 
        unfold Minus_Z in H11. rewrite ZPlup2 in H11.
        simpl minus_Z in H11. rewrite ZPlup2, Zminp2 in H11.
        rewrite H11. repeat rewrite ZPl_ass.
        pattern (Po 1) at 1; rewrite <- Zminp2.
        rewrite ZPlup3, (ZPl_com _ ZO); auto. }
      rewrite <- H12, H7. apply ZMi_uni.
      rewrite ZPl_ass, ZPlup4; auto.
    + rewrite G, <- H11.
      assert ((Minus_Z x (Minus_Z y (Po 1))) =
        (Minus_Z (Plus_Z x (Po 1)) y)).
      { symmetry. apply ZMi_uni. unfold Minus_Z at 2.
        rewrite <- ZPl_ass, ZPlup4, ZPlup1.
        apply ZPl_same_eq with (i:=(Po 1)). rewrite ZPlup4; auto. }
      rewrite <- H12; apply ZPl_same_le; auto.
Qed.

Theorem Theorem287 : ∀ f x, ∃ Z, |-Rep_P x f-| ≦ Z.
Proof.
  intros; set (M287 := /{ x | ∃ Z, |-Rep_P x f-| ≦ Z /}).
  assert (1 ∈ M287).
  { constructor; simpl; exists |-f (Po 1)-|; right; auto. }
  assert (∀ x, x ∈ M287 -> x` ∈ M287); intros.
  { destruct H0, H0; constructor. unfold Rep_P in *.
    exists (Plus_R x1 |-f (Po x0`)-|); simpl.
    apply Theorem173 with
      (Γ:=(|-(RepZ x0 f Plus_Cn)-| + |-f (Po x0`)-|)).
    - apply Theorem271.
    - destruct H0.
      + left; apply Theorem188_1'; auto.
      + right; rewrite H0; auto. }
  assert (∀ x, x ∈ M287). { apply AxiomV; auto. }
  destruct H1 with x; auto.
Qed.

Theorem Theorem288 : 
  ∀ f x , [|-(Rep_T x f)-|,O] = Rep_T x (λ z, [|-(f z)-|,O]).
Proof.
  intros; set (M288 :=
   /{ x | [|-(Rep_T x f)-|,O] = Rep_T x (λ z, [|-(f z)-|,O]) /}).
  assert (1 ∈ M288). { constructor; simpl; auto. }
  assert (∀ x, x ∈ M288 -> x` ∈ M288); intros.
  { destruct H0; constructor. unfold Rep_T in *;
    simpl; rewrite <- H0. simpl; unfold Minus_R; simpl.
    Simpl_R; rewrite Theorem268; Simpl_R. }
  assert (∀ x, x ∈ M288). { apply AxiomV; auto. }
  destruct H1 with x; auto.
Qed.

Theorem Theorem289 : ∀ f x , Rep_T x f = nC -> ∃ z, (f z) = nC.
Proof.
  intros f x; set (M289 := 
  /{ x | Rep_T x f = nC -> ∃ z, (f z) = nC /}).
  assert (1 ∈ M289). { constructor; intros; simpl; eauto. }
  assert (∀ x, x ∈ M289 -> x` ∈ M289); intros.
  { destruct H0; constructor; intros. unfold Rep_T in H1;
    simpl in H1. apply Theorem221 in H1; destruct H1; eauto. }
  assert (∀ x, x ∈ M289). { apply AxiomV; auto. }
  destruct H2 with x; auto.
Qed.

(* SECTION IV Power *)

Definition judge α j :=
  match j with
   | Po a => True
   | ZO => match α with
            | [O,O] => False
            |  _ => True
           end
   | Ne b => match α with
              | [O,O] => False
              | _ => True
             end
  end.

Lemma judge1 : ∀ {a}, [O,P a] <> nC.
Proof.
  intros; intro; inversion H.
Qed.

Lemma judge2 : ∀ {b}, [O, N b] <> nC.
Proof.
  intros; intro; inversion H.
Qed.

Lemma judge3 : ∀ {a j}, [P a,  j] <> nC.
Proof.
  intros; intro; inversion H.
Qed.

Lemma judge4 : ∀ {b k}, [N b , k] <> nC.
Proof.
  intros; intro; inversion H.
Qed.

Lemma Lemma_D71 : ∀ {b α}, α <> nC -> (Rep_T b (Con_C α)) <> nC.
Proof.
  intros; intro; apply Theorem289 in H0; destruct H0.
  unfold Con_C in H0; auto.
Qed.

Definition PowCn α j : (judge α j) -> Cn := 
  match j with 
   | Po a => λ _, Rep_T a (Con_C α)
   | ZO => match α with
            | [O,O] => λ l, match l return Cn with end
            | _ => λ _, eC
           end
   | Ne b => 
      match α with
       | [O,O] => λ l, match l with end
       | [O,P j] => λ _,(eC /# (Rep_T b (Con_C [O,P j]))) (Lemma_D71 judge1)
       | [O,N k] => λ _,(eC /# (Rep_T b (Con_C [O,N k]))) (Lemma_D71 judge2)
       | [P j,r] => λ _,(eC /# (Rep_T b (Con_C [P j,r]))) (Lemma_D71 judge3)
       | [N k,r] => λ _,(eC /# (Rep_T b (Con_C [N k,r]))) (Lemma_D71 judge4)
      end
  end.

Notation " α #^ j " := (PowCn α j)(at level 15).

Corollary jud_NnC :∀ {α j}, α <> nC -> judge α j.
Proof.
  intros; destruct j; simpl; auto; destruct α, r, r0; auto.
Qed. 

Corollary jud_P :∀ {α j}, judge α (Po j).
Proof.
  intros; simpl; auto.
Qed.

Corollary jud_P1 :∀ {α k}, ILT_Z ZO k -> judge α k.
Proof.
  intros; destruct k; inversion H; simpl; auto.
Qed.

Corollary jud_P2 :∀ {α j k},
  ILT_Z ZO j -> ILT_Z ZO k -> judge α (Plus_Z j k).
Proof.
  intros; destruct j, k; inversion H; inversion H0; simpl; auto.
Qed.

Corollary jud_P3 : ∀ {a b}, judge a (Ne b) -> judge a (Po b).
Proof.
  intros; destruct a, r, r0, H; simpl; auto.
Qed.

Corollary jud_P4 : ∀ {a b} l, (a #^ Po b) (jud_P3 l) <> nC.
Proof.
  intros; destruct a, r, r0, l; simpl;
  apply Lemma_D71; intro; inversion H.
Qed.

Corollary powOP : ∀ α l, (nC#^(Po α)) l = nC.
Proof.
  intros; simpl; induction α; intros;
  unfold Rep_T; simpl; unfold Con_C; Simpl_Cn.
Qed.

Corollary pow_O : ∀ α l, (α#^ZO) l = eC.
Proof.
  intros; destruct α, r, r0; simpl; auto.
  elim l; auto.
Qed.

Corollary pow_N : ∀ α b l, 
  (α#^(Ne b)) l = ((eC /# ((α#^(Po b)) (jud_P3 l)))) (jud_P4 l).
Proof.
  intros; destruct α, r, r0, l; simpl;
  try apply Lemma_D71; f_equal; apply proof_irr.
Qed.

Theorem Theorem290 : ∀ {α j l}, α <> nC -> (α#^j) l <> nC.
Proof.
  intros; intro; destruct j; simpl in l.
  - eapply Lemma_D71; eauto.
  - rewrite pow_O in H0; inversion H0.
  - rewrite pow_N in H0.
    assert (eC <> nC). { intro; inversion H1. }
    eapply Lemma_T242; eauto.
Qed.

Theorem Theorem291 : ∀ α l, (α#^(Po 1)) l = α.
Proof.
  intros; unfold PowCn, Rep_T; simpl; unfold Con_C; auto.
Qed.

Theorem Theorem292 : ∀ α β k l l1 l2,
  ILT_Z ZO k -> ((α ·# β)#^k) l = ((α#^k) l1) ·# ((β#^k) l2).
Proof.
  intros; set (M292 :=  /{ n | Rep_T n (Con_C (α ·# β)) = 
  (Rep_T n (Con_C α)) ·# (Rep_T n (Con_C β)) /}).
  assert (1 ∈ M292). { constructor; unfold Rep_T;
    repeat rewrite Rep_1; unfold Con_C; auto. }
  assert (∀ n, n ∈ M292 -> n` ∈ M292); intros.
  { destruct H1; constructor.
    unfold Rep_T; simpl; unfold Con_C at 2 4 6.
    unfold Rep_T in H1; rewrite H1. repeat rewrite <- Theorem226.
    rewrite (Theorem226 _ _ α), (Theorem220 _ α), <- Theorem226;
    auto. } assert (∀ n, n ∈ M292). { apply AxiomV; auto. }
  destruct k; inversion H. destruct H2 with n; auto.
Qed.

Theorem Theorem292' : 
  ∀ α β k l l1 l2, α <> nC -> β <> nC ->
  ((α ·# β)#^k) l = ((α#^k) l1) ·# ((β#^k) l2).
Proof.
  intros; destruct k.
  - apply Theorem292; simpl; auto.
  - repeat rewrite pow_O; Simpl_Cn.
  - repeat rewrite pow_N. rewrite Theorem247, Theorem222.
    apply Theorem252; rewrite Theorem222, Theorem222'.
    symmetry; apply Theorem292; simpl; auto.
Qed.

Theorem T292_1 : ∀ α β k l l1, 
  ((α ·# β)#^k) l = ((α#^k) (jud_P1 l1)) ·# ((β#^k) (jud_P1 l1)).
Proof.
  intros; apply Theorem292; auto.
Qed.

Theorem T292_2 : ∀ α β k l l1 l2, 
  ((α#^k) l) ·# ((β#^k) l1) = ((α ·# β)#^k) (jud_P1 l2).
Proof.
  symmetry; apply Theorem292; auto.
Qed.

Theorem Theorem293 : ∀ j l, (eC#^j) l = eC.
Proof.
  assert (∀ n, RepZ n (Con_C eC) Times_Cn = eC).
  { induction n; simpl; unfold Con_C in *; auto.
    rewrite IHn; Simpl_Cn. }
  intros; destruct j; simpl; unfold Rep_T; auto.
  symmetry; apply CnOv_uni; Simpl_Cn.
Qed.

Theorem Theorem294 : ∀ α j k l l1 l2, ILT_Z ZO j -> ILT_Z ZO k -> 
  ((α#^j) l) ·# ((α#^k) l1) = (α#^(Plus_Z j k)) l2.
Proof.
  intros; destruct j, k; inversion H; inversion H0.
  symmetry; simpl PowCn; apply Theorem281t.
Qed.

Theorem T294_1 : ∀ α j k l l1 l2 l3,
  ((α#^j) l) ·# ((α#^k) l1) = (α#^(Plus_Z j k)) (jud_P2 l2 l3).
Proof.
  intros; apply Theorem294; auto.
Qed.

Theorem T294_2 : ∀ α j k l l1 l2,
  (α#^(Plus_Z j k)) l = ((α#^j) (jud_P1 l1)) ·# ((α#^k) (jud_P1 l2)).
Proof.
  symmetry; apply Theorem294; auto.
Qed.

Lemma Lemma_T294  : ∀ α j k l l1, 
  ((α#^(Po j)) l) ·# ((α#^(Po k)) l1) =
  (α#^(Plus_Z (Po j) (Po k))) jud_P.
Proof. 
  intros; simpl; rewrite Theorem281t; auto.
Qed.

Lemma Lemma_T294'  : ∀ α j k l, 
  ((α#^(Po j)) (jud_NnC l)) ·# ((α#^(Po k)) (jud_NnC l)) =
  (α#^(Plus_Z (Po j) (Po k))) (jud_NnC l).
Proof. 
  intros; simpl; rewrite Theorem281t; auto.
Qed.

Theorem Theorem294' : ∀ {α j k l l1} l2, 
  ((α#^j) l) ·# ((α#^k) l1) = (α#^(Plus_Z j k)) (jud_NnC l2).
Proof.
  assert (∀ α β l, β ·# ((eC /# α) l) = (β /# α) l) as G1.
  { intros; apply CnOv_uni; rewrite Theorem220, Theorem226;
    Simpl_Cn. } intros; destruct j, k.
  - simpl; rewrite Theorem281t; auto.
  - rewrite pow_O; Simpl_Cn.
  - unfold Plus_Z; simpl in l2;
    destruct (Ncase n n0) as [[H | H] | H].
    + rewrite pow_N, G1, pow_N. apply Theorem252; Simpl_Cn.
      rewrite Theorem220, Lemma_T294; simpl; Simpl_N. 
    + rewrite pow_N, G1; symmetry; apply CnOv_uni.
      rewrite Theorem220, Lemma_T294; simpl; Simpl_N. 
    + rewrite H, pow_O, pow_N; Simpl_Cn.
  - simpl Plus_Z; rewrite pow_O; Simpl_Cn.
  - simpl Plus_Z; repeat rewrite pow_O; Simpl_Cn.
  - simpl Plus_Z; rewrite pow_O; Simpl_Cn; f_equal; apply proof_irr.
  - unfold Plus_Z; simpl in l2;
    destruct (Ncase n n0) as [[H | H] | H].
    + rewrite Theorem220, pow_N, G1. symmetry; apply CnOv_uni.
      rewrite Lemma_T294; simpl; rewrite Theorem6; Simpl_N.
    + rewrite Theorem220, pow_N, pow_N, G1.
      apply Theorem252; Simpl_Cn.
      rewrite Lemma_T294; simpl; rewrite Theorem6; Simpl_N.
    + rewrite H, pow_N, Theorem220, pow_O; Simpl_Cn.
  - simpl Plus_Z; rewrite pow_O; Simpl_Cn; f_equal; apply proof_irr.
  - simpl Plus_Z; repeat rewrite pow_N.
    rewrite Theorem247; Simpl_Cn.
    apply Theorem252; Simpl_Cn.
    rewrite Lemma_T294; simpl; auto.
Qed.

Theorem Theorem295 : ∀ α j k l l1 l2 l3, α <> nC ->
  (((α#^j) l) /# ((α#^k) l1)) l2 = 
  (α#^(Minus_Z j k)) l3.
Proof.
  intros; symmetry; apply CnOv_uni.
  rewrite Theorem220, (Theorem294' H), ZPlup4.
  f_equal; apply proof_irr.
Qed.

Theorem T295_1  : ∀ α j k l l1 l2 l3,
  (((α#^j) l) /# ((α#^k) l1)) l2 = (α#^(Minus_Z j k)) (jud_NnC l3).
Proof. 
  intros; apply Theorem295; auto.
Qed.

Theorem T295_2  : ∀ α j k l, 
  (α#^(Minus_Z j k)) (jud_NnC l) = 
  (((α#^j) (jud_NnC l)) /# ((α#^k) (jud_NnC l))) (Theorem290 l).
Proof. 
  symmetry; apply Theorem295; auto.
Qed.

Theorem Theorem296 :
  ∀ α j l, (eC /# ((α#^j) (jud_NnC l))) (Theorem290 l) =
  (α#^(minus_Z j)) (jud_NnC l).
Proof.
  intros; symmetry; apply CnOv_uni.
  rewrite (Theorem294' l), ZPlup3, pow_O; auto.
Qed.

Lemma Lemma_T297 : ∀ α j n l, 
  (((α#^j) (jud_NnC l))#^(Po n)) (jud_NnC (Theorem290 l)) = 
  (α#^(Times_Z j (Po n))) (jud_NnC l).
Proof.
  intros; induction n.
  - unfold Rep_T, Con_C; rewrite ZTimp2; auto.
  - rewrite <- NPl_1.
    replace (Po (Plus_N n 1)) with (Plus_Z (Po n) (Po 1)); auto.
    rewrite <- Lemma_T294', IHn, (proof_irr _ jud_P), Theorem291.
    rewrite (Theorem294' l), ZTi_dis, ZTimp2; auto.
Qed.

Theorem Theorem297 : ∀ α j k l,
  (((α#^j) (jud_NnC l))#^k) (jud_NnC (Theorem290 l)) = 
  (α#^(Times_Z j k)) (jud_NnC l).
Proof.
  intros; destruct k.
  - apply Lemma_T297.
  - destruct j; simpl Times_Z; repeat rewrite pow_O; auto.
  - assert (Ne n = minus_Z  (Po n)). { simpl; auto. }
    rewrite pow_N; symmetry. apply CnOv_uni.
    rewrite (proof_irr _ (jud_NnC (Theorem290 l))), Lemma_T297.
    rewrite (Theorem294' l), <- ZTi_dis, H.
    rewrite ZPlup3, ZTimp3, pow_O; auto.
Qed.

Theorem Theorem297' : ∀ α j k l l1 l2, ILT_Z ZO j -> ILT_Z ZO k -> 
  (((α#^j) l)#^k) l1 = (α#^(Times_Z j k)) l2.
Proof.
  intros; destruct j, k; inversion H; inversion H0.
  destruct (classic (α = nC)) as [H1 | H1].
  - subst α; repeat rewrite powOP;
    simpl Times_Z; symmetry; apply powOP.
  - repeat rewrite (proof_irr jud_P (jud_NnC H)).
    rewrite (proof_irr l2 (jud_NnC H1)), <- Theorem297.
    f_equal; apply proof_irr.
Qed.

(* SECTION V Incorporation of the Real Numbers into the System of Complex Numbers *)

Theorem Theorem298_1 : ∀ Ξ Γ, [Ξ+Γ,O] = [Ξ,O] +# [Γ,O].
Proof.
  intros; simpl; auto.
Qed.

Theorem Theorem298_2 : ∀ Ξ Γ, [Ξ-Γ,O] = [Ξ,O] -# [Γ,O].
Proof.
  intros; simpl; auto.
Qed.

Theorem Theorem298_3 : ∀ Ξ Γ, [Ξ·Γ,O] = [Ξ,O] ·# [Γ,O].
Proof.
  intros; simpl; Simpl_R.
Qed.

Lemma Lemma_T298 : ∀ {Ξ}(l:neq_zero Ξ), [Ξ,O] <> nC.
Proof.
  intros; intro; inversion H; subst Ξ; destruct l.
Qed.

Theorem Theorem298_4 : ∀ Ξ Γ l,
  [(Ξ/Γ)l,O] = ([Ξ,O]/#[Γ,O])(Lemma_T298 l).
Proof.
  intros; apply CnOv_uni; simpl; rewrite Theorem194; Simpl_R.
Qed.

Theorem Theorem298_5 : ∀ Ξ, [-Ξ,O] = -#[Ξ,O].
Proof.
  intros; simpl; auto.
Qed.

Theorem Theorem298_6 : ∀ Ξ, |-[Ξ,O]-| = |Ξ|.
Proof.
  assert (∀ ξ, √ (Times_C ξ ξ) ≈ ξ) as G.
  { assert (∀ ξ η,
      ILT_C (Times_C η η) (Times_C ξ ξ) <-> ILT_C η ξ) as G.
    { split; intros.
      - destruct (Theorem123 ξ η) as [H0 | [H0 |H0]]; auto.
        + LGC H (Theorem147 H0 H0).
        + rewrite (eq2 H0) in H; ELC (Theorem116 (Times_C η η)) H.
      - apply Theorem122 in H; apply Theorem121; eapply Theorem147;
        eauto. } split; intros.
    - destruct H; apply -> G in H; apply Theorem158_1; auto.
    - constructor; apply G; apply Theorem158_1; auto. }
  intros; destruct Ξ; simpl; try rewrite (eq2 (G c)); auto.
Qed.

Definition M299 := /{ x | ∃ y :Nat, [y,O] = x /}.

Theorem Theorem299_1 : [1,O] ∈ M299.
Proof.
  intros; constructor; eauto.
Qed.

Theorem Theorem299_2 : ∀ x :Nat, [x,O] ∈ M299 -> [x`,O] ∈ M299.
Proof.
  intros; destruct H; constructor; eauto.
Qed.

Theorem Theorem299_3 : ∀ x :Nat, [x`,O]  <> [1,O].
Proof.
  intros; intro; apply eq4 in H; destruct H.
  apply eq3 in H; simpl in H.
  eapply Theorem156_3; eauto.
Qed.

Theorem Theorem299_4 : ∀ x y :Nat, [x`,O] = [y`,O] -> [x,O] = [y,O].
Proof.
  intros; apply eq4 in H; destruct H.
  apply eq3 in H; simpl in H; apply Theorem156_4 in H.
   unfold Real_PZ, Cut_I; rewrite (eq2 H); auto.
Qed.

Theorem Theorem299_5 :  ∀ M, [1,O] ∈ M /\ 
  (∀ x:Nat, [x,O] ∈ M -> [x`,O] ∈ M) -> ∀ z:Nat, [z,O] ∈ M.
Proof.
  intros; destruct H. set (M299_5 := /{ x | [(Real_PZ x),O] ∈ M /}).
  assert (1 ∈ (M299_5)). { constructor; auto. }
  assert (∀ x, x ∈ (M299_5) -> x` ∈ (M299_5)); intros.
  { destruct H2; constructor; auto. }
  assert (∀ x, x ∈ (M299_5)). { apply AxiomV; auto. }
  destruct H3 with z; auto.
Qed.

Coercion RCn R := Pair R O.

Definition ｉ := [O,1].

Theorem Theorem300 : ｉ ·# ｉ = - (1).
Proof.
  intros; simpl; rewrite (eq2 Theorem151); auto.
Qed.

Theorem Theorem301a : ∀ u1 u2 :Real, u1 +# (u2 ·# ｉ) = [u1, u2].
Proof.
  intros; simpl; Simpl_R.
Qed.

Theorem Theorem301b : ∀ x, ∃ u1 u2 :Real, x = u1 +# u2 ·# ｉ.
Proof.
  intros; destruct x as [u1 u2].
  exists u1, u2; simpl; Simpl_R.
Qed.

Theorem Theorem301b' : ∀ x (u1 u2 v1 v2 :Real),
  x = u1 +# u2 ·# ｉ -> x = v1 +# v2 ·# ｉ -> u1 = v1 /\ u2 = v2.
Proof.
  intros; subst x; repeat rewrite Theorem301a in H0.
  inversion H0; auto.
Qed.
