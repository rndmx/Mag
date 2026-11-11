/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Sec10PrintedTorsor

/-!
# Difference and sum of lifts, compatibly with the action

Mayeux, *Algebraic Magnetism*, proof of Proposition 10.1: `g · a + g · v = g · (a + v)` (Tag 0618 in the
printed proof), on the test objects `D(P)`.
-/

open CategoryTheory AlgebraicGeometry Opposite

universe u

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace AlgMag.Sec10Printed

open AlgMag.GB AlgMag.Lifts

attribute [local instance] Stacks.Smooth.moduleMulOpposite

lemma sp_mr_assoc {P : Type u} [AddCommMonoid P] {R S W : Type u} [CommRing R] [CommRing S] [CommRing W]
    (g : S →+* W) (h : R →+* S) {Y : Scheme.{u}} (X : Spec (CommRingCat.of (AddMonoidAlgebra R P)) ⟶ Y) :
    sp (mr P g) ≫ sp (mr P h) ≫ X = sp (mr P (g.comp h)) ≫ X := by
  rw [← Category.assoc, sp_mr]

lemma aug_of {W M : Type u} [CommRing W] [AddCommGroup M] (k : M) :
    aug W M (AddMonoidAlgebra.single k 1) = 1 := (lft_of _ _ k).trans rfl

lemma aug_cs {W M : Type u} [CommRing W] [AddCommGroup M] : (aug W M).comp (cs W M) = RingHom.id W :=
  lft_cs _ _

lemma aug_mr {W W₁ M : Type u} [CommRing W] [CommRing W₁] [AddCommGroup M] (w : W →+* W₁) :
    (aug W₁ M).comp (mr M w) = w.comp (aug W M) := by
  refine rh_ext ?_ fun k => ?_
  · rw [RingHom.comp_assoc, mr_cs, ← RingHom.comp_assoc, aug_cs, RingHom.id_comp,
      RingHom.comp_assoc, aug_cs, RingHom.comp_id]
  · simp only [RingHom.comp_apply]
    rw [mr_single, map_one, aug_of, aug_of, map_one]

section Coaction

variable {M : Type u} [AddCommGroup M]
variable {A₁ A : Type u} [CommRing A₁] [CommRing A] {φ : A₁ →+* A} (hs : Function.Surjective φ)
  [Module A (RingHom.ker φ)]
  (hN : ∀ (x : A₁) (n : RingHom.ker φ), ((φ x • n : RingHom.ker φ) : A₁) = x * n)
  (hq : ∀ x y, φ x = 0 → φ y = 0 → x * y = 0)
  (ρ : A₁ →+* AddMonoidAlgebra A₁ M) (ρ₀ : A →+* AddMonoidAlgebra A M)
  (hρφ : (mr M φ).comp ρ = ρ₀.comp φ)

/-- The coaction on `A₁ ×_A A₁`. -/
noncomputable def ϱD : Dd φ →+* AddMonoidAlgebra (Dd φ) M :=
  liftM (milnor_map (milnor_D φ hs) M) (ρ.comp (d₁ φ)) (ρ.comp (d₂ φ)) (fun z => by
    have h := RingHom.congr_fun hρφ
    simp only [RingHom.comp_apply] at h ⊢
    rw [h, h]
    exact congrArg ρ₀ z.2)

lemma ϱD_1 : (mr M (d₁ φ)).comp (ϱD hs ρ ρ₀ hρφ) = ρ.comp (d₁ φ) := liftM_p _ _ _ _
lemma ϱD_2 : (mr M (d₂ φ)).comp (ϱD hs ρ ρ₀ hρφ) = ρ.comp (d₂ φ) := liftM_q _ _ _ _

lemma ϱD_Δ : (ϱD hs ρ ρ₀ hρφ).comp (dΔ φ) = (mr M (dΔ φ)).comp ρ := by
  refine rh_milnor (milnor_map (milnor_D φ hs) M) ?_ ?_
  · rw [← RingHom.comp_assoc, ϱD_1, RingHom.comp_assoc, d₁_Δ, RingHom.comp_id, ← RingHom.comp_assoc,
      mr_comp, d₁_Δ, mr_id, RingHom.id_comp]
  · rw [← RingHom.comp_assoc, ϱD_2, RingHom.comp_assoc, d₂_Δ, RingHom.comp_id, ← RingHom.comp_assoc,
      mr_comp, d₂_Δ, mr_id, RingHom.id_comp]

lemma ϱD_ker (z : Dd φ) (hz : qq hN hq z = 0) : mr M (qq hN hq) (ϱD hs ρ ρ₀ hρφ z) = 0 := by
  have h₀ : φ (d₁ φ z) = 0 := by rw [← qq_fst hN hq, hz]; rfl
  have h₁ : d₁ φ z = d₂ φ z := by
    have := congrArg Subtype.val ((qq_snd hN hq z).symm.trans (congrArg TrivSqZeroExt.snd hz))
    exact sub_eq_zero.1 this
  refine AddMonoidAlgebra.ext (Finsupp.ext fun k => ?_)
  rw [coeff_mr]
  have e₁ : d₁ φ ((ϱD hs ρ ρ₀ hρφ z).coeff k) = (ρ (d₁ φ z)).coeff k := by
    have := RingHom.congr_fun (ϱD_1 hs ρ ρ₀ hρφ) z
    rw [RingHom.comp_apply, RingHom.comp_apply] at this
    rw [← this, coeff_mr]
  have e₂ : d₂ φ ((ϱD hs ρ ρ₀ hρφ z).coeff k) = (ρ (d₂ φ z)).coeff k := by
    have := RingHom.congr_fun (ϱD_2 hs ρ ρ₀ hρφ) z
    rw [RingHom.comp_apply, RingHom.comp_apply] at this
    rw [← this, coeff_mr]
  refine sq_ext ?_ (Subtype.ext ?_)
  · rw [qq_fst, e₁]
    have h := RingHom.congr_fun hρφ (d₁ φ z)
    simp only [RingHom.comp_apply] at h
    rw [h₀, map_zero] at h
    have := congrArg (fun w => w.coeff k) h
    simp only [coeff_mr] at this
    exact this
  · rw [qq_snd, kk_val, e₁, e₂, h₁, sub_self]
    rfl

/-- The coaction on `A[N]`. -/
noncomputable def ϱN : Sq A (RingHom.ker φ) →+* AddMonoidAlgebra (Sq A (RingHom.ker φ)) M :=
  RingHom.liftOfSurjective (qq hN hq) (qq_surj hN hq hs)
    ⟨(mr M (qq hN hq)).comp (ϱD hs ρ ρ₀ hρφ), fun z hz => ϱD_ker hs hN hq ρ ρ₀ hρφ z hz⟩

lemma ϱN_q : (ϱN hs hN hq ρ ρ₀ hρφ).comp (qq hN hq) = (mr M (qq hN hq)).comp (ϱD hs ρ ρ₀ hρφ) :=
  RingHom.ext fun z => RingHom.liftOfRightInverse_comp_apply (qq hN hq) (Function.surjInv (qq_surj hN hq hs)) (Function.rightInverse_surjInv _)
    ⟨(mr M (qq hN hq)).comp (ϱD hs ρ ρ₀ hρφ), fun z hz => ϱD_ker hs hN hq ρ ρ₀ hρφ z hz⟩ z

include hs in
lemma cancel_q {E : Type u} [CommRing E] {r s : Sq A (RingHom.ker φ) →+* E}
    (h : r.comp (qq hN hq) = s.comp (qq hN hq)) : r = s :=
  (RingHom.cancel_right (qq_surj hN hq hs)).1 h

include hs in
lemma cancel_φ {E : Type u} [CommRing E] {r s : A →+* E} (h : r.comp φ = s.comp φ) : r = s :=
  (RingHom.cancel_right hs).1 h

lemma fst_ϱN : (mr M (sFst (RingHom.ker φ))).comp (ϱN hs hN hq ρ ρ₀ hρφ) = ρ₀.comp (sFst _) := by
  refine cancel_q hs hN hq ?_
  have e : (ρ₀.comp (sFst _)).comp (qq hN hq) = ρ₀.comp (φ.comp (d₁ φ)) := by
    rw [RingHom.comp_assoc, sFst_qq]
  rw [RingHom.comp_assoc, ϱN_q, ← RingHom.comp_assoc, mr_comp, sFst_qq, e,
    ← mr_comp, RingHom.comp_assoc, ϱD_1, ← RingHom.comp_assoc, hρφ, RingHom.comp_assoc]

lemma ϱN_inl : (ϱN hs hN hq ρ ρ₀ hρφ).comp (sInl _) = (mr M (sInl (RingHom.ker φ))).comp ρ₀ := by
  refine cancel_φ hs ?_
  have e : (sInl (RingHom.ker φ)).comp φ = (qq hN hq).comp (dΔ φ) := (qq_Δ hN hq).symm
  rw [RingHom.comp_assoc, e, ← RingHom.comp_assoc, ϱN_q, RingHom.comp_assoc, ϱD_Δ, ← RingHom.comp_assoc,
    mr_comp, ← e, ← mr_comp, RingHom.comp_assoc, RingHom.comp_assoc, ← hρφ]

variable (hco : ∀ x, mr M ρ (ρ x) = Lifts.diag A₁ M (ρ x))

lemma diag_mr {W W₁ : Type u} [CommRing W] [CommRing W₁] (w : W →+* W₁) :
    (Lifts.diag W₁ M).comp (mr M w) = (mr M (mr M w)).comp (Lifts.diag W M) :=
  RingHom.ext fun x => (map_diag w x).symm

include hco in
lemma hcoD : (mr M (ϱD hs ρ ρ₀ hρφ)).comp (ϱD hs ρ ρ₀ hρφ) =
    (Lifts.diag (Dd φ) M).comp (ϱD hs ρ ρ₀ hρφ) := by
  have key : ∀ (d : Dd φ →+* A₁), (mr M d).comp (ϱD hs ρ ρ₀ hρφ) = ρ.comp d →
      (mr M (mr M d)).comp ((mr M (ϱD hs ρ ρ₀ hρφ)).comp (ϱD hs ρ ρ₀ hρφ)) =
      (mr M (mr M d)).comp ((Lifts.diag (Dd φ) M).comp (ϱD hs ρ ρ₀ hρφ)) := by
    intro d hd
    refine RingHom.ext fun z => ?_
    simp only [RingHom.comp_apply]
    have h : mr M d (ϱD hs ρ ρ₀ hρφ z) = ρ (d z) := RingHom.congr_fun hd z
    calc mr M (mr M d) (mr M (ϱD hs ρ ρ₀ hρφ) (ϱD hs ρ ρ₀ hρφ z))
        = mr M ((mr M d).comp (ϱD hs ρ ρ₀ hρφ)) (ϱD hs ρ ρ₀ hρφ z) := by
          rw [← RingHom.comp_apply, mr_comp]
      _ = mr M (ρ.comp d) (ϱD hs ρ ρ₀ hρφ z) := by rw [hd]
      _ = mr M ρ (mr M d (ϱD hs ρ ρ₀ hρφ z)) := by rw [← mr_comp]; rfl
      _ = mr M ρ (ρ (d z)) := by rw [h]
      _ = Lifts.diag A₁ M (ρ (d z)) := hco _
      _ = Lifts.diag A₁ M (mr M d (ϱD hs ρ ρ₀ hρφ z)) := by rw [h]
      _ = _ := (map_diag d _).symm
  exact rh_milnor (milnor_map (milnor_map (milnor_D φ hs) M) M) (key _ (ϱD_1 hs ρ ρ₀ hρφ))
    (key _ (ϱD_2 hs ρ ρ₀ hρφ))

include hco in
lemma hcoN (x : Sq A (RingHom.ker φ)) :
    mr M (ϱN hs hN hq ρ ρ₀ hρφ) (ϱN hs hN hq ρ ρ₀ hρφ x) = Lifts.diag _ M (ϱN hs hN hq ρ ρ₀ hρφ x) := by
  have : (mr M (ϱN hs hN hq ρ ρ₀ hρφ)).comp (ϱN hs hN hq ρ ρ₀ hρφ) =
      (Lifts.diag _ M).comp (ϱN hs hN hq ρ ρ₀ hρφ) := by
    refine cancel_q hs hN hq ?_
    rw [RingHom.comp_assoc, RingHom.comp_assoc, ϱN_q, ← RingHom.comp_assoc, mr_comp, ϱN_q, ← mr_comp,
      RingHom.comp_assoc, hcoD hs ρ ρ₀ hρφ hco, ← RingHom.comp_assoc, ← diag_mr, RingHom.comp_assoc]
  exact RingHom.congr_fun this x

variable (hc : (aug A₁ M).comp ρ = RingHom.id _)

include hc in
lemma hcD : (aug (Dd φ) M).comp (ϱD hs ρ ρ₀ hρφ) = RingHom.id _ := by
  refine rh_milnor (milnor_D φ hs) ?_ ?_
  · rw [← RingHom.comp_assoc, ← aug_mr, RingHom.comp_assoc, ϱD_1, ← RingHom.comp_assoc, hc,
      RingHom.id_comp, RingHom.comp_id]
  · rw [← RingHom.comp_assoc, ← aug_mr, RingHom.comp_assoc, ϱD_2, ← RingHom.comp_assoc, hc,
      RingHom.id_comp, RingHom.comp_id]

include hc in
lemma hcN : (aug _ M).comp (ϱN hs hN hq ρ ρ₀ hρφ) = RingHom.id _ := by
  refine cancel_q hs hN hq ?_
  rw [RingHom.comp_assoc, ϱN_q, ← RingHom.comp_assoc, aug_mr, RingHom.comp_assoc, hcD hs ρ ρ₀ hρφ hc,
    RingHom.comp_id, RingHom.id_comp]

/-- The coaction on `A[N × N]`. -/
noncomputable def ϱ₂ : Sq A (RingHom.ker φ × RingHom.ker φ) →+*
    AddMonoidAlgebra (Sq A (RingHom.ker φ × RingHom.ker φ)) M :=
  liftM (milnor_map milnor_prod M) ((ϱN hs hN hq ρ ρ₀ hρφ).comp (sMap (LinearMap.fst A _ _)))
    ((ϱN hs hN hq ρ ρ₀ hρφ).comp (sMap (LinearMap.snd A _ _))) (fun z => by
      have h := RingHom.congr_fun (fst_ϱN hs hN hq ρ ρ₀ hρφ)
      simp only [RingHom.comp_apply] at h ⊢
      rw [h, h]
      simp)

lemma ϱ₂_1 : (mr M (sMap (LinearMap.fst A _ _))).comp (ϱ₂ hs hN hq ρ ρ₀ hρφ) =
    (ϱN hs hN hq ρ ρ₀ hρφ).comp (sMap (LinearMap.fst A _ _)) := liftM_p _ _ _ _
lemma ϱ₂_2 : (mr M (sMap (LinearMap.snd A _ _))).comp (ϱ₂ hs hN hq ρ ρ₀ hρφ) =
    (ϱN hs hN hq ρ ρ₀ hρφ).comp (sMap (LinearMap.snd A _ _)) := liftM_q _ _ _ _

lemma sMap_zero' : sMap (0 : RingHom.ker φ →ₗ[A] RingHom.ker φ) = (sInl _).comp (sFst _) :=
  RingHom.ext fun _ => sq_ext (by simp) (by simp)

lemma ϱ₂_of_inj (u v : RingHom.ker φ →ₗ[A] RingHom.ker φ) (h : (u = LinearMap.id ∧ v = 0) ∨ (u = 0 ∧ v = LinearMap.id)) :
    (ϱ₂ hs hN hq ρ ρ₀ hρφ).comp (sMap (LinearMap.prod u v)) =
      (mr M (sMap (LinearMap.prod u v))).comp (ϱN hs hN hq ρ ρ₀ hρφ) := by
  have key : ∀ w : RingHom.ker φ →ₗ[A] RingHom.ker φ, (w = LinearMap.id ∨ w = 0) →
      (ϱN hs hN hq ρ ρ₀ hρφ).comp (sMap w) = (mr M (sMap w)).comp (ϱN hs hN hq ρ ρ₀ hρφ) := by
    rintro w (rfl | rfl)
    · rw [sMap_id, mr_id, RingHom.comp_id, RingHom.id_comp]
    · rw [sMap_zero', ← RingHom.comp_assoc, ϱN_inl, ← mr_comp, RingHom.comp_assoc, RingHom.comp_assoc,
        fst_ϱN]
  have hu : u = LinearMap.id ∨ u = 0 := by rcases h with h | h <;> simp [h]
  have hv : v = LinearMap.id ∨ v = 0 := by rcases h with h | h <;> simp [h]
  refine rh_milnor (milnor_map milnor_prod M) ?_ ?_
  · rw [← RingHom.comp_assoc, ϱ₂_1, RingHom.comp_assoc, sMap_comp, ← RingHom.comp_assoc, mr_comp, sMap_comp]
    exact key u hu
  · rw [← RingHom.comp_assoc, ϱ₂_2, RingHom.comp_assoc, sMap_comp, ← RingHom.comp_assoc, mr_comp, sMap_comp]
    exact key v hv

lemma ϱ_add : (ϱN hs hN hq ρ ρ₀ hρφ).comp (sMap (LinearMap.fst A (RingHom.ker φ) (RingHom.ker φ) + LinearMap.snd A (RingHom.ker φ) (RingHom.ker φ))) =
    (mr M (sMap (LinearMap.fst A (RingHom.ker φ) (RingHom.ker φ) + LinearMap.snd A (RingHom.ker φ) (RingHom.ker φ)))).comp (ϱ₂ hs hN hq ρ ρ₀ hρφ) := by
  refine RingHom.ext fun y => ?_
  have e : y = sMap (LinearMap.prod LinearMap.id 0 : RingHom.ker φ →ₗ[A] RingHom.ker φ × RingHom.ker φ) (TrivSqZeroExt.inl y.fst + TrivSqZeroExt.inr y.snd.1) +
      sMap (LinearMap.prod 0 LinearMap.id : RingHom.ker φ →ₗ[A] RingHom.ker φ × RingHom.ker φ) (TrivSqZeroExt.inr y.snd.2) := by
    refine sq_ext ?_ (Prod.ext ?_ ?_) <;> simp
  have h₁ := fun t => RingHom.congr_fun (ϱ₂_of_inj hs hN hq ρ ρ₀ hρφ LinearMap.id 0 (Or.inl ⟨rfl, rfl⟩)) t
  have h₂ := fun t => RingHom.congr_fun (ϱ₂_of_inj hs hN hq ρ ρ₀ hρφ 0 LinearMap.id (Or.inr ⟨rfl, rfl⟩)) t
  simp only [RingHom.comp_apply] at h₁ h₂ ⊢
  have c₁ : ∀ t : AddMonoidAlgebra (Sq A (RingHom.ker φ)) M, mr M (sMap (LinearMap.fst A (RingHom.ker φ) (RingHom.ker φ) + LinearMap.snd A (RingHom.ker φ) (RingHom.ker φ)))
      (mr M (sMap (LinearMap.prod LinearMap.id 0 : RingHom.ker φ →ₗ[A] RingHom.ker φ × RingHom.ker φ)) t) = t := fun t => by
    rw [← RingHom.comp_apply, mr_comp, sMap_comp]
    have : (LinearMap.fst A (RingHom.ker φ) (RingHom.ker φ) + LinearMap.snd A (RingHom.ker φ) (RingHom.ker φ)) ∘ₗ (LinearMap.prod LinearMap.id 0 : RingHom.ker φ →ₗ[A] RingHom.ker φ × RingHom.ker φ) =
        LinearMap.id := by ext; simp
    rw [this, sMap_id, mr_id]; rfl
  have c₂ : ∀ t : AddMonoidAlgebra (Sq A (RingHom.ker φ)) M, mr M (sMap (LinearMap.fst A (RingHom.ker φ) (RingHom.ker φ) + LinearMap.snd A (RingHom.ker φ) (RingHom.ker φ)))
      (mr M (sMap (LinearMap.prod 0 LinearMap.id : RingHom.ker φ →ₗ[A] RingHom.ker φ × RingHom.ker φ)) t) = t := fun t => by
    rw [← RingHom.comp_apply, mr_comp, sMap_comp]
    have : (LinearMap.fst A (RingHom.ker φ) (RingHom.ker φ) + LinearMap.snd A (RingHom.ker φ) (RingHom.ker φ)) ∘ₗ (LinearMap.prod 0 LinearMap.id : RingHom.ker φ →ₗ[A] RingHom.ker φ × RingHom.ker φ) =
        LinearMap.id := by ext; simp
    rw [this, sMap_id, mr_id]; rfl
  have d₁' : ∀ t : Sq A (RingHom.ker φ), sMap (LinearMap.fst A (RingHom.ker φ) (RingHom.ker φ) + LinearMap.snd A (RingHom.ker φ) (RingHom.ker φ))
      (sMap (LinearMap.prod LinearMap.id 0 : RingHom.ker φ →ₗ[A] RingHom.ker φ × RingHom.ker φ) t) = t := fun t => sq_ext (by simp) (by simp)
  have d₂' : ∀ t : Sq A (RingHom.ker φ), sMap (LinearMap.fst A (RingHom.ker φ) (RingHom.ker φ) + LinearMap.snd A (RingHom.ker φ) (RingHom.ker φ))
      (sMap (LinearMap.prod 0 LinearMap.id : RingHom.ker φ →ₗ[A] RingHom.ker φ × RingHom.ker φ) t) = t := fun t => sq_ext (by simp) (by simp)
  conv_lhs => rw [e, map_add, map_add, d₁', d₂']
  conv_rhs => rw [e, map_add, map_add, h₁, h₂, c₁, c₂]

end Coaction

end AlgMag.Sec10Printed
