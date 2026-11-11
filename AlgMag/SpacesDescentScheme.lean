/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.SpacesDescentProps

/-!
# Lemma D for a scheme

Mayeux, *Algebraic Magnetism*, Semigroup Forum 113 (2026). `AlgMag.SD.DescentProp` holds for a scheme `U`, by
`AlgMag.SQ.exists_desc_gen` and `AlgMag.SQ.desc_unique`. This checks the statement of Lemma D against the scheme
descent, and recovers Propositions 3.31 (ii), 3.32 (ii) for schemes from `AlgMag.SD.prop331_of_descent` and
`AlgMag.SD.prop332_of_descent`.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe u

namespace AlgMag.SD

open AlgMag AlgMag.SQ AlgMag.GenM

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

local notation "SCH" => BigFppfOver.toScheme B S hS

attribute [local instance] hasPullbacks_bigFppfOver preservesPullbacks_bigFppfOverToScheme

/-- `IsInvPt`, tested on the universal point of `D(Γ) × 𝔸(P)`, is the scheme invariance. -/
theorem isInvariantF_of_isInvPt {U : BigFppfOver B S hS} {P Γ : Type u} [AddCommMonoid P] [Countable P]
    [AddCommGroup Γ] [Countable Γ] (δ : P →+ Γ) {T : BigFppfOver B S hS} [IsAffine ((SCH).obj T)]
    (x : specObj P T ⟶ U) (hx : IsInvPt (yoneda.obj U) δ x) :
    IsInvariantF (monCoact (R := Γ((SCH).obj T, ⊤)) δ) ((SCH).map x) := by
  let A := gRing P T
  let ρ : RT T →+* AddMonoidAlgebra A Γ := (cC A Γ).comp (algebraMap _ _)
  have hC : B.Contains (Spec (.of (AddMonoidAlgebra A Γ))) := AlgMag.GenM.contains_M (contains_spec _ T)
  let t := spToT T ρ hC
  let σ : A →+* AddMonoidAlgebra A Γ := (monCoact (R := Γ((SCH).obj T, ⊤)) δ).σ
  have hσ : σ.comp (algebraMap _ _) = ρ := by
    refine RingHom.ext fun r => ?_
    change monσ _ (AddMonoidAlgebra.single 0 r) = _
    rw [monσ_single, map_zero]
    rfl
  let a₁ := spPt (T := T) (ρ := ρ) (hC := hC) (σ.toMonoidHom.comp (AddMonoidAlgebra.of _ _))
  let a₂ := spPt (T := T) (ρ := ρ) (hC := hC) ((cC A Γ).toMonoidHom.comp (AddMonoidAlgebra.of _ _))
  let E : Multiplicative Γ →* AddMonoidAlgebra A Γ := AddMonoidAlgebra.of _ _
  let e := spPt (T := T) (ρ := ρ) (hC := hC) E
  have ha : a₁ = e.comp (AddMonoidHom.toMultiplicative δ) * a₂ := by
    refine MonoidHom.ext fun p => ?_
    change spSec T ρ hC (σ (AddMonoidAlgebra.single (Multiplicative.toAdd p) 1)) =
      spSec T ρ hC _ * spSec T ρ hC _
    rw [← map_mul]
    congr 1
    change monσ _ _ = _
    rw [monσ_single]
    simp [E, cC, AddMonoidAlgebra.single_mul_single]
    rfl
  have heq := hx t e a₂
  rw [← ha] at heq
  have h1 := congrArg (fun k => (SCH).map k) (show specLift t a₁ ≫ x = specLift t a₂ ≫ x from heq)
  simp only [Functor.map_comp] at h1
  rw [map_specLift_spPt σ hσ, map_specLift_spPt (cC A Γ) rfl] at h1
  exact h1

/-- **Lemma D** for a scheme. -/
theorem descentProp_scheme (U : BigFppfOver B S hS) : DescentProp (yoneda.obj U) where
  uniq := by
    intro P P₀ Γ _ _ _ _ _ _ δ j hj hk T _ x y h
    have hι := monCoact_isInv (R := Γ((SCH).obj T, ⊤)) (δ := δ) hj hk
    apply toScheme_map_injective
    refine desc_unique hι.isSplit ?_
    have e0 : ∀ w : specObj P₀ T ⟶ U, sp (monι j Γ((SCH).obj T, ⊤)) ≫ (SCH).map w =
        (SCH).map (specAlong T j ≫ w) := fun w => by
      rw [Functor.map_comp]
      rfl
    rw [e0, e0]
    exact congrArg _ (show specAlong T j ≫ x = specAlong T j ≫ y from h)
  desc := by
    intro P P₀ Γ _ _ _ _ _ _ δ j hj hk T _ x hx
    have : Countable Γ := countable_of_fg Γ
    let R := Γ((SCH).obj T, ⊤)
    have hι := monCoact_isInv (R := R) (δ := δ) hj hk
    obtain ⟨f, hf⟩ := exists_desc_gen (R := R) δ hj hk (isInvariantF_of_isInvPt δ x hx)
    refine ⟨overHom f ?_, toScheme_map_injective ?_⟩
    · refine desc_unique hι.isSplit ?_
      have e1 : sp (monι j R) ≫ specPrS P₀ T = specPrS P T := by
        rw [sp_specPrS, monι_comp_algebraMap]
        rfl
      have e2 : (SCH).map x ≫ U.hom.hom = specPrS P T ≫ T.hom.hom := site_w x
      change sp (monι j R) ≫ f ≫ U.hom.hom = sp (monι j R) ≫ specPrS P₀ T ≫ T.hom.hom
      exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ U.hom.hom) hf).trans (e2.trans
        ((congrArg (· ≫ T.hom.hom) e1).symm.trans (Category.assoc _ _ _))))
    · change (SCH).map (specAlong T j ≫ overHom f _) = _
      rw [Functor.map_comp]
      exact hf

end AlgMag.SD

#print axioms AlgMag.SD.descentProp_scheme
