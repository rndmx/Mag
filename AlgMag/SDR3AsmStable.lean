/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.SDR3AsmOpen

/-!
# Lemma D, Step 4: equivariance, `V` is stable in `Spec C'`

For Props. 3.31 (ii), 3.32 (ii) of `Algebraic Magnetism`. The action on `𝒱` is used only on field-valued points. If the
generic point `ξ` of the orbit of `p` is in `𝒱`, translate by the universal `t⁻¹` to find `p` in `𝒱`.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe u

namespace AlgMag.SD

open AlgMag.SQ

/-- The ring map of a `K`-point. -/
noncomputable def SDR3Asm_ev {𝒱 : Scheme.{u}} {K : Type u} [CommRing K] (g : Spec (.of K) ⟶ 𝒱) : Γ(𝒱, ⊤) →+* K :=
  ((Scheme.ΓSpecIso (.of K)).hom.hom).comp g.appTop.hom

variable {Γ' : Type u} [AddCommGroup Γ']

/-- The action of `D(Γ)` on field-valued points of `𝒱`, read on global functions, for a coaction `cV` of `Γ(𝒱)`. -/
def SDR3Asm_ActsOnPoints {𝒱 : Scheme.{u}} (cV : Coact Γ(𝒱, ⊤) Γ') : Prop :=
  ∀ (L : Type u) [Field L] (v : Spec (.of L) ⟶ 𝒱) (χ : Multiplicative Γ' →* L),
    ∃ v' : Spec (.of L) ⟶ 𝒱, ∀ z, SDR3Asm_ev v' z =
      (cV.σ z).coeff.sum fun d a => χ (Multiplicative.ofAdd d) * SDR3Asm_ev v a

variable {𝒱 : Scheme.{u}} {D : Type u} [CommRing D] (φ : D →+* Γ(𝒱, ⊤)) (hφ : Function.Injective φ)
  (cD : Coact D Γ') (cV : Coact Γ(𝒱, ⊤) Γ') (hgr : ∀ d y, cV.comp d (φ y) = φ (cD.comp d y))

include hφ hgr in
/-- `V = 𝒱 ⊂ Spec D` is stable, in the form of `comp_mem_of_stable`. -/
theorem SDR3Asm_stable [hj : IsOpenImmersion (SDR3Asm_j φ)] (hact : SDR3Asm_ActsOnPoints cV)
    (p : PrimeSpectrum D) [IsDomain (AddMonoidAlgebra (D ⧸ p.asIdeal) Γ')] (hp : p ∉ Set.range (SDR3Asm_j φ)) :
    PrimeSpectrum.comap (orbitHom cD p.asIdeal) ⟨⊥, Ideal.isPrime_bot⟩ ∉ Set.range (SDR3Asm_j φ) := by
  classical
  intro hξ
  apply hp
  let A := AddMonoidAlgebra (D ⧸ p.asIdeal) Γ'
  let L := FractionRing A
  let inc : A →+* L := algebraMap A L
  have hinc : Function.Injective inc := IsFractionRing.injective A L
  let Ψ : D →+* L := inc.comp (orbitHom cD p.asIdeal)
  have hr : Set.range (Spec.map (CommRingCat.ofHom Ψ)) ⊆ Set.range (SDR3Asm_j φ) := by
    rintro _ ⟨y, rfl⟩
    have hy : y = ⟨⊥, Ideal.isPrime_bot⟩ := Subsingleton.elim _ _
    have e : Spec.map (CommRingCat.ofHom Ψ) y =
        PrimeSpectrum.comap (orbitHom cD p.asIdeal) ⟨⊥, Ideal.isPrime_bot⟩ := by
      rw [hy]
      apply PrimeSpectrum.ext
      ext z
      change Ψ z ∈ (⊥ : Ideal L) ↔ orbitHom cD p.asIdeal z ∈ (⊥ : Ideal A)
      simp only [Ideal.mem_bot, Ψ, RingHom.comp_apply]
      exact map_eq_zero_iff inc hinc
    rw [e]
    exact hξ
  let v := IsOpenImmersion.lift (SDR3Asm_j φ) _ hr
  have hv : v ≫ SDR3Asm_j φ = Spec.map (CommRingCat.ofHom Ψ) := IsOpenImmersion.lift_fac _ _ _
  have hevΨ : ∀ y, SDR3Asm_ev v (φ y) = Ψ y := by
    intro y
    have h1 := SDR3Asm_comp_j φ v
    rw [hv] at h1
    have h2 := Spec.map_injective h1
    have h3 := congrArg (fun k => k.hom y) h2
    exact h3.symm
  let χ : Multiplicative Γ' →* L :=
    { toFun := fun d => inc (AddMonoidAlgebra.single (-Multiplicative.toAdd d) 1)
      map_one' := by
        simp only [toAdd_one, neg_zero]
        rw [← map_one inc]
        rfl
      map_mul' := fun x y => by
        rw [← map_mul, AddMonoidAlgebra.single_mul_single, one_mul, toAdd_mul, neg_add, add_comm] }
  obtain ⟨v', hv'⟩ := hact L v χ
  let mk := Ideal.Quotient.mk p.asIdeal
  have hterm : ∀ (y : D) (d : Γ'), χ (Multiplicative.ofAdd d) * SDR3Asm_ev v (cV.comp d (φ y)) =
      inc (AddMonoidAlgebra.single 0 (mk (cD.comp d y))) := by
    intro y d
    rw [hgr, hevΨ]
    change inc _ * inc (orbitHom cD p.asIdeal (cD.comp d y)) = _
    rw [← map_mul]
    congr 1
    have h1 : orbitHom cD p.asIdeal (cD.comp d y) = AddMonoidAlgebra.single d (mk (cD.comp d y)) := by
      change AddMonoidAlgebra.mapRingHom Γ' mk (cD.σ (cD.comp d y)) = _
      have := cD.comp_isHom d y
      change cD.σ _ = _ at this
      rw [this, AddMonoidAlgebra.mapRingHom_single]
    rw [h1]
    change (AddMonoidAlgebra.single (-d) (1 : D ⧸ p.asIdeal)) * AddMonoidAlgebra.single d (mk (cD.comp d y)) = _
    rw [AddMonoidAlgebra.single_mul_single, one_mul, neg_add_cancel]
  let G : D →+ L :=
    { toFun := fun y => inc (AddMonoidAlgebra.single 0 (mk y))
      map_zero' := by simp
      map_add' := fun x y => by
        rw [map_add, AddMonoidAlgebra.single_add, map_add] }
  have hkey : ∀ y, SDR3Asm_ev v' (φ y) = inc (AddMonoidAlgebra.single 0 (mk y)) := by
    intro y
    rw [hv', Finsupp.sum]
    have e1 : ∑ d ∈ (cV.σ (φ y)).coeff.support, cD.comp d y = y := by
      apply hφ
      rw [map_sum]
      conv_rhs => rw [← cV.sum_eq (φ y)]
      exact Finset.sum_congr rfl fun d _ => (hgr d y).symm
    calc _ = ∑ d ∈ (cV.σ (φ y)).coeff.support, G (cD.comp d y) := Finset.sum_congr rfl fun d _ => hterm y d
      _ = G (∑ d ∈ (cV.σ (φ y)).coeff.support, cD.comp d y) := (map_sum G _ _).symm
      _ = _ := by rw [e1]; rfl
  refine ⟨v' ⟨⊥, Ideal.isPrime_bot⟩, ?_⟩
  have h1 := SDR3Asm_comp_j φ v'
  have h2 : SDR3Asm_j φ (v' ⟨⊥, Ideal.isPrime_bot⟩) = (v' ≫ SDR3Asm_j φ) ⟨⊥, Ideal.isPrime_bot⟩ := rfl
  rw [h2, h1]
  apply PrimeSpectrum.ext
  ext y
  change SDR3Asm_ev v' (φ y) ∈ (⊥ : Ideal L) ↔ y ∈ p.asIdeal
  rw [hkey, Ideal.mem_bot, map_eq_zero_iff inc hinc, ← Ideal.Quotient.eq_zero_iff_mem]
  constructor
  · intro h
    have := congrArg (fun z => z.coeff 0) h
    simpa [AddMonoidAlgebra.coeff_single] using this
  · intro h
    change AddMonoidAlgebra.single 0 (mk y) = 0
    have : mk y = 0 := h
    rw [this, AddMonoidAlgebra.single_zero]

end AlgMag.SD
