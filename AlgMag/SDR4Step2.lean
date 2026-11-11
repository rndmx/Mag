/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.SDR3OrbitStep
import StacksFrontier.RingTheory.Etale.ResidueFieldExtension

/-!
# Lemma D, Step 2, with Stacks 00UD discharged

For Props. 3.31 (ii), 3.32 (ii) of `Algebraic Magnetism`, Step 2. `SDR3Orbit_Stacks00UD` is
`Algebra.exists_etale_liesOver_residueFieldRingEquiv` (Stacks 00UD). `SDR4_step2` is `SDR3Orbit_step2` without that
hypothesis, recording in addition that `κ'` is the fraction field of `R' / P'`.
-/

universe u

namespace AlgMag.SD

/-- **Stacks 00UD**, the real theorem of the Stacks library. -/
theorem SDR4_00UD : SDR3Orbit_Stacks00UD.{u} := by
  intro R _ p _ L _ _ _ _
  exact Algebra.exists_etale_liesOver_residueFieldRingEquiv p L

/-- **Step 2.** The étale `R'` with a prime `P'` over `q` whose residue field is `κ'`, for `K` a residue field of `q`. -/
theorem SDR4_step2 {A₀ K κ' : Type u} [CommRing A₀] [Field K] [Field κ']
    [Algebra K κ'] [Module.Finite K κ'] [Algebra.IsSeparable K κ'] {q : Ideal A₀} [q.IsPrime] (ρ : A₀ →+* K)
    (hρ : ∀ a, ρ a = 0 ↔ a ∈ q) (hsurj : ∀ k, ∃ r s, s ∉ q ∧ k * ρ s = ρ r) :
    ∃ (R' : Type u) (_ : CommRing R') (_ : Algebra A₀ R') (_ : Algebra.Etale A₀ R') (P' : Ideal R') (_ : P'.IsPrime)
      (_ : P'.LiesOver q) (τ : R' →+* κ'), (∀ a, τ a = 0 ↔ a ∈ P') ∧
        (∀ a, τ (algebraMap A₀ R' a) = algebraMap K κ' (ρ a)) ∧ ∀ k, ∃ r s, s ∉ P' ∧ k * τ s = τ r := by
  let τ₀ : q.ResidueField →+* K := Ideal.ResidueField.lift q ρ (fun a ha => (hρ a).2 ha)
    (fun a ha => isUnit_iff_ne_zero.2 fun h0 => ha ((hρ a).1 h0))
  have hτ₀ : ∀ a, τ₀ (algebraMap A₀ _ a) = ρ a := fun a => Ideal.ResidueField.lift_algebraMap ..
  have hbij : Function.Bijective τ₀ := by
    refine ⟨τ₀.injective, fun k => ?_⟩
    obtain ⟨r, s, hs, he⟩ := hsurj k
    have hs0 : ρ s ≠ 0 := fun h => hs ((hρ s).1 h)
    refine ⟨algebraMap A₀ _ r * (algebraMap A₀ _ s)⁻¹, ?_⟩
    rw [map_mul, map_inv₀, hτ₀, hτ₀, ← he]
    field_simp
  let e₀ : q.ResidueField ≃+* K := RingEquiv.ofBijective τ₀ hbij
  let _ : Algebra q.ResidueField κ' := ((algebraMap K κ').comp τ₀).toAlgebra
  have hcomm : ((RingEquiv.refl κ' : κ' ≃+* κ') : κ' →+* κ').comp (algebraMap K κ') =
      (algebraMap q.ResidueField κ').comp (e₀.symm : K →+* q.ResidueField) := by
    ext k
    change algebraMap K κ' k = algebraMap K κ' (τ₀ (e₀.symm k))
    congr 1
    exact (e₀.apply_symm_apply k).symm
  have hfin : Module.Finite q.ResidueField κ' :=
    Module.Finite.of_equiv_equiv e₀.symm (RingEquiv.refl κ') hcomm.symm
  have hsep : Algebra.IsSeparable q.ResidueField κ' :=
    Algebra.IsSeparable.of_equiv_equiv e₀.symm (RingEquiv.refl κ') hcomm.symm
  obtain ⟨R', _, _, hE, P', hP', hL, e, he⟩ := SDR4_00UD q κ'
  refine ⟨R', inferInstance, inferInstance, hE, P', hP', hL,
    (e : P'.ResidueField →+* κ').comp (algebraMap R' P'.ResidueField), fun a => ?_, fun a => ?_, fun k => ?_⟩
  · change e _ = 0 ↔ _
    rw [map_eq_zero_iff _ e.injective, Ideal.algebraMap_residueField_eq_zero]
  · have h1 := congrArg (fun k => k (algebraMap A₀ q.ResidueField a)) he
    simp only [RingHom.comp_apply] at h1
    rw [Ideal.ResidueField.map_algebraMap] at h1
    change e _ = _
    refine h1.trans ?_
    change algebraMap K κ' (τ₀ _) = _
    rw [hτ₀]
  · obtain ⟨x, y, hy, hxy⟩ := IsFractionRing.div_surjective (A := R' ⧸ P') (e.symm k)
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective y
    have hs : s ∉ P' := fun h => (mem_nonZeroDivisors_iff_ne_zero.1 hy) (Ideal.Quotient.eq_zero_iff_mem.2 h)
    refine ⟨r, s, hs, ?_⟩
    have hs0 : algebraMap (R' ⧸ P') P'.ResidueField (Ideal.Quotient.mk P' s) ≠ 0 := by
      rw [Ne, map_eq_zero_iff _ (IsFractionRing.injective _ _)]
      exact mem_nonZeroDivisors_iff_ne_zero.1 hy
    have h1 : e.symm k * algebraMap (R' ⧸ P') P'.ResidueField (Ideal.Quotient.mk P' s) =
        algebraMap (R' ⧸ P') P'.ResidueField (Ideal.Quotient.mk P' r) := by
      rw [← hxy]
      field_simp
    have h2 := congrArg e h1
    rw [map_mul, e.apply_symm_apply] at h2
    exact h2

end AlgMag.SD

#print axioms AlgMag.SD.SDR4_00UD
#print axioms AlgMag.SD.SDR4_step2
