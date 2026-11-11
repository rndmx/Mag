/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib.RingTheory.Etale.Kaehler
import Mathlib.RingTheory.Localization.Away.Basic
import AlgMag.Reductive.OpenCell.EtaleCriterion

/-!
# `mapBaseChange` and localization (C2(d))

For `k → A → B` and `s : B`, write `Bₛ = B[1/s]`. If `B ⊗_A Ω_A → Ω_B` becomes bijective after
base change to `Bₛ` (the output of `exists_away_baseChange_bijective`), then
`Bₛ ⊗_A Ω_A → Ω_{Bₛ}` is bijective, since `Ω_{Bₛ} = Bₛ ⊗_B Ω_B`. Corollary: `Bₛ` is flat and
of finite presentation over `A` (via `flat_of_mapBaseChange_bijective`).
-/

namespace AlgMag.Reductive

open TensorProduct KaehlerDifferential

universe u

variable {k A B : Type u} [CommRing k] [CommRing A] [CommRing B] [Algebra k A] [Algebra k B]
  [Algebra A B] [IsScalarTower k A B]

/-- `Bₛ ⊗_A Ω_A → Ω_{Bₛ}` factors as `Bₛ ⊗_B (B ⊗_A Ω_A) → Bₛ ⊗_B Ω_B ≅ Ω_{Bₛ}`. -/
theorem mapBaseChange_away_bijective (s : B)
    (h : Function.Bijective
      ((KaehlerDifferential.mapBaseChange k A B).baseChange (Localization.Away s))) :
    Function.Bijective (KaehlerDifferential.mapBaseChange k A (Localization.Away s)) := by
  set L := Localization.Away s
  have hbc : IsBaseChange L (map k k B L) := isBaseChange_of_formallyEtale k B L
  let e1 : L ⊗[B] Ω[B⁄k] ≃ₗ[L] Ω[L⁄k] := hbc.equiv
  let e2 : L ⊗[B] (B ⊗[A] Ω[A⁄k]) ≃ₗ[L] L ⊗[A] Ω[A⁄k] :=
    AlgebraTensorModule.cancelBaseChange A B L L Ω[A⁄k]
  have hm : ∀ ω : Ω[A⁄k], map k k B L (map k k A B ω) = map k k A L ω := by
    have := Derivation.liftKaehlerDifferential_unique
      ((map k k B L).restrictScalars A ∘ₗ map k k A B) (map k k A L) (by
        ext a
        simp [IsScalarTower.algebraMap_apply A B L])
    exact fun ω => congrArg (fun f => f ω) this
  have key : (KaehlerDifferential.mapBaseChange k A L).restrictScalars B ∘ₗ
      e2.toLinearMap.restrictScalars B =
      (e1.toLinearMap.restrictScalars B) ∘ₗ
        ((KaehlerDifferential.mapBaseChange k A B).baseChange L).restrictScalars B := by
    refine TensorProduct.AlgebraTensorModule.curry_injective ?_
    refine LinearMap.ext fun x => ?_
    refine TensorProduct.AlgebraTensorModule.curry_injective ?_
    refine LinearMap.ext fun b => LinearMap.ext fun ω => ?_
    simp only [AlgebraTensorModule.curry_apply, LinearMap.coe_restrictScalars, curry_apply,
      LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe, e2, e1,
      AlgebraTensorModule.cancelBaseChange_tmul, LinearMap.baseChange_tmul,
      mapBaseChange_tmul, IsBaseChange.equiv_tmul, map_smul]
    rw [hm, smul_assoc, smul_comm]
  have hcomp : Function.Bijective (e1 ∘ ((KaehlerDifferential.mapBaseChange k A B).baseChange L)) :=
    e1.bijective.comp h
  have : ⇑(KaehlerDifferential.mapBaseChange k A L) =
      e1 ∘ ((KaehlerDifferential.mapBaseChange k A B).baseChange L) ∘ e2.symm := by
    funext y
    obtain ⟨z, rfl⟩ := e2.surjective y
    simpa using congrArg (fun f => f z) key
  rw [this]
  exact hcomp.comp e2.symm.bijective

/-- `Bₛ` is of finite presentation over `A` when `B` is. -/
theorem finitePresentation_away [Algebra.FinitePresentation A B] (s : B) :
    Algebra.FinitePresentation A (Localization.Away s) := by
  have : Algebra.FinitePresentation B (Localization.Away s) :=
    IsLocalization.Away.finitePresentation s
  exact Algebra.FinitePresentation.trans A B (Localization.Away s)

/-- **Corollary.** `B` smooth over `k` and of finite presentation over `A`: if
`B ⊗_A Ω_A → Ω_B` is bijective over `Bₛ`, then `Bₛ` is flat over `A`. -/
theorem flat_away_of_baseChange_bijective [Algebra.FormallySmooth k B]
    [Algebra.FinitePresentation A B] (s : B)
    (h : Function.Bijective
      ((KaehlerDifferential.mapBaseChange k A B).baseChange (Localization.Away s))) :
    Module.Flat A (Localization.Away s) := by
  have : Algebra.FormallySmooth B (Localization.Away s) :=
    Algebra.FormallySmooth.of_isLocalization (Submonoid.powers s)
  have : Algebra.FormallySmooth k (Localization.Away s) :=
    Algebra.FormallySmooth.comp k B (Localization.Away s)
  have := finitePresentation_away (A := A) s
  exact AlgMag.OpenCellNotes.flat_of_mapBaseChange_bijective (R := k)
    (mapBaseChange_away_bijective s h)

end AlgMag.Reductive
