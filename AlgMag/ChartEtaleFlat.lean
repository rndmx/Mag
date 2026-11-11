/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import StacksFrontier.RingTheory.Etale.Basic.FirstProperties
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.FlatMono
import Mathlib.AlgebraicGeometry.PullbackCarrier

/-!
# Étaleness at a point descends along a flat base change

Input of the proof that the étale locus is stable (`AlgMag/ChartEtaleLocus.lean`): the scheme form
over affine targets of `Algebra.etaleLocus_eq_of_isPushout` (Stacks tag recorded there).
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct

universe u

namespace AlgMag.ChartEtale

/-- A point of `X` and a point of `Y` with the same image lift to any pullback. -/
lemma exists_pt_of_isPullback {P X Y Z : Scheme.{u}} {a : P ⟶ X} {b : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z}
    (sq : IsPullback a b f g) (x : X) (y : Y) (h : f x = g y) : ∃ z : P, a z = x ∧ b z = y := by
  obtain ⟨z, hx, hy⟩ := Scheme.Pullback.exists_preimage_pullback x y h
  refine ⟨sq.isoPullback.inv z, ?_, ?_⟩
  · rw [← hx, ← Scheme.Hom.comp_apply, IsPullback.isoPullback_inv_fst]
  · rw [← hy, ← Scheme.Hom.comp_apply, IsPullback.isoPullback_inv_snd]

/-- Ring form: the étale locus of a flat base change is the inverse image of the étale locus. -/
lemma exists_etale_away {R S R' : Type u} [CommRing R] [CommRing S] [CommRing R'] [Algebra R S]
    [Algebra R R'] [Module.Flat R R'] [Algebra.FinitePresentation R S]
    {C : Type u} [CommRing C] [Algebra S C] [Algebra R' C] [Algebra R C] [IsScalarTower R R' C]
    [IsScalarTower R S C] [Algebra.IsPushout R S R' C]
    (c : PrimeSpectrum C) (r : C) (hr : r ∉ c.asIdeal)
    (het : Algebra.FormallyEtale R' (Localization.Away r)) :
    ∃ s : S, s ∉ c.asIdeal.comap (algebraMap S C) ∧ Algebra.Etale R (Localization.Away s) := by
  have h1 : c ∈ Algebra.etaleLocus R' C :=
    (Algebra.basicOpen_subset_etaleLocus_iff (R := R') (A := C) (f := r)).2 het hr
  rw [Algebra.etaleLocus_eq_of_isPushout R S R' C] at h1
  have : (c.asIdeal.comap (algebraMap S C)).IsPrime := inferInstance
  have h2 : Algebra.IsEtaleAt R (c.asIdeal.comap (algebraMap S C)) := h1
  exact Algebra.exists_etale_of_isEtaleAt (R := R) (A := S) _

/-- **Flat descent of étaleness at a point**, over an affine target. -/
theorem exists_open_etale_of_isPullback_Spec {R R' : CommRingCat.{u}} (σ : R ⟶ R')
    [Flat (Spec.map σ)] {P Y : Scheme.{u}} {a : P ⟶ Y} {b : P ⟶ Spec R'} {f : Y ⟶ Spec R}
    [LocallyOfFinitePresentation f] (sq : IsPullback a b f (Spec.map σ)) (z : P) (O : P.Opens)
    (hz : z ∈ O) (hO : Etale (O.ι ≫ b)) : ∃ U : Y.Opens, a z ∈ U ∧ Etale (U.ι ≫ f) := by
  classical
  obtain ⟨U, hU, hzU, -⟩ := exists_isAffineOpen_mem_and_subset (TopologicalSpace.Opens.mem_top (a z))
  let S : CommRingCat.{u} := Γ(Y, U)
  let ρ : R ⟶ S := Spec.preimage (hU.fromSpec ≫ f)
  have hρ : Spec.map ρ = hU.fromSpec ≫ f := Spec.map_preimage _
  have hlρ : LocallyOfFinitePresentation (Spec.map ρ) := by rw [hρ]; infer_instance
  have hfpρ : ρ.hom.FinitePresentation :=
    (HasRingHomProperty.Spec_iff (P := @LocallyOfFinitePresentation)).1 hlρ
  have hflσ : σ.hom.Flat := (HasRingHomProperty.Spec_iff (P := @Flat)).1 ‹_›
  letI : Algebra R S := ρ.hom.toAlgebra
  letI : Algebra R R' := σ.hom.toAlgebra
  have hfp : Algebra.FinitePresentation R S := hfpρ
  have hfl : Module.Flat R R' := hflσ
  let C : CommRingCat.{u} := .of (S ⊗[R] R')
  letI : Algebra R' C := Algebra.TensorProduct.rightAlgebra
  have hpo := CommRingCat.isPushout_tensorProduct R S R'
  have hsqC := isPullback_SpecMap_of_isPushout _ _ _ _ hpo
  let il : S ⟶ C := CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom
  let ir : R' ⟶ C := CommRingCat.ofHom Algebra.TensorProduct.includeRight.toRingHom
  have hsq' : IsPullback (Spec.map il) (Spec.map ir) (Spec.map ρ) (Spec.map σ) := hsqC
  let k : Spec C ⟶ P := sq.lift (Spec.map il ≫ hU.fromSpec) (Spec.map ir)
    (by rw [Category.assoc, ← hρ, hsq'.w])
  have hka : k ≫ a = Spec.map il ≫ hU.fromSpec := sq.lift_fst _ _ _
  have hkb : k ≫ b = Spec.map ir := sq.lift_snd _ _ _
  have outer : IsPullback (k ≫ b) (Spec.map il) (Spec.map σ) (hU.fromSpec ≫ f) := by
    rw [hkb, ← hρ]; exact hsq'.flip
  have left : IsPullback k (Spec.map il) a hU.fromSpec :=
    IsPullback.of_right outer hka sq.flip
  have hkopen : IsOpenImmersion k :=
    MorphismProperty.of_isPullback (P := @IsOpenImmersion) left.flip inferInstance
  obtain ⟨s₀, hs₀⟩ : ∃ s₀, hU.fromSpec s₀ = a z := by
    have : a z ∈ Set.range hU.fromSpec := by rw [hU.range_fromSpec]; exact hzU
    exact this
  obtain ⟨c, hcz, hcs⟩ := exists_pt_of_isPullback left z s₀ hs₀.symm
  let c' : PrimeSpectrum C := c
  have hcO : c' ∈ (show Set (PrimeSpectrum C) from (k ⁻¹ᵁ O).1) := by
    change k c ∈ O; rw [hcz]; exact hz
  obtain ⟨_, ⟨r, rfl⟩, hcr, hrO⟩ := PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open
    hcO (k ⁻¹ᵁ O).2
  let L := Localization.Away r
  let toL : C ⟶ CommRingCat.of L := CommRingCat.ofHom (algebraMap C L)
  have hrange : Set.range (Spec.map toL) = (PrimeSpectrum.basicOpen r : Set (PrimeSpectrum C)) :=
    PrimeSpectrum.localization_away_comap_range L r
  have hlopen : IsOpenImmersion (Spec.map toL) := inferInstance
  have hjr : Set.range (Spec.map toL ≫ k) ⊆ Set.range O.ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨x, rfl⟩
    have : Spec.map toL x ∈ Set.range (Spec.map toL) := ⟨x, rfl⟩
    rw [hrange] at this
    exact hrO this
  let t : Spec (CommRingCat.of L) ⟶ O.toScheme := IsOpenImmersion.lift O.ι (Spec.map toL ≫ k) hjr
  have ht : t ≫ O.ι = Spec.map toL ≫ k := IsOpenImmersion.lift_fac _ _ _
  have htet : Etale t := by
    have : Etale (t ≫ O.ι) := by rw [ht]; infer_instance
    exact Etale.of_comp t O.ι
  have hE : Etale (Spec.map (ir ≫ toL)) := by
    have e : Spec.map (ir ≫ toL) = t ≫ O.ι ≫ b := by
      rw [← Category.assoc, ht, Category.assoc, hkb, Spec.map_comp]
    rw [e]; infer_instance
  have hEr : (ir ≫ toL).hom.Etale := (HasRingHomProperty.Spec_iff (P := @Etale)).1 hE
  have hFE : Algebra.FormallyEtale R' L := by
    have : Algebra.Etale R' L := (RingHom.etale_algebraMap (R := R') (S := L)).1 hEr
    exact inferInstance
  obtain ⟨s, hs, hEs⟩ := exists_etale_away (R := R) (S := S) (R' := R') (C := C) c' r hcr hFE
  let T := Localization.Away s
  let toT : S ⟶ CommRingCat.of T := CommRingCat.ofHom (algebraMap S T)
  have hrangeT : Set.range (Spec.map toT) = (PrimeSpectrum.basicOpen s : Set (PrimeSpectrum S)) :=
    PrimeSpectrum.localization_away_comap_range T s
  have : IsOpenImmersion (Spec.map toT) := inferInstance
  let j₀ : Spec (CommRingCat.of T) ⟶ Y := Spec.map toT ≫ hU.fromSpec
  have hE₀ : Etale (j₀ ≫ f) := by
    have e : j₀ ≫ f = Spec.map (ρ ≫ toT) := by
      rw [Spec.map_comp, hρ, Category.assoc]
    rw [e]
    refine (HasRingHomProperty.Spec_iff (P := @Etale)).2 ?_
    exact (RingHom.etale_algebraMap (R := R) (S := T)).2 hEs
  refine ⟨j₀.opensRange, ?_, ?_⟩
  · have hs₁ : s₀ ∈ Set.range (Spec.map toT) := by
      rw [hrangeT]
      have : s₀ = PrimeSpectrum.comap il.hom c' := hcs.symm
      rw [this]
      exact hs
    obtain ⟨x, hx⟩ := hs₁
    refine ⟨x, ?_⟩
    change hU.fromSpec (Spec.map toT x) = _
    rw [hx, hs₀]
  · have e : j₀.opensRange.ι ≫ f = j₀.isoOpensRange.inv ≫ j₀ ≫ f := by
      rw [← Category.assoc]
      congr 1
      rw [Iso.eq_inv_comp, Scheme.Hom.isoOpensRange_hom_ι]
    rw [e]; infer_instance

end AlgMag.ChartEtale
