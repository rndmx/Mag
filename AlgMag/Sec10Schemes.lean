/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import AlgMag.GeneralBaseMilnor

/-!
# Lifting along smooth morphisms of schemes: first steps towards Corollary 10.3

Mayeux, *Algebraic Magnetism*, §10, schemes only. Propositions 10.1 and Corollary 10.3 are **not**
proved here. This file proves two ingredients of the non-equivariant part, for `X'` affine:

* `exists_lift_in_chart`, `exists_local_lift`: local existence of lifts along a smooth morphism of
  schemes.
* `has_of_two_cover`: the reduction of a global section on an affine scheme to covers by two basic
  opens, which replaces the vanishing of `H¹` on an affine scheme once the Mayer-Vietoris step is
  known.
-/

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgMag.SmoothSchemes

open AlgMag.GB

/-- Lifting along a smooth morphism of schemes, schemes only, when both maps land in an affine
chart on which the morphism is standard smooth. -/
theorem exists_lift_in_chart {Y Z : Scheme.{u}} (f : Y ⟶ Z) {U : Z.Opens} {V : Y.Opens}
    (hU : IsAffineOpen U) (hV : IsAffineOpen V) (e : V ≤ f ⁻¹ᵁ U)
    (hsm : (f.appLE U V e).hom.IsStandardSmooth)
    {R R₀ : Type u} [CommRing R] [CommRing R₀] (φ : R →+* R₀) (hs : Function.Surjective φ)
    (hq : ∀ x y, φ x = 0 → φ y = 0 → x * y = 0)
    (a : Spec (CommRingCat.of R₀) ⟶ Y) (b : Spec (CommRingCat.of R) ⟶ Z)
    (ha : Set.range a ⊆ V) (hb : Set.range b ⊆ U) (w : a ≫ f = sp φ ≫ b) :
    ∃ l : Spec (CommRingCat.of R) ⟶ Y, sp φ ≫ l = a ∧ l ≫ f = b := by
  obtain ⟨α, rfl⟩ := exists_ring_of_range hV a ha
  obtain ⟨β, rfl⟩ := exists_ring_of_range hU b hb
  let κ : Γ(Z, U) →+* Γ(Y, V) := (f.appLE U V e).hom
  have hfs : hV.fromSpec ≫ f = sp κ ≫ hU.fromSpec := by
    rw [← IsAffineOpen.SpecMap_appLE_fromSpec f hU hV e]
    rfl
  have hc : α.comp κ = φ.comp β := by
    apply sp_injective
    rw [sp_comp, sp_comp, ← cancel_mono hU.fromSpec, Category.assoc, Category.assoc, ← hfs,
      ← Category.assoc, w]
  let _ : Algebra Γ(Z, U) Γ(Y, V) := κ.toAlgebra
  let _ : Algebra Γ(Z, U) R := β.toAlgebra
  let _ : Algebra Γ(Z, U) R₀ := (φ.comp β).toAlgebra
  have : Algebra.IsStandardSmooth Γ(Z, U) Γ(Y, V) := hsm
  have : Algebra.FormallySmooth Γ(Z, U) Γ(Y, V) := inferInstance
  let αₐ : Γ(Y, V) →ₐ[Γ(Z, U)] R₀ := { α with commutes' := fun r => RingHom.congr_fun hc r }
  let φₐ : R →ₐ[Γ(Z, U)] R₀ := { φ with commutes' := fun r => rfl }
  have hnil : IsNilpotent (RingHom.ker φₐ) := by
    refine ⟨2, ?_⟩
    rw [pow_two, Ideal.zero_eq_bot, eq_bot_iff, Ideal.mul_le]
    intro x hx y hy
    exact hq x y hx hy
  let γ := Algebra.FormallySmooth.liftOfSurjective αₐ φₐ hs hnil
  have hγ : φ.comp γ.toRingHom = α := RingHom.ext fun x =>
    Algebra.FormallySmooth.liftOfSurjective_apply αₐ φₐ hs hnil x
  have hγ' : γ.toRingHom.comp κ = β := RingHom.ext fun r => γ.commutes r
  refine ⟨sp γ.toRingHom ≫ hV.fromSpec, ?_, ?_⟩
  · rw [← Category.assoc, ← sp_comp, hγ]
  · rw [Category.assoc, hfs, ← Category.assoc, ← sp_comp, hγ']

/-- Localizing a surjection with square zero kernel at `h` gives one. -/
lemma pL_thickening {R R₀ : Type u} [CommRing R] [CommRing R₀] (φ : R →+* R₀)
    (hs : Function.Surjective φ) (hq : ∀ x y, φ x = 0 → φ y = 0 → x * y = 0) (h : R) :
    Function.Surjective (pL φ h) ∧ ∀ x y, pL φ h x = 0 → pL φ h y = 0 → x * y = 0 := by
  have key : ∀ (r : R) (n : ℕ), pL φ h (IsLocalization.mk' _ r (⟨h ^ n, n, rfl⟩ :
      Submonoid.powers h)) = 0 → ∃ k : ℕ, φ (h ^ k * r) = 0 := by
    intro r n e
    have h₁ : algebraMap R₀ (Localization.Away (φ h)) (φ r) = 0 := by
      have e₂ : pL φ h (algebraMap R _ r) = algebraMap R₀ _ (φ r) := by
        simp [pL]
      rw [← e₂, ← IsLocalization.mk'_spec (Localization.Away h) r
        (⟨h ^ n, n, rfl⟩ : Submonoid.powers h), map_mul, e, zero_mul]
    obtain ⟨⟨_, k, rfl⟩, hk⟩ := (IsLocalization.map_eq_zero_iff (Submonoid.powers (φ h)) _ _).1 h₁
    exact ⟨k, by simpa using hk⟩
  constructor
  · intro y
    obtain ⟨c, ⟨_, n, rfl⟩, rfl⟩ := IsLocalization.exists_mk'_eq (Submonoid.powers (φ h)) y
    obtain ⟨r, rfl⟩ := hs c
    refine ⟨IsLocalization.mk' _ r (⟨h ^ n, n, rfl⟩ : Submonoid.powers h), ?_⟩
    rw [eq_comm, IsLocalization.mk'_eq_iff_eq_mul]
    have e₂ : ∀ z, pL φ h (algebraMap R _ z) = algebraMap R₀ (Localization.Away (φ h)) (φ z) := by
      intro z
      simp [pL]
    have := IsLocalization.mk'_spec (Localization.Away h) r (⟨h ^ n, n, rfl⟩ : Submonoid.powers h)
    have t := congrArg (pL φ h) this
    rw [map_mul, e₂, e₂] at t
    simpa [mul_comm] using t.symm
  · intro x y hx hy
    obtain ⟨r, ⟨_, n, rfl⟩, rfl⟩ := IsLocalization.exists_mk'_eq (Submonoid.powers h) x
    obtain ⟨r', ⟨_, n', rfl⟩, rfl⟩ := IsLocalization.exists_mk'_eq (Submonoid.powers h) y
    obtain ⟨k, hk⟩ := key r n hx
    obtain ⟨k', hk'⟩ := key r' n' hy
    have h0 := hq _ _ hk hk'
    have hu : IsUnit (algebraMap R (Localization.Away h) (h ^ k * h ^ k')) :=
      IsLocalization.map_units _ (⟨_, k + k', by simp [pow_add]⟩ : Submonoid.powers h)
    have e₀ : algebraMap R (Localization.Away h) (h ^ k * h ^ k') *
        (IsLocalization.mk' _ r (⟨h ^ n, n, rfl⟩ : Submonoid.powers h) *
          IsLocalization.mk' _ r' (⟨h ^ n', n', rfl⟩ : Submonoid.powers h)) *
        (algebraMap R _ (h ^ n) * algebraMap R _ (h ^ n')) = 0 := by
      have a₁ := IsLocalization.mk'_spec (Localization.Away h) r (⟨h ^ n, n, rfl⟩ : Submonoid.powers h)
      have a₂ := IsLocalization.mk'_spec (Localization.Away h) r' (⟨h ^ n', n', rfl⟩ : Submonoid.powers h)
      simp only at a₁ a₂
      calc _ = algebraMap R (Localization.Away h) (h ^ k * r * (h ^ k' * r')) := by
            have t : algebraMap R (Localization.Away h) (h ^ k * r * (h ^ k' * r')) =
                algebraMap R _ (h ^ k) * algebraMap R _ r *
                  (algebraMap R _ (h ^ k') * algebraMap R _ r') := by simp only [map_mul]
            rw [t, ← a₁, ← a₂, map_mul]
            ring
        _ = 0 := by rw [h0, map_zero]
    have hv : IsUnit (algebraMap R (Localization.Away h) (h ^ n) * algebraMap R _ (h ^ n')) :=
      (IsLocalization.map_units _ (⟨_, n, rfl⟩ : Submonoid.powers h)).mul
        (IsLocalization.map_units _ (⟨_, n', rfl⟩ : Submonoid.powers h))
    exact (hu.mul_right_eq_zero).1 ((hv.mul_left_eq_zero).1 e₀)

/-- **Local existence of lifts along a smooth morphism of schemes**, schemes only: for a first order
thickening `Spec R₀ → Spec R` and a smooth `f`, every point of `Spec R₀` lies in a basic open
`D(φ h)` over which a lift exists. -/
theorem exists_local_lift {Y Z : Scheme.{u}} (f : Y ⟶ Z) [Smooth f]
    {R R₀ : Type u} [CommRing R] [CommRing R₀] (φ : R →+* R₀) (hs : Function.Surjective φ)
    (hq : ∀ x y, φ x = 0 → φ y = 0 → x * y = 0)
    (a : Spec (CommRingCat.of R₀) ⟶ Y) (b : Spec (CommRingCat.of R) ⟶ Z)
    (w : a ≫ f = sp φ ≫ b) (x : Spec (CommRingCat.of R₀)) :
    ∃ h : R, x ∈ Set.range (spAway (φ h)) ∧ ∃ l : Spec (CommRingCat.of (Localization.Away h)) ⟶ Y,
      sp (pL φ h) ≫ l = spAway (φ h) ≫ a ∧ l ≫ f = spAway h ≫ b := by
  obtain ⟨U, hU, V, hV, hxV, e, hsm⟩ := Smooth.exists_isStandardSmooth f (a x)
  obtain ⟨L, hL⟩ := (PrimeSpectrum.isClosed_iff_zeroLocus_ideal _).1 (a ⁻¹ᵁ V).isOpen.isClosed_compl
  have hxL : ¬ (L : Set R₀) ⊆ (x : PrimeSpectrum R₀).asIdeal := by
    intro hc
    have : (x : PrimeSpectrum R₀) ∈ PrimeSpectrum.zeroLocus (L : Set R₀) := hc
    rw [← hL] at this
    exact this hxV
  obtain ⟨y, hyL, hyx⟩ := Set.not_subset.1 hxL
  obtain ⟨y₀, rfl⟩ := hs y
  let p : Spec (CommRingCat.of R) := sp φ x
  have hbp : p ∈ b ⁻¹ᵁ U := by
    change b (sp φ x) ∈ U
    have : b (sp φ x) = f (a x) := by
      rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, w]
    rw [this]
    exact e hxV
  obtain ⟨_, ⟨h₀, rfl⟩, hph₀, hh₀⟩ := PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open
    hbp (b ⁻¹ᵁ U).isOpen
  have hy₀ : y₀ ∉ (p : PrimeSpectrum R).asIdeal := hyx
  let h := h₀ * y₀
  have hhp : h ∉ (p : PrimeSpectrum R).asIdeal := fun hc =>
    ((p : PrimeSpectrum R).isPrime.mem_or_mem hc).elim hph₀ hy₀
  refine ⟨h, ?_, ?_⟩
  · rw [range_spAway]
    exact hhp
  have hb' : Set.range (spAway h ≫ b) ⊆ U := by
    rintro _ ⟨z, rfl⟩
    have hz : spAway h z ∈ Set.range (spAway h) := ⟨z, rfl⟩
    rw [range_spAway] at hz
    exact hh₀ (fun hc => hz (Ideal.mul_mem_right _ _ hc))
  have ha' : Set.range (spAway (φ h) ≫ a) ⊆ V := by
    rintro _ ⟨z, rfl⟩
    have hz : spAway (φ h) z ∈ Set.range (spAway (φ h)) := ⟨z, rfl⟩
    rw [range_spAway] at hz
    by_contra hc
    have : spAway (φ h) z ∈ ((a ⁻¹ᵁ V : Scheme.Opens _) : Set _)ᶜ := hc
    rw [hL] at this
    have k := Ideal.mul_mem_left _ (φ h₀) (this hyL)
    rw [← map_mul] at k
    exact hz k
  obtain ⟨hs', hq'⟩ := pL_thickening φ hs hq h
  refine exists_lift_in_chart f hU hV e hsm (pL φ h) hs' hq' _ _ ha' hb' ?_
  rw [Category.assoc, w, ← Category.assoc, ← Category.assoc, sp_pL_spAway]

/-- Reduction of a global section on an affine scheme to two-element covers. `Has h` means that
something exists on the basic open `D(h)`. If it exists on the empty open, restricts to smaller
basic opens, and glues over two basic opens (`D(f + g) ⊆ D(f) ∪ D(g)`), then it exists on every
basic open contained in a finite union of basic opens where it exists. -/
theorem has_of_two_cover {R : Type*} [CommRing R] (Has : R → Prop) (empty : Has 0)
    (mono : ∀ h k, h ∈ (Ideal.span {k}).radical → Has k → Has h)
    (two : ∀ f g, Has f → Has g → Has (f + g))
    (s : Finset R) (hs : ∀ k ∈ s, Has k) :
    ∀ h ∈ (Ideal.span (s : Set R)).radical, Has h := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rintro h ⟨n, hn⟩
    refine mono h 0 ⟨n, ?_⟩ empty
    simpa using hn
  | insert k s _ ih =>
    rintro h ⟨n, hn⟩
    rw [Finset.coe_insert, Ideal.mem_span_insert] at hn
    obtain ⟨r, g, hg, e⟩ := hn
    have h₁ : Has g := ih (fun x hx => hs x (Finset.mem_insert_of_mem hx)) g
      (Ideal.le_radical hg)
    have h₂ : Has (r * k) := mono _ k
      (Ideal.le_radical (Ideal.mem_span_singleton'.2 ⟨r, rfl⟩)) (hs k (Finset.mem_insert_self _ _))
    refine mono h (r * k + g) ⟨n, ?_⟩ (two _ _ h₂ h₁)
    rw [e]
    exact Ideal.mem_span_singleton_self _

end AlgMag.SmoothSchemes
