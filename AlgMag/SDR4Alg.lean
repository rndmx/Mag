/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.SDR4Action
import AlgMag.SDR4Step2

/-!
# Lemma D, final bridge: the algebra of the localized closed orbit

For Props. 3.31 (ii), 3.32 (ii) of `Algebraic Magnetism`, Steps 1-2:
`(B / I')_{P'} ≅ κ'[L]`, as a statement on a ring `G` with an injective `ω : G → κ'[Γ]`, and the degrees of `L` are realized
by homogeneous elements outside the closed orbit.
-/

open TensorProduct

universe u

namespace AlgMag.SD

open AlgMag AlgMag.SQ

/-- `(B / I)_{R ∖ P} ≅ G`, when `B → G` has kernel `I`, inverts `R ∖ P`, and every element of `G` has a denominator in
`R ∖ P`. -/
theorem SDR4_loc {R₀ B₀ G : Type u} [CommRing R₀] [CommRing B₀] [CommRing G] (ι : R₀ →+* B₀) (P : Ideal R₀) [P.IsPrime]
    (I : Ideal B₀)
    (Θ : B₀ →+* G) (hker : ∀ y, y ∈ I ↔ Θ y = 0) (hu : ∀ s, s ∉ P → IsUnit (Θ (ι s)))
    (hs : ∀ g, ∃ b s, s ∉ P ∧ g * Θ (ι s) = Θ b)
    (T : Submonoid (B₀ ⧸ I)) (hT : T = P.primeCompl.map ((Ideal.Quotient.mk I).comp ι)) :
    ∃ e : Localization T ≃+* G, ∀ b, e (algebraMap (B₀ ⧸ I) (Localization T) (Ideal.Quotient.mk I b)) = Θ b := by
  let Θb : B₀ ⧸ I →+* G := Ideal.Quotient.lift I Θ fun a ha => (hker a).1 ha
  have hΘb : ∀ b, Θb (Ideal.Quotient.mk I b) = Θ b := fun b => Ideal.Quotient.lift_mk _ _ _
  have hinj : Function.Injective Θb := by
    rw [injective_iff_map_eq_zero]
    intro a ha
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective a
    rw [hΘb] at ha
    exact Ideal.Quotient.eq_zero_iff_mem.2 ((hker b).2 ha)
  let _ : Algebra (B₀ ⧸ I) G := Θb.toAlgebra
  have hmemT : ∀ s, s ∉ P → Ideal.Quotient.mk I (ι s) ∈ T := fun s hs => by
    rw [hT]
    exact ⟨s, hs, rfl⟩
  have hloc : IsLocalization T G :=
    { map_units := by
        rintro ⟨t, ht⟩
        rw [hT] at ht
        obtain ⟨s, hs', rfl⟩ := ht
        exact hu s hs'
      surj := fun g => by
        obtain ⟨b, s, hs', he⟩ := hs g
        exact ⟨⟨Ideal.Quotient.mk I b, ⟨_, hmemT s hs'⟩⟩, he.trans (hΘb b).symm⟩
      exists_of_eq := fun {x y} h => ⟨1, by rw [hinj h]⟩ }
  let e := IsLocalization.algEquiv T (Localization T) G
  exact ⟨e.toRingEquiv, fun b => (e.commutes _).trans (hΘb b)⟩

section Degrees

variable {R₀ A₀ F Γ : Type u} [CommRing R₀] [CommRing A₀] [Field F] [AddCommGroup Γ] [UniqueSums Γ] {c : Coact A₀ Γ}
  {ι : R₀ →+* A₀}

/-- The degrees of a closed orbit form a group: `L` is realized by homogeneous elements on which `φ` does not vanish. -/
theorem SDR4_deg (hι : c.IsInv ι) {q₀ : Ideal R₀} [q₀.IsPrime] {I : Ideal A₀} (hI : c.IsHomIdeal I)
    (hIq : ∀ a, ι a ∈ I → a ∈ q₀) (hmax : ∀ J, c.IsHomIdeal J → I < J → ∃ a, ι a ∈ J ∧ a ∉ q₀) (φ : A₀ →+* F)
    (hφ : ∀ d a, c.IsHom d a → (φ a = 0 ↔ a ∈ I)) (X₀ : Set Γ) (hX₀ : ∀ d ∈ X₀, ∃ a, c.IsHom d a ∧ φ a ≠ 0) {d : Γ}
    (hd : d ∈ AddSubgroup.closure X₀) : ∃ a, c.IsHom d a ∧ φ a ≠ 0 := by
  induction hd using AddSubgroup.closure_induction with
  | mem x hx => exact hX₀ x hx
  | zero => exact ⟨1, SDR3Orbit_isHom_one c, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha, ha0⟩ := hx
    obtain ⟨b, hb, hb0⟩ := hy
    exact ⟨a * b, ha.mul hb, by simpa using ⟨ha0, hb0⟩⟩
  | neg x _ hx =>
    obtain ⟨a, ha, ha0⟩ := hx
    have haI : a ∉ I := fun h => ha0 ((hφ x a ha).2 h)
    obtain ⟨h, hh, b', hb'⟩ := exists_inv_of_homog hι hI hIq hmax ha haI
    let b := c.comp (0 - x) b'
    have hab : a * b = ι h := by
      have e0 : c.comp 0 (ι h) = ι h := c.comp_self_of_isHom ((hι.range _).2 ⟨h, rfl⟩)
      rw [← e0, hb', c.comp_mul_of_isHom ha]
    have hφh : φ (ι h) ≠ 0 := fun h0 => hh (hIq h ((hφ 0 _ ((hι.range _).2 ⟨h, rfl⟩)).1 h0))
    have hb : c.IsHom (0 - x) b := c.comp_isHom (0 - x) b'
    rw [zero_sub] at hb
    refine ⟨b, hb, fun h0 => hφh (by rw [← hab, map_mul, h0, mul_zero])⟩

end Degrees

end AlgMag.SD

#print axioms AlgMag.SD.SDR4_loc
#print axioms AlgMag.SD.SDR4_deg
