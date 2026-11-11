/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Reductive.ParabolicAttractor
import AlgMag.Reductive.ParabolicConnected
import AlgMag.Reductive.OpenCellGen
import AlgMag.Reductive.WeylInNormal
import AlgMag.Reductive.RootSpaceDim
import AlgMag.Sec3Affine

/-!
# Levi version of Proposition 16.10: `G^{ℤα} = Z_G(μ)`, hence `Z = G^{ℤα}` is connected

Let `G` be smooth and irreducible over `k = k̄`, `α ≠ 0`, and suppose the roots proportional to
`α` lie in `ℤα` (`hRay`). For `μ ⊥ α` nonzero on the other roots (`exists_perp_cocharacter`),
* `N₊ = {χ : ⟨χ,μ⟩ > 0} ∪ ℤα` and `N₋ = {χ : ⟨χ,μ⟩ < 0} ∪ ℤα` are magnets with the tangent
  weights of `P(±μ)`, so `G^{N±} = P(±μ)` (`magnetIdeal_eq_parabolic_of_isAlgClosed`);
* `ℤα = N₊ ∩ N₋`, so `G^{ℤα} = P(μ) ∩ P(-μ) = Z_G(μ)` (`magnetIdeal_inf`,
  `leviDefiningHopfIdeal_def`, `cocharacter_inv`), a connected Levi
  (`connectedSpace_levi_of_openCell`).
-/

suppress_compilation

open Magnetism TauCeti TauCeti.Cocharacter WithConv

namespace AlgMag.Reductive

universe u

variable {k : Type u} {H : Type u} {X : Type u}
variable [Field k] [CommRing H] [HopfAlgebra k H] [CommGroup X] [DecidableEq X]
variable (π : H →ₐc[k] MonoidAlgebra k X)

/-- `{χ : ⟨χ,ν⟩ > 0} ∪ ℤα`, a magnet when `⟨α,ν⟩ = 0`. -/
def halfLineMagnet (α : Additive X) (ν : X →* Multiplicative ℤ) (hν : pairingHom ν α = 0) :
    Magnet (Additive X) where
  carrier := {χ | 0 < pairingHom ν χ ∨ χ ∈ lineMagnet α}
  zero_mem' := Or.inr (lineMagnet α).zero_mem
  add_mem' := by
    have hl : ∀ χ ∈ lineMagnet α, pairingHom ν χ = 0 := by
      rintro _ ⟨n, rfl⟩
      simp [map_zsmul, hν]
    rintro a b (ha | ha) (hb | hb)
    · left; rw [map_add]; omega
    · left; rw [map_add, hl b hb]; omega
    · left; rw [map_add, hl a ha]; omega
    · right; exact (lineMagnet α).add_mem ha hb

omit [DecidableEq X] in
lemma pairing_lineMagnet {α : Additive X} {ν : X →* Multiplicative ℤ} (hν : pairingHom ν α = 0)
    {χ : Additive X} (hχ : χ ∈ lineMagnet α) : pairingHom ν χ = 0 := by
  obtain ⟨n, rfl⟩ := hχ
  simp [map_zsmul, hν]

variable [IsAlgClosed k] [Algebra.FiniteType k H] [Algebra.Smooth k H]
variable [Module.Finite k (Bialgebra.CotangentSpace k H)]

/-- `G^{N_ν} = P(ν)`. -/
lemma magnetIdeal_halfLine_eq [IrreducibleSpace (PrimeSpectrum H)] {α : Additive X}
    {ν : X →* Multiplicative ℤ} (hν : pairingHom ν α = 0)
    (hgen : ∀ β ∈ roots π, pairingHom ν β = 0 → β ∈ lineMagnet α) :
    magnetIdeal (torusGrading π) (halfLineMagnet α ν hν) =
      (parabolicDefiningHopfIdeal (π.cocharacter ν)).toIdeal := by
  apply magnetIdeal_eq_parabolic_of_isAlgClosed π ν
  · rintro χ (h | h)
    · exact mem_natMagnet.2 h.le
    · exact mem_natMagnet.2 (pairing_lineMagnet hν h).ge
  · intro χ hχ
    constructor
    · rintro (h | h)
      · exact h.le
      · exact (pairing_lineMagnet hν h).ge
    · intro h
      rcases h.lt_or_eq with h | h
      · exact Or.inl h
      · right
        by_cases h0 : χ = 0
        · rw [h0]; exact (lineMagnet α).zero_mem
        · exact hgen χ ((mem_tangentWeights_iff_mem_roots h0).1 hχ) h.symm
  · exact connectedSpace_parabolic_of_levi (π.cocharacter ν)
      (connectedSpace_levi_of_openCell _ (isOpenEmbedding_openCell _))

/-- **Levi version of Prop. 16.10**: `G^{ℤα} = Z_G(μ)`. -/
theorem magnetIdeal_lineMagnet_eq_levi [IrreducibleSpace (PrimeSpectrum H)] {α : Additive X}
    {μ : X →* Multiplicative ℤ} (hμ : pairingHom μ α = 0)
    (hgen : ∀ β ∈ roots π, pairingHom μ β = 0 → β ∈ lineMagnet α) :
    magnetIdeal (torusGrading π) (lineMagnet α) =
      (leviDefiningHopfIdeal (π.cocharacter μ)).toIdeal := by
  have hμ' : pairingHom μ⁻¹ α = 0 := by rw [pairingHom_inv, hμ, neg_zero]
  have hgen' : ∀ β ∈ roots π, pairingHom μ⁻¹ β = 0 → β ∈ lineMagnet α := fun β hβ h =>
    hgen β hβ (by rw [pairingHom_inv] at h; omega)
  have hinf : lineMagnet α = halfLineMagnet α μ hμ ⊓ halfLineMagnet α μ⁻¹ hμ' := by
    ext χ
    constructor
    · intro h; exact ⟨Or.inr h, Or.inr h⟩
    · rintro ⟨h1 | h1, h2 | h2⟩
      · change 0 < pairingHom μ⁻¹ χ at h2; rw [pairingHom_inv] at h2; omega
      · exact h2
      · exact h1
      · exact h1
  rw [hinf, magnetIdeal_inf, magnetIdeal_halfLine_eq π hμ hgen,
    magnetIdeal_halfLine_eq π hμ' hgen', cocharacter_inv, leviDefiningHopfIdeal_def,
    HopfIdeal.sup_toIdeal]

/-- **`Z = G^{ℤα}` is connected**, for `G` smooth, connected, `α ≠ 0`, the roots in `ℚα` lying
in `ℤα` (`hRay`) and `X` free. -/
theorem connectedSpace_lineAttractor [ConnectedSpace (PrimeSpectrum H)]
    [Module.Free ℤ (Additive X)] {α : Additive X} (hα0 : α ≠ 0)
    (hRay : ∀ β ∈ roots π, (∃ m n : ℤ, n ≠ 0 ∧ n • β = m • α) → β ∈ lineMagnet α) :
    ConnectedSpace (PrimeSpectrum (H ⧸ (magnetHopfIdeal π (lineMagnet α)).toIdeal)) := by
  haveI : IrreducibleSpace (PrimeSpectrum H) := OpenCellNotes.irreducibleSpace_of_connectedSpace k
  set R := {β | β ∈ roots π ∧ ¬ ∃ m n : ℤ, n ≠ 0 ∧ n • β = m • α}
  have hR : R.Finite := (roots_finite π).subset fun β hβ => hβ.1
  obtain ⟨-, μ, -, hμα, hμR⟩ := exists_perp_cocharacter hα0 R hR
    (fun β hβ m n hn h => hβ.2 ⟨m, n, hn, h⟩)
  have hgen : ∀ β ∈ roots π, pairingHom μ β = 0 → β ∈ lineMagnet α := by
    intro β hβ h0
    by_cases hr : ∃ m n : ℤ, n ≠ 0 ∧ n • β = m • α
    · exact hRay β hβ hr
    · exact absurd h0 (hμR β ⟨hβ, hr⟩)
  have heq : (leviDefiningHopfIdeal (π.cocharacter μ)).toIdeal =
      (magnetHopfIdeal π (lineMagnet α)).toIdeal := by
    rw [magnetHopfIdeal_toIdeal, magnetIdeal_lineMagnet_eq_levi π hμα hgen]
  haveI hL := connectedSpace_levi_of_openCell (π.cocharacter μ) (isOpenEmbedding_openCell _)
  let e := PrimeSpectrum.homeomorphOfRingEquiv (Ideal.quotEquivOfEq heq)
  exact e.surjective.connectedSpace e.continuous

end AlgMag.Reductive
