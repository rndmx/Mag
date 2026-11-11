/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Reductive.BorGalleryStep
import AlgMag.Reductive.BorBasePair
import AlgMag.Reductive.OpenCell.OpenCellFlatness
import AlgMag.Reductive.TangentRoots
import AlgMag.Reductive.AttractorReflects
import AlgMag.Reductive.OpenCellGen

/-!
# (Base±) ⇒ (Bor) relative to a fixed torus action (Bor-plan §2)

`BorHypπ π`: for `G` reductive, `P(π.cocharacter ψ)` is Borel for every `π`-regular `ψ`
(the form used downstream).  `bor_of_base` proves it from:
* the base pair at one regular `ψ₀` (`P(ψ₀)`, `P(ψ₀⁻¹)` Borel);
* `WallStepπ` (named; W2–W5: Levi `Z = G^{ℤβ}`, L1, Borel conjugacy in `Z`, T1-dyn give
  `n ∈ N_Z(T)(k)` with `n P(ν) n⁻¹ = P(σν)`, `σ ≠ 1` fixing `μ`; W5 must use the weight-restricted
  form of `conj_mem_parabolic_inv`, the all-`χ` form is false);
* `GalleryStep π` (named, W6), finiteness of the tangent weights, geometric connectedness of
  the parabolics (input of S0);
* S0 `parabolic_eq_of_sameSigns` (proved) for the last, same-chamber step.
-/

open Magnetism TauCeti TauCeti.Cocharacter
open scoped TensorProduct

namespace AlgMag.Reductive

universe u

variable {k : Type u} {H : Type u} {X : Type u}
variable [Field k] [CommRing H] [HopfAlgebra k H] [CommGroup X] [DecidableEq X]
  [Algebra.FiniteType k H]
variable (π : H →ₐc[k] MonoidAlgebra k X)

local notation "Hf" => FiniteTypeCommHopfAlgCat.of k H

/-- The chamber invariant: `P(ψ)` and `P(ψ⁻¹)` are Borel. -/
def BorInv (ψ : X →* Multiplicative ℤ) : Prop :=
  HopfIdeal.IsBorelOverAlgClosed k Hf (parabolicDefiningHopfIdeal (π.cocharacter ψ)) ∧
    HopfIdeal.IsBorelOverAlgClosed k Hf (parabolicDefiningHopfIdeal (π.cocharacter ψ⁻¹))

/-- **(Bor)** relative to `π`. -/
def BorHypπ : Prop :=
  reductiveCommHopfAlgProperty k Hf → ∀ ψ : X →* Multiplicative ℤ, RegCochar π ψ →
    HopfIdeal.IsBorelOverAlgClosed k Hf (parabolicDefiningHopfIdeal (π.cocharacter ψ))

/-- **Wall step W2–W5 (named).** -/
def WallStepπ : Prop :=
  reductiveCommHopfAlgProperty k Hf → ∀ ψ ψ' : X →* Multiplicative ℤ,
    RegCochar π ψ → RegCochar π ψ' → Adjacent π ψ ψ' → BorInv π ψ → BorInv π ψ'

/-- Geometric connectedness of every dynamic parabolic of `π` (input of S0). -/
def ParConn : Prop :=
  ∀ ψ : X →* Multiplicative ℤ, ConnectedSpace (PrimeSpectrum (AlgebraicClosure k ⊗[k]
      (H ⧸ (parabolicDefiningHopfIdeal (π.cocharacter ψ)).toIdeal)))

omit [Algebra.FiniteType k H] in
theorem borPairingHom_inv (ψ : X →* Multiplicative ℤ) (χ : Additive X) :
    pairingHom ψ⁻¹ χ = - pairingHom ψ χ := by
  simp [pairingHom_apply]

omit [Algebra.FiniteType k H] in
theorem regCochar_inv {ψ : X →* Multiplicative ℤ} (h : RegCochar π ψ) : RegCochar π ψ⁻¹ :=
  fun χ hχ h0 => by rw [borPairingHom_inv]; exact neg_ne_zero.2 (h χ hχ h0)

omit [Algebra.FiniteType k H] in
/-- Same chamber ⇒ same signs, and also for the inverses. -/
theorem sameSigns_of_diffSet_empty {ψ φ : X →* Multiplicative ℤ} (hψ : RegCochar π ψ)
    (hφ : RegCochar π φ) (he : diffSet π ψ φ = ∅) :
    (∀ χ ∈ tangentWeights π k, (0 ≤ pairingHom ψ χ ↔ 0 ≤ pairingHom φ χ)) ∧
    (∀ χ ∈ tangentWeights π k, (0 ≤ pairingHom ψ⁻¹ χ ↔ 0 ≤ pairingHom φ⁻¹ χ)) := by
  have h1 : ∀ χ ∈ tangentWeights π k, (0 ≤ pairingHom ψ χ ↔ 0 ≤ pairingHom φ χ) := by
    intro χ hχ
    by_contra hc
    have : χ ∈ diffSet π ψ φ := ⟨hχ, hc⟩
    rw [he] at this; exact this
  refine ⟨h1, fun χ hχ => ?_⟩
  rw [borPairingHom_inv, borPairingHom_inv]
  by_cases h0 : χ = 0
  · subst h0; simp
  have a := hψ χ hχ h0
  have b := hφ χ hχ h0
  have c := h1 χ hχ
  constructor <;> intro h <;> omega

/-- **(Base±) ⇒ (Bor)**, by the wall-crossing argument. -/
theorem bor_of_base [Algebra.Smooth k H] (hfin : (tangentWeights π k).Finite)
    (hG : GalleryStep π) (hW : WallStepπ π) (hC : ParConn π)
    {ψ₀ : X →* Multiplicative ℤ} (h₀ : RegCochar π ψ₀) (hB₀ : BorInv π ψ₀) :
    BorHypπ π := by
  intro hred φ hφ
  refine (gallery_induction π hfin hG (BorInv π) (hW hred) ?_ h₀ hB₀ φ hφ).1
  intro ψ φ hψ hφ he hI
  obtain ⟨s1, s2⟩ := sameSigns_of_diffSet_empty π hψ hφ he
  refine ⟨?_, ?_⟩
  · rw [← parabolic_eq_of_sameSigns π ψ φ s1 (hC ψ) (hC φ)]; exact hI.1
  · rw [← parabolic_eq_of_sameSigns π ψ⁻¹ φ⁻¹ s2 (hC _) (hC _)]; exact hI.2

/-! ### Discharged inputs: `hfin`, `ParConn`, the base link -/

omit [DecidableEq X] in
/-- `hfin`: the tangent weights are finite (roots ∪ {0}). -/
theorem finite_tangentWeights [DecidableEq X] : (tangentWeights π k).Finite := by
  refine ((finite_roots (π := π)).insert 0).subset fun χ hχ => ?_
  by_cases h0 : χ = 0
  · exact Or.inl h0
  · exact Or.inr ((mem_tangentWeights_iff_mem_roots h0).1 hχ)

/-- `ParConn` for `G` smooth and geometrically connected. -/
theorem parConn [Algebra.Smooth k H] [ConnectedSpace (PrimeSpectrum (AlgebraicClosure k ⊗[k] H))] :
    ParConn π := by
  intro ψ
  have : IrreducibleSpace (PrimeSpectrum (AlgebraicClosure k ⊗[k] H)) :=
    AlgMag.OpenCellNotes.irreducibleSpace_of_connectedSpace (AlgebraicClosure k)
  exact connectedSpace_parabolic_baseChange_of_levi π ψ
    (connectedSpace_levi_baseChange_of_openCell π ψ
      (flat_openCellRingHom (k := AlgebraicClosure k) _))

/-- **Base link.** `BorInv` at `ψ₀` is (Base±) at `ν₀ = π.cocharacter ψ₀`. -/
theorem borInv_iff (ψ : X →* Multiplicative ℤ) :
    BorInv π ψ ↔
      HopfIdeal.IsBorelOverAlgClosed k Hf (parabolicDefiningHopfIdeal (π.cocharacter ψ)) ∧
      HopfIdeal.IsBorelOverAlgClosed k Hf
        (parabolicDefiningHopfIdeal (π.cocharacter ψ).oppositeCocharacter) := by
  rw [BorInv, cocharacter_inv]

/-- **(Base±) ⇒ (Bor)**, with `hfin` and `ParConn` discharged. -/
theorem bor_of_base' [Algebra.Smooth k H]
    [ConnectedSpace (PrimeSpectrum (AlgebraicClosure k ⊗[k] H))]
    (hG : GalleryStep π) (hW : WallStepπ π)
    {ψ₀ : X →* Multiplicative ℤ} (h₀ : RegCochar π ψ₀)
    (hB₀ : HopfIdeal.IsBorelOverAlgClosed k Hf (parabolicDefiningHopfIdeal (π.cocharacter ψ₀)))
    (hB₀' : HopfIdeal.IsBorelOverAlgClosed k Hf
        (parabolicDefiningHopfIdeal (π.cocharacter ψ₀).oppositeCocharacter)) :
    BorHypπ π :=
  bor_of_base π (finite_tangentWeights π) hG hW (parConn π) h₀ ((borInv_iff π ψ₀).2 ⟨hB₀, hB₀'⟩)

/-- **(Base±) ⇒ (Bor)** for `X` free: only the wall step `WallStepπ` remains named. -/
theorem bor_of_base_free [Module.Free ℤ (Additive X)] [Algebra.Smooth k H]
    [ConnectedSpace (PrimeSpectrum (AlgebraicClosure k ⊗[k] H))]
    (hW : WallStepπ π) {ψ₀ : X →* Multiplicative ℤ} (h₀ : RegCochar π ψ₀)
    (hB₀ : HopfIdeal.IsBorelOverAlgClosed k Hf (parabolicDefiningHopfIdeal (π.cocharacter ψ₀)))
    (hB₀' : HopfIdeal.IsBorelOverAlgClosed k Hf
        (parabolicDefiningHopfIdeal (π.cocharacter ψ₀).oppositeCocharacter)) :
    BorHypπ π :=
  bor_of_base' π (galleryStep π (finite_tangentWeights π)) hW h₀ hB₀ hB₀'

end AlgMag.Reductive
