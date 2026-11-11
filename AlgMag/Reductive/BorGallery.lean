/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Reductive.BorWalls

/-!
# Gallery induction on chambers (Bor-plan §2, W6, abstract part)

For a torus action `π` with tangent weights `Φ = tangentWeights π k`, a cocharacter
`ψ : X →* ℤ` is *regular* if it vanishes on no nonzero weight.  `diffSet ψ φ` is the set of
weights on which `ψ` and `φ` have different signs; `Adjacent ψ ψ'` means they differ only on one
line `ℚ^× β` (one wall crossed).

* `gallery_induction` (proved): any predicate on regular cocharacters which is transported along
  adjacent steps holds everywhere, given one regular base point, the named gallery step `GalleryStep`
  (a generic segment crosses one wall at a time), and finiteness of `Φ`; the last step (no
  difference left) is handled by a given same-signs transport (S0).
-/

open Magnetism TauCeti TauCeti.Cocharacter

namespace AlgMag.Reductive

universe u

variable {k : Type u} {H : Type u} {X : Type*}
variable [Field k] [CommRing H] [HopfAlgebra k H] [CommGroup X] [DecidableEq X]
variable (π : H →ₐc[k] MonoidAlgebra k X)

/-- `ψ` is regular for `π`: nonzero on every nonzero tangent weight. -/
def RegCochar (ψ : X →* Multiplicative ℤ) : Prop :=
  ∀ χ ∈ tangentWeights π k, χ ≠ 0 → pairingHom ψ χ ≠ 0

/-- Weights on which `ψ`, `φ` have different signs. -/
def diffSet (ψ φ : X →* Multiplicative ℤ) : Set (Additive X) :=
  {χ | χ ∈ tangentWeights π k ∧ ¬ (0 ≤ pairingHom ψ χ ↔ 0 ≤ pairingHom φ χ)}

/-- One wall crossed: the sign changes all lie on one line `ℚ^× β`. -/
def Adjacent (ψ ψ' : X →* Multiplicative ℤ) : Prop :=
  ∃ β : Additive X, ∀ χ ∈ diffSet π ψ ψ', ∃ a b : ℤ, a ≠ 0 ∧ b ≠ 0 ∧ a • χ = b • β

/-- **W6 (named).** From a regular `ψ` towards a regular `φ` with some sign difference, one
can cross a single wall and strictly reduce the set of differences. (Generic segment
`[ψ, φ]` in `X^∨ ⊗ ℚ`, first wall crossed, rational point cleared of denominators.) -/
def GalleryStep : Prop :=
  ∀ ψ φ : X →* Multiplicative ℤ, RegCochar π ψ → RegCochar π φ →
    (diffSet π ψ φ).Nonempty →
    ∃ ψ', RegCochar π ψ' ∧ Adjacent π ψ ψ' ∧ diffSet π ψ' φ ⊂ diffSet π ψ φ

theorem diffSet_subset (ψ φ : X →* Multiplicative ℤ) : diffSet π ψ φ ⊆ tangentWeights π k :=
  fun _ h => h.1

/-- **Gallery induction.** -/
theorem gallery_induction (hfin : (tangentWeights π k).Finite) (hG : GalleryStep π)
    (Inv : (X →* Multiplicative ℤ) → Prop)
    (hstep : ∀ ψ ψ', RegCochar π ψ → RegCochar π ψ' → Adjacent π ψ ψ' → Inv ψ → Inv ψ')
    (hsame : ∀ ψ φ, RegCochar π ψ → RegCochar π φ → diffSet π ψ φ = ∅ → Inv ψ → Inv φ)
    {ψ₀ : X →* Multiplicative ℤ} (h₀ : RegCochar π ψ₀) (hI₀ : Inv ψ₀)
    (φ : X →* Multiplicative ℤ) (hφ : RegCochar π φ) : Inv φ := by
  suffices key : ∀ n, ∀ ψ, RegCochar π ψ → Inv ψ → (diffSet π ψ φ).ncard ≤ n → Inv φ from
    key _ ψ₀ h₀ hI₀ le_rfl
  intro n
  induction n with
  | zero =>
    intro ψ hψ hI hn
    have hf : (diffSet π ψ φ).Finite := hfin.subset (diffSet_subset π ψ φ)
    have : diffSet π ψ φ = ∅ := (Set.ncard_eq_zero hf).1 (Nat.le_zero.1 hn)
    exact hsame ψ φ hψ hφ this hI
  | succ n ih =>
    intro ψ hψ hI hn
    rcases (diffSet π ψ φ).eq_empty_or_nonempty with he | hne
    · exact hsame ψ φ hψ hφ he hI
    obtain ⟨ψ', hψ', hadj, hlt⟩ := hG ψ φ hψ hφ hne
    have hf : (diffSet π ψ φ).Finite := hfin.subset (diffSet_subset π ψ φ)
    have := Set.ncard_lt_ncard hlt hf
    exact ih ψ' hψ' (hstep ψ ψ' hψ hψ' hadj hI) (by omega)

end AlgMag.Reductive
