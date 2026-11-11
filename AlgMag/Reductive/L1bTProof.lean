/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Reductive.T2Classical

/-!
# `L1bT` from L1b plus one named swap (Borel 11.15 reduction)

Survey result: neither Tau Ceti nor AlgMag has "every Borel `B ⊇ T` is `P(ν)` for a regular
cocharacter `ν` of `T`", nor the centralizer theorem `Z_B(S)` Borel in `Z_G(S)`. The full proof of
`L1bT` is therefore out of reach here. We isolate the exact missing step:

`BorelSwap Tq`: for a Borel `B ⊇ T` and a cocharacter `μ` of `T`, there is a Borel `B' ⊆ P(μ)`
with `B' ∩ Z(μ) = B ∩ Z(μ)` (Hopf ideals: `P μ ≤ B'`, `B' ⊔ Z μ = B ⊔ Z μ`).

Classically `B' = P(Nμ + ν)`, `ν` regular `B`-dominant, `N ≫ 0`: its roots are those `α` with
`⟨μ,α⟩ > 0`, or `⟨μ,α⟩ = 0` and `⟨ν,α⟩ > 0`; the second set is `Φ(B ∩ Z(μ))`.

`l1bT_of_swap`: `BorelSwap Tq → L1bT Tq`, proved from `L1bProof.l1b` + `UCandProof.uCand`.
-/

open Magnetism TauCeti TauCeti.Cocharacter

namespace AlgMag.Reductive.L1bTProof

open AlgMag.Reductive AlgMag.Reductive.BorelRoute AlgMag.Reductive.BorelRouteReal
  AlgMag.Reductive.T2Classical

universe u

variable {k : Type u} {H : Type u} [Field k] [CommRing H] [HopfAlgebra k H]
  [Algebra.FiniteType k H]

/-- (named) Borel swap: a Borel `B ⊇ T` can be replaced by a Borel `B' ⊆ P(μ)` with the same
intersection with `Z(μ)`. -/
def BorelSwap (Tq : HopfIdeal k H) : Prop :=
  ∀ {B : HopfIdeal k H} (μ : H →ₐc[k] LaurentPolynomial k), IsBorelIn ⊥ B → B ≤ Tq →
    Tq.toIdeal ≤ RingHom.ker (μ : H →ₐ[k] LaurentPolynomial k) →
    ∃ B' : HopfIdeal k H, IsBorelIn ⊥ B' ∧ P μ ≤ B' ∧ B' ⊔ Z μ = B ⊔ Z μ

/-- **L1bT from the swap** (proved). -/
theorem l1bT_of_swap [Algebra.Smooth k H] {Tq : HopfIdeal k H} (h : BorelSwap Tq) : L1bT Tq := by
  intro B μ hB hBT hμ
  obtain ⟨B', hB', hPB', heq⟩ := h μ hB hBT hμ
  rw [← heq]
  exact L1bProof.l1b (fun l => UCandProof.uCand l) μ hB' hPB'

/-- **(c) from the swap** (proved). -/
theorem stepC_of_swap [Algebra.Smooth k H] {Tq : HopfIdeal k H} (h : BorelSwap Tq)
    (μ : H →ₐc[k] LaurentPolynomial k)
    (hμ : Tq.toIdeal ≤ RingHom.ker (μ : H →ₐ[k] LaurentPolynomial k)) : StepC Tq μ :=
  stepC_of_l1bT (l1bT_of_swap h) μ hμ

end AlgMag.Reductive.L1bTProof

#print axioms AlgMag.Reductive.L1bTProof.l1bT_of_swap
#print axioms AlgMag.Reductive.L1bTProof.stepC_of_swap
