/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Sec12PrintedRing

/-!
# Theorem 12.4: the ring step from the cited inputs

Mayeux, *Algebraic Magnetism*, proof of Theorem 12.4. The printed proof takes two inputs from the
regular immersion `X⁰ → X^N` (Tags 067U, 063M, 062Z): `I/I²` is finite projective, and
`Sym(I/I²) → gr_I` is an isomorphism. `printed_ring` obtains them from formal smoothness. Here they
are the hypotheses, and no smoothness is assumed; the rest of the printed proof is unchanged.
-/

open AlgMag.SymRing

universe u

namespace AlgMag.Sec12Printed

section

variable {A₀ B : Type u} [CommRing A₀] [CommRing B] [Algebra A₀ B] (π : B →ₐ[A₀] A₀)

/-- The injectivity half of "`Sym(I/I²) → gr_I` is an isomorphism" (Tags 062Z, 063M), read through
any section `s` of `I → I/I²`: an element of `J^k` whose image lies in `I^(k+1)` lies in `J^(k+1)`.
The map `J^k/J^(k+1) → I^k/I^(k+1)` does not depend on `s`. -/
def GrInjective : Prop :=
  ∀ s : Conormal π →ₗ[A₀] B, (∀ p, π (s p) = 0) → (∀ p, tMap π (s p) = p) →
    ∀ (k : ℕ) (x : SymmetricAlgebra A₀ (Conormal π)), x ∈ augIdeal A₀ (Conormal π) ^ k →
      (SymmetricAlgebra.lift s : SymmetricAlgebra A₀ (Conormal π) →ₐ[A₀] B) x ∈ augI π ^ (k + 1) →
      x ∈ augIdeal A₀ (Conormal π) ^ (k + 1)

variable {π}

/-- "We then prove that `φ` is injective", from the cited isomorphism onto `gr_I`. -/
theorem phi_injective_of_grInjective (hgr : GrInjective π) {s : Conormal π →ₗ[A₀] B}
    (hπs : ∀ p, π (s p) = 0) (hts : ∀ p, tMap π (s p) = p) :
    Function.Injective
      (SymmetricAlgebra.lift s : SymmetricAlgebra A₀ (Conormal π) →ₐ[A₀] B) := by
  refine (injective_iff_map_eq_zero _).2 fun x hx => eq_zero_of_mem_pow x fun j => ?_
  induction j with
  | zero => simp
  | succ j ih => exact hgr s hπs hts j x ih (by rw [hx]; exact Ideal.zero_mem _)

end

section

variable {A₀ B Y : Type u} [CommRing A₀] [CommRing B] [Algebra A₀ B] [AddCommMonoid Y]
  [DecidableEq Y] {𝒜 : Y → Submodule A₀ B} [GradedAlgebra 𝒜] {π : B →ₐ[A₀] A₀} {w : Y → ℕ}

/-- **Theorem 12.4**, the ring statement with the printed inputs: if `I/I²` is projective and
`Sym(I/I²) → gr_I` is injective, then `φ : Sym_{A₀}(I/I²) → B` is an isomorphism. -/
theorem printed_ring_cited [Module.Projective A₀ (Conormal π)] (hgr : GrInjective π)
    (H : IsAug 𝒜 π w) : Nonempty (SymmetricAlgebra A₀ (Conormal π) ≃ₐ[A₀] B) := by
  obtain ⟨s, hts, hπs, hg⟩ := exists_section H
  exact ⟨AlgEquiv.ofBijective _
    ⟨phi_injective_of_grInjective hgr hπs hts, phi_surjective H hts hπs hg⟩⟩

end

#print axioms printed_ring_cited

end AlgMag.Sec12Printed
