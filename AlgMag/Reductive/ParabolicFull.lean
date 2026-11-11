/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Reductive.ConverseCore
import AlgMag.Reductive.LieAttractor
import AlgMag.Reductive.AttractorSmooth

/-!
# An attractor containing every root is the whole group (side lemma, not wired)

Let `G = Spec H` be smooth, of finite type and connected over a field, with a torus `D(X)`. If a
magnet `N` contains every root, then `G^N = G`. The reason: `Lie G^N = ⊕_{χ ∈ N} 𝔤_χ = Lie G`,
`G^N` is smooth (Corollary 11.10 of Algebraic Magnetism), and a smooth closed subgroup with full
Lie algebra is everything (`eq_of_le_of_finrank_cotangent_eq`).

For `N = f⁻¹(ℕ)` this is `P(λ) = G` when no root is negative on `λ`: the first brick of the
Y-free rank-one attack on (R1) (S-proof.md §16). Not used by the main theorem.
-/

suppress_compilation

open Magnetism TauCeti

namespace AlgMag.Reductive

universe u

variable {k : Type u} {H : Type u} {X : Type u}
variable [Field k] [CommRing H] [HopfAlgebra k H] [CommGroup X] [DecidableEq X]
variable [Algebra.FiniteType k H]
variable (π : H →ₐc[k] MonoidAlgebra k X)

/-- **If a magnet contains every root, its attractor is the whole group.** -/
theorem magnetHopfIdeal_eq_bot_of_roots_mem [Algebra.Smooth k H]
    [ConnectedSpace (PrimeSpectrum H)] {N : Magnet (Additive X)}
    (hN : ∀ α ∈ roots π, α ∈ N) : magnetHopfIdeal π N = ⊥ := by
  have hbot : (⊥ : HopfIdeal k H).toIdeal = ⊥ := rfl
  let e : (H ⧸ (⊥ : HopfIdeal k H).toIdeal) ≃ₐ[k] H :=
    (Ideal.quotientEquivAlgOfEq k hbot).trans (AlgEquiv.quotientBot k H)
  have : Algebra.Smooth k (H ⧸ (⊥ : HopfIdeal k H).toIdeal) := Algebra.Smooth.of_equiv e.symm
  have : ConnectedSpace (PrimeSpectrum (H ⧸ (⊥ : HopfIdeal k H).toIdeal)) := by
    let h := PrimeSpectrum.homeomorphOfRingEquiv e.toRingEquiv
    exact h.symm.surjective.connectedSpace h.symm.continuous
  have : Algebra.Smooth k (H ⧸ (magnetHopfIdeal π N).toIdeal) :=
    smooth_quotient_magnetHopfIdeal π N
  -- both Lie algebras are everything
  have hfull : ∀ (I : HopfIdeal k H),
      (∀ d : Derivation k H (Bialgebra.CounitAlgebra k H k), d ∈ I.lieSubalgebra (B := k)) →
      Module.finrank k (I.lieSubalgebra (B := k)).toSubmodule =
        Module.finrank k (Derivation k H (Bialgebra.CounitAlgebra k H k)) := by
    intro I hI
    have htop : (I.lieSubalgebra (B := k)).toSubmodule = ⊤ :=
      eq_top_iff.2 fun d _ => hI d
    rw [htop, finrank_top]
  have hbotLie : ∀ d : Derivation k H (Bialgebra.CounitAlgebra k H k),
      d ∈ (⊥ : HopfIdeal k H).lieSubalgebra (B := k) := by
    intro d
    rw [HopfIdeal.mem_lieSubalgebra_iff]
    intro x hx
    have : x = 0 := hx
    rw [this, map_zero]
  have hNLie : ∀ d : Derivation k H (Bialgebra.CounitAlgebra k H k),
      d ∈ (magnetHopfIdeal π N).lieSubalgebra (B := k) := by
    intro d
    rw [mem_lieSubalgebra_magnetHopfIdeal_iff]
    intro χ hχ h hh
    obtain ⟨f, hf, hsum⟩ := exists_rootSpace_decomp π d
    rw [← hsum, finsupp_sum_apply_of_mem π f hf hh]
    by_contra hne
    have hχ0 : χ ≠ 0 := fun h0 => hχ (h0 ▸ N.zero_mem)
    have hf0 : f χ ≠ 0 := fun h0 => hne (by rw [h0]; rfl)
    exact hχ (hN χ (mem_roots_of_mem_rootSpace π hχ0 (hf χ) hf0))
  have hdim : Module.finrank k
        (Bialgebra.CotangentSpace k (H ⧸ (magnetHopfIdeal π N).toIdeal)) =
      Module.finrank k (Bialgebra.CotangentSpace k (H ⧸ (⊥ : HopfIdeal k H).toIdeal)) := by
    rw [AlgMag.OpenCellNotes.finrank_quotient_eq_lieSubalgebra,
      AlgMag.OpenCellNotes.finrank_quotient_eq_lieSubalgebra, hfull _ hNLie, hfull _ hbotLie]
  exact (eq_of_le_of_finrank_cotangent_eq (k := k) (I := ⊥) (J := magnetHopfIdeal π N)
    bot_le hdim).symm

end AlgMag.Reductive

namespace AlgMag.Reductive

variable {k : Type u} {H : Type u} {X : Type u}
variable [Field k] [CommRing H] [HopfAlgebra k H] [CommGroup X] [DecidableEq X]
variable (π : H →ₐc[k] MonoidAlgebra k X)

/-- **If `G^N = G` (N pointed), the subgroup `G^N_e` of points with limit `e` is normal**: it is
the kernel of the limit homomorphism on `G^N(A) = G(A)`. -/
theorem prescribedUnitHopfIdeal_isNormal {N : Magnet (Additive X)}
    (hN : ∀ a ∈ N, ∀ b ∈ N, a + b = 0 → a = 0)
    (hbot : magnetIdeal (torusGrading π) N = ⊥) :
    (prescribedUnitHopfIdeal π N hN).IsNormal := by
  rw [CommHopfAlgCat.isNormal_iff_quotientPointsSubgroup_normal (CommHopfAlgCat.of k H)]
  intro A
  have hall : ∀ g : WithConv (H →ₐ[k] A), g ∈ attractorSubgroup π N A := fun g => by
    rw [mem_attractorSubgroup π, hbot]; exact bot_le
  have hmem : ∀ g : WithConv (H →ₐ[k] A),
      g ∈ CommHopfAlgCat.quotientPointsSubgroup (CommHopfAlgCat.of k H)
        (prescribedUnitHopfIdeal π N hN) A ↔ g ∈ prescribedUnitSubgroup π hN A := fun g => by
    rw [CommHopfAlgCat.mem_quotientPointsSubgroup_iff, ← prescribedUnitIdeal_le_ker_iff hN,
      ← prescribedUnitHopfIdeal_toIdeal π N hN]
    exact ⟨fun h x hx => RingHom.mem_ker.2 (h x hx), fun h x hx => RingHom.mem_ker.1 (h hx)⟩
  refine ⟨fun u hu g => ?_⟩
  rw [hmem] at hu ⊢
  obtain ⟨hu', hu1⟩ := (mem_prescribedUnitSubgroup π hN A).1 hu
  refine (mem_prescribedUnitSubgroup π hN A).2 ⟨hall _, ?_⟩
  have : (⟨g * u * g⁻¹, hall _⟩ : attractorSubgroup π N A) =
      ⟨g, hall g⟩ * ⟨u, hu'⟩ * (⟨g, hall g⟩)⁻¹ := rfl
  rw [this, map_mul, map_mul, map_inv, hu1, mul_one, mul_inv_cancel]

end AlgMag.Reductive
