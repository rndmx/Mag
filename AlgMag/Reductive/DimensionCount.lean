/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Reductive.WeylInNormal
import AlgMag.Reductive.ForwardCounting
import AlgMag.Reductive.SubgroupFullLie
import AlgMag.Reductive.RootAttractor
import AlgMag.Reductive.LieTorusZero
import AlgMag.Reductive.OpenCell.LieDimension

/-!
# (i) and the root counts from one dimension inequality

`k = k̄`, `G = Spec H` smooth and irreducible, `T = D(X)` given by `π` onto, `f = ⟨·, λ⟩` for a
cocharacter `λ` nonzero on every root. If

  `dim Lie G ≤ dim Lie T + #{rays of f-positive roots} + #{rays of f-negative roots}`  (DC)

(classically `dim G = dim T + |Φ|`), then
* `dim 𝔤₀ = dim Lie T`, and `Z_G(T) = T` (condition (i)): the Levi `G^{f⁻¹(0)}` is connected
  (open cell), contains `T`, and has Lie algebra `𝔤₀ = Lie T`, so it is `T`
  (`eq_of_le_of_finrank_cotangent_eq`);
* `dim U(±λ) ≤ #rays`, the input of `condII_of_counting` (ForwardCounting.lean).

(DC) is the single geometric input of (⇒) besides the Weyl elements.
-/

suppress_compilation

set_option linter.style.haveILetI false

open Magnetism TauCeti WithConv
open scoped TensorProduct

namespace AlgMag.Reductive

universe u

variable {k : Type u} {H : Type u} {X : Type u}
variable [Field k] [CommRing H] [HopfAlgebra k H] [CommGroup X] [DecidableEq X]
variable (π : H →ₐc[k] MonoidAlgebra k X) [Module.Finite k (Bialgebra.CotangentSpace k H)]

omit [DecidableEq X] in
/-- `#rays ≤ dim U(λ_f)`. -/
lemma posRays_le_posDim (f : Additive X →+ ℤ) : posRays π f ≤ posDim π f := by
  classical
  unfold posRays posDim
  refine (Finset.card_image_le).trans ?_
  rw [Finset.card_eq_sum_ones]
  refine Finset.sum_le_sum fun α hα => ?_
  simp only [posRoots, Finset.mem_filter, Set.Finite.mem_toFinset] at hα
  exact finrank_pos_of_mem_roots π hα.1

/-- `Σ_{α ∈ Φ} dim 𝔤_α = dim U(λ_f) + dim U(λ_{-f})` for `f` nonzero on the roots. -/
lemma sum_rootSpace_eq_posDim (f : Additive X →+ ℤ) (hf : ∀ α ∈ roots π, f α ≠ 0) :
    ∑ α ∈ (roots_finite π).toFinset, Module.finrank k (rootSpace π α) =
      posDim π f + posDim π (-f) := by
  classical
  have e1 : ∀ α, Module.finrank k (rootSpace π α) =
      Module.finrank k (Derivation.adjointWeightSpace π (Additive.toMul α)) :=
    finrank_rootSpace_eq_finrank_adjointWeightSpace
  simp_rw [e1]
  rw [← Finset.sum_filter_add_sum_filter_not _ (fun α => 0 < f α)]
  have hA : (roots_finite π).toFinset.filter (fun α => 0 < f α) = posRoots π f := by
    ext α; simp [posRoots, Set.Finite.mem_toFinset]
  have hB : (roots_finite π).toFinset.filter (fun α => ¬ 0 < f α) = posRoots π (-f) := by
    ext α
    rw [posRoots, Finset.mem_filter, Finset.mem_filter, Set.Finite.mem_toFinset,
      AddMonoidHom.neg_apply, not_lt]
    constructor
    · rintro ⟨hα, hle⟩
      exact ⟨hα, by have := hf α hα; omega⟩
    · rintro ⟨hα, hlt⟩
      exact ⟨hα, by omega⟩
  rw [hA, hB]
  rfl

/-- `dim Lie T ≤ dim 𝔤₀` (`T ⊆ G^0`). -/
lemma finrank_lieTorus_le (hπ : Function.Surjective π) :
    Module.finrank k (Bialgebra.CotangentSpace k (H ⧸ (HopfIdeal.kerOfSurjective π hπ).toIdeal)) ≤
      Module.finrank k (rootSpace π 0) := by
  rw [OpenCellNotes.finrank_quotient_eq_lieSubalgebra, rootSpace_zero_eq_lieBot]
  apply Submodule.finrank_mono
  intro d hd
  change d ∈ (magnetHopfIdeal π ⊥).lieSubalgebra (B := k)
  have hd' : d ∈ (HopfIdeal.kerOfSurjective π hπ).lieSubalgebra (B := k) := hd
  rw [HopfIdeal.mem_lieSubalgebra_iff] at hd' ⊢
  intro x hx
  apply hd'
  rw [magnetHopfIdeal_toIdeal] at hx
  have := magnetIdeal_le_ker_torus π ⊥ hx
  rw [HopfIdeal.mem_toIdeal, HopfIdeal.mem_kerOfSurjective]
  exact this

variable [IsAlgClosed k] [Algebra.FiniteType k H] [Algebra.Smooth k H]
variable [Monoid.FG X] [IsMulTorsionFree X]

omit [IsAlgClosed k] in
/-- **(i) and the root counts from (DC).** -/
theorem condI_and_counts_of_dimCount (hπ : Function.Surjective π)
    [IrreducibleSpace (PrimeSpectrum H)] (ψ : X →* Multiplicative ℤ)
    (hψ : ∀ α ∈ roots π, pairingHom ψ α ≠ 0)
    (hDC : Module.finrank k (Derivation k H (Bialgebra.CounitAlgebra k H k)) ≤
      Module.finrank k (Bialgebra.CotangentSpace k (H ⧸ (HopfIdeal.kerOfSurjective π hπ).toIdeal)) +
        posRays π (pairingHom ψ) + posRays π (-pairingHom ψ)) :
    magnetIdeal (torusGrading π) ⊥ = RingHom.ker π.toAlgHom ∧
      posDim π (pairingHom ψ) ≤ posRays π (pairingHom ψ) ∧
      posDim π (-pairingHom ψ) ≤ posRays π (-pairingHom ψ) := by
  set f := pairingHom ψ
  have hsum := finrank_lie_eq_sum_rootSpace π
  rw [sum_rootSpace_eq_posDim π f hψ] at hsum
  have h1 := posRays_le_posDim π f
  have h2 := posRays_le_posDim π (-f)
  have h3 := finrank_lieTorus_le π hπ
  have hT0 : Module.finrank k
      (Bialgebra.CotangentSpace k (H ⧸ (HopfIdeal.kerOfSurjective π hπ).toIdeal)) =
      Module.finrank k (rootSpace π 0) := by omega
  refine ⟨?_, by omega, by omega⟩
  -- the Levi `G^{f⁻¹(0)}`
  set N' : Magnet (Additive X) := (⊥ : Magnet ℤ).comap f with hN'
  haveI : ConnectedSpace (PrimeSpectrum (H ⧸ (magnetHopfIdeal π N').toIdeal)) := by
    rw [magnetHopfIdeal_toIdeal, hN', magnetIdeal_torusGrading_comap_bot]
    exact connectedSpace_levi_of_openCell (π.cocharacter ψ)
      (isOpenEmbedding_openCell (π.cocharacter ψ))
  haveI : Algebra.Smooth k (H ⧸ (magnetHopfIdeal π N').toIdeal) :=
    smooth_quotient_magnetHopfIdeal π N'
  have hπ' : Function.Surjective π.toAlgHom := hπ
  have hkerI : (HopfIdeal.kerOfSurjective π hπ).toIdeal = RingHom.ker π.toAlgHom := by
    ext x; rw [HopfIdeal.mem_toIdeal, HopfIdeal.mem_kerOfSurjective, RingHom.mem_ker]; rfl
  haveI : Algebra.Smooth k (MonoidAlgebra k X) := SliceSmooth.smooth_monoidAlgebra
  haveI : Algebra.Smooth k (H ⧸ (HopfIdeal.kerOfSurjective π hπ).toIdeal) := by
    rw [hkerI]
    exact Algebra.Smooth.of_equiv (Ideal.quotientKerAlgEquivOfSurjective hπ').symm
  have hle : magnetHopfIdeal π N' ≤ HopfIdeal.kerOfSurjective π hπ := by
    rw [← HopfIdeal.toIdeal_le_toIdeal, magnetHopfIdeal_toIdeal, hkerI]
    exact magnetIdeal_le_ker_torus π N'
  have hroots : ∀ α ∈ roots π, α ∈ (⊥ : Magnet (Additive X)) ↔ α ∈ N' := by
    intro α hα
    simp only [AddSubmonoid.mem_bot, N', AddSubmonoid.mem_comap]
    exact iff_of_false (ne_zero_of_mem_roots hα) (hψ α hα)
  have hdim : Module.finrank k
      (Bialgebra.CotangentSpace k (H ⧸ (HopfIdeal.kerOfSurjective π hπ).toIdeal)) =
      Module.finrank k (Bialgebra.CotangentSpace k (H ⧸ (magnetHopfIdeal π N').toIdeal)) := by
    rw [hT0, OpenCellNotes.finrank_quotient_eq_lieSubalgebra (magnetHopfIdeal π N'),
      ← lieSubalgebra_magnetHopfIdeal_eq_of_roots (π := π) hroots, ← rootSpace_zero_eq_lieBot]
  have heq := eq_of_le_of_finrank_cotangent_eq hle hdim
  apply le_antisymm (magnetIdeal_le_ker_torus π ⊥)
  rw [← hkerI, ← heq, magnetHopfIdeal_toIdeal]
  rw [magnetIdeal, magnetIdeal]
  apply Ideal.span_mono
  intro x hx
  simp only [Set.mem_iUnion] at hx ⊢
  obtain ⟨χ, hχ, hx⟩ := hx
  refine ⟨χ, fun h => hχ ?_, hx⟩
  rw [AddSubmonoid.mem_bot] at h
  rw [h]
  exact N'.zero_mem

end AlgMag.Reductive
