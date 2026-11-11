/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Reductive.ParabolicGenRay
import AlgMag.Reductive.LieTorusZero
import AlgMag.Reductive.OpenCell.LieDimension

/-!
# Condition (i) at Lie level: `dim 𝔤_0 ≤ dim Lie T` (`hLie0` of `dimCount_of_reductive'`)

Plan: `equivalence-reductive/T2-plan.md` §4.2. `C = Z_G(T) = G^0` (`magnetHopfIdeal π ⊥`), `ν = λ_ψ`
regular, `N = C_u(k)` (points of the unipotent radical of `C`).

PROVED here: step 4 (group part). If `N` commutes with every ray piece `U_(α)(k)` for `±ν`
(steps 2–3) and is normalised by `C(k)`, then by (Gen) (`unipotent_le_closure_rayPoints`) `N`
centralises `U(±ν)(k)`; if `U(-ν)(k) ∪ C(k) ∪ U(ν)(k)` generates `G(k)` (open cell dense), `N` is
normal in `G(k)`. The Lie conclusion `𝔤_0 = Lie T` from `C = T` (`rootSpace_zero_eq_lieBot`).

NAMED HYPOTHESES (inputs not yet in Lean):
* `hcent` (steps 2–3): T4 (`dim U_α = 1`, `U_α ≅ 𝔾_a`) + rigidity of `T`-equivariant additive
  polynomials: `C_u(k)` commutes with every ray piece.
* `hnormC` (step 1): `C_u` is characteristic in `C`.
* `hcell`: `Ω = U(-ν)·C·U(ν)` dense open (`isOpenEmbedding_openCell`) ⇒ `G(k) = Ω(k)Ω(k)`
  (`subset_of_isOpen_subset`, PointsDensity.lean).
* `hfinal` (steps 4b–6): normal points ⇒ `C_u ⊲ G` (reduced, `k = k̄`) ⇒ `C_u = 1` (reductive)
  ⇒ `C` solvable (Bor) with trivial `R_u` is a torus ⇒ `C = T`.
-/

suppress_compilation

open Magnetism TauCeti TauCeti.Cocharacter WithConv

namespace AlgMag.Reductive

universe u

variable {k : Type u} {H : Type u} {X : Type u}
variable [Field k] [CommRing H] [HopfAlgebra k H] [CommGroup X] [DecidableEq X]
variable (π : H →ₐc[k] MonoidAlgebra k X)

/-- **Step 4 (group part).** -/
theorem normal_of_centralises_rays [IsAlgClosed k] [Algebra.FiniteType k H] [Algebra.Smooth k H]
    (ψ : X →* Multiplicative ℤ) (N : Subgroup (WithConv (H →ₐ[k] k)))
    (hcent : ∀ φ : X →* Multiplicative ℤ, (φ = ψ ∨ φ = ψ⁻¹) → ∀ α : PosRay φ,
      ∀ r ∈ rayPoints π φ α, ∀ c ∈ N, c * r = r * c)
    (hnormC : ∀ z ∈ attractorSubgroup π ⊥ k, ∀ c ∈ N, z * c * z⁻¹ ∈ N)
    (hcell : Subgroup.closure (SetLike.coe (unipotent k (π.cocharacter ψ⁻¹)) ∪
      SetLike.coe (attractorSubgroup π ⊥ k) ∪ SetLike.coe (unipotent k (π.cocharacter ψ))) = ⊤) :
    N.Normal := by
  have hU : ∀ φ : X →* Multiplicative ℤ, (φ = ψ ∨ φ = ψ⁻¹) →
      ∀ u ∈ unipotent k (π.cocharacter φ), ∀ c ∈ N, c * u = u * c := by
    intro φ hφ u hu c hc
    have hle : Subgroup.closure (⋃ α : PosRay φ, rayPoints π φ α) ≤
        Subgroup.centralizer {c} := by
      rw [Subgroup.closure_le]
      intro r hr
      obtain ⟨α, hr⟩ := Set.mem_iUnion.1 hr
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
      intro h hh
      rw [Set.mem_singleton_iff.1 hh]
      exact hcent φ hφ α r hr c hc
    exact (Subgroup.mem_centralizer_iff.1 (hle (unipotent_le_closure_rayPoints π φ hu))) c rfl
  have hgen : Subgroup.closure (SetLike.coe (unipotent k (π.cocharacter ψ⁻¹)) ∪
      SetLike.coe (attractorSubgroup π ⊥ k) ∪ SetLike.coe (unipotent k (π.cocharacter ψ))) ≤
      Subgroup.normalizer (N : Set (WithConv (H →ₐ[k] k))) := by
    rw [Subgroup.closure_le]
    have hcomm : ∀ u, (∀ c ∈ N, c * u = u * c) → u ∈ Subgroup.normalizer (N : Set (WithConv (H →ₐ[k] k))) := by
      intro u hu
      rw [Subgroup.mem_normalizer_iff]
      intro h
      constructor
      · intro hh
        rw [← hu h hh, mul_assoc, mul_inv_cancel, mul_one]; exact hh
      · intro hh
        have e : u * h * u⁻¹ = h := by
          have := hu (u * h * u⁻¹) hh
          have h2 : u * h = u * (u * h * u⁻¹) := by
            calc u * h = (u * h * u⁻¹) * u := by group
              _ = u * (u * h * u⁻¹) := this
          exact (mul_left_cancel h2).symm
        rw [e] at hh
        exact hh
    rintro g ((hg | hg) | hg)
    · exact hcomm g fun c hc => hU _ (Or.inr rfl) g hg c hc
    · rw [SetLike.mem_coe, Subgroup.mem_normalizer_iff]
      intro h
      refine ⟨fun hh => hnormC g hg h hh, fun hh => ?_⟩
      have := hnormC g⁻¹ ((attractorSubgroup π ⊥ k).inv_mem hg) _ hh
      simpa [mul_assoc] using this
    · exact hcomm g fun c hc => hU _ (Or.inl rfl) g hg c hc
  rw [hcell, top_le_iff] at hgen
  exact Subgroup.normalizer_eq_top_iff.1 hgen

/-- **`hLie0`**: `dim 𝔤_0 ≤ dim Lie T`, from step 4 and the named inputs. -/
theorem finrank_rootSpace_zero_le_of_centralizer [IsAlgClosed k] [Algebra.FiniteType k H]
    [Algebra.Smooth k H] [Module.Finite k (Bialgebra.CotangentSpace k H)]
    (hπ : Function.Surjective π) (ψ : X →* Multiplicative ℤ)
    (N : Subgroup (WithConv (H →ₐ[k] k)))
    (hcent : ∀ φ : X →* Multiplicative ℤ, (φ = ψ ∨ φ = ψ⁻¹) → ∀ α : PosRay φ,
      ∀ r ∈ rayPoints π φ α, ∀ c ∈ N, c * r = r * c)
    (hnormC : ∀ z ∈ attractorSubgroup π ⊥ k, ∀ c ∈ N, z * c * z⁻¹ ∈ N)
    (hcell : Subgroup.closure (SetLike.coe (unipotent k (π.cocharacter ψ⁻¹)) ∪
      SetLike.coe (attractorSubgroup π ⊥ k) ∪ SetLike.coe (unipotent k (π.cocharacter ψ))) = ⊤)
    (hfinal : N.Normal → magnetHopfIdeal π ⊥ = HopfIdeal.kerOfSurjective π hπ) :
    Module.finrank k (rootSpace π 0) ≤
      Module.finrank k (Bialgebra.CotangentSpace k
        (H ⧸ (HopfIdeal.kerOfSurjective π hπ).toIdeal)) := by
  have hCT := hfinal (normal_of_centralises_rays π ψ N hcent hnormC hcell)
  rw [OpenCellNotes.finrank_quotient_eq_lieSubalgebra, rootSpace_zero_eq_lieBot, hCT]

end AlgMag.Reductive
