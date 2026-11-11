/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Reductive.IdentityComponentRoots
import AlgMag.Reductive.OpenCell.TensorDomain
import AlgMag.Weyl.Normalizer
import AlgMag.Rooted.ReductiveRooted
import TauCeti.RingTheory.Smooth.GeometricallyReduced

/-!
# Components of `G^N` meet `N_G(T)`, and `hdet` (Theorem `thm:red-attractors` (iii))

Notes: `algmag-notes/reductive/components-NGT-B.md`, steps C1–C4.

* `exists_mul_normalizer_of_irreducible` (**C3**, abstract form): in a group, let `K ⊴ A`
  carry an irreducible topology on which conjugation by `A` is continuous; if the set `U` of
  conjugates `k t k⁻¹` of regular elements `t` contains a nonempty open set (**C2**) and every
  `y ∈ A` with `y t y⁻¹ = t'` (`t, t'` regular) normalizes `T` (**C1**), then `A = K · N_A(T)`.
* `ComponentsMeetNormalizer`: the statement `G^N(k) ⊆ K(k) · N_G(T)(k)` (output of C1–C3);
* `mem_attractor_iff` (with C4 = `Weyl.mem_attractorSubgroup_iff_weylMagnet_le`):
  `G^N(k) = ⋃_{w ∈ W_N} K(k) n_w`;
* `hdet_of_components`: the hypothesis `hdet` of `AlgMag/Rooted/ReductivePure.lean`
  for `Y N = J_N` (the ideal of `G^N`), `Φ` the roots, over an algebraically closed field.
-/

suppress_compilation

open Magnetism TauCeti TauCeti.HopfIdeal WithConv

namespace AlgMag.Reductive

/-! ### C3, abstract form -/

section Abstract

variable {G : Type*} [Group G]

/-- **Step C3.** `A = K · N` from irreducibility of `K`, openness of the regular conjugates
(C2) and the centralizer property of regular elements (C1). -/
theorem exists_mul_normalizer_of_irreducible (A K Nm : Subgroup G) [TopologicalSpace K]
    [IrreducibleSpace K] (hKA : K ≤ A) (hnorm : ∀ a ∈ A, ∀ x ∈ K, a * x * a⁻¹ ∈ K)
    (hcont : ∀ a (ha : a ∈ A), Continuous fun x : K =>
      (⟨a * x * a⁻¹, hnorm a ha x x.2⟩ : K))
    (Treg : Set G) (U : Set K) (hUo : IsOpen U) (hUn : U.Nonempty)
    (hU : ∀ x ∈ U, ∃ k ∈ K, ∃ t ∈ Treg, (x : G) = k * t * k⁻¹)
    (hC1 : ∀ y ∈ A, ∀ t ∈ Treg, ∀ t' ∈ Treg, y * t * y⁻¹ = t' → y ∈ Nm) :
    ∀ g ∈ A, ∃ k ∈ K, ∃ n ∈ Nm, g = k * n := by
  intro g hg
  have hgi : g⁻¹ ∈ A := A.inv_mem hg
  set V : Set K := (fun x : K => (⟨g⁻¹ * x * g⁻¹⁻¹, hnorm _ hgi x x.2⟩ : K)) ⁻¹' U
  have hVo : IsOpen V := hUo.preimage (hcont _ hgi)
  have hVn : V.Nonempty := by
    obtain ⟨u, hu⟩ := hUn
    refine ⟨⟨g * u * g⁻¹, hnorm g hg u u.2⟩, ?_⟩
    show (⟨_, _⟩ : K) ∈ U
    convert hu using 1
    ext; simp [mul_assoc]
  obtain ⟨x, hxU, hxV⟩ := nonempty_preirreducible_inter hUo hVo hUn hVn
  obtain ⟨k, hk, t, ht, hx⟩ := hU x hxU
  obtain ⟨k', hk', t', ht', hx'⟩ := hU _ hxV
  simp only [inv_inv] at hx'
  -- `y := k'⁻¹ g⁻¹ k` conjugates `t` to `t'`.
  set y := k'⁻¹ * g⁻¹ * k
  have hy : y ∈ A := A.mul_mem (A.mul_mem (A.inv_mem (hKA hk')) hgi) (hKA hk)
  have hyt : y * t * y⁻¹ = t' := by
    have : t = k⁻¹ * x * k := by rw [hx]; group
    rw [this]
    have h2 : t' = k'⁻¹ * (g⁻¹ * x * g) * k' := by rw [hx']; group
    rw [h2]; simp only [y]; group
  have hyN := hC1 y hy t ht t' ht' hyt
  refine ⟨k * (y⁻¹ * k'⁻¹ * y⁻¹⁻¹), K.mul_mem hk (hnorm _ (A.inv_mem hy) _ (K.inv_mem hk')),
    y⁻¹, Nm.inv_mem hyN, ?_⟩
  simp only [y]; group

end Abstract

/-! ### The decomposition `G^N(k) = ⋃_{w ∈ W_N} K(k) n_w` and `hdet` -/

universe u

variable {k : Type u} {H : Type u} {X : Type u}
variable [Field k] [CommRing H] [HopfAlgebra k H] [CommGroup X] [DecidableEq X]
variable (π : H →ₐc[k] MonoidAlgebra k X)

/-- `K(k) ⊆ G^N(k)`: the ideal of `(G^N)°` contains `J_N`. -/
lemma magnetIdeal_le_compIdeal [IsAlgClosed k] [Algebra.FiniteType k H]
    (N : Magnet (Additive X)) : magnetIdeal (torusGrading π) N ≤ compIdeal π N := by
  intro x hx
  rw [← magnetHopfIdeal_toIdeal] at hx
  show Ideal.Quotient.mk _ (Ideal.Quotient.mk _ x) = 0
  rw [Ideal.Quotient.eq_zero_iff_mem.mpr hx, map_zero]

variable {W : Type*} (ρ : W → X ≃* X)

/-- **Output of C1–C3.** Every `k`-point of `G^N` is `h n` with `h ∈ (G^N)°(k)` and `n`
normalizing `T` through an element of `W`. -/
def ComponentsMeetNormalizer [IsAlgClosed k] [Algebra.FiniteType k H] : Prop :=
  ∀ (N : Magnet (Additive X)) (g : WithConv (H →ₐ[k] k)), g ∈ attractorSubgroup π N k →
    ∃ (h n : WithConv (H →ₐ[k] k)) (w : W), compIdeal π N ≤ RingHom.ker h.ofConv ∧
      Weyl.IsNormalizingWith π k n (ρ w) ∧ g = h * n

variable {π ρ}

/-- **`G^N(k) = ⋃_{w ∈ W_N} K(k) n_w`** (C4 applied to the output of C1–C3). -/
theorem mem_attractor_iff [IsAlgClosed k] [Algebra.FiniteType k H]
    (hπ : Function.Surjective π) (hC : ComponentsMeetNormalizer π ρ)
    (N : Magnet (Additive X)) (g : WithConv (H →ₐ[k] k)) :
    g ∈ attractorSubgroup π N k ↔ ∃ (h n : WithConv (H →ₐ[k] k)) (w : W),
      compIdeal π N ≤ RingHom.ker h.ofConv ∧ Weyl.IsNormalizingWith π k n (ρ w) ∧
      Weyl.weylMagnet (ρ w) ≤ N ∧ g = h * n := by
  have hK : ∀ h : WithConv (H →ₐ[k] k), compIdeal π N ≤ RingHom.ker h.ofConv →
      h ∈ attractorSubgroup π N k := fun h hh =>
    (mem_attractorSubgroup π).2 ((magnetIdeal_le_compIdeal π N).trans hh)
  constructor
  · intro hg
    obtain ⟨h, n, w, hh, hn, rfl⟩ := hC N g hg
    have hnN : n ∈ attractorSubgroup π N k := by
      have := (attractorSubgroup π N k).mul_mem ((attractorSubgroup π N k).inv_mem (hK h hh)) hg
      rwa [inv_mul_cancel_left] at this
    exact ⟨h, n, w, hh, hn, (Weyl.mem_attractorSubgroup_iff_weylMagnet_le π hπ hn N).1 hnN, rfl⟩
  · rintro ⟨h, n, w, hh, hn, hw, rfl⟩
    exact (attractorSubgroup π N k).mul_mem (hK h hh)
      ((Weyl.mem_attractorSubgroup_iff_weylMagnet_le π hπ hn N).2 hw)

/-- The additive form of `σ`, as used by `AlgMag.Rooted` (`act`). -/
def weylAct (ρ : W → X ≃* X) (w : W) : Additive X →+ Additive X :=
  (MulEquiv.toAdditive (ρ w)).toAddMonoidHom

omit [DecidableEq X] in
lemma joinDense_weylMagnet_le_iff (w : W) (N : Magnet (Additive X)) :
    Rooted.weylMagnet (weylAct ρ w) ≤ N ↔ Weyl.weylMagnet (ρ w) ≤ N := by
  rw [Weyl.weylMagnet, AddSubmonoid.closure_le]
  constructor
  · rintro h _ ⟨χ, rfl⟩
    exact h ⟨χ, rfl⟩
  · rintro h _ ⟨χ, rfl⟩
    exact h ⟨χ, rfl⟩

variable [IsAlgClosed k] [Algebra.FiniteType k H] [Algebra.Smooth k H]
  [Module.Finite k (Bialgebra.CotangentSpace k H)]

/-- `G^N(k) ⊆ G^L(k)` when `L ≤ N` have the same roots and the same Weyl part. -/
theorem attractor_points_le (hπ : Function.Surjective π) (hC : ComponentsMeetNormalizer π ρ)
    {N L : Magnet (Additive X)} (hle : L ≤ N) (hR : ∀ a ∈ roots π, a ∈ N → a ∈ L)
    (hW : ∀ w, Weyl.weylMagnet (ρ w) ≤ N → Weyl.weylMagnet (ρ w) ≤ L)
    (g : WithConv (H →ₐ[k] k)) (hg : g ∈ attractorSubgroup π N k) :
    g ∈ attractorSubgroup π L k := by
  obtain ⟨h, n, w, hh, hn, hw, rfl⟩ := (mem_attractor_iff hπ hC N g).1 hg
  have hKL : compIdeal π L = compIdeal π N :=
    compIdeal_eq_of_roots π hle fun a ha => ⟨fun h => hle h, hR a ha⟩
  exact (mem_attractor_iff hπ hC L _).2 ⟨h, n, w, hKL ▸ hh, hn, hW w hw, rfl⟩

/-- **`hdet`** (Theorem `thm:red-attractors` (iii)), in the form required by
`AlgMag/Rooted/ReductivePure.lean`, for `Y N = J_N`, `Φ = roots π`, `act = weylAct ρ`. -/
theorem hdet_of_components (hπ : Function.Surjective π) (hC : ComponentsMeetNormalizer π ρ) :
    ∀ N L : AddSubmonoid (Additive X), L ≤ N → (∀ a ∈ roots π, a ∈ N → a ∈ L) →
      (∀ w, Rooted.weylMagnet (weylAct ρ w) ≤ N → Rooted.weylMagnet (weylAct ρ w) ≤ L) →
      magnetIdeal (torusGrading π) L = magnetIdeal (torusGrading π) N := by
  intro N L hle hR hW
  have hW' : ∀ w, Weyl.weylMagnet (ρ w) ≤ N → Weyl.weylMagnet (ρ w) ≤ L := fun w hw =>
    (joinDense_weylMagnet_le_iff w L).1 (hW w ((joinDense_weylMagnet_le_iff w N).2 hw))
  refine le_antisymm ?_ (magnetIdeal_anti _ hle)
  -- `O(G^N)` is reduced (smooth), so `J_N` is determined by the `k`-points of `G^N`.
  set J := magnetIdeal (torusGrading π) N
  have hS : Algebra.Smooth k (H ⧸ (magnetHopfIdeal π N).toIdeal) :=
    smooth_quotient_magnetHopfIdeal π N
  rw [magnetHopfIdeal_toIdeal] at hS
  have : IsReduced (H ⧸ J) := isReduced_of_smooth k _
  have : Algebra.FiniteType k (H ⧸ J) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ k J) (Ideal.Quotient.mkₐ_surjective k J)
  intro x hx
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  refine OpenCellNotes.eq_zero_of_forall_algHom (K := k) fun φ => ?_
  have hg : toConv (φ.comp (Ideal.Quotient.mkₐ k J)) ∈ attractorSubgroup π N k := by
    rw [mem_attractorSubgroup]
    intro y hy
    rw [RingHom.mem_ker, ofConv_toConv, AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk,
      Ideal.Quotient.eq_zero_iff_mem.mpr hy, map_zero]
  have := (mem_attractorSubgroup π).1 (attractor_points_le hπ hC hle hR hW' _ hg) hx
  rwa [RingHom.mem_ker, ofConv_toConv, AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk] at this

end AlgMag.Reductive
