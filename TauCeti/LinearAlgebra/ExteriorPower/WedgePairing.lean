/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/

import TauCeti.Compat.All
import TauCeti.Compat.LinearAlgebra.ExteriorPower.WedgePairing
import TauCeti.LinearAlgebra.ExteriorPower.Basis
-- Private: the exterior algebra basis is used only inside the proof of
-- `Set.powersetCard.sign_mul_sign_compl`.
import Mathlib.LinearAlgebra.ExteriorAlgebra.Basis

/-!
# Evaluation formulas for wedge products and pairings

Inside the exterior algebra, the wedge product of exterior powers is the algebra product, and the
wedge product of pure exterior products concatenates their vector families. Pairing
`g₀ ∧ ⋯ ∧ gₙ` with `θ ∧ v` expands along the last vector `v` (`pairingDual_ιMulti_wedge`). A
trivialisation in a specified top degree gives the wedge pairing by composing the wedge product
with that trivialisation; the degree transports disappear after identifying the degree with the
finrank, and a wedge pairing is the trivialisation of the exterior-algebra product of its arguments.
On the exterior-power bases induced by a basis `b`, the wedge pairing of `e_s` and `e_t` is the
shuffle sign of `s` times the volume of `b` when `s` and `t` are disjoint, and zero otherwise.
The top exterior product `Module.Basis.topVector` of a basis indexed by `Fin n` is the wedge of
the basis vectors, and the shuffle signs of a set of `k` indices and of its complement of `l`
indices multiply to `(-1) ^ (k * l)`. Composing a complementary-degree wedge pairing,
trivialised by a linear map on the top exterior power, with the exterior powers of an endomorphism
scales it by the determinant of that endomorphism.
-/

section

namespace exteriorPower

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] {k l : ℕ}

/-- Inside the exterior algebra, the wedge product of exterior powers is the algebra product. -/
@[simp]
theorem coe_wedge (x : ⋀[R]^k M) (y : ⋀[R]^l M) :
    (wedge R M k l x y : ExteriorAlgebra R M) = x * y :=
  rfl

/-- The wedge product of pure exterior products concatenates their vector families. -/
@[simp 1100]
theorem wedge_ιMulti (u : Fin k → M) (v : Fin l → M) :
    wedge R M k l (ιMulti R k u) (ιMulti R l v) = ιMulti R (k + l) (Fin.append u v) := by
  apply Subtype.ext
  simp only [coe_wedge, ιMulti_apply_coe, ExteriorAlgebra.ιMulti_mul_ιMulti]

/-- **Laplace expansion along the last vector**: the pairing of `g₀ ∧ ⋯ ∧ gₙ` with `θ ∧ v` is
`∑ⱼ (-1) ^ (n + j) gⱼ(v) ⟨g₀ ∧ ⋯ ∧ ĝⱼ ∧ ⋯ ∧ gₙ, θ⟩`. -/
theorem pairingDual_ιMulti_wedge {n : ℕ} (g : Fin (n + 1) → Module.Dual R M) (θ : ⋀[R]^n M)
    (v : M) :
    pairingDual R M (n + 1) (ιMulti R (n + 1) g) (wedge R M n 1 θ ((oneEquiv R M).symm v)) =
      ∑ j : Fin (n + 1), (-1) ^ (n + j : ℕ) * g j v *
        pairingDual R M n (ιMulti R n (g ∘ j.succAbove)) θ := by
  have hθ : θ ∈ Submodule.span R (Set.range (ιMulti R n)) := by
    rw [ιMulti_span]
    trivial
  induction hθ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨u, rfl⟩ := hx
    rw [oneEquiv_symm_apply, wedge_ιMulti, Fin.append_right_eq_snoc, pairingDual_ιMulti_ιMulti,
      Matrix.det_succ_row _ (Fin.last n)]
    simp [Fin.succAbove_last, Matrix.submatrix, Function.comp_def]
  | zero => simp
  | add x y _ _ hx hy =>
    rw [map_add, LinearMap.add_apply, map_add, hx, hy]
    simp [mul_add, Finset.sum_add_distrib]
  | smul a x _ hx =>
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, hx, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ ↦ by ring

/-- The wedge product commutes with applying a linear map to both factors. -/
theorem wedge_map {N : Type*} [AddCommGroup N] [Module R N] (f : M →ₗ[R] N) :
    (wedge R N k l).compl₁₂ (exteriorPower.map k f) (exteriorPower.map l f) =
      (wedge R M k l).compr₂ (exteriorPower.map (k + l) f) := by
  apply LinearMap.ext
  intro x
  apply LinearMap.ext
  intro y
  apply Subtype.ext
  simp only [LinearMap.compl₁₂_apply, LinearMap.compr₂_apply, coe_wedge,
    exteriorPower.coe_map, map_mul]

/-- Pointwise form of `wedge_map` for rewriting evaluations of wedge products. -/
theorem wedge_map_apply {N : Type*} [AddCommGroup N] [Module R N] (f : M →ₗ[R] N)
    (x : ⋀[R]^k M) (y : ⋀[R]^l M) :
    wedge R N k l (exteriorPower.map k f x) (exteriorPower.map l f y) =
      exteriorPower.map (k + l) f (wedge R M k l x y) :=
  LinearMap.congr_fun₂ (wedge_map f) x y

/-- A wedge pairing transported from a specified top degree is the wedge product followed by
the trivialisation in that degree. -/
theorem wedgePairing_eq_compr₂_of_finrank_eq (n : ℕ) (hfin : Module.finrank R M = n)
    (hdeg : k + l = n) (vol : (⋀[R]^n M) ≃ₗ[R] R) :
    wedgePairing
        ((LinearEquiv.ofEq (⋀[R]^(Module.finrank R M) M) (⋀[R]^n M)
          (congrArg (fun d ↦ ⋀[R]^d M) hfin)).trans vol) (hdeg.trans hfin.symm) =
      (wedge R M k l).compr₂ (hdeg ▸ vol) := by
  subst n
  rfl

/-- The wedge pairing of `x` and `y` is `vol` of their product in the exterior algebra, read as an
element `z` of the top exterior power. This removes the degree transport `k + l = finrank R M`
built into `exteriorPower.wedgePairing`, so pairings with different splittings of the top degree
can be compared through the exterior algebra. -/
theorem wedgePairing_apply_eq_of_coe_mul_eq (vol : ⋀[R]^(Module.finrank R M) M ≃ₗ[R] R)
    (hkl : k + l = Module.finrank R M) (x : ⋀[R]^k M) (y : ⋀[R]^l M)
    (z : ⋀[R]^(Module.finrank R M) M) (h : (x : ExteriorAlgebra R M) * y = z) :
    wedgePairing vol hkl x y = vol z := by
  -- Evaluating a degree-transported functional only depends on the exterior-algebra element.
  have key : ∀ {d e : ℕ} (hde : e = d) (f : ⋀[R]^e M →ₗ[R] R) (w : ⋀[R]^d M) (w' : ⋀[R]^e M),
      (w : ExteriorAlgebra R M) = w' →
        (Eq.rec (motive := fun d _ ↦ ⋀[R]^d M →ₗ[R] R) f hde) w = f w' := by
    rintro d e rfl f w w' hw
    exact congrArg f (Subtype.ext hw)
  exact key _ _ _ _ (by simpa using h)

/-- For a free module of finrank `n = k + l` and any linear functional `vol` on `⋀^n M`,
precomposing `wedge` followed by `vol` with the exterior powers of an endomorphism `f` scales it
by `det f`. -/
theorem
    wedge_compr₂_compl₁₂_exteriorPower_map_eq_det_smul [Module.Free R M]
    (hn : Module.finrank R M = n) (hkl : k + l = n) (vol : ⋀[R]^n M →ₗ[R] R)
    (f : M →ₗ[R] M) :
    LinearMap.compl₁₂ ((wedge R M k l).compr₂ (hkl ▸ vol))
      (exteriorPower.map k f) (exteriorPower.map l f) =
      LinearMap.det f • ((wedge R M k l).compr₂ (hkl ▸ vol)) := by
  apply LinearMap.ext
  intro x
  apply LinearMap.ext
  intro y
  simp only [LinearMap.compl₁₂_apply, LinearMap.smul_apply, LinearMap.compr₂_apply]
  rw [wedge_map_apply]
  subst n
  have htop := LinearMap.map_exteriorPower_finrank_eq_det_smul f
  rw [← hkl] at htop
  rw [htop]
  simp only [LinearMap.smul_apply, map_smul, LinearMap.id_apply, smul_eq_mul]

-- [flag agent backport] wedgePairing_exteriorPower_apply, Module.Basis.topVector_eq_iMulti and
-- Set.powersetCard.sign_mul_sign_compl dropped: they need Mathlib 1b1ccf4 topVector and
-- powersetCard.sign, absent from 16edf57; not used downstream of Decomposable.

end exteriorPower
