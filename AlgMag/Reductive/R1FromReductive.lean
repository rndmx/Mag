/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Reductive.RankOneReflectionAlt

/-!
# Towards (R1) for reductive groups

`R1Property π`: for every root `α`, `N_{G^{ℤα}}(T)(k) ⊄ T(k)`, i.e. some `n ∈ G^{ℤα}(k)`
normalizes `T` with automorphism `σ ≠ 1`.

* `r1Property_iff_weyl`: (R1) iff for every root `α` some `w ≠ 1` in `W` has `(1 - w)X ⊆ ℤα`.
* `R1Property.isReflectionOn`: under (R1) each root has a normalizing reflection at `α`.
* `R1Property.neg_mem_roots`: (R1) forces `-α` to be a root (`W` preserves the roots).
* `R1Property.withReflections`: (R1) gives `SplitReductiveData.WithReflections`.

The input from reductivity (`reductiveCommHopfAlgProperty`) is not yet connected:
see the module docstring of `RankOneReflectionAlt` for counterexamples without it.
-/

suppress_compilation

open TensorProduct Magnetism TauCeti WithConv

namespace AlgMag.Reductive

open AlgMag.Weyl LatticeReflection

universe u

variable {k : Type u} {H : Type u} {X : Type u}
variable [Field k] [CommRing H] [HopfAlgebra k H] [CommGroup X] [DecidableEq X]
variable {π : H →ₐc[k] MonoidAlgebra k X}
variable [Module.Finite k (Bialgebra.CotangentSpace k H)]
variable [Module.IsTorsionFree ℤ (Additive X)]

variable (π) in
/-- **(R1)**: `N_{G^{ℤα}}(T)(k) ⊄ T(k)` for every root `α`. -/
def R1Property : Prop :=
  ∀ α ∈ roots π, ∃ (n : WithConv (H →ₐ[k] k)) (σ : X ≃* X), IsNormalizingWith π k n σ ∧
    n ∈ attractorSubgroup π (lineMagnet α) k ∧ σ ≠ 1

/-- (R1) in Weyl-group terms. -/
theorem r1Property_iff_weyl (D : SplitReductiveData π) :
    R1Property π ↔
      ∀ α ∈ roots π, ∃ w ∈ D.W, w ≠ 1 ∧ ∀ x, x - actW w x ∈ AddSubgroup.zmultiples α :=
  forall₂_congr fun _ hα => (exists_reflection_iff_lineAttractor D hα).out 2 3

/-- (R1) gives, for each root, a `k`-point of `N_G(T)` acting by a reflection at `α`. -/
theorem R1Property.isReflectionOn (D : SplitReductiveData π) (h : R1Property π)
    {α : Additive X} (hα : α ∈ roots π) :
    ∃ (n : WithConv (H →ₐ[k] k)) (σ : X ≃* X), IsNormalizingWith π k n σ ∧
      ¬ RingHom.ker π.toAlgHom ≤ RingHom.ker n.ofConv ∧ IsReflectionOn σ α := by
  obtain ⟨n, σ, hn, hnα, hσ⟩ := h α hα
  exact exists_normalizing_reflection_of_lineAttractor D hα hn hnα hσ

/-- **(R1) forces `-α` to be a root.** -/
theorem R1Property.neg_mem_roots (D : SplitReductiveData π) (h : R1Property π)
    {α : Additive X} (hα : α ∈ roots π) : -α ∈ roots π := by
  obtain ⟨n, σ, hn, -, hrefl⟩ := h.isReflectionOn D hα
  have hW := mem_W_of_isNormalizingWith π D hn
  have := D.roots_stable σ hW α hα
  rw [← hrefl.1]
  exact this

/-- **`WithReflections` from (R1).** -/
def R1Property.withReflections (D : SplitReductiveData π) (h : R1Property π) :
    SplitReductiveData.WithReflections π :=
  SplitReductiveData.WithReflections.ofLineAttractor D h

end AlgMag.Reductive

