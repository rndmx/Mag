/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Weyl.Normalizer

/-!
# The Weyl group as a subgroup of `Aut(X)`

The automorphisms `σ` of the character group `X` realised by a normalizing point of `G(A)`
(`IsNormalizingWith`) form a subgroup `weylGroup π A` of `X ≃* X`: realisers multiply in the
opposite order (`IsNormalizingWith.mul`) and invert (`IsNormalizingWith.inv`).
-/

suppress_compilation

open TensorProduct Magnetism TauCeti WithConv

namespace AlgMag.Weyl

open AlgMag.Reductive

universe u v w

variable {k : Type u} {H : Type v} {X : Type w}
variable [Field k] [CommRing H] [HopfAlgebra k H] [CommGroup X]
variable (π : H →ₐc[k] MonoidAlgebra k X)
variable {A : Type*} [CommRing A] [Algebra k A]

lemma isNormalizingWith_one : IsNormalizingWith π A 1 1 := by
  have h1 : (1 : X ≃* X).toMonoidHom = MonoidHom.id X := rfl
  rw [IsNormalizingWith, map_one, map_one, MulAut.one_apply, h1, twistPoint_id]

lemma IsNormalizingWith.mul {g h : WithConv (H →ₐ[k] A)} {σ τ : X ≃* X}
    (hg : IsNormalizingWith π A g σ) (hh : IsNormalizingWith π A h τ) :
    IsNormalizingWith π A (h * g) (σ * τ) := by
  have h1 : (σ * τ).toMonoidHom = σ.toMonoidHom.comp τ.toMonoidHom := rfl
  rw [IsNormalizingWith, map_mul, map_mul, MulAut.mul_apply, hg, hh.conj_twistPoint π, h1]

lemma IsNormalizingWith.inv {g : WithConv (H →ₐ[k] A)} {σ : X ≃* X}
    (hg : IsNormalizingWith π A g σ) : IsNormalizingWith π A g⁻¹ σ⁻¹ := by
  have hs := hg.conj_twistPoint π (σ⁻¹ : X ≃* X).toMonoidHom
  have h1 : (σ⁻¹ : X ≃* X).toMonoidHom.comp σ.toMonoidHom = MonoidHom.id X := by
    ext x; exact σ.symm_apply_apply x
  rw [h1, twistPoint_id] at hs
  rw [IsNormalizingWith, map_inv, map_inv, ← hs, MulAut.inv_apply_self]

variable (A) in
/-- **The Weyl group** (realised on characters): the automorphisms of `X` induced by the points
of `G(A)` normalizing `T`. -/
def weylGroup : Subgroup (X ≃* X) where
  carrier := {σ | ∃ g, IsNormalizingWith π A g σ}
  one_mem' := ⟨1, isNormalizingWith_one π⟩
  mul_mem' := by
    rintro σ τ ⟨g, hg⟩ ⟨h, hh⟩
    exact ⟨h * g, hg.mul π hh⟩
  inv_mem' := by
    rintro σ ⟨g, hg⟩
    exact ⟨g⁻¹, hg.inv π⟩

lemma mem_weylGroup {σ : X ≃* X} : σ ∈ weylGroup π A ↔ ∃ g, IsNormalizingWith π A g σ :=
  Iff.rfl

end AlgMag.Weyl
