/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Reductive.TorusGrading

/-!
# Attractors of the torus action on a group are closed subgroups

Mayeux, *Algebraic Magnetism*, Semigroup Forum 113 (2026), Theorem 3.20 and §16.5: for the
conjugation action of `D(X)` on `G` and a magnet `N ⊆ M = Additive X`, the attractor
`G^N = Spec (H / J_N)` is a closed subgroup scheme of `G`.

A point `g ∈ G(A)` lies in `G^N(A)` iff its orbit map `t ↦ t g t⁻¹`, a point of `G` with values in
`A ⊗ R[X]`, takes values in the subalgebra `A ⊗ R[N]` (`mem_attractor_iff_orbit_mem`). The orbit
map is a group homomorphism `G(A) → G(A ⊗ R[X])` (conjugation by the universal point of `D(X)`),
and points with values in a subalgebra form a subgroup; hence `G^N(A)` is a subgroup, and
`magnetHopfIdeal π N` is the magnet ideal `J_N` as a Tau Ceti `HopfIdeal`.
-/

suppress_compilation

open TensorProduct Magnetism TauCeti WithConv

namespace AlgMag.Reductive

universe u v w

section SubalgebraPoints

variable {R : Type u} {H : Type v} [CommRing R] [CommRing H] [HopfAlgebra R H]
variable {B : Type*} [CommRing B] [Algebra R B]

/-- The points of `G` with values in a subalgebra `S ⊆ B` form a subgroup of `G(B)`. -/
def subalgebraPoints (S : Subalgebra R B) : Subgroup (WithConv (H →ₐ[R] B)) where
  carrier := {F | ∀ h, F.ofConv h ∈ S}
  one_mem' h := S.algebraMap_mem _
  mul_mem' {F G} hF hG h := by
    change (F * G) h ∈ S
    rw [AlgHom.convMul_apply]
    induction Coalgebra.comul (R := R) h using TensorProduct.induction_on with
    | zero => simp
    | add a b ha hb => rw [map_add]; exact S.add_mem ha hb
    | tmul a b =>
      rw [Algebra.TensorProduct.lift_tmul]
      exact S.mul_mem (hF a) (hG b)
  inv_mem' {F} hF h := hF _

lemma mem_subalgebraPoints {S : Subalgebra R B} {F : WithConv (H →ₐ[R] B)} :
    F ∈ subalgebraPoints S ↔ ∀ h, F.ofConv h ∈ S := Iff.rfl

end SubalgebraPoints

variable {R : Type u} {H : Type v} {X : Type w}
variable [CommRing R] [CommRing H] [HopfAlgebra R H] [CommGroup X]
variable (π : H →ₐc[R] MonoidAlgebra R X)
variable {A : Type*} [CommRing A] [Algebra R A]

section MagnetSubalgebra

variable (A) in
/-- The subalgebra `A ⊗ R[N] ⊆ A ⊗ R[X]` of a magnet `N`. -/
def magnetSubalgebra (N : Magnet (Additive X)) : Subalgebra R (A ⊗[R] MonoidAlgebra R X) :=
  Submodule.toSubalgebra
    (Submodule.span R {b | ∃ a : A, ∃ χ : Additive X, χ ∈ N ∧
      b = a ⊗ₜ[R] MonoidAlgebra.single (Additive.toMul χ) (1 : R)})
    (Submodule.subset_span ⟨1, 0, N.zero_mem, rfl⟩)
    (by
      intro x y hx hy
      induction hx using Submodule.span_induction with
      | zero => simp
      | add a b _ _ ha hb => rw [add_mul]; exact Submodule.add_mem _ ha hb
      | smul r a _ ha => rw [smul_mul_assoc]; exact Submodule.smul_mem _ r ha
      | mem x hx =>
        induction hy using Submodule.span_induction with
        | zero => simp
        | add a b _ _ ha hb => rw [mul_add]; exact Submodule.add_mem _ ha hb
        | smul r a _ ha => rw [mul_smul_comm]; exact Submodule.smul_mem _ r ha
        | mem y hy =>
          obtain ⟨a, χ, hχ, rfl⟩ := hx
          obtain ⟨b, χ', hχ', rfl⟩ := hy
          refine Submodule.subset_span ⟨a * b, χ + χ', N.add_mem hχ hχ', ?_⟩
          rw [Algebra.TensorProduct.tmul_mul_tmul, MonoidAlgebra.single_mul_single, mul_one,
            toMul_add])

lemma tmul_mem_magnetSubalgebra {N : Magnet (Additive X)} (a : A) {χ : Additive X}
    (hχ : χ ∈ N) :
    a ⊗ₜ[R] MonoidAlgebra.single (Additive.toMul χ) (1 : R) ∈ magnetSubalgebra (R := R) A N :=
  Submodule.subset_span ⟨a, χ, hχ, rfl⟩

/-- Elements of `A ⊗ R[N]` have no component outside `N`. -/
lemma tensorComponent_eq_zero_of_mem {N : Magnet (Additive X)} {b : A ⊗[R] MonoidAlgebra R X}
    (hb : b ∈ magnetSubalgebra (R := R) A N) {χ : Additive X} (hχ : χ ∉ N) :
    LinearMap.tensorComponent (Comodule.monoidCoeff R X (Additive.toMul χ)) b = 0 := by
  classical
  change b ∈ Submodule.span R _ at hb
  induction hb using Submodule.span_induction with
  | zero => simp
  | add a b _ _ ha hb => rw [map_add, ha, hb, add_zero]
  | smul r a _ ha => rw [map_smul, ha, smul_zero]
  | mem x hx =>
    obtain ⟨a, χ', hχ', rfl⟩ := hx
    have hne : Additive.toMul χ' ≠ Additive.toMul χ := fun e =>
      hχ (Additive.toMul.injective e ▸ hχ')
    rw [LinearMap.tensorComponent_tmul, Comodule.monoidCoeff_apply,
      MonoidAlgebra.single_apply, if_neg hne, zero_smul]

end MagnetSubalgebra

section Orbit

variable (A) in
/-- The universal point of `D(X)` in `G(A ⊗ R[X])`. -/
def torusPoint : WithConv (H →ₐ[R] A ⊗[R] MonoidAlgebra R X) :=
  toConv ((Algebra.TensorProduct.includeRight).comp π.toAlgHom)

variable (A) in
/-- The orbit map `G(A) → G(A ⊗ R[X])`, `g ↦ t g t⁻¹`, `t` the universal point of `D(X)`. -/
def orbitHom : WithConv (H →ₐ[R] A) →* WithConv (H →ₐ[R] A ⊗[R] MonoidAlgebra R X) :=
  (MulAut.conj (torusPoint π A)).toMonoidHom.comp
    (AlgHom.mapValue (Algebra.TensorProduct.includeLeft))

/-- The orbit map is `g ⊗ id` applied to the torus coaction. -/
theorem orbitHom_apply (g : WithConv (H →ₐ[R] A)) (h : H) :
    (orbitHom π A g).ofConv h =
      Algebra.TensorProduct.map g.ofConv (AlgHom.id R _)
        ((Algebra.TensorProduct.comm R _ _) (torusCoactLeft π h)) := by
  have key := HopfAlgebra.productMap_comp_conjugationAlgHom (R := R) (H := H)
    (torusPoint π A) (AlgHom.mapValue (Algebra.TensorProduct.includeLeft) g)
  have := congrArg (fun F : H →ₐ[R] A ⊗[R] MonoidAlgebra R X => F h) key
  simp only [AlgHom.comp_apply] at this
  rw [orbitHom, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, ← this,
    torusCoactLeft, AlgHom.comp_apply]
  generalize HopfAlgebra.conjugationAlgHom (R := R) (H := H) h = t
  induction t using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => simp only [map_add, ha, hb]
  | tmul a b =>
    simp [torusPoint, AlgHom.mapValue_apply, mul_comm]

variable [DecidableEq X]

/-- **Points of the attractor (Theorem 3.20).** A point `g ∈ G(A)` kills `J_N` iff its orbit map
takes values in `A ⊗ R[N]`. -/
theorem magnetIdeal_le_ker_iff_orbit_mem (N : Magnet (Additive X)) (g : WithConv (H →ₐ[R] A)) :
    magnetIdeal (torusGrading π) N ≤ RingHom.ker g.ofConv ↔
      orbitHom π A g ∈ subalgebraPoints (magnetSubalgebra (R := R) A N) := by
  classical
  rw [mem_subalgebraPoints]
  constructor
  · intro hg h
    rw [← DirectSum.sum_support_decompose (torusGrading π) h, map_sum]
    refine Subalgebra.sum_mem _ fun χ _ => ?_
    have hχ := (DirectSum.decompose (torusGrading π) h χ).2
    rw [mem_torusGrading] at hχ
    rw [orbitHom_apply]
    have hl : (Algebra.TensorProduct.comm R _ _) (torusCoactLeft π
        (DirectSum.decompose (torusGrading π) h χ)) =
        ((DirectSum.decompose (torusGrading π) h χ : H) ⊗ₜ[R]
          MonoidAlgebra.single (Additive.toMul χ) 1) := hχ
    rw [hl, Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
    by_cases hN : χ ∈ N
    · exact tmul_mem_magnetSubalgebra _ hN
    · rw [hg (mem_magnetIdeal_of_notMem hN (DirectSum.decompose (torusGrading π) h χ).2),
        TensorProduct.zero_tmul]
      exact Subalgebra.zero_mem _
  · intro hg
    rw [magnetIdeal, Ideal.span_le]
    simp only [Set.iUnion_subset_iff]
    intro χ hχ a ha
    have hl : (Algebra.TensorProduct.comm R _ _) (torusCoactLeft π a) =
        a ⊗ₜ[R] MonoidAlgebra.single (Additive.toMul χ) 1 := (mem_torusGrading.mp ha)
    have h1 := tensorComponent_eq_zero_of_mem (hg a) hχ
    rw [orbitHom_apply, hl, Algebra.TensorProduct.map_tmul, AlgHom.id_apply,
      LinearMap.tensorComponent_tmul, Comodule.monoidCoeff_apply, MonoidAlgebra.single_apply,
      if_pos rfl, one_smul] at h1
    exact h1

end Orbit

variable [DecidableEq X]

/-- **`G^N(A)` is a subgroup of `G(A)`** (Theorem 3.20 for the conjugation action of `D(X)`). -/
def attractorSubgroup (N : Magnet (Additive X)) (A : Type*) [CommRing A] [Algebra R A] :
    Subgroup (WithConv (H →ₐ[R] A)) :=
  (subalgebraPoints (magnetSubalgebra (R := R) A N)).comap (orbitHom π A)

lemma mem_attractorSubgroup {N : Magnet (Additive X)} {g : WithConv (H →ₐ[R] A)} :
    g ∈ attractorSubgroup π N A ↔ magnetIdeal (torusGrading π) N ≤ RingHom.ker g.ofConv :=
  (magnetIdeal_le_ker_iff_orbit_mem π N g).symm

/-- **The attractor `G^N` as a closed subgroup scheme**: `J_N` as a Tau Ceti `HopfIdeal`. -/
def magnetHopfIdeal (N : Magnet (Additive X)) : HopfIdeal R H :=
  HopfIdeal.ofIdealOfPointsSubgroup (magnetIdeal (torusGrading π) N)
    (fun A => attractorSubgroup π N A) (fun _ _ => mem_attractorSubgroup π)

@[simp] lemma magnetHopfIdeal_toIdeal (N : Magnet (Additive X)) :
    (magnetHopfIdeal π N).toIdeal = magnetIdeal (torusGrading π) N := by
  rw [magnetHopfIdeal, HopfIdeal.ofIdealOfPointsSubgroup_toIdeal]

end AlgMag.Reductive
