/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import TauCeti.Algebra.AlgebraicGroup.Tangent.KrullDimension
import TauCeti.Algebra.AlgebraicGroup.Tangent.Regularity

/-!
# Smooth affine groups: `dim 𝒪_{U,1} = dim Lie U`

Kept apart from `SmoothKrullDim.lean`: these Tau Ceti files cannot currently be imported together
with `ParabolicGenRay` (duplicate `topologicalKrullDimAt*` declarations in
`TauCeti.Topology.KrullDimension.Local` and `StacksFrontier.Topology.Dimension.Krull`).
-/

suppress_compilation

open AlgebraicGeometry CategoryTheory TauCeti

namespace AlgMag.Reductive

universe u
section Core

variable {k U : Type u} [Field k] [CommRing U] [HopfAlgebra k U]
  [IsAlgClosed k] [Algebra.FiniteType k U] [Algebra.Smooth k U]

/-- **Smooth ⇒ `dim 𝒪_{U,1} = dim Lie U`.** -/
theorem ringKrullDim_augmentationStalk_eq_finrank_lie :
    ringKrullDim ((Spec (CommRingCat.of U)).presheaf.stalk (Bialgebra.augmentationPoint k U)) =
      (Module.finrank k (Derivation k U (Bialgebra.CounitAlgebra k U k)) : WithBot ℕ∞) := by
  rw [TauCeti.HopfAlgebra.ringKrullDim_augmentationStalk (k := k),
    (TauCeti.HopfAlgebra.smooth_iff_finrank_lie_eq_ringKrullDim (k := k) (H := U)).1 ‹_›]

/-- **Smooth and `dim Lie U ≥ 2` ⇒ `dim 𝒪_{U,1} ≥ 2`.** -/
theorem not_krullDimLE_one_of_two_le_finrank_lie
    (h : 2 ≤ Module.finrank k (Derivation k U (Bialgebra.CounitAlgebra k U k))) :
    ¬ Ring.KrullDimLE 1
      ((Spec (CommRingCat.of U)).presheaf.stalk (Bialgebra.augmentationPoint k U)) := by
  rw [Ring.krullDimLE_iff, ringKrullDim_augmentationStalk_eq_finrank_lie (k := k)]
  intro hle
  have : Module.finrank k (Derivation k U (Bialgebra.CounitAlgebra k U k)) ≤ 1 := by
    exact_mod_cast hle
  omega

end Core

end AlgMag.Reductive
