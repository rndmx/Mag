/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib.Tactic.SuppressCompilation
import AlgMag.Affine.GradedHom
import AlgMag.Affine.MagnetAlgebra

/-!
# The attractor `X^N` of a magnet, affine case

Let `R₀` be a commutative ring (`S = Spec R₀`), let `A` be an `M`-graded `R₀`-algebra
(`X = Spec A`, the grading being the action of `𝔸(M)_S`, cf. Mayeux, *Algebraic
Magnetism*, Proposition 2.22), and let `N` be a magnet of `M`.

We define the attractor `X^N` directly by its functor of points,

  `X^N(C) = Hom_{R₀}^{M-graded}(A, C[N])`,

i.e. **without** monoid-scheme or equivariance language. This is legitimate in the
affine setting and is the definition used in the proof of Theorem 3.20.
-/

suppress_compilation

namespace Magnetism

variable {M : Type*} [AddCommMonoid M] [DecidableEq M]
variable {R₀ A : Type*} [CommRing R₀] [CommRing A] [Algebra R₀ A]
variable (𝒜 : M → Submodule R₀ A) (N : Magnet M)
variable (C : Type*) [CommRing C] [Algebra R₀ C]

/-- The attractor `X^N` of the magnet `N`, as a functor of points:
`X^N(C) = Hom_{R₀}^{M-graded}(A, C[N])`. -/
abbrev Attractor : Type _ := GradedAlgHom R₀ 𝒜 (magnetGrading N C)

end Magnetism
