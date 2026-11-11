/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Reductive.NormalLieRoots
import AlgMag.Reductive.GradedQuotient

/-!
# Attractors of a smooth normal subgroup are smooth

For a normal closed subgroup `U = V(I)` of `G` (Tau Ceti `HopfIdeal.IsNormal`) and the torus
`T = D(X) → G`, the ideal `I` is homogeneous for the torus grading, so for every magnet `N` the
attractor `U^N = U ∩ G^N = V(I ⊔ J_N)` is smooth when `U` is. Examples: `N = ⊥` gives `U^T`,
`N = ℤα` gives `U ∩ G_α = Z_U(S_α)` (fact (F1) of equivalence.tex for normal `U`).
-/

suppress_compilation

open Magnetism TauCeti

namespace AlgMag.Reductive

universe u

variable {k : Type u} {H : Type u} {X : Type u}
variable [Field k] [CommRing H] [HopfAlgebra k H] [CommGroup X] [DecidableEq X]
variable (π : H →ₐc[k] MonoidAlgebra k X)

/-- **A normal Hopf ideal is a homogeneous ideal for the torus grading.** -/
theorem isHomogeneous_of_isNormal {I : HopfIdeal k H} (hI : I.IsNormal) :
    I.toIdeal.IsHomogeneous (torusGrading π) :=
  fun i _ hr => mem_of_normal_of_coeff π hI hr i

/-- **Attractors of a smooth normal subgroup are smooth**: `U^N = V(I ⊔ J_N)`. -/
theorem smooth_quotient_sup_magnetIdeal_of_isNormal {I : HopfIdeal k H} (hI : I.IsNormal)
    [Algebra.Smooth k (H ⧸ I.toIdeal)] (N : Magnet (Additive X)) :
    Algebra.Smooth k (H ⧸ (I.toIdeal ⊔ magnetIdeal (torusGrading π) N)) :=
  AlgMag.smooth_quotient_sup_magnetIdeal (torusGrading π) (isHomogeneous_of_isNormal π hI) N

end AlgMag.Reductive
