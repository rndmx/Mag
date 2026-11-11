/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
Adapted from Tau Ceti (github.com/TauCetiProject/TauCeti, commit 7ca783d4); see TauCeti/CHANGES.md
-/
import TauCeti.Compat.All
import TauCeti.Algebra.AlgebraicGroup.Representation.UnipotentPoint.Basic

/-!
# Backport: declarations added upstream to `Representation/UnipotentPoint/Basic.lean`

Tau Ceti 7ca783d4 adds the theorem below to `Representation/UnipotentPoint/Basic.lean`. The local
adapted copy of that file (from d2083f0) is kept unchanged, so that its dependents are not
rebuilt; the new declaration lives here, verbatim, in the same namespace.
-/

section

open LinearMap WithConv

namespace TauCeti

namespace HopfAlgebra

universe u v w x

variable {k : Type u} {H : Type v} {K : Type x}
variable [CommSemiring k] [Semiring H] [_root_.HopfAlgebra k H] [CommRing K] [Algebra k K]

/-- A unipotent point acts on every finitely generated comodule through an endomorphism `ρ x`
with `ρ x - 1` nilpotent. -/
theorem IsUnipotentPoint.isNilpotent_pointsRepresentation_sub_one {x : WithConv (H →ₐ[k] K)}
    (hx : IsUnipotentPoint x) (M : FGComoduleCat.{u, v, u} k H) :
    _root_.IsNilpotent (Comodule.pointsRepresentation (R := k) (H := H) (A := K) M x - 1) := by
  rw [Comodule.pointsRepresentation_apply]
  exact (isUnipotentPoint_iff_forall_isNilpotent_endOfPoint_sub_one x).mp hx M

end HopfAlgebra

end TauCeti
