/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Reductive.Step2BaseChangeCore
import AlgMag.Reductive.TorusSpecialization

/-!
# `Step2OverFpBar` is proved

`step2OverFpBar : Step2OverFpBar k Q` for every finite-type Hopf algebra `Q` over `k = k̄`
(no connectedness needed; the integrality and semisimplicity hypotheses of `Step2OverFpBar`
are not used). Proof: `K = (k(X))‾`, `NoNontrivialTorus K (K ⊗ Q)`
(`TorusSpecialization.noNontrivialTorus_baseChange`), then
`Step2BaseChange.charpolyValuesFinite_of_noNontrivialTorus_closure` (Step2BaseChangeCore.lean).
-/

open Polynomial TauCeti
open scoped TensorProduct

namespace AlgMag.Reductive.Step2BaseChange

open AlgMag.Reductive.NoTorusUnipotent AlgMag.Reductive.CharpolyFinite

universe u

/-- **Step 2 for every `Q`**: no nontrivial torus implies the charpoly coefficients take
finitely many values at `k`-points. -/
theorem charpolyValuesFinite_of_noNontrivialTorus {k Q : Type u} [Field k] [IsAlgClosed k]
    [CommRing Q] [HopfAlgebra k Q] [Algebra.FiniteType k Q] (htor : NoNontrivialTorus k Q) :
    CharpolyValuesFinite k Q :=
  charpolyValuesFinite_of_noNontrivialTorus_closure
    (TorusSpecialization.noNontrivialTorus_baseChange htor)

/-- **`Step2OverFpBar` holds for every `Q`.** -/
theorem step2OverFpBar {k Q : Type u} [Field k] [IsAlgClosed k] [CommRing Q] [HopfAlgebra k Q]
    [Algebra.FiniteType k Q] : Step2OverFpBar k Q :=
  fun _ htor _ ↦ charpolyValuesFinite_of_noNontrivialTorus htor

end AlgMag.Reductive.Step2BaseChange

#print axioms AlgMag.Reductive.Step2BaseChange.step2OverFpBar
