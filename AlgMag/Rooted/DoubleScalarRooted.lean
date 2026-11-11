/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.DoubleScalar
import AlgMag.Rooted.RootedBasic

/-!
# Weighted `Pⁿ`, and `P²` under `D(ℤ²)`: rooted actions

Repackages `AlgMag.DoubleScalar.pureMagnets_bijOn`, `isPure_iff`, `isPure_closure` (any weights) and
`prop41` (Proposition 4.1) as: the action is rooted by `Om w` (resp. `Φ`), in the element sense of
Lemma `lem:elements`.
-/

namespace AlgMag.DoubleScalar

open AlgMag.Rooted

variable {ι : Type} [Fintype ι] [DecidableEq ι] {R : Type} [CommRing R]
variable {M : Type} [AddCommGroup M] (w : ι → M)

/-- The weighted `Pⁿ` action is rooted by the weight differences `Om w`. -/
theorem pn_joinDense [Nontrivial R] :
    IsJoinDense (IsPure (attractorImage (pnAction R w))) (mono '' Om w) := by
  rw [isJoinDense_mono_iff]
  exact ⟨fun N hN => (pureMagnets_bijOn (R := R) w).mapsTo hN,
    fun N hN => ((isPure_iff w).1 hN).symm, fun E hE => isPure_closure w hE⟩

/-- **Proposition 4.1, rooted form.** `D(ℤ²)` acting on `P²` is rooted by
`Φ = {(1,0), (0,1), (1,-1), (0,-1), (-1,1), (-1,0)}`. -/
theorem dsAct_joinDense [Nontrivial R] :
    IsJoinDense (IsPure (attractorImage (dsAct R))) (mono '' (Phi : Set (ℤ × ℤ))) := by
  rw [← om_eq]
  exact pn_joinDense (R := R) wP

end AlgMag.DoubleScalar
