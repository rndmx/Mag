/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Reductive.RootGroupGaLie
import AlgMag.Reductive.GluePrereqs

/-!
# `𝔤_0 = Lie G^0 = Lie T`

* `rootSpace_zero_eq_lieBot`: the zero weight space of `Lie G` is `Lie G^0`.
* `rootSpace_zero_le_lieMagnet`: `𝔤_0 ⊆ Lie G^N` for every magnet `N`.
* `rootSpace_zero_eq_lieTorus`: for split reductive data, `𝔤_0 = Lie T`, the derivations
  vanishing on `ker π`.
-/

open Magnetism TauCeti WithConv

namespace AlgMag.Reductive

universe u

variable {k : Type u} {H : Type u} {X : Type u}
variable [Field k] [CommRing H] [HopfAlgebra k H] [CommGroup X] [DecidableEq X]
variable (π : H →ₐc[k] MonoidAlgebra k X)

/-- **`𝔤_0 = Lie G^0`.** -/
theorem rootSpace_zero_eq_lieBot :
    rootSpace π 0 = ((magnetHopfIdeal π ⊥).lieSubalgebra (B := k)).toSubmodule := by
  ext d
  change (∀ χ ≠ 0, ∀ h ∈ torusGrading π χ, d h = 0) ↔
    d ∈ (magnetHopfIdeal π ⊥).lieSubalgebra (B := k)
  rw [mem_lieSubalgebra_magnetHopfIdeal_iff]
  simp only [AddSubmonoid.mem_bot]

/-- **`𝔤_0 ⊆ Lie G^N`.** -/
theorem rootSpace_zero_le_lieMagnet (N : Magnet (Additive X)) :
    rootSpace π 0 ≤ ((magnetHopfIdeal π N).lieSubalgebra (B := k)).toSubmodule := by
  intro d hd
  change d ∈ (magnetHopfIdeal π N).lieSubalgebra (B := k)
  rw [mem_lieSubalgebra_magnetHopfIdeal_iff]
  intro χ hχ h hh
  exact hd χ (fun h0 => hχ (h0 ▸ N.zero_mem)) h hh

/-- **`𝔤_0 = Lie T`** for split reductive data (`G^0 = T`). -/
theorem rootSpace_zero_eq_lieTorus [Module.Finite k (Bialgebra.CotangentSpace k H)]
    [IsAlgClosed k] [Algebra.FiniteType k H] [Algebra.Smooth k H] (D : SplitReductiveData π)
    (d : Derivation k H (Bialgebra.CounitAlgebra k H k)) :
    d ∈ rootSpace π 0 ↔ ∀ x ∈ RingHom.ker π.toAlgHom, d x = 0 := by
  rw [rootSpace_zero_eq_lieBot]
  change d ∈ (magnetHopfIdeal π ⊥).lieSubalgebra (B := k) ↔ _
  rw [HopfIdeal.mem_lieSubalgebra_iff, magnetHopfIdeal_toIdeal, magnetIdeal_bot_eq_ker π D]

end AlgMag.Reductive
