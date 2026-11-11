/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Reductive.TangentRoots

/-!
# The Lie algebra of an attractor sees only the roots (F9 blueprint, Lemma 1)

If two magnets `N, N'` contain the same roots, `N ∩ Φ = N' ∩ Φ`, then
`Lie(G^N) = Lie(G^{N'})` (Theorem `thm:red-attractors` (ii), Lie part).
-/

suppress_compilation

open Magnetism TauCeti WithConv
open scoped TensorProduct

namespace AlgMag.Reductive

universe u

variable {k : Type u} {H : Type u} {X : Type u}
variable [Field k] [CommRing H] [HopfAlgebra k H] [CommGroup X] [DecidableEq X]
variable {π : H →ₐc[k] MonoidAlgebra k X}
variable [Module.Finite k (Bialgebra.CotangentSpace k H)]

/-- **Lemma 1.** `Lie(G^N)` depends only on `N ∩ Φ`. -/
theorem lieSubalgebra_magnetHopfIdeal_eq_of_roots {N N' : Magnet (Additive X)}
    (h : ∀ α ∈ roots π, α ∈ N ↔ α ∈ N') :
    (magnetHopfIdeal π N).lieSubalgebra (B := k) =
      (magnetHopfIdeal π N').lieSubalgebra (B := k) := by
  refine lieSubalgebra_magnetHopfIdeal_eq fun χ hχ => ?_
  rcases tangentWeights_subset_insert_roots hχ with h0 | hr
  · subst h0; exact ⟨fun _ => N'.zero_mem, fun _ => N.zero_mem⟩
  · exact h χ hr

end AlgMag.Reductive
