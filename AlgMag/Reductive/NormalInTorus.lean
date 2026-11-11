/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Reductive.NormalAttractor
import AlgMag.Reductive.SubgroupFullLie
import AlgMag.Reductive.LieTorusZero
import AlgMag.Reductive.OpenCell.LieDimension
import TauCeti.Algebra.AlgebraicGroup.Tangent.FiniteType

/-!
# A smooth connected normal subgroup with Lie algebra in `𝔤_0` lies in `Z_G(T)`

Converse of the reductivity criterion (equivalence.tex Theorem 5.1), the case `Lie U ⊆ 𝔤_0`:
if `U = V(I)` is normal, smooth, with connected coordinate ring, and `Lie U ⊆ 𝔤_0`, then
`U ⊆ G^0 = Z_G(T)`, i.e. `J_⊥ ≤ I`. Proof: `U^T = V(I ⊔ J_⊥)` is smooth
(`smooth_quotient_sup_magnetIdeal_of_isNormal`) with `Lie U^T = Lie U ∩ 𝔤_0 = Lie U`
(`lieSubalgebra_sup`, `rootSpace_zero_eq_lieBot`), so `U^T = U`
(`eq_of_le_of_finrank_cotangent_eq`).
-/

suppress_compilation

open Magnetism TauCeti

namespace AlgMag.Reductive

universe u

variable {k : Type u} {H : Type u} {X : Type u}
variable [Field k] [CommRing H] [HopfAlgebra k H] [CommGroup X] [DecidableEq X]
variable [Algebra.FiniteType k H]
variable (π : H →ₐc[k] MonoidAlgebra k X)

/-- **`Lie U ⊆ 𝔤_0` forces `U ⊆ Z_G(T)`** for a smooth connected normal subgroup `U = V(I)`. -/
theorem magnetHopfIdeal_bot_le_of_lie_le {I : HopfIdeal k H} (hI : I.IsNormal)
    [Algebra.Smooth k (H ⧸ I.toIdeal)] [ConnectedSpace (PrimeSpectrum (H ⧸ I.toIdeal))]
    (hLie : ∀ d ∈ I.lieSubalgebra (B := k), d ∈ rootSpace π 0) :
    magnetHopfIdeal π ⊥ ≤ I := by
  have hsm : Algebra.Smooth k (H ⧸ (I ⊔ magnetHopfIdeal π ⊥).toIdeal) := by
    rw [HopfIdeal.sup_toIdeal, magnetHopfIdeal_toIdeal]
    exact smooth_quotient_sup_magnetIdeal_of_isNormal π hI ⊥
  have hle : (I.lieSubalgebra (B := k)).toSubmodule ≤
      ((magnetHopfIdeal π ⊥).lieSubalgebra (B := k)).toSubmodule := by
    intro d hd
    rw [← rootSpace_zero_eq_lieBot π]
    exact hLie d hd
  have hdim : Module.finrank k
        (Bialgebra.CotangentSpace k (H ⧸ (I ⊔ magnetHopfIdeal π ⊥).toIdeal)) =
      Module.finrank k (Bialgebra.CotangentSpace k (H ⧸ I.toIdeal)) := by
    rw [AlgMag.OpenCellNotes.finrank_quotient_eq_lieSubalgebra,
      AlgMag.OpenCellNotes.finrank_quotient_eq_lieSubalgebra,
      AlgMag.OpenCellNotes.lieSubalgebra_sup, inf_eq_left.2 hle]
  have heq := eq_of_le_of_finrank_cotangent_eq (k := k) (I := I)
    (J := I ⊔ magnetHopfIdeal π ⊥) le_sup_left hdim
  calc magnetHopfIdeal π ⊥ ≤ I ⊔ magnetHopfIdeal π ⊥ := le_sup_right
    _ = I := heq.symm

end AlgMag.Reductive
