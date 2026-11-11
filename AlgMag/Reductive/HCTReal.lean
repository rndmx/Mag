/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Reductive.AttractorSubgroup
import TauCeti.Algebra.AlgebraicGroup.Reductive.Solvable
import TauCeti.Algebra.AlgebraicGroup.Reductive.AlgebraicallyClosed
import TauCeti.Algebra.AlgebraicGroup.Torus.Maximal
import TauCeti.Algebra.HopfAlgebra.HopfIdeal.Kernel

/-!
# `hCT`: `C_u = 1 ⇒ C = T`

`C = V(magnetHopfIdeal π ⊥)` (= `Z_G(T)`), `T = V(ker π)`. If `C` is smooth, connected,
geometrically solvable and its unipotent radical is trivial, then `C` is reductive and
solvable, hence a torus (Tau Ceti `torus_of_geometricallySolvable`); maximality of `T` gives
`C = T`.  The conclusion is exactly the `hCT` hypothesis of `OpenCellGen`.
-/

open Magnetism TauCeti

namespace AlgMag.Reductive.HCTReal

universe u

variable {k : Type u} {H : Type u} {X : Type u}
variable [Field k] [CommRing H] [HopfAlgebra k H] [CommGroup X] [DecidableEq X]
variable (π : H →ₐc[k] MonoidAlgebra k X)

/-- **`hCT`** with the exact signature used in `OpenCellGen`. Inputs: `C := magnetHopfIdeal π ⊥`
smooth, connected, solvable (`hsolv`: `C ⊆ P(ν)` Borel); `hRuC`: `Cu` is the pullback of
`R_u(C)` (so `Cu = 1 ⇒ R_u(C) = 1`); `T = V(ker π)` maximal torus contained in `C`. -/
theorem hCT [IsAlgClosed k] [Algebra.FiniteType k H] (hπ : Function.Surjective π)
    (Cu : HopfIdeal k H)
    (hsm : Algebra.Smooth k (FiniteTypeCommHopfAlgCat.quotient
      (FiniteTypeCommHopfAlgCat.of k H) (magnetHopfIdeal π ⊥)))
    (hconn : geometricallyConnectedCommHopfAlgProperty k (FiniteTypeCommHopfAlgCat.quotient
      (FiniteTypeCommHopfAlgCat.of k H) (magnetHopfIdeal π ⊥)).obj)
    (hsolv : geometricallySolvablePointsCommHopfAlgProperty k (FiniteTypeCommHopfAlgCat.quotient
      (FiniteTypeCommHopfAlgCat.of k H) (magnetHopfIdeal π ⊥)).obj)
    (hRuC : Cu = HopfIdeal.augmentation k H →
      FiniteTypeCommHopfAlgCat.unipotentRadicalDefiningIdeal (FiniteTypeCommHopfAlgCat.quotient
        (FiniteTypeCommHopfAlgCat.of k H) (magnetHopfIdeal π ⊥)) = HopfIdeal.augmentation k _)
    (hTmax : HopfIdeal.IsMaximalTorus k (CommHopfAlgCat.of k H) (HopfIdeal.kerOfSurjective π hπ))
    (hTC : magnetHopfIdeal π ⊥ ≤ HopfIdeal.kerOfSurjective π hπ) :
    Cu = HopfIdeal.augmentation k H →
      magnetHopfIdeal π ⊥ = HopfIdeal.kerOfSurjective π hπ := by
  intro hCu
  have hred : reductiveCommHopfAlgProperty k (FiniteTypeCommHopfAlgCat.quotient
      (FiniteTypeCommHopfAlgCat.of k H) (magnetHopfIdeal π ⊥)) :=
    (reductiveCommHopfAlgProperty_iff_unipotentRadicalDefiningIdeal_eq_augmentation k _).2
      ⟨hsm, hconn, hRuC hCu⟩
  have htor := hred.torus_of_geometricallySolvable hsolv
  exact le_antisymm hTC (hTmax.2 htor hTC)

end AlgMag.Reductive.HCTReal
