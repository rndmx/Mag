/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.

Compiled; no sorry.
-/
import AlgMag.Reductive.OpenCellField
import AlgMag.Reductive.OpenCell.EtaleCriterion
import AlgMag.Reductive.OpenCell.HopfKaehler
import AlgMag.Reductive.OpenCell.CotangentTensor
import AlgMag.Reductive.OpenCell.LieDimension
import AlgMag.Reductive.OpenCell.IrreducibleOfConnected
import TauCeti.Algebra.AlgebraicGroup.Dynamic.Smooth

/-!
# The open cell is étale, hence flat (CGP 2.1.8 (3)); removal of both inputs of
`magnetIdeal_eq_parabolic_of_field_of_openCell`

`k` any field, `H` smooth of finite type, `l` any cocharacter, `T = O(U(-λ)) ⊗ O(Z(λ)) ⊗ O(U(λ))`
viewed as an `H`-algebra through `openCellRingHom l`.

1. `T` is formally unramified over `H`: the open cell map is a ring epimorphism
   (`epi_openCellRingHom`), so two `H`-algebra maps out of `T` agree. Hence `Ω[T⁄H] = 0` and
   `T ⊗[H] Ω[H⁄k] → Ω[T⁄k]` is surjective.
2. Both sides are free `T`-modules: `Ω[H⁄k] ≅ H ⊗ ω_G` and `Ω[T⁄k] ≅ T ⊗ ω_T`
   (`kaehlerEquivInv`; `T` is a Hopf algebra, the coordinate ring of `U(-λ) × Z(λ) × U(λ)`).
   Ranks: `dim ω_T = dim ω_{U⁻} + dim ω_Z + dim ω_U` (`finrank_cotangentSpace_tensorProduct`)
   `= dim ω_G` (`finrank_openCell_cotangent`). A surjection of free modules of equal rank is
   bijective.
3. `T` is formally smooth over `k` (the three factors are; Tau Ceti `Dynamic/Smooth`), so the
   Jacobi–Zariski sequence makes `T` formally étale over `H`
   (`formallyEtale_of_mapBaseChange_bijective`); with finite presentation
   (`finitePresentation_openCellRingHom`) it is étale, hence flat.

No algebraic closedness is needed for flatness.
-/

suppress_compilation

open CategoryTheory AlgebraicGeometry Magnetism TauCeti TauCeti.Cocharacter AlgMag.OpenCellNotes
open scoped TensorProduct

namespace AlgMag.Reductive

universe u

variable {k : Type u} {H : Type u} [Field k] [CommRing H] [HopfAlgebra k H]
variable (l : H →ₐc[k] LaurentPolynomial k)

/-- The open cell ring, as a type synonym carrying the `H`-algebra structure of the open cell
map (the tensor product already carries an unrelated `H`-algebra structure through its first
factor). -/
def OCRing : Type u := OpenCellRing l

instance : CommRing (OCRing l) := inferInstanceAs (CommRing (OpenCellRing l))

instance : HopfAlgebra k (OCRing l) := inferInstanceAs (HopfAlgebra k (OpenCellRing l))

/-- `T` as an `H`-algebra through the open cell map. -/
instance : Algebra H (OCRing l) := RingHom.toAlgebra (S := OCRing l) (openCellRingHom l)

lemma algebraMap_oCRing (x : H) : algebraMap H (OCRing l) x = openCellMap l x := rfl

instance : IsScalarTower k H (OCRing l) :=
  IsScalarTower.of_algebraMap_eq fun r => ((openCellMap l).commutes r).symm

/-- **Step 1.** The open cell ring is formally unramified over `O(G)`. -/
theorem formallyUnramified_openCell : Algebra.FormallyUnramified H (OCRing l) := by
  rw [Algebra.FormallyUnramified.iff_comp_injective]
  intro B _ _ I _ f g _
  have he := epi_openCellRingHom l
  have hfg : CommRingCat.ofHom (R := H) (S := OpenCellRing l) (openCellRingHom l) ≫
        CommRingCat.ofHom (R := OpenCellRing l) (S := B) f.toRingHom =
      CommRingCat.ofHom (R := H) (S := OpenCellRing l) (openCellRingHom l) ≫
        CommRingCat.ofHom (R := OpenCellRing l) (S := B) g.toRingHom := by
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro x
    change f (algebraMap H (OCRing l) x) = g (algebraMap H (OCRing l) x)
    rw [f.commutes, g.commutes]
  have h2 := he.left_cancellation _ _ hfg
  exact AlgHom.ext fun x => RingHom.congr_fun (congrArg CommRingCat.Hom.hom h2) x

/-- `T ⊗[H] Ω[H⁄k] → Ω[T⁄k]` is surjective. -/
theorem mapBaseChange_openCell_surjective :
    Function.Surjective (KaehlerDifferential.mapBaseChange k H (OCRing l)) := by
  have := formallyUnramified_openCell l
  exact mapBaseChange_surjective_of_subsingleton

/-- The open cell ring is nonzero. -/
instance nontrivial_oCRing : Nontrivial (OCRing l) := by
  have : Nontrivial (H ⧸ l.oppositeCocharacter.unipotentDefiningHopfIdeal.toIdeal) :=
    Bialgebra.nontrivial k
  have : Nontrivial (H ⧸ (leviDefiningHopfIdeal l).toIdeal) := Bialgebra.nontrivial k
  have : Nontrivial (H ⧸ l.unipotentDefiningHopfIdeal.toIdeal) := Bialgebra.nontrivial k
  exact Bialgebra.nontrivial k

section Smooth

variable [Algebra.FiniteType k H] [Algebra.Smooth k H]

instance : Algebra.FiniteType k (OCRing l) :=
  inferInstanceAs (Algebra.FiniteType k (OpenCellRing l))

/-- The open cell ring is formally smooth over `k`. -/
instance formallySmooth_oCRing : Algebra.FormallySmooth k (OCRing l) := by
  have hT : ∀ (B C : Type u) [CommRing B] [CommRing C] [Algebra k B] [Algebra k C]
      [Algebra.FormallySmooth k B] [Algebra.FormallySmooth k C],
      Algebra.FormallySmooth k (B ⊗[k] C) := fun B C _ _ _ _ _ _ =>
    Algebra.FormallySmooth.comp k B (B ⊗[k] C)
  have := hT (H ⧸ l.oppositeCocharacter.unipotentDefiningHopfIdeal.toIdeal)
    (H ⧸ (leviDefiningHopfIdeal l).toIdeal)
  exact hT _ (H ⧸ l.unipotentDefiningHopfIdeal.toIdeal)

/-- **Step 2.** Equal ranks. -/
theorem finrank_openCell_kaehler :
    Module.finrank (OCRing l) ((OCRing l) ⊗[H] Ω[H⁄k]) =
      Module.finrank (OCRing l) Ω[(OCRing l)⁄k] := by
  have : Nontrivial H := Bialgebra.nontrivial k
  have : Algebra.FiniteType k ((H ⧸ l.oppositeCocharacter.unipotentDefiningHopfIdeal.toIdeal) ⊗[k]
      (H ⧸ (leviDefiningHopfIdeal l).toIdeal)) :=
    Algebra.FiniteType.trans (S := H ⧸ l.oppositeCocharacter.unipotentDefiningHopfIdeal.toIdeal)
      inferInstance inferInstance
  rw [Module.finrank_baseChange, finrank_kaehler k H, finrank_kaehler k (OCRing l)]
  change _ = Module.finrank k (Bialgebra.CotangentSpace k (OpenCellRing l))
  rw [finrank_cotangentSpace_tensorProduct, finrank_cotangentSpace_tensorProduct]
  exact (finrank_openCell_cotangent l).symm

/-- **The open cell map is étale.** -/
theorem formallyEtale_openCell : Algebra.FormallyEtale H (OCRing l) := by
  apply formallyEtale_of_mapBaseChange_bijective (R := k)
  exact bijective_of_surjective_of_finrank_eq _ (mapBaseChange_openCell_surjective l)
    (finrank_openCell_kaehler l)

/-- **CGP 2.1.8 (3): the open cell map is flat.** -/
theorem flat_openCellRingHom :
    RingHom.Flat (R := H) (S := OpenCellRing l) (openCellRingHom l) := by
  have : Algebra.FinitePresentation H (OCRing l) := finitePresentation_openCellRingHom l
  have := formallyEtale_openCell l
  have : Algebra.Etale H (OCRing l) := ⟨inferInstance, inferInstance⟩
  exact (inferInstance : Module.Flat H (OCRing l))

/-- **The open cell is an open embedding** (no flatness hypothesis left). -/
theorem isOpenEmbedding_openCell :
    Topology.IsOpenEmbedding
      (PrimeSpectrum.comap (R := H) (S := OpenCellRing l) (openCellRingHom l)) :=
  isOpenEmbedding_openCell_of_flat l (flat_openCellRingHom l)

end Smooth

namespace OpenCell

/-- **Proposition 16.10 (ii) over a field, printed root form, no auxiliary hypotheses.**
`G` smooth of finite type over `k`, geometrically connected. -/
theorem magnetIdeal_eq_parabolic_of_field {X : Type u} [CommGroup X] [DecidableEq X]
    [Algebra.FiniteType k H] [Algebra.Smooth k H]
    [ConnectedSpace (PrimeSpectrum (AlgebraicClosure k ⊗[k] H))]
    (π : H →ₐc[k] MonoidAlgebra k X) (ψ : X →* Multiplicative ℤ)
    {N : Magnet (Additive X)} (hN : N ≤ natMagnet.comap (pairingHom ψ))
    (hΦ : {α | α ∈ N} ∩ roots π = {α | α ∈ natMagnet.comap (pairingHom ψ)} ∩ roots π) :
    magnetIdeal (torusGrading π) N =
      (parabolicDefiningHopfIdeal (π.cocharacter ψ)).toIdeal := by
  have : IrreducibleSpace (PrimeSpectrum (AlgebraicClosure k ⊗[k] H)) :=
    irreducibleSpace_of_connectedSpace (AlgebraicClosure k)
  exact magnetIdeal_eq_parabolic_of_field_of_openCell π ψ hN hΦ
    (flat_openCellRingHom (k := AlgebraicClosure k) _)

end OpenCell

end AlgMag.Reductive
