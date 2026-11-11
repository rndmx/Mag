/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Reductive.OpenCell.OpenCellFlatness
import TauCeti.Algebra.AlgebraicGroup.Hopf.LeftTranslation
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-!
# The open cell as an open subscheme, its translates, and affineness through a section

Items 1, 2, 4 of the T4 scheme programme (`equivalence-reductive/lean-forward.md`, round 5).

1. `isOpenImmersion_openCell`: for `G = Spec H` smooth of finite type, the open cell map
   `Spec(k[U(λ⁻)] ⊗ k[Z(λ)] ⊗ k[U(λ)]) → Spec H` (`OpenCellRing l`, `openCellRingHom l`) is an
   open immersion of schemes (flat + mono + locally of finite presentation,
   `IsOpenImmersion.of_flat_of_mono`). `openCellOpens l` is its image `Ω`, an affine open.
2. `translateOpenCell l g`: the translate `g·Ω` by a `k`-point `g`, i.e. `Ω` composed with the
   automorphism `Spec` of left translation; again an open immersion with affine image.
4. `isAffine_of_section`: if `f : X ⟶ Y` is separated with a section `s` and `X` is affine, then
   `Y` is affine (the section is a closed immersion). This is the step
   "`(V ∖ {1}) × W` affine and `W` has a point ⇒ `V ∖ {1}` affine".
-/

suppress_compilation

open CategoryTheory AlgebraicGeometry Magnetism TauCeti TauCeti.Cocharacter

namespace AlgMag.Reductive

universe u

section Section

/-- **Item 4.** A scheme receiving a section of a separated morphism out of an affine scheme is
affine. -/
theorem isAffine_of_section {X Y : Scheme.{u}} (f : X ⟶ Y) (s : Y ⟶ X) (hs : s ≫ f = 𝟙 Y)
    [IsSeparated f] [IsAffine X] : IsAffine Y := by
  haveI : IsClosedImmersion (s ≫ f) := by rw [hs]; infer_instance
  haveI : IsClosedImmersion s := IsClosedImmersion.of_comp s f
  exact isAffine_of_isAffineHom s

end Section

variable {k : Type u} {H : Type u} [Field k] [CommRing H] [HopfAlgebra k H]
variable (l : H →ₐc[k] LaurentPolynomial k)

/-- The open cell morphism `Spec(OpenCellRing l) ⟶ Spec H`. -/
abbrev openCellMor : Spec (CommRingCat.of (OpenCellRing l)) ⟶ Spec (CommRingCat.of H) :=
  Spec.map (CommRingCat.ofHom (R := H) (S := OpenCellRing l) (openCellRingHom l))

variable [Algebra.FiniteType k H] [Algebra.Smooth k H]

/-- **Item 1.** The open cell is an open immersion of schemes. -/
instance isOpenImmersion_openCell : IsOpenImmersion (openCellMor l) := by
  have := mono_spec_openCellRingHom l
  have : Flat (openCellMor l) := HasRingHomProperty.Spec_iff.mpr (flat_openCellRingHom l)
  have : LocallyOfFinitePresentation (openCellMor l) :=
    HasRingHomProperty.Spec_iff.mpr (finitePresentation_openCellRingHom l)
  exact IsOpenImmersion.of_flat_of_mono _

/-- The open cell `Ω = U(λ⁻)·Z(λ)·U(λ)` as an open of `Spec H`. -/
def openCellOpens : (Spec (CommRingCat.of H)).Opens := (openCellMor l).opensRange

/-- `Ω` is an affine open, isomorphic to `Spec(k[U(λ⁻)] ⊗ k[Z(λ)] ⊗ k[U(λ)])`. -/
theorem isAffineOpen_openCellOpens : IsAffineOpen (openCellOpens l) :=
  isAffineOpen_opensRange (openCellMor l)

/-- `Ω ≅ Spec(OpenCellRing l)` as schemes. -/
def openCellIso : (openCellOpens l).toScheme ≅ Spec (CommRingCat.of (OpenCellRing l)) :=
  (Scheme.Hom.isoOpensRange (openCellMor l)).symm

/-- `Spec` of left translation by a `k`-point `g`, an automorphism of `Spec H`. -/
def translateIso (g : WithConv (H →ₐ[k] k)) : Spec (CommRingCat.of H) ≅ Spec (CommRingCat.of H) :=
  Scheme.Spec.mapIso (RingEquiv.toCommRingCatIso
    (HopfAlgebra.leftTranslationAlgEquiv g).toRingEquiv).op

/-- **Item 2.** The translate `g·Ω` of the open cell: an open immersion. -/
abbrev translateOpenCellMor (g : WithConv (H →ₐ[k] k)) :
    Spec (CommRingCat.of (OpenCellRing l)) ⟶ Spec (CommRingCat.of H) :=
  openCellMor l ≫ (translateIso g).hom

instance (g : WithConv (H →ₐ[k] k)) : IsOpenImmersion (translateOpenCellMor l g) := by
  infer_instance

/-- The open `g·Ω` of `Spec H`. -/
def translateOpenCell (g : WithConv (H →ₐ[k] k)) : (Spec (CommRingCat.of H)).Opens :=
  (translateOpenCellMor l g).opensRange

/-- `g·Ω` is an affine open. -/
theorem isAffineOpen_translateOpenCell (g : WithConv (H →ₐ[k] k)) :
    IsAffineOpen (translateOpenCell l g) :=
  isAffineOpen_opensRange (translateOpenCellMor l g)

/-- `Ω ∩ g·Ω` is an affine open of the affine (hence separated) `Spec H`. -/
theorem isAffineOpen_openCell_inf_translate (g : WithConv (H →ₐ[k] k)) :
    IsAffineOpen (openCellOpens l ⊓ translateOpenCell l g) :=
  (isAffineOpen_openCellOpens l).inf (isAffineOpen_translateOpenCell l g)

end AlgMag.Reductive
