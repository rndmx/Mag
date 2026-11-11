/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Sec11PrintedProps
import AlgMag.Sec11SchemesRep
import AlgMag.Sec12PrintedSchemes

/-!
# Corollary 11.10 and `smooth_faceZ`, on the printed Corollary 10.3
-/

open CategoryTheory Opposite AlgebraicGeometry

universe u

namespace AlgMag.Sec11Printed

open AlgMag.GB AlgMag.Lifts AlgMag.SmoothSchemes

variable {S : Scheme.{u}} {M : Type u} [AddCommGroup M] (N : AddSubmonoid M)

/-- **Corollary 11.10**, schemes only: if `X → S` is smooth, `F` a face of `N`, and `X^N`, `X^F` are
representable by schemes, then `X^N → X^F` is smooth. -/
theorem smooth_repFace {X Zx Zf : Over S} (aX : AAction (overO S) M (yoneda.obj X))
    {F : AddSubmonoid M} (hF : IsFace F N) [Smooth X.hom]
    (rx : RepresentsAttractor aX N (yoneda.obj Zx)) (rf : RepresentsAttractor aX F (yoneda.obj Zf))
    (z : Zx ⟶ Zf) (hz : ∀ (T : Over S) (w : T ⟶ Zx),
      rf.equiv T (w ≫ z) = AttractorPt.ofFace hF (rx.equiv T w)) : Smooth z.left := by
  have h₁ := locallyOfFinitePresentation_rep N aX rx
  have h₂ := locallyOfFinitePresentation_rep F aX rf
  have h₃ : LocallyOfFinitePresentation (z.left ≫ Zf.hom) := by
    rw [Over.w z]
    exact h₁
  have h₄ : LocallyOfFinitePresentation z.left :=
    locallyOfFinitePresentation_of_comp z.left Zf.hom
  exact (Stacks.Smooth.smooth_iff_locallyOfFinitePresentation_and_formallySmooth z.left).2
    ⟨h₄, formallySmoothScheme_of_rep (faceMap aX hF) (Sec11Printed.isFormallySmooth_faceMap_scheme N hF aX)
      rx.equiv rf.equiv (fun s w => rx.naturality s w) (fun s w => rf.naturality s w) z hz⟩


open Sec12Printed in
/-- `AlgMag.Sec12Printed.smooth_faceZ`, resting on the printed Corollary 10.3. -/
theorem smooth_faceZ {X : Over S} [IsAffineHom X.hom] (act : AAction (overO S) M (yoneda.obj X))
    {F : AddSubgroup M} (hF : IsFace F.toAddSubmonoid N) [Smooth X.hom] :
    Smooth (faceZ act N hF).left :=
  smooth_repFace N act hF (representsAttractor act N)
    (representsAttractor act F.toAddSubmonoid) (faceZ act N hF) (fun _ w => faceZ_spec act N hF w)

end AlgMag.Sec11Printed
