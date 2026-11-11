/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Sec12Final
import AlgMag.Faces.Regrade

/-!
# Proposition 12.1F: connected components along any face (faces-bb.md, §2)

`N` finitely generated, `X` separated with an `N^×`-FPR atlas, `F` any face of `N`. Then
`p_{N,F} : X^N → X^F` has geometrically connected fibres and induces a bijection
`π₀(|X^N|) ≅ π₀(|X^F|)`.

Representability of `X^F` (check of faces-bb.md): "`N`-FPR" means `N^×`-FPR (Def 6.1(ii)), `F^× = N^×`
(`Faces.unitsSub_face_eq`) and `F` is finitely generated (`IsFace.fg`), so Theorem 8.3 applies to `F`.

The connectedness argument is the printed one, through `Ψ` of Proposition 12.3 (already proved for
any face: `exists_strong_deformation_retract`) and `class_mem_connectedComponent_of_line`, packaged in
`bijective_connectedComponents_repFace` and `connectedSpace_faceFibre`, which are stated for any face.
-/

open CategoryTheory Opposite AlgebraicGeometry AlgebraicGeometry.Space

universe u

namespace AlgMag

section Prop121F

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {M : Type u} [AddCommGroup M] [AddGroup.FG M] {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
  {actX : AAction (fppfO B S hS) M X}

/-- **Proposition 12.1F.** `N` finitely generated, `X` separated with an `N^×`-FPR atlas, `F` any face of
`N`. `X^N`, `X^F` are algebraic spaces (Theorem 8.3 for `N` and for `F`); `p_{N,F}` has connected fibres
over all field-valued points (so geometrically connected fibres), and induces a bijection on the
connected components of the underlying spaces (topology of Stacks Tag 03BY). -/
theorem prop121_face (hX : IsAlgebraicSpace B S hS X) (hsep : IsSeparatedOver X)
    {N F : AddSubmonoid M} (hN : N.FG) (hF : IsFace F N)
    (hat : ExistsZFPRAtlas actX (unitsSub N)) :
    ∃ (rN : Thm83Repr actX N) (rF : Thm83Repr actX F),
      letI := pointTopology B S hS rN.P
      letI := pointTopology B S hS rF.P
      Function.Bijective (continuous_pointsMap B S hS
        (repFace rN.rP rF.rP hF)).connectedComponentsMap ∧
      ∀ q : FieldValuedPoint B S hS rF.P,
        @ConnectedSpace _ (pointTopology B S hS (faceFibre hF rN.rP rF.rP q)) := by
  have hFg : F.FG := hF.fg hN
  have hatF : ExistsZFPRAtlas actX (unitsSub F) := by
    rw [Faces.unitsSub_face_eq hF]
    exact hat
  obtain ⟨rN⟩ := thm83_repr hX hsep N hat (Or.inl hN)
  obtain ⟨rF⟩ := thm83_repr hX hsep F hatF (Or.inl hFg)
  refine ⟨rN, rF, ?_, fun q => ?_⟩
  · exact bijective_connectedComponents_repFace hF hN rN.rP rF.rP _ _
      (schemeContinuous_pointTopology _) _ (continuous_pointsMap B S hS _)
  · exact connectedSpace_faceFibre hF hN rN.rP rF.rP q _ (schemeContinuous_pointTopology _)

end Prop121F

end AlgMag

