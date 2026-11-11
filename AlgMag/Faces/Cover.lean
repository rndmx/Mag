/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Faces.Spaces
import AlgMag.Sec3Leftover313

/-!
# `X^N` is covered by smooth affine opens `(U_a)^N` (faces-bb-check.md, repair of Theorem A)

`X → S` smooth with a Zariski locally linearizable action of `D(M)_S`, `M` finitely generated, `N` any
magnet. Every point of the attractor functor `X^N` (`attP`) lies in the image of an open immersion
`(U_a)^N → X^N`, where `(U_a)^N` is a scheme, affine and smooth over `S` (Theorem 3.20, Cor 11.2).
Applied to a face `F` of `N` (itself a magnet), the same holds for `X^F`.
-/

suppress_compilation

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry Magnetism

open scoped Classical

universe u

namespace AlgMag.Faces

open AlgMag.GB AlgMag.Sec12Spaces AlgMag.Sec12Printed AlgMag.Sec12SpacesThm

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {M : Type u} [AddCommGroup M] [AddGroup.FG M]
  {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {actX : AAction (fppfO B S hS) M X}
  {A : Type u} {U : A → BigFppfOver B S hS}

/-- A magnet is a face of itself. -/
theorem isFace_refl (N : AddSubmonoid M) : IsFace N N where
  le := le_rfl
  mem_of_add_mem := fun hx hy _ => ⟨hx, hy⟩

/-- **`X^N` is covered by smooth affine opens.** For every point `y` of `X^N` over `T` and every
`t ∈ |T|` there is a chart `a` such that `(U_a)^N → X^N` is an open immersion whose image contains
`t`, and `(U_a)^N` is affine and smooth over `S`. -/
theorem attP_smooth_affine_cover (L : ZariskiLocallyLinearizable actX A U)
    (hsm : Space.IsSmooth B S hS (terminal.from X)) (N : AddSubmonoid M)
    {T : BigFppfOver B S hS} (y : (attP actX N).obj (op T)) (t : (BigFppfOver.toScheme B S hS).obj T) :
    ∃ a : A, haveI : IsAffineHom (structMap (U a)) := L.isAffineHom a
      ∃ he : Space.IsOpenImmersion B S hS
          (repAttractorMap (jHom L a) N (repCh (L.act a) N) (attPRep actX N)),
        t ∈ rangeOf he y ∧ Smooth (Zatt (chA (L.act a)) N).hom ∧
          IsAffineHom (Zatt (chA (L.act a)) N).hom := by
  have : ∀ a, IsAffineHom (structMap (U a)) := L.isAffineHom
  obtain ⟨a, he, -, ht, -⟩ := bb_face_attP L hsm (isFace_refl N) y t
  have hs : Smooth (chO (B := B) (S := S) (hS := hS) (U₀ := U a)).hom := smooth_chart L hsm a
  exact ⟨a, he, ht, smooth_Zatt (chA (L.act a)) N, inferInstance⟩

end AlgMag.Faces

