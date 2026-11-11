/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Sec12SpacesThm

/-!
# Algebraic Magnetism, Theorem 12.4: the statement to cite

`AlgMag.Sec12SpacesThm.thm124_attP`: `X → S` smooth with a Zariski locally linearizable action of `D(M)_S`,
`M` finitely generated (the standing hypothesis of §12), `N` arbitrary. `X^N`, `X^{N^×}` are the attractor
functors themselves (`AlgMag.attP`), so nothing about representing them is assumed. The chart maps
`(U_a)^{N^×} → X^{N^×}` and `(U_a)^N → X^N` are the ones induced by `U_a → X`.
-/

suppress_compilation

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry Magnetism

open scoped Classical

attribute [local instance] AlgMag.GB.gradedAlgebraOf

universe u

namespace AlgMag.Sec12SpacesThm

open AlgMag.GB AlgMag.Sec12Spaces AlgMag.Sec12Printed

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

local notation "SCH" => BigFppfOver.toScheme B S hS

variable {M : Type u} [AddCommGroup M] [AddGroup.FG M]
  {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {actX : AAction (fppfO B S hS) M X}
  {A : Type u} {U : A → BigFppfOver B S hS}

/-- **Theorem 12.4**, face form, with `e`, `e'` the maps induced by the chart `U_a → X`. -/
theorem thm124_induced_face (L : ZariskiLocallyLinearizable actX A U)
    (hsm : Space.IsSmooth B S hS (terminal.from X)) {N : AddSubmonoid M} {F : AddSubgroup M}
    (hF : IsFace F.toAddSubmonoid N) {Zx Zf : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (rx : RepresentsAttractor actX N Zx) (rf : RepresentsAttractor actX F.toAddSubmonoid Zf)
    {T : BigFppfOver B S hS} (y : Zf.obj (op T)) (t : (SCH).obj T) :
    ∃ a : A, haveI : IsAffineHom (structMap (U a)) := L.isAffineHom a
      ∃ he : Space.IsOpenImmersion B S hS
          (repAttractorMap (jHom L a) F.toAddSubmonoid (repCh (L.act a) F.toAddSubmonoid) rf),
        Space.IsOpenImmersion B S hS (repAttractorMap (jHom L a) N (repCh (L.act a) N) rx) ∧
        t ∈ rangeOf he y ∧
        IsPullback (repAttractorMap (jHom L a) N (repCh (L.act a) N) rx)
          (yoneda.map (faceS (L.act a) hF)) (repFace rx rf hF)
          (repAttractorMap (jHom L a) F.toAddSubmonoid (repCh (L.act a) F.toAddSubmonoid) rf) ∧
        (SCH).map (faceS (L.act a) hF) = (faceZ (chA (L.act a)) N hF).left ∧
        ∀ (V : S.Opens) (hV : IsAffineOpen V),
          IsPullback (iotaZ (chA (L.act a)) N ⟨V, hV⟩).left
            (PhiMap hV (rho0 (chA (L.act a)) N hF hV)).left (faceZ (chA (L.act a)) N hF).left
            (iotaZ (chA (L.act a)) F.toAddSubmonoid ⟨V, hV⟩).left ∧
          SymOver (chA (L.act a)) N hF hV := by
  have hC := countable_of_fg83 (M := M)
  have : ∀ a, IsAffineHom (structMap (U a)) := L.isAffineHom
  obtain ⟨a, he, ht⟩ := exists_chart_cover L rf (fun a => repCh (L.act a) F.toAddSubmonoid) y t
  have hO : Space.IsOpenImmersion B S hS (L.j a) := L.isOpen a
  have hp := isPullback_repFace_open (jHom L a) hO hF (repCh (L.act a) N) rx
    (repCh (L.act a) F.toAddSubmonoid) rf
  rw [repFace_eq] at hp
  have hs : Smooth (chO (B := B) (S := S) (hS := hS) (U₀ := U a)).hom := smooth_chart L hsm a
  exact ⟨a, he, (MorphismProperty.relative_isStableUnderBaseChange _).of_isPullback hp.flip he,
    ht, hp, rfl, fun V hV => ⟨isPullback_chart_square (chA (L.act a)) hF ⟨V, hV⟩,
      printed_affine (chA (L.act a)) N hF hV (Or.inr inferInstance)⟩⟩

/-- **Theorem 12.4**: `X → S` smooth with a Zariski locally linearizable action of `D(M)_S`, for any
magnet `N`. The morphism `X^N → X^{N^×}` of the attractor functors is, around every point of a scheme `T`
over `X^{N^×}`, the base change along the open immersion `(U_a)^{N^×} → X^{N^×}` induced by the chart
`U_a → X` of the morphism of schemes `(U_a)^N → (U_a)^{N^×}`. Over every affine open `V` of `S` the latter
is the base change of `Spec B → Spec B₀`, with `B = Sym_{B₀}(P)`, `P` finite projective over `B₀`. -/
theorem thm124_attP (L : ZariskiLocallyLinearizable actX A U)
    (hsm : Space.IsSmooth B S hS (terminal.from X)) (N : AddSubmonoid M)
    {T : BigFppfOver B S hS} (y : (attP actX (unitsOf N).toAddSubmonoid).obj (op T))
    (t : (SCH).obj T) :
    ∃ a : A, haveI : IsAffineHom (structMap (U a)) := L.isAffineHom a
      ∃ he : Space.IsOpenImmersion B S hS
          (repAttractorMap (jHom L a) (unitsOf N).toAddSubmonoid
            (repCh (L.act a) (unitsOf N).toAddSubmonoid) (attPRep actX (unitsOf N).toAddSubmonoid)),
        Space.IsOpenImmersion B S hS
          (repAttractorMap (jHom L a) N (repCh (L.act a) N) (attPRep actX N)) ∧
        t ∈ rangeOf he y ∧
        IsPullback (repAttractorMap (jHom L a) N (repCh (L.act a) N) (attPRep actX N))
          (yoneda.map (faceS (L.act a) (isFace_unitsOf N)))
          (repFace (attPRep actX N) (attPRep actX (unitsOf N).toAddSubmonoid) (isFace_unitsOf N))
          (repAttractorMap (jHom L a) (unitsOf N).toAddSubmonoid
            (repCh (L.act a) (unitsOf N).toAddSubmonoid) (attPRep actX (unitsOf N).toAddSubmonoid)) ∧
        (SCH).map (faceS (L.act a) (isFace_unitsOf N)) =
          (faceZ (chA (L.act a)) N (isFace_unitsOf N)).left ∧
        ∀ (V : S.Opens) (hV : IsAffineOpen V),
          IsPullback (iotaZ (chA (L.act a)) N ⟨V, hV⟩).left
            (PhiMap hV (rho0 (chA (L.act a)) N (isFace_unitsOf N) hV)).left
            (faceZ (chA (L.act a)) N (isFace_unitsOf N)).left
            (iotaZ (chA (L.act a)) (unitsOf N).toAddSubmonoid ⟨V, hV⟩).left ∧
          SymOver (chA (L.act a)) N (isFace_unitsOf N) hV :=
  thm124_induced_face L hsm (isFace_unitsOf N) (attPRep actX N)
    (attPRep actX (unitsOf N).toAddSubmonoid) y t

end AlgMag.Sec12SpacesThm

#print axioms AlgMag.Sec12SpacesThm.thm124_induced_face
#print axioms AlgMag.Sec12SpacesThm.thm124_attP
