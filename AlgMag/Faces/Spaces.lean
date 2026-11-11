/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Faces.Affine
import AlgMag.FixesThm124

/-!
# Białynicki-Birula for faces (faces-bb.md, Theorem A)

`X → S` smooth with a Zariski locally linearizable action of `D(M)_S` (Definition 7.2), `M` finitely
generated, `N` any magnet, `F` any face of `N` (an `AddSubmonoid`, not a subgroup). Then
`p_{N,F} : X^N → X^F` is an affine space fibration with zero section `i_{F,N}`, in the form of
`Sec12SpacesThm.thm124_induced_face` (the case `F` a subgroup face, e.g. `N^×`):

* the charts `(U_a)^F → X^F` are open immersions and cover `X^F`;
* `(U_a)^N = X^N ×_{X^F} (U_a)^F`;
* over every affine open `V` of `S`, `(U_a)^N|_V → (U_a)^F|_V` is `Spec Sym_{B₀}(P) → Spec B₀`,
  `P = I/I²` finite projective, with zero section `i_{F,N}` (`Faces.FaceChart`).

Representability of `X^N`, `X^F` (check of faces-bb.md): as in `thm124_attP`, the statement is about
the attractor functors themselves (`attP`) or any presheaves representing them; `X^N` is covered by the
affine opens `(U_a)^N` by the theorem itself, so nothing about representing `X^N` is assumed.

Step 1 (charts) is obtained from the subgroup case `isPullback_repFace_open` for `N^× ⊆ N` and
`N^× ⊆ F` by pasting cartesian squares, since `F^× = N^×` (`Faces.unitsSub_face_eq`).
-/

suppress_compilation

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry Magnetism

open scoped Classical

attribute [local instance] AlgMag.GB.gradedAlgebraOf

universe u

namespace AlgMag.Faces

open AlgMag.GB AlgMag.Sec12Spaces AlgMag.Sec12Printed AlgMag.Sec12SpacesThm

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

local notation "SCH" => BigFppfOver.toScheme B S hS

section Paste

variable {M : Type u} [AddCommGroup M] [AddGroup.FG M] {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
  {aX : AAction (fppfO B S hS) M X} {aY : AAction (fppfO B S hS) M Y}

/-- `r_{Q,E} ∘ r_{N,Q} = r_{N,E}` on representing presheaves (Fact 3.15, faces compose). -/
lemma repFace_comp {E Q N : AddSubmonoid M} (hE : IsFace E Q) (hQ : IsFace Q N)
    {ZN ZQ ZE : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (rN : RepresentsAttractor aX N ZN)
    (rQ : RepresentsAttractor aX Q ZQ) (rE : RepresentsAttractor aX E ZE) :
    repFace rN rQ hQ ≫ repFace rQ rE hE = repFace rN rE (hE.trans' hQ) := by
  ext T z
  change (rE.equiv (unop T)).symm ((rQ.equiv (unop T) ((rQ.equiv (unop T)).symm
      ((rN.equiv (unop T) z).ofFace hQ))).ofFace hE) =
    (rE.equiv (unop T)).symm ((rN.equiv (unop T) z).ofFace (hE.trans' hQ))
  rw [Equiv.apply_symm_apply, AttractorPt.ofFace_trans hE hQ]

/-- `f^N` and `f^F` commute with `r_{N,F}`. -/
lemma repAttractorMap_comp_repFace (hg : EquivariantHom aX aY) {N F : AddSubmonoid M}
    (hF : IsFace F N) {ZX ZY ZX' ZY' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (rX : RepresentsAttractor aX N ZX) (rY : RepresentsAttractor aY N ZY)
    (rX' : RepresentsAttractor aX F ZX') (rY' : RepresentsAttractor aY F ZY') :
    repAttractorMap hg N rX rY ≫ repFace rY rY' hF =
      repFace rX rX' hF ≫ repAttractorMap hg F rX' rY' := by
  ext T z
  change (rY'.equiv (unop T)).symm (((rY.equiv (unop T)) ((rY.equiv (unop T)).symm _)).ofFace hF) =
    (rY'.equiv (unop T)).symm (((rX'.equiv (unop T)) ((rX'.equiv (unop T)).symm _)).push hg)
  rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  rfl

/-- **Step 1 of Theorem A, any face.** For `f : X → Y` an equivariant open immersion and `F` any face
of `N`: `X^N = Y^N ×_{Y^F} X^F`. Pasting of the subgroup case for `N^× ⊆ N` and `N^× ⊆ F`. -/
theorem isPullback_repFace_open_face (hg : EquivariantHom aX aY)
    (hf : Space.IsOpenImmersion B S hS hg.hom) {N F : AddSubmonoid M} (hF : IsFace F N)
    {ZX ZY ZX' ZY' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (rX : RepresentsAttractor aX N ZX) (rY : RepresentsAttractor aY N ZY)
    (rX' : RepresentsAttractor aX F ZX') (rY' : RepresentsAttractor aY F ZY') :
    IsPullback (repAttractorMap hg N rX rY) (repFace rX rX' hF) (repFace rY rY' hF)
      (repAttractorMap hg F rX' rY') := by
  have hC := countable_of_fg83 (M := M)
  have hK : IsFace (unitsOf N).toAddSubmonoid N := isFace_unitsOf N
  have hKF : IsFace (unitsOf N).toAddSubmonoid F := isFace_unitsOf_of_face hF
  have s₁ := isPullback_repFace_open hg hf hK rX rY (attPRep aX (unitsOf N).toAddSubmonoid)
    (attPRep aY (unitsOf N).toAddSubmonoid)
  have s₂ := isPullback_repFace_open hg hf hKF rX' rY' (attPRep aX (unitsOf N).toAddSubmonoid)
    (attPRep aY (unitsOf N).toAddSubmonoid)
  have eX : repFace rX (attPRep aX (unitsOf N).toAddSubmonoid) hK =
      repFace rX rX' hF ≫ repFace rX' (attPRep aX (unitsOf N).toAddSubmonoid) hKF :=
    (repFace_comp hKF hF rX rX' _).symm
  have eY : repFace rY (attPRep aY (unitsOf N).toAddSubmonoid) hK =
      repFace rY rY' hF ≫ repFace rY' (attPRep aY (unitsOf N).toAddSubmonoid) hKF :=
    (repFace_comp hKF hF rY rY' _).symm
  rw [eX, eY] at s₁
  exact IsPullback.of_bot s₁ (repAttractorMap_comp_repFace hg hF rX rY rX' rY') s₂

end Paste

variable {M : Type u} [AddCommGroup M] [AddGroup.FG M]

section Chart

variable {U₀ : BigFppfOver B S hS} (act : AAction (fppfO B S hS) M (yoneda.obj U₀))
  [hA : IsAffineHom (structMap U₀)]
variable {N F : AddSubmonoid M} (hF : IsFace F N)

/-- `X^N → X^F` on the site for the chart `U₀`: the morphism of schemes `faceZF`. -/
def faceSF : siteZ act N ⟶ siteZ act F :=
  Over.homMk (ObjectProperty.homMk (faceZF (chA act) N hF).left) (by
    apply B.inclusion.map_injective
    exact Over.w (faceZF (chA act) N hF))

lemma map_faceSF : (SCH).map (faceSF act hF) = (faceZF (chA act) N hF).left := rfl

omit hA in
lemma siteAtt_ofFaceF {T : BigFppfOver B S hS} (φo : AttractorPt (chA act) N (ov T)) :
    siteAtt act (AttractorPt.ofFace hF φo) = AttractorPt.ofFace hF (siteAtt act φo) := by
  refine AttractorPt.ext ?_
  funext T' s a
  rfl

/-- `yoneda (faceSF)` is `r : (U₀)^N → (U₀)^F` (copy of `Sec12SpacesThm.repFace_eq`). -/
lemma repFace_eqF : repFace (repCh act N) (repCh act F) hF = yoneda.map (faceSF act hF) := by
  ext T w
  apply ((repCh act F).equiv (unop T)).injective
  change _ = fwd act (w ≫ faceSF act hF)
  refine ((repCh act F).equiv (unop T)).apply_symm_apply _ |>.trans ?_
  have e : ovZ act (w ≫ faceSF act hF) = ovZ act w ≫ faceZF (chA act) N hF :=
    Over.OverMorphism.ext rfl
  rw [fwd, e, faceZF_spec, siteAtt_ofFaceF]
  rfl

end Chart

section Cover

variable {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {actX : AAction (fppfO B S hS) M X}
  {A : Type u} {U : A → BigFppfOver B S hS}

/-- **The charts `(U_a)^F → X^F` cover `X^F`**, `F` any face of `N`: a point of `X^F` gives a point of
`X^{F^×} = X^{N^×}`, covered by the `(U_a)^{N^×}` (`exists_chart_cover`), and
`(U_a)^F = X^F ×_{X^{N^×}} (U_a)^{N^×}` (`isPullback_repFace_open`). -/
theorem exists_chart_cover_face (L : ZariskiLocallyLinearizable actX A U) {N F : AddSubmonoid M}
    (hF : IsFace F N) {Zf : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (rf : RepresentsAttractor actX F Zf)
    {ZF : A → (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (rF : ∀ a, RepresentsAttractor (L.act a) F (ZF a))
    {T : BigFppfOver B S hS} (y : Zf.obj (op T)) (t : (SCH).obj T) :
    ∃ (a : A) (he : Space.IsOpenImmersion B S hS (repAttractorMap (jHom L a) F (rF a) rf)),
      t ∈ rangeOf he y := by
  have hC := countable_of_fg83 (M := M)
  have hKF : IsFace (unitsOf N).toAddSubmonoid F := isFace_unitsOf_of_face hF
  let rK := attPRep actX (unitsOf N).toAddSubmonoid
  let yK := (repFace rf rK hKF).app (op T) y
  obtain ⟨a, heK, ht⟩ := exists_chart_cover L rK
    (fun a => attPRep (L.act a) (unitsOf N).toAddSubmonoid) yK t
  have hO : Space.IsOpenImmersion B S hS (L.j a) := L.isOpen a
  have he := isOpenImmersion_repAttractorMap (jHom L a) hO F (rF a) rf
  refine ⟨a, he, ?_⟩
  -- the open locus `q : Q → T` of `yK`
  let q := heK.rep.snd (yonedaEquiv.symm yK)
  obtain ⟨xK, hxK⟩ := mem_of_range heK q yK (fun _ h => h)
  -- `(U_a)^F = X^F ×_{X^{N^×}} (U_a)^{N^×}`, evaluated at `Q`
  have sq := isPullback_repFace_open (jHom L a) hO hKF (rF a) rf
    (attPRep (L.act a) (unitsOf N).toAddSubmonoid) rK
  have sqQ := sq.map ((evaluation _ (Type u)).obj (op (heK.rep.pullback (yonedaEquiv.symm yK))))
  rw [Limits.Types.isPullback_iff] at sqQ
  obtain ⟨x, hx, -⟩ := sqQ.2.2 (Zf.map q.op y) xK (by
    change (repFace rf rK hKF).app _ (Zf.map q.op y) =
      (repAttractorMap (jHom L a) _ (attPRep (L.act a) (unitsOf N).toAddSubmonoid) rK).app _ xK
    rw [hxK]
    exact NatTrans.naturality_apply (repFace rf rK hKF) q.op y)
  exact range_sub_of_mem he q y x hx ht

end Cover

section Thm

variable {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {actX : AAction (fppfO B S hS) M X}
  {A : Type u} {U : A → BigFppfOver B S hS}

/-- **Theorem A (Białynicki-Birula for faces).** `X → S` smooth with a Zariski locally linearizable
action of `D(M)_S`, `M` finitely generated, `N` any magnet, `F` any face of `N`; `Zx`, `Zf` represent
`X^N`, `X^F` (for instance `attP`, see `bb_face_attP`). For every point `t` of a scheme `T` over `Zf`,
there is a chart `a` such that:

* `(U_a)^F → X^F` is an open immersion with `t` in the preimage of its image;
* `(U_a)^N → X^N` is an open immersion and `(U_a)^N = X^N ×_{X^F} (U_a)^F`, the map
  `(U_a)^N → (U_a)^F` being the morphism of schemes `faceZF`;
* over every affine open `V` of `S`, `faceZF` is `Spec Sym_{B₀}(P) → Spec B₀` with zero section
  `i_{F,N}`, `P` finite projective over `B₀` (`Faces.FaceChart`).

Printed route for the affine part (Cor 11.2, Tags 067U, 063M, 062Z), coarsened grading by `N̄`. -/
theorem bb_face (L : ZariskiLocallyLinearizable actX A U)
    (hsm : Space.IsSmooth B S hS (terminal.from X)) {N F : AddSubmonoid M}
    (hF : IsFace F N) {Zx Zf : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (rx : RepresentsAttractor actX N Zx) (rf : RepresentsAttractor actX F Zf)
    {T : BigFppfOver B S hS} (y : Zf.obj (op T)) (t : (SCH).obj T) :
    ∃ a : A, haveI : IsAffineHom (structMap (U a)) := L.isAffineHom a
      ∃ he : Space.IsOpenImmersion B S hS (repAttractorMap (jHom L a) F (repCh (L.act a) F) rf),
        Space.IsOpenImmersion B S hS (repAttractorMap (jHom L a) N (repCh (L.act a) N) rx) ∧
        t ∈ rangeOf he y ∧
        IsPullback (repAttractorMap (jHom L a) N (repCh (L.act a) N) rx)
          (yoneda.map (faceSF (L.act a) hF)) (repFace rx rf hF)
          (repAttractorMap (jHom L a) F (repCh (L.act a) F) rf) ∧
        (SCH).map (faceSF (L.act a) hF) = (faceZF (chA (L.act a)) N hF).left ∧
        ∀ (V : S.Opens) (hV : IsAffineOpen V), FaceChart (chA (L.act a)) N hF hV := by
  have hC := countable_of_fg83 (M := M)
  have : ∀ a, IsAffineHom (structMap (U a)) := L.isAffineHom
  obtain ⟨a, he, ht⟩ := exists_chart_cover_face L hF rf (fun a => repCh (L.act a) F) y t
  have hO : Space.IsOpenImmersion B S hS (L.j a) := L.isOpen a
  have hp := isPullback_repFace_open_face (jHom L a) hO hF (repCh (L.act a) N) rx
    (repCh (L.act a) F) rf
  rw [repFace_eqF] at hp
  have hs : Smooth (chO (B := B) (S := S) (hS := hS) (U₀ := U a)).hom := smooth_chart L hsm a
  exact ⟨a, he, isOpenImmersion_repAttractorMap (jHom L a) hO N (repCh (L.act a) N) rx,
    ht, hp, rfl, fun V hV => faceChart_printed (chA (L.act a)) N hF hV (Or.inr inferInstance)⟩

/-- **Theorem A** for the attractor functors themselves: `X^N`, `X^F` are `attP`. -/
theorem bb_face_attP (L : ZariskiLocallyLinearizable actX A U)
    (hsm : Space.IsSmooth B S hS (terminal.from X)) {N F : AddSubmonoid M} (hF : IsFace F N)
    {T : BigFppfOver B S hS} (y : (attP actX F).obj (op T)) (t : (SCH).obj T) :
    ∃ a : A, haveI : IsAffineHom (structMap (U a)) := L.isAffineHom a
      ∃ he : Space.IsOpenImmersion B S hS
          (repAttractorMap (jHom L a) F (repCh (L.act a) F) (attPRep actX F)),
        Space.IsOpenImmersion B S hS
          (repAttractorMap (jHom L a) N (repCh (L.act a) N) (attPRep actX N)) ∧
        t ∈ rangeOf he y ∧
        IsPullback (repAttractorMap (jHom L a) N (repCh (L.act a) N) (attPRep actX N))
          (yoneda.map (faceSF (L.act a) hF)) (repFace (attPRep actX N) (attPRep actX F) hF)
          (repAttractorMap (jHom L a) F (repCh (L.act a) F) (attPRep actX F)) ∧
        (SCH).map (faceSF (L.act a) hF) = (faceZF (chA (L.act a)) N hF).left ∧
        ∀ (V : S.Opens) (hV : IsAffineOpen V), FaceChart (chA (L.act a)) N hF hV :=
  bb_face L hsm hF (attPRep actX N) (attPRep actX F) y t

end Thm

end AlgMag.Faces

