/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.StronglyFPR
import AlgMag.Sec15Final
import StacksFrontier.AlgebraicGeometry.Spaces.Decent.ClosedPoints
import StacksFrontier.AlgebraicGeometry.Spaces.PointTopologyEtaleOpen
import StacksFrontier.AlgebraicGeometry.Spaces.PointsRepresentable
import StacksFrontier.AlgebraicGeometry.Spaces.PointsOfPullback

/-!
# Closed points detect covers (§2.4 of *Existence of strongly-FPR atlases*)

`AlgMag.StronglyFPR.closedPointsDetectCovers`: for `X` decent with `|X|` Jacobson and quasi-compact,
`AlgMag.ClosedPointsDetectCovers X` holds.
-/

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Space

universe u

namespace AlgMag.StronglyFPR

attribute [local instance] pointTopology

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
variable {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- §2.4: "the complement is closed and contains no closed point ... finitely many cover". -/
theorem closedPointsDetectCovers (hX : IsAlgebraicSpace B S hS X) (hdec : IsDecentSpace B S hS X)
    (hJ : JacobsonSpace (points B S hS X)) (hC : CompactSpace (points B S hS X)) :
    ClosedPointsDetectCovers X := by
  intro ι U f e hcl
  let R : ι → Set (points B S hS X) := fun i => Set.range (pointsMap B S hS _ (f i))
  have hRo : ∀ i, IsOpen (R i) := fun i =>
    (isOpenMap_pointsMap_of_presheafEtale B S hS (f i) (e i)).isOpen_range
  have hcov : (⋃ i, R i) = Set.univ := by
    by_contra hne
    let Z := (⋃ i, R i)ᶜ
    have hZc : IsClosed Z := (isOpen_iUnion hRo).isClosed_compl
    have hZn : Z.Nonempty := by
      rw [Set.nonempty_compl]; exact hne
    obtain ⟨x, hxZ, hxc⟩ := nonempty_inter_closedPoints hZn hZc.isLocallyClosed
    obtain ⟨p, hpx, hpc⟩ := exists_fieldValuedPoint_isClosedImmersion B S hS hX hdec x hxc
    let cp : ChartPoint X :=
      { P := p.siteObject B S hS X
        k := p.carrier
        iso := Iso.refl _
        x := fieldMorphism B S hS X p
        isClosed := hpc }
    obtain ⟨i, u, hu⟩ := hcl cp
    apply hxZ
    refine Set.mem_iUnion.mpr ⟨i, ?_⟩
    let q : FieldValuedPoint B S hS (yoneda.obj (U i)) :=
      { carrier := p.carrier, contained := p.contained, toBase := p.toBase, value := u }
    refine ⟨q.class B S hS _, ?_⟩
    rw [pointsMap_class, ← hpx]
    have hv : (f i).app _ u = p.value := by
      have h1 := congrArg yonedaEquiv hu
      rw [yonedaEquiv_comp, yonedaEquiv_yoneda_map] at h1
      exact h1.trans (by simp [cp, fieldMorphism])
    refine FieldValuedPoint.class_eq_class_of_hasCommonExtension B S hS X ⟨p, ⟨𝟙 _, ?_⟩,
      FieldValuedPoint.dominates_refl B S hS X p⟩
    have e0 : ∀ y : X.obj (op (p.siteObject B S hS X)), X.map (𝟙 (p.siteObject B S hS X)).op y = y :=
      fun y => by simp
    exact (e0 _).trans hv
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover R hRo hcov.ge
  refine ⟨s.card, fun a => (s.equivFin.symm a : ι), fun T x t => ?_⟩
  obtain ⟨y, rfl⟩ := surjective_pointsToScheme B S hS T t
  have hy := hs (Set.mem_univ (pointsMap B S hS _ x y))
  obtain ⟨i, his, hi⟩ := Set.mem_iUnion₂.mp hy
  obtain ⟨a, ha⟩ : ∃ a, (s.equivFin.symm a : ι) = i := ⟨s.equivFin ⟨i, his⟩, by simp⟩
  subst ha
  refine ⟨a, ?_⟩
  have sq := (e (s.equivFin.symm a : ι)).rep.isPullback x
  have hm : y ∈ pointsMap B S hS _ x ⁻¹' Set.range (pointsMap B S hS _ (f (s.equivFin.symm a : ι))) := hi
  obtain ⟨x0, hx0⟩ := hm
  obtain ⟨w, -, rfl⟩ := exists_point_of_isPullback_presheaf B S hS sq x0 y hx0
  rw [pointsToScheme_pointsMap_yoneda]
  exact ⟨pointsToScheme B S hS _ w, rfl⟩

variable {M : Type u} [AddCommGroup M] [AddGroup.FG M]

/-- **Theorem 1.1 (2)**, `S` affine of finite type over `ℤ`, `X` of finite type: a single affine
scheme with a strongly-FPR atlas. Hypotheses beyond the note: `ChartLemmaStatement` (AHR, requested),
and decency, Jacobson and compactness of `|X|`, which are standard consequences of the assumptions but
whose library proofs lie in unbuilt modules. -/
theorem thm11_ft_of_points [IsAffine S] [HasFiniteCoproducts (BigFppfOver B S hS)]
    (hSft : LocallyOfFiniteType (terminal.from S)) (hX : IsAlgebraicSpace B S hS X)
    (hsep : Space.IsSeparatedOver B S hS X) (hft : Space.IsFiniteType B S hS (terminal.from X))
    (actX : AAction (fppfO B S hS) M X) (hchart : ChartLemmaStatement B S hS M)
    (hdec : IsDecentSpace B S hS X) (hJ : JacobsonSpace (points B S hS X))
    (hC : CompactSpace (points B S hS X)) :
    ∃ (V : BigFppfOver B S hS) (actV : AAction (fppfO B S hS) M (yoneda.obj V))
      (v : yoneda.obj V ⟶ X), IsStronglyFPRAtlas actV actX v ∧ IsSAffineAtlas actV actX v ∧
        IsAffine ((BigFppfOver.toScheme B S hS).obj V) :=
  thm11_ft hSft hX hsep hft actX hchart (closedPointsDetectCovers hX hdec hJ hC)

/-- **§2.5, base change step**: a strongly-FPR atlas of `X'` pulls back along an equivariant affine
`g : X → X'` (Lemma 6.7 (i) for all `Z` at once). -/
theorem strongAtlas_pullback {X' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {U : BigFppfOver B S hS}
    {actU : AAction (fppfO B S hS) M (yoneda.obj U)} {actX' : AAction (fppfO B S hS) M X'}
    {actX : AAction (fppfO B S hS) M X} {f : yoneda.obj U ⟶ X'} {g : X ⟶ X'}
    (hg : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@IsAffineHom.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS))) g)
    (hgeq : IsEquivariant actX actX' g) (h : IsStronglyFPRAtlas actU actX' f) :
    IsStronglyFPRAtlas (pullbackAction hg.rep f h.atlas.equivariant hgeq) actX (hg.rep.fst f) :=
  ⟨(lemma67_i hg hgeq (h.isZFPRAtlas ⊥)).atlas, fun Z => (lemma67_i hg hgeq (h.isZFPRAtlas Z)).isZFPR⟩

end AlgMag.StronglyFPR

#print axioms AlgMag.StronglyFPR.isClosed_badImage
#print axioms AlgMag.StronglyFPR.exists_strongChart
#print axioms AlgMag.StronglyFPR.thm11_ft
#print axioms AlgMag.StronglyFPR.closedPointsDetectCovers
#print axioms AlgMag.StronglyFPR.thm11_ft_of_points
#print axioms AlgMag.StronglyFPR.strongAtlas_pullback
