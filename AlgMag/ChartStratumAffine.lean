/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.ChartStratumImage
import StacksFrontier.AlgebraicGeometry.Spaces.Bootstrap04S6Carriers
import StacksFrontier.AlgebraicGeometry.Descent.IndQuasiAffineFpqcSheaf

/-!
# Affineness along the quotient map (affine stratum lemma, step 7)

`Y → Q = Y/D(Z)` is fppf locally `D(Z) × V → V`, hence affine (Stacks 041Z): the preimage in `Y` of an
affine scheme mapping to `Q` is an affine scheme.
-/

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u

namespace AlgMag.ChartStratum

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
variable {M : Type u} [AddCommGroup M] [Countable M] {Z : AddSubgroup M}
variable {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

local notation "SCH" => BigFppfOver.toScheme B S hS

/-- A base change of an affine morphism is affine. -/
theorem isAffineHom_of_isPullback {P A C D : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {t : P ⟶ A} {l : P ⟶ C} {r : A ⟶ D} {b : C ⟶ D} (sq : IsPullback t l r b)
    (hr : Space.IsAffineHom B S hS r) : Space.IsAffineHom B S hS l := by
  intro Z' g
  obtain ⟨W, p, q, h⟩ := hr Z' (g ≫ b)
  refine ⟨W, sq.lift p (yoneda.map q ≫ g) (by rw [h.w, Category.assoc]), q, ?_⟩
  refine IsPullback.of_right (h₁₂ := t) (h₂₂ := b) (v₁₃ := r) ?_ (by simp) sq
  simpa using h

instance isLocalAtTarget_affine_fppf :
    MorphismProperty.IsLocalAtTarget
      (fun {X Y} (f : X ⟶ Y) => Space.IsAffineHom B S hS f.hom :
        MorphismProperty (AlgebraicSpaces B S hS))
      (Space.Topology.fppf.precoverage.{u, 0} B S hS) :=
  have _h : MorphismProperty.IsLocalAtTarget
      (fun {X Y} (f : X ⟶ Y) => Space.IsAffineHom B S hS f.hom :
        MorphismProperty (AlgebraicSpaces B S hS))
      (Space.Topology.fpqc.precoverage.{u, 0} B S hS) :=
    Space.isLocalAtTarget_isAffineHom_fpqc B S hS
  .of_le (Space.fppfPrecoverage_le_fpqcPrecoverage B S hS)

/-- `D(Z) × Y → Y` is affine. -/
theorem relSrc_isAffineHom : Space.IsAffineHom B S hS (relSrc (Y := Y) (Z := Z)) := by
  intro A g
  have hN : B.Contains (Spec (ZMon Z.toAddSubmonoid)) := contains_zmon_of_countable hS _
  let U := monAffUniversal Z.toAddSubmonoid hN ((BigAffineFppf.inclusion B S hS).obj A)
  have hAaff : IsAffine ((SCH).obj ((BigAffineFppf.inclusion B S hS).obj A)) := A.property
  have hUaff : IsAffine ((SCH).obj U.P) := by
    have h0 : IsAffine (MonAff Z.toAddSubmonoid
        ((SCH).obj ((BigAffineFppf.inclusion B S hS).obj A))) :=
      .of_isIso (MonAff.isoOfIsAffine Z.toAddSubmonoid
        ((SCH).obj ((BigAffineFppf.inclusion B S hS).obj A))).hom
    exact h0
  let W : BigAffineFppf B S hS := ⟨U.P, hUaff⟩
  let p : yoneda.obj U.P ⟶ relP Y Z := yonedaEquiv.symm (U.u, yonedaEquiv (yoneda.map U.π ≫ g))
  refine ⟨W, p, U.π, ?_⟩
  refine IsPullback.of_forall_isPullback_app fun T => ?_
  have hp : ∀ x : (yoneda.obj U.P).obj T, p.app T x = (APt.res x.op U.u, g.app T (x ≫ U.π)) := by
    intro x
    refine Prod.ext rfl ?_
    have := ConcreteCategory.congr_hom (g.naturality x.op) (U.π)
    have e0 : yonedaEquiv (yoneda.map U.π ≫ g) = g.app (op U.P) U.π := by
      rw [yonedaEquiv_comp, yonedaEquiv_yoneda_map]
    change Y.map x.op (yonedaEquiv (yoneda.map U.π ≫ g)) = _
    rw [e0]
    exact this.symm
  rw [Types.isPullback_iff]
  refine ⟨?_, ?_, ?_⟩
  · ext1
    refine DFunLike.ext _ _ fun x => ?_
    exact congrArg Prod.snd (hp x)
  · rintro x y ⟨e1, e2⟩
    have e1' : p.app T x = p.app T y := e1
    rw [hp, hp] at e1'
    have e2' : x ≫ U.π = y ≫ U.π := e2
    have e3 : APt.res x.op U.u = APt.res y.op U.u := (Prod.mk.inj e1').1
    have h1 := U.uniq (x ≫ U.π) (APt.res x.op U.u) x rfl rfl
    have h2 := U.uniq (y ≫ U.π) (APt.res y.op U.u) y rfl rfl
    rw [h1, h2, e2', e3]
  · intro x₂ x₃ e
    have e' : x₂.2 = g.app T x₃ := e
    refine ⟨U.lift x₃ x₂.1, ?_, U.lift_π x₃ x₂.1⟩
    change p.app T _ = x₂
    rw [hp]
    refine Prod.ext (U.res_lift x₃ x₂.1) ?_
    change g.app T (U.lift x₃ x₂.1 ≫ U.π) = x₂.2
    rw [U.lift_π, e']

/-- The preimage of an affine scheme along a quotient map, for a relation with affine source. -/
theorem exists_affine_preimage_gen [HasSheafify (BigFppfOver.topology B S hS) (Type u)]
    {Z₀ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {R U : Over Z₀} (j : Space.PreRelation R U)
    (hR : IsAlgebraicSpace B S hS R.left) (hU : IsAlgebraicSpace B S hS U.left)
    (hj : IsEquivalenceRelation j.target j.source)
    (hsrc : Space.IsAffineHom B S hS j.source.left)
    (hQ : IsAlgebraicSpace B S hS (Space.quotientSheaf j).obj)
    (D : BigFppfOver B S hS) (hD : IsAffine ((SCH).obj D))
    (ξ : yoneda.obj D ⟶ (Space.quotientSheaf j).obj) :
    ∃ (W : BigFppfOver B S hS) (p : yoneda.obj W ⟶ U.left) (q : W ⟶ D),
      IsAffine ((SCH).obj W) ∧
      IsPullback p (yoneda.map q) (Space.toQuotientSheaf j) ξ := by
  obtain ⟨V, f, aV, k, hF, hL, hS', sq⟩ :=
    Space.exists_fppf_isPullback_pullback_toQuotientSheaf j hR hU hj D ξ
  have hPp : IsAlgebraicSpace B S hS (pullback ξ (Space.toQuotientSheaf j)) :=
    isAlgebraicSpace_pullback B S hS _ _ (isAlgebraicSpace_yoneda B S hS D) hU hQ
  have hPV : IsAlgebraicSpace B S hS (pullback aV j.source.left) :=
    isAlgebraicSpace_pullback B S hS _ _ (isAlgebraicSpace_yoneda B S hS V) hR hU
  have hg : Space.IsAffineHom B S hS (pullback.fst aV j.source.left) :=
    isAffineHom_of_isPullback (IsPullback.of_hasPullback aV j.source.left).flip hsrc
  have hq : Space.IsAffineHom B S hS (pullback.fst ξ (Space.toQuotientSheaf j)) :=
    Space.of_isPullback_yoneda_map_of_fppf B S hS
      (fun {X Y} (f : X ⟶ Y) => Space.IsAffineHom B S hS f.hom) hF hL hS' hPp
      (PV := ⟨_, hPV⟩) sq hg
  obtain ⟨W, p, q, h⟩ := hq ⟨D, hD⟩ (𝟙 _)
  refine ⟨W.obj, p ≫ pullback.snd ξ (Space.toQuotientSheaf j), q, W.property, ?_⟩
  have := h.paste_horiz (IsPullback.of_hasPullback ξ (Space.toQuotientSheaf j)).flip
  simpa using this

theorem relJ_source_isAffineHom (β : AAction (fppfO B S hS) Z.toAddSubmonoid Y) :
    Space.IsAffineHom B S hS (relJ β).source.left := by
  rw [relJ_source]; exact relSrc_isAffineHom

end AlgMag.ChartStratum

#print axioms AlgMag.ChartStratum.relJ_source_isAffineHom
#print axioms AlgMag.ChartStratum.exists_affine_preimage_gen
