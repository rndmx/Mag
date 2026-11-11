/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.ChartStratumCore

/-!
# A stable affine open from an integral étale chart (affine stratum lemma, step 8)

An étale chart `p : V → X` with `V` affine, integral and noetherian, lying over an affine open `A` of
`S`, gives a nonempty affine `D(M)`-stable open of `X`.
-/

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgMag.StronglyFPR

universe u

namespace AlgMag.ChartStratum

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
variable {M : Type u} [AddCommGroup M] [Countable M] {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

local notation "SCH" => BigFppfOver.toScheme B S hS

/-- A section is a unit on any scheme mapping to its basic open. -/
lemma isUnit_of_factor_basicOpen {V : Scheme.{u}} (s : Γ(V, ⊤)) {T : Scheme.{u}}
    (t : T ⟶ (V.basicOpen s).toScheme) :
    IsUnit ((t ≫ (V.basicOpen s).ι).appTop.hom s) := by
  have h : T.basicOpen ((t ≫ (V.basicOpen s).ι).appTop.hom s) = ⊤ := by
    have e := Scheme.preimage_basicOpen (t ≫ (V.basicOpen s).ι) s
    refine Eq.trans e.symm ?_
    ext x
    simp only [Scheme.Hom.comp_base, TopologicalSpace.Opens.map_comp_obj]
    simp
  refine T.toRingedSpace.isUnit_of_isUnit_germ ⊤ _ fun x hx => ?_
  have hm : x ∈ T.basicOpen ((t ≫ (V.basicOpen s).ι).appTop.hom s) := by rw [h]; trivial
  exact (Scheme.mem_basicOpen_top T _ x).1 hm

variable [AddGroup.FG M]

theorem exists_stable_affine_of_chart {V : BigFppfOver B S hS} (act : AAction (fppfO B S hS) M X)
    (hVa : IsAffine ((SCH).obj V)) (hVd : IsDomain Γ((SCH).obj V, ⊤))
    (hVn : IsNoetherianRing Γ((SCH).obj V, ⊤)) (p : X.obj (op V))
    (hX : IsAlgebraicSpace B S hS X) (hsep : Space.IsSeparatedOver B S hS X)
    (hc : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u}) (SCH))) (yonedaEquiv.symm p))
    (A : BigFppfOver B S hS) (hAa : IsAffine ((SCH).obj A))
    (hAo : AlgebraicGeometry.IsOpenImmersion (structMap A)) (v : V ⟶ A) :
    ∃ (U : BigFppfOver B S hS) (actU : AAction (fppfO B S hS) M (yoneda.obj U))
      (f : yoneda.obj U ⟶ X), IsAffine ((SCH).obj U) ∧ Nonempty ((SCH).obj U) ∧
        IsEquivariant actU act f ∧ Space.IsOpenImmersion B S hS f := by
  classical
  haveI : AddMonoid.FG M := AddGroup.fg_iff_addMonoid_fg.mp inferInstance
  obtain ⟨s, hs, Z, hZ⟩ := exists_generic_stabilizer act hsep p
  let W := Space.opensObject B S hS V (((SCH).obj V).basicOpen s)
  let ι : W ⟶ V := Space.opensObjectι B S hS V _
  have hιo : AlgebraicGeometry.IsOpenImmersion ((SCH).map ι) := by
    change AlgebraicGeometry.IsOpenImmersion (Scheme.Opens.ι (X := (SCH).obj V) _)
    infer_instance
  have hunit : ∀ (T : BigFppfOver B S hS) (t : T ⟶ W),
      IsUnit (((SCH).map (t ≫ ι)).appTop.hom s) := fun T t => by
    rw [Functor.map_comp]
    exact isUnit_of_factor_basicOpen s ((SCH).map t)
  let c : yoneda.obj W ⟶ X := yoneda.map ι ≫ yonedaEquiv.symm p
  have hcE : Space.IsEtale B S hS c := by
    rw [Space.isEtale_iff_presheaf_of_yoneda]
    let P := MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u}) (SCH)
    have : MorphismProperty.IsStableUnderComposition (@Etale.{u} : MorphismProperty Scheme.{u}) :=
      (inferInstance : MorphismProperty.IsMultiplicative
        (@Etale.{u} : MorphismProperty Scheme.{u})).toIsStableUnderComposition
    have : P.IsStableUnderComposition := MorphismProperty.IsStableUnderComposition.inverseImage _
    have : P.IsStableUnderBaseChange :=
      ⟨fun sq hg => MorphismProperty.IsStableUnderBaseChange.of_isPullback
        (P := @Etale.{u}) (sq.map (SCH)) hg⟩
    have h1 : P.presheaf (yoneda.map ι) :=
      MorphismProperty.relative_map (F := yoneda) (show Etale ((SCH).map ι) from inferInstance)
    exact MorphismProperty.comp_mem _ _ _ h1 hc
  have hXsh : Presieve.IsSheaf (BigFppfOver.topology B S hS) X :=
    (isSheaf_iff_isSheaf_of_type _ _).1 hX.isSheaf
  have hst : ∀ {T : BigFppfOver B S hS} {x : X.obj (op T)}, x ∈ (orbSub act c).obj (op T) →
      ∀ h : APt (fppfO B S hS) M (op T),
        act.smul h x = x ↔ ∀ z ∈ Z, h (Multiplicative.ofAdd z) = 1 := fun hx h =>
    smul_eq_iff_of_orbitLocal hXsh hZ (orbitLocal_of_mem act p s ι hunit hX hcE hx) h
  have hrange : ∀ {T : BigFppfOver B S hS} {x : X.obj (op T)}, x ∈ (orbSub act c).obj (op T) →
      Nonempty (T ⟶ A) := by
    intro T x hx
    obtain ⟨U, q, r, -, -, -, hS'⟩ := exists_lift_of_mem_orbSub act c hX hcE hx
    refine nonempty_hom_of_range hAo ?_
    rintro _ ⟨y, rfl⟩
    obtain ⟨u, rfl⟩ := hS'.surj y
    have e1 : (SCH).map q ≫ structMap T = structMap U :=
      congrArg (B.inclusion.map) (Over.w q)
    let t : U ⟶ A := r.2 ≫ ι ≫ v
    have e2 : (SCH).map t ≫ structMap A = structMap U :=
      congrArg (B.inclusion.map) (Over.w t)
    refine ⟨(SCH).map t u, ?_⟩
    rw [← Scheme.Hom.comp_apply, e2, ← e1, Scheme.Hom.comp_apply]
  have hWne : Nonempty ((SCH).obj W) := by
    have hred : IsReduced ((SCH).obj V) := by
      haveI : IsReduced Γ((SCH).obj V, ⊤) := inferInstance
      exact isReduced_of_isAffine_isReduced _
    have hbo : ((SCH).obj V).basicOpen s ≠ ⊥ := fun e =>
      hs ((AlgebraicGeometry.basicOpen_eq_bot_iff s).1 e)
    obtain ⟨x, hx⟩ := TopologicalSpace.Opens.ne_bot_iff_nonempty _ |>.1 hbo
    exact ⟨⟨x, hx⟩⟩
  exact exists_stable_affine_of_orbit act c hX hsep hcE Z hst A hAa hAo hrange hWne

end AlgMag.ChartStratum

#print axioms AlgMag.ChartStratum.exists_stable_affine_of_chart
