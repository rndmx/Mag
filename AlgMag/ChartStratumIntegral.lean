/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.ChartStratumInv
import StacksFrontier.AlgebraicGeometry.Descent.LocalProperties.Noetherian

/-!
# An integral étale chart (affine stratum lemma, step 1)

A nonempty reduced, locally noetherian algebraic space has an étale chart which is affine, integral
and noetherian, and lies over an affine open of the base.
-/

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u

namespace AlgMag.ChartStratum

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

local notation "SCH" => BigFppfOver.toScheme B S hS

/-- A nonempty reduced noetherian scheme has a nonempty affine integral open. -/
theorem exists_integral_affine_open (Y : Scheme.{u}) [IsNoetherian Y] [IsReduced Y] [Nonempty Y] :
    ∃ V : Y.Opens, IsAffineOpen V ∧ Nonempty V ∧ IsIntegral V.toScheme := by
  obtain ⟨y⟩ := ‹Nonempty Y›
  let Z := irreducibleComponent y
  have hZ : Z ∈ irreducibleComponents Y := irreducibleComponent_mem_irreducibleComponents y
  have hfin := TopologicalSpace.NoetherianSpace.finite_irreducibleComponents (α := Y)
  have hsd : (irreducibleComponents Y \ {Z}).Finite := hfin.sdiff
  have hne : ¬ Z ⊆ ⋃₀ (irreducibleComponents Y \ {Z}) := by
    intro hsub
    have hsub' : Z ⊆ ⋃₀ (↑hsd.toFinset : Set (Set Y)) := by simpa using hsub
    obtain ⟨z, hz, hzs⟩ := (isIrreducible_iff_sUnion_isClosed.1 hZ.1) hsd.toFinset
      (fun z hz => isClosed_of_mem_irreducibleComponents z (hsd.mem_toFinset.1 hz).1) hsub'
    have hz' := hsd.mem_toFinset.1 hz
    exact hz'.2 (Maximal.eq_of_le hZ hz'.1.1 hzs).symm
  obtain ⟨w, hwZ, hw⟩ := Set.not_subset.1 hne
  let U : Y.Opens := Scheme.irreducibleComponentOpen Y Z
  have hwU : w ∈ U := hw
  obtain ⟨V, hV, hwV, hVU⟩ := exists_isAffineOpen_mem_and_subset (X := Y) (x := w) (U := U) hwU
  have hVZ : (V : Set Y) ⊆ Z := by
    intro v hv
    by_contra hvZ
    obtain ⟨z, hz, hvz⟩ : ∃ z ∈ irreducibleComponents Y, v ∈ z :=
      ⟨_, irreducibleComponent_mem_irreducibleComponents v, mem_irreducibleComponent⟩
    have hvU : v ∈ U := hVU hv
    refine hvU ⟨z, ⟨hz, ?_⟩, hvz⟩
    rintro rfl
    exact hvZ hvz
  have hpre : IsPreirreducible (V : Set Y) := hZ.1.2.open_subset V.isOpen hVZ
  haveI : Nonempty V := ⟨⟨w, hwV⟩⟩
  haveI : PreirreducibleSpace V := Subtype.preirreducibleSpace hpre
  haveI : IrreducibleSpace V := ⟨inferInstance⟩
  refine ⟨V, hV, inferInstance, ?_⟩
  exact isIntegral_of_irreducibleSpace_of_isReduced _

/-- **Affine stratum lemma, step 1**: a nonempty reduced, locally noetherian algebraic space has an étale chart
which is affine, integral and noetherian, over an affine open of the base. -/
theorem exists_integral_chart {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hY : IsAlgebraicSpace B S hS Y)
    (hRed : Space.HasEtaleLocalProperty B S hS Y (fun T : Scheme.{u} => IsReduced T))
    (hNoe : Space.HasEtaleLocalProperty B S hS Y (fun T : Scheme.{u} => IsLocallyNoetherian T))
    (hne : Nonempty (Space.points B S hS Y)) :
    ∃ (V : BigFppfOver B S hS) (p : Y.obj (op V)) (A : BigFppfOver B S hS),
      IsAffine ((SCH).obj V) ∧ IsDomain Γ((SCH).obj V, ⊤) ∧ IsNoetherianRing Γ((SCH).obj V, ⊤) ∧
      (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@Etale.{u} : MorphismProperty Scheme.{u}) (SCH))) (yonedaEquiv.symm p) ∧
      IsAffine ((SCH).obj A) ∧ AlgebraicGeometry.IsOpenImmersion (structMap A) ∧
      Nonempty (V ⟶ A) := by
  obtain ⟨U₀, φ, hφs, hφe, hU₀r⟩ := hRed
  have hU₀n : IsLocallyNoetherian ((SCH).obj U₀) :=
    (Space.exists_atlas_iff_forall_etale B S hS Y (fun T : Scheme.{u} => IsLocallyNoetherian T) hY).1
      hNoe U₀ φ hφe
  have hU₀r' : IsReduced ((SCH).obj U₀) := hU₀r
  obtain ⟨pt⟩ := hne
  obtain ⟨z, -⟩ := (Space.surjective_iff_surjective_pointsMap B S hS Y hY U₀ φ).1 hφs pt
  let u₀ : (SCH).obj U₀ := Space.pointsEquivScheme B S hS U₀ z
  -- the affine open of the base
  obtain ⟨S₀, hS₀, hsS₀, -⟩ := exists_isAffineOpen_mem_and_subset (X := S)
    (x := structMap U₀ u₀) (U := ⊤) trivial
  let A : BigFppfOver B S hS := Space.opensObject B S hS (baseObj B S hS)
    (show ((SCH).obj (baseObj B S hS)).Opens from S₀)
  have hAa : IsAffine ((SCH).obj A) := hS₀
  have hAo : AlgebraicGeometry.IsOpenImmersion (structMap A) := by
    change AlgebraicGeometry.IsOpenImmersion (Scheme.Opens.ι S₀ ≫ 𝟙 S)
    infer_instance
  -- the affine open of the chart
  let O₁ : ((SCH).obj U₀).Opens := structMap U₀ ⁻¹ᵁ S₀
  obtain ⟨O₂, hO₂, hu₀, hO₂₁⟩ := exists_isAffineOpen_mem_and_subset (X := (SCH).obj U₀)
    (x := u₀) (U := O₁) hsS₀
  let U₁ := Space.opensObject B S hS U₀ O₂
  let i₁ : U₁ ⟶ U₀ := Space.opensObjectι B S hS _ _
  haveI hU₁a : IsAffine ((SCH).obj U₁) := hO₂
  haveI hU₁n : IsLocallyNoetherian ((SCH).obj U₁) :=
    inferInstanceAs (IsLocallyNoetherian (O₂.toScheme))
  haveI hU₁r : IsReduced ((SCH).obj U₁) := inferInstanceAs (IsReduced (O₂.toScheme))
  haveI hU₁N : IsNoetherian ((SCH).obj U₁) := {}
  haveI hU₁ne : Nonempty ((SCH).obj U₁) := ⟨⟨u₀, hu₀⟩⟩
  obtain ⟨V₀, hV₀, hV₀n, hV₀i⟩ := exists_integral_affine_open ((SCH).obj U₁)
  let V := Space.opensObject B S hS U₁ V₀
  let i₂ : V ⟶ U₁ := Space.opensObjectι B S hS _ _
  have hi₁ : AlgebraicGeometry.IsOpenImmersion ((SCH).map i₁) := by
    change AlgebraicGeometry.IsOpenImmersion (Scheme.Opens.ι (X := (SCH).obj U₀) _)
    infer_instance
  have hi₂ : AlgebraicGeometry.IsOpenImmersion ((SCH).map i₂) := by
    change AlgebraicGeometry.IsOpenImmersion (Scheme.Opens.ι (X := (SCH).obj U₁) _)
    infer_instance
  haveI hVa : IsAffine ((SCH).obj V) := hV₀
  haveI hVi : IsIntegral ((SCH).obj V) := hV₀i
  haveI hVl : IsLocallyNoetherian ((SCH).obj V) := isLocallyNoetherian_of_isOpenImmersion ((SCH).map i₂)
  have hVneo : Nonempty ((SCH).obj V) := hV₀n
  have hVd : IsDomain Γ((SCH).obj V, ⊤) := inferInstance
  have hVN : IsNoetherianRing Γ((SCH).obj V, ⊤) :=
    IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top _⟩
  let p : Y.obj (op V) := φ.app (op V) (i₂ ≫ i₁)
  have hsym : yonedaEquiv.symm p = yoneda.map (i₂ ≫ i₁) ≫ φ := by
    apply yonedaEquiv.injective
    rw [Equiv.apply_symm_apply, yonedaEquiv_comp, yonedaEquiv_yoneda_map]
  have hE : (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@Etale.{u} : MorphismProperty Scheme.{u}) (SCH))) (yonedaEquiv.symm p) := by
    let P := MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u}) (SCH)
    have : MorphismProperty.IsStableUnderComposition (@Etale.{u} : MorphismProperty Scheme.{u}) :=
      (inferInstance : MorphismProperty.IsMultiplicative
        (@Etale.{u} : MorphismProperty Scheme.{u})).toIsStableUnderComposition
    have : P.IsStableUnderComposition := MorphismProperty.IsStableUnderComposition.inverseImage _
    have : P.IsStableUnderBaseChange :=
      ⟨fun sq hg => MorphismProperty.IsStableUnderBaseChange.of_isPullback
        (P := @Etale.{u}) (sq.map (SCH)) hg⟩
    have h1 : P.presheaf (yoneda.map (i₂ ≫ i₁)) :=
      MorphismProperty.relative_map (F := yoneda) (show Etale ((SCH).map (i₂ ≫ i₁)) by
        rw [Functor.map_comp]; infer_instance)
    rw [hsym]
    exact MorphismProperty.comp_mem _ _ _ h1 hφe
  have hvA : Nonempty (V ⟶ A) := by
    refine nonempty_hom_of_range hAo ?_
    rintro _ ⟨y, rfl⟩
    have e : structMap V = (SCH).map (i₂ ≫ i₁) ≫ structMap U₀ :=
      (congrArg B.inclusion.map (Over.w (i₂ ≫ i₁))).symm
    have hin : (SCH).map (i₂ ≫ i₁) y ∈ O₂ := by
      rw [Functor.map_comp, Scheme.Hom.comp_apply]
      exact ((SCH).map i₂ y).2
    have hin2 : structMap U₀ ((SCH).map (i₂ ≫ i₁) y) ∈ S₀ := hO₂₁ hin
    refine ⟨⟨_, hin2⟩, ?_⟩
    rw [e, Scheme.Hom.comp_apply]
    rfl
  exact ⟨V, p, A, hVa, hVd, hVN, hE, hAa, hAo, hvA⟩

end AlgMag.ChartStratum

#print axioms AlgMag.ChartStratum.exists_integral_chart
