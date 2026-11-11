/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.ChartQSStabGenTests

/-!
# The generic stabilizer for quasi-separated `X`

Part of the proof of **Theorem 6.8 (ii)** (= Theorem A.2 (ii)) of Algebraic Magnetism (Mayeux,
Semigroup Forum 113 (2026)), through the specialization to `D(M)` of Alper–Hall–Rydh, Corollary 10.2.
This file proves the generic stabilizer statement (over a nonempty open of the base, the stabilizer is `D(M/Z)`) for quasi-separated `X`, without separatedness, generic flatness,
Zariski's main theorem or SGA 3 VI_B.

* `exists_affine_through`: an étale chart of a quasi-separated `X` meets an affine open of `X`.
* `genericStabilizerAt`, `genericStabilizerQS`: the generic stabilizer statement.
* `affineStratum_qs'`, `affineStratum_closedStable_qs'`: the affine stratum lemma (a nonempty `D(M)`-stable affine open)
  for quasi-separated `X`, with no further hypothesis.
-/

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgMag.StronglyFPR

universe u

namespace AlgMag.ChartQSStabGen

open AlgMag.ChartStratum AlgMag.ChartMain

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
variable {M : Type u} [AddCommGroup M] {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

local notation "SCH" => BigFppfOver.toScheme B S hS

/-- The trivial action of the trivial group. -/
noncomputable def act₀ (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :
    AAction (fppfO B S hS) PUnit.{u + 1} X where
  smul _ x := x
  one_smul _ := rfl
  mul_smul _ _ _ := rfl
  map_smul _ _ _ := rfl

lemma opens_open (V : BigFppfOver B S hS) (O : ((SCH).obj V).Opens) :
    AlgebraicGeometry.IsOpenImmersion ((SCH).map (Space.opensObjectι B S hS V O)) := by
  change AlgebraicGeometry.IsOpenImmersion (Scheme.Opens.ι (X := (SCH).obj V) O)
  infer_instance

/-- The open image of an étale chart over an affine open of `S` has an affine open. -/
theorem exists_affine_of_chart {W A : BigFppfOver B S hS} (hX : IsAlgebraicSpace B S hS X)
    (hqs : Space.IsQuasiSeparated B S hS (terminal.from X)) (c : yoneda.obj W ⟶ X)
    (hc : Space.IsEtale B S hS c) (hWne : Nonempty ((SCH).obj W)) (hAa : IsAffine ((SCH).obj A))
    (hAo : AlgebraicGeometry.IsOpenImmersion (structMap A)) (v : W ⟶ A) :
    ∃ (D : BigFppfOver B S hS) (ξ : yoneda.obj D ⟶ X), IsAffine ((SCH).obj D) ∧
      Space.IsOpenImmersion B S hS ξ ∧
      ∃ (U : BigFppfOver B S hS) (e : U ⟶ D) (t : U ⟶ W), Nonempty ((SCH).obj U) ∧
        ξ.app (op U) e = c.app (op U) t := by
  classical
  let act' := act₀ (B := B) (S := S) (hS := hS) X
  have hOp := orbSub_isOpen act' c hX hc
  let Yf := orbSub act' c
  let Y := Yf.toFunctor
  have hY : IsAlgebraicSpace B S hS Y := hOp.1
  have hrange : ∀ {T : BigFppfOver B S hS} {x : X.obj (op T)}, x ∈ Yf.obj (op T) →
      Nonempty (T ⟶ A) := by
    intro T x hx
    obtain ⟨U, q, r, -, -, -, hS'⟩ := exists_lift_of_mem_orbSub act' c hX hc hx
    refine nonempty_hom_of_range hAo ?_
    rintro _ ⟨y, rfl⟩
    obtain ⟨u, rfl⟩ := hS'.surj y
    have e1 : (SCH).map q ≫ structMap T = structMap U :=
      congrArg (B.inclusion.map) (Over.w q)
    let t : U ⟶ A := r.2 ≫ v
    have e2 : (SCH).map t ≫ structMap A = structMap U :=
      congrArg (B.inclusion.map) (Over.w t)
    refine ⟨(SCH).map t u, ?_⟩
    rw [← Scheme.Hom.comp_apply, e2, ← e1, Scheme.Hom.comp_apply]
  have hAm : Mono (structMap A) := inferInstance
  have hsub := hom_subsingleton hAm
  let r : Y ⟶ yoneda.obj A :=
    { app := fun T => ↾ fun x => (hrange x.2).some
      naturality := fun T T' f => by
        ext1
        refine DFunLike.ext _ _ fun x => ?_
        haveI := hsub T'.unop
        exact Subsingleton.elim _ _ }
  have hqsf : Space.IsQuasiSeparated B S hS r := AlgMag.ChartQSStrat.isQuasiSeparated_of_mono_qs Yf.ι r hqs
  have hqsabs : Space.IsAbsolutelyQuasiSeparated B S hS B.contains_terminal Y :=
    Space.isAbsolutelyQuasiSeparated_of_isQuasiSeparated B S hS B.contains_terminal hY
      (Space.isAbsolutelyQuasiSeparated_yoneda_of_isAffine B S hS B.contains_terminal A hAa) hqsf
  let x₀ : Y.obj (op W) := ⟨c.app (op W) (𝟙 W), by
    have := orbMap_mem act' c (T := op W) (ptTop 1, 𝟙 W)
    exact this⟩
  obtain ⟨w⟩ := hWne
  have hne : Nonempty (Space.points B S hS Y) :=
    ⟨Space.pointsMap B S hS (yoneda.obj W) (yonedaEquiv.symm x₀)
      ((Space.pointsEquivScheme B S hS W).symm w)⟩
  obtain ⟨D, ξY, hDa, hDne, hξY⟩ := exists_affine_open_of_absQS hY hqsabs hne
  refine ⟨D, ξY ≫ Yf.ι, hDa, Space.isOpenImmersion_comp B S hS _ _ hξY hOp.2, ?_⟩
  let x : Y.obj (op D) := ξY.app (op D) (𝟙 D)
  obtain ⟨U, q, r', he, -, -, hS'⟩ := exists_lift_of_mem_orbSub act' c hX hc x.2
  obtain ⟨d⟩ := hDne
  obtain ⟨u, -⟩ := hS'.surj d
  refine ⟨U, q, r'.2, ⟨u⟩, ?_⟩
  have e1 : (ξY ≫ Yf.ι).app (op U) q = X.map q.op x.1 := by
    have := NatTrans.naturality_apply (ξY ≫ Yf.ι) q.op (𝟙 D)
    simpa using this
  rw [e1, ← he]
  rfl

/-- **The generic stabilizer**, at `act`, for quasi-separated `X`. -/
theorem genericStabilizerAt [AddMonoid.FG M] (hX : IsAlgebraicSpace B S hS X)
    (hqs : Space.IsQuasiSeparated B S hS (terminal.from X)) (act : AAction (fppfO B S hS) M X) :
    AlgMag.ChartQSStrat.GenericStabilizerAt act := by
  classical
  intro V hVa hVd hVn p hpe
  haveI : AddGroup.FG M := AddGroup.fg_iff_addMonoid_fg.mpr inferInstance
  haveI : Countable M := countable_of_fg M
  have hVred : IsReduced ((SCH).obj V) := by
    haveI : IsReduced Γ((SCH).obj V, ⊤) := inferInstance
    exact isReduced_of_isAffine_isReduced _
  have hbo : ((SCH).obj V).basicOpen (1 : Γ((SCH).obj V, ⊤)) ≠ ⊥ := fun e =>
    one_ne_zero ((AlgebraicGeometry.basicOpen_eq_bot_iff _).1 e)
  obtain ⟨v, -⟩ := TopologicalSpace.Opens.ne_bot_iff_nonempty _ |>.1 hbo
  -- an affine open of the base
  obtain ⟨S₀, hS₀, hsS₀, -⟩ := exists_isAffineOpen_mem_and_subset (X := S)
    (x := structMap V v) (U := ⊤) trivial
  let A : BigFppfOver B S hS := Space.opensObject B S hS (baseObj B S hS)
    (show ((SCH).obj (baseObj B S hS)).Opens from S₀)
  have hAa : IsAffine ((SCH).obj A) := hS₀
  have hAo : AlgebraicGeometry.IsOpenImmersion (structMap A) := by
    change AlgebraicGeometry.IsOpenImmersion (Scheme.Opens.ι S₀ ≫ 𝟙 S)
    infer_instance
  let O₁ : ((SCH).obj V).Opens := structMap V ⁻¹ᵁ S₀
  obtain ⟨s₀, hs₀O, hvs₀⟩ := (isAffineOpen_top ((SCH).obj V)).exists_basicOpen_le
    (V := O₁) ⟨v, hsS₀⟩ trivial
  let W₀ := Space.opensObject B S hS V (((SCH).obj V).basicOpen s₀)
  let ι₀ : W₀ ⟶ V := Space.opensObjectι B S hS V _
  have hι₀ := opens_open V (((SCH).obj V).basicOpen s₀)
  have hv₀ : Nonempty (W₀ ⟶ A) := by
    refine nonempty_hom_of_range hAo ?_
    rintro _ ⟨y, rfl⟩
    have hy : structMap W₀ y ∈ S₀ := by
      have e : structMap W₀ = (SCH).map ι₀ ≫ structMap V := rfl
      rw [e, Scheme.Hom.comp_apply]
      exact hs₀O y.2
    refine ⟨⟨_, hy⟩, ?_⟩
    rfl
  obtain ⟨v₀⟩ := hv₀
  let c : yoneda.obj W₀ ⟶ X := yoneda.map ι₀ ≫ yonedaEquiv.symm p
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
    have h1 : P.presheaf (yoneda.map ι₀) :=
      MorphismProperty.relative_map (F := yoneda) (show Etale ((SCH).map ι₀) from inferInstance)
    exact MorphismProperty.comp_mem _ _ _ h1 hpe
  obtain ⟨D, ξ, hDa, hξ, U, e, t, ⟨u⟩, he⟩ :=
    exists_affine_of_chart hX hqs c hcE ⟨⟨v, hvs₀⟩⟩ hAa hAo v₀
  -- the locus of `V` where `p` lies in `D`
  let ya : yoneda.obj V ⟶ X := yonedaEquiv.symm p
  have hx : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@AlgebraicGeometry.IsOpenImmersion.{u} : MorphismProperty Scheme.{u}) (SCH))) ξ := hξ
  let Fo := hx.rep.pullback ya
  let j : Fo ⟶ V := hx.rep.snd ya
  let sF : Fo ⟶ D := hx.rep.fst' ya
  have hj : AlgebraicGeometry.IsOpenImmersion ((SCH).map j) := hx.property_snd ya
  have hsq : yoneda.map sF ≫ ξ = yoneda.map j ≫ ya := (hx.rep.isPullback' ya).w
  have hc' : yoneda.map e ≫ ξ = yoneda.map (t ≫ ι₀) ≫ ya := by
    apply yonedaEquiv.injective
    have e1 : ya.app (op U) (t ≫ ι₀) = X.map (t ≫ ι₀).op p := yonedaEquiv_symm_app_apply p _ _
    have e2 : c.app (op U) t = ya.app (op U) (t ≫ ι₀) := rfl
    simp only [yonedaEquiv_apply, FunctorToTypes.comp, yoneda_map_app, Category.comp_id]
    exact he.trans e2
  let l : U ⟶ Fo := hx.rep.lift' e (t ≫ ι₀) hc'
  have hl : l ≫ j = t ≫ ι₀ := hx.rep.lift'_snd _ _ _
  let v₁ : (SCH).obj V := (SCH).map j ((SCH).map l u)
  obtain ⟨s, hsO, hv₁s⟩ := (isAffineOpen_top ((SCH).obj V)).exists_basicOpen_le
    (V := (SCH).map j |>.opensRange) ⟨v₁, ⟨_, rfl⟩⟩ trivial
  let W := Space.opensObject B S hS V (((SCH).obj V).basicOpen s)
  let i : W ⟶ V := Space.opensObjectι B S hS V _
  have hi := opens_open V (((SCH).obj V).basicOpen s)
  have hWne : Nonempty ((SCH).obj W) := ⟨⟨v₁, hv₁s⟩⟩
  have hr : Set.range ((SCH).map i) ⊆ Set.range ((SCH).map j) := by
    rintro _ ⟨y, rfl⟩
    exact hsO y.2
  let l₀ := AlgebraicGeometry.IsOpenImmersion.lift ((SCH).map j) ((SCH).map i) hr
  have hl₀ : l₀ ≫ (SCH).map j = (SCH).map i := AlgebraicGeometry.IsOpenImmersion.lift_fac _ _ _
  let l₁ : W ⟶ Fo := overHom l₀ (by rw [← site_w j, ← Category.assoc, hl₀, site_w])
  have hl₁ : l₁ ≫ j = i := toScheme_map_injective (by rw [Functor.map_comp]; exact hl₀)
  let q : W ⟶ D := l₁ ≫ sF
  have heq : ξ.app (op W) q = X.map i.op p := by
    have h1 := congrArg (fun φ => φ.app (op W) l₁) hsq
    have h3 : ξ.app (op W) (l₁ ≫ sF) = ya.app (op W) (l₁ ≫ j) := h1
    have h4 : ya.app (op W) (l₁ ≫ j) = ya.app (op W) i := congrArg _ hl₁
    exact h3.trans (h4.trans (yonedaEquiv_symm_app_apply p _ _))
  -- `W` is affine, integral, noetherian
  haveI hWa : IsAffine ((SCH).obj W) := (isAffineOpen_top ((SCH).obj V)).basicOpen s
  haveI hVi : IsIntegral ((SCH).obj V) := by
    haveI : Nonempty ((SCH).obj V) := ⟨v⟩
    exact isIntegral_of_isAffine_of_isDomain _
  haveI hWi : IsIntegral ((SCH).obj W) := isIntegral_of_isOpenImmersion ((SCH).map i)
  haveI hVl : IsLocallyNoetherian ((SCH).obj V) :=
    isLocallyNoetherian_of_affine_cover (ι := Unit) (S := fun _ => ⟨⊤, isAffineOpen_top _⟩)
      (by simp) (fun _ => hVn)
  haveI hWl : IsLocallyNoetherian ((SCH).obj W) := isLocallyNoetherian_of_isOpenImmersion ((SCH).map i)
  haveI hWd : IsDomain Γ((SCH).obj W, ⊤) := inferInstance
  haveI hWn : IsNoetherianRing Γ((SCH).obj W, ⊤) :=
    IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top _⟩
  haveI := hDa
  obtain ⟨s', hs', Z, hZ⟩ := generic_of_open_immersion hX act ξ hξ q (V := W)
  rw [heq] at hZ
  -- back to `V`
  have hWred : IsReduced ((SCH).obj W) := inferInstance
  have hne : ((SCH).obj W).basicOpen s' ≠ ⊥ := fun e =>
    hs' ((AlgebraicGeometry.basicOpen_eq_bot_iff s').1 e)
  obtain ⟨w, hw⟩ := TopologicalSpace.Opens.ne_bot_iff_nonempty _ |>.1 hne
  let iS := (SCH).map i
  let O : ((SCH).obj V).Opens := iS ''ᵁ ((SCH).obj W).basicOpen s'
  have hv : iS w ∈ O := ⟨w, hw, rfl⟩
  obtain ⟨s₂, hsO₂, hvs⟩ := (isAffineOpen_top ((SCH).obj V)).exists_basicOpen_le
    (V := O) ⟨iS w, hv⟩ trivial
  refine ⟨s₂, ?_, Z, fun T t₂ hu h => ?_⟩
  · rintro rfl
    have : iS w ∈ ((SCH).obj V).basicOpen (0 : Γ((SCH).obj V, ⊤)) := hvs
    simp at this
  have hmem : ∀ y : (SCH).obj T, (SCH).map t₂ y ∈ ((SCH).obj V).basicOpen s₂ := by
    intro y
    have e := Scheme.preimage_basicOpen ((SCH).map t₂) s₂
    have hy : y ∈ ((SCH).obj T).basicOpen (((SCH).map t₂).appTop.hom s₂) :=
      (Scheme.mem_basicOpen_top _ _ y).2 (hu.map _)
    exact (SetLike.ext_iff.1 e y).2 hy
  have hrange : Set.range ((SCH).map t₂) ⊆ Set.range iS := by
    rintro _ ⟨y, rfl⟩
    obtain ⟨w', -, e⟩ := hsO₂ (hmem y)
    exact ⟨w', e⟩
  let l' : (SCH).obj T ⟶ (SCH).obj W := AlgebraicGeometry.IsOpenImmersion.lift iS ((SCH).map t₂) hrange
  have hl' : l' ≫ iS = (SCH).map t₂ := AlgebraicGeometry.IsOpenImmersion.lift_fac _ _ _
  let t' : T ⟶ W := overHom l' (by rw [← site_w i]; rw [← Category.assoc]; rw [show l' ≫ (SCH).map i = _ from hl', site_w])
  have ht' : t' ≫ i = t₂ := toScheme_map_injective (by rw [Functor.map_comp]; exact hl')
  have hu' : IsUnit (((SCH).map t').appTop.hom s') := by
    refine ((SCH).obj T).toRingedSpace.isUnit_of_isUnit_germ ⊤ _ fun y _ => ?_
    refine (Scheme.mem_basicOpen_top _ _ y).1 ?_
    have e := Scheme.preimage_basicOpen ((SCH).map t') s'
    refine (SetLike.ext_iff.1 e y).1 ?_
    obtain ⟨w', hw', e'⟩ := hsO₂ (hmem y)
    have hlt : iS ((SCH).map t' y) = (SCH).map t₂ y := by rw [← hl']; rfl
    have hww : w' = (SCH).map t' y := iS.isOpenEmbedding.injective (e'.trans hlt.symm)
    rw [hww] at hw'
    exact hw'
  have := hZ T t' hu' h
  rw [← Functor.map_comp_apply, ← op_comp, ht'] at this
  exact this

/-- **`GenericStabilizerQS`**: the generic stabilizer for every quasi-separated algebraic space with an
action of `D(M)`, `M` finitely generated. -/
theorem genericStabilizerQS (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) :
    AlgMag.ChartQSStrat.GenericStabilizerQS B S hS :=
  fun _ _ _ _ hX hqs act => genericStabilizerAt hX hqs act

/-- **Affine stratum lemma** for quasi-separated `X`: form without the generic stabilizer hypothesis of `ChartQSStrat.affineStratum_qs`. -/
theorem affineStratum_qs' [AddMonoid.FG M] (hX : IsAlgebraicSpace B S hS X)
    (hqsX : Space.IsQuasiSeparated B S hS (terminal.from X))
    (hNoe : Space.HasEtaleLocalProperty B S hS X (fun T : Scheme.{u} => IsLocallyNoetherian T))
    (act : AAction (fppfO B S hS) M X) : ChartMain.AffineStratum X act :=
  AlgMag.ChartQSStrat.affineStratum_qs (genericStabilizerQS B S hS) hX hqsX hNoe act

/-- **Affine stratum lemma** for quasi-separated `X`, in the form `ChartQS.effective_of_noetherian` asks for. -/
theorem affineStratum_closedStable_qs' [AddMonoid.FG M] {act₀' : AAction (fppfO B S hS) M X}
    (hX : IsAlgebraicSpace B S hS X) (hqsX : Space.IsQuasiSeparated B S hS (terminal.from X))
    (hNoe : Space.HasEtaleLocalProperty B S hS X (fun T : Scheme.{u} => IsLocallyNoetherian T))
    (C : ChartMain.ClosedStable act₀') : ChartMain.AffineStratum C.Z C.actZ :=
  AlgMag.ChartQSStrat.affineStratum_closedStable_qs (genericStabilizerQS B S hS) hX hqsX hNoe C

end AlgMag.ChartQSStabGen

#print axioms AlgMag.ChartQSStabGen.exists_generic_ring
#print axioms AlgMag.ChartQSStabGen.generic_of_open_immersion
#print axioms AlgMag.ChartQSStabGen.genericStabilizerQS
#print axioms AlgMag.ChartQSStabGen.affineStratum_qs'
